-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2259
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:10:09.344012+00:00
-- url     : https://prove2.me/submissions/06666686-8856-4573-9242-bb039a4affcb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 406115107 ≤ n < 406294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 406116357 1250 406115107 406115119
    0xb0f010f03242a0e04060e1807170c10031b031d030c010b1002070806280c0e01030605040212060d0f140601061709372406080303040f02 60
    0x4904000da00c606514540382e181d1910300703400c0c2101100c0d80403c0c5204c0865094600b001400e0901051400420340106038070010340350840d241030201014400b00f00201034014059004051090000d0b45900d100c0c0304282c01445001c022212580c0701e4014840b8908200240d220005641507048000d0000c14846401c074039041c0c10048610f14042006014004282c000019640740000c100111407240d640703110700715802042d0078440c28001007405500040c0c90500150514541c001c2e07004c1c1c104420b69010b210500e04032924181c00d401400096001209903810080d017a142d204101c1240602d0b00100030000341e00c00022460b051502d0503595060045506240600c203503a00c58410a942c6e01403030000340c0240b8010845190880340c520002305050f50f00c90420b281100c00250384550b0a5a0a100c5003020b42034031a17040407000110390700c503581c00380100031541d681c240203050f01d01c0920702080c0001040e041d82c02404c0a03101e40401e40700c3c81c070702a51941c0c42d140c4803a1034180d100901603038060 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 406117607 1250 406116357 406116371
    0x3b160c03081b3c1c050736080712020d020402190507050f031204030e150c01020705100204030507050105180a12050c010309120315050a030b0f010f0324 67
    0x1400e05180c1002c1100c0f1202c42d02245040f0140c070803940e1050240204014500b4007004400800000804e0803056441d04002030aa440100484d100c2c20b41076604640c07032809190b00d80880c0f05441100c00004101c3c0c2d228147c182c0d40d40c4034199290420f2007404601000d82440400500c0c005201e0500540010409070402502c040032141c200e403119000d1022690000d401000c0100034400100b440030090091802d0000f0403030040c1007604020001420041e8542e1403103299a200c1d000c00c2e180017581000252100658041a4001c0d0b200480031780d0b05100b5078000680000705402120150784d0f102014042643c940030064031543c0049110181c80f400041640006845105110005240e03d4001c0302072140e0340e0030001d0510302c0c0c0e81d0310541014207218221010950800c2810060a0340d4a00080d0b8417684504907203000ca10754002c02d030312521041000080c02282120306018102c110000501c90340e0f075002c0030488040501c401402030140c0041100d6800e04200ca1225040081c400810a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 406118857 1250 406117607 406117627
    0x10620030706020c071502060906060105091804150e0a150e030c061e0705070209010e06010e0607060504050c01050301030507090c030b0d2604080303013b160c03081b 73
    0x284e081120440b0300c0d035000304020809000030200c00b2146c022140040e1040d4101103404c19220315008185a042c00740c00a16550240c640c645001d00300c00032946d030b90401d800c040c03403c001d0b00580301c0307010b51001e41030981504002e80041840c3c41000e81c440820a802041307950620050298030000c0f1516001c280b01c441030387c20f0140f0003240315081078582111207040d94903600555a4015003047e0030080140052401070b19003650380b40c10b64000a12000007070382c44d4401291150910710603190400004204041003141c50707001309010314402c40c10348800702100001114140000d03c409451580070314400c001031201c0e940110040580c3c0c0c41c0c0410340384204000f00c0d081041d03c502c1151080350b0600320010307a06404c00710b50b0341241d20343c194902e41441c1140703065507808103000710b021005104000001ca40303450030306200c44100c4220007082103d8214080411400d08039401c0e241c00540d0705141c245c01303210303504c1040040c3d03054030bd00500b522208003100f030070811200d91440442c0c04110000300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 406120107 1250 406118857 406118861
    0x301091406040303151202040e010f0603030504030c0509130b04060b0a180b090108030901030b031005101a09010906081f0b0c070f0503070e04030504090f1a0306010620030706 77
    0xc035066440140001d090a140060840700c4101503064050500d0030107003c0c0c2d4030312044440d400c030f0701198085201041c860403180107200400f09410f203140750140010805070404058421280600e000c8507460341e9603410301c440ea00c0c089501103030103401150f070301e00092140c80e03a283d0800d000b848001400b0740c0351004030304003020541004100c880351510700740002145010f00c0c40307a248242c9803500c40d075261001c0c50303a40307000781d040b158180343e21010303130010342d89003000140c3d120f603241f5130f090043e4103180c01d180d018400d85000d080c440100c1c0a41450720030150404450319400c1c185e64242001d480c04000b00c603500c801030030386010781d0341200005548103a244e1291002c2d2400d205141e03a600300c030005040c602005a40510800100510104029500410990101d076000900103030b840e516031504682c1c0c0e00c59904000f5141e4600518140140c071140e004007201400803000e48440c03c0324004040d0b94030000d00c80c50000070f45208800c0d180c807280711039000480c40100c1c2103034102003440c2d8490007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 406121357 1250 406120107 406120133
    0x60201060b1e16080a080906060d03080604021e0706020a0f020102031e0402220606020c1c11120a05010605130510060e0411180135180a06060911040f14030109 70
    0x3000031428014482c001f60107001080e0804001c4402089100b00c079a400741c4203100051640c0c0c42a0b9002c500540340d00c401c02c1404050031f01031118a560340d0b034107182c40d80007508548141d0001544160440003100e0051085074004c5150440300d000c80318455030072524200c2e00070412a00015044240ca44165003e030440e079802d6080b21010803c10704066000341b0b410100080c281c412440b446000c0341c0c2c811104200c490458100c01910300320b03201c0f9004104580c1a80680502520400000005001040d48600309070303601214415180c0710083c8562094580c10b0b81d0381512811511030402c01c182c0140c040f810913901c094004a603000c0000c4440840d6001a01c2c00100c1c424007a0b05945903603030001040c500d4181040c2c441c0324800c2084941c007150768070801400318882048c008296408201505180721503141403c490020a41d0710740200600705a200f01560303141001c000590344102001601d00780c800700c441d0060400c2c5461009030b40d004690003800d8240d580c4403c00310120340c01c10600f04e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 406122607 1250 406121357 406121377
    0x60a0c0203030333131a0616112d0a090207081b19030e0d02060f0d0c02011e090f020301020f0a0e180402060c0124060201060b1e1608 59
    0x1035205959070900c090014800c3c001d41c00072080c1c03030004c0c1100c3d0b40d04100c8126800c501702e40010b00324035410014003c8100c07a644564424408520b56007000e061121203142944280321784061009080203101441d0580c1008800708400101e130644a0800c18131404c4c00c4150040c44440001d0f41c031104441283e0240d1819101d42c070002884c0310404800607440899219500f008100d002e0303441000c540d59000ba440c00504104120541980983d034018074000040d400902c000d981ea001980490801e5100408020b105814203a080e486c850040c812010107015181d41c0c8a044060642ca01c0010601c43c07504480f0b04420b510a040562401d02c040e001030644500d00c81d9131400083c0c40508402605c50241c0d00c00c1d205204508000140301c0c00c89900140e05440f21a180c1c9940410315024040c1420300b1a400c0102000c0004c624624443d41c1c8101e4025400805c04103484007040e6602c1d21900c072084610015a00c00846c081d82c0740780040502c50f006015511b80405550360b8815203910010b01a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 406123857 1250 406122607 406122631
    0x10501030b18070f090c020f0325050114180d020a020604060f0c05010906052406040504050702031606051e0f070507030203040306050106030b01031b02120d060f080f06091902060a0c02030303 84
    0x2e0321b1035404104081104800800542c2400040b05860740b540c200303007020441a6120385e0000301048000d4102d070340400e0050310941900d1a0038559401446281850040240b05200c002e100281c0085032494000350060005841e041c01c102c0c045e03c450301ca900b084410020303880316590100c0d0081c42410211480b0b082c2c0403441d400d044070004464880c0c0c0b50034100070904131407000e1440e51883c0c1110104c84040c1d602103019a20100203904600030015000700d2800889500d5082002c0e0360302c041e116854940407405440c84403418940c40c998219016511045c04c400440ca610340110060041c092003481224a056101d030703078a07000c0d600f0070781c094808680c480c204050301e5078050043e841d8440041c5850200540540e07402965103091b50890a01c94400040940c282181504500b000e05580c056a80b441c90351801207580c0c4100c10492021079000700c40215904100210701c01107111064403d040c0822100d4007003048940c009042401400604841c84d401a202840914802d54160140c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 406125107 1250 406123857 406123871
    0x90305060c12160203120c04030f050105010608010b07080412211d01050910030b010e180105040c050309120a03021c020315040605150c030412140f010501030b18070f09 74
    0x1c46070382c807000b400070718038403c011008804840c0c2c00401e90304c0f8110000c412509075140e2000c501c0003407103140c0024003644103682c41c131b005200c1c0540101d8100c852035554034105030b90303c41c4941f466008412000b007070003204010400c42c0d000540f4510a02a00070041880103080c2000b2490448485c1120f08002c01c00c91001c0c18540c82100c0d08440c0a11400c2c2446482d007114500022000d0444c5c080e031100b4180e485050300d0485c1d00c6043c1c1b02900d0170002d441000c6811025141940d004030034410180710380c4c04d140b0301c020501c0c4213006490182c0e50001c002c4c625418206517024443c3c0049500e041011b600b0300840b81810511400c0c094084000480103a6a0030b05018a400241c40b50301154051410080b003004a41c1f14884216418804204041c0d2211040207c072070540c45590b001084102c03082d42400240705502100c0c0c0300d001000c6003100c080581d600255030a03240c0900c4054003081c0c591000445c0e11040b04040d0300d00300c0700041910505900c507600c00c0c2010f00b05400c102e6100342d555032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 406126357 1250 406125107 406125127
    0xf090f15070f1703450a05072405030a0e01051003050d0206010b0306010c02040b120d120509030328151e050d0f21030f0507080411010e01090305060c 66
    0x4070050f600b00b10301e1030f03d40f45252241c2d00340701048900c1c581900c80c034422080800d4400b80c0c02e03140c0100e00b04025080401203c0408643da0f244e03101c0800390f403d030040050000b10428401000b140c4040054a06101e80480100548407a040206485120360b150010380039000c101703101c3c0604c20841118540c0410f82541010707403402c000d005800d02590f11190043c003c3c2d0680809503a4841d2003444c1000c01d0300900d201140240559074101c5402400010800041d00c1000c11100b01c10342c2180d07143d111903004100700ca0280e03441940c1000d8140c01c2000480c40f0504e41c00000c8040b414480340400041d006500341804680f45900707a001d150208000501844285003000c0704428038240c10f58000b1342c20600000c06000790010018202801102840100003a00501da16420f0610004409500c400840503003d4400c014040003024585400108503d020b46111401346420060524039440820019034103030326030440703450511403d4440000000e8080182500c640c120300c85464440030300030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 406127607 1250 406126357 406126373
    0x72103090e0403020c09150409110423071b0218010905090f0c10020f07060305010f0e01030b0703050402060d0609020702040f050405030f0d020405090a0e120f090f15070f 75
    0x900540007401001c41400086a40041e99400480003220260541e448000140a28001100c2c41d590828200320068092026110030840014010b56003400504005980004030100062001484ad04482c0102d008548a040390170b038050945450604140d074144c000940d00c0e0718412017680c040320003030014498141d950060981185584005040c1403d156440a44030304010a07401c0c090700f04181201107203803007003080450002d001804d4400b0941c68000042c0a45001d0103121242540308100041f07501c4100d00850499810015029240d15100c80031000780501074000c0c0c0e8002018000c81620008501c160401005a404c1c0181e462445106000a60390301364440098140782404100105601008070380c4c400b241c500a007a590410004030f90007d0007140c00203500110441e04001d00d541413503002200c0b15003400c0c2160007103504014010080d01c07460700e4410510710300b408041c01b1824030480d00c18410034010942d04108010380300680307540c0c1103c80141ca0401d1050840c0c01445142 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 406128857 1250 406127607 406127609
    0x201060e0603030a05090312040303020d0806030610090203040f020901060f030e0a020102030a080a0207061805011a03030f0a1115160519080403030b120601081504020d110307210309 80
    0x40d044001840c039103000040c0d2240540700b00141030102c001007501a5980c10310110781c14030301c8000800d440b180c40e804c00945c0c444941c00000040354051020070348915000800b5440750049d000203280160601012001940002d00100ca8002009030b50340300590312210394074064130300c982c0e82400640c0c0011004059aa234a8070010351504000801800340c2da000c000c5800410b45414603174010380301d5407007441c0280309058029000f249031a04d90619210881030800368503000b8002404074901c02102003980d500c0a031031095166004000322a050a203100241051800905020846e1001ca401e4079050441c00c402107400342001d0380411444858424403140041c0310341c0307092800c200b0704403c60019000e0310b0a4040034071048000203003c0621a400c0003501c200090210020313240300f9007181c2c0d41c500f400c0c010b003805400780035400303088104140c056074407564000b4080b020010198a60b4607802d030b00c84084c980c25001c0c0140c0420039a02d62900640c11507110365040c0e1802c034917401e00410080d40c0d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 406130107 1250 406128857 406128869
    0xa0905072706241103070f02010c0816140d2106030b25050708030a20180a1203050706020705192a12020f0a081218030705061b0a170a020106 62
    0x407410000d13100020000a075210203900c020794159420541c00103070313441b5408810041c1220000203025600083d1060610070329407061195860300e00036042e0094581d414407aa220001c1d6a00060084a10328041039060842c100a000250603480e40c0b14440b81082c00c03108d20760740324840d4000c1c00002107400004100208149020390402a0b10f5807010001c0c80090704d2044215100c2204170f21944c40c1110050001c0340704003a1565401d900e40d840e07101000300044180c40b0796405000001c01c0e1031a0035005102d6030f8543e4480749801c020390b44500094100c05015601c512880940000c02d5079031802861000380500c0c0d10740001c03454100d6013450f007034a030602c5841040d600d4104201c06420b003c49074070031681c100c400d002901c54030340108441544540c0310342507920070030502a42d0500c007071000b0411203501500015a1400070000d1640d1005248a01c50300820100501c0c01d0400f01c8241c1d0018800401055035013060316a16043d11008151402410302d02000031203d00d01e40e0240301c1c90009000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 406131357 1250 406130107 406130117
    0x20a12030801090203100b0a020d03140108030d050405030403140f061509190f1a04110403030c0305131d1e07020d0e0a0e1305060a090507270624 64
    0x205598010a00c074410310960640700c0c0c000c404102d82804100c03490001c0c0924141c0303a6111144800000e5403900c000e0304030804280762210003144580d0b8402650f050b1003019000b907290510312084036000f003400a00541d41030100380404400540b482c0488500a009030f001802810b0304141c107603040031000341800f076594850707204000d5192140d030f04e640d9000c410103c800b140b10104c502003e020b40040d024030101589860210b4000c010a044161b0b03900e1420764007000a40c424401c013a5031489a80005400315420740d14400c0003030300c11002005005000c10ba2411071a944034400d129041c03c3e06803071a0050100070800c4a034008040c2c40350600700d0902c1403250342e0300709004081e445004101214040014034081060551240d85d420801804542d81803449440e0404a130318115000c0403040710359010f91340c046568054240510380d0000d4101e030190040700c2c80c00000c00229140800644080740440395a4200c83e40140301e0400240943c0502d410344880c5907000040b150004810102402 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 406132607 1250 406131357 406131389
    0xd020114060d030302070525060c0c14130e0c0f1909110903060103050a0212241b03360703080f0903030408010605040c110c0405150307060903020a 65
    0x1451000c5940d820000560360385006181d1800c08901900c22401c0140183c1710310014075800c001c0340d105c403402d81c14035281c1e40d2176200d44480c8201d858103805c00001e0641d01695105018482d40f4114950301810002c107407136004001002440259003440360070f00d660790061400542207003040c40c8402110b000480f000315801d0003210058139a142280149001a6681d41d41d1a071652128012104644401411a0401c0d0780da403802c5551180388080c124040c8050354000e8100c110700003910044440a03402400e103c0c0c080e0b000817512500000e28102c00d184400f5004c0c1e01400c5180f0045010324006040b08100c1107040c2c25001d0100c20b0701d0f2001050136140c281010140b8400b013503213007d0703d40c070001c1c0035a91000006412124094400510b900d400000340000b525001540322108407002601e040c007143c5c0031400192528820b41080080702e4111183c04201c81c64540d00499100032940e00d400080440304012a2030034160b500401c0101c0d030a16400c0c41940f81c40f1001000403c40001070040171 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 406133857 1250 406132607 406132631
    0x90b090906070e011214160f02060c0c1203040807020901060f050f090a03080f04080c0105090a051c061104030c0902190f05040837021023030f07020d0201 68
    0x2445000740058100106201c042c0f6050b84a8002c0c00c1c0b00e6540d0039001d00220316103088800012400391347c0d0303e00c0c20401e0301c541040b407030007003262900b0395080360080c0540765034064072100140e11030200b0a07240d01425070240100b11907240a917000d503004000f56925203656105018045006820100038400c64400c00341c1d00a50200031200003400700400c01c0c4d1100a0034000c140307064000e400003451400b010602600c6040c111000e04100c0365490200c422821400006484501c50141000e030070400f81d100038015810100300103501d41c2c078041ca030b00340d01e541c058076224202c0b03000c1d581125004400040820600185c0d03940c06001e4480d0510451600013611010050705414444600500c101240d1149015000d50184e800809242058441054034041d654480701c0c2a1500d41107942135218000c0c005000040c00001042e901030301000741840025410f0340c80b141660342d502070b501d104e0440d400b4544440c030007540c040e2000d211400075506103080c0103810b1038040c8444800316031401002e0b50311 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 406135107 1250 406133857 406133863
    0x102061005010507080c030d02030f0a090f06022803060906060302122215200c0d030209040b1801140d0f060c031b0c12020a1110090509010f090b0909 66
    0x441e1000d0900030b95803d12440c1086090140795201c1c80c030f90101062040343c0712074070f4000394400c0b1942e82e02c0450b60703030700c55200808032417002d01c0c00380c541c81d03543301d0341800641c0c10b17401404604c0c0c22450015074107060a90b121960312070b84c100000008e03120102040b08403a47d00031003024005508065041011144810f020a007000704428001c84a032a6040d8401030b54204141d5502e0300300b5046858408a202d0314400341c4004c2032032500c8080c0d00615900c0080e165029100f8001c071200c041e01c142c40b003001d011000b83d00540d401e030b0740c0702c0d5403082c2c101c00c0d6689140180c402e500c00070302c41c40c0d025032501c01011022054005494050403241900c100001d0003550200b12160344000c000503065405c5da411002405980c0c1480fa070210614000156103820100840101380304c0d4440e0038940c084444102c0e203500400d00020804080302d08103446915242076501c3c22500c0301d290584400b903403040000d100c01e000f80d1044c04407000c24201440350050f580a0b108060344141d8008003e82480b0006541d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 406136357 1250 406135107 406135109
    0xc030b0f131e020403051603080a0309050f19120c0c030807030504050901090902030d020c0a0e09030903071d0105010f0801260133051f11060114030c01020610 70
    0x441004110303424070001c0d22591081080c600081c8505400ca8982121040258072a0006030b606100f80032041055641c02c5402600b0342c2e40c884219424407070403900c1038002d40000d489c201c405016010149a410100b0171039101e014407412a8401d0700c0314141841101c0c6600c2c44200320400c110554603002081e030301042c1504480c1e0049142c0d0350755000307080803102405036400c600d81c840d088200008960003070390450b00c4991b0086043e1000050410b206170780e583c4052200035002070b60254104000206001000e80c0a040041500c0c074180d01e5200180c01e01500f82c100c03030aa040310840d00250303c044100b00b81e001d0a400e0808104c26011441d001d0b09400051055441c2c48500321038180000d4202d1020f040410b00c060006c0c001001d0f02c0707031b01020b0509040103100000741324007841c1e1001c820102c4080101d500103040100034805110846030407224001d0090244041c0c14042a2261000c02045008100e290f0003000702c203c8510416040c4628804858115840340c0301703000300e244226803068 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 406137607 1250 406136357 406136359
    0xb06041103130c090b0102030306101101111903140c0703140d020408160807030803090a051002091005090936010902120a0308010923090a060605030a080304030f051605100c030b0f 79
    0x1601a82003094210cc3e1008151894885542802c1020400e000b40002074842c80d42d000b502040d00e03800008048003181c6030240c0a0340940014404100c05203c44001018818041d2078500440c200007040c1e0240c90b03005008500b1100d500260400140000380003501d00c49900c00040c0401510340f403041c0340c0d074100900028104010000104500020420200d9480303a486001d9480320040241040700039004a010f09001c0c01c109015aa00581704034200c4003003010081084940d40c40d4401780980c06001c0400014501c420040351240040011170408004080c4c01f0000c076a142c9544140f0942525100e44810740e90b002c480d554001035041504203054891700440000c007110005c0c0982c00707d0900c00c03100001144102c003405450b40300440e4040186000d00020301c00c01ea075450505540d80078031407020f0904081813003c640040d12481c0700c80340c95001c0f8070308507052204140e0051406550040c003122543e200c1690008809024019138100e072019060401076881281d000c28030546440a00d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 406138857 1250 406137607 406137619
    0x1403012d020315090907081e1504050a15050103060b0915040b13020406080114030f0318010c0b070c1202070609030209060301060314070f050a0b04030b06041103130c090b0102030306 80
    0x1203100728200800c034041c0c14024024041801c0c00074020b0340300c14880c01001c7c001d001d400b0a0464a24808460b1081890302070000c182c0d001e500300b800c010b4414058400c0358103001d01016a40410700d0030b0001040503500c2000051154510714000b8101c4036250007560190842c0b0003040103449109841d0b6800c01740543d00440c00c088440d00040c400650b61f110f031010390384049004100c2651009085050320303d070a007450010101c2070105591114210100065540200f201c2d00c0501c00d221083d40303007840c040c10b103803132032007090391381e490340542c0440306035000420030001c5905202c0c440c42c00290010071400a8400d036410800001c00342405800042e005516082c08200f480d10309500400041d508804085200400400c406442d01c0052049151640200001180c54035020301860110b408510483c0d15091543e921028000001071810360701540d036001503a220312004008500c01e601a01c4400c1d0312801c24645280800120f404c40445585004d4161800c6e9800100700e90f00594100c0350 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 406140107 1250 406138857 406138861
    0x9030806060a030e12180603010b04290f03150a141509090702010c0f140306010e030a05100b01030e010b0307170f0706080103120201020306131508010203011403012d0203 75
    0x401c2e0b02a04c2c4000b0310041074070858440030350244014014103240320192a90a1001c442102009180e00081c0600000a0f90800080046d02c203002d060f900780e01c0010313503401e00c440500706185649070004074106d058a2400400c11040c2c0b03070028000c02200d041100e148203d10309010410803100726000b100f9000e044101d001600c0c800310720b001d0b0740460100614100701842c1108009020303040850441c00818502924072405a00030075000c1c20071889012003904565400c00112000c00d1140105a058020010140082002403143e4010018400d00c01318000000600060031076651421104003a49040003401d540e66000c2190411101000d010700081c4400d0103ca906007038090408000a00c904000026000e401140c2203040340e02612200c010042d00c00c006900380d11045904642c00700c008080c00340045841d91020005441d03e1554a00041d1500001c0c0d0072070f8000c0c0c00503501e00c1440310b20100580740c24021044032400604240c03541190f07030648018290300c4540941110394000c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 406141357 1250 406140107 406140127
    0x402030a02040f0b18010c110108040c081006180605010503040f02190303020705042306011116081b0102010b130b0d08030f04120201110f0705030c06040507080601090903080606 78
    0x10b8901400b8031060b5900c0c0c1c0307540d40404089a50000f40c0e0103c0612030020304074403d6006240e8000c030150808122065444d5103401101e00c110002c0007100c80c11444135002ca81586c0c1042038159131030041c0c0000801c10b06260040e0114030800c2140b0388a2030130321703030180490390740f200c2500d40040d802043d1142c1c020141c40002d0b5204440c0340c0d43d00408075000400820b26900141c0703501180c50544080007501480c2c6402c9520001406aa21031030341000d0208036994440c1440141c001610016a607000c11603030304802c81c0c1171866000c90f140c3e900202200710a0412400d044100e5002400204005410000801c02c401d0300c0c0601071114559460b030381070745034545401ca203142640c4040c5281e62407a01150020311840241e4040e81d010284411a4480a00521880d14181046840f49040402d4860708410a0340050b000703c0300b5010a001d0380c800c01c2400c100007400b45200f94040c0c40c5441c10042e0f0603142000580c42030703076150b080c80e4150f80401e42140d0b5072038010700203590055642c20108 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 406142607 1250 406141357 406141361
    0x70b030603010204151214060604060f02010f1b26071d03060c030a1b0801050f0d020a0b04051503070c0f050a170c19110d0f120f030c0216050402030a 66
    0xd40301c80c5103d800701610b4001c0d668045510720500c1188070007007005081501461f078084100312880d9421481c1004180a000d008a5a80c9006e4082c0d1002003039501c8500c0341002a1524101c0c4114042da121080407050794114500740d404031140c10070001003070041002102e90b98409061312081c48802244551005c000c1e64090603a4900581204c4290a100d030003004136a108a0b210021149003590400f49004410080c01000442c1c0d5540c66060b400d0600300f043c840c0441480541c85101c8402c1800140c48050440d00101900b440307250700c0e1842c180a102c0801c00700120618403280800422600300c0d04094071210580e0400d403001d00414052415520b4081105000340210140102c0c8a902112200081500607030305d41c15160030520740c4e1099154650002001030122290740c280c251141080070440f4070181c01081028514445c81c5c5901c4220180c00c61008000386521021060b40340e098021100e155216200420311068006041c2c007150303159009681c400c64001000c240d5000f015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 406143857 1250 406142607 406142609
    0x8010b120c060d180804230f031213030606080a02120a03080112020d08030f0106110f150c0403020d110108011212031d100902040c02010506012a080a11010605060309070b030603010204 81
    0x55081d80d41d07601c0d1440200924803c0613211f125007111141d000c55820600d44d59813406402400138801105080038150254000c0d009144d445034500e10004081140c034081c0c0070080403410044e0848140c240140086148a0142124554081001480001c0c4d0101c005030460f0980e044108a42e185440065a16051401c2c0a05250004001e10250101c9418124100c8545880d403207140c0546148854a84418884e0b01080d40c00c450b4441c10002c01100340c09502c0441c50341d00c03e150503160781c0060001c004998007a01d1092003007058030041e58014404901520f0b203c080b41940c1d075112780e110503030324a048201d5401c00d5110300e0459150b08a100c81002c14036825401c0c1c0351801045811203000b4115001c09912460401400d10302e283c2c01845424000e100603514850f001820f9001d1803c10f0307131090903214540c891070780d422012551200103084c041c005640c0d004885070000e0101800d49409400c500d101d0755040040c40b4000800240e880100d41c0c402039444c0c2c40baa900c00000340203002d2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 406145107 1250 406143857 406143863
    0x120902090109050603070801110d1e02030c120114220608010e0c0901090c0503011e03020904030504090e0c01020303181e01090c1512020306041508010b120c060d18 72
    0x403000011641500310342001c0e221300d409400705d80c001940c0f51002c2d0b00703031107004090701c14182082210088240160300300b400e41484806000030318825a280708022680200e8000341d13402c60125421880c0b03040300b07011500400011000c0500e000f800400106032606490000102c40501a0150380189550704464002c1620358020480e01035103150443e107490003c0780070341c031901100001107203a2541d84611580b500a13503607010f0440c0c1c24103003001d1070340e020f81c00064480505504d000005995200c1b402e8401d510903a03035240c0300d038039041c80030040c0d616569401200380c11200c0a040141d03400429a40d01511810010409114000c051820100303001c2458036100e604100c03409604105400c048004c0d4410f03c40000c9091703844840d030000055031414040050b05000310f101c1105030540203507810000040002542103400180036401d080d0b190f00c84422179442e5402c44803a0314000c81d0810500c1ca013400075142d00030000000854034800c0c0540c0202c02030340c55001c8854442124800304030583c1c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 406146357 1250 406145107 406145119
    0x6050a0911270d05060a0b040e0a020904030203040803130603060506030412032d0c17090601030308150409150621060c141605120a08040b1f061d1f120902 68
    0x18050511303640340d510032034481d0348540c20b0402c0c1c10080d0405110b5011505005800b13800e084906508000c1903000142094046110500c004901c0c001c0c1400144024981954500b0900b0b190242c007030305940d655442240300e80801e0081101080c3e00c0c44001044072414640024040300000c0b80b42080e040c20b00c0ea0200c44bc4403c00c4140010380a54081c400108052b02d4280f034800c0b4040c0300c200b100c1c00032211344044c0d802010041001034020078075145c0110078042d42d01c0380f0300041070219048500c01403081d22640c0443d000c003181e0b843d403481198050150f40d429007100054021a040c102e65084500402850342c2c4d40c1d1126007144203070110740d408102e074103c441d61031a00c500c0c1c003140003031081400e07241401919540310100e49103404031010042d00307840d507900503038031502c0d010058a0000c0c0000b851091a101d0801c201c0100d401c2c110141004d5258071441d0020050070140f00c010003a0164080d90f031a101c0b4450b4200c2c030401048003031600345000c031503031088403000401a008448009410007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 406147607 1250 406146357 406146379
    0x71110020c0318210109020414061008070309060504050604021306260a020612150d12111c0f0908060c07021c0b24010201090c05010f05090303040906050a091127 71
    0x4d0040d000b180a2030300880d01402401e00010300440c0e0940203450f41030b8401c0c0564005044107004142095006009040000301c1c9001c81e102d1105441d4201d500315510b4003c2010041141b501800520070b0903a20712040007140e0814444c1d00381d040d542d22403211018401c400341c0400c03070020004100d2650b8064005611062400c802d070202400030703500b0580c05103a201e017009003030512241902855801c20540c408151900c01c00350360107140c6491a90540c003503941c008002c0c1004411000b81114540da40c4001c0c01d0a01400a2004074503420140054011205103c41c0e03d0180d810765a060b9012100050211074050102d0340c1a55120310050848a80c03104004014645805201005502c080c4e00c070100b11403200120701f01c802c0c40030f0080c005603034400c060210394454141d000c0d0108003410a24030b0500c900001074a507400a038821909142c56440030f1095040c145041b03070040010200c203100d001054401350000c2d006041c0b041035400d12021680040302800011a9114074000d000c8103014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 406148857 1250 406147607 406147669
    0xc030d0c090518040203030702270103110307061404050103022107020102070326040803091f05040c05010f1d010e040e0607030501211415071110020c0318 68
    0x41d00e142c8200740c4a00d200d1040300410f6580540070078072459000300036602c1c00e06541c1c00c00c42012580014004d83c910044401034004007100c0d045c50296014051010722648607500301468450660080000c005401c022201148540340c10342d8182e0b40f003404d0140e164030481d0591140761440c40840e1080300c280a05010070150107500610740ca6000c0c0c4c0d202d04004030351034083c2e083c080d41c80442107408500980010301040e1030308041c0d43c001c0c00c2001a036a0054601d1714400c0580c50001c994901155503105010410905203102c000030002030910882d40c0a003680040c0801440a41005242100417035a01d0103a10440543c5500c01004008010410141c0d032480d986100484400b4003181c0f900e000411840c058409507600c000842c100c0c0a0454440d40e00c40d8182c0f243d907a60641c0502c602d0100a048880002007588110303a15615103190201803211646070080d841d80c18039109204200301c006003880441114100e26031010900d044d43c81d0100410b00050b54000c10527810503540165010f5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 406150107 1250 406148857 406148867
    0x90507051e0a08010b09012c03160f05031f0506031c05030f180712020a0f080a05070b1c092301020406021002090d0f060e01090f021807140c030d0c 65
    0x101d4040c0e555440107a80e05c4000f600311324800c100c901c41c04503c054001d14212004002140012403043e03040c3c5000c4041500030a1901803040c2d5810a100c2400f94284144d14140c00c2e2400100701c12001804902c5c0700100504c0f15580c00d89101d1615519040001c00c584c070104905182c41110352081460743ca003c0d48010900d81043c7c82248000f107080c008513074050000c12603448520301d100f000c0c000b450724100240444100c8400106c1c0c001c462020001010f070202d0052070000d00a84c8007800c00c1c0c508a240c00360a14011f80c00c10240c2c000103002c12444110a86000ba541d1b40c154000000e009586040002659034002410018003580045034986260190041d004580498080341e40403421101c048060f0301440c6105a045440742e00c802d40030494100d01c85015600070f0200007841c11040131031509441d01c0c0c003010b66580180c0020310b011410000c41d4050851602c0c0e03403661481c103000000405603130780c18501c112a82d10100d43c2d075030001c9041c400c581110181200412084000d260090301d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 406151357 1250 406150107 406150117
    0xf030d09030f0306180f110c011b0507080306040f0b1002031312050a0b0c040f09050f0c0705060105121204091a06031e070c06020c011d0a0804090507051e 68
    0x40021280c1c0c05035030b070480c0a80521029034060f036100742681d501d0170072a14000d01c405103c41212a845403402c0741c07000658801002e1194010001080b068407014841c3c1c0190741401440003000810007003200402d0086050b281c1181040314041165103c030000e2101030312450f8042940400004080c820003900000104110050316500108507681c61481d2040611595806410703500304120341000035084100d0154000400c0000d141099185c10079201000c01c19001180444d036603406200600c21140104c0d0b900c841c41200350744c688061503803101d44811701880340d18000c010358400c50314a548280079803c500307034030051202d84481d40c03001801c024000112114040043c3c1085950b003c1c240304007160f00c600d0381d03da04c503c0d418140700c03c071146103c0300130070070740420408140301800034015000a286881d00c01c000490f400c2c42203402a148861041440621644041c45001c0054000030540e000c89011020014240d0f880a00a960702e101c0c2249040d00140d4101c1c40002203407036036001d04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 406152607 1250 406151357 406151363
    0x301150e13051801020c0a0f0311060414100c300207110906010c02060301060e010203070c080f0609160308090d02030f0604120822060e06010b0a1206050604170f030d09 74
    0x3620340010f0640b1401c134883c101040603036400c070104071404035100001d40e4032598801d2425030b24001320107541d0b509004040d9421030b075000c3c0d056440ca82000007004030b4080e41d003445501300660028020054640c007400d201006824031070003400b5000c108400d9981d030b101e000c01d11007995508420320300031b09446540211300348070b0742298007c0348803540f0503840c102080368007410311807a690030300e0001e81f0345004c03900c03003181144800c00000000a48000b2004001e001200013071030241003003a42e40f401c0540c02010500264401700703002d0b914107603450420b400c8a0b000400a55282c514201181110220200194041c4500b0300742200460740018114400c034090101080400805102103032202800c2d10410130596400300d15540d0780c0c401c4456130864034400e800015000364910089030900100364441000d564010842c500761540000c5804844010b969003041800d040000080340740c01580106520b04540e152049112241044010345207030241d01146d4840d040345c0303c4032015105489081b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 406153857 1250 406152607 406152631
    0x170d020c0708070b0306092a040806071404060e03011118240403080a02010b030a120f030603051905030f030103080703030b03030a020604060e03070f050705240301150e1305 76
    0x380000b000320b4484103843d50240914656150a810800031180203000c0c800f0941c000d408030b0409000d0462814608507181904c1c0d91603a20703043d046410610010503d40a1005d0700002100b480c424004035015a9040e0400414500b1110086401844030100c40450742c580003600304004c00c44034542c0341000034100c0c0c0c02c01c84411085201a00104100440007540c1814002440010300d050050004007015200002d4884c007041c0009140041c20081980d032180c0030014503c0403076000c0d030380952450701810240441031940d6a003655a1013030411003500d80034905840010030805004031648040324044036500ca58480c1002441d5510440d0120301007494140c4207205420080255000c0303001c281c01601041d41c0d11380313400001c0c040080000000740800c1200d9000182c000c206c1c000c981d07001e900107041480c1420107101528000c00048680203201c0c0c4012541c02c0e25941c210703419500e5403100e281c0b40c030b0341261741627030306000c00c0c3d200d070740e001d4400c101d06d4024008991203640301e04c100781d43d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 406155107 1250 406153857 406153859
    0x4080c0d0c08070222020d050402040e010c0c0f0f0f05060108010b010306032109091d0105090109050d0e130f0b0f010509030c06090d02040c0503070f080c030a0504170d020c07 77
    0x81a01d04255507070008040e8031042c000c2801502e070901c400c1d000b009540400002001601071020101d1344121441070515646d03c05000a50615100b1808103076a06002048880085000602800030941c00100b2400c03d4036010410071946440c20381f0741395032004840b40341c5d04540c078142d5119882401f0b00e80280d03180c507441c1d102540c0b080c059401101c0d0401e44841002156820310501c51ba482c6e60007070180881c0b8000001c84900a00c2035000744407400c0082c890010070803d4060030340d8806400c802e20750b81414501000304101058100200d01a810069003d94062000c256503e4503004603031480791a01c03040c0001480705800180040504841d0410742035410001507801c0c2c000c00c007100d601039000c44105001070810200400440b04d006007244151304403540010240c8440e03a40b02c00c0000d0b00441440300c0c15400c1540b4a11304800c603348920b0394030340a5010402400300515881c0d120307481d0800305040c42450340701c0611202a9003421617039041440c403000044c1d800400714001078402d201c4c1c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 406156357 1250 406155107 406155133
    0x60702041b170f0f0115090308040b0d051e01060516060c031a0a0609050105070206090409050109031206180209040f0501151d0a060c0816110a0504050412030507030905030304080c 79
    0x24080780f08100700302c680c818903406c4c4005642e10320540001e11080c005040e502101080e4090050300040841d9041300d6916050402c0c01019201c014082807540c1c0108950340b503500703d2107042d0506480040c030702161954001921101c0000e910200a0245450400c12040c02035042e081040c02e8079101480040c4102072800384600400d40d8030071330740010b50f100d40a02096114030020401540010160f50403e180100006d085840070103084400c5d0399220802c030b0030550842140041c0000083c030401a080c076180d20f801901801c0c00c1c0d00080e10740c0c001010800c0740c1c1c4a074809140e403104440304010960b140c4682a080c40c000110aa01080841e50101406010300d60842c84400000d842c48400c40c0ca012019101046605021a00c1400910040c400d074a00000d00c240c0c0c0340e0103400400141d401c41014026002c040fa00101c1c000e5040800300000302d00003082d00700041c5500e250004459a130300e80110b000340b4040c5030090140c00000280400e112006001e059a080c4507415a088081841 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 406157607 1250 406156357 406156381
    0x1a0406031103100311131109010806030a0f02041d01021911031e03040c08161505090603040b09030d0207060209190303020709090309090e01020a0206010e1302060702041b17 76
    0x2148002e4002601c030f82440014861100317208800c40180504004505841640050f00c004415000008a0100382d460300341d03034010355a0750028003d40c042c1030103007129114042018601c2c1d002038080c81e101c120344c81024030a000c0f0340c0008100d10f00215201c40c4002411070450700051540000501140ea52410406020003260341402401484244e0001d05107444811a0801807094441c400c05120015082105110030034803080310000c58000d503804c0c4580c0001e041000444207003003140500203201301d40c4842c001c69810640181540e1a582d031004605440d42c803400454103100307800401c07914100050758002d0894514102c1d21002074000c143c0c080c000803041c034880030300145d020a001f00300200c05a8040c000d003902900d403c00d005500c900d409020760300c581d0035810090b1f50009140c0c20195040c0201805090140c07040300c0d907410300c1c6854501c20094417001a1040b100014113408541c1c5940c010102c4400a8800d00410b104a42e4003910309034030900d240d110110550001a2914110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 406158857 1250 406157607 406157611
    0x801140117100b1906091a030709061817100608010209030a0b10080714040c03050603031905120103030c0b010b0301060507080904090f06020a12020c0309010e0a1a0406031103 77
    0x4900203102c0560035061850103808450071a80d0000309980100d070404008a82d54000f03042c0039190840c3c0c4528010b00300c0d89400383c035190845181d0040c803e014440d6845406802154254941241c2c00760020011040c2c0700031b0b071340c0404d1a00c0313000c00f07640700b80c00c1002c2940c2226848284003080800d0b6100c080c0c900341d05c2003105581c3d058000311941030001d0f4450ba10260045207000d120036580d600d03074120a207040d00710340110001c04202041400c15140c28003400c501d401052500344254144070000c6940c0c0e00940310f400301c44101d801e0080e041e007440b6905403400c1e80329040c000940b6581d2414003502c000c440d40001d43e1050755070400460b4454071401241c0c100e0b0b02d0356036103514001c41c40e00d07500704c20303042241425403280e10388400310007042c02c000c1e502070700074065000169121855980030300080c83c400d01e00307102140107010070800300c0e8011055518145080c2490601000480d00103030040d03c03e500128252005980d21980201d006400341c026603065032003c2007410320360240c0c0c0000303000c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 406160107 1250 406158857 406158899
    0x150d0b091b1521010605090f0d0b01031211160303090e0705030103080711040914010e07080a060e25060305012112021e16060c0804091806020408011401 67
    0x81c102e402e0141d00d1400005085460403400d44650407082010b40e06810301c0207901c00d000244000c54803c83c3d600c2d182401c5000700c40103c400c50307040074080d9582c804076841403101a0a04076040c101e00b04c40c5000b40e4980c11544682030a8ae00b0703500c00701070980c068060038001600006c52103100400c1070010034060500881e401c1e104c1e507065a11719030300c001e0742d90700c01c42c0b04445907864500500d12503141c9016030f0012901c541030800509a029494070b0856161b04003010055010b078000b0845610046100c00301550020000b2440c006000001894620010403010710902003041d0084640c0381c480c080c0058a0309564188900c0c1d03039890b030244542400c906855100020b00b64000005018030110350100c00207401074034440d0450300f00141401303098941011540c6c00210191a04894a0002c034000d4091420007191a000d80e03107817a140c038003a0f0b028115406035154003140c5585404050782d110183e0003041959955191000107010703040c5005030303212081c0ca0380004105001440c0700a480500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 406161357 1250 406160107 406160119
    0x20102030d2c0f19061b120f05070c02120a0203150a14010e010b090307091802130e0307030f18180b150f0702060405130b0a0b0906090108150d0b091b 66
    0x85038281e01d44558044501120134a586c1c6d45103482c540f5080d41a820b117000261901110944244201c100751110a42c0e515106860203040050240e0808a101e01080d010340b003400c02642c203000403d19151a0010181d03141c41001c000c0c03d00410384060700c41c0b1800c1559424410803145040c88004000280503210100c1ca81c41b00501c0454043e80c044d0684c07000080442d0b00e45990384c1500000c50311011040108201a86c07148070942c02d088d5400030a00e0051a02000340c42440ea52040e200d014480d00241080440308000b2680d910500e9401d035012000c4c0480d10b5131a54a0b820a44440f881c0703105c44100c617040a0041c2054071f00300e640302410681071142035141118060301590300b0303804140100e91240301403101180c01d490b10b5100c044045c06110000540e6850007080010700c0190ba41b1280b13607601c040100101a07250102501c401e80030078240005161144642d1060340d04400702c5440d0000d600b203400c08140460311085d103000304d002e041911000920120103803608000e10a171175800c10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 406162607 1250 406161357 406161373
    0x30f0f07030209090a0b0f010503010c1d1903050708011422121101022a03040b0904020a031803081b040506040b300402030106140d0f020102030d2c0f 66
    0x41016000f181d070024000e0291000602e075940e0303500c0010b4081d00c42c0340040308011b0044c0441e0a09102d00c202030360040c00d0017a1107484404e150800c3c00c11840e01c1a004112428001c044100c0484c183c00c0a1a80311003a940100d0301d0301e034058000c01b54203802104000a08010501840c0b501c0c4414101c4004d010100030300c072134152100031030a80306403010b00810014007a80380c2c44600a2001d05030780c8054460740300d11400c002e07a040800036140380119000741c100300010440d90100d8011555030b1001034401585030480d82a05400600b42198182c032252000d401d01c00802d0740c072071030b01841648000965082454155000c004500a81c09040d4000200b040f06000da042412302602088122044c44d10741056000c120788141036122041c1c4c840c48410300140030440c5001e0040e00d02070710004c048001480b200400290b10300501c0107021303040c5e0101d00501e5065920a1040761070543c0d5601c0140603074005040c1c00003005d09040707121005210790b141084010b40780810055000340d11030300145a40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 406163857 1250 406162607 406162609
    0x80a06052103090d2102061303030b0312040308071505070e040b0f03030c1507020105100306020703091a040e060301090f02011404051509040b0f130b130e010209030f0f070302 77
    0x3416050074034005910081c84050010b9440200e880b9040d40709480500c3d6441085120114003851442482c00395000310040000802202e41040115501446e01140c003000641c046801c21811080a0900040009002c8140408000204500752203000c0302c404018841d00000215502074070003500040002034a03200614054000e21109400144500d000751b9114001904d076900041c80b180298000824030340c404104540b1181d40005203000a000c546030400c1e125201d24480c0c0070081215501007400010f05203c0c881010203054004024009280d110b030302000c0a4000d40f18030144c807400440058140d0906000c0ca003180d980c00441042120306a40c01940e0701100d11080b0003020307100303000c00a05980e40001320a0320301e5101012f01e903901400d200703000681e0000a2014000e20190880014580780c114514080390444580082c5402d54000010550364441c140203440f14200422500318080c194001c0150305c8049080312400d441016010342c8540036101143c0031a00185000c00c09 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 406165107 1250 406163857 406163899
    0xa06420f0e04020408060423060105091303111e1b06040510050d020d0f05010b0c07060f1202040b04050405250e150313030818030405190e07030c080a0605 68
    0x1c10034001c00c0582800d40300d0390a1480d0080032541520310703400750700d1206591401200c0c4103981c1200103002d00042e40c1030a000c54861a4023504040721045a8020501454405c842c65079644442d401a1a18850300e0801c607000c2000c080f040b002c15014010039600713501c0b429803542580300c001a1015080c2450041000712106001c001503051180c2000802c1214402c1c2c030045c82c10840c40000003400c0c3c03650042c2d250449105800c044e0380c45070f0403c1003164900700016076104032841d40c0340101064030503440443d02400110f45180116001041c0401e8141290001e00300b0346100751410801603440001040000c0400e1401d1400d152480c40c4241040d4403aa499215603400030303081c020340d12141803400721154800c4a009d0540c000c1c130070444080652140c865034002030b00500303d0003400840d580b16a107e205e140b14207407040d0080a0461540e020110f42c840c01803505000c00d072054981541c015004d8135802449400145442d000070b000f03c0a40d104440c291762014041200d80d4201e40b03e8425 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 406166357 1250 406165107 406165127
    0x60510051f030e0d030504050c040e060f06030c0d060e01140c041e0b04030803091209010203042102030a0302030a0e01050a090e1b0301080c011b05060c030a06420f 72
    0x4100b64440809041e55942008490941c50043c2e0700000c0394036103414150300f042902c80d0094816401c0c81a0703e040041c00240b0550400d48800c07001c0c0c8149c550300002468903000140b102d810010682c403000c24001d02d6407112810701a654001e000c6001c0419050008240c212a44190351400f40420302a29081c02d89020745052030075207109219848040450468016600880f4240000400c10942074000e2005040554201b02118200084480041d45900503400f90030703880201b8060360f04c09680d0501c2c0240e581b03a009404d84d94860403e0030000d49039030001c1038071404074850702c10156040d440f800440d40b103821181d40b9016120b0402d844050714150142140c3c03040301e415004100486980c6008bd802003001400070071000c4840e10014144c43d144581d92208080c071503c040c0d01060010400c1d541c40101c420382660741e50380c0c20360342200401154118403100744502003481481080e04003900310912401104e0900c440091005400c0940074002d0000050580300040a00c10b0040d00c40003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 406167607 1250 406166357 406166419
    0x7050906060301230406150201140c1902030d020c0601030218040215030a0207050d020d030b060405090103030807140a09052e080907090e0c0f0a0608040206091c0f06051005 76
    0x242d00100c138580064141c0d4000c0d044031b40b01004011a065030541c0911842d554004046690852031030400072200b00e40c00b03140c07986280400c1030000480494402d00c22200a800404404c5407902c441440e07090365502c3c01d0104074026019020a100203071107902c4c850b48142d900a01051305d1907a002c61602ca03d80020344454140c0707801340105000540c0c1032040c4030500140764004e00e62035032102e8005040d9208900c1c141d009050411080c02181c40c0d0050f028156a01400e0811050302c5404084075070351802405030b204100c011941482003640b00c441b0f0012a0340c1150440c3c10b050024400136141d81514608018081e0350020450b080d030701820031182c0c00080d450549409681d100c03441410f444928021021a400a92038203110346007240781c8501c50003003a40c003490541d050560150044001030300c0684a8240030036011095a103202c0310403190354910098034550703c0d062512240200b40800120340d16030500c0c00095000202902d2107003103410041060101c02e40c4940c192031142c4940d6911 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 406168857 1250 406167607 406167659
    0x1416031a0d05060403030b0604050f04020a09050a09020405100807121109100203040f0b0408190204020f0c0d080a0e1203060a03061b02010605030c06030406050a0e06130507050906060301 82
    0x1440a6038880010005080c0190043d120b00c1c03901d898006c085a4459070100c1c0b14250034003043c0304a8545003548443d1140c240c03001603560110003c00d8407200c000b0742c022135020000c00310100b9180516000307042220720a54400c0c513134100300361080d140c143c07080b501e42c000101014a8240740c601283c11580e400320440704807900d0800d40c4400304c2d0101c80c118600001613400001c007048500351401a00c0b0003410082142400c16040500c101d4466107154410100c224601c3d070454155a9139a0440b40e43d00445003841c0d40d605800c030716140d1075030700d4800c0c41c00106a1140024100302040c0c0101d0380700f0000e44c00030388090f500340003d508081e0006010140c000c4005080400040c0081c071400000804900b58080054491072000342902c0c00750704100d01a4010080440c019102e01e0705030794016500030404101980e0f1841c440b0000c2280c4415080c85200340c105100c4403803506254030030030340d0007542541c4036141c895052001e080000d40300d180d040b020410040007240100d02d03102d5402d190909172 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 406170107 1250 406168857 406168901
    0x20d0605103804030f080d0e030a0f18050307090c031103040b01291b01021612170405070b280206180d0e0f0604030203190501141603 59
    0x100c041190b108a881180c81985071245808001428800680c038110380d0000034601030860391008007101c0117090040c41d43c0c0c804215100901140c1e080010341942c44d034100d0781c0310303490681c000b070034a100036440030040341c400d000c131a00b01503030a031408064910140062514520784030030407004017507008441e000c1660301c9881c1030407070740c4100c015070040b030050081c1b500d19418800b0103841c0280c006001e50b04815200c40411a001a4500380d401483c0c040303034201401c4d40d0502c94079000e403280348152080340c500101c5038001c20069000b507044940c080e5480c2c0041c1c0c40a4041c070700f4003060640c0c01401c0307603001400410950320340900400d40d080001141005880c180b20014a40384143c800d0320b405a084076040000401d1038809000223407003140c00410340202020006410684034050850203031040c03a505403402d881f60002c0314000d550190440c0c0c4180040c480d000c003803404039a01180c580d4240340007801c8805000640c40d0144010402000f9182e291000540090142c0c0303440007100d00b041c01c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 406171357 1250 406170107 406170119
    0xf0803071821151103130c05090708010303231201090c020f030f070602090603131a040209060111120a11010e0303010e01231c0c0510020c061c05240409020d060510 72
    0x1840c0500c40303401c095101c1b00c2c07240ca0b000c817031214603810160007002e81004100046600000c128112500740c00c05139581d03050b511a141105102d1180c0a09000c1e0008490114041c0b10320b105040781c41090041000b2140020300702c0e10303540c3e00e030f50303c00959000b4499220350445a00051580d0b6204480c01441c103c000004202179400c200e40d023038000044000c900051040200e00c00f02070070702c0424401424505540002c6080710041c0055040016040182c0c2c1c105101304805c01c0b601132200c4205890303000000c1700810114200d940e6044950074060b80f09182d140000540c2e06075011104510142d0703081a403480300007111605c0a22071140d034142e80c0c030403a4031614401d440c0032210440d0410040c405040100d145000c540c0000d004400803d14003804e581c0c007140155500c0402c030341881d40c9a05c038034281c6401b80170303500d0400001480c060501107482d03052128401941c1c01804070f00010545001000115440d156029420111900407600098035662207a03034046004c04010509944403c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 406172607 1250 406171357 406171391
    0x1a041a04080109030804030f1404090f0b060408160e15120309040501030605060f0d0201140d0f050705190509060a030c0314040804080c040207020d0204090f080307182115 75
    0x4030f001e0303000c20f02e0f0340f0074002815031155404005c04071904040324224088400601184243e200d2096416916070440c08141120b400032000003800510700c68442e03031500c6046132207c2c441c5505801452014000145850400321518401c0c020a00198002c0750300c0400c0c440304c5011140d071a6604e001c1007000c440c0a50340c5101c2c4030b02039409a000010145441d105014404070250f00e100e20a102c0482d030000180e0303020603505149404501055105c1031102d02d00300140c002c0700e65051840741000308121176507074014050300e04904c01895000501c1c85040e400c2c0ca951080c400c0c0e09401a2040103864180c5000f50821031000c0d283d8580000d0002101400710b40d0309038282c0c0c0495042200042c2080f20260030001ba001c8100e0071501103292411a90005000000403c0000e001f07648a0b1000700a00440400704281141c00500241c0d071fa180498000b04588000b0141c60400c0400e4980411081c81038001483e4840302c00e91185200b40d1191035610200c001c820503c1070141c4c455034513908645000f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 406173857 1250 406172607 406172621
    0x8090d0206120c0318030c060705090406030807080901031b14090d06051302030f01060f090e010b0d0b09061608040f0c0906030602040e0c03100b0c0705091501091a041a040801 77
    0x1c0e4049035264140810b002103c1641d0f45617902e0154002d0001442078080400e01e150003070100e01f45a566092280d0204d809808a40e0021707120302000b00d14031062210f144018088400241d800b0828003000406c105901d03454101c030840001c1c0308003d5040741d2007000c0020212040000c081154085007076580d00c003a0380c0f003240d01c03080c00358100f0003007011800d080103514803002001e4001e00c42c0c0c40c28005038030840104c5107c5c500603503031214180c4810340020341c0080303444003024007103010b640118103028407198400d0b00c04080f148241c1e000501c83e00404030a0341c083c55000d135a00700e001d40721612801f805480b00c44080e1000200d050001034480020310401004503c544009a00da601c1d080342046454801420704036003201c204100078201120340320443c02d4811901529485000418000d827501004da00015000142c4206202800070350180e824511142669071051040c0c481c058120300441000d94a420701000344006d0003180c0e00c807402c0d14240003000039228149981c451800c1c0c250f07144 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 406175107 1250 406173857 406173871
    0x507030219030f140c100b040e06090d110d140c16170708030a09051509040204060302070501052a0a020c090112050f0a02010504051e0a09020a0f0c08090d020612 71
    0x200d0780000f44503500840340054444000040324284081c1c040c00d59100c5030b038544041d03031383c6568080280d01d55440e42d010440b9007004408540301c601e4051041c9030b84040b14002d00700070540401c40f48100100004070f0504020095980c0325862501d0410003e49410403071208485004003446502c002e141d14036403100034030700f0743c04141c0030281b00c640c3c1a060011075007100d90640c000b00001280a13811455807402c80744140d8030741d0200003820100d50401d004000140da40a40005030000d009681500601401e90150700200201d884602d841aa118400451003481214082155030380d080d045010700f4020300035006490450021100084d8150305c2600410380d00c0d00d041c1101d2041c031004021061403540c6190040c401122035800191481c0a98411688102c528060b0103503d41202d142c0c84480f12400b0f058418101c0e155217898000e50840d408207000582241016900c0038807540e0009104c81e0406405440c01c075100042c0302c1c1c100499a010798210074100100548550008025846600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 406176357 1250 406175107 406175117
    0x20f130e060403081e040515130b090d030c030b0102060c161e050610030b131401050a0b01080702011a04151a07210f08190f1b090308030106050703021903 68
    0x1400c54003180072003103074005507556200170f03404100010b540091408a882e01c00995081d01e5a10300300b1018100a42e030f40010072180d891814004001c0d0009141000c0e2051510b00b8421400c0104086049808c0280140e00580c0030601081072070500c003000f0b0001c0d214141503010800142c0e02d600d07104402004015003403180c4042428140241849855009105814004209482d540b980b0140880203440f0a0142c0c21002c44030b010003242d07010316400000c015009000714605006100c0080c0008180c00340840c25031030018034040c0c410720403044030401d003c83c86502c0742410400d000c0180f90360864404007130518907000c10280c0c501c0c1207500070080030b0070103103079168124076016034901c1121007410509007a0792a60820240c115480c102d8803032203443d1858880ea900e000d0440401c05004900c590b8901c3c0055921035455a03400900c1d1101c0040c0e181401e03440e140c0405c80f580c030041c2c400501032170300900061080a00c240001e1542a000748104e60001c0230795010380003170300761007403044022807 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 406177607 1250 406176357 406176361
    0x1c0608030708120f0106050d1116150e010b031015031b17030403030e0402090420040303170610051809010e010503060f0702060a0c020304231309020f130e06040308 72
    0x200c01c10340f403035000150501407900b6500d4008090828007070680b002c0707001621440c02041c582e01010940d1050080d14503103a600c80b155040601d02203d44441a13048681000000041c07250140551118620080c00600f81708840c030070305000a20058140380500504e004e800000f18000f845c2e01c080c0184030f512080c1c42c03d40350110b0350b402c480d80b01140d000c1700c1d0002e02040000c03e41005107800e204005443c05030741d070929030000078000e0080c0f80c0102d420710510006060003495034070140007501d00c0303600c400b40082c103903104001141c3da040340c60b44c2d88820050100040180301d800609504901d001011006003800741c0001e500c2d02090b0800000ca00307242004000502c1e0400c41942c01c00e4006844000d03c0c00c050000940301c140040c600d81d5041d0319203081c181503501c01c00442e0014080301604042e84003a18036207544504514011500c00c06d450668590301c5080c52054150640d4000c10f2055902c0000e010b200b0307440682100312491558452101140000500c6501d220358800c0d0395585480c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 406178857 1250 406177607 406177627
    0x621050703150905010e060603090c0d050c01030e010608120a1b0f020406050f0a05060927071e230c010903081f050d0b130206040e010501021c051c0608030708 70
    0x29410700c3d480f4482c40b13824900100040003500d0034241d005403050b1400b6a40740d5801842510300b6035035540d050f80044012040b8030502c2004508078610356400d0383c0c140000c84120a1036401d98045001f650615040b1a00e510100c0004070000d00108205080450312003441060591005c0c10700300d01a1607003080100b41c0380840c40d10b4803032500500300403601c1d07840106510010031641c0030703207000302402110006581d981c29944c41c0100c402c26000304000c2410818050b00c00c4c4407400c030076184000071910707000c2d841d40720a0710172441d403003044510b949a400030000c6c0d03221110001c040e1341407004101820881140545003e000b942c003210f029445000050514442c106506d550055406032004246071060089581d2242c0c5030580540101105189e0345a60100326054151070800030b600c82800140011050000f40880d07040326002d0302505c0107410143c801520900e00c00c01901c00040c03040001d40c03941c02070000c0d8000f00307006180c40012150385542c0d0492640d80401000d6443c010045903d00781 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 406180107 1250 406178857 406178891
    0x6010201050703020a0806011d040c05070501060e01050904290702010c02070b090f0405360d0507030c0221031305040501210f082a01240621050703 65
    0x4082d80e440c2c114540400d00000406d43c0d40090b003280c2c100408880f8000501d0103244a402884030010b0040252440c0710300050706540c0036000c1121a5400c0000000c1c1400107441e801d412510080c08003d415502c0c0da03220620b00c480c0034009590020055003540d0714444484002d0b114400c16000082e140b040100040c0c07805035641c3c0301c0000c0b00d0081000d5802a140c02d08001c2c48400f042d80d012515032148100c454410f030a480c00c04408809105008030304905100441080c1c0e449031060b034461682c8094101d810348904000680454075027040e0344010305128403094180903060445e8110a04c00c08941e0341164481c1e00c1080d40e4540d40c0409104602e01031141c5401030070290300303013100545000707201d00003501215800380200101c0380406042c810702c81c0c21038207548440209210048090b00031101380104801c00d4102c150b19041d4090402c084d41500441d40401d030a502c150000c0c03800c00308407101c0c007240205450781052081049582d500c28040c02d03014181c00d86011030072010000341582 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 406181357 1250 406180107 406180111
    0x1103070e0a0b19030e0f011407030c0c0b040323031803030412030b0303160b0f060d0b0a2414090906041e0f2a0b040308221a030601020105 61
    0x485880a0002040651591000c450444900806052108220803025030040c21300800c17030306990107405915044140d040d0311101e4140c3d10311140b0b04c2e4684580301c040307003201c00c44501c0314003048448002002044040c48920380c4140300786880c0c20707a89440c0940b4060640c5020600d16040c00200c1840000c4039441809403c0e402000011811464140c650400303071121300b11042e00b8181e17104800e41050f1010300840b124500c15890000b40d0122501d000d00a100c411140401c180400c44081416031528019a2859680000011039641c90b030141c2c040041c40c03606a003c0071403145101c001c450310200010200101010255031601d00d2401060104840c0c004061260541140081000080b613110070036000443e8031075410810511450301e040794014001010f01802e0f6010741e9100c0d100a20b1181040101140740340300c2c640d1b60390b500020928051030100900d0030303505100389020041d50301c440c40030110348000c0e0008400d07910511200e10309010080310380300d2900001080341c95602409095 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 406182607 1250 406181357 406181359
    0x61c050106030c021c030912080406060b04120b0702010b1c170f0313030c0b01080d030b01050f27100c1406010f06300f180209010b0d0f1103070e 64
    0x4080268203c0c0001e49500308400e241c3e021000d02031480c07074654445d600c400c40482e4009042000c0e0942d0340e00240c100318045804071192800c0040106209000a00381d03012240c1903030403411181c01070f1f6a11724914030300518110441d984c848922a6507500d82d40a81c01040c000e84003c20068a075003445110030062070551001c500040103011140c14540c07007200d034405d000081d159011440e030f04d42100c0001c9041c8000d4003540242d400450040008502c00c0e10644e1035441c1000002c0d00d8200640741401680c0507510f840c1000d002d15051000c015030503c1500716017191030315000e5046c0c1c0020740720010030f0501d800081c100350700081c00c110844103146103801400740184101e40c0341c2a207000d011001802a041000900305244442080340918a109100c20200d54200b400800d0b240710018444030107140055424034886059070100d07400f040c0301c1160040c01400260307003040000d1030700764080140c0500755a555810514048010302ca0451110901984642e07a17080c412070051010314175000076 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 406183857 1250 406182607 406182611
    0x1810030e010b04020304111201020409090b24060423060c15011403032502040507081e09030f03090304150e040506031504020f010e180708010e15011805061c05010603 73
    0x3000c08980f4400040e0387e00f40e03080700c00326001e0082529035406130141d6400048258245132088007004034900300d41d03114040108102070391004098404956680001d01c80e0781021003004148440f1501c80000400784050003058003842d5242c4000c03445540c0060100c002e16001481d41146c132580340b0740064010200c0134891a400f007803120000362644200080c030110700c1c0c02640700703c41d81c2c40015203071620b140e0003c004200a28015801501c091001c40307071104d0410264803010940840e0003c06800b6844a078011401c060311034420420b01c2e80080e100c03200034401480005200300320740d01c685080e03d886a80c4c880598958000303003c1035480c09400c0c20702c00c2d0000078085038076903d030700c0480354442d8040703070b207051a004424016030781303207402c442d40c2030b00104140c041c2c2c03011010042c3e402e4050080b0355500e0906a13611080000240000d071034680c646215a490800250f20980148042032042c0c01909901ca0b625400a01ca0782e21242400b80203020f10305c01800440528494035006220301c0c102 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 406185107 1250 406183857 406183861
    0x4080d08070c150b03251202030a020a08010c09050409260c0a0303050f07080601080c091f110d0e061b030403050601270b0f04021810030e010b040203 66
    0x10261900418412441003044400c009100140300e20809900700380c000907030708610040c81c98204007a08000d28031034001c1c0708034058541c40440c25440500e5a4280c0c007141c3c05480c1c1007078200c8a9003a003400f03060340c2c184144a42d40c03000d80c0d12158804001c00001e400050940b191000180002d0b10661010744110316001c2d82c0030110b43d1070b00712b6011100e01c50460003040760f000c9050101c9802001c8140e141ca1040c0f42d8100101038040d44290700421400030031a100b5038407404112a8110201c403801e0004100c003001c04c0908224202401c811000201601041e000c0b545a503101040840e6244000880f6003000368101c200501c030700340f09903203075251503006040c0b6480821440d110310f010801d00c11803d109100c0e10300700284140d601841d4840b058a485582d00e20307445200e10492181d0030445001800c030707690b480c5064860b0f18503041020700320300b8500c0341c070804100003908498100810b00b000611f003003200f940d40c03010190700c004a41d10b0002e003102100342050308444010b884c00b40505d2040003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 406186357 1250 406185107 406185119
    0x60a050604150306090f0614090121030309061814060c040b0a0c0b04030201060f150801060e120d090f09050f0402060f07050703110f011b0803060a0b070507170304 72
    0x889090b40d6454030914100d0014030b10480007011507034403241d042403400c84200011070468000104990400e0110001c80030441c0410018081c02c0c440c4040c1507a413081100d1326a401840f100340018000c1c100011003003074030b0300d509050380d001e0301c03622841c08540c0d000351040010640c00744c00c0c2001e200d0024800743c40c10481149486c030441c0034035022420f02190341f81919100c1c06000980d40d45c0030415803003500f45450080d0290040c1e0180c1c1c01c41d082c4220300800e081800c0f00c139489503010144e48034456a4a0f101080d01c82d80d899071149900045100c281c01050301c0e0402804d030a9842e20f580e002c034545e1800c0b0030000004590303084490300340e0404050104286040000036002030301190050ba03901c0145000400d135125a80e4020311501560000000780a12808200c4150380c0a9421512411a101c01101e60380740748240100d0044003090329102240511016551181012f0f14a4540b0750700c2d00103045007074001030300c1128079910441c000c3c4070741400821140b00c000701c404010350520341408 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 406187607 1250 406186357 406186369
    0x31b1f0b01080f091f0b03060c0c150613090506010e0901090b06062101120309050a0305100506190b09040c0206011a030702030f0406020313050303040b18060717040e060a05 76
    0x30b08803008410041d0702191645000b40110001086052407176100e500785400c2c060013405002600a01c02c0c01584005020007281301c084840074280040a0007140710011810010a40040c0c50160032a8080c0d60f07a02d0181c2035481003185082c0204010b04240d0b00d04200e00c05e03040760051036150140d0500b03010754000746120340119000002255115218042d030b049078070250141c00302561a015440c1d000143c14008070f070008400074041e030354600362640c541c414000e1000881c8801051036001c88103080d0398118a600664000100828451400700900d80c41c800310507060708070b400e20700c10020b00c441700c91400b485034244141090020380b0f02d0b585801b8400b000d416101c028a18807043c00000504541c0c400e00840b05803803080070445444030f441d218002d60b690042120400620b40c481d030080f4680c030703000054804646507240d0181c40c03c40322045c030042c140d80342d0101c150000c0040c04904000f468902e458284401c4850380c00c0c4c0c0b51803414002e0300300c0740b42c0941018042d0481c00300030f1103681c90b06 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 406188857 1250 406187607 406187611
    0x1107060305041b150206060d110f040e2a0f010e060a052a06070306180b0f04090b1b1207260702030a0e01090b0912031b1f0b0108 57
    0x5400c0005a80e5500e050034540e0341d0600340801c2c01c0300c1030414041201042ca103080305078500244d007114060794422040c85441100d2079000391040981003035048203031510000c440f104540281001c90344140064806142014201190031050014492100050440341400c4000301003101c108803041c19070800604071140b0b0b6083d0a00400d0009409c248890040040340c645a0b864142c05a007401d40008402490120000d45030881c0142404651140e01c02e002e0342081c2d4400d2260144541d40441c1400c0040c400020525004440c02c0070382020303130343c551094406c070705d00411980c01286011440607655802040c01d001c0494802e1025401c802840094903500c80c034981840314840d25110200140303e0b0070440c030040c40f00120f004004100c0d9011000d8402282c150700c82200704090080103686a4080c1e0040c8261703000144241041441d020000785188500442030301d1070811100f000c0c0001d51601d02030312009900200c8000040c0000c210000044c103400324003000a60711100c0024441100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 406190107 1250 406188857 406188869
    0x1006050d06050417030903040312020303070e010f0c06020c0d0f08160c0204060b0a02011a04090512030a060f0602070806010902041d040309170601140607031e030204210b06011107 79
    0x60342d0b000404000c01d21602c92011008244a15205c1c0341c03500c501c0f5a69442800126086074443d200102c8c05400003050f0b0b402030f03107243c86407400000414011142c114032100b0100401a079020041d02081e5107100a0910003181d4026010b41100818058055019107c51008004049003009005104480c04143d005101c0c540166507024500000d400340500340c0200101c4000065610701d1150154403020640d22200714802e1101c00c01c0d4104403c440501001400f190003801c08480329081110041d984600401000134005403207000c0711030100e07480e0300420003580c80b50b4001d1000060030881c203801000840c4040d0700d1b00f03044c0303102d90003540c0000b80c0540c00f2403510b02c0842c0c209405100d414000d4103060410012030a040d41980d40d80300b100313110301e00500e1000b440924650506504640c04070f90180c80b10504c040348001d122005001c00d1881c081055401c0c00042900e0011454000000b6070060612007441841d042c00b42c100b01014000d141802420346810b110500c01280e180c089503c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 406191357 1250 406190107 406190111
    0x150c090a031b152a1712010e09030703050c1e03120a06050f0120012301091812030b090106030e150417180402120417090a170a06060602060601021006050d06 69
    0x3628102602c0081005a80240300b802c00c501c0c41c1c4c00c215105ca02502030394803d0f00e02c800c881d9a0329903040c8400310043d210003005030001c0007035601003800307803004024440000089404000c59141c0404c44500c40645421098000040310002d0f08100d110307250300100c44600401c0060318050001d00e0782800080c85e94180030340c8242c00500d0b01d042c1901d8142004000c0002c0c071a03882c05c1c6040c031120b00003c3c544a10040c50200c0042441d80032840703040410302406203103200d444500d0312040107404560a11404040c0c131051130000d5921011692402014142c40c04039840c091007003401d00301800b207040002201804410080030402c40c4401c0d8005219141000da03560001c108082c25038500c034400c80d90418000a102c0c410703054800f06a03403041d805043c1c4607854481d8244038410034480c001405d644621035010a1040400c01d4480c02c000c21428012103000c000f1555402041c1d44003036100700c026812600402c2503a50b010701c15183c100b03401d810b0400401d42420700050110840310300240c046a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 406192607 1250 406191357 406191407
    0x109060c14010501090b0109120f170408010911090f06010806090703020c1603020a05060a08011404020c010c0201050708070c200109030f05010207110d05150c090a031b15 75
    0x10400740d0644240340c4015000b03100f50b42c0c566586202921902801c1030005d00400340010700208464070075411703580d002031390f94018004d944a0002e441561340c40c3c2803240c1410007001540c4002440707080f800a20031f180180300414840d0400800040c0140601c100c074040344204042aa030082c0302c1d50f03201204a900240c0350b2181201100280140c81105006204080301680b00840040340c04040383c0c42107900280080d25881445a01c3c05696181c002007080100140714000e0307070501d80382c1c003c007025000506080c88046094203503070021082e0005031750364106026203a176100d10119407005650034818094001641d401c10020000102008050182c80a011180c0e105041c4139004640103150031212210a0a025000b94800c21040710380748150500443c90781044c41c0389091540e0482e0140100e0103020720f4001a105c40244020003440c420818404255201c41780764014601950481089110032030500c0c5c41624a5008051540c070039040d0a020243d02042403c810200c40310342403030031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 406193857 1250 406192607 406192613
    0x60c3016111503010f0906051f021009060f060509060f01050c07150504080f070501050d05090109081308060c09091b070803241002070b07020126040212010203060109060c 75
    0x24041d0640ea056002c40c2045292016200200c082c6042c0e40444000c16112035031208081d003241c1c1c15101f080c0d04440d00800c045d040b4210315410304010b001500556040080f0018008201d683e00714003165403554446800224003118403039400602801d440e404140e0030040005041c05001800c00e070704101001a1a1001501c107110b41c50081034050203400d041b5041800180070707504907008401062160030102c195114002036080c003214010b85a05141c5400d02620101400300100301c16110740d04c80b040e07080020301200080070890010641348440c42e080440190401c0000b902d170750800d030814051000980d4503502c0d1a5080801c0315107854410200c8091000c041c042c40c40c1c00b400201000c010020680c040b80c3c040a0361042d107010074580e000c09441000442c3c07a03002c0c42080140e00801050141c000d072030000741600c500505003803e0100003d840e11342d080346c4044100710210b040d602844110300f8000510700c02651500029415442c207140007c090b42c210344503503c100501c03c606a001c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 406195107 1250 406193857 406193873
    0xc0705010b06030403021e161a12070906020d080c030a05060a09050403081006080405060f1906090e120301140609011106251d0409060b060c3016 64
    0x514500500b00c2c075242c1c6001c2c24040e4480f000301d0a0f08203600341071801000181c0b00411401c090300440c0700c0c50702c0d080c0c1c144207071169041050807801c11016402c02900f02c5000387c61900c14429185036442900003400c00a000f0309150010300020140900c8600344440e803840e06080d2a806001d151001600d03584100000b54103171501c3e4445020306150506000600d0340c481c034182d200d058130002c081107065075210100ca2612088902500d1500f0810106241c1d00c7c00240d40c54211003000001503200c600090581c00f260401c1e0302c03220750306075580411348004009001d040f0700342008010306801e561601d04c540208600305c1400e144200c100180d4015035030f01601c00d200c0e0a4856008441c054580800808809200d2080a60b00422070040160003244540070300360a9600c00234510140b41040814007000c0e19100f1022202640c4603822040980c941d01c1c080c101903001c500c018214160110401251419801281c00911941d192840d516900b480c0442d00078483c005e0480d00782c50505c0c28000c030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 406196357 1250 406195107 406195121
    0x10b07030c0803041104060b0c0319210e0d050405100302030915041217070c060e0309030307051e01020708030c071403130303030b04060e060d050f01060f03150c080c070501 76
    0x202c001400300900c001d04c043c02d61015030704082074404008851700c0301800020b41c0244d1103056583e600401081d032000c061507050400420031400c080301c07900c8500240c092003001d060300d000402980d5007444c11400104000e41e020000c5c403424154540780c24100402c0c248000340700980207247d000008606028800c0080c0a07186030020f00e0b54110b4202454203151501310010040001410515541286401c8869550141c2507607200d0803070501c01542c07010040c0c003030a0040c1a86000174003103a08240c40c00c1c0001d01400b4854070252603900101c4004417084d110103803078203615a205000c404006201001181c1d0031450660280e17440e00c01924004d08144423101c4c4581840c000440d0b41c3d404100421400c00690b44641c07000e21658011b07000f4001158032a01c60145030000c0200414841d051481c06552400d0040d402e6407091510b44881c6030a658240e40401100140c0320404c2040c000001d50090144500080521100d802484020b0400300003414540040c8000074418040001c00d5000300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 406197607 1250 406196357 406196363
    0x70e060d0b040309080d0905030c101b08070803070f020d111018020307030510060608090d0c0206070c060816111005090c0d0803010504060b070b01140105040e102606010b07030c 78
    0x503008151031ba401086154548034190091113880c3d80210940303082840f004040e0030aa40f206651040e00e8800c0e200525401c00988080c4130030040000405e6140004520405682e04c82c00e5240c0c1e0342c1d01d0b0080c6800c0080140c00204103069200100d60300c400701d503090b14002c041e0380c0403514028494100c0d599032003401f0000c1d0725100300130002040180c04a04180307600d07a0650108050341d41c8440603074040b0811940c42a032030b0000341011400702c1c000d1110800b401d0000d0009800c008203540c800c20b4041e029008000814200ba0421600c0305003514414181941803800220480710942c4050380c0b4240d6010b860390f43c1c0d0701d810008800740e504005142e81080d004001c4004260701d4141038800390300c28080c82c0d015178141400404e15198070b1b03049800c3c0c150b1141c04922107a180601c00040341110a15a90400c1405c200005213070301d4680c001d0b80200ea01e181c1c0010030520346a0070005070841c1c80d020403040070440040b80034482010030014111910311480d42e81d00c1107030307190071104011860401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 406198857 1250 406197607 406197613
    0x8120a0e0907120b01022428090b010501141b19031805040603031e0e090702010b0414060d03210c110111091c020409150905070e060d0b04030908 64
    0x740c2c03940e0260144000c0c0807980380070000785401c0342c01243c50b520f40d440340e0101d040443d00c2c0b01240e482440011a4440c030084030310311351541421003408500d4507d10903440d03041d4840114100780310702210344034010003003400c4c4010001841d00901c60a402030341840c0c5800c08403103501c59071600c001d01400e1014410745500c100c042c0303410b2034041d1240505d00d80030050b200c001c1c070010800c0e04042c80f4076000c1da07802d03848107000d040140c2407440741c0141415440c2e0421070015001c2605840d00c01199025050a80021403000b12a100384000c40b80340408181c2078000e00c400340b20490b140c01c007003000030581502d880b04080c0c002008001c44840c0c4004015461880d10600d840b001c0c1e402524251510b15800007444032411900740c11308c042c01010f07070341944041c3c41040c021300943c0546100c0b0500b0b20151001c680443c140e1036800420840382c40319108d068031b500d05001040f006200c104007509201080c0c559a080000100b0701850607403800800c00080000031034245401b40d0703144d600030001e030021 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 406200107 1250 406198857 406198861
    0x2091005060c01060e0912031b070f14011a0f0409030302120114090109020a0e0f03100615030b0a030f060c270f0b03130204020a030b18011d0108120a0e09 68
    0x80f802403c180c440c5400c5003a1680100300118800b1031190b0380414024182811500c0c0c140c181c0d42e44da06203035981d000d100f900700070303440010348000c0d162401e550049580f10403603003038100400c0c02d4070320903804900d5103003141c0003003042a5500c401d4045e8041050b10001041c02d40c9181c254002d229010503008100c03000000007401100d4408078842d41e640a44044401ea66612a09401d034010030450300b01007183d0b43c81282440c1041c204038004407a008085601c841034008060f001c40c1c1e0b994004106e180c81d03a03101c00704665054042c0c44600f0009580c1a01300a2640d2101c003454554100700402040c1c980080402d9184914100400c5c2106485401c040c4c83d202143c414001100b0300c10700320f8880e040800024611402c07401e4a1160305039801c0b09040640c1903080100a6008806000500d0b80e01d414100903500d035000303000542500c0002003000c550400c000018170700d821100140440c040c000040c0117200c1c0c0800c82079968907074401c00d80d8a40d0300c0c2484c15501c510114008507008112503003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 406201357 1250 406200107 406200127
    0x50d0809011d030a110a0c090b0a051008010f05010e0906041d070f03110612070f02031308101d030703030f020d020a02030703110d1715030a08040303020f0601030c030209100506 78
    0x30041021510391744520341c80c410f41c2e064041c3ca401500401070551400c11307204005c04078054000041d0000020505d92020381c40d0310004203414550700c05403001480001c0107012074100e42c064a1f020700400d0030001a0455600d001030101c00d00180386a018940311003141c02e82c801080c1d01e001400000400307540380f042d25108200411143d43c8825174001440704000141401d000003100c6140d0050925481c80e070340c40000c1650716003015000f03841140700400400f0031100d02500403c01a241030f001400c3c81c0d901d0700d4001d100391103c00e00080040b070649028448602d00020485081503894180443c004104401d031700028041c18004044a600015184540c4c0d6400300c02000020700c0380d118215880910900941e840c1c41c40d0a800e004143c5038026880702c84201e42034150700440c200e520010189541c0007203420409200400c40c1c001101040c144105501031112184c02c4410400801c110340c0f65440f07001c1c2e6501d0a200184c0035030221004a642c2c501d0238141e03400034002c0900002c2da00d0751019 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 406202607 1250 406201357 406201363
    0x160609030c0303180f02280602070806090d0906140f07060605120c06090103180c080304031a06030c011409030a1b0609180e0f1501090f09050d0809011d 67
    0xa0000c40010340383c29102c4c00e1400000d00544500c58200d03d200040400c2c42d424441041c1101c02150140960284200c581303650140030a006005968003a2903143d1412035034070720340b05000e071001c401600010300d480346880e844143d030b804443c01d0385460032664a501c03004402510031107030701c900c2c50380c000103a001c18440c564001c5030403034405032606003004006240303c0c0c0e292024000400d0f0300c400d0411550b081581300340c00c4000049000034031000142c3e03182d504d8020001e84d90f0320845540d040480c0c2081032203503020101c0303030b2990048120005403401d50300213078031b2307100c1074105605104070106103400b95044030098601c1c8d03c201508603011258613042032100141b01d8044003180350000a4045049403240c900d5200700c441b07c0076030342c6581c441c441d41c080260002100411407031146241034452003000700000e60356501d601c418086154141a40c01c0c0580d4403444481442600340880c900c0080e0b00010b1140c42c1c20150718040c1107540b5100d20003030240c01546803800340c0318440300348a0071610000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 406203857 1250 406202607 406202627
    0xa1e110a09080307150c051201121b1505030a091203060f0504020c0303061c15140a060605070b180f010b0f0a0302090406020c0307060c030b040509190816060903 71
    0x1c0d281d60400765035503410b20740c2e20310400794000c16080c2c0c40c00301444804415088080382941504200f800d22040d15012006000240c0c0720140300c462030360f410014007002e5110714802084160165485505244042d6a00c0b11a92001c0c070420078004009802005180d000c5501298001a02000a240d41a0090141200b4002c5081d1500300039070014203803a0500c211356119800c000914159900c020401082004400e200c00103619890310702800213044000440b55030781c070500005690002c912082400318002000042c0d61441c0070000d204080d00704080d110346681c4100a080030b580c4054007440500000004072290f40300b01e030400b12002006400030710b490141500d440c2540d802030b100b004100c003111700c400707508800544040f030081549a0000d003055205607044074130744004c03990b50208903510441840f000980c0c603520240a45028040e0715003101c049002048039600c00b1212844100020200900c503140000e1014055070a407441c0750f1290b60410f0040041c0a024140500001c00b1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 406205107 1250 406203857 406203877
    0xc1203180305060f0108030c0d050304050708060705070b0a02030f221403040512030a0e0d0309050a060c020306090615042d090c0e040302100e03070c0906090c050708030a1e11 77
    0x90130b0004941c4510010a5611481402e0018401c180d100c040507900c90348003420a0301c84e40141c1d040030480e400e00300500f0380103102a0f502d062380d0789001e003080007444c0c1019042d0300c06c142c010410700c150b03000d05583d840e8020301031021448181c0d031540d070300c440317038002514004012541c90480c1c2201200c000c07024008031a002e6401c0580180e090640b00c4d107922689516602043c030038902c0410906205600d03407500361107828020344080d183c030001030003445141d002d03a000944080c40d000441c10b040c801c158110030300382c000302050304258101c0031800700404d442a000d155607000c040403203e20340c200d8000400c100200e010317441d0414030544018102140c030a46d4800d4820340f0014400590f014024070464165000e01041140d03140484041c1c01b4002c81c40c1c2d4a4030080c4a6000400c18800f0194000c4c4a6450001282e51a14001c01d003950148802d2034240807041c003510300490240310031264040c2038880000b4035840a10541080c1c410740c503072214070242c50500c0c81ca0201c49910000d0110040d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 406206357 1250 406205107 406205131
    0x5010509060a0e06130311120d20160314070618061b05030c0f09100c03090807050108160903120903051902100e1f09050415030c120318030506 63
    0xd000c1a02951350000340c9500f849074004449036004070b40b0480000100d0003801d020744004041d0013886452540100740c4081039a82c0d40c0c40d0b9901e9000c0303080070002888a00c0c030141400c1010481d02c1d04290180c25501030300748810040401c418101540882c1c0040307034005d04c200504000682400035507241103000f00c483d41d10b802c0314820414420711064112095544e680c1e4590b5985240b50109074014400031840e4034070a0000881a076a02d0b1210081c0781c2d920f54491405180710708005102c4000c075423002c07001c0d030056201441580d07846450690700400f003454402e4130110200c0b00301c484201590018007514554002c01c805258060801001c690003401112580c201040310f400c0170020019000b90b215418601c0024502d005a20040d0000f000070054000012049200101e41c841440c40c030740010106041440203207010f2045600d503448000c6088034581c00d5550745450b10156006e0001c01c0c00c50301241d101014031544048521800c1d805003182040d9684c600070f0b644000642d220032005e1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 406207607 1250 406206357 406206371
    0x18090c050d0804060e0f09040f06050106050322020f060f071103010513060c090302060a0c0302150405210d02130801140c09010e01050409090302030406020f0703030e060a050705010509060a 83
    0x32500948001c0103a8201d20164900b41c40c042c81682c0c5101141007042e0006614038620106a4540000301d1095014000401e685941c921341b28040721016049042444010300c24482c206111060082402d9101c0782403c0c1c1d41440344c00050420f0703862451542c0c0c0030f9800108829000d1281000e820580e105102c03400042d98208101400e03550f046842d846403946041c800c8000c103141e5044560a10f0320b03400c4c550000c42e100d4010031150384c029004000800d458500c2d80c002c05904015100711140309484142d0350b03040ca582c0d80d54031148c5001210300e13242c03001e60110b000c0b01030580888446411110381103548a50b030031060146003089100788e2030705500e030002415840600b564450311408110304080c8c40c040c0c0a1005454840c3d001e86c0844c100401844080341009161203003954182c0203400840d00c2e6894600001d1602110b6040084140c100000400c0001d402202100070003600f100c4441e00c07443d086030201c3d036900030814007515560805061041c2220045038036170040c1107151051181d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 406208857 1250 406207607 406207609
    0x606180b0301080d05070f0c090e0708060c0403081e03010303030c140307091e050301020706330932040506070923041404051b0411030a09080418090c05 67
    0x380c0400d12412005810844014001d1841030b001015014411251040301c0151600c4c0c2c41403105a581125284a681d1800d180c80c421003000030b030004006071001000035281c0915100054092840010f020140c08150a06081d592610b5a0044070317600c000c1a49035a0f4a04004015008500c126008184140d07201c41d5108003000480388554116124642103500c5c200012a24114080100f411345500c0350000c0b030300769820300090100d9406150082150100c5011800700031800d582881c0309182040c3c81d07911108443d01d4480221502010000f40d202034040c0c3d024114a09240342c49140e0041003a200f110340c1810b0318540c0654000d004071515a580c0c001c06440c507044501561500c0002102103891601c0c0b291090b242c082c90142010400804010a80c0d110383d80943d802c40705500001220070720b103e503030440000d401d9012502844a03143c641c1e0544840c0c48050000300c40c00747c590302503a0074402c80d0012180180000e011001e558000c4200b0070009002510003124003840c003040c00655 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 406210107 1250 406208857 406208879
    0x108070807020d0c0201030b06160501140103021e010c020616050d0212041403070306050f0f0609040b13050a0c0f0e01090b0102060f07030e010606110c0103090c050f01030f060618 79
    0x116000716002411a840b400406660141c01410101c1c1055110342800c6515141e40e00138040074802860000700c01d1825180590a4800d20407408040400400040015aa40582c04159100705600010303c100b41400101c81c641c00c9040040d420034800100000014442a50f404000e8085c20941310103062540003262680e0034800050300d00c42c0140428040c0c040516090f0120860080c1151201a503955420041c4c3d5821240d8160111603902008805508092190307480001165011003914040c3ea9441708514050301c03005207259602c005404200040180000954000c483c040c00707282e40b110035401d0b507641c070300841c009082d413103000040340f2644d401040f0b81120141c014081b2640e0b00d0082074642080140b010301019124200090449000c0c450b502c00b41945a4984809504a2410514013841150080c1c100b5140c480c4071000b240d41e803009041612411101c0035030000a41d001240a05105400b14006618280e03001800c02e0300500041d41e10280d54a20140c07803039440c104010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 406211357 1250 406210107 406210111
    0x10801030c050111030c0708031b0102030c030123190f1205030403141c0906080105010806093d1703130b0f0c010216020405100602030d05100e070e01080708 69
    0x1003007002408061001c0c0d800b5004160b400c030800c0048a050051301030340d03a4500b54041d030007022a50400642c0502400c0342c440c41040d08001c81e0020b515604003081c1410662005100740c5101c09800780306412040c443d2a02c0a0321810018038102d1862480c0c0c801030f00001c002d114410070700c050400c0014001e0b8043d000110401d4102000d141441c0c50b64a0f0405022101d0b2a009928080c1d00843c441150003282d001c0305040b52540c03249505030408601400e21501a00030506002c0200104a0260359080f007240d03120711f540789040c01c24142e07000008000004011200d150078605010400c01c0740005840038101d404d01e8003d20000c460760a006070b1a4410110703215401445500180400108440100b00d404024010a440c0a4480061a08a0f085030f01c01c0c0503400d1258450800750f18040c040d5581004120043c0c00086280a030301a60303900ca502526a03100742c80e4000140f140c06540441c1c0000c00c5c0c0078100c20007515005000400c08130302501913501190509010810062055003098 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 406212607 1250 406211357 406211363
    0x41b090515031b15091c0c031e02030a03120605130b0a1d040b04020d06020c16060e031906140721090209071808030a0e0f06030912031009020304080a0e01080103 71
    0x100c185440038004981650148122640140b0001804641c4064403032101d06c1c6140181c0381c010b0400d00f5481c1020095216a49810308901d1407894100980e80215102408070f0385424800c1d20300600c1d4120101401c5250300642d03203c06501c04448800c0c445820501a600080741d54003495501d0b40d00d1003100c03d05501c501d01891200e9000034000600c01c280e401c4e040f60008001e02c104180564504040c2d9005502c110400e80101a030013030740300c6d4011104d0000d400e9900b0094000080080030a54501d100184c00007644202c01d20f04040c880d0310780c404d01005070780f104803801c11b00e0480d801804c0b4031a08025643d405440309007506511480d44240d00b011980106a034000352500081210410602002d209028140580001d8111010001411000750035112a00403809003010004492a28101e8a0041e0000c00400208410120b814000600752008003600ca49070041c2061655a0542208070102e10000601090101000c06442400307004c2e42c481c40000001d200444510400303100c02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 406213857 1250 406212607 406212619
    0x6090c0403150b0411090f121f1b0201090b010902070c06030e030d0614010f02070f050405132f04090510051504050c0307030c02070e041b090515031b 66
    0x344000b42c0340041064040341268804680c50a114000804503900f94000d5101c2450000d10682c50b0308280082001c0c3e004115120303094485400c0701140c4400300f016a81540b9221500010089400c81d40440f864000054000d01710000c5180e01078024082d0000a58403002040c00010300d007240b6008036034000b6408801c0ca95883d1400b01c1c16000b4005180510f41e060100344180c02a40c080d41c4528001022681078036903051501500141c204d402d05401c0c00215000170300140600100100040c1c110b502c02d580c0000e951355048440d0242d4410504024050380c010180203401520383c0c40d12501410210342c0000844a00000300401c61345550402840d9400c000300c07038942c2c01003961025a0120b5008450309924140e90001021190100e42001040d00c000c030034000304541c14420403804014500003070441c00d080a00d640d42e600e100400007041c803004080740151040d6120a01e90040401040c00c3c010360503d00702c0c05010f950040700720b60181c420050b40c22402020020b0b0403441c03540241070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 406215107 1250 406213857 406213859
    0xa081c2703030207081c0902040b060c071401050c071806060306030b0f0705040b13150908070e060112050109020c0c0307120b060604030b070807030506010e010f0807110d0306090506090c04 83
    0x250044d400c0a84181c0f90401c0a0040c402241e00100815a48030040c4a001a00b80070314410801203034448611140149030034000d0303c0e0f45400001742d106c141c03050080483c0d810760004004860341c0c420200d036280035019200c0300140294800c0500301c10504500e04c2400580d4890100b20100e5a0507c400307081c42100d02c000c2101c4c1c0842c440c004e5002840d03442c0c80c500d0701c2c0d100d40310092194000c00025103030b003e00f10030401c551070064006002035589858440006450080303280d640c0c00341f5005081020004101103046603010304900c19010091032001e00c102e40e902c903140d400070b420a01440e005805201c00f074800301d142c0444c090003680c510240d204540b4443e600c941046134001450503802510811020000c111031401a41c4103091030386d01d12041e403a15440080980f02c01a00d86818480042100ca166a8000c0b41084141030513181241c1c0c95500c2c0c2d00204c440601034030208089000e1080c42e01880c0d5410f4101005403002040180196140c20301400544030044562034001001848 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 406216357 1250 406215107 406215113
    0x13030303050a0f06140118050a0b180d0b1f0e0a0e010204241103090901050d0f02040c0807110721080c120d0c0f120e0a081c27 56
    0x100880e0041c1c0b50020000304000f200440104480c1341d6044045494048401c001013980e02660640c40460142c10900c2518545400b04010f03d8043c0151408190049115044481440211000e40c4001003002e40444414100059030744019201d4200c619a01312070401c822200d030a203542202c10b403483c00070356640e4072880003000b452040154141d03550204400103100014111003040680352240409449201803070103400700091a5010708150014403490401d990307860320983c1194010390b1106120080e40c501350103c116140d00003035116103054038084180d0381c4410110300c41c070303a0380c0c4078000c2c0341c0300b54104d0a545044034401c04a14408030b80d4244a1514a000310040c2180b0031051207040209544c0c0c598202040c0c0d0113400040703a40400d0301c3c0b03903880580c0180000181706081c044141c0e0076000c03000301410726903420301440541f103407004680e204041042c800a02e03000011252648110300140300f1000c060b2800040071410480820304d00030600d0500c00d040800c1070b00c005c46c0c08110795 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 406217607 1250 406216357 406216361
    0x60306061011060c040f2103050304290405010b060403050a080a031104080102090324060103110d1e050a0e07092403080901030e0613020d02061603050304140313030303 74
    0x301500d0402c00e15980900d10102c2c02c0000d64001c00035070340300a4481d03040c9110405526502d82c07201d4540390355102403110210030a01003d600c145c0614015681e540c413030a0180c00007080e4818449401981000700041d0282c3e69201405148207400038400a01c900082202034000c9001c0501180c024042500015602c1c0e0f000b8101c4010700d003408075040d1555444407003550003a91081031165000207900006103801d215101d9100710101c3c01490290480300c0340f0815100081c2501d041c0344e03440364848101c5140100752281c0c09243c00301404102074181a00301c500d030110003010300032410039002c0785800ca203c2c05400d0407000c0000041400601e440c1c1c14801400f11039130503901210326a03401000c0c044081e041c0030003640c05002070742d6031a115400018222410500644415040001840701120790807402280f030b00e8040f10b4841000c1e223240000b031000d22541c030300002d0301004038400300201504003000d54840d13402000400c1c2034500c900642d54036482598840c103001c403081801880041e01039 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 406218857 1250 406217607 406217629
    0x901050c0109020916020c0301061d040c0b030903120f07020a0314040801110c0d0306060e040e190b160809030901121b110c121207052401030c0b0306030606 69
    0x20000490101c680780c011411008041d00c281700c00d410411046440584c041188428850b026030007080054900818481808402104103202003110004202440442440c0101a10b001400d140e41d904245408070741d80d40c40241d0704084a1840c00020b10000c1020f20710f40d2040c40d0a0300500715101069401b19140d1818050072030000c481400301045400003441150344440d00d00c5900b0740c0c0c0346620400240381060604920080504000050014592005030507114850a40740821109505011079080401098030007800700d0401080200f403049004000340600c41c012451000c0035500d00045441e4401183c07540107907482003000b0000c9501c03c50580e01d003813100c550000b80c002840c02034804e40505420f034650014803028010f9121180a028003160004203c0f1228210701529403000c2d2240c82c8907021411181000c502c10081c8501482079100f0449450030b014044030260300d007000d80300780a00094640880c4001d01107200383e91001200d0046100800602031a40ca4004100d903600a03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 406220107 1250 406218857 406218877
    0x6061314031b0306040209280f0b060702030d050306030f01180c0518010e04080705030d050609130c090906020c03030c0d0f051e04060b04090506040b060a06050d0f090c03060f06051203090105 84
    0x103104407100c2e288c02d844a4450810101002041c0a03c00c40710203015560114100ba100300010002500141d030005404644104141040c0c4d850341d070344900203400e008202c1462146075003820307400c1040ca625082c0c0301e04586d00c140c0d8501c03961500c6006011803c402d00b1001240f1411844c0140b0084400324500b6074002e00c42d01125103003400c0740e0340703441c15900302a85494841e5241c1302030211a140c101482903202150528085019007643c0340d10007846418412903135815540e41e840d005020150f0112603c0071000d00441e95281440c054101082d80f00c1c507a40b904103850803446400e1200940101401000402802c0d0b4001e1050b5092600030300c0007505c112003c0b566442c100c0143e81b201d0180d01d8032940280c0c0034040f43c1c601428003a001c3c0c100104001d03c04c0b031824400703014035074103c41591100c600c56140065000c65503404e01c002001e8a52025042c034985640010070030406800907a030064100702c0a01c01559144288505001c0c100d00c0880345800501c441000da510501c090300c84120 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 406221357 1250 406220107 406220131
    0xd030e1e01020f07150609020a020c040506131d060a150b18090106050c010501050a0509040b1b0706020711090106050f220b0c12070f0b06061314031b0306040209 71
    0x3d40c006408080e030b48081e4080700c400b025400341038001c160038070134940101100745082d4070b850000e050007511091404d5041e4843e540e90004990142c64000718840400d11006041004500890900c250100c80c2c0603211418400d550002d5000510fa00440e1001140203400380116030400124035580e4102001c41e0705030040039030a240056070396a005074002d20690300c80380d070b44210803c5140e080d07400580000780a48407200c0104020307140c41c54502c2e40b25170800c5104150351200315500314000c103844040c2c0b04501012400506101c095402403680e1441642c041010001e084c00b03128580c50240310b1000400e5041c80003699045080700217003002c208448000350004020000d4221b105c400d07411903001210003103454003d1070701c06c0101800000d51881000d0500d003107a41d0714248070301c0102000300100b41001c0030a030740b502e400098629802d80308941c6c1513016201d106161035034800c40c0e01d03c1e03c2841442405403100151000d00843e6010190281c225a9a2034080c84504d00340649490351800c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 406222607 1250 406221357 406221367
    0x117160303020c0d061b03060f08070b040e0c0403050615040501050d030c202d0613051c060c031406100c0b090322081612020d0302190f02030d030e1e0102 68
    0x651051b443c410b00344a0f843c0048d01030b00701200000c81d038103650000c594a60209a007070003c085001c0c20341d4100c0c1c5062040607c2c40d0b843d00e4040381203001c4c070742c03008046119040c24416140d9501c50607030481c1406481c2004284c0c2c0c0c41040012032a11142d02a0110b2040407400003c1440c0f90561400b0003104a080403644811201080b031040e90325454040111624254002031014552a00d202c40011a140c03401d03d03500c001e07200c0700b4200300e100f8584100a043c0c1d81d94200b081d590081b03603100e40c000301d0411516071320340320140140541a4440c1030b071112640000d41c182c504404034003481c1d00380c0d540700035000516907985070b90144040c041000520081c8410341d00201500b0442c01c02400c13441c090b03c00e26292401c5a45030031381e4030080048640c840001030008003404041c0800082d011201d112540841d424240e050003a40340030608a04c0c13054206405100d10700c0c0600c4e2049109800700e503a440c3c2800e100318100d44030481d4a0415410094a8a5011140c04503090605401d0b02c0014544 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 406223857 1250 406222607 406222631
    0x912030e0309120c03150c04090b031009031d011d130e0604031e03050c0a0309020424030b01050405071704080903030a09090507031b050d06030b0117160303020c0d06 73
    0xb4105521000e101c4d902c48041c0c085913040500600104c40040091402c50303040590003c03030305005a00440d0304560343c2d075508034140d54042201c03900280d86024100890350702420020400d122082c120300340e40b4114491514103510a101729510085261641c0c02c981c0c841c407007041b085c0c9000050071500d06803074002c4902e03074480a1000a0207240701e40c0f1403288860107241c0311381e500b034040010310060500e0709003000b003030a05180440724420704624000401c50400d100080045c0b45002668103071005410180038a00309810160059902822072048140c1ea20317010803080d03800445100e40050a828608010044500d1981b50080e1050010500b40309060f03012910716004560072800244506c8020840d000c1d203441456000a10781c03030103220b44112907151190907940c5039201010000700240340050784210768401805035601241100032560b55400f1020704003445801c00c84503000c0e0f6001e013240640c0c1500b402d000c981e03042d0040e01080c4040d404000b03500d50344440a5502c1c503101e0500d0340407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 406225107 1250 406223857 406223869
    0x15030a0212010c0f1b03050d2a090e06151e03040602070b0c03280618060f061b0201140912010c090906061407030207050a09060501080a0912030e0309 66
    0x12a07003480000180031540c1c544020044a03815140d2020702902440c00e904444d201c0c0b507504020707509410b203103035250b2449103810000d024855103407002401c94100380d50940103410074049541c94651b00c1c0181c6584401d0364000d40380040c0c9496500c190b0191602c3c0208910b100603203910b000d1120313500c80845422411140680c0110340480e030703241e40090640100300703102d40f240d17400a107085107280c154a050000d2405c0071081008280c000d440c903e94400c1018840c0e0042d6000e454484c50300001c1414001220014265901a420485104a80100d400e511074464007511081d99410021015202d4005440c002c0c0620301c030080558040012807107640795030346904102c0500900004900582035070051000c40141c0143c19901d0030b001b410071900d980441120781ea506242d6485a0354000d0345000d0745020100d9000b550024070200b000030b10118181d000710b08032002038883e1030003581c40040d904111100c50344010040c1c03500e08003044815209902846802c82e5000c00c40345805824400030740 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 406226357 1250 406225107 406225129
    0x190311060109020306180c180a0503030a2f03121509090a0c080f030912070509090d03360212030c2103010f050112061505040311011715030a02 63
    0xa2680d40000034058a41800103c0786c80007400715140180303d080501d1070038601e00c142110380310170030f002e400c428003565222600c034001060003c040300e96820300e48401408801c01604100b44190003807000501c0c2070f0303041c69820b0110f040e80014601d003035540c400b440506240a4410070303084000e8410040075440340d03440c041c003c01151000300258052407801f20401e1300c0e940c00c6074000f40c01c80c00700361440120000556202c08811114a41086843c0400b1454407c0691015a00c04041d4090196514002c90303c0100003086640c240325400fa84560030920818082c8040400d841150780200411180b2041c004c84134801425441110303840d00c00c0390325642080041c481c0542010300140d0008491420300c064090164502504642c9414010819400503200b0541407203400122000d0300d0f0041c6e4450009404182c81c1464600030800c3c000380b81d41c0090000721103e061241d0062010360003503026445104948004075066071b109a100b40900c050094101e40511800f0400d0006a1343c0342c58200c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 406227607 1250 406226357 406226369
    0x30403030b0a091b14041202182a0705070e15150a0315050f060a051908190911040b0102030705010501080105040b1e060108060d02090702070501080a020c1903110601 73
    0x1c15001307904008000c0c001d4641228005102e010710b21214007180500a90b03085401c0111542c8007980c150021414030a801c0e5103504809240d402000b06052652a581099505130000603c00d1041c0510710f44e40b40c896200040e00c1a40021400c00105c0c440301c03c02580045280c04440b00b112a50010803194901c8030400071140ba0049484a25103a040c032a410804209954640c00c0601e09000321749100300900c807860280500050402c2010b0107001113403070084800d83c5050000c850260700810602c406e9911103800318001c1111000741c12240554000340d604111400c00307840c902c004000042c00c00b000036606500041c032210010840c02e1054a000b0980c00b000440c89280c1441d2614001e1401846903100c440c204040001561a545101d0761140342824009210f444900c00a84003030200d1500075400300c0310a00300b1284035800300c0d121085800a80391800a81c0b0741d003c414080e4011908413031a030f90304c1811124a81121080302d403111500a08107030015100c81c0300319508009090b0029 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 406228857 1250 406227607 406227611
    0xf101805060a061403011116030507020a03120311090108070e0f0a0602061009021204060906020d180512031b0d0e06010e010303140a0e0622080d08010801060f0506030403030b0a09 79
    0x4c201180014807402504e1104800811102103207003075038030450007400b50310619481041d0740402007500034800c540090750000e1013884250354900d0240742ca80780030b00c804000241030000c4484031201640550b5002101612140c5c159a42c2c0030b0b04940300c20002500561042d1140b03581ca0140e200d414032200508041c1e800382680c4e2030f0503a40c00b5480d03525540500c0e291351042044032404220003280a402503805640815022042e060800180c0518080500040e01d011011555003aa05007000a814443d005441c3c00e40c000c07209030109800121200700c040c0b084039555511101105005010b21940307100d000032100b800181043c40c0ca10260000c04404014a00600a0607005030000618010762413455207041c480300383c024030040501050030b0242102041c6601c0b03241c03404a40c40f01030415002d1100c1240c0e61101d116940c1c1d5610302c1040702184541d400462452810f009020036101c2620340400d1107450b00301444000e9200820542c00c0590301c8100d04090317660701d55800000c240e44500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 406230107 1250 406228857 406228859
    0x1b030a061e03030503070513031e110a0503030409090f080a03060f080d2c030105090601140604030f03051b01050108060a0e010c0206040809030a0c0b19020f101805060a06 75
    0x6064007080e100c02540d200e1050002082002961000840358024018030304140c9400c2c0300c5100d8045081c05030801045650302c40642180c1c4200040076104003801503c0c21034920b05140d09000c00402c40f0b00607503400d600100421311044202d80c00555000348a44d000c1d42c1441c4603600d6201c2180c010000e10400039072901d104010000041c5481d10242544c040a0020b460342c088002e07004140e072140c040059642c040441844860103a800c502c01d0401078020b00807803034540c00300c64440c0801d000c1d0304010340300c0800e22076a500b0108141c40551742d11800c1040010626201603c0c00e0f0400e10040c100c00c07648045080e09800280100703402455044000c04031030400354050300950f090309041c070350301b60724240e401e1043c183c2c001074064000d40c010100c50703928000c036000f1a0802401c0c642c041c052500070b1800280c1c000c49603008201440b0ba8041542803546500b404a0b00c0344071512503007007281c0c0141c481540c071005a9102145c03214900034002c6c45c180c07840e903c0e10b060a0040720420700c0c65030f0f0707a10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 406231357 1250 406230107 406230119
    0x30c03050903030904022d0f12060f0301020a02070e0702010e0309093111060910120f06080309041b17090106210507090507090e0408040905010807090606090614031b030a06 76
    0x74411f0360940568854504000100c028a0242d01074942d8445180c0c1240020400b90f4882120000741c02002600030355aa45070414069921402841880c90707840c8082c0c009940b151040c07180c0c00d20b0702e503442e001d5854100c0d4103080119240d409441041030621075103a601c2e100f522011818035904060030715422070241400e28005c0f9850481201d4040c11003000103944956818210107010103071030600700791607601041c6c9040142100c0010030308680c038000c404103603001d000000d0301c1c048400311744c2400b04d245010395440c0d1034000f9009042c00301c1c5c400f60038010002c5000000c0380d80039001000000c0c5083d968840b005206155a026214210842d41d048041c00320600202001d00076009003880b80e03007844d1038018061515846225881f1826002181c0ac02c4000782c102d4000784400807007840303103507112402113440700201e12840d56413a251050008102e07000d144540200d806a403140310342080c0c081203845941e400100383c2c490404103410031407e0100040d000e0340c05203030131100000d0381d14181030b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 406232607 1250 406231357 406231417
    0xe03071e080114041e05010b061b0705040e060c070f08040f061101060501080a0905030705070e091c09060c03030b0409061d01020708090d1407030f030813030c0305090303090402 78
    0x242051150405600404c40490086008401ca03c0c0040d40d118504132081c0c2006070044c441c103400f11758843e800281021184610300428422102002d043d201110b07170791000c000c11607040410040081d04042c0005e0248a00100a03000c800e008901d4141000400d40d14450f06520030341100070849400038080c402c0f039a1042c0b95408400c0a50001c01c401401c200020b0019400201508012503d03101c2140401c1001d106071210f007170740081101c04072922221100c180c12000c903020780d0301d482241a0315241c2409442014400306d4070781c54802e405400c2507001c0300d00d9034042806800781038580d25041400c1d190f500c02c0540d818080e81c0700060042c010002d10848000346282880a80e00501441000c55010300c111500d042003210707003c0c6c1e942030a00e480100250a410400882c0c0036010380002400503408080c0503107482944e0300c0c11142c0e50300300f450728010707040c02d80640000c031040c82e14000a0f004000030460403400400300c9003808003000c0043c0c16a4004a071000c01d1540b80034007090011040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 406233857 1250 406232607 406232621
    0xc1b060a05060d0c181104030b010614030f04081b100e0106050406061407140a050d02010b0d05190c150905040e150f041a0a020307080f06060a0e03071e0801 69
    0x45903240d0f050780240e01c0e9108401e42c540251070102c450343d80303550200b20140e0701580076049060039464444d03692341080d43d07a81c402482048007180940c41450b000022220440f03103c3c4603000a8400540c5a0303485a00381600404d1701c40a10720305081aa115894080040650b01d200d940000704900805032092400c0d903080d9400140100d0401005000030b2f600402c2250400300015030300f035115100c2c0c0c1807450034260521440d003c1da01881002400b40040420805146442900280300c030003c0d880034080341e00d001a030042e2180d0010380000a405001618a004060107081704504a07501c0d541042c0790100c00240f0480414903154080110b810f140c0102d10700c0b1a4040e01600314000c41d25500071403020300803e511070000c48940040e04004100c801d401402d6001400030b81689001d2001c20b000b0360040d21f0450220303a120b80040c0c25902c12103050347c490b650180c111403c0c140450310607141d0300120882070b40d00d4054600049000c40a4821806c03561f0340c2541d1000d03100b441c2103d5142101e00c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 406235107 1250 406233857 406233859
    0xb1504181703090c0105071a0108150906060a090207030e03190b01080708030a0c1e032006070e12072d06090b180112141509060907080c1b060a0506 65
    0x41c401c003d0000c0d000314103c0d103280c2d07082c01d0442d501d0302c042ca072107040d202d03c001840f2050252040080707407a0100041d050041c0d00004c021960307035107070701e40c80580e5190101c075501d13071207440c500d800c1c000043c841d0003070b21a00703109043c156001d0210340002030812008480403048080800c101c1b005000d0512241130041ca8030802419007581840e841c242c0383c0c0301e8010300720709111401108100700000c1500461707c00d5120f25803500e80d070310940b0b8020201031042c0300344181c0565428000c00844e801081043c040c419503181c04019110810500c440081d09102409981c000c8060005081c0c0240041a001c640d14504080256200700c4c21a014910180c03c818108148040f0a010f442528422143c41c00c24a9645940404241d00103d51013142d6039400c0409600340417813800c404034a0f4401c00e0080d03a0300b1080d07913a00340084052150b00607003200c0f16035210030a0b03030100701c40500442d807440e04000019055460700b0f43ca111541c0c4080094814a80107034040810401c14100300d10500c1d8001c50 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 406236357 1250 406235107 406235153
    0x16030e041d1c0c0b060d080f040b07060f050709090b030307020618040c020718020d0e0a110901060f050706020a0203070b070207030c150f11011e061505090d0b150418 73
    0x100f40e101c1c00d001070300c010322060042c01404003140510561505403140321340e00d0701039103030340b1900c8a036044617030340020104030381c00e0b8101031825001d9405030040c648209072543e10503201e2072400350501c0c040d04803840c440e0340500041000801580310038009010f280b041c03045100c0780f210318034144001c8421401c55502190004102480781000c400c00000c1e101c1c0790030501680f80d5541e00d110034010015405003070454803a981d0030744104015141c0b1b40c410240211010001ca82c1e03100d40594a00c141c10645e20000381040000c5800540a513010b03005400451040f242003507a6583c074002040001d50340040587d100c00030800c02c00011300180d401600c1307000000c2d01110003c0c00d02a0013408001c0c81c0c0410310080d00000d11350450309602c00500000c03215060031280c01f940e54a10010001130050211484100900d2910240100122800e080010b442c2c050440b0082d100c03407864100103803c0a420442d200b09070442c1c2d551300e0003001010350030f0708100301002c52030b403510b1402030704e0300030300102019 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 406237607 1250 406236357 406236377
    0x109060911040e0a0b090c0405130c0f26010f050c0d0c0f171b0f0a03050a0903170705040b0403150b010c0210180306020c0f0601080316030e041d1c 65
    0x8900400c89019003a40842d85001719118020814104900341d40c10b0364001d0314000c02c01056100c0f0340202c0f0030303041c001c0c00e009a1198076000304240e0310308030703010746041c00040501c0c4028006410f0031541d180c21403c000000c0200c0300d51800d0703003a80c1040d40c42c12821f031004111340c4964800e500c82d00c00c82c0c02c0c05040201005403002c4000d44082ea2048012402c10079200000b03002800c841e4200d9003c10104010341e54410078039800050a401c02511400040e1034200043e540d510fa920951007030700e40507240c07814129900c4841c031001c003400030304401c204030b824040010603010940c042d1000d1803040c1c014100011349414000121030a0b00d40050400c11902154009a15540051152040d40e440e00040c0c144108104d00581700071030340001d000030304c0024840200040411960194044d410a482c45030341c3c0e41c2c603421703668051000b56014100d450701c84000040d000b00813040c01880050408500c000141e000c52845100e40b007c080e650350401c0c0c01004404442d0311840c8124405da00784a4000717 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 406238857 1250 406237607 406237631
    0xa06020105011a1c0509010c020d020714122107033209010504050d0501050105150f0d0510150c1b030b060d020418050115060c24020c010906091104 65
    0x40400c0503005600c40e00052000b1303544007031061030140001d04943c148041c2c2440010381b40202496091a00140110301e40522940e01c042100c03412a51600010a06480010200521800c040ea20084a480b4040904244030700c031030201000c0c540041200e41d180c20306410090318828000c5281c040c020807110501000d4905a52100410204031030a0f503144c00a61b40140c801d407081350000e69112206805010070040150011070581e0340540d031000380908040348a10940c0610170340c6581c0380c582807000c01110400c0303620045c1d00130f45615500402e1582c4941d1949140540e502d40d0000030402c0c0420030074058010803c00301d0403a2801034110303082c51500d98420039140070306250311600d0507504100540d503568004c8044030501555040060310540f401d14002d00c030928441d8110702d490123000402a0007004801056604480f20f80d41d60340111070840c1840248078dc07006407882d82840500446202403003200d900e60322602002610392150b051a003100da8218030458400c4e4240750060003e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 406240107 1250 406238857 406238879
    0x15030702033c0d06060512070c0f120215011a040612020d110c1b060a18090e0c1302040506070b130807121d030c1c050303010f050a0602010501 63
    0x1a085088060301181565090906100070160b200190076030700d0602c40741c5a41e00881c000b40600781007844104401956820280d590340a501000f0700408541c400240001d400340c1500041e03c0c0c4900c1c05c00004c0c012999607655516010035032040103a21001c54010000302010f88540540103050f962907a032801c03074049101d81e1285018100c1000f080c140013400d80300160b0151841e000c20400148a0318000c2c503800d01b0319401600101445101e049042544940c202c0c1c0d10f081401e03000740256280040400054403140d91001c1800326007200315400003070400d0700b03102d1a101c0742500da014102d541d61030010842d800030402c0019903c244100002c104230fa46550031030f030030250b1001003040c0e599501004210003003c11100a041d1200c000744403c01c000c0c19001060b121a80d0fa282d9850301511000310440312082c1c40300b8075030140e01c00810b020b014584030302d9206040c3c146420708005010150360b480d0440c0c000b0703032092101c200713103143c14846450315204241c0034005a2008020329850b064031852 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 406241357 1250 406240107 406240117
    0x810030c0501050a0315140306070c0201200f0a0506100f080a03031107051606090b0910051e0c0c010e0909100f060803270f0307050907050c06070e1503070203 70
    0x1060010008000d504c6130f000b50003040c200044148411000e070f40d900d1110584181c09031929201e0300851000441c0d450150040c27804031901079540091900746003001000c00041c524031560f07240305092220b1401c001c108040100c6500c91000f600880c1800f81d49250018042c0c0c01c48a4a450000c0003030203603070030010b00d480e01c02d40c1514012401c074140d00340d07010061041400c00342060003100d00d40c1041c0c100302640403007100c41c0c0365103c50070143d950961403418000c0407400e99001c000081200c20700d61042c030103032400196201d0040405250041c1c08101036001c00f104180075000b034004001c0d19a0001c0c080d003a0100b05844651071460a00402c940301e68210070381d0b9010320350f80c201400c41465642d11400c0508005403c0300c0d515900c599081c0e412140110840780b101065804001c0e8074144000e203c035a1072809802002d1841c1860304000134104020700000400009100c40240d030001003181c9400b45c01c443d02c1da00d907c0089501484100500d8000d040c81002080040c84407881e80041211 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 406242607 1250 406241357 406241359
    0x60d11040203040f0b0a0c080703090302030702012f150f06031507020a15050604050a020a0c031215031a0c070c03110a08010c0e0f1807081003021f0810030c05 70
    0x42c0d4950361032812070900e040d80075000d07016012280030850b00e9944c5a1145003c02c041d61604c40342662004011416120450401030041c4c00500032030b001135008d00039070203070240c07480c0858001c900010340300440801840c652080039449001c40380c40048140010765000124005500c45074500310b00443c0c2d45040340c00030003480101c1100001c1c01c051090051008065100c10900219001011020050f141c240c50302c500c518500400f26030343c0c0545108844040d811500c03601c60025042d10241c410400703440303441e1f402c01d4032005071500030348140307665001440c4aa1200c01411011070b01024000c0c100900b04400c4d1041000010040b59140c2c000c0c00840354883e00c2001050350640108407401c80a03808042c466080a0b03424130303120742000d0401072407501550b40b030301c0c0005114200000b08513164001c40b10305840802051406200e002803560103903e141d00650301690b00d60105081071641c00081d24000c0400c1140205944e000c8001c54120500e50349503c1c459040d5141c240c0c90800f588666 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 406243857 1250 406242607 406242611
    0x20f270f0d050304030501050c1206030d081602031b07030312050903030a0209040b030105180d030207122604030504140303120c0a09120f06140f011202060702030321060d1104 77
    0x790030040200202c41c00746030b00c603009000d5410500000412500a18000c00c800070a480000d03419040005104490f050190ba031218141c480c00c010740d03481c941d2481b950701140001c0000031043c10b101c03402e0078801032885004101251440c140200702031101e100d01c600d00b905120510820900c0002a80c0c0c005d520b0a00040c0d840d00c03001c00140062006440c4640c05508120801c501540d103070cc500e880b091107000503500c5c140e9441500720100e2203024001840502c1d0b040c161400c26100d00008034010040700000d5405032001290248415000c940c00c07000110f00090910000204003400800c0030300540c0107608094640d1000040001c00038120700340e0100c00301e420360b804d84c0315240c0d0600038035018840030324140550510107921500403100790365150814400181800c01808420b02c103041d60614501183d09000200482110f89c0e031060f03034080828020b00015176000c1c401044980810314a40302c1310703a4010030030562101d00400191064070544200c5c0040381d007003c03031200d03601c030100c1d40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 406245107 1250 406243857 406243879
    0x30e15070602090d1b050a08010b130c14040e06030d0e030d031a1309060b0901080d0c02060f03150103060602060c0a0507140304030b090601080d05160c0801020f270f 73
    0x802e06032000c3c41805010407030360290818042d41e80c007124000746c4006842007010f454071030511500344c1c0c151980780b030342095581e401807182026560081180044515012840210f0801c2031141d9801c141c0024114035003400501910745010020304404c0003030f0b418441040e07050000002e44800f032000c0d58800381602c4800c5503001070540c030410144014000c1501c0070070b5461680e0b002c018a88900102d07200d61411000304e040c1e280c8071005604890410f03008092000c501481262001501e110490b085a014400c034025050407001442c405e21040a00070301c10940780000500340c0f0481d03806502550041024082d808081d00d0450f500e1401a00344241c0e111110b15000e00e14450314200c0303071210300000c24007100300008001002d019003424400c07900140d80300d013105603d40116000c12804203804000d5510807600c800704000c519030250445500080e070311450740e800d90340604400d095040340001e080c1080b481d40898441e1400042c141440c02c000d030000444d0240c80c01c0042d06224558202c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 406246357 1250 406245107 406245109
    0x2070f0b03040b1312031a120a02060a0c020604090c022104090c0e150301170c0904030309030c060e030903010f1104030201030e10090b04021f080c090d17030103030e1507060209 78
    0x41101340310355101120107040014801c006000300a184604d40e803404d50030010411920342420012166071b8428050443c850840e42001000c1d03006e40100030600482d01c112a01503500c0602800040c0048200440e040b08002402400c00a201a035465609804000c84103a00c40e4201543c1c151505030000007062907414070103036207a01c240311800c0e51010b1640c0c4500c4448101a01650480c0e041e0f8440f52056254045c0307490321040f5003d002c075000782e0a0800107012900c00e800045440e0b0007401d00d82c40c2140191520302c10b850b800e81247c1e007550b1000580003540d0900340304141646000400401c03880329000c000300940d1181c2d00c0003904041d00e81824034201c80c0c040c80b43c440170668038a8200301c803200d2858030044500d07007150241e2041c44030855049050050020018210303803541d031105901d51f500c81c01d030941500300d00c00032078000d64042500000101101240160b10040303d00440e180c2d0f00d980703002000e84030075807080d42c05401103003d48000190900140c901d281da010402589a0402d04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 406247607 1250 406246357 406246381
    0xc03110a08100608070609030321020d050709080c040b0d1101200c0f090f060d08040503030406021513080301030303110d0527061e04080403060507020d02070f0b03040b 74
    0x740220480d40100012640348840c1c40d4802001c543c0da88058076449580c0326410385a12a0510029000c90303030f484c46014802070820120203503504096801030420816180040440380112005030126a1008040c00507880400c040c403001001142c06122654501010450003118100010b1003003480740307809a0f081c2e004044002d842c01402d03070140011140d00820968074051500c485004c2c00c541c40c3c1103a1581800144140f00f215070044e1034005071101400e102d0b1981c1143d005580b162028000441c282e03a050004200400c0c05030700910111813000600c100001025080150b40c500c00810940042c0070f0030140ca046a030141400039885840b040c40321858422184c0410180c4d2034082005119030a000750000081881084a440032481c541c20ba5501d001c203031807545500e101c1c1141d02034000c00c001081035000384100c001d00e050030395964400c01694010f45080d80947c0200001d01013041d4100842d41c002c00c48d80c01000401c92a202c2c600700b45210140c0058a24900000003071007030685c4c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 406248857 1250 406247607 406247609
    0x303110c030105040b0103031e050f13030b0a24030b04021005040819140609071202060903100b090f0c07023303100b131e09140604050604090c03110a 66
    0x341c0248458541458400c201000c2400b0480124008211261a040f0000e075000304204c043d454407450003c960084189a801000401580c1c1c85000b00120025084050040c0528088603002c0355220091504201484806415011000c0034010810201d9052011150032540564070401d114403e00c0049030544290f402c0386403540700f2008203420500000f68407030300d440c0c0508518103600d6074004070607440c2da60036110102d5942c40b04c5801e12401d0104a10080000d1000b0105c52900ca4924042400d2110005a4052090340c07000002c0c0a07003480e901150b80010720503158015131404100706445030081c02e9029004089071b1103004001401c401400c54460384803c0b1900240702402c100004590013101e41515245c140040068115a0003060f07800020101c00d03001c07403190a10410540500d81218000e090384400301c0700007124000ca1190741803c50162208580070724004092000b03942e03016203258003c0c0e1410a100000c601100c90380c3c410340380c1c0203042ca1a0902d11500154440f01c007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 406250107 1250 406248857 406248859
    0x9010903050d0c02091e1902071406160f020a0b061516020a140d060525091a180906150c030d0b030303071d0103020f1b0705190303110c 60
    0x1400b440902d00c90b00500d0f1806114422680c0c1328140d620300008204080e9801c46c03079242c442c43d81e4003045c8030000c0300310800641118003c0060600d078641e00d6100030781503044d803004007d410007010703c000d0450510304043d2490150030860b110b0b400c1510000d41d6070b0071f02540600320784480004034042d55200028001c40b0515910380d242c8880c4408035070924020a4032080380b04055291001462811840381c41b00d0845000341280c05090720394607914017800004001030100145045c07401c81c500d00805001c90400070b41c0e43d170b11b1141820040400b2960440e0710751401101c80903c0a00000161000e2040980205803401c1d80152103040200d034006402c0d191034008808081204140600d000024144660140078248400c460842c11b050310fa04c415681da4000800c0e1a4608486440b009982101c801062600614200b24105c4843c41a04502140d00f00c21030000350070b500702d074020000309001e060300729510311044100035841042c0e12801d1000405001e55901c0d95488000e091244940303c0d00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 406251357 1250 406250107 406250113
    0x92e020304030e0108181513050f07031203021213060603020303031503060c03090d0503040c080303010e1504050903090d06060315060e071403150d150218030a02030709020901090305 80
    0x249403802914049600103c18002030351040000c030410b492080c2d002060440f0303005058008010342d4a40710907107000f0711485003a000101d4100000c1c1040007100d0200c6a0b810107008090705500e01800c030050a04105800c040c014400f50741d68031034440c401500301d4201842021840314500d000c07030240c4001d80c400b13945400040200110380d4041c041c500313a0001c0840946866940e060603031111030006070360000741c582c0030b03800d1480c0850251000755042070061402c00781c06695000503c2ca1544240c102131208804001408001c01104450380c0c001241210244041c1c80c00c0b201c1183d0300d000701003002c0c0c0f01740307000422030040c4200340d401040507541105800000f412400101d1020b010144600d2510412a60001e01c405128825440c0100829040035107140c43d0300000c40c2541c0200404541d0000c0d804001d100022205120820030a078801ca0158890900c5180c080a46d0a41c41a032030080c2c01c010344030030069402150780010b540340c00d080140c03100b02c0c02e80101d6011046420050842c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 406252607 1250 406251357 406251361
    0x9060c0201021f0203090c0306010e010603090203031c0b04050906060d03140d050c04030302060702070b04030b0a020d151e0302092412150c04050d0308090c041401051305092e0203 79
    0x3c111900190b201e15080405c44808003000010715589501c00d21494603502265001030046600c2030300702c0903403d40000c040b6424040c8900342400150b48140004125550301c1c2500f003205e080c9805400e52103e40c46000e450340345441c0020a04400c411480241000070071280c4000600c080019211403042d241c20800c440e1500c016120040c1e4090b000507001f5216110020b44401d10000d04041521203003814a400c092a5035508022140003400b07001909030240300c2c030500420540b1680c0b0410380d080c05da500310107181400c00340c01043c01d5641e0b0740c0103000346201800503807100c4501035001034469168070b00c54803001c07034100d16540700e0a0b619980b1405062a0040fa950f00242c88440c80f2800c0c46641007984030100210003610440c030440d504802050b039414003081c0100452a844810700b0140d40e5031030703c1c6600140444806460b03c94024001a006000e1410480000b2610100000040005003002031103580e8444031032801599204460250700034400e40001b04004105040300250345074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 406253857 1250 406252607 406252663
    0x210030219120608030c10020c010605040c180906081b0f0607050703151505010e0a090524060a0c170c07090203091b091b07050a0b0906130309060c020102 68
    0x104600031440159500700780c030105049401008072000036644800501456400501f20300c080d4110040a28040d50fa400d400262034840b40188a003c802d80e661319010505002c000260890340364100a03c1c0515014040c0121480060480014204001100d292261800009079038500380b40e6110b4010b50081005003c100002415070103591240f0000c1c1640c1c841c4403468000c580c0105680030607000d080d0300c100510b50080401c00b03040302c2d0141400b1150f43d1540b01c0c1c0c005841003a5941d420103106003a000250085c1d56980a441b0768049030140d15280d1180f400424942d42400040d1100c41c203071001c00880e072035060481d038029800c00c00781c8400a0361403030920003d40088a05a1540c01524280006c002005040018911009148644a84421078181018071084d24410103114040020780d002c583d081045c030440134454241c1c0030440c50005a141c0c101030018289400c01d05404681c800042e40000d04074050743c015107040d1915541600040307140282c10307402c00e0100071114151083d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 406255107 1250 406253857 406253867
    0x1e0b060d1113290f0904030e28080307080403060b0d050f0a030f08070f032c060a110f0307050a03020f2a030a12020a0215010e070e0f0108040210030219 67
    0x4541c4070800400c003080d060492010724080224443c561041c105598030101c2c1c58441240d9030018000d241c014000003005001c21203803030540300081075040003050140c030508203401c900c030042c1286902070740c1403aa040d0f440d842180605e0000134034070754480e501d1001d107880307114070740000d076401204807600a01000c580a417641c8902000fa400500503601002a03280070301d1210707000c1c410960340c042d4520307a0240200c1c014640385120b002c050001c00c90319124080d0050a9050b6044510050007042c200046024200e07500444449480d40052104812000110081ea980a01141071841d682c00751010118000d00c2002c5a10000c400041381c48186540e0b40a511114461001c24a2006d40300700d8101566070b000c5c241d0608000f61a40d13003001c1c100303000da401904010341030b40125071526203180304c8048100001d800105425030a4010403102c1680820005401d28041c2c8101300003c0c0c00b01d0009249040c01000039000c1c8120b003a241547d1071081d412a00110481c00d03a11174480ea032840c0c0100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 406256357 1250 406255107 406255121
    0x6130306060e0604020906030718270f09050703081c140a0e1b15160b0f0105010c120302030613060b0a0806030c0d03110a0c06030204031e0b060d1113 66
    0x102d086a40002580b142043d200300d500400000b05114110b0b610b41270110b44e2200d000110355100c60081c07500140d203180070200d2504850083c03003032801c1420309400c088110341d0000c2e41c1d660803604240c0d40401085000c59020300762600a01c045580d01020741c52044000c0840860450b4140780290b00b80f040c05c00300c05400d004804090081c0191014000c40503552030016104500c8144c552072881c06038a04030b02284503c68040344154140702c10745e4a000c4c02460241e0007030f80c86041c0d0808210440e0702000b0958007501c0c007402c040000309156100d558800c00c81d1940181407543c0000899800d0340c80940388110036841c04002c0c40030584481e0f600d0007a4018580583c00301c4e1421010400c1c0d0301d004900032140d5480640000b140700820b850841d5088410b0035400705a0003405203200105041580990213441d0a032400b43e6070b145185081400580f52001c07860848000700310355000201d6021248e0b421072411100f5240d54403e83c00c10b88084680c010440798000c00140300050514013a400c008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 406257607 1250 406256357 406256369
    0x5210709020d0f0501050f0d150906020702030601120c031202030d0c020c030d03062114030703020715081b0901050f0d0504020406120c06030510080a030c02150a09050f0613030606 79
    0x449685011840c3d0400c0d02c07400e014481c0e0212106811b140745003401e41a110540b40580341c0320f40c001910000f040c084a400d058162045038000544006505007000b281d40140984040d54034a150329480321190489140401020141400407000d4890b100700107584079201c0161040207413921654020b595462061820ba01a0144100c810002402403069000722908066084850040020f2440e2101c0d034140044542081c0e8111070703102c4160070409804020703c03079002001842d06041109103807001d4039200c0c1d8108038103c030400407501240c3d44402c52421540209039168245000161141c1c0900180074048030740201d03151803100010303000750780a00d00071389041001070344546000c04100c0800d1800f401403007034a03404100262180e4072441d407050714445150f0380305403034148250404e02660000d80009803128030b00c03001c1d40341a001001134216000c180c24641411904043c00c540c200b0300c02c05100c0da1118911040b903481f40d41c1110701540c0d40d008180d40f16500c0b85440360080845014030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 406258857 1250 406257607 406257611
    0xe07050703170f1f030c03020906010504170304210f0b06010905040207060f0c03110711150a050702031506031e120301180b040504020f1201060b040b0703110d05030105210709020d 79
    0x41c2c180701e1019132010341a01c1d0400840e200d440d04603000d203c4264409494181002410031000400010a074070140c40c1c81410f01c084c646d1145401c000044e0f102e100075040680018004401c00018500b0aa0111859000b01c80c0380056031040c006841d48000c5a2109803c103000207800c0b4204a040d504c042440c800820040000c5201c401d4100c08555407400740c00d044a800300314010102d006088000300060b8010031159482c5054008407900341c00004d805400316001248420451905005c1d0b5000360f1401d180ba002c081c6000c20001e6035a9010700d5001c03501341110034110000d040f042c0400c1c641d512a0080041d929655025003003d0080c83d040c07002001803620302c5040c0c840c0f9050040341d000315001403054815145600030040c1d030ba0b103da03121070482c0d940c038107000854000d00b001070030062026010031a1521594280078100c3d00310810014020303000940752800342038024003501d06480042d1201c0441c001b10402400e80060030592411043c420000f0004140150790010003501c20f00d0882 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 406260107 1250 406258857 406258891
    0x5130302011505031e0f0102160501050a09150e03090406140108010602150106030b011704060b0f1503010e31021002010b010c0210050708042c010e07050703170f 71
    0x45102c400c2100e02405a06800008188140c9500340708201e1807108040140c0b1030038400360a030142280c0c0444042d0301e060340640d04e031109200c03007842001c5e80403601c46414891250940d44803030383e440000100901d556036034464850b140000300181c81d9100e1700038000700204d6840c0c920340c81809000b4000c00d8006038000001041d86407010601e842e4100083c3c00010844e42840415405401c0c124030180c1002049484400f00307032105c11000d4000e60060b10005541492107080c8050b410182403018060343e070304110b100e562204282280d046808815604d901900c407101240c035525649406158034101030b5103400c070352140b0004108142c52003280e42c241881c500400aa090311801000c15012902c00c0711010301500b440121580b091006180251400505599180441d08540c0054170340c0d11421015400d20b058104400e452410f55002c8440c1039850104035224040000303000c84100074004c91300c2c1c01058090b5001c2c1100511602c2c00310300c245003040605007401000c81d903d250410910741c1c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 406261357 1250 406260107 406260131
    0x5040501061d04090f05010c0f02010c020c010503010e0a02091224060f01080403090801020d09020a141c02030309090103030c0c090e2505060a0908011109060706050612010513030201 80
    0xa10261042004403844400b100090200401061400f8003600d210301e50100c0100003a00a10920009031019200c90041041e10324009084179007000b0b00c0015584040c4c120300c8640c2c0c10405590450b69442107908855480441e0710005c0e01406250680014038500030516045010588913084000841410400c1d190800c10002400c0d040e9441c81e00404d205201244552143c5011584a402030910ba10030541e40c0340c00ca400c9034000700300101d0031545c2d46880c3c0210715043c880c200c02000c02d16942400a19130306c000500d0340b444110b041c45c518000080c1c1c01c08549050040c1c800304200100384005a60752810081d2040704020001c03140e00c1846400410f036103581d8424462526150002800c840e1850815038140c0d1009111080b088401c00700700180c00e994100c0104140e4105aa030380521629010b00c90b82519420400c0c01038590040c0010b4459480d5a8151000650402c0380403030b168840780003281c8428100300c100c0034154201000c02c141040c02c01194a0614443d500800040101d40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 406262607 1250 406261357 406261367
    0x30b0a050412080a090221060a0903021f0906060303030b210d050a0e0d0f02102c040b0306010303081b0903061f08030a0207090e0d02120a090902130504050106 70
    0x460040c1a01050311040b0a440d11032888160310420140000440c40d25580020744201c0c00e501e00e1700180568080c4036038211600740709403908040040300c1880280d00d0b40d0350182d180c00b08020800c80e03c4810000b51000c00002c1d4003c180350030307080001048029100c5c24014040c180e500312a80c080d02c1c03103004484218000140d00141c5200884c094240c18402d141d080310141e200480103000c0151804c1000c407283e5a043c4226203d0b481208404148a03180c81030200c240e415000c5403051041036107030f0a00040c040380405590711a0051100c5e001e0748003800040060030492412609403040c48004000c0581004006000e05200b1200502c044074011243c41c03180704010b1000d4054009002054009004020b801c01415585c0d2004c41e040b0380382c03103146295402007a201001a40a0001009042628401c02080385804e23000340c00d144520300e4002e591074050b01c1039a4080c03080020540c404a104a40d0b4801602c05600155502c40b40e03515041c820440a010b55881503242900010b1024024 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 406263857 1250 406262607 406262611
    0x1406030c01120b010302120117010c0504030308041e1b0816030c031b17010b040b1503060d030203090301060306090b06030a1502130510021c1107090b0d080a0801030b0a05 75
    0x5a50302200d480c00d026666015003e840c060310b050540a2054140f01564510500d02070314101c0941c810900c000710070b003400c0d01c0f15541e1001c1440401c003c00d0000ca68008011580190002c1400c1c070485104000000c41581110015028890040400d40100d4810310341a0403900604100c0300d140c1210703441280350341c01c1840001c02c40f00040341c0400000f46840c060070780e603504640d1101e0502d0760703889007004944008400e00d140c40c1d640301d01c085030900c1d007880344071003504040e5030796034502882c40681603d6120140ca428860301003e4000b1081500c208102c5100340000740082c00031560f2460240c0190503107000031541305111000207440fa0074006600d4040c5600102c030026080250042c00000350310400c42d00309190607070000800d20340c0310325a4414080b459030b4020f20302400d4018090101c8940500d50204011007810b0f05840454006811002c0d240c1d01d1000256200c1240c1c0007800050b81580300a0060601003034140a06070040c002c0c80c1200d000f100c0114440d42c88818600c01c480302 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 406265107 1250 406263857 406263859
    0xc040507020312060d0212100f1802040b043309050c161104050f040623160e0a0801020a171006030903030b090907150e0a12050316061406030c 63
    0x180a5040e4003d160808260010009060841942074540100f141d50109a400c501c0076070103807140340c007072901905c500840703007074019410040070303417600d040340414007401001910070764844482002c1965a030344214200307004071089803580805165000d0f94015948000744c0c921268002c0004d10400d42d000d030324401c4140180103840c1c072614130258008001542c200382c8091407000386c4a0000d840c0c61280300e000f4894026010114a003034604401541c7c020040907840384000300c3e541e000669080a66508550030701d40024420090380c8048070070741c4540c03c2c1150f00c0b8001010001d801d48041d4000d0920074080c3e921800d40c09941c0521444c620310076142c0e08000c07040c142007005103510075482161020f1007840c02082d080c1c4010002001200c040c1c9003e4550b810007002008054503003c0c4220302504a4142140c85921440000e0300039540341c4038920300c90501509034800c0150510840d41008804940300c2c410540e28246040284003011214500807100d00108041c2d180004a00a0703400c1c3c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 406266357 1250 406265107 406265113
    0xc01020f0d050a020a1205091011070302040506130501140301050f040c090f060905070f0306080a0305090904050a20030d171f050d0b04020f0105040e01060c0305070c06020a050c04050702 82
    0x40d900740c00c071456070221140101314060a44a000040c070314a68402d010b28035a55034036101c915201c1003041904005400c0300501040845101c0b2103480401c5503c216901114001010f51320640442c44014a40080d0090030380752034000315001d5140702e40081e44400c158000c00c004c1c5e5a00d0852400c11405417000717040041c08103c200712541c8150424800d00c001c0d15804a2025600d120740e2068030403d481841c00304d8104403140d00f01c2545841580c00030002074005040d900c2d01520068020302c030b12607142e0700901880b0001414448100500000194809031040390402000031809182c84040907103071080c050446080c804510480c100c202000000702c4010300d980f07507000040b906501c181069031071406000300008183da01c410f540d50409024042420380713854244104a941c00d010a401411312900384030500c002140c441840d41503035414203144c1c40c2c6808a003010b032098000c0c42030051040b9103d140c0030500c2c1d0380c04502c00c10114422001c0350071034080e81c010001036030b104881e48001a4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 406267607 1250 406266357 406266373
    0x5070b060406030b151203030112060f0209061605060601020a020f01030c02010902121506030616181a04090f2f0c01050f0730111315020c01020f 64
    0x1400a804094000c40010030000b080740d960303540c1614022045808807041400d00d900603126041900b8116540c0b00e010f00074514540c100141441851481c0c0b80141c42c255407031407801807003900d40c0d04491007404e0084c192600c800d0740e54064a201158540e04441030700540c808646154000252658407039802010082030886400044000300b038070341e07091030456403126941000b684981c60701700400d0782c110011302007007c20700700b03444030903600501014000da00100400841504c10300c071502001c000e40c03034101042c40c4409101c110300d100c142c203ea90101604543c8496038124a00200211000030b0010b01c41d111000c0030071003c541d6005140c95148001c03a80c600781204450041b0f07041e10241c510007509003008801010300b181c608aa1104111401d1000c1c07024241d0040300305002c1c8100003ca800b8007100d00c0400605070034000005203011901c44051207101030030b90080e161054001c650107421a0f5490200715100412510303080301501030000856050b510202d0790700d8940b01944028a252 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 406268857 1250 406267607 406267613
    0x60801050108010515070b07050307090e04082a01020315010905040218040b01030e01110301030618260c160303030c0507020d0b0405030f0c0d0f031b111606080f06030a030507 77
    0x45c54890b042091210f420014000003c1801c8140c0b80500010780ea465101c1c0303002240a44011500e40044401c021004200300010703080000b1a4015604144c1488441003600b6079043c110072003000b4429070354000b00400c000000000d080034803c0c0401d0365a41041e60750345003440b0482c403071064101607c100381080d503a190f00b41908141c20240d41072400254141711000e0880c21205450400a03030040000700410902000c1e0082c00c90148070035002002510035a580c0c000c0c0308680c03940b0080112003800c1c85401a0054005541c481c02c00341056031180c0490266882c456030b5280000c07408030389040900d51980d440380341501e454542c0036101c0b0740499800d44421031040f0000780220b40c03600c800c01a00c1c0112816002604d0340140402c010030b540c3c0b40d0385402800707600d611031007401010702c0c0c44400d507400b401c06c0220440f10407032410300345e40d10031403441c4240c05d0903000400b50f1000f03005241c00040490b440501c943c4506d5107002107100307903240c40040640311001400050f0010344180110303404 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 406270107 1250 406268857 406268869
    0x17181512160c1403130303030b040b060a0519020a0b0c22120303090206070611040906061407020f01020a0602030702160b040f03150e0706080f07030b33220608010501080105 76
    0x150b0f0007040301d0400680b8001a0400200c40d002103000070345a40e0b0800b500d0400c2e018448075200103c0e121414200c1d00600241a806450600b90120091020203082603000b8000c400c0b450350402c0d0240340f985041c2d041880366030700600790070b0240c0480008c01d102000300c0840b04401c2e200125650500a9140c1d2802c40c0541141751b8240d130b01100c04c110100000d0060710034002d50054000c1e10f1911140b801009908440807540040103000c8406100f0004840b904103c50306194100d0355004905440700040b45001d0320803800510b42c6100106000000b6000030340008075085904401d1283d80c1c45101d0040300780074074401c02c0d24254040006000054480c4c207000c00c440b03005540042c01440da0041286000d00315071010300490081428004800100680d01e90320a005003402d000008440020940c0c0303100b80e100c0b100421341498241e81500a0004401c2c404a8085000700d49a809405600011096110a49050480740c01002440600a40405040350130503100c00085038646802c1c004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 406271357 1250 406270107 406270133
    0x61602100e061b130f0e1b12070e0d0c0504061a0406050a1b0b071706090601050a030902040e010e06100b090607060605100207050906040917181512160c 67
    0x202c111428811009035407104c4600000070003034951030744000b03440d00c070b202d109100016090160100c5a102c4107420161044201e800d6428001248095907a0705c030760031101d0814204445030701951503810541032045e02c0380c180c01920380403541081103555811303800c94520b09204113812414400e1108000290054024120000f0942484140b80040049151000d10070000841c3c8494100c028030028547c00400b00301211a05900200340d07041440002d02100001007450713040110005600b42418482d17080304240b03980c01b4000384000540040003c0c0a0140c0202d00380241c858400090084424058103c003101d011000302458840010140111548402d00035101e145d12880009142d0b01c07034803200320130707521a40d0180405a04150801043c128090440c901c10380c105a904070218603111103d58404000d5546544da4801b00808010515814030040d64004080000360942c25240c0c0c0c01048244c0070024030380ba03a55111080b90002d81c800804140020703940b42c1450002414013012a8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 406272607 1250 406271357 406271401
    0x3080c1303140a11040509032d040305030309010e1f05040812090c04050a200d0b0916030c0c0b012c0a09050f0a26070203061602100e06 60
    0x1003581c490302c0c0d41c006000d000740404082d034800c0788008240003000c0b2000e1600e1504071410700203400d0428005a583c0652007840e40745070203c000b0300c5180c8840c0e07074207068a030b440035134600d0b201c50f40d030b0a01a40325002110b0345103140d400c01d02e13201420000070a405055480d8080095813100d051143e00780200002441118940c0b0300b042412201c04070110391a20a100c280000c00e0f4280c144001e000650314007410f44400319051a0341c0f1021440d03608e50b4200c3c04407641c07044a4903040541c0b1a2800b500600c41a140c0010180060256440e540300001464000c07a071400c1c041c245080f403088606000090000d4541e9903c5401404113001e055185084482801605d40c0c4403000d00d94010580c03481a10345605071a51100d50b102001824484881c0313550030000a405c611101741c9600000c02451149203213100421020128101e0458040e50701003500641110b85500e00305942220b9141001c85410141c45800c80c0004001382c00d01840c541060004090300441d10740402048210500390415 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 406273857 1250 406272607 406272637
    0x19030c0b040302150a020c0f06010803031b040b040303030203040c1d0402010e040905010e011a01090e0601030507020f010c0203041406071709040b030a05030a090b1305010c0201091d1602070303080c 87
    0x1104c409001401c80740158041d950069a403810401500e2601d04004102046a000000100302e510008000c0c0c0354001c1801400300f00d050042c18148005225a40005214101c00718000c018141d01d075014510440c4120114090349844403108150340b08541e030411179844840b4001401941f049940b0705610001500c040717481003181d41c44070309480f25900c0c1c01600742c1d90f9022141c20101425401940e80c542070034480d88103402d04003000c0f0407000040c072135818542c98401080300700344200000742e140307c45880200041440e1900c000e40300d6000c1d114490f0f801e401c03241c2136102444c0003000c4610070f581c02007620442441e400f6007001643c1048902130ba003c0c0e81c0b00100402078400f4003d64510900c20360245544950300381c8080c2040e07025420494182c031050100e5503031410f51300710350010340e0b81c2424002e81142181c0b004031a01c00594000007005130a901040d06841c4c444580b442c01003031054205030f4003003000403003240c0e900351600c009400165088085003550b81d103a001052400280c02c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 406275107 1250 406273857 406273873
    0xc06021b0109110f0603010312050c06100e0c160620040b0301030b09301b01051b0a0914040209030a05031803060402010e0108070207090c090819030c0b040302 70
    0x900214920202615141a5100c00340b620412100c0690365004900032680c8044480b0030001103221070005000040c6002c02160000b03980341d01a0054651100c0604221030f10742c90b1a110300b00c0c3c00f290600c105840100d100d00130034034038a00542a203a84070b6429164000071002601c81101030701c44540d00b10301c030850320b5241069a810402c0180040e0000c41c000540c0c03540366182ca10301041e00145000400d4000b05960803000c0034254800000d20711039051461000802d80c00e547d030a1161050f007070f0b44600301c094035105110041d00064810b9a0414510480409030340307942c2c0b01c0b8031503581c4240004074040020300c03900c4207010006101920141005062901401c0845d10b80403a04806032402c1d4070100d400c084070b804250080461490950150401341059400a4045803904a00f00c0c1484031840005000610800c5040001c2c8030140c000d01007980500c03000f0b041e10b4901d020f00e602e14001c0c2d41c0d0780c0020301c5211041610039940740d0746084180b4071544a00c046501c024104804601800b00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 406276357 1250 406275107 406275127
    0x60304082a0307020114120105130b03030711102d03060905040506040c08070602030a0806060d0501030b191104050d02010909020f1206040e15060a030506090f061b040302010c0602 79
    0x410010790111000045549410600000d400c0c40b4180364945000b580402214821104c0c118219044490a0703e8010202d004500c20902819030713007803501d81600c40030403110700b03010f075603480c0320040d02098400502138030813205c1c119081d2003403807070b8000c644c030b0080980c2c110510340c3d80b40c0403850606494005455500e462444040e100c2c01d0303409407490b501c02c20500c820720600e42c0d40d4500a244040051480d1454004065124041c2455071000d100e54100050348030344950046170a81f1903140410403081d84c4901d801c9202400588081c803c030249180d03400303034086007403140f0380b02c4041400429040c1403074001040754052490340c0c205d040042c0b0040018004240b0b0018200c0c291b00b01041940320001d854030200d0401c001000980700300d040000c681c4c680c5d4800304803100307078021154140c1c05a42e00c3c20082000161039610050091080c007042010754003000c200611008600070a4580079258890000d00448114900b61540b617400c12003000190b000c0d44000d210188241009410180920 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 406277607 1250 406276357 406276417
    0x30403050a05030a0e03030c06040803041509060501061b020315060a0b040b0307021002090d060f020c0a0506180c0307090905070b04120605101a0c03040302040516091406030408 78
    0x910110b509520114030300340aa0b0f00045020541001600114104180d0715403480d9240d1028002a020b045c000011a080c0a01400c00c4c52207210780820034403046619160010003000e0903c10b07400007a89800081900f6402da03810a4540d60700140244012044420115a980c002411181c0c1c851080c80e000140440000083d0000304040146c4a031a40740014019051070303401210110000e1041142803102d54400600b01030f51502b0560014106c01c035002481c009109000045000c1d200c1c03440b0310010440d0015100d48201c0f07148142201500724101810740c0c031101551541da0541080c602807000784081d82c048103c107805201214080d642c0d8002104565000750000203000005510810502195004a940010350b031a25003032445d2030407180154130f603480c4900315000000010070b0711150608200b40e9020f16001042000141800094440f0030b6603003050680200c1d10b0410000b90381c60038403014450303040000d805203155607116603c01219901444001c40300c1544404800e00240080c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 406278857 1250 406277607 406277623
    0x100f05120c1216060c12080402040e0102191d150c0a0209070804020108090d08013303091b0b0901050307020f160602010b06341506030b0903090d110303040305 70
    0x40544284403061402d0031804001da000301d005d200c1c1c1c6040000004140506120030f1a00a140c5007440d500d4900c0010b02038101540301c90b80319070001c02d00003030701c100100c40000382c1141910760f104162429401420014a0214100e074400040300c80b00054261103001000ca031070104065030003035150369000030a520340548400002441e058208000c5580050b01d064102020000901c40c0000b20031004101e0b0805000e90800c5080c070900e040c0700b008070011480401d800c200c0781519030f22003822005009005076031059175840c403008036610081c0540503801007a55a440c20152401921000541e82d82c3d00182c50340d0f086105001d4074400020051000000d1b040c2280da0601075a40340001c000c0c20b69006498032480b400d030405c10a5001070900a0221001d045121100800e80013214100c1000a112a02a2410841d000d80a010012035409141501e00c5050401420f07200c000e85e81c0d42d2030207103035002500a94281050404544034500c0f4a80c034200040c1100d00d030649940c2e41608005c1c00d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 406280107 1250 406278857 406278889
    0x9021c090b0619030b070909050a1407050d0f0f0f0606050403030203030c131502010510060f17070e031c080f06090a0e0106080124120209010303320d05100f05120c 72
    0xe91f51041c00f40d030545000b11904601b044109000500c004c1100743c030b002002070071980510400040760504070110f0303002451070f00d01d6400200300d5603951142c0b000c00b5200c0c070300c0603120552410b0804109203000f0400e8809480c0c00d03500940c115519810500402ea100c00200c80c44416003000018084400070785071400c0c203c5603400070510741404040700c000504580c0046d03040c098082c50304d14980741d01c07910000945030000030300c141d291a80407003078406001610b021500340c003400c007040e44808840d403585116480340782d54000c1c040c0c0e180760144280d940d041d500b15500440880126010b12000c0c2c000c9504600a43c000007415541c4e0070040782110003031368121915200305c4c0101076140750a81d1024009000d1048089003042d120350008551001c14040202801107a5034108c2d07042c5802142d05503115003401140c00750402c105903c0a03a904040e54200c8805d050100260000029007002c03012900741c0c80200f2642c50800c020416014010300c01200c0720710804150f030300340d07a03941c1050002c1c0c1c0718 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 406281357 1250 406280107 406280117
    0x30706022a030a0816032a060f0905070f170601060509100908070906090e0708060f090c0d0b0103050613030f03020f1e0405031c050d0911030709021c090b0619030b07 73
    0x1d619000c6c1c00300410340b1641080191001f0240b0b1038041110344624015808600050b1803110022004010541d00001500320f10502d140801c044090500342030585940b01214103608203020310741c1c0d6548009000342c4000440601030b0700c0c59420040011990440107040111106031203c168615022a0b60711003549162900360402443c20144906103107411454080c19206003410b810350b41e1b412001c0c049282e405070003400201100340900ca211900d030ba0003080b150500b03880c2d0504500c0d6078020b010030b417284e0003140c01064044402c40c0d0a110810743c584c803003540d00f910100b0260020f4000624041e680e00042003140707c40c031000720407501e841b0900c0020343d485a00700814107151022102c8009411036540d1480004641c201041d14000380000401244d500d00e0342ca00700c1810300b050302c0710f550184120b40000c1407840c400e801420218120701705002c1c035541c00742412401c2d2900128050030961400d00881d1007800d0103070200c6e00d260400f4003280e540313641d240e541800c80c1c40c04a51440000c0d07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 406282607 1250 406281357 406281397
    0x9041407020327100c08042403050f040b040b1e01090e0705150d0203100302030a0b01030203010b030a0812060f060a050406030b09041a041403070c0302030706022a030a08 75
    0x201c00d2043d10340040f44040141c0038441a10041440c0d42c907541c440d00240545481031801b001318103422500980105001c0b03140c100449188448011030031000200804d05140c0040d0b104000c450740c1d580700d942c000e107550724180c940340c4401c100400090700c0150110344603007180d00e6100822085a008210102c00040c4603200903070850f06090f080c0d01f04034880c0c02c2036410500020b82400984180f003400103401a03480e21000144d20302504941d0009401d8021005108188201c0c000424100c078001d400a00800040d6010551604c11712035004282c0d035001d011500300c1250303242c00c542e4810005002c4030700000544e40002c4154210400c5000000c000207014400107600d805162000101a02c000c3d2041c20241e88001d0142142d81071030071100303001400101804036a46840741454103000c00d41ea5140d00c0c50412400c10251030000781e00911917500b001940500c0058034a1342c100c498940c640c640150101b0145110b8407511015516120341086940070030b2140009000001110544102207 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 406283857 1250 406282607 406282627
    0x51e04030c0609020402221e08070b21040602030915061c020a080312150405014506060905060a0e0d050a0516140a03020108060105071e050a0b0901061406090414070203 74
    0x60361028840107600043c0b00d608000214001502e43c084d03c0301010792544070590070128105181e01d6044407a064001c0f03305010601600382c0c02140152103050030f86140c8030702c00040047d080c0d804e80c0c5071a04482c0b280f8074a101000754a082182d8188010514800c495540824900d15004409004000b014100030b204405840f40d2030019408025541441030b1761402048c2058040d4070111080340964056034600c80b08100e50106d0a064485000700c0d08410801d07020300010100c0c0e0047c1404200d0030b403004035282ca42001a15511155580c03084080361414090220035001f01e13008840503c6041900400a00280640b0001c1098001034640703081ca0002c400344031400748454240500d051010a0000d81d80c001081c9503c01d00a003400f503540c03c902e290000414960804131000d0840ca0742d810303401c1000200c0c80000f018000c2c41d1110807600c90100d19400c807003042c450801c0d82d4919032036008181c01c091002c0c00789002c0042001034000c00230805014000422a40f89005820000b485070f02 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 406285107 1250 406283857 406283879
    0x310080601030302060f04031107030305090a0801290d0609030314010e04030206070f0c02030109050a0218092a061803120a121503080409051e04030c060902040222 72
    0x51460400400455145842c00b940f6110b0144c4801c904030b0040000400385801104034079200d0301030504845240d03030303203080c0140b880d0000c0e004148030b4a080c2c0e5000540345014059051301603502c090940c005461304007400c2c4a07692030b12242c0d422903a051240d9010440c0780c444c011180e8000c0c0c030007044131030403210a4200c9901c1604110100c041540911020075030000d074941d800015400c204a81c110000c1050b00c81c2124048000d41c5076090070000010402c01182103e40c6500c00d5030700c0e03040d0704001f030b0308001018022609074455502501c0041590003a41c000b42c0714103401c1c0403e4031084158140407500691002074021a401409800e81820341401c102e00c4000a100320b00c040c0c1014030b860b100410842d8082c1014041d04e032608042e241465440c100d0400540d40100b065540701d0b6110240ca01a00089484910b482022581414080b000c80c000d144556070558a10701980741c90341d03901008060140050f60031582c2070100c58801101d100255071940045910143c00610340600850 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 406286357 1250 406285107 406285109
    0xc0c0e0f01090e0604200a12051204030203030a1206121a0a110901030b0319210203041203050d15060309020f0315011502100c030203160801050a06050c01020d0608030310 75
    0xa502ca180080c03048525002181c49500306601105880162928403504a140928092015072200c3c41c40340000d07071100a0414080d010b0300c141c0548480f002c050148d102c89003d68880690150010030050b01c4991090b01c41021100035003000042c0300303440e681501403494204408503851038086409031480c150380c00d001d90b440f1060b02c01c1031100071511a548085802002283c605050b210500d41400d40d4082c0083c025074980b01030107000c8003c00f0300307101c1001003036907003000c2504a141c154084228408000c40d01540d070040366201c55444c1d241e40440340ca80c415a9202040d681ea080540c840020720b80c05440203081659010842c280b081c010003040821038221079100313138055840720800c104044440d904480340b641802c84401301c0d5100503400d180400b00380990320707442c210321845a80d400d80d010b140140e4100b6401561010044000c0d6404c010a01400b540800e4030341e070030003007039101340d00522462110f8070000d400d00e80e8960190017034403290742200c1442d804c003000700039260b00f001081c40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 406287607 1250 406286357 406286369
    0x70305061b0c102a1d03070503150618040302030732030a1205060901050d030c0b09061b03040c1e0308030c0301061106100b0a09030515010e2a07030c0c0e0f01 70
    0x145086508002a000350b003084061801c00c085c807595000107a40c14401e20004100103020381341013004c00340c1c007034420ba0021039600d8442c0c3c80030020300070004c03d180d0f0b04911555040d001146014401e03126071042c6030340c60080b5500c41c0710481414052407201050a09240c804000564490400c0080138001c810000c100304001d500e450304229050f6a90791840741110403e40d1030b0b458840d02c0b824102c1ea00351480c1d801600c0c0c1c5402e4424407045003400114584114098802c184000b05003890064640c4010b490150940e150354074288003100715220b1002c00000e400e180c80030820350301d03501e11299400c02c4410035282c0c0c3c004030041100b242c1084a85040c0070121010f0070141c80c000207110214402402030340018200812602c488500404954006e990020200c0740e28009549d4035038900b150901800010300c44000205480482d00502031850703451010081c203049180c1d880c07400060700212004c2d0b08000520724a58003245068080b00702425140c040188146007690190480c2d142c103a20034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 406288857 1250 406287607 406287671
    0x302061207020d0e011e05120c070b061f0819060b09150a05030112060b0d05100b10020c01081f0602030c010e060103150e0c040612050609070305061b0c10 68
    0x2030000e45c1e0307001501c15450328002c02a8020460552000c90f040c5c0940c420040442002d80144100c0703000d8080641003541c81a02c1520a0b551440280107003c841868039070107000c14200c4460001d40600c900b40e6200d004c0d210444058460020b548080d29036031f070b00c1042c8540d8001a42c5960b400e10400d90a4504a40781500c0d00c1d000c1d04020041451005215003404111700401240800449d5040b803802e001006189243c600100e041064440c0320700c89542e0002450a40d0014860801203040c2100f42c0440d005040900b00010065545500050154020380d50715030340582d034602d00291501c0a80100c8d401961a120304280d2031b4212001d648401a040d8040801040011117860302e0411885d02800c000c02c2c5480030b912842d213040d2039400030640c010305003100416001a181400040c0a0040c411203459841c0c0e402e5003515842c0c140006041504600005090703408101c000700d1155640307049451501c140b540c605820f01002c420003904460300d60600707860705001842580c40a00601e114 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 406290107 1250 406288857 406288877
    0x503060105061e0c011a011d090109020a02011b0f11060405100b04140703051b3a09080d06060e0901090e01111b0106080a05060c03100302061207020d 66
    0x81d80700e00581045544a41064401d56103103507180c4155201003118500a001c011480100034480c501d1543d4424000380c00100e14060004e023100741c81d02c458030041d1014140307900341841c2c03001a40c0300b051240190b648517015003840741e51a640300d121041d038075651310360301690b4040000d16528502e04102442d912500c140808190003141c10008082c00320000103003d008400810054811100143c40800820040180c03141d05600101e100c4d65001b9500700300c810801c001710741c490240b0310036118404c04c0b01c0b5089030400c0780902402c042c0528440b039410150050f4983d42c080e1401c103041200d460300040303a8290f040c9410f000703000c0a4022030418100b50608080401d01300d500511a201c0300580780c1410000c141c0b004c1d40450704401c860031000303650700542405240d0394103107046910202d44c030b0110001030440c408140008096400307005080c0c251a90a030040c500d03007000c0e001d03a028400346480000141d4030b0500030050041450b000c5440c5103081440a4141035007001d481c0240304120714 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 406291357 1250 406290107 406290109
    0xa120c05030a03052a0109060608071e1203200c0f04091a07090b0a050301170102041203180b0412030801050913021519020703050c15030c1c1505030105010503060105 73
    0x1640c5c22620101d0103400300103c0c132243c203817464080100000d00c1e9443c0400308014880c1b00d4004d80300340d07922642259440d46e515500c2d604030700c0312854088181c84164000744080540008284502401380c034065500e0007426010408441d990724800e04568030194070f480040c248401010421541103404100790b001d45d4403001304107103000051b071a00404400009000600039505036020384034134070045840d4407040901509950003030082014049484210510a40c014000c54003034078040c0c101c29006541581e001d41701c502c244400b06808518030480810703486181c001400040641d942e5820400c041800e01510b0720006801c150b00641c0b4100800880300302e0344041c00300700340e0705a6054a07100b21170f07015400107001d142d1080b0034002d03504204800c0306900164400503680a4400e4551003020704c01000454025000d080d090702d6014000142007002c020050142010250301c0c0c104011041001d0808507800a00ca1001c107845141c02030000303013800d115040c0500002d44c010005941440 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 406292607 1250 406291357 406291367
    0xb040f2d0b09031c0f020f03040f050d05010f0c080106031b02060615070c0308040f09060e0a0c0e1816021218010c120201020d051f030b09030403020a120c05030a03 72
    0x1c001c140d0451000101c1039042d0b1802c003c403019501c800002005040340b4801d00401d81c4104181c0030005100704549106640c2022013260100c402100000b2800c0d4070380014441000ca00038401c3e5550b542e6600105c2c904610350103001101c61150362009050f41c1416009000c0f01c1c07030038010102d5002842c6000300c0c00341e0002a0340e500820101c90248203611343e50303074001d0300e80304000c4020004143c0080000400c2081c0000d40b0a441e18198031007002500e4550600440b00e0511607680d040428001182096040b54402c4d28660302d9858002c86c0090b204011a11030b843d01005c0940c2c0c40c019800304000f2104928070a00d00ea0414070142065608062076503807280a8255100d440c00101c41c01e48045a00410360810000c0e0f00020300342e00303100c07034190107070003500300d5070280303402c01d040000003021881e0b03074461169401525101c004489003075440d01260800c000f850052a88420000880940d4a015a0390020001c40c29a590940c8251403c403c0c014078980c0454002c0c1d011030b81110001e600a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 406293857 1250 406292607 406292609
    0x280c02090a02030c040906120b0915040b04020a03060203250239091f09050601120906020f07080403020406060e0a270905031207050405030d080603070b040f2d 70
    0x807000d078880e111044804101d100303030341c0280340083c80e04a00003040c035010580b101c00f8501910045410f42c2ea140311298030792841801c10030805800b0000a0006106003030429000b500260044c1840e64880d912002240c1c010b8502c1c607a030345c009010010303400305001c58031082e9810610141c404200c24020032502c0c401c00e0106281d0040c1606070b10040c40c1180f280104069100801da01341c141450a00503400c4107100d0303141da8202c1060640402c060708140911401844180d44085000c04401c208000400240c04122443d40c1c08003c0d8075000c0b0150000342030741600540300c2c15a110720b94410081143c000c3d600000034070400d0b0041500f241d582c00c80c580100c91000c0c0400981c00148010a146443c804409250240c0f60502c0c50050100010140482a040700c010004a031a2900252520701480c801e25600d0380c40f500e03050140340d2050440340c1e0030240113000c450102da03d230028401d458000e0342040040700d02e00c40041012040700c90103065003d045c07040c420340e406000d00c03121a850307840d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 406294964 1107 406293857 406293871
    0x150b03030a05030402012f1522080a0509090a090210140f0a030603122109050c09040218090618030c070312090b280c0209 54
    0x1000001c85060305510744a0a055503a42c0d0700440744082c0c0348148168000c0303100c0d20801c00c0191507484140045000000d0321345904881d00080c014180140304810703c0a00d141c41c8215489250301440719a500b10f40c100e45e50380000942a102840380c21106034000b00001c0401210548980c451080103100b00d5941a01b00c1043d84112048604a01c2440c3c1c4007608110b12800c000c1d02d03000900f40c0c9906400c0221f0242d42e00d459082c2c1d00145102e00700045041129251400e13400002160845500c02d0020041c009258582036902c00c06004490700a0001502080035580c400b0354583c040c000542c2550168a4500b0109460303d5080e90802490840015001d8400b800030083c3e03000310f480c83d00101207481c515150400c0a000c3d01d034046040c80014a804182183c8101c010250030b01082d524100008100b001d1000350802c501390b0404000508500a0060fa600c1020f942c20082c = true := by decide +kernel

theorem cover : BRFrame.Cov 406115107 406294964 := by
  have h0 := BRFrame.cov_init 406115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 406115107 ≤ n) (h2 : n < 406294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
