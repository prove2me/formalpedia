-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5387
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:42:03.93308+00:00
-- url     : https://prove2.me/submissions/20a5b0c5-edf1-4d3e-8ead-6ba846b8437b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 968705035 ≤ n < 968884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 968706285 1250 968705035 968705041
    0x115020111180307081b19080a121803030f0503100e01060f1b0305030402090c0f13080613320d08190b0f2b06060503120f040509040302030f12 63
    0x50a004040042040900a01c24503603030030003140307800e40f80a01040c016640041c00104c0205032039007d070018007002d420b440035210030b810008903814580d40c1c0440806d0802101d51703002d82d60a521002102c0c7c040e941d003036800c956140103c2c1d86030f101800c40001c02084810225a00e00003070040760081400e80c590b45903482c3c50f42e001415802044540c100071075912032013500801c1e0400201d81d0b0150341151800c0d42c3c2e07074030200c0f60090340c0a2110542640180410b621426510307070b40b8842c081c1c40c0d0300000c03203004d40d4800030708107030711052a6170083c0900c90b6920189008101c40c46510a00110a00a0f982406a0303102d030600e080000264400000c03c00801d01195503100c480c20503c00079082c07000d100a040c500081200308125071b81c0103000c2c41051010803890440460111184612a0860313561056030342081009409107000e05031190095203084101004001c2c04c030303000d50710b1070104d46061034909401c0003405100204183d055000811400144885600040c4040c044048411810f03007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 968707535 1250 968706285 968706289
    0x6080d02150c1b1f02120c09130507030608060c071a010f030b0c1b101a0f0409081615060501050906180402090307030506060405100e011502011118 65
    0x30001c1d070804122003400e003060010302c0310410304030b0301c903040c46140044200340500c1d42a8034000404019401c0c180c0410315022102c8416002441030321032000301c0240617141e1041e40410303803086c5201d21307600c044010210a056503049d000a50720040c641400103021340e5555115050034000c5840c4400d00b0310000e52181000b4101f5070480c2d00550510361415690305086400c1030300001404081c1c000c0724271100044141d000352003210561000d601042d2502c00c00c100722195540480c807240440350b81886021150040788850060092030021301d2241c80828034003c1c04000c1640340000d548216081010710b00540d800d9040c00c0030a4490304031120a0b1440004200c100ca0082c1c0005042003010070081d40ca071b80d00d145c243c6d0307d050304850540070544088400180248a14940742d60140242d4000109120020a40718480c50b41501d0500c43c968640e14029920503c0340a0480324200803401480700d83e41c210940d00d000f1442e4000020408804a062001e54101000c030b0803003650040d130840c07024 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 968708785 1250 968707535 968707543
    0x12040e06180403020a0f15090302010228090311041d0a030315030206070803060a05030f0a1112120d020d0207112416030c06050c0a091409040312020d06080d02 70
    0x29102550001c15828940e9000352116200350b0060980310b0420110007d01c50301e000c0410074a13144060412152082d445c010703000c1c0d0070404079110540c620f00d20301800e01c0070007640455130300040c0c2e80d03620140d41076030f94000a01c0000c1b5052500150b0b00c3c2047c100c0090840003610346000350f48010200300034180307001419580411107205451480f9501040180c64540c03d0318001540202420384a6175401e0200d030103130f103165000581c9072007002200c481071000440c0785030407903005105044c0f0a00464080c07196a4010140560881c1d01c906454422160a45c02400000c844600f01514000d9003900b8142603802005090310200d40c0d42580451500c1c0901010324845052001c0ca4010358107804400c40c40c0c06841290000d400c03151012030200351103812040b0496503c074008001c0b60425110344031141d0000200720002c66024000071a100b00c400d40703074505451004000111315034480d60101da0404401c0c0da0410126000d000c20203103008580523020107041000020240d00c1d035140002454 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 968710035 1250 968708785 968708809
    0x61e01060207062015042603060607080f0f0409020409050a090c090b03150c030a110c0606010c0c0b03070c03080a020930030301090608070509060f04050912040e06 72
    0xa542c8505410000d07250400d200d100d98140000900c0901c0340c2e81c4d00040e00300824040030143c1c0811400411007080f1031405096800881e000364008841071000b2802c0b590300c400c0d00d081c0d0f48641c3c10f000310f2000441c60b00c010445e02e101d0303005060402820341038030140350300b10750400e1031030b50b03000b02c3c0500202d4217612499620030707905041400018004c0d100c4060000041c05410040d071f0325225800b50b035403001c118507200403000c0c0c0d20303c8105140c210307c0c0001542094400c00d00e01030401c00e807000001e02020980b00800c4051006e04081d4484100545040702e01d4581100c4079101588005881001040618803400c0d0b50740f500390b42d104840c94010003c06006000303a05242c4180560461500c4494210740d101d60703034400456080080c0350f460341c4444a6143c40710b8891000200200c0c6244040d00000112164801140d1459450700304218440008545081d0004401c0f40d54600c2361030030b900480e03000941c28041d40c0210820150f0b40005610582020300d48000d0035040c8003841c20081c40c2444 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 968711285 1250 968710035 968710037
    0x61a09040c09050d2015030103050c0102030403030914010c0807060c02151003030e030c0628020607120504210e010809060402010e0108090c0a150305070f0e150408061e0106 76
    0x149450402d0b002681198507a1405051011815403202d800c007948100d20141850041c40c0100b440e06c0410352440f86d5009000844040c012030007501e43d80e50001043da000c2e03e52540320764190b2810005c00021202181c85034174100140d54103000c010600703600040891600400010400a1240001030300d00300300074400349100e00b124820856500c2140031f07030740192545454008803005005d000640340954540c00d4036071041001030b80d00b1810102e115440782d0240e14000e10100520f0075402681c603480b040354a00042641142c003c500017138030b030f80225405442126040e1a000c8085162084150341c614200c000c24000041d4110039a000b00c0000d9000e80035800401c840c0c0381942c00213000748100300c5540c0c1405010408600c5080043c800751413202800380c100414240c2d10824a80c00c1500341c03586801203031a010108006038400c592030310f01142d890b01d603012200c4c2e010f428008583c1a08201d0720344200c080c4404100d0102c2800847d018692400040341c078840c041c0a1070501c1c0e00103031301c024 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 968712535 1250 968711285 968711297
    0xb18070b1611030a08180a0306060807030b1503060f071209080a022503020d031e0f030e010e06270f071409160302030c070503280f02061603061a09040c 67
    0x10300008106c80c2a07012a4007410204424000441d4101e100e03900001c2c00d45041c00000704078404006400000c0301c0c0104680043c948910144000d40054950041d405401800002e498240c03c640d8040c0c00c8030301c0303141481c4180083c10070442100c580302c0c0201c2c1c14080009032441d43ca60b0422500c01c070220124008030144029108802c60003009100003806141c60310703c6131007491b009501a0388400c400e0b50441c459002c0c1d4001c014081c410b080f44600120745000b030040001c00c01441600550300949008140d40d40360b48680038588400c00100c40c8551592036080c082004040c4268084840c4182c0148411030408440c007500081d1032207450302030b030118410844071002c080003800d2181c8450400590303e8941301e0342c075115440788083c09402ca22000450b030703821040294801e083c0002d00d02aa00004c0d83c110400c5590314034100402005a01c40c50200d40021002e04203ca8406014200000c001d40d54038101e0342740b85024420f50003402001f02c0c0708407440c01d09000c0c205800c21945860 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 968713785 1250 968712535 968712553
    0xa0609050a1a220510110a0201030525090f0b070b01060c0813030b070e06160818040c020d080a1814010b04050a060807120b18070b161103 61
    0x110700018194459509280220101c000440002104960b59904840300381420001500d074a003c4005080c81168000c00c1c074141480c11452099032426050310400c4040e040c0780011b038004402030000034014168040f50501c00c0b49004984d114511900e0003180c86a009451510807104000c03041d550007201c040e1400c1041c14005012031004a040d1400d03401c182000c003005042c480d60900505000455000003c03001000748000400311a1084c03009545030303450390042d4001d2090714002d819840c009441260b400400149110340a00a100c4a04026000c00b045d8030000505440a54450344050782041e810701c04210303400312045d81c1c081c800c10b0b414000d1450100309400341c121400d00c0600a211103c00301540074000f900729000587d0000e00601c458246480c9a00007803a081c407174112030740308248000483d00c2102400300c0700c02d5042880103403550b443e0b440c154001c0c601500186021700408001081d14003000010703000491503d17403401e10010030703407030211203040a030407143d8442e5210b5081c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 968715035 1250 968713785 968713789
    0x1709070e2a070f0f0c09050408040e090706020601090b0103140708160314070813121115010803030601081803070602090f01020f0d03020a022e0c1407020607031218020a060905 77
    0xc0c5460303944d00040b0405400c0f410300300f0700701c511600d8210030f40032400c041c1032205005c26140500180da200c404e0700307950364442c0200386541d10407621170740d001f681040e401001420001d80c06011200410704001c07913602004103101045a4040b240a8080ba5140c002c0c0321100d00c2051940700b501d0f1050508102d080f444103504d5400000091114040010203000151415006444010703420752100a0308074070301aa0b10003410f4400308940e130003c184200090b4810f10030b05088420b04988030720b4082e6185440c0c11004440013040140010000c00307080e00d21111407442080240021401030600580b5107902c14100040351112420003411580000038040103440c0206201d46d170021913040040e95002421301c16400c205441200c1e040d20f00000501e40143c03214903610380320b862040001081451100541664404039139615550030100a0103002c005007400d20040a6503030107824000218004000000d040c1da040085c503450a1090103000021414810001006403960703041440955081c500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 968716285 1250 968715035 968715053
    0x90f0c170a020a1101020705061f060801050609011112220b0a08092416030507200a0816020405060a06120f110408030315010801061709070e2a07 64
    0x200c841c01a81c0090b00315582030003003444180c501c0304e21000355203500035030070f20320b85034501220440ba030340d0f0308002c3d010700ea43e01202c0c1c05400d4071207986440d101e590800c001d0102540000726800d0501500c1890482c25603070401c4000c0b140501034041030f948405d940c1c1c501100c500340d012071b0f000703038892200306001d1389003d6403d9480110342440c014a6a60305c2030b500d10701d4011211419040e2501074001e6800304a0a951900d1041c00301c580505803030509104205c003224011211030000889010544804441c2440303513000c2100501c045500c510b0090321030149603408aa44410320201006018085042174042e465100204542001c6024030745500a81400b0051204440703603a80c03019156500c1c80707983e0001c0c05400030101c442d600d607920754001690701e44c001d4400b0000102c07042018100c030343c071981d215030503510310703664406002480d620300c503604502c003030012152406421070108a101d0a1050303544a170341c00d00150030440440046240500903080103480425004000c03c10210341914 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 968717535 1250 968716285 968716291
    0x203122703030a1205070309080d1d030309070e07020f030a0c2f0616052509060b07030503070509101206050612010522050702150601020a021e030304050406090f0c17 73
    0x1004c04146a80c03400c01c21001080d80540080c541040403c900e840300d045a032151a10260610b122581803080c045405d98a00003107039106856404002c1c18441c0c0c420322200306800a10034011600c03980002d1a001e411900407000c004005105080400c06024442c030364032034401500c901c0c181c00706200440c01c411100142414a002c3c0e07034006101d104a00c15170041d030100c01d42200507285081700a00b8101240b441d03000c0004801c0101120104840e030152003000102ca1403084c413a460103800341d40c10f5a880d00000d242606201007400140150745030400708107041c10003030b070704e48100c400b030102540e0440750642c1040d4020101401384201a000005505043d40c00407104070040410405003150b008140c0d03524850703a103061a0500c4001900025011010015480241d00310342c1c90000499a030001100041c1d0f102110700c2c0d40c001c1301c002c15010484e11420242c03d81e40f8041d1190003050551706107a004460043c0c0e14901d4500c009020f20483c00c0804152030a12134480d8401c050044200003e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 968718785 1250 968717535 968717567
    0x80f371211210106141204020d0206120405070e0a020906090d14071206050606190e210f010b01030213031104060302040e0a030906030c05160203122703030a 69
    0x4030400780a100241c01a561020603a000d140c884840304841c4012402082c0f1078000810070000d000505988800b050729004241c441c603904d01c6a07500d4080002d000c0070104140d03004031003040792178038000d00641a9841240102c009080c003a1406882a0a00d4402031018100310b02c1030204042c640c5d50b21084540c5050209c668078400c40503030904010034400d82001c0c0000e0b202d04940010920142049000d140d03004e50420400340d501c10080c8480c0d803141d80700c00d5200e619456013110159016406030700c4030703510261042c003c3c405a4094074940030941006000340b035025520200e4840001d00608801900c2880d0941c10562044d0141449041c01c3c00020102000c5800e00a03090702c5540c010401590000e02c18441c40d9400e6a0341601d4503180401540069601d00000c01c2c80c0b8001c0c090741400c200c40e5542c5514140510741a03d0321446004000c90b4103001e400c940c0c0c3c03000c0032070030b01070b00d14140c1d0382c2c440d460341059030381c01071220780b01c04082280a0782052058608098008260380b0014002c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 968720035 1250 968718785 968718791
    0x80a0f020612180106050a0f061b080f09241c020d0501060509030c01030c081504020403120206071106040201080c0a120c0f0e040203010b040b07080f3712 68
    0x2403000941501451940c10007010302401040003a0f000c0581c8110001c2201c0000c12074540c844040c0003460003180141d50000e00c043c3c104000d6544501030307d0203800b0a0360145403208800c1d603903500e503c0d8420f104c0701c440c041010804411a02d803c0b01c0d00d55902d0201c03205002034448014030314005015003000001204444800300d01d408085404440c01183c04010404c09913840700f0016255400103500c8501920450070480c8155019104066008003541c03912001555540b07000000403034440260b50f00540c080c04000005058400542c1078000940c0140803a441c0c5264000c1c0b06420201d03242e04154040818080580d0304a2411b90300103801d00869030795281103140588903055407103181003440d407502926440550340300c2d50b28001c90005d961000c061481c800c04000982c08213000d1007081032800c1004000300038143c0014902c032480b60070414105840041e100342a80c20000d0848040c200032120903001140780064502000c49520b4200340f100350003480240916009010595015a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 968721285 1250 968720035 968720063
    0x509010503100c17010806010e0106180306020c0c031002072114130506130906050303130509060d2307120807060c09050307090605030f070e070e0d140a0b10080a 71
    0x44136070070b0840980c0c1034569000107540d6580c5100d0341c1e00d50074401e0041600000c4004203485229506e030351f01540784a03200004581c11501c1e004000d41c0040c0400c007140c801c21070414040e440c01d05c540020300400d6a4010789071211400c0503103040036010107200009900c0e80c82110880e4100e207000050004c58483d0710348900d40c0540c03400824078241c01065124502003900d03001c2302003241003402903491900c02405155134071828195280940858410303049503c0c2da046c031050070407414265100c0401008925104280c0d203807240c1d0740c00c1d4180420700354003240e01038204070041000540000c0180f403038074011078074258880411038010071f04003c0c90681c5844c9501000e80c4507001c8503025260040c19140c0050362400c0c1c020044c06903200b1a0b000f8000c40103a1002000042520300442d1030074841c0e0341700b503910b201d0125120705e104c02400384e00003050600303140803c420310403005c40420003074020f00d640016810004542c1000414844122650840138840c0c00c101044900070385030b1082c4001c09a030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 968722535 1250 968721285 968721287
    0x11011a090f0606120f160f051605070b0f0c010e0321070e03120a0305011d0103031209060606051c0b030c12010908031003031701080309010f0201021e130509010503100c 74
    0x84580c500c41075400c480740c07040c40350b1040c040111034046c1e03103505903d060308082c005050311402d1120080e0400b088040c4400240c1101106458640314411b0099404590b01e505500c5a03c0e04100c164030560a008510f850b0840001d1040c20a050601c1d401035003850720181c1c0130502035001c1e00d5050368503810b52003c0380c00180200a021020b181c01000c0d100a44030303030b602e0700e4550f4004416440000c0e0400000040700f40c0c0c42007070014521845c4001c4201a821520240e51a240280d074111915603036000510100d4254410000940442e6a071075036203010b5250b0f52500805114040425140b4002d000207030342d60006a0f401c0440c90650b600030207804000d04940c0141074a48024052010001c10000b0700191100c004050300d119450b108501040d4404195100074240514001d50f4001c10540180358046c40104074401c000344000741c500410080000f002d141d0703000c100d686502011655540c9106000f020780003800f02035400e00903d42c54200000d03980c40c240c1c00208103c1e0f961b480c45d04940303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 968723785 1250 968722535 968722537
    0x6020a020a0b0411041401120209060a0e040c0e0108010b010c0b060616230a030e0906060c010c08010806070c0c0905070513060909110702100e0a080d11011a090f0606 73
    0x2440c0c020304200000e00d80307400c000c46415008070741144510314200c8140824031b140305246d41a1802c41548030401803040e401c0c841440405090fa961203207119400040000d45041007511613881031000c15134851134100000044801070300120966410906002c20a903441200300c07512581001e4629050746460300441d201d4850320300c50402c0c40d50321800400601407100e601150f19044a40a9140945148903881d2514000240207001030a08554132140d4908012140e80001005040e03615081c00a488a405c40d80e0035484000402c42040041200038418809564821310600b000b8901e1201d1f65106050100c40c1c0c05910081a910000720313100510401c01d840c1e10b00d68900301c0d13980c16511070720040c0c1400401d20555082e6803d0003909450890f500055517903982d4082d000703400490114805440c1e04019420590f0845401e1030700040d152004c1209020020090301c490703850032106403406003960350140c208a91154007028240c442c0e2500c00246911804140003414281c5658000482d2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 968725035 1250 968723785 968723803
    0x4050903071b08013e03040f05191415091228050301030b01090912031a0316051c170307020a020d0803070e1009050d020118080616020303010b0706020a02 68
    0x5642c68121364480c0301240300f44003020b41201105100e01501c9942e2410002c4801c09850071602106101040008600070f0380c80d40c8c03984c070550030796010600a000e141600c456520b815202100c0b00081c0d2068a0428070184044500e480b10b184c081e881d02c150302c0b995416407403074051031101001402903204c1804030102c400c12489241c00d0700f0b001a2140c4001c081e90000c2c00203681e0141c4500c0001200744191166403010741d4000c4000e41c0e28000080150700038944520800ca10500710070001d0302075030b070074496003100c03080081c003100c652401c000238000078521802c0d0000e80c51129020110128518121954902d01c0b404803003556503861400c203c0c01c003810f10314000d4000d91140d40c620300300050000550b00ca4005a9100d00d2a2000481040100140c4606940c0480c0c01c207802408603003804405658510b0040c14405401c4003a0034580c1e91b1000c40c2e40c0811483d0f00300d0340134020314280310340106180d0010762000754215410000280304070710600030300400181c0c0c006091100303030b4024800d0501e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 968726285 1250 968725035 968725049
    0x15070f03061802070b10082815150e060604050918010213180903080406020904140c070b0f0708151f020105070e0d0b040f0f150c080604050903071b 65
    0x44804015860b402a4101c41d40440b0101010300000f259030940110040c01c4038506801000111072135502c203003030602c1c148038011070048000300c80c40106a0420496130307480300583c4009800401d44c05898502c40641d0019664250810f043c80119070b6034101740c40c1901d104482090346600c6540a050140265000112a550000c6203154500341c084110700100da80e10f60484120100401080d4101ca0100790000d01081d8100e01180c00b0031002da0107050003810142c03000420014169158400c01c4007156514460b07003001038520104070711120758a800062485598183e401d000c04054200c2d03200410b918100c545800301c0c200d20380d551170038070851a0310f0007801140c03000d15030400174080c10080310300001052021141003503904041ba0320311002034000900801c1f6481d250340e160641804000140c51012029950b6004181e820003c00001517011900243c21b6404603009081c000e801011203114a103000100001d07150048102d4002c1136100d02080c7d1405c8031040740503000081608501c3c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 968727535 1250 968726285 968726309
    0x3120606201908040303030b100203070b0c0c01060902091503040b040b04060207080d0e070b0c0709021b010c050703080105040b01090302130e0f2103250e0301020a0503010e070215070f0306 83
    0x10043c0310360b1800a00c10f0300d000759020700c0881c1fa00014402444c0003240c0c4040107074001c016400c089038240310202c3d0032000c442e03051807400c8140c0c4207690030f40c0e05980080446540c00104444149002584190083c5800c5100e80c1145495201c0c44000117006002404c1d0203c883c00107010040d0341e50440341d80962201880d610760b2080c800c481c000b0000d0801084003031244180105030b4842d1030080e03c14540740500106509820002c2120194000d900d4111210700a146000d084500c03c0c020780d40c031140941d42340340d1160310500780103108440603881140a84d24201004505076404154201900d0701921030302d4900c1c5001000307100409804086051038050926140c10710000492450b41c1401d00021049107074082d9803405083e48801c2d5400d181c44951404100c0c0b410545401d0310f25a025281000800200f08401003402e981c0071400080000f82c000005100d805441107180d504513142d072004100840396982054903a4901404030310602001881c04a43c803803098000c4000740041610f84 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 968728785 1250 968727535 968727583
    0x2040302060319050a11031602030408030403030e0a090e0a0303180c0608090d0315050111070305060f04060c050733090f05150f0f0a0f0c0207030312060620 69
    0x20041803000012000c0c02c0c1c10306010403201c44170740c01454911303004410810701d10384408005000140080024a0a43c0024440021200d4052018000031802a00ca139606501d52900300085040a60403641d0344501c2c0c560807243c1c80c0000610b080c01d841d49418001041501d2140c0d1810b0990b01500c014113150034820b0101c1d55030b6000841034040c1d60551300b250501c2d18116800e03002c1c0ca0740c60b103810a516205100400c4198421000c0c0311a00505030242ca0020381c9a8880d20f0038000f04890b00425030701c01006100030042c03140700d049d201c00018603151f802c24910342e540d502420580d000890f0800200d03150f406a4052006114860f50440403080000005a2134020702d40000090140ea03d40680c503a00f2103608503c000b0203205d0780c4102a208110740d50046a030a0080019107611200b50f5100000e5940700b82d0b41c072a40704028581c1d00100040c910b149070080000c20340401220403e82040c83c10849990031000d040308504002000144031410228113510740841d50100703142020130a0f4038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 968730035 1250 968728785 968728801
    0x1608071e15021c050f03040b060d0b0f1605180d020a0b0406030b0a051f030e0a06140a0e190201030911150316030506100f090302030d09170703020f011101020403020603 74
    0x6034551420f5001100f852050181905456a010b00e4010411100c0100005000185a01c940e564000e900401405a40540340c5641c0d01c0f0042c11140c00241c9602402032041c0c0d00ca8010041c0701404151404034a0300c0e225818480c0030406841006004000540940341190307240040d240240c074100f185c07982c41d1955804000c010380f0070307110380c3c1e401266644004229424004840742c00c026100e5140070703070210344180c00c90007000412415140d90207840010000503006010719950000c80034000c06003400c21552303403012500c640700f00002560001c0c01ca07800c030b698012a040c900c01d40908001610606d07504140302d0581c0c113507090b5503100d85016070070703d044513000d409540501e5014425a1a01c43c80050683c1143c00545d11a40c2c030039102180e0b0401c1a01c22400714031204003902e00444c2850790307503000c28036244480c02008080f800805007400340074074900c110082c05035500c00902030703a0303c0c50700420300721401032594a04001000c803004190201c2501110011035000d4502c650724500201 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 968731285 1250 968730035 968730043
    0xa0317181c0810060905010507030e0303070818040504170f1c05071b050304050d062901120908030f0c120702031c2c0703050303181608071e1502 64
    0x315400c0410311002c0422003195980e54480c003070b41e001e80c03a114003c0b41000010f441c141c210740c804504002034848584400e450600140822501c01c1c030f450340c1c82c0e00080d009800e9010007411198025031800c420440401c00d05102c02040044800b49180d0b0390b0758400d407499591140c55405800502071506c00e5407805100c0d405144905215910708450108041d05102c0389a0000701c090080da100744414843d170315201005640c12413240000080002c00d1101c044d240f92001e500301760b55442c04480042c0c0950304074603902c1907001e0f2010b08200c2e0103160b903100b008602000d0300c0c4070807205c0510700003000f800046c002c6800040c0035010441641c036048038025034030b074002099000b181c1d413180603001d035015190040d4103a48802083d040c0c0c1000704100e001240b13090302403078000c1038403400d03000001240d000c1c802140264402c0d8109404a0b400e000c01d5131500c41400c4d00e15043c110070000820000f88041007580a4035507210141c504800e01413800300c04414a60041002c0003107100d0f80c5920260001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 968732535 1250 968731285 968731333
    0x905030c07080715021c0c05010509010501050411040f030b060f090c071a190906021303060b0307060e03060412020c1f02150709030201120f02130603050105030a031718 74
    0x1400c41d081d594550704603d07950202d084e10b01c030250303200d00400c40d110380c890300365142d40c5e0080303261110301d1540a84070f850a6941c180d4501442e40d6483c001800179040501400d1010203000007005e140504d890051968006944406405005c92401040d40c40c0d44e180c05030000ca0780d0003883c2405506082103648001d0b03107d40c02c101d42252a00c000151300e180c2202c001c52054110b0000901d0802e0603a82c008003416500030210754903a800c00c0b080b82002450700d80380000e940140303c00909102d66105041c58404540c2100741409240324100965507000076500f5803007540200c0510408601810a0f49032040084005502c40c0200640000c6440050401000580c00e5400c41e03140030041030341c4000382d22040d1900b00000b000d5580c00e0025501544010f44003c141d00000070701341041c2c0244404980000040a841000030f1000700700701035141c003ca40c05414100c1c081c04100009c1e5802070032010018000c84414408800080c81c41061078440319000c076451410b43e000307460a41e441c21120b030110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 968733785 1250 968732535 968732549
    0x200304060503090c090402011b0c031203060f080c0f12100207060c1e0504050d03090e10080f0309061204080918071b020907080c0f0c0606010e04051005060901030905030c07 76
    0x3144c460110745041001c0900403034040c1c5525109020140100c01c0741401001e0a4a9140030300f10000300003000b800203082c4641182da0700041840c2000340c0704403481c1182c0d00508a81d4071100a000c0300f40e4801602d07505094085034001d40071003c9456003400d1030300c0100061030700f510125414082c800745401603154580281d039042d44030940b00030015440b02001001030b0020728140004c0c07006081001c0c04050540c0681017050000e6502c4c403080e81e44000c2100c4541b401501b261081040c80c030100902c0091284550142d400e00384c046010600342c0c0500019807440e02c070a100458244124803088031034030a406004421850700c50383c14801241c60070359050001404811031400c0003442c1ca00204629940200a0103a546488508860048020f409060032560400c00d5051a803c400000c01694043c90003a00991502e01d0015101354410651280501c0c148400c214000c0b02c060100c4003607410445400ea11010800c004900800d400d0303500420b00d00c000606180c084e50002000c104544031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 968735035 1250 968733785 968733793
    0x90603121201061e08010e1e040507030218010e060f010e03011a030606011b060b0f120709050a090203100905070504020c060f0a021201140d17180f0a0620030406050309 74
    0xf001100213090342c8140c6012000079031780c40c010701c078450300c43d55203607000101102c003015058400386101d003603480c1c155000c80307aa0740171540801c21810107011003800c2c030b10044504542589804030100d9034a0004010300d1044140007480b03d111381c024014400c803404c0c00f6000300030400545980301c904100c1a80e02d10b101e4410080090340c158828110b030b01c1045c40e0510260060980c680d0b5403400307030407800c3c40250b1141100d28000115154030071224040c2c03024400030030900c1c2c94840307410211000a001210103904010380c00c40507850001c0c0030440302040000020b81c1e00214100542080e079650062640309000080910203200c00103050750007505542c0c070b840420f40342c0324450000c0f44160011002d16000c03810040164118603904003407111005042013130100c20030313031320000f4400c0010200c1001440c045082408081f042001184141c820754404900003107900000d01503002c0c5214030010040d4040f81101943e510304101a108034940d4200e03600c07262138140240c450b41003180d280c0000d201d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 968736285 1250 968735035 968735057
    0x100216021905060901050903010f0c050a03180c03140c04020d0207110a2d0e0c2205060415020708030a020622150e010e0d0806010e0102011a09060312120106 69
    0x2000201c00e00c2210401404980760040a500544143e0003081c1d05984c155038802a500ea81c2d407190042054604290b5529039554023504c0014080712440d203000012a442031000400041313000b00e031401035a4204011005540c00b81000d81c0c0740007008a803150b046070006c00c000d658040241c0140c90710b0340c41380b400300000c03844090a01c41081d006210f1a20403051220b0200a81d03080c5540d40c0d02041070400460350b5140d01d50100c07994a16090b103040d046420001940c00001da030203510b007903070008502d5042e5040d500e01000610039001e94010309413080700c0c0784040346413503000304400001001a40150380e2903501e0014042d403175903412900c6452502041481d0b61a031041e00090610782584141c1081c010725030040c10300d00506803c00c1c00704956584410341000164104610480007034950f64010180c603240b0001000a80b840d1202b42c1035a042c489840c190102c01525402c0244c01541d00101340c1d551600041e107022074441d44d40d01010b43c002101c20b0488030800345141038400756110b81103000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 968737535 1250 968736285 968736319
    0x9020915251209240e01110d050421050604080c0109050a0501060f0803040f0e040201032315011b1101180b031b0f09210d09080d0e0d03050a0210021602 67
    0x102e00c032413010107107464030241c0c9068a01402c0c0c8402641810700d0324080c00401d800400c3c1c5026a40c1c5403000100d00040707010400b640300d5095251340109a40d81c0000352841030b5544039079805000c0d00c02041b120000c682c40101c40786c00d510008142e40c1001c12151455400d040140c02004180903292600c640c0907000301c5c42210010898048542c081d142c0c41d5010314040001201c08406041203040544560081c2441e43c03400081750406541001c030392445040940c4901a4601540021410f100c00745250302801043d4440e254002904031017481d40d15203079000101c5910030603108200a825007050085036440041000d14400c6401c1800c0c8041072440885211003402070902c524541c0c00b0400800d815414100c100c214904e40280c103040e246909a90041e0600e000b014020000594401c801c0010502c04c07c05000c0d07a8030301c1c0c24441441d01501000c40c070152a41e50028060010026445070700f64403c0011242030b03180b0080842d2181101d10b5400410041d014081c0d225081c1492665440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 968738785 1250 968737535 968737559
    0x50a0e0613080c100c020102090a060e13050c0705150a0e0a171608041205060a060b0a0f021c030e0f01051918020a0e0103020a09020915251209 63
    0x140d844a058071448190700c0c1d64003400b6500212140c001d03030181c1903000550440074000c030304413101290009600d17042d002c0c00340309080c40140e00040400003502c0d0b100707080741c40d2850121340c0c01c210650086429914500316035002c0c0704d0000010a54815445803100c3c1044141490b40200300a030b00a003d55007012690541e00d00c8104005045822401910000448054001d00c4e00d9500c15200c900a050b007510b8080158010303511000f040c0c0001e02ca26400c00c103083c440d1903800ba40780e03c030401c1641e00781a10700700c190150040765014410703603490b04003042e8000c000c4292143c6001e4600291140c11100050203440401180212407207540300d1030b60385440c180a29032003624039152909900300300d40215406444560b1800c141020b0070188603001d80c0303a101c030a030050030075442d80051651452042c000c00500d40c2d88001c2c030480c41400310700c7c4035603240c0082c41110480b03a27038446e0310740109810302041489030301082298000390407c0c507001c1000c03501280c1e5070a14240c8503c42095a6014800307a4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 968740035 1250 968738785 968738791
    0xc05071205060612010e060a0606030e012703090306020324041802150d020f04050306010803120406050a0209040e1f0b180915010e0103060b04090b04061d01020a03050a0e06 76
    0x880c0c0200740016000c1c10b1280201050f540c1030400030a503542109811407d2140581d08461150f403214018840503802d4011201400f440c0c200070000c0c502501c00d17444030451000c0040000500e08600c544c24140b161034600c020f1900308800b10b549043c0000454a001c0c4a1134200c0d00c41008030309000300601c1c1c24842d49060841c405903076106139006a080050000600265101c1448280070101c40540e051000e03250705510720304a507070345504010406161a00507030040156500420001c862071004840964201d80e0000000c140d43d200e110090010f8040c02c80c00d0b6030170500c0c160f460100481c0c002502401110060629035401070802025010b0b40d0205818a408c042d04110790340e2154100422154000070101c00d503080c00d90340000d003401e040f00070b030701c00200103004070018030601a0700d1090060b01ca5080f141001221242e0381d40158200b0f00905c05803115587d0700203c00c0c140300507100f402200d101d0600841da521042d1034050020003003038400000007072801c404074640c40d00029803a40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 968741285 1250 968740035 968740043
    0x1b030a0c12090f30020312100f0306020d110a02010203150a0b0901110c06040303110709020304110d02030a080319050c0711150904090f12171914070c050712 69
    0x6520300c07041c0c80c3c2e0748a40240070300001c3c600700240f0a4004403c1d0302c02c40c24004859617030145030340d52904d00c807002d0303810030162004620741840034041100c8240654401e080760351048001d03071101000c00c12003006101d260142c00132000000349286190754198001d6211b51402020305a111101d05d040c800191241e005080c0104030411102103958011800d00c032a141211040f510854000d8000c83d805070003d80c421030120342c02d407010007220b10301400340c07101600c0c1c070410843c01d5107015254013440002149066000c2c4510302074030015502c0c1400842440e0f90001e205a0740c0381450082070095500341d601c05001145000042519515a0412504c415801401c19046200800c1c100f0042d020f944c100f080042804020300066501c450152100c0710307014040c000f14040407030402d010401d41406c8180c081200c80300c0f180c0310a00100581075042180c14140050422071400e00c0340c000c010100d8020200e0301203204003ea00c0d903004d206900c0c0715200e2001d03a07a01c580c0d0f038000c110341c00241c048010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 968742535 1250 968741285 968741303
    0x1128030e120708040902040e180c06070609021212040f06020a022416030806040b03030a1d0a08011b02070e09060406090c0e040317100b040302091b030a0c1209 70
    0x88030008280001d090031602038035100340b41503960502d20040340d1040e44070220b2140c0084c00c000e40c6000e5070420788030b00201c00c0d002d0304581000c03500040d12403241500040c031956035840c20103f50f4503406804422008500e040351818284110b5250154020b4440c01746012401c60020403c648040f485c945401e9016086103c04000e210b4003070034180a140c0161003043c0c2c00d2042c11707403813480504000d00842c003070340b20088242840818002900c0e5041c1240d40280e1080040a41040e40440141e0301210b1007040701160301c9000703000994240c02035200710f100d90f082c091441c54558514400602a0b4101d030219030446694201000094004841944140e045540083c0101c1c0c520780100d015240f0884040041c41c2d15810340220341181950f096002403400c800038590505c01c010403903008494010149402d51804448800c58807660200038003444900011800042c840700d0f642d040c10b10009901e0b5220314000b41b8030301c01410f507149040d0004650704051196601d45100f00c404031500302c1110 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 968743785 1250 968742535 968742553
    0x9011a0102060a180503070f020306060a05090a4a01060b180102010b041407090506030112020d0206070b1602010515091f0906060c060b041103191128030e 68
    0x702004120668110030780310f82c1c2104e441c000440500050091903ca00300c034088081c4140103161a01e00000e0449000385c900100c00d11565540308146540003006140100d0082405403000c0d1f00075008049190854101d003002e904c18035a07240d004040c1c00b0009042c020075500240b0441e080e42c000740b080310103501d03041140a0040089100c00f208540042c000480c40708003500104044a80c1c40c20038946020005052081d034540c0700c030f80040100400c40b8001d08650500300c40c68448003058038000d01c00c0104081d408215116502a01d01040c3c00c4441c0f9841c5141c135081c0030808001c80b24048006510740000200710f4071a044801005036009000340040f5170341c0c4550180c25241c1d0100b13a42c201d06008100040c008a98001c24001d0680e5a445880003002850b105003524000b281440c403403030030110090b807458803c409aa0f8840d0512440003010b04850b40300100504221190340c0d9801800503519021955800c001c10b00008041e880344001e40c038035441101112826000303070505400544e44 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 968745035 1250 968743785 968743801
    0x405040b04030810030819020c01030c020d05091c0506060102060708010303080103080d1d03210114010302220e160309020f010807020f030c1506090112020918060f09011a010206 78
    0x401c42d481301441160850080e26501c804e0505e41103003060110800364a0000b41c58640c0c1845031424400c03081c00c0c240034070044bc10020303444060340da25420070080045101d0328035589880440580e81d1152034500b1200405080040e143e4404440050242c800d40c4041a00644034603030050480341c01d81d07212503c0303900b159285a01ea03800860b51464070703915100c2800442d503004604e02081d0090360029541c0d503508a200da8184c4121081038009021201d00400c101e94450300b40750420b060074600141d841030001200c03092103000208510340c114104602203500320401481c1e5028002603048900e82c00758074034040703040c1c0b00484030083d040901c500359401294000c1c40d44980003517584c01520070014840c4100e51454005072820851035010134802a14070000c1176480b900403400780c42068042d81008900b08849c056210000c9c0514400300c0041e02c00c0d0450071000a944016205841050418841d1b501d007902041c1e414101a5291100301c2962030600520351720380d0380040c0c02a000e03554031005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 968746285 1250 968745035 968745047
    0x703061d0a0605060103140a060e0105010c051c050c060c0d18080922180b10050a030f020316031a0f13021c0c030f030f080717042a030b060405040b0403 67
    0x130341414140c0318040b000301400010100d6200d612101000914a07242a81d14092508103900c05d6061204040342c61001c1035022403040015042c2c801d00506c003c40300501212a8440d0f034904000900901080c070410100900042c503580543d030b0000d1080c1e011103032000480142c005c400500e90203080002c0445400e1143c02491012109002208801c1840342c0a506582c0500a81541c4190308800c0f0010407042c0000540c0140c14440c1003280d0900b041c0106040b00114080905540192040103046580c03c200c1040d041224118820310140d6030328000c0418414041400c9c03503030302c240b00011601084810290300c40d014210100079200303519028400585a03040410701a5000d50303d450b00440c400140e210029885402e18403000070071818014000003003d88500208120305c424031546c01c1d8850195103803842e00c40083c6c001c58403a45090040b01c50104120136881c4042200c00104403003120801040747d00624642c070041d61000100012076008843c0240910301c504045004207100d60 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 968747535 1250 968746285 968746291
    0xc031501050f22150c05100608060f04060e16090e0d0e1e03011109010f11060115050c070603060614161b17010c09050607020d060b0409080c0703061d0a0605 69
    0xd080d554010351a1141c44d501043c480d25804085000d00a50100f00942002040802c080707510040051904000596841e007001a10410349030301a00c0208041c00980c0c0d20030744c01c00f50b20000300c48203404004811041c080e91441903809861030711001682048000c1500c03090303803550b17549103000010a641004006804018940140c6160010310701e0540c40911801c1410000c010140361501501c0340010444044e510b900002c00c01d210300c2c80c414202e400503205054403040c1e29000840070607490104e0702402804100708061203800c01c0000c00c10303050790219081d1105980c88003951440003120112511540c940d500c810036101d5014408a52050590305407000c03207149030361491f0795031007024080d54104108001265034416111481c5900007500381c00910054403818104050b07500050400c041000300944041c0c1c5500b00e1490540ea1390b03010500c3c540c0d1103040161140c01d0684416900c900706d02045031b0240ca40014203158580051854501540f440010402e94036650b440074090803000e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 968748785 1250 968747535 968747587
    0xb060103020c0c0a0906170a03090e04082b06090b060f0c031c0605091005030d0305040309120f060b091b0c0312012414070201080402030709050c031501050f 69
    0xc89443e00f06581c0f110b02c50742c01802180c50105180741451007021840e46501d05980307841c0d00100002c070000c1d80121040003190940e950400459885082a259510800f80b90540528030303003500c84010614010300150004011a0420580b42c4a07030810003154444052030342e1090042c4041c05869000d0700090001c10010300949041c518050700050702c1020b80b80901ca0800e40b03446080c0402e0808000c51036010f03080711a00c10001e86890b001c2516080381030408802c00d9180c00000381450300400202004146030719012030480c050b810111880e02000d04101c0700a801d2034050200b0b450000d0140e80039145501d110309690400f4075a03900741d50b0000b031110b0914001400038441e443c4084d50682e0003000841f40144142e13041d40300f0030710b0484401d05400240031506024040e10740ca20300980e9046a0b080c00e0400d103540700c42c00000d00c0d00ea807503407207090354a08240c100700c2c2e00041800a180105641045854940041001034903103006401d20b101103081c040c41080421603030075401440c3c0103d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 968750035 1250 968748785 968748793
    0xf15040606030b07050c0c0a050603071d0306160912020307120c0509010b0406080f071e0e13090314071a1807080606010e040203010e0103080f0d02040e100806040b060103020c 77
    0x10b81d9441141d6401c08a400c030011075808108940300c054103100c110a9900c003102c02c0103800d8201780000d403450001802ca1010861800c000c1c4071480e2840d0054500c900d0300a044560f180340c1401803000c030809010300e43c0002a0300d801e00040e180043c20103604503583c020050045207040c071200300f0140080704415100910280b10001d50350b00c07644c070b00501900079105400c0e525814004040d22540000d01500030342e000348820020540d50020f951640d0751503421030380d410340c800418100c8421007c20680c5500296100031581524020351003446218469101c80d2101248090701c00514010b0900c0038120444611604d00c25801004549505c24030003040c6029a8001c520058074041058000c10400e80c01038062214540e0804408640010211015842c40d8140101030074159810710004003400c0300460f102c0080402a070035a541203015107400c546560f6546d0301d6440030001502d0056481005032404540c904010400900c5160030444501468030b484004400a42c4900d40c56825801 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 968751285 1250 968750035 968750039
    0x405071e0e360c012c060d110f04050f01080f0705070309120c030b150d0204020c15090c18071d010908030c0319091203030c03020f07061a030f15040606 67
    0xc1184120a06500c96038002d0441d40400f50005d0107030080818204102c480d458070b440c0780c2074010b614a0031402002e48000380ca03a0100001800902070701c0c951700703007c504003040d80240c0c0b031500c0015008550080b203070306440c1d421500041d5503c0c042aa048540c205c02c0000003050329004d034004000283c480e180ca90f51140da54410320106813130481007140c0c01020f001042050016544007150040159030310f03242d0f040c1d4220f0008482c00200c600c000e0040360046041072100c603080c81100001d90201904c10300502d01105100d44880c02524464840c15680408040c000806445148120391076200e0301c1038140311300074a446500710440701a04001c20200c0c080340c00181070003e0000c5020482c001c0d03440c0c40c0c04d08284160b07900c85000103030070070800f0b29082214171410001d1081031900360600141c0050006421006840364655070000140001102c00812140f0f51007100c6000d1a4114031f6024040c19080607112010b010049119038445c43e10342c002036000109854106200f070f60009220781d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 968752535 1250 968751285 968751361
    0x913200708070609050a12080c070b19180b0f060d06020c011b050d060503030a021c1101020406052a030316110d02070e010603021306080601030e060405071e0e 70
    0x139480c0404403941d4000060100400108090f644022010343c00c10704098901442045020700441c070f0003401d2000c89e0008905070003d00d45500e03142003080710080c080d0500d050503c10320034100382e00850354219505c00080009035081c440c41c1c01441c00070000451610181c642d8006500300100000640d5a2007000300301144407020850b00340409521040d071210602a00c0d2800c807a40c5a1105003e50420031004000a40c041b07a10a42c11914001101801d000305200700c1e04081c412603806640d40c8001400306035560020003401d40644944107a41e00080200080c14100c110900c6111840e4001e02c00304400340040524103400e10325a01e40500900d9210045030b180111031540b80002d81c2105070244251000402064090880b900f0254039210203884114031640f0184590005c1011a001249607070384a13030482907560000d0f01c112081814641030950302c40c98240b040024002408480a601d0040c101342e40d411224029003101850780e6682000305812030480d500d0420014131071b4000c01c03075 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 968753785 1250 968752535 968752541
    0xf05041205190606080d0c05030904051027050a0b0a06110a020604150e0907080a150e070e090105030f03090f0604080714271303050d0c0509132007080706 68
    0x8140103410114844d443c265000d030514600c2810002044000100640030032400070803600300c4002680d00041f6503035059040161181d490304410b02d00c01319000b4007580c1d42e0300c0580800c014030011004010710746030b520f5080200c41d0054940350b0405e03088881000300e0390240c190b007210a000c510546403441c0440e4000340082c3d1054100141c0c55203d000c08141c8281d1040780b8908030b0f0000c2e141c0100505044d031015107038880061104c0120750300c0300901c005019404e041c00c4018030f4984021803550418100151501d4003a039005402a4001800000e4518000a0040032102d400001c0d44c5070003071550a001c460000c240341c0f142c04c540b0400c4001901c580070054200140300e21990304504034290001c200c44250440030b59811504d20017009034401c00d032101150b811442c48490140409031724501030300c05000e00b070a001041e0b03140418204420760813200034a01004212801b400c0b20028032102c800700c40c40740500d002d003541b0300140c5203080001d4100910301e01d80503a03a0142485a599510015 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 968755035 1250 968753785 968753833
    0x2060420040c090810020f03040803091e0309312004170c0409080a0c030c0803090c011b1101050a170c0a120c0203090609040e0d050c0d0f05041205 65
    0x500c00f9034204040709060100e1080c8688020b015880c01d6844a07420900d40400303071018200e074100102203030b003d000801c401d4920188650550408807030054a081d1660421030f00c0500a001a042e4500081852104003240120303080219040c0c90803102ca0310010186041d60343c280900c60740100b00c0541c0340c600508010074488514640070303210740c000a82410103800f0310758002c6040052403000540c041082e10001e045a1428031081d88103420300300c84180804001814a0b83c0c0001400344040d008625072a01c203034207803500b130700200c0400c240415100d03541001a080500ca5100075141d5031240d401002700c440b040c5000621040c00749130f0014941c1d0700f07484028040c040021403100040d0015010031803121030900401c01180848006500c82c8285101988503090000d10380d461944c1d41da00543c0a20740704400c0701c60030707805040301810700d03031008010b54001d200300c2c24112080343c8103a00e00131019580f5580c141c180361a18a003080b4006c4a80030894050040d43d0708103e421584e0240c05030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 968756285 1250 968755035 968755037
    0x90a23011e090302120304080702010305040501021c0f0c110d030506061c0b04270321020d0b0f060c07030305030a020d360308040b0627061e0102060420040c 69
    0x20780b141c2d1031030701030314011040325001403561080c0100004110490140c2d201d1940a00b808030791982e851030700301c3c02481505411101f0310710085801201c90a01c0d0f12003410020401350801c5004100740f01542c6250300d0b80300c0005a43e00149030007607224030a8110a41200000d040f90303080620300000f0511020b03c0b21000100c01e075030b58600c9030040c034060203001c080c0c1035401e00d034051080c0c1050320300d60310000c060030140504c113070401d2286130714032104030024510305030f0702085441d00074621403c80075001c2c1081c128441c0c61041c000c0c1d126840c1c20002c89a240d0a05001408144c0c516a001d98080d040100640842942446109480070706401208102c0444021000302c280074811640000c0b01d0703820000401400c14003070349001a8100008030b411641100100312980e42c0c420009489840c0c21072402c0305000800f60b074400e00e0802e401c0440c0150700455184990b031481040c9104225031300b0492500590044d004200072417a0645a000d100e0040141440519018408101520031303208143d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 968757535 1250 968756285 968756291
    0x50f0411031e1302030a2414060f0405060603040f03020a020a140a06030204271b090f1508150f1009030203070f060e27010605070b090a23011e 63
    0x101c0c810082c40580d214030318011603414424241c0101c1c0da40c12040a00400e03410201c00c0c42485101030498100003142e801c0c1f07040c001401500c28440003d0b1042c1c1c0c416000c0c4403e007800071828179250081071b200d0b820160083d41075680b1a102c01d020f01c80b4032801a0103500032080e0704000758561f6803030540030301200380082d0480f15207001481500500369200104151050100340a001034185030300c00c126458400301d6000003001e4103180c0052451100c1490000424002d80b2007003504203060130100c0d600c10001540d410ba442040012048070f5140c8900050701c41c4000681c083c0004101071903680c8060402c5c8004617844020401d0740381c410100c0008651440c00800c2103140c01c200c80c1021b444845101c0e10403620749034010741041041801244941e84070701c1454080040d070700a40c0707101502c5d1035030141c0d0795a40d08000742003940a05c030305480c0782d0030100c00205a2180094016005580181d00c05408210310381e20415020080c040c05440307540317580a2401c040c155650301911a44449000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 968758785 1250 968757535 968757571
    0x70f0f021e180405072309250e150d0e060703020333060901050c03030c0715020703020d050c030c1b0108010e010608070f031d0a110307050a050f041103 67
    0x10b01c0c4204600526440c5a1403810000010390100d035110846210780380e03142801c28003241265000140c90b42d002d8100005404111224450760b00b51b800301404506c0c4800c05e103418400850b030180720040320a4002e400d600c462400c1c11051130040241211494000608a8406441d030b414048251803100010340c01006101211019a240790320803251a11040c0a03015403881d110f1107540c0c110300d005d203d0503012425080c980d0041040b0342200e091102581c0d602d250048409409070003400081c0c803d031600c90349400718100e0303901c00c4800c0950144c00400c07807090034140c01c803410f0380440d811569130300003480038046054041000078220818090100030804100000418407601640121059250040100b1081d42c1000c0c1c0d076500904d261a201d184200e540000343c014200c4504145884c200c1481c0101001c100820700003c039a02c070342e50345c08000360b80000309995004c090007150360040a1110410013890131143d10319440301c0140000c9a40b41d50022110002e8104036201c5004000304904 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 968760035 1250 968758785 968758789
    0xc020a05060c090a0e0402030f03040303030c0e041e0b0121060e0f040c0303030c051204050a0312150504090510140a06050d1709280f0504090503070f0f021e 69
    0x10740d680311034000d003941e08125100c000a104e40400707209001c49101405d000c81c003591401e04c0f0030110007402804480d500c40d62490000d0060103020031900015003100c10210040c9031038040c400300903500d0b020301548184d81c114500010444002858188044682983c200f0070142e50300a44142c40300c5030001c1c4562411008500c0d0520040030400c50100c00c1007000002102c1c0e1b00d080050f25014500001c036041018800d840500c81d049050420400710003c020810400140d00c4486c14402d9580555605545148009584c140c90141c0224200768800b80502d08255014641751390203801111400305442503000102c8080304495038181800760b08114025105000307943c0208401d0f268203100d070780d9a4503141400c2003907102c1c4449000e000110070030581d58028a4031a82030001c40d032402002c04c0b100100ba80700701584103001500f0708503030b00002c107460140324020340d10b500031003e18900425135940c83c920011000003120040c0c88400d80c600980c48441c02c134603d0030030410034074a1100548003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 968761285 1250 968760035 968760043
    0x11030c040f0c1101060509041e020a12032c01140f03160906020616050d0902090a02090f041503080f0c03071109060405071e020c041e0507090303140f04090c020a05 72
    0x5403c0280c0c10070b5403c00080e103880ea4090b5115821817540c03000d582100c81e800300d881c0000e0901941c407510001e004901e48408005c48100541f00392616401001a580214100800130000784407844190800c10480d50081084040c554035261a161510441d0407061099402c19a0101607400c0d8291604010640002440b40641910f00052006203401c052035013414804410b514104070000c140700045240d02d1300b00e5500103034001e11a54803407034411081c1c402504205009842101424485016414a40309841c0c10340c258a85000c2d0007815030311104402d45c030402c003c5000101c00c000c1407242c10020300203055420b05c910107004052340c5241c104101c11601800e00c0744914540001d100d01e45801078440d0301604003d1180c1e051a9410302000d07420250051041034109003000c420262303010340c035100e10f10401c50300c210420080d03c40000c2100e07915490300006001c01c8520005000301005480548407411191125034681522072100d001500c81e407440d494090f0380021009820480144 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 968762535 1250 968761285 968761307
    0x306060108090c060d0e0d03092001170702151623161103010c05071a06012705150c0c04110d05130b041212090f11030c040f0c 56
    0x441c09921504060610603201c01400020a1040c0780015040c2c1d008a0903030410100000040c040e00c44540c01400080d0180840348002c51f45240c0b40900e008807148410b60240e0b00200613034640c000d0966038407504c005600c026112005500c5040741c03041d102a91540304911400c0b1400c92a00e02d150810f201901406280c0e205030b43c0c0b02095803413501403241440660351851440d2405000f410f015003490059096044078007a01542480c1520f100141c02c50300602000d48a41080904504400c0c441c9842c04010fa5041c4d0020300014901c0090b111040011214810402540704c01c40d5640c000003a80008010407603480300c9004038440325800c03801d000c200015034003074505000c241c040d0100502540b142c14a501202540c500c00f140d8405c804002040000c3d50086140701c4a050504003441004011505040092103207801d41c20403041c9805142c200f942d01080d490707003d01450343e0364025140000700c0e003a0580f040700700b8000c02e90340d02d0180031140c202481c4001640b80b0000c0d00144064811 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 968763785 1250 968762535 968762537
    0x40f050f1903080403030e1c02150105030c0108041401050103030e130902060301090c0509030a060b090702010c0e21010f0507180305030409240b030109180f060b03030c06090c03060601 81
    0x40c600c481c401c8200c005091618907070502e40307042c03560340c1c41c41d05a00800f41402124000d21070114500d0150001d4105c40b00c2e05c83c425000c55005140001c10070f44040424054a0b0300341d000504486495406140c9898009104015960380045990403240c2140c000340d205400041c0c40102c940c002c0d042c92041003115120804041c049a10141c0114900d48410b205010a00d50b860300d0012256200d101034450b8020010103580ca12103071414030101a207618401c0d50b00c0349024070003007030b0726900510030301c41340700169103c01100581800030844580309129055141c0c1d0904140801c041100f0b225526002025000028541c10240c5005141006100c240460504120b4041c40492000420b58003120031014011580f100d840e860a4080ca800d00790303505034000c49240c003141c850352038000340d4161200014108011842240d00e41c4d60b441d1000000f6100c030304221090404034006070488070340c060000d41102c1c034082d07251040c14074085d403c13506000a07401c0398800000d14a024051143c10042c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 968765035 1250 968763785 968763793
    0xb040803010f050402090306040215070c08060609070f0e190b03070909050106110c212e110703080919110906010201050702060a4208281109040f050f 66
    0x244131b0100b9582d05001d44082d10034005040c0222061031010102c410f4180d0201e0082103003a82c44541a135510400d03641d0300c0c4512a5500000e148a129000c0c0300807404050381c94000a80f010707018802140ca211b0b0300f01d4802201003601084045d6030100650041c081079031500700f09490b00307413418100c0306d06800c55000c11483c0301c0626070b403940000c1c80300c94540e000c50324810071415641301c00d09150090031007a061802240301009080c1d0905105200c4503040182e41c5000703514151001044885050306403040d6001807180c0d401092003100d02d07650005102d000c851b40c83d801c0c130b40320001d0a600c403035040715101e08a48111a450906141d8a0740061081c0001d00150808080c041e483c0c0600800303501581e42c3e50000040c8010500302055420f10b06880c040c0c1890000b901090788030100b0403aa85000d0409050004003101c1c0024581e41184404100708a200c51001d02690403501042003519624007004003031aa5507101c07101e41e07000c1d9105840e160203002c06803402500f000d0201840111a800c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 968766285 1250 968765035 968765047
    0x2070609140402030903070b040f26030c21010b0918150d0302070b030c090306070905060a120608030a051306030e060402040506060c010c0e0a0f0f060302070f0b040803010f050402 79
    0xc80000950450000702c40158aa964940140345035020f01c01d030243c04032103800280410b0010904130188a1405450103244041700c9007050721100f4542c0142c0c0035210f0082002402d948604001f602e01c40142013280307541d00301c40f400300040100080c2c1145c4060500000c3c040170a207803d071075580d8800e4003482100000c0c40c004000d0403160400c01d640d01c0c000c000d803101c2c00040500c00d1020801a00da000c0c2000e03100d06011a00324030342c0d004602894060b1143c603003c501d034140500d000c0d608980f001490300b4030706200c0d410210380702e003c0d100c0902800c2d91212004140107005202030030840c0c00b56a25152580001142c59a44540c0390f8003c106151a181080300201404200d00303074860740548022449807241800305400384a40000185254130b80003510032141d0380140d40e4003151408884090060342c5400b00b814650f00e1034800c6132142e60110b4420003080e40290003030541c250182d0300b1162480c00540303480c1c816800480d8222400f240c00070050017000d2a807600f80000d00426202182009 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 968767535 1250 968766285 968766299
    0x807170424050903030606070c0308180a080109050a02120718020a08130c092d05010603060b09130504030e1002010b0301050a020708071b050a06030203190513080715050c030702070609 81
    0x2100c0501900c0c0210000140423060120201c01c18000f190300441d04ca03600d880800d106074249190300380443c407031240ca44002a44401c14040e041d4444c1e0004003521244031150700b0809106080e011030074007030050324000141d104244400c0d15081a001c580980c2d00c0000c010700a20b06003008240c0b010034031040b44406c0201c2e010740c041006454840ca0009a150800e43d42d20941d8600604880000080070103154440801a04014129503e47d1030a0062a8441503032051901469000c250400300c42d01d003c4644c0c41850300410380142c003900308018001c024801140c4030001076140140540c0d10798507080d809003424868030340d0100e500001181400e40301d0750755001d14407482101030040321041c003800741030310740004804008201c018240c075a02e1343c1d00e00e00580690412140410141c000c0702c00b80d80c200506000b558861200a950688011515501c552068110300700030f071045600c0400d80384124042d80314082c06007001c05909601da2070a0304c0000d1808880384c0100d4100b00e07180d0304c208002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 968768785 1250 968767535 968767537
    0xd022b1401060312051e0c030d05011a12061302160c08030304030c0303331e1202100302120709360207031110020429030103030807170424050903 64
    0x420340c070345000b0340d1354900d0b40000c1c61034080d5901b46803185400011000d10210703000000300743c038844c941d00c2405240c3e41e8102844900c920050310078075907082080901ca0011101900030780c0203038001c00c044074014518a0740c000720380003080940c03100c0c1c02e221907032414410541e08060050220400031442d42c689543c0003032680c0c3c8540002020701d501d524080c405440740c0b031110310442c80001008000e03071807990080342c820b4805205002c481085180c0c001401191030608805503001040d49503401801d0744c0c207101281c000d405000041590038000704a465200e00e041600410142c1c1c0d85012440c1800d07034000c0301c907003200700d18048244036a0b110008884403404410101031000c6c001622000309003800d50715042e20041440c0c5502a949100d20101c00716400352080d06d0194061000c10400034620005408107280380201030300b414001000000d03c102e00c01c0c2d0780711610b803400c00541031803892620f25200c2c1c180c2d01119201e040f1210301e2040c20403800204200b100e119814030407824919407036038907 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 968770035 1250 968768785 968768813
    0x3120109090b160f1b020d0308151e010f0c0b0906010608090c0a06110705190807051203120a180c061103040509010509040609120f031a0f0d022b14010603 68
    0x107001d908902514071742244403000c040346030050b100c3c4030412100d140c002c143c81e070121081407804201c11061007060605119902d405030800c3d07400c994081c400801950048440340c0b00400308200c442c00302e0b0003e0b080d066050701a45d0300200030440da50503d600504442e07001441840303998022a9071104950700c21480c0400c0b211181043c4005c801121842d40c101801504400d410443c15180c88039403544010080c400c907201c1506843c292510341042081350740c00000342020a40c41071100c0715031000c150851719004110a080003442e0b107860601a80c0ba0000c0b8074082d5200302c9103030010042d09400c0b13005407803080260703000782d40741c1070a0000090101d141030140c58026004e040000f4204000355111240b5035401101880120861000c002c12941089901100003418100c0086103400e26450100404200400003009a00d8000078001c0ca20001001607070322040700a884800e003011816400d9600690094024030300c48076040000000720304c80c01802042e89010300030404501a1044203030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 968771285 1250 968770035 968770037
    0x10902210705091905041b1d030106090c080a060509090d030923071a0301060801050d020102160906170c090705030a06051c0b090106180c0203120109090b160f 70
    0x20961901c2004a0701801403c04030780d04407000c2600d003d42c50744d268a546040722003ca809002d6a20380d100b007140d401d1203140c04100402c00c0c0c02c0c801d17a410840304151841405c4007400000380aa55101c503502900d01080400d00803a1410b024801c1c0c3c4d500c0c50250202900c1c003030314109002e080030000d06585103101c1505a0406a0381c040b04400c101d00c00c4601181c840c1d100c07441c00001c5207406501c1d23864000910a210a0401401d1074004c01002442502e0403a80245c4540000c1d07882c16040c0309a00d00500c2049045011320030900c0664040d42e078208010f013500007000141d07070b410000d1841d1344804200601d81d2541c421701c1c40038441c2d601c0303101155108105142098803902c81080e0781d00904a103030011680300380705014481c00011501107042d1f60600444038000151505071030142250380900404c1c41180300400700380380940503038000d40030300b007111b204607440e0111401c80d03200d54483c20b8204040301521150320009100540903c2038000f05072030390740c40c50982103d2020f4148800782d08200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 968772535 1250 968771285 968771347
    0xc15020c03210a0c0b0a0203060a150203041a0c0a0507140102010b030a020105070c170d0e10020c120a080c072628050a1a011703040306051b0a0e09010902 68
    0x403d08601c616455915250300c810704e008107007001c1e02000040e400c1140d000d40a1400c039840002c1103401c900c3d40c03101303880f082d402451810b81810740c3c0c07a003180c200c607910001100b020007001607aa1001c1281c0490280200041c0101a082c0b00800d29100094141d65045a040c2000c001592f600450005c0455609080c41a5580b2003854a0001510b01c3e91020f24001140b01c0000742c880c201003161100c20700156124800c07184a00100000702e0304640c00000181c2c06002c2c00011420301e01c031551a08282c1c9000c403000504540d4a43c100350380802070305240ca4004020400a80f101050360305d0348403090f801c90740450110307000b10340d81d138820103524042c401c845840d0707800da0100c480124064a54000c401e848851555060000c2c0d101da900e450301c490a48a50000104ca003006500c2c070018a8210028500d070500c0c0d0f0b110000503080c0985184024140c911482c81140c2c80074006180c854145e40b50443d5030180700d020055a0003059101d00310307590040050409480b68920b0300740c0c280020a840d5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 968773785 1250 968772535 968772547
    0x4030b01170a140705130207230102091c0203060106020f060f060612011223070b030a0e1912030b150a0215150405090c030a15090c15020c0321 63
    0x52501c0001040034000031a00041003c400f040800d0b1030040c1c0744242c030400b5450305011010300c00c911a003940078055080211325038542d01807903104000c0881040001604140514000030700e2841214207161440c4444040c480450130103000c0c2a00502260010703007400035070340f450340d40c50300002064140b11000040c0019100daa4003401e8a00d04501d80098020315a10360451002c0b05030b002c00c09540700c4441802039201c02d804034055903d02ca2009000d0403089180c0300c40700b203140c3c00140007d20801d40b40c0c062078050703002c1046030b5a1695403640c8154074090a42c1000072045800003072803000c15007440400303030712501c0b02c501e0641440d542100700c07551140c0c00e8808a040c00741c819003000c4112000006e129003030b580e800409080110072242001140c65002846548102e0006207580641103920355802207405a0f005c0320300700e84d00c150041400b070880e59954000080780d40144903090007e031440848603504004403007481100364000e00c2080d00f080600c1907030703853307800c00052450400185 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 968775035 1250 968773785 968773829
    0xc16030f050d050a0e0c220b0f0303120403080a09030f0c02041b050409060e090d051c0c02010c260103060c030f1e1b091a1c14010b04030b01 62
    0x7111000c182a000c00c01050804d0f0203618040c05001c1c4800e0386910524080c0950740c039200c6181b010004003c1596034403204e1210540c0094a512080aa41b110390020400422348050000702884a0350b0744104542d80b803e49000303480000068400781c2c4040c5400001800650458000f500a22130b90034008440b40e01807001801809401072040042081c404000201c99000341c0a0425a94039410a00c841a00c410725002407000c00c40301c15465511092000510a00400c028140e8001c00751030f2042181c1d98248540c00e80d10780302450307401030703544141c0310401b04e1b401503120181c00009010f1803070480079000c05143c0e460040c0405004141d0713666500d104039001ea4031411883c4a2000240001501540c0218003212203c080c009464146003501c3c000102100d0311a0784404162078145a0509000344c0202c40c8404402504940900b0448220305034080540c03015241580080801d030003524011540d280401a4000240c0c0e40c4144000d1000034260010710b03041d10a8024420882c0d04c801030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 968776285 1250 968775035 968775037
    0xc0c01081909030206150d0809040b04021902070f270e032506060f06120218040504061a01053c0f0d0605090709030605070917070e0c16030f05 63
    0x682038070680c41d11110074201900451000e104441074000300800c0c200c10400e1050f010380c00706000346100c00822170485035144c168030200204002030710042c280700c40e07025050702e40882e003203646000d0f922240c0b0400800116011590150480c0c2c044110350540446034610303184004403180d00f050b81c549950400c002802c0080d11a0600480c04107018101c2140011800f0007940906070743e072504108011815400f091403aa0440c0d0306a80d40064420714181100003d4001580c110803248080c00101c0260b03843e800b4003402180900f90019412100c030f410003c443c14118a1035040c82000d000c5680d020b009100e1000e004500000c603050140e1500441003414000716107020800c07030001c02c80c2100b281001c0050001c1c140b403038608115080d150010804850400c44d8410f0000c0d607039410600010310540c2020390859190309141c0045a100c078105040c00c0101580c8080303c0e880003e04004400410745000e0b04400e40407a658548a400940300c2d114004022002e010700c00900000110648188 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 968777535 1250 968776285 968776321
    0x109140d05030406030c021501030c0501140705070e1509040803014110091521060b21190b03030403080a05131d041b03050a060b04050c0c0c0108 64
    0x907060b030f640c1e41c0e200c0328050001d00d40c40b402d04005200341d002806c00b40400140d900c0c103894200040542d21854030340115404003843c01c806811031400c0c08010006441000000060004c07120218954500182901c58845604407224802d0f0304802c20300c40400d000404481c151680000d00e01201506008604400f40810040845840c41141640911840a210150031070360848a501c0d4a400205088801103d1809146040c1c15890780c0241c80c00d004e12424500b840940130101040d9004030031080031100640d0154100c488009000f00070709101039209030040899601412460900c419015149480004d10282c1150f0301d29131030740e044d60300308240d5004660100104c1c1d42d400008a0040a5800c0049a4003c0c101c6980c000300301520404540c80c0000580412940c040d9101e4980d9849135442c41102080c031000b41d040840880d50134014070103094090380c00444d50340200010b0204a0714010203807003440d241402907164880300800c203c3d00d400000d20740410503407503049140e18820142 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 968778785 1250 968777535 968777543
    0x1090305060f0a150320180403090510171b04031b0302100f02030a120b2d03010b060d0b01030f141608130209090c09010e1012020109140d 61
    0x380108090300d0b1101e0103441c4034900080d024040305000009801d082d05084c00018081d04100c0c0384204506090b4191b20320101c4002d14000507078108003802c410019041d10150f002802180c070074007490030004500d4000c1d4415141601d450003400c0c05400c40004040c005120704040c0031042a211303444c00003524040c640110145c0440102d002121f8840100383c4800c034062020464004081401a02c1d1995407840a401461801c04502c01c11164072003d603c03440c0c1070703d5540306c0c0080162120542032400d00107914240800342003540c0381c0c804071303480c5440441c442d1381403c8007030b455600d5010035500c406525140100e0740c4010359005a0242c42e0b06412140d140749081c450001c2c02010640460064003440610b241d104030544003100c44080031900c071881000b280c8070840060800801e81c0b60320081480640341e6544c0b82c1310020305810000c1c1d03c8160410740c42010300c01c00010b9500c01200a01c28203501d00031710011980080d1803400140b154030702e6580200c880c201603440344201c0a40341540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 968780035 1250 968778785 968778793
    0x70c030614010614070b04020f031005070203070203010f050c0f0d061e03060f050f0619030b0f04170301260a050703120e010809071202130501061d0103020a080f0601090305 76
    0x31100524840300ea09102e4800028180998036000b903e10031304542505400c2600e00c100c80e651902486105011840696007521502d071701c0e000d103610244150f902842c6030b036018513500e440300d004160940700400f134003083e903c1c03500c801d00211603009403c0f01c5610000c0c0580540b0f8500700d9800c10020300b02903012200e0814900c141140d80e01414030b401040d40c0c412501007101001c3c0c0308e0002c085540c12aa810050714101d00881c81900d003030303401480008a015007c06c1141d44a995110040000380c5550400d00360700014001000108605d000900d6038051a040c215854580084070f50b51074000d00b10a04070841c0400118020284603900540781c00c03004507240140d8901c1c041c013100c807001c9200f80c00a06000d0101d4401d600c180240c034002c1200384010221039051220341c0c2000c07000241e040380d01014140030150914980d0240a000382569140d06090004004038000c0b0820781034440c60401d0310400c03990890542040c0925000040c241c0000d50700d0f40c440340141e98404103501f0141c0b05d482 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 968781285 1250 968780035 968780051
    0xd0201030c200d3e011509020702030d0c050c0103020306120607020d030e1b15090d050106031e05060f1012050304140301060b070303020a09120b15061608070c0306 72
    0xd00040720b03510041240c2d0742030703203813041c0e801400c0c00103901c2d03540c103d4211500d5604100d002c440d1004422214080800010000c001c44500c50f443c40d01507200032622500030803008194a0280304409403510341d07044c41c500c030740c2e01da55901d9204c0c0d8084c280981850b40c00300105403503032248400103c506103120100c13503003401d041c40c001c1d51360062500010006400d12102c260452130200e10b42c901e8442000580e000300070a0383c1040102c812040c0d16074242581884048526a10100c6424101d030254000250990031130611070007d00480c80980c00c640e0780c896010001610009955a1140314002c50900342c0e1500f0191003060a0254040c898102e00741e4aa20305210f0301100610450310b1340300e01c5910111801c402c0c14265580c42c45141d08031003060091101080c003d4009103005c85051400302c5466494925110001c18100c0c0140d0b00214041d08019982c6601c3c0d60005a01004841b45030030440c410800c3c00d41e030030020314024030082021441e0010804402440d40146910400900c07441d8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 968782535 1250 968781285 968781347
    0x3130611100612060606210504140102030723070c03020d0c0905090309030c0a0501051b030c1506010318080a030e01020c060f040302070e0408040e06031e01061e050d0201030c 77
    0x19800001c00c4d1407542c600b0000052803401101620b801c4190502030f0f9400c4105000100004c11004000761061102c2031404113403400c00388000c0d803240e01b00392078800c1501000d001d012040c0320760301c0d200302f07801801300190f00100d00b01d448500101d03941201c61a1224180b80741848005845da070000c0c07038842c100b505100101c0f030040068680c0010a0301290361052018082180360032461007218040780c410800903042c0600050600588905042140e00d440c4e4003042081c5441c1c1c41007400481103185d40301740005503905004d06d4140d020f0780642050403580548402c541d030f10401040780145640c8148001c48542d0179015515240c0c506403da450620b000c6001c88821001110200d0040c02500d10101d108071241605900482d00080514246410900c138030701e0440700034000950520460b03900200e01050452402c02513043d51001260052400410482400c0440e0445e80150100101406651038900519019940910f008210010049810b98014104000785500304402103100c8c01d0341 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 968783785 1250 968782535 968782559
    0x91203050a0c030519022107030606120203100b030714120601020d08040506010504110c030a1d01020c0f090703090b0c0c10090b0412052209060503031306111006 71
    0x4041c4034000b030101d2800100110222001150600d01d04d013210030341e03003650700030643c05800144025140c615075608126074160b4021000c85075100029144c403014010140c3c4500c2441c1a080ca250082d821400c0c50758135840a90100d019451000d50040002207a045c402c1940d1600001183c110b1990b480d01a4003001c2104c1c0f003266058007520078100b8001e641381c82059610301c00c61300305015005603400c160420015103800492088050320074040c541e010316043c0020311840d485511490071410250405410444002561700d05541113000381000a4503070000014407203600300c441c00702d65500c030141540208a41d50000e0004048a01044401c00d400c0b0300030050b510740c07141240c103100c484c880309000f542d40044005016040b01c4012900040300051040441a103030b0130032074146140c4012440c0000d0f8054000780c01c6006500c0104218210361003610f0180a043c0d01652400c8c00d0f0400d0f840700c0c2b000d18415142044070740410040d90a40600c54240c0c1d03407404440034406550340383c0c649088 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 968785035 1250 968783785 968783791
    0x40503094c0203160b07020a080d050405060105030c06250c0b0703090b041d060d06181b082109060403030e01300c120e07032109051309120305 63
    0x1100c020152440300700e074000000d407840004514450302e42d1400c1070f510740c0d03903d6001601e84400c1d4458076001100140050300940f060421003200042c4500d4142805807412106038061402504080070383c103000c0e01c991048904c003011041b5180900140c104508122036a900d2000d402480b100c9404140703040c07444014560075003e60748480001d070316503c0002a500c121300ca2562200301007001c00c0c8262000310059548184024642d968002c0e041d00c0e030b0410b8a0b80e003035810910a02b40180401041a00c004041c0c00c0d40da07450760042010f00f40744005585d40f0124010f443d1840016611260f040000b8040781c901c807902070052619182e99103809442c10203038929079804181d10b510800d08050004000307032090001644030f2440e14000d5140c5200500380020048108a101c1c81c111950606d28090728440003890310050901ca495820840c5003002445e01c0c003042c080580c9400324119910402c19015980c0403511100d8071603400c1551002049500ca00600c405c0d49a0289131070039030541c0c070940c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 968786285 1250 968785035 968785159
    0x180702100b192c09031602060702040518071a040e091c03051012020901051306050a031406160212031023040e01021614030c03070f0c090504050309 65
    0x80e0044103070641040d0b4030f0403140810705500034000c80c0030000d51000d40b45140d50024050614210240d0041000d4800071240801807045501b040f613090b010800c000802040d00060b82c00d00e005a20075050098400c5200300f40444c5034010100e41c00300c03801c0c0480c00c1541003102d44003c0c007940310440503001d0641250000854604140300040142100c03168212956000309012841c1c3e08120810100d00c1d0b882001c3c3c0d4690b0f85d00d13200840c10751600035510028602071890803001e140c000a40600d401c0d8000c09031320101c20070419031030285800007800401042c0700b060258581d500c04600c0925285540d006c42490040200071064101c101c0400e6228401e05507800e00c00d440041c1000e038240e00c503452401c441d40e00301c55250341c0461032440d05081403e00e01c20075a841d1549a10210b895504091401e442100180c4440000c00407080d80e0f810050810540601c814500f9446481c2c490050100c51760040000310070750b0440032100301d4504640000a04034005105041000d8004881c1c03540c001c81d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 968787535 1250 968786285 968786339
    0xf0603280e15061008070306210501061403070902070201032c10060f06050304060f140f060a06121802120f010e01020309071a0c1b180702100b19 64
    0xc0d07203004032114501c912805020713400e098201c40400c0b00d61820007403114080594034480410848801c0e03000a0807035035126070642070001c1c04d003407090869040e039010307403103464000307951340c1807074802081503c01c0718101040142c0320000340c0016805404a840c030340c090b190300c220681d070910540c810345e2000030f01140c080b00d0440210000e60001c60302c6d2400703803a080d123240c440200714040c411401198454814100452080c0c400d0a000041d01e680001181c0d220407000c0030003000d510b01045696109404032400298a03142c80b00180c00c01110700010780302240c5401761480200106d081c0407110903070181542070009000c007100c0c0d480d400c0c4460004519400c1c2981040118814004c2d00e028210580c0640078151034400034941c5194001c101002070300c0e0130f010001c4511400c2c0320103e022018550701c0250100003a080120145c000c1d20f100b02456080c00601950f01d60001d1340c1c9888013000b03040000c04080e81070010307510408002c8003203500400e211001c44e41690249000b602a0072081390f50b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 968788785 1250 968787535 968787553
    0x10b03070806102003041a0405010809300705060a02180303190f0c050d0207060f18090203060f0a030503122401030923070512010b0f0603280e 63
    0x20105001c2500c143c030000307404003440c030b00310110400306640740d0214004603860680e9468400ca8910307240007080301140000719081040396080311550303030711103a04400b418000c0914540c035101e5201d10b0780c3d0780101c015044441c1400744200c5d0100c0e4a41d46e040b01c00c030b50341440e09811110103980070308a10315000307000e900500c00300d080001c1078640b102c0c040014145045d080300e008a5255480c0c52011041004040c42300012441c2072144801c038080c564098007403103052070406480307941c8000ca000100544007040c82841d5140e4000041078987c451800b44e40c82d1140ea00203000541c4001405270b0045803040c0010800c10000024030f00b080d5402c50180c0702d0380c0c56800b800c1c00042d0440c00c81000800c4203440c034906610a500c4026090f10440300c43c07405100c0343d440c0311440d056030412407100c1c1c0e004a800340445e14145500d0000c900c2c80b60000d11104d0034480c04103168030350f540f071060301492011021550503200301e12144000c603a10710b00c144038240c06070590801b40010805c0040d55004141700 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 968790035 1250 968788785 968788789
    0x911041d03090d0501140a090201090509010303050a11010e0f1b1914040609090317010801020f0a120219050d05070f1e09170f070e060307030201050307020102070803010b03070806 79
    0x325555400200c015600785580760052010710719480b00120b45070b550b11035a010700304003039070a507602925a240780050890860710014004000c180c000034031801340e141c0100b0000b40e0000c00c95100801510300101d40210781036019024102c4c0110003c1d072030181640140c1d0010740007800342600000365034019101102c0c1c9092203400180700040c50740142142d041400218400e0029904868000c1c0001503031503540c0900c0ea00300e6040780030071000110340414101803190001b840b1805001460021407402d851012181c50078820101c541040c4180040541803000007039059803652840b140054024001c070110042c0075030b0000101c4e020b0f03140f0b00300100340c0161040c036113100161079070303114101c1d101a0348443e01199040d00c00884208200007034042882d01e104a20040302c2d0040e14020308102d10324101c50760178100f55800c40580c0a00314020425250b030006000c004490f02805c00b00e50340e440e02d1404901a00c03600304041e00103c1d0000000a03e00382d000001c0d449a0119540d00704280c48441c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 968791285 1250 968790035 968790071
    0x9030d06050a050a0e0711011a0108090f07170f030f0c1207020603040f02370e041128030f2001090510030e100f11030c0a0f03060801091104 62
    0xd998001301a071500b446490240c04c10a600020301c0e00307098603803c000d02e9050382950b5110408002e0101407200c2d40701c195801c210025042800b034405010100000c5650690707458082c4140601d11101d54401c030f401da10b0a004007503c1c815003c0541e40e464a07842e0044049503c000c003c0c851034840e03208003d0b0b00b404000d040c0c4001960052110380b03503482d0b6403180b03854115207440607a031122040f4840404c44103c0400c04407030381203d0501000d0210042c200051241440d40800e0015101d8000c000001d007250340300341c0c0c810700111a001403c030301e80350b002070f0740c61140c00d042a0060710f021400f000b408410b0310b07a0740c1c41d076200320801c80b00024501c5100200503d41560580070441c2c1c44007d009a14081111210381e122030300d40080d22690080a083c80c24071801007000303c065480800d4096400540508409421b2140c40c46182d4245008000e036648110308501040040b910460101c0030b00c01e03085a0010946c40000344505101410540502d80f03008004600c42e85c034211000c45190300503c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 968792535 1250 968791285 968791289
    0x11160605100b0c071401110312060a2c070233180a061d0a1b050d03050a080702160611010e0708070b0304020d14031905070b0103060e1509030d06050a 66
    0x3e001e842001d00d080100c00c2d4094010160505009034040b01c80c15038081003002d00030018540341d6403a1942080340c180101340f445500000d0001c0840420401c45507050040c0030303182403c00f40e014417265030f008400c07802c0001140f80d54039844032200d0581641d5400d500d11000358250302411703448984070868141c1c48042c3c2030914200c076801210402d00420403070762203080301c00100c2000b40a8411260320003801c2131180082207924482c00c034090000030211807600000f40000340c5185080c00305946003e0310500030400030904102c1440c000410452090210303114003c0c00c103c03c03001c0396031a07400141090142340034840c8590300e0040b510285110000e1003c0440d2000c502620113141001461006540300900c16604072040358202400500c00604544401c0c103080040c0d91501199001303001035510014500c820860180304190100704117648160460b03600c01000510503d014050900300302d214950640350507900e03810091141004401031026440344801041011344400803c40125454 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 968793785 1250 968792535 968792557
    0x315150e010b0a0c0507060c030e1503061c020603010b1909050a150e10031e09031209031707030b01031503120e12010c03020a030f05130611160605100b 67
    0x400c010460050b4800040c05854250314010602c4881510303950714101c00c42c1c2c0f1507400205413401354010306078403c042140c0e0500c1180c0020302c80e0030f0301c03c41101c5d84c00040c009500c6a9050030021510125070880d803000b13141d02400c1580c9a6035583c0c2c0031202c0760020700b00302810340181003255140034070072001c0000355500180030f00c10880c140308503a144440f21001000c00d02c0260440d0f05c145a460b80c03c0880e500c0041c0e83c0104100501d1900c884080400050348900e580c04d000f11a000250000304a01924016520000e1f0005035810205c450f181003d882030041e0b12000d082c010f2041d490340000e9400242a01e082c45090100c01403c00d14550620000d0324134440040c007819024455407000120a000614100008040071081c908490441e002840400d07070010300b0000c496011701070200c0d0500268010486460030003010001c440081800410080d650b04107034946090010a407140824001251403100c1000c1c80c0400c020300c019280941c04214101001130865040d10449a01c1c5502c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 968795035 1250 968793785 968793809
    0x17121e0109020906040e011502120a140f1c0e072112090503030a02010e070e040f020103090206040b04080313080105240d0803190c03200702040f06031515 68
    0x81c000e540e40c001d400143e15603a01c80b0041000264805041e0340142c0a020b10100c248030891040c800030780307800c1000828100144003070101c041c11981024900301ca00703164189040c0d0360100344041020512840550780102c0c10030300880e000c1c803c1d02e9030285060788941d0044414041d12107651081c00c8401c421650f14003017202c1000300020701c00c0c0c1c24000d4898400d041c6003044d60340b10000642150441c600001c0141e5489260b141110010031a40005087d0b140c24008103003401d8507056121040b00300081d06154469600c07808540380c0c4000c8500400c025504145c890f0f44580049841e0740c00100e1458600f44410408900003030184122030140000320300041c510300c0d13101040c43c4541c40c81c040c0c16034000804d031424004a098107009601ca48007009207842c00141c084584401c451100c8828800c141c0307096444a0301960841d000035103051410080c90722002070b480000e005c0c1002c504000c02040c2844030010400004100c002c2400c0202042400700d019a45000c20901d90b5030320915004502e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 968796285 1250 968795035 968795039
    0x20c100b06071707020a0312020d0e090105120c030607090e1b160611030406020301081519200d090b0a0513020d0f0c0e0718180c090317121e01 63
    0x1920f01e00700041c0d403019005401e00403181c0000b0555001603005585038000f60b400c03542440e90502c40c1901c00701075400c0c4103402400340c00108000c0700341409a18007480721101b421070b100004004d50000da000040403a061841d00210051084005200c0c44400f6a0758174040f45c0c5076000d95039626600007900c0c100030304190307000000c4420300380703444030564a45503a05110a108074804c40214444c1d8050311001d6a00d52406013181c1c60040452800c0703502038040020302c82000c02c0303018150321080008801280a07221562000004850744d8485141000001400340c1c1070002a04444401e40c024150015107a9680004c4815500c0c201d650410135903800300700341d00500d000d0142880c1e45010300703482c0c0c0d1070001594442d8402134482d003000780d0781c020480c10403818660081011000040000c20354003080d20341a10303c0c0f440b402c15044500c516454000105980d44a402d201000796081032084540c20f010410604140d480f045180d071041140400254900c0b0035001c402c00485d000e00b0300700200d40c1c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 968797535 1250 968796285 968796293
    0x8030d020f0c0109080910030e150a0b090103050d030c0507030c06050709120615050103022a1f021206150d09231c03061d0c0706020c01020c100b0607 66
    0x15000d103103032a0108405118010b203049007441805140341c4680401c90b42e80300d800040000446145840404040c2441000c450005c004036403c017014201e0001411151180c0e66014060a0030b035030182d41041511f0000000d01100048103d82172103a500c0070080100e11850842d2a4400c81e0405400f043c0d00600600010340d2580c00f49520080c2c1c1e00d44910f05580366403601c1080c00312608150340369500c910321069811072103002c0d0401000c00b42411882d0071900f000200ca00782c3c2e1807003000780140800c8c50b0061400820f10510020225a2840c81c0003090884a000700a411600070600c0e17070146d020014005003440504004841581c42c0e00c1814500c0c00d0355200054180d0560172200c80a00f0080c0c1c41044600582030241c0c5102c05024020555800203005d408e5003240700d140c0205414124200175600050f505c0380000c04009088100e69036034242464803a10507a034000b0709562001400f503014800650290010740750b44c000740d4940c3d424003410391040e600c0982a41e5401141006400005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 968798785 1250 968797535 968797537
    0x608061605030910110d1a0a030807061805070f12020d0b0a0e0106320a12030e2e110309010315080123090105130803071206060509100302030108030d02 67
    0x902d00303c100e450100700c3c844000c0c00d03501514031405103100e0100720b1103030000070b50003a034403070260581d01c241c94145468001740134000d003880054034846001039210140300325500000070100c00c607d12406218940c1c07500d969203218030f00c5007040001804c8000314403032408100e245440c41e0000d020800d80f03060364558489000380504100f14a030341d900928008544203000d0f84000740030381d001003140d22041d0700701d58128000101c55025081804018480903a4070340e2500d02c08d0350403c3e003808200d440d10b03107400e840360342d000c00003941d000081041c0c00e401480040020602c0b424540b15002c20790040344400d40703100071146d6601702070350000e0110101d02d521070b610031200c06500c0c118001c0c0c01540c0782c40030741c210b8010907050260f1028100b208900809117001c15508400ca11340204603d1600001c000c0c60400140c000400c64440040803408541c40717080c004200228092040107020b83c1d071600a0006c6e0301400c0c0f428094420500c10100940c001d00c00da9040b9036480c0050b51810b0b00d41d101860003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 968800035 1250 968798785 968798791
    0x150905060a0e011404050f2104090510030c2909010804060c090b1b120f04060507020103020d020a0905030d020a11060f2107122309030d021c060806160503 68
    0xb4942d41c0712049411800d809100034000c2c0d00860261500104e03000815082076220028100702945000d090201c683c2d99504481c221512504000ba07541c0b500d20382c1030940744069101815600c2d843c1c002107600041103202c010303d410003140d00c120802001180405038000d50715a01d02180c030510004e070100c4c4490300403144080c040e01e00b910710750703448800c6003c460f001640969040d0844400300c1c40020f60030060031202c3d050800d150303030400e0101100305445104601035074041080109812086902980540780d88031101c103020364403804020301c0201843e00b2440341a209114034814020324500200c1c0407403c2d2a0000420808080384409004140c0d004201c0d06034281c0007004080da0304010f4092840c000c00d081603103000603090018004002032158903401218034501140081d65004a0080000c1540f401d04004d149540b01c10100b8114080c1c0704060080900015640007610320900e007174640f001140b0010480d440d01d40c1d1005a5544040394500244400c0d4400c0c00d03041400340000d168 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 968801285 1250 968800035 968800061
    0x408030a050c0709180b090f1504020a050a030510111b030c010c05031509091e0f150c0a08060d021c02040e0d210b030d090e0708190c0207050913150905060a 69
    0xa10310088d6545078940700100706407845800703158080c40114a05224010700910041300c881218608640380c85865590344c00d08020303855601c4030005000c01820050760500f0003c492034003036020001c0c503031648076485008220410b5103025001c000c030034002c0c02a02d000d5400029030461a011110901c051418061302c060351500c540401c00c0882c0382050000030520358a1400781410066085060303180801c08000c020701d6644d40000c111403032243c40195a8202c045242c44203507519600081109620780860281d0810b95a4120a1400d026085400307005803094404005120602c4a8582c0b18a031109448000901c14000da14100e4124800c0c24158403d683c8006941c20000c80080d10b000c007245501008144600030400a0580c101503055000c17000e403c1501240c40c18405817000003026104d6640340681e50303260290194800c011400c040d0038040c007440d0050030250f1040f805280d582c081150002c403082c0380c989080500780507801c05560310000409041e01c03801c00c03d801a00d20052509 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 968802535 1250 968801285 968801293
    0x40614040c0228030f14070f0305070b010e0712060803030c030c040e010f060f030b2404091a0a06141804270b0721020705030408030a050c0709180b09 66
    0x110110210800840014103e8108030003041400c2c0b038041c10140030b98450b030f81403140c00d10740b0403003800c03044044810869010287e20301840841c60107960500510f0740203003480819500101d11240200c0d22030340a84001d80700c0082912454007484161492400780056075081800400c0301e94000c0c001039900130303803900d4031749050680b1682010f41c060000d901030022424820020072469410002070342c03284559203001d0003111070305008228850101201440c0a09901ca400302c0400000f030240d03005007691243c2031180c08070161030b8903840400c004516214000c0c00c02c1c00500e0034011088980d800b03644007001070130085109803040c480e407010001103400c5500c54001c0100007428150342c101500019008024151460820b10f00b0400010215010f00c11159070b003100300b078448820071080040021015079140c03403a140160643c0684c1e40420014840071904850141c0c0100c0070740402040380d0100c899a5650b6485041920b00e9800c00041c400c1d000b03045180032a004101884c1c0c44140d44080f1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 968803785 1250 968802535 968802553
    0x230403021203030115050301120f0302010f09051b10020d140f04030b0f090309010516020604030c0e01060f0e0a031b210b10050102060c070f0503030a0203070806040614040c02 77
    0x3191940144180a598940000005116104040680d1780540100c1c0c648541150b041c0103000c1010080d440780a856545c041e106401014401d40158520900100f0148010f60032450000e549580307004c0340c00011140281823260b107040c0b002141c104c0c07a40550050001005150341501c052000041c00601c0340010840d44490300d01800040000f10322a400d4982c05e03141c0003480d00300343c410280c01e0305900e400401c9007c09a03a8011f0544000c1d1120b1481205011340a00c005080c500c1603620050000041c0c4030b0000341111503030419412290251140c0442500442e000c407030044a94480326404084110309002040300c600080c01811b80c1b410a080d0215201e110b14000d902c0020400c6c203442d03035451070400400030031480c55030304580c140e01c04a50282c18000040d4a680005110494150700031a8650506c01c242c0a82135845400c2825a6600e007045212140030f0b40c4211000c901042400000c41d095041605c101c008480462120301c035006007400800004c1d000d10003c507021803190401f4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 968805035 1250 968803785 968803789
    0x3050a080c2802100e03032701060b1c1419140c040f0801050108151e010b090406050306132009250206040c0302040f240306061523040302 61
    0x12203815400040032518182d203800780d00920305101400380704c0c1344500300100305509007800030a4076040613000c10000414544103480103280e10580d00c1d034440c030b50308004001904c0828200207000d01104c0000c0684580004401001524002c464124080d000b41002850a40340004d0400c4089200c11001c01d1030400c02c61404a0200d059801f201038410010302000700910b03032500c100c000e100382d0009103d650314081d03140340c80f0304241019490103214000002c00a9180b4032605031900743c0e01400c1c030440e5031249c0150b000c80d00408081c074000e40c502000411580b5000550300d00c6203450403500708503800c281d50340702c0014990140342d60301403c0707540c8168510ba880c1004144200303008100e19007075403180e03605405000f034080d44200c25900300c04240008a1540d0850030306594064a020941d04441c9480f00300034402e07040b00343c040402c812031541228601001c0c20084900881b0b040c01815110360030680a54142c6031b40310003182070300e9076034018614101c61030505000881503190405580b600 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 968806285 1250 968805035 968805067
    0x501050328060512161a041205030d0f06080d03090c09060602030d050c0f0a03022107050702090601110c0108091603081903090305090d0f0212150c0703050a080c 71
    0x101d8494072100280700c2400d010307010010b8011300301d004050405280385500115521402000b0203854200302c0203050300d1501c021500100a10803281c0714004540c28125140d403c00c28400072a90305040080520520f00d025560542d0b0094028111300e0b084003c003503004000500040700c1c0703001810340016180f145885018024103007900655505c10000401e00210f40c0b0040c580442444140207a8908a4501040d50341c041c0c5d50b1706005039580c0392003884504110104c50801e1206241c0030400489950043c083d00c18030b0700c00e440c0214651036000065451240e05c43c90101560b000e020350301015846035000640000d0204180c1740c0348080c0c10b18140d48200240c105580486c3d00050b01c102c444a140442c00c00d4800918040204040566008007944a90682c1c40c3c420310070301d2010b809110303a190640e44d803654018103a90031050160f820a85480d1260366001c0c20403500030018032205060b40849030619030554070030349442c10b07004044e510300102421009480d00188031a50354543d82403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 968807535 1250 968806285 968806351
    0x70c02150a020a110603010e22082b0b031b0604080708030c0d0206062d280e0c12130f080301091d0d0e24031506030f0105010503 57
    0x98080c0c10f14400c5800c14072914049088501d001c1c1d0010001001800540c0307003032503080300c400c51002c030100300c070000340886160b4800000743c00c02900280c000e440110b801e00005c5130408130f0b40003039040b10009421604590014140790780640215602d452007118882c241c01e92410300501c450704085e100d00c481e41c40c214090f00451115403000070101a0307510304000380c024641841c4014115407400d4004141098000081582c00d0300c0c8580b040c40e159010003460790480f1402402001e6031041040d075201491002c5005c0000411206201081d22400b40180741d00c0b4446100d036052078410700480314045520024012000e0a81d900c940c10001021180fa0590060050020720b03140c0d410100741c50100c1d1903400350450003281040500c1d503c0c00c07002c20441c00b440140d0070800240070740000890901e00304c0403600c9100c0a8100d100060500741080a0b6010303001600c0300b903191030740900a01c021413000740c840500d10601100104070543c8201d0085038000d499a00d80114415220040101a6030038 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 968808785 1250 968807535 968807537
    0x21515011416060b1023221712040b0901110303070507020f010c020d1b050a0303020601180204062007050a0803070512090117130b1906080c0108070c02150a 69
    0x582c00700c144007040c0603207490440d04031000c040310f41c5581e001401020400e00034041509941028803494180c1c4020b80d00d0080c1c004d450b61800200d000255840c40c5200c1c01500c00e00c45103507217840000310000506800c0c6841c0da91007070345814103014030305007141c000b5880c040c10024405002c8051000910265010b0340303240d101d16841b50240d10420481111010000381003000b071040c03650141c2ea0740502505050780003d10984c0100c10030082100750b0b03400f50000e580011051000000305a0b0001e04a03049500c404540b60502d040103c3c044141d20541c0b02d4903000402c28095000e03c199616a0042e20010300ba08840230076582e02d001c04c09062641d401801d15030004a0386109118041c40301f24a6281505401072411845600283c111911401803110710007507440041c01d0b0038a14800a4211a040000d03280c05192050005040030540324204110034103040000452260029180d040c80405071151000c0d035403003400484640076051410380e4460310403100001c0440317000c801082040c840b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 968810035 1250 968808785 968808817
    0x81b0c0d0207050d02151c0c0f110a0f0201081503070f080c151b0a050a05011b0908070905090c0d030905010f1b1e0c0905040b070215150114 62
    0x300540030341000c00d15030003580500b07500204400140e50708040c64407580b46915409842e01000d060803452000c061658010355807501c2c804240d04d03600031500d05946101a80c41c140840c818014258443e440c45600510480320300425074015070255035120341c0060030000d622502001580040d2070050558409003c500c1e40c40d90030301034410b052000c00c15512043e91000040140407403028551b108400104c0348000000e544040040d000b800b50000594120b0102c03550b16000703050050081c1940400c00d0020b090028801071818050041c00040761080300c05410240d00d000d8021b0081c250040004130607003e5180c1c40c0e0015620b610003008694002e644101105003040700246c61030f220380c1c4c40d04082c440222071100321000b0303c03a82901280c4d07000c00300403510705002020740350512644200801c4250a071101040b03031034807076100a104500424224246460714441640c079000c00302d050190101440300003400c3c0c1c01c60981950341c003036018908540c0603202d6112610050304480807069224117 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 968811285 1250 968810035 968810053
    0x20f0610050405010e1312050c07170610030b04020118031a01080c0406051c1b1202090c09100e0102030f0c0c130c020a0b0a06050402070f0201031a01020a03081b0c 72
    0x40c00e2007121301404454028845c141400301400040074100c180061017100503250303c060f0188101c0982d4001e82200c011034200c01d844400002521890042064013845101d001803041d200102902c1d048a4100c11072080589564004641d0959007003216803c95241d03484c0040019882d44603020030140c18043d0700d1195042025281c14100b085140a02c40da003881c2c010300003a40c60310261240c1d03801014800240c5541898180d0a4000265200c51039010241c000100e000c1d5448014248074400c85840c00700b1340c2d401a6651403405542029030f0080e0705030641c2d145440c040e504111400340140102c070300341f02d5040700ca40e4143d808801e602030759403c200510851418000000c3d400058090003d0086501103003000b5078400380b1040180050b4003d40c0801c2c2540440c1e0700c250b02411001e032040d9075644450a00785e40c2095a250100d00107403174140d241d80a0305081142402c00d11059000d840103116503101103c0d03015020f04040a5111003e20101005401c0c0005040c1e0425040c0a4017540c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 968812535 1250 968811285 968811289
    0x730050c0d02011505060c010b0901031505010b040605090613050907030f1b020604380708060a030209062202131a030702031603020a050105240a030f02090601020f061005 75
    0x11903841106002e583c140701d1000020340681010405440e010307545262070300c01342c0f06c41c28090f1402c00c1115401801e24400031040c081c42521a04a9140103241844540d903203040e0000584114414600040c10a1250700700071700d4407200801410403800401200980ca410014031844010755811010035521080410b03100305501a00c3c0c0001c440383c0300480c1480858001945034540140003e21594080c1d648081c00b40e419880c01e4541e01b020514000074482414ac802140c5c05c042e1380a1010800e01e000191083c5498403000701a240e0150410b001510317034105201404400e10552254102c012030848402089803024100510001090b01c40c001d1904a08100718050368003042002d41081007084145500041202e2006216a42800c105141070030304030708200e00040020020350a102c02e1103c40c1014020f420b440603a13003c0d0100380d0303141d00002c0141454061200400d0455440013032030262030003030015030b403108040c01583d4825100b5064942001d80485c0c00741241c408140080c0000c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 968813785 1250 968812535 968812543
    0x40c1106010905191e020a110f011505060304030e06090402280305011e050f0f10031e0903020a08220b040608060d0b040f02032103060f03010603080730050c 69
    0x10310f440a803c21403100010340440ca41d001e4401102e8109400080e91040140f14420340c0001d00e1408003680c0a27030b40d030b01d0301c1e150281c00300345140c3e92420004000428141f421343c08070b07401143d150b00d41c8800003100d041032000d59048a21041e80c03241e0300b07203c1707220350001287c555568100f1a034040100096489009411240c040c0c02a04200c0108642c841c2841c01c0c486c12072040d544229400785000c421100010030b0061042c03586c41e0410001c1c008240d940390550050384d0017000e440951030f4107810f8040403004a6080307030b4020380141e101e80120804a54600002c040c0019450200102035040680c080e80450784c1e41d12181d812280080c0401007554850141504248203da080c0a0f0b480710343c9031024051409800500301c80f1581c2c42401c1150740c02c00003203c0c003400404aa00490b040b4881801c00b640007102c0c0d240c041c00e0a000310080a01c1c042c4119415603070300225050903d6a0f030f0b12040940d05482c200507512914079058040c20400003030001c203425680380d84c0ca07a0794101002c45d1600b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 968815035 1250 968813785 968813821
    0x80408070b03061e061c0209010f18140609031507120204051f11011814060906131109150112050c03070309062403020901140609040c1106010905 64
    0x500801807060040e155100616407260843e40186004441390090008800e44030703000c4180180280c0c3c107500030700022260080c0520748800d1300c0300c441d070f1481c0708030641e03030304410a2230180d41000c1848107100c1160100c0501c0d8807480040d28983c140840b1360003081c5800403606a0103d80b041ca40c04000d40f0980c050b07060702e1f070201ea5030300944c2440e1420000c03520f80c0718642c0c14980d4040c0b80c580f0f41d004240c030601c440400d00052000074000d110304025044c07d8242d84110075901c142488581c4407500d0030010314540a42109002400300380c2e110251060f881040c10740c101c607400e80703001103052695101c0401502070074450071070b00b4280292500241141a1062811000134100020400b02850141c241c0e1b03803002550030b002c240300c04036180c0300d001071143c1c1c480c2c250854140312001149001051030b6500b038074401d40e83ca801c180d88030741600c5400c070740145045900c14002c1161092030b003029006021815040d0a0421414200704517141c01c1c03503401d800c0341021580c0c0d90100306c9102e4103507581e040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 968816285 1250 968815035 968815049
    0x30510021603030209040212040b07120902090403141201030c0905060118030b070905030601090506010f020f0a030c0f080307080712020c06010b07021207060509030114010e06090405030c010908040807 88
    0x803070445401d984610700340c1410301c007a06040d8041060b1000b52500d8044800d940008901b2076280d203042d00d40488401801d4a401d4005460380341c40541d09503240c460704414a40042c0b41c2c5070b01d41e139030f503604580008645810000b400e6003440300b044440118291a070103580314100d00b4900c6810700725030301c2c00c6070fa0040a1504100c100003c0300030300501400c220090307d40001440c0318585d2046010b0b503c0416907030140390544910400010420340d264805409010242d85504206d1010302c01207940311a0040c02c400705401502003013000900910300a01040c0c8288a02c14800b0b175242c4804840d0b0300b04582020104100d04100700c09503512048029040101010850815800480e00d603592030050060120089000661109550350703070381607811000f100001c0350101c0340c030360400902030780282c40c030580203600342a0b00780c214000703138044907043e54400c078146161741d62100100500d01c900500b058516010421401c4038003003080c0900e180030b034021080f103540c5a140603c01881c0409035070002c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 968817535 1250 968816285 968816287
    0x23030c030403030509030f0409240305073317180709050c09090106270302090402040c11010c0504180e0316050709050a05011d160c0f020d030903051002 67
    0x1050a491058a4006415143c002095030b03c448051340385110b12441001c030b0010200f40015014200d4018003144080989203000030030b0104504003468050780801801e0760803400003408130b8201c00001452096040d8122194010320414801004900c81d2405002804811541c1061041a0389080d0402054035201801d02c003051492600c80e0414001c44094a407101e0104507980c1101007030341e000c03050041c54410556035942c0058402012420107200e015004203892100c440304284000c00c403034010b8641c124541d55942000004d100c00b804903c10303c0102d490030307030f0701040034810005288102c1d12269a40e604200b80e11191040c00c44601c1030090900d0074114031704401000f56401101c10144804400e000740c030704142020900e0704141c0491b440d010030030085814540001e030488128441c00358400160030b03080c003603a500c00c036240e846000d502914010420310811040300101e000d030496611010316a4005440002c07150429000100840b2091081c444240150700041141000031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 968818785 1250 968817535 968817541
    0x40f02210708010603090c090e0303011802180d021201060f090e0102030603070b1317010219050c0601050111030d1406010806030708071214010507200c0625050a032303 74
    0x2840350605024130400c0540750a451000c01005040000141c1a0058144444540c1883d02617594209206181252700d6655454800d03140078030031228000039040004000041050510422030703402031080780c0001400c50507245015080c4120b01c040d200c000d908110f0585001c0800040c0d454000250840364410020f0001c103a8001800c841280c103a1102c880c0c50f501c4906101104008560210404a9106240300380074641035008100342d100d003641202c1707106081d4074200c600d8018490160308a9111100500243d8014104a805224102e0449203007036482001d04080d1a02c440c6d6843d0348070010300c140205507801107480c40e8001c0b03003940140411403900b111244c0d1840c407442080310b9084014002c03420f0182000e00d42202000840081c442810034040080c441d80600c801600741c000c020030001d901c0c2001040c0300400382001442141000485030200c0030003e004a0500d400d2010002454002042849241012070181d03c880030740024014640241d03481c0c0c030100d010780c2e0b1010010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 968820035 1250 968818785 968818787
    0x1807020115081b03010b21070605120612030f1602270c0a1b081306030c052a06040804090c0201050421020a050f010f06090218061305040f022107 64
    0x840382154902c0354032000c10703c07822008280140415180701e0b0300701244142c81c06040c80700740e16001f45d104003d01107485455071024110b6290103a01183e08001842d0700105000d407400800c0c032a1150500c0d42968605000c550003002c0580c00301c8003100c0c05c0ca000b40110419807a00440c3c40400040c00100d41d034400302c00300030b042c816003002044043e41e400e000c01e1382d48002c1c0c0b003400540c1e00001070202c02154680036007058580f0b03410042001d20b26105000d40883c01921902609041d1526500e88900b820503844a41c0039181441d6000d210f03200d0001280401d01c402004054011406400703034565540c1844c04000507503088054140c15a0306080a100000340c910504543c2800f40700b46000502101210490410907c4c1002600c10710449a215003036400651040c0341c50340f0391080c20030000d0368900710003040c0d000b8040914281c0f03810744294603080c1000c07401060b4507421040d503c9441a10303840020100c4070001007650a49501180c103a00c446909402c8a602c200603603400c0c1c1c0d19141541c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 968821285 1250 968820035 968820043
    0x181e08010b1504060f051c091101171326030601170105030709091b0602061501020c030a032a030906110105040b180f0f010b0901050907020a06020315180702011508 72
    0x1084008024400350103065052081e42501c102030000c0100ca4a0489034201407c094452003100362155204e1200701503056000c1c44141a4a41141c00901081c1d0341c6d6100007601c00b2180304081d10032034074510041c100e03002e02c07120b9a151902240c00d000e4507410610b00050140e403030400c403811411903180043c005680c8c00250071045603182c4002154881c240e1601d5040703a050010010355007001c2c1d0002040d299004904c0500c5818000c41010510041400482e60750300002001c2d60507401c00f0304040c0c046481484500d000c0300100301a10f41d20680d0070a103d40e2800e85940c10b07400103940b0582031124641c84640700209100c0c910091001742419180d41d001110003a01c014484a0321202a2401610a003e141307400803851003941c5100c240502840d01034201640700c03901c111014000852180360a020060040009a00400c2d4150b03a581c2d030f26000350f0015143d07003058800780b030080c00d40d80d5402c3c1d800100b101c042a5044201e040918000c1c2c2550542815160030b078000e06010701660780006 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 968822535 1250 968821285 968821289
    0x9060714070c090c030f09050a030e03030702010801150c020a030b04020307141e031f06090b03011b030c09031749020403021f020708031207181e08010b1504 69
    0x1000000e842072007110280c0081517181c2e40c51b40b60a0421070b50400380080425411000e038081c2d25150014030010701090341760701c02c078000280845c01900c010700100c118040d002c0925401828070402c2048aa000070782c1b000354031ba01c1100c1202420040000314101441108010030078009801080c0d80901c0001e00f6080e40b80e4003040c45540000510f0b0055681042a420540c00b034501400102a0000c46040500030380e0096841c042c0c2803020060780c038101440740303c9880e101c2403074a201c200c0070745c10b0860180441c0b104140800124942c0031002c100ad4914081c0a8001008a80e980c0e41001d41c044210b4100d6001144403a5146409080015a000701c401c18058681c00d03079400380380000c040740d8028000c80d0000fa4001145c41e18016480c1c074600c014032003c14460302184c0c4000c1d9a01c4d081c3d6624400c88411040c0e81c02c0036030100d034800e4000d5806c850640a540800c4000c03940307031244010b1060810820f2640c600c0000010040c0100c00c0c801c0300069082590b45c40d44132500400302603941e10880c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 968823785 1250 968822535 968822549
    0xf020712080c0a0b07050c1501060f0815130e011802010203030105040c020f0303010f05011b150504020616150c0c0c060f05041e1d06030a0b06030a060509060714070c 73
    0x14690001c0b001400203080e082d52101a284543c203000310010f1041d0080380101300c203842282403074200071451404a5040311065038904040c6000442d0803640030b0000b03031002c47c000740300da803c2c00e40303a58410300c46003010044000009030f80010440c015094039001c1a01d140c03003d02e910b0710703500543d07404411641520401d5a010840d1030700d030303a030882c0b8114214090946a010100000c0b99034030301c1e00c1d44541260426030b281e603509070802c070700b030030704180100c900600d0107240c1d9a0b00c0000080a400c50360f40140010017460410259000030a02102c030b0030021a4920200040c41242c0030040c031030580c0344105858030f54110451a03555261040c03050040c2c20602c0325851503e0462071103041181c0c043c0108100c40042140c101298240140031806180da00303284684101201d0303450340f00c02e5442030a009006101c1c000b0b0584400841c1d0801030701e244c0d05401002c0c51940400c0c0e560240a010b40c0b00c0c0c00040a2610780b254000348000c4604900840c401b00801910340441d001000d030909407919 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 968825035 1250 968823785 968823787
    0x3030a1404020d021905030f0c040c090b0403030e010504081e07060c02010e1201060f120507060c0812040213110414010206040c06030b06130611060901060617060f0a03120f02071208 80
    0x81d501e20035a1720405507010590501c60080309000124011454106c908001e481c14040e5880c008415038480281d4001c131080400140030070008640b0030b01e83c40e4604803040c1802c9290645903ca2035083c400501c24203200d0703a1060004a5071220100040001880b41d031914400105060340000c0c40418442009032081101031494440c00f0340a6004100030700d032401108440c1c5a89a044600c0d008103000140c0c0d181c001c000000072868041c0050903050f44c0e00c404001d1801203211002c3c0c98a1502502c01c1c0d820030344034444a4003560481c800c80120340800122280c94600e842c5210b20050640c849060441d0805400d02c40081c2c02c9801e0b40702550b0030303402d01251010b007440c0422068011100b031844500c200344070000d8002d0b00100701c0300c8408114030540d40c080d0b032854401c0c2d081c0d464501c500000039205034915030b8080d140e410100c0d0810710043c051064911048000380200d00541c1060b941075907052076202102c2d0308107407441c46080c3c0e540041c1680e42d16207501e00c0464842a40f0240c4031100c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 968826285 1250 968825035 968825059
    0x60519030c050403150b030109031101140105090a33080c0d0201141c050f0402040c230a09080f1c1d04020c032206090501020105010e1513020c03030a1404020d02 71
    0x2603a6080343c44100d1007e0020011103500d402c0041814250002e59440c651804d200b4010500850364040d0695001404641042c4c0b40d00c032814000700080760b03984245440d50b85541e03041c0000a80d0050042c000000408100750611450b14101442c40244520942d02181030302c0051b40c00c0740ca170b14103109944203c25125450080d5104c100c0c0b90500302428400c0c038140c1003003001c62010200900860089d5005c11065000d00d4050f201c214030341000a40003210085a400680d800200800c5500c045241c01e0f501d10350307200750092404040388820461500606c0380d1140ca600128018904182c0c075250001034030360444d040c40380c80706907441c2160140d5000603403004000b804008890030b5500003008030401313040721016246458224090540080c2e20000c0000c1c2a603c1401802c0c107880211818603040e803599004030460a8201008940007213a410909417424124406030290720421805580e40c0c0ca440400c581c00c4401c003040300103144214900f0700c00035841e015441c40320554141c0700b00e00701c0343d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 968827535 1250 968826285 968826323
    0xa0203120a090801271e030519171609030c180b030601181122090b030d090e070c05070e090610030f060c140406030603110916050d0213060519030c050403 68
    0x24000c080c1080203800c01b140c0c480800d80e004009003107038070340020b403200170300c0b400001101c0740f41206c06090f0004540901040680c01107e000d640c108140f4200362201c00d95039a10000e005c44a42d00c044440307210285010160001d0340500030a100c030841c094003043d070424064441c10044c0b1340402c01c1c0240d442c0e20300308ac20410030b41100d000380000da811680428010b1645240c403021405100e24060800c0c006a000e42000141c401c41000340303407282c00a29007000810026482d004000e001041040303508131340403c1c4c00780074043c0039001040d5031182515298440d10b2405001410070880005041402c00110f4840d1003103001081c2d0040d00451341260102007140c860301c100700c0180e2014070008001403041d070035500c0700080780d120b020320000e004680c2c010019507080841d1980c481c010a401c8800135184903100400d01420800780040c2400c0c0001c0f50a5280003554000101003a00018015444440c4010691100100386001e2002c0b2120f40ba0040c8640543d00c40101443c11507900d01c8000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 968828785 1250 968827535 968827553
    0x305030406080a02040e0a020a0e01030b1e03070302040504080403060e0715120b030d020a050c06280201020f040909050c03010e0c01210906060f080c030a02120a0203120a09080127 79
    0x10f00506e0b645030354038200791400c107009522884401d000f140c0c041003640e042d540a405600d01c6850f0003000c001c0b5a885041078240701941103244c40350315010b04080030006035607074452280a0740c0505541901c0d80e08501e0300c1011550801a81407146d807004408000c040120f40c2c00d0219032440d85010b070550f400703081d504005041c003082125818040c100004190300c2d800213030540f400b8003550464255202e9441401294030480f605400044201c0021486940b050203440c00390300a5031000500d490501000c0500603005a0480c203075a40c2c641400400380502013200d0188000210000c10002c1d4419000039601d0f00120030840c14000c00300043c07919408080d6507004c801034450414002d041ca5450584d0083c1980c1c0940c00301266140e501103100d802c00103080c030303500e0b9014006043c220290340800c640040040d03034220007441000f40640060310180604001c01c6140402c00c0d480303cdc04800042d2140100307400040b4283c1c500000103210080000300d498000d00c03074550340d611201241c140840c203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 968830035 1250 968828785 968828789
    0x909010905040f080d1e0227310f0902090a02120f130c150f0c050709050c070503130e071b11122505040218190518100f0305030406080a0204 62
    0x3620500340d004d90346d05d03100c42d00280351002030f4a034008005041c2020b41c03c0c0030805440700940100761038003020048003203100031000c6049664034500c4840042c0c05980d0540b138100032038500741e6480c0c802e9501141170000d8010303008a2100170944c00c041c0360902e00e44460038014040000e441040004c03440c40d10814408150302500000d241800fa52103a440040140030705404000007600d01b6040d02c0205c1c0715892400065030700101400c981403500100c40007070078024012201e95001000030400040e0200f0007000881083c850b07034621360749000003143c065070004240605100d4205803902c41780c640c00307110314441075120720141c11420490020401c841c480140150a0f071090f03588040c2401200c42403000303600488042849199107900601c016401800f01601140041c20306803920b6180000d801034004000b801d140e03104590320f800140105c81000490f094843e600c8042c4440c9800380050754000c0c144803940240624075503070b1199680d106a205910030040c91340e02181d1010781079011140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 968831285 1250 968830035 968830061
    0x80c0105030f06131b020c091b1b121209010b0915041d0d0c0b0603030403080a05070f060501120b0c0a0f1808060103030f0f1806050d09060606050909010905040f080d 73
    0x403903019581c0c000307555501f80014140c400c10b04000001c1d00462500d881c5050003540d4032200d0b00700044110941c0e000e691040d1100005d0051003031001d1284800c130040c00c000c0440300c5100c215414084061400c54550012140c040c8070703800100004407443e003100c104140025140018803014a002c901d04000440710480700c64000c0f0b032410200075502120002c0801e00581d080030719a2580804c15540348200e102c0201000000e0060059890040014100701d0303004604007103e98885030365020898100742c0119001c0d0070030f00000000d221065007803d6201c0c545540040c504006003030090701c06940c2802003800c02c40610410024241d424801000400a080444215503164600a800744100b4021040000ca8503641c00401c05d02c510720280601c0d0065081007401420641c00b1951544007503039082a458272107030541700090107445400011b114075038616441386852400c21000c07600607070080d00c4036814441030001168201c91540080340d8041c01d80c1b65106104031091018060b0035807001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 968832535 1250 968831285 968831321
    0x60708030c04060f3b1201020318010603021f120903030c030f02120106260906010602192a0801051602010f11040b0304050c060a020106080c0105030f0613 68
    0x2212401c0d04010304151005604e032000200b044100c11110440562601c48a6030030741101d000b020906a1800b103905840038100190b030404550120b0903d04683c2d4450340943c0d40001080705000c8100d0b940480c0710420402403001c40d00e1600051005801c1c42c143c0804c0c481c10380751414586018020a541c04900307a00300f40102021403c0140090048001c18008203042480c06141c81070203200315509100c00107103000007642050421a4600320b03100381410300c803030300c1c1c0240c900d41c00040094522400c1210000c128540c1446002418000c2040d0440000900034901800180c012020900c5400502508592125850601315002e081d59440114694600390a210b0382031525402e0f094180c209400074018801115441c6080703e6103c1038203c1c8010382404107104008004000b1504a809030f4100d955103800036000a03060380c080c8807402c0150307546a10400902c04280000380040c2001d00b80a411490142c502c0707081c0c01801049203200c0e8140e40d110701480c9045c1c1c0d1006149880e580c54034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 968833785 1250 968832535 968832541
    0x1d060102011b08040c0906031a2d1e0106050a05090a050a03030f1d030304050d02040207050f1c030c0e120f030f1b01060b0f0d0b0310050f0907030201140906070803 72
    0x1520030f078015603007642c800b141d00e20082621905800b5000c120b9a0114800d003404c034490548154501003c0c4c007102043c014002100c1d4a1501c00090441e4800c0c1c1c07910031015402c0007528801d500310319842e0112401c022000401046421000380c5004169a08005907640003901c0000c4144400c4d80000382c1c0558000408402d269100c0e40c1c50444250648030358040117850300e480c09024041c4003006d0390550003007100b84250305140c82c0e008819480688054145019581e48a060000b94410b141c1c2a610040107018011400c560381035200c5001d0808002070302210310001c001e400602c040d2070240340c040410400044040000b01e6216510303900b501d44a103044000481250f200c030a100e4403807403803105409911070040c810003045a031110104d624141c4ca054040b283e0f03070031201a08041540d907240c504000d440c1070001e410381c3d15644100098030302d0818145802040085c203402d03403d90108100f480181d812450001d4900070205945407100d4030303c40024664030480f00300510101000c018 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 968835035 1250 968833785 968833787
    0xd11030703060218030f101a0d0b1e010608010b1612021b04020408030412020a0806131a07080c2a0106170a210306080f0a1b1d060102011b 61
    0x20300005180303079003103d9101100c135041690f00e20102d0b05c10040b80e0003440c25080c18000d16806a0038001c0b00c3d8607403408081030003000072070324500f00109407407000012003003011000d4002c000d105000414040900e59504000d4018210381c8140103002a540f80092110440d240305100d4030951540046401580d900392030000b525414554454090030422201c03a4100307103000e009071400d940c3c1c4d0310011030902e4a40441a000307400110303000d036000580042c010a00480610025200b411a0003944a018265240240f002d0030611550742031445c1007014844102e900c6040190030103400300410391622180700803500c542c990207940c00c90b01e01840c00481c950304010b4000404491010034181040e07045598110b48851620a00500c07810310b81c1e0100704094640c841d900103400448c9800100300b5203a9a40e280790881e8408049500d81c0840c116108010210180001029150071000d15140c03410403410300c1c41503825001d00c4104143c00004240364400d6104000300b6000111003010b0b5020100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 968836285 1250 968835035 968835037
    0x3180f020a0503010e030f090d080c010504110a08030702090a020c01091a071e030207030909110c1605100c050a0203190303060b0901090302010507030c1704180b0307050d110307030602 81
    0x401207000c0c0203280400103031460107206210f030404001d000f842c586500c1d03140400b81c40e401106000d078040b01442c84200840c0707444026006140e80c0c600001024141401d00790400c110300c03c8114442d2448403000d0207503080100c2654202a0b05072000007490b11140b07003401c068040c1c8140003249600c0e064400f014400325072480305d4440142c7c0700c01405500c444a08503040c00660000c86c1070078041440e43d4030300c0c40c03084c1d00500c030640c041c0c039101c20a05d498121013819a2400591500340030f4010030900310b243c1e002d0014900c05a10b080410804a251501040300c1030508901c400900c5001880d40e000c1c01003d100d00501d045c0d005041e200c0034040003001c81c48098142d4001d0300080e00d00200800c244144204a5030f414070141c564130903061643d401107400341e000007812010840b107114000002000b50320084950740300c0381c00c85510381e4180600101400320b545071400001d4104100356155072004100007045d130300280e4403008564080e0800300100b540c0d544a03207805105240d070001c244643d642c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 968837535 1250 968836285 968836313
    0x91302030705120a0507020d05030a0f050c070516050306070c02040e030309061006020106030308181e01020a1206030c0b07080705030d0c03230711011805060105091012020906010318 80
    0xb07940404980360410040105c0d00211103810142c0e005a8102d05442d00880146a002c044100042014070205080005480090340c0e4040942c202058240c10040f0a01810524034200c0c0e030441ca4181c84d000000c1c0d0f03600e07030241c01d040c14000900095025500c07550004041c40d240001120390f01e0030070f089441e9070360404903081c1030f040418250115109106000b9681100d0b0107984200302c44e1102e515546ca000144581c181d0f261081e10007071080c1a090f00892280020350000050720350400d1680503260f85404032103104581e03d0094140005000030042000356030360074640a0725405540741080c2588601d40c405890b81c8408075800b0500b07000c681105070007081c169024001140310382c400c550400c00d212000b444a004510008804500c225440c2044c031080b03000101d131001c851a41c45040072403d0400355002d82002c001484142400000d041e08410340e20724444d07100b4035029040c0f4440d02d4851001b41b1400c050380100d0f095a01c290041141942204034403000c411140c5081c0303e02c101c1070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 968838785 1250 968837535 968837557
    0x518041404031701032a0e070804062d1112040b01090b04140f27030301090507050304050714010e1c050d0f020d031e051609051f0302091302030705 65
    0x101040c21044030040c0400e8100c90780030503280444a1500ca4100b104501b0501c00100c1c1e2280f101e0000d07034001c060a03240d000c0d040315103820355142401e041107001d44d81c86500c07841c19882000403c8000fa800400815400d0740d0580001810740501000e24403184502203c200070030794954180424040000002e604890b25880204014032046050005032108100403074003551105001170204240c1402c02e0b54029012911076880750b4802031103840d81c400300e4120f15215403000c0010b000051030340c400c890700441c0b0790512a09600d03040e40e40d2a07607501d66008680802e0301035002101c80740d001d83c4410720002001049000d0b01d00001241c5a94140c04c0103007540d09201e41012040c1d060f02580190441c15141d50207131040005000f0709070050000c413908690a8034516283e04a0f01541e0321600f0b0003243c0c182c07682541c52200b52001080c3c881c854020301e101d0340001d003110b4140080703288020290b844d5400c01507112054900021050388018440d000001c0c000810404011791101c01040d1944c05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 968840035 1250 968838785 968838797
    0x8150a0e030307081806151c0503160b01050f09180c09070c2609210d0f02160e1503161502100b06031803070c060822050c01051804140403 61
    0x80f90504643e6040283c5041401f20303e003101d00015402c0c114092050f41914140c20015681603540d20b61031540405011070030a50180300d544100004c1c14001401010101c075241c1c0400c03020b40c0020601e9074081e00500034600d50f4000d0b860448401d0003044040040241801c50f40d1800d1840034001001980d0103c5280f4500c072856010980c1e1070446007140814000a182401c0040060022155001c8122a0401c1c0d0031b4034400c001840402401803c1c410a0740c81003809401c0c8100613180402d4880c520303101e0319100800340400083c10103001d901510508a85421942c0306010038103102400d2000030080c0d005000100343c280340d4055020080301c840e403c4910f929100354206080f2445000199400706040011840ba14000d90a42c000f01c070700340047da8a4a0f44641d00c412607004d45600c010007240c0820108001050742502054686007885000442c542403940d45039140e02829642c01c0c1400700c00300f41250414000e000008250ba4060002c01030301c101e0041d05030301e90108590440020788 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 968841285 1250 968840035 968840071
    0xa0201030e010c0e0f12030409150f08030313030e0d2d05100209030705190609090902010e10090f03050f0709060b0304111318021201050108150a0e03030708 69
    0x6814416448105025618a04c8140b90142002035510249942030f030702403224040d41c08144c0041c0f009000405491070001090300c004031481808030b4440e8441d510700d1740d41240400001f81c0c08001ca075408640c06004a01c0f4441c9458161403150303503140c030f558100d0242040a0b04114803101b03c030861030800044041199a03e44000090f4054a88011300c0342c2c02c555000c03004100660003400c5a00e20050644074042d4071500031030050fa401c3c103143d038100300c00046c040001c16000034110010744a03010341405507001a07000640100310031a0b030540504881c101a03031a00b4456000303400502443d4020380c041550300d08100782d80c5c1d60640c681600c030340100440000d050b034091040780c0c1120722503101c1c40e00790f5540d1b4855100c0741e0440641c00e90803038040c0c40b020248200d50300c2036245080d20038103062080b40c018014090710924030700507908a030785000014072441100041c024104085850444a2952900d0003400940402050890b03d44004400d10110075040050644602842b62440c00c0d149 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 968842535 1250 968841285 968841311
    0x2103190f11010c02030906181012050606070c030803070311031602061509011a0d020d1a0a0b18030a15090b0907030c0e090f0f01060618080d1b0f050a020103 69
    0x103011103c40d180564410000081d06007040009800301d003420045240303001c840900400d1401440501b402c00141c28000340300121207061180320b800c04026180d42c2e041036980d580d94ac000e03400c0c0d80000b030244840400040c160a00c260440d03003c15003039030900d030b84034240071002c11055400700c1e0403000580035040000f60200540c00c480e0021074002040341c0482c1c2d00c0c00d1070030f5120f070098000e038108450b001c201d0800c1c0070030240014410005400000242e280d1a4110307179040030340504a20380302e000400b0003007154100520540f24150b108031410582808036500007840c4c102580d0004002146880445e03002218980c00010700c00d0142002c032485603900f4402e940c8501150000419040c0c0c4d40b8414800031807495841da03403019000741112840442d217001d4070b15291003501403584503074441d00103011169200030304500c04030320744640301c4a42d801e00c00c80a4031004103050301c00c100455074603c7c16044a82d40d40391172009400040d0055861254180355885060b80303142070740424102900b5043e98 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 968843785 1250 968842535 968842541
    0x415091a1e040503090103021e1909170c04230408030f01150c03140705060f0108010e011e0b0a0317040515030609061201110d0603020a0807052103190f1101 69
    0xd03075031103c00f840c50400c0b148010f400a400c9202401c0042810301c03160500c03651010014000b8031a442003070203141044690041075244182c0103010041800d03400c1040c52100004c05041501d811a00810141c50303541408000741554500c010204825401340800e00000c40d00541c050a102d219040c4641e0720744401d031040c11a03c440b000e0015482031000d00100f88590701603000d20b41c26002300c40c40c0103030603114640380134016181d08511081d8040100f240398424850100c8030140d400090054044184c0b0300303c61f501da1520702e40c603216203501e43c007229982c400250002440d400841c1800e100100e801300c4031990024001d05006040c1000c02881003031403081070b40c2c03003480001d02c40d4000742c0d284400d0040008100c0880b4082d50b40b11b1881c0f00045a880d00600f0450403000400180e180c41d5004001c3c0c00c00e201d40c0070b494113800c246801c1c00b483d1130341b08850807880c02400a0301c80d4059011011484c5214010480800d43c1d0806134040040303500040d00c0901c56815a500d101c0a141c0c06466070807 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 968845035 1250 968843785 968843791
    0x3020f01020106180906140c121b04030605061f0513050f0907120b040c020f060c0309210903030a031e0e1b0f090103050c12070503060415091a1e 64
    0x500f1144044d032882541c915001500005e11802021401084541000340100c20945d84007602e0400410203000c0282200c0c0303240d80c0081c0211846030400e0300520180010320485c0000b0300382c00c0d100c900098141c1c4034036101010008070201d092003e01c2d55024002e00c550418005070b402d450b00c0c144000340c54a40031100415456000700310b01c916442d801000e4a01c03001803901c9092036910342100d0700b007075912803052010185881c5c01074040c0710380181c005400c014009080300303c1d0910078418482c4494002805409000416540402241003d20461f44900a01940603410300c00090100c071455403640100300c00915a1100000d81402e03000355100761801840c0340102075010701740c900982c2c10055009040041701034a44081c00c1d500740e01080c0c81e84000d8205503500d5200f00c0014a1500b4540b0f00042c00808a4020303101c0303541030400281d1a65009440644400510b100020300b5540b16442210101c0d841a14080002a10110344010100c12610b1030342d10403141510b007218940b55002548 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 968846285 1250 968845035 968845049
    0x405030c0708011e051f1e06050f090108040804080714040b0609010e01080703060f030515060a030c15050d151707030c030602070c0305070605190311070330020403020f01020106 78
    0x12410790800003031380091800402244406000c95500c40000601c20381d03820152000900840c00d50b81140c02c2001d00c000180e00c10010440208941200c001c0300e082500d6102100b440c18410f40d450300d0030441c4036806550041039041c0038070200042d50b8146103081e42c4c0146c20940d0144030b00c2002c44200000c600404d1809400300303807034880d0032280c0e40c400c00031194046154100000d0007a05c890f2030000002440e00102e540d40c3c08100c03030208132000d40c079800ea40540c08417441c0e400c840c10342e40c0b5070891507128450840c03980c0810500c0171517103000f8010355550381455181000b40907829500112074075014428407a00e0b00c0400c5248034007200200740030f010340b90040c2c440d030550341c036541e59200291301603e400e54000c0c02c04440403000660500041000303051a58400e41c4071000407041c5000359548400900038140340c913013100700003100d41c0c0540315034940505111041c1181c120f10300c81801e2143e80380010074060740200b2403603042958090002d90f0300a60b180c04c056982080164202c86083c01004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 968847535 1250 968846285 968846321
    0x203070c1d041101210204030615030c060f120c1706040e1f020d0207080d1a0a03061505040c09080f0c06041203050c010c0e0f030a0b0601180b030405030c070801 71
    0x7401140050300f4180403e581850082c610240c2c0325809003178040d07080000d41d00942c0004041062118034056800d1000070081c0741072002d865aa00c0c0c3c5103600e0148595400d01c003008120080c80350040c2d50310711440521140a2201e0080ea080c010044020000f024105601c0350011541d42d041612523100381c210391030014030750f1303203079107515002450308200d2483d8055800b0000c012006880340040c1003442e00c200540340e250102520150107450500a10404002405a084060396941c100c80c10849410601c001760b01044d441101880384056004190003508250449284070742c401c10b620b00302c82002082d1440400e04c45852505c6108091199511040511081c4010901902411209486828014680800610582d007596000038a80c0045001d20200032039505143c2c40c4500c03040d42c200d01400b8031403841c1c1c3d141d40138240c0140c41d0034100400c09200300601d209a804800107441000101501c0e450306141042d6030b540401015007543c006c11130001500032050060422408450300d0030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 968848785 1250 968847535 968847541
    0x1050f0112020a0f0602030318010e0c060f160b09010b0d0f021c0b010e220314030603031b1b0d0c0504150510030e070803040b090609150a0203070c1d 66
    0x406542070101c4001e0b03074040c1a1a1002588403014a42d4600418807500078545070300e00700409042000d8600204401a41420f00d1842c041c140410110009c2c141141c0d9603407108140111045140240202060300a025081c09024401407a01c101d120311300c4100284000c01d0340400340b01d0b18a15114009100d800900713071180051030b24919002400224611804079a0000c0d00e0b0369001c0d01d0280d211101c0b90002c0010711050070451880c520301c0a490503c22100104c1942e0000e11203a6880600304104001002090407581e09004442c0d00f03120741203125408105414600b03458541800002c1808041d0a19007005420100c0c0314007161a00501541e40ca0ba01d82002d1002030070070518020341900c2d550f0004282d566807a459030310390f0f40255030002600d0f5a884007462801c41140c0143e000c0303a0080c8010040c0c820782e07100b2150301000075601d10307442d144c0340b2001c500c20304907500c0c80c0c02101c1c1c0040b40f41c250071039000002e8041ea034045d9140d01810ba43d5921101204907941c108000309011900c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 968850035 1250 968848785 968848799
    0x50306040b04110910060f0302212203080a2708031302150901090b0412021e03010612060b0603040209160e120a0b060f18040c1208030906070201050f01 67
    0x41c0d0740c414003c21a00001e048034000044124100319014000c4444048080c0181607010b19000740d03101c907a040441ca880516020011410803003070040d003602803081c00003403d00d09542e5100d1142a018040a00a4601c0385806041440111000641c2601d000d46c2e1210300e001d000300381d91034280c00e400300c481202c10076100c14280b03510060a0640d2841141c010740300585078540b2451b40c10510288141e19140204001001001e5076030140460080a1000b4058080155000c0c03180c2581218207414004000351003a10060414031503940c10751078682c0000740c000c0c043d0502d2903150300c00c240800c251450780301082020702050740e000e90003c0f071039000280500104020024907082034240303048144130960001e117032903200c4800100700e90029200401048203034140b56400541c101e0720800410104800319400c1c2c010070140c010540f401e0b0b4003003000e02c110710382c0d51005055070040070020858241040c080640c03040c3d41802e078034858840050320b1180b0610619000e403ca00c1300c1081643d181140c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 968851285 1250 968850035 968850053
    0x602011b080705031e250309031d0a0b0c16081506090a0207021e100201050903031b0c12070c080102120a021308030d060e0601050a020d0f0e041a03061005030604 71
    0x1198050850000143c9405d224008101701e2041880365114030a0804410f400340103041c0a240b003409150505d0751050001e03420011200e4203003090041109400f190000140b106501c0d90300103000040001941c81660300c2c00b0600300e07480707007041010840440d40d680340ca030b075540144004149001560408550140b9010101d1b50700f0400805001d0f01344550fa030005012010250441c8054102200f580d0500d400c10b0a1070070500c9145000030881881e00780b00c00c5d5240d1000800d010700490001e00c0001d60a440041034625613420007003215034103e080300c0c0030820382c0d000702019281055140d10001b0042014001c842d510740a103016182e8548921080030003a400c41030380740007001314182d40031404100400c060481e482101c3d03000706180b0310300b50700c03010103040150400e0b04110080081c010000d80004031425550ba282c50511101c0c60000d0044822400d010758a507441802c101c0102888a03170100d0b85000c29804800747e41050712000361050f085005031280c6a010341107100080d002c525914 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 968852535 1250 968851285 968851291
    0xc0201140a0c02040e01060b041a070b0c03060310020307020c0111120d05061507020105190c0b072c0102070911040b070818011407020d0312150602011b08070503 71
    0x810a0303450504840192040c81e048190080002864102c00409525080c0214494411510002c0024170b0424000020300e100740d0160110b03101029211200c1b5188400c2103490301c40e00b1074449c1c400c0342811404542f02c0d0780f05555442c03280c411101940f004042610131240170307100c641c00820030080716100541e0b040c84400c99200340340c018500305445c0d0711400710040040c0882c00c040000d040c03501c4010440b08030301c088100d50002c9014850200149d81090482d0000c100050410100c030840840403520992824402003c55000c41c080c81120f94000d605049a01c00192250440c400102c3c1c0d141440075200d01d4250041c0e211443c108540b068070b034020385c000c48032024203501d0715171240340c545503d0348920021503440d400094400307203250880c040c0c11415002460001c00100103080f42071540d024080c4080e20400c2200748483c209401500940201412040305014500d02210352084020b903610800016500740361304280c4c1e00c0b009410b07012140d501501e648480742c6070460700320b1b2150402 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 968853785 1250 968852535 968852537
    0xe15060a081909061803020721030c110d0807030f031e090c080d0f3f020702151b0a170a09080f01020a09050909060601030209040b13090507150f0c0201 67
    0x5680d402000c15414012000141c1100e05c0e2000b000c400d600d8002e2600c0d1041d030115111468500c41d400780c0701e0040d64074507505030301880d1a500c10103150805080302d044c001041c070f40c8968415030500c00c00c078551002d0240b45009465030480301342a083d040d81030380c201c490310b0080151903008055080c1c030f180d48610f40860084c170241c0203c68442d00414a403590000134800400c1b41110b1541c409a400034000407201d2403000d0711000c1541c58101810400903084220740301c669142c5501c980302c14164155444a90000d02c40b65003400d0704a0510000d5100300e0880810150070503c0001c4200e001a4042210b42e0150240013601c4004526108a8200c2d41400c0c0400956000016551300200040c0001070911f9000503521032680c14040e045a2207603010600a07a030020812480756004280356920160a00300503071307280e05800000d0020b1161030442944010190b0700d440040c019a803140200d64072640c11912182c0c2c554640124091007441b030200090082003207112858401c0c800004044d01c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 968855035 1250 968853785 968853791
    0x20c0f0f0f120307050a050609063322090b1302011205150604081f0902010e0d0501061208130b09090a09020112021c05010605040803040302040b120303010e15060a0819 74
    0x4903039405c1d082c00001e4106072941d038040428424256821300100e0740058a000c04124074244090540411030044405020180c11461aa00440d154080802d42c1101c2d50000d4410003101b601d00c10000f490100c0040c0c9038a03250000268000d84408841e01c135458058441f803081d000c44e10702c1c0ea4080e0000602929131818402000140f0342c448002500c040e102d2540a1301c003068001942c03402030100c8802c540c1445042112400250b6048191862081030a4684550381220750501c42e0141460f98080168080c0311003820040c0401000541104100c0001c4081d001c9ea649141855502070500c0c6568070485a4000c584144940c1d400003004610604040101d08120750303941d808c80e0840b010803660620940600c08501d07020744605400f4000781e061040c240f030705280c42c01d903607400b650100a02945e40c42c45003025541d20101c0180345800c10034112944d0b0740c0c4a40810309511401d561441d8003d03858521403400386001801d41e514071981d6654444255610b001d40710b90130804070142e01c00300355 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 968856285 1250 968855035 968855047
    0xd020d0c0e2b080c030c0a05011410030b0a062115050f0112150903030515010804080a110106090609061a04050603070f200f0d081e07020f0a03020c0f0f0f1203 70
    0x401170003d0000070340d05001500e035000c0079080c42d600799010641e801c58500f20312001c000308041c8081e01c0c00d0a40c1d03080040c4800c1ea0f581d40f0071040c000c1c10103400001e540c42490350030010780e0401801c0120b46d148115a1103914160960350072040d03820640e8200c007040b07010030061122091158800045134011030180c080920981000021210b40ca241a00001e07100c00c100541c0c01d10440f002620404286003820080c0f030144c88408079401504481c1081040d044018102e45409411940262103078080811182d682c5070004001841f0070302c02c038a940040d0000c0b43d60b03590250f0042d102212400781010f403035039560041c00c131440500040130000703210640c0782070880b1800c00c40e010702d451000340004194645151488915044112049004000d1010b0402994030b64948541181914031451a000f51b2a5000d05a080500000714960300d4401c5505508c285980050403107489401614800f00b0301e5070301424040d0303400800300400c1e0440c10300e0641803030505084c00c0510361200140203580c2484 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 968857535 1250 968856285 968856307
    0xc030c0c120a050415051936030303050c0c07051003090813092004120f0f150f0b100815060f040810050108150c0d020d0c0e2b08 57
    0x1401002402c40090404242800325401040c07809580c4506400c20a0600320041c13000e842c8400800030308000c010600800c0807901c41c61500400d01030b072120181c085100b0780b040d1008400c3c4603a100603000a410080881d6030380100310b04a072040b040000150095905000a00c101c2200100d4990101580d55240302c02141407040036107076034520050b920741c1c175501d82482d84054840004038840c0c00303100840801548030301d941c21201117800c54450383d10000b00d541440c10108070141c80242020a10401900401c017241c00d1030419000004030400890048201c4101140d02811003160400e101e110041c8980e8041c412841d44646040702840030311000b40041400e94212509108240b5008241807003005c0d0b09118040c0301040d006402c200310362400403003030f030742e84060110082c42004041c04103035466a08012100c0c15850b4000940d913070601300d86013400500d01e68100324006110300260002501d0240742d03800c18072002c110200c00c40620300035524040c2c0030340e10301110f00c03460070003c500c07583d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 968858785 1250 968857535 968857537
    0x50d030309020901050a120b040c090903050c190f0305130b1c051e0610050c01050f18010912030e070e0103081209010c080c090609181b030c030c0c12 66
    0x1511030340d0003103984040c0d84180055440e06030005440348081d8001800540a480954220685c120624800c65142c900b1300700034804c09500048111800c210a1a060582100003041d01c10780f01c02c02c403004820200303480a000403070701c9002007444401c1c64015002c030f440b4801400824000e0321070a60940d649080148c1c01d940903910000c400d0b040c00c00c00e203251030365600c155a4000c920009440e6080e03138081c178401c00e404005184c1c5101c1c1050035100e6011a00c1042030f20342041e0b8181c02040207040141500c00e00c0c09045408c0c013803803000d0344048000d00b00180542e02d0900d5010703040400c42e06040310160042d00c400c0c0c90849091182d900d0000e1880c240e40c07040e500a41c020f980640d134810b0380f80480d10950600034482c0701d181c1c1c100811104070070340c04101c0f00e6000d035034080b00c5a280c483c25400501130b4030514070074030b902155036440901c0350042c4000942c082c22400da20180c445c0c145c040404414002220b00c54003420003030000440c1e08440000403c90701c2d0b003010940355890200c001ca4015 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 968860035 1250 968858785 968858809
    0x6041407020d27031e0611040906120309090b010c2001110d0f030506121609050a0c08040b0618070801050109060e0306060f03010e030f130e0f010603020309030405 72
    0x1a8041c01c0c185507107a411542e210301804005001e070b90303c0f62000400320070b4100c2520004005c040701984e4010f030300840c0380c1d440070041c2c0e0200003803000c0602d85100004581050080b07021442c0b908000266408501c0162408240e054684940451421000d00d0003080c1a00b60707241488015000d085c00502c0242c180310040104007a0550151402c40004022042002c04410a1f51214001e2a4429009440514400c0c0640340204980d074841c40860130114400c0100d124a1258103c4040d18204022400c3c05503203c33600200120f1b43e612084100b0380d02d01514245c0031030390100204000c6a40203c0f0301e6400307080030f0012070ba268444000402e2400d012250a4002901140103000ca50f03407190a00c001007040e0b28108000507903c100090300c40501401051065101001ca106252429007000c1c0e030803140502900d4644292450611140c1c0c044080540180b64004000c60a8280380e8038440c05188032a040e040c03941e082843c20b40003940081d000c0140c9100500000840d80d44040545903 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 968861285 1250 968860035 968860037
    0x230c0c100921120e030f0f0a27051201180c08060f10090911032505120d0f0e0a0f03051e03161109040602040e010f06050f0306041407 59
    0xd9503003650401100a4100d45103200381e00d074290b0030006841d9809180c020780c500c611040062009000c1050601d540305820700c0c1c1842c000c010405903504250500904240a110b480740c0703079044145070031104c80000c01c0f6000498a1030b5040203120506020f052000480f030300a00000b15036030807510458024a2006048911075100902401a400240f010540051460702d82c0d6515041c0624503074050b8006014490b1440d643c0c80594007408088106400c2c0210060107965079900d59a820407088604007214141c40800c0d0100000d10b4140b400940760039030098030143c841a030318031008450030040e1308808420011541c0c1c04213810b075a041c10f16001495103600e0309004038614504241840031490140304181242d000300152144048101d41d060911074645d030000f1400307071130f10042e408c1d0140031301a08052030608003c10410103a00400607100341c640001451782e41d07200302d0442d14050f0300179140084c409101c540d60500c01c1d840a1904280c0040c00410076002207040300c1981034003114504 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 968862535 1250 968861285 968861291
    0x307150902130908090d02180c0d0b12070608040c0b03010806010e130302060606090a1a030414070303090513381014030a0e06010803070b0a230c0c10 66
    0x2811450110300048030303094035400c10b2180503c0c68580711894003d5156150040b60f04100b200c0456130303450024020301032200d20034000d034240310344100003c0d0081c41c12591090f1410106070460f14000c580802c41070056401000c24904060044542010281003100d844c0310164005c15890f081a01440c080d048090040c111980351030382281d0340008c040c103005081c0103034021100200341c0c04580c0c95840f0406981c400e55404145010548082c0103500c040b036142080c0c0ea9401060308403800840c01940520240c10180c1100f02405417038250605c8003c0200d54807450410903418040c1748652500c421900006442c030380c114440d6649440082028070384001c1e40103010140810114180c4000025152050500c0b074003100580741d04564010204041e0000c0005109049160400b03280407031004103480705965201045640c0e504084d004407a814503040002d1700d1690244208841c8100b030103245004600d048031880c0005d107024000c440d40c80c0040084084001c1e00704455205180024000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 968863785 1250 968862535 968862551
    0xc0c2d1706070509030307020d0213020a031508060712050702100f0203061905060406080c070c03392310170a060302010c0213090b460e030715 63
    0x905007040100711400303005090101c04155240002a15821035050395004590026800080d80d2040390642111607140002000080b142e0b0540011800d02d0018200ea000d403a1103980481c2c031400c04580301400164051035101031200c2c0742e0460f540001c03590064511044480c031001d8146c440100250241030340000920440f800d042030480b100440070443d00303035083d0610002907820710030384c880c4500704a5646d020801981a040c100d60880e030340201550b260725506c0c5008240a1072903c07030302041004480c0d004a8241c0040800c1c43e64180c103140090302039040c91804d489040101810110380f060800800b40c96840d09280244c0c00e080c50b0311407400c0408200c04c9051088001412441580e040c05410001030b40c12003080b00c00e40b82d0407124003414482c2c20b1880401000b64000240224201c0400d00042c903144180110303000c60040348a003014075580e062007114400f2281b9814540e60f101414010b04a07991744514420307032100d402d680c6000d103651107918405401d0101009500d80e58414 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 968865035 1250 968863785 968863829
    0x90c260c060f033111011d0105030a1a19031403031510020312070801090e07050d0303110f030a020702090703091121030c1006051c080a0311190f0c0c2d 67
    0x7028030440038007192036403001f008000206140800741010601b9520b520f24031840100039034000c0701d0140040d1405441d90070010b04503260070384509c4103940c000c1d2003a00c2c2c0c8002c41c501108480c4a102044c59083c44800c040d014482c00100600c200c40c1180401d002c4111411402d040103030249405a440701100d5041c56127a80803a00301c1400030a05500c9210208000d440e2010605111234041c00e0000c0d000c290411600710911030444d0b40c1290b1301d03000003080750901256010301900f5000740c41800d450380c1c0e5080b042d01258640a006020502000c6481840346820720700051001e2884d00c004080e01c1d0b4840d40b840c9550020b40703140c1c0d41c5410142890300b40c140d6510890000744000c886200031a621862852001051240050007880001410301440c074003a4000745034050749003020a54440301d40040b50032150f02511100d00103144803030700502c0188241a800c0c50756400007500640d2070f14084000c0c00d681546175490480b01c1584228451950595002100401204117446215031030500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 968866285 1250 968865035 968865047
    0x604050708030c1b0118080a03091d041205090d0804090c09060518010c0c0e09150c0909130c0b0a11060c0d090c260c060f03311101 58
    0x1081c040c6074000e0251144035040011644038038000f851802d0f0a0503800710049444505d0880009001d41d4041c400040c50503001035240c0d602402a640c0c003560a031165440d080c4140009030b01c841c100c0380400401c3c08510701441000110301c45081080c80e00201d240403031241949042d0a54080001290400010790540104008114a4501002d9050030000041c00710300540382000103000d00800244e03016406810000516038000e00d41201499458000030040841104c1c101540e024500b4900801f4480e4042c09000b0f41070125030340c0c01c1075160300510400307440042c0107110704040c800c00702000c180301d003c18901414048443d1640c0d0408188064080201c4003594140ea5101500300515110000196400c4220322000824500c00301d0030003424802c040d07000f40d6030b0006074080d030f200d14044000c400340d41d140401c41a41d910b40a1442041100e0144c0850f0b44003101c0108001a03003140b801054422290000700301c44e6005484010610b1440c11908086030491589015607042d0740c1c20070303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 968867535 1250 968866285 968866289
    0x60a0603060b040b28031a0412030603080a0c020a0e161b0c05060307030b0a0b04080106140904020909030c1009140d1d0a0810091b080606010507021f0206040507 71
    0x2d9028080105104041126400210760402e0049100401c6001c038500c081a01c0000396044104c81115424040c030441d48210300b48c801300c03682c050303003510307819614040d000d400100c903000108c05040500195042d10000f60000c812a031014202802080b00125002c8090040c07903140d81042d038000c617102d006000510b421160841c0c04511000401c00903065560440559000b951050307103903112664154090040a03080c0c80e84890702400100c3c4200a00307002d0300031103003074400a10500b651542c0000b01d0890002106400c6140c490016000d81000ba032b5044c3c200415504807894214142c1d4050b051500355405101070340d4442c503840003840b000700c0b84410036070060741c058010035004000c05414080c03040c1e03002c014240d33039000d4152aa950500c5810080c4005429100c0041c40426880c00420f440700085410b0811842c1c0d4101469030305040c032040d01e1000c0003d0015407510001501ca030740004c0d40481c1d2003640324049092265441c43c070381c0030034540c90b00180020305061501504201c450707 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 968868785 1250 968867535 968867539
    0x150a080c04110712051804051806180606060c190804030b0a060e16091508011e0501021e100e06041202011506030e0316050706090b0a0f05030612060a0603060b 70
    0x14082c26010888652050b28038180d40d051841d81c508039a206c0b440c182d01d003542c407154028a48030800c0415000c4648110310700c8514415140c1a6590040144e141c2403000050b0495030b105c400014107038140100149204803159048800340e4041103903800421120072001c80c0c049002007030810811100d1119541c111081c00400c2c8441410f00c3c01240790035000803d84000410300e01401c4203290f003394041d1000e00243c1d814421032a14000020b007403401c0078880c0000380c500354110000344ae00030300190300640700305902911480b0160100c175080c80c00c40b0000c52406008c0e0652100140b0140d20404030910382c080042c1c10a850603090002c05107881090304015a4180015101148001c000d8002540c0e070f40d040024104400c1032015245001c0d626051860505071507900e010700030001040022200c140c2c1c0c0e50701d951621043c0304416800380d0880c0f02c010075002ca4860a000340220041c6501140140000251030005540c01d031600c1e40030788503800a103942c1c41003031040c4200780c007803d40c401d001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 968870035 1250 968868785 968868787
    0x10e0a020f010302090a2102090109060608010b0f0c19120306140d05100507030227101b061b02010c0905060301050f030a0c1e06020a0c050405150a080c0411 69
    0x2054000c550811814503501e810180d000861161590b140240d00000e0004410340d5225030116500440f0441c8113060164417030500d241c00020625124003c0006407031180d506d8502592900c034180d5020b800003030744855101424045980000c0042000c2d000c00710080d440310781e045030b2600380015111316040c08074040505110003031209602e0740e003213020881c0003a40c11400340c50107810300605011020b00d030080003d00380000e108889501d6000703400e00071040c440b94410190502644d00c1c0c821500483d55800514115141003d540103409020404420844101c110241c0e540c0c0e503011142e241809882e142107984040c44056030900c1503801100c418200462060308102c00103a03a40014070940b841251a000800d4242c0c40501a0850260740056000d1013070383c80f140c6412441e501140f071220003903010080007410078070000d4900320050300281e55641c51420704052101400f00204001c03604c2080e1220041640c8072082c500004101d04006080c00c1c00a940c100001e0302d003586016640148 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 968871285 1250 968870035 968870053
    0x90501120b2206080a0c0305120a020c240706060905070c0c0b220306091109160c080906120a20190e04020d1e0e25080d0908010e 57
    0x11140c000421030b0326000801810051048020760151245070888072030345c051000200200314114100c2c1040d28451415980c02044130b691072401401911100c0d001a4400300399000141002d007884183c42c02e96603d200081403654102171071070f61100d14210740c000d555040c100101038561081da43c10445500d0a0900c1c0c2c4080d07154950000e049014000e4504070005654080800ca070b1046500861280100c03600c2940d81c0c00d0400c0100603c01059500008100881a075880d003484c0443c41030071074a95409080309064011100c682c0740603022560620204200491640c0b4000a400e41d020307161008212450070388508000d0391101d40322082d6540900d084010b00c03540e0700c1e09813a00050703100d550b8000c01040c00c07411a0b15050b40c98402e40c22a00c001080c285040c0b15070850011140400111055103186603026411141c0300310151840780c1101104500700ba00301c05044d0304215294141c4116a03488001480c20840782d555aa404149410360800040c00c1c02c1c00350320103819506003d49500c2c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 968872535 1250 968871285 968871289
    0x20f0a05060f0310090504030c06060914180c03030310260a0308091204230109180f021218120c1c050d090303021c0216121e090501120b 60
    0x8001d00b10b400410050100014040501c04241c6400414180e20b0a111034105410050300380040301406652440c00c1c4000850940d141b4085c0110401000d41c0c0d54503d07507150b60b6035158030b22114588800a00403001d42181030359080000e14013403409080e02c0c014103498503c6401032001820030000c0408140c0501603110000451200d00c0ca50f01400d00200f01e80e5110541401c0c0148000c8600200e0710100300407035030301c00c044d981c07030110303c03a4008018040840d50010740b0f000340c2611070407441e41c0248940109810742e9401070244c400c81c104016040c50409810640034110031198405101408803a00e104e9103020011040c20510341a5403518000300c2c601c1080c0c1b205040641c1c44645030300c10380d8004242c3d118000f101c0f0107058049007040448100c0c98000c0196200b4800400820780810b0182041c0c1d03858400c4900303214150044090108059407044916802d546414041c00355042800005102c41d44a40304030303003e140e0304c2100c01400d050024021100210341c0e83c04261400c42c0001442d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 968873785 1250 968872535 968872537
    0x11d01060f08062e03060203150904020d0620070b06100516030e1206090c13060f150e0603090102030f13050c01080c0c030f0309011a030316060f0203070804020f0a0506 74
    0x1c1403030080b255050358074001403001111360782c0c0b50711840e403000000c00006200d19a0302841c0141001e1544001003600c0100b0024044010345010794022a80244400002c2199205a0440a00459902c0f80802170403044101e908019010340b500c1802c01c04008161038009032100241486040c01420f00910b101d50150101003202c00038113004512035120300b0fa0340ea64064161281084d41182c1c240d141141442d40c80c1c0341055041405030f0341290f02044d00d81003500440d025100140c3c942001e103460701f030344180455034442843c014419903500914450301e80a0040d440307503450301700261ba642003201503050040401040d204c4c4c0b40c0400050341002440100d482010f41e4800d2806820f00c0d1540880038519102d41c1000a50b90b01c00000c0b03141e003410042002c0d40c49003401200810560603219002c8c480f08025800e06c0f03501d50000c001c04100a5454515000d090b0f004010004005d40c41d000c0320403c031303402039070700f030b00402c2c44002003008501d80114844030700501620040c1d1134620b047c01056072 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 968875035 1250 968873785 968873791
    0x703020a170f0d0e01020702121b0603070f0e0402130e3405211f090203091c0509180103020906100801050103020702012a0c0807180c11011d01060f0806 67
    0x1050304c446603a03100c0142501904c0b43d080c1c005000c100200000002d41d551280b00d03240c070350100100044205502d103806010342c0d02c56480307a1503095490541d05400c40715015101c21181e0302903803c2c00000e030108a2072911002408002844450905284105043c407080540000460502031001108007407061010040c3d2215070b81009502c914110810f00e0a450b1399024188030459203004003c901e84003070185110140120290044564075004001c050307200c110f0341c4000340d038002414022841c0440c10360020300d00040c82d000c1d08040980c5c00164601410304007002120401800510030340c505021003541000c0221400d428020b42040041c00080d030501c26113061507808a81074042d6402a4100b030040d002c007880840c2c500550140140d000800c4130029904d904242901040300040010f131682a500c14001406120f41d240c101d010107418501c958004101c105401c070444060240100c100d05403000c01207400d10b8206d4100942100c02552101418550300c0f1010002488089035407a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 968876285 1250 968875035 968875057
    0x340e010807030f1e060503030711090c070515070e030a02030718020f070f06050907063e070303030f06120f060b030f011505010903080d050901110703020a170f 70
    0x159a80d0790301401c0c0c0c0200030001003041200d00f00100f06111280700c418201c080031800c001003114540b1042815a00c0c003840320001c11400203110103903010b150409000f5403102c7c5100f94035103040f900ea81c42e0b6080c124900b1480c45850001d01c244100b440c1c0102c00048451015401131848641540020340d489140748100201d50922623030090040c0e4850701154240601414915910724092500c3c00e222501c080081d1181890a0f020465030100814640103c41f0103507180c421040440328506100d8648202c1000141007400f903c414842d01c1118a828202400c40070305002440c0d4100681616041000780c0005440c000f01444a55007201c0704250040d004008154640c0b01880d02c80001c10032800d009905209408010040c40015000032007402e00c001c03000f040e030541e80d600650740001c1502008024130010b0001001c900b610342e1040b5031002d044000030070b40c407a0003481c4010980c442d00b070a41c010b800154555041c418550507612045d054982c04a2511f02d440d00c02441c00e02030510707080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 968877535 1250 968876285 968876297
    0x4030305011202130b04020c0703050606031e060c0c03070609030c110613120534080102070c1e0f08030901200d0f030603060f0615140f0a090e340e01 66
    0x8074186d01c1d0340c0e05550100788001c003110009910b030305105595030b0040b039003a40b10303110741d01c4a4025040079140100c0c00005410040140303480d404a240710300c0c6c0004d018810180300070302c00702021071a6802481c200303038041d485008103450181030400054605103803260060400b0800e941d03d0300070000c0c80c20126503015000010b620403514116040550112aa0b500c61a40030504000407440748050f00300200006d24141c42d07665a00740880c00c3c1e0081b10300207000348850102c108610004069211445201c41621040c20703038403000701080740e03003803034100e49480e510114100805581112481d240519000c245400300c0b0002c121640d038800c0340074081002c0203041e012074030107035009421280c041c5074059010703c01d41c0864081500104941d116560242103011035002314035000b481c07488481d840c50219036262009928400c84c482c2d0181c8822810044180c400003402440d595041e40603d2100700c0b62513228000c0041002c1445035460000c0c1d4031040a4164210103400c5030008441c18002c1c2020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 968878785 1250 968877535 968877551
    0xd03020c04150e1602070f0b030a0c0c02032a09010f03030c0309080f0d120c080c18040609090506100b07020d150519060b0403020a120204021b060403030501120213 72
    0x680c201c102da580a165807001a00900081104030013480c0c41100280e402c40f003400c1e5031044146910b04e00c1e4030410034510400c01c04181e0401c40303078202c15959801d600745a905d0815950209240030a051803c15516190143e801041d6140c08200c2c201c03004200c500c4001541071040310401a0900c0c4030040600034224071103010180699142c0000700300d03020a8908005091030015100ca015140d0040040e100300401e40340754a16200d00f445e40c00140c5d50320344295840a0b00d4981d00c4c1d010490310540122640758040c6075540d5401a4005400c502d0000300d092a55850310501c0c0590140c50840c600d034860380140401c5407500191014990103c0d01c896020a640c01c168425400b400d8a122100341072400308000d8600000c50345c20507080d401002c0001d5a130302e800d081c0950103107000c025031007016a90f042000d52418a881c181d00c60000700010300c0d203024070b075242c0700d0780c8030103441488075400003c100014983c05208050040030506041c1101014a40c0050340d04442c0b0103115020b90350310184 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 968880035 1250 968878785 968878811
    0xb0703170a1e230a060501020d050c0636011a030a020d0b0c0735040b0f0706060506161a0f0703050a061e0e010f0506040302100e15040e060d03020c04 66
    0x100918403003083d00c2d254401e00b01459031402400320380c0078050151242c50a0381d00e106220310220342a40b000300340540450b440c0d6142d800c8180700c0500c0341041420700070b01d001d00d02190340030400603c005d11a0000038540c500c3c2c24140155040f441001c3c1c4607400020202003d40c9079001d8040f00c0b10780c40782d0020710b280d45510112000d8005e030300c4050b0046100c10b03003c1e0b140f141c9028509078016505808c400c54590a00043c1132980300d1070051400340c0b2420310404007890342d40c501414032148a6400856065101c00100f043c0b0340215840c10000d0042026075018480c9a000e500c482c002c81041c99640c903c2c1850f001031040c20060100d108241d6103200186106060381d100f64080c000d40d07030ba1402030042540041c01505c120f400b41d04864100b2800001c1d650680400c0030003190405010103082038956000c0107035030411a01d404050100701040360700c15583d9490101c3e2040e1074080b410f629242094000e02e410300380100300768040c0d1a03818000000c0380c2c000450180c8000c00b120003003401c0001e055 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 968881285 1250 968880035 968880071
    0xc18050d02091b0a09140a050f12010e0318100c0809060309031b011b0309020946050a1a0f010c060e060402031c080106050d02040b0703170a1e 63
    0x3003c4000c019022030382c0e01c6190390003200f000407100407410740644c80c0ca40d0820419159610320a1a41c05500840032000307506100e0042011082603400014003482c61054035410b5034840c16800100e4004520000d00d41e1900f0902030703001400341d207032000d19500340e0364034044103210700d0100713520403800440041d5003c00704008480c0c0150840800e04100481c1c42e1050740681408104034071144440d220959085210344107807070300d030f40e0010f040030348980760360003100103240307801018007a034030f8802001503424407085c0c10b070074801380704d007100181503030340d100150340460310b014001000c124105420510300b200c03408107410400b48210707480d0007641070303010050310603043e20350004000c24101884141c43c0080032903003030f200e180203500f682d40d404003001d0612002101000007030040b960441c01448680d1180001d0a2400d131400801860980c9406a0f044241c00c0f10304100c000408210b03d84058424541e600d6410001c0e40200b0b001a5070382807020810150001950390000381d49210b1a41102d40d001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 968882535 1250 968881285 968881321
    0xc0806220c08030c0607030e030a09122306040302060a0b0306040611091009080607020c01080a02030907171b0301020a050904091a0f04030816120504051c030c18050d0209 75
    0x401120b42c4d0f00c0c80d52401903200c1c0022111000070901d03190301c0e19480c0f00f022049912202040d41c3d0301205500300450100c40200c10f907015a04030140412018411400c00010f41c50b40c580100140401d250901d00280317004002803521203210704019007020262000903103150030950041c0042a140b02c4614900d040d40500242203030b0112501c2c039801c4440343c00c400b012050f41c0040e0143c0f201580d81440036a41c4004600141c0e000031240c0001030180780d1260301840c0c1149005e801e8407002565003100a100140d2805405440c0e00041d1722010242512500701084510683c000c2d070a0984000e0082c00c01d004800e03000d40103031f8440030ba060800002e008000e800c14134052546c44541000e000c0c820701041c0c121400c4006c142d44002181c6400c10003000c00300a10740c40d544080000440303c0455001d804c000e40110340910968002d042c1640f025481d0070304080d10755a0000b07116000f039030004c0c020f08410066241101007204144016100c40c034541c10400d4040d074010050340c6903154049240c070082 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 968883785 1250 968882535 968882549
    0x110f011406010e1311130e04051504050c0a03060518060621010e010228050325050c0105090c01030c0504030803010b0f1603050d050109020c0c211501030c0806220c 72
    0x40c2d21000508a045d002d4042c40c0044000005010b8860001180c2100c054502030166400014858001c50120184580c018890426240340c02e406801042000000c0d800444085498008202c0c0e840550b5107007103035410f100c40090a9506005011500e40c100c3d00c05110f0120780c08000340f10011401f5001411103043c074a0007155150080d0907491520408805100f5011000910180b652881a015079005011035141010740c86004034005107442101d48407001801000c0c46020401d00c001c3c81164410040900501540d030204000101194410104281400001d002c140045040d00b02624155010301141c03d43c0d0360485c03000d410013802050344100000003c10506001c240d40200540600309201c8001d1080f662150300d00030a038080c01d0810162a40503489600781792034400400c0c2441b04a509920018146c690750305414a03c0ba240742d080d4101001d030040007086214010301008010160143c003803414070091a402c51411114011a6003001a00041c00d20062030190b138010112 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 968884892 1107 968883785 968883791
    0x2104060c0801060807122304140304030b060907021609090c0f081902010e130b0f01050703020604030e060d020307030f0506030d020c090c04090c110f011406010e13 72
    0x800d8070701e0b4040d06441f0101700c1c1080900c41500c00b442d00420001c0101c1e4500390900c111104d10600149090f0b40c020002003000c0717803088030007c0e00302034101d80b10f401035110340c0000c0307240440d46048540942c400d00c000164010036544040800ba1180140910325030313941c803820b000541c10b4800c4100c15000500d480c0141029003002d1501c00e481410182ca19411000101d071b40480d0902a00450f90b650310300368400b614000030704445010003440e0aa240c10790319900251507404c00f03000242031103c00c0b246a0f110f9039032281a80c46100b8885000c54482c644201d008010307000c0c0b80b0030040750358504070114003942000700703030b10450041607001009480303255800d10101001c010207411040005110118070401540144010039909503201061201c00444075400d00c0c21103031300000d150b85031000441d00e68442400c8560f02220134241140c2c990964008a4201c95001c0024020585 = true := by decide +kernel

theorem cover : BRFrame.Cov 968705035 968884892 := by
  have h0 := BRFrame.cov_init 968705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 968705035 ≤ n) (h2 : n < 968884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
