-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2678
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:25:18.061462+00:00
-- url     : https://prove2.me/submissions/7c70e060-8118-413e-99b3-89f2ca6bd35b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 481474820 ≤ n < 481654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 481476070 1250 481474820 481474831
    0x816031e05010f0f0e010504030f050703090e0415050604151208090411040e01090902060d0e0a1403090f150901050703050c0a05030304061b0e1011010501090204150507170904060b03 80
    0x160f692036035140c240d0b0103219170030301090060b00030840c0c2c0c50030b075a001d02100c019001c043c0502c50049400c0041522418084019049041240e900c0f401c0174603001a82441c0c0f0750f02c5c0c640b26030070309000074214106071003100c6580451440d2046803900d0320202d00c188a1103c0400c0e6072042080100c00003c0d2200d008514400320503996180e134443c41c3c1b01868640c0c82040c0c02c070725401030801030500c0169403000c058074411aa6200c002445490841080780381c500c5010006184101c0064140403d0801001a00c52100161842150b86110f2001c00c00c14000140e541490301d282840060303900d510540103048060722a0500c186007480550702c461406d842d040b022030f42a4170010400003041403c0c02540b051180c4000c81410340e01141401a01030900c02052a000304404052850020b11840c1c80c903a01c040590000c02481d41c50b83c00c0c0300e02951050082d030000030347c0120310703000c4913100741c04580029400010b040e00d4200d0b0b0742198070f102d500c18800646c0c0961295408100c040c010801540a030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 481477320 1250 481476070 481476101
    0x70b0309070e060d0f080a030207050d0e030714030604060203090a020d150b120a11130903091e03050316050c060406020114250302030a0e0d0c03090816031e0501 71
    0x42c50300c085401d4092000302a1401040740030070940000e100021040801a0720014440c2c6801e2001401c4009000e18031010f0100e10484a01d41c4000c2d4002c00c51003034841e020b8094441c015101d120758000c4140081a00d60558042c800080102d2030030741c0595080b064070800d0300c80708845ca40003d6540b0ae000c08007a18822070307200003115003201b10b02c1047c4825506845c0001d000c890042c84e5900cbd074407031034000740c04035058440cc2013880d650500d20030307113030a160303201042000d00358200103122583c54041c544101103140580100b145403c0401e80480398068011403824410a8140030540500ea03803ca40724820400c10400c140e540002400c040c115580c00001e05019070345204651101c0542213201c0c031001d801058160891030700340e803a440000b90030f001d84e80c0d0325900344801c0240003c4120403050300031aa6030101c0e45902000511901c0e01a07511172245540381d41c103071900e44801d00d4905000e502d030b1401c00c200185640340065060100f15421f40c09403c201d0301d40c05d00b50349890303070701c003041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 481478570 1250 481477320 481477333
    0xa02030a0302030a110a0807020915060409090201030e01180f1a07030506041503120c08130303020718020301120209092e0e0303040c03140708030a2a03080414070b0309 74
    0xf07082e0310036a05e18045100320010500d914681c3c40f580f100307206080c40a4081c20741c030000904082c1540c1c1076800ca0301805803003950b485503108000402400769641c06c80c00281001001101404140204515584401c0800040c10802d6031900344401450704211410011100e000b05880c01205100e4815a04c644010400d447c080e0204402c8684500040b024500c0c0b103d400e0011502e0b0040c07121141c8a40d0905d410b20800d24107010310103024141c0e0a0022003a0220040105580440d005e0300312481225001e502400b510104002d03030100740210700c501c1c40e100d00d026000d407800d10043d580185468003903c00228450100880907820b000c2c034004420703407072040c0c640401d1191251110916487c400b86041d420f041e924401780c54041c0c44082d2040203070144001d40d501050103036100820340d80c070450743d1301e5100c1000500702c1c103242c01c0d203000801c160f8030b030090954a4240f980b4800a5060382c0e0481580d5680c0e4806100e4005400c10108503c2a6400407610350045d000540c0a288841d005101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 481479820 1250 481478570 481478587
    0x903050403020901210809040603080414012604020913020904050d020c010f0503060925180f03111516050f1b0108071101090206040303050d0609050105030c010309050a02030a030203 80
    0x1c038143c181e03c00d000d03a480340c9049198001c40c82c103030f04101503400307006142e842815000107005000c20360400b03080c92000040000b0051100422800c10fa2400c3c2c0312103d2001e41d01c00f1449041e00c0380b00d444031415495100103001480c041800ca68030000705840a607260f80290085241c41070101c40032616623001c003100110040c0c0403c003190314078000b4640107002c5420210000c0445c0130150605000f00b24180c04640d42e071261420119520301c2d0f4000003105101c1024008080315520410700301802d0340014085074000b0030086440030350b600304952401c0a4182810300c8091404100c01090b004c205000c04241d01280d540220200b50150000380741e03250070a07580e18140082e0100e000d050f8044205070b0080d50340c100d5002c550000c99800c00480031038480706446e014006190b0003d60105d00014080b0416411401030210740d401c0460802c815502c1d030081c8021580d080c041c0300d52603804252000741962013504200d11151090003680c0ca0301c004c40d408a45400c078507410071409030700082414207 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 481481070 1250 481479820 481479829
    0x20708010b01020312060a030602030403021609140103020607060e01020a110115080a0f030c120306090e0c0a0b090a080a0f031b0804171507090801061d15011101090305040302 77
    0x681104002007220348500c81c0080c2d600c0c03103800c90100304c0442c2c001c0005d50b541e40700c0d00c500000316006542596071380b4040c50000c2d05c404440d142c1581d41c0c900103201284045441c03145603403000c0741d607a0240709a425a020002c0b02c1e005400c045900d140c0300c8405019149080c000340210944030345602e0360000c0c00031012402e4400120803151490100102004915000984035500940164040001d0403040c01e049175000c01c0c0500c0541032140d400c00e9030300d00c29815400001140e882c6d240030442d1000340070b40e058440d00710b040740c030781c1c030542c0c000042c803030700e94100020700e0540001880034940b1640c401186041c0920b80005407843d0340b00381d9507601416006102c2c40920108107815031002c80c0d1503514500c150050b8001d050603441c80c2300b0314801816040200303020218070b5022030006c520b032100b0300a0002c41503000d5003040e5401c01400140d0f24103a2007041c0381006000c81d00320003581e15001c1e17060003100b40500c52410400c41e03400e0100071400a100c0c0002c014041e5503020341d070f18150300502 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 481482320 1250 481481070 481481083
    0xc03070f051b010e030601051507050102041e1203080c03070c02090f0601080c2805040305060f0613060501021213231c1e021203040801050406060806070203070f02191502 75
    0xc1c3c1c1405001040e480a564012034142c1c150f800840e245075072107d00000079411409881001002d81d840068041201500c4407100004560070030311014074951207160142104642d8000200442d82080201c0c1c81020003202940e440500c030301d080c00010320f5940000b81416003d0324914514010a010b012aa50b40105070580c00810307003801c18600310010664660403907690074001c0c4202d071041d000124061203070013254001c5030020200c4100d4140b00d545107034010002e6401d40d1107181d58014106921003180610011030300160040c0040d0310b8035150744411603003d00c600862001c400c02c008540c01c00c00c90b01c04c0311040031f0f403001c40720118100d00900c9041290307071003040c0c44407080c154101d000442e140b0300c00c8a21075460605003040500e61011607050000c940d0f000007035010201c0c2c0815041815408a8491801480140445990369802540303400064801f440181c00800c605000710f8100c200c121a21880a0088103404504000c108403001d0b0702c0d0400c0e50001001050369000f08e6041154 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 481483570 1250 481482320 481482373
    0x1b1002030406080114061c020d0e240606132402010504111c020a06030c1d030c1509060406050c014b05040326040203030406050c03070f05 61
    0x952400b400d000d405000039005100b81c80c01824450005451601c81c03600740d808240100c00703850544a6210300c1c100107508031095041030540340004004a504000642c42540a0340307a203440350341c034030341002e01d540100010503868101e08100203a04d0340c050035007400701c02481e1106007009481840d03981c001d801c541d900141130440e810b14003800045100507000f0701541d501100c0203080b802c1c03070301d026001c80f04031414080c0d4040340100b0000742c82505500500c4824149071f81d00320200700c850a041100c400c5c2900c40c2500740c0d01038062900c241c00c1c5450103c43d540c80f11003d85042c20100e1000580e540e02c560401e00c0080c10104040d42c002d4424000d00c03c2e02d1a28201c030140600d881c0c07a0045d00020060758014404030f00140445001042a61059407502c11020a002c0c918060030090f00b070004030750b858001d640c075580d10041c00c0c0c409101094010b56008000d1032819240ca94101d030260062210203045000411055000a0440304501d000d9032050000e00340310550b03041e880c215045550030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 481484820 1250 481483570 481483573
    0x30705011407030225150c0504060905040926070f230c0f060901051c0207140f0303070302030402010e03030c07080c032e060e0a0609050606070f030c02121b1002 71
    0x44031040c150000c840c3c0e1600e014000d480001c580043c20120f043c4403492060801b020703c0c2480c1508204e40c444018402c6d504a46c031450344407030740c0c1d10600044520014000c3e001070340400300002c2030144500600b00c10142000c00c50f040841e41e48588485070003012084440e071428034800da05014071001c00c241c501020078040c0140300a4400410b841140d8845158810b0100280c610840d0380500305136142a11242e03050710341e00c450000c0c07100c002d50042c1c9040e1543e04900c08000005400010f0a0441c04490805941541c564207002e6010f9000500704a040c00740309a800d400b140c03002c1000c0d00001c0e6a40300141460f929003089581414600444d250298000c480400c2c03060344450004502451000c1150195000e1030100c0e400905040c1c200d0905842100c00f4040c2504680c2c00040c00d407a0010307000c01443d26002c0c1046070350321801c10020010f24511021801003801180b848500740d0000d400a00324030788032001030f420300b00b00c40722001c03090903031020804480c14680740d2501c44480600 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 481486070 1250 481484820 481484827
    0x20a080609090c010c0206040f08010603210f0e040617030d050106030510050910150c0b1005090114010905100201020a090b040503030f0a05160b0108010b010827010e0307050114070302 81
    0x18040c50311414001030f0103052003082d0002c0421502c8100403207004040c5880e03118240f540341c4410340d000c2e140070304c81034071a00b02c0303845509040000200c0d07051000940e52100000380300e0840040e20864804032189a01682d9084006110150184030703100078002d28000d5545e60180500c6601110010f13080903040526020420030b8000c03d0b035003010151001117900202590390041c034105c1d03420076a0801c44030b400400404030034590300031003002d0302d440c17088150074020740d10a120450034000c280709080d8043e803410700411554910f0810071010000c18540504826290030106200c1c0b03100e1005100144c0d800609282104d80c00300360100903022040400345000c0c5003030002aa00d020307440044560340030001d20a808a40204202c8441000030715402c000302c0c0307813401e146440003030910400c6001d508080ca20300041d84036035082c034410502c80c0d000310204020390f9000f52080d0940700710320495640e21810480c9100c420005007142c03030310500010410360b0300d2105919030401d010f0440c906040c01403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 481487320 1250 481486070 481486081
    0x706032a091a1e12280209030c1c03020f0606090c090103020d090c0f090515040b0a080f071406030403020d080c0d140402040b10020d140f03040c050f0102120304060b040e0f01020a080609 82
    0x82c40d04174500203443d8030141e01d41600c0302c00281040700c5491160b40c00108148900300c240c448a440410342c40c02134003910100085c0600207603c80c041260401d6200b135100000480c1030b03014034080d2000c6001854010f081102d001c080400703c8080039402d98610307400b0082000502449804038018248900c000c5c081030610f80a8950030700c000e02c484910640c2c0340e94030240c09460f0315001500402d000c030102c40c40c9030020124a034848c6000c0c02440b2244403080c0440c8401d0401004070f0340207941c07681c001c0000b0240f044048813050381c05001007400d0a420010403002e100e05000301c03103520f40039a20304422414144100300c1204ea512a84d2802002001d2408529036004910b0302d10849441c1800341c0708541c141c0c1d504038584582055a0a030315804410b11062040181c55801540c0c800c0e1a01e0f4074001c0000b00681e0746518054007494440301c204005800581150020001800c0c045d00215020343c20f6407005003402d000742a10406a0b5000c10049465584034007400d03003121041c0e401d2075560330708 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 481488570 1250 481487320 481487371
    0x30b0603040b060f0d0b0a06060306030b070c030203040b040f18060608010312020a0209071112030c0703050c1e0d0306240f0c02030706032a091a1e12 66
    0x100040d00c81c180c448000f4125481e144d800b58070000008111080150051502c0000c01d2401c3d155a60094a0900c0c00304030303507000f03208590030349421000d05a0655038044c82140c0f004002030003101140030074400060004501c40141000e00000310b6480d8480342800f844181c20240c214200208a00b030407030401060b038019614505698000d0b440c0b2040311000c0320142d10707244100038001d40200302d540030404000c0d8440031f200b0b5440d005e0020781e0084800d40707504918a0006895000c0d0210042013080c3c0004c1c0201c0040c00603007006810380700e1002c030288110403a00800c038582e22080e017104a0484800354184030340e6018181442d00603090700940142c0d500d0981c14060a4070900286c1b00e4005202070040a41e403550b160f00400b1140350f551034010007000303401d03820b80041d401c07943c1d240340c0748214143e080030342c00c0c0c2d03c01541ea4442c4285040440c4588401444600b032402d80204845105000c45210030403081450500c2a55201c0c1d84017014440741c07100500044400b03040182c0007644055 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 481489820 1250 481488570 481488577
    0xe070e0105010f05070b0106030204030506060a0b0d0209211c0305012102010c020a030606080d05210402010903120e0112020a08150f09090a03020115030b0705030703090515060a06030b06 82
    0x1c02c1c03920211141521006070762500c114000508003908040000602d6545038006105803482041502d88980341c04040c0210700615006e00c652004060000301d072036013441d42c003038281260000c04181c150004101d03200361102e1a04c02200a58000701d030424020b41095514550f20704036813034200725a615102000d001d40f04d00c9020700e40c940421a2444007036a01c605038003c070043c0c0043c00c41c1e42190b583e03e407030300051120380300303c0040d8060400e10300105809801555004000000c1e400300d0100100746154009000400480c1440200758001c00440d00b6807811001c10b40f42900c80c2c00c0915034140025020000340d51503e400607004000d06241654002442038108034100324107401c102c03682c4002184100d0386510990801540030030041000d0000420300c42c542d001e60020081400705170003041000710f01e400003170100b0030f034403010a00182c40703100255885240d910b00010104c00540d619800c104c1c010180884888141c0f080c8505417030841110f0000305441c0c1810004403400001040c880e01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 481491070 1250 481489820 481489829
    0x90504020a0e0f1b0c100605010905030a0206090d0c120302071a07030c150b060d0203100e040804030f06111602030601050102010501141504050a270903080a0203092a0102010e070e01 80
    0x311500c01040135001400c05403a038030641102991601703180170701040e008160510030a4001984080001484c1c1000b24820f540302c2d4020306001e2405c80c60a0504c10391445401040360014807000b07002400a43c1590001c00301d40c4a41d001c0c0083e03074038049203000025004141510f80103801c00418000903008a0529000e0760720400d1144841030104200c2e009001400030503402000010344850550a941d0055100b030000e05580100d081c0c50700300b8040900c004440041103c0300810090002ca801e400145040ca407080a0115451480012103038164200342c0f2040c14580c200c090b11021031400303003d0b050150000380b00030021507250407404000c4030b6520042d14041c1904400c007aa024a01804441c05000d000c0c00202041e40d40395183c5184140b40f004c00359103c003449444045508030303405844c2c01c0e5905940c0300c40003615a111240000c0d030001d4a0140c1b14442c945003580200844c80c100742401d0013424800d12200f071420006401e40705915040b8416402c03c03801802032050b01558181501e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 481492320 1250 481491070 481491091
    0x1512050a060803031e09010504030522031b0509090f0c1210020f040e2203030c0c051501091a031e0708030c0d030c050a23070c090504020a0e0f 63
    0x54951040103002460550010500c40c00b0020420541900348415100040c008a941d5102d075910303180791608850b001c3c0c0700100090000c0100d02141c0b1000e1844170044001c0b0401190096507981d1000000a040c450a0000307040840c41000b6600d0a10010b5500c07900c07080c00740044240ca48190760300c2c0c0c01c040344258070030703498146030303456824003000700312899061800110766030444203084001640052103480100c08030a4005034550741510820300610041c0b501d40d45074103e8540c2d0503805046003000400400c2511803004010900400c29481c1807581d6100710002c03075051050200c1176075180002c4540070b100c1c00012200c1602c000074083c040200d03085c0f001144003001c4400c9400c00740035030b0290300b0500c404130300070220110228426921f800f0350b4904104030084410240c0f8140203058000002c00c90484c0908141040043c540364003100000300b640c90894913031350711181c4485030380120341d03403c1c0e80700100411401e2040b01003000e842c03610040c5c1c00741e240c10144007c80e0f00e0010800320b00c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 481493570 1250 481492320 481492331
    0xc1507020d080d1e1b02030a08010b030c19080106021e0a02060306150304051606080f190b0411030121020607080c01140403111b03070506160503040e0a061512 70
    0x4144070b0344130407000143d640520364844031180481e0003030b00110381301d4078059034200940c14104c0d00000480e4000c3c030043c0c230364506581c40d0404110042e040148100c0c0001710801c5400c03110300c0141343c0e10621030015101c25000c1d5041008c002d141206012016900381c042c4600159071a400164801c800f6a0403a00207944e0781d10800400c000e41401604c0403aa040e0101c14082004008259072880380140200c41805507a00d16007118915000d86002c803410826401044003010300b0002e18a0006a40707002103030080403840030800b03c60224403003010880c0080700500c41c0080d010000c080300543c0802e02d02c1c0d10300b01c50300007418a00c0780b01002000c80c5000203002c2d900003070a40285c1149800320108010340c0c9010304014200304840c1043c07408034000c0c5201d8504514220608848915025000300fa200341013609000d800e9008503041d80244100c43d80c4240000c10400c014005002030100d25500d034104010705500351001600000070700982509843c07000355018403000000008840302080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 481494820 1250 481493570 481493587
    0x1103011e0207022e0f0c0209010e06010e060d02130b251e060b03060f090c060904020f030a090c090b150d09150e070f0e01120c170c1507020d08 63
    0x951000e080401d01c101d01203290322034400e1040d8040c000f5031001a441d00c2036440017400044452076060b0030000e501c01800380050000700e042107401d9910413410b0500f101d0122810000a0303664104495260380142c00262134603050900000c0e850082100319140d60410032000a151120103007124480c2d450500e81c443c040500001c8600385095030b481c40e11420b20b99627a41000400780401e42510f5000b841214042900c10b040001140e10400c00c4001a201c281000c100b0890a035024462042d8015002e00914101c24800c0300118000e400300880043d00f44090b281540c2503c6041c0c0c0708108603881c10050f6a820b0310340ca101e02600d10421010f56a65450051811004208901d0094400c28003038079182d6205101d54803001c115039455048840c080c0e9a03055406065105002d0082d456032028010080030800c0c520110f5818450b50769035912a84070100351100140d201900b40c283e034070101e0750190a0900032001020303031910f0311620b4500f0b01c0a801150751040d8040c0d00420120b00001d4120 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 481496070 1250 481494820 481494829
    0x1e0c1e012c040e0f100216120320090307090c35010b070503030a020a1709100509120403020d064a0303061519030906050601030212070c020f06161103011e020702 71
    0x241030f298402180c03023035050b403440001c009100d0020603010101d6850204004a190001501e402d508010002e1200a081c10b4580000c1d0903200080310900c84501b400f00c920301ca040c105482045600142100210004000703805021410b17880030294890401810001c60404170032207034050900d80001da990801c21508540d0002c1c1141803814000e080028408050300104924a1000d50740d0713003c1c88942c0316803800c070392100031907a4001c41d4030408110400c01030405c3d01e100170b5014050302d4006401c0440d040701d114801880c502c40040c10000194003058481d00a0412000740d4a06100041c1c1c0540f004103150350744809404c0c03070310800541038900c4031000300c041207e944190030b46000184d0740103108058058402c003c1e0846286040c00001141c5521070320984c0c00144504103c2903213612250f1003664034104800040e81c10450141510b1519142d60000340141600240010609030417810300100d80200f45500d14400d074100188440d151445258140b90440117003001030b51501c2d1480000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 481497320 1250 481496070 481496107
    0x70c050703110109090e0303070f021c030513020a0806011701020a08010303080a061e08100c08010512030717030f28020a0905030706021e0c1e012c040e0f1002 70
    0x2a80c2801d014002d4a0f06c070000c009540114141e459452808800590581c2c031038000740d4041c0d040c1000d001c18020354510a0f00f09540141e140e20511340c0b1982d9680110758010740642014010b980003a004010b609000d0001c0103c4444070f0008500f0400d04240c001d14a0006100240820208030041138283d0003e5112000030841c10555902c01c6401c818a40c1418078640700380030a07400313208002401e400c0940100700781200c280c1d451004580c2064200490301c0015a10072010307200c10300c1010000b81c03924185840004070303181c4140d01c07803420024031401d001c0000d0031408075100c01e01ca050750541c4c0242c0900b60225840c00017503115144044101c4d042c00e100e2b40040d515100300407001483c141c0116030440c44403000001c0610702ca005066566541d080c2504040d00300c0612070301c0000d00600c1030032580ca000310502d4aa00302c0c455440b40c1c2298040c64603001e03503140f44110381c000f0b2140340a10464040000ea0005051581f0300400155100c6010300b00ca000400e400290030704452400311100b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 481498570 1250 481497320 481497329
    0x50f04051509090c12060f13081903050105150702100f1101060e01061106070c12140a0909060f03050a080702190f090609050103020d020f011202071a070c050703110109 74
    0x500b910b103015030003283d41d2600c005102d4014800b9098200d503503180480c0c3c9500c02d1500c82c4800c03200340c40e07580c602c000e03501500c00155030b1181c0074401655660010f00c540040ea08850f076021070f155060504200303012030180802e0064200c1003001c500141c56041c119841d918040c106140622046134003611724400c1e05030310364055440e1020114803280c148100e40e050700e40c23507610410001c5c50100b019030750710820303106100400c0c481074608000400814410401032114a0254803080051038050290303000842003c0128180407420702c14404c1d103210300c1000306a141c2e40c170a90f09180d603c5050300c0d0059504054100a8005180d2081d500d51007041c9230910103881d45030541c907a03194000d02445545004102c43d0a003011070001d581042c40c020a4140d94000f402d1840300c550701c2e0300f0005007000c1d142089051002142c900c60341d00c2c0c660710240003603e00a4003001d8011080040703440b20143e009100c0300900c6442180391002c6200005e441080c3c0b0341c0321801c10580080c1c54010b031140c03540c5601 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 481499820 1250 481498570 481498579
    0x30a0210030f09030804051002070515040609080d05061906050901180b040e040309060e091621090606050301050f16020a060219021509030d0b06221e050f040515 71
    0x40803404c02d81e002800030310850040d4203982c0d9900030740103818240c0c4500c440141c5254005184000c6019001d1401ca41040c421480000d0001955407804810b4000341006420710b540c5408000351800c140c1c0c1d546030340c01d0000b9505440c060a00b0381c013401d2401100803450420040f1a1840803040c0004034150142000079119616295903440103400804116801c50000f10024400991380d4061310000284010040080e040d41c0c0d0b070207035800c0f0003031074140c0020100000304924610700380380c603240c1d640c14940c40100840c400c0141e007400c0c0207032080350b4001c40c02a8540420002000080c0380304c2504002130710000800f003080c4250403460f0288151000d4081840002c01d03030000c1e050840e02102c50030041e001d840e10b50048010100c3c032480c00705d0708490300340c00401280d07000503403a60142400c0000144441e0030700000c03011520803401c40800040003000b10540c24064810680032010ba000c403142001d003402820b080100d0404411804080e029540b240e010902840e80320300550801c240190 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 481501070 1250 481499820 481499831
    0xc0804080f1e070b03040609150903050d11120402010302130e15120102070203120d060b04230306010305070509071403040b060a090b03190c15030e0709020702030a0210030f 76
    0x84a507102c21803541c860b8010b5881d2203545450081c086804421503500c0140c907411591580c40c0d14001d0304460500321209044240450841c080c00c1c450300c071480e8081e0b41c1e081d440c0e0045501080498410748001101118144450a8400c5140c220703680c0c01542841c0240c1c0f100260b18541b4040c0301079411004420520108020007080010405200d5500c22501d8070921041c0e90240c500700d2182c0da0000e909900818518194030400d040140600c1e503100c2c60018000d0f559401c9041c0c260455040384030800c107100140c420201141107a614214011406040154990341d1541c1e40c4440300d10a0501070704805000034001d41c05a81010280c0808288143da28a07051510008c441803c9a1451040384920808100c014185c40b940004100250050140300340303080701c410500c09095011907209000030320214141580c1c2c26003c02c0c0348000d807400b0407003042c03003000300e428002240c1007510b0542c4144010384c0540d1303001407100d1200d901503920090030f1160b05011405041464020503582d0b0812 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 481502320 1250 481501070 481501093
    0x6090f131e0221040206070201210609021201060905010503190b090405010906240b0f04030602120f070c15050603010e0318030114010302090105092824030309060c080408 75
    0x80d0003c208a0002d045045880c00015a440c1c42c400001d4034060340110303041c402100103501403110b40b851818000840c405100d0140805401e5038455040314088540102c0c50f003425002e9843c186001d0501da040c00ca062604000000300a40401026a01000c15460b5101000031299014038141c00024081e4072191409080160103840c41190413521685801d0702d0400d04a4882e03614403942081520002c003280c038100d06031100d50484446010482d008100002c002481da100505251010060791552031a0540c03207803003a040c00411101c01e020f2003280810010300c90b5810a4428004018000b0300b5441e4940840d0050450700071181044c800041c54011170031008030600040c4c0710890082c00540c2c12112102e81000080c80002e420070301417001402507240041041f584031041048890013800c0c41403113030310b10114107041c28007041ea40d44100806402d10701c20509050300b19549111505c0d1440c0c1d002420352460303200307d00400455841c50b40403c12a4421a40104294002c440381ca8090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 481503570 1250 481502320 481502381
    0x303060f03230d021f060503100902030f1513110306190c0e0f040c02030d02030c090a120b04020f06040302040509010f05240d060e030a1d06090f13 65
    0x1031a10070040b1010091240040c01c500103964221101207501400207183d107950601100f080305c510344124140c1303446022690b81c504010403c2c610580368408901003100d4014141410f0080080460796000b0713242d240443c0b400c1032002500300e90100100d00ba00209030070060088410920b075076a060090106001c845907410442c4000308050510410241d401e400d0700383d411184003c844c58000030380760403035280382c40c2c40c2d8803150400104d4010749143c009c0c1c11861804070380c012180c5071001040440d2041d0642003d03544803000c0c0c20549242e050034411034645280c50800280000d02c6540c040c190106240c0707031513084c2c60046901400511040c100101d0490280c07414121788207886103058000760260740b03481c940189440850301d60403901041c1c4414012202d1038400280c2d103050300c865045422039020801000615466542c180d8101612040f203403121a288684511502c402d105050059a403502c04414040d412a0054042405420450050950703a44409124001d00040082032483d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 481504820 1250 481503570 481503593
    0xc0f05030a020a06240e0c130b1905040608270d170c0423060915090a05010e15160506071d03010501060e0f03100c1205060612070c0303060f03 63
    0x208180600070b9a00e40c0207415200c0422428010028106a8042041b500e030030340301c0c94102552000c0d541c980710901000904c001e050703034030945001900080d271210003178400340801444c070304900d0160310741031400400412004000d41144110800c1c0c41495010301039154400302494000030541d92403004076074000d000c0c100b03054089010030700207030006046c01c9078910494007a04c98402c1184400302030660551000301e8941203081d001042000705ca8035681e654543c00d0138003441c1f140c40540c0c540c159000d000e0000141c2e80410306001c401c50407040c0c01d64600701e400c1c0c0c4040400120710b4403a1100288503640c1440c080b409003240c02502c040c4009503074000d00400194001e0079034083d04284880926080722800d100342c01c0042d58516a1000c2417510714400c4000503801400c032900c5804407140402114040780382c0b4000701e00554000c42c5004c03c00c4c025a98004401c80b0b0f040d00b04a401003030070080359002400c28040040807018901058000e074800405041401c0b15809800e44a00e041c416007070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 481506070 1250 481504820 481504823
    0xd090c180609230703063507030804050111190804030c0e0709031713180b060702060d090213020304060204090b1e0609180c180604080d0c0f05030a020a 67
    0x14103241c0040340c2e4601c0b50040071260854180004090390050800361080c01c0064502c000b050784818001805052100d8502c20b00c0c0c034031492110354208810a0900001002c460646040e00302401c10004035081034240c0b811590300b8204000c003030104200090800d003900382c61580c07132012000300c88203000c4c1450141050300e01c00c1a80c2c00071251101c4c50305140f500c0803610000007952106007480003da002100740200f05001001c43d081054607060b000c0700d011542c00940400c0096140039074030301061302543e0384080e41070360041d10303140395500424204c0c441d030100500099280c10800742192200490998070340085602152681060b02c0c00d032000c1d51051250711811810b1108603000c03454180ca654003888121601c4e1094000100140710a6030805119a48c0c001c0c0220b50300e014a042502a861042075003092203607403044400307444440b8142420505014030810b000c10b0115150000d01c038640c0c0c0b801414040380180c510726000400c842b4050008126003c00310701703c1545900054400f030b005e0b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 481507320 1250 481506070 481506119
    0xa0207080f07140604210602040302091503011107170a0c020d0b061806090f06120307061b05030f190b040e06060906040209031e07050919060b130b0d090c 68
    0xf281c200400107a4020742c0142d04000b8411000e40600140700a0044410707449a20050b08080c1e07030f80c000401c1c140c02120440701000141e040000da614081c81445040075890301c3d20f85c284651034507155108650725840f40a00071000540c902814018010b07013602d1075004001d140038010500d00b60f00c0007281626000c2c0070749148113a0111719000e880e410361041c08003410051550f696100e014070f0800300606415048404089510341304c1d002440101080c80c01501c003c80d1a220524170061286c540c10004001c21200303006124645100900c2280c01910000c801c114049202000c0c1d402016004441c2d80e026240a400403200000420300300d1045504440c942d003140e40d000c05100a03803145001c030035415009000302e910303407140710401038840d070684108640a40b5150301c041542030000390345540415280b0801d65a980305103025170000f8003107029407a810000e4005072500305901c1d500502919a41c04500b448660b030440c5c0c44151602d401041c0e04175410351714600d9040302c1c03001005c010040d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 481508570 1250 481507320 481507349
    0x7090303020c0d2f0604090e100504110d03090b0a0e01030c11071509030f0503030f090703110111150f060a06030b0303030601050918010305011b030e060a020a0207080f07 75
    0x2e07441d0041c6002c00c0541c00003401c010001c10608854580a0070f03640c0440581c0b00e8008200c071075141c580251016200c031050010300e054084441600d442c0141c66122032090401c000c100004081c152825071000041e0b5010401b01030510302600d950b104ca0304503002440d07010032040b14482e0302c80b030781001066080e01c0410400101d0300088840c0d0343c1050303402e080c55100c400100140c06000d104810f5001c1030f881d0002030b031600c03940d840c001c3c02030814003a0f40542c4080140011240244059070f00603802100811160386141c3d1207124a031440104241400004014284800018452440c848614070706c0c80c07942e032402c10141c440c0e000781958600d020301002c80c4041340755406032050f8610000d0050046096075245401100c160303000d10300031a004040c021100d0900102e0b4014913010310b11520003c212082d400d040e071a800302c030f840111010981003181d039400c166801700c2e500390004141740d0050783d1030a06400a80c50415141d00032800d62080681c410f5000b04040b85006c01e440181408a13407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 481509820 1250 481508570 481508593
    0x2030706091a1f0303110705030f01020409050c04030507030209060f0607120e03010204030b06190806010b12060907081602161e0602010212011530050106080903090d14060709030302 80
    0x2c016421460100b20341d0000f405001081c080c403888441031646030700715482e040d21140400c1c01c00240014070713502c1d80c0d004074042c000103055029045d404490009290b04003072440e120240d441000b448044e000d0110b00c008516143c803000b0111000d144c000d0449945c036801860403082c011a4881c50a001a60b1440030200c07a02e0103000312030480e030304440a452243c40b07003005c0107c0303600c00c0607070341c02c000d64010fa0008000e83c0920400d4000e0642c071010036120a241c81c0350b92120240103050714801c110120800c0b01c5a80c003c250507030801c0c401481c490304001c03c01c1d0180d180c50800d080c3c000c40a0810000060b0111036490300c0000b2401c1b5008801d00c0a03030302d51007a42030380900e041c901825043c1000501840c1d18241c0c3c1d020310082c55252244085a150b18401d1032b1015408800c4940781041150484058080c05118010300b2141781c550040c0c605400c00c03907140e008001d02280701c5d60108140406001d600110b00141140f9803054a10505115070060640d0b83c06200c01c40150041032168907 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 481511070 1250 481509820 481509841
    0x70206060906010f18080105040305032a040e0604062301032a0c330c020f0c041a060409091401090804050103020c030d1e14131202030706091a 63
    0x600030b00041c4c5403106107030b00380b25040e1612820001c040c0b00a002c82003000401043c03d001c2c050245000ba2140d65503800c1c05500028900c258240c000c004144032403519079690038160481e0100d90642420601c030f07440d03000001d0f0240110350701c08000140d00c1c086072410341036070700f400c3c806055003601d0402c002c90110480212041e1045480040754500f5080941124001c50800c942140300741983c645a11646010200d01143d0f5011440000e2400000300309c0790500303108620401034140000d220880030103200580d546070b11308110f4011612031020390308991040e03448070b0b50008018081601c482e22114480014a40100191145500650031900d92007041c820b011000d9001800da07171400d414940107401030750103500f10080500c0200400c040101c214481c21340c3c401001404000481d8008203480103075500c0501c07900d411003030700c4107100010090b174104a106075402440504041079a51080c0d0642c0034640c0090545814982e001041204081842005158100358008039031159038900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 481512320 1250 481511070 481511089
    0xc04110418180209091005040c06141309020a05070c12020f0d0305040909020a150804060c031413020a0e011d0a02040501020a0f061d0102070b01080c180c0d0501030b07020606 77
    0x15020b100d4034144102500b0034200c1140e0120301e802c11900c0d0325070b90030f0901085a44c12035056032214000d80c02400444d6102c1305e40352440c244900100d0410003a42003ca810310564070072100a6903001411001d40c900a07030076202c49540211003c0c084039981d41400001c88086d82d012442080e0b41d060507c600d24003056404a115010b40d205410181042000300041c02208801d0364010089880051310411705400500c046109a66079074003420103103420015900180444c00505040c905248542d00c4200269035100f205621951450076240c00400c10301000c80c0c110701c41d903080c0040042042c0d40c1c907138003032205810760004415243c0d03100040003080340502d010303d43c010380041b403c05d4081070f00c1c1d800d0b603100c0794000c540000e1418405480c00140991882491110343d4021a044003449100c80d11140107141d1000509402e82c03c0e03d000618030100d1085400c80840c0000108207050348a2090781c180c1040032004106950712400c14454000085a14000500c607601c00103026083c5481da4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 481513570 1250 481512320 481512341
    0x2070807052403060103092009060f010c1b03050708030703021501150e030f10150e13021207091122061d12030a0f1b0f0b090c04110418 60
    0x7110010100540b09160590001d030603a41059240c000c00e8003c20302d80c4c0c8400101038030703000d030800700003000e4824881800c0008140e40d204d584203851104040e41c0001300461180d91003080841410369041c02105001e80d07941000d011803040e54408207030301100000400c1c146011b81c0031100d00d49003051004407218024000e0301c0c5070490501d9140c0309079000324204910080010700f0317903218014840d00c6514001d01440030001080d1242c0d2100d40e1420500381c00c2d809024203c0c000b0034149049107100400384545a0700a000d140b02444a07580c1a0702445210054189184240110322481c030f24202e4a801c1101c0701003c8440940907039220741c00303075a044c50071110562948100c5010076403410200c030040c070004030f420921021490982090610060510354443d4649030000f20407030700001c3c8070078002c07050683c010240707030101004201403d034596291548000e1101203560340154031414101224000d90700103007041282141c0c030011202500c1070311600c1055901c0c0744c03281811402501c191294 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 481514820 1250 481513570 481513609
    0xa020406091a0d0f150e010e01030b070203160506011a0a0c080c0a050a0812070c0803060d0609150f0f0606050904051e1003120314161b030207080705 66
    0x10208440c807411a008070b5800e07685958142011520b041075800d541c09007420a0805580f4452070750b0b01912070300c0440240103e0000280d183d0b04100105800b40c2040c04060100a035040020300000e10030800c8840280c0c010344214448206440d089503600c0c0207010320486890b66046814060b4419800c0d204003010b550789540c0c1d08a59a02c8079086507102d0003021003e4095921510003150040111000742c0f8450110f042d0f4507078030301c040751003440409882401081303d181c150501107003148060383d402120440d1802c0485502d46400001408410001003043c450751120f0400289180d11010030780c00c3e000301c00d1008003040705031101110359038040c01010640600c0f680f20141080e5000079802400190104560b0b8100100c0c2e00c04042d0880740c0d101c05000c124410710400c01d201071004c00e00f420508007071107280d8021b0000c3c081c04d0002131140f800701004010050010f8400c100010700c0e800700c45000c001c02206030500940b00c005038010040144202d9a00141c00d05100e17003a000850700d03a10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 481516070 1250 481514820 481514837
    0x8120a1b0c0f0c0801020a0903020f041503080904060f0e090d11070603050c0903030403050f0721060902040906020d020901030e03070302061f0302031b03060f01030206030c0708130306140a020406 86
    0x103030303004030b2001035403410b03074001850600c0030844130000d100030500880292a106c0c41c2d1455481040002c01c80c1c045007500440c141100c1d01d0f0002d0203413000300d054036882074269440f03244241c00b143c0245071541c00395550b0000000000342c042240c8c0030150040300100250b803501080c11000307880046800f80f918a05c0e84c8070610800540c1c1c0300707900c42a041035400d01c0085c6401c0c0d98400091464016800a03151604100c410310f16104042109000502003020b4448840d00303e001e804820b040240005051319881382c1c0c1c98030841d983d41c1e2100d4030702c9074840d400310b40790704085070490025049a091a0301080c54504540c5a860000040d0f4880a602d035004000c0e907035481d400041c40b129241040203151050f01000300042e075003440784810140d10394182d0040c2d11002c404140c64600003402072180341d000440107001685900084a0780000022000743e5150741c0c62601e00d03440d110b503841074035014009001c003204000302038000f010403110003102a03003e515141e184108038481c07440341e500491480c0703 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 481517320 1250 481516070 481516073
    0x117070608062e08071e020c010302090f090103150e0105060f01030902150f03160507050a02040509120c0d02060609090705040915090c0504111e0d020708120a1b0c 72
    0x149003020f0303500009407003803018000300c0c200d240011580e480c01e4010030450b1042088990340300c5c18000062011340a11a000442c0080103515a44c2c243c41a90416030000f13888001922041102c00d080d0070080e210f6276866035a07080143c102400e801c460486035052101112103600140a9940070790001025601c0034440080107500504561104036008240b0310b0103042407090420180c12014601440255030740b42440303005d40d040c3c44031840d48040c01030600c030746404030340b00003400c005a59041d00e000039070382ca56503000c0c3e00d824010016044803c00c00206010405400b00390300e013503161180c00300c817110b0316094100114080c040b145085503501400c0100040e00d0f05422405905001d00c5d0134004418040d00c00c1e009445c50f8201c240c8000207103c80c108240e00f1b10784114219100020f034210308200c0d1070b41c491141020f030792091804610b008a07544100340250303812203003e41d600501860f600d40000606136400d40040f00c041e42c0ca140b4054206040d06e03204c40313884038100340944e5190011030342d030f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 481518570 1250 481517320 481517329
    0xa0902040e0a051e01110a05090907090b0a230a020f0f0111030a0209060403200a060e0102031b0102041e090c0801030f02060313020301050a092a05150d06030b011707060806 76
    0xf101c13101169074a40a01036241c0c0d80d00c50040942901580c1d82666a49400c018003007200c0b00544050100700f0303410400c04c0081100c134140d584680d21850500084042c3d4201428242205a81d1085c9200009284074000da00003c08050b01022101a07400b19800c03520220300725a106404140d10030020000100101d42650090125180c005c00c414140764072602d4420040341e2680c0b140d010300f011144201c813a490000d801d50010041032400300550205800000d449002c0c181514ad6500e031841c640301c801070020340681e00540f21120f0070080300d070b4500c40880500c00041c85204891b91901d0000200d403846418018103030394000724490840c01c00c903428481560300040001c1d440c4482600c060005a03020b000300c0b40074050852000c9a070200904009050034240d0141006080c4008030000109000369404000c13503000f200c0341411110111800d031070500c1400c00b100819490183d010003008030086015040e076540065a150200030090080d90700d414500404002c24400310005603103140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 481519820 1250 481518570 481518613
    0x606080720030d0b041a15070212160f08120403020108060414040803060114071e211701050d020a0308030c0c0f0109021906090b0906120a0902040e0a05 67
    0x32480707444058058403400090079600901c0100183d90344540f1007840038a000d0040e42c0707828003800201108140000b0020320b800c1c0d50386240d110514404502d103415540c03070b014100c100348c00460545144d00340d00840388c950103015002c0d202520080d18400709084000286840c02c0c40407680c600f520701400d41e0010b4501200007042c6030380c0300c1c0d11034000301d4290b040c00711014011071150301800e0301c0341040000501021200040c0e10707500501445203c003c640811612030105414002d01d00001a150a02580030703002c403603408016040d01c0000b20480755004c001034699031a0000c042406988903070030864101d80c0144c0203544807140070024000f240c0054029500a094040030074a044505003116082a04407101d161180c0d642c2c084403019420103070348102c0109596007412400740d04104001d0881441400741a02c6108042041c500940b0390108a540401e18240340c0b01d01c0b4607054050201901ca80341089000b503003405103d581884c0000b6042c800c09520030080d10400c80c0980b5150003165 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 481521070 1250 481519820 481519847
    0x60c03040b041112102904091106070506090c0907021c050c070b070c0603050c19021f05160207060210090f060c050d050c121303020a0b0106050703080a06060807 71
    0xb41080d881a5181d4619858000c2c40740080041c101292417038105100310b036003e000d4203485440500ca00c54606411072103401c00800e003103d00044004032810f00f05c1c020041d480c000b41c0c2003000064030809000c80080d84074400c22401040302c4d5003600c418203200308900c003640c480c00582d201c600d010092003400310460001b40c0851800c0b0b402c19658424507880c00000da8040c541d8071900252240c2800458014400904403900742445582004a10441c00e48540610510040144000828031910074401800390b20217901038903880c03144050b0b0110040000f696080800728100714008042800412010110b0b003150300a06081201681028003601e08800200da951101d0305000d00060310705d124040c41c018507507881a403141c0401c440c190440308058101000e26605000ca246d00580342e9807495484480840162194006d82c90180d2030014a02e500070580d00d03110740013041041c0d201c800381001030702941d10010b91780c035031000c49000c45000d40103580020f81e00c0d00c00242d030305001c0c2a030340d02600f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 481522320 1250 481521070 481521083
    0x507061a030d0c060f020301050a06080405010204031a0a05071403060103200a030501080f16180b0a06080603100501050f060a020a080d0c1d09010314010605060c030703020d02060c03040b04 83
    0x142800040c0c1003000d0200103201180f10041c4000c144203040c031400c680150459411482c65051200007032a6608903c01c40041004003070000e010048290161001145c0c4500e1448031010303a0305410124100848804450924260020300c0140c4500300741d01a1449902c3c0140c074503100c05004502a2401203e1082400180e4440040c034172500001444100302c1f81c1e800088a5052511603410701441002c801e11540c03110060319a5142c1e0840c500781140c1c1800c0440703990400e000351000240c000903070b4150b030200c44c4441c002100c640100940d88505400c0b400d070f5070310a5401ca2803508035072081c02a180c100b184803440c4a03a60910304001c05c01140c03d0b004441181034503030f451000a6004d139200c4c3e00c50f5500d078041042c01070f4000340100da111800c2040c0070304610070785003c03981d203440512005e00f8510104046411940c001c2d030001c4064038000d000d540d81c0700e01421001c0e680c1d500c807410890040c404d080c04540305910225206015200800300903146840d942c0b5a64011100600250b130a03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 481523570 1250 481522320 481522361
    0x2090610031415040e030c031206010e060705010e2e05090a020d140d03060b0d0f060b040b070c1205060112021c2604060912170a12050601030c050706 66
    0xc40010460f11441c1c030102841c105002d0081480190780319529450500d45c810f0040701e41d00b15012090f0f030500c0b49501c804540702e5540c000101c40c5202600b0f0703100d400c0100011060140441034012a141791004002c5407040d001c00c480c0248190300d1008581843c00704000f01d0f04209541c4c0d0807c5030000b007070804441e4207048a400040d0818031170502160030306600c000350118844203204140f202031072401e0801c4014500f1816506030b03c543d590f00d40d1251354400c147d1144a8840c7c1c0103001510348104000d44690700c2e00032034296907200d0a01600ca020f6003090008444491020306030480e503000f0040c000c2a480c08a42240c10080380d6800c80e0700c040d81e1143c031450818194003064000c0d004600740040303000041c00c10200c03003108058010701c2400411083c452260003080810031246648900d10900c03110b400e1192202247c45407091000200180c842d80300d41e8010003640713408102c14810001a151640150212035146a0160214038103000c0034021488990042103124181d0401c141e1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 481524820 1250 481523570 481523591
    0x606180303110a0605180606010302070f0f020a0b1b010b03030c0325051506010e0a1a070f1505060109060306061418040e030309100902060723030f0a08130209061003 73
    0x580e85c0031501801d510004034041002000b00304901c81e017001c806e082c210b01d486916250b070f030207a00400310080e00c0d0242143c40d04046407520240d580040c0203410313902d0b895000000041d00f0340030352103040c64a29820051484040d181c00300440310181c040c800150b144c554540140814508060010411280c6140000c1c0210341c0c1440b411141000740d00f804c3d070091401c40000340c141d2191142403030050695036001e00410044507803000281c00c82c0d800c4251508941d02d02246020350b000340080109240c2014200c503030304150440c0d80222400d0701c840701540c0d11010b0403011660700344200d40002d408038600e0440110348400406084000781903042016072810041000d0b13400305050050a50b100108114048105000d6203154010740c5805011280a40d0000b514500174400c0150216440c01401802690310703403060304c0955480d8064a881c0c3c040f481a03a060f07500018144008220344200155403000c4107803003012101c1d8001c1540440703480300310600603034a0455107107100b490b964000850 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 481526070 1250 481524820 481524833
    0x24030607030218060f04092c0106031a0411011116090c080610051c02190c150b0117070c0b01060801030b0f0f04140f01110c0c0d02011b020301090b0405010e010606180303110a 77
    0x100301c848c200001103031640c42c0d454090085609107086680c0b240d0b180f400c0c40f00050134641c2180c0602c00910b444102c000c0340c1103409040001c00110340038a070300120320015501102e038214090702c072241d403110000303036448405008070a56061201d000042c010800d000200c60200000c0b0403900c24140010304200200c0e400400000c16000b041011a41141107041088a840c092004412240700c050020400002c000307001010611104010000d02000159560381b0500440e111160807a00c900403650f51406c000e06a50403e010680300c07600c0140c0052625607554204030701428240c1110bd05036561a2a6071000710451510000903001e0101c800104600074091107400848400409541e402c2e03004d42c1c6c1d45885100d8000e203000b13007840100713500940c0c2c1009020407807141d0214000400ca5180c07000070b0040140741c00042080e003092060009204056005c90240001c80c0020007115494810540d0181075103040815075020585003031001a00c520800740060f24003400f203031444001c0707603600c2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 481527320 1250 481526070 481526141
    0x403050405061209060106140f09060d0615110c0d030e031507180e060306060607150204090903020c0d051e011b0e1005070b24030607030218060f0409 66
    0x40401000f060a01c4115402070162030300600d41800c1252254145500890b45806035440e074a003503081c040b41400e13644d1030340d10840f190000b00640401c025034032010000c011103110f105210004a061800314020900007915030328005004220784105491540e04503281146002c03420b0305405103c4d80c210109694a039440d001d464503807200e20032100c5043c2c1c3c00b44085034551000c0340300b800c840240729140c0c0300032821a41224050f1943c680d500c0300c505202d201d03c02192180780750144002400030f5142100e50140140364842c0d0309443c44241894100a5000c1280d40c000e805134018642a000507040c81e4400c552000794580041004074400704081030700e00c5a07401000100f000711404030f440f440c00c01082e501707000403401c000f41004000e80b41d2140121000300317510078595000c55024518148580c45607803000009048403410300e08141c00070080e4000e41080c02903520016404610f615000341030364040000c0e02041341c01d0074580604480a01031210484030b0a04480340c10014507481502030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 481528570 1250 481527320 481527337
    0xb040e130b091f02070c140a0320010305090a0c090f1517210a030c05070203010c0c0506160203030402060d06080723040b130b060409061215050c070b040305040506 72
    0x20340306408500c5803510f00d810f65440c41c00d4000e841007059100145041c24043e00792605000300051350300185000c600c088556420142003601076005440303030382040c42d81c1d050070140b017039034180859242c04101c269100032200c0020410a5241001d00449070300d80e1082400d06000e902c0800d4818030411444103441240c0c1020404101c1031060b494180401c00c6a03107107002441c4181c01e4030300038105185403280150a420020540c803146802d516510076410344401d680c00030003c000300690544081c160628010b0704030b4013400b034203000500b49490025030f40c40c6001e00e078019515651300c9508201190388800b03240a54550f443c44089100c0390100304410140c940450004070b0503010240b01810a141011218422824101c0c80340300d031b849520080d540c0c45881040850401948400100396010b01d401130f401c40c1d450200009510740b054220741c114103014811801891641c0e54020040d282c0440f100b61032030718104981800603000c00590b60b4014004e1400b41c1c24143c842c00080c5a0394030007030b039 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 481529820 1250 481528570 481528573
    0x117040b04150f0518030703080f0402010507060e060a0606110a0204110403050109050a0b090705130f0b060a09030c0f14270a06140a180b0a030206070c0f0605040b040e130b09 77
    0x100705c01d40d818030f4046146081014011810181c5a5400034840907004282544210301200840d0459014506684c0e207a80e000c0381c1801019401e824080e540e05c01290f4503c1484e00b02040015218065012074180c032406102a0210042940030301014089030703032003194455000c02000000c11002e104c0c14034080c5c45000a01580c1c1894140a840c80d00c0250030145540c011800412103591410a51010384400c0d40c00841c42002000d841c100a104640120b5081000003503160303d4103034051b003094140c81c03080d20417049594944c034041e101c03030200d0300403801c45407980c0805003818501a00e800c001c1030035203c00c00340383d0f405418110049020030380b1107036100da8071020144400c0c003800030078602c41d0707a064404901c41454032071020785605030700c1544200c450351200780310f01301c1c3c41c1c1491000240d5005440c199840e40c8614140c65020154030900c0002c914401d804113010b0702c10002c80b001c40d030303c00048506060038101d5070300c030f03001001c0d1141010b64004001940002c4c61900340d148140754003030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 481531070 1250 481529820 481529831
    0x9080c0609030a120519050402130516020f03090f0d02150a03020717090919150329090c0402031005090f060a090e0a060b0109081005070306050117040b04150f 70
    0x107005000441320500780c10985081c9801c02460b1810400e042c8055045007a005c03a00352550700101d046241d040c5509550213003000204120401c483c100701c220200c081e400c480100708030b400c5503902c0380030b9604a19030100c06000d0110310b910303140c510b09036180c0c0001d062812501110098800a511405441c00841d4001c80c4000074040e101c60b1300750b00c00da150341c1501e1511072000001064500010445400303803100c880c60750755895807903203c6100364150310b140e181c1c0f0940300e00b400401e4207102e001003a0f407851000130701450319a811254900440300d039001810799070080402c00011750070040c10b039000b605020000050720781d20400ca0502401881404401908100c002d1042c8054184c104640d110f042c034506252444d00003a84483c110742001c00016801d420b440101d03400b1403144e01010700c1c0c1c858400640400c8645078800d0340036902c1c9440410607203545400640e050301c40700560711a0309042200040c0441c0301000e219a000c4d11400803403216001602601c0121039680d1481441165100c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 481532320 1250 481531070 481531087
    0x9050603010b01030203040b0708040503130b030f0703063204050c070b0c0f1e0c16080708210a1107120506010f1a0705011401030b0f240409080c060903 67
    0xb881482a108420f19003540380d032501e5140c400c00d5140141c00e00e01004601c0e00001c0a202e024000e035850001a41480c111066542200300f08603001039400d02d0712400f45001088655029101d502e048036203141201170006000c0c408207410814a5254130314803070400c0c041c10300540d40c07445640e200d950910241ca03100c00d501e081c4281841030050000704030f03000c10405410113480e001d0030b407042d00300145000c07010400342000382c0d2024007a520402100b8843c0ca050300d002d2449200800040d2413149003210591a5503800e01070740c0e0742d20581c2d500810240100c40c010510700140052061910350b0415960b80d8006c0d070b40c810720b040d843c0da0161000b6054904c074a420450284921801002c00078070014180303082c028814100e04080014041d02c500005000c010440b0030340081e050080c030007042ca0300543e0f40341400300340c1c25011121800341c0c2c92139034001011503a42c0c92441050841e0203514207001c0b1400000d000c01048580c80c1a5003c0c0b03024481d03043c4020b41002aa882050703d80042c50702d03901c12 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 481533570 1250 481532320 481532323
    0x61c05070c12020606010e10020a051603022b0b09010b13020307090f0b090103020a120f05010510020114060103051b070c0e100308030c090a08011b0e030703030905090a0204080709050603 82
    0x102c01c6064110b400c0350051001c240e070f0003490420440c4086903050104119020300383c0c81c15508203401010b41c055400501c107000c0030980e0000441b8021f40c0e00e400804941032060340300149842143c09900e03800b403440d8000c40c4ca0034210681c001205000011129010301c0000c45024402e00048842a000000c110782070350b01811890050401e015003010050414140c20b00328014441102c0c10154041018104c00780b0404140c14004120b90302082194413486000d8050403007402154040d90014440c0c1005520500c0741c201c031038699248812545e100e600c0114050304014000c1451100b500805403900201d0400800340039204211100c965403401022000351000140740c501e000d00007050400c0821040c00407a64800c541e060301c1e6994414000025602a009411856440d0300c5d00080b800644540c046100340101a92030321002c0701040d0081598a6032103010060020f410f14004101c00d0500550264004d0102500507003040c1d100c1c4d480c1d40ca800403a43c0030b40c1c4120345850500909050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 481534820 1250 481533570 481533593
    0x120c07060203150f0a05060f0d021201090903020106050913060b0609030d0507120e03060109050a060b040b090a24030207080c030a0c0c1208030c0a0c0b10030b1003050c061c05070c 79
    0x13415608401028a0100000e040e8040c100200d5030035080050100203150081d0304580b501012500840f4145d40c40d50400c0004103000c0304200d026600c0e082e8081483d15044500d18450454904001403808070740d03492034040c003444079505400080502c0601596501070020b00c00344402523855079262a51030070003040c21241148043c0030301c0340440c40c0020b41d440200e15541911a42d08001c102c2d5100c620402d80144041d5101e6607448802150104404105000a100b407407400c84a2102c04e544840b0990b0203202c07080101035101742d4510501030b103030b0b0003a00944a81030242032440c0c01c2c010788000e45800c0d640300c02e1108000403030080c100010000808410005001041c400d18208005580c4088141c07001a140c1c41103240081003405e1000d1141c10780b40c070180d521a082c004207041c030f0b04141558414138003046a5011a16000602c035039003101c003400460b0f8100c0000c00030070041c1c90600841e0352015045041c0c000c00701000d1301442c5070500981d40201c91a81d501003004411342807104044c0d6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 481536070 1250 481534820 481534849
    0x2030114090105091b03131b03110a08190501060f0906050a09051323010606111e0a021009080105010b09040c0c0b0609070203040e24090408120c0706020315 69
    0x601001c05c0c130003110528040000ca03050368158465a075214186011556241e505d802070510018080d90036412802401306011680b041c0c804e400d8400c201c2040001e04181401150800c1d8410480c002140c100300c0581480140180c00000f015030320340c0824204009549c03c22014251110002c001d14200102c2c0c00c0b00920525800700014144240680300030b09904c10064030070440304110610810912900c40c01081484000b040400e41d50f1101400b8001480948101ca000c1c0c40505249112500b40c5804400c0b03140d00685100700381b0740e00700050f42c1d905094150402548100c0851090001d105841c0600600000070ba204d5101404100c25104a00104030400c02180354031000140c2040000d034005070700703c9030501c0940e0703000c3c000c0b4514040caa2158036000c030400140054807900b0a00d17469100800038241d10340c4404c007000d000800c0320964000b00309020821600f800b045000388400c3d04941000c110034a040f145444040a9800542c1c428100d503c10840d00d83e1689003580b0860702c0b40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 481537320 1250 481536070 481536079
    0x31006020d140412020114030a090611040501020703060f0b060a03240506030412020c1e0907080412050c10060e060108150105180d060905100509011517070902030114090105 76
    0x81c4000d4050003a000f584614090340c0c01608100c07045a000f140e032940c4030550060001e8691810143c10070151680d01d00644005180040c04d07007025044504580a64906800810440e4a10b540f080c000740041141c1e00c000c15075541090800d55038105c02802c3c0103100b0f55010030f8039403800e0f4118a00818400d104a6800e0003000100540c0d1507040c00d4a0340b0076046032561800240440c0143d05029a8030700301640084000148040110411018000c144042d20701c0030151752952400c0c1c1d41c82d07806a90103000200c0b4100541e001a00c41d100400d408031100050310b84400d00f90701520305441c1541c00003440702d81030508011880d41d01010059210801e819107605101400f07001814500c225010300381d500888100ba400140c885158034418180d003c1010001038069043c40e40c1c55010b4101000d134098200b00c0424641041400743c0501c1c800c0000d0b030402d1041ca40450b650305921540b600d40001c2c0104440010320851602c00f44d03000789060b098980d1550b0000c0304004107044143c0000b0710a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 481538570 1250 481537320 481537337
    0x1081005070e01170406090c0b0d0b030307030c1b0305030406050c010e120d09020f090a0e0f011413030c0b07031506030e0703080304080c2d0a03170a020d02031006020d 74
    0xc1d6a4481d0082c81000384c1c0e003040348110780712030170030b01c014106111000c3c0028101480008400e018a0003e000401c60b400e010003405100701c0c100b41c1c4a10400401a0016a4440854000ca080314140c1442842202107010401d992940e420341950400d030b00c120003040000c54481100d213801c0c041c044c580c40b810005884c0199104602c1403260103041501c1c41201e50703c142c00b00442d00e443c1480099440001c18000740c178503002c04d64201400c070040b5044000d000741480551801014060104030b00c100f4000085569941c99103607140c01c880060980811500e10464808a000c440340c2d94042c07903881d039021642b41c00c108921524440300ba407008041503d005c03401850840045200b1055a6010f0703409580d80e240c0b0b003030402850251040f900e1560081c2400c0010035000c0d06d40401c0e0007501c030040c0080d0400c60091164480882002c0900426080821100354049260b1303001d60111003002e0040c2026200c011010481c1c1040b2100c0702006070000040c8000381d01001782d55900400f600d0100304 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 481539820 1250 481538570 481538597
    0xa0f08091215070f1407050105042303031527040b0c0406080a020315120102090109090603020102061807080f030d060902040b180105093001020a051b010b06030108100507 75
    0x180d94010f181070304002c004003203160400d12504280f144d01c0c002c04480781c1c89410904195000340810f0320100c5206000340c40b45210783d03982c408503080750603000018504560f00c082191204c669031103841a4400158107201e064007640c042e10400c0403480881000f039520340b0789080f041c190000b5000aa9940080c4002c00076680c2c010380c007541c410203609001d6220b448290064940f10a2180c14650055440c0e500e4149072105501804001009a9804000c0ca0f43da0031000d0485066000103801600060005240344060a1295202c9141001252900ca039103200040c10900c2d0501c0545103904000350095090750b40b400754401a1001d401c086151618201419840d48540e0140141d00c61002c00081a20781c0501c050394980c110180c0320751440030f0301c000001ca5600c2ea0a00c40114220015044225000144240d13586a40c10f507c5507860b21080c03200c8040c2c401641121426259241e04030020795440c1c6401440c0241603070401440444400090b10003500d90007803c03902045003244403004d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 481541070 1250 481539820 481539853
    0x30e060306030c0f0d021f020705040c0e10120c0e0102011d0d11010f02041203260a09080c0307081201061706060f0d0c050a0e0406030807140a0f080912 67
    0x143e032000c44001504440440101d000c100c240c640183d030101c900700c640c045180c2c2079500c4a188842607400d0315074181d00c800401c0101c48100341144005003520f00054514100b240e40150908000e08103085c48602d10f0300d0140a40383c02121000000303200d503440314a81d503024000da0801c0d800211081101070f1050b04415510200c200c0703400304019030b82030001c90340002035000a0222800c940203641d1251103050651070f94030f00300c02c2140019401c2e6404070064414907000c148a0a20300340d8421140c54405485007d005401003d0b24080d00030461011855402c000902e0301034401d850054446c2080c15800245080591084c3d003404000c210041d03010140c038401e2944010211940d03900c07540f4800341d601d881c0c05510940d01c02140f800d0700d04511560400c02401104d506561743c16000b5071281c0c1803209540302c1d8030000346454424400d03000010702421144c50b01e00f50032402c9a190300c0250711640c204084251081d10b85e03a5000034102c6a40c20007106404985000310000c2c0500b00c001100d20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 481542320 1250 481541070 481541083
    0x6082503020f0424030f030807020a11011125061e0c0204090804090c020a06060b0c03030615070b04060603061104030f02130e030a27061b0f0b090604030e06030603 72
    0x4603c26a41c2d1031602100201e40300c0100a0080c0240d84a0380301500ca1070b080101d03007801c030000e5004c034660344002540d45100166015140b42e200e01c0e031202001e4218015240350074800c60084080c026552a10220720503c1c1d06030722070101c203900c0c15011070b14201014000c2500c4000c2c41041900b801e070f040480039003114a021f0000d5050f00e00207900d56a5041c2013555000c1c1c0c2c3c10a40a1030b0400d03c5860005500280052010740103034020045195200b03042c15040c462001c440001d90000e00000360103142203906a414001545aa1817920202e80d44d41040305404803030454003a560f030a414000d104a80c810340d0f02d50f006022280f40f81c94155102c20440d440a500300030b109600da51186015800103400a4950b08031000071070340c64509180e0f0140c0760160010504c0401758414641d04e0328000342e171070514115882d94650304013844000e00700b1000c031040f014003910070311080240040020700040f0054401c01400014100904240c90010300343ca607840c0c092817003101c090041c05069540031821 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 481543570 1250 481542320 481542349
    0x90c03060f0c091e13021e090607050609030712090506040509150418021903030903020105070c05100905090a06030b010b07050f01020a03230106020303160e03010608250302 76
    0x4500c07031559405816095803290b1401c6a400c0500c0d0300c14100c85803030381d0349a1051440101c0e50705040c5909a0160000ca001c0c02200d01d014088074003201139510705643c0140340c40720000e01185d241181c3c54841c1854050250b030076140e00e81c03000810a05100c0344000808047c0c0d124039008160a240c00002030150049000b1144030745d1351040071070464800c0d20603d000701600a001809200d50810404120040c0800181e019a01d800c0d10344188100d81c44410060342d40c0340d00d41c056110f0840d00111015000040c08031000441c0d0700c00421140d503014220501c080040d590a001c0d142014103200c4d080380054041110700e8201502071000403100e07840340e81134404a0001e56225502030404600d40501068216015440064104101507058101500407282c04c10701c1148001d607910340b0074000d1000d2040500581081c404034045501c0004e030240111006d1400340e9803001078900103821075145034440d03095548000781e0354185500000d2440216a81007074608005481c41d004544000d940703106 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 481544820 1250 481543570 481543591
    0x110301140409050d02010c0306050909032b050f06040e010c020703170f1b1203040f1e121112070213090305040f030f0201021207051c11010e030909090c0306 69
    0x5602192a01d41c00401d4264000003144d488110000c0040e000b070460140240010b8140600852030303040c50031074680500501801146442015108016010392070195041140c20220b9a0b4400010034040c041c05002c00c0d0600b0011410242c1c1000116200822120210f0741407080302c00d100c68000c5100c03000c1fa90001502d40b9140240c0c5480d900600c074545d49864204ca000c2400c00050342c0341c0b0b2030340150401401c1100e00d110380d800100e6005010840300241090350304001c000000702000440c02c0840080341002e11500f50a54548d102440c00d50b00c1500021501181d50810b844100000c0d18200c40c003140d094070300300725074001c0f40e016009000d2086089407a0100c11041510401c1190000c064112412128580700e181c52a1340d4980006d00761700502c9510851940e104485040b00c01c115402030080c05c01306071f0000302228800c5001c66810a00500703c100403460b4901f8000c0030100d0040002840d596a06202081100d100190000280d0303808000c1002a507140007419a802015404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 481546070 1250 481544820 481544849
    0x60a0e06040b0a06090c08010f06140f0c1c0807120c1b0c0e0903041d010b09190801020d1d0601032a08031603032414010c02030f1c03110301 62
    0xf541200a44101e138401000c0c603140c90a490040c55000000700c1c1030f20000714684041c182c0d6001d08469503003442c86814200581008400b030b505c10341600602841051009a5000981684000d806200265400700c04284d14600300030300c00b54001007101c581e13251001c7c10044901c000c0002411500d100c01031220407c01511140180300030725440b440140030405c5905402e1502c030040c1a260303000b80c42103801700b0b808061104a40a50404e0340c505031458585800c1c01d0120ba60300308119481c0444c4008400120480c0200d1550428001000040c41000d80481c40341202c41e0074080f4080c40d1103070340d900c6400080041c800590882403403250ba510551416680c82400b07502c4000015003a400314041c2e2100080084140e1070700e4021100c01c5000b528200074031503c80204500f00455108252060320160360305000e401040704000f03008010615103000c0d09481c03903012900d021900d81c40108242d002e085018820401894501d0701d81e15249400c1c840030b801084042058041806003003c0c00c2d6220 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 481547320 1250 481546070 481546081
    0x3080301060c020d0b010b071209060f051804060b0343021203010f0e0a0c2a020603310b150d06021207081506190c08040602060702060a0e06040b 64
    0x7061220310ba0445d201030b9a55035141c40441443d0300c8250704582c4c201d01c81034034000c1b0f1401000c030842200c65544880f54160b00904044426a00080303041410b1104402c044410f80c42d58070684010b010420400f5540c0d02305074480d91981c80c1402406030b10044c8801341e280b40400c02d4800507056600030349640000c0c1141182c20b80c148a221060705002d030358003000004d01c40800140001c21a650814031641644406420a05a0340300c10181c40124540da040340d011000e40545140e0b2507411071210005400d4582e002070b00c10f500558420034004001d2825400440c4600302c400c00400c020b0240f45418449907464240f0b244d07009085409034030042c00001c802d134403a01d10300c0c071449502000c21540c45410403c16031803c2070641d039001c0003c0c0740200040b250205850351618241e03008100900f407114000d0078807460182c04445508110404040318002040030f40030380017038070660b002f8161924004100034500980140113800c00303030a2920b4000d030084045040f60300181c1000106e021540c1d130 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 481548570 1250 481547320 481547329
    0xb041818080a020a020406140105031b09030304090b0f061e0307020a060504030c050c01051c0509101509050f0609010302010c110306070c0b06030303070f1b0213050609090703080301060c02 83
    0xc42202405100001504500b1503030301040320741c2854400c86081000d00e455110344260342c1029040f45000c5401040410700800032025900c03a69800d142c84240b07030541d90713004a429500160721507841076860b410149058a071005e0f850002c4041610002c1c00c005655000d5900c102c00c07150451030380c05000001c00c800920034132040402c107411400c240f045050502e0001e008001440050302c01d40034020350010590701c90030498491240c088610401c03c241d0900d403c0080001504950381c0e4442c0c0421b200c10b4010f180501c400011042240310103207403a1111034410f0320802480c000c030700411042042042e96420812078190381c2c080c604464194214034084a0054010480c136a00d4410715040000e9a603010341078025252107020488403603121081816980e0006680400119915400181301c4600c00c030744044c2052170000c000d0207803500603000700d034101c41c828420018280d180d81c104030710750614511300750700701d500400104141d40c910307240c1091a00060017074400300400e030030300442075589 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 481549820 1250 481548570 481548611
    0xc010c0f060f0c0c0605340e0306011e090203010324090218010801140c030a050603070905101505090a05061c050901050103050c03070f12061409070f0b0418 69
    0x24507100b0020802d59440251913060055011a407550a1100151440802410308240034940100c2e4190504000300c0080340d01808080c46802c1080000c03c11546582c10400b540c003c0c608800703244106038620b02d41100c424050340140040600400041000810000c080c121600d14003003c21140d04411182c50040d215001c000307540401c6000803004029014600c0a04032407521008208442500c1d01402c0c107810200d078000004002440000c0030361941d600102e038030040003403d449929407601c001008460080c1e42903441190016810711010186a594990740303001414103a042214002c0064401c1c3c8040c01a54002c0c500412010280b0390f459036440c0541505aa00307110318644110030318001c00003403205540b6440742c419010880d003004100c400a480d040e050054040342060511080321038906000c4030450f0350755189911601400210f6406008480003424501e803912304039025901c3c05810100815004010801030000001900744a0b004081c501080f40e20003101a42038065 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 481551070 1250 481549820 481549841
    0x203041424060315040b130f0303020903060f06090703110405120a0b180601090e16060c1101020106060203160503120103081e120103110a03060e0d0207080c010c0f06 73
    0x704104031507801206040c40010480100080242503564260400d030780d03010009120750120401c0e80100740495051403020b503100c07600d006000441c02e4240e82d89849a0440c0c80e083e0002a4080340c601d5032460217002e156004070490860301e019040100005e442c62002800d41c20500d0303a15010004002802000d0700d00415000b480800b11744500343d90951503011084040301c0d180d08400014202512035140201005c500c0030040030700341c1c01c0c24040390040030500354080706072107200110302d00745200480210282000c1d43d203c04580c0010701c0c1c51091440151081819641400c00c148045580001235860041901d42c101e100d6150740d0600e40c0c01d52061525011240142e100044144103031840104414102900d40d1300384803043c3c04410034030303028042c60354444160301001003005c2499201c46070402c400c001d11241c50107569075541c00c00c40d02c0b0104016039a400c5019003c84c0e180d0180b2410f0014030a28010b800d0448205000806030800310400402c02010400e00c5418810783d94410075045 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 481552320 1250 481551070 481551073
    0xc0909032a080a02010212010803030907031202030706050408040504140f07030929060a0801020f07061d060f01180b1005030711030c1606020a031d0303120a090203010e0a0b010902030414 82
    0x41c0442d43d4000d01030350010500c0d403211400b4900000c3ea480c00007044034410340440c4007418059055598141600751031700015400c40c07005001c1038022a411348500e5011314881e00729613584901c2c24007400166907038900043c03c400c0c40442003110071100300c1e2026610000324900001c88010519208140c0c0801075003035040040d80c603481e02004185908100d008200403546900d805507141007150031303440b40b404001000c000a01503400060380c29001b07040010680d4100045074024005200d2178604d00f12210003c0a4404004100d234142021105000e50b0b171a000601042d0000070105e0003818815100c4010000d00100040d90280b03e29540c0400c45c9103182079959449540c5035195450050f0b84a07078180c1c1c590b150000901c41d00002d500d2420a0f410b8580700d0a144504401800f0301e40c0507103040e5010b020400c0b82180101e4a5001c95108400310000051419018010300d42103803809951443d150b80581d40790400701d0f441d45001070441d0802c8401594907911407814035285504490007000a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 481553570 1250 481552320 481552327
    0x909050105060901080715052524140c0904020f0d09111e04050702010e0f030d0f050c16020f0d0f03120b0a0303180e10030c0909032a08 60
    0x100601904640e02640d012200f06443d41d880c0c0313050a80b0352546110f074107180850b200d0b140c18501e000d0005000650200e0301040c21000c3c3e10090610720f030f0540390044840c80e880c1500300300c4c600c586004025200800042c20402c3d124019050030071010090903044640c070010500400c15603450301285d0301d041c0c82080c1c544c0c894420848410140c02c00900448600c03201c401141c01c01e08110144801c0d105103103040186866441041c4001040c01804910855407030300400329131240b00b0003006408080c0e48008640e900c2800364100100c50040e20b168060608040500c404949414144e40862140025240340800c240c400902c1060000341655041182d6090003011b0040c4a105051064080c0d11621885400d0304503000488680214191f03002c0440720091010078460707402c03a1000d444072064000d6494540411084a640886031074080c007030210320910400c4000c1c10001c00505219405100200041da005400d04d002c6507640e035000c41580a04801c00449000c105c2ca060313400940142e034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 481554820 1250 481553570 481553573
    0xf040e0c15070c080105040c060c21020d12020f0301060f0c0b01030812060f10050f04031e1205090303030604020906130905060102150603031209030d0c2123070203040909 75
    0x4854000b036405446550b107100b800600108103004552049500005c000810342c102041515010148a82a24101804040710004034261840000060066001000400140507004100c420082c09120102c1d00601c51801ea40280c0410340341551542c1c10424903d000486080350001d00c1d0003c0078241c1c1000800002c24331614500614081200f4425040640e86001c1480b40c0680840c0e4079a401c40213011480c920f2900c25070103000c9100072821607134a0295039031502c00c44401f00b012040d0044000180510070854544021b0041a040303080c070900302040c0000082e00c030b00005140d54000e40c3c0000d503520644e070b00e41382200c00c01169100009805602c2e034440e60010174088401b28003520810038a00e40d81c00c070b003100c00b41c80340c00e008004519010700000c0b01110f00740f010300880d4141c8420b00850740c48011501801c082440310f561030450300303620300401d100c810340c0c0c0002c501c01d5149010f03010101e0740c885040781c0310018000c03201c100454548180c201c0c61407040358010b001240c5010107030340 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 481556070 1250 481554820 481554859
    0x18060e06191205070513060806060d0207050106140924060c0f01140c09030a12090806090d030c030b10200a060b030105090102250201021f0e0d09050f040e0c 69
    0x80220315841410045580d0ba4003045d500d0340f08500c0744e800820705a01003002581d10410f000395001c4005840c8508002c0c166420109a03085006d007196580d4403480b0038081c1210b003880031880080c0441d04401e050a0045c068150b08140e5035901c7c0c01c4050b003081c00b1540b5225042201c02a40e00c100840c0c0c0c2a202e007000c001d0003400b800c801d1203070404003540860b040e200e03441c00f9505120300080140060581c15500ca088410236083c44106000d440c08000500d000148042c4d8480e0300f404000c2d01c000e5070843c3c0b00501300c1b25448600f9007450718250182c503c030b40304c2d8145503d42400b181086059000310140030200151281480c1845125400d664001c109031600001c0d203901d01a0300a00c102d441d455003071400d0303009003800c61456031a802d03024400042e420762800002401070051321081c2c2801c209850a210b00c1c900e00c08029919945c500408010400408911441c203241240040b030134800011118803044071843d12403a04d41c01724030b180301c0080c00410a4030000420307422a441c0241040f0303 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 481557320 1250 481556070 481556087
    0x8131101091226191d030d02061b0a1d13020309010f0b12120d0b04020f031603050702031903020c07080d090b1e03040f020d150b0118060e0619 63
    0x401a15512040d040d015120a0035580c0074034035803c07407480b4401d130410200d0f105032420520720300c00d542d1070401400ba5282400540c01c5d01c0001d501400491502da01c180c0310114032800c2540d49041d08000e0a00398a522841800031081e490070400c4208512100041118075072000002529100100307015040d401544221010151030a0034800c00b1540000c01c4040b01200e40c3c2c02c1c5e401d40042d50314082c100c0041006012015a01c0d82c0000d000b0441030220b003c03078002c1115039100d01400000d000d00c150b011401e480b00750301a8a4144002c0ca01060020340324040d102c403031b034800c10440104184950180d0103483c201d10000302110390641d910102c5a903a52002a42e510200e980c071000412120f01c030808881d901a80103034001c10400c82c01071501d00301d07800180180d4a411821220380016614241d00c0ca6180707004007440e10041485007024801c07035000d00450b506208a100b08a00c80c1d003d24001942103401d039007004c0c0744840420700841c6103403090304c0030804401c0402100030000358001c01072 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 481558570 1250 481557320 481557353
    0x30303110d1a0f1816140408010603170307090b030a02041e031205030c0712211410030506041104140c0a0806010507030e0910120b0412081311010912 66
    0x700c503c07840f064051010f40c0d94104810a0a4844400001c8030b000c40d070131201a5443c12460048002d905080481e001904143c2041c50a6511500300304240165010071074a01d22045804a241d4245400050701d2100c0b10712412102d1440480001c61419540e07041d10028004814910051129108030070840301d441e0100b16142044013203070350456031040056922407031540202c2c6117000b8050f203c0005a080e0003a0756020071001121844003002d1151206002c591741c620041400014140076011494004007030b1442d004082c43d0401c00b044c030003d40a900709402102c080640f11116011034040c242200c0300e240c120004006001c2c4000101000706500306441c2d503004942d490b02001114540b00319100a070010b541158060305525000c4500d50b000742070031081c1c032101070ba0b880c020031344103080040a840403a0580100400d01041c1c00d0389803050007941c5401d080c207140001440c901040101c4000c2c3c0a4520003070307900b01c3d0b41d019544084c083c0c140c40a00c007060514074030b46850808509001c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 481559820 1250 481558570 481558579
    0x90c0f080705041b0917160b1c0b1318082208010b09040308150301061707050f180703022a0f0a02010906050c10090b040201080c070c030303110d1a 65
    0x1940c036449034440d441c05290b442075176203c0e204140f030001d40c0c9a000c5070001c07450039a402030702068500c095074030505800038100100100d86600489400900c440d035820001c0415900f441230800d801e40c0c6800f42c81c607010000b9135000031039080301440c1041448175020b0013130856400040040c1d0a0081d06100102c100c101915204100c1c0c03220501404d8940000c0610303001015070001c103000034015400c9550005000001318502c2504000182c00d4a2a03030b4040017003c0c071207000d40c81e0036107020310107100980000c6e034404121488840100b80321f004550075440001580001007a0040c3c4039030115014100d20a225481c480b40c15504030f0500c1c10712594071103841c856120399064042c000304201e200241c0503110401154613200c1e0503900c5c0e034462181007510b4007603d070000c449138560b07100300c00820f13000d400f0360115841d00d44009000003201a0100b00c9010f8144611000a80c400d4125010b896040c54085409a200b18072040c0c1d5008171482209804d04016011080c00042ea2541600810444 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 481561070 1250 481559820 481559831
    0x80708121003021809030c0105010303050919080a141504030e100c0203060609060d0c030b040302060702030c1902012606011d01081f030f0c0f0603140703090c0f08070504 75
    0x402203003040896102c000e400825880360016001c44107100c4590008407941a0f81c5803070044058982140d00c02d0304110080b9001003200001420704100612010301c8165803000c415090418041e56003007030400c0108500303a07501c2c01641703005003031200c0e00d01082501c0c0180c085080c1842c025010084803a8494001d84070000b014610a01c41c03141503003401d8000d4058806501c0701c80c18454614002800c00e50085680d541040004043c40140d42c011406028034078001e0815240c001e00345000506000b085500a01c2510801503000c40c5070410940003115865000c86d00d440165840502d07901030303c020003003402e280505000368007401817103220242d9400c00c00380c041c07916407807444c070b40309a90b540015800400104100d01c20070501050030070076061078442a9032555480441410000101c1e190082e004081180307112144180001e0b1500742024880c8010022045200c040010034100030191240541c806029480047c1d4000d800800c41e26068a03032510f034019525041032143c0c500451808 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 481562320 1250 481561070 481561081
    0x30a050d0f1b080c0405100e03060f09330901142214070302100f0201050f0708160c0212030c1b0d03050d020909010906060e0a0f05100c08070812 64
    0x24880c1805126034807080003801c650040c1d00303c034140300080c80c2e40852001007001041e00c7c0e0382c0b0542c1c0103c3e24204d982c0c40d0720340702114083c181400303405010355a4810321441805148400400e004030700c1031107554411520025446032003904000d100780d0614200409091101004040d0000d5011081c810045d04540d00c0c4c50820b4140110003629003c040c2015614440010308003540102c52142904212400191250005160101c9070200440422080d0818004c060740a020301a40000c1b954112806072a003294080c220280007030490711103544902054114600034110050200d4000d80454402224084030350340d00e61014251030042c0c4030f07410210214071006041440901409441130b80403c105950507502071300180030030b0131050380a010a1565440d11425140200001e220100f041450b1260140081c5950b003021802280401c43c107000e0070340407074250011140155100108a94550b031b08880d110306400c001030020070000f03003e006002003000a848026160a561203480e1140d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 481563570 1250 481562320 481562351
    0x4120305091b010e1314100b03060d03050a03150b0406090902090604090b010c0b0a05220b010302100e0411130807121b0527060607020d0f0203010e030a050d 69
    0x40781100c0101d80780c00c0c00b405081d5441035081a003e00c002600f6111001014000482510b81803058503000e601098200540d1416511000000309039400070103296043c10408107882000300240a000c1c0600001d610980314400d6000342102040c891000c00741546841c905105607015200f5140010f003442c00120700a0101d1007140c0144074000c110600d09890802c000c005020680d09040c180588140340201046281070020310074008407070700150301e00d0150602ca40070107a0741030804082c0301180502d0005032070302e10000d040d02d030100c0e0319414810b0f064074100c4030040e41c410310311340180c140094a4202c0d9104005028502c0141c10016400d0341c9030300d8070075076582d1540328889540042103400004518040c100f4204940381501d018409500c030008610303100740c940100030600e81c0c081581ca80f01c0d000310300706940080c2c04550040ca4481e0a0700007603500b140c26140545010540310709402195000d500248600400c0741c00d59840c1d210094026129811200c80c0312141810300480d01c854008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 481564820 1250 481563570 481563583
    0x9030305041b180518030c0a0203060709050f220e06011a030f150103020d021903050a0e0c0f180106200102211b0f180402130b130e0412030509 63
    0x880301d10307402c0701180f242c00684005460a00c42c81d08502e00351510071302c2031000f004078a2031078000300810903852041c5860550300416036410041c1c20007007030100356128405060340e010201c91948020101d00d6000c143c9000000e1030026051800b859441000f40205165040f1f45d12041c0d0f41059820313815051070740c0c0c0300440708805003105120000780600e20300c0d041812060411f150050600b54280041012a0300c0fa12059102c5c51520f608105000d5150060a501802001d0b0901002a0300c1030015600d08041608600c100c0d00700d0281d1403140c884007030070214015010400280e559445101600d80c2c0842403003800e20348201c0d40e0340d90041c0414000ca60510304517045034014040d80389502c2100c0d18002d0040f00078403803600903e605410400c0c01810949400c1018959164440714050600c010350781411400790b0300500121548810610311030341100d1503c07a400f0341d03503624110000442d45641d00102e00001051040c0014007000b80719a4039003034401c0e1410869503c4604103a43d5030072 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 481566070 1250 481564820 481564829
    0x80d0c061a0f060a0311030c0d0506030d0212070203030904060b090a12050d1407020d0501060f1e060305060d05030d060303080f090606061b0111072303030109020f0d09030305041b 79
    0x100b021682031281420002401c0700c0d5840d03e000141c008007182d8080890384180c50300785100b43c01050503a40d403400340c4103e07078000354200c0c000c3c05418240700300607403a5040e05e45c0d00b412610303001c2040810b54030288111028044014000c002c2d01c2e89440c40c1a046412901c1058000c010688000c14007040e02c103c8181020380081c01800ca240303084104440d901001c1c02007480e018424002c80005072100d06044680c14810400070900a0921000622100c1c05038491901b103001c0c003007000380c5400d01d08201400d503951403601041039690100803940345d1100d010000c0c964400000c0011f58031555900032400c1c0c900c44e50350031000351034841c10064034080c00d40d0149200c0c7c00c094041125460114010045003020164091003200b81c05802400c45010080044981e100015458200b00000f20001070440e00d54804d9401c1c0681107402640e24003050203030802c9a5800200b03400c50b0f00304c890039604650f0007242c2c180b003044100d10f0014050682600c0c11911510608803110021110060200030784 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 481567320 1250 481566070 481566079
    0xb33040f1a03040c1e030f050607020c01090e0f0709080a050303040201090902030f07030902120304060206040c050105040e18210a120516031a04060b070c0602010501050d1407080d0c061a 82
    0xd82406841003012204841185c0c0c4d40c903050200000254a00c2c08055030389000790302500007450500d002070704069100005a040200f01d030402e1208052108045400030f64511944007a41d90307040d011380e1415050340105207a0311075118100100034001008511451003a40e61940c0c080c1e5441c4500140d000030b840001c4bc001300c03c4001401184603070300a0f0751113400204400b10403002c80c28040c0c1541d001b81c0000300140c00244c10001031000c5803200d88010310007881d01d40d1805103085054180c103e005484dc20300c0c004c0c40d001e203550405003000700e80300d46000c44149030012034050880ea00203901c011a42e002007080c550480820980600c40c01e44282600a090f640040500208070020010451110b24070301e28040c1108854407548642406400078071003095469055050014210b06950300c0307201160b0400c4014407458450114005100b607111088140c8400810166420f150082c1c001c0c00d51841000c0940d03185541c01280c004046d80a000704002c42c59000c4c4035000c040c4c010b1862590130 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 481568570 1250 481567320 481567343
    0x705090c0d0f06361104050a120819050c16080f010c020d0e0402070602040f21030c1202030c0f07051207140d0c08030a03020711040b33040f1a0304 65
    0x340e520000f04500030981c0e503140c0c0c00d01c1007070100d41d542210400c045c1c4058140c40440e050005092804001000e002d8401c105800408540d0b295011880b80c19150008141c1e010314120b0740301c0c0103009552460000300309070b8450308400c806511968425110352034851081c4123012442d840180b080310002207150780541500020b4490030b0310021040c1c002c1d190000da003005500041070151000c0d00180030b0f903a0151103001c3c075140c81d000e40c2c1404803070116140c009907625030001176041140c144a40303070b01c6200940101e4007480140e041d03000711842101e060050342e40c00002c03076401050010070303501d0456910300c41080003154a5691502c3e4040c0b18005c088001a01c9a01e180080c49201e0041c81080703011103440e15110024119004001084086600490b05034100001d0100891084400b90307410001022100c00003030325041c081c540700b40078110f100c000143c480b40998506143c1880c1c080c105031b80b680d41701e034065103002c0b075445103c24048112040c08002c140000032a4007031500407200045 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 481569820 1250 481568570 481568609
    0x80d0f0929180604031110110601060e0111011404170a020717010b030a0b07080609090a02091518100b090144060f10021e0705090c0d0f06 61
    0x194800e40344403480e028842d0040341c46a032101c0080c00914851503044c06d9403402e4100f4013920b048180242000c1c0614203030b03482c80c46800001c4c00c5045908034074110841845982c0141da21320840b03141072155500744110350f0303520401c5000030f500030351007600400c0d01130442800c501018007400d8411401078005282c1003108840401012001503511800025041035190000c0d01c1c007410800c00319810f0800c3e400b00404141c200002c2503100758241c407820071a2810030800307a10741e14a000028451042e94000c1003003010b2803d84c0519000c00502106802c940b1207002851f40030080f2104c980c00a213222000c0303075210044045c0c90101c42d042c0c41c1d46c005000091782804072880258004040a8a502d010041c204410600c0b1845001d1074110617403642040c20074016003000a440181c098610040340300c04044e400075202c0e185d0600c1c0b02085071206d8503040c195051038000c0c0d00c6950f00c1411801030060b060018401048030002560b401c1042415141000c000d40703042e44542c1d906c564003006083ca = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 481571070 1250 481569820 481569899
    0x20903071418252d0309060513051b210a080d2307050406031808030a1d010c05030406050a140408090a050405150f010504080d0f09 58
    0x4420180041c4000d465103102c0c03092050420080360319005200d0f02400704076000d022843d08480e00c030302514007000c200b0840300031400c48000d03410340c003000c40c0380003e084500940319600443e40e560340301e0030920190401c041d14041002212001b03480c2809112010100e41c074600340003120103200034200f240088040e082201c0d00000b8610090110302500049c00000307402d4000a140c403000c0f14078001950800381d00e0b07600561010751840c032103810321076080c0a5502d82000a0740c04030b030000d2402294403030f50020144410420703140000d010010110602101d40c05640005a402113880c4180d403040d000030543c2420703250803110b40030209c0c50810104010036001e0704003e034401116200402d084200d005400d01000c81103605a600c410089102c040c14a0940c040d0402000d0840e020b000c1030904401803421072045580b03440c40b52640c9440d42e0101d90042c400d84001303000d2007058406540704a407024214904880c0000c0010340003101c08108031a81d103a441701e45151000c400d0007407000d424402d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 481572320 1250 481571070 481571099
    0x30a060501050c10090305130e1821031506030406020301061b030c0b1003120809240a0e07080a0b040209010b0a0804020f0a051002030d0f023a020301031101090902090307 75
    0x16001c10808005442c40c1c0040e078001c05000b0880c074427141e461441c0600040d130019002a0001d1510340140c030b40011198900800d91500007600ca101c3d0303a80380c4800c0d2039a108070441d01c150319005580802040184411980070b18103d80d803945034480c00c500c0d01c0491101c4222170080040208a1111114020484010b1600c0e40604945002040f1907202e855a810b000301c02d41c281c10000e1614810840c03520780c288103c1c0ca8a5520020107071841260803071848010178020500429203075200403080800308200002002007094a003641c11039851400d0210540908580590040000d403000142006c0428111f4042203410b030707a141c40d180c03940c2d0301300041e8880f008103113130340001a1701c00898944d07900c61659224141ea40c004560710307c1d0240700c04081c0d50b10007924031040ca2043c00101071100e0440040c0110340189507020030b030354142d180000c000c0c19400d02c7d150703c807e1000c4000700400a4140c400f050352807090304d8400344e5941c0c841d020300507031081c81700407501500041c908114009441951 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 481573570 1250 481572320 481572323
    0xb01030318053303100627080a05010c02120301260105070c06051b07080309070905070507051b1309022202041d010b1207180308030a060501050c1009 66
    0x3509081d9a5078070000348100301d2008210341110784005207001521407803603205003c03502e00b00c80d1410b520707121005c8105140705129000c1481011000c0d00c8030310050301c40c3d60755041c00c1d1b91101c0b4001e81e1110145a95034003c5841140c2540c6054018160103000085805400d41024011407950303081c8103c200e05140c20b00141c00100e1400d00a04056603028002c0b030f0311a41640e51500c858000a091000503a0700180841d9030000c50140404900b403400c00031030f010079400c0035516640e516403083c1e040c03070110180e214081036031810051113101a4800d00409805010310115441140b811510340302e5403c4140c180c80d4011443e0b0421b0040021541020000d140020000a15003000c4d50004c91480b150b50340142a6660024050060b4980820485680f4030400110003041d8101410880c10b446085842c5080744440c0001034101842481c1c030400d00401041c01001644e81e88c608004182c00546581e00618140100032445512036010340f21541c044000a1604210301810b1000038400c0b243c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 481574820 1250 481573570 481573607
    0x706090308160318060f0e040504051009080c0f0c0103110a09180f060f0e010f1512110d0c2703080702010201093c050c01111009060213090204030b010303 68
    0x1c00c50369513081d210705001424280c0319035614200c012001052071942c900034511440c5003c00707100c0840d07030004124a0441c450303038001541e0b00c2c240c14918082d0065803c510442d2158908101d0070280c04507444403580000c1c0c070140001441040302030128000c0c1644c10000038003142d020000301e115003d0404101040101c00200181e0311803941d800e80f22a07401c0038142d407549c0301c410040301031a040f80c00c0c014505415036524160409107602440b17207070140303004200080c085c2281102280d55202e00318019503a148070b40e4034840001d11601400c40303526540041001015103c503550005101c0c00f48000400f08005565400c554540c0210f0b00028420780c11503584070204c40020f008420302c4858417140f20007402c00c0c1a203001c840302106030503550314014188460000d800281d40041c035050310044c2400d200192201310030f0306901d03100d01c024074030880d90b0600c40f982c0b0901c0704660040c0300c101c240301d10f40901140c940c15407005030311071440300425004140c0010000f19100340d0002c00400c03091038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 481576070 1250 481574820 481574837
    0x609060625050706020d080424050f06130b060d0e19030c06060515090906010c05030f2203030c080c0115030b161e030e0109060504060e07060903081603 67
    0xd48501005040c0045551036070441c0152001c0c8441081010020040d51004160132114000000c000c1030015000414424910145a51040e40069520b4001e10248001c121394a0507908144180c031050380c1d420f006102291414420960310b000362030700003034060104d074035100d04d05c420300300100aa90354151042c0076102890120507144004004542d010b5075a4841041e624141002291425030160384104207800603a0158140b031000e95080301c0007122488203a60b11980103903816042c004000740f05000010313030b2030320309a41d00d8007900482411408840c140e10240103014110201408007902140c04903640740c00181c2c41d200100501c1c801e860001c1912107070f41c0c4000b400d5411940045418140c10406c02600111034164426403066504d01424102404210380c22010b49402c0c0c41c50030551103c0e240384c229102500510501a07014a0801461030300d070900c080108003030f601c086682d0003540c031300088252085032554107072600849200d242c043d403000c010040b03000c9000110b041c1705094 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 481577320 1250 481576070 481576087
    0xf04020702040903200313060e040b1504080f06060d0b07090308030f0a11031605180d080403050606100e09060a120c1a040305120306150a0f031401030b06090606 71
    0x28040e071545a40f10391242e040c0381000100000c0003103400740d10305d002540700b482404003086041c0700f107508694076800c0140301d48601c01b02150140c0044452240c1000c10104400c103192101001081252a85000e031280e91200082c0359448060503502140c1c4900042082c0c0302003078610312070070b0300601c2c0340c20024207660350317507407401c440340c1080fa8000c902f5044802042803215560003105002c41c1040080341c5540b8240181120811203440101c0402c0b001249460b84c03282e01608080e0828001090007080460134a8030241070b61041c003081302e4a006143c04100e80341040007130040d5102407521103019a00011062012454008004691000c0728420000d880e8611444243c50303d03000b880254045810600b001400c91819011a000024208401c00200d803010810151240e0394803500c568a4030385000103152944440d90392007644a000a541c600c282e0480004010701c98242c8082c81110018060f803004400c003444080e000191003000529a031402c40da540e9400304000341290b0605418 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 481578570 1250 481577320 481577329
    0x902090a12060e070e01060206270703050109020f03120409090602070803070f030b09010807091508011401060201150b0d09050a150c090e010b04122402040e1b090f04020702 76
    0x2490945442e03588882c0811581c000b8030456010700b041c004008020b51600300d00035034810b0002c00f0300481d003144050b88910503e0348030304540713591200d604a8002545a080040c024010450b0880c4103000c2c61541d81282e080108114140d580c0c04405503003400e2900c0580005000360550032a03159608019510000e4001e1000e180520b926a0712405050724400c0054101e66448850901c200d0101c001082241400111007041d6101d110011980301c1032001110003800f029044007000f54200310031900804100c060840c100c840c00d60017485040350b40c154080445485014442a03024100003a4a12011a0300264441351261085480000c0c40b52120801e1112002c1200085034035148c11001d016400401740020b00480048400075516008044040388290f210b1041140b4504000348280400c0103001c2c000c4560b6030078581c210200b9102104002c1d07116008200300c6030910804111035270320414929410200d60110b807441d141540b0300b000800215815080e6015400700000e0700141c45 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 481579820 1250 481578570 481578599
    0xb0a0248060f04051804150c0e03030a03050906011a0403170702040f02030610020f060a0e0a080f090406060f080c03101d060306061c0803130812100b04030c0902090a 73
    0xc6002e036503a1524102000c208648030b500b1100e40c14602450240f0001c161a0407400c100c0002c481c40004150314059001e0b201600310540c000e61601000c50596000b030b03015006940b04074003900a035003480e0b0700c52401c945603030300b50f2a041c1d10300c4a0601082c000a0000810203043d4112515000d0504265500003020754202603001d1a4150300841804060300302280035074580801030014041ca024068940da960b4140101402d80e1a40c4820180e9030700c0c0800c0c0805e40381550080080760ba04ca10803484500355a02945249000b245480c4001a6a52241f0f82c1d4802c03041c0d856440035140c1d00c9a6000300f41ca07810240c032030301080001050000f0720b11101000b4102510ba4600349040a14203071013010f0a1420082005003d640050309484000c0b01040d444511071340d00240e51500c039201c0c2d0007100760001188900510461001a100150840c05130305940f145038a509280000c94485180075810b00403440001c2c4940029641072080000320740181c000c46034007610082106a50310b5a2440c2c008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 481581070 1250 481579820 481579837
    0x100905090a0e0d02030a05091302071a010510050c1b030c03011805010b0a0b0307050a170711071e1215060b0d0b06030103121d0306010b0a024806 64
    0x60380c0d1900c0d080d41040034000701c0d8003c403050014500305141402c01400e07a109551085202e5800390b0b03500e1002d0b8100340d05540000760403100e03600c3c07480707007c01542c450030780207001d81e9100312070b0300c44582c1130b4910510480d803c440400014182000d44048442407106070120701d83d80c58080e01030000202c0e240ad10440c1d0003598914079040d1170440608201e400c4036400c0c00c00074021419040e040c4000c0c030181d0f0441e0740010071490300035915200d0003130031501c81c00c0040c12501c05408040a100b82d440c4e020624403201041801076800040c0d6401503544204901c0c90340300341e58040d80c2c000300951740488207501d10041c01981c407443d011a501c0c0071101200c00716045004008400310b504d5000244600c55001c01d0541910650b2440d410354a44207030300c0001c1d144d0b203c200b0580f209030401d00f48103603d400d0b0a259002c0d0488040396100d82c4e101600c0d0700004608001072140c0001c4180d0a801114100c01c05140300303151034512a148225007a210b80003480000000c028003403941000c0d15075200070121034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 481582320 1250 481581070 481581091
    0x1804030e030f0a0618030e19050604030c0e07171501111c081003020f09040201030b0405090705030c09011a1e04080604111e040e160909020906010f09030210090509 72
    0x81d542c3d031400c0d07070071903004240f80341441024810704030009802c040310096002040b20b4018200c216003c0d20990705038183c01c820340104000c45c000042002c1506901c3c01d8820f041502005a0350b103410880d400092030140b8061500040c0219501c038610140d900680c20061401d546c175485c0d24080c00703181008240b1501075031001642c010204541c80500150803614441100007014034540003e1040100519510322800940e00030070110ba000c1c1c1e01140c0f480802070300a00c10307840c1c905291602c0341c0c02840b485d070080c02440320090586c5846e100850507140405011305052030000503201240d041040304d0000d1101214000c205001c24002400041040800812079132402f803514a08a400f92133005000d410b2400310824142c0710041a01c1407000c1c20383c0c0000e044103110b404686000030503599801c3c40013520740003252545c865002411a640203603500b80c0c42d5282c02c0300460704d8403041240c05000401c445010700052601c040c0c80350380311034540381c07001c081616240019011901034603490900c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 481583570 1250 481582320 481582333
    0xb1305190e0f062715040b010b07020a0b0a20070602070518150102030d06060c0b0f0705040b1c0e06090706020c030a03051309090f0b090703021804030e030f 69
    0x104150061080341000180034092004211a280340e403154050000140010303102040c400c0760003241c1c1840c2250b984c08003260840751216441034030040c8165410f503032044c03402e400412010044070495450f954094100b1405915041d14184150040d4140a04100c80d50dc0b1000c200c0c0143d21684560444407000303890418078055019140101540c040340c0100c112840a0743c205049107800c5921141e00b081d540d00480f0f0110040b030561041099018126140c0000400c5490b4801146840f4500c6000020300c60380b11a1420203000d00c04599900024034100010712260001e0400340451b40901c00c244c02c52030204054034400e44801003014030655000404002401c2000c121250040c0b078140007621030004038070046500da40078400d010b0240807000841e540202d0150007600001c002022003000384040b1031030314502c840e006030001c0c0e610207084d0010500c0844082000801ca950081080a07244211f80300d140d801d000c01002941482000600c842040d1018003002c0c0791402040c000c0c110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 481584820 1250 481583570 481583611
    0x10612050d0f030b0a0501030c020a0b10080106051509150f0703081603140c0f0c030408010b0112020313030c11090106080a06080a020310050907080d030209120105060d02040b1305 79
    0x824a090b400000301810a80e000e5090f80340c0c60b00394400d85400b03190100e01c0700b101c000d083c0e1800184603002800300b003902c400c206040c0c1140d101c00c000d94910300000e1000701d56500801c0003035895045c20224900007045642e0040c0340c1409003020b110080e010702070034103030008150300064122480640c04902000d0400ca401c40c0240d2144020543e00c3c101044442c0000c3c01214850b08010003022224000003074111444103050161100031102c14100c80c0c0d00c85d22680c02c00c0c0a080381040740350115031000e0040c1169007503802030341c2c42002e80c0e051000036001c4684045480040f802001d5810080c404807038215516582c2025000c0c01158035102c005007050b88059048a030300e607001e24881c1d04040201030050340d0100307646640300002a408102511480320b11810240e20f0b9102060700c0c0325501d01c0c1e00c1d54a40540140895540484075040b121807008074260989404544450703129406192101c011b00d040d600041c1e02030300103400303170300001030221840048075010b0740c40c4069480a81002d20 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 481586070 1250 481584820 481584827
    0xf021219121515020a200a0501170c070606050d0606051512060909070510020c0a060306081f02130f090b04020a021c1b1218050d0303050603010612050d 67
    0x445a1003040740400c0580d030004840440386460b030068441c0f000c95414031000c070a2081042c1c481c100d8001320102ca00c04600400210360b60b05101131503020381c80502d400200ca6010f004590166020710610784030590ba0501100c142d030b800031004403044c079030700d00f0040741c1c40e29030304540c91727041d449940300059240c1070404001c1c05a41c2c0c0c1281c0007013840d08020754180c0400d51224603402c01810f8030b2354501030301c0e0841c2c0a4282070094104642219540d40c6038203c07154001754001c0441420b4503000642926540c0413010f44103240102c1c4515400084003852250395409410007180d0302040041c28608000c40004150601d90700400c400c0125903014400080301c0d10581050242c111000c40c600207405030040d40b2000364582d20244940c104038610304c010f0040e0b00b0003482c00307001d454241801265281240003044142e1ba044c001514610b644041018144041010b51340000c01110280c03040d95021800f400e401000d5a400d9500c6190000f203506201e0090400c051040700904201c048100d07005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 481587320 1250 481586070 481586087
    0x60118030b1b09030c01030203040809040203091e150c030403020f19021903020a03031101020c07091409060106090b0c030909151f0503041509020909010501060e0f0901060f021219 79
    0x140d114101000203e4103540d0001e001c003d032400c00e0801503100d589505140d0140c4c0290a00681c006000004001d0052001324900801c0c01c1c0b1080d107003c1d46405000b83d65502c9107502c150309484000940411484039a04020710f6019220380b040340c05620140c0c000d142403205100301c241d40c4001505c081c01c02c501e4948805240f2017603640d0300c60096899600000c81d030209520010f03090003803040c180c0c034040341e080d012030b4540542c040440309125694410039005102141c2003009151082012802a070000f0410701e0403108550745000c01d041c28544080ca15501c041070841c01484200610400c5403102800107108103014102d5102c20142c0b0002d1083da0b00203e5021034130000000f08a01d82e840e001820390750419000021210f1103840b60b03143e10014030101001a52040c420f8007008030041c0b054100074140c4000707a5070449207000b00010701400f0804074014a5005a07080700601c10b4030b22520300f84108002910407600005d500a40300140769102c800d242d680e40031548000040642c010465 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 481588570 1250 481587320 481587361
    0x80124081e0a0f1115030c031f0906080a0303050a1401030210032003010812030f0103030c08090d060912020c060d0e1c0315051219061d07081b09040b060118030b 71
    0x2000d00c2d47c5007440700800544002040c5040441e40c80213481a01c0070400710010141c80c1d285800c12100c2d8079070b10450360320001e00d60304400003410312001800b0240c16010383c0d5031740220000e25030f01d142d0841d400c003c0c0300c00100307009004140d9200003440003400e43d41d800007000c0308051072141e500d5040000c0b890030201802006001000200203006040d0251000181120b4252500ca441030320f1524002c5000e214607003200c2c0e400740400d0741c5101801100c0e032140c3e01c0d061058440c0562107070790990030387e143d0501d960500e50010040c000000d04042c0ca030070400e44041c08a0940d40400024074400ba85148910700388000030359500f01c9080d890046032400c001910b011540340c60391035001c0304010b03541d00360b0621859143c2000510700040101b550410500380f103001003417007075a800c0042d0181d941c01041c0710b40702503841140c20b900c0c15140310f4643c140c03038a100900102056650342d11522255400548030b541000350b8401c66100c1340e0400603420010f1840b4142c00f110904000d00e042c0c444a515090 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 481589820 1250 481588570 481588609
    0xe0a050601111b04020d0614011e020316080f03040305070b070c080403081c06060224040b16170f0403020d090501230408010204080124081e0a0f11 65
    0x10b5551030440080d40200e904548509412030385654004600070f4003401c9201c040060901c940407076411011140c0d580012000c1c1d0302c2c2c41c4203030714411950b1044500400c503000941c004001c9090403000d8400701c1c01040380103201c02072610045034990020399104443c1138000641c04130f005001c0009606400350810340c640f42c0303584050341c41d4444850740c0c4501e02c401014a000000d40c0400d100c10081d658001e200340010402c030003039851201a4a80460044100e00c0000420b1003c82580f0200348a074051b6800c0020404550b88003140400c8040c1c3c29000c076024408288a0446151212400c551144095449464080c201440c003c1d1502c3c041c01c1141c003e003c00d41800340502e9912020006403110a8030108012510581c00d00c0000d10990300662895400020045640b0105401c1100310070b14003a0b18070714100c0003801119019899002d0010590425038865880c00018104106c0912200d01515044409550303140f02408254204031072180900303445c180903140c5040e14888801e038055 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 481591070 1250 481589820 481589837
    0x40308150109060503061215160305150409080d1112071115180703081e0f18210c040b100c1202030c0d0509090604271b0e0a050601 58
    0x80c00b080c1032805a1820443c0c0400050300075901c601c0c400211a00c0b0400b0355007c00c808442918a81c1d108940001d040c10041c40702020480c464443e80344628503440198450b2405901080060041c0c0d00c2d00359031988082c46a03045500a5200300d103007001d00c2c0c4200c2c80d85c440c0f141030845407204008004005001500450081d40d4401040752082d60220790080603c90b42e402c5128800340e40064522443c1d41b041007008002c20440b100204010195180b640c03501ca15884655500361040c02542064024240121614003400b205940c406c41d20052030030174114200c0d0f602503e0604d65165400d00e941c010100c24003282018480c5100080c41505c12174481c25045201074000703101d03500002c01c45851122420240c0f40300380161507103240c401c000d8072140e1000d118001d00980008444038842e400560100740c40c1d180074414207000d5410a8540e05031101d0b1503480c802c0030802d601c010b554840c011050714034031032544c441d64030240080e860a1b01840c101104890107c440c010146810702002c503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 481592320 1250 481591070 481591111
    0x4060503031e0c01020f0d06050d0201020a0f0606050607060b120601052404090509070807050a060816030b120a0b15030606061c0906060510020d080106030b1206090105040308 77
    0x100031a2509200c441901e490450b00a041580c24411031402c042254400300340240c880c500c0c0c100811854818840a210198543c0100000c2c1d0300c24410003405030b44595130803000619030580400000d40510000a405a51540801c8459020900840318a42e441c01c9107081483c0603c490261443e088004040560420011404200c1500007400c031052010042070040c80d0701100f110082e103001713002801107003000f02109076180741500551215005203400400c1505111821404840c0180d032136515949929148134031748940008408105500d410f042001c1d512070300d00c2c842008801034000d160089030350420010b40d10010b0030340081902c8400c14600281d41c0081c03940d401c09801c8400c150390f09002c106403070090007194014001c490a20f0600700600290307501c100e0861310180c0d50201c6071801101c2c120b854414420540011030074400043c0001740c0f180c0c0c070000480c8005407540281c0004030103080e141100031584003441e42e449504100804d9480340006400c00c040031005000410794 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 481593570 1250 481592320 481592323
    0x1804031106010e0c070c0510200f030a0f020a1a150a03120f021e0102071703090a060507020f03040810060803040605030411010903020405070c0605071b111206070f03060504060503 79
    0x14126034141c103400705018081c40307a8a50903100030040184002d2380486441c50103013590100503880c0c20100b44c154500315110f0030110b0000300820310100910702d030020500c0180e03a5041d880e0419004c51081480d03a00004888941d480002c5134a100c210303100d40781080200908030a00310885003d900850000c10003d003509180c203d05803040c0c141143c03010200c200032443d0180c8a81d840c03d04842c56581204040410360040204074021022000302d56855072961089120680f50010542d11000415002ca0081e500c0700b900800da510580365250a81400340c0e19503000b9800201841d0000f42c0b9400c40120700303216800060055002550503e8980600034184d40401080940280000300703061100780e214142c2c84000d11350043c4104924104060b0080c880040c1050860306c40c0e1512001c1244940216000001d03000d400810905d40086681c40b10b1982c0c1c07a540811350840f00d1035a0490392030b8000c1c40024880d284030b58034038005403070001c0d00500380c0310a03500540c0510f152800c10f210b1600d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 481594820 1250 481593570 481593599
    0x100c0201063b150f0409110409110618090f060a1a0f0a0302070b010f140103020d0207050a0f05100204140d0302070504111b01050108031e09180403110601 68
    0x40004400015900551101642c0300d000340ca50000700000100040d200034694000c00000f0b080d01d00303a11400b0420103200845034401e9000d020103840c146001100d15144e004501028402c19060a0031a141000f081054000c2040040101040b100002d02401c0800e522580001d8103014a240b45c1400e0011a0102b0a640506415925804007224145461008840890071740c0d80d0311079502c0c120244000c0081d040481c3c225010400403000059400c005034680b4150b42d00159100d2441564400650084d0322100000490a80a00402e40400d200380300d100b0100d070007807021a05032a0245030881c2440c2c0740f15544410030744140b00c1445801c41510030040b01c10420740d4010b1b0240803509080e441c0250550000743d0090130500040e01903080c04000e0310042410f074122484101d440c511883c203031070702402001a903a00611509240c01c443c01002c0342444407920b01c2c41c0c07810040c000130a11980c0001e4150301d00380940d005010405500c145043c1d882c2c3d10341405844154102800071644c0c84 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 481596070 1250 481594820 481594859
    0x9010b0f130b19180606020706050c0c09040804030201090801020f0d0e03091216061704080906070c060c1505100302150409021801090605040305210c010e100c020106 73
    0x16440308000141541da010112400d801010b82d01000c10756101005203420390b0140000002c882405130303064008a000d1802075450b10740140c9441070400f04115025000124500790901c135030000c19850b611031205036030085001c0c9400d107a8403402c1d4000581a41d02e10361040300b0f642c0c410444000c0201401007511200c50804101040c1120607492072461802031140403903004407000c0c2280e070001c0b0009900d840d485940d00c548883c86681c1d21040d00c4180300300d03010304052a901000500020600c600801224074001e02c1582000469200c0c40e48004040e00721070003080b404080756040c840382010f002c41e90307000084184400c3c586010002e081c103519100013801501d03424111070300240d0300c000380d90180c050341d80115290642801080300c04402c211119001c1041e0b91000300d21244920b0403141585e401a004004a0803078401d0780d11a81ca228182c490082020b000c1c029030003800b0300400060041410040540c0a154081c00044032070219038101960315011080040e04503406c44c0b1800340 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 481597320 1250 481596070 481596079
    0x818042324040f090b06030a03090b090d141c050901051e160303020307030506150703030e0f160510080c0f030403031805030706060506090f0402030405160b0d0e01050c04051909111209010b0f 84
    0x10260533002ca4030101c60281c000b46076943e0642c0d0001d820f40c000800c2d820440c41818034203410124a40143c4042c030500320b0860016004200f80291484070100380fa11440000c6000d0380f802c40c0c0002510b07c100c2201408034002a000400e01c00c00e01e03414090290000c0e8119036508000506003211059849042d100400341034a0ba0b401030508031081c804c02d900c03018081e094a6043c125496001a84491806060b1207a2465280e00900511440090344682c03455180c4070315003400c000e401034950304000d0040b02015119601c2d03507640e2020760100b0000c10b02c10310007980c40341d40e5454508203641b05900842e0013480140b1140d12666a0b1081108554ee070036a0016a03e48460503c1d5003004000c00c41d00d081c0b03071a054400505064140c00501c2d1040030000f04000034003e2204250036903805032029228400240003d01c0603240813011030784020460001691460f81d5a2810000e44503840700d007a5840c1800f00d200c030200e00d10b14000c03c1e40615194020494480c40710000f4954024505140c1c0c0030703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 481598570 1250 481597320 481597327
    0x50405060a120902041d01061502030a14091801050103180206041208070f0b01050102100506030c301b01020a051207020d0818042324040f090b06030a03090b 69
    0x102d01590041c50b5541d009002408200c8000c180c1c1d83c504140c005c01c040c1e039036182400c002060300d1340200103a94195654080d41c0b0300011154211511030210001c080f043c1d90821035082149d54404621001d00b54080c4030400c1c5600d03200005d004c8802e03000a146042814070500801a030b207903800c40c0c0c180c65502d90884119615400d180401e401010002007028000c58255011b002e9144034060407140c0982c22036144a00030529202039950540c3c50a40582c00045000c80038900034041e1004402901c03c1c000748030b02c10a52050100303450558003203d50700201d01007840703010790314600d8441850a000501421080b1f5543da41c1d1220340d44d800090401c03000c207441e01155034020140090a030081001500c0c1c80070304102885480c0c0c00e0344072612540c600035203e101d9150f40c4052031140d800c480e00d04000c60b5988496526422214002c800714468003603540780c07250769607100c2d40f0604010200300140e81070507840c020590440150016100c0d501c000c01c0103001941c4442d100040c0d849000d2200e44 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 481599820 1250 481598570 481598597
    0x3080307090f0305060406061208272121030a0f09021005040f090e100c09080f03030f0709050604171c03090c051f08060a050306040b01060f050405060a 67
    0x9003801d1940010b4a400741149000050110006000e8002c600901d82007140603a103090203007106491650044c2410301c1071000400c2a02026240c240642480412000d41126000080c2010b0505800e01d6000c0803150440035114408010100d0244a2580340b14000b1600d440350060b80d00008048545842d11542007060821050700303c0c40020398050300340c3d4040800c0c120080c040750054003600703c48400030000042c04441c44c3c01910b259040d040080c014480080c00300c0c0000d00b91488018051185815000541d07100030840345800111510103981c407420031949079a1103901c05040f000820110354030a00c220b0342c444d070881d002c440049000c580302c20b1401e02c40340e05009504076923100104880064407901c2e07400d41c00c801c0c0b1841c407a1101030034150700d8800300040e05038848030369095410681c1c01c0700b51190180303a1103a00309900038140040300da0b071040064984032046800300e408800007401042600c3d00031842000010b1942081810700b41000c0100d6036034003a4a030014200007a0350306004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 481601070 1250 481599820 481599827
    0x60906120411191e0609060e0a05090c1c020307081f1d09010b0409030203030a0f0204030b04050a030f2604230f070f0f140a090c081608090703080307 66
    0x18000c2001900c1c40800010b041030110041c5054814440c000a0010300c40b1464004d0700c1209050f148a9280c003100c807402c03c08122101407820b001d0715040300c0e81882c003003455500c0e10803a41c403070410604083c0d60303400f600944c1c94000a03041022604035005109024040d030300718500641c401079048181103090032613043d813580701e22142d000700341c903100d12103140b880800b81c4001180310320f01690081c4045800c0d50b00f400212249048050300603001407011a111440d2500b0042c240e104038400941031980302e03191800e80d08002c0da81118954410740400f02016003104a64606a02c3c6060607070700340490b400c003c5a07600340d00007101c3c03c1410000020f010080d1880004800054007000328545950b0540d4465481142402e080141d101d0300c41d0010302079007101c9510040d036410030711219000d481c0c02403001d14182ca00c06e2260f031241d43c0d0040032038403100c41e114080f400007003a41c1380c480a0510800300d80709105207800410801050000f0031203c0300000070b507081103a51102c1420f6883d6280c000c102d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 481602320 1250 481601070 481601093
    0x11a031b0616030c0b07021c080a061a0d0608032704060e0f040b160e060c0102160b010f05060708191b0807050c0102030319020a030f0501170c0609061204 68
    0x21142e004000c02e0000c1495402a083c0c5002440354000704e41e552203c00741603a0324503c2070201c00d0000c0400321004c02c2c00740315410454100300584400b0600d00d8903aa58000480040507080c100c2580219440e001c0343c240d0f004440082165201035440e10b43e8601c0e05c00301702c2d000030040c4408413611086036255910f80354400c2000340013032030b180804c5007003903104c42030455400c1d03405454410402000c030f1030912050302000c011001c140c9502d24012a42018442c2617080742c044404155824081909103104041e8622041c0340b203448008010b6051101c1c0004001ea01d400c100e006240a12035900020480001c6621001805d03120144070241e03020300f1034074110f050404030440881901020101300c1204081e102d541e06c900c1c05d0f030742900701e039100499a030f00007101d001d6035268110400703001240465000300b045038020300d030210314000714070510025561300f82e0100400e8080050090305443c01809006502d050440d080c1c1c5c54056140d000130000d000d02e550f481d44002c050008070302003000c002d852 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 481603570 1250 481602320 481602337
    0x2040806042603070305060117060a1404060f08100c030c08011202130237050301060c031107060c1202070e06040f020c01051006090f0e010303030e100608010e011a031b06 75
    0x690750b5a02c0d1844c0c000f07010304030a80f141c5e0301080c9646480e00340103810542092041c10b000c2c29100116203001c0803010710902c076880250300255604404151040d01d014000003030440003004000f40d1300070b503145100311420781940108051030300c00e400310400c2d401100f03613044640c10034030500808114000589800210252030f2003040c070008500700c030755041240710703c6c0105690705001f065812a40e800343ca44810840c0310780008800700b00510450b40510549403d49009103003c500d1600c20b01c54261a000d00340d00b00707802041c43d04000a04004500c007042c1300e071000900c05010598540340d44000c1441010700031074421600ca8202441111659054402a141120080c8507900b040490568200705034010034002402c00c540110760b08180c59082c0b400c8408800214816a2854508800070000010000060300400c060b80c02d2000c1c207030044c200903280c000000150545003c50356070855092103402544007c1c104140c00c0c49079404120100009401003128600104800010780c00784a44800d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 481604820 1250 481603570 481603643
    0x80d03020901030e0d030f0b031b040213090c0206060a1502070b0c10110414090106120b0a052e020d09050f041401120b010608092e060603140105040204080604 70
    0x117001541036041d00003040c50481e01030304022041054050544400c81e07100c03040e5811381048140d61480c140340d8014401413030283d060a800c1c0340c4401c001c200b501e03000d41d40e1400581c08078007031184506d0110010703802030409481c0001c4000292002a484151510922122240104210000c43c0c81401551880d0590410801418040314500103194110740180400807880825540c0c0760b0410b440302d02d041c1c030fa5944404604960491444000d0103880b07034080d800181c100000992900c52940e90407411b80707280484901842703405880040f05203900380c00d4003190b1000d11440503160f0131443c001c0944d0b00559460030107507284000706d000352008100101841900000019885103081e00d1810300b030748204110301b901c6e41c0c0d8034030441d040d071002c3c3c60044035508541d00b24014404040910400030052050b83d04070719a58444070001c558480c0d0003c1d0101c0c1d210b0510302e503884103100c00c0e1409410100c40c00c6080030b06024020b5074034035000b04024a40f004a001c100070042c554051030001214910 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 481606070 1250 481604820 481604833
    0x2509080304121103010506240910020307020f0901050d260c0304060e06031b07020a0b13030506060d0f17070804060e040b04060b0a0c023f0601080d03020901030e 71
    0x700c21401114010b0081e11003002e0046001c009280600401d03008200003002460f0291000f4410245c0c0301031000c2400c0311080030440043c25413191a43e8401281550300916141d00c10780c01803050942012880702c0c4161084001030003581c1e990002001181c0d040940341c450350608412000800741604c4101203013100110b40c807002498004010816942c0a546000404401406001d941d000c2564540c000c3e40d07030b483d0505804a2464040d020050000302641d01107640c405904000e640700b00c150030001c0c2903e61090040c032400700441c0307410000650700142d168089031600c0c1c20703010140400400766144200440401c40b604029641200c0c0c0021103181d1f110b5503044050310440c0050030840c000d500f4003800040074074082c81217104860407401e0071881c0040c19542101d20b110900c0c4220781c00022001c0d0011051800f2081401d01c0c44000300c1603640101d1042c00c464910340f40140010581c0c020f0f401401041d0f0046020195001c2604002d0380303c2c440800160050f1880041e2419a0300c50310 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 481607320 1250 481606070 481606079
    0x32a010905090f040215090a051002250801060803180f01111504110d02010e0906150301080303090c0904080a0c0f05010c09150207060512041407120215032509080304 73
    0x280c3d00ba000300d00c200c440b49507019200240d0b102c1ea000750700d04180e1052003c107080000c1e0421aa24603809116481920049502c907585224422240044441188500c0d00c0030300412034240724040c040d0403d000214200001756031420340e07040d50f591059000e03540216007170380319034001c4411062440c0385174140d03138006c6006151300005400407039080e15000800a0780e844ca5007881016440ca8640682d030711941c0142e00800d2101c503003c00b6000b29008402c4030b216507407030b0306080e002e540640041c001455813820107502c2136150224400f0000e224440290500c00010030310700468189241c20304101d42600c02c903042c004004c0d25460030260040d424500f49040d4260700c5189901581d82d11180300400c07010300c41342242da5600d03600414002c20310030003500303050fa07800c1114030f41d101e84146002a5100ca18221a80c00c01030341d0340c81440040900c2c0040811441c2105030004041c560703007a0340f4210320f030904a410290404c28401903007a15a210002440ea21075010103016182c944112540c0f250394 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 481608570 1250 481607320 481607341
    0x12020f1c1406070e0f22020a0518090601120905010b060d05100f060c0b180d080103050c0103050f01090509160f0e0c121b04090f020414032a01090509 66
    0x605003070340041c01180c0c0050115030040d40e12410b04200601800b0b80c0d91040e40c140403660540c4602248158800d184000c0610118001001880c49656560707072103078000d0306d8480464510341003551080c41c0c02d00811003142d9100c104600d8071099040081642001428294018060070100c41d0b00b007140000c404420700502d410030350158900f0405015031540e81d4070742c000014682e0040a0026200205a0010685500d00e0580050380b40604008022260310180d14100e00b0350041008183c03814010000d020060100c44440002800d080c051898440032041105805005069103030ba51030740401e22580c1e040121100030748858802c00034840e110300301203442c90400d00c606560a000780300052400c1c0745020560790002c600c41841c1da503680303882c4000c061851026081c3d0060b180c0034003001480070501c0c014052000510800160f0700c07410200c0e0347c00380f91406000d40d4000d83c04031201050052680180c6071041c01ea0074691404941e5030f0340101e03020304155020139881000c041c14411210740303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 481609820 1250 481608570 481608593
    0x20120030628240c12050a0905180403020f1615121e0c020a080a03050c0d020301060f0f11060114011413080d18030b0a0f0f05040c06020712020f1c 65
    0x40401c2c82ea0422110013201d9030031030420024400729902e40200000350044000d03000340902401c22102c1d65841c4e002180101600e14036000c0a03c030814144130605070180650000900020080d048424090140c900c500d040c070300c5050f451440041602d51a1031181c1120702111a4080090240d0b0101030070071801360b81c00d440100461445c2500a2003890300000c0d04400d002d40c40386a481c101251444181c000b404000c2000902000410100e10036054620085001e4009611040b81025061400170440303105840a0011f002545018400f03600002408504540320292402e01078000d500c0104d131780d0503284601a01d0703d00e01055210544004401c17440555440100b2140c520758000b40480f4860300728000084051011901031002c0782402d00401e902002030b0201050701c0c020b691006085031450640e01c4041681c03181170200304040120500014003580c4001c080e180d041c034280502c0103540c101d00901c51b092491015040c0d442d11404420701005003180c180341d00c0c40c642014410f820 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 481611070 1250 481609820 481609859
    0x2102030f040b01080d2114130309050d03080136050f0c0412060f0b120606150910110c0d061d070f090b040b0907050310050d0308070c140f0706020120030628 69
    0x41d02d064010846041c0f0000e4100400d0305982e3b07480d480d91900f07a03001c0b600748002c1c4c1c1c0b00c42c40080308000e0481c0c3e0810f002c442080c08000c81000109071405541c0407280038009132100c2d5408104100c20481a540b40410101e480e422100000381060340401e0040204a00050a82c20442e039240d00b100d840340c04078000344101020b442500c40d03038102800003c0644540c1424550202c101030200651070700c5050100c1d21403a02100316443c142203035000840071441e442040b00d81a0f282c5000604000300590781584640001008000103030808107002d15840b203900861540d10780d91144042155119004800c0030a0080c00084e00f6003803103080100365500c12103410010880e002000641410441341d4000341039050340e21340616031514041218600d005150513940100c8107041c441c11141d0520071004541d4011004025641c6042e001a0a488000e14071032406080d0001780700040c140d16084940c000740840314a100b4010905864515030700c4103032240002420070801056000d03014841e004d040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 481612320 1250 481611070 481611077
    0x30903082d10180204030206161104020d0608011a09010621020d0e0f1216111003060816080c0114040e0f180303090d2102030f040b01080d21141303 65
    0x104854242c40d0161700c514070009400040400c4401091900d42d1401c904d01d0f4400c00c00aa10a14098006000d90700100c804480c400d55500041095082c2480303001040501003d05010b941500d0000a0512205100719002d0107818111a0003926541c1104071008611042c210b448650f4003010304000d19100c8141c1d103052050a40c082803a00c40041c140036044502c18000d482e02c04000e06000c648518050111406d12801c00400b409503190761038140c0380c103050764000408602d06903001d450b004d4410120030300e0b800400c009009548020130045c4081c1c8081c2084a2000c420294003003043c8513039405070103142e0320b078802d010080d103031803040d1f9002e070326110810080107031200c0ca95038691100350307005402580703c080c500c0d80017400343c84a1545848054141460310a6170f940007401c0c0d07441101d941021105c0001008104074102c0159405011180c005045e03200c8031000c040d007070085200200401c0a18062030400240311904404401d014100c82880740d420100d111003107009040340d040380803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 481613570 1250 481612320 481612349
    0x1303020a120506150d020618040b0d110f01020312070224010b0d0b01110133030f06020309010207020d0f0c090213030623070809060106030903082d10 66
    0x40c481d008414403180d6422a020380402c0c1c45541c1c111081c00407410201e500130803039002d03083c0035a903414050922042003136284004401584c0c1040210b8007040541c80c032404000b82d00c10f0120390303401003000c1c0b00d0400b07842c0e210001b01000c005078514010000f80c8404c61440c90f01704441c0320344c0850740c05280c0c042c00703045807911080381065111542090144a4140c0c20900000750f121686801502240d10181840118000501d040a09451548813414045050010144074240e4140d4400700300d0100201c4266031a070071565a4a8081d1103803e002c4d00340c0d900840860b40107682036040360f50095000300700c13154800451610b59007007402c90b641038039640141000080c2c2c22030b042c000c458609801c1400c11500b00e0559540310010b2442c20442d00b1035081c03580e0b00a1004c40b425040702d004115070785a840d05440c101501d20724111050300120101410a0100d40020350420360305604a18581c103000d01c1021400842c2000d00d030b4140b13041c50824104014000c540c0010300c089429129140c0b00f075600c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 481614820 1250 481613570 481613579
    0x8030703030f11070201030b01090b0a020c031b030a0b0a061806091407020d1b050609030417010207120c110a030809010f0e031203180609070f05240d0b04021303020a 73
    0x200e5110740b81c0001d92400420040006611a911500448c44141040c00b00c003500c0d80000c0686410128012016901103040320805103000c0100d19004011285074003070400704000840d40722002068001c10f1501d00710040703082064541c10400281440d1644901003220401c06800900004c0c0724900a06107403000c492604a03a00341c0a0b48208056001481d411600d20401c0720108210452801400c000c0a01c1500040d810321009000f032085000031a01d40307040c0401e9811800103c2800e814580c81004504001030104150310043e08540c09d0051602140f41400a507c8001c20103207540300101110210402183d00090007c200c005c0c0e0750f690000c00e003ca0155001c01d405030703c25074198170030601c4482d48050074006642c003410740c1e02160440003460300450300d050380a542c0040c445c0c020000c00c4c400c00001403181c0c0b00070442100e1250500d159520004040c000030204209091400a104425501036800512075001d000d0001c660740c2e80b140d4541e05001c41603000c103c0c40f81c03291400028 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 481616070 1250 481614820 481614851
    0x92309060603041101140715050414060412030c050904020a080f06060903070909030525020312090d120311040b0904061502101802090412030e0f03180d0c0803070303 73
    0x81c400c0c1c1e03202c21014000103a140040d81c001081c46d201061003030003001070400040d40f81800f0340b00450710580c0402d80741070920704030407400300c00c0000050036407000341003101050007403041615010450900266403400700c07804a07110700c00c50080a0700903000051868071142c0c40b411582c4201414100c0c8141a2608020001c1d0b500c01c4c41d81e50b0f90b165009140034807030100d640e03000b81034052007410000e00c3c01d42c50100b12860900c2042c2540d01c0c0b004250030240c21b600341402042111103d840ea00d62400400000094000c45070a00c0a03100c0c03050310440e019910b000381d00c1098280501800349894035969024070070668450303060725001d1070800d80c0015800000c030ba40f01040700c032560050601c1d1a00e8003094801080d0300e040b4016520031400350003026847e12650540100e0040c3d08120140900782c2d0050301781c030421200040203034440c03000c486a411000c01a140c807060049202e005907010315001960b030a86447c0082c0000c2540d03800091409400401410744911a0300d0034000010b82080e200c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 481617320 1250 481616070 481616077
    0x111c0c021216050a0f03030b030307020108130c0806090706090806070807120609060e070201140603032b1104050108010e01030206030f0c120403090501031116120923090606 76
    0x101503406500002601012034018194022109080000d00b000584400307103040e01c05a81a20b1468000c0c80340401d043c0d00d401945d000c203600781d004501e408810b50000700070f0140103010f4000e00d01c0c41c1820400300b140100740305009003c05401c5a11508000031140c2c1c9500c1c180c8100d10201d42403040000f000c1d5000314a2134440c3c1401d88410039590b403002c0301138680b4070a42c44034000c0c0f00c0d614403011a4844903407145d5005822611400c010354684a24041d00b150384624212118603032080030001190780000888035420001d203003c3d44041d180d400264407142072290700c00465418076038420500c1c040d260281c41250b41c03d07030380c0440c541d91300c0300c0c20340003140c0a0101940107170003000080c030782980d081006904003007202c0e199498105100403410ba01f8a040e902200000d0181000300301c19a0702d07001c1d410020001c00d5000c0c0c1341481032442c801c000d10203043e00420760f100350710318904017034010141100202144112900342155028404100203403070b40d41c2c0c82c4503440312000328800c0e04064056 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 481618570 1250 481617320 481617341
    0x60c030c020c0d0b0705030606071506030209090118060b120109210801080d0f050702060a03060e01050604050d02040b040b060309030409150506070f0c2303060c1204110a0306111c 79
    0x8044170740741c0d120704880e0b60384011301c032941103e420001c10001601040051031030300d416020000e0164190300c10080d0020011b80010340c140e0400b000c002c82c1400403540c029405a1003100081c100e032000d00407400001501c182c840095181420600a2001c016069411141c44800e61200264240c50664120702c0a014010b840c2d03019403e0f0b04181c0380181c3c0499403800490408a04001c460350008115601c0421010006512010b040000c2d070300105205014100031681380e42054140700c0490150742c403c0c000a841941c8909048400d42c489a1095003901c90191103260380303282c200c0f05136a4a901920881a265141c16214000782d1a484d0442040c4c840013001e01345450910380300d410a118100005550f03c3c69000c0c80043c110004240a056040b007114204d010140a1010581000742c02003011b000c1820070007610b05042124450150301c594010303000e408610313070200030500e540741603040103105a1078181c0d86a800841580900159900804d4824244d80c0c00780004050b40c2c0c140700c1c13 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 481619820 1250 481618570 481618583
    0x70b1806070c020d0c12141b0103020906040905180c0d080d020a030b0a0f06020111040302090c0c0a05010504060b0f030c060f09060903070b0702030d030501210f060c030c020c0d 78
    0x4680070901c1541050005070000381038904c64030094030340700c01c21840c03030340b010b4800b1203911700050421400001e40038161755840042c00c0c102c00310150704842c544000c070f2074504041d400101000d041e40d40205817000f40064110800103803800125100c191600c9449140c2c05203d10070781030380c2e03526102e5004040f050707125441d58100203060701003401a400502ca120141a10781c003034256241c4841c0ba07018020310071020404051840c10704082d084500c15101e080c8031100c208802d0026844140e90039410400340040749a44245640740c49040c800503140080aa5092009120a104007504641c00c00d0104450014160711014101036542c480c040314150041c00610803140d228180750042d01c0b000b00b024003454a0305454800280c14040f81d900301c10b04d245008540081541810485150200118242000954100444c401400c100e40c0c00340400581c0988603c010401f407070301c00b141515840030080c8252403031140c0180c0a003100b482550700620600c0b207107100a00d1b1001b50394061941007803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 481621070 1250 481619820 481619833
    0x1a010b0d0903030906112109030f07170f18040c0c030302211024020c04090609080c0a0b1303090915080a03090501030605010e0f010f030b0307030602070b18 69
    0x205200c0241030715000903814103544da0040c130301203940c03809051038840d81c0c0e06070142c1d1120240700307404805c0d441100c44581e01610f1410031000c0080001260a400c540382d0b00282c54480d9850400ca9401700800f90408075940865200c20002c5044044c04865003a051852040c031202c50a000840d481e90316080c0c00a1040c0011502103030080d4001e00304d911010240b41c000c607a0756100e0045190003030f2038081140000505c100603403020a4910f0340761442801015040c0d49020b88002d58904412901034881d82ea5107445108000044d4001e0254030362000385213495002412100e610340c41c0d003503410f4405000940c0000d100c0d02d00454000c41190345034943c030800038140051200100140101524111b90104d40411a00d5040240a01c0c0078440d03510658010f04001c00101503030165131000d41030048400e81c45546513034010314075949010038609801030150307521088000d00204580036405020751800482480b40a4004150710381c016840c03119541c84860107005003819003550101c075500700300c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 481622320 1250 481621070 481621087
    0x62a010f1b03050c090406270504050307141c0302120105010905061213140f1b1003020306010e060a02010f1503050304031e05010527060c1902150a091a010b 69
    0x290300407031300310031010592424181500e000c00e003159010707002400300e40c44031500c40b6031801c1221540c032000300d40a40d040c000c1d0b081a0740c46694034068898020001e00c019080b51101040410100004402102d41c001c115944041c0c058001c2d030041e00101d01c1c2c41c85034400410309500070f454104c2240c1c0f01503c02440e1289071004d0491008ac0075200988001d214460100030070700076089910070250040c041c00103d04020201c1d4501a1101c0855103448018800c581301595000481c03101c001d032906025a0381c2e41d41000499080b0152041994000c402140320705105130b05500a190034030681408000c81c0c58405090b80e0304084900c401040d540c42000300744001824041c4c01c000802141414003005280c69440909442c3c04907031f1110b60451b108184400e100f4449503100226803101c3c094803140c18034100b00c0b034580c4103500903024409101c05402180314400c202d41c014001050807902032500b40702040b10042c0001480c01d0b80c911102c000c07012441c2c0310b2201d4850490f400c1020f800c0c07611150 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 481623570 1250 481622320 481622327
    0x30301062a0b090609010627060b18090717040308150a0602010c1d0a030201140403061a010909020a020d030b01050909010308090f1801030605070c0b070306170304030b011202062a010f1b 82
    0x6848c111404540c9403c030025010703184601070003038001c641280301d000c007501d002440b00302c084c000e00b48002c122081450304003000d0216000f0390003c0c1c04d0f2511072040d41d2444980d084aa8189034944d03006140e0440010300c03146d0651140354025003a41e0350b122000e201100181410700c2d05818568400100001000190701822104824000d40100e883c00c0030b50325100c070000c90700c4003880a014903001c42501012581e0001c0504064880d5040441c2080d20000000790744587d10300c043c8003803503694450b0381c201c0c0c1c1c041d10039180511001000154290384900d040400c0341c1000c5200c5010f004440841541850200c01d00030150010810322440e0b03030b1850b02c0e643c010300800740034402804552200c03034010400340c1445500c10307002d90700c002c14001d14001d85007084101145460000b90006d10083c8009404440d00b01d0448000101d18503400800e400010014840c60400042d16595201d5a41d400e15405003d28100045030008000c00c1c1e926400303d0058410089a00c2c100505009081200901 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 481624820 1250 481623570 481623629
    0x12081014090403020f06092b1b0c09020d1b050f120a110720040509031e0d090b0f0601092d03020307060512060f03030301062a0b0906090106 62
    0x784100caa40c5000c009a0340d0400205032002247c1e030b00324513502c0024130100c603001400700165128080000c102244001d1001001040000080881049071014808112094030103000748032411960b444451409400521002d408803000210a8001c00d070080e01850070b50b40e00440108440d40380c5a83c0380d40e030100303094004002018450340c600011407010040e00280510b14490382d042c810b12510481d264109844500000c1c0c4a00c0c142000c12040003400300981c1e02002049100c080c1d12000203494510b01d015a20400c002140340c2440300092150768145103010704c4c800c8451200c203440701c40044460850382d019044010200f04d1000090b0030303030004117410100b09440700301042c03901e9600107810520a503024800103100814480121580490055001481140d020740340d5081d90f40880d07100c0c04140308040a0001704003c001e4031000b0703d00d200301c4084186514100001f5645000100c2440541f840601845818001a40900c05105507000d03200001030903c0c0c1540c038454409850341c1c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 481626070 1250 481624820 481624823
    0xe0609100f0603020a030e210a12050a0c080a09110f03160602061506040e061903080a0201050f0a0e1509030c1009050c0117040f021c120810140904 65
    0x300114001401886491014014050303d41c1c1c05a41c45992403801402d40e560464103d04503000456800b10302c181c50000010782005100b18652107184d212000d0f85c22107210302e05100c0d0141031104001c034030840e580c417981c018107260712025041e441e03100f0710404450700e8500c010702200150f9002c60880c138140c1715481001c03100070100c48600071100c0582800041030740c880300146c1d0000051042d020f048006049070f241e400d070750301030601c2c0c41d06140040c1d90b203001c0c041c24003c0007580c064651242c5040915000756406c00403050740c46120f9000203008040854000e0f40b40c4080c40701145c0b50301502d000c0c04500c0901080107001040c1c2803805200b480302e000d041c54000303220030021001405002d20040129402269000032200c4c50303418030700d0034041c13003504090400284192414034002c809a1043e0041d42148450402d49440d202143c1e010540d000302e00e0b8164040c650070f1003004402c14107104420b4036a0346055094403842002c41c140d481500030810311103a00d0b0f00a15003410070b00320403130340b15 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 481627320 1250 481626070 481626091
    0x3050d0f080a18021905030d0c0c1509030c15141c0506040b0a03030305040203060a0c091e09020d1a1f050708120103080a03050f190e150127060e0609 66
    0xb804541d00244105d00c20741208030320850405170400c030624007440107010740703242c03824254100021591080490203440c001e0705a52101c2c800e100317002c3c6104107407e42c0619070011256000d582c5503100700741c01015110207400000c442a1b015500c2d0810303102a03800445640e0f4a00e0740700401001c0000241100915080c3c000c0d40e148204071851341c07504440300c02580251400546130038180141410400002c0c08180041c0c145159419001e50149000e81110f402140f00484d8241070401800001c03025444049038a0022604004c000c031240e100000e110345030100400d00f141c0403020721029074050014803d4000940c103821164034040c0000f4000c2500c5225401d140002c584000d58a03804281c009494000001c1101e5641c183c2510800d034008800303403c02c00051420440034030b20b2245681a400010f0f4407500c0032490800100002d20070744005d00d98010707184da168003080360340050a055070120b03585a8403051004902c2845240e0548415500d00d540568401c0e06102080b00040d1000c04a07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 481628570 1250 481627320 481627361
    0xe010507030c03230c1522150203070e0907020706021f0f0c021e0c090c0c0321150603010b0f070f060203010305101a01080a0c031e0603050d0f080a 65
    0x1d9035141904400c004506100103070b02e1300000d440991030418002c417082a0201e110080c00f100f1a00898466001042d510556020344150710f0a4402c05040408488d807031030020049c040340b5030300583c0030305140344292480c292990740c112080f65a540c42d44110000741c0c0060b001c8010b4400076017400513036880944000700d00001002031100c1100c841900000060300846d200e0000000c41c04240a200702d20380004158603500c520004100340000f90040c407021500003a5002241c6052065460442d4011103124102000324540c1c1107120048907a8600091161080f40440c5400c81c10750b4165916405942d0601d011044520b08961101800341e4401811200300000921140025400395200d480541000d4030005040b00a882002a0032044003503a45005416039034041c1d0b00300e81c42000b081c004031711100c2c59802603000704500c00300445040000045201c03040590b812400c1200d201c2e5084a001c01d508040466002c4508802c3c2c4000900210208010021680101501e00f8090f00c610300c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 481629820 1250 481628570 481628597
    0x3050306031e07050a0e1501050702010c02061306020c030102270105070203120409182f1c0b09030a1e090905071106010f0602030a05070f0506100f05010e010507030c03 74
    0x149082200882c466502520b0700348110704041181c1c000400350351146500a082010041581d010740050190410030702049130010340e803051f01101d1041c0e8000d00096624142c040d8005000e0080d401800094032502c1814001410f0520803142600702c0e450740c40503d649407040f0040d1801004071018100709081c400ca102613030b0140f202d401e145a07084076155542d85442c01d0a030030b41d0b0030811004082440c8800703200208071500319101c4481d18044c0105c0600c17a038848040f61003155481c0d00c51b0000d91000e07400c03022000d005208039035079001d210905926070f0703404481070b076034031455402100261035002264028052400c1c0c41c0855069414902403d6031122010b02c101d40d800c450440c0018401d01c1d06000042c0d0521034a405401741c0c10400b80c00e00d00f843c402959900c140e42c5e506003001800038000f81400042c00c0b07012007041d485000c0ea00c05003402801100c10900720f02071500840504007000900d5070040d514400280d5041e101c41d800e11403551000d66400741c2c50768082e020f00c840341d00c1006 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 481631070 1250 481629820 481629853
    0xf0203150108030408010b0406140d0f05121b0303130308070207030b0a2906041403011d0c0108280908090409080a11071404021b1b01080c03040f0305030603 69
    0x180608050401991201c1c900700b0384031b080d42d04840c0703810b01030b91922000784101c2c50b40107441d140c22401035074070407507040c49880c00d480c110010a80103400707405158601483c0c0c0010000402e4084000350342d60f10516400714000e904d9101c01d40ea442000100c000c420310020740a00c0e000c0d0b0b0301409900681700501d80e00d81381c8003407400044580203400c80e070303907082075880c400000400c20417905552044090b640a03030f00442ca41e88558015030040400c845106021030380c09400c41407820740c81008014a90112002050395840c1c8441c49c02d001c01c0d07903000001c0084085c00c0b0901d90804081011803802521480d05100501000c0700039614200b01700700750030700d94031680640354401e881411003507952a0440d0006042070380400a04545810003a0b003005202c211503030700020501c048500581e039640102000c100c0d40540c1202e58004e0181a005802c50240c00b451520440002e0f00c0360201580c800c40344c0c500c0307484102d600520307442e1020030110100e44a030025642c000c0025040b0707100c108a0720340c0035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 481632320 1250 481631070 481631113
    0xe0402011b06151d04030905040f093503041e02011e0f26010b18030d0801050f0904150c021e07091802030307031b06051501110d05070f0203 62
    0x81004000028003005044c5800e9801d03c1303294020000b4140038107050358000c0a109107071007080d1041c0d850360764007104400b0a80c488011290b119402d1071059468242c5602d4200c850306034a608408014a81020b15112004403403103079912542d0300a515052001e941d40b11050020143d0401c503014200420105004100c0c90801005444002c20308003902c40003481c90039084009604c100c00b80d0000140715122140c20390540300c03e843c41c59103804940d81d1aa4003200052040d80d0b040c03007044080350f180f1f40c000c00c00390f050701d01c180c81c3d0480d41c07040c6005010148a081d640101080206070031404ac151039a403220214881d0b500c16100c1030700981d01c20240460134000300f0442904070300b0040284821a10030202e27600c0314440b0035003800070b094000949a000c0ca050241c28400e010029400f416605200c103420103510100401c61400c16031404070182001200f13aa0116101884180c00d01000040c220b107083c40d290303590380c0303490815a10210304565442e8200d07050721468064002820240e042c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 481633570 1250 481632320 481632341
    0xd150b040b0c0f0f070303050304051203070815040501050109170f07140f03070b0a0c080922152102030705090a02030403021e060f09430e0402011b06 66
    0x2500c55484890107410261000f00e10011603018045800f100035011403032004072a010704003d0349940d82c5041407414000c01c40d00c1c026440b400041005843d0350444031450094844800002000c0c05285c02c4c8001c81e8000c2c041c85000c0b03122020308000710942d044444c3c035103550010640d049090860300d20392500c68282c02c040c0c00440e01400c106c0050807d0788650b117034210221f0041c1551450030340c0000061003a941050108410080c06e2018002010203c903030240e006411440c0b0540181007205000401600500c13183c2d003810070034040242214200c4040c2e03418a01030350310ba1188400c503030084018244003283c05000311140052140d403410f42c05841245400c030b015a40345054540282000e581d1134071502e20707052030794403500c0c40c14001030f1080e0f0018aa088040d0b5030340300c140346945031120103c1c280090004000d103480c103440c41c5903111440d800c03100d800840000c8052240c450409040c0c0108902400b04400040140d846002e04040340c0c00083e88054901ea116200e2800756140c0161 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 481634820 1250 481633570 481633589
    0x120c030c06010b1b030f040303050903070312081006020102030721090f0c052439100f0605030316030e12010b270609040c050a060305061002120d150b04 67
    0x5450132858511489100a040c0b0107018620708100d04949403c28003c43c0005420400045406155510104500400f0b5034100000f02da8142d000d41c401080100e089500209071100700c1c01c0010410300500a9901455580d1959030000c0260000f26900843c5004040c158944902003070000c20413040d0346588081c0030380c2c02070b0030b0700d4100f005209003000b04002030303003460304c90501120108002c00c059400358088034440c0221807450900020039007060100000079204503614820306c0fa4070014124031030100010f0f06008042e0143ca002040310354610400ba0150402c20000814021078800400a54400c0c2082c20074600b03003d0111f4955803081d001200300360b5660382d0034885441e00b59540d090310044958818034602101d0001c020b03405000d4603550081c2d204001050411142c0025070025190150280b10314940d04c1c08020017814098030300b6030041040d43d1914046601c0030070b4840d6078450401031945041c019400190040c40d030035800600d0060341110118402001e04010001010044d5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 481636070 1250 481634820 481634827
    0x110312040923040201020718090c09090c060f050a050f12090f010501080102071110021011090f030a030c0b070509030703030509030d030e060106120209030102040f0608090708120c030c06010b 84
    0xd0008145038400c1002d41c18014031820480180e9001030b6204c141c540c500d00025200340e04101700005800c0c4950004d100081c07a13180486e402c1c80980c81003170500c0c0130341c040300f6034580e40300e1041d07441a0701c134011880050300c20005224050f02842c000c0c014803110030b48083ca02507240003440e41c210310a41d52991150042007040d01d810300c090190340e000d001084000c41c581040b554402d0b24500c515181d0724080c01303040c01300c40600c6000303000030120801058414869032035070300c440c140240d00c180101d9100d0300b144444500142400610702d4506a0b0503190000c0c0420240c88224519200511203400c019040050520a031000d1094000551003501d55030385031403040e0109030800c803801442d84101460310218444800c400103074607044540c5800c01001c20300700d4448510207841400003840d095800002e00040c030a10f82c064040072140c0940c1d81c03000a40b12121416140c01d001e1152580560000c2c014203140c0c1a01801426995118021203160107020004581407802c00d03030003020b5020740403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 481637320 1250 481636070 481636091
    0x312070506090d0e121609200c0a03030e190605010e0105030d0c021c06020c0703060c05030c072306090601140a030503041802040b04030f030212070b041103120409 72
    0x7081115001441c0c40058580e02d9040c01c8014800d2004044503485401ca03d07812485440080c03005e0b05018800c1c0c42001c1c002038982d560307200501010580da0782007001040d5001e0f0141c1c1034000741c64501450300003600380d600407920301b1009400c08a00140c082d0285103406d0111341180310341a1460b501c9900e000c06c0a624000b01c0d420740c458140d00040c080d401032090011a0f0750f100d0001d031117180e41210500802d1200881e42440e000c00c585000b001d0070310012f0b018a0074900024402c0c00c40307100388814448030703944140864842c0410b4402441143c400c0c0850f2000900700c00744869a0303e050307180e4a1740030560b0b17030070189400402d132000b406030b0300100d0051208680c1c0310080801d00d501502c4c0b401107a4650b5882683e240718510642d82c101d00c180405001c4690a40c048500409403e815142c071035407079081c91060790310701030300803405032140c62101159030508805036070310b19410813800303440d46e980d50b2180389100e03a00c1103403203905000e10411842c100c8540c0002d400a070507621800248502c41 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 481638570 1250 481637320 481637323
    0x31204030905010f020c1201060b040f031203090201081303030207080319050108060601051b0c101101060e040c030b07111b010e0a082a0d0b04064703120705 69
    0xd40010f810414134000e03d040081d00044c01c40c02006041c0c0f1506921508035650500420721034100070900d0000050000303030305242c5610304c2d058034040e020a01c5150a541015402c13603980001c0240403039124800a140c42c4105900c441c01980681009441e141d0310f680e070701511780d008441d07a401d0010b5440360303030141c100580304490141c140380e0000d10803400c00c140043c05030301a1906454210003400071044035404144841203d030a400f601c1104012075a01c00505100c0100d01da1455075032810030005124842c002d0b02c58012900400003030001c41c11500c1340e10070304000600c0302007402140d207000c140c18181048040c8018100c017480b00c5a00101c8070005010100c000f4510b44030b08021036050205907400319550100c088000203418810340281c9500109503001003809900540d04508142805020140e051003a44a000c0070490000c1da41384c0b00c0700e02c40e1040400e041d082c0700b03a00e1072464140000d484580094429000741074030620840041d1421040081002c49104049240401c0060 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 481639820 1250 481638570 481638587
    0x406020c06060315150d0c09020301210c05040b0303090d061a09041a04170a050a26010302101205421017090a03020c03010605090c070501020c03120403 67
    0x44001c0e0128070445085501c502c02e01170b22003404034000450210481e9038041c664030010760f0007613408000960b140724400c0250800d11132114100303004200d032a06c480505444900599119004100160511060100038011032a00a07018401000300002d04c1d95541d4800f400144215404200b501d000d01c010044100c5c0c2068135400b80200c40e0a000008480d84102c0d80d07412010784500c1c0980d60303242440c00c80495240c00302006d0113030016613034600c0766200d40280282c0003551034001010624018098102001103080f081c07031403200c03006000600d00b001d402040f03030b2014985920301070448000d8404940082e1005600e845a07041c4901c3e0202c40010100308891007040903110440241401c0b8181d182c504c6841c600c146180003031f1a00d0070703020301c0d10244141089070350b805842ca000c1c520f041d62400e10700025805031244000c001c00a02d014003401e4103586000d000755100d505c41f91141002070300000411161550280801401d00404101524501040020f08182400d290401410703114 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 481641070 1250 481639820 481639831
    0x41e0303110a080301091503080a03060e010b0c1b0a051003091205040f060c0f0f14060f01210c0308070b0106080c0f07080a121a090a060f121a0406020c06 68
    0x100b0505441d00800c00e40c1c000d40c0c0c1140c290f1180415030300600101c0c00140310880e04020000301e0003243c16204107600d64007aa0650320328807140c44061b601c40707400d23515038021108800d00d40d40c001d81c641c5a80400c10507000c9400c0c813015060f2001c241c0c03201d002420403040c1c00800310000707503120220302c10310401d8030340300402c064607007400d910382800c000da00042c01046002e24828001c80707410000c10000000449500c103504202d08005400c444c1c985220402c4030300e403890069200b418003140035503080d503002c14100c80c80070f0f0f0300d14010840c0404030046296a508161450030140c0000000b081c9600c004104403031060102400390760508802400546003c4c0a8519805060241d110300503040000c464441ea08500175076151580104200c0b00c41103680604119203040c040420486500e4581585445000f110a000590b4641d6801d0301120014410f1000400000d841000741d080701030030083c4924002d0912080341e00b0211a00d10b194002039504841150340052940603004003803100d5074100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 481642320 1250 481641070 481641073
    0x709090c0b030709121109010b03270325050f030301052803030e0607060c0807020c040e0606010c08310605160212030c060c1209061003080f041e030311 67
    0x5041c081d8006140000502603080102c41001402080c4444060071511b00c410080c004c4180e903850364030544160301f0994041c020800c003030103005680a0740b203e01c1c048207681c8000950400d03c1501e403107000c107102c03910b600c5c0d550f44030122000e020070018040715580540e654001d60f40c84d450f007414040300150342000401e1030084070350541c4210741d07140315501c212905881c140c0c40d04804200010b44900c03a2000061030246410003c00c0c0d12500400310522a0015400381e03200c40c40c00e0414001902c0c42003d901d04250400000034280c0d41c09030240e0440079003d08101420800001034440542c10361038a11580400217880c403003403000b042a188805001d00349085410f0105413007840d0784a0500100003446803207182c0d603c040e4a0402c00030f0340c1d9440d080d90111101820300c10610000c6d40c2c441003104d007540c0c4400d0b002507802ea02c002400c5006000c40d8583e51301443c6541c441004070b402403030201008e00000c10002074803222a03e2a18020040440342ea2855455464041e0404001303030302d030781c00300d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 481643570 1250 481642320 481642327
    0x905040f03180608310b060901092a1b0b010e01120b07030c030e0307080403020a05040912050702190b09040f050c040b0c010e0304060c05060609150609120709090c0b 73
    0x400d40c4244c01d9a0070803061964801c201c040300a0404034020000076504048409190001c1409900400c00d40511000e480d00300310399032610011000d13141a043d498504140d401c21000310002e440e194000c02105e180f401c0b62202d031088681e0300203c141a50b080d036220000c50014450340341103410007401001c03080c04c581110041c603980d9140600f03002701a0011306aa075414440003d0090704480d44056604054030741c0c840c500d00d0a249250024041a80502c1c003407080030986040070b105604400b50040032084132203032000d001316806c0d807200d6412608070b8070003205000521040310b000d901078100000103a417a080d01c44288000c50344200c820344001410b003c1400006444181100c2c00d80d0b00d10010282d0342c1c41040710650160001080004452000086c0080da0380e500c00d034aa0980391040080c0c0d135040e290741040007000101502c00d44048151004a61194500701c00102021880901b513201460039492105d820401e166001c4855251034a25810400001080342d0b0f01400b88181290306 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 481644820 1250 481643570 481643579
    0x80f0c01180306180203030a091404020906120414030a0305040302060f0714070c0e1602070b18060d0f110a09080619050702030f0a1d0603040f0602130905040f0318 72
    0x6030348064440607215603560069071322080500741030000e0154002d000c480e07940c0e0540d01c00411036001446100c50031094000c03010320b2407615000703d801800e0010405410300c0d0f00c0039030560b400000640100c0d880c502100c2d001000c5081803000c3c000684194400040071326050034060f0601d00020520307403460204d501000031581d0044da840001403005401140c0300c458500c1c01200440d100d8100d010b200107102e0801c400c40345c3c614480706102100c1d5081d40e5140340d9966070400d540c055081c0480c40d410740c2da58070007502d080136005002480317581c03580418410748140c110f8088880c01201e0000601d80001c40c1e00043c2c2d00180c1c600002d28001008021a01d8025240104403075100e400710140d43e20b039000706188a01c01c109941c412048180358039940e90300080068110b4102803c4040d4201d58107803031000b41d180580c07d580c0720725003008111600000c80d9940f0300080d031005140b020b0700005040040342128182c4201d505c03452103074801150b90321007818007800e41005c240d0044801e58400f00b0600 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 481646070 1250 481644820 481644857
    0x11190c020a0b0a030905030408010504020a08161203030b090f01060305131109150a0e040b07171503030c010617012a1d0d05010f0b190308090d0c080f0c01 68
    0x1011030b0380359110203444190880e4200d001e030100440141c154800401c4c0840d00b5001948102e000744c5c403c40f801854640d07144a0140c54a200034049102400e5014041010003030340c519401c0500c0c401d1a0006598a12600142150f4419101600200c1c2010018050700ea01842040e820860012091124000756500d101030024403016041c002c60141000c150143d803201c480455010000b811000b016440f001e29141201003101c1c00d49100810b6000b20b100307036000b0b400a01100480a0b00c01c01296508807000003100494103030346030140b10400481060300002c1c49400083c1c03031141c009842403051410020b081d120302c68a004903030301c008402040c0260501e44144403113080c0e42010720094284a18070700000c0c0004440d02c1e00030003100c88a00c10400194000b03948020f814008000c50303020201031241c291001c1000d07400704c10701d0310401c2c001f141c540005000681e400401c440e42c7c0c12202d9441d620296490762099510f0703880030103040701c161401d2014481078942840c0510189203070185a2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 481647320 1250 481646070 481646089
    0x305180a05150a2705010e0f041803020114042a1a0c0c03070f170a061a01170c03010501030f0e0102070c2306090909250f140306042411190c02 63
    0x10305010550b07d03103641c5921a00003190f00c66600070b004110010820403d2041c107031102d801100194039103000c030760040c882070041900840e00700480f40c0e0b405120068240c4801c10b10309000b540f0f00d044450024894010207281c0080880502d01c03151590101d0340110301e02070052904904c02d8103c101c00b40420603481000c03d0849510a01c41c1402c80c45a0138894204000004050211410301440c40c0705000c104900c00d04d40c01c0d00380d840b00c80038207000c12801e039003800644240e80c00c040208010000741d0700c650000d00207290090400030701b0114500c00b82d401c80c0c0c00003604946590614400b00010044c12201580b8005d50810052008080f140001e40311310078804414485d00c000d1010030203801041000384451002e000e010000300c130600183d007190003600c2c81076240c628421030012a019001031150782069401400801558482e0f41e9034002c1a0203401442200300c1c0100107004a0f1002806008071440f079804031196942035050204ca505040d020f024000e0144003504400141c8984c00c01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 481648570 1250 481647320 481647329
    0x1b0103020c03030609060a03060903030b09060f1f110a0b06100206151e040906140907080a0803090c130c090509011508070e04020403060204210305180a05150a27 71
    0x3504003691606c002a400703612607000540524a892611010550544d00c051002c501c100e481780070f16074800f0100001d45800e0310714aa0451260038103490001301c0715003240c01a0406003804902c078401c5812803450469003041c1a9400115030081c0b203c1030800c418402c8404055101a068601e0b140c080041c8400101509030300901c400c5070b20364164145500103c8460000400920010809081800240c042c4404000c400e804500c04102c0c0d01c100010500c044441030b9001d494840380503282c000f00c40d00020303c06102406002050041c0d9600c004080c031154040b260006044201ca1034024400c540c47d400150044000c407005000c460316480c039511720380c0360ba460501030990ba01e0f001290004040c0a51980050020902204000560700680103840a81540541c0f1180000204004000700c80d40640401c0007044020098034038000d5090114401a041441265960010400d60f540600540c0b08030308011408070801d6034040403514211502482c2d00341d003020194040d011641c200c0c0724 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 481649820 1250 481648570 481648579
    0xf390f2106060b0c1c03142802030a091101080108102031141905092d040305120c0f070b0609070c03080a020904060816031a0408041401110f1b0103020c030306 70
    0xb01231441c1d0040c64510901c03810103a03000c0d916801e1890303100000d00550030b4200c681d41b0b51141c2c060030079481101002e040710746d03840080141d410801c40e000c005045650329040080c0d041d4090048000e0014001d08940d01203098140110381c0002103d980c0c1c1d050500340c0202c04080c03c0b130821a05403604d000000650301114a4051070b21024102e0b070b003c142030b80c0a40d030801945010402c01011540d8204d04040468001c4100441c035144551262a0704880c01804104240032045840c02c888005c1a0f10447d80d4203c286040407a50344425541c000d030b4412a002040d19041004a00b8a600c0d2940c20545905002e298036100d65006401d1140044c0350812507580440c07080300740d642d140c100c400103040e080241c41c4801c1624a00f1081200f260000380d40060030300d07291000c51000015068819908403440609085c1418003103000c400091489a040000480c0c642d03d12180c28003841a6074003c4000601c450300408644000080c0c0080f00241450320500074092042c4020003180d0744990200e4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 481651070 1250 481649820 481649851
    0x4050114070c0e18070f050a081203071b0b0114100302030f04020405060415120c0519180f0f0608060a090f0f390f2106060b0c1c0314 59
    0x82841880c1c82d51011139040c51241ea000054905401c421030070a4030415070b540d102c1d0f03540300c80030903903103e0000034081d902030420000154480d1103000768145001e2018130f8500c038101e854403200342101e002c1e0820600c1444002030001d203454840413441c00302541d42025400c503d00102c1e15081401c001300040d000b2911100010303e950340b2544080c01c1c0c642d40d03d04100381f2a441d5040c070209118206411a1904410000410503151980049415041d00d4000005481c1003219141e100304400321041111a12501d03220300a948138003503d09958840c0f01c00003100c42c0382209540c60801c0241401c0c1d0100e18000694001c5000700324008035198108421b048104030a02d040c00c006144a180350320780c070700c2018183e500b107031203290014402d0148130700192405482d003131080b840094034490340341c40c01b1440d1400070301c0070f000c10001c1203510300070740780043d41c2e9590b0200c0100c0781d0f1005403010700b41e4000656485450405100502c00036510f8035041040300400410000704070b0b03000e00803010107500d80 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 481652320 1250 481651070 481651081
    0x2906030601031e0c020f07090608030304060c050d1b091e03200325060215040b0603160605070501140c07080705010e0d0309020f180a1a1504050114070c0e 68
    0x3025400c0c4048400c3e00200028840c44000945074806260760402c507004401000a00c41101d00890342560408005580345840b260b9403040140416051381e824010213003c0e41c0d10b44081c0d849803800260b05004075180c00d001e00f56000302508901e8005500308082101e2190111035000d0b00c010659074001c0203142845c0c0b10801c0314098086d02420144c0c1842070b20848141c8103040880c80c100ea680f12000817a201c0c0c0c42e250300f030741c0303c01854180300c0c0d1030100a0005404280758888050300b091010b000d0710440f031542a40c203010720845800c00310200704001442410801c00b442240b6000c07022692009031424901c0c90302d44103104001011f40740400209080003405401c0d07008201c0a45950300b120068102c0d0076020b4080c00d0b48032401c2c2d1040f10000041c1c651420a1200114655402b25110005545d00011007005114400240e01d5a03601080109580e49130400d2113800801c941852a480301d00e0000014504421010f5015a8200902296001515900007001a02c00d4281c04080581c4c8a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 481653570 1250 481652320 481652351
    0x1401141002013207030903020a020105030a09020d1b08072904240f020a0c0603050c0f03090304150f0c020d03050c060f150a0e040809030a0b0703290603060103 70
    0x8201003c154000d21000c042c80c0c84100f8801c00c00460040c1000c880990f4030300b0b100354100c95035600d000d0056001030f043e480042d0310840041d41e000e404000006005a402d4000c280110001c501c1140c03907600c00d0184c004a440065021401055990006c10105050501220720000e281c0d640b01c0140b03043d81045103d81c084142a140500428100c05800c0401000e4030720704440340f0110b0801017211000f0b6151054400306400121a400c1252045050f281400072002440c00604c0d81d071001300140410307107c40740c50200030360150884a0003580c44608258164001d00003030020703034081c041c04118030390000ba004040e8000b581d40454100310b05015908040c0c4051041d42d0b01d07245203009e410100a002069000414000c0e0710380c50010000c080c0000500c01f4540c01e0340540150039500070b000130002000300000b00244070b00501904d52801c901e9a90b085030344e00680e201c0000ca501d5110808066011622080d0b504940c50100c11084201c080400c90034030001e8002410180c40b0200b841c07032007c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 481654676 1106 481653570 481653581
    0x3010e040209060301020c0d0215010e01060212180a06020d030c05030c071502070609030804170a0509120111030a0614040b09012303011e140114100201 67
    0x845800b0018a510000c0c0310a0b03166400304407d541e1110103210000c1004029001401101c645090810356401c058204401c503415440041101c00e80c000340003403000102d80310f59a61541130081e02c200c1c6000074021213401000910b00080c00990010f4040002c010329541040790107418213045072248070940d203860b4842410701c2003001141040c6480b4a4825803250018134240b069547c8105444843c0401d80c00324585a0800051100610072603400c4403004501910b0545030040150090240c4c0903054001c1000c810656040e0301c0940c0140b04610800c1c3c40b45031641713400c041c6640903005600444201040945820106041c00d000f080c030304001c001e110040070307800e12105140d180410800b2400d001c04a10a01c150b907242882200035400c1c030000d604030044800c1e5000d00a03a0408083c6194445507000100215800f030040c4140c0c1e224200d0345402c003040050303000c138050706 = true := by decide +kernel

theorem cover : BRFrame.Cov 481474820 481654676 := by
  have h0 := BRFrame.cov_init 481474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 481474820 ≤ n) (h2 : n < 481654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
