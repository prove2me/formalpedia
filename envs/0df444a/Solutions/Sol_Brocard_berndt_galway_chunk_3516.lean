-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3516
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:53:19.298947+00:00
-- url     : https://prove2.me/submissions/208fdc02-63c0-4db0-9aad-c779c0d4b8e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 632194244 ≤ n < 632374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 632195494 1250 632194244 632194273
    0xa030b091b19090908040e070c12020705060301170708061504060e04031d0102030c010908070b0606040518071404030302060906180d0e060c060f0403120915020a1103210603 76
    0x2586000303c40c4240d0b542e0440508019079082203030040c025031030010040c1d140a60000342040d2910404851420300c40288050050000807803105441000306024110703801c001c445841d100f101c1072074403810301c110704c000a40e9403010b024084c021580300b24480c50066000050205031a100d900004951040404020100e50310107440c0c00107000400950401204c9100102d246010700c100c400e00d254a0203d440f002c0005a8004103803284c400d401711000750303071050104400342c000c604c00c241d00241d500c00d040c61404078218155038005400d040007211030710041844901500103400480143e84020103002c4221000c10240e42d0052003d441c55141d1281c20f4840c0d616004034290107824002c2000010b8141d5483e03100380c804041d910400c403101d51030310100c2c51054a4043d2415400b04d460a01e551090355064051150b80307a4103c05401224402280e10310020f5000038038840801c03440000030008548140028501e000d07420401c2411a41190101d404107000584040c1c408c0d40065411040e84 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 632196744 1250 632195494 632195539
    0x30a090f0e06060711221a1503100803030c07060e07031509032303010302122418070b191d01030c0c050102120a0e0d0903020f0a030b091b 61
    0x300b065528a0f00c901c010302e0010603440481070901d0b40410a043c0000385d0500b820070603801403000880a1041c40c9000719007101d0710342504400383d003041c0001c0d10031083d120040c00440d0025051a04041841c0c0d882d107085045070820780d104218904000b4007001840107a0040c0c03280070380164003900740c0c0761642e03882d4241c0d03004015001b03d01940b82d003003280505004505003140f0008a42c0c04902c405807141e030ba10740c0b030b500c02d000c100c1c0300360322404010403408400169907070304d00242c1d0482000c1410882c1409100c503001040055010b50001410380301c080240502c100915105007103503114100c01000d2040c84003104a44000c002310310100c2d20301c50210300c160028280703082c00c00085409102008030703486510007102426942c000901c10600c00780c2c8400c0c40d407181c148040104036015451000c1e03629528400003900000710348100a10161070006c0d1401c0c0c135084000c00c1c0810341690b9660310b40ca84001201c0802c0507410603103008034440c1c0048020380d60114116a0105800c1360400c805004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 632197994 1250 632196744 632196751
    0x61008041704080304030804060807020d05091c0618030e181909240515090402010f1803060603050c0109080d030f02070c0305010b13020301141507020a08030a090f0e 73
    0xd100c0c11900e2265116101c4200e8001e4800c00d025207581c4ca40f03a081c4229036034024030611000510410008070a540301059051801000307035602e62601d041c01d02009030303200400b2110305201c40c000404000241181c45890844007114100c20707101465810701800b0500c00210840c0502020f40020000501d0340c22015480320314200d030313400d0340c0e01c1c04552030004100c0420000d18080b0011181c00c4038250050015100c1d502e0941c083c07000d42d86940b4200c603400c0300540303413030b400035000c0d4003040040d8090320040d82ca480e06440c02e4081035100c01444540c4100c1c0394402d8400c103540c1c03d8148140002403080001c2d410b028284891050318100107140e480b50301903c0503042607501c00d6402d2101420340c044801017a00b04420146041e143d0500a0080070f0f801200361207030940300500c8200300c0750344c02564101c580d0030382c1009000c482d06d004e000600481059640c8004001c10040005a65010712031028052400c020740c0c541100320009401a1140c0e01b180029074014601000415261a240780c1e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 632199244 1250 632197994 632198003
    0x9010309060e030a020325080a05030403020111040b09130203071b0f0c09060e13030f3e16121202100f0c0201060f0f0303200a030305060906100804 65
    0x160100c550a0a10091407a0240c0140310b00000401030030340d50340000500308007407841d185210f40807000480440c4511031884010240e650a029440800703004002450788503001e80004980c1d04030001c815a0036600681000845000c040340d0b100a504060600d80c14000c030107401140b65040c480000f802d0442c0c42e000008403107019004e1007007089058442400c0d21035101010801c080d0311b428084001c4e240394090f00b00c0000f900c0d00010303070b144041200681e1281d0103840384218160300301002c84801e4010008090f5010711220f500c60ba50042d500d103002d481ca0038860510b40740e00000b0f40981080000c05c0c240e140104e12143c240800c00320030380c002c51266802600200303642c503402420390a00c02800e103400d0301c481c507120302c80d001003038250403018007000c1c1176000300f110b29100c0d400011214a10301070400e14036150310062002900074078240340c80c103290354010124000f1840c4014540a1100700480c00207440704140070043c01d0101d80c060f00803508a40981c02c120304007500a00055000700041c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 632200494 1250 632199244 632199251
    0x2030618070909050a020a110a02090c16170309160e13021503180f03072307080f07051503190911040e06041208010605040b07020406050a18060e060303090103 70
    0x1186180645014402040f9842c0c2c00d00051409890442c02504007282c1300d000704404010358001c40d00701180405d1005d500520b51026034803800c1801c0a15040301501488088420b10b60402080c0c00404c5800100e104140c0c0e0b40d5207240505a40303082c2901444640d080403d6114103102e104c2400c2100390340300884004900100100d0300024215120034100c10080e50300c00800d200000180307000140c18040304c1d40c111802d0361034200c6140e540e0311500b0f2000c1c0512100c9054000410304105001c10200007020499481c161500c1d4214140341a0b020b4640c000c0e0310011003040503040c036180341400750003e20030784c50035032500c0c8104008124404d1810000140c1c0c0b182c51108000540000040c14540500700f0003c804031080030a43d1044140c0d015200d100e03c002540309514483c007c03a9043e42d86030359416082502e003050000e01ea8000800c00c983c4682c960b50089401d48604114a000f880d41e0540312029180205400b82218100e8201e6021100e40700b0801c11a42c80001c11506034800a01c0e000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 632201744 1250 632200494 632200501
    0xc120c0303081f1203140a050a030e030d0e0d0e041a011b06110408060a05070f23031003060f0911011b080301120c06090e0402120c130e0c0402030618 66
    0x41c0c2c034021a07036200c1500442018010440d01d101000c00f0120b5417203911000552407080581090b82d004001c3d40000140c800c02048104611035000103400214040440f0b003040c0605854a050324210a900b16070740e48100007030545154440818020101c0540c0c0c100007800301d030501100361000c1015000d040c84005007007198950b6640036107203402c0340c000c0300410411a017101351103400e0b40a44a000301034400c00c004a09455a507100715401501d0ba51222488907220340d1040d01c0170703011004013400a054035241805804022401144140c00c0d440101c0b600703a080d1314040e0b007100c1a800000c0441d030310b402c4c8034900080c085543c0002c41182401c0c0144402d46110855160642007039009105003008000001c00642014856880c1c5100340b04410941391075100441d050b041a00c106200f06000e40089000340c1400b24000c00045000001d60321195441c80104c0c2800d45503400c0d0f81c88140e600c0c0030401c100a020b0141360f800407005c40f419851170400701d00048540c44c9001c5481c034504440c0c2d001c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 632202994 1250 632201744 632201761
    0x270403030e0a12050c1e07140619030c08070309050c0402180a0b130b0c03070611210a0614030a061d060c25080715150803070c120c030308 61
    0x828a04030380c00800d10705203803e00400285260006260307081e944c03113002c3c0700080b958008900c004581001800034042c680c0341c076107188400d000040000e600f280c010000308810b8001201c180c207004c8100c2c1ca010400c1c07107d410740204103000050140082507d00310300800010400715900b80092000c64026844080d07400b504911420868a0264403000c0c1e454005030103c440303006400340c009100808061555503220000c0e0b00c5c03052800480103500104101000141e030755210105143c60622800c0c00c0110f1010501502d0010780516050302c6035420401c117102c00903009503000b6010707110300450355040c48808203542d0149540b00409441e1144a0902c04419030740110035003a42c40e00490b01c06041c04240f44441364040c8003184a840c10180340101d404404040c9092940d9200070407a291042d40d80701d543e103920300310348170b0142a80c407801140194440c1c0d86580000d0464400656912081450311400040700c5511441020550780e01c0c200228980d910760034112500760900c6415036070303a01031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 632204244 1250 632202994 632203003
    0x3020a0608060612070e040f1a0402210411040509100e0d0c02090603120a0804060b01090b03010b03150405011707050a0305071e0e0412030b01020105061f0201060305030309010209270403030e 84
    0x360347c004d450800550b070450003541003446100c00e030707218031802d42d80000b051105903c140b40010082080e0714002d01c4066102081c00da5110307014219103000450200300060a64105803000007a43d4441407040803052401c1c8074480058010000400c130441c00e1190180c4100ca19201c080e10800c0706900240041c0c6040c0020b5410900030452180d6039140c00e4000380c0440c0c41520103941035031030b00c0206405540115a0131045e103e50203d07190070341c0e00c2c001400c40d003540020b001141c064003003c3e420107540c03100e000c0d141c0078000f41c0900c501480c855550f404e182c4040ca80c8803600c2822501c60400c0820340c0403a00307a00392140503c106004150818004984407090303407150201034544400c000c14085604680000c0000c1d55805108645258004900b61402500c050741d0000c1145c2074014651306011031800400c00c2ca0001244540d0740b500d466056401c01c81e09600c00c2c1e5000a0040714900d40022080303200c54002181e143e07007020032a0760560b40400204014185030780c0d818110110701d030800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 632205494 1250 632204244 632204267
    0x906050a2d0e1c02150103030e060c01090506070824090403080c0c16050406060f12180203120403060b121005041a09010e011a06070602030618090703020a060806061207 74
    0x4049980c0c90b126000750f9103c844800807074100501a00314412208040030a41034104c9415644414001c044841000000e503c8140c41180740d65903500340b64000b031010701c10544200d1450b1103480700392900a100e03030141c1000014203100c106034007460709282d9442c1000c081d003040e09480c0c601c941e030740c80317a031822000c1c42040e0152040341b003000101200039400d030115000303440c0305036801d1100c01c0d51040180c9400d001110101d0104600c03072171a10314920341743c5c4100c10101241091320318804ac50380211b810109010305845218400207410710070700550340035440c20342c0d0087d10034001c90425640802d48030040c0403c070503001a1203c000c0ba0500001524851882c3c0000c9440105070401e0071003103009140c04a1084101e5003444064410410000c1240e01c022001408071441d0202c079580300002980010406540596914032296000d01781009051080c403445005218450540c01040f0308800c40754003910801c0180400c00c04a0388412040e9840c0940d11a03030303c4141d44866070261880801d11303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 632206744 1250 632205494 632205521
    0x20103230a0c030203040506150a0b0a0c0c081906110d0507020303040302060f13020d050102040b0c070303080105060f0f0901090305100b0a1208030f190f0906050a2d 73
    0x2808404031805450421409004108030801c904520190141c00341c1c04115809840c6821601c00140c516880d00c00043ca404402000d004500d81ca030030324200c2ca50003104a00c00080c540b0710f090020051900b00400103814100f0040c84040d0040103000b00e895a565401801c9540303904543d00d030144640241d60001d03000d030300d0500076403a205500a40d00d0700119010b400501c81c5101061580e550390300750a000d21a00c0169602c00001602849162211000126a2598200320004541c0c0b40f002c054684074100300090f01c40781d441d500f4020000b5806030000ea10a80d400c03c069210040a64119854001d003404080d4668007072800584c2c00ea0840d03880a482400b44040e00c000840c140da00c1032140701002c03503d4640719a200c040010303d454070f03404010010a41000850144141216a80e074001d00d500709074a500400b50f200310007510202d26100401c41c5c3c5a9000508000d041c0c02540c0d4001c401e05000c024000f0304144001c240868a1004c0301c00c40805070105059005c59003100000d00e810 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 632207994 1250 632206744 632206781
    0x127080a050f1c2a120b010e09070c02130605010f0c05190606090e03040305281203090309050402091f030603060908031e040506063d08060409030516020103 69
    0x2031181c103000341016450f4680e0210031407a55084e05146035031070315503032101c55075010840c00c0455040d500425120300814140000140030036825505d251034148901c056580d2800415030380d2050203410100c2c8005882880d050003070900c00c03668844122040c01d121440c3c400c076000d100c1e007085420701c40714003000d4110078070100c00d400c184162074108a0465144c15810072011510880e020303240e00440c00000c0c03641c0c02510202c20801030040782000c94850302e03808130720910b0700c0e03603102031241200560501c0402e0300e50f8460790900d500180808010300307040d0750a6242ca0b02c6100000d0304416020114540003a6a9401607512440303503110300040d56105000304032010340381c103202c40b05420440e80788040383c03a803a009540208111108a00a55008005001c152144000c0108010a5400b407803200c21480c1804141e1001d40c0a044480550010811050005c0b03074000600c500030040016009506052040d00083d50001c1222820921001080080421440120060b00c0780250a5000041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 632209244 1250 632207994 632208037
    0x60108040f1e02030d020a03050f0702060f0a021005180d11010b03160e0618010905040f0f0b0a0b061c0b03100606080a051e07050c0c10020127080a050f 67
    0x100d400c0301a0710b40c000c40071140b0581550b04101da95490f4100d0050006005000c803000150050003d00002440148114140605c50201c03001c6a0030000c0c001d030040e1700841c0c1c01c2d04510403d01c50746801005050360444000e800354009581c4551420705202005005001e5010010f429484203005040050940718000058034440c0b040c034156025180c0000c040401044451603c41c2c50000848101c50300b41040c0e030f103130032911001050002e1098035503900502c0700e000000c41000c4420300003441401d9000b00e5003401c0710b0230401c882542c403196015500800035810040d01008103440c80020b01400454490540004a82820380402420313240c00e041c010089130131600104451311403c5001d4041255958040b15941c00c4881c00701c04607141c0101e00c001c00d160318414801403008110ba0400c4443d62054940401c1011200c1c4031b603040140d540d003041000400300b50400b8075400c01c1e9440403807070192258581c00c000388141c810817000c1c00000104241d80700c0c88942540c8188516801d0000c0080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 632210494 1250 632209244 632209283
    0x6030507150809060727090f02032205030d021e030a0e060c090109050d06090f15241203021608070608010b0a0206010e06180a090623060108040f 64
    0x112100c18020660060001e94542c02c0050b0003032250529a5525440b90180030b841840002410315142101b80705c100089440442c500550740d10407260180160f5925040b1800f61705003034000b8a182ea645010786c01080403030701c000169031040034a600f0042c0d4800d04141c4540c0142014086110501c002000300691540d0690000c205002d01c5001e80703c0e2981d40d44000100d034402c0301c036000d01141c0588030911a50406e207508803100c51103250000343c0701c185501c5014104030354000842d0291200814031000b81000e000d402c5001c42c40080d0003035040350854a841040314140034284482c2c1802404c682454070030020145900100c0d00c988aa85d074131108442d031101554000d1101158100c000040c1e611981000c4400c1411154041c140030b03420490304074910380001d0921540402c400e07000d128a501d01c0c511003030207030084220010f00c450051404a0941c0d07403800c03901c50070510410340e07284e84401200c0019802902440c0920340ba584901d0000030351550141c0141410b02d51262044104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 632211744 1250 632210494 632210519
    0x1e160b0c22051509130f1d1005060109030506041b0b0c07150e060702090603070506030709030507050108012312010e0114010b0c06072f0604020910060509040216060e031308010203040c0e07020106030507 89
    0x14804050305011a034ad9400c010754281ca01031000501e5580501e00080102d022030020780b280b481003c5181e0100c0799244403103140e41c3c204000a00703c03600a40410400d640100288040114240c209442c4058203080050200c0c050520064003c81c0c0c0c80c3c0020307296650130f04c5140040d11000f85000d4803401d15400003001d480990000325054440c907880401c15602424503181281d4603500080e115403400c20700310f200170004e8504c01d60030421a0011090140d404c1c003c2600c034000500c0002034400c0c00c07136043ca0070040184e0240f801480200004101ea42d4081086907020b00306041c24403030304190030070780040d258219007a49000143c00c040c511032190082600c9000d01d008030368440b081c5d15103a000884040e02c5203d00000714034200007424503820300341c01910150030800c0350240c1d00341640d20307420190f0355181c0b044565074000050001c1240c102101c0b002c090a2400000c509508d030030755611481002a0043c2200c40e9441000140c5107032007504a0405503a0000503503510940c0c944810414 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 632212994 1250 632211744 632211763
    0x30f110306040c030b0c0306061603180b0703090e040804170c1804061a100e010507120305010618140121111e160b0c22051509130f1d 59
    0x1400340d180c0100706c3d100c2880341641c1c02580000c2c034140ca07003601d95903881c410780142c0c20110240440403240d0900c0b0311040384088018858482e07100d90300c030319516005010158039005119804840028000484c202c40c080e102035520010954a810601c0100a441d1421403210140d00080c50b61001d0383d003110b0f00b007c0f240590f2040b00e0901242219006914103c0b240c03480d0250401840000d12aa2034070502610720a080103050040c50710020b602d400141110007038044001c43d44407001041815403086103107003d4030b504249900c0207410102001c041031300e074000140c100204031841061800c0040025466074a1654081000c04905034078003134a904402c4070940c078010791254070740c40312001d070048070401c00100c02c1c510806020303a6180c00361301c64090096408040c062141c40c00d0044400c90515020a0180e4030744482031611080090360a41141700d24002e080c28414076025403a20a004550180c6c032402c080303400b13140f00300000000c0400c0c6880c0720601c1040c66515114090102c0c46201 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 632214244 1250 632212994 632213003
    0x2070318060528230f0f0405010905030d0206070806010302040512100609021c0e01090203030310291b10090605040b15060a0f1b120f0305060a030f110306040c03 71
    0x10f90402ca00001c00c05200b81000305004100e40198803031452401c00c101d10f0010202c80602401c00640610419140d0084604942e01344030014040c41a0b40c0c000c03203c2c00003010110003c044200720070300020744030203003c0c000405100706640403841c0360b8043d4040c0c81c040c100141880180300c5205170055590804144420401442c00c000850901094000c940c00505c0c0040044003004541c045103004000744094109030355039460020340142c1c0c0910082d0700948090194501a5060400c2c1c5203d58004281070080c00400300346600e0303440440c805407450f540034584002e05040c0c1070f1080e1410a80319083c000c03102441c11000600700251a44064011401001c0b0b018265550400e02e050300041c5c4585150302c09814450f14075210700c030341c40300c0d8414121460030b204250302c41c3c9800d142d0f1050b1140c0846120107081000d181055001003140c4058070b19103018407590604102086090007030340070213484481401c02a2003803201030115150040e5000c2c00f19400391070079050141e0705818a000868 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 632215494 1250 632214244 632214277
    0xa03080702030f1c090b010e01060207060f3c020f070f0e01050603130506041103060703060e0114060c0d03020405100302071e2f180c0409020703180605 67
    0x390100d1000040c0e52801e1808440b461504507a24081c0c6035040401306203a4080e078540394050300003101c070403055000b402070604204131541840c601030300b0800e141d00b029040100e48240041c4182e070010b4291121310b483c0d1401f40100e083c981168511a82c14004104210086008044c40075400a10b00c0350030f40c1c1c00303000c0c0e17a181d41c1c60b541d20a182e49124441d00c0c5003001d1800c0144603c3c42c01c0001190001562903071031724480606d5681d02d05009003254180c502c034445041e984440d04007405400d030f20815610b41040118105070b440d40303c0d0101130044ea20a004a0a00d61800e0386404040b00d0401c0c006804607441d151034005c000300a54454000d95000c0d901620304030390708601034000c0d03032031040d4404440c2ea28078204400d0040c88108504c820354620b05100d0b04002c01c89143c903141c2004000c416004400c100c4003100780920700c003041d102c040b40c000d200800c0250401401043d141950803200c00541d6805590400703c0385484040e0201d0058518a4030014070150080010141e880d0301d01c4152 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 632216744 1250 632215494 632215501
    0x30b19051005040b0406030c09030f0c0501080a0b0d08031803040e060111070614070201030204050607030801050103050603070e060603061f08090106090614100516032307230a02090403020a0308 85
    0x21109070096128003044c03500148001e01c106802a040340c840b1601c0c0d850600041d55684d11255001400050196001c081c080010320465030300c084000d0b4441400b030020b00c103880c070b00b50205080b2402000090101c070f60100c04540035202025a4070100c18841c0100c9403241e8492600381d54240081e281140407031043c9003110309481000c1405070448405031901080c0074607907030383e00762583c3c44154102d04040c2c0c00c010109c3d5030740d1140701801d200c900940c0c40c0035580d81403074000f60072174001400c0039200c1c0e4414101004449694072034240d00103429224147c807030301e83d0008900d03231400b0702c140c885100b140e694200340c1c4594040d07846032254000360000e12100b40c0da40c03101c1080300c0250184481c4000740c074111140b41e003802c8455042004451401a21705880368014010f4148043d10850010398a44800b00740021155040031811081880c440c0c81c1035943d0352680919003040e021160f00500f40703983d110b0150f80500420060f241c02805010302d81c500b80c42d0094580d0f01d00e071801c502141c40c0c040030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 632217994 1250 632216744 632216747
    0x140c06180c1806010512010e190e030a0c140a050d0e010905180702150a0c11031602190b0d021207030c020606221a090903070b16030b190510 62
    0x54050805040408414a850303202120318000820513030500204100002040b80c00101d054024407082c6403000e06c40c144840024114603000718018002410032045000884000c0212450802c036400e01d03455101e140e1820601c40040b1680d000d034103020b129609400c3c0078011428442c0851143d66000019000800543d103110700d034041d10341c000c10400b604540742c0468912a60704495180100c0300110022001c4102010381201d040d640b890312400c40c40e5407240c0050b84201d0b11100c020145013043c0d0340e101d285c802c403402800064442d40c10000101b86055034030901001800c031042c0002d9589049080c0070001c2e5000d1707800c021050310180c0001c0e910b2417092251800780302e00e41c0e0140030707152110420042044508d030081280c1c03140c004407807030750f000f814400c1030514107075411070041603001801003001042c0300134200c50554000b000300e0800a440915455800990044140b81c00e281c4450114010111080c003142c01c4200c080052071040081070790740041b100c00b244c0c1b090051f15200030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 632219244 1250 632217994 632218003
    0x405100305090c010c0203100e070602240c07080706060303050703090b1204124b0804080d090b070c06050c04080a06050403020a15150f1410140c0618 66
    0x1e19042c140c118000721111584a81690b80f0f5031030006046410043d8020002030407181c0481d0302c2100380d804580c04000554061001400303040401c0c84031050a03c0c520002e054605005040150003680080c0d00b0003000000025260ba4603009035080104980320702d00984281e001035070540c04114038200006004140c03c0465070041021450358500c0d40b10340d641c12040480f900071140a10a42c09030802c03442140c0006102017102403544040d07401400c0c602d40c280aa01034904038032090080410749021900001c11030340040d8000c1d59150380340880000a00140003415000308504041320a1101055000190040c554090b00d000c01c140e80324194000c0c1e0900c2144207410b56604401140004500680e001c66813160090041c4c030700c6241c590f615020420700c140c0c007411000360394500c542210040301c01404040e040601900c103101e410000d04200c90713952801180d01c240c0340b40100c40005486405801308a000b251100c81d00ea400f8030308516201d6900315185800d103450400c60035044040000d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 632220494 1250 632219244 632219251
    0x2012903030d1d1002180f1f0c080408010c0923090a09020a061805030d0909050901060e15011b0308130f0209190506030c010807120608070603020405100305 69
    0x10300552610111001040c0681100c0481680501038400d294075610001d2240e61403014a4003c01a071303481420075280344501002a4850040f482c3d29032107141a00c0701c0340601d07001d156141c190081108291710450300d80381021002030008202060009d012641508488600c0700c0c56121401950380318902d00c2440b002c518944940c00d4001d0310341540e241480c860329500402c604c800801d4006080d004580c20320310f29030103840041e110f20080400044035400c075502920003100a01074003080d07a00020208801c4d809204071944c0c3e90070203d21400401d40c800750081107880e020320414075140604e013005c64503007030900b0b000c540208081070360070407290820216241c0c562104451a1600c841e150744885c04e02070210703080302a03044000c0240e41c07002210b91140003018095011921203581c400c0903204040c205500a0703214403040300c0d207a07805c03950013503201c0c9a500c0c2076031124600031821809000103a1242e0014002c1d0607020070456030540041c0182d813000d9036a440f542c21800b030f0440440304120b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 632221744 1250 632220494 632220499
    0xb18060c041e050409050c130b090109180c03030806120102030f16050f030c13050609030a03050306030c060c0307120f0c0204110d0219091215110415020129 69
    0x410040c0615100c1902c804015503203007021448103a10740d008102110040701058450381c0c070528a000b00c0c0c1ca0649480c0900204580080c0318403110350b80807654640c0103000d09241d56881d0311036035004948440754410340907008004a034504d6564180984411004d8038224050390071050008803901c014000c4a000e003100015401c01c60792010340401c202c004003e201001c0101c02c2000412184900004e54010502d0307031001c0741d0312010301c002c00300045180d5100d180140014001900d45d40e070081601102d89030181011652503031840c00084c1420b480244a0f98040e4000c030b001c6030780440010140100701c0c42100203422185a042c000d550044c510100d50000402c412582303801810250414489569840461401c121111225000f40c3e005600e841d28079140b02c442c00028168130000d010020302e58172100512070541a2122018424010f501c080c078940c5a1800e9540c0c4501101194000c1c4180c11003400c9141119100074083c0003403904480761003458030274084228910316449003900030700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 632222994 1250 632221744 632221747
    0xf03030d05090c060909182d1018020f0a050307030312141320060a0e19050a030b0c040306021908090d050a030b130c1101110309060106140702040204030b18060c 71
    0x8041d03450b810b000c801c20324101f481c011913601d6180c5403854005041c0d40800d440300f0000440b400280140390101c00740380344001e641005040500401c0c2e000001d010240c0651f822155842404042114414a58401c40e05032084d61800824160302070f01c1c10304c02900e40c1c0c205200d10240398401c40c200840950300d091101560300d0b9880001010b030000a03000540d440320b40d440b202c0f40c040000b005500401000c0d804103001c0c40380d950541c80c00a50300d501c0d8044102e8039205041c1003001049800d0200e000003803c90340d445010802020030310040e58010750340204103550390302c0c101070302c958550000c06100d40820583d0000c0b485148000c01d12820041c0241d80311814640f101c40c080b0003414160344059084030000d03959542c0f00c4c660380542d800504403070706c807040c0a015001016085850071407020294060034014486901d602040c854115401440d003118074107190172b40742c03403107200c0c07950029403282c0700080c00020041c0c08142c90384181c0c9549003580e10031001562150b2038213421580c0d445402130 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 632224244 1250 632222994 632223001
    0xa09030e031b0112090611090907080108030307050a0201060b0403060b030715020a080306041b08011401080903070212150a1407080603070306050709080f01020c1e07140f03030d05090c060909 84
    0x4211030b1030140fa00000c101094174005900d0320411240162041b0201d86000a180f10580c100411a05c0c0c109400d03243c40180d81d890101010703201c2c000a41030304100a000924403806030301c00d42246000c0c02441c46825605d55592400200800111204500a0145410000b03003941e14544c4802d17a40c5032500940030703016056840304103e50000b00707003591055865044d0240144242c0304d003d100c0400d40c1301c3e0461135040050424100b0304084c82941005004010402302c0721000c800d1b91011981034501004500345024010b0a0050072038082003a0940c280412690f0b00c4103402c15215412445100361141d20b56010440c0d9010003100c82541551001a040000a0981e4080d81d4420070b0380c074080c1402610780411900308086408404c00170b81d000709125a081c0c205100c10920400402c40400e14400c81d951030b81d854111a10560100c0340d0380c8002d02c04242c4410070030705aa20002070680b599000504d403540c0c000c100540c0e0b1031009214600d000e907400d040800c03c4443e0150010494180c03640e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 632225494 1250 632224244 632224247
    0x14100509010c0c0909051e1605090403110f1506010507020603270f030c0d050901020d1b0807051c08090a1712130b0a020301180f060e0a09030e031b01 66
    0x4180b031408a07410780000e0000564042d00b4031860348007620482c0540860f80b00300700c010501a910b003207050301c01e4000c07032100ca0865000d08254801c07070b40300f651940e0b06036549040a03100900640c00443e07036030091142c1038038248008144140519521034041c03246445038401112580519900290861400c02c081480e98003045c406001d07145821490601104180044508104c00000e29030f9032540007190041d9000000d2041c9686074070300349032a41c1020010301c0000e40c2d9007140318180c0b091002c0104c0d400b0480c400024010042a007101c8010780e10006403501a5131f94151032291100d400c804400400c516201c0e03a01a80a810420300410381e03044c2d1606c501401141c250001c10301884104040182800c180b5145445aa0003003a0a1002c03500c9083c03a15402c2c0c0300a184003051072041005002103801e0481e03120500000c12800140001d02025480027804e4640045c2401c55050b002c110519040d0740003880f0365440f030340e1070403030421549042c1660b9074082020034013034000c050715200065 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 632226744 1250 632225494 632225507
    0xf060305070e010c06090620130504020a140a020c0d030504031101020f1002090d170406021e071a1204150b010e030c28090203040201081303021509010e060f011410050901 75
    0x1801f9000000d610200000c94407003030b070210010804000c00100c1d40f142103402d400d402600070841030381d0561900f41c1c407850050042410284c00010101c008c03507419030340c600c05c00a5000e5808040c006861044080c28050b11581061004880440c0744c225032103c9540b0106524200441110040a20040030307801c510181d00003d04581c0c210040003a035070003141007140e0810707185001000280e9610b040080081c100020802c00f82c44a0400d40d62000b50b4040000c0d0140c101c420042e0464940c072804590b0461a200315004038403075000c82130903c010300000c6488400545240d4008120201c40311005454400c84043d0099040d00148070441d10344c200402180301200d500c9040e1502210141c001d42c800200070b41140e40801d81c003104000445d40c004d4203140e04200c500f080304400a40e6076030b000350303520340ca060b01c9142d0740c0c244800710710700010940008042100030b6080e21000d14110300d41903850942440f407032a06000e4140c5004250920949a002c1c40c016551903900d00009000191000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 632227994 1250 632226744 632226761
    0x601051002030f1b01050c0412260c01061e030f14010209150c0106050109150f11151005010f02070e06010c1707020f040506130504080c06010f060305070e010c06 71
    0x1940410011440741c040400d004000012000c8030186013645030292960071510000c00322640e080e000c01c02804298460780007190034592044805e8016a5003d030b0115660002030302480880501095407518052b064100c3c00030b030381c562210341d64800e094020003004424644006003601c8070100304003000c00c003c030003d03001f41841c0d2000980341031401320102e11400b00929941c0406000801e40c1c0c0352524080c022540100000d00e400c0440c0343c102881025801c003007600001c00e00035070b03030805070f0958001c400344101c560b00c0c4404d80303944c019002407944081c142120104420b040c500d0700403901358041c5041102103a090781c01008810708000c1a80a0303484040c10440c1800f84881e00c1000050120091603078580490064075196001841400000320711011080e10850034001004a5a26944a02c0e0207181100d5404600c58503181010078140c0302d8924661154010000080b03011041001801c04070b4500f590100b00f640e43c1c0000460f559586000040e00051600103410082032694000720f84 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 632229244 1250 632227994 632227997
    0xb04020d05150405070605070c0501050706090c0f0e1803070f0f022e02010c080c0717030106020604140102040f060807020102270a081203060105130909230d0206010510 74
    0x9081561101ca103400015110100041a003804020401070184000402409582001803c06400343d540e620381d40e47c01d014290401c0008030b01341040c001d19810a0110941124408070100d0b240c010043304801031303000306141007145001294155081c0c4001c1c1ca801d46800c0003543c1048090340d035a584003003011400783c0305500003440300b034056654000040e1117079025034684d07005024507005101103e66044808001e6924110108000c41d400140380ea034807400c1410a40e5a8440c149460b4510000003050b08444400100000c14107375000190310b03001d01d01070030b00c80d65400c1040804a00342d01c00e60054501c80d605410342044510b01032210550010310f5800050305003114084041c07026800780140848860300d8000c0c42d89582441e21a22002c1d1003030b50044c0c901c160040c4c00715040f0384800362902c2d04201000540001104410740031202401003217005000004090400c4190441000c01c4a8002e082007041c03448802000252a0184d403110b40103416075a180100300204040c2100384c410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 632230494 1250 632229244 632229259
    0x40507090e0a050115050306090103060507020f010e060f1b040308181201140703090b0f250306090f05090c0f0a050d150c050c030d0c030f060e090c0405070c0b0402 72
    0x7403603041003001ca611450b140c0b01e0008496242845201180e00703414113130018000108184000350701c0e10300c40141929000040840e5079220310700101d28280018003d15101d510f07001d20000b40c2c51001c1000350142a070711100080c0c3e9100d1000050415401040da161021001c0000b0400200312401030704810710310051001d00c1000038404940b240841b440301490a075500c407003c8402000740c1150076044001d07454204a00c043c40c4e03072a0304051501800b41c484400306000050303070b0754110020011280604210310740c8140c06540d4094040c02c00ca001d40c1ca21035080548044146810f8418944500d80c0400101070814034081401454500d160302150000c0f401840450345803914810445514458100c049078120001d20b000d0844064100c034108001007040b180d107902c90000b00b554460402d4403000901c55411840580040012641c01a989401c1c420001041030203d00d80e148114450f2043c0c600c0500c0d110100002c50384100c0e02100441c00051000020802100000c1c6c3c5c0584041c02c0305 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 632231744 1250 632230494 632230499
    0x50303090c0103020a120b01140c0109020907020c011d030f01060e070305010519140d050303090c040f140402060a09080d0f021b01050421050f16060807050f03221203270204050709 79
    0x9e2120352040c04a03031100ea4407810103400714284018029032140103031001d0111039000ca000280b04050300e10001c4801c40d074040a50500755824000301000c503020b1002000480c1d945d4606034105c2404450200100740307003100005860401c1b01c9850800843d64010000305814545460258111446880d0f00900103140385c50008000f00b00940c0030304031810091041015460410095806501c14608098100030341000c40c0e191407400d16030003aa0440d0040c0d11341e8050300c005c0304c1c40002ea0748040700a00c07621035821540b0350172070b60300d40c40e190350b030750035a290110324006080e0325207255900d441c0051800c0204004210f42c0d4420044003007001d01400000403030503180d1524088003012051070b2600841803045e2000c0d15038103400e00601d094140b02c0c14920b0211000340060090300745042044000000040c00e000d1100c2c0341c0c1407607542107210740340300d490315013007040c0300d1a20168140b0100e880c1050711084541110142c1e9201d107048010382043e00596400d002c084c2c5800f52841041c0450820007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 632232994 1250 632231744 632231777
    0xa080304081c33050a030605091504060605090a021207180b0d050a27020904030e043e030606090409080301120c1502061311030703050303090c0103020a120b01 70
    0x4a0400f03010b119071080400a4a0040c4518020002e070b440030980c800c40010400c0d40c407000240012640c0001e0001025079034060903505080c88200b1100d8014449000c00c020440c4951101d0291001a5401c983c2075a0300c508010880c440d00d1320000002101200041d005842a5010040c08000004040031581e8903100b108090f00403202d40302c589505d030b030100043c20809200e00303403c2044503800d1040e201d2503400080303615096488042d0003a440c01c0009828507009005d042b00c01b410280081000c0421881d600d1b423405880300540811903d66614150b4105000315000302c04d02000d07140754607507101c110400041e940448442a0001d4440d45000d0105903284065402400d4124801d041c507400d13232070300c2031040072a604810755103e0540700324400c4030760020b90302e54003070002d8080d085105d4860030304405500840340156814495010040100300011005c1c5000310100300807079141098590040d0240c0c000c945800700040d1001401482d48485034124250214060401c504010001c000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 632234244 1250 632232994 632233001
    0x307050415090e0106030206040b0d110711010f050901350c0c010609050c030703180c2d0305120307050c0a120f140306060913020304050c010801080a080304081c 71
    0xd91849800c20060400a01c80301e4065000391541c020f000b0864581140d0008401d40140e000f030a90080c000300d065080d50003d60300c0307402c86801134200e20b45c40e80e5607450b1071818140f041c00d159001840c0e102c40c000c1c02500031000e440da03030b40c4161180d0b003e05007029200e9400c8560400c21104810200c41d01008003500301881c46c0c050010450b14a0303032801010422800e49001e54040d02610745014104180881540b06407034100c3c00c41d1502080c1e00c032030001089010f10325184082c2c0074480007070300003e8002140441b0300304207200604d0800707500010940310010303040d82e1001405641009050400303c420100046034056010700b401800c1c29100301220349481001c04040f0f80004400000d000c0b415007158202d02030506514200f034001180d50303610140c900003d040315009520110b80400c00e0751394264480c000e071890b1841192245014100315030740b900004501c03400b00d044135001141c103500100e0f40c04102e6402c054400c2ca1501c542c1e031007285a511450031100b030682d600100645801c0c0a00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 632235494 1250 632234244 632234261
    0x50403090312090b0901050a020a0501060902031b1e0703021011120a020c0a03110a0b1f0803030c07020907031d1e010c0c0f030c080d0c0207060512041103070504 71
    0x58600c10024154544103400300d1441e4048418442100400c02151000c5000c49516000030f04c1c103117445100020050785403015500000b440c95080c01c00205401071550f0241d441006806040c075011844111102c03200d1140f42c0080180244c6440d407000181c0440d001041140d00c42d20468202e541d1825124040700c042d0406082019000902c0004104004501641080c540d01c0c00f140781c000424030a80d81c40416071801410301c02c000b05c50701c000b82c0052203503040d4150040890186850304802001d40d903092441c40f103081ba0300500010944c1c0c2c0001058030f208001c40c0301d81034034180003602085410303280100719800301921968103550902ea19003565004200b400d00400000316a0408201800c1d10a00c0c40300b0740e82e15014800e800c4a90100e104920640c21210f09500550103060031103031081e0701007010306a0b060004052803000b09603401880044070990030303214415104e000c02c4415120f4815004100004580410701045038010700c9881400c1c0101140c40071540c44020406588001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 632236744 1250 632235494 632235497
    0xb1b0d05061306060e01140c030c0c10080402130905030421021f0e01180f06020d0206100605041e1701020702030f030301030201020a081303020a030c05031501030c0506160204050403 80
    0x1801070011900300000a0207800110007014014182080b8005011115840707142c0c2c10841c8a03008141c51036001d5048031310035101710b07003665030340c040e030600d480d90b241c95214078640203560110540c8541845541032a000e01d500510941c1400700d000704c0342001d0450f010055036940000c210014a15440100c00f050014440404104040b10340c0100f284803542c0c91405040289160701d980f540c55405070088002c04000d0826001049580080356018205500702c0c0381c10900e0320310041552a0005100d0110b62616400c6030708558440300e442985040c4e07841100c0200340c081c4400e000380c0451464900c02d0b9074242000007080b958500e54502c0c04000d802d111485039600041100550170140b212808d02841e00f002540b40d03500d5640000c0d0348442003180030701404804101203406000300980c401c001c5070000e042c9100c0036124141070203043c1c214071a1502c6841150040c07242040c400e140503040302d8014100850080c40d14091240c40d0380a10324080d40207442e80485001a940c620403540198020b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 632237994 1250 632236744 632236751
    0xc0f1309090b06041e110409050f0f0c090d0609080d1d0705030703021807021e0313150e060309030f070b09060603060c0306011407050604061b0f020a0b1b0d 69
    0xa80c1070540b41100d014010fa80514101003214840440842921300f04003050000003035011808184207059001c0c40d0480701d1a14204000d10080d00c0b4460742180c001c003440e00c2c944945498a41494401c0e01c140810b280d0000c0211480f10040744041d4800d0081a010303021a030f20340500164070300119020507a14060707000c840641c5401360300c003c00c111000b4000c158000d1241500703640000b2050550a007800b2078012403880002c034024428094203841103c10113035854824104001c9076100c3d0400d90004540d0700c480390f00004c04c601d1a13448000c200043d901c41c1c03450010a002441030f103610040c0350403160310040103a800018a401e001344102e6020340030300c0596003002c00050b81403140c080d00891103235000e401401220810b2008403a040002420401401003110f0b5044990f401940da01800da4054102080306100040d0000c6500200c810040d016400d44011300380d079030b040c48510740b00050b88004c0c1c03010002016580a182c2000c002c007081c840040c5816180400c90703020b16060200b1b60b45 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 632239244 1250 632237994 632238011
    0xe06011403010209010207171203040b0403020c0f0f090709170a020a0f0e131104020f0c1c0903240c050d0c030b18040f0507081b0907080c0f1309 64
    0x1a9a000035000e560228025440c002c2c032040001d54880d410702945090f465100c089514a400c100124a4001d20600f20b66480e490241007540702a0001c0b241640035002d00c01c003520052500c0c1c5564901d001005051480d0100603109001104400900450034810103140219201341d55011080c0002842401000550014818021102166409400e01c3c840380541485003002e80c016a990101ca01610440c0ca0400c0d0704107000080c03980308a072a0030510000d60308141e900654020070400310071200300c6005480424125140000c101d82d00c00015900c82d10510009030040d80301d0a140710541101240c0ca24001014000c80d5540658a40410b8000580000103840340c010ba400c0d1180724101040440d05080100b555058078850f52040240c0d103d0018081200020329047d105800500f200d0b0042d403503000c90340d40d9201c2e900c41c02200e0714542c0110340043c035052540910501c2260b803040c070039844194404225401040b210300b100001402902007060702030b2242c40c010180c904c4040350b40781 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 632240494 1250 632239244 632239259
    0x80a0c050714041103060a0b070f080a120b10142a010504030f0801030302031206030102120108030c1b0a0e0c0f030a05010e0c161101090b07050a1205040608040209190e0601 76
    0x132000b40c501402004280708024081d03407040b600100701d031b0701d080d1410360701d004a14040740d030b00e6074141d8000c1840c1c10106042c051244c7c029041e003940380d500d03002005001000313000c11201c0e2400f040e400000a14550840d104185400d018014045074203212160481101c06c20001c02003070a40b1030242c0340e548108001c1455844904000d400407541407160f02135046440003516071003503d01000c201000c0001207006a1400d50444420100705c0d100200c081d40c4501c8103d40746c0d0f000c031080050b90301c0b80010004148000d00d842d40c1ca5510010402139025181140c10808011700405806582805102c00c00454404100440c420b68007039000007515810b040d0031800d8518040c196404007081400f0300001900405490f1180e5500414242c289540c0040125500b00590300300b03143d101408507080d010042c0008507072140510811740b403060101d851404482d24004c0b88900300016110201150150401c1031095800410a171251340103100b005420300f095454203007a0300c107281c3c0f10800400206 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 632241744 1250 632240494 632240501
    0x1c080703031d0613030e031914120405130b130207030207060801150809010e2506050306150304081207020c0102070504021306081503010615090503070b0304080a0c05071404 76
    0x12901c2e8103080d0025007440070960300d10f0001c0c0402c100880d075030500420b05019091285d40407070300400f01d0717545103901c2c079034004000481141100c0650b441c2e14a900c540030302103158400c500c80d40380c0440c201460038003040b108900c040321a002d0960f9620080200c3e4542d081d1441000b1203080025a0301c40b0b213454000d14000c80f5a2099041011900041c440020b805c0815681c0c041640341208440d1207d864160040c546074010110074843c00d00b008041c81181d01000b174010130408484180c0550b0b686094400348402c44403960f001003450004035515088002450b00540038000403401d12409a041070f01d491000d50f0414050b0b03009140701015503904210071400340c601a04c00b03504001010705400d11141d054041e100074402c3c82e6000890701b100000d004079120758018000e01c40666240c0e401c40032601d440c8590707400203d4264001c540780c2000601c0c642107a1400c00c8161440c1e40d9a116219180c1003000140200701d440503107030011840c10040302015040843d242c004c4560000d080000300e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 632242994 1250 632241744 632241761
    0x9041103040b040c1401170403031b02070314010902180702010605150c0f1b010311120c0a08090109030206070c11030f011d01090210110f0111030a0c05190e1c08070303 74
    0x3030179a40b90041290b903400010490140d0201c001c05107c0d840340d00e416400b905004140c01c1c00991104a4040358a0740041c14104a038001c640c1c031403c82010385081804d07180348220103500244022468030111007940280c0d64402e0f42031000052281e140d1000810107504864862005803003c160211491020b02106114000d00c800800030318111420039550302180040d01418155262224100302c4441c508130b41c4034072005104181d86240c04944881c0681001d11284d0024600b078000400c0a4814850a64166016001080300d0b1391070203812110f05c102c1c0381d0200c0d0010003080e60305046447c10030a107500c0911035000491010020000d110b400801124038220681c1803080160260722070b82d11410f0458250310b04082c00780c4c8400c2416241581a500d043c14541c41c2440c03600c1c5041c9440301550044495800c240310b448000c030011101070041c01407102c8245c0042246440c0140105000590365101505081c941d898660f0001454214158192903002000444038101035061048462 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 632244244 1250 632242994 632243009
    0x90c020613060b0f0d050a060e0a0506010e0c0417070905150a030212010e0a0515070903050d0e1f12060e0f130515010b0a03150503030f09041103040b040c 68
    0x4840c41c00340c1ca46220907501c074201504860f0340b50019000c90b2a0f000c4a08040750b405050409400d441d881c21513503a00311003c040d0350306840c1030090341c141031011850000e003e41080050403d80d0030101000380807503024058120841c4100030010322540341541d0350800d00007a03809000203d141401e18001c2c0c2d600201003c07462000a107403284a581da07040e0709400e80c0c2e011781d0200000400540d039107004201507c8112024032800004008000000076402d84c043c400d0044002036890350202a91880a035000040c00c1c0d03001203c9076210207209100c0003260300c0b070081402108002401050101607034264101c00011162006150018824002d8100508801d0300256071f61a1041c5a0705001030041c1c01b6807d0035210001100c00d0000030861005000d600700600500c07940c0d54051400241c1c040e0801e05d0100b42401c0c486000210ba40790040d08540d40075025525242c4980c01c50f40942d031101da041d42d8010b80c4e41c00755542009104025600c132b58802d8210242609240c18600070045607a4085407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 632245494 1250 632244244 632244253
    0x5130911030102041a0903010b041b12050f0703150e070314130519080c010204090f0509010507020c010c05030d0c020106170f0c010503090327040b0f060a0f09080313090c02 76
    0x1107204024500445c4d40c1e0b120200581700d072440f1380003e0141400120442c0d2140c100549820703061500ba80254916200e0388600c2407624001c0903143c1640d1041f0f46962088111100240005029400c80310360b013200b03540a42041c546800100007218800d6691000081d41c1e03100d6101c1c1046511251130b00141504840c00280c20260380750ba40d207401c1505c0d00e8503100d03c3c40000c1e50410035008191505000610000d40d00c2e10340380d40e2450001e00e041001502c1d29824000460740c000418440c490041a080d4090459601c0d0300005456518101008550601c000c000d002c02044007449010500350540d8008964540340100d100041c12403101c010031356070000d840161002000041c10b81d000c20f02800d045841e640c8089144c4d041d13004816100101c0e0f4919502008200503440024020f04411641003140800d0701091003840c010000055401c02d00401c40300748074030300907030903407203420700a15182e400d0540303520300241582c020244200307148820300c01c103000c00318041c00703443c48143c0e03e0700c01403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 632246744 1250 632245494 632245499
    0x8060a1a070813080307030e0a05040b090621061303020c0907050426010203090d080c0702031e1603050d0930030e0604120506280e070513091103010204 67
    0x45000c0e10400030000c0504900042c1c0c400c00344000c011000c01883c2d05070550340c41e4031440c00c0150034034000c04030161082c0e0843c0c4010445190900c03881c0360b5114090000e000c0c582d100400d00800c4c01d01c1032002d81035001d00955265502004000e15403080c034035203441010b4a44c40d881c0103860648005100ca200350850f904100c08903911005540466a01100e9401100200d2103440400c0c0c807607070141c821070350001042040d11000040c201e003002d13030b0a50750803540350344030b8021901c14090108000d5240c0c00540800010b00c031009600044980d05406948070311402481507008100c0c0c0d03510450ba5a0030800348105500d8202181071700904080300814901503265079a0501c4200c91124901c44030411004c0c07000740b42c4140002d80541c080580070b541d45680f01c032070b00d050303a00d0100c42c03c4842e0702c16040040c01c0500f40b5a04402d540700100025945076a8181000003d010301c00c090b4441886000720000e0300d6a5441c003002855101c0f41000200c019150400000000091b40d255009030f0040204 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 632247994 1250 632246744 632246789
    0x22110f03071803020406030605091606050a080c04052205091501030308090109350403051e10020f0c24270105090f070f050105071101170708060a 64
    0x300e0768091030358900800c001803030030308410105080f604080d40191405070080304205943d070006001d0b0b01c0130741c200c904449084e030310f021043c4024040c0300c00050701400300c1a001e5001d501c0304c68101c0091110142080d4a60380419101c0c0d0710142001e12248900c006400d00741ca03903100c1c3c10b4001d11800c004e4114001035039405070003000103100040400c07048000160942600b0b40c020704045030702c030900c00c11a540112107071140c131600c601c54000e10720034950100610f11082c8105c03001c5a50080140c640f52100a5009001c1d03164004030220364010260b0302c4e51102d0482c401005519110401652100d00c1b4020461a20b104025128040f04442c0707645001c2d4401c2c000825401101c16a203142c0701180702281415454401c20f601285600f03002c00d01c071540c1001702d4240d03040340d1401c3c110f820480d9a500c0c0d0031a020301e0ba1040b1804108100b0003500402c095000d140003e42d0181816640c2c42185c410f0645540700440b42100043e0b003410611003903161421641000b40140c1c0011443c00303509422 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 632249244 1250 632247994 632247997
    0x140702060a08071106091b090415020304050f0105010f032003071a0903160501262406030406060314070503190302011409250303021005040203030922110f 68
    0x111400d0003440c10000e401c084c820350140300000c0004e426201241001e098095413007040164440b040c903192212034030a81042d0250301d20035034202d8000198980700320980384c0294006001500c10340940c00006410389401d01030503000788180e9182552091450401010580080f03480040f0001800d0307440c6015600042d005c4191001c0036214452060305441941840c0b0400c221903402d40600001851800e50710445041262400c6e03c5180d1144802681d42d00ca505200c0e0304205005550b40c0810302c0c0c4244101200510000c94960710050031700c2030b0009107160800c0710200e07001038442006000b0403207021040902c403800d00000700071490809001980350000d903202d0458260488001342d080c18400d42002c50000c00311044050142042200da0f03131a20464040f252621010001840381d07000010010b004494040c5c0c05000e0041c03150410301c02400002e00280e0b890b11050014a2669942d203203441c06c0d14031015003140001801400782c0b0b084d034101000c828030b82d81040c003142010300049030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 632250494 1250 632249244 632249257
    0xf0605090406150f09022116051c060b0702010207050402030603030405062a0a05070e0601080c0a090b030705120a090f1b0306090b01030209130309090209030703120203070314070206 80
    0x702c2c00726060501406481d41c41c2800e07807100d100d55880d20000500580320b58018602c3c19034101c507240080000010344c9454080c02da941228400e100c11800c54150b20070340190030a962594030210608403503020400940c0c020f508450080500003451004660301003098600511040c0d906600714a05080000c0e103c0c0100d21070701e4010030380050b004518081d8001c4561219042c03041c3c844900e1060480503a58000c900422541480340600120b0401c0900f0b150b2481440c059540a21a9503906015880c0750080901c100034028000320109080e58008080c0d40f155411b5a1541d448048a0034840080030300a00900c50716450306403401e0216094265000301280c000c0c4401041c0103140c0501000c10b80c5951000e80298503100ca603100300181d10a030b0b24102ca0013125110304c15204e00c0250080f03500e480c00000d010074002001003061442035009095407903030003000d80e540240c1d039440b899580d15298481d0700058000003420405c2540192083c8501500c0000960505040b82e0101e540c0d4403926 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 632251744 1250 632250494 632250503
    0x10806100312120908040312080a06050a03080a02010e0f0d260406020c030d05070c1703072025030606270b0a09021612020115090506150705100f06050904 68
    0x4441410300030441350001c1c2d00480d0321507020366442c2d03035a0400c001000752410b421070000c6d52450105480d143d0394003544080c0d8000418000071180355958035041a40441a500c0655482c2ca40304420000180028420108035a000d040045d010003001064095400c080c02503070030f6602c141c14060350701c4005407944103030b0103040180d44405032036200c1d29602504040c0d6010504000404c030409510560900c80700c0d10a01d6240783c04a1003007841000c5010448001000a00b00003203032120880301400c80150481c400140c8072200e01c00c200010402c201d0840340e4903a00702c041c20030020000184124002031041e2030b65542c2d024100000c1c0045064891401c1e8000340c0c031030008610300d58508031140010400000c00b107680e4039202c441c80110308418003096400300422000c8411203401070081d00c140040d0805492420360030010540014100540001d8015900741c4040301284603403002020218045d0008000c484003000c2d0071000d0b00c05050300d58a00c542001c40030031258680320340d05a0005d600c07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 632252994 1250 632251744 632251757
    0x90c1a070f0206070c03080f0a0e090601020307151e1d061306020706020405060c0a020307091503060911030d120c020c01081503010b1003020405010905060301030807080c0f0a0308010806100312 85
    0xb5810174910442c400c2d00007405041c4002040740302200840c000f030900c05139a803607140300000341d1020000034900c229510b90158004100b04400215a0210200c00b414882400142e60b01404401c2079002e400c0281d88802c10f58803402070032002051801c10f0352152503103004044614005500300050083c110001740040e8010500404000d05501598060300000e4070b11601d82c0680200b130b980e20f41b12941c099009000d05880482d01d0203940c022001180002e000c424035141c80c55582030020f00b080042075800c2081100000d000d50b40601c48403121140030b60b200400120490850381c204c840c00703c001000c1d980410303d2180e03d640c012240560003038902034810800581c4102080c05070207000700555214080007084803d098140d409031080e10700030790b00d5085894071081480240c0c8400e0101500c402d6080c881c2c0700005408070001c1008500c014180c5001420b00e4000c0d0b86008403d190440100e6884001440b00100800c16240c1c071041e44130340364134090321b1038071069400b802c407104c0001089070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 632254244 1250 632252994 632253007
    0x10f0819140114010519050303040b0c01060905070809070e06011407260309010e01021c1e02030a0605011418090903070212030a020c030d1e030906090c1a070f0206 72
    0x500700c41d900d10061220300248000506500b29062070b440901403d885501c04043d60742c008030856a5200950304040d000314609403d02c0101e03005600b011200200130b40d00c81e00c010549000d24001c550054000d0303203450b845400e01c2d152240c20602250440360b0f00d06020000c000440ea031052001200c401907020595407030b14036082403035403000380904001d01702c0c2c07000720902220f8a20340000d51060506400070042072405003222400e03807145954802818030000c60394603e0302c210380d000781c2c1b4031454198000020110800110b084c2d800482d0201c100c5a91104200b00a580203090360400c403400084181c03900400e110700c1c0901201e4451403e0082500c4d10000d0103c0c00304004440c0d00c5900100b6003180c543e44007c00d0790f62a4482441c000060241c040d1060351400c0000e001800030072151a01550705807100d0f84030214070005083c2c58101a110107a0b600880d123984100b4046034000c042e2140c445043c1100e20400464211082c504194100108400706001e04010340d40d159049499954a04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 632255494 1250 632254244 632254253
    0x1b0f0809030f0315061207020610080a021201021603030c021c081503120f030402040615080115050d0c0c052a06030417040e10091a12010f150509010f0819 68
    0x501a031401341e0000e0000a905820369961404640305031401d500302e40541c1c0e1404640c034420440341c840c040b0150b0103040900014135019a83c10300c0e150101c0300050508141d58241e40384400103100980100c2d9940a405100c590305000310110600c40114100040030309820040a990f802045a110004031a0071840156000e0185080184003444070f0707a00e9100b520481266a40150f03400ca105510342000003450140b1500c03140c000701c0c4291220f0a4a03840c1002e03c01402d0358125000307080200802c40f0041003166031080c00a40d03080c998640407040101d02c0d0003460801e100c800b002589151400030058a031030844200d20300d210540d0740c192242c0301c0789020b44526029002030030203800003040c0400e584280d010100d12400c04c0c40c0c100500c5559501c41d08040347c0b03040c0c4400111900e06580c03181281400744100444100038000014228205489141150402d81c0e14210300500660304100074640110300a0152030700382d0002d114585426541ca9840d0800d10956181c116081110402e11 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 632256744 1250 632255494 632255521
    0x5011401150c1109330f011209210f020c03030d0f0603061407120509030307081e04060b040e01141303090f0e061305090a02090c0705011b0f0809030f03 67
    0x3e0b0001d4000c0e4000c0c101611040740320b10134444d44201d41c06220f044407003035034100342526660b004083c0031030744038001100c01100c4a0001000c070546140c2ca030101070340010642c4140090700c2c0e41200c0c4078803100891000007881e00221620b8000ac551101d1001d0110355008001c03680307440b090000c0001c03465070304008540903000f83d91016102c980390005000010000c1003601d03204070910350311076404081080e40302044407000c0d1940c00103940300340002041180228001e030340114000801c190001182d90489020810448040326105e40b502014034150801c2d003e145a5204080d0081c892500b20107140b05c500721006009505ca400288800ba003407501035200003001c1c040c08000e82e00c94545800208000400a8450b00e010340c0824400d07201d604c03190720600b800381440b1009031170312040540070003400703e0000d824840824010842080012024403550341d00303001d0640c011410800b41c507005000420890400d0081c0708808080054000303004c80bc86401c0b080d0a5002e603140d480303801043c00c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 632257994 1250 632256744 632256773
    0x15180105010f02010e011b091a04090506010302040819060516080a050601030e030f04051504050913151a09060433091406240d05090a02031905011401150c 68
    0x840d460301f0000801d84941103030420049481da103804011980e100141c03800240c0084074080ca2071000c0c0030070312071024103801451300018149030150900b5202c0320080d062a9040c440c04651140c020255402c028240c02503a5000300c0502c216003441c0c40300ea0f006040c0440091640d41c0c50b1b40c0d540e0004419070301a51000c0c501030f000c031040302d44451141e09601c0e5154054069180f00b03072500f00700041c840400804603016150098800c2c855511a258620940403500d001200c0c03240501d0344541d01100148520300300410090032030303107209600c18280031041001500c1d00c0d0003141804246083c01c054003200d901c0400d20f1861100c2202100034014803460030b0b5401036402c11b4100805400f58401c8141030f80e000b444100c5030243c1c403000342c03d0034030a1807041c006005840481480f1040b00b20303910b644a00d03400300c404c400ba10480394090b13000a017003031040c1c00f0f020502d100c2440c0003000d002c001d104000c00790b4007600820000d9410f00c4550350300d814800c00418100329000074180e00b00311048804441 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 632259244 1250 632257994 632258021
    0x1110307080c28061505010507080a14030c040614120f040510050115020c0a03111302070510020c0d0908070329070807020d0306030c060c02031501080615180105010f0201 75
    0x90303581e440720406401500d0341c44152001c4d4206603060200c0e121907100141150340503112a071520b084c41d0340c0c101442e080560003009000d032101c1c0b8040340142003001903202d0502c0e0715101d640e55080c850094801c611a11011400060a01101d9075401e05411081d4104d0701c045002030107641c0714a03096140c10b0003003885d8180642440700000d0100003d00350780d1418441602507a0b0032040341ca00f80074240c04688005480b01c0d900e00c032400362504000c114400403100c0700c000540f030311080380c07030385841c160541020231060795001494000c12241401004061410342c034000d07107661301e00200284e488400380400f50059800c0141044800400c03201040700c075903c1c005030600340c89c0800300a060301e00e0458641004d0f0140c94074a842c0c19200344280415207621000a142c8581018021280c3c0c00c2000d80032070309072240d1500d05000e82c5514400a001303040d10801001c003803410140043c91104501400d074080d118400b20a44082075404800e41912420303c3c1182003607401c100d080340541541c0d03c1c00700 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 632260494 1250 632259244 632259283
    0x2070b2a0d0e04062c0601050409020c0a06050714030a0c120f05011401051215030309032e05151009260f03040b07032303070c1101110307080c 63
    0x65054002c800900200c00896041040c1503030360f0750121603c0c00030041840404241025482088040880d160700306d041031502c40e04150715141108101e9000180c0c005c0c52364080c0340c4130002c00600740078041e802490341c44c024429440300c04000b4124040501030041980c0c0311030f40b5414940c4207407102c09602144400910a4032030313500041000300001c3c040d4442c5401d40c01c4035014154055022a150544404009421640d9400700c582213800d100104507858041008120720070340d803c00a060001a007001c07060303c1c81d101907a41841802040d40403c050b541031404012890031340604548500300151940c03440c0703032419182241c1c1401e40c2d801148255a0300046207011140944040c0344c0140034000720350b0701c00a40c001440e928041c9100c0c4a00040080144800091140e05040005170f82c4800e024000305c640d0300403010b41d400807903802001921039103060051011000000600307120a0800403030440e882c40e056926882801d1001e05100400904420811b008206051038a09c120007110f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 632261744 1250 632260494 632260513
    0x20a080d091712150307090b0307080319020601050f09160e0406080109020f04270f0606171b0915030a0c0603240609380d060602070b2a 60
    0x2203154224034000d0218191090004405411450b0030490318030005008080c907071f14100c1c4110140c071819402c030b901030080441c00510000c04002404940c81d0301502140340c054002c10007458401e0580c07109216580b440c5407252140c03100c02026810050001644030b240030100c905403003031303130420f203020760003501c4d080d00001c80c1d10f010341c01100604c3c8212148120740110300200029616071a00034410b44000c0c412070049070141003008a04184509a22803250101d038550308221000e55009101c40011200305070034076032050205032621f04484007241c81000342407000c1400b640b0020520181c442440303c5c0038100340e408000000e041c6501c00d54103d90030b41c441d10000d02800140b01d00250302890340b80d8115402c0703a060030b603100f568403e0b42d5a48820b450030540b00130000a181c02c180c08006200300002c5036408904000781c000d96002d40c1e040d50345414466200c2202c0084d0b2086d030854000c004180100100c00d006c80c0c0c48804d003484c8030130015141c401300490884c0e01d03240b80c260910802c10303007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 632262994 1250 632261744 632261783
    0x90109051608010c081b1b0d170a2a02010e0a0c05090f22020d020d121d0a2610061a03090a03030e24010806070e01020a080d09 56
    0x70799042d03a032080000d1080c00c007042c800ba01c3c520b82c1a139200e400078a030070800c0290700306280080d082207080803048a013468600d089640c2071403108049840010b416104e10449202c042e016190050000744040210143c1d42420014419030802d072000e0052181e0b9407040d1340c134400d4001030203405105060703425905c4c5518051110124510a490041c2d001e84001840e03a015200c0c028400c46580d481d0071041242d0040c44141081d0308c4408903844444d40382e1034800358680c1605d00b0051841041d000180d109020405401100340c1c100a007441d40303000a0b080525211012451304466014034038140e0f50300c49005415804c8800b0110010384d1050351400e6200b40e500d50000800c1b10704402c81c00c40560a1144c1113011480210b03200501030b0310401c0b0b80000240301e41d0200b400c0c00314a405071420042910341404032001486281803034440118014803000c3c405003c0707250040594244803080b19417060010b51901c1d05058040d0080f040071904509001c02c603006480080d60068038440d480403400407 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 632264244 1250 632262994 632263033
    0x15060c0106140d050d0f030207060c0512060405070f05090406210c050609011d0a0302120d0e03010b0f100207050312070506070c0c120f05030a0e030f070b0a050309010905 75
    0x210348502c0000e040ca8061410801081044180c2000141c0741c2849269410385120903039804200816508110340c00c089a460321485002c0383d91075481c10340d10901c01c1c034214000f00024006a00c60b51078101071100d80350300503003818800751072070070f10320303200c01c0c241000800411143c0d205828003281803200da000351020f20014141c0510940030300c0107564482e1709102450244e4008180441c1c450300e4100c0900c0c0c2d80a204006d268802401d04003075a0b1258046140508843c1d08044d095109904070408a500550142c0303c002054000308008522840012010301c42e420400d4014902e240084540c1482880000003401014084038188809a03ca010103980300341000c1d00e16005d42408180c559102d100e0888030580c11403040c0341003a091038618200c020745510700b19100441841e02c0400660240040c004082d080d44900b0031186408080c0360401d80042001c075020740107a5024404900b191064861704c9429260483c0c40390384060300c0900404603410090041e10501010001c010000d20 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 632265494 1250 632264244 632264249
    0xd0e0f09151c1e05100f02091201111806160804032102100e1f0f0516080403030b04110705010501210201020715020106030206040915060c050303040b15060c0106 71
    0x1da51007042e95410500748907541101c0e20040100030441400d50080c3c00c0301c4a03519500d130041c01914000d4080303940100403078000c525100f95aa03008985840c4c60310740525403c0216240700028003a1fa5801550b103290f07403280700c0c00401c0e507500d9007110681907290241642c0780041c45e4a00f00c20101c649081166068001b84400c590f001c03000c2c0c0f0702c0340b0005500d00c0c504403103100a40040051904c0c0032403000c00f6100084090f2511310a03c02100c60120301045441125440c40100003120855541c0c150252500104110004a1110381c0c20320000d511590b21396009405283c0011407004a030b0000b8080e0003980031101c074414020414030148401036000034101d904001c40c4000421503050a542c1d4000c80000c040d000d6007020b0801c20104030070380d0742c2512102c42c0d03100000f401034580c0d0008844d600240c000320061a81c40c101140e00b440c00b9100c06001e04000d0401c0103410926a035100e50324480100000d103005510800f02e04100080303654680307485d0000b02826101c12051b000b030742c0203021a1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 632266744 1250 632265494 632265499
    0x40806010b1e0a1d01111501140603071403150a03080306030105090606010c030309110907120b030615040f0e0f0f0105011509032316081501080d0e0f0915 68
    0xe18034600219140d41202c08250300b5480e0030042c20113884004501041141c2031034180a50844001e240a4050016001c900380d000400009941020000c58105151007461401181c1c20401d0002454000d1102900b05103000c0000d1390321355421032000154065030050301c1e04180d9852005c42000844006540b00301806c0c0c00070007842d690784101c90794441c0c06647e26808140350596080c0864402d4000c041035a003d41c40c034034020a0280041040076800704e07000d20008078000d070301e8010b42e51039024a07600c04004800400301e40c24200b08030003010a035001121707c180d039500c20703248091031642c0015035080f8506082d80e49444044c1c4025442e10350b00d10081083e5441d180000c0794004510043d440b01c403085039039a51140f0b055686103442e02407010112881c4840ea002d0f04c811900d01000b8824000141d100140701183c40d00c00398030703e881910079a0340c03404c14005005202100700001c0030b2007240300c01c1c60205483c850341004103001c407c42141d0580c015425804120201005480400445505 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 632267994 1250 632266744 632266777
    0xc03060504081b0d210612050303372417010f02041202060c071820090f0103020a09050a1211010f020307110f030a050607090b1c020f040806010b 64
    0x43c104015144d0f900720b81c1483c0400c14101e90b440c0442c0f2400c2c102d4107809142c1c04c2c00a00580c0b11003030b038086c0301003080c0c08441e161300010811a144480d608881c0405c00140201c1c00006d40b1601111041c0407800c0d04804480d5131958400380360100018103221091045401610260300c65260491100c9010b01d030a410703608042c14104d041c1c49070f02c226403c861052014202d854100e908000c202d0344201030b018068030601d18003145081401c5000c1c1c0b1201c0003000006104512a0a80c08041406090b542c007041020b1003900b80b140c44000341198505002d2a00581e036a80c2164151881c1c2c03604d4000c29009003030300001003030f4101000310807418580140710b800300407003a403001151010004405039005800074000400004c002c0d9101c00f42c8000010405017522011a001c2440c01c01000010f48082e071080050080c200e230002c10b07030001b40024070f20307040c6082c4020703040f19101e1280c3d440c06c00d80e159000480945c0006000d0980300030780303010020750b901941e46031464034054114421070b02d049000d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 632269244 1250 632267994 632268037
    0x2406301c050a050306060f04080f010902030d0305061014041203050414030d1e0c0f030f0806031c0518030a0c031104020301180506040e06090f0601150212070c0306050408 75
    0x146040d1084108030390f0715913103940e580700c0910450b80c1200b41d10f001c01100c18000450010004c0c0003608038001e4142c0000f42480240c0101403410110712402c20a141c81c4c0301c18010346807501e15003208154054141500c080b444001c603004d01c1c2c456544811810581440720000b0554094000d00459039500b610b00701d030b890703200d08164440c407150b90040080340e50080c4056100e104100e040c0c00f202200d0915652410b0580c8500b4941c8510540880008010f01c07449030f0142e4001320f0680c1c012906030010200c000c021024a032a0100010100c400c2c0304001c24100158502d00f1000c40103907001400362070b0402c2d40c0345003030714505d10b0500bc11201e50444422084640c00c0503c03e403070480c0c44207580140303040c018010a1005003000342c080780d081a01c030b5030604600501004081d0044140c81e004058900b480c580f030908102060700030b00403d42c5520b0703075014903990004400d130038503003c41e1105a940c0454900a04165484e41c00145802d06140410040c445004080c180c11000f4112400720201c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 632270494 1250 632269244 632269247
    0x30801050d111002100f15180f091a090c03060c07171902070e070507060915141005030109050a1106130e10060507030c03050a050d0207060e2406301c 66
    0x411f20481c1114020144800b04041c54860683e0080c003008840c0020f5010344520428050300c0129405075071700181c046000d07105c5843d807068160301501c0d01c00a410a441c86800190b01c500c8007615002d00c0200115481c0e00f48015000000c07508200700e207500d03603503401210940c0c1c00003079401c21507800b5003e2480009040f081005400c0e218040c2a0b0311180380410b140d984c403000f0410818140c510868002d0220702040d0a0f1040c50f4040105e40e071401c4040c0313402d0000781043d2205410541c081c6e41401e5001c0001800000c0300c004156002451211a03048440800d855000707690100190304043d28002400203590a81180a8141c0ea5402030015450309030681e40c81c45030f0000100010260650381001c0303807181001e070070003c0d603d180403450117900e4848801030383c00008056549030764490015560400c10844246d0100358162100c0d00c81102d80100b840d80d45000b01010302401070007242824209000c0703d40e451030360a9427a0f0113007403d40e05045682e41c1641c5200d120301244004920710196 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 632271744 1250 632270494 632270501
    0x9010612080a200a030309050c010e0a0b0a050c060f0103030905010908060f0c0c0307030203090a090e280b04211d0411040305030a050a090b07030801050d111002100f 73
    0x464010000034900000450201d079400c00d214242510300282d500543c595800a004094003d130280da00491016803500300542014100380c005818440d00a4103e8826183d105460048401c030140064880c2d0360301400f500d00307205400306c0c00318501400f8100001b50307503228a4941a64041d5a50041c800e807150010764100700345000f22034a80e4402c03070024001e0000b8220301c96002d207126a089040c03204d050000752454014010490141c1c1011030120400d00704440d000d401000c4070a07042c000e500303480303055075110307078000800390704079010300301301d0b441c51320100041c1414160b001e02000014500f60515131701d1480b801e910a02240818100000c40a200d248510501c00400d060000c0c0b80303001038100300042c0391444880407605000d000020120744140050f10011604e42ca07205e40d1031941d0345005160080682192080c68414003030300002c682c2c401071907410740304195500c0b2a002030b02e00f0081c60b000e000315215a842901506952006640410391508146403000203002700c02c0c600c03c541054 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 632272994 1250 632271744 632271779
    0x203010e040f230307030215040f02120c09102301021e070f08010c09080f0a08160636020d1205040308030705070213150e060a0e0f090106 61
    0x1203000030082000306603215501485107105510748051052603040c15000d14441654485094001088440034560144660788a08502e000d0240a40c42c155590b990590344100c0041c0c02681e5152a82040f0501004829880c01e402807101c0c10034544180c08441c515002d002e03d000c1e149159241c1109600020780300000010141c000e4410b400c080b42950f080003810f0000f01a2500c22100c00188800310b01142d0170160101c000045440c403080d8a01602e21000e9a000e84100d62100682100c915130210b240c200f4a9403060200d95185070074024a221a503e00034050001803411080003036080c0c87c020781101c0c0c2e00c00306403c50390048080c90000c0c6842c403000c00181d0041d0482214234001226105084154516424000d05064403901c44e02c20541080341d0880c049080011144107600e06a0301c0e0070420340303810b50203010b40300c40761101605181d50740c880d0810201000001c100316035111850400544280d401c5000207180440b94044080d4040e9945601d0f54030300400800d5915040117007817403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 632274244 1250 632272994 632273009
    0x6050301020a092102060309070905090a0f080d020408160f05150301090b04020c0628020a0e15091507142a1305010602160609061b05030d1103100801020301 69
    0x224602e841e2110f42e0655002d413000c0c00c5001506202030050b56030390003a50052840c000140005402c00340301d0310403034001030408075040c2c1c130451020001a401500c000074040c1d10110a6840e802416802c40c041e0241c1e0b0800c030064014100c0c0302c400c41510441850072213140c032945881e0140e88100380045d40c11240280c0302600301c1040188801d000c10b03003002d1082c86000d0300051800740e40500c080c3c00c7c201d00f655400d140f20b1915080305058155100207004d401b440681c01c500c0c21000300f01c00380c0118180c02449004690240120110700c03103c01c00e84980007800703030545090407108181d029060b0f11441c4121220907103441441d03102440002c00b81000381c03c0040c95a00d0a035210a002e041e414a1384449a0100000d14110111b560500845008060310740080c00a08640503821500c0b84940e00240704000c070601040001d0f60b4040c1c0440c4030000c00252541d813121507828414158894100d0008107035060008141812605100840c400c82440010b07034641a12401440d003031b44801c0c8134054 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 632275494 1250 632274244 632274257
    0x303240b090402030402130e03030106020f030f03010e040309030b0c0c010e010b060f1e0d06060e010f08340c03140c0c041802030a060b0a08073510020d06050301020a 73
    0x40060030954001c0d40c05c00d000808402c0000700244486d016540f104400060b1034001200420040d0b8040004c00810ba007030002070750404002c00540e0120340814032070855143c00c0140800c0501d402007807158040e60700912001c00c2490000344030b043e00c5e44207a00955056190900d1702c5990a0184514400b001000b0005440d02d000d455004280348c000402e510004005950b0109408001a00803c0349070482c000104615280079000703400c2100150085060010200111075540e501450039036001c44960740802c050180401e902d002c200400304041d04894004c0000f039811038111034002482842039482e801f602070030041c86403550103490f2480d40c89501114252429103000e8001070740740c02d1000c0602d42d0f0700a2a800092030326050a1040e640075540f00c00420082c180200007401500d4150001c000d014504802c0004501490000d620441c111490f0012417801842010018480072002c5a10369107021003100700a5000940b03800d00d1074500480084d503401c040c000e9a800c1800e907110f64 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 632276744 1250 632275494 632275507
    0x1e09032e0b060f13030218040c15020c060706090209100f0b03150913110a030224160308070201060f06051801110706030614032b0207030b01030303240b 67
    0x14006402512402540300805002089800406101815507802c04d02c100f4204a0700d58018400e40d040c1003403c49020010740000c000c007007040002948100c48a0101c992604421001c0072814000c0140740705030720031270020701d2406220250300b100e054103000302c0700001e06460703124440c2c0301300741c452044400400c0720100400865541e0400740d43c0c02490707107001c01c20191460000946e07404c011500e16003e00c9480c0c20700c90a005044c4078410f40e4001c10348400000904580002d44905183c4015600d0304411005c01c03c0c00072030100036515600340784c0d400000c1d0b50b49149000f030004081194044015032800400043c4181410301d4103084560316110070b8034000e00120340081110041d2405810f2040300e511840741480100f001c40f0042904c1d0341e001901d2800d01000605c100803085074248a5440320540c1110503d40042000300b450490802c048507007240340e81070b801d14100398000382030f01c2c012800020034542c1641120785074018500c04011032101c42c080b9101c041881d40076505003c10180202e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 632277994 1250 632276744 632276833
    0x11d0906042a0603050a0c11030403020904060f050c0a0f0302032202031e010605121606080a060503190501050a110307030f0b030102070804061106070c02040f021e0903 74
    0x20195010000b205148010081c8851001c00082c00d80c04000042e50f180700700132520200b032084c800fa410b502c0c90140000e840030034145960380100d00010348a62201c43c00b03d010440309500038002d421840c142031000b407500701248815904a1221203000c14001003244080c1132081c1708072481010100e0076901c5055003218001015400b0310710490709481225046075820200b084035410b440184400456140e050606202d1010405e000c1d40001d035110002140d514540f0950407003d42d4850314002010390f403210650b00160040da40002d4242c010320b035100b44021030641c030b00407665028400030b00182e03c8d010140780441d00d40303502d00c000d501c006202041a4a20039080303640702012840c030100b000c0420700006800ca80c004081201c1603480028200304968001688d001d155403444082d03c03003440c0c00308003e407030706405080081c441c3da6940f550030000030050b07054910690341950409003064207402208800d0f80520220340c464407404107075126156400c401c00e020381492100e000154440c483c0d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 632279244 1250 632277994 632278013
    0x3031207020309090a05011508010e0c0703020a0b0411010329210111030714040602060109020906070602070c140a081504061b050a1404210203031c05011d090604 71
    0x28440842c08200800310541d80c0d258100342c06010000380006180d4034040d006280d0f104203403404018040f019004010381d040341c10403103501c814080100d81c0c2c0c50741289001c900303001488000400c6d598441c0248010710002c184815510b08081e00c080259105482980010302141d40780483c902c0d8005440c0300032400c0c004041081c01d9890f42c64031510700e0880314500e00f07407035600b0310b0a03d01c44004000c000000f9030140602c0c44002e42c1c0350242d842c0504110000351111014000d016202c1e400194220a50f1918021181d00c1034202c4011502c41d8018075128444000e5031052032101c12401403030b00211718044c94064201c6a02d14000e1904500300c512911618500070070941d00c55903242e410821000b12680d4101003c082540c80729a51428900090403a660866411000c045c06220034080d110b009101500290980060401e04800f58400a45140300317504040000300140200c0d004400040d8002a0599411038034161400b00d070500c40e0380608404864001b0032342d201c5408980840d14004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 632280494 1250 632279244 632279251
    0x6072703051c030209030a030305220f030509010c140c04060807060e0f03071a030709060c08040302060711040e01061404092301060b1c0c0e01050d15080f010903091202030312 77
    0x3c0143c240036600c0002801d00aa210007500402e407034408010341d8160400f80f40c0380c8419065810640c01000b5250181075000c2300c80d0042c2031190000745140c00342e010b00e0403c41110717404035195440280f60f0f0702c119101c00d0305002031401079040c1400490072010128405040e501a40d03568542502107108121180080aa5040c0c050203046804107151100041c00183d29102d80c0d0080d6580c14000c030001e0800130760740d0100d802c00c02d64040d5500043d10460445084276011105662a230741e0504245032251158800654042d107010041010300d03106421840448030040344403140601c11505100a42d540c82e50b0081064001c0009181001800608601600015000050659240c480b0454960b0085502c02d043c010000c940711820901801241d658070b4030341c5881c416081e103220000c0c100b4020428010b140340e071a80c041107581c00011690b1802007881c01c0c1101c01180c4214031407402403050388810f8000458092011411151642c110401c28bd4003500451406071840600c1d908010043d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 632281744 1250 632280494 632280497
    0x60f020a210519020a1404090203190c08060411120f01080706030b0603070c0311060c07060b060918070311031609060f0f181206060504050a0c021b030f06072703051c 73
    0x1c10b24901c040106c05400500448040141d50b410030924151003266034104128069080c90030785102c59034001c0b0b403690051001d403408030b002c0c1e403614500d002c1d5000d00192040b4140c1e5220800c60400150f007803d0341242d6440341079900c1750741c8414088094584441d85035800103802c1003c203010070701c50151106007074040e180010b2a1050810420304004090307c80241100700440e000c024010300b41701f02d20144400f16002ea140020034004a45802c003107008000c60150104006803000780241c003d06514124001c0c410b03602d280c544090390003010340d003c10400150300c001c0e011549900844100c25452101d89070040380350412070045801c0305c1c5c000500c008030081c00d540001c2520140c80d07140403091064401082840c20031703041c0000c03940d0003010581d0140c20001b090740001d03008940a0b005000920500c120300c0203100110b843c3c40009160507241d44652070402040e140d01c600c0e0036011400c080300d14815448020001e5241031070500010f00683c000314403088460340c0c002074501485455 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 632282994 1250 632281744 632281757
    0x10c110d050610050307090e0a060504060e0706110706090302031c03060b04090b03060c040f03080c07080a08120c030402090a1d032706040f12060f020a210519020a 72
    0x1692030500307091042e924008480f5445409000c0f9290910554015050404042000c980307401c40e42e0340d5540c0940d41c0031700300340e50b02d0300030070148151500701001d403400e0441180c0103039a03107d000034058511101009a076000d203050200c2d01c284510710420441e50018000d00130100c0740e1044c8c005071150600b500d414155580c2000694903062805000140018400003402c04c07070300300c21b05040c40001003180e0541c0724104002d00c00740b44112030710700aaa0304013103404d803102c80c07640c4400e24010036030f0031000491003203e1010341040403440090140407200036800e011134072208480407150009403030003503110507070100051030030869610519411a0188400340000c480d03251544c00c0d98084000100e030149400c031003c031201d620450710405400705a40741443e0601d40452007014800381c0c0183d0b85100200b1205401303100c91a00004401000c0002c11503507000200006000c0304072009444070002e8440c81e05840780c20321441102c1c807400c14072040c0b020300700119000c0002540101c1c00c43e03051024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 632284244 1250 632282994 632283019
    0x90d080a0b03070608091c0f050c03040e0f04051504050604021c0b0403090f1415031f0806010603050609072a050109081b0706020d0e06070609150e0c010c11 69
    0x2020410f0000502940e200e00e801030500120203801c05101c440a044143c00e08144850001c3e48500c0c076500369110307803a24949407a1101305032420740c42188d1014a49510303030b0f0103101d40107029035070817400345110303030201c4000b11f4a00c0f298030394120044801816a41107030001070b015003080412000e4402007002c4440c0c2d080c00c1c941d0380380305456040c0ca09500191502c2d10501c5040e003c8028000903000306604148110421000120f4012a400d80e03410290800310108290403114041c040c074005141240c101030340e840f0740c90950754400c00d1250100103400c6c00c020500e58180444414094105547c0ea94080e25640f08074000b1540c1c40800c0d0320100c44610030b4900030580038802e011290788039101d041e9461800b4a40b01d0004107501400c0303842034001d000d0800026400141c81403d02149051a040006034030000445134003070380b000a0045030404c2c4040c01005086c3c6a502d0507102016001c003c45038822900e2662502c6010101c0d000c80c0720765944001242c40e100c1c0d44103950724020b0101c641c499 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 632285494 1250 632284244 632284249
    0x31501151209021c020102010b030f03190e030a050a02011407020607060e0309060c0f0d0806060d2a0509012a20190e01050301020a09060f0215151206090d080a0b 71
    0x802c0941d1450368041201e8503802151fa0a005000710880110f00501c0d25940d1000c010761648209000c0c95248030a10119a01d2103000303125170380f110200101601e40d404101e00707000f07440b01c002c018100d00041e0010080380341e0707074200f0050701c0c001074003d080241800c8951340c50200415041a2a202034401401303020615940c090040103000301d80f50103090104008005140740c2480d0501480070310501e6810080d03d5115a01a0303440e450b1004004640c1e103400199441159480400010140300110341401e00c942c0c101000703050400003a07855003032800300c91030f141150107210b800d85950a0102811074010885000752500c258201c0182e0984010020300011155801c3c94100200b609002c14100150350b01d498241340104801c0c0c00030b43c6440102100180140007501a51003413207148030f00008000d208018030000d08041600e04109414481e220b015501c00c0c0e07060061013003030708680c114800f2402050b81c500850b41340703005140c00d06010206a544580003090420303443c2d5916011001c40c1d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 632286744 1250 632285494 632285509
    0x160e120109170405040f0204140603070908030f0a3f060f0e0108060a021c0e0a020d05060901182013020403030c0b090d09140117090c03150115120902 66
    0x44810084541d01d40c9802c4c180001d45210400c0f03140d22034414401004a424007442d02c10340ba050495140360340380e8600105a400e4410760300719288511000c903d400402c0c0d400b07001000c09452944800311a4000c0301800b80c2060003c41218201030a07046034800b0001700c4080b035803001d000440d0045119511303090003d43c00221944040d896450460042000b180b050110711b401410b540415850840f84191a030b44900306803102814031596142e18200c41c2d20140a80f0f118a603008010610301c2071700d410025950315082e20001d85652074940d030442620a072080d1981d419a00406100050039800c280c2020b0724040180180c205100d1410503404890510041c07002d50b1080d280c103d0400306034100020b1043c401405001e0f260f1209809080b40c0d50072013000012581191108040e9000d00380040312410b419811301400f419045041c0b0241100100d8a0041c11400381c2c211001882c0b42c07010180044420322995505104080c506039941d8441c112200c80f02d076132464081011180c075030116424 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 632287994 1250 632286744 632286773
    0xc03120907030611070c0e040c0302031605090106020c30160e06010e0d0605040201030b030d03061712180f1807091a0405010e030a1a040308160e120109 67
    0x340d03005460180100724182c8074440c1c0031300051030a242040c02d107a48800c8166810f015072041c1240032800201080201300c080c0c0c01841e4050b098a40400c86404c4544100025006042c40303004500c00100300303980700164003164240c00903c9043d03201c000e044180034600c0701041131140e81174080040030040385c00f003010aa4041001001d2540603141501e000c0c01800090b0008c0e0410002b040105015501d045610104940049000440da1902e03c0160001e0170b05a4030540c150103007112001e201034040c0e0285003252010300b0201079050010109036100c0c007214178078007a544801d21030048808103025205038940e2022303104560712540307800003a0015090074840c4420b05101000c025009030b000a10b03030018841c6002090904445005c0b03404140950700a01d810410145800005598104a160039081d0411100030600b0a00304c02c0c41354a920880707096021490007808100318950b038800b0204012160342d54080c2c0c4802038801c000b0b440c400422160000c1d901c8601c240e003c5046240c2d403110 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 632289244 1250 632287994 632288011
    0xb0616111f0905030102210720070f09092a090227030705030303150f062a07031211030c0f032104020603040803060a0306050702030a080105100c0303020c0312 70
    0x10000002400d100050f081540640d005102403014a0b8890701c603104c1c52084100461a140c1d5009012600348203103104402101c00c9403840c148900b0004542203007511041ea85402080307032036901100070b407910084005d11130001c9004030580065070701000b4260143c61940700d104144d44002d05001c0c1c1c0c0251100c94072010364180c4442e40341601800ca259410810b5000e40a80c500d80710010b9100e0000a040300b042a100741c06111403036850131201c282c0100c008101d1078403000e0700088405410980d08007000ca503456803058840343c800009402007103070380c03004440c0140e449620003210194500e06c00f25000748014404d1501c2d520b400e101005804600800640e01d50041580164001b59190b46550806c8500c405000c0942c9480046a41c800e4100d11403907569251000400c40e500c100d030380080d050500c0c10007800405c86d4040024140c11545580342442a42c0fa142000340b1140818010404105900070400000e40030390040c00044400105a0341800c03c1070324240c0011200f100c0306407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 632290494 1250 632289244 632289289
    0x142a1c030537050606160609020301061a250501050901050403090f0e01121a0103200603060d0b040201110a08090405102102040f110d0608010b061611 66
    0x107844040303402d91030010401151a03005941140d00495a00b01070405041089074540c0000381c00c41c0c54040481e2201d00c55404c02a891403080e081c07060003484048003c0384254280000040d104018908a0b04614041070703625103409a842c4003c01007406501d5405190b0406422120200d282840b03043c2c40f40700300318000302d2245050302c1c0003030100d803040c1c01080d03407031072141c0d02804005104070b201d90545540d12030115603680942080e1420440300b02003640035500ca1000401007000d0004d51501d98070020040d80c00603610441000310798002192540c0d004880c403481c8101050081aa0300e8000d40181080500345118140180c00d01c02c4c0b400059401850014404007142018400c01d5409040003401d0102c3c4c900b0903200c0302c4800001c8042d1740403054520988025560f40c0e40c041c08110f10a444104040000a1141c01c407581042c03184460461401c0741c00288814180140d0008080080400e07180c110894804040c880d82048280d816410650780c5104540315980b100390400000302009 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 632291744 1250 632290494 632290501
    0x605120a050c091e060a0509180f030a0806270106051b030901140d020c011a010f08010e06011d040507080402130c080402040509010f0c0f142a1c0305 66
    0x61800c2e4002e50706a006101803400c2005201c600034100c0c0c031009000c00040c444da21100002060740c1c00513000706078824940014031411101e12407060060100b0081981d03400d40200007010380364003c0807001c81c0800d200f080002d05a103007171501d80c01c0c0081c105071801001c541c2d05801e040400001d0f00410041100046c0d800c500601c0b925502400c1140d8a0041d49050080b500007010300e15003040340740169001088038400900355405035201c4000003402048040008111002d946442c400441c2c04101d107030012408041c41101450306a541240c40000300380c0b100c5004503403642004600d03c0041540304144c040a0f80c8a008070b501401e03ca60311a1550f00b003e00400428a03820112840c6062030720300320328400b42d0424002e90340980c0403200000c00f60785440c0440d0260001c40002c1540c50b00d0320030510045500803505501c010b40315554440c06003042c0492010702e114119100c8401603901e040021202c1c4600d105c040c140c0800401d4071117040c0762803001c402c2080703100c03020400710341c454040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 632292994 1250 632291744 632291753
    0x90308090429011202070512280201091203052701090204020c1e0a110118030f0b0f01090b03070506070206210a2a08092e050a150b0d0605120a 63
    0x88145111301c1000840c80c01c0000d58450f0b03590340d4000802001c201010071646000904104428404c5110303090060f41e4052180000340200303071a1108032288404101c15001161007840b860303103e803484036080f80f1000c44840001600154100d4030140b40e40d02e5214034001070729a07001038007030410301d02c00030911094050085c1440c60b014003e039650030340c858413030003010525580444000400a0800005052280003200403451868002600300a13074407081008118241c0c1c00d940c414545000716010a0341c94090040946145507003040e03041e800300c4002c3c00075140950080c0b07261440204518540940340e10465240801004d0007504d0007a14020020346400034080c05010080d46805d01c4103101d100054852544011080d40b01086038140014030843c0d03007084504503240c0001c22280000302140c01003c0622002081c00211a050102151481455009540400c4136080306400c48904008103d0407641021403c03031492030726420001440d461300c6040c0c851001c00600641018509404c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 632294244 1250 632292994 632293007
    0x6090809030a081e0a1205040f1a07080a061401050903071d0709050420031b03090d110610050d030905090a02182e03140a0516080709030809042901 65
    0x6202036140c05c0040391080d650204130050321494400001900d61141d08001c1d00341d02a54000900b408000e9000618055040c0c0702180b1a90b95075a800d500da640300e8844070240c40705413051070084231031080c1010b40e540c05000a0081908090304031610b865607041e500c60781240c28042d4181f04074064050003041c90b84025690080d060a0303c1c28480c1e12a200d03440392400140314181101d145010000c40e551407015400303032520b4403241081c1c0f9180d00780611b0a649a031401c291203804220007aa0500b00c2c0240400c5c0c1d50f00ca906a00c1c0149803041c80d00003400301c0030410703000440c1007004410001c2842e545203140c0b240644c1c4600001030b100c4030150740b800b6190444c210b1280c8601818504400e20802c075941011160f071816041140c203100d000e0301034024281418040c03440340f0b414000c0100800c0c2c03a0340214030803c864100300c11510841c440c1a500d4030029141c02d00001e02c500414004134414100070543c452014000003540401000340307060044510300303200784103110244c05520560740302c61b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 632295494 1250 632294244 632294287
    0x10c0f110f07140118060315170d0c030507051603062405040c0306030206160618170729011a090307120809060706050901230406090809030a08 63
    0xc010640751074854401a0b640b141d900c03482d07003603210528220401d640300d60002001280303500b0841c0d24040d11900003802610303036040c0c0030130749101d407110002c1e031440b515141700f01c41008500600545040b07618100c1d10092600170139000d0007010421140003030001c001c000301d020f0345103509000303a5085203091010394080c9044000c074400d25010240e410907083d00210106c03070049400148413600c01d20701b50050405540b01943c458800309801911a04000d00d90814a10490042050b904a28801d541c19509010045d20403d07582040c0081c0907415401032030924002d41d13010b447c489110845c810790030804460300700c1d940d446200412501c03800c8034042d8481d0390110001400c6c0041200441c1da102e45900c944407ca0314001b0750b09051180074401c43d00d0300b69000e0040b03595643c207410303d80060b14081d500c0806030341c640440380200c0303003100c0c2d03c15900301e15101c040e8074180c98035156107000d804035800a40b00305130100900c64031980d080204c43c107210f01c1094020b07100c05400554411882610 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 632296744 1250 632295494 632295527
    0x11011403060f0108061f02010f321b031503070f18020723030a02100b0f0f041e06050103060510090b0c010f0c05030921090f0f03010c0f 60
    0x2030091040540d10b42d524412050070a203890b0303109540303510010706c1e80c1440440070258200714100c140111907064009041c0041d0121043c0285003080c011403c3d14400749000600e00c04142c104120806d03100103445801850700c000c0c0583c40c45d01011111003e41c001d07521804512500c00c00b142d49410184801c100424100300c0c00c004191403d024408543c0c007245600754035030b40c0010751300c00304a05034442e510010274056403162a1855aa851642ca5102d003425402510444442003802d8449010360154010080c14401c0c1c0f40202101f80b0604110412407140d00980703c600100ca81e0389903c8450300c0c02d072024a400b041061405001404940b10b07500054041c042d50f040c444002c41e0003400c8042200d40b42040c142c0e49520031480c1500600c4d110b44402401800c1941e4000040c3c0c1c8000074501546240c000c0d1290a400382c8002c202010441030480181c02040c0300803a05844c0c400d88a02c2c00001c0504010b00d844048800a801c4a504082280104200692016800c0d07400300e007034407114610 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 632297994 1250 632296744 632296747
    0xb1303080a0603030905010f020f010e03030106020708010216080906160305030a0c05070807111804060207030e031f02090a2c1b03041101120c0306150905090f04020616110114 77
    0x31600c4c001e00c04010360003502c0c140002131500d505d0f100e100300249800450210000c1046080080b8560340700d03071013881102c0052040b0304011810304030610032036540b43d8074050070003860305565403401e200d50480c03c9910360002041c01a24000d040c40813031500c041d840799955598030322348072113420202c4130302c0c910050410106011050010310802c0481c0d80740754214088007902980a030018071006030504052100701e02500901040000d01d0300505107252103074441c19603d05500302410360350b0602409044001720800711140c00614141e00909080300080c0c40008030704e4685070b1441203020301c1b00c0080141d881120403655072405020308036801c40c100c20412600151290030101c603602010308041c001c4001200c141c181c0b070380948000300c04090301c1802031002001c00030700940180400e1103a481070343d00070760030942124400d01100040d01d50007440c500d01c58552044000e5030090080080380c000750100481180350b042c00c10075880c880d204101c294000c00c03101c070004000385542692106007600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 632299244 1250 632297994 632297999
    0x203070f1d030307060b0303190206161403040609050709090f0b15210715110c01021906020c0304050402040b0a090906051305060310061508180601210b1303080a06 72
    0x3400f10854100980000c0089410803091000a041d44624504440340d0766060070308408103031700803030b04074451b041c3c80c0b4010000403190242a980c05d10550b00b0400d80d80010800240040c510358000705015014200b00d410031900c513240301040b284c1510b420380ea030b0380d0f079590407400700401c01c0e07034060384007803036094207007110107414046201646c0b444030307100060030b00c50904407413842e003002154018440b081d08225590600b01018145c40d4541524002c1030007000d000c21810750001400e0003194a000010108003120f54403020029008000b105440e4042040001055901c500140c005403503c42c000380d9a071409494003600500e071584c042ca00c030604113001001580d0f100c03011415101c5490310046815622540000e04098210700d050014524000700480c0c038154800500d0b403d00c1141d00c03010078a07142c0f403410815401d420b101d1614182d00c02c00040c040641402c1c652071028006a8070310720240d40702d90310b11002090880707204204802c18a1101c05240c0c2c4120318680082007010200680ca0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 632300494 1250 632299244 632299249
    0x902040b09120c0a090b0907020a0503250b0705031906030503070602160b01030b07020f1b1002030c0706050909220822260f0703120903060203070f1d 66
    0x152081d524420b400c60407071001420420700c10300c414103030b008140c40240f0303403203090080051400c154818003480c0e0110009101c14000100c8192803900a0004c50901041c41a90320112022120007030450040002032400503c041d9100c5d8020380142c1c581580b80d1805226085014122800d845036070350400f4801c03c0400d1000c000c030f0f051244c00c4200545d6410f50503080034108602110b00074000503000c4000800e015000c0074445c02032090345e080e160044c040d1807600b680d410b08415030340c40800c07861040c12a589803c4a5026503451140183c81c01d1410266205041078883c1c1d2141010540c0040c020307545280413440d1981c0124201e40300481e03003130019040801040da4140082203008005600040b03e0100c036191605182c03c0d03c1407100458031281804000803240300c00b4024044800074080c0f100c540865440911200c8100920b01c880c51034031400f21000c03007010100240080c082e000700c045281d90006500c141540d0701d840042100340700c8000c12581056550a41c08503070041c0308480c95 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 632301744 1250 632300494 632300497
    0x5010f05091902063601140723120c0303010e0c0703022104050d051f0203010308120408090612190e0d050c03040b0c070608090c0f010804030c0215040504060902040b 73
    0x42d03019a2416103940301070400c866242504500036130b40d2030070b42011811701d0079010b811041801081c5c0e14460b100c007460b07800701c0c0d0500801000904410032944480120024071200c50610180341040b5200d081c5003142c0e03034442d80d002811154050700004014022510303959206504182650740040c50010740e03441c000d440e41c02000c04d01d80e0120002c100801c1702142c20083c3c0340030b02030040c0f01000f098200d141c4203960300024624030312100011041154819420710a8a04903904000014038007400c9034448100488010310803030381d03040705101044580d141c0b0000b401c3e072484403900b1170700d250420045541010642c00c0406500e14105002c1202500000c0344540c6070414a023081510380d0361250310319040d070203190031891000304045124241c181d80003d1072402c07030302c00713444440c4143c4030b00c00e00c0368464219056060b0402c0c0e42c1e904c6200300d07500c0b94564903400f41c020b10740510b18103000e50014a10f503101030490050154042018801458244959401000341080c2140b4262404402940a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 632302994 1250 632301744 632301793
    0xc06020f041e0e0105100c022b05010b040b0117100306050f0114090c0d090503090409060b121911010e09010609090b0f10050318030a0315170a0204020f040f0305010f0509 75
    0x41001f41d44a0381d0840d1500c4111a5180500902c20009889407000d800c510001007203040d41c066003021b072003a6060509100e03901c408881070b56110005912048041d102e0400984428445541d150001000c2411031007454003c051810384400782e9490680c80b03061586100e48110b2099030084144281d04481000f21500c0c141203800100700080a401e10b0750440c007851111b550440d04200741c4504001c07695004100d60a01150b11084001c41d07502c92a684d03143d98090000601d60005101010034503840c0541d0440b0b60515000c844981c0c42d00114070b2103042a441200411007070141840254132500501c04888420356002c0808400400001c0881e8425010041031000010106294400c503d014100c3c0074042c00c02c80e17648590702180240105080044e06040a01c1483d011810ba44040041052080e0760002403900d0525070702004025482104490f0144030200000038046420042e00b90046018030000140c0324142055003095a00042c4a010740e5084040c50506403401d1400981c403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 632304244 1250 632302994 632302997
    0x7060e130b0d1211100207120c031205220308061c0b060f1206040b160518150c010e1b030304030b0a02030901090b0c1e09010f0c06020f041e0e010510 66
    0x4103030f086444240c9039084080078aa8003406008135608044c00240c0040c13000314850b440c015210081040c0444110410140c014002400045c1560610328241c00454000d001080780c3d0161200c200541c80c903048001d4800c4011460200410070240740550802440c2801a4503540f80d00125685955400c500207000038030600d541050a030046e120041c86100c0c0c40162402c48504d818141020050480101c50801f0011114400044010b06c2001a140d08181d08400c000f0341c1c3c40c2c42d004001c0017055450b46500071420900013040782c600240965a851414000941200142c0c01d0125001c8507030560190300a901c100801c00c001a0043d00b45075001158050040c6c680d220088241d000d40303046203000d003114131450144450504003074000d10689001c078840d403e081c0401c1c09100043d0040c03006040c0428140782c0460350850160114074212480782c42c0051605240c0310352950103400c56040140808200903030029810300310700340780c0090000d040ba03181e03c540c034080010320107400d522102d10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 632305494 1250 632304244 632304263
    0xd0305070e041e02040b041401020d17041a011806090b060f0d020c03180112050f0106200d0906020f030f030a0b0f09010608070e040603051c1107060e130b0d 69
    0x40b1040c9982c100001900303550f1041d036070f8540d2010101c81e281c0180c010030a460080d1680c8008541c00059030a00c41c1900e900c480c4505c4030250b00c140854400248280c552110f403000c01703075051051480d81c2c0d001e015240c4005405d008170600000c211403182e0860140340703240140680c00c940c0c9a40503940303404145c4948c2651000350300c20b400302038055803889400c2c5101c0407a01c44c1d82c80c03003002c48110b40600e003a40c0c1c050a010a00c9a08002e0315403c1d81d15556000c401d00050160500c2500e0b0b10b03210704005454605400041380c291454180c469900b034000500320001400490f40c180a5014650501401142400c1039074103800024400a0801c01001da51810b000c0c40340c1c1c4034030a0b40000403000500900440da91404c021740390740c0c0c040351100006940e41080e4245442d103441740000703503074000c0005c0400300c6441c0081c3d5180080745400000f44100c940b0004400e410070090306001d01902e40e2216060081c0c00c0601c1000c01014032410742d1b00b41071500c0e01c08039440c1c001284290580048014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 632306744 1250 632305494 632305511
    0xa060e0f0a020f040308131401030911150f040927150b0f03060a06050405100f030b04050a020d08071a0f1504060807120b0108062509150c050d0305070e04 68
    0x15aa41305076800181007a40100b841c00c18a408110008202c6118075901c41c440000600114102c4952450007802c1c00c0d100c404221850400505141d45c100251018600e0444ca005504d0003d4100340d1010800715166041001071503800703944a8015402001e61400044e165070b50f012a107055400d84084280d56003603c914581d5584604281d0301c8030180540f1540d081205030b840280c070b114000c0c18080c07400c0002041180712144444411604503400c803050180c1541e075040c24000c00648261128410003040c0809039031051140d41c01c0d9481072280640e41d2540340340464240c0c600c421086128841c00c410450b03402c11440710310f5440540c0c0040287d100c042100014014200380d0085c4007035128004010070b4929070643d0b1245524041d100c8010305a070b0300c600c03141c4c3d520400c0f203490300c04402515000050046a1041103071068060420001881d2603e11151487c41e0b4900c8901c0010202c40c180e5040c03040c2400301d0000c070303030312454207002da403401420140100c6220f8900d01d00480e526481c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 632307994 1250 632306744 632306767
    0x10020c0d06150906060302030609160914152704200d060f180f02030402060703050705070b0a0804061406091906080307111302090a0e04150e060a060e0f0a02 69
    0x20b182c040c00d080141044090b498030700040c025001114440d0041c83c040e40800c40058620500001c110403075a0b88807281410710b03c801d131605483c01ca0035038111180d1610f0600304040754000e4205007101241c1d041ca403050284491200410005040380540c1c0b030038507100200210b8000200743d14012107030040d0f0702c124070f140140040285a000d294940c030040c0c17000c20340b047c0102c245144907900f035805102c1c02454a407404102e03c0181d40c020b50001080050b000040d000d80041c0201c6c600038000c0d540c8141e510b058a000b1680721400700300019122108100401c004e9200ba0a588400500075504526014000c21107502c1c0142c082108400b5441c43e10f42c2c000301941050000e061070b0b009803a1203a4003881e0405020f441c009002c0d20070384580f00880d245003810b1080c1d440442000300620203e5150035035070416254003034000d86075100384806c0225584400d0041e032422040180043c1142d180249452080700d86a400c500c85070403154060100c0c19000015140c0c0062000c0401607941d08258032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 632309244 1250 632307994 632308031
    0x10207331e0e1816110610090e03040f1d0919020609031914011b0509010e2710090e060c0a09180f0f02040312030509011508070510020c0d06 62
    0x200c00b910031408030f0420a0900c801c0c20070141c229120703154592000d055903912a1906811602e084160b000c2c450100410741c002d8004080b400c0040040c2c13864140c5540b4503060248984d04904482082c850707003c0680030b80d0025407a484001d40c00503205d50031030440d41d81c41e03806038000080c0c81541d0201e41c0b0707070481d981803020314085c44c2c034104c83c40078110703151404014001c08401d11454551904280444400e680307440c5481e5a0700380d590340e601c6c00e403500e0015104a0003040c0580c0d0800705c1c0c141c0700c0307031814040c024480300020741050b2441140381c145681403041a454002441e19820480c0422401000043d040c0d003001b80788a5964a0b1288082e080b115101d90f64010041d0110112000c9111640b030341c8a0400c0707200741942403000602d58460b403c140e03c511310005056180c0b000010107000d00c40e50240340c11150540011500180d10000203d17408040c3d007010b41950000c0d0b800300004d1502e401200c8039101075002402c0490001030000d0640b0380710b00009450702d51100c4c402d4066050308d86 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 632310494 1250 632309244 632309269
    0x409030905040903020f1603050d081b0301090f060f05030706050c030d06060503070305010e0c0d0c03060503030a0509120111070b0c0c010c0c12180b09010207331e0e 73
    0x901c1000f54588609009507035000c02c4949030154022913103251510344c5031080041c29244c0041c01001c1420396054110b0b20300c0801400174480202c1840030700c1134001d04000850082140c86004110041192540d030212030080e44044582140d0303070020001e40c1c801040420449485003006071b2602c55228602d8107500c11840e0030700030b05107044008901590481c0c061030040b0116501006161388821584204900644042c020400c0910010407403060540100d078003000e80d45804139660381d4610119241d5000441e611006c03880104000145007003143c00310181e0b4001e00021300941108200c0d4202a12400a014101c9880c00d00051050070f40f51080311200518000200140c070000d00307008041f4400008112415003500b80c501e034140344500d00c00d0011100a24240c11441c0c58403a1040b965840001c00c01c1c1540500540000c01d500402c282d07555140c44014070781850800c000b903210840740a0b01440060003840c40e924900c0c3e028003014401d00321110704100084004034000140024401e9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 632311744 1250 632310494 632310499
    0xb0f040e0109091502041206050603031611100e10050c0304080a06050f0c03040201020c011b0c030b01150f02150a0b0405150103050c09030604020f060f0a020d09051e0409030905 78
    0xc800014110302c85a100c3c1000b140122101c04902c00f4814111043e40304901c10b00102c41c400b44401030100310f036640102e400400c02811685031036600000c0d150f00c98114001541d2810700103842e0b00150a058071a602038241904e07104480300c00580024282403680e0501e4800c03c01c0114007a104a003040040328003404094048410410f010b203800c101a140c100c2c0c40d00110284900451340c1d040c014001e40780a03550507005001100d140740c004560600c01246184000c418408012001c1600c40030322102460291608005560500090140008945017104200003210211542441d8042440d903040c03140c1c1140d404103601d908032034501a18901e202d081e4024988014400d0b1840d5256403c40014030a803800d000d0b5544440c100c1e1400d010326040580c1541210f0001030040c5040b405070902c20754014800380c10180c51115581094110851903c0540d02ca040017101040d00641000d004110031034100c4800c207802c08d100300b410400608114015134641d80c0d04002c050051064102a0801 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 632312994 1250 632311744 632311769
    0x3091c0303021c0911010503041203050c0913020c0c010f0915020c040608010902152a01020c0d050408011808040603051003120c0312060e0c07030203130f03050c01090806010b0f04 79
    0xb9640404002c01c00c005044541282c080c08030300c05540610188c0f4859a049100080d02e01c80da60400c2d400780500906101c10144100310306052543d5043e0803020950034540016110394620034204c4c0791035420f0360b00505012040003116113650b84020b014060f101c41d0300442d400084541000c0c0e1500d010070401d00d6200382071100208010505601c03000e8010700883c3c54000d500c40c0103c12482600c0781100505d840709400d00a40e014555112000e06051101c1000500d440350400e0407a040c01c6500d418800001d800140c00c0000c0d00d801d00502000766900320305800c3c00c00c450795900d44035102e0ba10985007807603117030030000c3c1d0360010540f0020700540c0c01800348000c030031390340d05c1c010031000e00c842085000c5140c104400703080c00554881d14090b6135200130282c5041c0c68841c1038100036041310303c04404521042103185400d02013601300c00300400c00c52101d2010b0303504503d01542420558602c817410441d0000d001c2007400700008225044401c20f100050b516043d00450380f009100315002906000d45 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 632314244 1250 632312994 632313037
    0x1005070209360613050307020a0b120108030301180906140c131712130b130e1302013005090601050a0803040b0307031d0a060c1103091c030302 63
    0xd95012285850380b280694011445072000c5000d03214034480d000c00402e40c41900000c016403c20b85071035032501d024508607407c009099000596a5034283c000c3d4400f410081500d141d40d0b2000d400750b40c05445008043c6003191f040c42291000c0c0c010004d03080e0381d171549a150245c24081d669205000d0340e40c405032103039081d10305901e0589a940c0014050b000700d00c180100010f00c07004280d000c007035940010000d458142ca0444a819003500042c0300303883c04543d01480024800c845000034880500349900b01c0443d949428803d0040ea00000c010140001c0320000300340042c1c1e4130950501c0c8540049103035070200301c071990181c00c02c40c111450f10480245480c042c890442c00009003141282c5003110549540b94582e0b12054482c06580700d0285084018070104281038041d030000b481c0441c1d19043c201206044a540d50700c0c0c80e403505000d8074459911201000030301d9204203519200788002004500e440d406401140489103040365940c072218030918200e003010b120350120360380d409983d05200001c60 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 632315494 1250 632314244 632314261
    0x60c03031109120109021306030c1719120305100b03040210032003040c08070b0d0f09062906040503070302010e030307050106030c080d0215060d26120a0501141005070209 75
    0x1520b17542070380324810080710545c154500c1d0080d0750607a613010003042c008528100035070424031650f48001c8424012404107500000070740e03140421b000d02550070001070300b180180103400c42d00b004d000036500c00070104040c00500134103001c0307070b81142d81940c0e00d149094482c00d04400426a0106416100308102030310b40c5070380c81080240d8011030045030005909603461840e41e0b5203117100d12031107085940502041e03215004076402500d61031504680800d80c503c46995600c03c03100d582d984c01082c900210316002e251800ca9190310100e241c10742d40719151508010010307980310605d100081c10001e24600850030740c5c506005541b05950b0101c02482155100e18100242003614010340c1260b1040880c00c034045072000034030044c108200441c1c07194584a840502c900d184040310141d9031641d0755030851440483c4c0c040035030484184604800c1d101d41500502c00c6440c00701412280310310341810014840c2c0c0382001d1030300d010600201e801c6612031075907040070780343d5000c0c45501a5000703080c6410440b03d40d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 632316744 1250 632315494 632315501
    0x507050705030d090911040503150a09210e01030507051e040b0304080a020d0309020d140309090c0301060207060e03100216060212250801150306030804080f070609060c030311091201 80
    0x5e5a4a80040c00700706038002c009040c50041d0301c0713001c0d4075500482000364a0000340d640140c128241000c0403035008105c0e00c0e0307503c540b1862059507150140346080610032941c80307004c0c0345e050340003460b05100e0750400403c010483d005a4000e201591551501c02c129202550219402054180c00075038491405c2d0a0918094004081080140c000d9030f44658800f071007803091081d02540240380384e03404130301038844070700c081c0045403480010f101c00c0000354110b6403640d520622684450f89032607500e42c142080203041c6440c40c0c0c0301205010195401048541e008a035641070041e44e460700688070b0340701200034888810b8041020301842c0c130000d8030030082c0d440c4a050501c146844907444001d460b0b456500141c40d02c10510303c42c0011160b100600c8030003000301d03401d24200e28500e4049402910b0752a20300250b031040d44800d08651000b0100040b542c820311254004040a04101c05660310307200d0042c20408050000504140c0c0d83d0045c02d207014624016101c40c180090210100030003443c0000740203 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 632317994 1250 632316744 632316749
    0x1090209010305010e10180b09090601050102011b02030f0a2601050108010f120b1506160212030a02071206060e0c070c090605010f08060a05030111070b01061d010507050705030d09 79
    0x3400c00c800460300c50030418001c0c4c080c40c4e40c015000c4482e46030118201c22001130200c1d01c00301680340c1e041c40e5101e694002422b0f007c0e118503c090150365243c48006030844003580780702c0700303050700c2c0c40c500422642e00807003035036135030070821007050741e141070040c001c8070190554130742486145040e00045041010807062103040e20000e8856054030390700da078420543c11100d4072030304000e030f081010104009001c2600c901c0d00060810758202c495041180024004d0b0400a030342401d08003620440070039440d02400c400c0c01e8003102001b561600001f075100a40303906160280f807d41d000084034880800c4000d904c000d005107142032500009007411980c459843d8812041613070548200c440104607403c0c6403161700101d4105854221307040301c2407801038980b85801444980e1107000c045000445840030301550318000f900c0300d61031b507a8a0356841c02c801c51640603040380781049403401e000c04984164500e181100da009082654903640141307056032134000c85812013a00f501400d8180d00c801508606000207 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 632319244 1250 632317994 632317997
    0xa050a140712030c0218090c1503130b1b030a0609050a113007050c0f01141512010e0f0d11060705090d05030f0306330c0709050109020901 61
    0x200586046229a18151409455465916608040b000a0040000104891020b0301e0010b41d480031110180e40ca0004442c411419048000a4400c030700e00643e04064465030704588506506110310160030700d40f081c21000704042c0005c00800d03402850454030303410003016919455504d20744a0300b442d000d4011031080304ca02d2410b05001c194502028007032030401d449407008440c1045101d00703000c2d002c1c80120042001c4022203a19141c980000182c00c64420381040c0c403019504c4e0038424a151400d00c02c80391340100360745001003c0301c05030144001150049041c1030151281e25000000400f0030a8031103400d4150740c078052500c01c103410045090b40a4810a8083e00c605680f900c0c815103540030494610082070b0003d000007950640514098400020040d000c0d10070404507950701803440d440580009800100481000814035103680401c4ca02e6017180c100c200c03038501d400c0c0c00c2001c288041c030b00000c010902141c0030351401400c100210080020302018803903961340d0800c1d10b00075448580806d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 632320494 1250 632319244 632319263
    0xf170901031805060a05072705010e06122706100302012010020a0302040e010b0d18120e01030f06061106010f08070303030c020a12110f0c0d030c0c03050a050a 70
    0x3095104541c00c18086543c214018014a13034880350010000c1c480101900306201d001c005540c40d2102040d941d0860841c0d130a2011010390805001402c40181054581d2158104200c4031030648200b0360140c1e041850340c4820b500340300d03240d580b0060440b80030100f100315120304c3d0100300e407403800003140700c085a0013a01c40d110000001800406421110503095240758440f0711404543d0101d5070080440ca0000e16005060585815010250103c280c1c400c0c0620580495440032032806880b502c5407040001807562401002580d41c012010159080d500c24090580b640e001d440c1d019810081b5142410241000050746441c40600361080b40c00898002e442140e00204d4a0070701001594183e46c0c45000801c11946035980c11801740c416460002c0c00c50045446102c001030f15003500c07080311650340c1c54440c0e078495111600f9103000c11440204800c0c2d8442d1040440c1500c0700e0401d070780b1841d050300e803074034181070a800c0400001080340c1c4000e2035442440300b400d041c4000801c080d01098491b5000741c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 632321744 1250 632320494 632320511
    0xd020a090b03160e0d170a080702010603030804023001020703030b0a05011403090f0d1e0f050307050d09020a091b09030203070909050c03060106050408010c090e010905040f17090103 80
    0x4407024002280d800c40c2e0341a0000701900fa0a003e0505011511030084c44a649a105a6141c02210074403564100403c4400f003011800d442d004402258008040d1000f00005441d544000b0000080a40064050a280b128141c5444642560541c1d03500060809050207566001190f00035409610240c001074a407022403422850f1508884e0201da07416907440c1014024400c621603503070b00140004030944580300c1e100c000f4a80502c0501d40b10000c1c0e44620a6200741e900c42c03d6200424002e62104003e001a0701c088407e40013001c1d203030000c800d131070f00544403542041c00800400401001030b51003101d54800041d80c02c220341107940b01c110004086002d9030381c0284161586030300350100175416000500f040c0320403070460744103507d4180a001219103543c000740c0400c0c01d180003070700401c0c0000c400007010b00c01902c2c00d009003400e0400b1f5240046a852130244189001141070144c240c43c603442e040030909000f05d80300c003a0b08581d00940c25110344042d070352050625078400f00c2601d01090506002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 632322994 1250 632321744 632321759
    0x204060608061503132d0f0b070315091805010926030c0f0313060c090e011d0a020d0908040618050a03050604060b01020708030703030203010815041e020102120d020a09 74
    0x80c1c0f400307580c1545a0b016542d010359104285110f18070350b01d0440710301036161503000080345030704150003d000f500600740d00c080c0340c10f090035441c3c0700408203c00e02d420300109007032100d06414040d040300e336401d1000460500e40345181032142c104010151044d030030b16a216040c0207079010441c54100c0c502c0328110b01d09021030702c40489408202d078503201c030503c2400980c115113540300003140d01440481094881c080280d8803501102c494000050028175244c00c1070106040104019001d06080d40356101c10150007407450380c2c4903034010b000340f030019008543e80680e410309800400000c0d07070102d107580e10b0b070341c444600800910b4001d02d00003044046117000175580c1000c0d0101c405498001010744015070741c64175a00043d01000e24614114481c165001a020500b400a001d600d403003642c003da541c1d4500207405180c0b00b8400000c1d0f100014410174007000490500324119404111313440c01c1c4441c41640010f03404e02180d8511005012000120740c03100303c2e980d5009003c4160aa115003490030b841d00394 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 632324244 1250 632322994 632322997
    0xa060903050f21060a050a12241a0418021306030b01150e0406060f0c0c030b09100506120a0201141204060b100c03091403012301060f080708180a02040606080615 71
    0x1b6958100c00840c50910141a16901c0000302c14012848800d0b01c200340b030003002480c1c0f803000c01038061668a0f03444840c0442900542604000120f0b01441070090a60061940403050303403000340b0856401e01104040714581c0c00c591b0040d90803c0b0006015030b950050151000b01e0342003554005118440380002c1c7c0d240c24840d91007a180d996035035000b06030a881c3c081e51a40c00050042d03039110040328000001601e4200303001e1140ca2650302408011080c0c240c600159040a40524481d0050118031840c4203000690140000e0302480c0142044402c80c0108490380314050b007512840304020104010710140b83c01000c98540d05580d183d451000c5c0010498007000d1a88001b00054103089042042c91441400b80700d02c40740c0100000754078a50b00c81c20305995000802221803003000380e401005103641111041c6d050191600b0520041e01d0043d400074405640200500000403001c0707801d8103082420000c0150003070340079000304500c1c0d031125005044101c040303503080d10800c3c581000d5021805102d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 632325494 1250 632324244 632324249
    0x102030403230a0e011d030601080717010e19020d0b010e041403031005061e040906080c090702122503020a050d03090f020409050a021c0303061401020a060903050f21060a 75
    0x156107280c00030b0384c1001100d00c810342c070486201c071852a0039803005640d4107000f241d000745004002000c4291030000708240c0c410304240c5218007070340341928011140c1d0300403408040c034005080b44440d07000401c1c400120551403102000c0d001d079803040000702c1d01c40c104005240c0a207004480c11003841c000316480b41d54030b20044982003c1d00c1e903000030410a60901764061310050001071a860064041100341c0c201c540c005500101c1c40640310401008010350a00c00c8001000060b40d800d0900c0c640300c503010b0f6858401000315007000d84006251110706145640c00001c441a101d6031400301c84036420000d580b03040012050300c0500403068850b11480c082d01c12003460707503440103140985440076000c010003000c1d50003064920b806404000001a92801e500381d092405030485a0301c081d185090050844582d0f4000710241c4410342c281c44a140c0e000280079400c03a500c40c40109040006240848940c003c2d0b2022001112002c15282d60140c841c07907040040d030804005a01280c0c0c1c1e114100a60a1840e1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 632326744 1250 632325494 632325497
    0x1091508090c0a2103020f1203061201090c171228030e0d0305040503040510051b0309130515060d020c1c050f0a050c0d03060602150609010b09040b030102030403230a 73
    0x526150464004c0a404a034002c0c01135036101841c89804900f8115030a505c0300100f040002081403902d049148802c03102c003e100200400302907551410707201c00680c040d2070200c0c4008110740c015481e00b0001601e4202c101c0c007100ea12590074455503101c461018268003000b106c0341160f8500b4a210b885080b000780e01c8031005203a9610003042c00e8004000150051340d882c003041001107055241d40c600c0e90074142c2e060307540564030510441c401c400c20040003a401150303081005400d00c0c0f542c44980444000c0da100e0000222520383c200b41c0d9050b1031240c98480d0b04444046540510004580d000c4c0010210610641d107865050044d0280101341b2044410701040c003e0000741d08000c2200094900301007079041291505441140c440e152140350f802c040f0029440b90010b120003a418040c0390008003409169241c2e6007411000186800d40c14040c140480310042010b550a40d215049200b02c4a0060001c40d03580c2401e0400410004040c00e00000c0b1010240501c004403a48108403800846da5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 632327994 1250 632326744 632326769
    0xe0105120d1b0f0c1d010902030f040312020702040f050a0c081e0727031401020316030209060403080403060e0c10081f2301030b1c06050601091508090c0a 68
    0x500500c0d10403404000f5140314508102c20000100444100c074060060251346035035000402242161001058012405040c01441400640150411126082036060806000081c034114a00c1c0003801a03140c043d50007410b105480c0305000e4554012801420855800d0040d00b8100700d0644142405803940c1c00500344010303068101c2050300700e0f61900102d0300d10b007800d1445000b01d880b0141c0444c00154600b02c00003071100304100401100d141e08501e000e00029070a502d0546941c846400c02c0145c0311080c10b400140300f0300f40381d584030700312005107901c281071640703468582c1016001800c404240f20380600c2a00c10100e183d24056050703110408250340d904500d0380e038295541e0001520400e02c1070360b04d0f007900008140380c8140301c065590180740d50000c40c0300c180894001810b031000442101d000c2c022882000c0ea82507011003150342425048070004c10300340c40d4240101d90718002588240003c1400c032160b20b072030310352000200f80201c1914003140c1405100c941002111310507071141082d0140c0c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 632329244 1250 632327994 632328017
    0x3140c0f0f0303040509090f010b0103051302010f0219060b12011503080904110315010905090105031506061308030a030c0905060a1d060307021608010203010308031f0f0e0105120d 79
    0x3049580c0c42454900982641e09140c3c0e45d0001c030321120815030300c260007900204101c003c07030301c001d00c9202c10a01c03092a06011905102c3c000c03050b40411120040d0420500e03280d01d1540c1c0c3e0080009e03130b01034a00d0010410344110141403160082642c4040c0314460030350b9141c0a00303c00414011009441d178807405401d80c0303030301e9135503221035035400781c030060790413540b00c1500d95007890170315010358440c1d0080b0109055440c81400018081105600218481c0c60300030014041500d001607a008081c40018050107982c8890001034064020241d51440f580c021040c0031610307400102c05045ca00346983c6007846446020001610018558020590010400d00900070030381e204105180510001d00d08080031034480a000c240317103a000b12645800f60b1f020100300c58203c00800c050344014401c5400841c00c65040d9540c2c40b5051001510001c11a81410103000c040010500407400611840c02c020742200d0b80c0d41d0030b03101c07452024070403d8070403003045409612001d00850300c959202200da503440e50125 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 632330494 1250 632329244 632329249
    0x170f01020a1b0c0510030f050f0702060a0c0c0b070f02150106051204020f1f11030712031e15230a03150617060f0c3405061003140c0f 59
    0x410b2281c25a03684181150000d42c9403904a400f0016100035540481c0c041e00c0b4203400310948002034040d1150000480800c01003d50114526070001424100410000340700300e4103c658146400f00500305190030710a00048030341100d00c911010896800382c91400036406000307804a1001d102c2e010100e041002210042803220041c07560192000746107070314040040700814a0030f00040074100c040b10074000c0c021022904250013000d14001c1c84000c41c9050141c1e50f441c10350030000d01202c4103044e11201c01d81880094064108030908092908209410300c0c01e00b85401c448040c441d54101050b10500b49012144410140a08820180945030703104c0ca16030b104404040c451309a129003658844010440400c0c21a0850003a001c1d08014003060038605065aa101006480600000300030030001c3c0101d552180c501304900004201100100b80c02d5200311090a000c40c0c004206005010030800b035840310b001d188054a004000aa80354003942824a9440c2603480205034010a0004807101030f1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 632331744 1250 632330494 632330537
    0xc03060a212904060614030a0206040b090109030819080609070804030809070510030e0c010504030210030c0c080c0d0e040c090e10051206071d0d08091801170f01020a 73
    0x80b00d8105030600001c030b41c549001c20445040e0b0301162001e4441004210030b1020300e02c100c00d20001180501141c000315400100b55210307a22419500c08400b2501005c0d82c1c0c05205403100940c1c200030314554400c0c80030a0301c42100360410140c400305214801148460804010740d6100342511740ba040300f03d440f561000d070781c0d414000709214082e214044002c500b64882c00000e25214070341b40c030085052042003403401c1c104442c103040302c0d0401c00c0500c000c20242c1d030f401e407500085035500d0400281e0140035003c11191950903c02c05070805100080b015040c17040018011040034440d40c0c0c0100c0101d80384100401d0304c10026100f80040c0380b210007806090581c4400c82c2d000305101982c1c000d090381d02c5000c600780d0462202d0b4800c5540050301000083c50300403c41c0400d20a84d0f000d603d094401e40c00014400c103031180d6000c4c248170000f251940840e01c895250000240c3c0351002548590f170f50716400112510451276002d8503000e00c0c44000700a41050003550042d0701030751030ba04d41000c8004080301c6031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 632332994 1250 632331744 632331773
    0x9010c0219110d0c08070807050909030a0c0602040308040b0705011a030c12030d060605040e0c280c02090c21102114060402041406032a090c03060a21 66
    0x44054440003000a465001c03401c02480005c3c05882d5039450b10700154140041540114001c000c0d0340100011802c0110446400520605003c1040c04413410064001d010300d4100408480d40040d02090000106026241c0544550024000300754007404403015482e0802d40f194041e400baa6056081b80391014050260440301b500f1a4103100d04110f1420585072564420004210b0000e000c2c00b400a964603041d03400100844441d20b010542d54190038001307084500d00048411044c85042401d211f400f04914541c0c00601540240c144080c01d299290b1091420000680a2902c854142ca28440d10f19105044030b20045414500d400102030700c00b111804d01d0161380b0a078008a0002030b00100380c032000350000500901d51490144180401c6070a103003108102d00324008104000e0780c2d0009a4889110801c1040d400850040e030003a1000c4403c0078025a84070207007108024000b4036040146101e81c40c00c0348c1c200599035586542406000c10500350f11500210900005c011903030b00000c0741d21 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 632334244 1250 632332994 632332999
    0x2030601020c06180102010b031c0305070504182403021e0609060705010b0a0e0c16030e03070e0402090c07080f0a0207030c03050a05060c18040b0d02100809010c021911 74
    0x2c520304100d0019043d0f50012001d50f95100c003900380d078140381d43d09105034122001c09400815007048415036400b406500d9100714003c06840b000024201c2e0f102d202518010090750b030001510000490460740136001112018080b18400581d0404014003464108110381e00500003400661208841a145042480d4001d070403076410014003c690719071100a0215074055000082c44400c0101002480e8000b50700180c0180e00b09000c4c001907202c910212103d5802c103081c0344035541c80d01d00d01524071901c0c1801c1356a00d0700070102c00051a420010400b40709074030071190b622899640140e00340160244020250500406112080403180000010080840140115203010355a99a01d01028106410442c4c2300d40081000d03504001c000c01c005604868490916400c0880c4030140404168441d01403d20664581002c2240d513240c0d440045e0000303402415101300511212005080070301c044e01c00084543c038040000b10824804030740d41c4071140d00821648417024441c0c0b62810f140420842056 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 632335494 1250 632334244 632334253
    0xa0b0901140403230c0f01120b0d0b01081605030d0203092103044e140d09210b07030e10050103032c0303070b090f0304090630060203060102 62
    0x1c013188884413503001010210f40036503101c5800e146280d017000c1c6019291030085681400414580c0c0c0c100d00324103502000b00200145175080480006c01d840c903468005007000030214004104918046130a181042e80441b0700b000a6075140149540e07111098503c0740140c106203d8044a8601007913840e404a075845901c8035031007526503c050941d4001c1e0301c1700c0140340c040864010b0300000010781d0a510b0040c0711480841c4400e040060b50b00304a0b0128031950142481183c208011000030b80e0140e012001080340c011194600780580401c8040c006c29130341c240080880c001d107c008541c002c0c080d035408000c0780243d0700d5108055000d0483c580f00510300c2c0c06200b6030000b201207503224280c000d50180d81c550541007070040444403c5c43d22a034542c500100ca018220721607880000484001c2a40290b0310750155803085086030174031928491a59a90200040000b103070410b54100200703444c02c1d0039510312544001c00c0c1d907140000020b0000c1805240a00e04400881d402e5400382d503001c02d0600541c3c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 632336744 1250 632335494 632335499
    0x5071a190915031a040c050d09110a08280c030506070c110f0315090a0209070504090f0606020c0f041e0912030509030f0726030a0b0a0b09011404 64
    0x90503040344208003000a00304030810481c0040040c88030002400b941400c1002c0b2100541c01ca401c2c48440344041d000c0c41d1509060001a40308070210f81c4a0502d00c20b0401c60380e8240e107402d801405002e20094071400301640042042c0d1404079010000400a031612680c3d812004044030140900b000180c0d19401800c4002000c110300f4041544101216030b240100400c21746804050100c00450040c0100e1664004442903140061003601d01070a03642105000c1d5540c040b0f20740340046c0c202000f500920554140000d0540040103402942d404540a100070b0041d0510300b8102d4189200b600c0c01644503850640190905561050070030034041c201040d80e1102c103440c02000040302024005260f07035020800306000368031200d122408204d04d010311040c00c10300d1a040d17a9000c0d103840524010400035140b0108080300700c400030002c2a4903015004580070001d1050a5041203138102d017400d0821138409920b150481060058800303a0740b0480c186510600111812000c40b00400001c80c1c040002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 632337994 1250 632336744 632336767
    0x90c02190b060108160c080d2403030338010908010615090e01120b0a0f140612010603020603070c03051303050f150f0c0a0e0d03030c0f05040305071a 66
    0x400c00114040c03210041a42024000103050960051200c40c004801c00108050a0303802511140865008031030707181c4032021403d107803004002c0d0300724040401056822100c0c2c502c40c000703030800c1168000e840810100d82c040c0f00b007141100441c0348030210728155048110900c1c03820710103409008410324200c0c0000b5110b038451800c4440640149620b5a2010014286c103640f03c00302d2b20207050344030410bc001e54035055a030b5003546610000200008000ca00241040b83d45500602100000c2d580600c40d8a0541002c00d4411409032115070084d42c00d880c46140c5501c05000320700840e40d02810303252443e9134004085514082300b0104404200e0100540d951144007090310f000914050070107000d0100324400210700c0c181550001000040b0382d103041020020400040355444800503951550382c2140d03440465000c0700f5114420713404501c80b0b08107014183e069201a0118001e611468403000fc0b10341c040d1880e004a00c0018965402070304280300320546000080009a00010914100342003800c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 632339244 1250 632337994 632338033
    0x3130b01030605090c03160608041505010e0612031801030203090a06110904050f010e0c0a0525110604080606040903021c030f1109032512061a0613090c02 68
    0x2a00c6543d1610700703014480740103110360310840f10110010840c10030f40600803103800c0454070801d010301000d600010240030b10280c0e03040c4d880c18a50b100f00095a181c9001d01c003c0d680a8030708902503152600301042a0100000b110021400d400c02115000344101c011406540010f00d01e4225008900104000075443e000e0312101c01d0111010549500ba94001e101c201c8000410318100251a400104142018201c401d6001a50070141d10394402c51041e094449100c3c0c0c0c00c103036036007449081d01c46102c3c90b19501103444803846551f12802c0c42005100704400c42c02580100d608503000380011510524113680700e900445c0c440c0c019101408a80c4184e4000722009178800c0001c25129440121005030600c07a10b081010440034950a01000002203035842c0b407a102540302c0242c1c0340040750300c2040da0a102000034000b000342d1805080c002c0c503142d005010500943c5000501c105da070861546880c005480d62080c0004e00751500a2070410640040c0105040100070342c02850140c01c4005040007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 632340494 1250 632339244 632339249
    0xf0303080412111605090c030f04080c1507030b010f0e030d03050a09080c0303070801061d01081b0d14010e01030f080a090902030408030906090a020a15020f07030302010c020d05031b03130b01 84
    0x38254030034900001d002d6403000040030303d451f8020420800480b8400040a90381042c0c12a500c26100c0f100c0100c16403401c0981811022100f0307902041180d103e40c10b4000c00d030852406e0340e44100d20180b604065030140d10901006500d5040b081310744503000d100c0d512041d44400100c4002c12030803019114070409900455400c0c0d21504000304220119800902c0c0340c7c010515481d1815281c0b01000545952444102e20035042005204c042081e503000445441016034640449940e08c02d21211400c0080034400002503204424000002c0c040d1002540b4a04a81e00000d50700355100103a612a21079601c00041c1c40240321000c4800300301041248061807182c0e1145003415520308040c59454505000100000042d904c48452440141c498114030b00c102c03201103418102c410b0303420070107030b042c525040c0058007680300b9120000145a030540082c0b14070b0714039409075043d8081800c000c56072840201c07810032212489a182c0440030180500559100e10a0028001000c403950746141800c0301c2079 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 632341744 1250 632340494 632340523
    0x1e040803071a07020d030504140f0f07060305150103110d060905100504022a0c090408131e0b07060227010806060909010905100527010f030308041211 66
    0x1c10118200400c14620504644081c40051802c0c50036400080d03981c1c0c407140c104810076468002050170080d2000100c030109106005481c1c442e650000b145944450724045403130030380f20340c100000301c0c1c038081e108030350044000c0a038200b200c8100400540282c84010014441780c8020441000c1c110403522412020300820075010442e414411007600c5958290340006104a00c104040f40044c060f1204405014403840d00c52072204007203011383c5051440355550305400580000402c000c2041d40802025501050714601c03c0861700e6002c2107201c2280403e03014510359006809002040604010303040151007444050300e0500003032801e050704051002440c40c407200b0402c8021980d0303000080c030740e0f00c420141c500f14200301c48000050094601071255a5084d5950710200e61124000b9070200007800d030107841200c007050105502c07200b4034264808688160300140021840a901210318030440e40c040e074400c0c1b060344964071007048800409000c4001d012448000c590640801d01c030a80002145 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 632342994 1250 632341744 632341747
    0x230f030306030d0311030a0b120a050a05010f060e010b22030809100203160f05030408010e0d0815010c03110f07060c0605060402070503160f0f200a03050606061e040803 74
    0x500140b40c5003450403c03558041c10b09100d1042d01446980d0141c0b0f910030000180402c024941c0c60109140301e02c914482e01890191703002030b006000e0002032a901d140c0c8194001c201040b440d01c102c030110b410743c0c010000b51200c20b6004010420005010b0b08040400c03419080c2076001120b103a5020809039881107440b8140496010064904441180c40f912154000b45260841610541d2079000e40d194000304156920750204040c81402c2080d00e004d000d02d800200100882c0c0c01540390303950390018000340050003d0b0000317070301e004d515000d011010506845100c00901c1c950340c1554010006003a0080c503206894014003101c2003080700c1c1000700441d4581c00c01c558a1400c0c03a00c2900c40040695001c0c1d4010015140051000400c40d025007a1680404030840e40c546004a8403048240c0060a00c8201d03100c0350040c084003811110601c0c03202200040320600200900c501d801d042d103c0a001d40c2c2049000840504003140104200301c030340072100400748a10001a84180c03c01e4010f000a03170300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 632344244 1250 632342994 632343001
    0x305030c27311d011a1e0603070e0d0209040b07091707030b090a06050906160309020a0e070207050d0b060306060d0b0c0d0b0d030206070201051005030a230f0303 71
    0xc084105101d8214014402000642d01080905503120a000702c0d000003030f641c0300c036400716076405901076030301400110007408007115103848500300b00300f400c801900c40e04007101c0c6520b00d2544c00000391340c8110042c00e050b040d50b4a010b02501e1000005450035000070303015004100603629011020b00c207038400e01081d106810807410040c0803d24036080b406a0001c40c0c0c40f082d1001d480005e4100403203901c80b40d200c03490382c2c903d49454102000307048000c10841c10503050165000c1d000c160f040c452890042415400f251320328085003500c01030107010350086a000d48c180003176030700c511020f81d10030290300480724842d650b400460600683c0e403100b80c840020380020710150385010f00030140c00140c03c0310140260312654990108807080901032568141001034402c0e082d40e42c1e908854910300d801004500842081d08013b034460000b210003c00551030000000c18107506e03d0101425628054018540b648180c3e40f00075404400c80b00103a40034071410030240d10313460104441407418501c1800f03140c5904 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 632345494 1250 632344244 632344249
    0x2704020d24060c050307061a030f030c010b0f0105030a0c031e051e040305031618090534080606160c0e070f1704020d052a04050105010c0305030c27 65
    0x2107042d00a00c041151034203503000400c0f030010a403150180c001c0d00005050f0701450960344140456064141c160161f140c1c0140c840c007010005c0c4c590324680c00001c0c003842200100700304880030b01c3c44046001c280c080c0041401c112140d400740880240a050000b44002060558200c40d1205583d0007546030700d8904000d254080c000300d280c44100c0507c080c0e007082c02c140c1e4014003280402418000d4080c04c00405525907032040714500901e0032000240c0d18855140c00307280c8080c00084407041c54980080607622030f41c2c1452904028450b14440c5d5400301407001d1070049070348030006401e95521001c01e10544580140c1110710300b2040d44982000e1b01070602c0d1074924442401e000b030206051040ca034104c181525002018046405030304110401d01d03035180c2c80040c0035044a42000340c990f01c42e05240e040440b14104124403c40030707101040c5000e400382e108000030b8610034020640016641e0986c0e90001e8001e03405503410042c992011400d1400e990490707e00c030300281001c0900394405044e542c4550 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 632346744 1250 632345494 632345561
    0x30f02032a09010507080a0207030807081213051002070602040b0d0509120a020601170a0515150d1a1008010207050d03111216050c030408070303142704020d 69
    0x20700c0d010601820100c42c840042e11034000c01c40050424100094501d0040e8800e00092028643c02008143c4031009170030048640e0300180d5040c8a40a00c600c04140384081105004060a601030300401c0864040300d410001394110807021600242c003800046114142e02c400b81005299500700080c1c980303404004140380444082c03440840441c104404a4501c1d4003203003a0b81540e0003505902001c014060000d0300c4c0ca078041501a000707000e501c05018a0759000540035000740300f81c031500204034401c0d90400c60180d50409000b0098050303030741d01e000100b000703458181d8000346070419400164cda4200103800da074040b09045030250030502c0d0312040310b038140c403900d046184c41c8a00c0600345444403c50306050000034140c2c407541070020f030001441500c98011983e280480d402600c2d141c0d42e0f5100300654075450341c00200c0214549004c503401c9504c1c400165458443c001c418203104196500078182c0c015001048150456000c01c600c1c07000755050f02034189260800b20a5002820310780080e514403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 632347994 1250 632346744 632346811
    0xc10021305150f0306011e030501050f030d050304171e030405010c08040809130b040624031b032307020a0c081902120c1005030a140606030106030c030f0203 69
    0x182d5a81c0c1c4072041042c801020f41d0983c146110002e6600e4039460010b864104482e850615000c2c3e41d00500c00049525410840c1210800c0d100c001aa100c000c04068542c0801782c40a80040d0051001402040c2d04038800070050f0040d000e011304e010444c0f880386403c04d450442001c8444400003d200801c03000340300304040c200040c5400d00080c2450350b50f4804a21070900c0d0144034424460744060400b215510220b010000100708111055031009650817528a00081c0446c9200000111403128005c0c060746e813002c0350854400701c0e90444030400358010448801c44005031007682c4107100d1807150411101d801514036400030880c0717007100d24040542e1851078002c2d0716246c00c0014500f101c050081c60400c4100d0741202c1404147e040400100e01c2c2c010901c0300d003980081c8503c01d00c91255048001580070740d408180030312100445280910210383c0554906401030310030001000708921981c4141d19040c0c0c90724001c1070034411240380e00143d8000b5070f28014a00070220440d40154000d0300711002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 632349244 1250 632347994 632347999
    0x30c06050a1d010210051603050105030307020a120c050306040804050f040b0a090b06192a02180402030a051f0e1605010503040c0e07051b161a0c10021305 68
    0x50680712020040200c1003003044050200451440c40b00180e000b0700c0301015a80c2c4143e020051880d020b810540c8824080c03c001c00030a00d010000b00b001c1c2000700480d5045a0082d10742c0d451245010120390569003031200c20784c0e060b88000004129036a06100d541d0081d070003520300903292400d080c10441c41c1d03010000300620a501c0c11880702d800340c8400289504540014600180b841c1c001c4e4007260452142000b01c601c80c0c281ca0b012075144c00d030095540e040444604200c032040d07008200c2012000c0e042100069032201030380c402c10084048040d58580e0080c4064140c034034054880c1e4500385410031040320450107080d0724039024103000752882505602d19240d8014200d421200100000032581d50059504000b00080041c050214622005009000c225186507181c82d09480c0100b5942040c0c0c481905a00c043c08500c031016000180040308910603521a25140d141c058442000784000b1010101180140b040145001041c4a0f010b4111508480507980d5101c80143c0000180030b504010b2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 632350494 1250 632349244 632349247
    0x2210d02151810110c160806010b03460b0907140d0513080a080402040b12060604090606120c1503050f07140f0d021903051501030231030c0605 63
    0x1540e90200144884000000361400540941c4035030004c40240b0810f102d107203403481148001c0049258106c0344100701e40d0500b09481199884510f0140300d848192225200c1810100c1031421449501154041284107d0307441191b406a400c2d01c08030f010150010711420a50362030784419a4101300594652020052030082801a00400d1265160144078603100a159503403000640b80c82e110348100711a01d0b00000c11a441e1400c00d14010700204037110100c0c0542e00305600b04026040c40c12911201c038103004080d01c800d541d00c0050000401d030300c4800351406c0d03031076420000300602c0400c0c4007001d1a010f030324415262410144c4103400201c0c0000325004042c0703000200201c018004041e150403c00f5882d00c1145a41516100074903030088c0710300411a2140010003080815031940100f100030903a150303240150b40c500703205404540c0112003102580d101c82c0c03140382140d03200e58020031070480c2d000d0030f80000c28583c0501c0e0007040482d0108010100e46900c080c41480b10329070320080246910718040b03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 632351744 1250 632350494 632350531
    0x80105010f020d0c26031f0b090415030c060c1a040c0303081305011119140901033813060f0603051e07020318090c0702210d0215 57
    0x250f5510402071500c041002d91100541000090f80d0a820b0300c0c00300307030308014404100c011080c6450740141d95042120001c00001d4013000364020103c012101d8080800342812100381c03d0002a10042242c090808085200840010b4822034040301070201581e44034400012460008100803803224210010403946d0b040000003503031070540409a03645031400410301c1e1a4040c00d01d0908040b40c0c0300034480c1d42043c0401c04024034820250200309103568001402c0b801c1c00038141c45044c40042d003e40d9003c0d00b0030100c915940a50040650404042d80000c0b0740b0804800300c85d200082880755070b45240c0b59190603061441d00901502c0b11600d80f400800c55246800c000800c8080e0310b21803482410344030400130b010300c000201c001d098644491040080351a101400035103c3e805100345010190a14520044c00d05140d000c55208070b200c0750235185402c0b071940801091000001e60344207004548006508041c009100c1c0d4284401c0700d0300144400380c5aa2041280e624001385445842400840034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 632352994 1250 632351744 632351747
    0x40506070204020702032b080703090b06120a060203090d0908070e19141501080a02090306011205070b0714060a091e060b06210708011511070512010903080105010f 72
    0x1111034040d811507006030740320306a01c0824105003150744920900c2e1090345620504e42101800c1c06102142039540208076943c000099084490b040409003031244104002103240c2040c010300c0b81c40c1e804020450382c03001c450b6a00c01c000d0740e1007110105016040603406003013607030f04046200c01410030740000d40000740c00c0003c15145401c005000d200c0341c0003024484021070b940da900550300d051402da1012002d20380b42c1d0410f040c50890307a8500c0d00003000040003801030b841d98825129038500c0100070f04416482d0052200d441ca083ca0800d54081c018200001544403d000081071458071480c491644244d00e45001c034140350004005120391810314508000140040e0003182da080c003d8109035041d41b16078102200100005c107075107500300500140800c400d040b2a01c80718824150b5421190700d6940706042200d1400d400e00c2040843e02c3c04002c0300c03c00c180242c48000720465401d08440503203039103a00042c04800e50b043c404007117964466079902495402100107000d042c003030808030004541c0c2d220 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 632354244 1250 632352994 632352997
    0x109030f03050a021e1210050a030b04051204060801090e010204031205130918060b030c1503150a0605090102010c0c0308011a09091510020d140a0302090d0b07090b040506 75
    0x200c04003010766a00010315103090039410780700c003110801625102e40c0501d03611440c0319400400303858610301c851000548500ba2040d80c090a0354030107010f07404a20328503510011074030307009442100c0030301403258200007031340100b400352004292980c5c074038038154501070240044450a44d05007203140d0040006001082034070402d540620780314500030741d4940244080c0c1703052007250b40110707900c5030404210550310b0f403d0000c072050150080004129070301ea030104050b5214002c0300348a1304000740660420403141408040d607400b107500d04020315450143d00008601080d250010800300d10082502c02e01542d09100b0100d0111550800b00000c0000d42c0307000c0d20b040301c14030a0381c800b000e50039100b2a85074000c50507070b90912800341140c10369042422403a481c14080144450169664080711103002d84005600d0600c82c07515280d00e10004400130241245034010001002416001c0003074051544840382c410480e10702444118031503040c60180100414a6035005081d40d040031300082c00365a54090 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 632355494 1250 632354244 632354267
    0x2100504030c050105030a020c010f0605180f01090c02100509100515150a1b08090f0a0e0f071106040b0114060703021f2a02211b0313030507080f010903 67
    0x1700355441e0b40c5e131030650b072019102d890348020895003030040301c800d000d8041d003080040d180e00322084003615018030b400441814080301d411040d0906580104403a25080e80410600080c07403040d560800710910180e000d903001660003010301d07840300d40c00a020202500c90707541c0148907141100a050075420010b5100400ca5803d10002000010303c1041daa0080c04c003400c0800c0441c61000258100741040b95154110818141c014030294400c01014540520000d040e102d10568400d180c0c0c072000c0302084110002020701d03040c400a02002c0820360410054075100d0b9110784005515523041c07100d651060020b102c0490301550080c400100000d1300800e98070310558040307600207006031980032400060300f841c11514203510300034202d504240c2c49105880005540c03603000c0710448030042d0740b4000170700c00180005107088420301803102c2003040740340038000b880340714011242808a046800c00c1000c10990089415602041d03040001c210103100c200002800080208940800394401800400f00700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 632356744 1250 632355494 632355497
    0x4090f0b040f02131a0127080a020f0105030403050a0309062a0e03070b1606020f0a0906020f060c090f030c03010f020918161202040b040e0105092a070f12030902100504030c0501 78
    0xa290a081007000360815040d8101c0151f194195540d0b81010948401d0070040580c000c66440c1c03074111480d40124101c900846d490340c1c5251030004500800c070b0041201701001c490342500c8070321407540c0c0f031500046810040400302440b0204140050042e0030504440700070b034003a411070002086490b401c4001d03503801c1580e03c4510094901546802002482240d0800d09804000328014800d20381c8440503000381c51590302100c107d800c88851007136881078119015080100100034400d03c334140141c02807e010409401c907002c11748210002400e4442c11303000e00f0200c0303130f02140d808000d1424103c8092480c0c8104001006410018142880218004050010700034000400310079254264100e40c010180c26006548031900c4840050389c0071400c0c0b090503c1042c0c8507000c11711420150743c18034a5140c0368032000f203000b2000b401200f4103800c402019518881424020004240341503075495244102d40d800084101091041241050601d4002420020280700900019403501305007415a0400d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 632357994 1250 632356744 632356757
    0x915120a020916050c0f0c120f060403050901050904060e060a060e0603220f0c06080f060d0212100f1b0f0206060f060705100c030b060f040504090f0b040f02131a01 72
    0x3001c10580c4e6501c900c0700c1a84980c450706019903800d40000c20b19107a5400b04965501e405c048420580c1c0d6142803902c02c0361203a070010004180005d0185000780b210b4103040c14920300300b556010018003264103039840035003520103900030000c840ca84584c440015080c1800e00403401d2100702c021802d10b020041c86540c41ca4600c42001144c85504c00e000c00940746d01841180f590f1842e840d20303251a10003403045d840803030440e0780803c40c1400340120603841407070050469130b214180d035020869500410a0041d080d07008040d5880000030300c41c051144108040a800310f580d1001038001c82a4147e040d00c6001006801113200c241107a02264240c0c1000044841c04600046000058103602c15800010018418450300125a13140c94008002040c050b8a0130461441d542007031100904c180c2c800040e14074070400090105150030380c84041194010710b0341c10344070356182c2d44071108018190b0b410740e00b41007405070b0502180f404107a042090150030720240000c045503031a0440181b215101207052244 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 632359244 1250 632357994 632358031
    0x703020c12010b091e160507030c141213140108010905070e06070302010e060f13061808040308030a050606040e01030b13060c0306080c090f01061202090915120a0209 73
    0x94016000310310f0300a1060740e150030240107500345428911850702030700d856400010070300f51502500c80500d50182d11220320b4101c540c0c2e4110b400401c031407022a2480c0e41c4400000540310b0401000000c1c0c103600d1043ca81d40d40c00b001c1e05614402c1550310610140c0e4074419144610f076800001c0c141143c061100c0443e00e074581c840c05541c06400c5400c002c1d0814400302c2c0280526505420600381b5900101c241c40c415181c401d118008143c081300c4125807901c0c0305c00d1403400240e03254031204044800385017480d540a04c5a44030101030b40540e00c262065800030040c0030a00e992841100d40100c000c8072681e1500d46440395041001505100181c50b0101201c0081c4403980c0040c2c01c0280294407102c10003001854050180c01010a030042c603585110784421a02c0d1030030407090b0103020300c0c00c41c01c00010036881c1c034030304455003201e616101c140107400b03001050968403150490790195204c450700d0303641c030200c3c03400340074423000a4210102030303910642000c005078465140d420341000042c07a00780d00111 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 632360494 1250 632359244 632359279
    0xc0507140d201207150506040c0f0f0c020604120c1e031e1703070e030c06120613050915091606080c0403080730021f060b1303020310020703020c 64
    0x204460391083c030061002540008000c2c507402d100b50340900a15040005495801c10702045807206000c01000c18031204100760801c5c041d5071884005a881d152020038a81546c0c0440e20721f030400c2d4403480d0b0b90254102d4030410040c401036010b01070900402d8440e200d4040108072168a8214840034108600009003d04041c481918000c503043e000740710440a07040150484450b0350046030300800041480c51080300a240224007030203481001410141080703c503214191030320760054103a0342c0c0100104045000d02d40140500e40c42014080e000e000b601c84240078044940d131000b400100da0346c1060207a040740c2001c0c0f5500f1400d071280352500303070030644c0c80c004440002e00ca5500301a041070300c0455108202302d1032078240c81031084040f5516064841a40200c0381d5400150100303070158004907014403040141d80e0f502b020b0180440404107100c1d40e200300031100c99101506009900900b50814004d504003000081d81c030100c002c1c0210301c0c148281c0c9000303440e2403034810750510803108004012401d2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 632361744 1250 632360494 632360503
    0x11011409041b0e06180616050a0b040b0708070c0303111e0705010b010c020907030c0314010e071707050a0e030a05010c0503040c05090403050f1605010c0507140d20 72
    0x410003800802025610420314000c001103080d905001031500180c8030fa49003041c0080d02c2455220610085114034100208809504090090006084c0e92082400494802c0140441441c001d110101031401c19041c64542d079000200000244070094007030000e25540129071021440e0145800600d20fa04a640c048462040c0300c002080030f504501031400c44284070340105a454410402000321880b640d006503034051003204c001e503122084a0012f6021070080d000440e22500307070700c0c0009a03061f00450100c0d5440003a005500d039568400c0c01c00c5040e60301300e020900000c5140241c0310b0a807521440081031846024003200400040484901e500d031010010143c0e42684a0003e0200c542c44c0d0341c0051190308101c40070382c1c0c40d1840c0c000020380da00f880410203000e02d8250743c03401e1401c00094440b8005611070002c80c88015070881c0b070840071940a02c55424442071a0380e94659401d05824a10310140a5429900d01074000c20700b0300e413003150007444e10950843c800d246210301d00c849040841c2031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 632362994 1250 632361744 632361757
    0x907051803070f170606150705010603060f06150c0213090309090903020d080c0c06010306050612070b0301060e06120402090907091107032706030b0d15090618110114 73
    0x98802c102000c40e241c1d404061442c181c500118241c40310f201601ca1059840c60309445d081e40050445000c0082075000e94010801036024400100e480740e66556244120b4089984c540d07012990b98400307104220b05610041a100c41d24500700f0300000e003d8001542412001d003c0f14211590b0b640041704050042c503006c0010700000380100600c44044c10301030345a98140d00c03640300103540000001c0340041d0500c159494030402c0c60003000d90ba8211356a00d001043e01410f01d07607000ea45001e296036030307460800006000d8165900002d0f140d5144c00030103000c502180070310911818040c00b081ca00301511200700f80d8001c0e0111200007668980c43c0845040c0803041d000000c210741812a010211140c040081c2260ba02c246c1c1c2e00310b00c1303840200c0400d40203036005071080c040b4000d10408000e03441c03007904030b5051050001c4c882030014400b41c0d06d0220030600c8508004086031540b400b03805100d5244901c013401e121090004203c0e0102d5592644111640741e08a4140210006541d8440c14440180e401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 632364244 1250 632362994 632362999
    0x16031214372c090a02030115021606032c0a02040510080c1005211605040620011b08010905010807121407210b10080309120c091305070e0609070518 65
    0x20303142000b0f04c03020040c5d13009000740044540b50711032848002e0b100003203980e00c448a08900325405801c0510881c0903101c0c84081451031640d403040140400c029124030744017200c14000800300c40ba15403040c0b00c182d4100500c15044030019603000c208496011401240007081182c8a1601110404060340d0600442544e40300303d00c0c0d4100d0440c505910f0043c0c007130003441c0c6080e12925035403020000712000e20940c001c460002c0c03d24440201020b88070740884260401500c00490147c040003103901e10001c0a00d0302c003002030f18400040064114030f11505014014680c040c0c035007903040c600e512076190040d841c001c4c04501000100d80005c082400072102400780600100005007040220400f148203850302902c00f0180140070400c10340089103e9011500e070f81002d5070900500f00300700030302c1c0303920940c500e12580107080701400711b50348640700076215507102481c0401c0303203600b81082490301c122070300b00c03001e00300340102480700a596079501d01e503100000e4a00942d0707481c0f68040540c82c9210102e82c41d034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 632365494 1250 632364244 632364259
    0x20f120703180f0e0901050a020703090e09100e0d030b04090209010605130305010908070308070206240303070c0e09070605040501140c0a0f030203091216031214372c 73
    0x10710888041340319025848000003030120b62034035040351049102c0c03000c00402046c6500c00c100400500b0322482c07640b0401080c156418200c8a07080b0b0002d44800414500858200d0301d04140e07a15098450040010710940303040000220342d9011403035410b03060080406001001c90000b41c2040e0580d0423078041e5502c50b00900a04170a880c0894103900422001c401246203c00000c030802d01c00940c0520a503201e044031045401585a079082c40a40000300036010f004c1045100c0c049454180e41703800420200c00755114a1608241442c00d221850300180100041000208140d0307034406c2511090308040b100540d41c80c0c4079080b01920309041004001d0914424080310700c107054011000d031004034410f550b42c000700c1d0541d015690304e9424615202d031140c00ca040080c00490300f10481d4110840160601c8100c1d0944140511155001341c1503804c3c040903404400107031822010010300c480203e00000042210072613074041e06100d042244400481004000c900b00c1e609a16204100380710301a1200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 632366744 1250 632365494 632365499
    0x140c1e10091a0a0b0d1203150e07020d020d05180d020409150f09150203070306080a110109060e0102060a0e03160305070b010f030209071d0a080607020f120703180f 72
    0x441004600036004048482c1c0c88002041c44156000b082100b2000912040701c41500d070f42d079409003140303100c28003017095034031440200702d14091448140034104a1001c0b59452420b0440249040c0078003050000715080058000788103030304102604c59000d0320074a40c802c0740c4a10700c00f01d21985510b0a0280d8001d0074100341d401030103082c0c804c42d2041c1d005050240128120580c0000550b022030200402c004c0200501010300d101c15030146811118500c1e0120310150394480061a00e1500c05040da03102d948501012030644e00f0800410040045043c04000803250360000303500d942005121410a5480e501c006a41400500840d648550204041c903464003003400d005025400070315086412820020010410013488915041140d50091601d00942d40341c032400c03145208608140c0e202c1c01c400c4c40000081b50350307101859002c2c0a82000800b21450f0404000b40380c00d80301a19044550007694801c2018030004c1c081b200c0c0c040d09824070240c00408221840e51815840e40004840e9200c240007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 632367994 1250 632366744 632366753
    0x23031503011a030c09061302030403110d020105040b0f180618150105030d2001090b0a0b0a0602030a0f021c05130602070e0105040504052b140c1e1009 66
    0x4008690240c00801112010b0b51480041e5a14900d500e0ba25a2116041c80ea907490550502c1e5406540500700c0c1124400043c18001030340c1040d10100d000c26624032101c00d09203000c0081c2941658a0700c000e2185082c181c9883c034001c080134124a10481c0d4a000042c2442d11204100316040544812241c00746851203446440044136003010845028620080c0303a01c14954281905803035005014041c0c9408154003503420511524002401c44444500d07807055402c28824443c6c1940039071400000d5103481400841140da4440415208400d209400e02c0455400400d075003000038a8241006040000c00060b03150004202603040c1c503c0000410301c01403075200028207041449861511951a102d24099880360924090420003c0e0300c1c0c001041545840d8115540142c0524151180c200c00191104115825a0a615031800032000480400340c0e02c01004000d184000c0a0a410002e0890a030750321075080140341c15644002d140701d800200001e026120300c08440f807100b041903002c00d182 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 632369244 1250 632367994 632368021
    0xc14030a300504080d210501080a030e1f0e06121509010611060403051b0d03090c151d0301110309010f0516021906060b071b1e062303 59
    0xc0c0340311410340394201c80141600803420b40c0c0980d40b400d005010700b0401d0030822108000400c0104413480210182e85040d10110f2290078040c05298001d4050741c56a8100a49507007035001c105801600003a0800c1b0034080c111119a4442080e80340c105c21455000e40055803a00a00f03192194801042040c441030410444585449000a940280d443da0f030300c002c142e178609060500c0555981100b030010340024030034030041c05035495280801c0003e49040c1c24040c81c00b80c0f5104040b0219a0700d4000d2018804a40c9540c401071142e50380c207045112034140010003441e5400e83c02d88000800040ca0300d425942074110140002000200c0e680f00c0c0b92502d0f231203002c1d2130401d4200c54210b2038000401c84050640a5082ca00207854008180580783d804000c9039042c580c08043d11a40c0c1c1e00c032004035207074501600400e04540201c1c0b0141541d07180f80b010740d50a0304940c0c0084114500d4010548910070903400c55412183d85046c000d00740011051031081800020134500010303200002003100074082d0300c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 632370494 1250 632369244 632369303
    0x806100e041508190219050918120415090b04060c0f110303071b09150e0415060603140903070c5d022d040e060f0f040c14030a 56
    0x41b15100c6e690354050030982c05034103074000c46801001d034070001100c1d00c95500214081c0c503004401c86488a69001d440c03400c03600180c20600c07294441010146056034064050000381c82c003000b01602d070928200c03000d021034004100013010f1002480002c402e000d04909035011069001d401d80e9903429080c40d0800c00e183c041c601c50011908500804941c40940d44198901c1d0300b101102c0000c0d450a00e41c1c070550030300b401081140e11410b03031148180c0200041c045c000060a89440101e90032100083c1c5000310384004144d03103000d920034001c4001040100400701c0c1201c07456281c003006482078070422480a080036840c1070443c460005d002c00030a08408108180c101c1501148424003140c0a90440307060700e40d207000e503100310380d180c1007410b6041602040b8032201389558081003042c03202001c2029666105154001508040308100d00101c80f004400c0d8480c2a240c04998a490301d540d8030604c11400b40560b05214440c0ca212420076101007002e40d0741c66030446c1640c4816110700d6404001c0340c05c0710 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 632371744 1250 632370494 632370499
    0xc01030f02041e0f08060c0318100614030d02031c020a27031101030207030f0305070201060512030a03060806130611070818130216060b030a14010c0806100e0415081902 74
    0x220303000a04a002050701c5021f0411050401d10b10340310003500411500311010700010700c0c01200300da400c9503c031600c00c0d100104402c2c41008814a0b01710101800c0121003002d420a5420401c4100c03104000404158030320342c2a558016140c1c0806441110700007004441c465031a001c80c200c190310071540c40080c60450303202da20100c214049400044040c4e004a510080120700610007001d01070340690840399200312144000580c5a80d02c1000071070b000342c0644001900c0c0c0001491f240d485038507015110182c45008014845818200004c020381001080043c008640d24200c1840102c810b800b1581016001003400d5162045940c008103c920307881502c9204cbd41c4201c4000c40001401c3c000d07100b00400b2200f5031840c42d0041e45a01014080060307401c1c0d41b500410301604000b640c4001e5200c001c0f030341e082c00040d00f414081006000040d0242915105030040c441100b0f129a100804081070380c0d055402060f0302d20601450000c451072504028a58041c4dc901c4003a580d2549070881b143d103008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 632372994 1250 632371744 632371769
    0x70519031a0402250203030c0a140d0201050118020f090d05010c030507020706091208120408040306060f1215060b04090b13060803040e250e0906120c01030f02041e 72
    0x5008020891142140c0c0c0c113a001c0b0130000400c0b030700a182d50742140050002d81642d14102c3c00c0c00d8004d0500030808422034546100050300c8a4189081100300000320403030008001039410151918030480100b000060026000207100a401c80c044064904102c1c0c080d000480c03808191905070301906150307000b100061f18000024480d036200050446c111a00390319922105800c010003000c403079880e9102501d103000b080103182c801d04030380800c00740b0030360054598907140c45c290301d05003003030341c03042d601941d550700b0306081c103200c43d61460003280607955000390822a04402e10300717150041d00d495031200001d2413010600240d5070b411b5070050041104111500020514070301262000c81d1028060030740c0c1039105110601c401442c80000c03d82110700c40c4014035a2020b9044c01c4d41d0003100c881e00b0440040e003000751b5000d140c10070915041c0c0224040381d6050310a40005a100c1e0f98501c80b402e014101030321959403103040006681250301401c120121180740c5d1829100c0008001e20511451400a02c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 632374100 1106 632372994 632373041
    0x1020403080d060e0901360b0703060602010b0303040b071704122102010203090a020f06040305010501090b330708090301140103050609030c070b0307051903 69
    0x101050049041420180c10014131900a005440e0b140e052a0808060000d000000e04038080030390b001c40c81e00c414451120044001507080580004190707001c0c000f42e254150003000554000350001d20090407001b050503078034419445070803d9000140030f10030004072140c19403003d91103204031890400c0c0c0c032071034401001069001d040b07500c403038012035405004070400640c0501801034002141140b41044445448500da60740007842180c80c181d54440503030b9450b041c0c401458218008000307641e11424810002c2075000e0340c0c01d114225000071120300341d8120405011080441c403508201d20031148115140e030f0810072040307034200811f00558555842c00d21525584001100034130556500d5410308606011024250a503240c20422003600540340006072803044a02d554419035803551248802c6445000300c960207200460660740800e071140d03140d0082e40b031000c40d103a00e80e55100c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 632194244 632374100 := by
  have h0 := BRFrame.cov_init 632194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 632194244 ≤ n) (h2 : n < 632374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
