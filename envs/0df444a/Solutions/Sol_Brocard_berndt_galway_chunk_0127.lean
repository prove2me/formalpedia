-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0127
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:58:34.638254+00:00
-- url     : https://prove2.me/submissions/1f7a0d4a-b13e-4355-9ae5-49d2af2ed83f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 22661876 ≤ n < 22841732 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 22663126 1250 22661876 22661887
    0x50d0503091005090705040f0e101a0603090a020a0f030309291801020c030c0a03020402070c1a0d060501080106081603180605010e010b031017150106180b03070203 72
    0xa00910166800c02078550682d4540102038030680126078045071a0010b66104140c10412410644520000c100b60084240003006400725200d680d24070241042c024140d03221120303900c10b032600741c1081d00840000e040d40e5680c00c01d894200e580e5404c100b4180c0c80350f840da0704001864003060120320300700d07079054840e41100ca01d00100341003018050700d9032402d500120b000381890000c5000051120000030031542440c40091000246400c030081e810602070307030142c40c0780c42080d074421070582c00700d03a0f0448000d030356080d0310702d0104200c9090f9440300c469444020341001d04019400b01400c0d00c3d04150404003d100e50f5035004560403c428803a143c08224188045a2a1508503005d030307034582654100412217890070408108454198030b020f03a140c5644a006020804d03061802d94010220603000c1800c0d4200070a8200c1c0451883c07040303030400c1c2d04c42d0f80700707240909050004800340e0b010320985922a6955030005004160083c180c005004115200032410104540035a070242400303900460405 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 22664376 1250 22663126 22663153
    0x110102120a06120506040b070203041208070c0b040803041206020f03010617070c02010c0206030702010605090a06090608060405070b07050c040203010308040302040e1b010f1209030e011b110103020304031b03030204080c0d05 98
    0x10f50010b888c0000314001040701041d000b80c2d507080103602c0c078030495480e6600c1c0c045050102c0d041010b0b0300700080540c410002005500d20002c15030b01035401c2076000364400d03545890904000d12515640e000c400f10040000100300350481000c140e0398905007140e80403952100030440d41800c40b0b01009011503c403840702c0307002d4184034020399441212800001201a2118009503804008654052030030351036040901944516002d0308000309204001000e03039003015a503581e1200018025074090480200e20f41d4140300302085152001d01c1c018000719900d584a08090201358064081640200d04002030340051107400540300f925440115140000030040b0401110302156212808040100800c0c042000032490b2003245c0040d40303e03840710f42c6c3c4884c080b80094101c0c1c0c030542e818884550304802c860302180d4030f0158288200c00905e0016940e555514003561480c013048002d5000544110b001000c054141d4018019110810221070071541600100b01501900d104010701a4001d41c0001112 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 22665626 1250 22664376 22664393
    0x110406050d09051b01020f0606060904150b03040f0309050105120c0a02010e060f06030105010b1c0b0409050307110108010906050f060702040e060703060e0609091c110102120a0612050604 82
    0x141c440c0c40c00c003141c01400703a15498a40900030386042e1040c0c200c420041c580c2d680410000c07004059000c007901403494030100150441c0110713000c460190381c98454503480542d40c0c02c401009040400d40340c540324145030030f0501c0c11b28007280048000c10041c95001c0341540c05801030b14580b03855118000c080c0d507107001c40264540c00490004082d592904500030b0703487c100b0f10119203d071149140f10641843e005082509503001031348100040d640c100720850846001900744282c07042e2211021403a0040440030400400c101c14024040b8040414080300708013040c024401c502c0b0090341d03030103626600c45080400300c1d546446607507400030351404080100e0620401500503203000400005400c2c81105843c0d04050f821208400065990303071051003c0030581c04203503089501950140158580b00600c80d940e841055030082a032050100c0480c0458851003102c0010000c1000079034540142c515891454081a83c3e105121410300d00301148000c2d82c113404001c0c10f5003100041c01d990710f4a03200d019a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 22666876 1250 22665626 22665637
    0x11070f02040b0409030806040c03050103080d020c15010b0a030f05010506070b040507090212180c130b12012309010b030a03050307050408030a0815041b050c150907051311040605 78
    0x20896140c1c182d00030070360b650741300c2c4a04550183e1500f440b031b4a0310104000c122500705400384140761502005102280311441500c0b014035000c9801640c552007130802034034281441880765a440d80300c0001044030305560303001e04001c1c6010b4a043c0074080c0c41c4220380090700c0d02406030075007102007480364202055905c1b020941240c001c02c02c3d1004242c6841007142030360f01c44c4d80f016000c1400c03103091005000e4180c003c0303948003540102411030031000b40d0004000c501038100d040041d58440000b95065520341c88500c0000d6180c0c8002c000180100440104035102d1040c0c0701c198a0440000400481d818000d0322010b00004000d131440701c0c0b03680e4060350141c20141403001004400e000204250340c0400080260a80b10b403034141007803030609540d1081e460003136100d0b40102c0c01c0402c10004c1241e0304564401d000d045041c1350b07442d40d44012040d40381524104030b0034502c0c51400103108c5406000b00d6003405484058400e046409041d0058500340d80e03660000d43c1c17004800f04001c015092140d0003400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 22668126 1250 22666876 22666879
    0x70615150c0c0e07050405090a05010e1302012c0f031203070810030f050109120302070f03050d090602040905040b100305070b0f0d020a17060d0b0103060e0c0306090f010f11070f02 79
    0x7070b00c0d41c881141d000c2c200c02c215881c1c03001c42c100043c240b001d860280041540458510024021356040c5090310052150281881c540040d4101c018070031607002d003007c2d1950f009000703420400c80c2d42340b0301502c45140003c100140035000e01c00c414941810040b6405180d480151841446c2d6190614212541070700140342252850b410440880000c0b4800008801c50307006800206100e117240c01d1901401505030620400e0501c100103180000322250000310032203405041035510381885c104418060000040000c4c400c51002601240d01036461340494043e500400300711480b80c1c0c5a5003489899070290102074030542c4042c0c01000b24150f440c0007840200242800e544c140321082500c0c5099030004040366000c41c12181d044112110480c005135445407040b58200007200003a201c1c450501c0d0180006404517441d40072040c2c80e600b04011794030141c14098111038a620b0b111400302c1c1c5030040324900034a15400e0248100c0c0c0d541450140e441481c82038020300d480e02000d5030380c83c5051500c812089 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 22669376 1250 22668126 22668143
    0x21060506120604111c050c0c0c0d0c05040609090c060305070507120903020a06050a11010b10030207080c03030702070602010506040911100210050a02070303110a050a120905070902070615150c 84
    0x2c4c421581008060010207402400724102c410b4540c0340ba9083d148014500311490000b0b0203519003a81c400141e400704000c090b100040110000d08250120b00060740080e5003240c02c2c61000200912190712250703049005000c0c2e00c541c583c40701412816140203660b001e000800c00c0c007030007011490310301c804664142070b41400e070200c2c5d03a80d902103082559994007960120790041240c50311140c01203050030b40303440260000c22003007040f0800103003501c581501c14010981c0c08550300e0108801da000701c500c01002d2004903612843c1400c4000c1d914aa64007d50005500b010045070302e50410380561414240c4c00b2031030240c004605014805601042d80b6140218410624540d030071041e05d10446010704003e100150741c608441c2005820740c1c51201d04400c004801304284010503078000c0c03d80b05140340e14038080900240c4120b80300098605180301030200d009a4038000b0302003850b5402000c1ca01d200c0c40741404207055004881d250501140724500680404042e80308506104110701101c1601c15030b1030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 22670626 1250 22669376 22669391
    0x1d0609090102120c090f030706120b0102010902060c0d090e160309020d02090103210203040e07050c071d0f1e0403030c0504080a0b01060917031801090306090321060506120604 77
    0x3d031241e0f019200d808100300000b504004a083c2030001d101e1580c010380c001c0c081d00b0310344000240400e1501000801640d500d4007800e0f0b9683c0300f034005410254009080a48030a0b401c58a55101e02414000381d011404c001c070000ba40480901e0405d100341100301009903840781c0900141c01601d541039080340d000c00c0e414110401030740c0380da10060185020b0300803003080c8440b107004052040d080f080c00c10250343c0b0910080244040d4960800e501000904c0c0c803a40f91004810f40317a10303041c0301e900000080d01e401c400604400e020a0042d0348111803c060040c490b031141d016207229101120101c600c0a44103600040129029811000c2c2d60300e0320303140c010300d0503507180301160031f200c83da4001300d07066070590004200c1590f0206c1408040c200d440c1e1040c0311600a4a100d9a580c49008461101c05000c401c41000c260702078101d2a00840d040310041c8104940740c07500501e00240500c50b0400c10801000b0040e840d800d138850141075450180110b8a405e002d00084103018130000c0610340d00a40316100c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 22671876 1250 22670626 22670647
    0xf09040b1201050106030b01111e03040b07080309060a0905030d0507050903030d0b030c0102010b01080114030a0b010e04030212090a030803040212030708070c0e280f0516091d0609090102 82
    0x200710070000426000001d440d410040020140c0b1001d8900504010300c200c0c1c508106e40d40810407140074501c80d1080c80b100c001c020707085429030055a210307a41c8078401083d0b0606008400c4015032180450000740c5016590301403280c4102c0b4a0120003420990051201310b4451b11039910454005003203003041b60802d0038083c0020f1855000c002d11041c0d403030721070b2029a0b0b5800e0030000c40c954040240020312030404000002841240148503041120144484820311303520305001107070005400100110032503844210200f641401610100c00621131090300b141d0b075090711804d41d8040300b8010407074040b0740d1035500c0b69003e60b08060001c0e80d009034008503004d00e608c000c000805d0031511414400d0340b00c122a00307185142c8c0a059100b48040c504402c100610854140c48c0c0700305104000b1500e07003011198182c07031001841d403042910035540ca00000e100306e6019141c0c034140f0141c001d554031010349450b05100d001d0365448940307180101000c0c40c04030303215180203076010340d11a44101c001410700f0780140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 22673126 1250 22671876 22671889
    0x5070306051203072f1e04090b010512060c04061d0307030620030408030f07110a030504051504050906040e1c0e18040f0803130b100e0702060c0f09040b 67
    0x1c00251982c00000e82c142001a9540320002d215245244045c4c4041d24525410444020040352846004000300c0800341c005d421505134103a080142c0304209203619484c000d000171900303010b594801c946503800100a010001400c0f403041c03190203841c5091610f40038041e074500f84800c0391460700d8503c45c4101a919201041020015802040c0204100c039520700070103000016904400d4400c0001c2013000049171003042200c7e0040c90703007048460b45664580c1c003290070786020511041c113809848031410038564800003400998504444080071080b01c07608034100c61242d4460260405035840c0020326a1820754000040d10f641c0e01c065900102490074500c21606200c0901d2001c08c40101c002c81c0541000e80d01d64000e94040c00c0e0500e810f003020348070300034440c200c81401012510000005601c074a0b400002c0444168000c01c01c9003036050004e500e52007012980501244819080e000a00341c0340300003083c0f0302030510014414905a0801c0580782c1c42d5100c000340039001607c981c29202d2071344508 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 22674376 1250 22673126 22673149
    0x210e040c12091b0b070c0b0a03020c0307030305010501080a09020d0b07020a1202010e0709020a021b120a030e030f01090206071b051302090103050702010b18090118050d09270507030605 81
    0xc11a8424446103403101c1d0f200c0035099042259a4a0140703e5080040c86100051046c1c0c0d550141080c4c40b410141e1085019124400e20048540408924001055015080141665001d0300c500034241d4950007050112485504081e502c81c00c8061102c0200d0741c071086598000b80c140c81a02c80d130700a162a0a0301e00007405c1681d4006070b55800011000f0b90090090001a00c020315040d4a8a584150025070303c0780c034070900380490903150f401107241c0e55908600030114413100341502c003920690705024040ca0040300b0100d00900414048034440c0d101032241c0750182c0e40c0146541d013000c2841c0c030b803d4032061a0320310001d1603d14032000820305540300129800014805100965500305000c0018183d40002d4005815681080c403018140c0d6103121400141c40328035151403000c0e965140b0403c1c0036013911102c5034290009201c2140a10a01181c04411500c0507122040300c25a101e80e091454445981410500480c00d8100c1c01820b40c190001174001c03101e4035001c00c07825140e2001407001d5001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 22675626 1250 22674376 22674383
    0x206040816050402041802090d021c031404030f031101060504050f0a0c090e01050105070302070902030a020403020a1a0307030f09020909071805060604030206030903040909080304210e040c1209 85
    0x1032981d6800e495408440400390074290b41c00d5007428170f172220707540502e4100a9031900b0260042030b1981c0c507480302c1a09045264000f030841410381031009a01e401001007c806500082e4121844050a0203540c12170b401c40381c3c0b018595548211644003103d501c5074000c04820595221a000116a038032802003a0081c0745000c01c1c01c40506160f0b42c0c400427034190500d2503003030110b200f40400262080b1440181154001c2c00d1480d900c000740c1c0f0f4100d003002035603000824020f00c040b05100340350f4034550240003a039203b0f03a0500707109c03a190001744240c02c6101d1281c0c10034030307410000a803405209400854110103803810110ba4800700fa8001450075108442e051040d03840b0394810405580002d07400e0810a12440c020031050400002168884c4039901020740145000804a20f109904104880060540d2201001407180e14030300085207a00c25102900d80706412030501004140b8100c0e00b0310401e089440721103240c00e150701404041c00c402180744081c452000c110303501300c03051130040e030b81c5c900e20 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 22676876 1250 22675626 22675633
    0xe011403070305010e0601020c090403050c070915050307050d08030604091106030412030c0e01020a02090403090506070501150605030c1207030209060c03030105041b140c010209040204080309090a0e0c060705010902060408 97
    0x400d148400780c144006c2640b03045500c101005e80da6a11010300082d0001c0d00b40c0307000c44d0303520f800c5800300b0300d040b034642c0c00a0083d1b8075100b402c012940200740e0301003d0796401c03016140d0059440e01000b48001c0c81180140c6980c40400210311a440c0c19403015000c144500d42014455040c500000c14940040743d090306c48604658840108070f5151094642a03405030911180c50419180003e558000c0114028080c000c110081400d141c0100c600c0703030040500034030171595981c203403805502030204048461a10210a1000f04410f4010070589128101ca00d250f141003056280c07020000085c0030b000070b400d0550030048401c041e11103000501880c80d201005656130f514040074001102c2e8860003e034880e2107080b2601c42010b52001c011041d009030313004225250b92010341594024400c10b041ca9a11a10002d0001a0410f01202410b4003401c11030b54580c003503882c032042d070080d5100f112074800789800000b01d6180701d24205015240b658040c0000007050740c601d0703012441c07640c010b4201803169032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 22678126 1250 22676876 22676879
    0x603010b030a06090c0203161e050d0311030115120b030105010f080f030f0909040c081005070215070905060f1605060405060702011b0c08070209010303080a18080405010e01140307030501 82
    0x160a03000f00e00080c6011103080014250215009490b03005400034061401c989010381c4084c1301e440502400390481c03402c4a810024001d1500d80da072040c00c12200b0000c0703410000760100300450441130b01e040345e01100340e0206017841901c0031a2700e110040031051b0603d6454044101d81d4409100e014040c0c04007190000c0054180402c1130300e4004080c0c44040c02d503008000721011001c0060503120002025560075400f0744551070a101d4001480d08440d88520404140d0b181c803016136042540074907481d400b42d44440480302040c0c40352182c2220b5041c0401d006000800c09406d2031030040078081444003807036003801078040b081480c47c0740c0e4507001c0c0d41503440b8000740024847c040c090380d504007041d80020840340801780700040008a10109020520100b050410280b001e844c00725940c55074000e01d181680d60f102c4c030b800b03420150140d0340e40d0102454031100406070040c41c1c9114900d1a04174000c0e0b41014a800b004445071100403201504001866035030020402c50400954018603003038901041d9907 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 22679376 1250 22678126 22678141
    0x30e0105090607110102190503060303040305030c01090c120c06050a0e040f0c030b0102030412060504030e03011e050606040803030a050c040314030901080a020906070b06010201020f040807080607050304030207090b010903020603010b03 103
    0x4c00c1c0502007045903403040188103141030030b0480360ba800d170606007407850b1280d64070b200007800e44c0500d60014181e80000920344044031010750008402d07a104440d00752240d6121050301081c4650801c0003000f903070310b5040a010090280c005082c2c402c03898603000c603503c0c40c1d80b40490203940130158011600340c5c07210b41d180b40c226014083d090806100384015420145418030360414103038021005404259503101150506124084034816184043c00a0185a4140d0180c80000d8079006c040301e042403514010440f103103440800c56007100c0b90480190f003992581d007039001c000c0101030200380790583e0402c0000002085101c09483c41500d502c081c2d41c075509000005040c1d040018482c5141c244100000756165458800b511002c9421821200440d5112030040c2c0c02446030012244a205001c20001110039001074640250780219042d03d0781500c030b800083e1190301041e02d0040150300a0402400300c000c480c0d008101400c4c051500980b416603940124119510a80001024038000070411000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 22680626 1250 22679376 22679387
    0x8010606050c0307060b04021905090a050301050603101505030f03030f010509040f0b0406060b03090706170c12090c180601030e1501140103060f0603050105030f0105041110030e0105090607 83
    0x101080d0400901c1c000402e480503450f441104001440b483d5101341d8594107480710341c15038035869001d0b401e0280f00140c0c0b200c05411a0009000240310740034401c40418141818025940a1240a0018081145009c103444080c1140d289404c0300d10185003c002919a010481e212002480e10301450b540e00b4424040c10b0143c00580059005036001e805206c0000d100107103003002160490420340b0581c0f12890200003410103607101c090380110101c1030103051b60780400d00c04112041a1150344a4480b60030285008401c21102c14070700e40c0e003d000280d030100e02d0b060441e5101d91070301c042d91513019004002800700d610505c0190710030f02801e01008480d50305880303040300d98400c44005104070040b8503a00307011901c0501a0142c1400c030b1550194081c1d019800000280c40800b001d103a0958480b00014005c107024071685109200e210244a0f103000103100e41400349030440d100454101010083c09140003803500003008040d51201544840c0b0020301c940e80c0215440005420517081240c0002c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 22681876 1250 22680626 22680629
    0x60a0911030303040629010203040b07060b041104060207080c0f2b0302060105100c1203020c01020706091104200901050f0c0d0309020102070504060e13020612010f05090c0309031b01020904060f080106 88
    0x42c04001d03848496a1f07030b03000019281102c9114881654844103454402c2c050062941050b8016013014080040c2600480151065419035801c80d100f0702d98828032903030f4030004c0942c95038000128004001c400d0900089000d4151035150700c0c5050800010040e000d01c01800318140d005070407040041c0700300d103410b84450314881844e2605400703824243e01c94502c0080100c105106241d40010184e1920601390190781259420280c10401504141454100c03104480503c911030b51402501140d0240c040e240d007142c00780c0d83d0242d241004102c400658090b44085202c08002005001c40c8440481c00c0210901c00a40c40c0e4002c18850a98800a40ba050a58020900c030f182440d8040c4618190606a15842118110111002125400418001d110b403000c80781445910390004a640a5000115401c40da004c2d10b621506540722140c0e1081e900060702d9000480c2c00c10071102d906d441b41071030b60902d4441080c00062400c8441c60000d012500690b0001310301550310801044030311800c2c82080c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 22683126 1250 22681876 22681931
    0x20a05030607092c0609041103120d0608010606020a0605070327020406050f03030702041d070e19020a0512072705090a02040f050d1a36060a09110303030406 69
    0x440c651041c0e203c0c00040c541c02400140601c6d00c010026040c8031a800f210045440090252142c8044401c0601c401c0d42c840f9485c002103a050110000b0800d405200f8030040304c190380d0207008404034503030310000031f000080c200e0800c00d51501000406400f140c8140c1301c0b11100c8203806440350f299441404150395190780243d01c551508010be1704552008400c403034900e1f40c112000070321710b04a040e20701003020307107000b1129042c0b082400c08503484c13460b84032007030250030f980d0704d209460b0341c80c01c01d103606130311030340d08000005203007440710940d102c40c4001916081500c0381007030500c01c480c20b050300210300301803000e05a028852105c104880e0074200e50150700092407800662800341844404540c0303126501c505405181540386820a100d19003030015621105c2000011081c20301d08521010301d070302200040b14940310308454500c2802e103590103001803c0300e900030744026038401c5040c10003846103034015140d42e01940ea510041d40e80502c003d51080f84121b2001411603802601d0346420b18620b250301 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 22684376 1250 22683126 22683179
    0x1060c140604020f040e0109080c03070308011205100c050c0d03020301060e0f030303070e061309090b01050d121409090c2104030c0213060801050f0403081e13020a0503060709 77
    0x100250704c41129000320040143d4010404c00b504c02046c03801010014006001c45402044201c40140044010081180250745840090f41c880c010300340e10000303a6900174005d501070040e003140a800d6400c10809040a400c010307007040880f000c0c482c1800f032044140000130f03a00200600001d900505e04180080d02606c0800401d40d403540401d0352440007400810a0058410222040307070344960494860350500c07001e12195039510b0804c1d0005e88245801123400220010001c207041c106103009008050b0800540390061848003019202c2c6a1051650415410100000300c1d45454130b1f481c1501400c80d801010740d80b21140d0342e04000000c20804040c80104000c014032010a40c84984a07602640490340c400200e410003154100800540d480000c155080c041001622400c0e00c070414829802174036842c0243c2e482e140306010b441200303868000303020042404940500001c1e04030298007440903104aa1058851001a15100e000c5411034002603003240705010342030081c4524585084d0000d9030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 22685626 1250 22684376 22684381
    0x1142107020115030b0c0403020604030605062d010c0c0906170d02030705030d0c050915070302060c0910050c0a080301150212030601090302040f0603120e040506100206040f140601060c1406 83
    0x61038110f4075103200241c13601c401d8002181d07002000104a4001f164001c0000d42d03256600e1a01501503c4119030840c8101d1300d17400d80303800e03480000c80c02804d810154800075201b50079001c0152042e5050000c180c42d0399101210203c0c0760700c01031040d03001500e030190f03101000158851100c0d1400c3c21a240703041c00c46d0001d110031400501e000040d20310159444801048007228541c040307403d806200c0005030310010892005401c200240e00400200380a80e085d6441561083c10952161041a5055401440e5010a003103c0340c480d0003d04000d0f25040706903000d210240e25091215002070300011850140312a420384140c0d010082d00c0c3c4105928007010341107250100000c0c00e44034481c030000e40100e841e0031303c441c0c0c00340c6150b0154001d0343d0302c45800d10219003040340050580803103400705402035181002044203481c1100e155140034001e079000b03000b2660380743c0c1c82c030b00c900039001011203200184454000180c8805c0c01002e0180507942c3c0c0341c0c66141c2e42d41c10071072448a0391031900e5006030068000e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 22686876 1250 22685626 22685651
    0x20301110a0c0b07110d08010602010c08010302030705010f030905010c08010501020f06190509100908030a060b09030c010f0908060c0a0f030b1e0604030204050f0a05010b1204030e011421070201 85
    0x5844141036040320f141c05031660391210640350345407070310000c1c40b09000f480c0c800f400964102c00c0546c1621081d034020042c114000d001a601030400380006541940300307200400166220b8410826998485c1c500800c1d020300300d030380d603509480c0202c118a003c500d00304010300a550b41000194045180c2c40000c140c50b00f00103403102c01c0403800705040380c901912a000122001000c11001d4001e5030381b11810409032420f401c021040e5041601e00b206160705105000400188640c1500e44400c03001340030b49000a02d00340150b54a145101881c014000310140000d010641400310701c0c810200c420300161748100300d490080414410b501c1c18014140f8040c1c8569807521900684a0008a01e005540c1420801d8000a040e40a10345c8003c0d8450f04010400500e05a0101c40602624059000703000598070303155001847c0c00303210741040100141000181c01f107032003008111620340c1c042c180405a41030341c0c01407001582c4040300881c05402240300035107400141d590b4041d485140e6100800625250b41c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 22688126 1250 22686876 22686887
    0x1109060d0b042a080403090503060f06040e120f03060406030f050106090c03020a17071101020409060f1202010507030503060d02040903211b03020f090901151d0d020d03020f01050c07020301110a 85
    0x14000130021120005400c0501a0b10b1000c06030000030212041880c0001504225080c1202c00d50300032828844009480b8400240031505080c4054000d030801a503e107005a054100804203507110781c592070b0010100c3d010b002c2400c2054015000860b40c00d08000c20503007a07540011507030341094410040391252a510030281c3c004c503140800c41c2c10040d201d0000031166101c1800c0508480c2d48001400107103000d071369000e141290070091101000382d0340e840040e140d0802145011340811807c21403440000d2060004540c000c0005200c00e03c5c0740440c0d008a41102c01660044012424140360a500c104d1920b600c01201c0c2c4002006024120211038031440e80e05080f0160383c14990007003500c1081158a0003522003c20015110584541c2d40712062180002c141a507a03000c43c0180d0080a65280340700c0c0307000340d0708501a0410310300c66110b41c2030068040880c04150110f01070300c2e00d03d400e400d4080c0101030003500c0b9420060b4951945c3c1c0101401c41c2e045680b451705088082249601d4140c100c0d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 22689376 1250 22688126 22688201
    0x3020a050913020a080a02030705040606050a180f03060c0e0906060a0f020307020d080318010501140d0218010303051801080f0f04030c080a021f020315041109060d0b04 74
    0x1a515034207681c0300c8070018100c0c002000c000943c000842840402c094200045d2503021074000c608441166540c2c03807d100466840e80150300000308100102c2c460b50b80a10510141200c1c1d84494400595a405002440b0480c0350030844909460f00d44055400303034400c0380b00c070201e00304a89003000d904001001940f54032619007500b01744a00c0001161881c0d0090041e540070640240500c50181010700d4824103547c022203640c0e6003500d084581c20106e0304148503545c16580c0081983d9420300c850000c0020b40d0408450480c2e01c00000805510042c02c880001d034005c2d840f0351580790b200d11200420440b600d4844801604111082040212152002d42c0c1b282e001821001c486685845a04040b10364014214014081c1c20001602e60203942d030000b0b001c0f800c0400714000106005c105c1c40e952080e0720013034a061400807104c4c0035289440c50a68010000c041203803414034640f024a1002c90615040340c2110440c0036601d504408141c1002d02603212480000c04050040c007070b1040b000511450b04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 22690626 1250 22689376 22689379
    0x19031812030e01020f0706050906040c0506030c21090709090302070902070602070b25080702060a1e060801090b060603010302090118020904020309010203070e06030c04140d1403030106080f0103020a05 88
    0x4503405001481c041d9000501c400c04090081d0f50300e0b04251885052648100400c036022490000010b480940210340c41c0e01965109200148180c54401040341541010b010b1a401a604200700c8443c024042c40f00c02618040361790170a142d20f06807152504016040d80300516135030500d501c8000180d40416004d040d40c0c0007a00c016180d005905016009010b10b003001000340008405011254803810303a12280110780b000517988070303410203a00711500802076880d5805684290041044820607810507a02c1301c803c024610010a0705807550011b803007a07a4003900301659201c0e04002842500031902c1c2d031103001030b42c419240d0351544d800304510311030500c40c1e0581d00c04c454030001c2024806404446c20760a0041041d5207030304188d03504034001d40c01038070039074085050001e83d2a594140001540d10541c9400300703543c01d0030302d0100d55503407501d4050010303644054005d075004c1c00104840180e0950721038982c02151603606188020700742c844060300440c00100c44030010030060351041040c0050303810 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 22691876 1250 22690626 22690643
    0x907140705030403121808150106110a020a0b1209010209030703080c010204050a17100c0806010509010201060308070b010e0106090302060405060708120114040b06030f180a0501050c190318 83
    0x5103824414214003c5800c028000045000b2403d00258440b03800800c4407039441004010540e41d45050343e91b038210100e078010707034504180100031345030052070602180900b031b900792103040890b0750000d1040362458000b1542c00e02c021030881600343c04ca4a00e207034040210b600851410480344000b81d030f00c80803480010700c03107000068824481d40081d019900101000f03089808015241d0805c00c4840700086482d1609104102c20801d141880b8043c05401c00030f19190f282854951000441355603000091183c1903648540c000000074135040c0040c01400d00901c41d60a955051004c10000094184d01c07008c2006040c540500c050f0769800111401c0760070440e00d550780d4401da0700d01401c081c0101e8000c140d00c0c4e442d0f48000100c07020204684a5900f80c1114100414040142000280c1c08160390307100701c0c3c1100c080021180441e0303000017042c401d00700e404ca031014406a91ba0302d0a4800440e640e640c20071010900d24400c240c00b01c200c001e0842c841c14140240b08070514505500b51481801501c2c109 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 22693126 1250 22691876 22691887
    0x503060f071e030911030313090e01090203120a021e1f060503100605010201060b070b010e0601030b030604030e0103050112050307030807031d0106050a0f030203070905060102120a02060411090714 86
    0x50107640300400c64185502140100301000c58080c0c0280b200204c05c1d1020f501e080b000d816240b601008a403240303403420480510071406c00c002c04004152401c03986103299690a02c420246c0e13010010300c0030034810040700b50b66a102c0c030040203003444401e07400c015462400007150706c42c0b084003040c90440100f420644031240540342000300c01030549a400160140908044092003201076004042552000c0e0000c1c0810b654800f1071882d02d11030720030040c0070080490010301030220342c1103407540c118205141c00b203810301072880001d0030b082090750b0880c041512103110303003031079609400b1300d60050a1030300c4e2250a4141c01e80366680c40784115800102040381d00b00004021500940c0502078207101044d44030190001111044c0c0282a64016107200d080303a03900c00079044060101d4a030940342d02402520405142c4641500a07140c00307001f00341940104020484410a5000a01004401c50780201035a0525051200c19403c9040204c0d024480641c1001711141d00006442e6040da00d000d582540c60 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 22694376 1250 22693126 22693141
    0xd081602030c210610060906121b05030901050105010318060b150f04030c0b0307021905010609110703081303020309010c0201050c0102040803031f060c03121d1c03060503060f 77
    0x22201801c1c1ca98010f26032442d5a00030040c0000703500381481618100c60040c0c5889007940400010752150f01c0010703030680020701000b8800c110414288401ca180400c0030440138402000540142041c0300004801104004030000240103650042000307080800c190400d00b40c000c54204c0c8050030140c01c441e05c1d400102c00c2c0f6100c07074a145009107003a00e8551303150311903204112019070052000340c0301041c1005020481d20f0000048a019507007a4004058000c0b040607501c89050710224103a410307550b03e250018144055001c0d625589010b0f01d0903070342d91000b0381b0b0302070042c40d00501414699104450300400083e000822039500400c00d082402c840c604500c01201c0900c500d140e02801540003040018041c1e100101560140d1050205c10009216418080b4014101c40c4602030018148480201c00300707000c0e4000180220031070703802091800d1642c0c14280e0100301e9080d4132103164080c1070000484640180541c103400034502c0d0611950f40f030a400607554405c040c001c2c40d4411400404900d40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 22695626 1250 22694376 22694383
    0xd0c0f0516080c030d0504030201050604060816090e1009030207050103050a020a090902030603070306090f030e01020a05030304080d180302060901060f05030606040b03150403030507020709050403080a051f03110f0d08160203 98
    0x2001e178058188801d1501c0c7c1380c024081c08094400c1d40c000c0f4103001021403100c1000c41c54503c0020381c400b840c1c0c04a4034002009002e0b1601005c0d40f0528054400c0c6a502c00045020341c242480c06900107114103443c0000060488800030900c003100c92051102e2210254462003100403142d01c51009606c4e03880c2c400000f401c0075001d90004010b185000760b0361041002c05500c11000340d0182c4c5500b0700440c2c2c1c60005989072146020018069041000001d0010344400c000e08034040c0081000592130348084103002508400310070541c00750b030140c020011415024041c0c2809002008550440c1528000109503280c4025251900c1641c44615020f01c0340c41c10018542244082c0c0115012030510381400b4005040503030740c09006010f0316001094005003402103d0080340e143d5a0024550340c1e1401120040c4405032200c00d00290040d61031710540f80c0c00500d003002d1800703450707034400708001641004080c0d221100c03900d0140c1003800d010004030701e515041d02d010301803228482c00e60074500e100103405d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 22696876 1250 22695626 22695637
    0x40204090606090305060601030b03030a0804050c0d050f01050604060b0d0b03010209061303030e010201111209070e15090a0b06070201140f03010b180d051b01020709020d0c0f0516080c03 82
    0x80c940c41d002000407150f51264541c81240e020b0025107490303840d440b0044060b900c580300b103103030998000c01c026903496100e9141d075035226010b00f05843c145a26800006c803801b0600c2c00c01c0d00c45900c034918004601200384251500501c0c2118100040d44c030b0948600c0850041c030000441040d03a604840015440c20b40441d00820402490fa0395142603400415045042e00c0c0803e070002a50004008519401441511403000080d00a241403400070b2034480e0342070380024102d0109014080000074120f0030042d4017402480c4050504600958031400c2c001c4030035000b040c40345094140100004580c5031032040310380854080c64420124030000b20307a036240d481452900c1072000344c0000001224451304c03001d4000012031807000720300b481c40300007004068140c080e0043c00c3c030380081210840e644000d04c03d2402e01c1406006442500d940c40403c0022071704501c82e00c0c58402c0d142c203201231050380d000310101000030541c03e02c07508000c11506070607904045014003c0c0f5a901c000b50140c0c4001003001542c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 22698126 1250 22696876 22696889
    0x40c090b0d060315020301050a14030307020909010501081207020a0b0a021207050c041815020a03090b01030b071e020601150e04091208100b0d0c050c070e0402010801060905011b02040204 82
    0x6655064480ca2000201074074032050721350491a2a002c10718103240d0086904a50004120f034181c141881178401c1004004004a9811b00c0100f0030000141c480c002e2651141d0685000012039601d070104103802c044022511030a40a8104040e00040e601d1914100c01c1d5580d0313000c041e8541300355a00c00d03440c0c130941041d464811103000c500e0404110000504002243d4195010b001035914a0043c40103e06c0700a030090440038640d10008440c81254060700c0c0540c40380c41c0210304240c0580320540345501c2030b002a50780750448020001c04540000241203910181074600c4999501214001d44034030040c05a107064098920380000c580d841452428400d0304001c0c8200a6801c844c03805036042c9e4003000b56080440c200d1400900c02d11068103040044030b82d414400c0d4601079180c00e02c40d0091007000c0300d5105014040c4240d18010404018400280120510b9802181068000580307c02d0050b44540c04000d8132140a01c8680d07842000482034038481c0045c020b20300310a10026003c1d0080740c1202 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 22699376 1250 22698126 22698149
    0x120b012604031704020d0212030d020c01060807140901090b010903060e010b01030b1002030d0207020a091401030b0f04030c0803040c03060e0c040e030705120d0e01090308061806030705040c09 84
    0x2020016618030540c0150700c01d84903050b203001c0210380d025107820b00700c0380a980f1042440810303016041401d5090015540c0006582c68507156080110480c2c2200b1348a8103540e5440f4001e000c89001089040081c0c610503403040c095490784c000040907101c0500504d0091516480104640e034042c056000c0510b41c05030042c403114608440b03603070013404420100781c0000d0070155007000350b0a0903090b10800302100c1c6d01640c45c041041103164042d501c08941240c04c442490301c001426800c921401a0b4000046800c07802549942880048001c0140401210480d01c005010010b40c0203c140c2200c3d83d44001525140d43d99070820b03040106903540003901480c107022000c0843c5a001c5104080781d0f40c00c0b80c2c104580327500f80300559501c2c054120300510961140725440901c591401c098020f00d119160041004582481100d080d2428014201c01051940041c000a4500080404c019030140d462040481c90b200340040d40c2e6000f41d04c6500d024594402a01102a1180c180c001c050001903021 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 22700626 1250 22699376 22699427
    0x207111908012909040c26010f0c090e061003110c0a030e010f0305040c05060313080a020307060608010509060a02160c08061006020d0206060f04060305150a0b010201060303120b01 79
    0x4412800c40c880b41c40f1090300540c950002442c042142c107000395001502d9600c000c2c01d1500c1118417544100202021b480301488400460b034003401800d6551002c01c9000c41c00d07000101c00500030311000d40081030354032a14030400420352030f11141c4941744407007072402107100b011025601d034652040400902c03031406024403003400c0c141c000181c1c207481202030342c1d41c2d20041c0c0b06140480403650103503802000c9249240d020401e03850b080000d903801280d206030443c9502e185607104112503000390505c40250b00082094000e21285100d00320003070444000034041c03494005c50180e2584030060400c0403056000c1441c08144401d100340e070400607445400e9810540e00c4070907441c0e036400c00b101e024411840c0f41d180450300c40c1c808aa442100d280c00c1d0010809502c0740020440010405491f694029655100c000003042081041d02d060150784203e0201c0b5051960140003070300e8881c071106066a040441c20400a540480c40c82900482c0450020b1104078100040700e100c0c100d029000e000c0d51100f800c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 22701876 1250 22700626 22700651
    0x30b090109030e10050403060b06040b030a05090d0c12030f0e0a0b01050301050a02040503072108030f090d0302090f0402180406030b18070e060105071b08030a090504020711190801 79
    0x1000c6040c5009071143c42c40c0d00400010010504040c0007000001801031000304000343c0c49030000c038051400144100d007455102c1030b440e90242c1080340c86098403901c4e2410f000d032480040c0050301041ea01c84c901a940c68450f40c90b4450710f4840c07040c1d20b10070591782c0c041080350010b00da0302580008030400301b51143c06206040211a0070801e00542d0b20030352805001c0b0ba24031205100700d40884502070041d03ca01e510300419001004400038101100c05c2e0001840e00c00036554500442c03103030084c0c150002c0e045c10414040c5180c00b1b0250914814188101321013942660f072048110b04401c0d0465002d41c1d81d92040c1400307010000d0b01c00182e904a410068003004100b444046280720702c01351485600c4a040301c460f03c0355140f40071320503040c210342a80c0100e140c551007400181000c3e40108000740355031001390b100003d206500c0d8070400d12500003003030400103d0750200d540e60040c18201d4086d0f007400440d403035800000328015030b46881251328562016001b180030460100500d103850003003015055065 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 22703126 1250 22701876 22701881
    0xc0a0612050c0301050a030210031e0e0c0111101a0409050105071409010c03030203060105130b040623092806080115080411040e0c06030103060f060b0408030d0b010504030b0901 78
    0x311501041800c100018106071603a8041e24122940101424282c525503020f100e102d16102c00301c04100358460703e419070031510600758800c1e400440040014408941600142000c140950b018100843c0c00b5503542c00710700000d80c02495a00f00b000024203d42d523001d41c00c1174041c2e0b9000d40740d009404c12035410140702c0d066202c1c511400143d25104d03203080b50b07852101264400ca030314085c040b508101265012a22943c040e690103d0103051142c03400540203080c03410001640e1000c4180e0500003828007549034443c0a036078400f0411101c2d40780001d000000b0f4015805400641c5002d074101d800c0402e900b82c0c810800c010351403900d001c064a6039444041c01003a40e1802d0140040e40c15681c041c200030350b40b26092a81c421600300010010b264411000c0102030900c50400740ca43c0c3c4142c0311340b120540c1c0ca0100840c000d612852000ac0d200900840c0401626055840105610020305c000c10100e1b80100858080d9440d4080025450780c4001c0103036401c2c09240c00150131007141c030041100041056 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 22704376 1250 22703126 22703147
    0x3070f05060105010e030a030f03050705040e190e0a050604020609040603080a0903060614090a0e030405130203090708060903030c030910020d0902091605120a0905060709090c020a0b040b090c0a06 86
    0x20ba0314000f17003120b07002c24035550f1015200d00400041d601c40200c1c804620076842190030100c03910341305150950b598404101c40300251198003480721141540900c9445034490100c026000d1009058250704680300c091316040000c1c40a40103440c0010061021760761580910302a651007100036440c1c68000340f000b800c07524580011070700a85410400303d84a540d81e40c000b040404020149110396a401d2200406000040818621031205000100b826a2107a95005414041e0746005803280342c4043c0d024034000361540304018503003090050011400d4040200d03944604420100d41d525114001d21310301d05580c92554129051011400742c49840843d0040100c8a00813075100820ba00c5e041380c06011490304035444000704600700700f081d13804e0406031685640302d03802c03010001c1d20380195102c0342c2c00c00b07804440000014855100c02e0100360318503c40c032110407456100030080300c403056a41c603131410b40140002e00103d414100050399a502041181112032000e0499441903548090213800701445 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 22705626 1250 22704376 22704379
    0x3200a08011a070b06060a0c080d0207031206060203030402060307050d051302031006050901050111010b0301060303030b1503010302010c021315030b100b0f040b031b030114040e06100e070203070f05060105 90
    0x8003000ca02000e1000c0b0030384000130b80110a03102c280d107900d010800a03902810810b4203000d10048008003081c2154041c1c40038818520025030f450405160050001d031035084c0c180c84091400d0800d014451740042500d0b4000e80c140d40150f0b6a407502042a07941e4090000f1140c000d605042c2000540c0d42c104c254040914802d80846900050034014001524513501031160001d40d480d00404c0251f01c2002d80c00c00843c0301c1400054160306107000300382901c0c1240c0003079001c2030725546020700700d09140c1c04000003442c641461500319411079000030950130121304040d04ca441c1a001d03012041c641c55001d05640030141100c1d10b2003e64070b2a050b44900012518190130384400400087d46840c0c1e00c0403200c5050a582c0040e141c1130400c1e64810f601d420241c240703048a200390f1000c900c0e280ca0030f03000351b010301034a8440b401da020880342040161114002c0c1003040390442030a00c0100c00000350808160307440007102403102e03503131590b040780355000d84c08019040600301001042449000b15034036060303840 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 22706876 1250 22705626 22705649
    0xf050c011409090402011809050c07051c0507030c02040e0102070506040203010608070e010e0703150b18180402090408090409060509070b04030c21021002030c0c091603200a0801 78
    0x1030160702450640140040ca0303400030840000100150301c00c1d06801940d6000a032101c130025100c001000c2150f03411a071b62003480100054040900204010740030070800300081c508441116078078010030601400c0b00041c14085d81c10084811965241c00c28040d200c00702000b1900d0741c9081c2070250362080107a0703090b40a075182000c0881d80341400700700301703041d1420401e1f00380407646000d482907110301c80200f0450030503688000c080c000c032030002c0c03040e401030140e0300702c2c5611414400000000003521014207032141200e03100c2909480403240c81154441e404640d00883d0303644905080c1d025104403030b2101e61051400f4005030802c940740d032200e405000301c44201d1b07103441e4079842c0c04500d92245020103800060240e0f8100500ca150703612941d02032000703890a86c3c41c0d040950108406142011003980940c2001c5840f0501c000304002c01503101c00c00311608901810b10f4105411346410740c640600c2055126a4101c0d02e8010082c90842d40c0c081c00f40e40c01d03988191003440203040c01c04c2800f0b165043c0c1b2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 22708126 1250 22706876 22706897
    0x40f030908030c0d05030921030108010c0305061005090d06052a0c0a1226010905070f09061b0212010504050607030b0603070e010c1202030406030b0102070e040b0c070f050c01 77
    0x74000150341025450200030b040d0f00406420907a9550401444462580710301c078800c01c0c20007580c1410b0441d4035840c20741d2a44030f50410b04803d09441c8442c80c00ca00705460001048542c1d51080c42c4801c00c2200703424510b6550174604042000d210f14040c000d01903d0405052100c0c0491201c000c40020600360000b8141a401c518104250b210360100ca200d984d11400405010031240386d0148000c00d8070b4140b407a011b0706c0141d00c440008990956507015070310000010041e4811a01038650300c55024034003070300d210200080c05480e05c110b6000340010882044800b410b01c4514581802130140c00800262544000d4540e03240030b0502210304852901071400840e4800e070183c0200c1c010400c0007007429007156221031040743c1542c034614a69042000c0b0f1039440c0017084145d529620b1003040780c3d01070740d51107081c1036003d0180d8403130709050b078115030000c1c8080100100080303480390815409607800400e500c410f401d00d800750291600141c401c0018801e50010070800080307000c0e80144c01c1e00e9041046 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 22709376 1250 22708126 22708139
    0x8030406031503050604080c0307170307030c030b01090b0307050d0f02070c0501090b04090c03020f070302060105030d0509010c0b0903040803040602030901030f0605060315120a0302010504020a051210020d02070803040f0309 98
    0x328003c2c44003c22550210010400080194001c0d00c02d40c801c0c8401c0300d045c9111a1104101d08034403a101d204605000420f1001c00343e40360103514a50321141c102803181d00c44d01d00008100c00c4691041070400352002c0701013610b10780b00d03000300c840b401c0c8494001e02401c401252203600031341c0000e42c115584651030074001001d50041c03484004880d045011076090030300c0d050070003015240c0140d944003010707030030040707408010300380000b506029002e43d00900c000d43c101000c5c11314003c000811181400b005015160b0b03140c2c1d0140201c0090341c1d22020300705054940340f410600d50700454212501034040440c5c0403500f03d6000000e082d5820b0243e0b0144240034960031000225805401103039040310040001545220001800162000c400341c09190001d1100b00700d642000c0c1c2c500c000314010303511001800154075180071030308050141211440c44006106000f0f030350f81d007550303d0f82c2000c0540100e0b507050b41c12034a5040c5c440c0e82e9000103100c2d80d1b91500b4504104821340c40c0c00c01300c011500804020494 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 22710626 1250 22709376 22709411
    0x6070905090106030b060f030f060429040e07030804060f14070c030305031f14091f060c030c1b05040e1c031104080304030803070206071d09130501060803040603 71
    0x31a640075040341e140340d0900c4001c5000c2c011000586401440400031500146c52a20085104260042080f40c0c42d0901c0320410090702c20860004250a0760024009805500b005034210f0052040f1400205880104c030072a050040329800a89503040104001515542064100407802d00542e100140500d4884900043c0d02170100c0141c00004a500d080c03000038000e03001550030290741010708040c1c00a0070640e015000b042c0d000b030107030081012110482c506202d0350540d0003010000040484000f1042d040e4400d00a42c4503c0e402c21020130f1060341898040c03c902c072034290304840704c90000c601d070201e4120b501d09a4481e407030080789025a20038080d036000c203403c0602480c030380d05004200b2650004802500d501302c0c0810244030b08000000380304404000802c0250f124465150b180d02e4840301c042e09011005106805100d60001030051050300b60080d0003030342c1c004488e07410310340e140c40003d210303042c0070400b00600075131038001c0101d0f180c18008050412101d02e5074007400040210703440b0710364 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 22711876 1250 22710626 22710629
    0x20703030507020d03120509160e010b0306090709080d1d01050313060506030f0a06140708010e0402010c030e040f0515010207030b01090b24040614190305090705030a05030408060709 80
    0x50080c00b50000514000c0c0c2881c1c01c05000785050202a8000101107040382d00681d84040654000382c0c110301d6000b041c040c224020100d0240541040d8545922010b540c80001e0046209181c2803000540c4e46001d000c0e542c024000c040b0480706102c1200d40090101410268070f034000499050540da0a58490800c41e0302c18503280404a62039407407582d505020700b102a1840360716010b207481c0c02144500411540c0111400f550000c5401c2c884845000c84a0001501d0401008030344c0006002d5103861a40080d0490b0782840e201d8911400c90404444c0030401e039500300da101c2e04141e5045948800c0b500010300900b4420510030104442200684c0d03560071502c00106442e52680c010005c1200c03c0e80484c2c0030700c0380688104141a040080b8010740c242c10000118080004034060080680c024841050000e8500c085441c00e085100d0850800c1984d40b44001007648030000581307101c0782400380c540180800b80407500d00d40000e1070840e40701e030028000c0401f14822540000c0505204552400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 22713126 1250 22711876 22711883
    0x13030804090612030203340503071101020606010c03080406090f1208010918060510080303041a0709030201050415030b0a09020d0506090103030801030201121e06061709030306120114070519020703 86
    0x41c6020340780c150841c5c0c0b1860040c8014150440b8a47c058007140360360012540451060f0043c5503107072070b245414044503490340745550465118404100403660002d00060307003141c01d030800c20003540d554505800070b8055018010102c580d003a000c00f0230400342c04d4070640340c1c0081d600d90050b260780303403000e000c115141481150352244a61040c43d021401c268000c03600102a0000502210380703c40d075a0b4078650003601d003181e5020300e000282e49126528503070076030040340c5442e0403080107285400083c954010343c0101d561441e003400c65183e855001c0d0303020f07095101e23000e40745a110a0b07840303078100001e40001029410460070710000074600d01c1c005c2c0400c0e040e25407640700c80441d41d003103400440390708044030400685c8a65900f01e0b00e0140e18006000401501d6600e008070b8114142070740142614041c003010211031411405000c0702c0324001c8140c030351046043e0303020414413001c0c0c5609405840340c5a10351600100942c144610329501c02c00401550354400b441401142d49030304100c4e9200706512025 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 22714376 1250 22713126 22713133
    0x50108221109070309020a0b070203031e1207081b030703020c100605031e0d03020702030f150402010e060304050c101812061b08150103020d050907030606080c06040510020102130308040906120302 86
    0x901241c8c80c80c001800c80c140c005070440c2e0421184844540300c04450074042e100c0081e011440b40d4000360310602041e40043c117840c1203082410003075007070401030024401035981a000400001c6445109074143e4400380d140c84110ba510704181c10080d4000c07d158056140680200c070b445401603903c82841b0700031951041c2c01483d99218000302140203400003401241c0c07601072040c01c040d552000b04800c003080545983c1103075040c1030030310015003294100507940740501d805100b000089000030821030b0300301c01d081d1030042d0100c0c2e400b40308403a4950000e0b200c0200c5a8055004680501050f1001c1080d6110340001c008414181e002c004a02114101090016002a00190200040d403580074400c07081810301509154070500c5a2040d103001704c03018400d075403001e84100180181e5001e001c00800348100506245a208004103295100c3c1e401030764041c0a484424850300351003541107130742004640c24220801d035124540400c455000b0310804c004c15042000101d112080e000d548044c10354940c004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 22715626 1250 22714376 22714379
    0x60718030b0403021603050c03070603050c1206011803060e010c05090303030a15030f050d021506010e0f150408030403060b030714010c060902040216050712020901050108221109070309020a 83
    0x702001604020800c50860003020b20040d65009000e008001551050003d0200340c0c081805061030001c6940c45042003504000600980004c0fa20440f40c0002440007170001660701c2e8001641c42d1400c9503050a503401c64001c2c0042405004d9216014044040c0700a006107040346604803050700980000b29032540007000443da40400c0d503800310b103241408841c0e509040f030b56a1074140940f10071101c252019008076004200099040c0304407441c0d0a00303480c0454a43c1000c4000a02060301030885500070600b10b40c40200c2c0740d03920050140074064644485590b03e07298840141c40340c025110880325035040c420621103c1c900499000156511424050fa403041c0c0b0390700444a91000404c15106070f50b85064580260b00c0d02e0000b48203400b40182d80030001c0215103001440e052546e488541604640840c140041c1d03102032000341100c0c0c0c2460680c01c80d4499070b03c0d041481e40085d1320007401e0450101e0400c104283c1e50980b071605076085884588035503803032200740c1c25201000002544005032880 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 22716876 1250 22715626 22715633
    0x1109060a051b07090e16030b0703020c03072012030a08060f040f0c0806010909061202060c1606020a0c08010b0a0306020a09050405011205071502030d020a0318060c0206071803 77
    0x80c201490340da0102d400d40d8110561001c1c1400c00d9070b0030100c106516071038050700c1500100200b0446181c104801649903145440701110078a01424860415800180d8011500420000c0e40c1000343c000755042142440726820900341c0f184640d181d401038846c0c148080e11100d0102c10b40e08501000d84a01c102580c54000700001f104598003007580c4150b03565040300300041288a2801300b0b61281d150003200e410000300250400d462544044d1107a41003030802d11610b030340340480b440075a50554500761105508404c8a0600d0030303404804440901801c00000c1e0306900040034900755008502141410751582562803d0303402e401105604860300050810006410b5401400c580c0300070300d040075846440d00009801e0b11000c2e404903640005420101b4140503080c00f288008200008440d0007201c031842d0701079141d0046040d21420aa030205620801c80d00a4210300e01c0140c0c080000119520a0b15003540285180030322040144910000904194003500c455a03040e03641800c8821120700d50b50303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 22718126 1250 22716876 22716887
    0x50d0b040f020126070806060405061204030c0b24040203010819080c1506120105040302150a1103010306020a02010c020105090a0b0406150b18030a0b0604050a0902030d050a02011109060a 82
    0xa008034108403c26000c00c1244d090910464041d04008002519909182500820000e0054185c900c60001000200545e988032401c481c0d01c101c0c0e4505080507030355182000e0b20381305180d80020b0500c00380c103000c00082c0484008080ac803131480c0d4201480704841034040c08200c0c0002d0268031840c1d4440ca00c00d4036800c01c8004810905071040c50190b1a02d20f00f40701385404c207940c0c1e100c549806084803060194500d0030450403404410b418000704003a250903100251f0b01c2d4414510010540507400100d50194600d411030700d203000384030540c2d07641d070359403440d01d40000d500c40c040b00d40055180001c101e201a1060044500801242c4010b1900405036150945c8044000d082125010350343d000c10061042d00416401c0200901d0600b29111014004045220801401c5951013500103400600019243c9203c140c0c201001b40c070b0020701075440b1500200180078011000e50306201e840c83c03a10001c3d60140c01040344c405164004d003d0488200b030709481c40d001c0d68450340e61000060041d82902442013 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 22719376 1250 22718126 22718153
    0x123040203060d02060415080906070206180106030f0b271b0f0307080303040203070b0405010801090c1b0b0105031002030c220b070507030b0105010e03100e030f040816050d0b04 78
    0x180841a4500a84d00041640e40141d100800380807004521048094100b8012a07004505c10080d095601e402c0034000d442d141d00801e102c1107a401c0344040c0070720500950040c0e000e95031204c40300c804c1d0146403c151048a40490f40c00b8107140304d820210038801c2100020312400703c081310080c1600c01c02848030b01f02c0700c80036002243e00310090011500d660ba80c00c01001c0000e04410011319503e003042c1c0181403d010464020b001c4070714080000b0052640e0000c15681140e002c100d0014010f00c03068403c031387c00e0018000d0a1401070600301c00501b804403100e100c6048a500710100d0b404105040c0f40002a800106e840c0740c0703121001e001000900c400d64043c0940d401c001603c03506d0107500e4641044103904008020340c0c10340c0c44990103004000d148030403507001d89803d08025107076410b0000000d66034100541945803d03a12140350305900c003c00c205032510209420003d6444030b07220410541e50f080c0911408015032064100040c04d41480a03200d0442c60b0003001c4180c9a07550b503280c0e0382030a03945 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 22720626 1250 22719376 22719379
    0x70809091f03151103010315050c0301120201080a0e010e0105010f120305030c181f1209120c06020409060b0d06050f011205060d06020304030203030402030c01180314070b0a1205012304020306 84
    0x103071010b00004a8240300151b010b903115000242c00301e144c410030703102110001411100c40720b00800c01440380f8001503217a40550b5509180c40e0b031a0341c2c0c40e01c480c40c000c0e183e00310700a010342d800d00e185560042c00640045040c0d80800c4000d1200c030b941d0300280b40c8801d08400000d00414010408500e0381d1842c20024800d02108202c0d501050f1542c01c0400c04014000115071900c1e4402e403241d142042e03000c440148140100c040600c491074550321078510f140b45541c51001071248400600d010011035806583c010180d8035001c008003540c0c2c0145031519800807501c1205249414404a254036120300724201c80070b010703035030b49550861844d0102c005200113080d21358000c10107402c1d03000213491070000350b104500c6a4003454403400d2501c1071614100d6140f0100d810711001072030481c91090054003070812260000c030404080e01241c4007450400c201c0340c01920005c08000b0f281c80d0340582105c04100c20b460301c81010000d680c1d0703d40040b00d0b100c1545280701089040b0300c513841107a01d81030f00a140c200d0360 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 22721876 1250 22720626 22720631
    0x11011404090b030a0b0106050a03110a08070e0103060801110703030501081c0c080f0a03060305010e0d050f0a0311120f0702030a09090c02010b04140603010b01020303060a1703040902070809091f0315 87
    0x4d5220b14440c0e88003640908005400013909882c055814000d030b403c9a5414410341c2e052405540d405007c40000900002c00c202d41c015038440143c0c42600701c2e40080010000810002c100094540d6a90740101010350201c1c0c03c04000140d000c000152024082c1a1003518509103c1078507401c41380822290310641d9400700520009070300684220050003142403648002500030b06d1890241d0075100407200a0300b168004403840400207410404903003da81c8864800c6690b1500c404065008140e455460768406c1000f1400103070360b505060040d4010102c0000748000c550740d0440887e640c1c4200d048240000c1e1503131400b04011082030300700c845180b102c1e0001040c0d45900c0400305048030120744800c14400310203000d100301ba003020311804d05106001e00c0994a10326000000c00c2180b03641c1e1140b5401d8100c50070006c8052a024800c0d14003810030304806542d01c910b5810f06c0b00d00f40d0044075009104c0c3c180c0c400030514620180030750240741003906a81111040c51a120210300390081c0803000c95064 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 22723126 1250 22721876 22721893
    0x70305130b1809040203060f13050a051006080609120a03060503010e0d03060f050607080a090e09060106030606082802041205030c061513020708091c11011404090b03 73
    0x3095000d0a010700098552541c8844280500c0c01c00e80320b640d10700e5402600040c0c14400980ca020442ca60b0000184036207039502d4450059082e2040765812000d800c50151940d03280c10008046030300c14486501243c00e000b100c4d243d40d441a102c001c00d80d04e15200d540541a04401c240310f850142201c4100c504000400c1644c81020071309580203885005020780041e180000c04079090321911740a403800f24202982d65042101148892040c06000341c48141e0100300300d0440c61003461b04402810600240404a06007120317100e13a41d40080c01181c001ca4140100803d405104000d140c2c8548072910610400b9032401004006464000003038041c0d880e02000302080c20740c482404800d101d84280e0045541b41400b0012500b040c1000d000b452282c01103841280c8155940040680720000040300146c0c0d8511318548174100b48143c07102e2503006000492415144154482002051030144070030308281c0c101000115808500300e1a81e181c02c0c1014041481240000da226440e6010083c040343c0100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 22724376 1250 22723126 22723147
    0x402011b0809091612180516030b09060f060d020109030c060203180306070e0105030c0405090f06030f0a1e0206090405010b04050a06020109020609010509040f05040c06270308070305 80
    0x10245900141c030591400100034079a030509100d100d40c0b01a0200e1680300805110b10010580307068486031000c082e803203100b41c01205030854002010558001e00301e4400150080c2c107905811440e200555200344030700700041110781d0109071503100c1c0700d1207a1400090b0703803030000f00061810300010503810000701d600d0201c0014800c9242401600742c41d0000d6071542c80041e000b40e01015651001400381c0c102005103c1d182d6005610701804d003209013000c541760303541d41203840c05a006950101d80e20414080510a42d01d030301000482c0242003c4d420790325440a4585199074a4010020040c2107688030b40c0b003400c0c542c2c9521002402c081c0b00030300740352400b10201c0018060f10000c1e04466a00b280c001020811440c01c40300400040003180004d012810050300020b0380c40c05205400c41c180003001a8450003607a50b680224440181c4000030071040c00d0238100000c0f410500d001d810003085051050782c200280300c40140080546c094941001c003403c55558241c6a005501c0c110280541031020741d505 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 22725626 1250 22724376 22724417
    0x171206130e121308010905030403032105070302070b01091e05060409050102030c0901030c11032502030d020d09050a0b1605010908041202010906051819050307090207150209060d05040201 82
    0x50422242c0d40d0f0f150803400302c0201c000320181d4051895a8509200d01300002c0c0084291001c032505410000743e038049002100c1d00c080ca6008000b01c18515010030000e0349501135000d40341190061902801907030b2698082011a40c28101d1841550422040c21004492603088140d100700040d101249460095540c5426a0425690303914461000329107512a96031500c5841c1205000b840c0c0745030103091040c0d42c1600c2e44516244441408020000c0488540024981540340c91307028003180d5000c5d540c50030080d2285106d074040c000045450800040500d0051004816600745202c4140b410070312011809039094291000c0b00c45540710039859000c80d054101400c01031107010f81410b0441d05500c001090300145400c16020b010003404030285803000848801d22080c020b440304804211403505490741104154002072f03041c4519a8003142610030b50b005001202c0c0302e6121518014480c00c6100f080c0e024851106030040401d211510144503183c0105402c2401810410800428031609989 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 22726876 1250 22725626 22725643
    0xb040f06030b04120e0d11041b02030304170a051b070b04031a010806070503011401020a02060a0509011209020d1205040305030a030203090c191e08030c060103171206130e 75
    0x100401c1c0d02c0b04003c00d00c40f244441c03500e44641854101c030142c0e0f01800103005402c010b2006024422003070003042c3d260701e9075030027080001035619601140311702d04a0004e589038401c480880e48240c0c10b960200e00c40720558203a0300c94020a40380c0740e003400c001498a0740d204982c1e500c0310382c076072084120004d00c120f41c06000308055030258040000c071000000310000d03070200c1a4032901c4580d02240c1000501680103007039030306440a80e00d10308003071114000101c0c039100f011078000c0d44c41480001c6003d41c60740c00400610a1b41002c0e03c4003d2198480106c500456000c0e00b000794000c0355100c40040000c401d01d81240450b4898200b541c20151261229880d42c0c00000341900420b0780001844500c1e0020084500307003050840303405034851461007201a241341a407250b1609c0100840540d8041c456021451014001d0142220b880b10f0012104540d562020f10080e508845503d9400134a00c6c41901100d02601188068585070785480c02800132101035282d101400540d074402e40d0005c0d000c01d03c0380c4e01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 22728126 1250 22726876 22726883
    0xd030c0209070206011a0304050c220e0705030604080a051b0105070e0402070c0e1305030d090215040f0b0a05070b090106060305060301060806011202041506050301030b0711100b040f0603 82
    0x966940161050058484018040b101036620080041008150307000748020780c08402404540c4985a03071420354904011441d08607441541da40d0366170030b001c0412040d404084410030041c405a485034815980b50308050240d03d4068001c08001000300c0d090300004e2405036001e1811511745550f01080320302a45441e150300302e031039440720300340311405a01410340d0403011011502140f07046981e030354548410b00184100d02007140d90100017005080b401141c0f840d480e8121090700d9480c1441c0000710000d041588089101d060b650200a4465181c1c03816102035440603104c2105980c10311804400c0303070300183c2440c01000410000840051444403010f40501e130500e001040700c500340350000e0190f4900911281c0070740e1401c070f004c012a01380080ca1038112903042844806001d601c1c0041000740c020803130711219104202d640041c003294880300841c122800703908420740a44a601d822519681345460080441c1d01400106c0903054056118941160000f840003e10b0032603102c900302540d429074400e0307 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 22729376 1250 22728126 22728137
    0x110a0308040305150601050a0c08130306020304060e030c07060c020a15050d06090c050406030f0209030604081b0303010f031407090614040e011107141204090c1106040503030c0c0304050d03 83
    0x10000c201040003c01c0c9180a41c0c4100301585c50f01c90002440e5014034103109080011a130880c0381801148811200c00355061111610100d840c5d0600e840658003d40d41103034141c0c43c0c0f0201185d8800080259083c000d04180038241d9140350180803a451030a03410113a91100f1940c000254003000c211111300410400d84800c5e40b1603103101d000504440e42603114030013142c2840700c1c40034481d0341311089038295061800c002a15420210f50100203010b070100381d070380520450080c40280890400504064041c0c82c4505085031010300c0503d8483c04284228801d96052070381c1400003484c0c1c0701e10344500100c0ca400300d0700415518403980c8141c80c0940d10a00c41e100b043c408035082410240107241c2e401c40c0d040021300160071480340541d42c034800c20901420341d00402c050001041003c0c00403d180800c9443c9641c1c44c1c0d501c5510200050440e0741045001c00d815800d0300c0501c11010420034415601300c1e02070f508507568188071129642c0440710a1486001c10040403801d50b48a11681080d0b500903030701c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 22730626 1250 22729376 22729379
    0x30206150a150203040b1201031203090b010b0c10060e061009140f060408030703050409050901090b0106180f080a0302010608061005060702060d09061b0c02030c040504110a030804 79
    0x190400102404a60400300c8080200000d616403805500482d03202c1407846000080300c1c035049055004035008200e03542e00003e0748201e81010f800641d4180c0340034283c2c612002110210035401c87d0710300a4003c05800e10707440100000c0c13400c0005890707c01c54010030b4886584424010b84100c0c0e4050f0000c01c42031403d0700500166080075003074108580183c0c1400c01e00c00e401c00840f14028521a0000c610505d8400300b01e015903100e160070f940c01014210101d94941007140303400340c542d030000e0041540e1640303044005200310a0502a950005800c0800b14016900b17040c0c0441d40b6000d0100c08601684001200080300340442d00c00100800b0761901603c0303602054a802030a4586660040040d940510107020407aa07195a1013000c40c0c40440e56150384144600c00708030305014101014604501d450780741c80902445404c54402030380540036a4444101d01c01007625a4016044041d405031701c01036500143d804d20b0740c8482d400501441b22030100c04c80120001d905400c058004a9949101040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 22731876 1250 22730626 22730633
    0xf0309070306270b090a0b01060f02100c05071511040602070311060309120d09060606030902030c0603160c02041503080c0c03060c030703050709050301050a060614030c0f030a11030406050103 84
    0x5408030080d55041e0103c3c0c10341e021540c0d0070020002181c080e00c91500f1601161402034208010858a03512030844a150f607582d0710003906c2c04001300d004001600840f407494000502da031087e58600d4410751109403c1c0855525242c040c210040055403020b90b0300d04c0c40d44002030001c4003400040c0010340c0145941030031850a41c9080d040d00c590356001c0e920520500c6184500400e034011400b84058020f40c0368019030034900c000c4c3c055504e000d0511351401c4000b18065505410020000d03000703070110380a003402e04013800f016100803110340369025610b480d460805482400701e80e031054002000881c40d0b079140c80442c0c02e240000e500440d04070000048030444240244441000480110f0142001d4a070400000e6007600c4014500c00c04c0680d6800001c50250180c81c40d40007a20018008204c1807600c018804003c24550084402140d58003444514240042003202c2c4282081c0300040d0130100c0c200d2035a10181c00c040d00e88103059440340b19103c000e890314030146225500410020800394035504 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 22733126 1250 22731876 22731881
    0xc08010603051608030f03090c09070f0e030a08270a080102040611010e030a050702030a060e0f01061406041202131802040f05040203060621030403060204080f070810050403050f0309070306 83
    0x5803000d468002441c0c01308a5800040251501c60b031065215a03602e5070360b811007909180b1108215a4410404d40501241c7c2d940032424031a20340154507681388103030409007015a904c3c4640c0c0010b029800400c8421401c09a070500070750a10b0101031904480540d8000244a00d01e241c1c0140718280c0d4085410000983c0c42707100b0407080b0f0780d05070081100d040c1e0090150340740d00c5003925041c03d001b8006865400c640f020009841d059802200c10800310030b0244180d600c41c4103d80495045609002e030118800000c0b10f000c1e40306040c0101960f04e032034034000010a030182c038160242e900c001080c9014560300d41c280501c542036a40360560f9990f2030701310720411080307403079144c880322800e0700d0041000b0040c0c4002a0a50308441d0803114241d020248000c0322441e502d07880c45451041c0004030700003081060540180c01500c1c08081610901d9042d5030a4590322110352150508643c07000340345800d401529808144c00500a15180f850310089112400040d40f0a0b00c04000325404290b08109000702407 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 22734376 1250 22733126 22733143
    0xd0e0a030b161b0507270903020c01020d030b010804020f010c080d0203190b010c03030b03070801020a030212060d0201050403060e0c0405070f0206090111040e13050d08040308010b04050604030b060d0c0801060305 93
    0x11030041c1c5610b02c2c0c1ca6160351420b2600a82c11400382c0300101c02d00c2400c6c1243d8a00148580f8001407101c02018036000b0745a050b0fa21045026115403102c40744071500a0240001d03002040c0d646000076603840e0200b182d00c114001c0300380c0c140100d0401000215241c4170061050300154503003d80e4038100340400d4100903609011032030805141800c44980e50b03a00c81d14000850781c00d4500800c04103015030000382440761640c40b0007155071000490192140c0c16401400108102d032848100560b03c0360103010f0a4450068000d0008004000501c00206d080c1e12481070780566404440c001841400070504581d010360b4254086900103801c1c1d00324560402003d40d010013110001d0000094100583d900c90003980a5004e0000418000482401515071034049a41d0498220390b469001290041d0801c0c0081e01c0a038002155000040b0b04035480304101d8049403005040107140c20702c5d64440d404d60082c06070505030300c51904c45520703000c2294004103a0190260100009005103589441c0c0d1900c81c90 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 22735626 1250 22734376 22734407
    0x12090f06070503010f0605070c08100b0a08010b030304030308070903060501180510061d0612010905010f0609080a0201030203090c090405010218040506060a0c0f060207110f09090d0e0a030b16 84
    0x200f0041c00009103450481c4125001030400715110070301860003202c8081c1a801c1040c2620600c40b2001050b9040d40041c42542004ea41005c00651503994190a8803e8445203503003650080100f040060b12400c0300319481885868251702d042d40ba90341c2c40302035072000e038006c00c14001011008040e10070319214254003c1140e00d864003400e0315240700600340b02010300401d0650250034255010365211720707089400741d8020104a100d00e60b140c008800081c1030031300907801624240100031403900d015000110a5410f190002d08802e4102e50046001e503200800404080c0030300361f010f58958031107202c1e00c0d005502c80c1d4009a21260343c0c290088100703817071030580c512071401e000601c074164641c0c41c100c0f1540400340c90200d40e20042d6042910a015030000b00606040c0f00048100601005100341000e07814100c41c0108400d0601c0b04022003c5001c1e9400c5485410032042c0c221602d008202911018001604011850b40c3d241c80710700c40a042102e0a24108120100030021241d0180201000c0140c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 22736876 1250 22735626 22735637
    0x9021201090209010e0c04080f0706090f0e0109090f240b01020703032c03060109020d0c0503060f10020f030d0e010507080103050604030e040207060e0309010806040b0f0d02040212090f0607 83
    0x220780d000910400c1e0103120f20000000e0440c04150f42c040200210380c05000f0800484004a81c100e0030641e035400144104030000308584030205220303148003001011a9501d030691001a401e040c6900c0003404082c07001c80b02a21110340c0c1c1c01c006018850801c4103100c4800c400409060b48108140075602139072805411508082024000030360001ca054030044280300c500240c091005452070700d425201c203415a45842500000111000c16400030700030807040c0c100c2480707002400384091b51030380015911242d001e0112000d5a456040150b031030103d200307403072040342c1c0b0b119000c2081601310352004010140407030f191101985020002d0040b10f03003100d050314041d1490361464030b400e40c403000042c00040c1001503081644010342e4698040c2c3d000c0070b42228080001d110031000a90341c0351f101074403e0340815901070018109142c140305005150bc401b8058009041c0c407503081010074800240300300d0740070f6800d100501c1d040001c811400c1c03164103803000038035100d085810b00b14600300c0028604010880c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 22738126 1250 22736876 22736891
    0x90204060212030408040504052d0709060507050c060a1205090c06030c0c070f0609080d0c0809060a0302070803010803090315040201020d0c050c030a0b16090e010b03070c0b0a09021201 81
    0x1c0d800200c1d0441c2034a640040c68882c2c80b20702d030140c134030710642d030100354401d003042c050000e985004081d088800c0000300d140794207440700d00d031541e0310110f04641c50b2010806030310040103001c0c0142d0003421018030690540d480203100e48002030017038110740790582c006408015910300d034044601c551900b00070084024400c0360652000140d091100800c0000d085d0004283c6007954030080010038041c00300040c0c01c2e821980c484a0061020485108070045845000d4040b92994080c2a0724104150030035561860400c0c0002406910350103038402c24101542048503001140d01d0354055030103030880c0c1c0c01a5940b008098100751070f0002480c1c907629401d01c14414400182e800048280e002511807c1280d450f03506804c0003030030500c00d0103100360076000f205110003c0129140b6458070640200b01444108001940100c4549109005509000b0120001800356181c0d28002d140e00c003d0614240c19614001e0341c480c0c1043d54140e8040010503100ca0b4104110320300030329203c49403a83c0100801901 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 22739376 1250 22738126 22738139
    0x110405151c0e03040902070302100b190603110c03030112060605090708040b040602040506030403090302120c030a1b05060f070302122104020301152304050f010b0c1608010b040501090204 82
    0x26502401d82004a5524104418100d0742070069500800000b441107484594500f4080d4540c4c098000d40034225241a0413142245040228641000d40380c00c1c04074550382c01c219040d001050910301c4441c0411051004201103a0200f0046018008484c0310000c5201c1d149030030815a49250030141c402c1079500308000369951b111280640c01500591842881e403543d081c51402841103801c000e40000c0000108000c0c503400c802c544c801c03640309440325280070300c1c240e00c1c05881344245880e540c1d06802410f440c1021072f0240c0c40c03201d030060a049078514900d640d0400542c40ea407120151107854880840c28070245a014001071101c2250041402e2912107509100c40710045070340300c0350a000044601260954400750f0216804400b41c1c10741414103a120b152400300320700c0205400300401d00150f084801400c140c0180350182c4c0c031108000c2d0442c0d00313000c40d880b5282c10000303a24201d8803c80201403001006182d44400030b0a180c0700004031030007d02d01740400e039001600040c05481c010402048030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 22740626 1250 22739376 22739407
    0x30a020307150605090a0b09070203090609040f1107030f0e0306070504060309030306260609190201140c01020301092c06060114040905010f0617010e01050907050c0111040515 77
    0x340781e00c54001c4605075048140d00b4000e01a070781065400106110800c6002c012640c07000d0202842210300440343d03941d2040490b640c1c40340c04940c2d50898803d0000440605280e0400900c0c40c101900c0801c51083e1807030150750a4200800a03000180701d68001e2800036002459421080e5040e03000d0315191610302000b0700315100d5171052908065403500c1c7e03041410703c658814009400327031450003820f48540f602a01c1000e000b0005000d0075000f482d0201e01115000100244c01c0390300700c410b0040c1490300c1d800560b42081900700102c3c042604000e1079140300801c1c4000c40c06810704500004540c21548019903a40202c4030810110b1950b08603a05002e0b0313000105c050f801482441e00302c8514030b0f02803003202e072070040354040701d0305a0405001040c5920380120031019150190368141030090205901c0007690b81c03c1c403517180c245440704014031040c00c0900e906a0700100c2d900b0864540580c00030540d0848040704110901d000000c47d080c400d038034040303403035510b0002141026820440d483e410080d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 22741876 1250 22740626 22740637
    0x5030f010801140f1503010c020c0a050a030b0a0e070801090317060f2818020c011107150203060d0f05010614030706020c0621090109020f0402070803040b0702030d06030c0512030a0203 81
    0x180c0190782400919001288071178001d0740c42000d8001d006411302001c01941c1c444000111a2243c9118000400e950401610050889402c4000d4401c1c0381c880a031010020141070304002414000c0040115054809015404410f8842d07600d640400854142d000140d0001406072032142402c15040091036031108480c2e07060400d501c903003403003400395864010540c007410783c0030518401064059900ca80c034141c0c0644100c4100c58000e0004c00c2410b01c80460b00c1c45002d4bc0144840150040030442c6407907903000d560321480151102c6030046041d2600501140000c9045505a440e14014442001817041e500c090010a800800c2d440c4e0800c0303806901da40188400358000d0001040a850004a070130401a134280c074900c0301050b40c102044020b000e0071181201740c2c09009070417501001030400e40f089480b19a04405001d040d51582d560320000300c0d40180041c800c40c4002e0280d0380c242c8459206507801540700d4412a580ca920300001d21008110001c00e0498a4200f4030070000c40d582c0110440341c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 22743126 1250 22741876 22741891
    0x90609010e0307120506090106080304180209040204090207050f01140c0706180f03081b090604050d0204090519020103050f010303020a0f2603150907021b03030c010c05030f01080114 80
    0x240480d0000c0c1c003103442c240183c2d1000c00c0004156540400303010307001c60386074051040c0000910507581c03101c5405990340300368442e1640b01e4855440b411550661580640f41a02004202618040d691480142a42c02042c01615039800a440081c1115024480c2c0b01e42182000403a41492030b04800d005854000c0c16009080941ca0780a5a04040c40c00c2c0b10b000002c0354050100c005045903428000c0040608071780101a0000d018901d50316064200f00b91001740400521161400f420802400081100d403442240c1140d220401503002076401d10040001d0500d0070300c0940c10103800d000040a0f9500a0041400385c4601401480401d5020405c0e0903100e400c6192a42241083d2500688801048001c46207025000d00c8100c0e11481d00e1000f1030250400c943c0386c800c2c078083c08040007940502568214056845144c0311045091610059124042e00a050320304101c81d000c159070075200040c0350300c40014000000c008108545803005405044400b00820a202c00c860010303004420180a50 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 22744376 1250 22743126 22743137
    0x4140f090112020d020904210c050706050a0c0203070303120c0306030206070b1b0c0d120c0e0103050709050603090a0215030708060f0d0f0c031202010c020a02100309020604060914040209060901 85
    0x1c020f649443c048000c0d8a907000e407070080185047d040452007101020020391700003240d0b1031500308140c8540c4a00904582000260402c01d11300070007603405500014031030040c00255500311015130750a0000100460080c0c17644101c403c046408081142c0c240c8840905151038520240302588819042e43c41c820f6008880031016100c150b141034000d0f946030b190060003400080e00320350280b0007013001813802d601900e410308809805039104007a40d07071f80c2d4880d40008281a089035240d62080c0c01864000e41d04c0c2c00d0080801d502c07100810440c0e03008440303100032503210102d001e0450500030000074401c01440765481c114201703104010003144010709980c1c4102c3d062031031384415980d4001d1403907460b0342c01100f8104a1026103048005e0103098401950031342442c18080c00080c2c01030003104000c4095502600100b00954200a5071404542c10b04003003580d21031035580162607043c001c0000d40b907a6182c404485280c2003604440265403414176000d180140300000481e1941c906884400c1024200b5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 22745626 1250 22744376 22744409
    0x1005100e0409170c010204090614010c060b0f120c1201020f160201120501080a030305060a05030d121409100f0606050304021201140c090102060a05010503060606030a0e0109060204140f0901 83
    0x243c0016074454000807a2140300050748908020154014404c85200f1141406815600c6a025500200700d020581c041911304001c6000602d096000400b10003004002c400c43d042c81801103504901d4440740d20a00740c0c089401a041842c00d84203011100c0386810017586030014000805030180101c003c40707900311500c000a102168003444201b0059a4014000c011540c0c0d91b00303581d661040108420b40c0842d2170b00010465909040c0107207010303200060b00a00e0f1047c40d8a804982c01a01c1c1100c0072041031f520440d0130a07681c203e4080a0080344100d004100c0d131910720b50340008890300001d01001d00c40c5000810000707140c110095030780c81901180c4004000303800c1ca42d094050005e0060481d40d14942c8000c018291604001402c20150280c1c2103c0c80c9076a201044401c40f03038280902c03a23056020300e00003240381c507240c4025170340641c2c1703c031010403c2c6c4c01c4440541c1c01e4401c00603044a82a801007820b0058075446c060b0080070580840303800c2207040d400c002180d06900c06004440620024105 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 22746876 1250 22745626 22745633
    0xe010c030e0c0303040b0d0204081005041109060307180f0c030c02060c07121101150b1e030603060c0307091205060f0702011a010e0301020408030f04090506010c210e03030706051005100e0409 84
    0x60f503005202c0c8205660356603000500303078bd00401301260122405003064050300210300b054a0342522510001d0014a4402e0401c6500900110000010014992518980e0019001034002c10103140700316100403035040030494010342000001403001100c40c806200a8001c200000000703120580d090604801040744a281240546070003400015101a842c10005136840c3c05002005205002014401025003100e1040e00511003680c20660580c00304001c10b05a2641000541c0c00c00d06505024160550382c1064005200b205032044e261078100004025000080100441c2e02034080c0c03008001c1c50540a4240d00070440b25030586040011000d030001c1c02d0f0b107095048402601900c0100c0b03488590004400038184e00600858204a0500010840b25405041c1c1e10340761540c07008000340e036060300c481d140481072000205c107002c1103094030800d03030a518240002c095241c01081c1c007041d82d1521650b180c4544010b640481d0181c920401c100c001707240c5c400d031004c084190865001c52190344a06 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 22748126 1250 22746876 22746881
    0x809100507020603071d01090803090402030a200901021501080a0b04020301061a0304110405011d0a0f090f0203070f0605040618050405160f02060c12060a03060e010c030e0c0303040b0d 81
    0x200039000706000091140c074076000f0b040141c1c001c00c07906d16040d0760303201880110382811042c81905286d034030500031816286050f0300030b90341c4001d4001000611b00e07201c042c50002c1481c1071a50842000c800500390856507418400b264001c1465000b807421340d45422030f459560b454599003c2c01407000d540204046603821740150004000110000b00c2e008d0240b1a10321303039035206231401c076014640e1445202550405008481c100e620042c1c540c43d447d03131440481e0006080c010314071910309a680c0d100000c07000e00ba100710075219000344d00840c0000c00301d1050619010294100000c030020304030041154552000845007600c2c0f907803808981a000000040500340226000036030b20a00b40010011a403050540189008410395214201030740b84203401d90703d4520a4400c000450360810140c03c0c0c0d410f88015050f000a005040040515076984800c070403515000c0c24402140d4440202400040d4507000b070084003800301c000780c415002c2c002c000031391b28416442007038155200400d8820402249a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 22749376 1250 22748126 22748137
    0x5040b1201020c1e061012030c020a0e0a0e070b0405040905030904060303020a0b0a020307050d02070201020c030111180402091027060c0b01150f080603030d0e0a020a080a08091005 79
    0x350000e5403200c00b809841d0741c03038031000e110800040d000e540c10505680e4000034000e0061203103454400446003810061498071542002c19024005888001070050b180c10034081c00522008160004504040c0b980c1c41c2512001c041c00ea82c4d55104150502028101c44111801c07079004850001d0f0b51501c9150090031070180e84043d90340285450800010b15402282443e54107100310444003507944c5800d011422800140d03424000901d060250164100c110b070300078a0707514014011160380104a100090a50b903906045d03690054000c02c2c09092044000e005660315203040f5400e50a00200d14042114811160566009c000d6424900000d0118000755124914251003412291548072100074058000c24681161016018000015180e69009480c811010305940d002801e825140040b21611006480c03a6418001003100c0d80b500c104c41c0c41810003c4507514040d1840c0c045900411404002c254003803070941e04001a40400200c0450440c3c0703019000300c0305002c041040400845160041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 22750626 1250 22749376 22749409
    0x9030c0603070c05150609180a0213060801020c070f0501020a02010e040f0e0307120e01090302090601030f020c0304090603060609020313060203070c02060d29220b030a0b0103030807031505040b 85
    0x2150328520328009400c204500c650b40a0318103200a4031400b230b11705050707100350b012030801c2e03000002d2040041c6803000b0300c020021404803004c5809070300c5080e0b40b400c9034400f8a044010780d00404040081d6840c20818200408c404d0001d00651501c0b030300042d00c481401c400c51403040b540c0b1278651510060561140715030034035010031291101d5403454000c0f080781b001d04800000c40c000114000c0d817580b2802c400c400340c079400791440c070098803803000540203445920b205034002c3c0d170244290b00e103104041003e0401015a048045806461400c003078040391301d25007254040a00400c02c000444007201c002d1429181d000c4001039490f591103500b05c4a9180c0818020b600c03030030001e0b060380c0300007240d0050804007420300041614150910041c0101060940706035403c10524144000a111003940c0d141c40380d0110100428070b0015540003e08041d5840c40494408000718014020b041d881544658010014203040022916840700141107404a1248074030a54903400380410341d454503034000700d4141ca03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 22751876 1250 22750626 22750633
    0x1021225080f03010f050301060303051603090e09030d0501091107020d0f02131407091401121401060215130302030d0903180902030117060c0412050a0503070308060103060501020309030c0603070c05 87
    0x22507250b0020342e00a20420880410382c100c04910303480c06218003412a80c1c151030312494a03a400c000417415194442c0c0541c1401100d510004501c81c40c20407892054803182c010310b90b1070205020038400c4441c1a000408500e240607030f00280c001e070400031100078a80403241c00084200f90310301003115200c0031800a401002c0341503c00060fa846820800380c0841c86091840165504802190900a54071900800c151340c00b1241540c3d501030503c0d4100c174190001d000c49c4000d4282c80c40da25000f82a48070f400180c0c8009214400c4982c0c2c4400140c01c1103086d48180109481038400079900d002d50b400320460580d94903504001c140c090421240d1000840c01060912617445070f145009400c244941c20a820340c0950991044c1400b0841c10f00ca110301c00c003a1400c0500b0030200206034082d0103000c807900d202e80c0a00360041b40c010800b900f44540300e55a03000861034480001800d40d0301c16408241990700520402402e6900490441aa150166070443c0c4956440304201c64006506101030b08500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 22753126 1250 22751876 22751887
    0xc030d050a180309090f06050301061508070c110108070509120705030c03010b0901030b13080d020915160308060609040903080402041d0d0302070503070b09011a0102122508 76
    0x800e810241c465122480c0400040b0030707465003504001e074103100080c0007a005410070b1112a03407035802501c190304114400210075032500c010034215005a003103d40010b10103440306460070b40c00320360780e58044068548101400343c195100c0d440180c4400c0441d0600074881300103080c852242098400ca190014072503000c480d5024001c079100c601034090a4028011503180381c5090071f05024001e1003a4000d00341007110fa00c1d5454101c1e031900040c180d2843d41850503400f030080340b201c0c0090401e50390080c000507507800c175410030442406168410740c1039506051003810001118080c3c4005500c4d01030a1000441d03a40c0300004049220b5902a142c3c041e2926000405040c0d00a8400f845684207035001c1114804002001d0010b0103203414600c030b00c3d0f2010074403040592094028110b0320b031155040303074144241d42e95903884240b000c03580100f0380d0f0b5450075400d456060208042c49225400e00240038101009400c418141c4642c80010b428080000713499481184541d90380303000345422010864490 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 22754376 1250 22753126 22753147
    0x12050a060501060509120304120609020301060b1c050a06140d140601090204260d0c050309090c070302060609040507060c02130507020106051e0d0f03030b0907030c030c020a050a02060f0c03 83
    0x35040820528022499040c101446e950004212802d075203000320107041c84021aa00d5101410340d500c8201c1c4c1554070354400042d08031070400034001c601400803c8030f0700d41c0046043c600440700002d0081e031409041050401010350648140c441da0344041c0ca80e500d0b030740c0e0541489542c031501e25050031018450741c00000f50441c1d01c0d501074025100407104942c8042030720030344010070f01c10048082d02c0c1038100010380c480b100d015100d8280218410005d49080c0700c0303400c0016840761002c41c0e025040b610000799000c101a4140b01c000c0e840181104c030f030003060820382c0351a0b5540070503001e11014041041c44400540da80c166822004810107001442035241c8200c00034041c0201d841200c1c0215140c8850841c0702d842c2c90405d000c03804000d0307c411200b000c01d48074101d1300d01c0ba1040560505640d0b030290a00354451302c1007076100359001d85001c120004c504500400f00ea520507404401c54004641c1d01000400100d0694010f5404031002510b030001410710f811648202401c01059102c00510107141 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 22755626 1250 22754376 22754387
    0x40204050a090c060e1908060711190305040f0603051302090901090b04050a1703070c030e061c060812070206030f071404060e0a0501170a0510080a030503010320030712050a06050106 80
    0x5c0301060358241c140d404200c180e00600082c40c01240307280d41100000445062043c1f030251046c150203011102e4440c8003200c0150605015801540018800a018001101c00c104680001c042524042200b07103000d40c5140c6d4602c50820b070080c0300d014242c02103440310409400241080b50031070b01d52000c6003001d10b0403a40d40d26440508451004442182036000b00300303002500d2250100c0d48400f203a001e950b1360304a0384a0f600b0312403a9401442842030042d900c140c296401c0d00c040e4504000540035007002291403800140201403240700d0002c1080100503200c1700e0035241c11460744c03050710132181c0300c0c0b00c07007a00d40052000480c0b46500c0c001c0741c0040d51907800800d0040c041426100041403070348131001190b031040340d07100b040139402510020171200c800d03642c03040ba4400780344904159a240c55a2445041104495040d000540c01000501c1848003e801007010490074002081c5244460300c042516660349d40300d00e509600002c0112018080c8c248801401190b000a0070401580c403000701802 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 22756876 1250 22755626 22755647
    0x181f05090724030203131e0c050301020c030f07020301020909040c030b071b030e0112050106021b0402120103030f03020c0706050d0506030604050606100908010c0801031a040803040204050a090c06 86
    0x11912520400140502c0b0303044090240052000201215401c080e40a0f8081d43c009440d00810820410100000c510010001c81441d1007101a8403126840f03410070300188000d68009a03c20391041000d0741d0042000411994444a1010b030a03813034050500000b402801141101a00040300304104410401c040c0311013010b4a21a02694116407a05542104d8030340350102c11180b0781c901310b01c40102103802404040c1c1c9014051501c9203900c61403c942800352042030f0302043c0540d0181d200100520325103440003510000c292421410300001d0f4178401c1d403000c0c042c4000f800740425029100300f407a12a0301210080c0700c080302141c420503502e040c002c1282d84110f0500441e140b070180454214580072070054010b03a0007d00030b01c8581c441c00100800c0b001c41c0c200d00b10900c00009000038281e40c0038054241c10031090f1322543d00540c914103003240600f141111800704107406204210010b000181500c0c0c00607010b0710f00007015682c001e04000182141d41010f80303001d101c0040011125448a507501 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 22758126 1250 22756876 22756891
    0xb03070602030405010905120c1905010311070503030a110c01090503030601030f05060901050f030f06010f0303140f0d0507030f15061808030304060b0604050d0c1a04050108181f05 79
    0x550080d91014101d85038000c90081d83d0000303401610400c21464509246000c40c40d030041a00c4103042c1107000240ba900c5401d005103900e9100100c1009039613010720407603060721406400d40303281045569505859101c020440e40c429a036542844d2002031100003510203144140000700040961030518a03925001120050300003401c081e4000c201c40c03424010a805403901402d1304400781d0903c000c12086c40180360b00d1642502c5a4040c1c900104d00c100800c80c028240706844108160441c02c008294910300355600da811101000701c015907032031090403030300074032400d13403001846441ea076a04070050b158101d01d9200c12814014500c240a1403168040e0844c2d55940794180d2030741119403690200c1c940c81c4a4010b850704140001008150260040904050001d1a0500e4140c40354000b403c824808042030f80d1095500343d040c086a001ca43d03014180b80940d07001a030070320380b80c400020055280103100e480724200d03003070502101d84402c10041013045210801e400407007114a422800402c4103ca0701c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 22759376 1250 22758126 22758133
    0x503040e15030d110102092d03030702010c0308060307030b09010e0c010e060412110402040605041d1b0c01060305030c010b1801030309050904150501060806031605091609080d02010b03 81
    0x3540606400002000c2041c0107005007050500394641540d800c041542d0f00d082d00e5408000481066458001b0524500180a2000e182c0120050000407072000021220b000358010480200580e1300f100d21500309503807514100040381d0303c00c0040380c100409030740000c0156102c03e0900c51502c1040d00001c0c2181e0281c011030303003100c40001c01120351025100310359800140400c02401001c900c8210004014014640380e48070300100700109049900641c072210000b04089014030240405443c28122440c40c0300c0c84448030305100f812052894202e0002042c020b6001405016004003900420700640d0403000740c0c0d40790134410070b07200d0191191001c6d003407003440c0d441c030010f80441680c580c80d4140d980603598603000c00d0034181440307507001d0081d10a4400030ba004024401400003400344078003070040303950740703645a0509005151610b0041500c003000c210907001c0520461701d0b5207501039440340c00c10704000e29800c0c1200d0b09454010342900843e507075000310b1550100380d0303805403c00e881c1040160100e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 22760626 1250 22759376 22759381
    0x6050108060102160612060b07110319080a030506030109023a12030507020f0d090609080615040b01030f111b070e040201050a050f0a08010f050303040b030c070f050a0503040e 77
    0x12601d0b00c91400100e5070038200ca80703050082e24858031100403c02131b54400014113603207501d4100c0d540e4202900444681e1047c00c4044600c0c05d081c13000103d44c281c9115042c0e41050980c1c0c803540b1500a048402c030805075290700064a5035801d40042e03070640c0d005094494149680800d0000f225805c0c01085461104041c10500554030000b511100c1900500c90110007884807401f01c01034100034002600318420382d04c1c11407840e1803d0001d61070f007103408d413102503085290080c06003580074540d01c0850f00d900083d08205124402c022090402402103900140407481d58005078000d10f0800c0207400994684040c42039600c007035800921510b004043d555281d130f40707202c1c0d1031070340c804041c00b031024006806030114005501410140a80441500340517040c01141c0c04c0b00e5407180c2010070b5001c001401e09004121800114880402514095016514040c01c00015040d1032002812010040c0d0300003030008284660101560042035000058071081040c6061071a62034000e40503082601c08030402 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 22761876 1250 22760626 22760629
    0x6051501020a1505040311030a0201050a0b0a0501050a0f090b180f03030304021503060406030b09010b1009060e1908010513030905040c0801060309060605040e010c030b09011a070606080102030a0605010806 90
    0x2030312008298854a5040b07841084480745014050141040b414400c0c007c020401002c2d050014294429403640001141e1501180e058180c641000d40c80e801400e8106041c44a42d90000c225554220f00c0c0c1000c40c601c2c11012400c8464001c0e039848648410320200b00303004100802c0c008070307030641012100304040996450030103072a44025a0020341c081d100984500d410f030f902e54045c50b80485c0003440003602d05c1c0e0340d4660003c05042150400a180d6645d041001e0900e852104c0031011580707491300743d05160501001402504040100b50700c1400f100c1e403010710201401d080c20001d008100700030310807402d298180102c83c030a10001200403d241300701c04941400c061207840b445600955407100c1e2a46410401e500500080c40185c03400d60f19280046069201c4d409150141d4880c1800001c1610428600904491a10121070b1044c40a9401000411140006019603a01980f081a0b50f00314900d440c82c0202007030742c414021940040204002070840f135008508584007a280c3c0030942c2c0d0b40300d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 22763126 1250 22761876 22761883
    0x2309060402030f04020d051906090b0708091011160507031401020a02060109020a02010e0a0b0601020d0e030d050a0504090c051306030e06040813050d12020d090f050603060406050d0605150102 84
    0x219540800f81071000060050702d0014442c421845c040c00c280c80c1d5000c031710600e00ca03000360190400d80d0300c3d40c1c50307240e13500411026801305a40400305241000d240d0a195141740c1e2242c802c50120078100b61209803c2402004038021108407201c84001140341e01c42a140c45500d4900a04c020b450f0f0707000c0300702c1c0d20b20804018000c0741c900e41020350142c00540c0c200a0741740001d4020b402c40d20115940c03080382d200040400c10120400c140500c178084500e14004000915104410752180100090504002099200020890031805070b505185844049914085a06001300d50056a0990401800d80002c0d074001d401454080054000c01d12502d40301c90003501a2002c182c01020390742e2001c00000d01040c900805003203903c80d40318044084550391800079a5441c0340c201c05640181700d041c18104400c0e010440e1400390b246a041c140007440c905030b403004d100d00c0d00344a00c80c0500000000105203a403a5072180028160013015181c4000703c9080c054004d0030211003440070098060f00c03640280d80000b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 22764376 1250 22763126 22763131
    0x5060c0307060c0c05030a09050907030c09120302030c030a08041122090512040e0f010f050d030305040303021317010509070f1202040e03070503180f0d1209230906040203 75
    0x1400254a4030250342e94610007040d018484104000001c1e0388400060001c0c4000c0145101036030b540c220150524003001071803400640094149803400c0206194180c01c190510115500da0040d605030903400d08050b803c603c6030020300e59a03030100041040760650454001c6000300c1c01802c40d6540c070304030700b000d001460641081040301f4100352010110302c0400c41d0010b11010f4481e1060f603904200300000d000103900a83c111608119607007041040e041c0c1e141c2c0c101801480d2500c640002c091510b000b01e40095502c0c40c01604060700e8500040515000e40c0484030010305a81d0440051655910620950161605485c05035428800400d101000004041c4d0503130300400e0b20702402501c1c1c5440071000d44003c6e04120b8220751240c001e100130020034409400c1190041000d1990351070184056884084503914171885025400c044007c151242074680300441e138802c03100300d41e8072005c100c191040450b40d848500c40804225082038044800c402ca411401000c0e0340ca40c003141c88801c100000c0e800304 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 22765626 1250 22764376 22764397
    0x3090f08030403172d180301050c0708030705091009090f050106140d090803010e0f09010603030512060d020d1b0603061404110d020d0c120203060a29030405010e070506 74
    0x1c203403131a0b6502d0951002410650003001c401c444124240000e81091030200020441c00c04012841c45920460302c4820706d101072044000300001e1030004c150344094050b032000038060400c04000994203501800c111540d01c00b004080300821031001c0b1004020b12560f010b401101030801400f68604601d5019450503200151504041000703440821002c54210700d6032000000d842d40c04413004200c0c44002540a0032048881c2d400500d03000480c1441c0a00107416021160f260060030400700368828141d50300c1d000c2c0c5018100f2030752038090000302d480035400d5001c0e52111108468908000c0d1403400e01020304054503c0208940d0b4415040e011540e151043c0015043e09210b150841d00d0039070b0101d400024100810f505200e09034400200b26046501900b0203148d450800b084041d030010380d0508440c441140941c69032810310301044505c1c159200d82d03003505ca40041c881805101c80708040e002101c1d041e040304d4032031519003040c0d40604400d9018004074020444081181e0900d2012901c22520 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 22766876 1250 22765626 22765643
    0xb0304030e09060108010302010503101d070e150a081503010c02010504020f0a0608011802120c0702010305130809040b2107170f0a03050310050418020405010b030907030b041401020703090f08030403 87
    0x2031f680066900d42d00081040c03440300e9080401080e0100d01c5040c02641205404412107149001400070348604503090300c46125030500341110034a441d1810440390300d07441f00e05d0000710701e07142c500c0d050b030385032051000c030f01d5055007001c5424110340d03815880980300740c1c0200c2d80051641d0000003071068001c014010900010003240042c880040324180241c001c02c6408801031420f640c3c004007501c0458107641d540711035180090b0100540d03902d4007800e604040b40700c078000710400b039558906000c0d03c1100c4100c1d01454554058801696922041c0d045880c81c0c0d440484002903142001912030030680554a80320714038000d08a43e000e400140c00341d400040c08028109078016803002d44103034000605643c0c1075207818402280c1c50300c4500486130120300d1040100049030492040000741c410507080280601024020025440f00000311101100e0308100c410400382c03030303a040001c1d841d092401c49410b25800094001c04050780b00082a0441c0c460b1004504060b4540c207c0d29185c0c07140d0f20024007040d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 22768126 1250 22766876 22766879
    0x20a020c040e030c0f07030605010602010b130e07030210050913110a18030206071a06010810060c030909150f060206040f03030515040501080105160207080d0c17040b0304030e0906010801 82
    0x10141d0001c2e07007010301802180c0c10000d0300d6110350300c0d01c12451042021904201c00c10410030456000e0240541b041d40020301010b034005000c100d402c0401d126038030750140c90b000500041070051203020060354000e0407004a01380111070117000c5903c00d140b03560007148040491942c0d0915032003440d20040c944007070340b4a820700170754040310202e4820b40303169404007000c180040142d40d400014400584034454a00e1843d4000c41d11703580f4064000c3c68a03041c022510100300c1c2d20418880c01000307a6040c0d04050054560314101103503421071030307008401c0e2a031400c0200648045000880802c4440d00700b03000c1511034450701c040740c540000303440040050145540c010300180c0280c020310b6109002145c880b92214105000500744c920a0f807210f5102e95403181070000115110403504c0c41c10006000501c0680e1a29942a503181500c8803440704200c000d0b0084020080703210403404504902181b0142c8170707034862242c0010341c3e000b92411800304a58000790344160426151a0744a884141c4403200c29a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 22769376 1250 22768126 22768129
    0xe03070e041a04050d0f020c0108010b1b030705010e010506010c0818120a1202070518181603030513050d0f02151303051b0603090706030b03010f02030109020304060f020a020c 77
    0xe030064412140c0071410200c00381c001504a001d5845030b401030300109810307403200760090001c8508031070700d03400c5400c03105e51010266003003041107044924850703c241c1d4461120076030300404004402c0b43ca000e0b0000040000a0007030540004000403c110002c204689480703005599030b00c06c14800030080745082c01070384d6801c4030078100c84803c03120140002c0c07812102c0e8040da1741091082ca204940e00300e0b0321010001d440783d0400c0724001504060703540044889841840c4102d0940080c40309c081d042c4030150b1002850310906c02403c00746081114607028549924024101c2e40049500031a42000d10324000b0f203529004108036a00c0d90400b040043c113800607003d00880c541c090b096035440150802c17009020003211425000110f001d1006032502010388460303220701042d80c00c24240f1130706050082c041001d030b000c10b2000071180f003814006072080d00c5002180c0580245110056660310210000440c40150780040d03209510030f00301042981e40001c040c100324005c1082442c01a0303c0307030b048403910f03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 22770626 1250 22769376 22769399
    0xc0504050102100b0d02090c03040b010f061704020a120b04060c090f050d02030705130b040e0309310606050903010e160b0a0c080304051f0c020c010f110d030203160e0307 75
    0x8405020f0b1524800da121a000f00d900071f50143c030b0000128000000f00800d01007114007060162030b00e40c504440851404c14010180d51f07421110b0035602110401003421035852030354207001459000090401d000080c10300140c40d102c211000e540e41400c28103c01d0740d9a1040610708140c078240c904d1109100d06100c1802030000c0c5210040380c141c410031101048603502c04501401c001c00007003000c10110892000c0c0b00503500e1140c413407012517006105164169447d044e484410b00401c0400d031101c0f0954400303200b01202182000c0c3c0b0103d20740725011400b0340e4000700030440c81209600030b1040b035880e9004a9501c05041d141010501001c0c4400e1000c0885000140991070b02441d041c0f4011090340c8506102d984155412111a031014005a4403841c412880540100c0d000d5400c1214010504000e516445080c0712941004000051450250700840a200444034500200c500340700560001400a503c03c1e50705030b0f07030001c80b406040c00e40c40c031807440c03043c1300240503028096280c50029803804 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 22771876 1250 22770626 22770641
    0xb0901090c091409010612020d0e0d18030803040609020d0803070203030a060b120103080f07050313030c0b030108030706050705120403020a020906040911060708070206120109060509090319020f0a03050408010c050405010210 98
    0x21f082ea02080300d4110300d0924040c0000d0a05203001802c00d000202801030700012114210400ca000a9803040000c5a644c80c1540d620580004003c20505000d10008125141c1524000c10355407020081c090104ea000028600c50600c480302005040e85600341c2e885540550360a1110503400c5400600000d00c507a00a0415410106103240c200f8100e0b0741e5460454129031a5800d00d0700010b01e04209000404200c80000c01403a14814a1541801c0342180c9034400d5240c060040f5032100003260425120f00101c03032413510700703c0c0042468102032034000c0d181c103010340050b0311a459030008500c441c03429101e405565a44a050741c02c6075414002440240d0304507070800d4841440501018025864050042c2164111040640c89560600b1a11801c1b5811900064019220001000407200b0300000b00c80c1107025201e100880142e43c40750403441e1501d0080c07050802e005508040b070415030800090000c0d28a148000d00200905034011543c80c000e0b4480c80340143d00000c00c15690950a074408038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 22773126 1250 22771876 22771907
    0xb0411030c031f0501121509050c150a02060906100509100503030703020619020f04050616020301020d0b011407021f020a08030705040302120c060912010b0901090c0914090106 77
    0x4407007184200c0064148112030164070800d50342c8003480304040000b8030480b40501540000780203140750b10745503842d9050001056a40b140c0d0780744042d80500c182007002d0b122400004002d100d0001603000200d0494100c1c0c00c800b0058464180440c0b1078001c0030804902c0f41880400e13940d01640781c1410400c0c00c41c0041c1c90040d40141c000800304243c0c50610041c0344250094000342420306010703101a11401e0783da002042014418007884010340301c500c3c111402c403103049992070340310302c10080701d05d1a00442200c02981584001007282c1c40c0040343e0407610000304240c0321790a010240c080480018414500c00a42c0810b03e09401d19a00280030599200310586104031061080c1c2507485440c250f20644002c0085140803800308114034001c2001c03148401c8840c0034200104500340455514055011024481d111082d90040c2d4180250f00651035441c00030032a00055a48490701c0740101009030f22080010000c1d03102203108042100d480c0d560700405080311074281e04c1c5c91303001c45110303402103000c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 22774376 1250 22773126 22773133
    0x130b01050408010908070528060e100c0806010201060504090f03030c051c1d01020a08070813050a0609030e03031813060e16031b0804060b0103060b0d021c06030b041103 74
    0xb042c0040c09100d07080405210303600980e503070304031418690300e400708400c121040c04100c07441006050a101440400c40341d44a00003003190323100c018225061100026810b17054070301d4208031000c4158848582d6014910030380081144c10b444006000a0f50f061890162181842c1459540040e21139802880313001001e00d4000d00303200306295100015400036503082c140076110b03100c901b07000035074004413190f401e070040085143c140c1108000c1c218000041c11031050011100001e40441c5078004420703c07040d8820250b818400300c620b0020010091002c00b80c0000d10031a0589540d0308001003101c1c80000f01d6140d0840c031100301402c101d17900030319446204a00c0d40b11203000901c0303d41e01940500504044d0010300c24030a98010040c11120103016129065403400700701c7c41c010380c00c003001640240c4c01c1000410003808002c01600641025404540030007000500e829049405034080c00149840070203a40e001c8451014400680c1c000c0c0c000605001c8070000403800142c84842c422031b00384409001d6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 22775626 1250 22774376 22774379
    0x30302070b130c0509040308060d050705060c01060f0501020c130f020d050a050a0e0601050a0509100e01080d020c0315131a0703150918031110020f0901031a130b010504 74
    0x807031071010301c1030300c10040c4806026104800c000a0002c003902411080c4d401c52240e24194600070014035001d0012030058000c000e05c102031282c2400351074007800000c0c220540e50000b600c03400d0f00800c40b0344035007209010280008142584040740e10a5440c500a0000301080c491042d814000c0c41002c11052140c0e908101c2054100c0607030080d2403007140301500014440ca030030200c2c841070315000b5610340380c036070441801440556a1411004142d81c001e48004003180d46204031034440c440b1341d40041e0400d0291800010308034200041506142c403155080c0d41804076240281a50f4440707269896210501c61800100780281c04c41964034428082c05040c074030002c0320301000c0e500800507a41740c000207454503c1149080002c448420051100c020b0400004031070303402c013802140c1c0803180201001310480303058440c0c9408000310001d4035046001103566441e8201c614000f0f600c0056194007090821003665014000c0041e02803440f0801351503009032803100f03032040c0010b01030b13050510705024040c1f00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 22776876 1250 22775626 22775633
    0x20403050703030e01020d080c030a0b030109050708062205030a050d140702010213120b010302011b06060b03060a080d0806041d06010b0403020429010507031e09180605010509090403030207 83
    0x41c0000450007a11401d8004403c980024100032140c0503050501020000340561243e6580c00c5a5122861880000b0800100d00010f8050004004082c14a204054020a2001010614500654203100d40401c43c3d01050b0860411900034140540190400e1100c2c020050145004201400c50314600003075a084a2001c000b0b06842aa618070040c0c2d800b00d41000740c4010794a403600074010012010b840302100c3d81d00c03400540c10501000381002400781d510302c90780910990400440d07621071014010140c6698400b0240e400840344030b4441d021300304000414100125456111696540d24110550f441d02c041c00041d00044403180c0414800b00c10700101d0f080284240c0b03001e004550300c1903548e01e1444c01003206449200460004d0035510f0440390500d1690040d400c070403078a080c00e240380c940165060990342440d540e0035141c1c80c818600101110307103900891a038240e5690300c45100200c403646240400b01e401501402e0301044c03003009031500d64901882c0055025100740703000341c9041034070303903 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 22778126 1250 22776876 22776883
    0x3020a020f010c1a0a0b06040503071203050c030304030807031a01020a1103030d060603020c0714061b01020904021209010e01200f04050301060303170a0b0603010e0402031015050405011409010e0a02040305 90
    0x1184213a1141104248407018200b8000e00880070000c0f0b07038550801d070901c03000a40390720b05403040c0b4030091302c1310010340e00309030081c1c042d108004201c00c103482e00da01c0d003801d0181540310125203800c0000d15299a501c00b06140407585404108183d009010034516a900e12401ca004915801c0c0d05110910181d0102841c50140501409040d500540c64021561045182050360f810603e08607840b070400d504d20b61268402d558481040b9028680040500801c16009209001184dc2c1081c00000c40301c1c1d80000b48542907000301810002004810107541700642203d05003036505504501146030751a008892030080c02d9815105100c027440c1c80d0b84c900000e821500341d90b00071004a0025089880718803d01e81001d580003c450405004d84100840020040c0c44140100c0a140540320701050954800700481c00b181c40d511201000204641d0481038401c0ca2680b2600388074600f0200045100d4205c0c800181c110750026003014926405d144017165128030003400000441e0b42800000302040381007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 22779376 1250 22778126 22778153
    0x6010f11060907080c04061401050d0b030102070b15030d02060a0f0608070e0f15010504060c030507060903080105030d050f0901030518060705070309060e030a0809030312040c0806060d03020a020f010c 88
    0x100780080c50100885d003050800a9918860f5142850070803d4003280140348041640918096646600c070550010080440300302ea02e40540c4040790103c10450003015080c001c001c2c680603940400d20070b504060380d074a101c001c0c03080180c0007600803900c3c00ca1217400003402c4107088000820b0700c82c2c407194514a000304907030200f00608000c0080c03040c40d083c882d40587d080303034800c1c00740120f40e00301c84006005880f49101e84420850101c854005051141055980da20b601c040d085c40032020ba42401401003400b0301855100b0300540000e05140340c0a0f00490322040341e070f0021103051901040054004150061200e41300b2200c4842d4409421420302c0b040d4400e40c00350b2100c9444801c1418001d201100700e4000c042441282022800b840e0360004a4010081d03014055135900c10111000c24214020903070131800440c4000d05000070025154220401c2e070f0608011141d075a0380e15420040042510040940560454034280c40541803600611119090604119184001ca07960b60f070400c6580 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 22780626 1250 22779376 22779391
    0x2040b0a09020f0a0e01091215090b07020f19030215090c030d020312010603050105180a0b03030705010e010509010902060403110103060509070302030601020f1f020313061805070b1206010f1106 85
    0x7030805003650001d1241389190428a0400d21160410900300c48c8082d00035005000b44827240c00c00003c0c440c65800500980c0e40c0110112150305200101030b544921f004604040c0f80640b2901809a22154903030400198060f4020031446407400954104560041c04520032070040229a18040d101080900000780c103590007136aa9106043c0301007440241a0000002c040c1000010046a43e5400d246922441502d05104c49a01d80e000c50360000c024101845405000101b030044c14804194400c5d45450b0200e0001e00055460203a000d01300e0791079000c001c0d4010014807050010840e0000c40e0800f040c4103040014513261100f00041c400e940849078500040e030000100019568180300052446c60700c0801002000c00c04607200844090f1054128480c4e98084001840270b5809402c1510480c0c0100080013001c00400c003001d24003100103c00d440710310441c500020010000d200326081c800e5190240c90070358864100441304000b4204241c820449a0a92400f03210002d2041da400303400c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 22781876 1250 22780626 22780657
    0xf05070c030b072006040804060818160302041a100c0507080a06050a1404020306060420040603140c030106051b01020904060b090a060302071515080708030a03050901021602040b0a0902 81
    0x80e1100d01100e00203412100c04d240750031240502000851620903139099408505001c0e581d5501c089441907400700020402074944581c00100e00403020303040950003a240291030502c07140380c42d1229041d1074400094165000320a0600c140f2249114504541c82d0f944541c043d01c000e242c2d1560b00758608140c00d0001c1e20580d0342c50042c040303070070801d00c14010a40100303d04e43c801454160002615060b0050003035014544a603400501e00480b01003030030441c40400752080e29240c81d0080100281800c6000000303203001c1c4c00c0402d03088521031003500e040305c0d0255a8280340002003612201032205402c481c0b01d484d0740034440101660f540f40140300180c149038003071a40b00c4040c6001c0000a03c1c083d0300540500d44104251008211855592011103900c400e000c02c0c03c0781c0350003000003c1744407540300d020a400b40282c00308000c00003000518000303040365018015520341e001300340d01701d00c100b60183c0120302c1121240d00041c18150010000114001c00100380c4541c1d480511060364020700d148445480c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 22783126 1250 22781876 22781897
    0x70602040e0105040b0315010501140403080408030310060206010b070807030e0306042604050d0602090a05030610030512041203080705041215050a02160b04320606060a0f05070c030b07 81
    0x41034440c184000300114001c1041f41c01058000c180c200060241c941000801c01091185000d958115402950321a0b80503136999074840000f13889420036141c032504c8000d406400560320780b0004160b81600c00e12820b2519207160b646e540c5155a010000840a100b0b644400c25000e0b80d0a100451056004010707804221040c0c2142c1c10043d10a6040011110020703c400c0c4019140c00c4100001c40740d00c0840140d580c0004400128001030759400954148503110802011552032440242100d104104846c25200c884e420f10f411405203000740104e8507414005440843d10464600742c101420b404c1c400d10301511030300d3340160f40d03094600507103840d0000758002800706141c0c0b0680c0e500130390442d81103050107503d0881c10b04030490040043c0091295401143c10311001c1da210741f490010300d442d5840d2844150600c200d201202c00e0b8510014000d1a0000d2140c0c2068001c44610100603507451001603003c6034295456089100705640c00300840d900840003c1032208440d001d02426100d5443e0103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 22784376 1250 22783126 22783129
    0xd030509030d05040f05040b030102071b030c0902160b0703091407060801050405010807060f14030a050105130b011e0203070212300702061b0d030b2107031106070602040e0105 77
    0x1840096105007000380800c010441740b0104501802951800c84002c0381c01595140001d019006200340500303089400c104000b1040e481c204c01008a91085025003a501c3e540c0d42c00e43c0403402100c0360b5002c0310750303005500f0340040d0450040070361011305402c2c0010201419202c1c100d00b60243c070702c0302a09a01128040c88003641001920340184030440d400e022643c10701010315226049846500284880100300700d15040c041c20710782d404078410621460310380c80c1000701a8082c003000c1c800c2c18010b01e28010711104c88a61b90141100d080f0040e1140110740d8903402045e554902c1030000001107010074040d1344010f03900d08030000d0191140ca002011003000c18180b030120600d02d8400b032408140031840c6c60035500f07203110a0740d10319901210b09507200d044112801c18601c4c081c0d03081d0043c50146803c81003840b42c0681c02070364101c3e019544624030810f1060b44060389408135010b2061540688000c1000030f09800e490b210400f00a48100e007081d06544c0c80300c040e40c01582241a0400402005002a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 22785626 1250 22784376 22784383
    0xe0619090209040e120417030408030a09030201030f09020a03020f01051608030f010b03100303030203060f03030c010905010606051c020f070b0a0e060f010b090111160f1a040806070503150d03050903 87
    0x7542810001d0326000d42e2444034034502e0321a910400840404008601c7c0c030703e500910035030b00100325440076030f03941d9188070900030070b40515404102c4c0880d1405c4040d150b91101841842005035001c0c4c035040c100c5045070200040b660504051a041140400440800c40250010360121718412001a500d03400c000d00e440c0d4002c00140c01a00d01c003002030007000000c21245104030101d82d0141001640c030b88400005c107640c0010032560581600c070003d0442401e41e01588110354190040c4000c024182d00d0ba07804541302d1040c40150480b11402036070481c0c8482c4941c0c000c02c3d4204c1c007000ca813072a1054076a2801c2035581d04941c11481159601c3d0038016602c424404940d00098490b03001003a981800c030081441d0182000300c40c100052406141d884c10810080401c151501d41c58146843c3d40d01c04100c654100c80d80180001c05107000c41e240c203035800b00c2049d142911159005411150359809003250750b604000c01d0f1000f41090480200615155090320081c40ca000c0c3d0340302c0d95940710010a0518 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 22786876 1250 22785626 22785641
    0x90d1104111e07020117070c08030705070303060b030606042106050903030901060504050402062d03010f050f0406061e09051801090b0a030309120201020f010507080403090f0f0e061909020904 84
    0xc10042c10044000141e90084c0c3c81c03643c2c605094282046038641c414101c8a030075021000030a1054000117010515401401401e074182c4a0754061246a407a003241da01c040c082a108650001c0090109110602241a040c02d840c1507030707c100d440a00071501c0700c1c01038500503101c1000d160400800c1c030011860038090480039080549080c001810603a0202d0581e200b100350695201090484200c6544081540c0b01003079140d003071110740c40c0c2d40c480811424020240c41500d00c210000840b0440c5418903002c1c2c4011a202a261441c9000c0c503032031a080d0f151071202c50b0741c00308445a140414250b40d0b491640d50f00045030507141119604298070141103801040903c0e20907a00b031802007001a500620005c159a0402d840c410341500e64401030385010421400c0c0707003030f0394280010410b40365444685070b4800ea000f40e48046c085a07031400c50740240e620900568050906103a0140311000a600c88140c100360003034211402c00702c0e4a20140181041070700003c80c03050300006c2e0b40c0440d18081c0543e44 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 22788126 1250 22786876 22786927
    0x708070c0b1c02030c0c0604081815040b0327010b0a09200c160e061018060c1103010e0604060501050a050a051002030405100801060201050703050606090d110411 71
    0x2071400300b869405001180c0c0091000780d80307940010000e0342c4000c460f41039903812040d03981114100d00b81460034200d0341c5c10040300c000121510711041882031510b15001c900030031000444625050608603106130315030005118118807250340c01004802d005d50340b1841d144091141c00010b510f01e968081003d5a00039500a00030309041501c915943d10f030200311340c25541c003a401c1c495503c0100c0c86415040003640340385100b1264a02138001000700d00d600c8020312404c811540c031070741d49031034401c00c2c2d13802694074000c0104815500700c240240b60240580c001283c5c0600f1414162020003800071f400e460302d982c070010340c0e030f08038400744000c21003640a254094002100c59506043c2081c0201e0720300c0e03510b171040031b1284182c916903805d445d00038000c0b60060500074100c40304244d04028060000102845524010346c43d003000100658401d204060180d04020700b21894a10541c0800c40791490b5198160780e001000080200d213652144907a102e038826403500c00751510703401104c0e5640468540c0451 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 22789376 1250 22788126 22788149
    0x60609090b030309100e0402040305031306050310060305090309120c040b0102010b0102250302041103070f030c0c02060705070b0a0306050102120703080f04080d020304030c1103010618110c01020708070c 89
    0x20701c52580d0100a480b040042501d44224124049104460070200803c805421510014020060040100081c11a402c106462940d0302d50360307100c1251544000c55200642260850781805500d1213504216004000141261b060514540002d5101c84500303d80c4019a881002d0f20121810540680e00c0101000d0000304034030406200080c0d101c1d6a084030344181010040c4001c1e2001389001641009142c0280c8104900d0105240304034840d402596000040742c010022541410b22074003039065418100e80d250b103a0b0456076401c6c0b2840742c1150404a40f40e0203008004124000302101402070340340565004102c00d80f40200190412182e803800030500001046800c0109030404100c54019034240e120001c01d40d03d0b030611003440e02035040014821400041880241035010145000c0540a02100c007030301d441007401c140c2201c65911400e0382c90311043c254019142100c1c0e00c071074070440c200f000280c9800000101d260890b840258115009100814440140801103a08001610503100c08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 22790626 1250 22789376 22789391
    0x30e040219031401061409010201090f034b031803020c011202070b0c0a1206030c050405060612070807020a1a07080f070503040602070206040b161403040501050702040e010605031006060909 83
    0xd01078240701b80c00504200001a401d51705034400d62190458641120b07000001407264900140784002c1444400072021f84600c071105803000304544c807007642c0c030001b4184410250b4803008800c40100380c22100305069445140c2245042034101049207070b84690b0140a03680d40801c009800305c00d0039040040030354030506c0040c0008546c138100903008110125a262a00c0304010304548038211030440080080c249100002045440c9a41000ba124100d4082c00f00b40e03500340a11010b405550800081b2000c401e01064500c1d01640366560804900e1040c0e40940c0440e84902c41030995102c613070651204288204182c959011401d107410500781d195800460600070030003891408043d2016250503400607201c030456941e04102c4004010170820141c98100124201000400c00c0d0026140c000e150420702224900100854054550503159541056003d401f0b200007820410702c104000d640e1041c000c140341e40e0030400303079800c00030a01000c1915030400c0b10040c0080c101c0d50020040e1410201c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 22791876 1250 22790626 22790639
    0x20729130b0411030a051506030d1106060906060405100e1c0b0403050d060f0602030903100213030303050604060806090f0f0606060904090606050a0b13050d0308040f030e040219031401 81
    0x500c00d4005402803030000c00c00f90500d00181c01d100b01040b00508622038610301c40340c0c040001203140d203d043d00314140e03101080191005d5508481ca5041d01c0d4140e04914005034151428101d6181c0044001e8003050900e83c4400129100c02c08401c210004640e401c041c0c00107502c0c24080f040c140e40341c140481c0e910503043e550707a0508034070b0183c0024244031021a43e0034140e4440e41c0510000c000c031042c000042c07075175a60040d440e981b040340b001d4002d000b208441c0e04400d6140c000c0b141c0703144501a10540c030f02e145807401c800801c406800343e035106854030f00c0011180d50402040380103401c1c0300c0c0a40f030000000404d03036160507030400420043d90002010000c03140d0742c4105483d9038180c1a40c0c0802c0303a51040c41d02400400007904180d9114120701c41c045008800c42025020000070340303020a003e251940100301c004002010000d00144200c1c0001c1c0001e103040126080c81c038880d0408403402d00d0850b000400344d030440001c28404031140030580c08100d50500540c0001400040c0700100307941043e1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 22793126 1250 22791876 22791893
    0x50717030403020d030c08160506100e0106050c03090a08031c050601120902180f1e0c0301030206090616080711010c05102309060103031404060c020405040602072913 73
    0x10010303106031020604c08050600900300c05060542c010461076a444040140400d4000d000e81705441500c41d000c0003070007628026402c0b0007a20601c40702c406d003503864008112000c0e8840308100000c1e00040c84035580c030707460354000e080192440001541e281d40005004080340c0c080c021590030800d0801040c807811340d803c00901402800342020200b40b00111b400030444030040c24942c0365031041d8801c20889409a820074090242006d104003264034102c400c0300e1015001c2c00c2c0e8500b404800304000410041c68040003c12802c2009841c02c0d0030b14400c100c040e81c900d212250709a50500d40082c0300c208221014000309010700090800381c0c4202525116159592030702841445019a42c03110702c07c1482c2500c914440e0454142016141c40c540314064584a82d403c0c44200c001c00c1c3c000b2103003111115242d09a4098a8289c1e0341e44140c0b04494003040040e00c000782c010b0310305a41c00c001c1d0001003042031141c10a0600c512a038070700c00000401036031001ea44001c15800903140c414155900045012 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 22794376 1250 22793126 22793129
    0xa020c010c230304020109080609150703021317160605030615070f060f0b03010c0302090a0603090305030c0a0905091e011a18030304121b080604030503071206030804060504030507170304 82
    0xb50300e940c2c80b81c1d20352005950f4514160001c14141c0f103803c0800a40400009103180200c18260039010507880b154403d5040c1d01541d8035030803007924000c0c000d02081d0b403400444540442d0b500d080340c0c8040f40f010710000b41244950407190005000008100c1c050900c4000b10041102c01b0b20b0252400074103454200802c1609400227001c01d4036035003002c0e100d50b140d802c01c0c1009000103000b007000200d03240014009500c40b10120703001c0d02c442480024203d00170700c43d60a400350962100c0b0301e590746005011159030b10000004061010850011a0548035040214410070603d01200091140c0d00d204110259050f4410040003100c118441036000140c4103646032480000390304124075104000207821360142d500000c905008298144007400320701e00d0b06240045448413240036058a406040e91030350030460b0080c020850070004148103610851281000c0d00c5044000929240c4a982d042c80f6984075900101c005100842d0074001e202003800b048004200c0b129032961000d0856011540f80d0086 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 22795626 1250 22794376 22794437
    0x705010c1a04110901080a020405060d0c030209040609170405130e0706050f041203030605090f040b07080402030c090a050702070f050d0b0705070b0c030103030e030f07030b06010c05060a020c010c 86
    0x4a1002c2010049248180268818010500021036031603001807903030346000d440c050744100d050030080303155420222304c0031101e00d401007c903030001801c40d0207201038601d01510440e6001d07650002c1d080451281c1e13120001006004031011366903843d20341000184406024208600707403920100c4c01c407900000500c14100c900342c1c00e1003525181e0b004031584490040341c1c001d00459900107080d01c1010b07030581c07105069460445102e180368680b6101c2d0042040c0860b4024424611b4030702003089a030080400a42c445d01c01011942004025404140d0b00601903900c10b03050741d2280144080c054050026001030704044802e81e080c140307080c00183e560004140040c002c1880400032030750b207a114800b02c841c62500803280545904040c0c4a280d0242d000344070943c0054041d82c3e050035285404a24244a800c0642c010241103084d52500d50081c04090300a41c180030103442450b00160007805024800d00100b0030043c2c0703034441030b070340c1e18207540300192404100300c050300440341d20f60103140c8100f448510 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 22796876 1250 22795626 22795673
    0x2090c131401090e010801020a0f020a2609030f2a031504080405091501020d050301061706040e0d020106030b13050304060f09050a09050601030f150302121e0703050705010c 76
    0x900740c00503505105590088480000c000001142010054008214021165031801032024044404036100c80c0c0a05000700441040342d070041c650640101514000780d40080341074508400500003915080d008404071010b50406006121507441c440c84221400e90f0b0609100c10b128011b00000b0b4881c0e0700c42100c07002e800c80384c0300450180803500059034040c010150501d059820701041c000b4070312440195143c010322410b0030031050709100e401601d0407145a9151202d40075202000f007900322900500f890f07040303070762621451a1070350100015440044031b0b400014199056003815180d109004180c1c6c0314084168507000d0000d9000000c840484d4090b1800000c1c0d40785800c0100c945e020b803079011503400540c3e401d0100f40e034491079010f540180001d80f0100580d05440e18600141d6020f68107000108200b20b0023040036007411514000d0303807080c2c00180c0340074200c00064440300141c50070804110740d00150007403042100820800018100900300007401600c142e5504440c0d607960340d4030012011 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 22798126 1250 22796876 22796909
    0x60f0115021513021207230d0201030b030109060f0617070b03040308091207060e0c0409031b03090f03050307021e0901060309030c23010c14070605060d0501050c040302090c13 77
    0x108410101c000300e9500a14601c1c1041c840001a40d8801d507e0060b582d044207a41080001007864105c0c2c2d4050200c0904840710039401ca0700150000c001c02d0700201d806540710405000015098450500307041401c0d80d0009100d800c04000140c2540e084907607182a41c4803120a200c60700b000d80c29698001d60504d410403103070791135801150510b18926581c0c11081008510701040281680140303800600f5902211000c0c6a08410482543e034203c0700500828044c12550f030701c010b111140101c2450003824400000e0b50303a0035a030a030304013a5902c251030640010402c1021441c1001081d002681c484d80a070f05400344180000d59902410300c10802031503601c1200404260103107150030806500100748091541500d400480703d0150442c400100c0d500e00b1060003105401081c0003400c110742014107034102a0b0075514038000300005800150300411010030000051002d0181a02c540080540c2c251224558418452100d07006411008a07840c2031080000800710780100740300303d5000082c03041140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 22799376 1250 22798126 22798141
    0x518030c0c0d1707031706010804030c060e0c0603090a060b030d09090b010c060c020604061107050a060c020f10020a0f030516032a02010603150c02061f090c02060f01150215 76
    0xc1c140c0c2030544580742c50100c2c08006060b0003208890701e50030001c11480c01b40d40c1710001194a06002c8800170701280c000c6140d00040360003940440e91061310b680413038140049520001d01e00340c00844001425a125044840230030400707018103440000180c0051480d1103c0c0b41c0003908400d61401002c0d0895543c6088000d2a0b101e90750480c0356130740040040200da141c00d440251200c4048070306551080c1003881b243d10101c0aa0100d5640c1e94111000e04401070140e03a4010141c0611101c500c110322409940d0340d03c120040c010740164800403800103988006402307024084090001c19282410700d8a8100031064010f49183c580021952030005103680c4201480b00980106d20b4560035075180c5c0c7c0b10300103183d0f601540030206490169240c1c020400c2203075000c8040d00c040000f1400103801c14000b0070100390f040355a0000e996a420265441d05031900c0000045456071502d200050303116038148450302e60401c010781e0240c5494080c8804807a06404081c1d5102d007401405018150355500040b400c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 22800626 1250 22799376 22799393
    0xb0d020a0905060f030402100906021e0109050610060e01020304050d0b040f15090204050a050903070f050703020306070917010b031f02040807090b090702210906070b0106030518030c0c0d 82
    0x20b45002441e05840348410f2440408642040320128002c200280408005500a440c9101140c4556005002a210140c015031002c40b4444401030031359211086840040c905004c81c43c4294041100c2d0780754a40f4004008021040301500780d41035400400c41030005494000000d2046038200302c0000b0035482d80e14201e0051071541c00c0142002c000b421102202220680040c400c29000310780621240d01d5400340e00702120740994802060350300401c00c1c000041c80202d1000c0c00c003801582591880c81d41d0782c001c03074101142221510300280c0301e4035043c480601150341e03100640c00d240c802005581e04100110340e03904a11301d0ba004403107082a000b40c51444c12a0105d5000d0204141601ca500f9541c00d5104080c0004140c2d1921900c014000500710782d20004140820b504200c080100740074078080c41500c558810742000da040a001c01a2030041559100c406000f0329180e58000fa091601564040750441c56195804940d00208055990303101c0016000100020446000b04140d4071482c05108 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 22801876 1250 22800626 22800629
    0x20111030c01090c06090602121603050c011a090115081503100207150c050c0307030804030e030102120708130c0506090109080609010207020a050409080a0c110d08130e010b0d020a09 80
    0x1115803c01d1801410040620146000c980481e1951554103403a01d07400e030b8481e21040d49981c030381c83c010f02c101c0744901400c00e11001800e001c0d0070002c0c079000c0140c01150030758a24120075501e1030b240b25039038981d40c00c1c03405000b40100803001440d00174095010004000e01006850290010310740c0442000599003480340302a04000a81c0c00c40d500c881500c1d103180c0280c2d0200b04907400c0d0740380c8020404110f004008a030342a2035a100910320b0000540d07810395100e01c028000760104005c001e0880101d0b1801d200400c2045010f00c0c03245002c3c039040100030304100004003251007405065031184005160340c102041075800440d201c070f84401b4102d0040301c200419a100340f4051042400b4442100303019070041c401a402541c020340d51a44600a00c010f40d42c030a207000b05004010021208802e1180d5112288580300381d00420034807801c0000907104020005050b120b0300310004d5500301ca81e6140302120000e0004076881d032078562500c116840366005140340b08400640001710140c00e81d108048500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 22803126 1250 22801876 22801897
    0xc020106050a06030f0c030e15090721051b010c11030c060a050a0210020f03060904030e030d121404120c080d050f0601030f0902030303130609020a0801020306030610050102070302011103 82
    0x205007a0780c3c101c000c01034107048035810030171843d011845141600c039000c0c2c00c800202c03003801840307460944002d021032080d00030000b9069008254020412004144280e03104c3c03a88030710f00e12041180ea0424500700141030207500f80c0c880c1d8a02603000340780d07044058201c207030f90001d0210307000003640700200381881c200c1020300d03602c10000240d0502d055003000c013419810006508595819041201070b00403407107107010640c4102c500b40001003241c9490705103e640107100e8944031074001e6032100401d01e404c5405030500702055512540c0d40905200348a04e1038450130103403845640742440c0d2149d04109480a21200c2044044c400300c4041c0080c0c1c0c0c0455105920ba1841040246031007161051041e105841c910700084c01c3c0502c0c40020002405840c4505400030b01852a50715042c04141c140350280c0b40031124180c8864080026036200050301000380b11340c400140c0e9a02d019401c00d401c04000401f061702440220200b8040e40e40d000694900344d0f075082c01c01c0d23004c003240090b40d01d00d940151070306d00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 22804376 1250 22803126 22803139
    0x50102070f17030103260c01060e1e01050d030c0f050303160906080f060405090f01050f040c0f0b0702040209060d0c02070509070201060b0f0d0e0d2307030509040c02010605 76
    0x210401c1140005000c00c603008602405103000740240340c11541c8800c1c8006059a560b80c40d07440501c0d44008441a0745003440003c65103829120f04a03142940c41a83c0410791003d07001c8200800624000c0100c4081040411901e80660504000506040d4941d00280800c02081d42880400141017020380c041500103003100c5d181d14041e41d5000f914080d0b11000030000340a0040090001c0c003400102e8050200d81d000720b04581e03030310030911008000040102c076041c4143d500b140080310080c0300d40d6000b42064501d00341c2c0380c9018113185c00300d00f01c0f5903c0700b0180d0003000b00c20480200e0b44c0c0143c0d00c0b41e550455015a948104200145140c003808031581c0c42e50380341c5440b2a40150300024120100c503429500d5002541d1a040b0aa08807101c40c880c442094034100060502c44003103d000305004200807200160b03511410326010300d0074035413021302004140700c0e0310203018010323221240400c150005884280341c1911507400030240d01484c0b908501441d181e0482c000894001c2d00114041d0401800c803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 22805626 1250 22804376 22804387
    0x40b030417040801091502071101030b030319050c060115020703080f0f0301060206040614160806030106081c02070b04140108090705030f010f0510050a03080a050409020304060207020f01020c090a090f050102 91
    0x3c05000313000d12901180c00300e005007094036100f4028000c4e01e1034540c0051040c0c0711807601c180150068001c0b1128664075010800c0030070b9481075510b2103401d41100b83e40d1581c0d100c0c0440c580c420304e00701044e004800d5040d40318880d1410203070b00213030640c01c0c0ca61140025031610008440c20b000340c01410180d001c80e60000c00042050340e40010f042c0d2040c0d0052a003808075801c80f50710703203035080810342c1e0120908403c0c054200d81c0700d000b1511070360004d50150002800c0b0355a1102507043c1103207a0020700310b08194500c07005541d41d04010303031000f400003000c1580c034151a007010702154a00e81601241070100050020745404070911013100100300203003e460810310514a258001c080c940a14250289440c02090001c40c51a03505016510082c1c0122007490840e110500c003130b0030541f0800c2c00c2010401c000700b00d12070a0700246004d00e11450000d41c455005104210050483c59205411940300583c2040c40c4c0d41d40c0b0b641140c200304200340015003071400c5e052020750308100b085d002d005580000340c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 22806876 1250 22805626 22805639
    0x405090c0d09150507031a090604090f0f06060303091a0d0b042004050a0f05090a02070503070c060509040f0b0d12030b06120109050609011208031e0708150a0308040b03041704 77
    0x30034428841780d0380402c542010401e104190b441c484000a0300700c290b50000074541d003041d503c0a9045405140c03051101201560348010a003030350401203801e5034548000b0401c1541014100e4064401000e035002c042040c00300c000002e010f091104070380e06840381c03aa055162110740c86110344d12012a46420712182d000b00f11b550660040c0300c2c06002c2e4a85400011703122409102940580d00010480451a00d03100c4140001c0d400c0b0315402d5829000c20090714000441d40104400100510344031356484203014001c0200720b0b0300b205807950549083c009030501030390381e4120fa00c102a0340311540394140901040100c0007032031000c08482e000040001e41174031070031201c2042412100d40351810300407503a5000030b02c2103120080c4600d030220340c52071900e0300026009401440c0c2c40912401903503112044101c14006048060b01c10a000c58102c40500006200ba07542d030300c86040d001e80d44445603038915651074100e84602c1c0b068086005011010404014070001180d006051814210751515100c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 22808126 1250 22806876 22806881
    0x1e0506010609060507020306060d1707030207030314042405040b040905010f06020c0102060408070510230106030e0312090c030307050f010506010309020f0402090307090e0109020f03030405090c0d0915 88
    0x424000c62031441000039540c2c81139088403141680903001d8046515007005116090303401200440d04100d03a201c000b0101203001010308040c40c001c0d801030141924504020300210f1000341102100300c0204070178410951840c3c15603002900400c0b04032a04664683c08031654010303032304142007101c8006000505000290040c81c1660b03080410290fa403a900c4205994424000d04890701680040c000540401c0308803016121050050054844100280e00010200c401e40c0c0884000e0040d07074800a0a040d11009e0824054040c5040070000c0c0642180c00c40e41d0b034014108856810b5030342c000011003400b0f00340490000c1c2c02c0d01604032503c9200b41d18105c0d40301c2200c006a4041981f034030001542c01c1d031181c00740040a0350054214282e8003102c0d41400f001e9840003040e1500b40c0305115001070340000600c036086c3c84450300000000c0701071092041101140b102d43d20603203c0e078410b000030301003640c4441e00250000500040c942e500d000c150310601c05469841d0001e031008480903119015521941c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 22809376 1250 22808126 22808129
    0xe0a030c0501111501090b0312030f01060503130804030303090b1003030504090c05070b0c030106081b0a030908090a14270604051e0705130602010c091404110d090507050d0302030d05041e050601 85
    0x104d05617243c1c0c9c0c110f100004210300045070003400401d0910300410085003e03000654000c442c1c04c404506c002c0b0f071307a141e103c80f56105034030880c002aa205043e009004e0b01074070468100490700c00742c48207076255860040c49401640549004541d40b0200400c940340a102201d0310340b42c0c400b54654161030141800382d0990024819000402d0310000081d50720300448074120a0000000d80d011b003032401c3d8400850060041c000102d810100400069005039120b0714940010510120b640c0717040d581030b205220101060310400042c0c402d0301003080d6803030500c0c0c0019961020050b03c001a990751941071010034401155800d00c01c51060f0401c0c0010760368000001d1803503d64101a05213415500c01c4200e00f00c9144819400c0061411030091040310354008203d040031000900206441c20307041448003155000303010b54000150780e5802c401c00c00c201402400020b140c121800c5101d0b40381030301c001e03460b44600c405151800340d407000040d0420400c4080368030050001c04d201150010585044c80d580c040a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 22810626 1250 22809376 22809379
    0x60e010905010b01020f06040b072607030c14041205030f04060e0307050906060702040c120e010b120601060c060b03011b0314010806100b1b03070b070e0a030c0501111501090b 77
    0x901c3c1c203050f039035400010034454075804180100340c00c1d51181c43e07280c025031010701920100003680110007070b03403441141c543c1005501c50001010742d050140e00a000c450340b080c440f0b4240070160f4400c2008560728800d590480e10310605540d56102185803440c10340c859541d02260312880410b02180495008181050021060b4210b80d003081d125400c101e500c40049400c1e03540302c9401c000d03990050a003a040f4950400060408481d0883d03c00341d10380580301c0c03c42e4855403ea40d42c24083d940e51900048191807507c450003c3d00d01035040001c002c1c101210140064410f50300d034007890680351805d511254401019904141344c01d4002d0300010003030039280d04c265010104050001c582c0040c0410124001c074005005125660314024090700641c10442140015041261800038000000c2c8000c0281c14800e0007020901d01c3c1c4000060f21120840032400c0c020701e48590140001075240c00410b0a90340c007428001d1041450012052810b21580401006114076000002d0802d0040c0c0040031400740 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 22811876 1250 22810626 22810631
    0x6090b09030a090f050609061804061403011407020d1110050f01030506060103050906070c031403040602070b07020c010903020105090607020a080706020c062d0706020f0301090507020f0604060209010309060e01090501 95
    0xd4404403074604c0561401029030109080080c030140d8030303200004281ca00e00c200380304158105501c00142c1198401e41c0308040345825204440082c2c0303000e10400840c0700511003078000504006000a6880b07031404139881c00d101e0030398038403500c2c2881000b0f01041e1001a550500c070720314104252103a2103000788000c0351644600c0740420300701c1d07029010f81c078420540200244034650b1005030446441007001c20640038084449010b4800e10784001c000c52085000c0c120142e96400d01d481c000c80703c018010442c0d400c5410110030000b01c0c0ea409000380c82140c1d02442c280d07444810710000a403040c49004c01c000d501800f2514001000500402d40000b00d440035001c2e102c24501c1c84045c481c152180d503a4483d2002a12120880000d02803000c040d490443c070b1503141c6c1404001c4e03a440040741d02100c1501d201d02404401007140050501401fa4811224800b900031b40c06000d003480e98804002d000140320540102c0e0814869220342d0080c01c5080c0c1010050061060b00c0c882c09000b02042001901d8550 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 22813126 1250 22811876 22811879
    0x4080d02011e1802040b0a051f1803030509011404090c030f0b0102070b07060c0302040803070602041e0e0406050a02270f01090503030706050603150115090602011104050d06090b09030a09 82
    0x4142e1007a14280583c0900d07039101c5229a508100003004407960444c2d2122915401082603241e11034480c013180d0030100e01c0802d82c081882c001d40a41903c00880d00b002041c1ca00030710000b5803020076035103c400c080c07e2481200030000d2241030300d0302454110355202854528140354495040d0000b82450264002c20030000d0190001246c8511003801f40c0f04014104000741400550194846407049046240040c00d16407246141c50640c4e011280036201c1d280c02041c103010340c0420042c9030319680c002e02040480341d4a82180482105001403020700900e9907480054000400d540403500c806c1d503907105010818030800346c10048030341004a024051080e02c00c040b43c19500804031340f001e850000b00111308181180d502d80c009044020100354060080000c40f50101e107604003034a000e02900590642040060b00f8000c00d008501da028400b168145165030054004280031142610740c01d44e03d4220709901c90802002410561000a10040e49c8400300400b8038030100c0580030b18040c42d0f40c1c00c00b405 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 22814376 1250 22813126 22813181
    0x21c0807030810080a110a0305010518012f0c0f0f1e0d09030b04050a0204060e06011209080a0c05030906040801020912031201060323070504090b06030411010f0504080d0201 76
    0x4445409401c459600ca8030600001c0b403001c03100b1b49034658000341002c0c5141e03141c0c0d80362425a0029500c0401d084820380e001c0c01c811b0b0003030241078072620015002602c181800300543c517007180782030081819804c0c00103103004610001d022511003540c0180403288180031201500b55124592201e0f0301001030030180c1e104450308040b42c40302c0b0055007503075050b2005085842d01802c145003e0001c9607076108005000d80140c460740242c400038a10040420954a4020005043c507890040e14540030f51400f0000c00003c4c2e03509041e06c251059a113040c6881d0320f010314081c4e06c3d40c81801d922660001d008103000645010540003404545001c0e24806550105520a5540c1e4040e6610b00107001c0882401800344074449d07400b242a1500000c0717000b143c684a00c84404842d9010749001c800600c00140c14803014459024000b1847c100f41c1c0e000746189003584403440b45400c690b940d00d040107007070252415101d11603030640e00680410800e444415500200182c0242480c03162502c0d0452046011100d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 22815626 1250 22814376 22814401
    0x14060316030206030f19050705090906030d08010e0c040305030c0a02100504061e140a02070302010e01051c05040501020c07120b13030806120102040f06020604150b060a030504021c08070308 83
    0x12640e014100904646445c815518506002085074840b82d030305208000042e81107004882c001d0049885442da20061181402559040145042c0c00b0b03901640c0b82c202c041380c1c041134240c110703600c2142030003142d101c510803401320384120351014cc80c620010800c4940302c9000304407101400e00c22075a002c010f00c1342c16025149070142d88969000b10706000c081c0700c481200750040741c284502d40d1400351640c03601005e40300f41c25003252040c0001680038000503c115600241c030403240d09000d081103800e0103004500c0c2184003843e81c43c0c01c43c84944a0010400704a025016a004444440d055405854840e500c1000e080000e50045e104d07012014007103108440800964010140c06503520300065441505102142411190440700d9650810001894541062402c0b0241c10b10b03a01404060070319051100041030030f9484c1c0c0100038900a0580f8003a07072410202c0e204510541070101d42d1ba540c03800025840740340100000703210070004271072004001c1c41c8130040040b41d00c00e40b180041d903190002d05598 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 22816876 1250 22815626 22815629
    0x30e0307141c170604090c0902030403020c061e090f04060b0c0d0302070b180a060606090f1406030f0a140a0c12050f01060c050106170606030706080405030406081914060316 76
    0x101d040d16145a40703c2c06004032640d44070f80e01a00204035412150f03035440340800c0c00d6000f0860140d000c4140801c1550510582801c0302d42111a0b40c10098116910181d0071750049003c0350001e1300180410b00c2c0d440314a40314143d520000d004120381d42e03545606220740c0c0d1110b1000c607190b00600202080c001e000b4403c1e00c844540100540342c040d40c0360101c086010100e81d43c00b00caa4818915400c001034124043c080280489586581c0041d181c249440c140c0c201603000700c0d40c800180b50340001c1940340c010540344c4c410b2207251030710032585604012038010001d03d185004600c0102c800c015400205400040215185584007000311159010500844000391400700b1060240001003006520404100b0a054066000040c40941c0c03648130b20244954a40480c3c2150041e01c10042e1602e03040c08828010300d21820030b0b203014502607440c03c0e240e226902554050004820220741c2400c800d80a03e01072030843c420421003003000a603800e091304d82c00ca550511074440c92141003403104020580300c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 22818126 1250 22816876 22816933
    0x18080105010f0302090408092d0105030f070e12120a120e1509030912070e010b0309030d020f160b0103060e030c0a020603040201050c060403050405100503061e01030e030714 76
    0x15003843c25642000f6190780c02500540d0301030800d00034900c0540d10324a0000e0346001800d10752942c030980d1841d03250210001c0300281d0602ca0103104003d50740d480d444840c0c1e440f80c5d05280400b5904400c800040c0d032200100d40c110380522030720025000c101e034058000c0500c0191a203d103400c042850182038103803422541c00c000c1c1038014016a80c41c1e22411242c003600014100300350307400e00608001044400a035079082001e15400313040d0410001700e40d480c1c12800350010100d000d05d549442269250740380700722401084141d50014495010502040580e0490446484e04403108015400c1c0003925490030b000607640c0702d2030000094043c10f0004125840f04604c0780141054540036000c0010036040144180d0600401308001c0d8004981407158604c940d200e501d400c1d0f1107d0400007881a040c840300b4500d0180300b401c200780100c6a65482d01402c1e850010031103201c2421148004a001d086080e90b100458413003c601003040005078554034409425803011204001c5041c0c2009500c03050114521 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 22819376 1250 22818126 22818149
    0x5151008011803170c0d020f03060907050906190c0602040e07020c0a140915060301030807030f05130b0c010f0e030703020c040204060813050703150506010314090d180806071808010501 81
    0xa101c4138819041c61a4080c0031814581d0415040c80840402d0360700ca4001c04900707070800400c011031450030250443d0030601d2403504234200741c080702c0400c4162040c80e400c07240785d9101d1942d44541c00d11032226068582e6211900750344890350f4911b403004500c4191031032405801000c58a000b40d0400a5000084a22800c840048041604180400040d0181105d0741601078030f00c590a140e200c440040d8000e510850130035070745004a05006040030841c0205404000b0b04010741281c0790000c104510075950a40740351556400002d0f002401824486001d240352414401c0d070b00d81800001c005000780a0003a025540b0ac4002c800c2048100c1c407881c001e07400400c0130708000c18014860404600072103032043c3e044a000c19102d0b11900e5050b900c21180080c001e403034104008941d60306002d44a80850343d46c0d842065818000c4c0e1994480010090380010030620841908164869818450081070140f0a83d8441c2c204844020140030b06080c9a0b0111302500800207802070051295604813003000740807 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 22820626 1250 22819376 22819397
    0x5090604031d01030b030106080706080c0301050901030809040209030106060f0909270f060e010501030201030e0a02031002030907050a182f1e030708090601080106050306040204050405151008011803 87
    0x1c10b0690001030074035034101a42c0300c40204c201d440034800e003805416400c0040219500c1d040000b0701d81c20000300307900303044038080c80100026103419816505403980074170015101d10708040460020300a00600c2603042d0b080000014840350003d5079400d030018159200c28050741c80e101103c013030f1507805116044c01448001014a244620011703018150700c40c1201d4001c0d070035aa11a20140c8580b90403014a503551500100f0441da050710503c003407c020b031805803400702d9850b000280ca80015501c0d804140790000001080344005000070b002802000b09100c5045494035550170061092641c01040c19242a14460220034070f0480011000513280e800312400303602c41c10307605668012070320290244008140500031086100082d6216210503614031405203440d141c0303185042d2060348032802c0c03a490440d040c0318a440100e060380d84a6015103000c00e45071168504140b90203c0d030781007010009040414080c40c19035603020082181c010030000c1c00315401c40b80e240f02c05000010002404a01c40444 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 22821876 1250 22820626 22820657
    0x2102030903061b040b040b0d050106110a0b042102070503010b06030603250b03010801092a03060504020d1202100c0807170712020d020409051308090607060204050d0602030a0509060403 81
    0x2010004940c0f000d2a4508069841490900f2504190421502e81102207058480211244106c0d8010030891a000202032001d40c3e00035251400883c1c00b8107001480400201440380801060845034101e98a001e500140c07240000d4813000503005480c825400c00219007890310700385c400d0b28020303140280906010152011015601d0090200e07403003142c03800d000e0019000000700c1c040c0d0700800ba03100020461000d5450614003002c800784401d1380b100c00c200201c03596590074004410680c0d03032040000403503441d0340c00091419040c601004010070341c0c52105180385a80890701074454004000c3c14820000e8480098558101c00c171802400a00680c1c176040c0703010101440150030080a04000707405489820515090b07a10190301d0f225141d40004041140d0000c03840b50551081e41e00041c103031081c03005d40d50400d20f8480d036080c1701d2040c4800b2401342d0a02450f6412034000349001400780308202e05603d044000b80d04200c4481008500d09000500d0811000c02d605100c0d540c1655010881d000450 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 22823126 1250 22821876 22821901
    0x601050a0815090f03040303110c040905030f0901020a05030406050a0801080f060412110a0506160203030f04020d03090b0304061b030911040213120f050f03071104020a0e0d210203090306 82
    0x4001e00030511513a000919110b00a100500c05140aa998100322100c005440380c82d1031a4444014000c2e86800c0c1004041303134000c42562a9840030620040c0e44a610400403441d00c1c03c503001c09002400001400141542c005004004e02e9056854048950ba40d03030080b1364848801c80b800103400d070424000a00055404801551405400d05081d400d21a150900b03d2405040390411942a80540300b8007801d001c02c22944102c0c1d074100d200851442c640700d20f0840c0f210f071000e80001e00a10180c64494205030241d08180040c00c04000001d49038949030520001600d80700c032604120700100c0c10100c1c90148070b4000d00c2c030742640200e200000c100400040c000207502090417140c0342e044c1c0d1900820b0381c0241d1802e817100745025080303003582148142030141c01c00d011840861001c0c3c0c000c01410000950034031403805142411100144c803141c42c4030069070000d850103250741e030042c0e1420302482001010284d11210041a040341e94541020340310a03a52407190020b0150305508c070382c0015041c21500c6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 22824376 1250 22823126 22823131
    0x102120a230c010f090219120209041406100303030f020304080304170c030a0206060405090106030b07030c09090c120b040506010507020d02060403120203040312050703091401020a050706020a050601050a0815 91
    0x2061030034034048500d5142c50842e184590b1821089446184000643c40c14038410601280c80140c1c800c4190300c6d020f400b4510514846000b40100d914a0014083c42541c95403161180c0400095901c949400303c4104840d0f442800224046441c0442c1d50624003007504c04d9034461640303c8841840c40d259a00d4111036032045400d0746420b0002000302800b041381c203002800c40135026400404803400c2c400108400c2d00c10080284410f41e00d862820400700ba5500500358100e141c0d410001016000c0c40d030101c80c2040c2d5501f101d10224103052401b141d03a640001c800801e415482ca007000180014000c204c241c80040d03a10070b00240d401d10492000d85001c48440900e50310003841c42d40b6050340c0f03071b8aa80403001014007000c013580001c036040040c0516004141e000d00345501d0423074038117189a42e005e051100c003030040150040b56405004480d034001c010300d034559a004422a10a2982c40c50700039510030070071600316400d000301400001c090800c500c001b0180c401b680c1c043c14082030104150302000c40e00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 22825626 1250 22824376 22824437
    0x708010203160518030106080a03120b0306180c09390406030b040603060c051207090b070303020703020c09040c091a060412051905010911010807092306040906050102120a 75
    0x100701c03040c130190303400744500002042c0c02409440a8402c44c140500740c01d440b542060141800c054a9800b141d0b0041541c0707522107000c0001140c0c00d50b00700003852500e0244a5003503000310b0b40c1e000744100e11030002551195508505829005005e03401080d44110514246440c40828140400e00465020780c22042c00900090310002d0201e560361035600660340c2c104640320102d180000c01d054201980340c0d40c294400c1c0507060042c1580c0c54504480424031415001030201a804a0307001c1c1094400e200310707020858010419050b500300b90800940b008031501ca50440d007440c040000100c40f020140940242c0c0d801070400341824031303024240171282c9062404598502a01c400c24503685201d1403da204c0318026000041c1b090f9036031824600e2034120b100002e0501c44100308225059034010403100640381d40401031125070015010400100388400c80301584130101080100e01940c065110f0011034800740e00300e503405e456040d03031500da03842005422400100080e424840384d042c040240407041c0384 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 22826876 1250 22825626 22825657
    0x10050f0609010903080306191e080601060503040312140f0a06090b0607060f0b15040f0e220201110a0f0c0501090501050d051f06020f01060501050921010906140907080102031605 78
    0x23102500401000350802000540b04103101100d031007d400308103003d0b100e10002030819504040d070280850200a00007420041c1025198000710590f8200b078a070300d81c0440580700a401c0c100240b4400410480b01055000d14140b00015454258003501e1115240549000e01e800c5890300c8a02c05010540301c01720303c0903103d04078030009413101c00031064103801006607551242c2c2400c48400d4031001640c0140001110201840600000755141400c16107088603482c20324901803005a030a07401e0300000400d01d0081001110a001d904440049014031540c1d071003c859442d1401940c0301a59030148600040d424444d140d04e00c5166030050f81c0240c4582c40c880c003000038800010345025020f4000500681010301501a441024040c8030090442424500d04002042011500d02e0000e42c001d484a00b0106070b0380c0f07a500201b9401001500e4000209000324624154800c030040030a458143e9144104500065450018402c0d00e000d601179070340301944c005c00000c00325201e400800c031030000741d00b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 22828126 1250 22826876 22826899
    0x90103050901140f010303030507020106060906050705010e030d15080307050a0b04030c1203060303030b0904030e100e04180b01090e0a020d1a15030c030708030a0302030c1210050f0609010903080306 87
    0x780c240039070f54410310110b1a0b14030707103604600d801001d890020f040c0030256810a1000d011164007c1e14401c292100e80c0391050f219052410881d02404400510940034000002c020010200c1d9800c0100c40b00d2240100f801421740d030340c2603903640748038201028100e5040845108001001c5040c0250800d0080c80c01e801806001d40f00c0c000050808075000300071a03624001001016098026002004006c81d44240c442c50f054402520902c13030900b0041c0b040d00700e80300000e8280d0084c02e01e8282401c000d4000c101c800d03036074228141d004400040951340061400700020308566a802008000c00c0a42d005d00007210720340d03090003a0400c51140c22101040d04080c0a0411800803103050b01c92010000c144220804e001d00741810712460f4a004d0f8080d0704642002d000c0b04800108680e4501304030f20300180e0383d0396403e400340c00a001c0c410b013058075282c15105220604220164110a50728100e8820035407241a10070458079111b00c445035804140e80307400410104008801460b4840030180940c182c2c070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 22829376 1250 22828126 22828151
    0x23010b1c020319060621020d1409210a090302040b010306091401030b0702070b030f131a0f060a0e040209090c04020a09080705220e030f03090d080a05060105090103050901 75
    0x20b030030842d10704084904050300c01000818074010b4000405c41400c1c100300e074804a80385007038603d0301c0351040b92089400040507054020103a01c2441841c007400c010140340e00740000001e0b20703903019494a40c07000d4002c4105101c41c1000703c0480302211030546444d00712518590a210151005e4860581419540c0c0c6000640038440d00644214000c80c006c1c03030000b0745c1503140c0101d000310094415011584070b02400d00000703200d8003c423900181d42d1030040348560f8601c030001c81c90312800503004020002c04040c0c40e001821031105280292040e0750024030580d160024007040040da40f0851170048201804100075040000c0180d03080070052007514804c0c1a590003040c140da22031001c0c0c3c0f0000e9a4190100080d120a01910018202c112a501c404031761025282100000d004400e200e1907590f61181c000342c0c1c0c820802c44000c0000c1540050312481c0084485844010341c50080010070b6040c0c000130031410440c402c0078070455058443d1424074820034011001860010840c011565031031696843d0f0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 22830626 1250 22829376 22829381
    0x3030b0a0e04080702030d030e0a0204150b0708040305060a050402150a020a0804080a0209010b07030e1e0409080c0f1501060c0c03080304060207031103030907030f1a090105010923010b1c 82
    0x460207400c00c1584d400c002d05c145480c00034165100c108061030482001400403000c6101d03d036180d0100da010801a03c03511610008660030381c45180814070025507c020090301b000680112401442500c0007070780e0300313030710706007598001c4400950000c41480414840c03034003d400fa116a0686104442002c901643e41015680c0681c03c25851076101c50402000c43c94104603140c094201b0441c1141020203690340a0400145181001c0c802d01001ca21084840503842204850243c01041402540c415041488495010901c214200d0240685111410400044002e0010258a07400c0300e0b0340c0c6010f808440446003040100d6007061249030002c04240740c04061350003140100740050ba14030b01441c01074240d645044d40740c4030580080c010441801c1000c05c40e4021079030000b6088400000300c0c500196601d05080c602c03900c0d5005030f8140880131905500c0380e0b06980f01c54500300820000c02c0c1d0340d212002c1460780401c1e03881d15072000500049041d04041c1040401d07040c0d4030304480c02c0d14001d6509 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 22831876 1250 22830626 22830631
    0x20d09140f07030f03032c070902090a0b030403170a05060103050133030f02070602030702010c09030c1505090d05010608070b040f050609060903030a0f080c04060206040209251710080a03030b0a0e 86
    0x401400c0947ca1100700e001070125000030200d84030f08500d4000c4403008260140b02c10306c61500401e401000042c04c6c91300482600c94007401200d14281d261030310903044c00c002c1c841603c1240c0041e29040c004509102485064600300d00989000ea1081c2e5000302c42c00c40c0d281c88007000c1010142c6030403802c108251070b400604078035407081b40003586910b070201c0001d0850701c0440c055410491110804c00100e211845004280c803039801401000d154a1071041d03816200e80e0502030b8100d84288024024810198003002c240c0d850709042d18982135580070f5040d0680524001c010040e100224200003915044009005040019200b9800c00c000c0c0e00c0083d00f150025804100803c04502c4000c41742c4da0300c0008030350300c41d54440886040c103041c084000e50703c0e00c005000900035440708001c151070001c0e00c4116544c0c074075864001c6c2002d804160006080802015030710107110401c0700440c4002405040c0c420540310140010091320b40c490314102e0150800d103020a400c81c5060300041a914699044c80d071 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 22833126 1250 22831876 22831931
    0x11040605190203090109090c05070c03080a08010b090f040504020d0215030a05010f030f0f020406030507080d020f030304020108062101020d1b030b0901050d050c04020d09140f07030f0303 82
    0x68842191503446036580c5050720355039003190810001003082c0da0300000d0300300c103a800312a00003c1c50910480c064950744203504001d0411440680c0000420401a009001c010740941c1c40788600c0e6070324a01c03c0d03003c0c000c10800d00d0b480540080200c80c14103241d80a56030103030005142c0e078150440c51300071501c1d24002607940c5050a000000b0030403031240c00d0203400c1c0189003000310700e0101ca1468680c0010001d11403001401c1443c40b80c4c110040d555a9002070014540203005d960906a59180c181d07a03ca0504030070030003601803400c46229003500401034900c2650181c5a104407a07413400100500d481100c4100f92003c020b901c125107502c842440900350b10028040000741c4407040d20741c0d00021300102c010030340c02c050924840c00107580b0382c41d20b0241120310588440794440d00500d40981894464043d2940181c4082043d40d140350007601700e884040d0017440488842e280012250340c443c02040102803850f40500c4081000912031880b110501d4041d1178000b42500c44e0041d0f0a0303100c02c4544841 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 22834376 1250 22833126 22833137
    0xd060c0815010c060527030405030705010e0303040e060d0f0302012304051506030c1504141008130309030f05060901050c0c0a022404060c050d0c020105030402040b04110406 76
    0x1000156008600c0c160841c080d501c101e0000402540001e02045444100510454641e004035440901441044150700342c800216403202c0d094115480c1c0c1c0c2d40151151034480e00c01d280c00021a94050600c1c00c14181c0042e014518141c2441845141d18401401487d0000d07441c01405022413a84041c4103201d501ca82d0000c0707800d41d040c060405c0c0c258140310a41c0d414152050901c0b000410000d43c100054a0700c0009000303d654034400130781401415000150400c01c020b010300701ca204184000e0060315502500e5416020f0280c06003c94900f65840c00404900214040358541e61f00c0340790b20001500c01d01c0c100180e10303240c0e1f44403c00710000b4101107495900241c18021007100030300600c6c2c1d201007880c16071800c1461300c1040e15562000d50700e0280c01050759112014015001c03409440552081120255643d0f0380c1d180002d1800d000c4840c1035960307000b02402503034500d2240081003c1240c0503951a400c544654007004000c01080c025541d1180e500d00e0300500d80d800e2800680014095134880 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 22835626 1250 22834376 22834391
    0x120705040506010e090f04020105090a03030206010f0902070308010308030402040b04020403060f0c030507020a020f031204170c03060609070302160624050f0a0e0705040b0d06031202010c0806040e0c0d06 89
    0x912050341e00242c1900d040c428480303042991511035440c40c0d0780c081d4420320254495184d078001601e00e4450031400d103400048010b004824181c001451030f0482e0312024800a00b555101010070890288080041c005501e4400400224041c41c000d141c01070300007040040c13010020781c00a412030348180c2c02240c85540340c03501000034030060f1203000010700840c10700f07002c213280800d03000351a07001120009114923042c004401e0162000c00c800c5420303049814007070fa90307107882d00e01c0d684041c02c5040c090201d601c0340740f91505150901288880c05440c0c081e01c0b224941e10b50007000d03400b07900314083c25404041440340c0b030070210308280034240d5034600d0b4002165a14000c03207a6801c1801803a040030f8050400e1030400d0201d903c0d83c440c0360080b110070508000e103644032a88211442c0c4034503409507040c00808510741c20034402a40c000c0b07003140e02c50400d01100307561441c41642070710b90203140100030450182c0080d51a04003600131502c0e2010705002d88007510f03106000500c401030071080941c2c40320360300d402c2c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 22836876 1250 22835626 22835629
    0x3402030331030f030f09050303030a18150506030d05070305120c0c0a08091309020907080408070b010b12090c030c040e0a0501050a150501051206010f031b02010524060403110102070302120705 84
    0x1501c50040446d1034001030309414200030039a40d201c060010401c0b103543d07111f40d040251914041c220015401013007000b0084815240701c018100540d0b07241d1003401248600200036025000320385410340d158540500349510720021620003180100ba52803d02c2080000c5a02c80901388512443c00d0b20031001c84d038841903900705100d022000603540c7d070889858082d03074801690f6000d8985a000525240c2003504d80d88a1901c1d41c0b03540030700b6034010a0350440c0800401c1d40010000074000c5520300340100075141d43c88180d0150360300f10000c00303960160070054544956091035040b11003011020b00494400da1013554402d0308460b01101c0700b085690780c070b040e5001300d141101d10a100426092800a007070008101d0b05030501038001d000181070101e1605c081644c1c90094100e901c44840b4618560b5207001540c101a01802003110161681407803003e8592007044c42c070720b90a80814024001900f02819540d170070740609003644000e4154418034400000507030b545031200d03501180d801d0103450b03140c0c40e040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 22838126 1250 22836876 22836887
    0x50708010608010e0c0d03050403021207050906090112020d050102041a0322080301140312040b03040201120c020a1713060504090b040b091f08033402030331030f03 72
    0x1000b0b0070090341003010603100101c2c00a5241d810100c22030b0b03005550b0509190503151031003154030080d0440d4038541030858100001c030b1010300300c40095904014641d62181003007103121090050025620303100110001500b4206001c850a1340300c2c0c400146850303240e548001c00469000e00d500c0380280e0010800c01d04085580c11741e003002daa098040d10491030a07907038040890005024080349035200f804c0a0545c0e580c200301204d1040d03100342801d40d0f11901c507003607401103500c2224141d0220b45489244a810140ca00c280c0c00001000c3d4040c1c08040811349d10000241003461035100e210006002c0c052010001c0549640104019160305544520704905902501c4080d16130340e10584c9031001b03c141c141c84001e1880d40c49020262960b01d12808840640e0103e14103030040c6006100c08110030804a400c0c3d150388001c8a00180c500c950951000b03070034007914145810094246c3c000b4803074030608103c0032250004440745222003452008000880c4c2013810080e40c020303501e841061249105054105 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 22839376 1250 22838126 22838129
    0x18020a0503010218010813060203010b0d050615041e03021c02011d030a030f0c060c050c011104080a030509030708030304050102030709050303130302010e130908180d0b0703270507080106 82
    0x107034001d50900d40c6003e0480310f0300e0681e80c625030601c4035400c0000d0f0f0300704410040804443e03020500b15200c0d45c40d0410003130b00c0e4010003c28002e09107020041035861415005019180303100d083e00514040c100fa604051011001c4508036203500c1035030740800140e5800050403160110b40c1c150007101e110030300004140340b01005200c91800c520740310032031094a010495401c1c50742c26042981e084c40c13902004845804034a038010301750314038018142842e0b80d48840100700b0442650000d010000d08a502d1701c01034895445145044d41c0408414030000b40240c010309000700004050303482d01a510781b921404c581c401c8404444030f950000800100c03a4003c0b08041c041c2900381d0003141400c4080aa00100030050700000c2c1c14410b0600f102c1c0c0080e0b0f1120440300307242c4020981071003959511b01c0d1844c042d40041c070900200940100c03500006050441d90782c1522030300480801455100d000094009200c120b400700b44400460a80c2000c851104c40d0f1690144e12500c0200085841c04141c1401c4504a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 22840626 1250 22839376 22839379
    0x3060b090c0304030816120e06070f110303060d020a0503070303030b180903030f0405010e01060605070606060302030c070803070215130c0501021c03020c010b0a0b031006080f0a0902040b0418020a05 87
    0x14024800420340c005d03c0c440c0e004140c1050103420180359030050391603d0103c0300440117142400641e460207480407401d980595010b03294468004405401a0755025401c4a8448903900c18800910b113450688880c00c051400070301080e26898803030380464203100305604143d011a4840512040500304a24420001d02541401220703070f051801d03003a0348a1201901410300c140c04c06010030b05000703080d4403450607003c40070000c10110769144030107002504003500c256038480c504040060024080c0c022203120344c2c41440503900e0940c0710355441c040c680010b04035204500c41e0311201400181c3d4801e50078010340090f100c1e500b43c00f009192845915034107401440c1107401020390046203000081c50408007095908003d42c403040c003411058014100c41000642c80072800d080000c0c41140c0307200541c000d030003040b004504941c980d001174403c04c2066610140000d090000552005155440072600c90b10040011910b294000c0001d4141c451408407006021502c1900100b146810318205005100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 22841732 1106 22840626 22840651
    0x30302090307090c0c030311131703040807060503010504050610020607120b06070b010602060108010903020705011b0c08010b010906021506010c0804030602030f010e01140f0f0a0e0103060b09 84
    0x4443c1425404286800804441052903800b152034a19009c11352a14292401880c220038281d0386114807040d000a010116802005020f10002001280e9819071254144001c11085401c06840e15210755810b0344079901c480d40104805500c80c1407401c0a400c42d4140c40700501c040d26000703600ca80e002800251440410581441c0d51b4180d617515400c80d00c2c1f581e00c900282c0d088803100d40700600941e11001d0200065840340a44800321641070107500c040501d20755544480040d250001c0ca0240d4650300c05030794a5900814a00c0180b220344001c02d607141e4030b02d40c260000d20000c0e1019041143c101c0400081c0810201220000c640c024030841d5680b6280d14040b400c80000c1c00b410044100b094000a070400d048a91841c90006c0140081e0900e4049000c000241049610440d0401200035002801d100c6119405000b9401590045012010101042030207003005125079003848 = true := by decide +kernel

theorem cover : BRFrame.Cov 22661876 22841732 := by
  have h0 := BRFrame.cov_init 22661876
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 22661876 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 22661876 ≤ n) (h2 : n < 22841732) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
