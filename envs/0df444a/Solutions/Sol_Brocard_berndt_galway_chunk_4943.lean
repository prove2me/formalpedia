-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4943
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:13:56.376914+00:00
-- url     : https://prove2.me/submissions/d2d81e23-608f-4b19-83fb-a03e50656cd2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 888848920 ≤ n < 889028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 888850170 1250 888848920 888848923
    0x10306050603040f021503040b061908030a03090206130303021b0402120103140a021c060e0c030a06090f0503071b05010c0f140c031e0105060307080c01050a050d06030c0e09 76
    0x25030240e240d0102081000c640051001d60410554501c090400105c07a41c3d01102c4100542003103c0c2640c940254100f0484140341030040c400700164000c030b1258036039007814003441c6c0e42d0003070380501c10a0658400501c0150741e268400d07150111000a14a05880d85030701d0f000f07440d2012982110f801c030102800010703452409000359032400082c1170b0001d0642c1c1c80c3d42c4030100700d28888101404d660203080c01c1103015031596020b488016650b0fa011070940003051911030201d98056002c4501d9801070b4402103410754010500e901c080b90040c201040a26280c00c007007401081c40180202a480001001010841e0b980e5092103032140e10441141c80d02d544500540d022851210000d00b0700741000c0350b21000881c4400d08004020400d0120ba24441d1400d022a18000e0b020028400030340e11a92a15109070090048a81c001c4068000d0180c4c2c910f007001035a83d030b000100c800d03414440080362017503006104805550501001c15020b002e100e50300c0c21312010007081402003c004002e0b10001960030300b0b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 888851420 1250 888850170 888850181
    0x8070801020d1b0e090a0b090424050925150f0207080106061b1a1f14090c07170301141509090f1e0a0c110f060a0b01120e0f07050103 59
    0x50768842400112130a410862210b000518a040039541c81803800e101d44c544040507489284244205840c0c9007000f440c418189940c1d40c2c4144c221400c0c103081040307200001c00c1c00d4004072001c2c040300c8406010040080040d000c5c03500300d84201d605100c13040800303e520101c007071034200700c0f902520700a5454000203030984001d80219004164521552111100d99045104580740511903405815448407a5800e002d0301c03c1c0c03144401c1141400c3d0742c1400100b042402e4000703142402145c8240d950400100e00403160040c00c50160303d40108941c028489402c1d03a2002030820307444459600d42c1c45880f2810100070b04179441d8040c0300034039201c440b03610742001159444180205014456a998501c3d550381110003400101c00c04440460703e426051308500a900410082802040400c50305400501107240510781082541c44400014901580451000d4201c4400307400411100c813070000581380001100b00c0c034103020b807800b010341c03440d02e03004100d01d0391320340c101d50589100399a500d00460549a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 888852670 1250 888851420 888851471
    0x50a091e1205030c090d030314090a0b01050d020402040503070e011a0c1c090f0909060c0302031612060b030c07050709060f060e030709060b0406080a11090d0201020708070801020d 79
    0x3000e002030026002d5406180d1040715103c64a191807606400b00e4400303070305100d046010130784804103404200040c42096030705c10440b8000742600f00c019101d2103020782040c0b150901400f58611202d095490319011140070700809070450780200c0d600c8284a4048400f4031683d95411143e400008084801d042200c24080038440200030740c91552041585255403580b420061140d001d60008000c03420a40100091118050008092001d030400340c040c2c8100c0c49070603003094030400c1008404202000510030390700031031400701000d8107442d05180092a41d41c001d501c803144003208003c4e9501440004000e0940304406403099140c0d0703095004281d030305a0003a00c640d6000108240300c3c0c603225800c0e404041200808613035109275150a44801c03036002c2d4000b01d0312070100140620155070480740e002d800049099040083c0e0912060103841801074000700c91007952400e22080079a0300c01c20412018010031400c1e26050760396007a10314001d5100340c00071003080c0e0600003011003501d14144240d4200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 888853920 1250 888852670 888852683
    0x70b061e0f0301060306111c2706020c1b13050103110409080f16021002060f0a0e0a1b05040c0e06070b0606070c060507020906240306040f050a091e 65
    0x900404104545103000c100740c0c6070150b58071031000020600c9402501d00032690700c101c0d103a031500d03943c01c0240300314080d0244d9010141404205079036602c0084001c0500626000c00e190f2852080c03401e90b0181c4910f602d544100d00c16802c50032402e228618802404441c1242d0819400c04404034000070380d0000d10003d4190292030642d105507041a801640966201d40050391034004043d199500503001441d1041660307a82050020460412850703102c10856940003c0c8014a0007200041d01c3d148010007800d034803610350034041c100440801802c0d96040c2c0c06034183c005c61a24500e4117048602c030303200781c0e07100e14200a540e10000c0d002e100718035803c4202914482c5840556124004a13010150200360008c0b030410140003c1030346182d681c405400741740c1d141980d4110707034010000340050141962780b050711a40120b000c0ba000c0e40c0d4a0401401e0b43c03030304450322a07031464005801040c40d404811043d905103810808106c2541d445185424030a041c1d2002034101c080c04560b2010046d10002d004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 888855170 1250 888853920 888853969
    0x80d12050c120903032a070f080f0d0f06090c270314010c170903192016152c1e01090504110a050d061703070b06 50
    0x1a2045034200a50006562522926209010032881d100790001c942d8407072950804030600115017a00303003106d034807503600f200d80c0300e0320126803450102c05101e00c0d10001c0c092070b40043c00004100800054440400b40d40c083e040d183c5d103d0324040c0018044021030126220b1400c071020415030b074907209110301e8401580d10f6440c0441000704020440c060a58290004c09440c4800000103528140c0203944148a00010602e400b608402a0030324141881c45040d003101c080801000401c000b0550b901d6816104c11070200300c81010007651854401482201141c0741081100303c5604008dc10558048440034200309542e56240d41081036005680d18000090000b90300c43d000441186000e140600107200c0307000d002c004000040c01d0003400a4001009055040c00380301c0b00d41e0040d00e0b0700004c1170f0a99081c42003142688204100f44281580c031001d01a010070116040c1605500c4000900400c0310308603030f0000c035820055560f07000850211202d0a80500080841c00c181d11a40110045c06112100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 888856420 1250 888855170 888855197
    0x21c0e10140a0e03011b0f02010c09030f02061e030c090315100e04030210020a09081e030406050a050409060602060402030d09050a12050a0c0906140414010b0f070b0f010f080d 77
    0xe00310101c283c000e40c107640b56080806d40c0c1e800c0307140d01e000e642e100e51141102064805400303402d403000e0b400e0900c1032118000040010800904101d600c040d0b04817099541e812001010381601c24130906640e190400200403c15803100c0e110041c0b03c010001c5007200d0140e24241e200219801040b26258801050341100304682c544201c10f00e0340140c401c0c01641c0030594980b40100032a002101c160001401c10b441c2004844020700c560549055102001070300c0026000d4455503d200d00d204000400000050741c02401d071007401030303070058081060700b4000f6540e5210000c0d07075004195400d80c86800348092510110780614003050403030f9005489404620b12340301000010f641d00341810394040c041d985050707000030007a030740d071401405000d0340002c0e82c1d6081c9940301c1401900803404a00607403401d201d002160b20b81d40300705811203c0400361650790340c0500036181070314050480300401c1d00030f040d002c0c05210095000118141e620281030202119610180b4594030786800e8070710030100701e14680264 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 888857670 1250 888856420 888856427
    0x1806140f031002070b0f0a0209450405151e071412010608091b0d0309180e10110313030509061605010c0c2001021c0e10140a 55
    0x14030000a0644501d850351810400690b8080701c0c080365800c100d98104850b8000c1d111049030412031200d001c5040c01311100100340b05c0c01c207a524480d0303d00d2806d07080701034076403e481400d08407407640e54400381d41e84039031500284503280c2903a04640e24001c072803002904400c4181c0440c82402e000698030062490002860081440a4104000c101d418010701d0b004ad4002001080200034455036510990715203c03009000102c042d0000e00141c12116140c08850544007901d601c8007002c45416103a00d180c0d140903103443d084c03540220000c00754018107004509052b4850040389455030305450340141c158552504861420385801907204041c0082400094070312540455207110b400c11500c1c000048000804c41e800100c465684818040210f00410a00f802545080c00c024200000455216615107022600c841500005103615540c601c1c0c09a2003001900c15401d034203070400c62200c00c020801006222a444200c1c01001c2030b00c80710300b030a4442c861603050030a1501e005403c044000c00e045 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 888858920 1250 888857670 888857689
    0xa0611031204030c110f060405130207050f0307121e03020c01090213020c12040305030a0516020405151f0503010902090d170a17060102070911190504180614 69
    0x50295100601020107114072031041240614000d031222107001d989480c1000c40f40300c09050312030141c0d82400c011111602c0c0d45040e14203540007191003208019200e1519002409000006800381c401c040c0000a45d800c080001d080e002d01132101e181070f040c14510181c400c20f105095208500ca641d8200020741031182e4054900c001c0050000315028040d80c00040d001700b10b0091411500c1d0340000c0030610080208800d50310084140e46003420a4910746179203449000742882001481000500b8007030350f443c1a003000f0071080d0700810400550038000da8003503903020501c1e00399006d40c20500000c494004500d1412a002c21260b5450745142c0c200620789000e90072401459030040041034500700041d00340108030300c030a44030710b180710b86034410004000d01885000ca0024400661700091003892703607004c02c1103401d555075454049040707085c50984020070b204041440300500c10301c080703d01083d0381c064002c204484441d080c8610040500f860641200d500f4803544100b0700200d510803603a420504d644 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 888860170 1250 888858920 888858947
    0x60f0a200c10030f1e1a01030b0d030e03120c010b040b010e090105100c0b090c01021213030818061207030c02030a1d060c0601060305070f030204050d240f0209030c0f0a06 75
    0x400d035100010404020900c0b007100c48401c85d9110925070401c1d41141e51444103d050905c2d041c0301441c00302001c1800b1121090029040120380e00b020386598808000c55406440d140140c02d55600d101e02c02c5a00910003110b01600c2682000090301c5d9540c85000c1703441d86030304004e09000c1c00b6442c280c1000420560700d8040001d0115541540001c82c44100c84544908103910141201c00d2031000024140aa02e0045800100080c030503040c4450003c02614140c80c1e00c0b84041d80e480040e03001003443e00483d08c0700c550307000703400080f01201c001c4901542c41c0110010344041c04624001501642c40740116a0010005603000c061581c00000c03607615a0481e44024000515040c00c1d07480ba207050001c26000040402d44910602052075030008017414042c2d000e00c1c046083c10708220001d10402051040500401d0001301d00740002d41e0f4102080a1f074a5415008000c80086040050040d42010280a00c41c0c040c1d07021100013400c25025940c01c0d043c00030324801c03185041039030030749050280c10b41 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 888861420 1250 888860170 888860201
    0x50603331503041e0b071202040308160606140d0816080406080f010e040c05090a110a02070314030301080307080c03041509030506091c0c02060f0a200c1003 69
    0x1818002625104028a003910103003261650b207142606041800c0b0401602454000520050010114040511403a0000c0c1d07545411404c0c2c801070b804c0320f0040d000b0ba80018004d21000250092400c0d8401004682030340b0940041c0111951401c03001003402c1d4812505801c1428a40f011002032039803001003080c0c0d004204040840c0c0480c0d1507466003900181c0104010407600c4c1d0501141200701e000130f83c01440550311505c05440e059958040ca0801482450f01a20f114004540071070320a804c104018000c0000180c2c4070b01e0074000c020f5658555200988441da90250403110303450010084174107a0384540c008528240e0070350354048042d44040e203498401d020034400482e10300030603200c04001000703070303600e0807600c50441c2803036414104080c1010903d9841600c01600d0241c000c280451250f14506104030200c1d180d0002c41c08038821903002204001d40052030700b200d00d8026000d4401081000c411a04c51030781d0014841c1d03a0880c030451aa40807081a01d8406264031a03000060700c0c0340c162a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 888862670 1250 888861420 888861511
    0x13170d0f09060c11010c0f080601020a050f1c0e0306151201050f25080103030e010c06020301080328050f03100506180906010f09050904080c030a03090606050603 71
    0x161414112005008210b4070315032500c19a141c0507520405030700f81200c11a000300140041000060400c0744100102c809120301100042c405a000780604490540c100041da4507501040d490503880c0c449401000c0d2411401e4040221034a2003400d03170050550000d00100075903140d121046808404150a50307074040352110b4049060078003809254040c0c00003541400305420086a40f211124202800300d07191524481030007221a8028451811280c06042810701c4c600d92078012207151131007c401030300c0030740000b00000d0044400002440100345a04040c0d92901e2100d40300501070424945501c00260207000e00c401c00340c0048015500310054440b102d80056969000ca0702e11b40001c0680419003041d03a24424142c10241031450748200240f03020420800c4043c0d024122131000e019103800740c112800018100000203046440c510b00310400c8a859500c174140040140642c0c4c001224000d090410002c1c0310300b04041901e005814112010003114141035844090207011241822a0200c02 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 888863920 1250 888862670 888862691
    0x3010e030a090e15060c0606240306010809190311070609030312020309070906090f06050603221401090b01032d0f0203120406050702030f06010308162603070813170d 73
    0x5d0740100b11160700741015010518180d0100007080c03155a120107200d00311005804030030b00350030342260307031000742420200d449031290f6142c146060f080c210b00142007641c0b200b82005040c1c000140b45240341d02c907002c88510035240c0e079045881d619603201c01004190319000c030040c2240c040e0061540400000125100c00d65241d12039810b44459501010301c66981d075035440890b0007180100805000141d92103481c509090100c04844903c4008104410110780904010014402d4103008000b40100003030020500504081c1c00f23290b402e20080b1906c12006d0600554660f250000881c505551002c044001c841600c4204860300c1c140001c980c58003446e98071000300407c00025102410381980c032207031039601c40d1040c1890480c8030034049106038084001080060204e008a82e24420b40108040208426251040b01d01c4401e910742d440345030080d11003038451141000030310b200d01ca4030f82c0d4003105034540b02e0a20580c03016002d005801e03400c0c40c0d100f00040c2143c1400410080c000d0368030005611000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 888865170 1250 888863920 888863929
    0xc09070c05011d01180203120a030b06130510020706080c070501090b0a0f06080c06250b07020604030f080907090c020708060c04090b01051204020d02061b0c03010e030a090e15 77
    0x28941400301440082050400400c003d118070382c03c43c040c03402040561700150700040e944524004c0c0184d00c0000010382480c0c154803c1e0016024200041e0000c0d0b258800ca82c03003901c2d00703611401154020001d10191080c028030000307800e0203c0d111031720f890142e5203038003041c1ca5069006c03d900b80d0381076498054900015000c06000713480342c1076400c400603c800103000703c441a500309038041c0405038401c2123000030075aa031000312100042c0d121b166031039000b404c040d200140e5400c445e001d0200b443c10380070070801b1030b000303c2d40b213204603c00c4d51003480c40000380105403005407007540d889246034884081407120000c181d100e212500d141e40100c0c0c0030140e8a519580c40c2220807150aa84000042000c01440005014404188100b420114102078085103411102c20004101031b100d800559000340075912041c0841c0c1c803141c802615912000d0303104400a54907681120142d0103503180101c0101000c0000c402d60382d80d540345664051120b86052003c1400c1ea6010781203c0d540e0401c0000c10000382d44 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 888866420 1250 888865170 888865181
    0x1416030e06160c0302032a0d060b22060f0b191806050705100b030607180905040311120306030307020103051e041a010f06051c09170c120c0c09070c0501 67
    0x104034101a4074505501c140b5041400c01c0d281c601e481f41400e070210070b819450080300e01549400b9264256040c2280c00c11102518050040640000205801810721503402c58103c0c00800d0b014414460303181e407001011794120640c80740f0040c56006100c2824103844032480f4090983e010720305101020f00d4880010000e00c503e42c00007010403000a00d200800c801071246070030150480c40708000103400180440d44810005142400f04080c0d00c1c1c440b0503001005040340041c01403080104854549460060a14012580c0001c034038401c2c0100b200080c1d0049044a1140714054055810f0402e00d60040d006440094078100c1e0811480390340380c9100c0c0c100c1691300e00c110b0042c5060315442d0f12280d03a184255038113030061141c1481c41d0405001c565001400c4032111250712460504145e025984a00200700031000206004e2208111041c204101b5024165800350107040e201c54403040101c9048a00c80caa0380031400c0c1c1c10070622640e0a00c0e0402440e98482d00318201828044502d45d100c508407903 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 888867670 1250 888866420 888866423
    0x5061b0304151403090613050a0c061d030109051906020c0d0e0117130f030e040c030c020111090d081b0307062007020108010b0f04030f06050103031416030e0616 71
    0x3500c0c01007100c020780c40169007032030b10300035000300e4030718140100f282c0d0702c03140c2c010911f8043d100c242426808202c4100284c009017500580b40069064940030000d0410281000610038181408100a01c0d442e040c0310b52980d42d0350020040196604160350802802d01c4d100c001e64016600744840d080e61007090240240000003643c640c010803080d000050242d80200694655120401c400c20040344100c13020b180070180c12500301e0b4103c904a107800c942c2040c07000b101d00e4020b400c0c1101c09e90303155015003091841640640080c414601164150b160700c2c000c000a061307000c081001c4034030102d0702480c01888d402d111460032540c60032180d15003a1456100d1030301240c4c8280d540c0c904d501b0224170000007210241030005842d00d091020b800080c1001e030180a02c0b0b018840c006190b10311107816504130f80045510500800c1000d0b45410800c00800c002d210503400720b030a0024400040e148c800c1200c0c0382d44a8402c01017001c5441c1d840c2240c0d00084a00038a4200c0300c10071901c0b8074410981d2160b103489 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 888868920 1250 888867670 888867689
    0x10e0105180d171b16140d020303040209040c0801140a1a03030d0c050708040f050310020405180a0b030f1501050904081905040e0a050411040e0c01030917121b040b030105061b0304 79
    0x240410300c6c01410340114400e080c642c98010b041002c0700a60301204482d00940c04844010054035507041080980d00c072a0700201031980791403819507007408031800d250f114104406040141e450358901c408008104003030f200303a00d80c108000340f022107907880d4010102c034a0301e440d0080c01c0800c1d56440c21003580c01038100241c44001c0520400491808000c494444500554150700300742c03400010904030341450040d00500c040031400a000501c60358000c0d040b0f62001070854910086519103152106160075000c0700c82402000041498140011138500a40d4002d00140c034240b40211041e0b001c0d940303c2c040c50f00b004410800018028011f144090142d5100c1d40002010b0405140050f080c6010b4401d03503001d141000303140208100081100e100011084c00d01148409051038101220b05114001e000c80031030200c1c840264222014800b44218030181140f6030303035000c0c0c0c074840c0e2690090b44a03020549100300014001410000090040903809071825240a1121522181150031070380008094 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 888870170 1250 888868920 888868957
    0x1103130b1c02160b04050a200102060a1b120b04021b1908030117030d0507030204030210321c02130b0702060a080612010e0105180d171b 60
    0x124074000e01000001007000e001180390002d211041c4030141540ca501502d00000c0e00001018031400b444490481a032110502103441c02083d0100c1001c80005803050051003aa00001c0c286291442484207090751540340000c000090001124400400506e820707074251580150000c9449a002800c850800394643c000d192451080306803a00f203292a550000c1d90101c08914041038402c0d0403281540d0744110800c0c454021b115003030303182d403207040f099090040c0350104010500713a160f4041c1c4181c80c401c031009507010030800800c40d803804060003901d001341c4018220450b080440a5001544110140000e05001f981d42001e26111080080b2000c00b640006485041034010712241001e4a80003000c3d40c00e140680d0003191b41c0d40a610001c10500541d0004141e4958589a03070150000d002d0000b4030803c111441158081c15040c3c07450700404d010560755035800400031598041c0c642c0d4564600c0400c082507086140610405810024003000c000b140c07481a1030040000c120040780049110741 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 888871420 1250 888870170 888870187
    0x1091706010504051e070f0e0901030c09050c040b0d0b0a08100606080a090c0308090301110f04050a0b03090d031a0604030b100807080706140f070b0912090f011103130b 74
    0x75540010301c2441720034001404040c8641404a0280d0010203d280048800b80d411030190360700e0002840c84d581c007a0200000100300b050148440059603208002803103151a0510510380601860045111522040c020f181c401b15856102c582e06100041c8030504c0340d0740c2e40351a2820150495000316449403255010300c1031640011116401c01240303642008808026200d403a0080e43c035000c020720340c4c0720014007410240c1d800d401a00a01080800040d41c55200792100f0030b0942c04be11520f4001e459007003000814100d110b007540e01ca03448008c0038003042680314404900910122600d030b1400c0080d038a1410741070301d07028050000303188203141d406a0341c1018058901025a40c0d40300c4025135001c0b49042c8101e50011801000f10b0340603080c000045c24100c041d64400740100f140041c09500c1c085800750a0010007864680600d070362074190364481d0764001c18600c6a2040c42803054000034201e182e4450f0f544159050701564103990305403414400344002a50011015500088410b4001326030004e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 888872670 1250 888871420 888871429
    0x8090d060b19060203040302120709020c0a03080604062d0801050c0a02010e0c0a0605031305030711100905060a0f17090d090b04030b1303020f010507050d0f02070b0114010917060105 80
    0x9922104180c02c1e03090070303403030000029980d00c5903000003070107800c00607049080b44c501003103001d001d001c41c40015234940c038520080544c1d800140f4016400a107029022aa160070030703100e40e80540742120003219400c80541e81d920700980c003204039003060042441002400e03107420f2140c1401496280b811ba075490a86010090a40301d58020071501500310038241c0703109030340386410340f02218890300b00b0a84170341c1c5045000d030291041d800d002d03010380000030310442005041007140601c00001c03220302c031080344010741c100c48010450103602e402c054200580d1590500030340c00070786485010310f4203210100e40c26401810161050f202c20740c44d40c0c050901c0407000758014813050050181c1ca0b90a505092850700e60f04044403000c1c10440b0100380b607180d01400d0510a114808556a035100203001504041100601e6548895042c2000e0742c80c1c0301c030002503049240201e81145410a10f2055541d00f03101ca95001c68944507455410701030035010018540d00442101c01c030750072000c4081c1c1707925890042840b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 888873920 1250 888872670 888872689
    0x90a050301060e04020108130f0c06080f1e0621071a0a0801050108040812100f0803040308040317040f090606020c1021110f070c0b04031205030408090d060b 69
    0x620a03410700200f80280308080145651081e024a802446a25030840e242100101400c010b00b8130201d02c0e111805001e40071103010201c2e001662046265550180a00300001081da40503003089964003010a14000e14400b03a504040e000302500310b107480181d016000351002c0000d40103d50400e0004106503034109403000c4460000d0403d032132500f188107800a04160050003203030b062048120101e0706111811041c0c07011924410306070219820181130030000480503101d01e50035801d540c0004540c10340c01100f40c4040329849041d9609041c01d640d41c12034424090114500769071401d120000d41e43c001038030700c1e00060004802c000b403c82d051150081c03d01d0030440041c3e02818540d0402200c0c1c03540101e840ca1415819003028801c0c19200000704042c0290900e803252421010070071043c1c41c02e81100512001d40701e15282c090702d0343d481030a500c5078042c0744005030000c2119240c40501900540043d940144542486440e0840c000002085e581c07200350161401d41e6101d00800321401d010074403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 888875170 1250 888873920 888873929
    0x90f08030702011211040905040602030402120f070306020904021303140c0415030b0403030e07080c13050c0a1d0307030605150a1401030c02030408061815100b0702010c0611090a 78
    0xa546050700c2900040c02ca401462120110650349a400c4d18100d800d05040c1d4000c7c20041005200c6030a003410103074061740050350143e205000c069040c0854603030028111040c400814054841b40b461511510002c0d000902030320b41140e0204501541e021a0403014030183d441380c0850740302d418440c0c80e040c0c5810403844d202c41c000c0e840c0100c1040800300d0582d1b05801ca03076101e030440000f80e840f454220080c0c20110700c417102920548401007940100400c00c01030a581c00d6401e030241107480ca401c1c5050b0740f0103961001c582902004000401e0b80708200c0c200740c4d000c14101468900c2441d0001c40e18185850740190f582c42c0d80d40c0300384030719403800c0c4201070000b140c110740c0842c41a080ca168458141508005541810354484c00b10f40f40354020f05c2a038005028000a07260a0f18201640d000001c0342140c81d00c869000d00c1144040031071844000328001c80e01002c000030014100b440c0103149a00901707080c3e061145104540002403d58081d4034441d14010340d10503280c0c04d154042c0000101150170 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 888876420 1250 888875170 888875173
    0x305040510020a020703141009081e03060901060f091d0a1b020723090a060306150e010b03070c12020c01030e0a050c0f0415090c080a0c120e030408030a090f08 70
    0x1070030f0310103079000881c1c8040c1e0350000030100c00400c41e201030320701d4107044562441d0302a040440000c1400000c8004d489800920144800507600e903204503c507501c0100c1c1c00315404106840103000b600d200700b0f140d5503980d0329402d1035901292600d10440b5402c406030060300740d143c9800c08002a0034958001c00b000340d1205885403c503140b560300b001e1740350109401814032a122640241d02c3c20f14500700540050440603000c00c1c21800d10011010142065000540b1400e0809002c10131014455507602c00b160949404000c599080c110300966aa10117410708082003075141900022400c29003d40c010328103030780c0003402540032070310000d4196180c03000b0240c000e0b0050703082c60011400c08501c40b03001d5001141c202c5641e0a445000070000c064070104910041341c20200840c007020154890310034031216444580042e81d52207a4001511441043c1000040e050356401504003902c0d0010780322103000200741c904050300c42342d6039495a0000301c6508001015518100300c8600101344007405005281d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 888877670 1250 888876420 888876427
    0x19050406060c20060d0c12051e011701110a0206060f0406080c01081003170d151214150c090103110a0e19030c0b03090c0109080d03020a14040303030504051002 70
    0xc5520383d0f8107004510320f140001075684821640c0d030b1441d0480741c00b109804420004001c0c0018000c03c6d040365800c107404014501000715030380100340501c02c130858480291912071603003029180c042c0200381e000c140d4910341d01d542003405e5069021000d42110a43c5600038407151806404105164810004407401903141c58024040500042080721040d4003e00302450161100951a080240254006026060b07000503625070f6081400c002d140f405d544400a120714954038060020b40d6507540b09040d400501d01114000041c551000e02a1440c245010384060710708000e42080c40e0b0800316180013802e840000e000356207603054481d00d2945545004098180f22040c90701074152126001000e100754180640c2c0c2032020141c0d0600303c0a141d0010980030801e0380c90a5141c06500107a40c0a030706030040040d007107800e520035600e52084400140c0100100400340d0740c00d8009501164038242084101c0c03107800181c80d04c0da40280011031082d039000551b450241091801c0c40c21041c0c00e540882d0041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 888878920 1250 888877670 888877673
    0x30a0b010e090c1806120a05070f021207030c03030b0904060506040c05030402030c300a02041a010807200601030b091c0804170415030b1c0c0e1519050406060c 70
    0x100a507484c40d0700c060845401c030303500c2c0b90005e5554003c0c00d0050400740320003001c0001b141c00b03d40001c0d018801035203900c0c1c0c0c001d1040c101070384c582251648104a1102c02e1042c100468403c03040119103600a09000820702030320b40100d505400100c0f0150344c0591180113100703c0303041a109406090303c944c90b08505509140d0b00213500c0c0c001805002c1d200d00d4528107125290344498200904131500104803499016019240d15240e0b64500780692240f0b240c007001000181c050001f00030003840503510040c40f6954110283e840c540c0352031140b407160166030320744401e850040244901940c01500092143d03d070456180d490b14212100555031340e130004006c5036003503410000302178100d0791015965000050001080e481c81c003039580802c0c1c1c0c1c081041c0030860800d806070b000f88000b0720160345400840c00031842c40301d0a4182f42d10024440c0ba0154805c0021446200300560000e1510720501001d503601800901c0301b1151200812100c0045c0301c0420042c0780501c5258018400e038145000101c900c3e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 888880170 1250 888878920 888878941
    0xa110610080c040b012007030215031501031d010903020c13020c060f070c0b010b130905010f03080d1803210504020114070f050d050c10090f032102030a0b010e09 71
    0x8110b0002d0286444030380c001044c1c1c0c0112040b401c2c65050314000001020560180342d6240000d120507406010b602e03805a9001c00c82074101d0380f191040d10b42124580d8880401107005101c6140b90821700c03202210900c2c81041c0038025600a103020303a0082c0030301c2d51001c1c104281c024034a994541700c24410001c032162500086802640405118004845039450800070344400c414bd10008103d46e08070740020034800e0030301c4082d0400840400c64a1080754488000c1d03800c955080c06000c6550164560400c0007941c5e42c0004c00c1640000500414020f071584040c14201128000031008229148400c6003240b804d90000324a0074032071481801182425000a40302880d0100c4140c24800c00040103001d0010910105000e10b03801401c6030768210810700d0041c9a07030444a00e0088601400c80d8140303501015000d00c8400715041118007003801042d07a412349180c0c842c5140d0001260000f01d01c0070350b0340003078805584101141580400e101c03081c0c00004000003d503035103d80c480c005400a000c1c580a2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 888881420 1250 888880170 888880183
    0x309030c010f090e040c080d0e1c060921020f010902150903210a030c1805101b05030904050906042a0905090c1908030a0f0909020a11061008 62
    0xa08000140b64504141200d03542c502c2e801c20041d07401080c0500003080014401141114003039000c0d60360710f074a01d03801254909210300d54103901c40b20444200c0200c0c84962044543d40313110303210010b03000690b66180c104550000030309950925074461268003940c1c040c00401b50b10480f0300020008000e0035070005101e2600300580303441c4888040b0740c400d09501c04111210548107841c20a412651041e4890606580900c0841c0002410301d440e458103e405508402141c03aa644629500103040070b003401b8015212400100422800c1111012041200880881d046019070013850383e40b10f0319030500c000e0350310140001c2c90952088017003002041020500d80f9000455030000c10300d10f0784460702c800d112201a00300c202d01601d0003052000d0010005070300d060101040e0b5000003050340c0110042c0d00300600d40f00d48100c0750401c121030344c40a0300ca080c942040b004641015100c1c0c980b1050200100c2e00001c01002c089586840304406820041044603032011101c3c460f0702c11142040b40d90760700c885 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 888882670 1250 888881420 888881443
    0xd0503070e0621101536080723100e06042c070e0904030509030a080c0109050c040516050f04030b091606020303060f0121020426030903 60
    0x801c05008050a0740c8010450b080902c3c0c00000c0d80030070240c040b100c02600015550301240300e80c20030002400f004031a004c0c0441c01002c1e1030303400341c01c84003050605201d00500c80b480303401c00554040380710200035284604050301c1e406008124450814402e4845421a1400fa583d4251343c094a005541c0e00e1840b41c2c2416400351074011829401c1c00b001c40c0d01e602a90b0070442442c600c076001c01c404d88001c008107040c2c00c0c80103110050162144101950580e0213840880d401203550300019001c0f070b004200070951000c000e000c0b14062007140d01c2c0d40d04250002010780c011a51111542c41c01e000017002402d5240700c04490030015414001440c0703505200814050081c04004190401d440021070103480c0150342004c21035007986030010f5116250b035003c54655210000c00c503000700d8603034400001e1b039218442c007400481403803504100540b82181c00d9507070000780c0c08040c82c03510040314043c000341c8028802d40c600c3d85081104501e003600c18682d44031421909610500c20701e01140d80c0090b8070f00502 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 888883920 1250 888882670 888882677
    0x29010302011803061b090e0603060f040c08030f091306050319080408030a03021b01020313110d150b010e090f04060b010c080f0307090b0c0c131404230d050307 70
    0x8841034845902d9070005a8405440f0034500090307800b401c070080700741060074400c40d941c10503940c0c0c0380c07800f403144110140d4002c0d8065004200148100c51442e418580040c043c0d00b8031503038155070b900914a95031004100c1140303504040303401610340c200041070748001c040000c0305102e01401e0a0200742c1d01c0d08000300c0150104809013100b418407400c88115805085908292940c80c11900e40280195100303080210407070708102010114243e06209330f901039042c1914051041140e40c440ca54501d04030020140d02003031001050000901140c4200c0042c1103113030740801d00101c0e00c4000361083d00c1807940a0f0142c00f000c030411001d00b400c0e21980747d225602420002d00700c1118070040710703c898602d00003090008000b442c820400da40307001a502c10341d01aa0780b04026900c54448112a010f07101414819a1140307001303680ca450010842101941000c0001522601148040e000300006481c2502c03502044800e80c0284048241e0300c0f55025035050042031000a00f283c0140307070b8030006181d607041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 888885170 1250 888883920 888883937
    0x102030f04061e1503051608120d020d0c08060a06020a031b1e0308150a0b0d0e030918010806060d0b040308040305040f15270506090d080a05072901030201 68
    0xc428a0301ea180700000d06a40042024045034040600350b40c1031070109a44170320518515410603007041c0601f200fa58131000c003030102c070200c0b12804903264111881011100d0b40074041c50411038024480c040b1801d51079501c10070542403040074000f0407032264100030115001200120007290304254402c00e1020303d5001e40e884003405007401d0301c00c162000030380d42c8100480400c6809159001c40b9242c000d01205500342c208144035001c00c045105103219400d100d290034003407030084001603400314a1166868043d2840c1138100c800245491344821055500c4e140c10100500038540e0030071946a000d03100340c0d03044d4030b10f01507500e031080d0000340200300604104100e00010304051081c010b80300180050881846015210f004000703158150540f00800621204d610040c480700c2c2980c440c80c240e00c2e81c254120014100814010307194070010000f83c10082403114440014a400005c00d81d4801550f14a40c44801070301d05803e150500c0d03104400e007120000103080710250701444041c1102c2d4242880b212 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 888886420 1250 888885170 888885191
    0x6030a0e06180c01030635010f0218040204030c120809030d1706090126010b030f01020405030d03090c050f01032a110114270a0318080102030f0406 65
    0x303403403404194656402071a05000202c0500601660900c64101c1a1086840c0ca10b00440031100079215040c03801d03031040b00c01180b11119402038950080b65105005000355042003030b6081d00c501507041c200071070340054548054588172040c2c848151044a040d440d043c13440c0c17a60765406602e03011300700200c2c0710000c04034208a9010116628400c0103429142400c5117410003900c462001500300c51041c1031000041c80d00d00d06070030540d040c0d540341080c1c50403018007241c040303004070700f407456411003596035100741a180d5030108401100d102444001590f160300f81403d150400d20503441c080d0504d8205410351000404802c0c408055801c140c2d0b44840b10003034180101c02034644148101407004010510168000e14402c0f03c40141000351124001c16045003241401c848118404500264011010850099603080480e907400904c041d250b80c2d44001000340c50805018401c100d022644060050000c3e400000400b401400100004c50641c54074180903444101c000f04010041039840d4500c09 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 888887670 1250 888886420 888886441
    0x8012307031e1103182d12070b0108072304180807110a060c0305031305030c030c030a090906030f2a0611010506042007031e080406140606090603 64
    0x12002142c0300414012120b2450510340643d005940000700d52401d0020442403081c0001c1401703446032055200001c2e001401e440c175034460985181e00c600d038042d07080505040407095016041c4a0f0088441d40341d80e501d488643d510f03058495010410a6105094a8a8100c0180c070f86007050b0302c060b10045154641105440d00d5003024880003022110041207040500442540c003441422082d520000e01c10388401069480c0301d1409030040001d20100006246840003202c00e0100c0e0b485181100c0c20314007480191811074000c1045044554030108081d00d13100d500c4401071005207088074042060b18156214080c81d4106010058004444026004c08810b48441a0005130980c507038214501a240c03070303000b03001c07420300c038a1030701150300f40303004620180b07080c1c4180c0c2c540d0040400c2901810b421260003084640140c5001d074148843c8101c0001a00308040d4009418403566a030402d1310b00c0c4c02d14005044031011a00340d0000245030080014503203030901140e1071400304469141c2c4075510354070f051 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 888888920 1250 888887670 888887711
    0x180611040b0307020c0a05010320090a0909032c130c09050415090b09060d0201081824160e0f0301020412030c15020a0c0b18060f010801230703 63
    0x800c24a00c00003c001c44158041007640c403c40c002c960002200d55100c004505903111060908500c010395044e6104140c85c81f402045200030107085041035544c0d4070341040c102c803442030042d004241c1201f00b55004081c2c9d0000b103c0e0480450700e09580b5250301d80c0200300c01d030303403040301c2242e442d5a560039049103d400342491200400b4014010f01102c110104800c0301e2182d240314030b0700c009081c001c00921510300358001510519028110500707403141d6400460742400702030101e400003d0f2040410030750703010900c002044d1743c11800c0098002d840000c0051400040105808620407500302d01e085041d9001080c1080581d044400f17682e040c0d05c400000340280308030b0340080002e0a250803080e0805401000103070cc0580612a07080805081130b4011041e80300300d0b0040800114407070000710000d4a601a4550094039112022001c14400b1200524112058030a125900c03542801080540805d01400080c00c0c41e040c11200e1401400030300c40c0c41c03000042e0114003816100c495410101282d56843c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 888890170 1250 888888920 888888929
    0x306022a151f030302030d060e01050f060304030c0803040804030326040b0c1b010c0806030f0a060911090a0504060e0106050d290c0403050714060901030510082506020118061104 78
    0xd80036800c0d904d140c065626403114001c1d0203910705000e0001003140c1022641030482d00c02a00b20b49603400402c040002c0e540c4001c00031011700003900f61880100703101102441c4217a11a40c0003540d40c0b400d508001d4005400310000c403054004020621120040c00c80c90a600305500c07070004003017a01d031800d03080fa440c0654404004800c181c1070100c129290150030803108541181c49944aa885090070304d9250f608650039000c00d90321900c07001e0b0020302e01341d00c01c02c0300d98064211548240c4d0000000780350030401b0744e4001c0c0010b4442d8180320074010345103e0304460282e08002040184e00d49800328441c807481c0280588003c1c00180440011034006d40f124283e00d8200d040114079207031548808031720b500640803d48852180c1130b000b241d80c00c6654002d003502080181420300304441383d4011009000000c12180c0d107941c14540000f41c001c400c12503200414074281d8100c1110b014078141a80e0b00c2c040e07901181c2160304000201003d001080c80011096400000205818400c0c01c08050343e072156074403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 888891420 1250 888890170 888890221
    0x81c170c0c0123060102160b09030a0204020a03020a02101517120c1b09070815031c0302270f0d0c03020907091e061e0e0405010306022a15 61
    0x207414800d003c80b41c02c1c01c5000380c00010900440c0c50b0072004980d164006d65041d800d1070140f0200f0301000000d0005440e48407402011221b10b401c059001c14207030303005040c0b507401081e00820099011a01841440744026413407004010b4601d1b0042c000c0303a50740389803040045000c404400390200c1070041c0582d800460580040340d42c0c80000358800c5503511048181c0d41c9075006000400065441d000d510300d401006a60fa6914541d21903c0c0b1071001c0d524064559136040c4104480120007a00c001c0e1104030009054034016119164039581400042014400020702c030000320040710555507180b07032b42d807940c0342c2036030789411003200351400120b81e11154202030361180903e020010301c694811540015901640501008a4010140100c000c0140e00030540030842000844004160081b0b4071051199145003074101401c400c0b001c0f070b00300d403020703081aa52180c000403102d0004541549000042e5102407841b42d010034443c0321a40c880f4246048000f042c15110086469003000c3d09000d5103d011225 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 888892670 1250 888891420 888891431
    0x801050f28090b0c04080d1e0e0303090901080106090e01020712030207031101050f0109240501050306180c1801050a02070603090f021027050d060203100803070309081c170c0c01 78
    0x3410000d40c001b40b04900c40c9201d4181c5442c045403040840c0c0c0b0081c9400c0000c6484d5058104050f0b6003043c0480480c0c2e018401030140e50603070307a01c1546081c0203002c50000081d08074100680002691030801c40b0b880d10740e00410115002484900044448040382e14005846602d20b10702201d05034203113146c4007015800c000a000154080b00c542d11b048a00710582000508001e01a50152090302000302c1003048211208010030350141c802140e000320021300f1071a500d686c0995240c0203000c1900c005603c80c0c40031071020303501080000004055102407c1440c1003003e0140c0081d51800680110302c00c06489032a003c0030400a00c0c0e4030b4111990080c09299842c403054401483c000d1210200d50107a011209548920074043c022407040d1600644210300810858030340c0000396001900b005c140010840000420f01d4060018110b024070036542e029000340380c04071540c5090400020901031071218254110900d400c500002c1c40000c800540c06035640e21101c0305590343c040e04284c20455401c1c00f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 888893920 1250 888892670 888892681
    0xa050a0501050f010509010506071709060c0f240115031508060f01090203060d06050c04050a080a030306240c06150902210114090a0618060801050f28090b 68
    0x40d0006071250084442046041e85c4e14030030803003104000e110f5250055003c02480c00841c280301e400345043d000740b40c8031a10308949000480c170a40d10003d034100d01500880703500018410244443c100459000b045058081d0300c100314552501030610480c44c1060b24180c0041c81103020390410081221203541d0b2540250b80c601190341ca404c03045640c108038084920000c506001ea81c070a0328040c040150000a000d5400d82d6120020803003d0708480110005110001d41540c0e0050140c0191800e00e014111203500d525002d0156517903a08181842045075481c0c03144003101400c62050084180781c003c0c2d6260007820004020321040c4101003402e40203103008a0002207580081012030003000c08035544540002c0d80708018034007030248801242000950f00c0e100c3c90924400c80e0081d640d20000078400e682e03801e4034803000c2c03000c403c1e4440310307178403140200300c2000c1c00e00c07074944d000b181040c002080780340084903000c94501110ba40c88003000000390f01001c0c140c0c40d511200d2403903030002d400350490400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 888895170 1250 888893920 888893923
    0x3070309062316020f0d030509010219121202120a0b13090c14060412050105060a0e07080106180e0c090316031e08070f0b07031107020a030b07020a050a05 68
    0x241c018030020442c2801e055403402c900650041e1503507a1200c8007801d04044265000b0058000070060740e0103400f2560203502c03a51011403120003e072091f01c511b65550b1490001a0030004031010080c0c6d00d00c50201721101050709840800b600f00a0307854a5925a2400f080450003401180c0050540b51009010010040b036164005807290701c04480042d00346005110140c241c074406040103104542c03001c010400f882c4c1d0015040c03295800280500d08050302c800501c03134420040d110036180d5039190018004142840260b0f00003501c0c030311004055900e001c81c0045c000c6001803103200d0400100620969110703c000c0c01c1c440c00b81c44044442e1186040c0300b02d0300c0c45144c02501c4081c5c07180c09034210441c50711403600507200c1140c2d8408220381c00c4a0018642c002400710244040e241d10b0301c10000580014082e900c44140548034441c41401d0f4105040c0c02011102c50380c1c0600240c81d0308011410150703440712080012603502c4a026a40c950702c40310102e05080c9070041c001d0461055150360000c2180 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 888896420 1250 888895170 888895187
    0x4080313050604081f1112270c040c02012012010b0307050304030c051603030c0c0e060a0b070c0b0a0309060c030209012007150807020c031f050a0902120309041404021f090503030703 80
    0x883d02051800c20766125524108d0302c2541c80210382e036001540302c880c181030135080741203a00d480e400002500c03040d20441050808814a115809040016440d805820507540301c42c094032620313450300e06515222030007500501c000707000a400e02404400b0002041810800390310802c011015010700241e480c03030f020300640c0825404541c4008442d6003c5021400211914070404005140543d80c0f13140c04240b01c6140d1092000b6284480a8800415440c5540c00100f0320562240d03400030f0410b00c00d06109003218000300b00c4100700b5004200b14019a0780c0000545406100840f050304d41407960869146851090740c420030082c80340e880c42d61070190700825848d210309210780030303218409010701c10562205d6a00b001040542240700d0840780d201da86a01282d0b00c440c0920000441000a4000032040030341c00591001ea03500015416415041c0790060300004c003440e06d01c0e08118100740e40082c0c07000006c4006942c0e134100780d42500811a1240c110f86005110240c1a25507814807810014207001c07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 888897670 1250 888896420 888896431
    0x203130c1409360f1b010e1002060a020d140a0209030d0201090b0c0c0c03070f0609060c0b061002070b0304081b1c12020f04080313050604081f1112 65
    0x22000b50001d040742003a441e21a0440510000c00c0b0301c0c1010740446180540e0201400e0381d16131040b100d03100d02c042c008000c0300c6001c200041a0300e805540c2c42000504007041c04440f0fa001c1c80c00c0350810a01c640c0c00043d07582d009521400c0150b26100e41e40c503d8070051425030203214420207582c05000c1c040c2c0e0aa402040c44200035001d80e0070f00702d0110b03002e82c243c4d0746a0100a05121050f000212200d00141c003400c03008000d4001d440d1035110000009103130000b40d8010044500007400c04100391600561a50010107090031704103661007003030312050700e881c0c001003a050080d400c00101031159407082c0010000b4084141509403a4109800c14090f04c1d0840109640c0c080b803980d44d28030001000096030000c40c42e1034452100307003504591049451a1300d40407174061164083c029000c03803040c0d0f24050300180902000443d2202801100b0f050400296485039019120403c414440c9072004218007140a40341e000081c0300b10741014240c80202040103000c49002c0c8080741d00e0020603000c1ca84a801032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 888898920 1250 888897670 888897679
    0xb06040b030601030b010b07060b18060102010516080c07020d0c0311131a130b0a090e060106031b083301021c0c0f110a0b280f030203130c14 62
    0x354030805069880703000b0302028102e0502d460041080c00035807030051043c2071260781c0104111110b000030807079000c00c1d400c031002c401e042d0303404024455034241b0a1036840a5030b07155080c00340c0c80310310340a4420322010b0680442610002070351415500c9158059041c950300c1150403490540e07134244150a902407d1a007403082960404807200201036006620110702c9206801c0d03448200300b42040122029449120407081d00c1e08144a995659441c2807002428800f10200d41c900c190b010090820605030860014103142801c4c0e08107198009008050010031800d0481841d00c859001d100124030954074084901c0403480d600c1c0514107159100b1a50100a800f1504048401150300700c0144c600d801c444006246184c400c1c0110314135044200349a80115450301000141d40d0101d0400d10285d000069003100000c2c01488800740900d0141030118074804550203915201001000005062000d07001c02d0b4000c0701091030806110b148600855200c510007256940d40d0032940d1481e007199289038842c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 888900170 1250 888898920 888898931
    0xa0b04020324030a231b09012c0c090109081c0807110a0309140f1309020607120f020613020603010b09030c031e16050a050d0813120b062202250b0604 66
    0x18006c25078000070001000f07000442aa0030300b4022000d0112440c82640000c003a1f1144420740415180078500422051146a075106074110001d0400a00c40d0700100e40da80c000c1e00c548071003d004501071700ac0399040c1d280c910740a8a42203812a403140640542528074040c580c40171003015007003840f001c00c44500880c2421400800c400b0031000306080b5442c0c90304a00d0221010254003441d92014540602c000c00302c41c1440c2702901c80c00081d800f0845903802280ca020104152250100101e40d40300f5040c20700104401035550100b06940810700c11600300550114040c1e000d50b81c1070090310603100340079044071382d401d00c103543c00f000c003010b034005d0115a8020941c041080501008140003074580240c1180d004628000610403508215002502d1100081c002c1014a51280d40b401e801480400b0005c840c0311400d0903d10341190000c0c01d01449100d074102d25804021a1455221781401e00500c0140c07210644042c84446401c1c450303403104520410a01d400c00c00c0803010307281c0d002d410166800c111 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 888901420 1250 888900170 888900193
    0x2031201060f020d0f0c081305041d0c010509121515030a1e031b050a02031c0e120f07060513060306080a0602090103150e0a0b04020324030a23 63
    0x1c44148104407007005821244c520051390b0b0040fa26500a64428541040d0020060b01c402c4420b070800390b08107d8007040f40b001009030b0f2500d40503401c040c2603034056084420070382c10501ca41c0d400000c1c502c68144180851148403d0b0344082480340110006425501d40c1000c80b410001d070618119000e58052402500c0c03c103140c28002002d07010309500110520032011003001820000b200701c04200e0800900e0103481045d100440c0102034020b129130010100c002007481010b0404074007010b004800d80c03290b00003840d079961100700c80511690603105c620110203003140c1036003009015041400144030307074103000a2040e4000014041c1c42a0361100e42c1c1c1482c2c8408003182580c041d03210b16102548095039100210b40541d000302844441410002031a014070706d120b194801c025484002c250b2240b204100e403545a900038a4112141150110718501c2c0031a10181401211011140c40513050004200c803a20100709400620b90003818841d00d04408220341c2405401c10b480006250140303200800d03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 888902670 1250 888901420 888901427
    0xb120702060907030f1103030c0a060e0c0a0510030e010e030a02010612030f05250b0f07170c07051f0c120e0309011407201c0507090506030a120203120106 68
    0x9002e410840c0207440d00c1891602d17100c8021078540f105583c200c4a180d4a1406503170100010030b50000300401400810700282404021208691a602c9464124040c1134240f030356203172090800d880c8121000c1403d286040411002005c000c61f20301d002d503183c4a40142e164030b0000151440500560003030201c0c0b81c4880c60710495000407078000b00841e4030b10300e0000009001e0f1000c0c1c80b40c0b9581413801c5001b215240001c2018115605068a29000307200500c1150581c0c9090b050f4081d42d5810000300180c0c2c910300d0400a280010f05041140c1c81c0031481100300401030195850190000c8a401d624803c9031442c8001050003a00ea000800c05503d40c850107510a80258400440250051810031000500644512104444000e055501003007040005181580c58441660b035441052a00900301c030180b015282030701c0c1c2c20707184242100c602c0c5000940b00103a18001c0e51031100d40070460303403112004a0311303017168840c0080001c03503580d01031030919a000001d00005014103041980a0742d036a00c050b07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 888903920 1250 888902670 888902683
    0x9020a140a08120304030e1203030a06091803120b01021510290306040c0c0501090c06020c040b1c0204021903200a020d0e060f12011e081f0b040203010b120702 70
    0x1c0000303030f0180001000b1034042e58051400701c03805443c0855454946d4111070441c2c1c01142c00d1581305030740315001e01043d01c491040340d448818840c2c01c1e540e00f440b192005480c2412515284022640b51080342e88564805d1166a4002d17181103580e40180c106610028002c08040c0a00c00e021901c00d01e1904451002c60503803880b005500c048949540c940005210251081c0d144040521108080b0507000a809200309100c407401500c3e480d00d52410040003e0030702100407039040c030071401c20b107080100f95100300104c0700d400c2d02d402e50203a01c0300c501d20124020b400b9040001f800741c0c08501c011000c0c0d503010b811085c12a0320b440d42e02001103849444020b0103009202aa0005038030070344264982c240240c030300c10845080101964200f40c0b42c2480b03581540e0290280fa0407001041004001c00656115035220b5901320a140341e52240c207183c9a5a070700c0d16280308400038068070011030890080d00382c1c8001540c41010b0070a565035a1229403842440c6c2c440e02040440d03000c2c960010f804c135440854071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 888905170 1250 888903920 888903943
    0x9030c010306051e01030204170312011703250c0303080a11121504090b070e0a05060a140d0e1009020117061003020d020904061706071d011209020a140a08 68
    0x40300590004421400b10400d80b00100d00d046c10750801c4003041c0320400f00c103400445024500210b584400d049084141d15106078040c0f02003020320195a8170418020064611a000c00307806030000200ca01c04d007c0c2894020b41c40a4240900358002005065010100e01d1013441c00100c24004d42c1059070714515907102d8060359516101105005c5910168200c2c090701206c4001040441e00b80465150301200c24803c0e1105c0e8086521451040c400341006040c0c6001010b0444005041561829010300104081040402240400201d06007891f0040d0300074900340318503c0440c4c07405125819072100808001005070b000c50007049050700da030010085074a214800140100104c1103400200f540030350000741000205d145c0a1040c0711803612a8071580c8001c04001d80402d4a4051841120f400c2c420054608030420070090200c1c14007051a00701104261b41c02e03e000d4000c41001c420240041201c10402980001200c0000440303101c1000c6114038800115071304680c0660300c1400c20b6030b40c403101d1380 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 888906420 1250 888905170 888905179
    0xe0709050f030313081b0d020328060e1506030d0f0e060f070c050907020604110126160f05120105040b04020702090412081008060423030c0309030c01030605 69
    0x80600803410914440700d903070300014080343d050601500220404c0f842c0e0760000c0440c2e920505030810b0075440803c800780b036000180d542c6000801c1540110341c5541c01d000c510302d0b0015200720101c0c001d4031740400d00c0f102580c014804121071490b00c54110780b5804042c0c484400329040c030000c81c000749000f0690692131201a00c0f0300c01030f04001c00f070590b8020aa03140d4954003a81c01d0114402c0780b0700c410001c215091140712080c0600e82041300b0016111405403031a01194031800030000020100c803001c1c03c41c00c0c400d080140034190741c5501d80212108880f2500d010100a20501c156840043d0100190b1810750b10b901c0c0c0d0040000004942c00e014050405d20100d6036640100b09600340766021000c0d50301c0c050000b41c0303800766940108017000360580b421a05050f0140c0b240040c11b601102954101724004031000d00b56141084403555104064009420594012100920750380005103000e001441d1a040d01d407500101c000305078481e04124002802402183d034005600d40c400d100d10380644038000d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 888907670 1250 888906420 888906437
    0x3010509061f030f060f031109070c020a031509080a0f09230f0402040b130e0a02091005160b090a0302120a020319030e0a0b0103021c03021b0d0821010e07 68
    0x81c102e029200da021314220141d41d6045c0401e14058201228000c4c500540040301c400d802d4109001044a00921001c10010003219000042c1d88035100703c4c0480f50030046403502800d1001034180140f840a40c020220000020507505644d00107804100300c52241d00c461005070f5640350524441e0407021400d0800d0038440404101c00d1401540c0480184806030005080c0364072440d012500d60700c080c00035416103140c03100c20040982e98100c183d611070300c0c0010560400f00280c1c082a0415509020541070240203d4181c1158101c1103d03e80f819410480b05052820140a8161244103885040d00140541400c00821903004c2e8200e601d800d1845d030040d880e02554002034403000038048441400c2540b1580300e145610401c201c00401c1c4da006101201c50b951451040220078076051003a513841a1111110a002c05e80129440c22014800c49082016001680010311104421074006010745000300340360750948040c0f0311400074809a02c60960745c41e44ca80004a00401d82110541700250403103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 888908920 1250 888907670 888907729
    0x3031d210d0509032208070b03040206192703052503060606030506130903020a110d05060f1f0b09060d1d0a050c1009090203070903080f0301050906 65
    0x1a034214003120505282000d1030070490905460059401611562000c81e1500b8200398881c003203402e4695a1190150481ca4201d803d51a00068403550740c0c981404070010b801d6481d407030100d40e55045450b007210390000c90900e000e001a42d10140810010b0b00608108000c0180c600405040d25000001855003201c1d80040405c031480c10070f8502201c203800c060000c001130040c040c98003d04401e850108141c9068000d00c020021555120a82141403050907400b09401050943c88950012041c81c059038181001c2040758084140003429441074204010070201740c201e919001c1d40000c07005001c1c0440d10303600c2041c0710309540542009100c0810400f4503c1c03070300c007008049516404801254110340044c140c81c8103e030550305450a0b8001c50000b6080083c248000048c800b811600c00605803690007005216141601a1a02d80c4d58000040b40105005620355002103a11801050791107130304564800c4140c000b849240c4c018a0644003081003031030700c00824410340010400305100c14846 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 888910170 1250 888908920 888908953
    0x519090203060f0a03060b0f04050106170403050c0307030e19150309020f0907050a17151c050a080d060815040305031e07030c0e030307020604030b151c03031d 70
    0x5003100b0f42c0300022002c01412030f00c0d0414054002d40c024072000a4080305d21003400301aa00e428004c030710540c0750000501905801c40140700300410180d0401e5209e543c2c614003640c0c1ca1140c0000d0030040c1c07001085602c02c260b44100c00c1c101120081d251039044c45203000202054008500603c000000c011981540192180c1c2c04401250300043c03046d0805003071400880c610280940d15030000800014180801907040030104c01c0e9213001441c0c1d42c0307191074090300008101c01d0451b4058400c1455200c5103242e4400e49496441c0550003108ad941070f41070314a400724052b80300d0014000e8060406000040f4140042822400101c601070000c19554407564200d420758002460403907103010198400030810f003221940c4e8030491880d1000036580e40d19107406070400700350044161190340700b040102e005898200964080300c0d44880c010007540c603080c81c1030080c0c01c500006135800268039507000e070309917041585c074801c80c81c004d4a0030404400c90341e03441c600400c0d000007142100e81c013038460074000051 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 888911420 1250 888910170 888910177
    0x1c06080708061603060f03030f0f02070e130c0801110310060c020102060112140601090221090a060c050d0504060f0b010813080d0204210204060e100603021806070c030303050105190902 81
    0x11440c4c0050945d444190400c8004501e030000e80000c0ca030b400000c102a50059898205081e042c001403088510704150070b0600c0f48018140c2c0200c1050601d19000c00003000781150181105000070702100321044c140a040d074008480c102c081e402110360024030140101504101aa0180e0150480d60300300030740c940419122040407680444800c142c039882c440d050100602038001200090784c1c0f40c044888102580034464000707072031452040c05001c601d1a000442c0261203a202c540030460144207681076806014203103001a009060008100c1001807691241488425104080200000c4c2c0c0700119140e050844100e024100c90302482d201044141000d02682c1d60b5901001d0714094807800030600c1c20344441d02c25011205042003a80451615000701401b824030401003100c00c0c40d000082a20031102440b4a10a05900040e500403581302c6414000038000060880d1307a64070014505026050342510080d030000e0f20f414004652072425400c03151050002000011015040001800c001c1d070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 888912670 1250 888911420 888911461
    0x30606061323060a02060402090c0a0215090f1e0d030b010c020111030f070f0b0106081314010b0d0b070f0302130509092107110f01082206021c0608070806 68
    0x200c041c1005082d41c2c0d89800500030002e8a60152940d13052620600c080d812014241201c0c0a50500c00c140d140b03540003030400c10758008079507640c48503203803c03400c681841541500d268450107003981d24014844400283c010f410380007000c4440b0049400713802c07011516111021782c0054208a0b100d0007540c85010b184420b0703101101542c0c40d2a441050010483d03024400460308007401481001c24000381031025401404c007410046800d1404005802d40500310120003803c5007442980c4c0010600258409840040c001c0c2118101b60101d00305884a076800300c40742800940744d9500d00f40c0c07042c0304c0d000340d4035021021040c200d030041c1003008000100f4401480c8000314403450f4050070001d110580c01180b4808a2841d103652035070103040a43e4038101d00c40e00b41b4000c006444011903141d900400450303202c000110ba1103603240c0b0010750104104017880002d014640041482c1d50302061128103d40340910542c030420030740d82e031195426102c070054030485001d42c101400140c20320040041400303088 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 888913920 1250 888912670 888912719
    0xb0c190912030e1f110f01231302060a11010c1e030c03020f1812030412022106040b01080708061b1b120706060e09120a02101404020306060613 63
    0x1000e04004904c0b0120030607103070ba0009007118803001744100051100b2071501c5000c0b402408036101140f21000302e0305141c1c1e0710254900703a482c00215580a9a28000e03200c0364010511a1b90b0342d07202800406609181080d00d0840d4030300200b96041c01c2c016034a40300030b2150050b4140c1e00e01624003003070b401030241d8640302060540070000710341814443c400820419805080212506042006000f00c2c00d6101403220780c0c03940100310a000340390065403440e00b00e560403241c1d840c05c8016000e420416104d40300c140d4185209450a020400c01c42d03c4c0510f06a6181c08100d50b030055595840301d5607900b0985022580c0703802d007004090300700441001030854040a0398100d1642d64605030052402d18070321222450350001045010811450b402404d0040410031301c2c2540d51304103000d4094442c0d00e51210b4811680340002ca03420141d0003481010f0024a41d032000300410303803602801c54030301907003124224868000c0340c000030154034141d0155007902000485030700140c0c2c00c0c545c2125903001c0b40f4400e0301e010b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 888915170 1250 888913920 888913939
    0x1318270c050f181812041815120321060e1f0e040b0708010504020c0d120b2709030705061503030d05041101020c0609060d0f0204030b0c190912030e 65
    0x744000b032031a56001d0a9440344c05007480341c604018604256100c0d212058a03c0f0800003000401403481071240040200e15001551812038210340c0485041b507401007000c800915400401d00d9007065901d40e419480129030701d5504501d00b0143c046910a000c4d4a00d248818000706481e84c0f400d08040c41c40c01d80304c0304810711403501c2d800c80c0381d00d100742110210b03545c00d544408c0021055003d06020700416081d50158107000c4055981038507a81030b00b0440080004100c01c111030500ca030303040a005a82d0150140c0a00450500060908014503030b10005806030000400c07040c000c00412600110b4100c80038100a031a0551116091b54420700c589038144000d002400113070000e845154040c91003540c1d28807070701e46180000fa0601000d4000c5d5846018140302c50380d01500c41200302c1300201c003914000185c100c050305002d0000c0c00341d40c1020702a82151020444182050001800d80c00d5100c482825018012001140c00500034051403226908038100000040d0040190b045030b42e01c0200f04220 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 888916420 1250 888915170 888915199
    0x60903060112050f0601050904031809050109020d24180603120509030c090708150a03060e010501051311091c062a020307080f1318270c050f 62
    0x94540c007a0040c03403515441c4011101080701c1041840d01440100340902059898440060760b06640100b0180600080b07d030000b866071551107040c806000c54020421195840304848002504900b0344d021815240100c0c282c641a020080215151070013045000c54508204e58480c14041c0340030600300c41601c0d03020200020b0301900124100c215a60742c3c2503120403c14040601e012004e1035040d00800c0010103000020780d0009000343d1004400d41120309000904000c0b6601440390313800038040c1860408524240c04040d0822412100e045406481b41140a4550004c80d14911b01010445608102d80c40040c104800c480c03441c00084028900136080d162214400d94001c125507a10a006100000c0c01d010201081d94803002c070144000d608180c5c041ea9020104c1c8a01c60b5a043e07d900c020a214071344060508258000d0305d200c19090300b440b9601c8039288060401c5514601c222a9010110310122650002c00d8044541201e45251a94541000d001414280d04109a000305586c0021079 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 888917670 1250 888916420 888916423
    0xd050d02070e060d42050f07120b010e120726030d0504032f0601060507020a030b09161e060f020a030e0f0613030203060c03010f030308070903060626010623060903 72
    0xc00403180885640c54a010170f4481c0c0122407009100e803400300080d2041c800300c96401b007114140000c0074200040d04d112540016100b9000780c0844a51005c1114090780308500d010507090100d43c2d4012400d40c0703143d8840b4070402c20b4840142144903e600511a015401495400039070b040340c0282803100c0c10000c904001c3c0d07500f103070119244181d1191039030603500c000e20400481e4010111880c0c001e041c6007a40d0b000a100820620000c0d00c43d41c10038021a5048030103004c0c000140c0c6071034426103080c0c1e07600c601c20102c04181c1012040e0041d45084005501401840007807a07085031540500440c41542d074040d10358030100300b50180c01405400012480380c403550000c11800050320840d0961514520405181c450000d0800704120b03020700041010800c030040351015079034141070040040c0d0343d8a4007100c1c1c0104070303440a80480e0034650300041c5c2445c8140554442c044401030365074100c04900034a400d85040344203242000c0e8100100303258809201004000700c40004101903c0d0400710400039 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 888918920 1250 888917670 888917753
    0x70f15020309010b0a0503011a060f0f1207030605060307080f07030b03030f221d0c07060f0b09130b1b0c060a1514060a1209020d050d02070e060d 64
    0x40b50380d91126084840c4c03410441c2da90040004070000e0042410281150a9018242c154940210f401040e040f40e0030454205803102810800e00c3d0036256016900703c1d0a05c0c80040e90860082450030f0000b140500702242101d201d500d03e6151002daa40320b080c80c50000c140002c090310101a50360f040d01241d9070341400240810225029901d8548981440c0700c481d942d00e180701c01100c5002280e040081c43c204850102c603c0c498284844440c1d0b41c0d81c00c1002661045050040c48589841d04003411b07080c1079408441001c0099980701a282c0d903049000f01002d4400c14080c000c401510000703114645148890342d810040f03c514542445460301040e441d207801510244d240540790300c00540300c2c400207078064000b03103c001c40341601c4041c0140401c00a1052079240070410a0040041365071000a8001d03012007603000e019181c4484940c14540c0d00c4003202d002c4200140a80e242c0000d205010808083c0103070b0f0000c01c01c0c2c41841d102d64403d0350541400c1a00d40c540c81480e14851811040c02090 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 888920170 1250 888918920 888918931
    0x90702011805160803211915140603191e021201090510030b0417040815010501080604090b010e090708100e0706031e0b03010b2707080c070f150203 65
    0x140454083c01e0040c8818070090b4000e00801d40c024040d02041c1d10501160654844c800f1141480a4640030424041a42e4001c1c0f8440e5460030309240340503070344000802004980101c12001211038201040220901c015100150f0340925003022401c1c01c5200e611082042d00303900107680600d113004070003030160b07004491880204042500108141b20b041d0087c9544801400d9003403c80d035007150384003041800081d00142555081e00a155900c03862507048401401600301150040c41d0700f40740c00d5600300030034042c250001c3da5240100b00703d030400b4001c0a075040d6103c5915400c51b802c0291098884038010050b8619206038500041da032202844014000d820403080481c60704a8400c01c40c4c9001042d901680030940b40c641084092821040180000b5401c000007040503e00c40c00024090407422142039071142075036154130000614103012801107540140840d40310368032004282d90744081280d2a82410307004201d10b10000d0114242d16078114410142c504140c0d00c200c01754001c03038008035038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 888921420 1250 888920170 888920173
    0x120339060510362a0311160303051e07020d081e0609040c050402031302010905031b063402030f0d0e041109100c1505060d02090702011805 61
    0x42c440c8024000c0e00d008060441010604184000c00390900c0e00541500d802c814000030340060240a65070a400094103580d80884d283d9800b04c041c1a042c0c40314025180c4003010918105942c0c0400c0c0300b040c1669411079601c8101c00001046480035000781500400c814501580c14100b0440140840180c500a81c10340d40140003440f1107c0b00a00080b4010306806004006910091404a44405860340c000415115070001e6201ca291140d030745945504281d41c014000300421444c210041c1c008100b10317001341c0c0c4140c07040b5038801c18183c5a00059002c846022005140d024850810a0003000402d00c46401c90100c89404245140500a0740500c2200100900289029881c0c10440100e041c1d10360406429018640740000c3c1c1f0340f98080300010b02403520f540d40000b401a420f02900d040260207000c040002d1400140113120841d0703410100d44140036042440d0903d00d240c40740c903100c3c000151070816100f6060b0208a59108001d044400315900c4d41e90004e02c00c80102010045140f2440 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 888922670 1250 888921420 888921431
    0x40203180d02011103060f13091115040e06040b0a090501031110031505010f1808160b031603150302130515010201090201080612011d0f010612033906 66
    0x154918100026484040704580c100014400790f500c0b00c10880c4d400c058121000070500711750f4004035044d600540d5481c04414504002c000600285c0709035203480007400c945050818940707000e4007820380280e000d5402e68054040024005003015803048141a0f801040c0204560795506044255074098104903990030343d611802d501420303d0050f559044180e030906001c580c92000700f18162041a1145604001c3d8030352200f00740500401ea101103011044455140782030f210540c05235544900e004100751590030142c0001c07490030002c140c07801100030b0101020b81d0110190308030060a685200b1600c0140c1c14080040183d0320401e0b030170710345800904042001c0c030f014a4092010201a6112070541e410403d4000043c1e1f801040d003070b401a000c0b81e031032507482024041d11380102021800c030503020041400b81020b0f00b80003d48040e4540741040248241038a8410781240003004800040c00310756140350098203440400d140220b8809003882d0948900050003040441942c21030040d103a00d960794 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 888923920 1250 888922670 888922711
    0x103140c0a030809180c16020112021b15010e070c1a130201180605041205010603060c080109050c1932040e0f22031b200909120a02010b040203 63
    0x2812024010305c6107810080d2903190a610303050161142e1410200c0d02c00d1051000421a0300643c0c0d0070f00404500601103480b81c0402d200740c4400e00c0005031941503445981030080c41001d203100194147c0d030300020410101d8545900590b0701c03070805101218220600064241500c1c1513402c207500c1840443c22382c50149005000150000191100000700c220400d48180407040d0440111400c540e0400617100800d40130b802c1940c0140040c0d00010225420001c1072071441d6808090a0f068130102c010400582d1038849a241452040b20741189000c240881042c0516020b0101c04014981d560440f040000ca1289540e102c0d41c81480c0015680300702080900001002d01001c51b40050b0030a01403d060030700004034510f40c80d0074902020395064a950343d40416126202500c408400742c84110702112003841d103a1110075240400c3c40f01d01c1580720344a021860a00e8150b400b45001e000508444040703043e52401703651100480c28155900d500c10f5041e661036600c001c501c2100726001401503000701 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 888925170 1250 888923920 888923929
    0x30c030109180c060c0201030603080a09180905151e1801060f0e040f1a0f04060c02012a0207050a030c06140708180a090212041e0302060103140c0a030809 68
    0x941000e8480e03212030b4180d2001404180c08041035410a081601186100b440100c016040c2a00010003910011940400c42c64002c030120080e51000e40300c161031400102c81d568112072150384c010b85958080e000110150701f00f05900c070b0300482501d10414a1003c1340d95103003449042079600c841c5280c9004818141e480080c030030480500000e8000c9201d15181203a41c06c01050043e202822014849001c001004120178080350118001040050680b89c130744241114210100c0c0c042d00c03036604188896002c544188a9400741040310403642d405088240284481d0442209500c030a40c898404003003125640c00d000200103510907c031260100f41488002003a600c40a031090071150401c1c0070b4140001c540c0000c0da00d82041154001105089100000c0c0200503154804400c003440000e43c1c0c0141001c08000c0303031003507005110756900849003446220f1801522403000d00140c000350010320014040202009000d091750040b02c0d0103404000000d24519215030003115039800c00030303000c10141007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 888926420 1250 888925170 888925181
    0xe100608061c0c180c140a051b01050604061706150102010f060b09040c030605060409020a030204030803131a15060c0109050316030806060a05090108041a01080d090905040309051c08030c030109 85
    0x40b8040c1802260300040c030160202101e0301400301c00540100b01d088060b032250007038819001c0b0100304002c14009c1c1900300d9000b080113558585c085c5003401004a03c540b00c3c0c0d00318234a000f48160003494141e40d4048404814015081c1070340c119503c0d81500d110180d020300809010f019048203082e6100115402c00003107500e0005000c0c141400e140301013100b552101c007610122012a0009a664210498110700a220b51f401c010012030004c8244000c0c2812001800c0d4681d1040e20706034001d001848044401074400c4922040320b451013504000d0fa0300b0b02c80c1c00f51003240401000070070510003580d030395411904000c6000c403071120340000e0070040c160702a181310303001002a5141464411070090007020ba1080d00b00d0039046c0014071002c2010403030034400d0b034003070200b2602072140030707585600c90a42c86d07060b80e000302030000e203070170101040c410b407544a0781c0d00030380e810784034802811302c1c20061110805810003141a9800804100400710b1003500046100721a0806065525030416034400c040700d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 888927670 1250 888926420 888926459
    0x117090102090319020f220203070e040b030a0b0c070609020a0b0a1205010e0103080703021c0e131104030f08190c020a0803090d1502040b070c030c0e100608061c0c 72
    0x1441d0001820150700c0d6031458112640c03081d80c201e01f099442100c45030000e0782170000240030754400070070001526400704d6917002e940c40490302880701c1501c070030400d41d0b580240400038000b0519000824412482c54000b001d006119403404600011160002011002c0960001076446000116111342590100001101d803851f070301e0130070140d4100026811b1207a01408018101d81c400101c18003414002c002450003040782c5034200036101c01c6140020210903054001c10701030810100c60107402241c40c0103881c580982c00400604152858507408542040144203860f200001c000502c0c0e61035001c0000722080542e52a180e4a2a4040c1b06121025100b41d02c10440c2d900b0038010084030b0766030a004e1003807280e0800c0314090328207031500c1c40320000d206980c061899207000007400f10400000d040140110f80c06500254103603541c40385203130f400c0f0340100d40403980720b10513010a2041e1070082300c82640145010f0030b0312000c6900c900f00c000401070340c20010350302a4940081000291a140600a9150b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 888928920 1250 888927670 888927703
    0x90902090108071802090105251205040b090d0f1709031207120f09180e010b041112041e0614010b0a05040e041109010b0a181d0601170901020903 64
    0xc500d802d0068030384801401c2d04c64005a00002c0140307040c0c0c03081081e220550140424003100c030704481e03005400411200c40880380c05200f101001480ad0080c0162411540d11145443c036100c292001c101c1b40c5000020100d9880049100c1e11011514110100849140240e0016a0b52000c40304051a0144071010010001c00030059000064803684010144115078244642c0d00c0e040408141c1d102c0c2416041618010340b0450302c20f0405050340c12811140540710003c001e58003824007400160385004018442d040c0d01003000d90071745040d41d8100c55010740a40d60810316981410020401c1c141c40c41030541e40c0a480d8003c1c1c0702040081070855004081e84200c4900d00050940c000c1d105010303d2091743c01146000c1d002a0511400c0f02411503d04802404800c856840e502c0e2070800f134002c281c660740080e84010019841301081040401507400c0c40c3c001103c0c8900780a1343c846628001040141000100000f01562240540006008079104400036844054840a0501e030520350b00850317028 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 888930170 1250 888928920 888928933
    0x7090e16080c0a1806150203120f010b120901140c09011d011d1203070302151005090f190603050304050139050f03031e1e0a05090c030601090902090108 67
    0x15030f5205003041d42224501040340c0c0681001100d050010b005d50780c8500d0070054941080c065003a03003c401841c0342d4450710b021500e1501e0b2050300200d460782c240181038025400300308404e48030100c900c44940c0130030400008504120300c40040b0581c92002c1c2c40d000302c04070f000b203012610380d84c0211161041910360910452285446c80008001142d88190f418210070410707011405038460a079003900c8011207004980c3c0d6290b00d4034000b96078080000c1100d622203222804121000844a8100c0460350010043ca1583d21412044151074001400b40c0b95000008111141c0c415804d005510056000c0c8000c3c5844074989400036091500c000d21141c0606038420b44024201a0103103400300300c1c40100c00f00c010903002498410f1522421017101030460bc00841049541c08008000b0f034025410003c1d111071f50748607420400790400502d0016001e21903058002a40b1720f01541c015940b10700040101c0d8481000c1c1800b00f03042020a8206440300303030b01c5460040542c2050607081d401070444600170001c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 888931420 1250 888930170 888930193
    0x190824010e040f06321807030b010c02031e0601080a03120507020304030c0f0f0914070c020105042c18030a180314010f0515010f05030907090e1608 65
    0x80c0126445502c215558600d04403006116442100a80340441d004001001c08002c158609402070203110600c202d002110303500f50401c0c520346865080c410b5000001c0d42c40760801900500151001e070b030b0400070303146d0600000d0f80e4104185496170741303851614070f00701c1d501d000801c0c01c1440503040301c0d040d035029158040020354800d010034070004d222240002d594481100c207d0551040344d00c0a01994640e00c004a03524040c7d003003010172035814140c0700c20850b54851842050305c0000c210042900d103c05c000540140c0a00707030012030f01c0c2c41450400e1810341c64060090111040d4007201401d03840d200c0a0075a01c1c4407081102e0340005198407101509607a4074072050341c2e03210340d100450801c01804d50030340301150400384d08001385030b1114001c1c01007081d10003064000c01c05000d06c6200c050038040070070303220800e0320062820010f0696407003201c2014880280c90315071018220143d203209180b000150326640348105c00d1419407d002900d049121048401e6901c5500d070845000c0b42c00a40d100b50 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 888932670 1250 888931420 888931427
    0x1101060806220c050405010f090b0306070914031005101706010b2b02160b1008070918080408010c090801050903190e030f0705040f0203060d08030c19082401 69
    0xc5040c418201c01c2c1400e54030500e001226043c1642c409604107007858001325148000c4840300d0709440070780501300300144c0b6450415030765140640d1280c0c00300340e11003018401030002c10300d50901c00c24040c040750800c41002078110100d50702142c01c00300c0034201e250180700d00500d03008440c1801c1186002441294100b64200405220f17114516101c03005101c4040c0210645d03c02041c458515a10215160f1554840e0040d01d407200000071100d8040140009441070800400203056651000050411a080c00076080c01848503800600a0214580094000a00e68801440649a840000700e9003010081c40900001400e401080c900e9040000708207551900105407a182e0320074410b65034032002c4148040d520340c189040c3d40c41c1c150181d408000c041030f0340003d001d011514142c40801c034030600740c0c6104080380019118954418002c442280105218501854200d4818100c0c0d501e068040101c001d1042e04500c04039000c03e80c0c90040003a524803a07280551b9449500c0c0344c56024981600000f03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 888933920 1250 888932670 888932701
    0xf0721121a1f1707050310090e0a02220e010f0506010c050a0201080c070210091e0305070e041a070806040b06030421050d021206030d030c0f030f090f031101060806 72
    0x201c80540481c40980c0ba254410700c91008030b4608140090030314184440c0080c07407076000f254516401040c03840c0010341d1031064410721008510810281055001650030801cad03501711151403606011a0844600710b40b002440f59600700c100c241c0c00000c402854183c0c50301915002040c3e039044c0040c4200c100013040c0045401c240c0c03183e09180490150791840c002000c036000e400303406500704103526031400505410550301001d458400881c41201d038103130104920030041038080203040e03801c490010021317007070041409600f1a00c81c02549254181c10100920303540011200040092220700900076181003038810104046825a00d140c03842c6065100c1000d41c070451500072802803620000702c41040d12036019104401c140a006660300d400711a1491600c2c04203a810750f2080c003900ca5030840c45402445203040354109510b4800d071504800c1015030007411080020f1200685030484200010310902c1002c038014403030344401f0150140340211a007107a1480e008600706a01c540240b041111031480030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 888935170 1250 888933920 888933949
    0x61e0406050601140d020909010f06020a06150503010e06070318121d060408010614090708010509040602160303060e0f01030503030c090a1a0703110705060f0721121a 73
    0x8101034490000484c3c4400148402d801c00c2800802c117102c0d0101aa00203003962502120210440c0e40c86501071f0781c181485226403809a40480d0340e0324002120342d04445922424580000c0315a550380c030220b42510099100302032030f03801c603400b0001003039014403c0d0344480d0aa040ca484440145a880b000c010315000032850600c03075228548034005420b03030a841907a110142c41281c4482da40c1a4440c081c091038041d4000900e041c1d001800642410720419108ac101582e4281c04c0da440c0ca000d004000300054004e0391400c1d020420a21150108816811b03014403e40d000a040307403401d03070842c45052000e854000071100080040000c42d50010540781c1050540303078000d58894a43c00001c560317000e41c2d400b1440190a0081c88888820000b02400c0c02500030384580b40c0303949852030550744400c0306000c0d107540400b0a0000e01554072402000d000c4042c81f0700d010301030342030044114404100c0510300321400030744410007001c0340c0d0140380115291100d0031031071140d50b030b07940400003401e41e00e586c240c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 888936420 1250 888935170 888935183
    0x6081e19032c04090b06131a19030c030b0f06030a02090604020a050409050109050103030314010e04150f1d07091104050d021c03020313471b061e04 65
    0x441e001c81050250302110302c070b0001c004000f0113000c0c3c64010403000c0102c92451288215141c040a4003105001c4c0c1103078101100c40d4043c0700d0300840c0402034505c00c140701c0d11210a0200c140800044c6820404c3c03405540102290502840c1a09000101080c01000d06000c1c0c0c00c08210b0744016101c2c3e401590b0400c800b1500541c4590480078102c60700d010700c0e4080d08405003840c1c0002481c09495008074166800790341d050010002c3c40800115500007882400b901c2c2488000040c0400c0d905c402d80222003000c403001094070b03201c000520f016134405141000140d00c13200c1c04400840002c000440c010a80280240500d001d00c10148080b03000782e01c5064000d4000c070b0000411552030342d80b98400c01001800020400d905428000e40d01e4009129400c0403092060700450301d19103045046c081802d40e4070100040c3c042a070070444000b007200c8200003607144617a0035195100c0c1c001000c0d08038900343e94240b0421012400d55a8688980600919070a2128148049820a0490400750700582206 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 888937670 1250 888936420 888936467
    0x302102102160209010501110303010e0c070f0302060f062413050604030317130b07180306060612050a05010602060403211815060b031906081e1903 65
    0x1104400414200360551000301c0c400100e0400002d8503210b00400140243c4026509030b0700d0710010345004104a8900c40d0a600c10700040258ac4600083c0e1076210200468107810007105036038524110103408400c0303015801040820902d600d5180c00b141c1d00003021a56002c005008407142c5503420104030000402003030004020b070281c84002a10f1000700030282c1150781c0c4039178904004118078618118405506a070b01b02084460b2000d0788002101d541119261a40da2140802a11581c0601c80c1d10b030400349401d02c0c0000403031031074816180141001d1301e41a084071341c07500c1d04d075048590042850409501d840d00510401e580085c06d507a2265040c03c200d9407844203e00403c11305458035844049803400c001015402d04445c40d032407441c40c6d2144d503c0b9000d0075881585042654058017604403995801d100080c0102c60294050021200078400010303010f450303a5015091242001032444402580c0044e44c0c09500200a034079a9044000e040ca07000310500d0f600280145c180355641d950400c04c80 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 888938920 1250 888937670 888937697
    0xa0902031906060806090307080a2d030506010e01050324180910140f0403260901022d2a0a030f03050105010315051207050d0b01030b10030210 63
    0x20071030300604400565102401c520145414000f0301494040d401283c0a40404a0b1032070340c002059036281070f40b100d800c9082c807659400407102c0c1801c05041c15141c0107500c840039041c80014060000b080d00302c1d0780c003080501d000030000d009141200642410440d003003040000c41e1100e0b04140c0141e101007514441041d03018800622411403c2813000e112170708800600942003000100d07042030051190040c02441c000d1040079072811011503400c906150307000e0000300000d00c40c0c80d019a91140c2d198482442d04d240c00f00b44515460121550310f8a607600250303441d14400000741020b114017003585000e100040359140010369000c1c00401c084648425928400410710109248180b11007a10032038001003103e0800400c20394040c40600e011a15090003c42c0f1548071f0700514040365900f13101040854134007824001403124205545483c0e018242000c180c660b90004104030107405141125259415070a00c0300c3c0c0e41c1d801070b081410400f0001d100300010b84928603103040010341402c060b54480f804 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 888940170 1250 888938920 888938923
    0x231305060a050c070b012414120a180c03110a050d060504031704121d010906050706021218010c030212180708030f040603180c030b04080d0603061a03150a090203 71
    0x22480300400c400c030b05400200303047c0c1942e800b82c100d80b0b08502d0100501005c3c42e10981c6c1c4407410409070403507103004101a03450780550030301c2c1680210044200003030511031005030340d0004809070011900b00002c1d00c0304100f4002410440c3c421b046049816016980c17506000401009100b04020301083e105c40c0001c09146c00344c42c2c4448031002129070751a442c81c10f40b03094800d029003200000081640e600036580c22107540ac0b0380000c2844182c48034480b640c10103e00340c60640200404840319a000c2050701c41da0341c00c016601e0702440c0110980d00c000c036a045500c81c05d60b103c03082401e003014811310989644117001c60700301742c10002800e075000c60941110500760a1200070741010095110001d40c41d1040e82940c00200f049551558080014524105456021400080010704488260b00c003c0c00440c6a8002c07007500248a00200f524220b100951402030f208158015208c2e543d81d078800c507146002004450080540440c080c1c040240008020040100058640a0016030303851003c001c40d01d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 888941420 1250 888940170 888940177
    0xf0e01150e0d12110601080c060d150602010b03070617043f0e0f060f03071205070203090a0608071d010302040509180f0a03090b030703060504231305060a050c 70
    0x5030440b1060421414141d40408118504000141120030940c241050114403681a1688100900b4950340d070301041190360341160250220307881e038450a01c0f261044501c00f503c001c0c80070790004240f00740040304042c100400d603800740082c080d107044480c1c00b1086d000041c540c030907400240c00030051031208070101800030603038644082030000c3ea01000b5a400c2071121590300480c950741e00448003851010310103c106198481034008000b400b101c1240801400956808501c81c580840c03400c10391000502551020b0742c2d42000350700006503a00950809400d600d025110a0803e140c2d00c0c1001c1d00001c1040b0307004841e002c203149002c8007441c107680c4a138040300d000384030003071440e41503007001c0003400c402905140c00c0a4862041d00312110702c1400c0414044039031505900d500404900e8220345d07031440c2e0300003010a02015a1100c020071195604d120303003e0b04210361760801c401c0306680000d1080300200507000480c152292502000000c00001e1260303842540d01c9400b1840d500c0300360143c0d14601 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 888942670 1250 888941420 888941447
    0x3080f0a11010903030902040605040b060d0b0103021215010f0314060d0302070515190f05161a13170313081e03010e070207050f0f091504020d02040905010f0e0115 72
    0x5091021080130716600d5003041c4422402100c04020003a6503400308000c4650981f04c03150840720500070030072242450303071205a4603e070606002d40b0703010441c1e8280041d12021908011070029560190380996800f00b0480c1d4810b842d400c08000c10703481c860340b158414400405643c0b140510f0080c0c14109842840550018980a4107030100301000300c4d04401035801818803499200d004c103004003101403060440400019050f00c90901e40200c18000c605001c0c1c84450507a04034245000d48142c099182c114144079845442101030402d070a45418202d0181c446080c41000e0010b0060040300c880a50307143c40b14a80c80241240d48845c0d020b0311401003145d0080e800312156010000251040e05002e490744103040f0340c2d00f9940d03c5c0c1d8540040000c84990000303000c0d00683c616100d41020308181403542d800c0081d42c1d91800c1c04503407620014059a100354044401113030045001c002a0b000e42c001c6c1130141c00301e00e8066005074106604a840803905210750080d441d0101e03401e09600d405a20594030a6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 888943920 1250 888942670 888942673
    0x31b0c0f13060e0a090311070506040e0a0b06030f0a0c080903040b1b07060e090112030e12031b012c101509021908060405061e0112180b010f03080f0a11 67
    0x1441d03c0b1504a004008220301540440c0320001f42e41d1145002040910554000030100740c141810070291802c0e10400a1090120782d0b5158614103840c1c0d101d00144d0301c80c18011298512a00d840740411058032003421524013401451800c1c4160450080155410780d0f541a9003a902d89142c102c1d1410b01040c1280c24178103500072900086240d0303502042000401c4002d60314001c95907641c5c50701d04510160514081c0018104190011030351070f15411020240b580d44c01181d0803c0c0d800c110440e41e0070b585150038501c5039503a0140583c081c5011303910040c02411400040300c00c0d081c1010700d41c0c5800a811540c1d14890f038494440c618a10b0790382070180604a07010b000c40d104c0f189254001402004002c40d440031031070800c00540c041c58103000701481580094403007014016580081c0d00d110103020f200506110315406a030103400d000f44110002c88502036100f00d81c10007182440c2d02d5090040c0c022541c0080d2a82c410700c041685c1c0f07021a400106046001540c44c200c05100b10740034406401501e515 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 888945170 1250 888943920 888943949
    0xc03090a2d0e060402090f090f060306130b041e0c0b040306320604020f0c1608161719060b04110c0a060207081b031b0c0f1306 56
    0x340c5606000200d628041c00c0a0300d16800010314092400340514410700c0c0e49031507810000380b228142a009090400005030204801c10500c0e000198481812a40300f06150400810000e86150030011150024240d01c200000c10780c0945891440500040000d480000600404c1d004800c600408514a030b4000758148042074481055250a5115203c01c0e2038050411a05104206055040001c0c00ca5000300c2d085d1103201c2484818a5a02c1c02002c06038000e6080c8112822074100e02d00030000c00e5429030140c80a00b0030144454140900c5801c015a1540480011030f011120f52407900181d95480d500e5a41c121140310000386440b01801030701450303d1415010b103003040601c0c5c01458150388201c0b024000a419603098000c0c0e405502c41c80c4110364444910b0310040380c03069005041690140600a1800078040f0041440025000c05000d09a000141081b440103042c401070f0402825103002e0700c680c117032140000721036240e200700d002d01c61004510132112f090f172280d00440041c206051501079 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 888946420 1250 888945170 888945179
    0x60a0509040308180114010e100503030c0327061b0a050d03050703140609010902160c15020d091409091e0123040c1512090524070f03020c03090a 64
    0x1540c1c4250ba21902c90a0450040e4014504c180207601c001d010410300d9505e80d070301c1d040c44801d407010701070b11407103010f00d007000c010580c0d84003400200102542032700150f03656054210911450240c100048060101c901c0e0744036845e50765a012104041c248450145604091804c140d00f04407101000400ca4420545417029003a01500010311481c040d440820007450180804d01c1a0700341160701d190300041180047c01495210790141c20107a100325108a4140c82d00d036202e05c8161100c0c0c106100c0701c840c4034080740c9656810000d0451050462421b003420603c0c20018a000a80e10480c683c4a07900200c0080c5241c2070410182d107502e00303440c155010080717050038828020001035000840d141c1940c00102110218008004d00441c4d1065881c85a41d1030400c01560740208101140104285030700c0140c000c421031700401c15510f00030000307030200142d0780084800c5030340d400c2218007031503807180200042c0720342204d41900350840c1800c026a03076001a0070b880303003548964004130760700c00d102200104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 888947670 1250 888946420 888946427
    0x70b04152d08010906090212040b0a0e0304030f0501110f120a090f140f01020a020c09090a08030c0a03050a111218070803070b0c0909011403070e0108060901061e030b060a05090403 79
    0xc2c100e9544c40340410040d920740c0000070a9100d0b500d00c40e2800041700303007c90000380041c05807a50007a62103c0000b0a4250300b41d84604541c0954000c2c2c8000e10075010141c1844030078801c1100e0003480a881c14585031082000a1250140400c186440d820000015040408a4200000443d40b00da08803034400300626100340940014030000c00e040c461200b003114007003014030841d20750300341070b8000703018800b002d004000300303500001c0090034140184079a002c00604241c000c0c501508608280d90384603220f088005003150001050003904609011441c2e0041b010079044494501c0e5044200000e6560262904500e020b17580c2d240f150b91181c0d00300040c0808000c00603002040c42149808583d456800c0c0c440d00e54061070000590203c0340000401c0b0400c00c0c038000c079400907800f50603500115038440c0e1444880400341d10410864102000b0899a804288a0240a0460f00501a134000101d01d40c100a101c41b034000100042040e2000c100c0301e50f51812050001c00001301030038454075003031a008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 888948920 1250 888947670 888947687
    0xa0c0e0d03211e0b03190206090303090d2306270c0a0b0903010f150501081302040c090302030c0102070609060315080604080a1806020a061a03150108070b04152d 71
    0x14043c10f40fa00c50044080d01c3c0205080d80251021401c100300d202c003540030000d00e68014141958584810892490360762070301c0d841d40c102c1e0b0340510f40a1030446841320004c07540380500391042040b500400100030907008001400052885038016011b005024461001d02c0c021201c3e6005900109428000070040c00c1180103140c60701c02a40240040401001c007001070340c81c1c846003140d0800b20550180055441149803943c04543c03006144460602c540200701144d20086069000690410080c8294141001041441c01081c0700a00c0d800c4d18200c0014481c2c0341d18080c1504050f1680048603400c1c80030034040020b0698401601c01c030b41480c3c41c0105141e40151207202c0846c40c0b004404520a8008903001c0031170354190090401d0203515038600e8018106034046010143c030070081c0d168035403420170078641c0c1164035200c40c4030294104080f01c1c0c5021032950102c1c2d4841d4081100f8803207500d0140031115004c54600f031101d1310301021026202c0d030708600303900030198106011020b9032091380103012 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 888950170 1250 888948920 888948971
    0x9010c0c090e0706091805040203031b0d0311030412200709150602071d0a020c0303090703140d2a080d06031208130f08090a0803030a0c0e0d0321 64
    0x120380c6000c1e07136188181d80f1031030f692041100c05042075507090441542d5400250b442840101940d203018070f00174805202660280800e2081d601c1800c0d0081c00c80d40612460b03240c0031140d51120b00b14641079079000002d01c1450082e008002030020740300007240000008504190702d440070798030072940b18480e20000700060b1190400c5c0404030400018031078000300d01c8006842c50141c036012180c900c480b0403101d2403005841040100c4e82000122540c00007400694002d94162002c0c1c603d1030b18600b0418294906080c80c0d46064108141074046150041c07038000e8819a00040400d0b14901035401083e01000040050240700000030451590046a48802c090305d1203910300503460541e040003211000710864000302da00308805403100218000d5800c80752814440c1c14828604006200030541031001544103400c0d41e030001c414410a00301d47e010300f10030040507151840320007100c0ba00050610300c1440c400390074031510552141d650391011441042c103581c801c030f0500142414040031440d40c43c00030613 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 888951420 1250 888950170 888950173
    0x31809130b0c0a12020409020309060a2c012304030206092a0f13200a1b0501020412290906062101060e190207050d0509010c0c090e 58
    0xc0d0068a1040103048080e82105561040d69154101d29031603030b0182c0780d00c20500c83c1c11442d070700d000907041c0014030280c10070540260726401c01c0100d2924040000d440050301070b0a003039011130b40c041941e4541181c501c80101940d52014001881303401088038501700c0c0c0c064917009107115035030013a034941c46000d03600c030f40c0c02c540156079000301103502e5640c82c0110b004070a407803a951320504600c900f1a105410f030010035212000041000242403d50540c1c1c1070388415446c3c81054004582c5c03089074440c0d2354090041e10b440e1a2400000800494110307ca0b60a101880d45800081c801c0945c1a41d014288110014440014a05042500014000c42803002d021194041c8101c3e03842400c0c250b0044107044001c1c03855803900020000941d8401440200b15080e481e049040b03a982400b070380d0b00405540e210b0b80803e08144c00840b82c501420b000c0d100e0440d004100160028400164042c0780d0046454965241e20b200c00c0122020810300201800d600c21261020a0003141980668004440e040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 888952670 1250 888951420 888951439
    0x402010801061806080c090909010f180210200d030506040c02010207030c080a0203071505010911070c050105070c030204020304050606030f0d020a3903150902130c02030c0318 77
    0x4040341c80f03c8582c08418000d15040c001001031a0150f02d8243c1c203c00e030740d00241d04100d10b05021800d4040200c0d50401c00782e44980d02c509850642d445000803038826065640f40d2014603401240710400580c01d008100030104400c100c0420116040c603000024450680d1280e5500800c014040c08040d00c40c58441d80c030308030b840c81400c0e00503c2201d801e50f61548032428001c0d4162140e001c0340d04980044015070004000a00011b184890042c50400880c0c2c0009560750600c0242822110041d1010b07542d20030801908011951000c440030440c3d400340f0307207669070300c5151034240e415081d258070084d00940080188000c12202140803403041c9030070b030103d88000c40c00c01d00c20f41d92250b214a01c0c60141c0c0040c030740c1402003010029408003240b050b40110b11881006a0f115500f010010800000190910700a0003000081000310f1118002084113200c004801c0d00050b401601214810b0545980c40c0c000c280141d0090080d10601c1d1011000c0e2070311421180f1b64a00104c0b080c0f4238461141d40980d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 888953920 1250 888952670 888952679
    0x120a0812060a030f1203020f0c0f0c010206190509070905040302032d1c0b03060403180905010b030711070e1305060606030906070c0f05070b040e24040f02120108060402010801 77
    0x6001c1102200e80000442010031015114281901005c400440401da0200446000c0c00344145c000d2400542040c01003105400c0c03d01074900703003000395188a0441d0407080074007640056040700001406a070410009194550300403940c0b030025036601200640b030406082005244d004005085189903c0c00c3c100c00807043e4020035021380700e1182e4000c440000a111006d81100c000603010040358000700005180f030b90050000303103060003c0310121b00003081c0307180c9a004023203040c0300c42006040e050f03011300c41941050044021030000034003a008005040000380301558040001e08000e0407031400102490408002016030f1464060055405100e580049411410300740b0490780315101c100050003280d25481804c81e6081528003040e180003200c1800540459804e0010300d0003000c0100780aa5a24900750ba0003608400040c400310f0134400391044804401c139118032018180c001150b000504920260000009000340384101070502159000858441e0000032034070701540c000d0700d49066582c4d03035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 888955170 1250 888953920 888953929
    0x219240f0f08010b0702010507080d20090904030e03031306030c020f0601050d02010509030708010c030209100c0c05040f0204080105130c08071406030c161209080f0318120a081206 79
    0x8641070040090500d0004108807920600038210a6105152079442c1c580d5540b190450b035044055140116a0b90b0307800c0135500702c0308006c0c15076980300e281d00a5040402e48800521314600041002e01401241c3c0001c40c142d980a0049800e00428015059506610380d50010010004201700d04094882e42c4410b40034480d000440504a810051547d0307081c44503940110b800d0b400c00112140c01d48903801010885010078025013805104954006841d2952001042010246a000f4100744009081c0401c042880080c042e010346000340c0b40412070615410748d00c0002e00c1035a00c0294103520301400c1c0100c0d55134104040c1c2c4250b000e417000310041922481d18688034801c510035030150350103039110446a8242240078640c000c0040390106e007403540c0002e40c0c0016a90183e41140c55290140751040c00c81d400400700d0000e014248001d00310401464849541c910506035400030b9104e00d040c05081076a10071502c014241014410750308601114540240160441c080d885114003400c0002400745c02c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 888956420 1250 888955170 888955187
    0x90d03090333020d0e030403121704110d26070c1a18060409090b04022d0103052a0706050a0b0120070b2b02070308040219240f 56
    0x1400c1040e40b0720b000007070501000962000300155072641e103400154100800600c0600300460243c28180152550f40b5001044415800c1c1c07010280c841407400c2c0000b142c41c1c50362801c1c21070019104100039450505040711601c101d0400049500c070f0120341d6080c40a002c8010309201440b640007a000c3c103440b20301401f40c0e000400840f8041c030805015100d00c07030200601c08404080c000d4004c901c1d154858900c40300b612001c10060701c00304100001c0c0021070400d00c40c0341617410f1039580c100818103243c000d10002c54000c00140c1f030400d6241e80120741c002905810700c1707e9114250030006a48000600204216042101c090340d0b00c2d40341c400054041e60b450b004100d44180144c0d00c08240c80d811011510103200d608504d51003610441c0400b240e400311240040ca5900540310001d0800e040021081060b4034056441d92051401444000300003600003040c5600558103d90440070003000a014a1464040c0d40c401d000c160344c102c0b0f61454440a88451419003071055a840e100d41c0b295074410382d603044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 888957670 1250 888956420 888956483
    0x9081303031d030d05030c0705070b0418060503100f0209040c0309031b050c1e0904060b27010909051c050d0501050f0d0611070c0e07080106110303010e0408090d030903 74
    0x300007204c01128039218500966000314180105030400e195a11054075094554012420b0910001400e112503140600c1400901c088000c091103074a04110210f0b4950390240c050340d000a40700d0024000c030500e560140c03500c4030000f0303104024001c035048008000d070862600642c08900e2a40d440003920360100503580003603401400601790300c40d03600280700007000c40c0d000c1c0c5031121001445004107699200b052a0085019103400b040742030000c0d04000f420b50094050b03060300e032002c003071551319602c0303181601e41129507403200050071396101d0038902d092107140301445800070101101144101d802401030100c540340740204000c02d83c0c03103e060045030450541c1380c03a40003403510032407000209160030041c40c0c0c5402ea050107040010558030040e480740d9a0300412040d03002041081803640c2e2241107140182440e2030804440490a5180c80d20381c8018040d259003403040c540054180004481201c60311500036001000d0684907040003801c042403400111001400e40040706081d646141c400c00305034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 888958920 1250 888957670 888957673
    0xc04050f06120c13030b070f0207080705010806060d140a0603150b06070f02041b0305190203130f02030703150b0f030d052a0a051606021c08040609081303031d03 71
    0x25143e6406144031504084130748850320100003400720009007a54920390280c10561a42c0e0380420300030788040d0502400d50410012648000310400890ba4048084c82d0401c0e0240c2e0101c0c0e64040c07a2445c8409400c02c00855818156440d060020754251944000116801003203140c100d0895120b00750103031501c5500d51035004106000d4400429101c80520504a20081000a8400c0b48444003100745400750b0240b400301e40e80310100000d82c0000346e11412074a0b00d80b10214518a407800611121100c0300c400900026258800181103490400400700590f8019801e200c00020381c0d80300c0d4001e858422171040c0135030365043c0c1020483c1000210180701d2000c3e070300e410381030500344002900391400c440481c0c00741d100c000c2c6045064840c20b112000005000f240540190701e9500d0101802c03d0f469800304045500c4031034200d5174005042824280300b48140340116058807581000c001802000c000503080110000d03542000034100c1782c00f0411130b8400d40f00c064142d5060058040681d618043c0e09030503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 888960170 1250 888958920 888958957
    0x1508040b01060809010615050a0306050306040305040b22030606060e010206060901120204090b0901050402030601150507170c0708030c0c04050f16020a06060906050108090a0c0603051506030c04050f06 88
    0x10b5801a4030240d4450028000011038582d40c6500d008070290b5209200003003070340000c1d42c62446505000c0c15020341b0080d001400c00c1e00f440c4d0f50003400c80c41144540400340c40d001c1070b082166401c0c0c2074410392030a104c1e026150380b5030700d034101a030050410384500b401144005103100482e5001040c1e0342c0c03107918000c0c0b28203803d83ca01501c2180c1039000c000e080341d105588055020011380102207090050307402c44c000050071b181034414540b404006801c1002e801d9140c00001c44015400000c844805500c02607148000c440844141068010004104580c0c01009004a1084c00000181044800107401c466411941c403040c031049810030f58020040400c0c6100041013171010306641c80200342d5500c101e40300b810464079000c0071156181c0107184040d80714a070401903503910100c1c8075040002107005e000403a220f40c0e5541c010315100e10a06092640710b070005030300d8820f080286010003e02030807040c0e40c2c0c5040b211010a13944030380540c1d8482c110415040040b4188441907981d441c0020021054 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 888961420 1250 888960170 888960179
    0x317041d0907210b0408090a05011d0d03200d0806010903050307201306081507050d050603100906200f07030c060f0c1d060a2102040e010f1508040b01 66
    0xa88040c1905811108101148807200081d40e103400c80b449280141b040f551030300d900d681008882c08944d40098100b04040014082003030003240700d580d00c01d104580421600714070b8502a642e0940305050310310194554200c003181440041010000384100361343d0388951741d0315a00155085689808040c00a41c801c3c000d40d000074811504a41e601c41e80100300414011107180020030600707003840d40c08002c60321008100000b01080042403014041c8003005810307442d0900c001031090041f020650701050f02e8001150850301e09000c80651141254000c0c4401201410440d020740245e4011500304611035015000c0c0d08240c000740c40b03000996101c8145014410b4034100d9880c034400c0001c0e141156100d510b68014402ca00c00c0c210368100383d840798a000d01810340d6400180c0e03641c8035160300680c03041040801e8a80d1000c0c9501c45180030340d880c0d800c1101d24401080003030007640c001d0b203100b24155001061460b89100303c441102c0040d9202c8201e041d21200032140e2040c01d9070300502c3d10301e14000502 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 888962670 1250 888961420 888961439
    0x1d01051b0d020f190207060201180305070803190e03070201090f0f0611070b130905070c050705061c1d0d1d122b23030103110a0317041d0907 62
    0x6083c460742044241052966500b46406403038404540c805031748400820000c2d15028025074414800f1890301c0d000008060710050010f105081000b00140c4002002440b6040d138110f1006c00060702030000c100f43c000c050821a40d07540180d9059020070140e1000250251810100307409a030060030301c240c0400e2805000b0f43d010b01005804450301c1c0a0300c0000b00341d40d0070110203032110380d00080c400c11070285026000b074200c502c040c1c508000c0140410b4150040f032800682c4501726801030300c440359254203a110701000702d085d070045a0803440c02c080d010f07100c2e107403090310311600c0301413080c2070360741d2489071000958544800720909448841900315074000352070b003003a030303c4031042c6c0042c1078551a030b4007142c001e01c5800075070f1080a00c8070341c607940c2d03041d90b81e80c044010741101c41c4540440d03c0c0c07442d0b004815802c50105100007045014190309801043e02d50a0b0200011640b1204c004c40203011044240c085030018010324801c0310f102c0c003840112000444166010307414900203403144078109400c0703c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 888963920 1250 888962670 888962677
    0x70c092306150a0c0803070c031d0d030f02010f09080316050a1209080c031b12090904020d03030227041401030f1127040204060503120d0902030703061d01051b0d02 72
    0xc8113000d40c43d030211021500c01001180700f18426074444820003480e10b4040c0940380040c500010944001400c3d4040c1c1c2c50304581554442d416007492401081e42da40c04a025061107842594035900703110798901000301d082d02030f50107401c040940c007940101c2c12000321180d00038000701c1c400081c00041d9500c10100b496124005207405000501d180c0900c2c0d141040c50755202a0368500441340503890304040243c00d00240c460000000b01243c82c01d8650000504201c0c40030381b020384503800002d503010405010f83d04440501c580707803100310000103486910b083c5510b8040b40f198016810b110390103e0440242d4129410b0b42e85c0603c07044003034056910790081e03407144101c025802243d0070a1030741c2007044d0031520200ca10602d9031090f6141ca0f2503c140015640a640000d002e90300280240c0c100306004001e07217085010780c040001d40c1e8200f03400006d240c14495032002d4840d502e003020306540e42c00300c030310301c1c401d0384070868024003194880744c1508029000c1040701c1c8043c0d980078442d1404009040e0020b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 888965170 1250 888963920 888963937
    0x11030f220f1b0503031309050901020d0c0903030f0e060703030504230106050f0901030305041a07060c031a0d020127050910030210031406060a05070c09230615 70
    0x54640e1046260744180c1e10111420781510720300085032002409501c9041e00c40301802c41a800b8609104100201b40c01c0c008242c002c4002c4103440b80c000409800c000d50544602c00c850b07050901178090781c148003400000480c002540003800c1d401c90400f505000d0f4030049050200a884075180c001207440c00ca000300005002220740901110318a480180c42c0036008400d5519180001a403a19100400c441c071402d0b103a10320b001d0603a50004001094021054908880b83c2103501050541d01a00841c902e218181006005910386449c058074158150b0114205c0ca0f401e041004240e10340c3c004001e10303101840c030003d00189200070b03944070800f541282c10707540380101c50f42e2028044e150340c0054403003081100d0010140d00902c02c10410b502e40302403130620540140c02c040090fa010060789140c1c60f0001040c0c44d00444000580c0d00fa0b40e44148100c2e916650440d528400d0030391600340240181c207000b02d502462942c480c2c1c0000d10314240085450041d1402000c0c09111101c0124414036074226890 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 888966420 1250 888965170 888965221
    0x2b140a0c17090409061b030b0a060806270615070b06151611010e0a1422150816050607060e0a0506150306011205150a0e070b070611030f 60
    0x101c5080b9454a0003180121840b914000ca101802513890ba0994290200864100344c01d2034003000309030f243d01c160780c1c054564a103030064881d9101c2010584035803580c2c1c040d01d0f840045080241c03803810440307891030254400700e0302da5401e844215aa00038500401d04041c14103040382d0003041c4c691415200044040d01e404131000d04003094212100f4904c100130170162140303442c031420603a00b507a0280d841038455070f003240c00040d501d0800040d009c02c800d01e4210725000e03002e003e00c0d140042203901c3c00f4000c46442000240242c80c407401c86041040003d100c0c0450034460303141f01050702d04151801000799640a4529400d043c1e694031034002411000740d09601c28002d82142501050b000e1080f07501c100080411010515902801d0602d41035059200d02c80d002c140b459844001035010070003100d004002d0141c0009a01c425a07101c000307000c3d96800104030302c00d5210000309850281d000c0d11005014100801015a8040ca41002840111500182541c0c2c94000038880700750071032a104100f10301c98 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 888967670 1250 888966420 888966427
    0x306070f0905100203070210170403050c64020f0307150909060f03030503180732030d0507030e090a0509010b0a050907030e2b140a0c17 60
    0x401080403d040383c100440143c100080039815070918130722158041c0c00501c0d051880c00f01610300c0e8040c00c1c0780908020208079000544080072701040004800f20b03130481d089401840009041c0007284070344145000e0010307074259902c029842080e1140d4503a101c0309240c10650500c414111840000d807504126445030b070496100c00651010850303580a403010407407032462002d051802909081c450741c0012584c40c140340d0207128650f014103c004c00c807581800e020791686c950710444045402401d00004d56845860302c001000d0300501d5070799022940c008218890f03070703240740354440c03001d020b5409054140d480400400c0ca602d214500030582c0f50f01a1030100000403d400c00210103540603140f80c281192141d0500c00c1346502807060180c1c0da101203585841823454180421743c55000100045c00385661a07040001001081c0011007401c4461400807511507801501040060904000240040d011003060050035400c002107031890000340d25444c2c2115282d40c3c03180711380c00440744070b804410002e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 888968920 1250 888967670 888967679
    0x32a0c051203071e0c1707060504060c032f0f070605151201090215030606130e27061b090301020d2004031e05150c0301060e0108060306070f09 63
    0x1e011080205201d000d8150b6a410002c0e001004111441a94244c101d030120310b1051007074114000d00852a4804070b602956490058081c100d8010000301404007801d0504100130801241d200c0180e042083e1010040b510201030180c104c40c28407884405100480d50b49010100e4480003c0c1c8900f1032076004103440c0c014140e540209903041610900184581803950041130302c0d10810000040c401d4400070000c0c030203290000395400507038039990340000d000000403034015141e040884100e02c040c90109100c5507900c807400c181d0030504540580c244040e4090f507004070f6040c400b098402440309001001e10b41c07074000c4c8442e400c4603099411030030705508000031a52900c1c02c0c0050820070101890003c1c031b0181e07808800e8116003400d40d8410004200700000e10001e0050f82c11a00c0031400c856041e00524003e1401ca45410000d02e203640e43e6080110400030024404002541a03030240d507200b05024110000566400c10b0907a9100d50641017040080d00d03080c450000001e0300842490822250303960b8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 888970170 1250 888968920 888968923
    0xb0f0d110d05010c02060c0c03160c0504062c04020a061206090903050304021e03030a2a0813081c0e0f09011e0b0f0a0804170301090516032a0c05 64
    0x100e0070868142c0d440780388180c1c0c080d4042c003804c2d46c0000031009070b03450811410071141d180c1c40743d070740b00740c0c42030100c5101e4000344040d01070700c02c0203454054400c220454640d04401ca080c41d41c010408411110b50b03060024803544403040030b00450340a052201445d0a0000980d40d0a21080d800c2408990304c80000847c80d6603401110540d0b80a52195552401c0038018020701104428081d080c041003052441c016032800411525614650314120b903000c09191100040c5900310603040c00314018401554050000000081001d8101402010545035840d0b0180d610b500507515450842c9003002007211545004620303180c007a50005145034034144901001800d030302c10a170480d012240040c42c450705c0d02c00c0303031020820140010381c25540c10880240d0b080f0300207100d03103111030040000900100e000c02ca00c0c0000000310200c40c00d00d0b952a0340c1c545d4002d0300103001c1100e103810390590740700c40554158081e102d01c0080c4240f13076000301160b107039481e040d81403024489084801c104a1038060f4010900 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 888971420 1250 888970170 888970189
    0x3020307031b061407030e0c0901050f03030705071517060d060f0b030625020c03190c0801050406090b01050f0120030c0303040506090706020616080606070f0c180b0f0d11 75
    0x41113000849a09101900030b04580e005154408140d0200d5480070321644c0d0b00c0750460441d13400f119691039010710304001c2402e6010380b00000340380341328499010400610080700c1312800d0455540304000403904803034405210005840064204035840c02c108080f030300b0341d0403c0c03c03200c2000c0c5001c598814038901281c9010380446200f5400b9015071801d8028548202100103150602c1c4000c120502c1c241001a840307075402040c6041c80000d030181b100800c01d81107890001040c0d150b001b08154501070400308060603078050121400ca00c44000428681b038502e0201003a00300682d1980920004409981400c018640300f00c02140310500c500c4d041c0810802c001c51150348254041c01d9241000d0214030f2419960750071880541d00084104010607459003044030300d401462400c20040d80782c041c0814042d1160300c2c40540482c804003010402e006e1b01000c030f04110303507109003807034080ca8080701544121440e4100031036021070311404030b040c03510f032004110390b20f580a40b802800c214039607070014690700d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 888972670 1250 888971420 888971441
    0x3080d05180a0b16030e0601080c04140c1e0405060d0e010c0206190c0c0215070b09030f093d0f02030307050d1e0509010614060703020307031b06 64
    0x1a00d400c100a907030400140c1e1018840c00300c00c001c100d400c00590700c80c42018001015122495480381c1c4038904a0b110780c0101c0c2c01e40300b44106852440d42c4800c1540d0316441103082c2036004600b0441c00340009081c51481a100f11003800019040c105881170702280320801110180246205020218060351403030004d1005001900300011b1780446603509509449143c0301103410340d0030507020420046030001a000406507854000110259600c509582e6003981d40c1000c0d41100c0e0030000c01a800c103800c0010106503006081560090b82e0f940100b9030740340b0999000c2031698905000c0010315040544480d0284200b8410424840f5100100150a4403542c0480207025442a69001c086a00000d03e02041c0087c2d1016511b540f81200c005402403003100c40900109548075002040903201c0300d07002c2c001c1142c03a0000e21040c2050342c07849019295038094144100009119901e1614059048800b20760b0700d034000d18180b01660702e05460400040012030910090740c40540000b403054450414500c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 888973920 1250 888972670 888972697
    0x509011205100c1d060f0405011202190c03110d0e0613080d0c15020909040b090a02040e010204210b0f100b0a030c170615160816050c010903031d06040308 68
    0x304e05001c2403d000c2e04120109801070404004400c0c0c80d014102c101c41c140c0d002800c149003804400824400288100300e01c000480c0d0761a150001d90303a60100119008034002d80e51407052078464600d0302d454010045142004c6503820307030300e100c10782044006484048805c0511000850752002224200320441440000250b0450510401c010f030300312018901d4032202000f14100401c2c50003189600074090400780120140400160720220104005403005601500074041c000c003221200b0b010303400034001ca46100c19442d48414200d150b100c810490140c100201c2c03284e40c2c0b40c001c0810f210002c00382c610405c15072248800310b03001c0e10520052407885440d54002602c051481c5006040e81c030350708000d41c95030903040244002c650311a5010482d481502030710f140c1e64003640121003503000340c41000030325070003000c030b034480741600304181d80c86800d8000c1d41960a444c0f0b2170783c0111201082c2d40030050120300c0010860270110448180c14519000103090700c0c1c5060380f203072a0407407150003409650406 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 888975170 1250 888973920 888973937
    0x5070512041707060c1104061d0405010c0201110322080705030a08060a05100f03180c0e1b12130b0a0b1509010207060c020a090905030d05060105040509011205100c 72
    0x240d0200e03002d41444001c140c400383c10400d042a400034258020154080c02d4040c61411840d440d5580341d200700020070302d400304003d08032440015603581c12003c030780c141c485500e0300c40781460060060081c0d0480c1880d0783c0b44a407942c2c2e0380000000200d0b14031002c0c55400d4078003240e55030016400000401031a402640150780f03c411451001702180001031195000f01e01800d8104100d846404990f0551140c900b0264000c0d90103481c12030090818120800156680c400c0b0402840b24a0820205442d96003400b507806a41e80352103441a0700148084c2285076008020b00ea910001e0303c5031f40d40d00301001ca000b842d00412961030700722804d1810b661048006550360842960361401900700a10740101e804101d04010b19200082d440d01d01c01e00c2101300f8001124001021999140d0307041000d8038400720f08104007400c80c142107a481d084100410701942c40c18000c12025030080060b1021a10002c060050613800d200ba00721980068680444151042100c0d0988440aa0045001840c540d5171040070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 888976420 1250 888975170 888975179
    0xe1902072a03151d01060609051c02010804080d06031a0f0f040c090c030912030c022406011d041a03120705120901050408030408060105011706010903060c0507051204 73
    0xc0103401c0005150040084038100000303580030a81c0440582e1520300003440a00c40082600000164014885107500e85a0045006038102c1510015501c0507240d404206071100178046503840c80c150081c1c0420b001d00300280c0090f0654000f00b40d10743da40d440c00700301541d50703503648201d03803a40d07040d42c007000c8001c80d04101410365200c5805a204924a07200402130070941c0301c18941040a014030200c0031f46906184007250f0090300f03caa1501d501c0300c00c034407030380c4054000100101500d90400c2c0040c05a402c544803000010100d5550000304160f140b8490780380e200041d90400d10b68410740381980c241c220340c0c07400350766188201002a07410102021110050343c003018200004010000700441042c08294042000000d1070804842040c500650320360081c001a00d00780500c1e8000082c9100c0003401080f100404a07038281211020f80310880e0b442c8180b40c0c0721103044e000300e50140c001540100c080010842a401001003c2501c1c200140341c201503440d950f0504003480a02074441b41d000a0412 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 888977670 1250 888976420 888976463
    0x20102030d110306151905090409080f0a030b030303071704060b1309060f090b061215040606090b043305040c17060a030b0711070f06031d0105100e190207 68
    0x249007588141708070f0b01e030540c03800030654543c513540c52810800001040d0782c042510355501c01a00305400c019a0f075140c1c0c017002e00e481940d501105031030000905001c0700d808142000816640995940d0711090080ba9080d40d0446034440010f0050300c1d084e85482035182242c990b480e0b04200c015110101160700c54141c10403105031034211200d40d01152604100344081072045c540250085411252801c400f2840a601440c007a01e000031000e07030051580a1204114041c0d20050849103030181c2800020600400c0104485c40210864101038900f05a601030340500040070481c0d00180c44117000319519030300814102c91401c49202c01043d41c102c018405030160030251a0320000c221882c0c44850304590312015404409441c0400380034500c03491400244092000402810389015241462555840000c01503c0e080202900c911201364400f102d4401c1030007240d01ca500c0d001c5058680340e1910702503990a040003025aa4038500c107185c2d0340d01c0b41c0d030a80010f160080c0503802e0480140202c61020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 888978920 1250 888977670 888977689
    0x30917030c090f0a21020f060309062406191101180605010905060a0e071209030c1520070c1d0f13030f0c1104060303080711031e07020102030d110306 66
    0x14844d0009800c02c100060a80b0305200f04071000050300c1c40301842c5480403454102c8140d403020760210703010040151200b4001070b03a030301c510055140f80402003210014014540c04a01c1c4042d04100c04110b03141d0300840000f80b0b80b00b40b901e2450081c031045048801142102d240d58105041e01b080744014000b44070320717405064090820346008000034100300000039040d02c1240300d10076898144c03400180c01c090246111824000b5100c506002940c0c030303468010a5120701c42412504403103540e1003401a0009132103500e03506210f116a0440c52280003c40c0116034101c080100c40d103d1238128041180b009075000002c842c120782280c800c1e9418041040551404020590200e08900100c54004640c5c022405480301415081c8441c0004060034030080701c40b500000300f40c109040c110000101a400228907114002c0341e50761048022100200607200c0c8030390b55804035503059500d501c20002c03103100010b1000e10b2050040340d10786140d0340c4010041d950700c0311344a051280007000700610b41c03c04a410 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 888980170 1250 888978920 888978949
    0xf11192408190b15120109050c03160e1201020c0d032405010c060f02070f1502090a18021b100b09010b0d110c010603081c0b10030917030c09 62
    0x10884030b1601070100000d404100110184940d164420441140c66042003032421002030212030707a462015820301c071440c3c00700b032142c900b41c0c510302000074210780343c440e060303d024501e00c0022009180200408884030084407400550102c0b20341c03d03840a807803003480284800c40c00c0b413003e4040c0700b01409000c1c00b100c2c0204a01c4041107401104500c290f0501c04080050b610309003407580c5040c1160a021004061841024400920001e11042400380340242000060b11a010110500c0d4a615006c802d82c011050103540085100f041442540c207580f00200d420162104011b08100c0310000c2041186941c050250081d00b1081211490703644c10f0059000c607881c20f4502c011994074090120b016442600c0da46041c244d44c4011082d0034094100c100c480214010700288041902d90070603c102d03a10403403604101245011030b0070004407550281c0e01e48400b0081044480d41c00b00740081d80600f001c610115080c41041260075003841218006d0740c06018440300e401d0b01c2c0c9010b8403e000c3c601d10034104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 888981420 1250 888980170 888980177
    0xb060301030201020307170f2110050321070c12050c220b010201060302062b051e10030609140f01110306060f16030302070c0b070f111924 61
    0x500143c0d800004882d030f1658080d24061003107041c1d826040460043e1442d02101d034a0000e40314140300054003000c140c0b6001e01c0d001d00001d4036402180301e040200d601c00d40350140c2081802041c1c0ca4044100c0c070106041c0e024003d0316050195407840d5441611780c02130440b010320706c002103051000c100700050800c0d8054595104041d08140603e45480740b01d4400701100703480740b50303110140e4402e4000342d0055a016124584403801c2e4a5013094507214000390b0700344d01c4050090f9a991060b98065039001e11800c524100e14200c00c11000d82d14254024440220450782041c0040020031511440d141580520f40302d0a50304440640e00e41050740301800c1030141d070b04100640c05815003450880e6000704084824030354841c9849401230007800b44460000b284158007000009068041d001004040d03ca4500e1500341d50b2071310f0000107a0f00030110050b10445030701c21040001940400b41c011203540c01414401e4910740840b00ba44a454550400b000041620f406400c5001440306204008202c608 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 888982670 1250 888981420 888981427
    0xc1d04031209030e1f1101110a051e0c0d08130b011413020c010204141504210209090c01030b180a05100b0c010b0f0f06181309060f0b06 60
    0x48004003107280184044603060b55841d100001c00d80503402e284803d04000e42282d12609041d448100340a003120740301c0002c5049915191031411040c07165070388502c003085242d0b05203103050304100c0d4140c002d85a40803072440400442180042180701912510842400a240740c1c981d00e54001c25501c006043c9c0d00d409159a6074420006840701d10581c15245000b82001031a001d04000503072201d62040b2810f00203100241c0d4581d04c220640041003a0341d00c0c1403114610002480034401c8402401c10020b03d41141840288404040c10a09650064100703041109142c0190000703600180e0a581c110103075031001d400e200542d6014021080060b104554a1042650589115900c0a0000c0440c01e070190346000040c8140100ac1c074803800380c04800f0304240c585400d00c940038021710f1608422442016440c400c40a14030381484222501500a0445030030403600d03510b003004407441d000906500c80d4403903040d00c140062a2085400690065402240300101340d041c0204a5002c1445103014070000c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 888983920 1250 888982670 888982673
    0x3071b020607150f020d050103020a05010206010f120606030b0903130f06090b030c0c010504081c062105070315140c0307020c1c050d030903020c040501030507060513030602070c1d04 80
    0x1c42503440003034121000072034000200d04080d00030012084000302440c40490301d44401038070f561050307040c2e034405e444d00030016454100580e1340b00c400b441380c03503d40d01c080c0e41c042c07140c001f4480c12520000c3c400d0101003046070712a0384072030b003900c0100c0741505154000305400b504440d40010040007010100034980102d820041c00501000702401915400b40d030020205000c10036080444040c158400d008200c6420989042030040e4002100d01d00000414290044d00356414459401202d03142404035200540e040b03012291111f01290607140c1d4041e0f0103001021031500e0a8417000f8089880002030260109140c10012800242030542d01c42e50910401900c140c0000700d00189840881c2e2200d0481101c154516001038000e44c02402c502500c0c049103151340d0103420603d41907210342c082d100382244201c1070004440c2e003444098100d03405880308108175401a03004041e112242008050915142e454203003d0340d01900c2e04a80c6036800003000c0160489030103440101901400c3d00590780c1c1490f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 888985170 1250 888983920 888983929
    0x31d0d0210230301030609050d0206270f0607020601150207030b060d05120f090112051b0a050c070f03020301060602071a09010915020a060c0509010801090b04110c010203071b02 78
    0x10700d01c04400e208109600e000003441a04841852440400d0810760700c1da140d10701040905010341c1c085075503204450052024500100c1c07900d201e803000740d404c0581c41c0744401550604d9244c0c0f00000100c2d012701040009000801e000c024032034125900100850751601010001414010403e0002c42d049031205100140030760b900c858000300100d4051200003102c1c14040d041417105042240e10640000d8041600b070003c0000d498090400d0700c03400c00220082c7d0304c0505540d01119684400c0030440d8a02612840d030320064540c5070702900e0f200d414548084640740c03034911980c002c800780c5045441d00b002140b90034040d40001e440d85201030b05a0b18640500b03e823010b50400c1103204419400718800300b040e44585983d034010042c1c0192880c12500c0c589000e510f40d140720344207441f4181480e0041c1e01c407030300a00071124101d5041c0e41d20151a803030060003600400c40140c05642c0a92103101003100380703c1d804081c1854040100c00180e40b400c0500c3c0142000000403088400c1c1c0795514000400341e0703103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 888986420 1250 888985170 888985189
    0x9060e041a1905030d020a0303150b091002030d0e100e0115090b031f090b0a05011d090f2410031505040c03081b0705030c09010303200a031d0d02 64
    0x4059803080030b042202c0c0855810010503400c90f42d01482190b00c6020515400030310f921806000c0c4d00c003000701060403000c0702268402c034000c0e00460b40080040000301c1c00c02002c00343d8204031610541e4144034040c4038010030744010754512400359220f04040c50740f01e400d5105100c103c039082d0008115035005021010809002c5216558007103580e08030072210341e142485422164508415045541120254070350300500f030b00c42040e9142c40304840064860002c600c03a481c10388180745511400c212401c50040c5c88101d00a0040c1410b0290a44030a11040d00700603051013004016070307014803e041040440b40d103500003000440269008001040031400c42005100788503100d00f400b040642e55818603100660055000800c07404d00020605045a881050251520181000d45100aa079401090307960000114443d51010ba86801000000c2c014020000d41c40c0117000043c0c4021200b080c00c506241c3d1080060b0042012802d0b910040c010748840c1c1001c1c14400c0780c0740e8058030201d0b0081403403800f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 888987670 1250 888986420 888986471
    0x40b03190f05070e0a050a200421060c050307080f04080f03040320030d0f0225050f06070503180d090e0907050a08101808070f2109060e04 61
    0x1007052185002d200d000d21846000c1d0140544082950500c20071072001808120b030078074001490f100d4201103010b06806c0e044118580502d915080170f041401110414400701142c8114800c048070140018405028039880e440c01900c0700f540b40e19103554050306420005110b81d07050304003c010000040c080b0400d8460070208491810789940d1246400d490414100980f1f001007a8225840380001c0b04c004014040161905028012003059642810a9000e0004901000c1110003016103602030140c00052180d406141165428658131034440c1c10088140d805000107400041084030450b40d42505040300e420800040c90518100b41d401811030000d40a80f00381e4103201004980d0701c200400c1360314060700000700305008442c0d0716090a582c990200920002103030400300300c2056800ca803d4805001c540120340c943c9000f1869441c0c201d0055191000c031001008104840d401b2640c204007890a035100352582c00302c0a0501d10040c10382d0202c2c406151085017004017200d55600c240e292301503c40d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 888988920 1250 888987670 888987683
    0xa0b0a18050c04210648050706090c03170304231e010e030a080901111e0306010507080d140a230c04050d0b220b04020f010c120e040b0319 61
    0x781ca4525102029100312035000000002180d0550341000c0c8540001c5d90101001044546d860304070244c1540030711480d080600410414411800410010b40100040501c80c25030ad090b038503140e40d910700414402c207010840200c03011042208200e2020408081c821340014200244d000c83c07480ca0765902a02c2038620700040030b1806840115501750000415444207000750fa0703c0c0d41307142000901041c2c0031112025650309280c4142584440e0804a40c24160b02400e47e80e4030710b0007509a98000d900143c81c2c28100902041008007003940d0001416000ea200c1e0700105607038004442c40303000301e0006400e01c0c40b100d01d007092007030003c0c4e1002c240d01155661025068120b40c0c44200080d942e02450b413140c0c2d08407081c910200d0402c201211003601c2406006130310350102000080c48000303081801340080100b00b41c0004100580380040c000c80c80086c5c145410204c614256446041803155848890042a4511100d070001e2515018080c1d82540603001042010b0b03c0e4040759450796007546014114 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 888990170 1250 888988920 888988979
    0x2010c031103040602160b011e15090b03041a041a1b031303020717060105090702070f09020c0307060c122a080403170f0709060503150105030a0b0a18050c04 69
    0x20841b0803074100b0f813180d004189107106680d6900c404081c0094442d070f51040c40c1aa1801090305040d041008000c0400340d1354481c7c400b070a008164075254030190040d1507421020b07007140c805070103d006d0b9620484c41188586011040d1000ea0010383c41302603c01d200305902900310301107102c0500192a401030742c00607200d0b822042400d0690034000660000000d0400201a500c035859001442034101c500a8603030030300b190b491108c00c0303850b0241d03801040032446a0040c00c02035a02507801900000a6a81c10b50b45042c030f10b5960003044403a109210030214100384092407200090b0321840125111807050349801d03644118120307100e4080006134105000c50480414140341c41045c020041240009400049041004144444150854084001400e100008200f1a1185c0305683c05481c84100103000e000075072006407001d400041c03800280e6507982e04003060540d2884000001021003584865589000c0b0381081e0580350000c0051130f5500c0100420480c0b250314410070400304c0d081c00b41ba140d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 888991420 1250 888990170 888990187
    0x403030b0d06150e100810091106070b010e0105190504111309090c140607060c2f060c270f04050406020c01050a0b0a2d08060702010c031103040602 65
    0xc41d07034040301001d0300329490001402d0301c00c404030004a0540d21084d54034030640d610707243d0948100341680101c40041c1c000510700158100140c000c4200f040c441e00080c40000c4801000c100355802c1408182c1da002005801001f2034001131841501500d0281c0e01031502030041d000c2c1c00c001700928482d071401640c1c1c80303106940e202142002e5680b00d4000285d01c5045941e90414840500303c016019110003801c800001590b07400c149100608480240019040904a4640ba402010194810001d2000c030b01400c0064601c0300941145865081d103da002d0684240c030b84034500301c00104188003403541084411080c0740b140c0800d1940c00a03101410080f2207a001c0803501b44282038441d160810300305010b020401c101c40d005424811500c4000300314503580c13035036a0020365240300d048540119080c0c00600072000b411440a05040400958550b03406100140032a002d0342075101c04200d81282e41803003d141d50a00401a940c241482d041c0034035009440342000b64400a4002000103500040804 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 888992670 1250 888991420 888991429
    0x2a09090b03031b030405060f0a09080607080c07170c0a1106030702070e0a020c01020417100908090d170c0f06070903050606090a1b05040501030f020f0703050309250303090e0702060403030b 83
    0x4000c1c20020709120340780d141101c08d00b26a5006481c004001c514107040108000d40c0014601c1d1081c0810395994005072501c0c1d680300c80c030703911040c1c059440820003500c1c002e42c0d44003800288440c0030f00200400132118181460205c06044025140c4100c00800a00c010140c2c0001c0c0c140c265003030350115071183d4a0f0400940f0081c030841107008110f5001040c0055200385150481081004910079140e1420305c0c00e180d0f00488139174120044c18130100744007c0d00c0f1403c141a440342142e110f501c21016808401d8610f1206801c140c210401a5000f002c00c1c0740040c0c028002140c01c22003e0910301c0c101421035445541b20300d4000c2c900c40c014034803d00011507842445e000304075052500000c0c555845d2460384020030581c0140503450109050050000c0c1c0e0181310301c02c5400d02d07100c00700010704080d4569402c8882d584082d040c0885071081030b50b0044000e030304100d0344a84041c07200780c0c8080c42d8034500d00504400c1e103542c01015204080410401030a8010803441d504c142c0c507140000d40f124401c00081d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 888993920 1250 888992670 888992677
    0x1204080c060a02070f0305151614130902030c0c07080604080427090309090501080f03071203240303080c0322080c0d030603110904020303120a2a09090b03031b03 71
    0x4031024640a000081c014041030074040c10480f5640c0b0011f6030327280240c03074103121a00600c0c14002694522400c0481301d00801414400e00c00d140e0074103030a66140242010b0fa003080d10f03a513a088a00056201e0710100401c154001001190050200ca107056154161180503d10508007070b901060842100102c0100c0d8003040c144403000200030b040d03e541402003000c1c066015040500d4500000401c1c040300006200e00900d0004004500d003031219900d40248003a03580d128001c0c140c568241d03840131540c562810b0035421700304204945091079420000c205240141c49024000d108000703000035051280c0d18100404e410702501004100540f4120229100b01d078201c005500520b900e980c20b407545504240d04580c0100d840d1000d043c030b05801c0182160040d14002e51580c030402c2254001e440007884258070030480c150000e00441014000c8415010030ba0075119801c0005070403039002c41d0040500c80142c103000000300402903507100869920300c640046070005080740c41038440c44810405c00c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 888995170 1250 888993920 888993929
    0xc0c0b06010c021e04062103033b010f022a15090703050c0a0f1502010e070e0601121b0c0f0c060816080f07050a0302120c0c1204080c060a0207 63
    0x44400c036092078440b4015868083da41c02d40300da8181b8600040c01c44900d000e414001944036824031207455165402e8000340220102011000719038166980304095000604512001c40205181c0700c16240c0c60983c00c5981103000c404030b90784140b140b00a6a284200c210400700f0502d00c44d0440c4040d0b05032410315102c07040010b040c1c503030300034410055602800b04503041101e10403c120303405c6a48220821034925054012550f03441260082040454810010002c14ae001030000150140d45c2d030101504001458101c00d00328990344090204039603000001c43d01382003101a0070002015903150703480150812410040400c07a945210728103000405000b8212268032180074000d04da036804000c0d010020032510202107604000c10130300303c1030042d0702e407511403c05104600815503400030180e40715004602540c08265083c002550455011900c0e1401258010951901c650803001a54680b2458880c035950310f12044c041000910000100300c101d03110122071580d15011b02035404c80c031b4040c1c10740c403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 888996420 1250 888995170 888995179
    0xc050a021203090a09020f070210090803040906140f0a140a081e12070c060804080d020307030603020a0f05011706040b090a0906060e06092701091b0503010c0c0b06010c02 75
    0x304a49000000001045002d50035149040a0342c1d58491140882c06002d047c0c00d8610b604102c03800c012325000c01c0014201150341007030040203407a891204d00d0340e04550420340500307030727210418480e800355029148008030b030889184281322840008583d641c8800e01c29001022800911050213581d5000103101a1401100b120780b060501500304980544403c1d601000b4040e00142003804100401103c0e045904682028041494981c1c102c0d101c1c2002030003502d00130003d00c410703001e540d0280010740c01040300d83d40204409007140104180403003d9804144003a082e0320040155982201540040c3d8907481e0804800f40d4a980c00f140141c22544101c03984840801c04008072a0b889910914549000e00020480036072143c10f0301203c0d00c0c0c155010381e441510040001c0c00c511010303424114825440e855182c0001040342100d080d03450244046505244007000f141603402034081c005c00404007240248408100f00d8406041e684600b1406001b00f81d90400113a9680d00070f480c0d40004c1750b800760 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 888997670 1250 888996420 888996439
    0x306220b06220f2313090303140901050702210f0408060a0e070302092e27180201050c0a0524150906010e04060e0c04080d0305070903030c050a02 64
    0xe07400b41c41d00c848041c10309520310071080041040402c41c0c0ba22401c1d603583c0c8070f42c0c0c00151050540030f5610300d003203c0956404640c02100c075440000c0b074000c80119520986000c205030004a49841c5c030104000c04881031170f894401008070383c0ba4001207801054007580f410350000310300c04042c40441d1284040d40038004074001400038912500040d942e214a2040c0c20400c048540036244545800d09480065844030000c00411380a01060f4104c104000740c1d052107600f22925512000d00752021540841344110070900c0c6e020110340711640f403840b4498802410086c18200d0100390b82000d4495002074100319003c210b8030f50385241085880006500703d021600e01d071841070030318400325885104900031028682d0210301c001d0039002c481240302c0c0b0014111005036541000444190080303145035a402074403940e0004100102d428054010108000c5403035555043c100c41c5440c00c3c10440354070302050301d85800c001c0d11661200384141500c0c2e15140440210109080542c41c005514801030342c030030301c030b0b0303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 888998920 1250 888997670 888997687
    0x2030c04090201051e0418060b180d0c060203030a0e0703050615241b0a02010801180204050607050109062f0d0f050a0b13090c05040e0a1406100b0306220b06 69
    0x5c06801102d03100d844008400f00b55444100907100c070352140b00040d10007807010303880031042030020412042000e00410b1051100d6158442c08039403c0c0d11a80c0540c1001040c032620007564010722040c41041002026050b26684c0d030941d0b580c900520008107070040203842242d96903800342d034807212820b07003011031001c011141d20100c103a0b0155540107501c92444104010060b40071400700c14064050b1104e428070303860100342c0004100150148501c2070f900300300c0494160755480c0a0700708035000c0c0740000344802c01450400125200500c4815001504000d10211804440940c550038990102c2031921101c5901c04840500030104007500c016041204200030103180b98020311000c0b10407544885528050b00304031080b1000c0c010081c1808507251820711007402c0580001410b00300b00c0d0b045804640d8591615410420303190021580781c0c000340c003880300c82d0700103240f1440a0131369010729501c0e42c11316500155210035101104d03a0300300152a10144428803507800316108000190440d030b55008007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 889000170 1250 888998920 888998977
    0x270907020706201009080904020c06040618020306010303050a020304090614010f0813030c0c03120c06060603020a080415060f060c03030f05072001060f090606030e0a02030c0409020105 81
    0x1c0c02224009070100c003005021850f51100300d02103105450140030008962188036025000c0b90700f05883c0741c1410003505a080c0c0b118030042c40c16401220140046050500d040382c183c0c2d44806840907540c20a000840c003586e80403501c94112549402c2190b0381d18090382c5c1c140c4c10b6000c0c41d4802c1e0452850001c1c005054409081e0b2181407841c2644c502c0031a01d26841c040e100e04c80f0a454a50480710349a1413600000d000d002c1511802d4019a02d5000a07940c1c0c1d40e40c1c8400c600751507102400601e01c0c1510204104003402400b000c0e040c241402d40c28115104401055000010000b60200752080f07400360048010b0740c008000382413406006640d182d2121000380005403d074074100e00107443c2600d50000c052091040c1c502401f490340c1d0740102109800c1c00b4007007442325005d2003405550f9944000800384c5080403480c000740550080410040d00d0301c0070141c100c0754051040c030000c0e00074803000030040e50003280754161a5011070300007849030454001207035280502c403032402c1c80a0705001e14200d044d10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 889001420 1250 889000170 889000183
    0x1b010f06031109040b06210f01060f1401171302030a060b011b0206030c1b01050a0c0906081e0c04091a03060c0c0607050d24030c090b0627090702 64
    0x48103026040510141840070100f07003280d01030803009041d03001c21020f1900c0500091003d103190f00700e064031030070707015800e04040120060100030b07907551404003c8964100044001020410003240c60070f1003203800a041144810305101220210800059640074003001d64415903402a0840e0f105130110f00d050b00c01059451021800b061540c2c2440d00080500c0451014440c0d01a0039141075480d178110070149a007003025042540a4484c20fa690318030070034443c01303110b01d4500d000070440d82c88080e40640076802c5a0044001c0009401c20080c000b003029040c000d00b8030054144007500d5030303480001c0e000f5015542004c030308641031030750070800000300341710499500204a041e588580c8815000c06803508c1030b441000d003c3d8220f0000100c1450094001d02800c5c0070000c8007040d0b80441100c00110440c07112595074594510324800d1060000c03e001c603002900c1501000c00c10341860348000ba419000d00343c02008500c42c1c0201b01a111280c0031070003100c440c0042c1a0b80014140600080c2d103d06 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 889002670 1250 889001420 889001423
    0x304080c101d072601020903151b03060f0d03111002070b010f12080307090314150c0f0d050c130b0d0506030313030201030c140c070e091c051b010f0603 67
    0xd002c502c2e4100031200c08541c910440c0c42407044c4900158000e203203419040030154540c00555428800100ca40c0c50074801414101d62406030403001c2d18280014442d04803d0440080c6000c01c00c1c0100421394450b031841d449800c4084078107014403a414a0101e8295203e106142c0f134034010849005940c02140d005441801e201d004a020300d45e8841c1640d103c2515148510303441c28840354000c10100340d01400643d044034503071402c100c05540325220407081c40d5003080c40081962044c650360300315511140030075811110218070b007440d020140d030303184480d4050340d118440b03a19903910100304285450011035042e0340d81c00250010180d919021811241c0200c440c1922640c14400028100d180100c115103141610703507204d188540c1542c004500a0000303095480511420051260484051350040d009401515006020281c2050b20845e01c0f6200a031450303045038019840310a00e04800100d07808484040d262058645420540c40031240c41030080c80c03000b5500e013000d10030f86110241c1100b016603 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 889003920 1250 889002670 889002701
    0x80c070b13230607080f1306050a031b02060a15121a0a06050d06050a0e010e0c040c05130e0603160306060510170403050a0c020a09050601020708030406020d050304080c10 75
    0x1200c182c0702180b00455580715560780110100b040e0000116a600540b0a80e213407001c659040180114203a121442141c01a801013080824400c00030746c2e15009480d800841c11040c140b94840301d03100659a20409050500c0098230342654242c40b954114401c802001c42c201f074491901d06604049141b03506d19030000c1400d01809000841c9865203024020440301c0281c90200da0464540f6800c0007800080c1044120548a0307031549039480d001d0240039a1742e41d000c00a401d90400001c10042195010142802071202c00c0c40383d8418040084640d40480381c0050040c00a591100b0000e0f05001c1c5a0030585400d2005010100070b2000661145081c0d45056a25416041400405072a03140030350201c0a0080319a80001e000284901d014002d0520039061404803039a081c0c1c0052a01403c82e00315075200c644d52001c2083c40c0d0380c10030000c2c00820398a0091442c1500b881d000a40304c440c910000c0b400e000c00003010900f004011400c8480f514510340c10b480f5880c940030f1840028044410748a10329 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 889005170 1250 889003920 889003949
    0x80d02331e180304150c02191415161a01090203071d060901110c040e01090c05010305091c090b04030318140604091505030a0b0a05070309030804080c070b13 69
    0x1a1000c010410400b0100e400640c1403501e8200c031384410f11120803101c0100003982100c5401600d8100d00030703141340307990342e181030503207041801287d1607041c0c13042518407650700f42403c0c1380e025440d034003101c900d5201046018901012824545003501641e40402603605541c000010801c01590140d40141d0165403444651400d81c2c008070044160340404550080d810040200c4940c080d0080e508440303e41c00c113940403640014002400c0b46c50300200f07002c55945038a1400200090050104050442420f040250741030501030385c1c1ea940701103181c0301d0403042d00301c0704240b1481c02118508000c0031040c0119940d96200e1600501000020340c00b0300c0240030a00020070490744110b01e101c3c0404000e84108e0520780340600f010060107981c1c56a0041984113640499030b43c03000e00c0760704501d50040906a045051106200b0210380c4010b014600b01482c080c0450000707540800c0d0544c01541000c4c10316100d007101540103042a00075445040741000001d0b14400c0000102503d00440303200d008103442 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 889006420 1250 889005170 889005181
    0x2250b0108010516081008060a02090414010e0c0715020d090b2a0f090d03080907060302070b04120216091e0e03092b110901080d02331e 60
    0x3a83c40a560004043c9160200d0492080c0300b80c0d0415482000340880c0300a4039175451035281402002da60b110031040d0005015682c41c01e06004907101d100302d400000c45190f14090700402c14aa0180400300c0b0284005002e0050040035021a05007088440046544003082505a4024040400c00b2034841700250300081c0c00380302402c3d00910610240240d800c020380310400c2d54440744d01c00c0704000b84502c41442051010f8a0741d1406584081c070035203c00d4201d0a00d002854500103440e4403c0f020540100165400900c001409642240d48214440c0d5680d80d4a44141d00740040800c1100c480005000009000d62443e04100b520080c80000c6462603102013401d4400c0d111080304001c255401000704900c942041800141c21001800a8044070301c8401c00d000002e05c00f940045e581d04002014084140c03900070500c2d401002c0540003481061901c2c00069201d068081d060300c43d54083c440b000d982082590b000a40c60607a1500d502018a4011401d14101c0c00341140d25214042c00e400161 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 889007670 1250 889006420 889006423
    0xc17010b07020406081b0f030717070603060f0308071b031a01090608030c15060d02180601120912030506010509100903150c08010308030619060804021219021302250b0108 75
    0x280300c4504100707803c11b06c00208080c0a4003058294180b40c040c417844200041110004000d0030502310410040c000161504400506481c0e03242c0060103458600c600410000f40c03100c0454070007680c07010624071802c80c5048000e0400030140c1c0042c001d4040400b0a1540303d903580000b5050721202541084103513200c281c01039690141040c42140e6a02c151402c2c4030888203d001241d0280d4010440e1450710b289a001c2282da21300301180203544840f80382481202c0d078200c50141541805140108020700c3c00c6c0c0c680300c4401d800c0703008031024155184003180142c3d10031400c4602c47c1c00c01802d05940c03442400c070300800c0c42009110690340e03140e90030b070748600c2c58589000c2c5030321040c410f6556400c00e90070341d2103014941c2d02c0980455440941e1160003546004c4401c2a840108016200c0481514013401400071925034040c18060f0758001030080018003290912030a03602e80c050ba4800030f0f020b0038035880f500034496280110315940060785954041d00780440342407081840b43c648a00641d13646d003080d5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 889008920 1250 889007670 889007683
    0x904060906240b09030102190c1406061008070c0615031502070804060f0216140925050c010f050112170a051c0b04050f070f02060606030a0c17010b0702040608 70
    0x80003000c0d50b50040002d01402c1c0007615032030000800042c40d100081200460296440186a02180d50349201c20140460260011450020030003d0005480d20800090140011303407102c1d424400d20f040817138445480b13114610481d55105a041100c51003009820203016207074882180c0c000c07120318000c3c5068980d80240c0303503860b40c03004556041508284040d10541c40d510807460031403180b80314601381481d40c030310148024542550f94514602501d01807201001c2e008021031030105800c00100041c8007500303011106071019191681d02d84410386011809001c90b02c1071400c21a050034008074030021a4203229101903c281d002c500d0600554501081c14000d102106022450500c9481600c0300f402c00302c1d039040a900e5000007900201040000e088403010b81d40210400c01880c00c1003400c1e1341210352100d03143c030345000401030b52034502d000841503c4010300410301c0c15111031004403624040c9002c4c03429141d01c00980849580c40350080309645cac0104400f640f04506042c00020061b4020600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 889010170 1250 889008920 889008971
    0xa03470f0f03030d050c030106030f0e070905090705030a150e1903200f0a020f06070f0f060e0d03240308030a1e0608061602280602090904060906 64
    0x1024601103000100101c600803a100160180010483d107800076065115052003441c101800030b03200c0d41041c4005044450b4080290155454155250084c060015100007142e481c5400420a6030399060641c0c00e01e05181d110542610501800c0400c108248a0310015081c00040c10003480000355a12542c80d2010105407442031604002c10740070a02c580340380c0707950a144102c020b0130b0151480d107030351a000220f80e00c0d040d5604a401c841c421481c1040d030110028204a034614202002e603110040400c1c0c2c0b20f4001407889000c81d041904110240c1c000055440120302a1101950241805000381c22064110901400040000040e02c02241c0074581a40c1d0051a4182540e50380703c1c1d944000c003020a0b2102d0b6055407001503c40c010001c0c06108040e150300c10280065040041d01900341c0207802000b00103541040300070400ba0b03040302d42001da0001c40030109100c107004c9810700b10002d00c5055101d542011442003000140071454201d5403240748140000c000040d9021790051940318000f80 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 889011420 1250 889010170 889010179
    0xf140412091d09010615020a062909150d05070e090a03080c0a021507180b25080c062d060a090209180112050706020c010f050a0347 58
    0x1d503881942c10700c041581d102c0d0411000040054448088450080c0c4803000c610060b40020320aa040002c2c2d17008102d81052181441c03003d150904011804540d00790402034001d8449400107074064400c03001414035a030000c0d00c80200b101050034242d40700e00780740c01912440501d03900416074400d0001f401081c25901680d03245c3c8241c40744902c8202d958454019030085128842da440c100d1514002494060122030710358103131480403030300010300705000ca50010015031000e10403000268040c69020b204111a80d006100c551a01d00d071501045c0201e0003140207a1140004021022204400250918216013401c0220707907d034481c180319011084503001d411026140b010030548500e90054580720780d00800d02d00d000440100c080c2e40022090340302841d020b5940d4000020b0010901400000d1718081c4050b0410040940c00604030351018028402004000500311150301d01c40d5010714000c9103100d0450341c0d41d0300049820075100d803c150001d1005800c1411031011400020314540007043c0c0a003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 889012670 1250 889011420 889011449
    0x8180606012d0806010201110403050a02010807090905040b0609180705010f030212150f0d03080106050702040e03070b0a0509073b01091a0609010804150f14041209 72
    0x500442d40200d940c07a01207001c0007a261100c2010142000444600c0e42039654000580b910100090944841c840381a040e00410403080c804070744041101c5a0068080c2070100b180d490360316003120042d015a002000c40d83c9450305101c01c2041307015245010750011514a91151030b0f00400f129140c00704140d204456101c1c2600708801d50041e44216a1964540ae0040c1460303010050003040a400300c0c2c609280d80d08036415090b0601e002c14601050781c80c150b8030450516020b94003c1d2601d44107000e0541846000305c0d405085584e56080801080400c02c01c0e81d4541e6407500e41300590320000c1e0380051801e810305001444802d030006848003203840051005000310000309a400c10343d007c20209010008403040300c00500000d070081e00d4028040c050000910140101c04041010080310f0003502c50002040b2503100c03a82e00140245d00650000300300c0901c0700d034141c0f0250080a00700300c0d40c15800c0c10507803446603018403c500c0c944103a004083e82c2c1c03c0c64040072421101007459009080c502000203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 889013920 1250 889012670 889012681
    0x803011412120d2a271215050c03070c0807020a06031505040513061a04110408070806010f1413050a1e090308160c1a07110a05030a050a050d0f050106081806 69
    0x68828280022808000010440181038031840e01c884a42206c01c2c8805109158402c2110450804900c6111080c00b0409404c0a560507409403002600550070001e9a081440502000d1000c0728070780c1e9401482000e440740e03584000345c040c02802c1080701650b950124001018105405407a1080c817000c0045c4118107115a100d0b00101600248008101440080c040894950f80305035005002a0280540c0382d5213070080291911440b9006030300141c21120040100b503400014420507500e0b10f0002d41612180c900110b01c008503c0903040d05002e0800c0c007070240301c202c1c40d071000580030b0345601c404851034200a02001170341d00310341340180040c03440c00028803025001d80e0b41010b140154a4050308495158071140d011019440c05500c1c49400c150502840c1e13904586680401e00d40c1c400a000040020b45030300741c6a01481c0c12400c00c2c000c000038402403882c8220100d92150380c507008200300c101c24500c24500104001d01404001c103088002040c9141c594100c51900303001400d00a0138541d680 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 889015170 1250 889013920 889013927
    0x13020609040f06030204060b03250f050c0f060f1b030408030c1b01060e0f15030d110c0316061418150903060a0506090709030803011412120d2a 63
    0x42c0d606003814a43e842c0408030041c1d549000300e1004200701c148440c1c880c10041910720404098003214801c07200d1000800800540010b64803204d1040750a00b0303070310343e0350709440c1c030b03080c4444210018400e01072407080003858526044954041d90713000416040300e1005180382c0c0c519200c150380203801ca1405000045003290240010300301107154012410f04000210840c5094070813507042a220761500c481046600c000c50114554081c40c10b210410b02d280042c000309494128996449041180402920100040400164006402c080d0484046c2d403140360815480321070034003034800005e01450b60390b0710b541702c00c1042c1d03021010a1101500820b0201d410090390790b184074000041140107004400181d5014003580344200c000d0310002c902d0b490081c0421403e100000d00000a1080580e014404030f45100b09a0341540c111a024081c2c40d810310000a070704d0401d64414424920a031000c3c108101c0c011009010398003140d1000b031003204011506900e503d44c040c80d4043d8940c070780c01506040c0c80d11 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 889016420 1250 889015170 889015181
    0x80603030a0233010e0f0a02092202090a081f020405031b04060f060c0c0609080a0602180904050a060c05030c190903020405100609090221180714091302060904 70
    0x804030030352801070a600180300d000701091780314203c0b0401d441c0070400094800c00c1c880c0e40c8030301c07044411460240810005990180001200180d410b544400d4030b001002d02d03412030b8608140205035504013951805500d41c4c4161007600c60101c0410301480c601d0308941402600c00350707900200988500355103030545281c2d40340143c0120354015150701000401303412040040001c0c1c2096980c842e0500092704000303800301c24981c011801c02000b07220070050940b02144504030250310510140c0d136854010004080034030030020b17080c0c0c045a58010700080100000340301c240c0511551050040e410f54038400e075224042202d4400c250a410480c4698005c0032900f070340f028a8050814020a607100c1c0c001c58112001200d0304402840f80c104103011190708100712500500008030190710308400700c1ca48e00c0180b00701141101803640b002000c2040704035601020b501c0320350018100d03680d00f03994803c60b0405000c2d1040090240c01103c021904070b8903038004140005401a0080e441c045003c402d0000501 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 889017670 1250 889016420 889016473
    0x307020312010b1803070605030a0f1104240f090e0405030c0601030c050a0519170708060907090606020f061504020702040f0e01051015080403030f090501050106080603030a02 77
    0x104000c1e00302038a0010301a54042d00c80b8082507621040b00d006030301140001c04c80c40a10a5100a50030044c4551007030889500c21901c400224510210030740d00000f805000b0000780001c0c10104010803081d04805c1500509a900001c0300c040d02c80c5c001d002c1d0b9500f0402e058082c00241822400e2120780c030303118021500188900e040ba4584100314009a060074400c0e0400c440a5022010410880c508203000300c01610044904001e0f640c0241d00c002c270b4107501413150401e01d54844181c030409031380901500b80104401e02c26111b151a00c00126601c80c2e40324058014050300c1c00c003020551034800a0b908019402807401800039480300030b604074a88000910a0f130f481602004083c0060315a8000c25010152844001ca103410080d118182074400c0145100c1940c08000020001000e0f140300c0c03d116a2681d0510410941f20390404030003030308200c43c10007502c604203050801003003415400f0314122045645e0381c0c0700986810042586a110300f1000340010307800840101c001940064144e103a44 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 889018920 1250 889017670 889017673
    0x1b0c0209060a2303100c020a0f02062502031b0643050c042f070c120b09030a05040618030c0e09010c030c08011e03050118020f040203010317030702 65
    0x2e81d0ba5900720000300c0005410346a030440a1030f906007505040013200c0034840420070910101c40c0402d0000e543d40c682e16000b60030f03051114400b20540d01c42c201112140b00c881e203079200c02c04142034aa0307404110b540f1000c9010b4800d215451200d1403041c03c0c00102100e00400c11454140c0c0a40312640d00241c0d11002e60902d0126107160703d001400040c003540c7d0508000c0d005000d07280780c0c100903042030020108035000324100b07001c01000c000c1644c407503001c5400c0b00080084180c0c0c0850804054000d0080003001c0107001b1f2008101d564003a610040d59a2060b00303550001c0c0e60703c0300942c0d1039008074888180821000e200510881c0d000760320808100c0492401e80140955039101c5d898008515032000401e440364405108040700c082c0120319181d801410188040c1603802c000a0010780c2c1442081c4080400010080285000e0300240d0000c0d41c0240080c030054100040340903503204a038030200c1c402c1220202144681c200b600a5904803034000c1c9071881a880c0c0002c801e83c15500042000c0f045 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 889020170 1250 889018920 889018939
    0x40f0b040b0418291207060807050319050717090d090513090204050f041407050d060b0d1209050a120203071205030d0905070f0b0705210409020c060a1b0c020906 71
    0x84026800030002080400014541100b541840200c00c6500b17482040741c2c0140c4801d00c5800e8214640303541088551401c182c0c0d982d03d0381d5103c00900d04c102c08520055040c03106100d800c43d4001403040040c1450007006215450340c150480e41e0380382c542d00b0710300425002501048545031602034060a80e54211f0045414116a400242101d008961f04680c000528090000344000c56420b10381008030b8000910300c00f820000010944003004074003c1c07010761604c441000c1c036140c1e00307000c05200da0312480340001c8200040010f86545aa8041c00380550f4212400080340d000e0401400801500030740940803013804d051030086040c41c03220055076544030070816100850317410720680c01d0003405000035090041c02c24070f40305110f01f00c44d80302a444074400d00140000c61008541c0c5040c5d0010713460950b96038110184c0311b90b8070380140d5100c0e02d002480420108928440443e0a901c40d6040d41820407410341c0d030b102808a440c510071040d0000644a080f45401824236400f0590459002040141e4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 889021420 1250 889020170 889020191
    0x4030615030b0702032b0e100e06100b0702130b0909150702030a0918060b0304120905270709180b091b0d050402040609020d020702030f030301060c0809130c05040f0b040b0418 77
    0x508480e03580e6044c42c0a0b41c80d0800a449d1030140100d640010300d142d242606d80d40b0b081c1041165020f1a140a03120b2070a0707020a104030718550303201c001030b101d01800d41c1c034543c5000380f8444d848002003640d540b000071480000540507803011003102d02000710307921240750031030400c000e2200f52040180c3c500b4030700350343c0c0c0d0002c034122420300d001c0c0d03105500c41d4900c40301054400000510206059100b640102000301881c3d1001040305503c1e021a80c0501c400090303592096006c40300c07003509030710a01205002d460415910360903a0020809440300b680d41c0e1f6200c0d214140d64001c080050703448400050010b10900052174442d810854100d80000e01c045190307074850044e441240e00c0400414122540000c6040860a040c8810301c407002c0d10002840c00c540c9401e00203019000c03003002c001c11000340000c408410360303280324204000c0041d020007040340c000200d10242142c0d2050040d0b80b481a400003000448006203030440b8107507440180401d04092912000400d80441d8001e002c0003107449403180310 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 889022670 1250 889021420 889021423
    0x7090e150c0a020f1b0f0103111803010e1603170f0a0909140c0307050c0a1e0512040803180103020c0604060213050906100507050304030615030b0702032b0e 69
    0xc0c090a07004850a64400d16079002038034001d285401003902e42c00c0b002c2d51000419070088180c201d820b080d01c26114410703c03580128010004040c01444108001c10741d00307a10f01c0404142a40c030f40b0150001c0211041090b04282e68010421030b01e100081078050900c0000d80e8600c1020400012040c0b29080150800640402d500310f100c255002815001040000c6400c0b80141000d00710b00420401c1c09040014080d2854403000f4403103824044c2c000742d035070441c000400030100001c0d0051051b904144820020b000c072502410b034281c0b503920440205104107412034003114121103a64004504c1c004c0c1400e040740703500c00300c402c0d054141a42804a0080b0b0042401344c544118415000140d40c2c41c1c000440401500080c0c00c894003c00c0c4403c00c005035520740000401014626080503512695a403528034507600c595000184854206801c4803540324032a8041c00a0760b1159960141e179a0750007004a90b80d00032400c401031104d00074800d440d65040319800d50b508014110030003056000e080d03903046 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 889023920 1250 889022670 889022713
    0x2703030b031f0c1b0c030b060613080105010911030702030403030c0309030f030314070f050405060904060b1603020c010c020306181c02070f060905030607030203130f110301050105040b0307090e 85
    0x81010740f15014000800d0b40548880c1d0400701c1015080c02884603038490011540c41d50200509400e03171030340817441540d5020107032042401100305640d0075548910f03c4074041d010a118105d1810b0a10000c6502202c0c0d00d000c0d644102e005074011400c00c0e2a40e02c003100c410904141c1603090000301c040100c0440c1441c010310503018003985001c0740705c5100341441c0610104c01000d9400301310401807409030a99100048404903141241d0143d22130505400140040070180e0103413440020004044e178100003039492464801d030090702500e00c8009880010b6031a60803008000303500d504901c00080d40c58400caa1921041c1400d10704845460210341272018010007440410702c056032040608100d40703061102141301400c02ea00c1d08400031440c2402081d65803a0161025082c59004800208601d070100100711003036401100a04810946080801c184101152403a000e542080004034a6003880e0003910302c5404003030010142d10340340ca42c2c000004c22005441d00303014001c09181035a45183d20661 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 889025170 1250 889023920 889023973
    0x1f0c080307050a0e01020303060d060e120a02060a0b061201060f140417242e0f060e030a0c1205030408060c19110c040b12060406050a2703030b03 64
    0xe1581c3c0c3ca000c100050040410074480e83c0c1154800c00410120340c507000e8000e041070381c0c406004204081c0780740b40181070804500d0503000d5a40c000c9000001542d000895500030041840c0c100000c8061f48107100d450f1051552070106078115030700400c0101d2040c407142c01c403e4000d01c0c0c00b08080b84001001e000da0340c400d03801541c420707c8614030000b5041090090400d4074044500c0c594500220780403440d02101c0003032002c1c600c505c0030b52850200b46212488d40450340700c0307030232100c1005031140c0c0a0b2207618043d000340f000140f2140d00107000760400086080b00c50f174000d070014064501d4003010803014215080102c6003400705100024910b5005c00900f800f4002101c04581c0ba19072900d401c01240800c0ba248000b00700d604201e1030814840455800c0c04404260b402081c800e0803140420b1010f1080f40146e18207205d2241088244000d642c0243d009240c0a00c1c14080031481c0400a02804c1c000b6004000d0281c00307090b420700190081d481080c00c400080d0603250480200c00c00e0a0281c00c3c1000c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 889026420 1250 889025170 889025177
    0x9040608010209030c0904151d1002030a0e0d0c0210030e01020c01090b2a28030b0406050406210c0e130201021507020d08040c05040608030414010206061f0c080307 72
    0x515100c3c1e860140241c5a01e04410b07100f5074020315007510b82ca129040340110800c4055681e04072080c3e0310004e107000700c3d94030344100101c0381a507102c0c10108000394800c441c3c0200c26460046034042040c0c01041c6088440003e640c3e52a0040d5207400300010a1810b0304083c0c02d1550301c0c0001d0314050001e0024021b00115200002002070090800260381032005100d18a024070358a246c4211034002442c3d1041e0403a903081d22600d451444003a03070a03124440300b1841e4011500035010002c030341c0c1a00440e00c200021742d0184903050740c4005100940d4545d0082d2881107118a805074007038050400e20118190080440f1009a03a17600000402c084007603401c109501c100640d49029560100a02d17901c0743c0c00444d034030031285081d0074025181c3c00c90302c06400130400e200707001c201840460107070840600f00c010410000715580d81111aa03951080c416090841c801c6801c0c09015800496264071640003c0c0c60030600000d0004068415010310140314148040f02d0071050100c4d1210f40514450800c2d9103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 889027670 1250 889026420 889026427
    0x41a0301050a060e130c02012a120203070f11030f04030b041a101403070f08030406030e01140c0c0a0c0303031434110607020304030b01080f03040b070305090406080102 74
    0x1050150003202e07034100c0400c1c40440703003180c40d03035032038008205039000c910a00c000740728184450101d000d07044010304c2c000c0403a4110042050709004428880f984840303500d940d411010100c4080059000484081c40400c41122201d11811300035852606058000c100340ca20340070b90740c070780c80302940c0140d042541e501003907004110400103005d14404c507418003803800b4102032424006602d01103d0341e014400881024219001036605d003041400090940340240c000710907111015280e40e138209105807030000f800c0c2445405c2006062081c100e0380309640321080010703a1100c600321031a0b0310400c40d0070014468021000086a00c1444100280d4030a035000300d90000f13404004a0720f004007070000ca40c1c5900148000d2000304840118030014008405024808401000141c4810660102c1e401d22400b030b141c01c020341e49602000620549200da054015541d072039041040c0d03540280a0f4900003580100418081305a44501170070081d4444d281891038413400c2e20216090392260b03400140142e4011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 889028776 1106 889027670 889027679
    0x1005070605070f0e1f0e06070b2701290d05010204122a0b280c0b220213060302031e060c03010b0a03050606041a0301 52
    0x190030000d502e41841d0241000c00c0303002c503990000d00c0f1411034a009141c11941e00e580780600c1000c0d520075501c50711056036216100c0400e954030400502c045000a11a1003840340b04484000c800400c6070300210f90100000404450304051383d0405113948010b80401c40c00201d03e202000030070300b4210310000410400c151061025009500008011030f47c10151241da01c0c1d0203100720118145855a1122081d08000d0170a490b00f002c10314040800c20901c44101800c00c0d001c00c41c0c1c0341505100000e150410084e00c0c1085900420720480001c0c080c042c214161540c08130704100c003026400d41400d240f2610507102c1900a10440f010711400c5040c039900e510a002451307014003155003e42190710300d2800c40d10320300000c256a2081400080d024100d00058904a54400c2c4500342403041c2041c1c00e0b8042c000003401c458210000707200000e6826415500d40c200c1c0025020300075aa035050 = true := by decide +kernel

theorem cover : BRFrame.Cov 888848920 889028776 := by
  have h0 := BRFrame.cov_init 888848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 888848920 ≤ n) (h2 : n < 889028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
