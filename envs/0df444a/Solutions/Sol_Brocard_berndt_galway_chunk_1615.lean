-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1615
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:52:35.724182+00:00
-- url     : https://prove2.me/submissions/d5ebe551-58da-45aa-8fff-dcb2b09807c1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 290287769 ≤ n < 290467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 290289019 1250 290287769 290287783
    0x8181207020f01030b09130b010902090f060d0f06030b0f090601030302120a02011d01150e060d02060a020c040e0705030c0312090108090f0d091404091a06061308060108160602 77
    0x4121074028442d600440100d000e41031422034168001c280c4018481810b01c06550022854840eaa00314034681e0303984112400c0703028002c94140c019040480d011100d1a20b100213080b0309103180d40000d46000703026147c000315105074000300d0b5248248030600c072075420107686a50340300c9200b0004204540c1141d500035214041120304610109020508080d00c500030b4010802c016071584110058421203840140a8002d00c50054481c0036000b9020901c00b000e080390f42e00c1048040c220170040984d80d424031600d98001e030800da00314022004444116a03e5000b040b5003060180c1c01800901c0c00d200405003004488602c282c0b09510040c44201c40485d04019035544003400d080110f042e81c0c48010050508140c44140c003200c0c0181c80c086120300760402d01d1003050746c0740400700710454501e900130b0004403103000b04081c00a201c65080545072801035000301d9882040604081d09001c1d4202d520201903401d0340003201036412103001480012420020075034000700c10313103a8101d094605007000e521010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 290290269 1250 290289019 290289023
    0x10c022803200307021513051c0227130b0105010c021c06020712020a0b071b060e03091003050915010e0f0402030309060a0c05070503120a0806030c0603010608181207 73
    0x182c10a00070380000c4144259003c154010f807950100030403150380b00c3c0c240d0380310010450400c41c840c0c0d800308480c00d00243c410205075a052484103000800d402704007109d42500b03100c8441450041e100f00001c4016000d60707001d200100035242d0b01070007918007046d40380c505820242c10494500c0c20140984d441d0101304a54000101c1005190905800c20b440a0b2195401c09860142c000c1c40c0b03228226400180d241c4424010b06030510103403182c110407200541014000a0000c5070745e484880480c1d15a40318540c00d001c030800f2030f03143c15041d401181c25202065105c00c0442c2c2d0b100204090784506005244e549080445425810b606205005014502c06001074541e80c048400260840d10100704640c03a4001c01441142c84100100780101f1844070030710704546a0041402c0054942000100d000c100110070002c0d6041c000c0704c1104a40800008040d50b91500c5420311140f0981c480c03600541c06040d184c0e07500e0b0303030600d440510000500d080101c05103040e80100030b40c1e00c0030003040080d100055 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 290291519 1250 290290269 290290307
    0x7050402091513030c080309090403080916090204060e040b061b15011205010f090203030d0b0a1203091a070b0c03040212060a020d2910050705010c022803 68
    0x510200340c030900c04141401550b0070018001e01001e4020990f0340480340301d160b10845040e2200005c0d6203034001c00307143c03036080000c0401250009008215040d8850b0490f0116902c0709824850a90503042d258440300710164009014000680c0c044d005154810091701d0174011000c030b40c0c000c65841e2140d80320079011120311015103009500c0510201104042d580e580e04480d50b100d210301c1c00d134501c10b04000c4900c0e40c0f078101d00891001044c010161440c5e001000745003044000c031070032000b86c0200612941e10401c1c00300003003100c0d109010000610350190707941d0320308141805c2c0e503250b081001d0900344030406418421040042e002402d0b0551080d681705142d6140d8980780702080e1039000c01e4034200c0003070055008020b01982154041d20100c4807001007880085103244581e4020708100030f5000f1220303940001d0b0307500341c100100c6400002032103107000c510740855078aa480c04c560503000030307000581050f0310201d108d4070681c5009405854000b4106000c5e100c0d960b0140844002e079007090b000d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 290292769 1250 290291519 290291527
    0xb060a030c051207120c03050601080c0309030706050c04090b0d0f20030f0604051b210a0f050a021f0f03050402011101020f130b0406080c250b161107050402 69
    0x32440b4509969104803418000c29150404c0140541044180003030010142e28054003040a2442802424081c140c103840b00300c502d07101d2008420480d0b100510a16140c0f00400000d030014079076200d903d22448520801c130740c84038108800d25085d038550701c0c85540315104c80d000030b00100c0c00304032000424079480b005000c8103030002c040312070800d1104030043d5454011400201203034040424000d11551080d01622144030800c3e081d401c12400102c012034002c1074036017640211350004400c0303641d05503c0004a90f010106651070106114032208202e07501e40000b0b000c00308505040d4851041c06c80007044d640300c000c0c00d00390000c000d4001c108099003010344642c046410b41e4010005c01080580b994003d40d80c80703d20b06000e08441d408003aa01e0314441e00440009400c040c1482524151540d070b2fa01da4240d41c851a003080c0064001c1500c4c0c0c0350014000070b100e0f460541000d1401050351003070000c40c5992805001e9800c840f007130308032114203105031400c04640a01c0041001000d90b03c6c225801070715 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 290294019 1250 290292769 290292791
    0xd050a080a090c0308041e0e09030d050a0213080a03030b0402030c03040b13150204051504150c032a030e0a27020d020a3603030c022d040f0b060a03 65
    0x1081c00d1380080c0480070005000b040700303100300ba41c1c10000500c500140f20615550702c0c040750258400c441c11642380e001400f0b056420002c0380c004c2c1d900080c008c0c5025050030701900d108203801030702d603010015907402a83e6071000c25405001716048080200c800314211301e0500d084007890300c0020401001065802c000400c9508080002c1b859039400c0303440900c000102e511050007c1d80103018580c8102074645a000d0140240002c44080e28240070144820011b5a4001d480003110750108905221000300c8010780341da001d106003001340180000e0b00743c1b408010709010349070105000d4a1130040000440c01e002101c10700c8101d540c0902d0b040680040751191000c1e040080c02420301070311740e4500000f138071201140d1248451111040d0b54154040d400c50316502d080c074000400c0c9107011030b020b4503041000468010f03103101960f54009081341d000c81c4082c841c10360b0304200510f41000042c031075503405211410b0a00c5204010585203400b00501204031001898500800c03044104140e29180b03c1c41c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 290295269 1250 290294019 290294033
    0x1020a08041202100e250f290d0504020907050c070308092b02010206100303120902040b0d0c09050105060a120b0d140f01140609181614030d050a080a09 67
    0x7044403030f400300714003171710300d02e2640c0c0350341030040100002e543c0c940c40306074581d404c07a090904403030705007049449251902032040300d074040382462543c223444441010502c10904400404040c10071240000e2945440d10422282c10005403030501008010300c400940f680c0005140000c3e2a0892440340d00e4040e00c00001707412401a032542401c0001d83c660340030115083c201810000c0b8400d0f025a48581d82d1901c0308141d00c45140b00250004100c22268902c200c1300f94407045190b400500081440d034030b117a000c02c0c84048400d40c02c0714444250360080040001c54450203000d054103c0e01eaa213441c2800c64004c02402c40c00c0550307a8099520f040301815a900d020509880e154041c44103510001100600f940b503640c40c1c15604029400c3c4031811410306211440300384650402002d868964860140c4081881d800400d1040584105000f003100c0d0400020b140300240349a040390792460502d02c080c982841c0c0311f91459814041c09102069806400803070080c1d0104202100141016107814204 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 290296519 1250 290295269 290295283
    0x6160903120e060928050105031006030c090e0103050607030606051602010e0a052d040b0117090f191b030203060c0f0910080601021b09070f03020c011107021201020a08041202 77
    0x15071000303105921419015400d001c8140c0c85c194181a00b00f200e946000540d4548001c82c1c5445141c0300180f020b1101d04c0c080ea200c200700810a103040d5450a0b1a2141072290901c00e800c103403481e500c44020080c000303905005050140070989089414682c8180c042c80c940024900024107215242c0031032407054482580310300007072500614001c0aa10320300141002c0c1c205829506d02171590240d00040c007420580223408141d0f41c1030355145202d00314510034114000c005000f0032807134001c0d482009440b10040040c0060485441c84402c00040c1624003842c1c0c41d0394103003a00d185d5942d5000100013590f004a0001d9101c552008141d40e139a050707481078440c1e4420110200e038019980c0c14080751080d031044045104030f4007a0220380c07200e2642d01d0361004a091040d041d50740408c920300050780300d5100f140300c1c41038400786003000360500c15403503495829203020b0200b500c0000c401050b00015890410885019801d03014001c41ca4002d4103400141302a20060000c2c1035151108049500f480c0700b00461 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 290297769 1250 290296519 290296537
    0x40510030c3f03080a02091503130b01030c14010207080d05130b030705030106080f09121312110405011706130309030218040b0108070501050d0e010608060906160903120e06 76
    0x200b8940d01e001c09a40042c80412401d5000544850020b0044a5503100712000b01000034228030320810ba0806c2c8040d65070004100d40e001440c1c0ba601c01000480240c4458003951080961100300c90901c49500002841c1c41206411903020900c2000040800708000642e01b0f4149041c1341c0d21010b401c0042c1c21a6010351054104080020812600c50b074081d0145060724513640e580145504e8080060245030710a41e0003c0a642014501c020307099108401412252050500c0404507555880400c0541a10007001c0d02e408075116002d040d90300e030921955001d40074000c00314410808041c10156551401000c11800046070780f440d6041c18000d034003010085a005215034500d190348401c03801c0091059404075040026078001041004010a00d20284c071010380d210350819003c0d01c0494094808440d1a80d82c5560f1510007050442051044a1080c94044000c01e15820065102103041d2103031070030001040788508091000035580c60300d0b221021800c1c58055040c6240b880001d074207100e00005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 290299019 1250 290297769 290297849
    0x103022115060406170c0108070e030d090503121603051e16060c02010209150f040f080615030109110d0c05031014060604050a12080702060307030b040510030c 70
    0x251101d0420055489140c056406104696544200c0c00d010700002d1643c00c03854002006c5030000f5485282050750220b21850940e018020300300110f424400d0008010000a551140501072414200055510002c00c0000d19291112071020040030086106004080110000d6000d1096044680c00682a41d122220b0b07542c1e05142c200c1e00101c00710044d004c0759000d0800c28142517841c010300c00d40e84001e034060b10100e54003007071194480140d4001c5890f5110b0138400d10020405812030f0440c4406092054010011400c0c03a9010075148100b40100710320a80c1840c11980c001600224900400c0c1d405548802c1c020031945410410a070840e04465058480c183c000ea1a581d0907070400340340304404091922590700c0c0c450a014951142c4c0c09900c1d008081c60781c0800c10001005a400c0038107000f404480d080081603400100300d035009447c0d80d40080e88491801303180f807502c1e205058200010714401d031205803460352540d801410328800c031240da445079080c012001c03800d407e0b81c01d03a00c14100d00c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 290300269 1250 290299019 290299033
    0x60b0301140414060906060103020a0c0b0705071506050a03062315130510030f0312060308091503070c060b010e0a030602070c0b0403030c1e0818012601030221 70
    0x20400700300e40700071102900c840090050403039000c00b010402c0c80c007a000e404040c0c455962002d005602039403000aa0030104a035500c4000e020840c0b08140d0f03401005a90f42d09a0b44540700d05044404800c01c2c205600d4003440c0c18403c01c402d070358516074a800c45e6031002c00031400410f02082520a2000720f000321b60001101010031283e1110b0000088000108998881e11142d40002c904100c8030120713284900c082c011030050004c600741e0f200903442103101e490b0141c46c41d4599101142a03850940c02154400e0001c9160782031441c0201079030300c6c0825020446801d5203481e15000700456a1200042d08280c0d5880003403203541d201c3c0d5181c00d901d0802404090380c486da030f864200b00a520a06040d66030342c00741d4401040c2200c104040b603044030341664400e0300c04030740c40d212034100030460000407407522030841201c0c00182000c0c001d02641e2980e075008a213104040307800940a60544030782c4a1655011440084212404440c60390640e070701980c401040c1c510040200c036600c403c1039844111445080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 290301519 1250 290300269 290300291
    0x50907020c01031512020d050a080c01020a09050f010c150b0a0311030706020616051305090103030c05060105040b1503150402190e0105090d15060302130c0318020d030c060b0301 78
    0x80c8801c2503072020398040204032400c400212601071140500c00340c182e03d0f820940c0151a144050b0f141a07800b86040c0c070920466a518028240d009408500381a5004a00e007a40c0541103125940100825501d910006c0d00c898002001d001c072502000704a803c201c20f5a80c0c101c482d0358011142d03403c0191012001c00d84a041039480f0042c02c8e00000d2081c0f152000c00f01d0a144041031480c0a8000302041a031100d48a41c016100c2c0c1c2c01041c18205043d800e9140000c8550702c0c541007038000c6001e46c1f1043c0b03502500d41051800c09038141c01090140303050201014103078680307010503503843e030603130188a272a0348034039100200394580b08a40c51340c0070340041000c007180d044180401d0084c01183c1c8821596407401c030b0045d60725015800b03040e81e00502081131000800e40e462544005603150b41c00004040303031650b0000e6110083c0d0341000c014607a0f5000381c0951260184640e08034034841c3e0035001021455503000400001248900500700100106500c0400144c2d40224288402c001c0003440f0300c0502d9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 290302769 1250 290301519 290301523
    0x7060e0102040f17030901090e091011030106032313050c040c081e011805060d0b0906010810020f0403080c03070804030602130909030903030e030a020604030606050f101e0905090702 80
    0x1d8040c44c0394002220300480550380d0000f003183c0c0903445c103855600c0d850f45400e41800d20540014a08002c41c010321802e500c42012904c142ca580311b001c1540340c0d07117035414240c0c01000c44841c210b500b00c0c0341601c000740307035020b201d104440b540c8403e074140902c041420b00d140c803c3c100410010199000350400c3c40504505070010103142c0301d100303011122554480e481c8403000c4003ca0078420a0060710610507a0b2846a1968001b1980f040f0040c00580b0b84000b00d58680810203030840305182541c0100c4014080c051082c46140c90386032213890705608144106c01402001d11980c400205a8900083d0002429a0501c241e40b89580c03c42641521181c0c1c07820b0010195200022003406100341c0301000c070b0030721034a10540000c2a050765440c000142941e80c10386941d50380c1d100301a8584900961580140da45100a00207103200301008240186880c0030b000d005c101460303415119a0351190b004c0d0580d0307803000c0c0c00c0701c80c81c0d02074501c02c200300d807205403e071004e00c07858019070b41254103903080198031900 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 290304019 1250 290302769 290302799
    0x5100501090b0603010303090905061503070f03050a0911040c02010e030403080a0801210b04053306010206040312020a050f0d090302100605030a060905120c0601060e0105071707060e010204 83
    0x2800e001441003025182c1040100d100c2400700401055299170180a0704c00e80e940f1456210001030314605c0c4c080c0c401502d1400a420884204000078030000c980c000b00d80e40b6000c0d00f5009114018180200d403502d43d94061402c80000c103460040b995130f01c256442034401d402c403c0341e690966003581e40d1903440e428240300d02d500008243d0701140340d22000103403000c82c41ca481e01c1008106401ca03c064185540c1d0880115809441038030141b20b084086912402040044002608030a90b40303055685080303000114803600800303050641d0403081c00c02c00031a4003d64000b03c90b0201e15001a0b035440c450205540902440b07582002d820008608025840510303071001152034001c2d000c8070904006400e0403425600d250003000e4164000314000784c0024199080702c0d41d028170400940728032072090710f0003541d23039000025584d0f4070350710050041104640040c8540c0ca02070080c0382844c940780751a110040c0490f0704154604070709100081c81802d02c03c00e075100300c0c00f00d480980203558031a500d021290392004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 290305269 1250 290304019 290304029
    0x19060806010e160f05070312020a120f0614010503041e060f0b0f1f0e18010612090816050f0f0601140109050904020d02010c080706020a11030a140c0a05100501 70
    0x2854102081c9110710f1186104840000c0f0b5480701c0360041d800c802164a5040104202c05006d40204080d140c0c00c04c600185c0f10b0003685076a40442000c960031014283e80c00d0000314002c3c24546001032081d0078086001c1d2114071800c4c281190b80340c5039032822684402c10a2528134640040c410746204010194100109141c070381c25092103450300d00310400400024040c100c5900101d1100303960350310168142900c2c07030303059142003258541030748101041c0351814072201c0c240ea1001a4005000c0150440082034044e002804200071b9401e095841458030b10451442d1400c0300051494503040100800c402e4040990a0041e10108107a048516036108828042c03840c220500d00b0b60f20b0070f1548030380c1035482202e100616042a6407120740a0000b02200160243d0412100203441e00218200704000c00c50144036510040e40c501c0710907801002c03d440050400200d402c2088007d40d031035440700d0142030100407801c03180e80d204009245185005150100140036004000b00ea044854982e80018100c42d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 290306519 1250 290305269 290305289
    0x19050c09040c1706010f032c0106080706081b0403050d09080606150d05060f120c1905060a08150a030308100b0c061909081204020f1210051906080601 66
    0x107034849000c3d6021010a060030b0102e80d8020700140c40703584140710b000c1c6650303400c0c24005041c011031901e102a51003034100440380c040105040c0c403441c041c248a540010480c0401409078071342800802010f250703019082005803080c290550000c2c400c0482114010340d44002100c82850084402810741c8100348125161401b80100250340350401b80c1945040703a15044040389404001c05c818002000d0190486030400c4245c44100102d450704d05c1c28484005e800d4004080c1000725030200309003400410502c940110b2104810807044d00d0325000d86658201c10305140d04140d0b200102c50002c81240d1080560000701800d0010625411030406c9015008010503086820f850300084034051007254071140c01a40005c0015212502101016000c100c4209000c039070305100c7d80f1442e44a410401e4550706100204d401d000442c5005503182e000d6035815112480c07000050324025840b400d00c004031240f015162800142c810040c14140003080d00140001c00207241c40f00c9055903144824083c540d07140d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 290307769 1250 290306519 290306531
    0xf3314030f0f0105040b030a08071b0810050a0c0c0b0402280e010e1e07090f14040e010e0d03150b0406020d0813050706050724020c12030c0406030519050c0904 70
    0x2418030b8040c0c0001b44c40c2c060300030b081d942c503160780f042c0196010075015a050b188002c440381240d6211001e150042241100030500101809008021510080d013400d81007894481d014078800e030046e91400c0c1241d007110304c2e8001d41d5114004600e2134083d040c0e445001150401880305050018220f04056420f0241c482c403d5030b0700c80070300a0640d00141c90240c5409000d00c4d011110090304240d999024545141040c2c07641d0303641602070b080002e207030420072010044649201081c01c00d480740c206610070b424001d0005d030001e6001140c0f24080c3c0c1c1c036010101a05c640c1400503005212000350020111102c1c803903030700c3d81c1d41e1741d0007504c550f00c040340500080d4013600850006058424200c000316040006000564941041924203900000048455000c100d0640c0300c102013105500614901e2480c0250350381180441c85411320481035800e9842030010f105001306400000181c03026155181400a0b10351542c81c03a5039440003911741c1254085041c0300070008c02c3c008400141240c2d281c2581c040c400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 290309019 1250 290307769 290307779
    0x2010e091f2607030f170c010c0206060f220b01020a0c09050702010c050c0607051b0a030c140f1b01090b0c0c011709030306010807120908040f3314030f0f01 69
    0x4615581c400a019840c401441502007000c0c2c1c110211b040c3d400c580014588a00703100d072039003503034458400300c405030300500c0401200c3d0030108806229a50200d882d45003543d4800182400c4034074183c0c0340d038a115a07880912041d41d000304000c10906e9001010a00c215a465201d01d014020440d078140044d400d009041020394020420f403000244010060016581c445108a5268001001000342189074038a065640a4207101d121080e60090b82c2e4103c02d800141401130118a44401d030103542d512414610191250210344840c13000a40024500c40b10180b400484180c012500b2103108002d0008540400c2e0900180345000200280c94031414000030f0040480c0d1f0500490385540309410400004a5641c80740b804d082d4421030a0801342c40b0007540d800782d2801c440301ca400464040d50009801d11050051240140040405050703006042401044500510320b140381c0c1c80307680321a4185803001050040d01c099080010315072080f0385070b16110302c51980414080c1d4000552414280000c18 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 290310269 1250 290309019 290309023
    0x7050c0303131503141510081509061f05040801061a03010e04031404090902190807030209100e070801090b01020c03030a0518040f022502010e091f26 66
    0x50b480c0880e007820225180c20403003050319922251071000c01d581c6400034101c50506401490003040d0030003c20804040c0e0344113000011f22070041c1030040c060000c2c104000000128003c0c56035034000d483c420f01d0303601c0d200c5c0480da540448011a4907290040520801541c0c1c3c40400303002200c000d0b200a12000b60382e45202d0039200c646909101c00c110b0704000500103100e240c16946c0d0490702c2460101c52003808848200940e030400d4000d07401c1140c03a41640c0080d440c04600581c05d00300b079070500756000c914042d00144d0b281e2151000a02905040001641600884d8070102c02000c10310501802490110030040c41180c00340103a9400510f0042812410f501c0000c9410121101400641c50110546800d9440c1c2d00910a414a006070b01e50001c45151658001c02078a0103608002680b2030901c04144d003444901090301c1e82c141c446c40c3c4a000007507a44114003400c0340009a03113107d055114614114a6400d0a0000008604c05064000f43d900d0000c1000440104404030840444482c41041a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 290311519 1250 290310269 290310277
    0x90f0609040818040f050106120e07290c0618150105040e01060803070506040201030b030a0b0408073305010f0b071704030c030f05070b120708040501060f0b07050c0303 74
    0x20342040e2020002030008841030020660070303c0c1d0b8400e24540340c0310b4000107425501c5000895280381d031280c00402071580c105518800742c0e00c54075002d20001d0784000d552659814103104101121a07440b20310f40c21981513081070311110416820740f9903684210204155104802e40341202c50b080305200306021013030081217a840000b1003240900090b4070340390800001d001528242001c0355620080020002410130013090054400d2014000c80d160600015046408142809000f60020040b4400003061a800301e44d01541c061074007529002a4200441c1204c0540607911400040c194488112071030180243c5650404c0c40b02884140e8030348400740c00210342d5200c0e29154600510101e000954a500143d440f5080400c01c1070500b03039070f0389421661030000d034001c0d568040802e03036072000c4c0101804084043c20000000a01c1c0c24401a88a5800940200a44100450b420100341040029042a40108185030080c4c0c40507840b1510001d655104410480c0d080c0f244503071000d00c60034044107031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 290312769 1250 290311519 290311531
    0x50307090902010c111c03020f0c0d0302030d0f021209100b010914061b0102030c04091a060301050f1201052e03030203030402060304140a210201050c0d0c0c0f0809090f 74
    0x2810130310b00c41d6840381030b4100245100c0741c0c041c901c0450420002d4031030302800d460301c0c000e500810340c01c0c0d0107a0205042ca00550851070062000d84000c50202c0d80000449040b8040013a0020b03990f042d04144000a0240e1511000300e100003805000034010b0003d0626108408042c04002c584901c50041d00c42101c60f01c10b400f0310410301080b580300c9140c43e0020f00411400038000d5246000c070045080d089900848001042d000081414000c01603a481240703008040012544410b400c09c0b0009040c9003c1441b41c140b26840b841d01c40d04182d00d400701c00002400c1c84100030b010b64201047e0300000c0400038074640040050800803510500c40160384074085903010b80141d4656100ca40038403100c2d80c0024800c0c1c444844040c540124400b0030080d1442c8280103018501060702c0b1081700b5242010411955411a03051000384201160f8120480d11803001e0000c0001e00d0031501c2e142610003103004400540445007001c07545051040c036900400403070f002280e2609050b03407284251403200505445c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 290314019 1250 290312769 290312777
    0x70b0d090b0f0f07030e03070206040303030c090905070e09070210062c060f10050c07140a0b180f0103060306060e040b09070e0c311502010207080f090402160c05030709090201 77
    0x4640300178040d85c011500c03401c6140a07a403501c0100d80100d2190f5100d5401100021b940705140d22030756034001b4104010b454000028441c0d0b08024400a100c040c0b040310083c414420135010540c0300d4020446981c207800025030500001e540d80020a0b40c080c030100d00d03a1500104000104c0c400d580c5c4903051441540010031407041501d00109201e45001d05069800900c02c08000340070040104010700c10051076000c0c0d06040c12541c0000f07003c54800f10f03a01c400034038001480b041c18600c4098040c0390100d88262144141c401000e00124064511640050021407903c200400e409900d01081032080e030050001e160b0035182c80c1406075448802d485840550030401010800c88a12840200201000b08008810b100301000690340b120750b660641841c0301c08080010800d03407082041d0000b070b00382c050008504040440c1c0302c0751860f2180c8042104070a4001540700c030283d8980d4140c81b4004040454080d84039002e02d8140740d0130255000d610302c203229040c0d00088200560284811007581a9a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 290315269 1250 290314019 290314021
    0x1b030c02100c050a03090f092f0c0304030510140f070c02130e0601231003180b0717070206090a02220203040807050705030307020f04090f05010e030904150f06050c070b0d090b0f0f 79
    0x349804075568181982c020b10380410801cac003040d8003080070700040c0d0b004801900d007146884c2140400c0321050151144141c0f25582008017507039584d14641ea04c1011070400200d80303039051000641c441c004019400429107404d20039002280f000603000d05a900140c64182400048243c6424566541c28515440b0300f11440c00c540d03451280c0c001e8211840352070f000310072078005559050087e5008869038000510071406c071404c50a40d2050490300500c190000c1c040c0c50409903081a210000020003038060344240c111000e910b44400e20b100000f00f250310003103449040c20300e0300804d035901041e0301340da5074424140003050323500e008001c84012660081880c026100c2890500000d0b210002d4182c54807006821007a010920030f000321940003d00402031561080c0d0300081004850b460311107072042080c100300c14801c6030311030344a0209503010b90038401d4892000201052130480a07800805101c01d02048082c4410f40a400485940e88121092120355807030f18040382c40b0340401c6441c4007210340454 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 290316519 1250 290315269 290315321
    0x32105070c0b31060902040903031416020303011e080601030b06030f061303030c12141f030503120907031202061b13030206090d060e030a1b030c02100c050a03090f09 73
    0x8400c20f155846540c002c64590310a80020f0200c4445820a601181d102c00b030813080c21a5007290154004222508101103c07010ba4000350b4902050280c9442403400490803041c1015802d1584010278801c0c044a8880d0f840780345c8401416800c1c1c410b03a01038440c0000d0205078442c045842482144114a41481f01030f45131000ca01805e01c064a80c8248600c02c026841d89a0300c07405200007800f148200c0300300c0c0d42450b00314120007000d40d80118608080e000350602c0010f02c08401c50300e44c4411342c100104552201c0156a0510545501c01400e00c090340700d00702812034011032003a104407500741203600815281d02000c00c5c1c62051040440d20350400c40030500052510b0405045041e40140c41c10300501c03103e60380c400444400400050141e032001c513400e2842e9a01a054400f6886001281940d03011240e0b4060080f4011901c024800e42001748155841352090b01e07402c0c1015002800c50300a160700341405401e890150041407101014840007207209102030107121490702000421510184001d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 290317769 1250 290316519 290316601
    0x40c0f020d12020c151909151104050d0605100f03021c06110c03040801230408090d0206030f04140304060504060509060403120203030a060608040c03032105070c0b 72
    0x1000c800e01d04250709104544084e50100711403c0c2c03030122045240c00303c0c14030003810305c01e5400107458200602d003410461800201c3c201c40c2c0c2c580340f01d40c1d07800101d200e6404142c42605070180740c110a400103400e106207828000c4030f4002d5030040b44003800a513a101c0e1168180c110311601030001030b4000d071703280030075010000e00a0300750032105003d14400035400e61000c160150550000409039503640c0301107402c0c40103840a1140800809500d100344849001071000b61700403860040000d4444a00826044100d03184d00031081245030f0700601c0fa61ba05e1804814070100654103907015212410f805009a0740d5500000480d000d4030342c03645900b81440c0c1303018812510703a0701480e01a50070080034480000007070120312003400c00c0c1806130055620380c82c1000c0484100c80c206d503c03081c03c01200d81c0c00d001c082008509054256905494500101401c10b200700028080714100103a0440c901020843c4595000401c002500d00c500c00030302407070302c442e0003446540741201454240c0038040c0002002000407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 290319019 1250 290317769 290317787
    0xf03021e04060609031401020a020624030109030804060524060c070503060a140702031c020f07020909010c0212091804021f02010614030a050601030303020d090204051005040c0f020d 80
    0x382503050300020110012034240c030015808000030500300b801c2030041020a00514075008410f400840c00c1c505441d4000b50b0352035002d040c000350018015030380c07203070400900b4000c420414040c00074042d00006180050144008440036100240782c180850240b5034542e03030224800100c0c0c0061060300d4034100820600398003c4000202c2d40c400c0c2e100000303441e20b05211b514800c4613020000074504241d840003010000e001820f0600310340003000201d2a21130040000c400d4400150340041c1ca41641400301c40c0203105d43c40c00603610591103002c1016407001500300b03111802050b070075248c10b0003482c00303130480314000e10300c0c0c20350703c4204611403d4015a00c0d524441e84140010f1005546101d4070281303c440e1080b41c0c100d0401070b51900d006002e060351700c0a007030040311001e070f000344208411900d03126241c2c403040c0401400c0540020700c2030710705249034002c449402d0300207001b000107003010039501041c201c3c4e5204a600071802e2a03520062140511100b034961003554001d4071100103440d60860328111 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 290320269 1250 290319019 290319049
    0x30a171005091518041103060c0301030602130b0c010f110a05030a02090307030f0804060206010e131b2c0604050609040602070219032402040602030406260f0f0603070f0302 76
    0x103050750b8140180d134400011048410070400f041d03800d42494104100030710680502d080c000d83c800c400b070186403580d88080700d044a4115900680b243d03d551000401191558843c807582000132803902c1c400700041d0f00c450800d0070360410400c4040d843c0300c0071aa850288100c040040340003800003662501c110707001231242c1500141640c2c20b464881d940c941181140c00ea00713491499001c0303028059140c04000440c09401c0724103011800c1d10b002e1804848a403010b8100820320f0107210704010741182e2080544010f0000c11001c803990000701c852200032101880c80c0102d180b4000c1001ca0b0b140d04052240b613000b014060003075089980c958a43c1c3c8042e600c001e004a80000f203003117180100d0102c5131000d0000c1c622aa040c00c1c2c101043d0081c41000c81007485001250070b00c1007004104030380d000402c41d0304441150500644504034500080710079481c80c05030104062180301007164a1030924906440740420f191043e8158440c8800d0664840490080a4981d051030506001502d08001f240030401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 290321519 1250 290320269 290320291
    0x70602070f0c030b0108010501050d03121b0327030e061c020310030302060604110412080c030d021b0d0c0201031a04090b0712090b0106050318010e030a17100509 71
    0x60415a100640741c0440002070b160320002210503c00c121003140418018200c050080c80301354148000104038140002e001018030880e100c0303800c400481ca13003124006e03103041d51040e505c4060500000c0c000d4546440300411450b046040004201055005040e0141d010364924946240c6603092009a6011000085840c03020003480c440c1408940000e501c1580320304640d45440307145160203850072034040c040718842c2e0708003502442044002c20a85003251010481d0704041101030402c84454881d207107400900d03000005100d014256550001d002c20084140510740c140f59201e070b01a2903280c10325400000a01006190380950712941154041d407001c0400014040441c00000b8101c4034510300865030800280100000d86410030300720400c2241040040c4108000c41e5180c03a001d030014001c8806000c070100100b849070246804808280810b00b00030440c8082803802c1540e00c1e042050000b000034010b135080c1e0988500c0100b802c4c022000c490610708407600781000c00c005400002c0c5280c0340b50f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 290322769 1250 290321519 290321527
    0x20108041a010b13060305130b15060c060718080d140903012412080d0207050312151c0506130501021e18030601050618210c130e0304050402070602 65
    0x9120054030750300800b50344000503a25085014404c0e00142c65920172001c3c1031500080110b82c480d91a8100003003a031150342004d4550700c004102054012080c1b02d00c1d08503902141090070700400207160307402410b058032800c0790030888200e29070246010b800362070304a030800301e14210042c4c00381c02150250341002c0320701810120581c2c0400c2c02c44161003241403050514000720b01810300c0c46168039010740720400c2440001ccd00d1a85070304a1520a24039142c1d0004e5000840d841408818030030355035600705041000d5454104451070032151515400840d1041c180c12802901b0b1013070315107940d000e180e80440540a02d980e0251400003449002038141c2d03c0c6d540801011200081e03c0d9421400d0f108022049a04d44181504e42c0c01d030420175002e5580a68010170041c8115500e5805403050245c100c4050404890341c0c034049041c03203003080c00c48444040620076419080401081c2c00c80c0c101c01c1034403910705513000c004191040d0b503071060305c6459a0700704020900c031900b01500148121400343d8005468 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 290324019 1250 290322769 290322803
    0x112020d060315050f1f2706180b0303090a0311030a081c0b040b18071103070803041101020604021e030a080a23030906132102030c0f01050c0702010804 67
    0x451420822080d88165034004011000b808902d030030b1740004a07030700942d007a80603038101454480d1050180000003c0894850803040001007004644082c100b101031008c1991580f1650b10003254100d4580180d05120056500341000030075100171000003480f020707801c4e2031620f40c1c40c24240700c001c005415009042030300c40803441d603000408444000480540580402500c0442100c030490300d030030b204031301b81140305600b66100ca40440312048004200109a00d44003020b0320309003100e40c0d09504a000204180060010000c003440c070071409903412440c02464000120f80b0b461049500940c4110190b4038014084074901188110001c06011158480e81c0d5440c1d0203026004204242c0014285041c0c2804c9200c2544c880f5940c0d440c0e0420403030550400095164030f900005061203e828110501c2d4401c2c05402000d0900d6519a070350740c2c04211641000c001d4585c0d01643c050489841825118424848140f00d00e620903016054445d041511a50044654960151080d20703094284521404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 290325269 1250 290324019 290324033
    0x305250510110d0503070f02061902090a03060908040e01060305160f031401030c050a080a050309010503100504021204060b0a061d01020c0a17010c092103050d1a030115050112020d0603 81
    0x40c3d00b0825454142e100d00e040c44c4000e040102912900045401280a016441c024850082d0000d4a41e01d40543ca402280300801d070b03100c101e54009090203080100b221b061000b14001001514045031100100760307210354003603043d180300f0794000c5c040c8001e200c01984014400c602c0f0381701c01e03440c61501007081503911a0110040c0c9080c0c10544041d1007000c000c2103d403034524800c40040c03100c003004d001610101d4030b425803a03000c0e1200b454144280040010104183c0c42495005488018411500c4200c1c91040c071400700d100b120119692803030000303e07041c1850030101c500111074480d90380e02885440f081a1025001d02450b480741035108041c14107403e682c030102390070b010b0088621030340c03644180c5500d15030960307c0c800c0303c001c1032180302001070180a450a40041b802c0e04001006000341000703242c1101e036403003120018280103150010340b079280c42b06e410038499803007000ca00a11042800d003600381e524034a00d204860125a140e048a104825150064060314a40d00c3e80080c1280d940d0311607032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 290326519 1250 290325269 290325283
    0xf110705060c07080105250c0302070509071101060801060f09020f070501050f190614011808010612050106050603060904140a020405160809060403051b0f0313030525051011 76
    0x1c0c0181c010010904c1106424800d05900c42100980510300001c0b1070017801425103154400340400220b80798034420300d8002c125900051038090000705040c64248401891400311065030555542402800604500140031300000d070342d40144042c0070780c1c2c0f52500c000b0080d4020342005400c05418800c61002c55002c0c4a40e44c82401c007450800410700d002c1000c1890081010064076500c5c0c50954140841420101d443c09803141c00c1c205014800b54801e500703035480090754030000c0550708200300486c003002000c00c0c1000f080e01c18402408a80d442e4001c01c902030100300d0384a0f070025020000640455500c160300003101d20402d0541780b2000440d004201a1003084441880f1100000074540409a2014070207074032030380c40c0020f8860703803c090f50000e00d03e109118034200b2510300100313481d8400909001c03c000071400d03103085998800d401e420400c87d5810700e01c0242c0e40c1c0c3c0a0950907292407500100f11910440c0b2101244801609010420028100d030284490400c0101c0e00351400b144010840c02d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 290327769 1250 290326519 290326537
    0x21c0807030b010c14060103051002040b0405060a0c050703050c0f0d051c0903170711030d02101a1e01020f0f0c041508150906011d130218191b0f11070506 68
    0x6d4685581182016440d0810030780021195620410081240801c12020b54040d140110b03821030f503565420400312121042d142d40604140543e0b80000100000000e80c1d00d000d8800340c48680044c11200300b00050b0382840b40014015400c41c2041ca40c564076450002e030605541801c0940e401c0381c1302c1d125400d045a9841841d0f050741c0c00041e03040e042c0402400107001c0c0340b5080780106004c2ea0109002903e1324482a10707802003507221200c0c3c040d6a0416100d580c22030300007800c08180301c01c5510500604000300144503002d07001d10482da0710715500200743c52132591034070310040120403408000d100007408030b100101e0b0010100940070801e00070600c00844421486118131840d0b0a08402c0b480c1883c0c4c0c10703440741c81000b03041403012485400a1010310752180106416400c0da50f810f0010076690b0490241071448420880100311881110090324403542c50703028010001004002480d541c840d00d0040004081240061443d00262040d14039a004200c03820648003001d5440001c114160890100303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 290329019 1250 290327769 290327773
    0x20f150415020709022d27100e151e03010602010b01030b1207090510080d18060e130203090c04050705271807030e030d0903021c0807030b010c14 64
    0x41a210740d941006014003520001108503d030880c0e44010f4440462284014102d203001c901075a40305155000c2945c03c0ba0704c0d0b40400c80d07058001c0c5600ca82080c0100072036980714180c1400215042445039540116444020340703054641101e18400c600280c2028004001c0d41d180031000003100404138001d10b000307018540010a21440e2100050141c680900b00f140c000c84080d01412003036940081e100f070446802840000303c076101d44185581d545199000390141d4800c850500f94210345c824185d0007541040e01c4200c0740140c03142d07012940d80c0c1c00940308660298610040101d11202540215007004644044130110059007001c501500c1e4112110f10200358041546d1803c3c540c2c6ea0103407421030310481d20814181c85068002641020036011003041806074200160791a4001e0348114090489001180c1d1a1402d03050741c280074101049003200103020304d003c042d0b032621122400c290500020389550342950784042c1c2c01c034001c00642030120f0410056070340447c041080366202c2c1d0259258500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 290330269 1250 290329019 290329049
    0x9010b0c0343080a0e042901090b090102030306060d0e01060b0a02070b03090304090b011215150804120518090405030a0f081506090103020d1802010e0319020f1504 72
    0x1100007001c0304480000b00d0040500c840000580003100700e074009000d506005000c05a03540104005003a503c81140454092040000c50401c580d0031401070320000342d84403003c254640001f0400d6016004180e40542c0c41400400c41500d0400c014044504000e1000070b10110081e01c00c50944e15946d01c801501d8030000345080c12036a050181d54050081191f480d851070420000f1141e07240b0491040700280c981d00c5080c0260342e0300c510107449100c2e11306201808803485607800c0c1611000c03180701c0c0e01a800411603c0011030ba02600c2c210380b00e560420744201c1c1021a52a00780c54681c85941c0c84a1540c0b0311408000241d524401e804d4000d83c01100290b031100340382e04016140e4143e440d06182880460000c0158004140003c0102c510082e2212030720303440d102d40141d01038040c1c1000b8000c40d500f050031003131a10301c400c0401075585000742c1c0d40030010035070b0b0001e05032510000d5056107070012000c500c203000f6080820340b6040c008000303800248102040501080d0580042d0410b44880f06540 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 290331519 1250 290330269 290330347
    0x609060b031f050c0705190201140a0e1e0105070605041103010603030206090f0105040b010b07030e0a0303031a0118030219030803040804030b09030406080a0528061e0509010b0c03 79
    0x12261960020090851300c0c98034142d91034060740c0b0f00d4586040c440640120901c2000c5910801d002c030364030055400700c2c0d42c03541640c00016060300c008800ba6405960000c81045041c0002c065000351007006840d0903140035500c0c0c81d07032400342100074400e079800e2400020350106038800b40700b400021070003540a40103074200f0718412403c00403003094607207030f40c0e0400007800080b50909008604452410b0202d07550741009143c2541c01300714240c1c40300d80c88440c3c01c000009168054000c01d502d101488a07495181850000650b040ca00d000500345140035032200510060800b01c0d00742c10440003030000f0484050750390f651654a54400c075021141048046020410050080003141c1c201341034038080c505150404000400c000f100520360306050342c488010401c106404602c00e2030401d00c103151744400094440402018000034810032000c8580621550441403e4920321810348200078800030159107400d001d09541e0f0011007012059000401080170b41e1401c034014880844540305620209003020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 290332769 1250 290331519 290331521
    0x1801032004030c05120705011206090624080f0a1808031015080c07060b1801060f12020415030522110a0509040506040b0c0403050312100605070804030609060b031f 72
    0x180d011a001c0c008944170340305580c60200310300d01034500c00c0c40d041c1400030034001030750094120303540002006450b081c1c02103040c1e82514000b6641c50050b1207040305905d0940011180d10608452801d400068000801c0264216402c0700203d0f10440392144c1c0000440e441d85c1400e0f90003521414000120144204440d008400803149620080d00300030411746800107903c1181d100d090401031609a56840c405e049030b40c0c0000c69848004d07540300810640d0303107610000d02014841c552480c0400c8840d40e031a41c1c20001c50085800b900c444c2c451102000940080035400b034140980700e51100d00d51007849500031405030010921007030088801c1115070540f5020300c80d010509401c410f020f14815001c201c04102c0000b045034005500c2014040150340d80c0003610018000d40e00020468000010398650760f60700c0c405454001d01040103003c9045695520655851040200040001d4002e101c1080031501961200b40003600502010520301040f00010303040400843d0002000e69900e2039102e0b042c46a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 290334019 1250 290332769 290332793
    0x20609041401090b011107080601120218090a0b10050612041103030a0f030f05040f02130e030a0201050f01060c023106080a050106090e120c011b020d1101090305180103200403 77
    0x1b410240401d5410071420742e486000c1405006d0f24840300102000c11512030704541600101d045810f0700380c0b410301041c0e11340c40c0c040504050310321040302004501c4200040000c04102c1e45c00900280c82c000d411201c0c071100c00001007060310420000305040744591001e10081441822950381c14406007501da00181c2141d640c03c2c440c41005140030208030000d00c100ca40d101026404807200c0307c0c00403000b0400005000c814104403e24000803810750051501504030078000c0e143c00b61442441d82c0c840904592620110304082c0d0b1020a0351920790304048014402c00d80358040144a0102c1e032110281001501c042e0340c04012182c0c49180e01d44140031080c4115400f5101420b02404900400403c0382d66510444601020106000412401810003540b040e455041385c01b40018a40804260181d255480c00300f80501058403901c0c80004032006101d07005034907902d40c45490030302c1e0007401d070010012100021981032596404101c07200c0c00c5170741c082c00b4444100c40745103541c4a055150420342030f59 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 290335269 1250 290334019 290334047
    0xa0903060e0304050301180c0905162118111c080c120712030b03061b0a09030c031a0c0a02060420040608010209011404030b01060c02060409090b070e030c0d020609041401090b01 78
    0x210700700a108a442c448411282d055905d440e2140e8909041e4241414038400080345004503850281c04144404100c500344500398054550b0109070840032060012210360010030014400d030030340fc45000900500060201c086120b0100d9076503e129030307420519680800d1096070303624105094002c0b03c2d80d040c000c0d0000200243d001c0c040c0740c141050580c0781c2242d03600006003100c41c04110105074500c07d03c81365005540100d000c0c0403159480c00d00300c0b140400710010a2440000400040d010b000c00412204000000d0740201941d0350745880b002002804007800e040c041e104030700051501c3c0d03118001c403c0502080c000040e46c0c1d844c0d0130b0000d003034403960b4166a00081c100b4402000400c00403020701d0304544050070002030300700052000030741c0c1e88900e4008464251402c0c1e0721400348012801c1c03141c402d1000b0b451342008642407400b01650342c41c042e814035078004000e403645c03401402c0c11000303400c2c050005000454140306c0c589004030151401d800c4a00e0003680c400302d506641d030b8001031514a10f5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 290336519 1250 290335269 290335271
    0x2715090a02010f05031e010902070b010501020601030803150a090510080c0109060801140f0d05070303020601090506060a120219020c0a09050708160c1a070e060a0903060e0304050301180c09 83
    0x301003580060000d120318805003091210201c00039507038005400010b5500780182e04000200d40c7c4070701d03100c2d0003904103034070603108498074100201d600c0d40002901810b030303a0041075030b83c1181d50f2525000c0c00b08406032802c030b40254180c20000b84039105800b07510f01503405640c04400d082c0c2000c1820303281c07141007a1031a0404c449a4002c00c11a9001034406041da0303113030341060803070807134580c00310300e1800c4200c07191608001c01d04610707400d200e00490042e003624441c0d403e076006640e840c1d41c40b4040c3c52054aa8960100081290040140c043c0001d140004d460300001f5013419003221588291580803608000540c05c100c128400d907250407440c110250070003420420603424038410042490350014032807c1850700c1c0e030300202080e50142e80b40c1035049500c10400d03280c5030542910f100d10b590080d1408400b00f90440104039443c40c0c00d0094408101065a032001c1c524170b143c9428000c3c00010201c002c442c00204404a125282801000c6900d1b1051001a01800891034818040a070540c002d80481e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 290337769 1250 290336519 290336533
    0x60513050606011407140111071a131707031403011805060904050307030c0f020312040905070c03320703030905120703140d1e0e1608030a0503271509 66
    0x2e0495181a5030841c6d8000720080b50b14501032991300d00600c140d04000300307848004a11802008a2031078000700c80042c030035400d0401e44558024020040400400030200c41042080b1003505000c00c006d410641c4c01b0749800700151024111450255000f03070403207400b0782e030210992000050640035680d04200b0035508850f0303615043c0c840a40f2401081401800c0010581c044001d0192001034103190607002019105065010442003026074824410b046045080c4000260068061070340c0d401441c3e0180c41e480740540b100e9101d0154a9030f80e801d0f9200c40822440c80c1480350a84c003029000c180d100b0b450014400c0018144180341103000b800741b01c0822001c214a000103503100030107080081d0541c10683e20342c1f0120151038040c0074100b5903107030010504034100c402850650000680c0346110020f0301d158045218010910420342e0081c90001d9200b001241d019038420710045502c14400d510b500074408030303804100078080e001d0248141c141e11481410f11212450741280f03400015540c000d040f1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 290339019 1250 290337769 290337797
    0x14120906040b0708040806070c0303061502150613090c030506010f120204020901031404060903080105030d0914040e0a05030909010902030f0609040507090e070312021504140a06051305060601 84
    0xa20311460203404804000810601c080003801011740c0c0140248005a6895181c04280240300d205030700c400390002420514000743d949101400540d01ca413856003d40300e484031440041c400c14201421441d0481c9039007003a048045410300c036082c0c603944650183d25005145040551400c0010f03040311081110040c0204020041d2140c100021541601e0242e210011800140c004101c0c0e9a000f8600d20f5003031082000b000350691090749194400d445e02c0610366240d1050503a1a50500e2940c408901180c00600840079150b03078190840000502c0800d1103004002424144924001e00710381d00d07800461303452410320700444014054600200114114603026510104182015000038042c0d0162800718083c00301c1800030300080c000703138103051007200b4115040660f5500544019a0120310307601a103405180f010507510340d65286104081c0841e241d6484060084d0443d4500e01e40b544030302d03070b02d460024120380901d511411a0300c131140b420051720b0421506012000300140e0421004404080c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 290340269 1250 290339019 290339029
    0x801090c020f03120702070b0c10060905070509010c020d1a0f070302070804060c1b171b301b010f020a230703020a12140c0105040b0f1204141209 64
    0x6001c55800c0f5204ca450384071001e00f07a0800c8269084005030b8400003505038208100091101e202c101c508a0410840c3d98455001084802c29a50100080d20401010380310b50710500402844030700050204c81c00b40340e50365030708003251003285000d070104180b2000c0102000c071401071f00f54000036a080a524102040c1e54500c11031243d801160b00303000078a0b141c0030600c004281e07240784011048882d189005d40340c2c003803e40c80d0030800b5044500b0b8415181040086185040c0c140c1c1e1201d00070f4404941000814803a8242000440712500d00400580c010f02004c28100610140d040c4010300d1051040c04100c0010318080a541c16002954000c02450b0b0008030162201b000b00c520380d00381d82060b01d0070b180040d402c01e03000f94000795114281d0790010a2050344a8500e0212078400c1c00c1c0e107800f80d000c3d81003080c0c17511100b01c0701c903003c280180001c00540056200400340d4042100b4203a1900d030016040f501a204159000d64071a895003d0a41c0d202e1010400015201340305411030b4104100344000038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 290341519 1250 290340269 290340277
    0x1206071e02070e040b0901020715050a06050409080306010e2e0905030f060a0e0114010306020409060e07020a080a03061d0f0c0903030712020106050a17010b01031103040204200a0801090c020f03 85
    0x2005d5581c0c000000c0c03c40030080d411b40e03803503940c0910300d100f02c2c041c1d90707100d103011b0902510724041e41c502c1d1000010b40c41c039241c418454000d601c01030041c00d69441c1e00040d2207442101c902290004036422180c40101003e8542000f011819041060201c803505401005942c464000900981c0051610040290000303034450f40601103080204140c100d500066014201c0e40b2030300c500004c80f0300c001004001d1260050030035114440801c2102581d07481400820620035101d13140982c201d50b14440c04144d41e0002000c00810908001c034581d5668517420107841c070741c3c0c8204541c0750809010300c03440344140c0c2500b50700410649109824044003500103034491017410360041034042103070103882c3e64034000e40003c0020b000050429081c2030f1f8482c401d045034021002078407090751910100c41590760103446510030036918000e8460a6030b13565070921000b000040c00011300465030031902e40000440e1401050002159a41c0c101954900f00e05102550039201e00038055403c001000600498004252 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 290342769 1250 290341519 290341523
    0x20d0605121902270610020a08070303090f020a030614060102012c07090e10180b0c030406090c06020c0910050d150f020d020a02060604060f050409021206071e02070e04 74
    0x4035002c0045100080e40342d4070807034244901c440056074860042e070703101c1100780c814501640d0001440e030412108a03100c044006000300345510521084000c03910075071108413070500ca12030408480030310341c00156113002c807940202c1c2c4194942c1e000011b0146035a1059410a02c28002402120b0b524100c0b001c3c030401c004142c00040640c403c5003841c0d80c2003001740d04010515000200034403001b03001d50035114020001860342c00f600b88032080e012491910401c24030160040a240500d48494074441c145900250040e42c070305441c0e10b0103001003482001043c0007405990000c0080000b40c03002c2c840d400724000c10440070700709a800100103540740d509800782e019601144003d0090400c1c60400c0003815404280c1400d18404985454800c05e00c0c2e008140700b030f00315001c42d0469034a000c1080169015800785030310b40a06100d0802850505030400d2560303c1c40103001190b020340050b80189890303400c40381003000030820381e403015102a01c591140e00d003044a20181a4440c1041d901030b1b00c4600240c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 290344019 1250 290342769 290342803
    0x918101202010e0603040302060717150105030403231c02040806042d05060f010e131202010e1009060b06071e0f08070c080c060705071a090d06020d060512 68
    0x40004580c820030000c3d10110000303000945030305050030000c0d501c40040700e0b40380210f1a190503004001d8400341003e48209450000c2200000388800111110303000500110180001040700248074101464a83c07400d100704102940c40741142c150303880e071031081804200030051040000384619040802c034564020f070000000c0504190042220040804140c80100a1000208000e040000100b1960700510b00840f4024040c1d884c0d503007450034048207a66480e09030052204640c001a4003d010040000c0140000550b4000300c10841d420407103809040070032581d44850100411000c4d01c030300404080d0075104075081601d240c0c4c548910101c088140081400016a084204410499040c00555002e404203484105030b01d0118034003441400f070807246000e0210040840d0034071106880616030080c0042107150728120f0789106100c850224000707107550400c032a201075100c918007281018850500141d0719600c003040c507003c49669811007032003000c0d01030514030280700000f450041c07001c613500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 290345269 1250 290344019 290344049
    0x1031103150d020306010902030108011b020c0d050115060c060c030204060f05090607080a0203030f0708090a1704080304030c0e0c160206160210030c08090307050303240402070602091810 82
    0x140203000b00d100095144c070546001164415558002d5812183c12100034000400c00d420110064641c44d401c400060b032020310070b1101c1d85481030711042900e01130300c000070728540080418550140213410003800300d030798051300720108680b9205403c07004545240841c20306003000c03402800c6000a0403010308000002c640840d850f500d010841c3d004540c404091075a8142c0318601a480e50001c4445280988180303000a0f200750041071403600c103030040f80103042c5120042e51405d18034062003000700f00f200001d0002081c1c4a504100400241d40070780c801c1c1803020320342a507007420749800408000030030f4024490712030402200c120307000c1000e604072270031900e0b102c040021071104100c00e50065440010101e003911810340560290f90300d41c3c4141d4401c10b941d07a404c03108580d280b2515800801d9640b040000410710140d440a81096000e5030f21040300280740400010144d030000141030b140e04d40e00266071902441c01911505d00304160a504e5102c91a010344c813519040708034801c00082c0d1031000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 290346519 1250 290345269 290345311
    0x90f08060c033c100f0b160b01081c1b060207060207020405070504170109050d031508070315051f09050702010908070609020a05090f0105150405030f160501031103 72
    0x915800c904440b11040c0c41004059081c0e491549003c3c000b003100c1a01500046134920003201c40c4c3c4820b0310740800ca404110742c50000344030743d0795221900701c5240000c03032000100010255000b10307000701214001040c000700080b00840440b800100787d031003030041c44258080000b0300e21100c140080d402890050301c40c091420404080e200b031443c000e41c031514000403c00e44542002c041c0c000e40d03165135141281c0c8408540e040d4200d849804003e05250f100c1422140a40d2007608400da440307296101c000b40c4036a4400c030321882c2c140d29400444000040e02140b00340c8494600c20698404c9409244244103040407200801e020410701690030046d40341c0b400103c01c28000d402030f100981e489464990313240307258100f400003080502c40482c03098484510009484c941a52303a140501120082030720f075a4030f080d0403c00c1709800e8000382c106a002c14400000c5558041c060700c0c055801d20b8000e484440d00b85040c104071044c19811281c1407500e0605101c80030048101525400380610107034500c004919 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 290347769 1250 290346519 290346541
    0x270b0612010203090d11010209030712020a0b0a0e1e09071d19030b0105040221132a1a04031b0b0a0c0c050612070c11120a0201090f08060c03 62
    0x1003525110039030002080c0501c403180020144003103001507568180b100001d1074020700381e118040149070301d03070b001507814000d0420106411050500c0101210311481d500c500c000890b0708605c2a450108d500140c0820700b034100205c60801481d00006142c1206403403c002903250640500a5030070044a6010580301840c00c5540d5448000010110302000488001c40540c000c000c0c00100c50199900340000703070354201402956001c1142c4030b01c1e240340c03617488200c602c0303440310040c072681a240451448030049514220000c1c0121000000400d80010340e244008900109a003d6408608406000040e0b03004035001d9400b500d510040c1380d118680700f2a8001103280d02c680202400d8007000440c400d055030011030004581d41700c0c00d0345c100390658803020031003640507641103a00045d41c2000000c002c1c40c4502c64070b01502c0d100d0340e2018152000c1c41d010a0707610703548820380986580034031500b40541d03800603107520080c5602020b000c00d00d41440c012586812000e4203400031030001201040e01c0e100d803 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 290349019 1250 290347769 290347789
    0x6081008070b07080a121814070e040212030415050d0b100e040e0a12090614070203030a030c0302070c090c110a120305070512040501020405040b1215100506030f0901270b06 76
    0x1051b00c044c0401d00346c0c0628451392221501c030440d404140041c0346020713208007140384030849100d901c504085035a280c080c0407141c2e00000314038400c0d000402c008606004000e8075405075000c5603813a075440c0c0d4600c2002c0011a2000da0009101d00f00e00703d0090200750707014454106e900300540c0d0201341800ea000c1c0303041ca0b12181250007407528010781c10310001c540d031000c14101158500e681e10245c7c00d0041805030324030f101d5544040e4064000b0040d0a881e68002c0c0c01001c0320949a01d4010726240c500d8441714070604080c0c200801468490590320400da0b8400301209202039841d0103030101a1003507640243c1c0051b60b102a00501d03480c1c1002031031395800365081d581c1c0c03c1d241720341c1d070746039450507180483c000d61181c09500d2181c1c0c03821000c41920f04021310b01a40c00864175000300112908124048101240107001300308940d03d8007800b20b49611000e010b580104c403c1d00030074255040c40c0401c1403c1d02c05480300021165610900c07c5802c2c10038001e541e60050300000440840c1e01c07202c0215586100b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 290350269 1250 290349019 290349047
    0x30e1905010506010e0d0c091104150f0f0302040608010e0a090f26090918030c0109030507060f020f0f07050313080a0c08030c1005061906081008070b07080a 69
    0x1424012950902a0640003a8421482681c0701c40c1e1802c50344e0100b2002484c442c0c000317040302022144c1446000c160354000603803181e14501460606aa40300b0207201d0004070407503200010320142082804079004015155040c0e018102541002d0074043e0086c5000300500c501ea09030414400407c250b10740d164050500e15400040d030455075281800c0090588900103402d0700104a00803000004200303807000da400103140204203410580300c1c613002001d665400845810280000c1047c14900c1d0030034132030304440500c07036103850380c5600190420348125500803890306400d500402ca01908a64000c048a0880040003003050310b80605050145c958002d07001e01c0e001d50309940e50085400320002031829005071148200310031158440d21f8060b100c5c01282e0a003019079020b00500200c1c1c0343d16400040d44184003401200c07541c2701c0e81103000070356000c0f40d2041c3d0128500da814801d45504c031861000203030201000071b1072014604845542248225076002d00390b000b0200701d21062038461180c11040c0d070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 290351519 1250 290350269 290350303
    0xa18020f120d090e010806040317150603190f0e211e0301050f030f0709110c03190813050316060e0a06020a120504021018090f05070318050c01030e 65
    0xb10b01d0900c05410880c642c02030444448a078400010301c000d001030700c584602e503d503503190224150641c415250020180c503940c4002062844826103496060203540701e599141080004115444c00394011a1050096080d020b0b00b031600741c40c02414001388200c00c0d0501c2d00440003088801c441320030ba03203000326101c1040701d036030111b160216104528040c505a42c821502e0b48103012864003090380c0c034101c401407140c03160494541040b499080380d001c0c0c03904104c1001118034106c40f5542c3c0f1070560340006068140c0407401110100121341c4039940c0c17035101340034001c0e4105100d05c60b2105c5a4a0181a9035851038100621240040140941003040e501d54860101c8003595410314050b0081e4011100d20f0001401c0170054a50703220f800d001b081c0c000c41e000b614030750303c3d513809a030115101080346500d888550181c04000404540c0785c418541101c00e89000080c060030000c04c0241501c42c0d03072500100c034031a100d0050002c83c0010400184008007401c00040c11001c400550703050000d483c40c001158 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 290352769 1250 290351519 290351533
    0xc0a02120c0109170a2a06022a0312010b03063c1804080f070b0103050c0312041508060a12032601080303010317070f0503120a18020f12 60
    0xc2032054002c0103078148076070041c1c051001101410807017800380824100000d076030090820b14000c01048041048640b0a514182c1c203403554483c00c05a90040403425102c0307906111002c4100104551840205540d80140d46801402551071012900c10b000d50705681000001080c926a01c3d0811448900705480da034180031100610001c1441800000d1034203014140c911803402441c0c2070f810024101342501425a5030344848d1122040c80d0003590a03280007000400550020954508030180214800c20040200403d6401494140b010058070317070090b03400500c02440b0720f82c0c02c9801c480a41003949030564440e5215030000305604001c1e400380c1500e40b001c40f901801e0660004505c2191800d00d000b441d800590f178440740c400c0780f00902c503034901d903082480103000007610709a010340e5a01c10345040500700300f569111217076540703030b00002102c4c10b80c000244c00440102292583d603000e111202e04201900d01007240e607446041040d002407144805468000d0075980d41e942e0161031360000310403034a003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 290354019 1250 290352769 290352787
    0xb1503030a0f1b32030301050102070612061e060f02010b0a03020123030106090f0515160305041503091a060a1a19050702031005010b070303020c011409011a0d05060c0a0212 76
    0x107034214440d1134400045019007281c07000040001102d048410690081a49924141c0115640342d003072a5003486803a1036400024220312085151701481c0021601a84800c4c40c01a000d0240010280c48006690409114519a6541c040040101c0b502800c00d910100c551003001038ac2c5540c0d1405920b4201d0000c40045103041c0d004d021082038a1420044412550f198010403420201104004984440030055807071460100007000b203103c0d2290400500f0240c90fa806100b07030100706010100040d40d5100c07007038148071042d0b00c1c90303c80d8640c03900018007a06140c80800c5d20350300700303004030f0f608001306102e40ca181010582c00c854150b645682805060032201400805690114006a1003849a07078800044401d01d0f00c6018100c1d580c06c0036880c540b08442d6030a03070180d00a0340e0b05078144e5603500705a0210f0304c0e940808030f00c540d0355500000344611034031207988c01426070b10016074011041040b00c41c00082e000208507410000e0404480e4030b034400c28204908c1e10900c15241c00302c5032401700c0c05107a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 290355269 1250 290354019 290354063
    0x20a03140c130e040503040303030c020709020a08190e06070e0f040513020906030d09140f030a111201090302060a050414120306031b060919050a030b1503030a0f1b 72
    0x200b000c4030880d0b442c0b02c40d540c81c00d10b6001c54034181c0f400b80198200700400c20019001c1d511407014201c2c2d5005035802c003a9100005012601b00001135004102241e0401052503990143c1500d0f0700f00200040045902e90b901080d0303295001008030050051041a4030071580d02e00e1114560450010700c10710981c5400c9480401c0d01d0a0034004a00840402022882e076190109001403030440c19500ca4440c1d5107080d808410070002c0d590303420741000c044215602c00e514113014401c0324501030340c0c513129098098003e102d0300c0c1a0510001002c0c2c0d15096451000a40c045a1190020742c480d40104040e2a141015500c0c810712584d06000c0380b117810014885d4080c10805544900c8080b030a0700c038018500094000c80b1401081c0307156200ba8204032504003031400d00f040306480d003c10328031078803110b0300e80012485c003001035002079030640b840d402045202c00d0b400290813560403082d406180cc0c070031301c0100030f450401510550ba0600c10824400600300011821811a080d0400c1c1401d440c00c107240a650 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 290356519 1250 290355269 290355277
    0x1080703061e150c0b040b040f0f03020d0914060403030c140304080609160e160908010510081002040b030f0c21042901090f0e0a060e070603091104020a03140c 70
    0x600d5840c00d039400e450940c05903480d0104c50343c01900e900c4d002e035070300c2d034942d101408002c0048450001c0c1c4a06e01001ca00e1030094045013034440d070001c0403e02000500608409103a900c10703001900701a44140c0551102c50a03102107039031504011203004950303e41301120b0b40320341002107800d00c0007050004c0c2e500070018401c0e01400105060b203402c0304101e8102000e03428030f03000d000c0d128140c05000c100c03240c1d281d00941a6115861400c1e000007901c800b40fa5082d62401d0b189400c400304100418802010203200c0d2451109041404504d0a450003c0e44070302400014a4501c010002000194a0b4100038044801040070500100c1041c800052a030b44061000d50781514004402412944a803c42c00c00b0a00c03a01030180d03101e06103030b10b029520b00160440340a500b0009444903e91040590304100c0f00904078480c9001040510b00704103a02e04d02002c03680b1410401d0b090080f00c40124403281c4c9040c40c9101c040c3e901503a10140c504003600908580c002101c4204400010803e22800b024094 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 290357769 1250 290356519 290356529
    0x30a030f02040b210a020313110301090c06030c0905030604120315030807050706030501050409050a060c050937060c03050f0405090708060406050111060f040302150a060f05100c0201080703061e 85
    0x515690300c41c64045c00890008850500310325039800280d001160b6120340c00704e50384a0003000492101220750b42c4107110350541e17119601003911204c0d2104070315005481d281c05040107400800b02440d081d00c50800c41c0304030344c0f01071040c1590f61884403518070390140d80320040d40c0c202c6242542d440d41c0d45002e03545e440d040e129800002c1d2600c0c00110b40d500d010b01800c0205a0040000e11075003026840f92802000d0020640083c40340420185138140c45490051702420018001d0f1079940109400c2a10041812068513100010b40d02c07041c00480c1c1c2080340c0e0181140c0600e041e985501d000f1701100010b1285420003544035081c0010085220b0740b0a80d45441118142c03010f2061544d03c1c030041d40c011264810031501070b0000b2000400e0b0000040410f940140688122010001a0044a507030460240c1321100120744940c014080c0c014414001c200a11003682c4070800361210031030041c0500c03000c1c80001d0403c806000070038001031091700040c016144018240804811100007000d00ca2001d1080c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 290359019 1250 290357769 290357827
    0x6011e140d1b051203040503010c050c0d050f0d140a0606030605030a0b0a06030602120403030606020d050409050a140114030c04110f030703020c01110301170a05030a030f02040b 78
    0x10034004041903406500e10400340c6080071a804580e1520207420401165010000350000b00003035954800c14000361014407080a19900c50030034003498290b41c91004082e09200d002c01940c0349100340020f19070020161fa2400070345407110641c541c84284200101542c8085c10080143c0c80c0140784140c0da07000320f545070400c04c1304a544a0040d01610114414540d04d07030450800d1801151400c80c071203a009558107400607403035459036206001c80e001003044050080805080004141c0c15101d1600980044c0c0000c100a011544005105200394041c0d41900ea4071034003c0f5111030425004000641e20034001c80d8803030741e1140044007040d001c100c043d500ca44503007010100c49080a00c120319003807a21031102440c04124220301001940050072800802d07500f081501c1c00d0050030300c502d502c0b221003884102d0742d0f075141000c440c0c1c2202aa1610101c103402091041e40023031000411941046003500303003c1a020403a01601d030083c0174a41c4811080d22000680489a040c0015082c41808a03045 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 290360269 1250 290359019 290359079
    0x6030309170703050d120605100207050114030f010513090b090609011113061404080d0c02040b0306240a1e061b0c0b030a0b0618010206090c010207090b030a050601 72
    0x4140c0d81e107000b10b11000d0f0407a04140340c4140c030144903807903a98840d900410040384243c0d03100085240f8400c002d05450040c0c100b48800d001960388088040705201c1101030700c40c150308080000c4da03000403061040714440c5411034244c0b040c2d14130305d8008911854000c400700c4a0351818800e103035110102181c4c04d41c02546484565540e903040c1800752800c1441e0f03d000c1c00301d250700300701e4141c030701e10014000110b10b002c0500c800121a4130800203000503220303658070a840d5903580d10510054500b8500b00034400e1700444200101c0b0603d01d00f4101d9000362014022842020050100d0307500929038120112010200020f500b1000303140a8800441e9003d560711034401188400c51007403104c441000500b01c14500204001c1d204000002c1c5800006050001031181624000601554031591084e102c03408504001c4030b0f5982c040c08001d90050f12500603000032072a4500003900c9140300e000e51844c8a80d161402d1800d61801c2068030f0015912100700c85407035840d442440c1002a003041d0940310a04255 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 290361519 1250 290360269 290360309
    0x121d0a030f0908060c070318120204140f0403030911030d0305091e0d030e07150c030e061602060c010e03030c340308060102010912030c170c09150d06030309 69
    0x2c18a04681d04100076100545905544070721591080c501901044802c800c4070b906401c0d0507850f4401024881642e42000001c0e00c14441500e09000da00c00c4264aa6030800401544a14415038042da0501c1d0025240a00e0f10f003004204124041842d090f00c6240351b41441950150b00540c01020000110b44000c00302d110071a80d8146950040c1340190048251405024040e4200460102c450000d50340b10684a045003101090052030220015003d146030005142d0420300d00c040000b825680c551a0520440c121040f1128826009010f07000000c0c015002620a42c440f00f82c414511082ea6580d0524000540003500154442d84051403150300d2050303049480010181d49814400d680304d1000c0789601c007504e46000042465040d1754854845100041c0300342c40d030301300360351007030310001041003801c42c00801c80408400348034a034900b0074040c008a030b01240151030801000f151070a10072550119041110301802c0d814203411800e200003c0100350300111408240c412401c049040c0203010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 290362769 1250 290361519 290361527
    0x20a17030a1211040608190c050901120507020c060903030f16051b030d030c031401062303010506040b03040c0e01080102070b07020c0108010e0c0417030a021e030307121d0a030f 78
    0x80c03044000041c03010042003258070300540f00e061f8130819040b220640340a0288074041030b5420402c102d000030350001501a92580c2000c3c005e01e655020707400401c21485e0a05000e95a01300e80810280b080c6c0020828011550f0b0400854100418000304140c40d00b842c95807819040c0c1c1e1950301190b20340a04109882c031030000800303a8503030321001801801c124260401c1600144107003406101050b40300d074404c01e4007a6010798814000c00303150f40c1c3e00d1586818045c030b1400d03854144000e03a0880e20108010843d5542d00400d507400d4503510507800303989403101e291454040c06181c0c4242c600781c5240c0c0001407202010341c040d1090600404440400c1d6460310720898455120711441c0740450400001848200308404041d0b9002e012009214a81511070810031078401c0c0000e4241031681c0300180102d5801d60511018184044807a1003420b00d0034141c0c442901d90000400c0101003010244800503041440d42103251600103081c2480522840c07501c0d1151100e40c03540040d000b250203411820840303132203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 290364019 1250 290362769 290362781
    0x6060602060709090b0d020303120a18020f0402030901020c0a0309360b12010213210c09020c030d020706020a0e061303080c0f0d0809120415030207020a17030a12 71
    0x10340c1d0324124004e0400d210b501c024842c00290781c0c3c219101694500060f20308200030a4205284200301c4424503080040d14242c0d02940c0b0030011008179001d040c0c005840b164100d46002e507040b200580c81c1d5448980c0703a402801014140c001d1803050303010001c1815000750b06042504d40764800c030348401204140707a03043d00c80c042c088624403c21161500300c09021541c844200c902e00101b03081c82c1743c4080340c543e9007680c1142035070302c5074106080340c104140d021071284030348402002420720000030810f890b15442c9003011b2250030125600010641420306007841101c1e281c0c04201421521081142000d000a40003800e5420209801b0a040e80307540c90800141c500f0000b900400407801800c5644020a503000303404110303254031600740c00022014061000c3d810001040e5a901c91516000c0c10381071a010040551902c0340000300811302000810507403011900c440e506016071b0343c4003184042281d000c4030386d00c004290701c4400b003442070b07501000c00107280203540c0d0381d42c01d03d08080d541030150803181 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 290365269 1250 290364019 290364031
    0x15010f0f05090a1d06010b0c0106080a030c02060310030f20040501150c0317130b0f07090504050c0d05091b0f030a020906010c0501060303050403060c051e030603071806030606060206 80
    0x304842c00101d00c044150490400381d22200705021542191845103071804e0801c0e0001d0f48810386c08590140a003900f445604000d010450081c095059107440103400c0f42d0844102a0080c1e00010004600104880c500c000a40d44411500075850940c2400c2c403071480d0b4244040601c502d2030711075010703a15141c00384a040c2c40000c164275404040f9401c0548440c4443d180071411701440311110245078048101c2d9510542000d1140321005143e40f0342216001c1c0c00501c40d42000c00c10710107001c0c21544c0020f0200540c0d01c1030320001074580310b03801440c015014201858101b1414042001076948002c20103618102400d401038044656070400c00c1589000c0b18981e1b44c150303106d50381e02c801525141400540140c0c040c1000551005191120b0f420348078650015000308400041c10800c0100c035104184050b04140b03415410300025000e8200c64020004030910359000101c003042d0a9642401824020411580c0a0141c40c0141100c031014000d14881510000e260040c0090050300109409100f10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 290366519 1250 290365269 290365279
    0x2060105040213090216020909160e0703020c0f0d180e040b0a0e0307111c020f01080a110a030605090f0103030206130501090f0f1103011e1d15010f0f05 67
    0x6800c11003400000d40140b403407140310451141001803211100e10081a922009110450030b91074a070042c0903002802410800c0c0f41c1e4060203000b00b201c05505c4044040d2501001c00300c0317580c1c0b41c0030411800f9010b030552001c060b000307080151620010000d62000c0740642600c1e001c494140781c9000d010b210308648100c0e015401c40c000007400060103110030702d50000d0301d18000113031104e0800f00e103481d64026803821600e041d00c0700c01c00d07a514500051700383c8240d480d580e00d66490341c29990100b200c501c80f102c411414405160040380450026401c0307000c1c0a0740c0312590584481240b080100640a2441114041c800c840003049410f4400c5404a0590390140c0040c055030301c07040c0000d4a19081042e040d22195030303945c3c000c0001028075039600c5046001d5400100f400c4000c3c10250520003003c0e403000d10036894600e11140903031500800c28030760590400001007a084440b25801e00701481034401645001d60701681c5c070390742e5201d50300d54107907204045030004042d100c85000e110f0761402d0194982c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 290367769 1250 290366519 290366521
    0xe060a020301060f2a050708010b040c140309010605040f0c14070f020d03050d050a0506090610081302130510080f0109030804020d06200c0c010503040b010302010507020d050f010b040f0c0206 84
    0x13203400350025800c48051031494070701c0702d011880c048020109038242281d09400401c000c115204c424090111504000c0b41c0400681d019224050b281c0700c60524407042a850210006403c10429448240103100c00783c03090141c100c54241c10300080c00c0c040c1c409000700b0400d44000c000d000d0300b034080d1911950b00401003502083d4540030401c44d2088950100c00f000300402130540806600e0065502809582c5c20214590a241c03042101e455001044c02e4003450306404695155917102c420980c1202c0c00380c0c143c0e90f03018014004078000c5a030380489007859a080c0800d00982c100c2814152045171b016405940007061a000418241c440607130028000400c808041005803030301001c0146035511a07400040c20503c034000d9240c00204802d031031400d040000c18000c0790710700180b0501818035424a0114510f140c1a55840d91580041c00003074100400402c81d4011500e6000d001c13201150040c0440d8480c0c41d040303c440d40a041e251000700d004c0c1d402d000d801c0412101a000307620054006401802c16 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 290369019 1250 290367769 290367797
    0xf060804111e2d24190e030a0c0b0307020109020a030c030b10030f0b1503011514030102040803160f05030d0c0e0604030b060108040309170a020307080705060f1c020d0e060a02030106 80
    0x441c845100c003258141403607107000c501c1c030310304c0350b005100312004115006020310900754040c1034049110400350003a00903141b03141c0082c15088058080e1407102d810603480740c07601d000c100e0050002800c0290084400403000c410300200b80c030807508880c03044004240b40e50b58121009890310302884001c020130240c105d5000040c11030385510b503010103141c5002042a02e0440020709640555120782c90390360400c3d0b0244280f80300105218a0142c041d00298a010328141c8ad40b40d982c4698125200c0c003803601c58421b0700f0412640f500c59040350300001203e8640c1c0000c4040340c01459140d0508000c80c8555000303000ca0300b0038000752411260041b52565803551104010355144600810403420081c1c0b01c440030803241e000403076054205101500800f2000c040d841811300d0050719400c40c00a0303a04ca0001000380e07079603102c11110382542030068603884020865000b00c1409401c10014601e0b4004107030f44049600310741c4444c00003d40f21048541c00d403180d82c920f000721701c0700707010340000180e100c154544 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 290370269 1250 290369019 290369029
    0x80a0b1807090b060d06030b0411010f170417040b0a1814190305071d0a091e03050c0303010b090f0d02030d1b0c0b090a0801060f060804111e2d 63
    0x407000d40c003d8021460500e11070805e0f0100d802c190000c80b4046000018007050084440b0007910108003820040c4440d6107108018000e04400114466400c4040d0000343c100004c421030484515080001d0a4840742c4600710058503400401c203180003d5206049903c02d079a80480e01011560562542080e080c035a4092014030310040101901c8042030070b07000400108200090310041100070f40540078207007180d01140c441d01c0301910f0108894103100c12040818208100880344104110024040001502c0c05507030034004d08101002c140000300001900c2c0b4500d50042c017010350300b2078881078070340d00c0d900c1040740020711444065015400440d4425505000c3e91000807141041d80040903210260341d555080406142c01c040040c0b44041800c846900f0880f9040c00030f084104003e0040314107220281ea000001841200308104416010500f441400300c0500840e840140991241080c14461303040183c0385144602e00420304a02c058416000d040484240c160b983d440050041051404200f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 290371519 1250 290370269 290370281
    0x8040804090c050c0a0c050f06091e0d0b0708060f01032016150c03060803070f110109081504020909161503020f0315040f0212060103050405070f080a0b180709 70
    0x82400410851880300b0720017007001c8103115110786010942d0a007090148071180c0b0843c90740c140241424854444c0ba60341d00d481e04581d04042008000380c00012000160704078030380040144c951101c4400f4014502da028940921540d825942140a0f500c14001101103a000116524030b08c100b1200c00c00300701c098840101100e40c03441d00d0000188880d516034211511400128400d1142d0300c1041c260034503054020403004002081c06182000215106c030100310b000404000c003104940f1700c00c108183e020305d424030702600c40d4200311540a07940500c0111307442e4007500c0503840344003203500050b9854400220100c2188030b010b84448038501d08240c1c21501c022901c0c082080c15020300c04010b030b8201c000085e503c185000c000f0000c6485051007800f003180d46080c9600500d0b8010401032401000c4400400d4201d00300386400611540e0300d08007039042c60b003c9e8021400034209032030001451680040c66a03c0140181803035400740d29280340300e00e6020039034004036104d41c0001c40c0800c000c414681c016 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 290372769 1250 290371519 290371541
    0xc03020c0f1f020f0606010203040b07080915040306050910020310060c050106080607020d0e0102030a05070b04020a03051b011e020715020c1c05010f09030509190909050703050d0804080409 83
    0x260001070058490700c2441480c0c000c102c0016408068420015030040203c550424002c1c0040c6180c1400c282d0304105902c62b1080107018524001410881c1d6150040100030b002c03a0000080e071545e483c5c0c601600a480c00b80c07448001407040c45540c5400000f00e1007168020011100800c201d246483c5055400d40e141318000d5406545e509000684c0500601c9007610440540d400f03000315883c0c22034041d000200584070907046500511008000680040484640d0740d00411032007a6a5640e100041c4080720075003000307040d80900d11143c8034541d0f104414006083d002d0b21402615010135000e50440810303a1103140050703000c00c00401101084d418000406038161041e6405801c1c1000420141800200c054003801c210983d15030a005081c031031980801c400178030501c922a0750b520028a18018089514130458080c55548850b0032070311400c20042540c88002c1c4085019130500d02c0d2a29264401a50503000e103840c81c1d55400e120300800340c400c65000703450505060074a0000002814481d5907 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 290374019 1250 290372769 290372779
    0x30324061112040303020106050114040b03070c140109060605040f0b0a05011b0f03020d260109151208030610080c0304230f0109111e0f0d02091503010c0c03020c0f 72
    0x42c40c620814a0380144040e6000c0d40001c03850610340800141603480d5004d1410810500344800c0c804411000c00301d039041110340c42e240a00c00820700301a945014804101211586422041000c008031500300304119681282e08004410700d0480800603540c046213110790080092009102640c00364031202c6201001039139207540041282d9911a100041700c4094015078040d40300c2910560b0f001c080e0b00da510b000c0482c12070044800c00d040348080c0c05c0600590103501e80b01e161880320a41c0e00100741000748500000e403580c849150500311080c3d4401c1d205075010f010780c07030314642c9c8040c040c14102d03015841000303d103480d5658944481c03d515054900c0008510415120f0719203004c020000b038201441e0080c00041d0090007464403800e03030903949003094003030b00d00c202e10070102c1c1e04031405081a40109032006030752841c0b42c00020342d42407800c18000b07602c81540003e000c0404100804005403080940080000e4165800b0580e200a80210002c2c0143d1051a00e40001d08181800c0f03046d00f000905 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 290375269 1250 290374019 290374033
    0x11e1404060f06030813150915140d0c03230105010206041115030a0e060121020613051512010b070f0f11092406122e120303240611 58
    0x1744426841e84001404140400207150a1100d05241002ca296030b60031404d1549401d131500c03c10807001c03081003116505012074001848240d044102c200d810742c007040b0504216070101e02c507000d07006001001000c080004010725004500082e8030003107060710390507002050b1b03907540d0380d9030407140441c0003041c0c2d40c00c12075000d4203007882c0807044051402001c1d58940442c200c0c5145803001e1501c00f05034400001c12800001440d00c00304c5005602c5040343e01911400e03601c0442c1c0a03c8250803500e40d112075006040c1c1d040c40c42d1046420b90250040c1c82c1002c8503c102646d81d5102c400306409a0340d40904002c054150600001c0c1c014110760b08040e22400c3d01c9181c2c009020002451b0010031602c510100f220f50b4580d20342a00051591041c401044030680d080007801d5240e01c0000000408506664980740d130043c880703c40f9414002050300b54008031014498550005883d800300080080780464109000000115030804100340d1402258443c4245246022401c8030384520b510f0700d0f84101e000e02d007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 290376519 1250 290375269 290375273
    0xa090302030601090f050907140d0606050a080f070e010e160314070503150603090c04051b0304030203070303050711330c070c170304050d02010e040e011e1404060f0603 74
    0x480503e00901002c040010811054035105090b141c001b0403a60040e0080441805503061076100b111020788241ca41d0038075000a0318010000b0000780e0800d541c041e07010b0600050f4644009035602c9540d0210007940e0070599242d0340d0141c5c68800f80a011208450000080ea4840c1d2440c165004030480d460042050284955a00d6030b0b44025240b1400051002081290000720003076101c0f0010310035544185107141000350303a80c5560744441d00030301c80c649540105803900004050b10000c20390f480a820743d41d05107480e000c1d5407a4040b600c210040390400c000a0002ca00401003000c800600300082c040b40f405c2000e940b88060180b412040220306100c034420081c50410840c0fa20a5803174840c469500c02c0d02d03041100b46140c09a021000b0858044a00303510100c000c001d450441d40c0c1943c038590248014401a610b0654411030305810070300e41100480d00c0d410540050306030301d98155041080310302400e81001910404028a80c042204001140015111703a12805c2803481010001940075142c0e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 290377769 1250 290376519 290376523
    0x1815060d02061218070b040308040302040e0a02030d020309090604050108061b19110f01090c030809040204170604030801080705010c1403040906030b1e04171606180b06040c02070b0a09030203 84
    0x4c0d154515030b6010141c3c3c07880088004c01c80c03100601050115503040070314642c0d90f51014410ba00000f400b803901d4451100e501d070703010050b140c0410350050964000340601d050080d901d80115a0381440f03109580d0120f00241060710646041c2c50000c805041c06549803d11812292133b1410703082814803007003080ca41002c1040207008031400896507120702d0355003c03801c00c1d480e0030040d8881074034a9252082000029074801c1d4041c04580c0c3c01001c807921080003100140081c080c591040c0350084c3d050200210030710b40401c05910891180d03e42400c60b981385c41000366246e0b81c0380200d81c04200301a03901000310300e00081034514482218101c9280c10388500d005003d9a0183c2d204541c00c02010007030004d907190024803030110014442c645610b52506403070703c0307400d00e50002482c110035100160b08200308030000c0c0520341054002c007007808402c1592403004c1001407110411399003c1800c102041d842c1c98640190300d00e4500035802040c8460030841441455406142001c043c0651104000010380301 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 290379019 1250 290377769 290377771
    0x140f04050106050715020306060910030b13020304050d0c020f0607060b03031911010b03030a0c020105070b04050d0e06070507170715080a1b0c080f0c06040b1815060d020612 76
    0xf030756010740340c10180c42c10742c400c000d020080030000f900520408c1603680f1410250340c40c46200310360b11100c810540c54154001c05c3c00500290704200e854912003400c0301940c00450150388680120b8060380e0000d03008643c10500120002e500c0100e00441d01414031b460406000001d014100c0010300c040c1d52400a851039011801c14030218901081000c000e6810a003034203401d01c114002404200d820b000081e03101d20441182da03041c014414490025a4411001d94041c590b0010419116040c23a0800d1a651001c21944030300207113900ca080e200600f0300c042650202d07a8440001e040b01d03410440204c080c8400c89202c0d109038840c80d0b10000305094160000017110005496114140c20701510102c180c0794000611010302d6517598280917601d521100007012141c214007083e884400002060145100b840c1d001034140c82031400348030502c00c48814160007541d00c0d05001c100340007140c1000d515601c880740c90034041c18011002440e0390810070b42074207099100a10350fa1624030000780200340500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 290380269 1250 290379019 290379029
    0x6070f030515041d0a1b06170106140409020a09090609020901050f0717070b160503130b1017030408010c090f090c140a0e0307081b0103020d06080111030714040b04140f040501 77
    0x100e51b040c0d1101011103440850301410306880e03c084042d4503c000c407100260184681780420401c0c0c02c8165a0b8501c81d02958003503c1003071400d55580c50010402031540c6950300070504918900140007989810038403c44021480684480d410030800c2ca407190550f4010b000151a5005501000300700e0940d60401400c1681c4a04c40040722070605924400c40e002800200300c05101c020000e00504100d8034400c255802c0c2d0186441025680305500805d00000691140c85060076140c80b0404032000440504141c4071160300801802402c0a800c40e1021030900c503414080c891607070140200d11480e0071072166031402c2e080101d040010645048a41d90100350240300180c1c018000c8000e924040c4038440003030008400034034180700c02000c0594020840108107050540c0060f041009003050340103030009141c80700081050308800b45003402541e00c204e840300d0001d03121090440594610341f090310701381d40d9500e12481c2401d0030314451401c00701c080010250b0050070000130344020741d264001c0c940608 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 290381519 1250 290380269 290380283
    0x40e010b0705070b0309100f200415051e0315030715021603020a0308030a090c0909140607050d0b0f10020601061107030809220603060b040b0406050f0f130c0206070f030515041d0a 79
    0x618107400d0552f88002c8840480070840100310350070b6410b4001e0b0036610718000c2100c1541d03507600c0d01d003010740c55800410b80c1c40360903000b41c08001424405a546581c0c940b940d03a000da806117a810400105040e0050000a6000c0c00c008401e10109a8000146078411880e040c0041e142d000ca44601400c0310180d40700c050511b07203034180d001c1001520b46a284121002c2c030003d20081c02e0000300034080b070140028a451850703844c2c400b09800e980e848100c006403100a0010200d21802800c000d4880d5000d00801010580c480c034001c07003591000030b1000031203800c4440b16003408481d00411020f07001e41d07110059225002c0c2001e001c0792041d403264200a600c202e0001924042100a10080e92f5000b4441d0348503500d4444c2c20800c2e074644400c0e0800300107044403500c54034101480021125103c2c9050700302503034036205880c0220394000501c140100f041d40c2304d1250450910400300d0503558102c0d100015600c5055420210742015000004d032990369083d44400c15550910362442c042e010b5006441c50 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 290382769 1250 290381519 290381527
    0x121101020309010b040b0103021303150209060c010912020f0d0f050702180405010506010e0a0909031b051b061903090804050310270206030714040e010b0705070b0309100f20 76
    0xf0f140500c12108020306c02c3c02e00f0760070844407403070315280802c0501c0007401c0c950f00071291264014150b030440703101900080c4455202c03064a51160b000b0103c1c0d0380103c42c5441042581d807106400024441d0003403140c01c00514055946c52800c0300c0203000201d07024180f1001340241001070b0789603034088921000010200410b031400e4140300b82518005060700c1e060010a80044c4140e4444007142030644850800102e00eaa0451070100d076800c10041c2c1c14440c8181e030032000000c016020584032040c10000c092810802c950908100d03440c854410070501e50070b83d000c00c4209040c003a800119141d0b00900e18542070a42d500c020034204070350f12110b00a500c0c5d860308086403000c00800d0320500c802412108408201269011408a00c400703082d01c0140030f001100a80350f14a400120340140c280c003aa40106940d55080058503604061412134282c051041c000c9a404080d5090f2449010102c0041100303001e0769000e04010714044c0b0f10115000d884110032000c1e1100d01d441c4103e01d400500c003443d50703 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 290384019 1250 290382769 290382791
    0x3030201050709060e18060f040203090313300f0b0702070509090a03020307020613090f0e0c121c050408120301051002010213090e03090901030b220b0412110102030901 74
    0x60740030343c0d400000600040000e0040103840d01d01ca22110048407942903080d5458010000300c80080b0040601e50040c0000700b000104400800a0403150801007203c1581a4507007941c10b00c4251000652040400e900c407180b22480c4140213440f5000f0301030138040c4a038140a80364010b046c502282c0d90300143e800f0003010003150a20807045580f00c0004409011a0481660700a481e07200307003003000e8410000400d202d070618191310074940040810300020408807280b8000e620103001030480c038607003d008000759021306060001841201c0600b41014040f59289800e10042e1880c084e5440410040c05100104480e441000200d0f018030880c02c41548940c584020041d517080d1107242c41e4216401407202e4104c40c8080b4081800380c03080c0500c0400c81da00380250484c51800740d0b0100726403205035035000005100100c1c50550052000d4061f0240c500b003440100c12014885020040011101c0b01c00100420040c0d100c0354264a00d03442e05420340c03d544050107083e40c02c00d0702c510640d65514001128 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 290385269 1250 290384019 290384027
    0x702090a140f1501080408040306050c0c0f07140f030a03030509030d06030b09070f141c060f05010905090304061d060c06070e0108070822050309060d0e07270f1401030302010507 78
    0x303c285800d00c1d00034840d150a58840700c1030b0149100c010050381d119008110f144202d0800d83c1c040080c40c6046a8502800311100c1d981d808540c411000c22140d00b00c0b1035074860900e100024a4544090010407400b0301c2a50304a005140c02444003009002c14402c251040d18103014010055000ea80c50002d41e0401d086110304054656100078941903401200b080300300c1103981e110101361002c40d16550015103c4003407400001d8001c0c002481d46207006c4811082030001e40c0194183c41186030104042d039540014550b8034492070003600c0220b01604c0881640c80641d0982c48035600025000e1410408441000c5162901c290380007130100e140c00c0341501d07203943e0001d451139110100c1e16102d0401d051845854844a0020a03014280c9098640c40428030104000310342c0c0c0484041c002d43d40d25694040b6410081c0761180654180703014440c2c002a0025000071080031030900710082c0562080d000c1c0030b28000300200700022503100d0315540541a0069001041340c02180203400200b020b2814882c018 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 290386519 1250 290385269 290385301
    0xf09030708010b010f030e0a06051e090f250e13030305070201090c0501110703150e0c06040503030a120f020403081812030406120e031602240702090a140f 68
    0x3241c40e032520700e800c1c0d4560307840401000c1c443d80320f040009909503494405c605107080000c01404250070311043c40f030128514050101e1006005681800d140c41c0d00c0d1106441356101280e8040c1540000d00380c0310300c891303550241e801c20186071038070740c40780f50752800103503d4a48121354802408040710580014185c2600603a58410041d1008000500060f980c0b403801d808903014560400031003100d500d003001010000710b00035641084480c41040316140000000d4007030018a008e07c0d009070300c081002070804209980a896000f000346040c660b800ca030484000f15040303555080f035519020b0401401d030040c401000a0350007150740a95034542444d501222031a00941e190049030008841c0340c8400c808016a0203442c0c80346025000c02d0484080b0b00c02500440d20b041c1700c18000010714003220200c081524203010308c00d44201002c056280c8802c0c00d401502084981d12901c204612001490b00d9000e0640c8000d0100c00040c0c1e0882d4030030405445601190303a00360580d0040d06000700e549104800c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 290387769 1250 290386519 290386529
    0x13090b06100309080703111015051008010e010b0f0403080406080a1109090f1003020a0e07080f07050301060e0d060207031206050303070201020a0f0309050306040b0109060b03160f12020f090307 85
    0x500540e0a207944e03400c0507100344d14000d4204105c508403800c411034188aa200c03d21902c00f0700740b10421101880300b400c0e214600c2401d10034244503c140400f02d0143c491070f4121101120320110980c43c246880b1510f5000101a646000040101200041d0b1701400341c000ba00342da0f600c2009a2404108801c00c48407506105032512500f03004500c0d0594600c035426a2201440c101014182c90300c142081c1109038035040250300c41861b460100324100d90310750f11445588a662010240d45600410403120a0182c1d001e1000600407c010303c6941d001e55603a24048802071310745051740503e030b1110030881c1c01c1481c00f200091850011520b561140e03000d00d00180c50214041d61601400d0ba0002c1c0d6952203900006085c1d00c820b103010014140920a0b0400070600641070b91450300d824034200340358060034006c1904092601401280302c0d105031054070302c1641410800e10444160f004107032401c503028040e0758200103440801031489052400a04101d60001861984a0f0030203010103091003081d4002d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 290389019 1250 290387769 290387771
    0x105011d0a09021225171b150706020306040516090605030606040f08030904140910050606090a03050a15051006031a06040f06080f0f0123091501020c0f01050a050913090b061003 78
    0x1840460300002c07a10035901d00c982000e845580301c803400403c022310040f45018006103000b1801909100c0c00e9001540301c0c2c1c00485041003540c1e01d0890900e0010b0501510300c0005600d217009100030743c0180010754103c1b8004020310304065484144948010b8036402441e055000400d0204407401e050003110040208c07070007240e400c1e103010200b09907120a41c40c001000d00c1d0720b40703011600030384402003141c94421020f002c854038940c503070400b00d07135440850350100c80100701d8881e5000e030040d6034400c00d8040c030f52201080f10301341e1500700d0403400751039040b202c02e1085404801c4101c040d6504002807008203808060080d040303142010152458070000c00d103d0943c43d402042140090900340694150b40240c00c204400d01041c4c010b03013811540364109a50410223640620540341c2103801c43e0340a02100741e0032100c0d0f8101b18020f0001908901c8811780c007186080c4500403c1c1c0f406003000e080100c07005080c14035134003100b011490503550440700542d04005c01e041070203898200340021303180007049410 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 290390269 1250 290389019 290389049
    0x1209060b030d020a0503091003021917090d0804020108151905010906030506060d022230021f030b18101703040501050a0e12010e0105011d0a09021225 66
    0x5d62a840c4e1140c0700183e44591380c82c00b03e200c400e0340254107a91801c034000c1c00e01012201c0c7c0d1840175041d11074441c0850240040c6100080040c0d10026075031124561a5980340c8a940b503d50064601d0503011f4200c0c4122103000440b00d80c2074942420358010074520005490301ca03441e020000d401e80c81c01d904820105070400c010050340e504c8010440f001c0001484005994002062041c00610b46c0c00810008201d1640350015400c2d1031103034409016114000c601004043c01080707000c0c140c3c440c4800a4200083c2104d020f201c07034900b4010044043c1d24100450a0b08102c00044e440140340140c00d4076210008061103050600c0341140c4015003075140b41e0000008540c1d00060f03a0f0700481c0308042c1040303030000b410181d8902c079007103001038030700e001e04a201c101c880150030b20302910013111041e14030b40ca020000a00c0c0c1c214203001c01091018807c403183c0350340b550b18008000e80300240c8183e0304103444401d285c0c02c80900304400b0300590007503040ca0901805800007282c11100d964811526141c03502 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 290391519 1250 290390269 290390273
    0x6130504031d010c1a10030c060e0415031101111009060912090302031507092601050c0901091406090904050d0801120c0b03270c0102060a0e060105060a1209060b030d020a 75
    0x30032450003c2d5034403075518580d40e00c03c54485060791b0790001098400b004400054140d0800180750b100c50089074144001c02030003000a1f00000d0900c005040710488441016807035005044280341301c0558026035407900b4400c10b8040c159400714008541041d5515000801d001c94040c1c2401210a0351a00351040e600c0c0d03800080d96040880c80280103c40e0080115201d14016041c0700c0092144100c1101900c00404401010110158000009501b000300040d01103c1010456a1841058540e0402d0b01c2c00d00c407031b209902c070b01002c10039000038040041d4645540d6115035980720704c0c030610040603000072040b402080b60383c5c1a840041e480080b1010f100001d45420408401d8590003080103450b83d441240f4890360030080c45040340d07904071080e0141c8881d034021505100058017a0219084d03600c07035001da0303400c541c2d0481580005401c480014045407600500920f94501e052804a000403540c4402c501100c1009200701c0d08555182d100400a040c00d00855950305064006004403e10769 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 290392769 1250 290391519 290391533
    0xb1311040525020115060804021201050c220902030a05010302100207050f0f0f090414151003020402070203100f0204142e1407060203010609120c06030506130504031d010c 75
    0x485061401c044142c00760220501c02d5108030842c0c6003290380d0b400740707554401d0003804038841030380c060340a40c00c486d40b0000010014003440d40038200503a41c1614159801820b062502c04080d03903040c1000035104002041481d600107140900d028a00000d044d51442c41001410b2a407800c8032015500f2001d400c11080e0b0700e080140f480703c2001e0703800803039032441c00700041c0e1040d010b0070080c2c0e0b20280b14018801848070403113640008881a108482c01400c0d0b82d803d40300d048404072502c4100054560051005040c242c000d0100d492018044410000166070740344151140e03110140c10003580440c0400c500407041a44103911141551007807950246052200d4241d035441c02d00c1407940b52400c002c0c9080c940b1a240031469034030880351540c0c440d0384038078003c0e02942c820f1251000180d100a8049481c88000a104403101e900c4581c0c94100e0b8a006010790141c54020306c2e140d0b003c4882510746a43c045540240343c8214071a90750100b8002400000f418401200261641044090402c4200003645 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 290394019 1250 290392769 290392801
    0x130b0f160804151d0307050c0111162603040803180d021f0e0301090521040b0a030c03020f0f0a02010f0608070905091213030b060301090b0606030907030b13110405 72
    0x20a0f601041c0c00060841040c62484d102115090901c40020380b08140980425540340004090b130303a00c0c0042088445d07841c1c1e03420024000b000c20012032102000001d048402c2d001310f5200c9100c5622004c91800c091506580199002d4100341d04006a81c4100b220801382c02901540202d89440c4642e0107a008100d050b403862001d4119007600c034803a03040c4e40b406001c5e851180c2c00010003c1c0039a000300e2034170030384580c06001905c8040c10312881c2141c0421481e8280c0b001c0c0c84031640c02c0c80c10211481400c501404c3da694045003410390800c005548900750100414814120040c20341d62080503d0000342110401150000407526000b014812072038081016411100403000101d81d80c1c540080003410300030140c0f5140d48030b0000041c80601803e00c83d0200d002caa0084110404d10f0762484103240c00e840c6c1e1144001c160581400000f401840c3c140051030304111800215264180c0301c0d03490458440d81a01c002e00b42c07044e000400c400b00a02050b2074620010309580030b2005040407100b06040d054 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 290395269 1250 290394019 290394053
    0x10609150b070201022a040f02071703040c24110f030d020d110706050106020607020c060405010305070509030106030b0a06061404120f0c03080d0c110d08130b0f160804 74
    0x1078005500000d5a2081046024481c20001d401000b01044680300e1070500c5c404c2c4141e802681888150160405140b0985030000e4201603d51039421801504d60f02c03542c8010021508040380341404541c100c90700800a5003000c1d48480540842d44e16100a00701c1600300300c030751a160f8050035000c184580c02205840c00e015440c0e4015031146000030000c000703080c03118a00505480d02040c00410302045400c5181214810f0b000d5840503200c0c14002c81e1101d40000c042504210204010042d95101e903001d07951020251404600b03050220001a080d40d26a501c1541c40c44546401d1115140142c0304120003001c8074240308444c02d103109441c6840703003e0b9111b211580c1040041010601005940362540710354020743c52140580c80303140c1070903160842c000d06412185005064540c05000c0c0c0403c100032150301e00103120b00311200004413505040100908010b013410024400040c540010141c000c9030500f01c81c02c1c044ca443c1d010320001007a030200180410a100040c1f0003c88e0f414045410740c1c007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 290396519 1250 290395269 290395289
    0x2091c021f050903010e01060311090f0114060415121b080c0904021909080705090112060f0e0102071a07090e010b07050a0f0803040b090714090a0612050601060201060915 75
    0x20440c032015195405a00f0f2410380550800b0348842d01e651040d880302058901c40d03940b901da28410007003030080d1385c10704844a20078240307508010b0082c5500785d90307010401c01d4000c00543c0f03032a0302d81c405c204510700021071900114000d102c9554903810700e030260043d004052005042400018440140025000391017011034100008100c080c0761541d404407006e8005060024101405128005088815500c14916035004816000c200c9140030300300e19040302d0181c02860103420180d00c44ca00106801d12811140d07555903502c103040300c4800e00140c440e4a000e560100c000d440b290140483d2060018069410031062002c03e1003003403003c4040c00e042d142d02c103070350b41d4403840c46141c29403a00d6450700000e00012040e00c044801c10541c04000c5214600c605110b254944075124200c1d901c0d0070303c1c025001c02c0d400c551020851810004200d607403111248070080754440e42c40b130a4030221201c040c13055800c0c0d000f2500502c0050b809004480081c90000000c01a466a010210042d040d89006020b440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 290397769 1250 290396519 290396569
    0x20303060f010c02040905060c0c010c03090c140103330803070203060115020a20030d030605030d050d091401050609100515160b090303010602160b07110310090602091c02 75
    0x15417655805009400d5000d403c441c21420081040a1140c1100704244825070070a040a84e13164868081d00802c2a40182c010038082d081ca034600d5050782040d41c689042550b40c0282e000c040c902d002c6001500b20314000182242e6400d00d00700d00a1071115000071545034800c00c6218010380f400101541100c6080451855081903840100e003031111046000e4001c000f100800e21185861902c0c5851524045040326004501440c090303060f64800c0c800c245e03040e00041c541c000000d011380c00500c01602e03150b1002910303913115912410100010100440103039540c00800c101401c10f411030765000a10000c004500900d48000242e42510b0880d00e02002c007400715003800302400e49503901e58403e070b00560751500c0d80303017004030940c1da40c000f4070440005200300c07031105031a5003a1504507000e8800320b0750708616000c0c1039100d2046680d844110f890709403080c82c008111000652180c01c86031445400050703038a181102c100105050704008440014800c910120b005135542d612070b440b111642c180c00ca481d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 290399019 1250 290397769 290397773
    0x730020109091113150807180503070b09010e0607151a09040501091203090308010b0a1704051f06051305190608030d050705030c070f0f0c030809030d020303060f010c 73
    0xa400d0700798000242141081c0c1c8001600c1c500001070055070012511550203503039079003c0032041413090511000812008000b003040d0512a40444200c0d60312012031b84501030361040481e2a20b29141e010600c1028041280d00031503034817848842c0c091104031515400e0942540314110802400e81205495950b02c000410300b6800b00074003441c40c4180140180321178501818800d005c1c0010860031504403030401c5150124a00038400d2001d640d4066903100400d070300f007020a8520b544203154400500407011034190071a0000e002c0c41c0d00c124410000781c2203c1c0360040f403464035a9002c001448003d400c04105000720f45884000c447e01c040e680d0310100d040d8440f00e595030340c10b60900f0030300110242007030000b01e45210000000c012001000308108000d030340c2c102007100e4a0000340c0300314205880070011b25010440a1907454042c5014400082c1d6542060341c510708518032a510894450102091508103468180085010401c040c0040c618614004001400b004510301145060010302848541 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 290400269 1250 290399019 290399027
    0x3051b0c13020d05091605010e060f07030f021c0c0303090c2313020909060d0c081507021504020307050409060204050a08010203160905220f06090e07300201 69
    0x1010000909181c10700401100440041c0d840340424020441c2050081040054005484d4003010100303000c0d036601d603081038011541c1e0a04019030740d50002091021004100440e40140a1030348282c552079101d0b580c2242c00707400c0900140e600c1c80003400b04010180e903160003030100e61003030394545000103a2000c01c0c502403098a02c0c039080343c22071802d100044a0b008441d40114500720b04125003ca81c0290076207500c0080c1d100d0080a241c000c0311407004512241414117844551a200e80003c006290b03d4048a500e000310400702c1c0b9180040c42400d01c04288e40512402c0c40c03400450b82c29101f2031615401081d510f201e18461a4003d6503030304018428400c55505403405400005c0c0000440d80e62268164041d4006130781020340c0d2a81048011501406040c1550466102402d0700d14006007030801c140d01c0403000c08091b0313a0980c6401702c09903414541e20842001d454108000125684002852490201e994100b2421000404840c103034009045030000700800e0480100c3c1c10520321440122 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 290401519 1250 290400269 290400283
    0x708090a061b090e15010507140a0b160203121512010608010203060415150507080d0c02060a051602031902010204030b13060b0907052205130f0c0203030403051b 71
    0x34080925050903070150b810000c120501d80012556600d00050b180c0400150003901510303225454441010a0f6149500900203402c9041c002c3c24018003211542c02541d0424140d400200c0e080240f000401c484c20701e40300c85081c0c0001c8a84021814808010b0306601110720240614855062150501c546c0303aa904849114011a00d002400115aa520894084d403c141c0721b03244581e00701005000802642e007002030403508032802c0340c4001d40c03020b41c0548007a4041d0b9816603022804019180c060319440c018540894202d034020181458424400801c440c4098441072002c000c0d001182062507000054031015a2500070240380e28281072004e03402881154002080001d120782048841e10f02000642c5c5c05074041c80051004c00f08050410195020440d000c0c0081a01481040850a075000c0904000c5006c01d49150013140ca83c000203e0712410490304004107a07d81503030f000354003518024080c0102e000d00046065040580d000703881d5001c2e40200407480c2c4088454032a503500708002c24 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 290402769 1250 290401519 290401523
    0x406140d031112070803010905130f06020a050f0a3c052a06070311090a1809210216121506120602190c0c12020a08010c03020915040308030708090a 65
    0x142d039400313040c0740213035864000f481868041e5282200142d02c28500c000a110100c0d44074041011070001c0790740d094001c3d0030003c0c000c0c003042014013071061002819030040c0301c1800342d40c0f603a40d1710035124100c103418210010790a8030031000c000004040c480d410b0314600c1102d48581072041c0c6031200300c2000100342e0035009040e1881030310001907140d540404146507000d101a550240070304122800f4100c10b522956103203136000100c2007070411001a0711501e20342d08072100c80380858004202e0300c070362200d0305000c841c049500b45800082801c1c107404201412060051078118440685090318103400c1404001025181c0c2030b19698148840181c0d600c400702500008502d00c56211590910f40000d4010b011402c41c0c120115801c0202d00340261043c480c1181c1c00f070031f410541401e00080c0f580c00200200d049030040007404010030030b0202070052403e5241c242e600107031201c001070100000f0200324140200ca2040800c4207201040c00d10044a41c0040c190a001c070705034803501c0ea40ea01e0000e01d0880 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 290404019 1250 290402769 290402803
    0x120f0501021b1c02071503090212061e011a0c150115080c090a091a06042903041a06011e180f120f0305040f030b01050406140d0311 58
    0x45581c0c0003008030030b101000c0703422004840c006009200765243c0040c0c4100c84030003682c8600003c0282d107200f00055090a040e51601284444042c0c1c0442d946982500d844402c54004104220b4040340c40c85e95042c4400304a0742103c1c00d94504203d054030900050713102d0300e42c0240002e1103104944100070101a001c010051640c0039a552001129441d0600682600103800b40300032030315100b00d400a5950f158001044141e240d442c00c1e03034100050130303400c081c1410140c1c40b00e5028965680e00010708000d25001c51a4101c84100105a428408004001d903404107014002c0c000820791641d19000d0002e40b80c4640c44071074407100d00680c0c001e0034408181c80a0300c04402c10007900c5601010b0040c1108940e403194251588030b01030801c103540076000e6000c007007000f003d0440205448000341c0a081e4081e05040380b41903295909402018800c0d001914850600c10040041c0c0c10180310348001000c0c6001000e814092a00000b002a400000040d0070003641483c0032043c881d050102c0400a290f03210 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 290405269 1250 290404019 290404027
    0x70306030b16260a0b010503041101120e01020c0102041806150c06090606032a1413180c150203031009021e0313050c0a030203120f040f0f03060510030507120f050102 73
    0x100180f0001c0c1c2c203c8a14030500d080401000041d40144292070050340c2c4104030740000c1c03415400446040345400c44a9413040d46030310039555001d00a1005050741076160001507511824401e05030440ba0400b800a0b0141f45462003c01400d07a801c41c107c00039400c189050100c040b0319040c1007000d0034584030054811440c2900000405c01440310346a448060713400312800300805071102c0441c1020520420f4800152519070805a04e0041e49400100d245100009413901c0c614810050380c80801c2c07000c41d43d800b455107080c4000103e0404500030410070744002c40c07451a21003074a460b036620704e1046803a03141c0c003c02d050740b0540d00c09003a0500f0070541150580c4901e00b10f04c61800e80c070344041054a03280103004140b0342c6030401c0c0d00c114040c0e82e0043e005284086001d1001e02441d482044400c200310018400442c416804a6454000305503004203110401d0030b5007000e50443d2800752440f0b00380313114880100005a004101320049582c40c401801c1002c07150b0928810003000407100610300c0d44005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 290406519 1250 290405269 290405327
    0x81005090c04171c05160b0405060603073002030c0d030e0a0b03040b3c1501080403020c040e01140907151803230d02010c08070306030b16 61
    0x10700500216050607038400c041c02103002045898080d004401a0b030310a208880040043c0a0f80c010140c1c0144c40104003050101c80d00c036030820703000c2500c1c202c40e41c0d00030b41c0030f000181c9410803e81015107a00400021103101007045c940541140c086545072200d0801600c60640d503040c401c400d880c402c0684030a008415074075004000fa229200390f81d105883d80744d00030611180983c01d4030f11580c0c0c0101c0074200d80c0c45005000403181111810340341c45040c1204508060104400c90080d80500c81010b4615400e1504201a1701c0086840182c104901d010030480840d0b40016500824401030314005440901103070319501501a425100040001c10024030000301d400149010840784800321a0784140b091800480f1020800c11099070484602402031001c11100c03400031003058185003812070341c0044c400c00a800c064105a902001d82d41d2164014006500048120751015940c44e0070040c16007180e0741d45003900000307480c0c042071984410000300f800340200400d100b89203c441c5202c420300414 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 290407769 1250 290406519 290406541
    0x7030e010f0b04060b070201020a110a0f06120c21090809030a080c0d0203130b030a02040e0a02070323040e060303090d0b090c09060d08072d1109040305090108100509 73
    0x503410b00703402940340134400a9603489643c01e41d400140e0590203440301d00072350b88a20409070301c428030071540f281d002c2030300051243c42400204001c4c461900d510702c40401c1d19640900304d0302203503007040c18001c0190102c80d44502d51090008510140940061070b2007207400c1929141c016a00e0f0a505840340403206014004e081021348448442c8100320340841260780301c02c80e1280201d00380d5420662290300c0070b001d44040080030316445100c01c40300604090f903401c1c00030f003040d2007500c415681550001320502031652205035960302004002d0103811424400c069011184141d01c160b02e0401c0c070390070100e5041e68052044411200d4010102e1007041d043e0b08140c00d41c50401e55502c03800b4440c2628403009810050819445508000e1880745001201d80301c40044e903004020464031650035650320320803a03034004003091803810702001860b080c0718203150078504051401802482122031204010029074440304035000d0710b0081c44c021031103484000d80c5a0700030605400c1030350b0000c118803c0008070780309 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 290409019 1250 290407769 290407781
    0x3020307270f0f0503060403050d090b0103080309010c0801080c0105070201031103091c020601030302340806071d0901030215070c0320190605030c040902030906182407030e010f 78
    0x41c01c49030112203a440f5403400c207544082c4030f5250950400c000040210b801080580501010b903403001c03a41d01e11503681d181085109800c2111400c4000c03040c000d41c03000900c121040000355040880381941424055562003d03d020f5142c1041400505401164442d8000d582946904407285440382408000240c035070480614421941050814242d030b00d51002462904030b80c0c05401074124501e15010706030500c1e100a81856083c181c0d2182c103070381400641040c20040c00200301501803810248401001066030b80c41a8070321240540c07007806d1131f41d60030a0460440343d04445485204486003445681e42c0152100036103500c140304000814013192106402c0c400481030303030b071280202c0341c1001c2044030004a00852045c0440e0354003840a1400781b030045804c800c52520003402c090345e900c4030209a0707204a80c604803d40011007800341e8003800d5885085447c0800780949001e0704031074040c0c1c0311902c41403a9058a40503000200d0011402680446c0f103040c1c0303850003400746000d04010480038041c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 290410269 1250 290409019 290409029
    0x30d090519030e01083d06020a0c090e010b030604060603051903051206030c03030c010b040f14040f0201170106031a01050406020d182c06060405100302030727 70
    0x396802a000d080508049120307010b0707050703d81d0f0044440c01c10044030328000003840e440700030741079626000320b83e1396107002c1111908014281214484200b800c07049040240e50140f03095501950000b80068042525541903540b40d02d40050740a00741204940901038406d0125094010300b000d1009114039604200b0580340228122030100305049240b200701d80000c0c038050002001401407030441c1c0d001e1031015070084002803c8504880d52400042d08603807104040c002e0f03980d5a80d023100e5460410707004070440840165800c208800300d60541139424100180010094141c4c04021800c5a00544411143d034072030350340040081d030b107410000d402000341a1440b010040780c04008003156120b0030840e8107a66096014180c0d0a8800f80c0c140e8040001c1c3c5a4100c01c05803007000800c403500010007440410000c109041d8251211255032001284060610784c06210104000d01c00c2c4d880d0b20400134500d80d442c0c81c00603a20754414404032010b06909941e69211118210703001464100469030805403a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 290411519 1250 290410269 290410273
    0x10f05040c0e012c06010927050c0c0c060d021c060303030506030a020310090201020a0b040302010b0a0911070f02040f050a0608151605030601091e0f3c08030d0905 72
    0x703603c1d80c0408141a4503060705607894107030220400c1440d03021a9006405c0308040c1440f4614076241c4004c8401e000c1917044580180d01d9208451300c4c00c80e000d01503150054840c0c01c2a511300031008448603202d11036810858010200001c04500003c207a81c101c0c0e034a40c2e0140d0040b400340c4012a4200083c100d10f21090300000d0410000c11224980441c1058640794000c004003c00380111446030060708601130268158001d00c800d030408078000426041c440c5201e0303030000603000994400c110034422560010b003210340c60590000c070701503002001c035a05a5041081e5080c1d558491000130098411000c48501650800d424002c54400b50341041e802e44000c0c4c4152000b1525101c200c10412400301c42c0da02210f44052030b014082409400215004001850140c0c155516030140100c16906046182c2038200c032000201b1081048400d01d2000c0d0202c4104601078002c03080840070242542074514246008101100040324404980d0600401842c0c3c00c2e05c4e01c5105a0764124000c01e400a02a00c040c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 290412769 1250 290411519 290411521
    0x14070b09030f1603272114160f0602150c0708070506060f010e0906240301080d080c030c03150a0504140a110c06010e04020123031b04080c060705010f05040c0e 70
    0x440c815060500500c4055240c43e030170980361603605a83c00d01e00c0280c06103e1840e14410340d0210b0001c0020702d520110090003040542650703002d80c0094906030b07100c1c81664101030001c0c4000c680c046012050034580070419035141e190129408000d00c15510000e050101c005401401c100d004140c00e44124000c445802907445c05e00c0c01552101403800c203840d404441880002d040f46401103521500d01c03044400c40000c0c895001d00003840b607000f030308250420352203038412080741c031360201016910650240145040d800d080d02c809055005c05800b40c0310f843c00701c001402194a42c0b2040a005042c0208140069941494991004041500e0360b2641d80d0034191584420442d207000c403a030040ca150700a000581c60702d01ca410411001400c200d040010794910b121902f030142265a1180c140000c5680d40c80c2000d181240400c100426444c881d00d03401d0104116051020071842c075010015a2400d0340c4800e24074000f4014243c51070905446072030b0000340020700021034145d405a0707158a00500345 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 290414019 1250 290412769 290412797
    0x90f0702100c0f110a060207140c0102010207020f120c0301050106030b04051302090f18060a0b0108090105060a0b0a090305101e0e0a06180c0803180114070b09030f1603 74
    0x2610804102103002c036041100700d0f44054071904003030002d1948081514083c150039551002a0380c04441c041d00c15148440107450700c2c480501401a10134824002146400d0f540e0303000c102050f80100c2043e10410440b03501003400d98040c06840c0c1080700080080204e9030b11a03001800501400385480d0007a40707801c0000d00001b030340704a481c8040d071700288000030700e60710721034021069040108a4010050114030031441c00c0000c100490085e8802100804d484902200042207940018000e00a681c18a8103111444e03c03180b0340f8200b91021712501c60b503285c032040300c252001100342d840244980301d1106e1841090b4a503900401c20800d0400d110464140c0e040721110aa6106007400e01c10b981103c0d8003100003c0c1558060444d6480811040d40210740546403404500000d911031682900001820a00f80d00510081401a00c003420a1a02022542c03c85041402082d000074808a6004007081c4010400c10644100c01445002c00390f031403d0340a5070088400754950100d011450160a180e4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 290415269 1250 290414019 290414021
    0x11d0c09040b010e2d0726070f020a021207050109080a1104020d11030906070908010e03030112020604051c0c060306080a240f0213050109150507050705090f070210 72
    0xc0620b4200507074404030703420142080500c00014011141d00c84503100303034940101c01d100e11480013454200340c401d4546403030b07600039011003041e4240e11131141c102c030f0904120310040e10140340c01c03c800b0f1500000900881000744d10b8600180c9002c1e40c000321240e4070307200c4a6000100031003644e000b03980728a040b59035002806e9507021403c5004040380703024128000c45003816409000d05298442000c2074032200b400040802c1d500c00e031800421a0010002c12440b0703508072584500400381c40008124071011903072500e4590006010340030720150911100f8042d0340e0380c00181c60141000400321070303203c01485541c842d80c1142900c2261021000b200005200740070744291001c6070004006401c074100582e8410564440074a0b682902091901c0c030741401c00044c1c0f02d000ba1114081200580d0345103500411510117000341d00c4141046181c20307003482a40ca00e0345110302d860301142441625143c00d03140c1b072030034100940c008680045442007004008524144400d0080087e6002d69070030b0b85110302154 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 290416519 1250 290415269 290415271
    0x50601020a110d020604080c120712020f0a0801020a020721020906010c030c060c0c051204060c14070305010f0c0f0c030e01050717180a0b031302100e03011d0c09 71
    0x240580c1041e44040040750881c03550040d9035030024512180c64071150f0000703c898102c0c1c2c001e480681c1c04007803140410300b0201c00d0070801124407802001418a40482d29140e941c170424004d00034418039480600c19110340701c00c4409480d4076002503444121400000390f48480911a00d9065041c90041202c01a600c2c002d504c081074025022201e107944102c01900c62000c0c1d040110200220b0b00c1020011841d00c2c1728940071080b00b0342e21400c801e181814140d2528285443e01c0b0140f0104000c1000f1b0300307810100811569038411440d48550344500169410039559500141165082017a998400001e50703010b03c9a540154503010b12190080c2011030b01503074038101c010013103002111000c0480d07000303001600c202031041b4230340e80c00f4140340e007020340c510741007803034180344006648552442524001c00b211015004948030340e41145480615403000500590b00030780142c08115211480034440d072400c00004901074024001d5082c400f441b030042003031560003007200707006005012038170b0714064a41c6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 290417769 1250 290416519 290416531
    0x12010f050d060216150617030c0706030e03070606060305042010052a150106110601090f020c0618070824100f0e0f0106050f161e0f02120105 62
    0x10107400400d0381d81c41c1d00951190300c0030304602c944a540710340000e40103811045501d0310842c01003800c0b46440c10f82d191801200c10191500e805c240001020302100103001021501c89143c041000402601e2880c158824854094141401d000c404513080350990055402103204100d041e03884001801a086800314502003950301410f1089001940e5109601074809207990300c412540c5820704079540e1601078032803804000f15400442d04d2143c002c40038548140140107604164a00341048210f02e82c446405020b16510182d03540808004600ac9906441496810300103d4040d403c140400c011881000e0f448070046215144011412840210343c0143c50490081581d00c01001d8940c0a03940e510000d00c00c06070100c010710000760680045121400502060b01c410141c0d007003001400c2a1144141c02550500004000d10300342c84600d0b00c1251030540295144541c00d0075640703000c000307100b10b00b0880c0c01c0c1422000740740c4003070054407a001c1044c81c0c800c8440303a40800000b0302040c00d8410803104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 290419019 1250 290417769 290417779
    0xc09090a02070f060b1306060306140906150a03110307120b03030a0509040906020c011b03060e0c030c0703030b03030c010f180b220f1406060d0c170304080d0512010f05 74
    0x2000c0d0004d01c2d03d412142480800421802d948600880d1000442e01c06500440000340c0746c0404206800b00015075841c071140c103846104c03903481d1010108001c11902040280c0096000465442481c401d81c4050980c1c440860100d0b600d003810140180f9000c040074900300428030300207111701c552900208a605d100c1d0740342c0300d5900f002d2101e010000200042941079600c0f540030000d040303800200707100310400800c030200c090f00d100b005001c0040460b030054008103503002e100002c0c00201d4000c04156507014008400a60b83c640141ca0210301500e4203403009501848080f4141c0ca440c50f040d0803040303000000440c10009500342e103030114100c45104102800e0005070780301150f408242c1403205a440402000302490f2000a40c1d07034003211282d444401c0e20450702c0d02e110042920340038025603030005001c80c0c0203900e80b0035684404442c000288a0419001e15808c40f070600c500003803003620003e040c8001036904000050201400c540d000b40e403004081d0111030b0020440440960401e015500003402e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 290420269 1250 290419019 290419043
    0x10806010b0c070510020717030304030c060203060402090d11040e160b0a110a060207150c080601111501030b011d07020c04181407091a0d11010c0b0c09090a0207 71
    0x4101c12075400124102d00740d005a65002ca5641c0b20710880400c1102503500a044191801d00301c6001c2030362100c64000b580e0010420300c404241d04c010031f1615145c12060043c0d40740c49150014000703200ea005602d8000d4144001d24007445214010402d011005413030a0200600045d03501e91204079007940321088071b0a040c07042c403540d18010042e0030301c4107650400c030140300442d044151070800e00c640203ca002d038001403070718200726504404a0000c0d074040804d214140c04c4503400381c40b004004001d141044210451140703c04020042c0c040e039400028041c0c5400d584034200ba0904100c24018000c8040c080078040c4141111080018864516540603052044841040201600395043c3c43c4c5c03020003a0210074008110030b803a40f14402c0003200d00034107540346000340c480103403001d40410301c401c2d484005880400d038030b400e400001c807194444042d40011051200513140014282405051082d50b00200540501c2802c002c0103049401c0b0340c403007407542e02c0b00c0b400c03010386c030440f00c0042580b04400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 290421519 1250 290420269 290420279
    0x3060921070c1a120a0f0605040c0219170412230618010f1b03060509130f020301140c040306060b03011203050d0914010f0f0510060f2c130501080601 66
    0x2000c083c0303d0020141103140640e0069103181130f071415510824403a544402402845240e07201d0316000305001e07502400001510000652211282d0419181640c03150012004210180107201030520b00c014415460baa29010506515101c9141c200e91a8098412030301010b04402485082c4205000c01082c0540d136160708113178442c0300c1d0201a400e42d901c8203041c0d0842500c900030402d5800c201d1202d01580710711494000e090320000d46c0328a019100d04400d0046c1400d03061581d01405070000d044c4d480e80002840072074018a0310b06e20342d03c03104000c0c405000e200082c480080040300d0041d034040c80003d40301d2003008040d00c020320a41114004038040d007030000740a200a0440c94070401e0000400aa2a8550098203c800460000359954400401c02c585103d886880b0001c410090100424500340c0c01209030810303070b40104030510000428440903075126580100700c00c120005000d078144400d9141c0d440c00c02a45000300c0c81034a00c1e55448480c42c5a0384640e0b81203640003802040964070b02 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 290422769 1250 290421519 290421539
    0x30915070309150c0605071416020a0801020703080912030f160309050f030c120f0a2a0602030610031b03240f080c011b021e03060921070c 61
    0x12002c0c4a441080010090b80512840140071a0b81e01c0707401030050280340c25422a00e008201105000fa0b415075803a002000c0020b4030510003211816120301251400011400310140d032240d10b20791300018401c401c040e0301c208410301840a00044402003030707042a0324800e40c007048480000600c1c0b01070008901d10342c1e00d09101102100c5060005000f80641c680500300080c01c508014075a100103085180d507071003048440341c0c00d840c814840d4108280d402c801071080c4968510344082042c000309018150701d6265040c107040001a0307140c01a5612840d049000e5041281c180d4072541d03c0b1080c654085001c0c2c010fa88a8154064450142c2c005e2854143c000b4809028188183c03089003403400902072a00b0030140c003030a002180c00400320f1034001958074100b0050600360402980c94100c00d000001c80c034040016030f50413038090300c1c004c00e0b0540f03e0b084185110852035051081105200004401040e0264188190b580400048c000010042c88903c03402c61b00400c42010303a04200240c001c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 290424019 1250 290422769 290422777
    0x12020706091e230c04090507330e0609090c0409090309080d0c08180d08040603021201090e0d08040203120703090f1a04170f030f040603050108030915 66
    0xc14a0001404002521100c15104112540c00032030b0b2211002c0300c0a015010710030010303c03100c1022090360103c01c0c01066032a19119030085000350785403076024040000602c8900050016452008140000b071203040d041064000760301c11440d10345031426090303144a4030f800321308000060701d405d1800d002c0d40244030000350300400034180480c0501c00450711015602401c2c0788a40a03586084038941003244d12401c0800340381c058014458440780c4000050410700c151002e00020300c88400341070300103a010622014002e076000b00901000200460341503015406801c20701c800f0821a0300a81c0c940d4102021120a005040710030b910102504061034803520080c1d0313000380301a0a48034038042c5207424801030b4010300400c401084183d08140000010380b4602c4004040403110104054540c200c81030542c07155000f281c000010010341811064001c1081c00c520302d504030120395403604080c039442c01c10b030028020040000d080c00e000052201c80042659486100208003110882005610003c0f03540 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 290425269 1250 290424019 290424023
    0x212070210090e0a0e0f0604051905010b101d030607051608040e1e0703110909041e0c050a05060c0c0f0a0e04030c060e0303090604110102031c02070507080a03120207 73
    0x3406000c049103079114030119078001c401c1403401003114030801c1456800e100d2046e4080ca610740c030402c20000030400000b1401d240e02c562801003001d146c158100035003d040d4046a554100c500c124240319101e07071152100c4070440d03441c0c800c40e0020410904054861200356100d4000410510038042150044101c0701e103401d00c0707400b41a02d010395558400c600f800c1e00310b4620035107100320b0f945030101904046005521086916040120244240c4280c0c01401002400c0c5d0080150000040820031048459a410b01151141c04000c61503850a21111038442c015140a944203203000919401c020044c1c1d01110340725005007695140c04000d0001000706410f003294070580d0f110300025420b20114419000c1c501035600c0040704100341c1049010b489403a1407000031035004100300001e0b0f10020460640065200d045207085c440c1e142d004034a1800740c50381ea148860750984001c81c3d81c1c18958018840d42e4482c000b610b110b02c1e0350721303140b1351520360255014001c6210780d00f01c03100044907a802859518 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 290426519 1250 290425269 290425277
    0xf0604060b040b150a030b040f1d1204030b1021020103150518070905212e110c0d090e070306080d1103040e01090911190522050f040b01060212070210 66
    0xc1d201f100041e080c4e80c0a16003070162260f50b6140c0c00060f24000d800e02c00031000070342c02048d25142e0080e8071341c114440c500c00500070005507400300704112015901580100038030131440314140141490072141180380e2008a000c207203042d06011140e185103a048044410082c0301c550415250700310f244801c80d0042599007005402038000c40c4c546c0c0c4038200621743d0546400034020365540b14664500d04801c089981b0620741e01ca54001440c1d003200080b603c10404980c5c0081010000c0740305290b101c1c000c421019100340164034003d414190700c0a00e4008440b889100901d1584a09100344d040762501c5c001c581181c0c000e00c0e040010f4a0083e180307100b81c1e044800840c0e241a64802d2244c0700708100781c01282079213860710302e80c406000e03c3c080c0c4000801340403030b080c03000c46041d110740c1d140e0b0722a00d21505014004000d48a168a1080e0f50b07051008816882d0a015034688401c00014180c02150700329042c9480900104806200103a1144610810071180345000015001c0080078525160360300100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 290427769 1250 290426519 290426531
    0x1a0307060e120a290c13050607030207030606120c120503030f0c0403050106060306090e0c030d0309021f030506030d0e0d0b090a12110c1503060f030304080f0604060b040b150a03 78
    0x141345503081500f030030500d0203d1007040d40c07202004039840300050840d1906040a01001d8200000305007030a040b40d60031030348a95607200600e4244d0401505602c0945214609440007907014800c00e01001c20600c242000c403221619041c0f0454181048a4050401d500900000381c455045110701d9070050785048074075044c6a40c0c0d40c0c41500751186c640240f40025200c4d10100070103d01402003200d14902403010305440c00710340001c640d860288091000815031145600825500d8200b01220b51844440c070300f9294041c0c0c0c00b03010b00a05415241e5a0280c45070012200314a031080110070703105071004101d08561a0030741c488200a01c40603000304800e000e02150f40c0005480c2c0301020069540c1910780f26091144500e1060811804000407030058441c24809942044108200d991000007124040e03e09964070380440d03e07500440e00802c505100380e120103218050b00190041c49148035440030711604a44109100540d080841000c0e000b0341c01c1c1101c0a012940d40d400307000455880e140010300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 290429019 1250 290427769 290427773
    0x20615040903090b220e04030804030e0103061208070308061f050702010e030307060617010213150207030206070506251706031606050301090c2307050102040906091a0307060e120a 79
    0x150f0321440d2000c0d05c0650804d4041000322014490740024440425121071034542605c0181c802000144010100020550090000d0f070083d4401c0000e84800241020700760141e162039503256214a01c294041a04040003511610389186282882c41e5050000210141c00c0308050f907154010840032414000c00810031451a2800c0016003401805504007084bd90314000a41080101c07031180c04000da4010000a01c00000c00d011000490b10000d401d028200d1224400b203061001c5600000e43c805800900f00301800f80005074035001da080704815180c1981d01113207070354000c4015000d0030041240307084540804403804c20444c0d44403030041c0030760b02c0c040c3c451240d0076428035440c1c0041012640c040300500a00400d40301d8000d0400c001c0c104002c2d21402c2e10000039071b40b5070f5a00c1c0a802e40200140401c2000301c00e4055400034441400180145620b03907010001400030204c696806000305d804160140c0785c005441802c40c0c5007078407840d00181c6001c041c032911010301e6013228082c0c8120200d40340 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 290430269 1250 290429019 290429039
    0x709020c011103040605150f0315040f211206030209010e0406060902030115140403020a1a07080406030207050d031a0411090604080a1e0b13060b03070b040f0602061504090309 77
    0xc0310300c1c485c02001606d071502100c0e10f182c20302c400c2c410074081d40070980c403640c454600003048040008241200346240e60346150042580c07031101c00007000d4203039508000300d25042541310309498aa003900d42e111045003410090044030700f02e02c00a54400d92100042080020605010390050700511000c981c882e00c2d00b00c28416a13000380d000e20100c024000d04140c1a0380e01886400c10200c03001740a900d007901c3e64001500207015400740c0600310f0301d01800d00d201b400103a001c403038140b80e010344201d494554415000d0300941203902e081e59140030b802d62151606100c4c5c483c00040120740c41400010398510702c180700051032503882d0b8034000d0307504008010899407a60007610040074030710002c054000c46071400c1c07114001e4000b402e80780985404480c0c80003a848020055110000841c0717032102c3c00c450b0400304040c2070700845054160182c0000412400703150401042a921880140301c1c160781c0e201c40890b500c100440741d5039801500800c06460724585504103100da1070180c0782c111300d0103443c2c011040f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 290431519 1250 290430269 290430271
    0x1b01090803061008090a2a031a0c0717030a06050301020d05060f090403080103030c030c0f2a0807050409051c03020712110606041d030403050303040c08010e0709020c011103 76
    0x2440100020040100524090034038031036541441c03410131410304015545a5640142160060920740c0c640510000d11071142c0f6081c40950b000c2c041c00c03540c1a0b503402c1040c0f006001071102d9090404550000c1c581c3d1030f0780000c98500075803192604141c0064102d040310182c00c041c000c0c0ca00740d511000b00107041d41e024005400018644840084c16003405020070201034044403005000702240020000401d400038141030440f03825003080407010304180b0f011560b16501c04001010901000c00b10818400d0700e014000c101480811f1500048400d028840e481c0b01d0584204034445e03020450a21490806030860010340d0301c80d4044500d034940040b010300d40004100b41040c0066400b0031504244904510090a001c0c040c0c10031031100780d680c605e656124038000f085a40502c0d110b05044084040c56014076850701e07401b40551b911030741c592819507200d600942e02070f10110740f0448081101720307040c420051190840002003070502c1c9007400f03420194114035001d1040b950f0b074040c1004014003d030021 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 290432769 1250 290431519 290431523
    0x604090f05010e01050118031b030b0108030309011103092503061e0c03050c040302010804170406020f011a031911060414100216090b03120f0408120901020703081b0109 74
    0x2007010360404100f00410360050b4401d504001c0a2080d10000001485002c0300f900c1e045a182032180100ea41d03011219880d07680b00030071030980c882c0000f50045022001e10302507102d51009002c5040c040c2035404441c04140c5448000780c003c90380c84450310542c45248030380381d07131a0054040210355a40724182181d42021100e50390070300350b009600441c07800f0702c590511040da50408000f80d09054002d03007080e000b41d01000341409501002f01e014040e41c45110a0030080c1c110040e945c0d00d0702ca1100a40b034000e03040035007030a5030a082d290f503500c90101440010b4210042c004107000b05031658025204030b0003260503030b10342042e0310101907281c54550041000d0203102d44400e146031852824010410300600d142c008540015807104d8800158400b0f03502201d50b034076008101800705a0010741405119003c0c2c038500000090b00244201409010700100c50000b400d60345d1000108031200c195114002407640103070000300e001c0c4001000f040c0038101640c0342e50765a41c1843d00e8407050700d084071005401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 290434019 1250 290432769 290432771
    0xf18054b0610030809060708090d030504141212030c040801110405090106020312074a0303030c030a0f090b1f09020918070201200901020c010c150b0604090f 69
    0x11a4034010010011241c0007540d4504140b180c600e56203c604003405007542c024862880000e5213030511142c02d080c0c8040a03401080800d0300301103490b01914680c890301c214900d2905504012010346040d521038408100800007601480d03c203946003038603c3d40001c00c00c1c010548140004100300d0000d06c5000d1801e002080100d59031410442003000f608016804042150710801900e116042c03415803442e0080300500b007460302e0000d01d0900b50405034800908907400c02402406444003107185a1841d20000101d10030314125407160705154403884119004c07900c0703241c20400f1480f240030700e030f0041d00d070710040034000242200e00340d0301c49001031007e40301d00400d80d902800b21507104481c9120304009002003403086280200c0703c0e0100e42c0c014089080d02034580300c10400159524000e42001d00d030822030030f03a1151000c2001d042c16140e40c020265540c01881244034510070380d40110302c803000f419009a414484a070010034618080d0101441150708150140300004203a00b4600401c05e9184007444 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 290435269 1250 290434019 290434153
    0x105030610060e0f0103110d060510020703030f141b0a06050603011815060b190306050402070b04020f0d1401060504110406050703080a0204050a090f1805 68
    0x4161824001400c0d60000707200d6040100b1069400200d42003c04600f600c000604901c0100168000d04404400c400200400600030f060705d42941c0c807140664804450504d001c800aa00481c0d6406407400020040340c000000300c942c040c0207102d5118462440c0c00703804c0c50141c81d0340c020009404103003055012507110490b800d003000a98050180c0c844015002040070b00101c5c241c0c46020004000081d00e100d42000c1c040f48200307116008003015100400c80580e50b010030200c00103c40c2c0680e00b51800091800a010400d0700e0720340200e40013546c01141c01141d80d152038003008911030200d208998840f8041c001180022038411422000361480b000001d0900c0c94081408203891048003006150341c5d00300014040240c0220580b90102e030035141000c03442d80c503040c000d40207102e240c005660081d000d44002070100503a411802d0b0203c203103500ac2c8900e042c1000e091001b42d08010008009400c04c40710b5103401c003888080000c200c042c045081815801480d02d8054041c0f1903003120f15034588030310f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 290436519 1250 290435269 290435279
    0xf02040c12050f0412030c0504120b04031d01020c120f010507092105060a0b010c080304061b020120091302160209010b030705030406090f080a090e06040c02030304150e0307060501 79
    0x1104003035001d07414442004051130705a0714418030303e0340c008040c024965500351000280e8800d0302580e01612141000c0d4680442a041045030740c0c0c4203d5007240000c601c2c1c1141d4840c482c110010303034060311060300104208004102000084603803100000031600c100b08213001000c400340201c40c000e078200d8407034140d52814105c8444810b8245403c2d1000451a80c0b45240001c03070004800d5801000c0a03400a440626100100c036030511840700a41075200202c140018440390340d12000030b0ad0801c040c52101500400d0301642681d01c100307040349400303220042d0950040c0d0050000c0030141c1005040948822240c0b942408a07004400c04100008001498400b14203081000502501c101112a81507282c41803000307005200042c001070802e0b0711b808001d401c211984020700106580301501b41c1c2c4420502100604045940c03207103076403030107480b4003143d102e007841d100741d155841c005d0b4069880c0d55070b5a103920040108885000c5c10381c568a200031447c004060000d068039502c15400401c2c694581 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 290437769 1250 290436519 290436521
    0xe3d03020f18040905030a02010b0109170a020d050f10020702040c0504181503021002030901030c0e18060f1807030605010e0f0d0f0c290705030909040f02040c12 71
    0x401110414184104070035007026492009072040658400b41c5102254950000b00f0003400060784000c000c2e110128074514440c1d0190401c0403000f0081c0d88818006070340e07401d0b0f40c826141c03002d01d42286030001c60180f0b001d8103040c62a1004503006d02c040301c400350500328486140c007898624a580341d0740d01042c0041189480d02541e10502c01034500300b41042e0404060211340c00002c1116500300759500f11801d0b50030414441e0701d00840c1c0040a095101c00030f018041e407a54006400107000074034100c260f1030300790f010f02c4500e16603a4001d03060288510031a17800c0c082e1440040c00d003d40c4072201d000f22644e10341d61030000c10304030446c030f1003002c03000e050583c80a002e5803900d0b000f079814440881340348262a11385c100428002281241c825101444030b04203044a8035075100301900c11070350114041034504118a169901c1041089010f01141e0b04202d9280d10f801030043c01015034100300200c14052803c83c0406030403901500604840b954039500040807030b60254000c03008529611040740404002d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 290439019 1250 290437769 290437879
    0x90e16060923010c0b0703090210110f2d100501060809010b2d0a0b0a1112160f150e010e100203060f040902031002120a05130c0603020a050403020d0b090606030d09060e 74
    0x94ce000701a107200c000500031101001010143c0d20b00c42030004003801c0c1c4000c10a00401d041c1c1002d04028a5840e61002004040704641c801290341c00d03e0302103602801c20f400446400c00c020071300c0e401106282d0032103a012070010444150300030410381020035110a510010405001161113940c603d4003011141410800802c1140d0000e15050100f01801081c00030400030b001c3d880b064828054003180b418483c140142c10317941014078502035545800302015449020b0707101d090030445408841800c4144c1c107a1000300d5859030400080008078139241007682109264603c010141c0301c00355000300100080340c004802c580b4080324071105011714090319200b6103800264412861141e079449888165651f11688a11000c050b80091006c00e854400c81c1654091680100302c40e81c04801c904120702d0881094030741031024004c80c80812118070700052042c4014005459040409182034015a5584003c0c0c074190341020410a413900004011131900f00381c0901d003500c0d031031110200360f113140041c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 290440269 1250 290439019 290439043
    0xc140d0812041407060e0d081902151006120209010507171306051204030e010306051201020403121803060b360c030c04090e16060923010c0b070309021011 68
    0x120b107105000d01383d400200c04503c4502600c0400403400540f0742540342740f00e0b411801d21006c4400c07260360105035000c01c415151a04500c3c0d5a00551600d4403100f500101500c24803012070310100314000c0158403900900590394050400c0c504095803900c8030078a102c1c603a40c80302e00c4041e00152000c8140d02d4115510040c01542c07070250708280e10008005c4070007030f01400290030f10440c03040c004216071080d00004041e01c1c01501090640e0440c040940c082c2d0014001110040c0d10003c10340f142d5842118030295800700c2116010358649175485c1d200051007000c20654118121410548545004800d204132894a1080720191844100c0304403466038005000981030aa0401c28843c80d0309034542a5001e43c2c1029100045402001a1040c03034034100300411001446a540005802074209456500f210044020241461100c0003e0541d1700c9442d030416010800c5100d5007008240c00910b10b99100d203140c00c002403441c110750002400d40808100000000b5440c90710f14080c483c0078000058145 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 290441519 1250 290440269 290440273
    0x901050103080307030f0b06040906030c05040c0c03140708040b03010501080717070e03150c0301080613020d080a031805060a140417070201120e0102070c060c0c140d08120414 77
    0x1504641d02c0c402030784006080f01c1c0405480f5a500500509180c1c410291f040004100743d40d240da80341d203903402030441c40c441906c403c00080b00c00030b0f4070b080c80e0041500035001c0780e65407002c3d40c44551b019900090520305070310100409005940000301108001c1015100d050040d0b91258034202c00144602030080201e4200411403112010410400d0300301600541c0d0b40c1081ca0a100c8888040380c83c105141e442c0c042002880401c0c040b80c405c074100298165100c490a61b0415501c0b0154031900500c0c441c802508600582558404142110080e100b00a440d01c0c001c222064400102031400c40050381c251403541041003801245003161054940c180b9032144403151030b01e840d8640545900d0719204080521000140c80021a07100fa15030540c0c075007210794100819446c0001e118000e42214104940ca0300301c0850100d81c060254805c16141944005a20030b0542050700c80e611401c01e103851180c2084800901c0c2000607903800c080c0c40028003a580310402840c050414012560210180c00d542c1e0b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 290442769 1250 290441519 290441521
    0x1e030a120209040b0306130b09030f040618081b011d030a0b04050312040b072c040903030f090510060b041a0c0a020a030b061305150427031205090105 66
    0x541008010300d00c55811040180c980ea8020041005000301c4080140d05000c3ca4007041820402c0c0032409500a003d010f981120b41c0d11003103995900d2003040c98000780020305000400410307115006c440d080c00c0b51070500c6041c00d99074401542c82d1005082e071030300031044200404c40341942d100102c40500c09000122640318860580402e0711800c150a015012103500000201449400c0044807070303158960102414914003403c003400340c200140c883e10f0003d95042000200e540f452460410ba83e0106d060081060300c100c010000107020154044092588451240070392154510034500c0c0c9902541c082c2400000510048088900941110400c40e106020030301500503a10241c10030b02841c00d2505a84000800001d441e103211b8550003580801e101001004000300791580c80e018560950b00c504680d0180085001581c0c000c46035107000c521060f480141c5480c150700142c0d006030080c0e120005054400c00d00740045c645094050300481c1c88462400080c030700520855038043ca55100801c80703 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 290444019 1250 290442769 290442787
    0x71805060906030c04030206120a0b0103050c121e0c0c0105010b12040f030306030f1a060102060403210906020c030c0d0206060a062015060f03011103011a0d0507021e03 74
    0x4103004540009006160200011304100c00c01c6040300d01468004100035100c8200c0c8100e50020305080395a40504c0d8101034825031554001e000c0d0030b00814000b151242480e982020819402c14020400c0c545070340600003150000e84007041d0345024245500c41180da980014541a0030f50358181d03c51280040200200700e401e02ca000c1605410950011026440708041e08084024000f150000740a0381e01860021040003500d0701680151900c81e0f1b10886030b5a1342070700581e1205011038001c0c0110301041084074540c904a11607002c039509401c00000d0708007654990a040b84c110303102d9103a0507840002d41300007503001080303803071200149440249102c0c500840490700b0902684507050134411f20380c07803000d1003400626140c5600d5401504480c200f8801e941c480094010640709540150400c1421080c41c1c03d044c062481c0c2c1c0e06200a0f440d03e140d203817100381d1100060010101d00c040005110f210401006401014004c5041e42d004101201c079949400245100c854200381095008104141d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 290445269 1250 290444019 290444029
    0x21201022a031218100203060f060c0601030206031906090617070303140307031103090c0f0418080a0507020d0f0512041511030c01090b16110a11040b0612071805 71
    0x80d00703d41ea00445045844000c1031040c01c1030122007142040c0034a581d1074165a5803540914071400044400424015251003840154807c0380c1058055421060040c800740c2030500086411403000c00042940501e80764140e001c0f5170082e0404412640c0301c0c1c00805c0a6141c05401c18440c40303182000d010400e00c0c50340d0240000d4502c40d07008480c00780100010700568080d910144000c4100c8100c030780d603407600200d0305882d200416011071166980001045503810b0522540fa90601c03403003a05114900340f9252a00b49401003900b60003048004c002c00c5005807104d140303410b002d51080c8040e201002d0303a803411508000f44035089a21241c000d20042000320054841a80d040d14142469900082107441540c1184200c22035800e1a60038400d2010800c640400c100748100c1c5415000e240040c2a00ca086881c1c211041d50200c1e01d50260450342d0101d001d800c08810035080c010320005205894401140f0350703405c000003043c8000d80041c200511541c02880100030340c0c0032071640842c0e0a06000006e4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 290446519 1250 290445269 290445277
    0x3040b070e0913020d02041a03070603020f040b07082a06091501181b11070909083004030e011d0a0b0f091302070201020714011b020607021201022a03 66
    0x80d03c140c1481c1044000e644460440c00302c00b82d0042d00c00d02c04103204d102c9424a031144510704602a116803640028128403034402c2e2295101803081d030030701d03261030001d511080b0341100c4002d81c1c2e44182044120400100c1c410511407280c002100241e04c201584003003410480020701090803a000340c1d804c6070800c242c42101c04d054030032280d8000c0d0b960700d04008440c0241078043d1003402541c2c01e02035144201c3d40140308000038011042c200c0d9072558640c0d0078001a10031404000f80240000e101c944440c07000760340482248034226080003046208840000c1e82a84182c4040e804034820408158055a00000007920031800382c0d0183c124101c1100400d01c40b41d01c601c221280e00702c01042c280c8601407282e080302e0b1641801032141030300400c10f0114000039880124202e026228200c0006900380f98205000c4405205854054014440c2203801c0c183c07624035002283c0c445020003000c0010b0f2f0390741005001d2441c581000584517940070354078071202c2922500150300101800d00000300020004115 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 290447769 1250 290446519 290446531
    0x10e0313050a292a011e0e1009020d080403030e0a1202010e0613080703120807110c0f010e030a0c0f050a24021c1d0603070c060c121103040b070e09 65
    0x3450762100c13120307549400c4013400300d0703e2001c0c14181501c0c20101c00054104142d03000c001545000c0082c10000007008840b8100707402d4a01d9040b21700343e18958065a1321020450b40083e18600510703034940e40b51005031f40150401c50100c3c40001c0d006109040c03102c4000301a0091204035148440d042d000a4060303107010f28514491240003070300700541c401d20650307100101400700840d51003c1d203e1508404144030f072004800040c1c241400543c0e40340c0300d00340c6124041402d10280002403422018044c03855034048510341030201c044000c44554030108280e40c1c491b401869002d00746030801c1c1701c5038000d411a9103c41d110700d2000b2001e00c10429000c40c010300307209142c0a460454041d0100c16400d0006400c4240e65884441644410b85a041001c0d1030008660400101100c49160100401c2d40000e440200004881244150010b07946600c00c1c90544154140b249414011146520035518400c604096010700070051000300309229100740d0b004603450800076a50001d0034040780301c0304002022 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 290449019 1250 290447769 290447849
    0x30307031a04060302280b0406030203010305010f060e0f1e090d0e060f16020301060b0a0c0507090c09092a090e06040506010806150c030f300a0c02010e0313050a 71
    0xc1c106c0410b40100c194001800130b80f000d00c1d02c2c0c0fa910340c2e02400a40091001780d4480d42480080b41c52034201e489001c0503680b080030350f100d4a4559005510007004010710790a07078611144041c050600c0f400c203480340324000141c014907405021540040c10500118059801040b0900c40740400350240b0003600c9504140b0111402810300c28000a40907041c03a500c100e2000f0800680b04551660062106041c10700800482d41e0075503407240914100c642c13480d45903001401d2034000344424505600840c020000810300b00b40078002d0740b58030202d8410304d0075808011698091042001070740868889074081c01c1200c007081a8074100002070441d10004050610510700c80e8807084c07900c1055030544e07440303084000c1201c3c0c64949a4404000c1d641c030640e0320003052003100d52034801101e0900c0e60465055409031031b00740d807602d4101e1100d02401d0b1a408030010342d52540c5011480030410005805481160b05031184101d180c007050203419039041d04880880600e201c3c0e9070b00b2154418110b0710300c940da0461 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 290450269 1250 290449019 290449069
    0xf120d0f060302040504112106070507020609030d0e04061a07080a052104170a020c0603181c03050f01030507030b0606283005090a0203030307031a04060302 69
    0x10031540103096580009500c6460f000911040c4841d0307150100820b0005d44040e01d0304403090041e150301c07103511400000030b03a10880000b048144208060300c0024809041c9070b0528890310002403c142c0c0703010b40b9100003000d459039100a07181038000c81c1c004045580280c0c8000244054603041e900c10940050b1000f04002103d0740400d21420803940c50200400060302c10300c4205803013030301c1b00c8001d0310290340715955501c100b0075194000c0c081b15000d010715002040541c1011060080c107800091007000707140c4091081c400485001e21200d58141c07a044442004591848005030131070380090b044907407164010006100096000401105581d00039021340025910344002604620075047c2c0d401900d40700c0c0b42030250b4940c00b040303c0c02e420091741e150041e036821508140e00011a400090004019160042e082c0054044c1e01094114001d44c00740c5545070060b401082c51030b4000d079081300c0065038803480e00241a400c4032040c04082022941408818916000a2501602c5039007600310094690 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 290451519 1250 290450269 290450291
    0xf09011d06010b0a1e1e0305060303030612070909050102090a12020a031b05042a03020a230d11030f0f161d13060501140c120a110616020f120d 63
    0x440e1030113001200e0350040581c40c905e10004100d07021411112507030740304041111096a0083c0610f41c460040540250300b165503820401c003100d407152800c21603a010b152030108001c0c80c01e009078105c880c0504005680e8610000034084852070750391010f079903440d154401031700581c0d65880c0b580840350001d076041400d8400303217400c1288241d02d9000c0c990040c9081c44141c5014007c080700500e014072544404070440301e892007902039111341070031000014546500e001a40c1a194440f400400e0706d0076407a400e190b01d201418049804c071805101c10b0b640e0100801001580804219601043e283c0512266041403d00d0007449801e02280a0500c200d4a80029092120680400d860344c0020800191500d1900c6c51400400460046034001410145481003126006003220a0303221304400034143d424071620001010303082031040c2e00800211846619600400300821401034401c030132104d484000104000c1d280914039074441519410407410018284400b4041e07902c0e400d4100340c0130880c00180317 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 290452769 1250 290451519 290451527
    0x70e0d03020c180106082a1b070609030c0801110a0302090d050601060f030c0c020303090607080d0e01020a030b030a02030c15130b03060f180406020d060801050f09011d06010b0a 78
    0x5089000d800941d030f80c0856101074942407166048079000c0d1600d20503900c848214003407001c00b924035441ca0103a0309803058100ca1203074004000a5654490a00d1940000e04009041c020268481c40000703086810074000c2c0f24078110a80000c3c020740c4020858015040c0c0c04c1180c5000b107543c503005040d408100000251030f406c00c000100d80c2c1c0710702919099130b1a0100606450386503111680000d10340454980181d0003510166107040e002801942403a0451b800c0040d00c1d8407901c000c035216082805403d82a060318003501412054090001d0380703c404000d002001c5441d500b6901d032203a840444201c01617180424001a0708a0940d59024039031104c0303039021203d120718180c801500c0382c0000006085512007010310300400080b1180c10a01c8038045c10000d400072140f0481d9101304000c00407500242d110b5004000490080c03401003015507981d4506421504100c07605018882c40342d08114107e442840f4801c1c011400c0d1491b039000111040103143e540105010f01804000300050210240d070003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 290454019 1250 290452769 290452783
    0x170106120605041e0c0e060d1104050d060e0c0607020f0409021507030c0b070203090a0e060103110d050604050c130303030906150f06121e0f0b0301060b090a0806070e0d0302 76
    0x5482401214600e8025031040e01e00c107042002c446203054032450740d0900c59003007240d6002000340028100307150361008c10001c0c045a503141d15031070b9081100040e01c0d240c2c0e04031203003a070b405208001104144c56103141c4c02d040d102e0f030046100b01070070020f100043c0e56255003049004410765001500f2455840840c0b01c2d41104450103034403003008100c44080603804075116051038801c1c40c42903039503162000c0582c0e880c050303c40a01c0d44041900c009101010781c00c2c1c2000e500c00014540494010701407040d07125182d00c01108812026242e1003000598200380c0105504404605842880e003c4040b43e88001008540401000c054030355802c4000e100d00c64209040004c882c0b43c03400c2546546103407200703c20310140b150b02c01089800c1d42c0900300c62010700c01c00c0c8a09009030030141d0b030a0003240344100140681e4003031400d010340c0c0c0e08141e002c07134500344200d1015250b17051070309580741c0c0d10404000808000c0d501003081980600d0422102070741c003030311064401d42d0540b040c055950a601d004e80c10201 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 290455269 1250 290454019 290454029
    0xc030905030d0b0a05181306140103140114060303040b0c0709060905040b0f04020d0f0201050c060403050a0e0d0c0510090e0f04030807030b10080a110f070606061701061206 76
    0x10001c6044500c41c0301c01e40c003081101404445100304d481c0e40700140700d00500710000041000346100c0006180c0c07120040542c0c43c2521400002680618003004030020350742c00e03001070741c4040e40c3c074607113a41c0c4160900c200d106550755900032042e28640302c00004c0e43c03441240070b4180c0110000c162a011407608120382c01c040c117030900c028865541c0b075a203100001c2c40125015910f00c0500e501180d801c4001c1100f1500032500a041c0101d1625941c032001010112074004a041000030007040301d80d24818060207000da48207540b180d6595503001c1e4000c266408410940b40714103016800e4038001008000b0341c2d01111340a64124501e1212203400f039a41c00001d9012411100590301004813454400000781d12807031103038460148949800f041201207810008100d0b4125004840d0030740030601580c1402c1d8003110804020078000c6603005000041c1d000248038441c10716001c103044003044014080c2202400700b0385810303048100704c40c1000c0300d01c02e818071400050200701001c544d000b811315000100070304 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 290456519 1250 290455269 290455273
    0x1020610060f050c01050c09030c10090302241209061e0a05070509060a08011a0c030714160602010911041b03021e0a1d0a0609030803180d05071208010e01090c030905 73
    0x49407c15000400b0752000d12054480e0088a081000174a8a900b8840c0030030300c16034855045c1c50441c0e09209245110421810b0040b42c1c1d081440034030303001c0c44014940200745028580440c01c2c01d10410785010009031040e14040c2116082c414041d40c0c40350003a6000c0c2c0c0b444800b150a454100003076610744070714282d0301d400c01070005249120a130010300860407201c01906044003506c9024074442e4900890101c082c65170020040900400da40c00b5045c0300004180094909882d1940c400a98108032a80701c030340540d4403602844284064054114004181554140056644845440301d4004003c4c0080245503010400d968591529605a041080000400c5580b150b001c100a81018540000c04d2201c1081620079855070070069074003400c8072415228001c8403800d40d030b45c1001c0b90304010103201c241c00e90702400b541c4c0443d00300b042c560820070b43d441c0c884d0760300482c2c14000300c401c062404620030f000c140f500400c0103071001840181194061400010b401d079142070210090000140d014001e8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 290457769 1250 290456519 290456521
    0x70905070c060b12060412080604060303051b10020d0c11030a0c021210020f0d0e0703050c0409140303181005061e030102072003010605010c0209060d0c0f0303030c030b01020610060f050c0105 84
    0x82826811f0301d04400301510340030320700d03507802081009442c094000140092410300c10050320305078070420b2202c05411101a6411646007403101812604844400c500c11522464801901c0340c01108503441c00c140b070005145810300291001c3c24030190f0a034004e001c1c80099100c00c05141050014000003030000c1019507070382230180d0490b8000d8001c004840d44c4076181940c0111190303030000d24101101d1344400034090004460041000920400d54181c401f5420319000700c02024061009511a0041440d0f40030602d4454000b503142801a0380103448040c82c01040c0140e69491088104039460210071825002c120600030034064001c040300100600e04040e1001281d600f06624070405801c2034000700703d150740e80c0004648211420380d010f034005d4803841c085505070900d16407000d0301501441c091503542c1c0d0f540c400504003d601c0d80c010f03000256100d440d0360700180d15005891710310070309100604450034a00e030031003d00807203441078100307010207014010318860040050790510925030b002007000d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 290459019 1250 290457769 290457773
    0xe040b280501050a05030604020d0b060d060e0f0115080c060a0e062d1206090a090203060106080601080109020f091e0d11150a140a0e100e03070905070c060b120604 72
    0x1500e42801194071070f010340030000c50700e414001002440b0f260002c0409007807004070344451100030bc0141440e0b4005070440810b20120b0400d000310701c0c1581d4290018010003a152506c1c2d801c60301401c9985111001400c010030581e400003d404040100859500366036041c1070f4020380e04102000c4030346402c100041003580e440d244080114922140088640c0254440483e0341c40d4a40b0590080b0300310100c501e00801d05a080c82d05030317a94071004c203280c00682e1401315000289000c0c400d0380300000007620b100400001d0b5901016280c0140000071b810341c1480d0048103248054068001c10078051595445110407846500b0b002101280c80607050461054050410102c0011004000c501500301e081020301d010312044102c1c0c88039480c50361407100ca0904015402807980c00410090304002c0b200005140303958403900f81c48103503d01500c1d5601056103d40c1490f0926480c2d0b0302921000345040b0400842c140c2010401c42001da000030005003106101d0300090022843d4109002c03a88070b00c20070007007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 290460269 1250 290459019 290459021
    0x21060b06091c11040b0105121b040305030310050105040e070e0d080d090201031a0f10091a0301031e0b01090905030d050903070b0f0907180b040c0201020415090e040b28 74
    0x1c43d0140300150722010600d011300066800715010789000400401c00e402012402c0e00c25a50404170000e810304100901c1c3c900341c180b0350002d0700140e440da0000030600150341a2600c0500c0141402e08059041a10348503124140306401408a801c1c0700e85c80185002960303c2e0380808441607400324030340c1d88070702032031130070200404a004049000c2443c0c10441d103a090030348003600c03d40307140c018103200d5070003800003d02580c02c8036161000288003403c080400c2c11901e45400c8090701e03003401800c2c1d0700c0390b156050601c0800c0425015800200016a070900441c2800340090b0648080e0f403404588860a4501640341d403240c602e000030210b00e000c1c00d0100105000c0018926a1300034411003800707880b2000c01095405040d15051403d0f0301942081000c14420111154400c41010740000e07420f9510300450700750303121241400c1c0181d5000606200c4031341e040d161481782207a02d14044910741c1c02c141801a074640080c0c000361011140d1400101c04031800c2c00a81a58002c4100403420760240d504150 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 290461519 1250 290460269 290460319
    0x70905150a061116030809010f02030f16020f0612011a040e0a050a060b0f03010608150306090f010e0f0a060f110a0e090106030e06070c0203070f0609030c21060b0609 73
    0xa1528064100c611084496080f42c0d070701902e410801c011f203402c100d0f1005603410000820750106502081c403a00050107544e2000c0d00b81c44000c01c109a0700701445104000e803e034042038030140304034414450584020030740440581034521141d03801c0712081101d5410789c01400b44e54055141e0b080200b01f0842061441d800090082115590600c0481d481d001d401c1c0590090118483c0200c0c03003403004015141c4100700098002c018911560310201c05580480e060000449003212a40d0203072440406481b402d10541c14081c010b8030290440440402009848482201000d025070351201101460f0702c0403036005540509c0c42d8520380380c1e1501e640030054040b15565100e070f4403802c14075000298aa0282c02003c6640c0c4206010f400e2980d1401800e6407182e14030714090341c040c440c84a01240603c000b24400d4040c00190300c41450107403135854507003011089034001000a081d95841e4071a400c1c00c0100004641c1d500140104032020b210000c0b03804c500682d07480983c000140380000003540030b0300c0500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 290462769 1250 290461519 290461547
    0x120804050a1403100f021201060825020703020d020406080f060406110301050a030303020714011a03060115050306120f06011203081f0b07020402040506072108010503070905150a06 79
    0x1000d05540d1584040302c0c140c10112001c2e0582c0007400a99082d00a40c2d001ca1030303002c1d005070700500b088040c43d404212060260410400b00d1001400c0c4460800c00b4548c00281600d40c0b1502c00010350705210080d02c454251200a000740600e403400c0d0b0440d515078000001504000040b125919503038180c803661880180c40c15595a0301c1c0150702d02068000604881c180c0300040d05c01d0081e645542d800320025400908183c50018052880307100c2c0100078050800040c5420080503a51650760041500f0020103038004100c4c100b040300da4803d010340080580350300040c205d1b517450b004d2494208070340c10302103540d1240c4c10350300400b000840c040d40c2c0c05001000b194040d61b03c0c91810745e00c9900300c028050840340c00e040c5c0402510803c120480c0040010081a88054005410705503a800403445582100700111034550b0010240070107002c2001150303401080c0c03450b151144e07524180101c0e8803450540074000c0300719240c00010b80b00409003890b010b6030001c0074109100c00b55a44000502d560800219 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 290464019 1250 290462769 290462779
    0xe030a02030d08220c1a13030b1008010203090a111201050709060f08090705100c0506040c03050114010e1306110a030c030605010c031b02030a150204150809100e030412080405 77
    0x1030801c4e08030010b2080200c6507880420760011a00f01881c00d01c841c0c1883c0c4407050240d80c2085164079030002d00f46440021807056004400c20b080c056601602d0750300c03d41120505d40c1c414802c10452007000160003010707941141014054029040216040c2c0f542e6040c0c41d65250700f02024003600b1940901e180c000c49490395908600d00d0f0310004219031041d426070b458015a840041d05000324074144030600e182c071440f400d001c9260406544ca05007411000c6030305855141c142801001440003e003e928140b801d9680c3c8040b030356040c400d05884c2990042c22150040c0321100701c0b801041303002d60100034541d003400161615407607511001405889000c040000190a00c034000540c0d5006801603414a0790540f642941c0c0c07082000f503c10080e0710b00000b6030f4184100001031006c030f088014a180040031001000d6903813800c1c0110090b41e07000c1d0002d03410802101401f0000311480c0801c14042c0300c0502c0784003182844c00b0140c2645140100c0d0001d008030300017110840108050100140115803099034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 290465269 1250 290464019 290464051
    0x90a080d0315081510170303010326030c0d060b0433020a14100204060504140a06090e1902030705041d100b03090f0304030609050c0a05060a0e030a02030d08 69
    0x800c0c1e4050b00300034820480b050f408510003006181c00c544407a40c0c071400c9044440c0d801c5a42d4201441c840d462200e07801c05c2500000010302c00d00c03c80d4810b00e003000424004240c1c20318a503400b00c2c400c80c8002082000a80d00200e01480142d0700d03038215030000e140c90503402d511503440c0c100030309a041c40321004907400700c44401c8103110080401c9106c1884125070b005001c4407200358030307840758551075680d09000b035004808440841c0208c52000d8800f8055a980d56500d660804000105c00c00000340000d220383c405034001c21000b0b610103104c00940c1c880c45580c04003500c2c0e000b03c80441d1401c4030548070304207002004106c0d09981c0000900300f01c411540e00b040321031071015032030003400c041074940c069010000350081c8002000e001c000c503044000f002c02ca442840380503d402e030070754010350401c559030358a40c03581c0b20522508016480c618082180c03085511850140058070600c2154860024841d4806651241c4d940500040b640d00c2d0f000750940c2c1152000340001490050204c599540d42e01c1c2c091 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 290466519 1250 290465269 290465291
    0x1030b070e04090c0b07150c0c0c080c0a050f04150e06030d030603050309060903071d041a07120b030a02090901020406080f040c030b190f0c1d0d0204050c090a080d03 73
    0x3002c0c0464a42c0c001e001400d08900380044604146d1000c4025140d0010090040e11142158414141c140040fa41c8103400300c42c852900d400d51181c3d660101517168010702c80510075503200c020300030888078111241d02400f40c0610219000d080d62140c2401019010140024008403403001d4a02c2103404509035101e404800780c0980840d6654080584941d2050042100d02e0800e60006c008941c4006d04680c0c0c100c0d612803024602c0c1c01c003403013001c00c4000401b0510007084005014800503240201d1750818515107143d0051004100300d48075032105441d508000d49544052140c0e0140c142c026020901030702e4901c469601079809880f03850f0010b210350340041c0d85e2044038070a4901075544401910702003031554481200000d40542a07011515295000b400504d035140f00b07241d40424a544049030741c0000c101e000d041c014030158000c000001c50100300c40399a40c1d10188201903541250001180c0d01d61041444280c011065a540c010315004004101c001c0000f80341400804503503402e100c0c0700160 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 290467625 1106 290466519 290466521
    0x30f0609011401060309020d12030213030f110102010204031e05010b0d060c030605030718020c0c060f030906011e0902070f0618020f04020a0806060f0405040501030b070e04 76
    0x40c0d420b200300c0303445104101c0c01414030b82400c2003501200e40100c1c103200041c0360b0090616643d03106c030b408404c1c02503050b24444960724001118240c1c9914000f5008514101d09549440b640d000a0071590310500899059a502011900580008101c13a090b556901c407003c13980d03552120010f2156494400c4c014440f14000c1001044c00201d0300b00240480724550011402900000d001340000a14044040f01080364040010703940c41104040604100030090059071160001468806039140b1b0340166000b9501c50b0f098a070140d0b44e411201e120300c40000190ba0041104060070407440c1d040d07a01806505000e290f0b05102e419090307031100700700d0301c05a0754200740c020703c8041c80c425400e20000c41c20360350740f081d034045142c908500000381c9490b00041c00144208000517401c0b044180751070a0b0381c02008050001d1080303585920b412070134218122058800640200d9100c000ca1401d = true := by decide +kernel

theorem cover : BRFrame.Cov 290287769 290467625 := by
  have h0 := BRFrame.cov_init 290287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 290287769 ≤ n) (h2 : n < 290467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
