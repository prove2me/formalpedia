-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3061
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:32:41.482692+00:00
-- url     : https://prove2.me/submissions/fb53ee9e-d741-4fc7-ac7d-1f077a29fd3f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 550359712 ≤ n < 550539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 550360962 1250 550359712 550359727
    0x50616111201060e061c0f0312021207020f01060b040b180307080a080307030e030f0a08061219061a100c30022a060a05130f0608010b03100902 63
    0x111034207903501c011050024011196680d072411a052403c035041c9002d0b000d003441d5040481c1503074030610b204941c8004030710b0f840c400d19241256500818040c109810390b0821428030306600410085200b12034550060400c0201c090105003999103580c00304181d8141070000340422603500e4203403000a03240c03003907058100c4060000a898032500354407080031070041c40780c0001803080b4100218860016500d0512622084513100c0365030307116000f146140401c050000d8120707036218110742e580194004100c120601031610507117040c1b011a43c02e00700c0000c81ca142110401c0a140900004041c008030703001590340e100c0000c00c02c8201c0003103440c0100017903a00902c08010841500d140401036180702c40813802aa41c3c0100600c6101c8025100035105000e01d040884200080c400780c0d090944022400c400a0303403040c0805900900c903401c3c10300a060104203071009400040e40000c1c282c548aa294051034041d01600340d90041c0c02c1034002050810401c1200160094198226444031100603500d021 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 550362212 1250 550360962 550360969
    0x220f0f15170615040f1e0e19091b06031b110d03150e0109050a050c09030d0e011403150406150806090402010504090e0604050118031b0f0c0f0f05061611 67
    0x2c80d0848481809401004500080b001606d10124040b4154402c45240c549541090384070702203681d0302c3c51041d400c010850510064000b05910382c426511401120788404001c54201c041c3d07080080001c0d80c4004d002000c0255035030380c5420782514280718401100a0501c107494040d8411210b05041c2c0b00c01030140c1c890800012a0300a00c0401701c01143c42d41c441c4c0001020b030105842a107101413b010104400120240c01c540313010300010b00030014082c20210948480c0300e554403941c10710860f44800801149202c006610589585520250030381d190b800f08400c07904a90842204041c005110741115500300036502d03000b040c02c41d4882c4242c1d40f1440101c4143c031403600b03c40c00c405e00b4904941c240560004041d4000e03440707003000344100728030b51865081400700c0c0303c0050009110194a9000c0d0b40010016045d071a008480301001c1ca0056203551401c0c01d070f0341c0d100340444240040100120f030344a4000070007501040354501d10f003003030240d0050311491903502d01900000c811810702c0004d54 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 550363462 1250 550362212 550362217
    0xc02040635030f0a05040303090f05010e040911130203160203091e0409080c0c030709020f0d0906020c0f060106020f120d0507090e01080a170301030305220f0f15170615 74
    0xc2c40c03d01666861455a0080440e0424030044000c80c40450300802d03209110080502038900607900d03030421410203001c00010742242c00050310555411801c00406c0c2e22070400711100340c00108409a96802c0030312050bd41c044640c0d1011085400074407072500e203036444111095050010821040300e0591100c001802000480d000820180e80040c1c01d04c184580424920303402031049007550b4403180e41d024028107034490400c0d600c0015804001e40c0e00c01c0803140c0d0040c10100d000b50703001814501d408440920784803040140340c0305580080c004004207503041003400c040100398006000011170240001c07200e4090048241d0440c5d445800042d007051040702c040000f42110701683704156501c8001c02d03100c002c4480140c0d20300e2001203525481c3d015000031241242e90550341c040c030300502c4221040c1d50b42e200b00064002018034510004200080c0d06490700a17254204c0d02c01c050910308003080725840c14008081d03003407000c001c00c4008892140c010b83c5901400c00e49d020455041301003000e11852 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 550364712 1250 550363462 550363477
    0x1a1b0307030f0807090b09100507082802010e03030103060c0e03062e03020d03031104081605011101090203120a0207090f06061119030e0607020d030c0204063503 71
    0x248008619a400d055021001503030319070454980d565241c55024003294a250319006883c0c2110040200c2001400c240c0c000c0740d060043c1d481d001d0f092000300c0d43ca80110358080c0c10a4080c40360902c490a0250500d072043c07031421b455900007049240900101d9135180e0005200107862240d8900110304130754043ca4035080004002410343d01c2d80c0c901a14012a10610a103901070701b1801d80100f64580c12401c590034064980081021075000002d580c00c401a211f01c0c0c0482c28944d00038000040c40709010070114100308464480040e681e4140000144018070b210703a508000c1c3e0522090f80c0150306c004c02c02d00d04014203615620381c0c9401c08501680380c0020340e80180443c030f1428400e00741410096002d4001d4501c283e442e840c501e880414016a80d0605d415400c900d5540c0318100d4000a010314001001041c01802c4a410f10391540c00003007040e002d42c0b80c158041103420110004515282c440c60010b8000b0817540140b40e03072002211400b0000203e85c2202526070589020441903080090b2002d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 550365962 1250 550364712 550364767
    0xe060d110612150303070b0115020f0d0906020c0d0803040605060303090a0617010f0e0f0402030109020406080d14040f050d14010c053406021605060106200303011a 72
    0x944490b014480685103003200d0000007080760307003d071610300d19000c01100c0d810b40c2c001f180d40213241d0900008000c410341e8080b000d419886000d24040344c00e681400070803e011820340b90500b20600d8200c001e0300702001440315031b200d51850344a440000c1e0200c010740c0c0d00a6004000000c0e543d90312804240303584943c2c0c07036050313200084910004046511000e00740c0310056062440005907603440c4600f2115240e400b8440d14041100c0c00034410350388124409034020300050001c1596045500800c1c00c40c2c00c960019445a00700e842c24032200c50700084880302c034034200c102d6585070038907202803000780b2011801000e00c80c0e40081200028401c2a0948028044540000b040280c0c5681c0000d001c991162034000140100c0035491000300320142c00c0304a104104041e00122640f40740c0da980c000f50300821302c406001c020200d00f1301c0410801c02100d80606000d4560841d031a03602c1000c01f0310304c0715222081205600420050041c2c603419203400c405891080c2100c1e40790758241010f4120041210a0181c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 550367212 1250 550365962 550365967
    0xf17010b1e0102010e01050906130305090d0303051f03110409020a0b04090e06090304150c140d05090102121c0b0307081027050703320a1208010e060d1106 68
    0x300c0d19001d501440d00c040260001c00ca140c01640815090721403c4818480a402c0740c00040e901003803485821000034440d252140c6807160900004025048101d02030300040c1d9030380e041003c0d14069110362005007a01c2c00c520311000d132a5644840601010801090086032203480d07080841d150007103828040d0201140709034a0700d03194040389004114440c880b90b00c500c240d00204828641c040129002ea8009120f84d4024054440301943c104410b00001c0300c4020703000b0703090034188200b031103201c05001c96a030710a0340d501c00d85400246401144800c604c0c15032020030681200000108000c411911034800211f00213182000007420005140e000c41c1850042544540880b0356070381c04040b403c2da5000b00c03100004600ba084008802034034200500c1075200b036074240b01155150300c000c5110b80d20728135030a0351070034014460405690500703040450307a80a640680108180088200e03070242d003900d03005040750b1420220300300349180030301458040c130040c0036100240902d002040c410141c001d0300e034a5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 550368462 1250 550367212 550367239
    0x11503060f0b07030f1d0603070e0402070b0708060a080c0904292a030a09060b03010e1c05030f13020105160b06030d08091b18010605071104060f17010b 67
    0xc2c05038000c031022400210101c4044619500484444844c00c41b0300d40820a040e118a00348100e6603c050180408c0c003408400304035156540380020b020003407285050a503c0c0c01c05000280540b1750150110344180070090003440148800186c040b10302031704807020b0441351554200038060071000080c0c2890354811000d1a080425503c0a09020300d605403d12082c03013070310710340d08013504c10201c800407001c0c80204007040400d10260842c4031a5030107a0400500800b00038002800c440c83d4601e0040702e40c01ca041003c1c11110100c040c07070b0440400b410b000d0703d1031030320002c200c01d140c00c0140a92485100140c0000c10359100300c0a03103000d4004400205840130907820510791300380003100c56070b210307100740d4402c00c020500c90942680180c40d07000061144480b0310b140ca02c00608000f02c1c0c1500719280c500b004030703072a0b00d070803006000f0106900d03841e580f407009081c0010060184c0c00480c1c01641410f008200c1841142e20510440b1034200300c011125042c2a10785015001d9181680d030b000d007003400300d903 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 550369712 1250 550368462 550368479
    0x303050307121401060305190630020d0206130e0c1c0c050913140103080304230d050d180507081525020a050d03021917011503060f 58
    0x850242040381c0300c2c1e01c401002000c520066030302c00d00e043c00d010b6105100410034070303000750041900801100c0c110001c44d429401480c046800a5028801c0001c1100d00b14401d609598120f0001c2d01c1483e0a40c0e01e0100b158010800d51410603000900914001941d80d00c150a2459000050700412201e9aa02d007040281ca03007680e0000d4180341e0200c103040040200c0351125114519507043c4945415040402086c10484404031030f002d2440e80d80e8442082c0440300c1150881180030314400e03501c4c0703600c0782400d0826551120903011254a2000c60b04c2100042d41000102c01700104600e180041c0c0d40d5102d04041d4003d0b01b071144844102c2ca50401c0054200040030600300140e030300c01800c583c04000ca070703c00803400d01d105860034405014003001d0f807a58042c0c2d0b0014002840d10700e00484440022030f9a94a00e400801d1544000082d80801d11141d050502000004001041d1420003c40790341c01d00c40580c07035030041c8601d1049407002074010030b1300c0d8040d410403802080e0340c6030000e01e030790b6a95802 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 550370962 1250 550369712 550369717
    0x301080706081e07050c0a0c150e0316050607030e100f020d09060c080a0302160309151d0d021f120605040204060f0f0c02040e0c13110904150f030305 66
    0x304004540c10300009807001e080640d0034140140f0400e002030301515034402c1034500d540604c0074a9014015690305101055500054200514140c103200f03d03401e940d00c070020070313005d9450380c1d04d84030b034101340f040b50028150846846c0070303148102c410035a00c148500d41135071100404e070038850300b22500000000f1140d4000b0140d03401600150242c1d0a030802501c6c2c11641c1840c0c9001d1080454024078411012506a1019003084222420010714100640c0f11801c03d09103000c10031400650007590510802302c1a4036140030016560400c0c0784910010034241940c44850804280101082c645010940d40d600800c3c1400c411a5401c0c070507038a0210030000c1c01c04003991851480107061000000703035401c0c6442103400315405030380c4440e2801071001040701c0b9050540d00000800005d03000c0e41001d03a54034402c198078840b40c103000f4103244602005001039480da03100031407840c51a000d81026000703043c0b400c035401ca21084800180c02c1d04a00c110710914007898200141e09807000d04084205a0803400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 550372212 1250 550370962 550370969
    0x70201050601020d1803151d071403060c03060405100521072306030702030c01023403050316091502070806100303021e1011310b091503010807 63
    0x20780310b6500040c101605c07105022655030b450041c800001304049a020b248030b588804211102140c0e03200140382c40303c0382600308500b6134080e801250f0108140400c450307807407039415400c1d4042c26092405140d80b084501006050302e0040792641c00082c1080107141803100540f000825075100c0c0000c3c024003c46204815950b8105031181c168080741c2d00c0c000c0503040100003000d000701c4005030000002d1000b150030150120040d44000d1149030240340d02030002c0c0008245055800c050207403080d810705000084002490f00084400785614007213070344a1304490344400b02070944d4241d158440d80c11202c480781544466019504c11600001c519030210700c00c0c003118900002c4030095140c80810782c0203809644001000b69016644018440441c01002e40402d081079040e151f200240741500320581d4050b030981c50358502c000406001d441140700701e00c1c03080c0c0e5118480a2003804002c9070662411050300a003510300c0c8000c940c41c0500c1d03494507a8603d042e40328800d03507900d035652a8a1150b98140314007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 550373462 1250 550372212 550372217
    0x6020105060f12060615122d0906041709040f0b0f15090108060a0b0c0f0f01060812030c0912070807061110110c0a0506100801020406090e0604060509070201050601 72
    0x801040300e01e04503030b000010f50450009484292105000c0102c0544c0314000f480c114a805d0085442c243d210719a0303648a0400304410070344d02601d4840d400c3c510901c010002e410500e811090081281c400a4000e40c02984280e13144c88603134041d03052071141d0181c90f6142d0742c06410448980590b07141504545419201035a1185aaa49a000700042c0440070032005c07450311400d0100c0441741d88600b10140c5c01202c05015001d01c581c07240b081d80d00079408aa83d44944e03501040e195a4204810012500462a0200200641401c041203140c441c990b80302910a03000001c0082008248550102c03514134000408065050903911409034544e602031042044500981c40006199401103640c6800c80010b540900b8000e01d40500700002001c007034074907200c12001845004440c09040100309203440c043c00082580b49000481908400040d27000144030387d0050101700a01070b0032030f18400c10f440ba28090300c0203960300d00011030014131b00e651019610102200612030810340641c4900d004400c283d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 550374712 1250 550373462 550373479
    0x61503031b0f0c030a1502130905010902070b07030b13020d0e0304120b0a0b01080103060504140d050903060c040321021929010e01090e0c0a0f05033714070602010506 73
    0x14003015211803003024041c0c500526481c51b14080c2c0055070060003e03400c408405115582c98608050413118260042840594001442001d11031807500481c0d00c840c1d07604e4140700c00d1420724081640c140040a0f099402078000c40d03800740210864000000141203081125100c42da556062042484c107581c094076401320340000314041848038002d100141c50182c54080c01c50740f171581d807030000702402001a5008036814516800c0b24400380705a10410010f5601d182e22201c45c2c000301401e01e1409820781086070300400c01003001a9030604040c40e107014400038446c400f002d100c0300340e05103420040c8a040e001d201a000c0d10030030040130804140c0c1e085c81034000540c03440c40d40f00c000318074800780640703c411411100104002d001c140c001c0d0181d0300302802130b140501810408a0781c4080c043e040603181001d07813001400a42030400a03903100b103505005904842e501182d0340c0902d00100341d0003e8174143c02047c0d00c07050026420014922035074030320480d10746d26540d0348020b008000070348000f841850761 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 550375962 1250 550374712 550374733
    0x6031d060403023405060d1e320f040309080a0f060606360306050405150c030f04021912061406040e10021303080309010207061d061503031b0f 63
    0x1d4440000c0303082403051038500f0503003010f04102298008a8040c5c0409444003002c05094201810341c0c0d28081519401041c0c03030203800c40c091401c0300040c5409c000790112a5030075466020300a049500072034000341280641e00c4034101140d41800c2074100c8141c0f0301c214902d100401401c40140704c90a805418100581900c45208031000e00c4070014483e5040c0c40b4030080c0a0326a278060442e1282c0c0c000c5020301710410ba81e031380c0d1001540c030101c50540790780d00b040701480450000c116600f603214036514112803951a007440c240c4d06e1043c1c0680040c0c002c3d4454081074240c01c80724802040501004d950310845e0031814503143e809000600204e052000b00d00700850920300b0300d8001c2200c1c00840d04040c200c00c1446440700402504014481c020100c00c0b5003000002c0b1310000015400350035104005a502d100e18104001507407200407010036110309200c440b0740140004030b14550480c210402413140300068600191a6015203003901c01c1800141c02d074410f00001c001034034810100340c1e00c16959000318 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 550377212 1250 550375962 550376023
    0x4030c020f0d21020f0a05070503070f180203090307020d0b04050c010206070f03050c0403120801030605071b03050c01110a03060303120c05090603040618060204030209060a0b0406031d06040302 85
    0xa0004000d00c112102c0f040048103031000340c205103208620344129044141005441c40c039110906a0039621500500410300c414101407206102a0840d500d10b854840d1a010300041c00c00300d04c20300d42100c02c1d400300c0440d2800740700740100c0303020a400400d00b40b007401440c00c10400500b002c0d10203c07514882c0c40c4114400394004150181318001c5501c0b00c2c26940400202a070107071034010001d5504203803c200100000302c0c40302506140381190ba5511505605501c5c0002c1164000351912050040700100b14110f1100c01c00312610040d8545080fa41341d500d810040d6001d090b118a41d54071024000c19440300181d0b05a0006088902036540c88900185482d024800c0300c000001000000e1000c02c118501820040015034101c0d1084c000050410440550413002d441660400c580c00c2d500002d040007507281c16100b01da00311004884030301d01d0900e44854510340e882141300d640181612001e603042280040600030f42c4190b113100582e0500d00c0c080c50001d407030b0580c01c2e40e01d030245000c2c1c0c100c0e510900d5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 550378462 1250 550377212 550377229
    0x11104060c082a010b0102010614010e0117040b0709080f030a0c0f02091510171303052205040e30040302090c0a020f03070f230318011b0215160b04030c020f 69
    0x2e81d8ad807488060700c14050b00450b01c082003400154180100301d001d04586080a000c038501ca1070048050700e24030f04040f103004100b4112a840000303207901541c00301c2c6000e0300120448201c5009800e00b04480403184c507044004003071449010794008a02801c00203890383d0420100c80c0c01d10f0840d00040d222142c2039040c2d514900d201c0358016041c42c00c00014040d0707480070500003804e501134100f190a114882c0d10b940f10029030020541240d50b900282040982001e010302c1c640920201c000d080c032810110842003407031144041404950407180e034200c804440020407600a16005072031043c0628144821051035400b03c0d0f06100144600701414032101c9010050340d9019920106040d101d813820b80350000c0c5c00d010111041d45010181d440b49086a600704000c0040f0100107481d1124215508000740a40f420000e2010000c80581c00800050ba00c07400100c10b09a64400a80d4803824415008684980c54150040500003d88180014142c0080103030148902c2201c041c01000c0406050100c3c1c45d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 550379712 1250 550378462 550378469
    0x907061e030b12211204060207020406030818041109182a120a06030209041205090d050d17101e080607090f0b09090a020c15010b040f08011104060c082a010b01020106 73
    0x26512008500007407680c1c1c000388040d2b030009002044094690b21010008e90000711003101e64000a40b4210403400d0602401c00145144c030882424100540701260f00e04045940510301c9240f0b000c0041d4259075880b0094004142e1502804280c00040e11a60360540c4000005030344004850001403d2514500803002541e0b4050080354140d102d582d07500c3e09004502402e941804400d0210215a44440d690b10b074885019000405641c00090000382c566010300f2041c0751280017540401100f00c40c041c03210000c44070108206040b003a801841c3c42440c51041e000b412041c0200014051010b60007805071081e102c035900308035001582cad030300c165a1512490b4682a0480400000240301002503809083c000c41e1a00950300394541c241511010043c1c26080848a401d01160a1066800050310103000c0d1901c00003c004000c2c101000803414041c0d4407498013007181000c001000c02802c001a28549258000c40140d03490b80c40c1d082c11003441d10150201102d40c03810120703088a40c814054a0104d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 550380962 1250 550379712 550379737
    0x10b07050703120507060203040b180604020a05010e0109180510080307030e0d021206070906021608060606091f21020a1d1815090907061e030b1221 65
    0x10728610350b070381c0344468203280e041d000b40034043c0007410100744540010761003980316504404c11468294441280d29118003440203155018204020050300c540202c9020b4600c2401c11030249002800125039090168000303176151855028031030b180981d15042107014100d103038840b40101d40c0758211282d4a004002c0040c0c00292140b01030f0311039041540c000140ca500107080750100c900d200c0c40c000e01e442800d1b203078180010500482080001e0341071103040c1c1031505240301500703094035100e856a038520000d00458407a4100107a0504aa542c42200202080310884641000208418040d044021070303a800303520640c0c012041c11340d02c000340c03003101c01d03101c615207801d01442d802c0c0c489251002a0000d0854011030036441c01d04000508400302c2c0e1007031000b184a003411100c00401c0c404d03200f1001d4080f40d91944186030070300c03410360843c000d218501da030070056005040a02d10100c010301b0070300c410950030110426600d5260000402c1c801100340410070000800d40c6c0d9401081404d02c20803074071904 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 550382212 1250 550380962 550380973
    0x20901050d05100b0a08030a110105130f1e020909010902010e0604080d0f020304050604080a150e030304080c010b100c03031d0a2405010620070303170601030608071706010b0705 78
    0x7250011644256661340015140e00100e40d00d07000014695480420300c2408686210740846001c007003401516448448602814007410a956030395004a180d014000c209a4111030314000e814040c020b0704800e21f4000303000c0b169600340790703d882e4000d00d40c2003401d03800070310740c4180055a4100700341201c044032100001441070100004048644030300c0a21000c04600081000050980d200c4003d0302c0941080406045030302100d1510011035072210191550282c240b40c120001c480b80803044c0c0341e10039003103100c00d66901403d900300d070b00607c040d0b85001c2c0e02c00200280026065031100820b0031040c840d403020442010745c51403404001180303071144901540012417007030001d41c00c00d1410344035841d8940040e13000100c0c1c0e070250007611000d0b08210300281144109468000b61031101800000c10b20018024250864800a004130205912801c4201008000c9140703a4031036400800240008000e42d12816221100700e0700040d014071002810344510800800c8c01d800300b508646445030710100038807 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 550383462 1250 550382212 550382233
    0xf09090c120f0b07120b102f0a03050307020d0e09130c0b161502040602070b1c0608010e10060f121e050d0801081b0402090411070f020901050d05 64
    0x5800da41000441da030385441180b400020f554560080e018012985072056001807840211048480303951700075100782d48150b1643e0507039401001d8026082e108105280c45041210b480c0510141c10780c1c00d282a078441c160550040c160f001000c3d600401803039003510003465203280104c1d01d6465104c94664000b4040c0c0102c1c99400c902c41106000728031507200c0c04105c0d5500e10305038040c0d40101010076117514244240b0720421030200b600b1420b07203441100844c01c0c0b5040c414020740c0c0d20054018048420b100085944552500000008408061300002d1012980b200540340c040e003400100b1007058880d0214040404040e0f008803010f80e603d044140415502d0408003403501c48845030140d4004540485c9220003006c00a10070514500540080000044040e4005c10784423059002d80385e684c02480805240355852085110805021030f005a1541021800500103089680864417910750002d0b101c02002100100303690164004c554225403030780e0701c000340408122107840041c4250012041c82 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 550384712 1250 550383462 550383479
    0x1e1d150607240b0301090b0405161a0d090209040501060512030a05030619120305070203071a1e0d1514010206040b040b04060b060403030305090c0402090a0522050c03010f09090c 78
    0x402640e40342c80d6000c210007852001080c2140c42c003a2042d56541c0c0740004100a00c1001c1252150b90408907030b01d04003a40c44c004854070f4039000608150b00000000030008240c22554020005042e00200700c0380542c14140ba1071402003000e44245400345030b240c42044100100441600e148a0701611000d286544031010004d14009031824491040840d01c0040b640a00c11422074940b94800c1e00c1c1c3daa51a00c0d5030040601d071450b6a440f200b000e075441c540180b90744c84001d041d41d201171000000841c04044020f0a10070303d02032404501941407a229003481081d00c2414034004a6050051003104911340d0b8004a0312250300311000350000c041c02021400144405010a03409405000d001070019000350008441d68880e500540020f511b0b6024000d800e4800c1c4040b43c4100300440b81149440c0c0208041100314260784140707803266100386602524403012580044041c00c480d0400c100701d01d030040880e540740e0000e0207150000c0f1074038480030580c2406886096281c54115899510343c40c5803007a003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 550385962 1250 550384712 550384763
    0x40506070b19020309031c02030411100908120a0905090907030b0406020f190f09030213020d0b0a03030f142502010c0209040506012306041e1d150607 66
    0x4601c1e445100c80510b00300a50035201440c01080d18002071556115110645000d01c83d100f200d40c081c1300d104005200010f51203160348048035000ba603000010b86080442503c60350290f0340f00080c4e6004513513200504040c0c460044c11410510317120903040c81c1c0c440c4107000500724120b49400c1300d030303110003401d201051217060b24503032040c468440549030007920307410b54400e030701b040707080f900300d0808000325109482d04038003c01d554484d10b00d40784a4007895a00080e2000110444e00d0b000d0b5507000580303004000b081e030810300c80e0300c4d07003d030080d10103d41d00c0c900202410411040d8500089a02d1411b0342007400350750440c0e070307001c2d00b04420514464000310038060119100c44201d0506c61000fa400740103880f1003010510440c0200058000340d0b14103a190280c044004905260041411002c4034a030755411040c0d50613544542d140303585601071091b405e401840313190408082c1e284104155005240f02c4001da500c15013564030545c00e40c3c0882400e0050500901000401e4a105030005403184900d2611 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 550387212 1250 550385962 550385971
    0x190e031009320304030b18010e0d0e0103090b1005030607140304120c060f050a15031e1103071e151b080919140108070504380c01050705040506070b 65
    0x10302c0d00b49540490b4100d01e5507000e0707482102e0349002d4a08001411403e091650100880c040003808409458910742d5160303120079044009200c0c10880b00d0055074071075405020300d5544402130b500c3c5800c7c61820344214440501c5058071074481c5000207802d45115040300f1080c44014202181981c40d140e44400946e200342254900b001407203003070503000c00d8460048260007076148100040714180558080d080e01c000983c4944500c0c0c145004200049892080341c01c50a8104000416190680b801202c030080c524002e55161003000408503a240c90204007001d61600e02201000c1aa85e803286030511022000d80100420b10708a0510781250040d807068400c80e104006c45403402d1114030000f010000342c0c1c031021091480450b02401540e2500d41040103101c001d09180c102890980b000401d240701e14011408600e03030100d503400b10b03d01c681c0c01041040c8a04402c1407541320a00c81c00202e6038010220f000040d6080c00086111240950110707401d8902c05046180307440354940f208c0385988000350 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 550388462 1250 550387212 550387283
    0x503150c19080444190c0501060504050930120f0f0402091602010f020a110105010506030f18010603021e030613030206070f2601180203061e06190e031009 68
    0x288900481e034005c0c40031041003140c1c58070b2245844908102d0f08403059500484e000d2858401842110701c0006040c1202c15984500014203000c000d0700c2001c40200103a103550f031640007007401a1201c01141e030007442400920391800c000e40e1104c031070751500c031801d07079020750043c2c140b401140110807211580041c01c101070001140040c1002d41c11000c036845154000c00241780801d043c490458280940c0740100001c030380c510300b0360070607203200078040002800000e8011508280b80031500d0003904070100440d0014046070a00b502d40381e83c0d1f5400c2101e04880b0348a4000c0400040d0481101403044048a805a005114036518840291080000070b0003010170302c00c9032074210000c561813211803407880c4035810a951455140900782810070300c0340d5685c00610f9006000f082005d4803514075803400302c000c9120340450004544081031662044121008007039001c515848c16154000311050042242030701140c00001d8040040802c0701c50303094008240f018960140800016800fa01038005801803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 550389712 1250 550388462 550388467
    0x30a0207120206060a080309150a0c0c0b07060b0904410102070c060203030106051603120207140f0102130311031f0c0206100503150c19080444 63
    0x1500d41c10000155261558016408482000914140707222107a00902181e0020350900d400180080c946141034030300760307001f04400300d01689142d21400e11185829081012180c0b80303500c583c0b941005510414040e103450b41400110b80c02820030002d50707031003150090022043c40150400360742103402003001001400880480e03544005030030229159461060100060342d540140c940100c6c0380007c0c0d44018299041070004100917900503045542c0324120040c00800350360345140c1500e13401500351115200e00d202050080070040010313000c03803100c0041011607010800040c000f83c01d0f485100500102040c0321681000003c0c0062480030540d200101a2403801510b041c01c1c1401d004001c0d51410b140303844111840240341c050210f1601b103240340a80d8003260741481c0101c0e0b611b0f01c018070585a0000410b0002d204060408251010f182d50640354417450740368071000420340c1c03405980540f0501902d1600101e6121000749040080c000410a0103411030300104210798810002c600304d0b142e0404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 550390962 1250 550389712 550389727
    0xf120f0c0305060a0611030f031b03040f021207140f0d12120c0c030c080c011b0f080c030105300109031110090b011202190305030a110d0e06030a02 65
    0x28058503024103081c0e60001001c0c94203508208406410354003500030310255030b5108401340f034040101c1703075110790725040b2582d2a100d1145003001c0c0415000322082d400404070a1000700004003440740441030089585104158500d171074070743c03219828412401503840b0307034900c020681041100700125100c000e01040c110291030702c400d0000c0707844d203000e17000041c940c0c1d041c0c485040d01e40c0710b03101513901145808104034503583d9000e0f211404044015100c1500414418450f0100750422a50100d03003000c5c4018444010310302604510b900d02030031010400180001c0c040c0010301d426681215401840f0b12144482d01003410104520040704021521079807000c118404824011110028425514080d481420b01c84040c1400700f40080310720524282001c035004140c040310003506646440e00002e00704c190700e100213000c8500e091841e1309205011907000040c4030021000d805070000075126444001141001e030364440d0114600000813503e0a421010075040c4080510f030300c00142800103191514 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 550392212 1250 550390962 550390991
    0xd0c030e1005060319050303060d1b0b0d0c02010510090b060f04150801060e0306060405070215010b04091b080106051602041803020111040806130c0e07030e010b0f010f12 75
    0x408400950307040b601c80080c0801c504080140d5410a210410381c41361414850352010303101d10005d07146500c01c1c0700c11110702c400d200d5916411001c03003142148020a00c0d941b50b0a00c441a04050702e201c2a080c41e2500c2030074900d00600440e44602d50103002d131484035091208c0c50700205140541c070f642060007403140071000501c036401840500440c40d0001210300091100422a50051304401c00b000002d500e902140d4600164843d041b400032200400e036661800d01c220b18256041184100a0340e103c1c000113605000340008006449100c2020711424501c079803106c4c0040910441500040c40400040040905c1580640040307810000d1074120036206400140c03c1d01c1810510305c0c20110f030f0756149010180c0905c80c0c40e0048250301c144900303140c90216410b4072840c009001c542020240700035501082440010080034003480303040c3c10000d091410b001401070502c1e001a140c0f82d0b10705840c08030303a032404ca0f55505c00c1c28016903807000140c000707030404ca401c1c0070701490900c00c2e5030716401c400c00c107040f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 550393462 1250 550392212 550392223
    0x1609050609310915060608241810061412070c1401052e17010f060e09190b070f12020a02150606030105030c151e0903010f050603030d0c030e 62
    0x302c0c40c50010804540c00c2c2400040b20500110300502d0500d401d408025407a0442d0b541c0c0d50000d200880103c4030894035021360300f0090405001a070105680c1e0381c0423582d0001d1640c0038000e42c2c1410702c50311000d4803603c05a4004404414444600906006200c11f40c15410030840d400b01e02460028011140e5980c0e2110890303200b4aa0300a907516041084103e120414101a003081114a40300c002408118003000304403086c061603024004000e1641c1c80301d50300f50008200c001c0c07681002c1117406e64401000900c80b00c2038402402c640200400d07459040c200c075812050540d0441b028041c6a15050300c01d90f071200e07560080005028141c0e0b00c41044601510141140402c55000380034205552480000f29440090003d44241000c0c0014069614009001c0a040ca426140321120381e011070495035460140b0241400c3c80f1030024007600040c01c1031400340154500640003404504203002007101031721307800c90307416401d41d1040c00600301074900e54001042c1d90340c80d0300b000105541405643ca0820 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 550394712 1250 550393462 550393549
    0x1602030306101b1218030c180624020601060201020f09040c0c06050702030406020706170103060b1909021224011b080c06010501201f06080a05061609050609 69
    0x44c0300304c19800f019940c01c850701450048070fa2640601081c1940d60710086d005441c011100c0703c0088d050010407a9a00783d21920290100c07440c0b0b1040310f06444d19401a040ea80032184005001e000c00008150340140290f508099201a80342e041640c078005000003400789010a004011480d01607502241e41d5201d29405a6040e034091681d0f1810540c0c0a03241c2601503110310100b01403644000301900120080c1c0d41034030380c00a00800e41c02c0e0010300080034680c10220072084c802d004940060b9000d410b038000c002028240c064048190394040415001d400c49500d01503050300385142d00f079455840b824800480c0d0851481403a01e1020f0740d2900319154000d1080d03a0482d0384140d0040c04a5038024001c2020301c3d0320880c1d00c904050032140c01986601c4c0c002400e441050005518007980754058000c1c43c0a011301c2d0003200c580c0281c5013405583c8030320580d4211580d00c0c620400b40d041a10442809064070300c0501803c0c60031292001780241c1c184010151124011440c08201e4880c0b000410200759 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 550395962 1250 550394712 550394723
    0x415020c010306051005031b22080607030209030604020108041e11030c060705100b0a23040b030c0114070602160803010315020a0e1c0507090204030b1602030306101b 73
    0xc03200d04400581280d0302d43d000503104070a0080551071071a1301c402280e034040300c580d840d412208024420050603000d130520b0140321000041d450300c0500d540c003003032800b01c4980008868042d114900150b04a115131110680c143d0001000103001d540542c0c80c0a40040c428203061540c0c09002c1d48140c1c0e022401c20040b01c081d032503901a0b03e903500d802c0100d41c0300c5d0442204c6036441c001d03696998995900181e078042421940341c0c00c000305140c0d143c192002c0100b0400920240300251007900298105e5072400c190300c198581848851a4140061070101058068682d280c0341c1140582a4085803c42c2c1d6003110340030703000c000f0000750001c1040c484403164070ae04c124035242d505600c0c0080a038880c50348400c600c4c61040c0321103010302d41d1155001c10002c03000d55194440b4888150380380300350010040050014800d103000082d110003142d0003401100d001d07900211058440507038240c03400340180c4026006074000e0021502d14540400b0031000541103007018200d5007030001c280704000041500c01d80780d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 550397212 1250 550395962 550395973
    0x1909020d0e060109020a050301210203100501090c09050109062d08010512030304020d030503041b0e150108010f17070e01091a1206162a0515101406041502 68
    0x50508007080250b0242013000c10550800e209038500502c64001485a00c000c002c01070b440150034420049021302003900541950740701c81d4010030303580c0a40740a100f1200807910304148902c61500c0b80090317900703880c0142e484c801d4152510004a851400b5400140f10481c00c0c03188032804040203031811036596075640c4685a02d907240ca41000075681d8511a6149a50000c00c100702c01a41d84240d81001c0a80c11304010b901d9031501e08126030b80c60034540742886101d0400b00c020484000c10910184118900d10000714215440c200440d03004c4820320400300d4561180e24240504100c0b201c109207819800004c07250141d40d2a011b4501c565001e074000ba44c0c5c65601c180000032030b030229032520301010058482c0241500a00c0c0c04594543c00184580070303c024810300c0b08520351240001c0e056202d103010301c4010090f051030b900f0802c001100c004684500c5146a002900010042614407039020360040000640c40e20705040d00e440a4491075651000c0f0800020a00c800c0c11040034070410580d900801 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 550398462 1250 550397212 550397231
    0xf1f0207180b1903320105090105060909070f0b07211812030f120221010e090f0303010303050f090603010b0903060c0f07021c0b0c0c0106060306060e1909020d 70
    0x203c404103c41901c0c040003040d81400454000c02007115241a100c04a00fa58040307224165440042290408015404c25091109085054201501601080350a8840b43e11010380c0d41d5562040d6204003a41c1e0b0b1210042000f102100c4030140016a0149201c00119940301f500c03c407000704500044004034403110006c0d0100380500107c50040e15036280000803600d40d644000e0000c45a62900604000603510100c9802e8090340644410340402020400100c84048850324403c2c07003400740721207550003a40020342d8410b0003d004100c00c0a240082c41ca50390a507101120182c0c0266001c0034940c1d820407101d04651100c60042d0300030710045160139101d03a401c4081604100004d40744800c43c003c21701c403408030380d403024044810642d0304481d00c80c1d000040c012542c13101003194002600304200309003002250f5005400820f0a403103510003c002c0c85443c0d000a8041b0b030500c1c0180b00c001050003c0380507007030a1800300f0040070095582e4202c01c183d606c00b1a10140e034000301c103c0c516141c6035204c40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 550399712 1250 550398462 550398469
    0x14030705151602010b0a0b0a0c0209010f0603050901051b03070c0506070906021c0e010c060b030321091b0904030318060b04060e04023604060204140f1f0207180b 71
    0x340b450384284000d00c9011000b6000415580d02c41c040c85d42841c000090651026000d00d46205c00c25030b015015100075a0346011803400c02105109040c04641010001412040c06104191280343e01c50003640c084561074418181381c1d00700500b1a410b0040384548040490001c2003121700c8bc807500e0b81e50103102400d0031002418085400301c01d00d1142c28020800410300c1c0c1000444031182420318020b904c403002c03403c16001a1082c0c100766a0540000035030400189095140402c4c101c1f0f5a4104040a44550340c07401c0c0c1e0b80c0782c040560441009a51120102032074460350041e0000e01924011500307804107100102164060801111929a500c00c040514142401104004c01d1040c0d4200000c0c645074012070f1258040052045d2507900f203480c000100950310191200b20420301814540c0ca240a10b00400250f20078000c1c8229407203000c41c400c6951501c200c041c6450342e409400302e601c40d40e0106104640d0000d400b00c00096016903400800d4010080306203018402e4103c1001c0340441084062 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 550400962 1250 550399712 550399741
    0x190203100f08010e0d05031005060c150c0a08040b272506050405040c11071e05120c01030b0102010b190312030b01020a030e0402071a07020105070f0c1403070515 71
    0x1070b5070f41810540040792102050706a28599581401941ca680798041c3c0c41c1201c180e80c016a90040c1c001c1590a40c80d6400141d501c1e01000d1103170f03c0174440d21040300856850103420314200000f01d02600050004104150716030b04a0101201020005d18602001d82d244c1c01c4640010302da03610204038403603520641101c0b0364181c243c401d2241d25050602100070918400c50051a00981d140d50070343d04803030302c40d80300c044407101601c069514080d122703c3c00c401c690402d0702c46d079005042c2c0d04e900414640b40120b40202c02226100042c042042054015806414003620090665583c0c2c525560039442c0e9800c03403020b854400107404041d906500d0035408005c000341d0601c04245c5004040b4090b43d8000606c00802501420b183c1c07602100000040c02030b10825a00800e450b9005ca0a4409100402100380c01004070ba0024412aa100c0201b240d61681c00414040081e40302c06042c03020880500c207050408000c0402c0d2803512400d80c4071249404650309014078210300038400c00c070b0444480036070b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 550402212 1250 550400962 550400969
    0x1002010c0e0910050609030f120c0c03011802040b1212070312060b1b1606170a110d020f0408010507020d090f150e041b270b04030b190203100f 63
    0x300012142080207003600b0030503e60091078040d800018000300b41c0c0e6010481947c1e940a02422114848841030001e540c40d00902150070700c03842480640b0312540b40601400003044440d9151010032070442d02040050480c030000b058100c0541071a02e40c104205001c2c01038000608034500b6910a07880ca4010b280c2407207090301c03203091482e02c8024400002c01c1000c0b038050f0446101c400301a024580222406e016442c101c0c850350b240001400501c15405c5001c6000d050641d550001442d50780142c60015a24600c0410100880400c58881c860b03606901804006640755805401c01c2d440e2100142107460984400016905c559103842d22240c0c0102100c016140c1c0c03a032030450003403501802540e0405a502c000c001d2181101d480881070321154441400e0845200c0d400025560740b15000d89144140c6045024009032068000f40040b81e0007151000c0700c140d500c10a26262840e20b92007205007002c0c281c0081e41e03000c00c0000c07420001740d00155004240c1c0109500340c552401c034010240f480b0550 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 550403462 1250 550402212 550402219
    0x21b1005011712070b070909090c18181205040515040509062d15070c0303020706031e020304050102090d0c0501081b12060a050406030303050928120c021002010c0e 72
    0x201000f03010102000d4a09440d84000380351165107070600203552404158105641052030b000107102445000024441207460140d102010030225210120a41b0140b4064a40c49005007204c03000189645c001000da0707009610308a400d20b601c400015442081c0d041d102001c8440c04102482189000030500c3d030000d90444a810065801f11030150000e114a9840c4004091540c441e00864a4031040b2110a045048511396500858501801300861501040c0c00520501c0c1010444074000d201c0d420000b21801c0d03030107404c2620607a84002a40c0300403c115250354080c070980b0380e1504d03032100d1000c0c0b6511030105c84010780d0401d000104050002009404494000e00b12407058031107100450340780c840c080e0314542407a0f07100408940b1540050b0302c40c641142c035159000042c1549507110320700960049043c2e5403142400180c580c540d071513807110030300509202001c04001680074440c040540e809418101d43c101c8064000030340e031840c0204283d01507511200b0b0480d0081d40880d000381c580000300c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 550404712 1250 550403462 550403473
    0x350912070302060114040b04020403051c0f0207120606050a241d0907090513090515010303020304181506080603060a06030b0a0c05091e01110d020c04021b10050117 72
    0xa8800950750070045c401c1000d14000920300c010561599040040c60a901610035543caaa5a1811994616440c6c2c41480c1032400c00d03280219040c8200d408040080c40365004003011402d00a5801140e18800c2c0220359460b80c0c0c9a001031180c079854685030081030310400501c108401e02d0043c070702041800301e10500b048203030307110342c5420f180700c1000543c6a130090700c500009548064094446801541141d90f1040380400150034101441c0c004640c001c1c49603080d40c0321240340c0d2080000100c801c0c04000d000d03030000d0100f4070a6464010311890903a00d07084d00483d5000487ca1a5003120340150892400528540100610390404000e05900001c1e1b0f240104900c510b161250020900041c0010200980380e032450480c0a10541c181d503040880100a80040c2e000100e90b112912021900f9a000c680c078028040c100e8000441c918241251640180042054070410440254001c19a10035001c1b107101d80c00700607083c00c22035001c20205920f4002a1541001030030760b4203a01e051080100d80d03224 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 550405962 1250 550404712 550404727
    0x906110a060902011809050109060f050906010f0212070807330c0c1b0e0603060702060f04080f0304050c03060109092a03080f0405130c0c03350912 65
    0xa0900e1125800a40c002440c120724030040740c1d015411031280c088400b04120100c0c00c02032541c0618100c50b60882c0400080d5500e03548900c05908500c40d00b68402d0001c000105903500901010504240790310580c0c08901c406980302580b80c00110094543c00d4000c190441007080301d1045101c41d00e10001c09000304004490184890707802c0588001160791200c1f407541034640100040d0201d59404981c034549000708010a4007040914859110350220031401328030705050120307e040c0640c4459014000790b55407101314202c0c25002030001c844400e810080c140d040f443c103001075400fa40c030500252030780406007410103191000680051704040e140840e007100051031035000111026103400580c444864620390a45440e103140c0c00600170900028142c1d04e00305400d00140281c400484070115139103900d4448104658510380b00d43d010505400311800840d002c1c1920340e5814450ba240e09814006015024294a0f034007070b0f041e2500002035060100b408e8042c041001410901103820b400c0201 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 550407212 1250 550405962 550405997
    0x1403010e0604170405031209041a0d060c21020c01060e04030912031407110909070b0a080a0b03010608070f291605250e0403090510050903070e061c03121a041505010906 74
    0x3800d41c0c0241000c3c0e8420b0f500750340ea0f000e4021102080d080d100740c14102003b10381880045c0d030249544504035445c04c40042001c42202803150301035505951030b040c020307042c0401c543d0410b816490580c24060540c88190f50080e40300c00a0030400e11414564800600020a0040001024042031f03050782103a001801410265410b0b100d580b0f080b0f24044445807100c1400500509011051075099428040086101000014284100c40030b410001c4a00d940e6030b030a201e0a04070450003016540d0051401e01c400d2140e540140c6240b4041101a2282d03c00a583d598641207822101c2821941100d2102841006041a030130003041800c0703c80103280f6041c1d400412960050003224843e5559404e070076100da01c504291341c06188041c0844814a40b40c000c0c0c108400d1f0f08030b411b6407107568007008a8000c1540f030060010f1042e8151501002425484040ba025104024942140040303240011110b03945900a6120310020110001240c030300b040001066040650800750902c00041c07440488441d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 550408462 1250 550407212 550407229
    0x120c0302180306221e050708070b0309030f07032f012007020d0f0b1509060607020306010e060f060403060203071403151512101403010e0604170405031209041a 70
    0x40c07041c400610110313803d191090b44c40320401c12024a18060f4030421081203800100714040e1a03207482282d4003507640d85109213030b40c842102c1200c595001030245e01e080180e003038098042c10340320342098036001c02d0401400c0084415400039101c003184104036081903603800e20602e01d05a0000ca044a207582d1106000c1149201c1e080c402400f5640c5050707840d0520010705046841558444510080c0b420440015012901540012880340c2c0b4040c2c04103015141c580221120640e003e0f01800382a0f1802c0c4042040100050409030400f803141a000c1165031144020006140f05050050b101c0c103144d8002040c224070071100080c0224104203001c109095011040c03060340302200e520402c1203021a1081d42c034000c2c1d103200c490a15075401402000241d10844a040e140821310102c0031050b41340416080c0c0341c0102c01f0340616044600424041fa1004d82c0c0700ea030342000e00780c40324070b015170351070109103403060502c0c001800d00b402040c800a03901c2d107405061621022690940c40ca003411100181055 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 550409712 1250 550408462 550408501
    0x1b08090a020d1205090306041a010e06030d0e041d010e01061202060f07030201020f07050105060f010305071713020910031502040f14031005100501140f04060f120c0302180306 77
    0x2000f0391451042441d10410441305c030410082c0984109040c01c2c5401038554841c61031440800c1e414100120303007030310884040340c450b8100900818008203481016504601c0002c0100d411949908032500a5034440601d0381894000f0800010000703680504242141c40b02e82000c83d40a03504015000942c4c0c900c1d054803a0012980f80540da222000d1601340d0091080c0041d4015644000c103000c3c06000c010740c80644111019a1503019111184004404a800c00c40e84030001c03407000c8040780031509000751540d0740001142d021642c80715181e0009603030018116525034601c14107000501c1000031050090801081700c0b002503042604041700c54064004c54054880f030a0800242c800f1180e400300141c60382d0600412040000e801c2c031210540c110407040c010346001c01c41c402468950300303101c00d08980500e5241c144441c01d0504001c0219518150310a444042103540002c40e00c07201c850b4424414800f405440040e640d4a0f0080340ca485895800307081440790b0800020086607550344881100300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 550410962 1250 550409712 550409723
    0x6080c1503070e09010306020706140c0307110708011104060207081216060b041a15070b0c0c0f06011e1706010b030c0403081b010b030607051207050d1b08090a020d 72
    0x8942e501d0000f110f2418202d814140e1000c80301c2c1c000024855207038002d240307082c004c1d9028840d1a1010b0200c0c00796200a580c0610318250800004815130720500c206009920b82c107082d100d4442d40c90768038509452f070f1141005046d80000404210182c0c0400c84d440017810408041c2203110079604880c0c05500504404000d0301100841281c20400941d02c6100e0340c2300c00030001c100111010024202d49105403440900424000341000d0480503107805a60300940d11540c2028240d80b0510861426048100340c0d12a601c0703103000c003840305102030000e41d0103000068904404103440005507020422a0303407011412032104010080e0400d40820b445064880941e00207a80351590001084a4400c540c070141c0251004076a40c0d5000d00344510310aa030422040080c003981d90402c08168540c01c05440f010040750081002c0c000c2505070781080d0750f0005003400c059042c100c00d0701c4000c01707442512444103215401000d02840643e040b086d031070380080e941c90003016803009580c080750b2090f8400ca80030b4079 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 550412212 1250 550410962 550410967
    0x305070318030e0102060a0b030a150912110c0405013203150a05010902030708070804020102010b0a0605070309090203070207031113021204170f09010309060605091906080c15 77
    0x45000e500140c00c00400c5107810802094503080050444054001c0d540c014041e180105417241c00f10301401034664001070190103504550f0b6111070300140c101e130004896a80f60310904010580c400e244440c0c00451f622040b07080d00e80c2c580ca0a040c81e03000c088075486130303107420b00601a500986c181100c070090f01424070204811700c9008200d022101c01a090f6051180500442001c0c0150080e58041e48241900b4071285c0d88440020050380000c40e030312400109180300040519104405680e002801030000180ea900400049103900b034a50b000a0041540001e0b81300c100340d840700c2200300501c0811021811410103040080d12005203100c00703401600031402c20746032079546244002080607031080856035240b12102201c13201c481142c0580300388403040d41b0100c3d503a5020b001c4481c689003440c811850208003100550051240c9101950b11039542c000200d281d032190500c10b80261704811030202118014018007003076030b030070b030704500b0440e00714400e581c8017600c8507081006a150325030304654 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 550413462 1250 550412212 550412221
    0xf14070309210e0108060d0206090d0819110c030601080d0c0501022110140a03140a0f0b2208161a07091a07021e040f09050c030c030d0804030305 64
    0x10302441401e0101400c42d031041400d070380640049015030710040071780b1008090780d034080c02c2081011034404040d40010b810800800301c1d00c0c00e2403106200910488400381007038a030603205040d40d80169070101c00700301c0c03c000385081b4180070007080c5a611800c4000786100c0d81440841034848001d104954244a41c0d01c4580040200a4042c2c07000700903202e2100c00c90850070031800d0074640058401141c606a00c40340800e6a03c00d80083c0b8058100190521041c54a90755a40d42c089005880440480c0903e131505400206074400341000315004101081580c00c05000082611060030201d21019041d00c011a0000c1c5440b4190740d00080701e1114109816440c0c14140d8515074038841c040001d01220040203022900040c084040d40e14082d0a001d40805d00d2a10765000c0c4a4400042c0d404015802040b103125014031540c21402000b50011a44880b0745607070006a4080401c00c84080e0030101c150380003428100b15888a215007100103110508541e0b60140035044042d0018040580390800034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 550414712 1250 550413462 550413473
    0xf0e090c060c010f021612050c06072006090a0b060d020d020609010314092a0f0415052d0f092d01091d060108070905040c030c030b04060f14070309 65
    0x502c413402c40001e0555840c6541c0700f0b41c0c006404a040212032072642c01c0c4c460300701c103071041c01035035906940400181410b4a82c080b05aa0150083d0210b000021480c0e242018200060002341d001346c2e070702d800030120082d0500e041c401e141d1008040e40e009000b5441502d0140ea00c001001032456015991203645030a0440100c014084042c0b060340c1c0100f0000a10213100000104542d49610f0b0240512411908c403200d0141400e035010001d40c41000391449080c035140c554440c486c0300d1541461075100e550b4490114443c104a6100c40360003440d1101030348518501e00300c41301040d1800300e51180c0301410000003d00c0955000c6c0003204008042000003110801c200300c0c0d6242038aa00d80001d08540e5070306480c1019081400070400340b50328400105d9100103000440d50706950704c40025000490030243c00c0402440020300070382e045c40c1101030000100e1100305141000e503005010b0010645080d05054040c0c0390f6103440107d00601d402c165494074120900c509800400b1481d011a8000f92420030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 550415962 1250 550414712 550414721
    0x10203070b0c0f030903040311040614060309100c020102093604060e03031302042409020f1306050405011403070815120d0509030712080d0b01050408010c090f0e090c060c01 76
    0x90303420f408030010034889a040300001400841c1c0c401e1810030801000c0c0e00510090b240307184510200410003a014800b1490800c001c0d6500c201d45400300c890f42d4101503c050117a810000b409400b503540010b02c000c15092100c1c48c20104401c04015031480100030704000b0b07890000300024105264444082000c005460b0030900386220010200c0ba201d007002540c0010914102c1400c900c203500c0c00d140c40030501220059002c0c5d41000d5240510b0303107890081c1c550003030b44c00503505507100341003001000b500d03006800340c0102410301580e440f80c0310f506200000d0040f61160400e21402c100500801107139990003480d203948445507a0920322107078500000b144040300f5084a00207940140c0c1048070841d40c2c402e01516440c41d0440031a92126a0b4241d036a00c0300140e9100509440d104004920500000c0e80240f00801010307d08245400e076605085421201c1c1d6000d160001001440304001c014810f808140c06040e03a102d0240c191b06010a021f90740e1040384c102c90380601c0300030a40403003400c001c0d8003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 550417212 1250 550415962 550415977
    0x110c010305160536120a03080114060405030a0b0f01211101090503011404060b0604051806011e02030301030302010510150c230f071a0d0b030a120e090a0b010203070b0c 74
    0x1c80802003002090604400c0c892568610700030311850308000c40c040340c0060340b40c4040750161a07002459003000a0b112b00c402d901c508150300681d04000014881c2c800300319502c10903008102480c414101a40983d41050b01030f8413424910244005092509603007402c6010096841220380b20ba2100b803a0040e207030651150710803581546040d0108010408008103d4815440f030f0344104459040d81c020000c0d43e009500500b0703002100704466012695a00b49000c0d00000c050401440303820302c00d02d6403210300c0f01a0792100c00603080400104200b6409002e50b9400003140c9081184240c1400c0c0071011300b4031f41d1051030381001a42d000f200140210319245c0b1940c0b400011601c0209400c640b207080d03a442121449040301e00c1134120024585840b601e08510b0b4516000d0064941a10b00004001a0940101e403a615024a07c2c03414001040b000b2070312500d26486d26405040008c0b4410132058030802000d40c1042800c00c0d00c000c1c55a03901000701c40501e913100b040400f00e501c0c2d540b5150344034080c044 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 550418462 1250 550417212 550417267
    0x525020a0f080c01030b09010f05130e060127050c030606180a0f03110409020108160e030303070309140703020907200a081903110a120209040c110c0103051605 70
    0x30500c0c08001c0f03080441035a00381c9052080e10180b074203100300c9040074400c3c5010500c0e080f10900a80ca00030b10011003c1501c0107020644c0c0c1c2400744e8840c1032900c01e0740030300300019032206110f4002d203040c01c488902480b4503000304404c0c40d103220520603a201c0148060700c50400010100c159038441c00c0c01d0440d04001034420000030f0388640784d8014501e060702007505c107004035042c0340e092490b26025888849506a41c0d10701a5143c100b170f4102c055070605c41f44014400c183ca028034407034404001540c810140ca0b074001c0b400c004131342410304141c107200b511102990017841382880542c49211450741c002c030f0146059400c50500c051200d401ea41031513074804890003490350000034051004007504c00265031030707402104007481c064164211580b40c0c000a000e07220a01006410758010081c02031910912000545086041d4002030202c4100c40554004904540c00742c2108180c10052803191203401e0030204203030b04200314003004040801e16144200440010704024000c0740807070060320031b540388 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 550419712 1250 550418462 550418489
    0x10120903080130031b0f080315030109120503060d0f060204030506090a0f020f060906030a06030c060e030303011a070c0603050604050a020403021804110a030b0402100525020a 77
    0x51400900100d4203124140007415844040200440c80500a00d03190708400f0081822000c40d56050314802c01110b410500094134840030340200300c055504080d6039206290030b039075a181c400c1c144010700d101c0c80e080380d010ba898500044000b69002d030000400000c2401d04030b84960740d00300042d0b0a0b0299003402405030035020b18010820205801030015644610160b40450f6a04003405503911510000540041c0014102c1000f50800200b80d4040b81c8010748582e20382400034021a10680c0280c0342c06c880140e031800c0c20014004101c5411000d1700c40d519011400d101c25100080d0b507400180181c22004621212900300030418404540708250703c4410900d10a94541c1d02034010f2408480050140741024001011442d90303100f20b500340c2c0d03070041c00003000300c0e01c01c250b168046d10b00410494444080704014071055494600b041d00441c0300b40e0090903245043d00c10f012001140803014024000c0910060206419007013140c0030f0300051011020401c03802c0d000040c800e4050368080880203180 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 550420962 1250 550419712 550419731
    0x15060a0201090507060f141809041203050702010216021e031c020c010c02060a03021e0d0b010201060506160803250e0f09040b0606090105040b0a05030601110102181012 74
    0x1034106401036401502912544d990b114415144139240034500c00c00580141c14001901610601030480f08103110410901e41460744085010741c103050b40c0954285004040c0032341916458000c0e181d10005900c0251b040002420003904608100400203200da42544428609040c052400c903802c10310080886442a14150202d04074000283d0510018052680400100c0d4090001d00082c20b9005d0041c502c1e1003010b0b84120004c2d040403030381d2006854041010203d80f6051405408140180d50300003c00e2a071071000607084409a605c524080c20050100361034010b64403011070b9400c0d0700700340c0e8580d49a403040305140c00303065688100c400041d0000d00442e2100d501085c100b10302002604e2030b50002c0701e01707001c00500c0882107a000342860103940000345c0c0c42c01c00340301412030240103042450901d03844016119081d0480c4072000d00040001c42089042c0d03a00c20005007074541075000071440e16a82075041c2042a2510000d2400341d451384001e2030b2600d200701001111049000010071580301c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 550422212 1250 550420962 550420967
    0xb280614240d151703070b183c0c0d080d060f0609140306040201180314010b0f06190e010e04050907080c010e01021e0102040e070504050310140f15060a 67
    0x40c0300e0b980704060900b040c3c0451100800a0900080140200110309020442d07666041640000345602c001819000300c1d02041041008800010030603c120314101c90401041c00d1a01d580402c4a0506106d0318024140d6910700424050301410b8140ea110540000c80d040c201c40c18400d114503600340520b0188000307601103c2403c0c82e000d80d08036135584504255030f00000410503c00d1961140e26800420100f0015070040ca580300c1d420020f2a5100e00d001c2d0b903a151200846030000601049944070059403d0902d0a0b41d41c0144c070380c1c01203030070508004030482c0304030b103900300c08012000f404030408014015a000305449802100e00610500c1545849085161500680d1065106031700c21118017004039800b452809107940c4c0c042e401425900302c000c2d260240403451100008055500300b1010400c0700c0d021410522611081c0c403460355a5103018141454444a01c9010324514501501d204509408a41081c1c1001112010b800302d41c407510351200081408250450b440305000070107006c0c154 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 550423462 1250 550422212 550422221
    0x60405100510030903080c0403080d1a0d060506091006021002090604150c0308010504020918130602070c080709060e0703020711040e101a0f0603040501090b280614240d 74
    0x9103ea80c0c0c03001d06460347c4c1c1c07c1c0181400340c3d000c000c003900000e0190f003004103003990280182e480000c0030842920145c03004a026120038805c1520801c1d01c1d0820403000e07042c00284e41e42c1024022400f02506807520300001c2d01d41aa84544550482d000142150f041e81d581080c0c5010300700052500c1d4148807034000103071819062044c01c4001c1503800000182e03c0c87d003482541d07040341002d40940d80c1d01c0c0c10703880c0d6070724802d5008000107003d0047c0703407030304000c500c0d14406045c059205203030241c0b07030a0820f076031646081c4040d03001020942c00c00310140700d90341da21a00d141d0000500e040268035040079107455a40d07100c0840c2c046401c2803410a5030703031003a4070000b160030f00d08007000303010080160150340c056a018410102d950700650015460001030429000543d0711501800001a00c002c4503030f10440c004005503540c032114204801c000c01101525015420f100b012007004025132458194040120001055900d1249100c428190a089003030039201c4403864495210300d68030301c40d0000020042 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 550424712 1250 550423462 550423481
    0x1c0207031e03030f0506030d0f03020418020a021506030a0b06030c09040b06131512030c0b0703050a0f150e07110f03030405010c050301081005040204091a1807030b06040510051003 79
    0x3e42000c802c102501c00d40c0c443c56010310344c00350160074008006601035414201039400142010b43c200400201c0c20985040741640c00001c040140c2c0d90003400e031009103017400305084014500032010a205482c0e80001e908411203610601050040e40e404000904060707140c0403694114141204100800514410107481044e040b145030440d000f0000032a01101e0003100c01c4204030403072140a001d0302c094142f008802a2092500043c071408954814035010820307035100c0701187c2c41d0020310000003850300480004018191040001441d0607a4803e88007209101c0c0b07102c0d01d2010000324a07128818040c02070016a03c4044820003c568150b440d030382c3d0700403207040c1c81c554641803103011600d100c0d2044904840300c5100030703c47c460216581c00001e2070042e000b26801a5299085000220b100c00100c8880d20310f2007913805140303050006c2e8140c40c4c11386604522960003c0d0428800500052036054001d00c040e80c00060300c3d52440c0480340c4c10040c40c0c020030790290402d010344641d03d034540c0008504 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 550425962 1250 550424712 550424717
    0x70203010203071e180314010e12030a0f0515150906070308181606030c0513060c060e28050a0218011505040b0a1d09010914010e091c0207031e03 64
    0x43c0034511030304845e074041d0304401103044015114200049a82d004082151f0301204000092003904103018a16105040454805c2c0481c007104100f00c6141c14800d00070024020b540c103100900c0c03c285210300c0b00f05540c5000d4450606203000c4003814030039500382d406050f80076080d00c1d601c2c50a030030301801090046400300b00f095100440321302000400f0591003948028290783c3c00c10a82004001d5002e010503840c4003003000710622010803000740341c5024000401c00c0b5180d2125815507403c1c0b000541c0c0091505804562144607200d08044509080f00f200380b4000c0c2d401d01501d6082d01d00181403003203082010350302958002132030511022078000756041740e400488115001c111010140c410f80624450701012140502042034420300400600000118120312341000000010004101000c20b07001030480310b540b5001d2946026413440554007511400e02104020b10b82070f0352150307071462070700b01c2d01c605111350f51040808680204981c078003540d80032419540b0308107040d030f4903003860300038003001d500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 550427212 1250 550425962 550426007
    0x110c12030702030c04111605120d0f0b041401060f05090a030c0602160f180914010501050a050d0206040515040f1d070c030c0204050c0c0f03040f0e010b090405040807020301020307 79
    0x603172a09100b95030302c1c5482c1e11080340c24842005a108103054404900b0707265406010001182c0a022000400030000e0b084400150801d04000707100460710441107041c01145412280f035240402c05180c01c0c11103045142c2103000d030030340034400c50f00342c002d0000c0f0036000121040c0100030800e040050704142c401603400c03a20280d10101201040d540c5a101c1c00c1814144984144848003000c041c81040c09403100002c11040303840d0343c4d101442c41018100c1882d50350f5a0005100070310741000b458005000440b02000d0314400fa80016916104600c119486504481d5400c0300082d0707294242e80040c14619181c65881e960f0783c01d1075074031119802c0a46803030718490001591b4503000b00c0f01c043d0065015a9096440502075083c00b00030500505410b545180601114990344010486481c0c140c0b09074000c3d40d03c03035180038002c94141206070000c40740d10640d100103001e4100484151842001e0454000c030b402d0720745007420210b910500e94040d4040d4000801c02c842203405c442150b100c984c10407406072 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 550428462 1250 550427212 550427233
    0x1022d04030804060e010c021e0321030606030403140304030306061205090d0c02030f0d0909050106023405040903050909010b03071b17070c0617060a0303110c1203070203 75
    0x12880d00c9a030100078900c2e0010702003801030398030a188002d6405411b04007a18451a1600050040620224401c0540c8d801080101c6141024005054030b0704601820b031070540c241070381000303460000428041c010040440010705151061482600c0452800b0700c03142c0d20705040c1401009003c0d60b000d100d0101c0c20010a18492102e544104d9106180c4400030f44441942200c0482c1c02d40704220f402d81c0d162007000034103241c601050101c01c0311100b40b034032000700040c5042200300c26110140d0002003550000101040c0b08034003601003040704400000c0a0420468100b07840031080d100350031a5030002c1c90400070a041613040b400401c240d60741182d0b941d507581c0c5d807060780c681244400c4070484001341810317510400f504c1091002c40c0c4484c2c8102d559070340c220710303242c240e802540044005491422010030200411500300d02c1c0460010000100e01d1941e1030300e0804160800070310311004041107502308240070a100144400c00e041d200003062001106001715103185c1e01d1308800010303442802a00040f2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 550429712 1250 550428462 550428547
    0x302060f010b0f0304061a03060c300408130914040510061802130e04030e1f020c060307030219050d0608010603150e071d0412051c1503050102 63
    0x2666201003d01003036180d651660b030740d107000c0c00c060703580f0340310032201c044580c2c801e5902401083d11039010070340400e071580f1070005083c0c14800d0a282c541181000c41e5102c0c0c21980f10341240c9548241c00c0130200c0d5030b03085824500f0318868282d0344252a01c070310b0159900e04208121220074011400707003040300c000305044803c60781290f000c1d00c0391070802e280180501368420704ada0050029034010051051465680304010908080115006c42c0020250358000349140340c000d550a9190b15a52114181c04c0c803c101c000e5a141c9a124006201311408400594528800c3d0101d8041c2c101c41c8040522214001001030820341180c0769082d18035007000e0011030410fa05200d014201ea8000114002c61180407028400401c07641c211504036005246010940380380d410550303005c100007062204100e1620b410600b0602c0071070465a010040204661882008440308005036a881c01e803001071800c030b1880644d11a10681c5d8001489075001081d12220201c0c3c2c984844181082103201c408081e44c1c01040b0f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 550430962 1250 550429712 550429717
    0x312090606101701060f03020702040204030c051c03050403020103092a0e07021b0409050c031219030204050d061a0d08130b040609060305102411010b06070326040302060f010b 77
    0x1901d207507202d660f004006684c415183c1c04d20004850400529105c280d801040036a031060f001520b0503c450441040141000d00703c00c090001034031145200c40c1c100381d500400758441c602c07020381099100c662034018002545a1070302412030700c0460802c60088ca00725081c00703445074800e10803a02c10700d0740010505030000c556420050001000c10003a003204400f0480101052201510280b240340c9202d050340e03c04025001340411034a81c1c103030704d40400c1150712201e000280e001c0b208141c0140030410207912006c00707401d00140d0107071010444d141c54142522075a901400c03841e6100030340b42509828045908010b0148207407980204200300d44441080300c071031050b4802c0034000307100c50030b003044450f20aa210300c0d0820003508000290940c0d9071021215040a001118051240d40840d544500d42010039020304640c5a0002e000001d0207a00054031030040d000040c0500c003c0c010074400c490103018040d90f003580c0030900007026003881e040082d81c0e0902100c6a80720892018008106003514006 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 550432212 1250 550430962 550430987
    0x311040905040614101e03082701030c0801050418050303152103030103020d210e0f041e0902010c050d08010e0106020a02030304031e410706050c031209060610 70
    0x404c18152400700910300020044012046c1008148000300c0000d40c91401444140c00007030f0040081780b40050311074030164407404d0345814180f40c0083c55001c550000070842c111030b0102c40000748030400c0c0000e580c084400f840020f1590000000704000210840c81d1814000d9090359010310340d4082c000b000e050009108040103265005100400051a140e8446c1074280d10900b090b0350008a40701d034108210100110401c0840c01ca0707a0f9110b4581810b82091a501a08031070501c449150300013604e910208110400200c280c458903c0020b5900503100400f445078444200c4490251400740107004c24000e000c0c0c66150300c8404000140c0901c00505140388a40040141d450540395a0780d50198160450390b8018068030f0700a40c1e40030074441c80818110305141d004607140b80a49240f0700e5407403001e0500c4030300401001038200c246800700040c180140c83d01401c2c1a13a0f01d5055000d024554007400c40d4080000901c00100103400102040300f42c003d0f64256100d00010b02c03d04010340f1000d84545 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 550433462 1250 550432212 550432231
    0x7020f070b2515020306060d0507050d0f0b13180818190b0313030c0f1a0601050f0706150302060301290702060d051533040303120c0311040905040614 66
    0x900300f4101000c240d00440c0c00803002080c55150000c0e40c11500c05031101201c2e0000400c0022502a8107401c160040032003215070a141040407074407800018001c4598058282d00481c0c0d240759209010001500c00c2d00c196800c000459142c2c00c40c500c14001c0550400c0111380240002c0043d144592413004200c2d050311490243d840c115a0323080e00d0229890200307041501000340100c91784000c1860500f4261586002d2048071a5234403e080b01c5c3d40c5030080150805040040411003000181d40f80f400b5644c0d450f078408408030794028090b003502c91060035a003000c2c0d880000040000390080641010651500c000c1c1540c1810700c544511522413401001000383d0002d50400c0001c00004040e0702181c2d100c204403200d5451070ba42207000c1282c00c807400e0159009a01040ca0880022800410f087c08c00507025407102d06d018251342d8010030381d01c94000007040c080c0e1030703c00c021441070094101c07071001c5185480d9162100e41e80c1203020003030310007914280c891902e807800310100c2e5403000700150301c140b0201 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 550434712 1250 550433462 550433483
    0xa030e0114130312080601360311040b0109080d140903010507050d0506040603020f040b0102100c02010b0a05091317040513091509050303011809020d1208010f060f0807020f070b25 79
    0xd6034241341150022199110000740d23502c60302d80d005420700310201860241e03941916601051f0113001c121000050001c0c140507a8280801c248a4001401851002285090b64882030000504c1d070450050f00d26440d4594244810004095403140180c40d00800040090000d904c0300007c0c0012a5040d00000c2d4000d03488060000c01c2d418280c105c1355a204040c41100c0c0d000d011382c1e8035402100d82d99000302d001070751504545d41c40c03072901504000191800f00c0e0204024100365010000403141e01c1c000810036a14a05501052075103038040c2e600030078004c0d250001c15040805050020022a81c0483c2c11000300200199010041c4c03062000b2550b210008501c2d50f401d121a15000d9a8119405940c5a0f2521803030001078854120440d1010f1180e0805440d100301c40c0b00180502905801c0b407500c00400c1a0b04000c0541d22540086140c103080c06c0400e11910303800800c904244060490007100e100d0721400013400400c520040c5210300121440c0045008a01805608100000d00181410190 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 550435962 1250 550434712 550434737
    0x905030604030c030c0b01030b01150801050904230706020d0f0e0109060e0d06020f03010302010f050f0a030b060409020715050a140c0906190e1f020a030e0114130312080601 76
    0x5a10b050a90340d0081c206007617207060700e07554403040e070100b40c01c220783e00d00c0100c0c01080b24030104002e4184000443c00c1a44c215030602001c201071040080025205103d802481e0007440d0100507000d41261881098400260b11840c0c065603401c00d480032000081c40350800080d1161144107501c043c000c05940d800012031078030304201e407108110702110354004550700014000840c144020700881c00e440c1032280d100e6145000140000e04e0001c041010300404012081200311040110380406000c1c1c20002a44c031301e81030105045001d02e800c0a003909100084401c14004019524580c0b041d54440601407590703038540d00000e4400200745103400800c2d010200d40d80031010000340c80c0b00c0c000a800c1d50705000b90750105080c030502c2005690082200448640214241540312180382d0b502071a8104280b0301036074000b0b42e00d8592040140410041125642c0103a205a015000c490980c0c3c03071040d282e944110b200500c00300c2e1884125098030060403089116405829504c1c4556416160104140031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 550437212 1250 550435962 550435967
    0x518040309051e153112081b070308120a1a0d0311010b06040e090105070903023007151e0801050d0602160f061505060901111e0a050706090503060403 66
    0x146004518421000e0086110144074400c1d840745000450b44e070200c4a41c1d0403502041d1750880d5410604d0340c25054105c3c0702c04588540101c9004489900410041c0c4030221099030906078541c1000340100000580d016440c41607408186c09002c0c0e44a0030841003132604402180a10031001442e00012540000d0000c64050040f440904145034008034041c0b9a400014426500640009004c1d511500c03e210343c0c104e00348141eaa100d10141007400c2201d0841d00042d044100c1c2c080181c1d4040c000ca1000c259101201003c20705150206040300e05442c0c498440a00b00380480d0300a1001074013140c0449440c013010006500c030500c0ba916903081c26428942031042e070b01d014600c1070700c4154082244a2040416810882d49540200c40175041e07144689800410765480f01c0a9201c8400b45603c14416565100108c3d04001030909045001c40e10511a4608003030300844000319030704014032101d4000c6004513011030400d00ca20240d07040d058039035074107803011000c5015040d059403013540041d000a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 550438462 1250 550437212 550437229
    0x14090d1d0406050901030303092f090402012105011406031302040b2206060306140f04051902070c15080907060f20010b010216030203060f04020402040518040309051e 73
    0x9401400c080b440503201e2003c5800241c00307074400c40020b40c0d254410400c1c06142450080c5400e0350382024a402d90402c20050102e01e10450243e1245410901003000c582c01414040407600001c1640e806103a070042c2200014a400d100c2c0d46004842c580040c02e4034076140c42142e100c0c5c3d4185001c244028415000d000041030103098a64102c1c6042d00188411824680c0d240b80c17000c1c5500780420160305005004040e03c4450748070346411014240c1011300ca942d000062a08028280d80008040e901c1c4425801248565200301040314400914081803005042c9144151400c003000c03551000100d25003210900b0b0100d66810481c0c2000401f4030440340718500c089036070f68492030034212003801c100c1040303180d221036250850160b40d200302c0a4103d5805000348070080b00d452a40ea85c400b451500860340f180d00085c031000f4050022400603046668990555006c0e02c80607141440c4402040c4030200c030408180c0d01074000c6000010002528602621681c43d8980c40c0c86c009121480210203000360103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 550439712 1250 550438462 550438517
    0xf02041b052d070809041505010c03080a0b1c060605010e060301030609050a080301080a0b0a05150d051504121112070210030608011509060b040602120c070e010914090d 74
    0x8201d000501c1e468801070400b40c07400318084c41c9031950301c0242d1001c0104917041e400c44405801d5031608100003d230b81007100c044005400d800e16107095540d841001c001000a0780301c0c2a4045800010048001d08060868604501c1034008014482e101c00c01075034503001c0146070700e80c02281000180001341d040e41000d03032020b100d201151081c414507034404003540c00c244c00022803580040d07403e100f40412500c00540008e0716036004c00260a040d0a40b801414140d4001c1c0c4c080d81842c2100320400500b08031051030104050380300d40450800b0f2600c525030900201103600065007846003081c0154002c42c0140241e8112000c0601e00900ca500f8069046284d594540038140e0701c5030001950380082c0510000c00341c60390390a44109050420364000c030b46080c0c0090a001c9401d0009200c41500050440041650205040d40329000d203480c0c91710b0502a6003005014030760003000010b0900c000d4200304039203401a000908296200032409984600b241089070028100d0000304080b918280c030050403e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 550440962 1250 550439712 550439767
    0xc1e08070201180b0f18012c0303190306081608070e0a0905060703050a0c050909010311060d020c010209010f020d080403110c121516051e0c0a0f02041b05 68
    0x2c0507600c901c0009a41c114110340310017900c00180403011689626040c500181d400d080c4403c2d9800740c1d2a1407045080c000f08200da001e03802d160200015542002510408080c0b0182445049166480140940003c0c410758510f44540c050000c2c144220300022810758803a00000d142c01c03482c011240d02c6404000c1c1c0340c007464554a0210307002190f824410342d417280806480210780c1d0b00300162001c01b25481e151903d42005014070050318203a4640c402c0340d045a030499000c6003d11041d000040381841010349001100d4800100034890082c19005085802c0d0244c80d042040310000340c1c240d845000305d08840f4001442000050006405035407024426200300b02222440540c3e5800b10f00c45294410031080d03103501c068a031100001c40c44014a0317010100d980403d0b2202c054043c0a0054000c0c001ca075000c860801048440305d100400a81321048480c80889a001455007409501c034280319009900550074082e00e010307040403034040440500320a5580c1c030f180804243c9220b81c0c0b0701184544000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 550442212 1250 550440962 550441007
    0x221160e2205100c02060117060f0c090303160201140406050a120f020a051b070e041401090f080c0601090b0a1a0d0c050301140301060e180703120c1e08070201 70
    0x2c1001003101c002c542c3c034540700000310030108440291034184164030800c015401051200307085d100208500da000107044007045000d407509007071100f41c2d0040310309550701440003003030010031074005800c82007406000fa00c0710303140220012201c0c41184294000c04010030401c0250b410702c203205901401e0140403a10000991200c120501c8042c1c1c1d04c4a905c2c003000038008962200300a010300444100181c9100007410410f24003c241c0170750141c002c02c040c20405881c00c62085c060420f4114440c400e40c45890007000104501e4034603500c1e00a40c0c40388013640300e03485c004500881a80b007010344801c00102911185844c0c191840354040c1e000d208041c1c410010b00507003a001c0c000e030164511895643d01e03260348942c10007140b0400c680c0840c9403030788a0303030419504001860000c002240c200b01c0700c148000740014101c10807490240554801006c40108503015040c0a03405003119000034403503441440840340075441c110041c00c8407503000d00501d0040001d8001980984c00a41d03442002d002c0255 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 550443462 1250 550442212 550442281
    0x11203090e06150f041e05151809010b030108060f041112030d06090c14070f02040902040912210905062d100501080703091a060d0221160e 61
    0x4116001080301210700311022030301b0b000c0030340d44018011504803000440443d2510b044006007c013441e040010480000010300c0f900c40b0350780325800038042039014000b00c013203503503ea540840a500c240304100090082000fc204c0c0c86003450099805560006c48228068254204020600408a12124461004002c45d80e0b18410307a008000081040301000254080001006003440c2000650711942080800c15400002c1701f800b00946607036010307140060455464404600208a216006090401203c2040c522158065004007805120070445140303205600801000d4500c0f21600905a4000e40c00150040c144e84902484c41c41d15850000c505900ca2801558007280540c1d01c01d000180d0b07a0810700403540c10101e0f80343c02c11030614080000f11000e4070b07803440d00c0070401d6200c050000001e011920550301c0382c455210b065002041980035a403040382c12034054000b510a0360050250100300030394600c880f08050200c0b4500402e4a00300c0d500c000d4401d80d142950300c001a0010f100a6100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 550444712 1250 550443462 550443499
    0x30209060d0c08210a140310050607050607110d0c0204180b040b041b0b090d02030106150905090c09031002090a0b041518050a05090405070b071a011203090e06 70
    0x10070080050101610a01010482e01d2a0380c8107100d4105513010010052030352110361240310340c40034074404114141c494603104500170034540707107600c250b510a40209120090240100c0d070103009501c1525031503011000c00502c0c0303883d80115402d003004901031000210140c02c054104850035040881d04881a00f29a95094421300c0300751429101010220104010468048404910358982000f02e040f03c5152000311203040c464495200c4c003c16660000c02e0441d142504440050051810b001d40ca00d681c0b2403006061000e50301c144d61103440342c40c010441416103001200c4592002802401e000300c541014407002e907100c14180c0360400401500004c21000f0302c8081d10203049a8101d00844e0252a14001d024600c9170100080b4050100b0003080255503071038035034080310300c165910111941c80d400c11506080c55540911007036000020494100006003c1004c500b9140030311403101030740c07540090302c04403561500080211714011014000740754600300d4554817003401040c90032203000c0c4000c0d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 550445962 1250 550444712 550444733
    0xa140607050f0a03030b041b0e01030e1b0f040509030a0c0f0209040b0403030e120901180b0a020c090f01061b110d06060512030f0403170708160b0705030907030209060d 74
    0x800b8143c110010070810113a01d8081c51840074001c803014400b66107046001d005c110710b400e139120705000841c4112500b03640250402541142040191204184403401800411a4120005202e06580c0c0e03000c45c0d151900303106560045941c10011801d010311a0800e50351014411740958600301c11100840051b66001c0c0243d105910464203c01c0508081c5070140a4501004103410aa00403094040a050340401503401104092801050300780002016a4400c80c0503000000100000035085c074100da0001440d03098000c069a011001d13941c0c0c0390309102022800e00034100050103c020740c01c80c032003201030841007090040380c00328100f00030700000a840721080c560840e402c40c0c44000c10402407034401002c180c0c2c0080d2070007940ca44010410454810310071400010820b00b0443e10303030000c10609400b5603242d00d910000a954410115104060a40c202076044450000c008006044240700f102034900600d190401001030745c1c08c3d6030030444080c81c0103100c0c603000104281c843c004103000d00798 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 550447212 1250 550445962 550445983
    0x12030d0207170c101e05040b010303020d140307121b08010801060902070302030d09050705090a14070f1d0103151d090a08041203201501080106050a14060705 69
    0x50341c903034640ca0600070820102464420300031061028890302000401c00c0310514030148400140c140c4500c0c071004011810780000308030103281c141000100050052103a050b40e00a07000c03a0341000017842d04413411214010104500c4d0800d0012525080c0150100001b000c103040c00420f11a4121150110f000190b076014000201083e004100031002031040034080d000710347d025840c006864038040d41d80c0c460400f0010106a0b01d250481c1031190510030203000c0d1800401c81180c41c203001d15400d01400b403000c60400244025030229031001d005e0002040142502c0e2900d1128081900000c5020701200340310b5810706445013080c4650a04140c281000b6020390004560019500a14180b42c000001c020304802e034045010080410528801e460880d003003230340b442e08000d15030325085a40d0364183c0000784003040c04010b0441c81e444003084a00003003066200798461603036525001400c0c0c4060748915a08094024030901c280700080302e000780c0640c000742c030b254600692652224a40f005261 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 550448462 1250 550447212 550447237
    0x150f0c020102070c05010f020a171308030705010b420d0c02160e0f1b0a09050f241806070c05310209041814070803040b0301060804021203 61
    0x1407a5420000020344d10009494280380c450403615002a000e0750303d03184200080c00e40703401803112100419003002140c2b20203c4034070740c0818851b500c580f100e507282c210900c00c1303c003035081002c04207181c2040d84080e1140e600c1c02c4c8020860340340b64510110001d41c60680c0c10b4000082229a5038015045d50007418282c8245000180341d41c3d410a00a040c110509491115992807480c1000262032500074190020041c0e0204251a00c920032901c0404030300341068240705c0b10108241c0011074001c410481120002d44011080030040d40070030160001511004030502004c624525090b031001c4007501c00d00074070310ba918151041001c00241c0d580c200c003a0844901001580502c81824102035114804107103111003020400c030000c0f01c45031020302980300c9410b0750303011a00c01c0a591720794000c801c62800f8441681e0405000781401800b04800300d41c006a64403c545000610742400002c840864200000d02ca00716401c080d0100d4061f05c015109a030b10404000c01281101c9007840100b8034180c699 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 550449712 1250 550448462 550448467
    0x601020a1709040c08010b0a03020a05070b0a021803010203130b130503030a05090d0804080909070c0605100801182303040b0307051e090d06051f0e0f060405060d150f0c020102 77
    0x300b084240c13549034241600308100807004000c0c8002200596400032012304016849090741d120403640e600481c4405004a0f26a03c00d10550201d1a4000c04141c14821042c5103070b071001d6810300d4242e00c410b60314001072015884803800841c45c000f074020342100614190600316003403600c445203140c2054400710801507890050010510080150705011203440c01c00e8001c0e803402e602d410045010703802c0014003a0011000145415200b9003841880c168045002c20185c248080c1c021a00d244034040c1520075840c1403110f04154001956500c91954020843d204080180d425803000203c007029480301840b040c4030200b40c8103d1100550f00c1040e4540d00c00d80c1711408001e04040106180003014041a0200180101f9440e500d1442c0350140e00004046059164100703030000c1c2000d10170140d000c1e000c0410b80800c40312141b045040c06011004000501038540d44100021a00251001a406800e8110f884001841c00000f0404200508000034480c1c041c0300f160004d440d0201c4500340145d500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 550450962 1250 550449712 550449727
    0x70f03060e0f0114010b070c0504110a02061b090418020d12031a010f1b021e030106231002010222150807020705010c142d12070303050601020a17 64
    0x40055602989000e8024404c00c0b0212070380001160f0103004120a201000a2000a2258005ea0240100800fa03c10400d11454141c080b50f2500402d40990050242101003445600010b282031488007801680300e00d07040da42800c00c8000c00c004402c0c000e04184680c62400035035501c0810b010302502030003d5000c060b4424800404a8020f03980d440c0b04107949042c00d07001c0e81d0f480f032017407411004503041c5108015440108d0b8040b81d82d14030f0b8000c0d407100624100d0100001c40040c19a00d81c0400e5000b8010036132a401002c14621090b5900c10050310f060a10070381c1d07850800f1070301e08201d907540001450100311000d6450b042544030900000d42c3ca00103000c2010600c400d000c44040c408901d02519142042d003402501c0c1c400341d11805040000505900090110749803144445401d04802c0740c00c4a41116200b03c00c041c0d00d14001001402100401d400256011805c00134100704104a9407030600150750507001050003915043c11449a020f04074006020f078048500e02c0c4001e07106403525a2070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 550452212 1250 550450962 550450991
    0xb12010c0c1a0c190c171c0501031a0717040b0105010f030506280b0d15061e08100902130e060a0302010804080a1e0503090c0411070f05070f0306 64
    0x39020103400707040146020001242a0f1100343c900410a49000000360a00208200d416001182015220602c1c08444800340c030801030061503000700c1882d1301101103219048045c02c0b1a424031015040c19015055203180304080c000c0940e01102a003041341c041510b245030b403d4480400c07602200c0b115040c00041c0030701e40c0c10450300d00d1144200c2c5414402c034500540071602d412030600b45041c0083d40080302071010808a840903014000003180d580e00c030303115028210051320314640010f5048034860001b180440c070901d0f8002e031703007407003401c00058000d501c00c0c0c216031081c4002d00320004840c07221340201d10408180024052400200701c1c18500d5810805109420307207014184a1080f14002d4042005076040500254040e4201580d591240c08040040d903e841c000d40ac50829104201c50440b4829081030280d4000c1c202c40d0119002c1041800510003210300c000d40742c0050318000e00c403120010303900c01503414800b84590b0a695403166103401d015000c0c0b9040c3c20489155442d9054400e0800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 550453462 1250 550452212 550452233
    0x20111090d0c0b0d061e29040b300c07030e03010906020a0201020705062215110c0f06070f090512010f02040f0317030106092d03081b0f100b12010c0c 66
    0x140001403e010040c074162414254990104002c07c2c0144d00c0b418000c40c0707062003002d031401810400301d0b041d55682e410030641440020003001903e080340768003191a04451101070340c3d224404400b140e0745030504c20784050703414000c039101c5640c6c15901c40b40d0110000c2c54134006020b03002e071150005a00e8001610700395041c410001c207100c60303003c4000781c2602c00f030101d140340c0c4042c1070b04030020b0216014005c1070903007c1c228000780f200c5698000030b021810300f44005041b1903100c0303000d001c0d40d4168071104c60448940c00500801c1c0c00046040c0b1060040e0300d4a034121a01d1202c050b800040c0a52400a0034010b07a0841d50260758070201480d410818012151051410b01003010611440d56051400c082e00d54034960207070782c44200c801aa84900300c40052440d12001004204004240303036a4070f0220450f030300011200c59003070070b02e06400c009400300096110003440048007510a804001c44442c0043c4001060070354445070f84449065216400c5c1315070b183c0e41005943d1000b0304900d40c00e11034202d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 550454712 1250 550453462 550453499
    0xa03170a05060a05100201020409050103051501080d0503160c020405070e01020c03030403020d0b040311060421080402101803080c030a170103080a030b061c1b020111090d0c0b0d06 79
    0x340c1070000700a180e076a41c204510540b0000c807040201d25141c41012802030146030800c2910718985400441440400103240c00c40880c480c6100381c0c00d03a26620a5070302c1e0310109529101040003440410040e898031070400c0008a914078203002150080d800007419150250b865101052152488941c0fa59041c00100e4100009400842c90986558041547c481e001d03103020305100d110f840814101445401c0800c480d411000c02c135084d5080906151115038008174240752050921090103104900502081e44206d4006080003c40500f80d101034900d507803c020f400345840568070307010000512810207003031011008002503444840742d4801400840128048000180c0c1b0403004000240c065421220790740c000e0716021038044984804502c140c0540704c40114501c440030030942c2d030b610141c0d07c40e213103040034000b140c18210700d020400c0e82203441550390000740700701c10030140d010303418000d086015851140452042055582406101941000c180d40c006d0381d840c2d03901085600d91003086003401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 550455962 1250 550454712 550454731
    0xc02010c0c020109030803060d080c0303150a05130b03010b1e12060f070507081204080d0b06210415090b0702011a1315080106060c050f0c010806010804140a0317 71
    0x8601c4540029104900d0f81c40010a0748074000002041a1139000780010b031075520602c8291a020150584c40d03d0740c10480b415105c651400c01a01010301d081300984040701d10180440840d24203400c207843c090070014115940564894010b00c440d40c496024005440780c0c0c01c0d00c2d11950786414010000440440004024160312840900041d2010002070941080c49418031b140d03220485e10b040407040c01844040d50704100301804100a005403080104810711306072100b00711110001c801c07c80b041c01400048401000f603814100c90401d0f00d90b000710f401a001e410803489407020141c0c5101940c4400c58100c918034040000d01003207603024000d03040c4840086149039001880030700401c075015000140b07400820b844040c0050400c258034003c00180420ba00244280360f1110005420740c003248004841612419040042003680441d408807407500c1652692041c0d12442d004441941d80940180d840c0c5100d1410039010b403404018028034a8420740b202c0340e980d00d65011800039003100800b0742c0d20 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 550457212 1250 550455962 550455977
    0x3100f080109020429190e070519023009060a0c02091003021027230303030c040b030903040b0409320f07051c0f110a050f030403030e100c02010c 64
    0x44411010301500c0140811b84050039919140e205403440141140d000c0395a205c150424400084d41c00802015140c1904940794151152060300302d070749040709031060300b440700001c05034405400b8903111003000050781540d460801009800041882c0d2281101001003040e540e000b40445c24944001640f047c0c00f036910181d1940f4680200c0c1450300300b00d8502c41003106428682c050310014400705d11046210309412450a925108011454041c8000e2010441c2252480e5400c91400008817441803003910611402c10303241212810603034001901c0311145000c103010115103000c42401910090038400c0340403c010403480d050070030220a800c0d08900b0640483c41c0c102e00b0300243d21040ea04000401d2050240d6600e03090200c5040c0a203138074015403658403003140796a11800e600280e000890840e000c001c41c0d00100300c1c00304184107858000700869400d010a03400b0040980c0950350103030217800c0101e1000d21150115040c508400c030f12400c031030b644861700352840b60b091068042002c0107040510 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 550458462 1250 550457212 550457261
    0xa1502030636101409180f010504151104050f12030c0304180c0219140d0e0306010608070219020418081908150904050727150b0f03100f0801090204 65
    0xf03604a0464013140c05104181c01043c28500000c209100c60700c202403c1d81e40d9102c6814855018200654043e00c0d00c1469104082028080b40300350240b2030703c40c0410030310701403a100a1150380c000e003110392940411003801112141d01c061005020440740c4902440d40c642c14510240581e0446155030f042d0303a4503010300154000c0e00010440c0740c0780340741c21019508402e54549040610480ca00b00f141c540104420700c0201c54228801d8114060114151034050b078841004440d40c40c81103400f5801640900c2d2961808810b040040c980c0900142022501081c020014207005180d540c084850307000005545625100124400d124039145140074084e6080c4042010002c40b22109007910980e0104042805c00108000540007410180d4006030802001039202c141c200710500714601c620f0030032100c600b10007019182070054809054883d428109185200712071900020b20703140d00503120507000700d408450351110300f0007866000004990843d5520502c4103552500030088445480c10704540c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 550459712 1250 550458462 550458479
    0x307020a0909060609020d0b1c110d0501090501060b03060f03010b01080a18050d0c0c15050301061d03010504051c0201090c0306182a080a150203063610 67
    0x80125075039004042401002c50924000070325056000f03400b140c2c40000c00c440f818885410105850604565612580c98400f66080400c0c00c03282004000039542e4600120707910307041c1e0150142e140940c00009035065140e5980303007103951907000998a00d6000c4100446441c000101d80ca041d0400d42c0280268038800c40040c101c1d86020305004030840c0c488500116100d0413104098403a030b0030404440300c00424110103031100f81c1050007650400551030300030071440250b04101d0401c0c4404c0c0e039480c0c50341e80b8011003251900c0160f00607085074860b4040312403469500b4028140142d0040c1302400000108224462070710400380d4059096904044c000c03008940e8071030300e034802c9a400c01c1c00401c0e5090401520107081c0c180c0fa10084c8603402c40004800d40d5054000d048404003000f034068074450380c42e484040e80d10002101c000742041c03900c103402105041a60050358000c8805010b020b405001091807030400c1c401c0c42075623050300610700007485103c01c84051054015074030b961510700060030708004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 550460962 1250 550459712 550459729
    0x10509011d0c090402070209010308040f0b0c1b01121b0810080601050f030705031005010801111c0902030c0a0b070c0905090a030305041e0501090b0705180d020604121b0602030702 79
    0xb0250b45110106004001e51541e804640751113500901118041d030310303442c00a9050300540203102009154040129454000310b0848040c041d200004081c00c420030b401e420454150411120b041102841c54207001060500039111021260a1039110740c042400004103070710700003403030041011141001000b400c5070200c1d22905582c4180c0307048504406135404239240ac2465440130350984a02451242c40e40426803019060f80c0c641da00034021040722029074840e42c0181c13820180c20072351030507480141c1c01c5140c0c071503c6c8051014041c3c40307040a0310400124081101e0348442c1c0030a40003d030540411860703c5014007c0e0081280400040c1842c1801681e580b80d9807a0003002e01d0790b2040400c051140008179040510960b4a07010312007982d40c5040c6018119201d01107503a00c0d0000c000c0ba180b1402031042e10a4400c00d40d08000034000c20100300041c084d00102d0603030304503108001c04501078600e41200343c4201d015404441907200310320740d10140b8826a90140045400a000d0240181d85000c403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 550462212 1250 550460962 550460971
    0x60102070f060e0402070c0806070f0804031202030406060515092707081509010f060f0207030b1f080604120f08060618040e0d0e012006072106060206010509011d 71
    0xa184400340c1043c07000c034000b4810714201418035264030301e0010301100300242d03443c424400d90f40d905213851183e40d42503a40344405d9030001d0102e0b6150170310500310310495001e103500078010b40c400b0410b16900d8010800d0003030804c55022085d04005010601824640b580409105560108c01403508120490341c001c0540a043d410400c000c81d80800d0030800d82e0680c02c0c0c1b8810004010b0041560341c1e60100421904d1881518041444c20780d001c2c040301d001052000071280c2041c0c1d9100d55680d070020150b800d03403484260f480346203881800440e100500f0440705100314070405010004034000d1401a10f006a040140d1040144070006c2000c80d40360740c4140c0307030404050300c16000c06140f07401c0001c02407c5082005801489141c440c1c006841c0c4c005084034031040d0a0322152690b41100c120300c00b4190800002d40a242e1102010a46880c808d101400c284460320851241c1384888204802c25074042ea417011006030700c00c00041c041c0d45841601c040c010075030401c00714640258a03410a890a10041 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 550463462 1250 550462212 550462217
    0xb0906072406120507140303121003060f0b03070611030c06040b0103020f0a03150f0b09070c06050c07080403111c060204050a060c030e09091f0e0f070803041a13060206060306060102070f06 83
    0x4100f0740040d1001c0060b50301d00001e4041104061500c40d8ac80000034005100540d51181040c900821150192051134109000903028001c1c82d418624152001282c154000c11544000c200f1005610014001c8602a9229283c041c0f81545140100082104c207851a60712801a4241c20000203083e42c62500320010700d1003021403900c000e282101d000b031018000c21508603142c20100014640e1100221409503c2040200401d49481c0120320740c50168440003442c9807020801400401c8003181804425280201002c02d101d42c2010500070501c05480200c03012600810140028a40b5064020141095107410140c01200307480007485443c811700c031280030305040800314407968014410042c03162139443c80c400d4800440c20b52000240b03556101034203940241000000031140c0071440f68122207040e801181842d00b443d03011a0028504468104000b000300501c1300c013201a40d40c207000a1007036401030300c3c0500e0000c0030305091510041c600380c1150002201032010150b021000380a899591 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 550464712 1250 550463462 550463489
    0x1003060503280b1302010809010e030d11040807080d080f130f030c0501020c100b030c090118091a0106021009080d020f0d05090c1201020307090b0906072406120507 72
    0x40486056003900401d014000b1a10401045450200e034030640314003174402c0e80c5510f002d9465200b801d00b00e03280b149100c0003580080043c411400d545802420320690003c021515060b80c0380b03109450040703150710503507854100b040c0002015030040810b80e4084440d03070030740310b40386408285600c2d900d201f0600241444914006881070520840002c1c880d02d40c8074000b1540d905a004a01d41d440c0241740b0b01483c69414600408014100810b844008000250208100c2d0f401e10b0070701500c1c640d1840a07201072540d269503407400f05510708440c0c401c00710907644c6a451541449402400c003029003c0c8844c241d420110484005500602240c441542d00c4000585a40072011a44000d104042000300300b20300382024002c4030a0b0101d0032020f490400c689000c0c9100085100500740e0100329600304c08580a500e04005980505000341800700004040d40d1801aa943c2d440c0e181104d020414003401c40c010440401e4906030b403282d400a48104688401820140d035110b50f03407015640112000701165 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 550465962 1250 550464712 550464763
    0x616050405010c060902092a07150e1c0314060f010f03050a09020d05060f07080c1210050603070210060f0308070f170706091208010e06090c0c0304080604021003060503 74
    0x5551003085d0140e802071140a66040c15190302c18845400042000040041ca4081214a0b031000c11144c05607400805c0d201c1002c440980040145840f2800c0050fa00a03a440c0c0f100d0f40c10340c04039100c2c020303809440008220040c014010703000e080090496010b58100045285c060ba0000341c10420344d0b5444c83d01003000d549807544080604041d000007134115080905070410000b0110b030640c40390341e503950b201d02c241ea01c1900841d04000140d9207508004001c00005504a40000c0c1c0ca640c000e20304016420541da680700814504d910407602c88005801551503c19403404a020314001056484114452203080d510303030381c03010b220300c11004101c1680c10303200004200c0b55098004100d80011085605d91410b400c0080141204030000c555140e01c90501441e114043c0520505a0b2480410309034290344584c1070107070006000d840203070004001d1045418208041000f04060006100601641e04061042c48803d003501e130b40c854141801c25a00f845561400520601090f08460385410715031b26 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 550467212 1250 550465962 550465973
    0x30a061a0607150e0303190c141b071e0e060a0f03031115130b0612100c1407030e01050f0d09080a170c030a11090a080705030616050405010c 62
    0x4000301840c0c0c0002010030040c0c28040850030341e484050100c031090100202c0610125204e1001700e5a0800e254030807590350b9850306250f4050f05500420b41000c2c1d6921000d200c0101355900100034448130102809407014402406004601c000c03c0840c0c0600c01e1030034507002000004003030f8010529001e900c9000140d0690b10442c0d108010b200517075142c24125140d01380100003a091142e5841c8511034007089620f0410809499845407101400f40341010420380e41c4c80e409000b000d001d507a072280c64104248010741c0d01380f054000303403010202c0001d00049114406409454145a07141c451141409604007107a00140501004082407a003030740d5508008150550a00500c800500d086180c103440d40c080020745d0005102c4102e01341c84e04620307044206003c0200c41c4d01240c00295503c4188080f60246009030840898003800e158070505140030f950214004088507480f40e441980600400c0110b4201409903d4000c514841401c0902012a0014266204510a4070b04124140a00009100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 550468462 1250 550467212 550467251
    0x108060310091b080d020f1f02030c1b0c13110a08040309120501020306010e0d030e100306170307211d040219020d030f0b150f0708030c19030b030a06 66
    0x105590f0b100c000c3c2e162508645070b0b98072040941c0b00098414280d6a000c070003800559460002003a81c00d05405840143d6050302941020304010601e010900181d031070040304444204001200800421039620990204501e10000c3d40c21114403d25001c0310812103036600007202d180481c142000b0710162511702d8211207800c0650b119281ea4000307000c0d031004008064000350302510090780d071030400d60004400c220082980d0400100407903248944240c0904068003042ca18408900380001d05640c1c0b40045203a051003201e04203040c0e04005001410801b451100580100800c41c100d04500ca080c07901500b441e00d004001c00401d4003202194000da0f4a80d0101c50304011030a0010f2101070150f10080e699075401c0345a03801103410100c10305001c1001344107419500390b00a019a4049034810006512640912412175030858100141c0d03020411a030001c3d400b0300d81442c00142c0c1e030258088200f0300039000b0010a010982041c41c00c008a9400081542c1000c0e08014005203d2803420003000311074 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 550469712 1250 550468462 550468493
    0xc15170c090d06090209060108072313060c061508061b070804092c0309090c130e0f0c04060e090a141905010b0c301215010806031009 59
    0x1412001e00b04980c13030704810f4101c1c2c400ea0b610001501c40c0001550030300801c41d003d8000502d10b06003141402001c1c034200d0041103c0180d954600914250294100c041e07540045011508891603001001101d1007000990000103104550780340c14151219180e65015020340104044074200b412000d04075021070740032035407100142c0e036160364510200028180c3d03141e400005540e40f40c660303054141252030f203600340c032800c0340954503290032401040103d4502610710b4810150600500489004030f0f00c1005c00750800551080700c602d401e8030845c03000300d0010081407545405010030050b168000b61080100e000840f982c550b20341e506071580c0020000254502c40f1000c620013030200280d6040707820408440e08540511881c2e80300d01c0080341c1031182a8035211141c2c003a1030010680114003c50488000c4044500c05205200791803c0509800405070f01c03105c000d020062110762050803001d503240801c00c1c20041c0152900c000029210401400d00000c2141c807010140708202006040c282c0710f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 550470962 1250 550469712 550469719
    0x40519060b0402161109090303130809030304080f0d0c08030103061a030610090e01020c0c150c1218090f01030803060d020d060209091e010302040f180f0c15170c09 72
    0xd80110303103142c000d0b05002020943c5e1040203401510210b0a1024003030744501301c484019403460f125458143c2201441c07800603183d03100309010404190340c00344001e10080c9000c00003815092035890b401800c0c0175108480b4810f00c0180c08007040061500d4003500d0444e50010000a205016403440310008410f21401c55494000d110401c40901d000d014400196003001c03804010180c01d80866034200d214000c07212501c0d9100200c500c3c0340b0318001c90070b4601c08200207030581c20301400d112601d1620030500050181e41c82c1c0850040d00c501600542d41041600440d44c6921900f00b01c141c14040310410301007d40030f107070004000354039501d0b03c141040c0050b5001d00790090030040b500b0100001d41160036080c0c8103030628008112500154441a003006e240000d01070101d07484c590800004101ca00f00c5c03200c080341c858007070b03195a40c5007030040c9403414007030b408107642c1c440c02d03250810382c100850304041d44400040145540d00e69200c4103481200e040d80c08400300944039610310320054014914250360 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 550472212 1250 550470962 550470967
    0xf09080109200621040f0506040b06030d210c03020f0a0203040512030a0219030c020a14040606030524130c17151305040212060a0204031406040519060b0402 69
    0xc000309400d10b1003005003110245400002e044040100758461184481c031003510034003a848003008190255604039102e02d80e03909044485548890601c81c01300c50075142e41000c00300b00304203402c00340401d10301203030949080d0314040141c1d0000400b200f2002200340980703641d81c40c0158213500a6045801c00042d4888058540c0010f510007950307544240a803074011250245017910401c0004240d800d01401c0e03030041c04284c0201c050700741c0c3e80f440d88241641040500310004025840b0071500e140a40301c4452898100407195040c0f10075a001680700c0c1d0304052403c400c028091011001d40c0351507407501000480c8a05060000545804500c4214008a8580342304160141d4100c5507000304031070010100c8031166202c602d81d134855000c81404c250005040505004e00701c595a01459005100900d00b00015900c082d207240b420800705ca0208101c0d90010782442413000400c002281c01f5900002010300e407602d555056201e054103003085070340580091444041110a400100c85604042c0c0b0454 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 550473462 1250 550472212 550472231
    0x1b030b03030a08360f071706010b070809040f020304031107060f0c020d0b0903030718080604080913050403270317030c0d0509010605040c030207020d02060c01090605040b010e100e04030f090801 85
    0x903250b8260f04d100350280e200381c020006241f0008010340001d412000d000c0c0c031840c0c0c81c08821400a80c0b00200032a4501001c0104200d19076803482001c0030600198401a01c9191a10f009001520448048000303507204603801c1041c0c0d58481d002550b01d0a031464000026850f62000c1402c50144400080500640e10b080100505000018501c140c00740d650316001000b01804100802245026010058100d00e00190105103140d0013401c1e6548040c18210f0640c070450300700d0080311820355040300028080703040c084c0c80c56541e055403034400301e0240b01002c00320301c1d656551041c0b2541c010000e030141c40100c0050091860b003402d0f140e50450280c02800680f50050b016402040540603062040c3d06d4013001202092103442a1080c40e46d000e4400d004124458003000030315085111840c00c00d40d00d0302c6140d0700181580c0600c5e80158070800c82201c055042c42c945484c114801443d00f000c01480100800600246c0402d040e00b168250400e030003d9400c003241101c0c1d0b1101900548503640c288840c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 550474712 1250 550473462 550473571
    0xa09111012050f0402010206010611030904020319020c010b12010c1b02031e0c01021513060e0c0604030b010e130210030b1c050312011e17010b041b030b03030a08 71
    0x3d44914401d17400c2c0c1b00545c1e00c1ba5003e407213941c4429803c0d6080d50040c0003061a900b4254011600b0580624040300840d0701103001d0001e03a03200206854550f515201c010a2905041c4083c0742c0281c1040001d01c15090380000090460380849140b403200d0f01620440015503d051012400000900d09001c02000d40d2500e016615603041c84a540103100da22401050700b50854480c5001d01030204070b2064240c0661a50005064240344114040c06000820f414540c4c0701310003840214418143e44102c1c0d0b242403a200d0050303500424450100505500c4400103a440601552000401d414005031550441d00419041e804242c084014030f040224414144100040035000b810303d20031065500c0da88980031029449400040f81c1140d51710382c0f8040c004400300700b030107030800310141c000040d2548400700002c0540e054881d9880e20341c0c0302d18050a40180d070600903880c401d8002c0e0001e5281900600c0002c1031190020040c588a1621022400c261903480b01c3c0e00da48907198051060703e01c001d80c520f0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 550475962 1250 550474712 550474741
    0x6040905030a0203031e040c05060d0e060711010b0904020109030206030a021621020106050a0527070c050615011d03150f07031a0d03031d030d140a0911101205 70
    0x300b000c002000e031200e0000c2d11424244d0780c490740c1d08c1100d40d0b400d1403500d41403181d1900300c100325031000c80c4c03141e008000541c0108a12031180309551b440e0164890310014140c21103001e01009400f5035801c008100160340c0010007001201d5061301c14550703c1d0798206448009020701c00c0000001070044140c0740c2403000c150503940c40c6805800401c8444d0000c88400e07400c0b60000e2240320b80103102c80400f00f2881c40c00050751031070100d440c3d002c00000d0740510300d03110740d180e03044a907a40460442e550420a002041083c2c0e58040c03a4180310301c2c801c0c5503600000e06003c1d0340c3e61803081d840d000b26401c6400d50f2400d20140202c41d03003086124256042820003c40d401404855010003c0d01d0010748241000d0340714402d0300a5207003d0142c0f40c54a0241d201100074000d03040120003110b0001051a1504078200000c040710104403100080f00718411900c1c540903a005401c03c0340071801c01c440318000c41d0700ca12104d42b282c401256407000c400c541c0002929500300300e6246180803858582003001c401c504118 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 550477212 1250 550475962 550475971
    0x706030902090a051b0f091f02150c03130f05100605041802221512110d021e01031806021810050406030902010c02090405012a02031206040905030a020303 68
    0x20351000540c3d07840001011190100c2d003c0b030f000f01143c1c1850401c003000e41e0007041c030481607006103460520508003051068180300800782a001e503008550400a60502402004101c0b80b5151911420070381407503951404081c01f51404038011402e410100880c403511902100c3d848000d9070150580016110000c0801c2c0c03164900a600b01403c0c070000081844a02001c107500405840c00550046850404840201442c82030380b40d5400c800e03c52820b0f5402090004d00416900103040070161074500102c20690f00081c1c000c11110304013a0060740c1d1800c080c04445081c069550040551000480c05084d10010146580c50800c80b002d0501142e50020010600082c4007014103100700305c1405150001e5074200c0c00061014402445454031940011100341d005161031401c071384040c0c00242402009031811240c0d0f03992080030521a502003040c80303811540500051805001c074280c069201e03c1441142e020203d030b2000010b0440e541c55205020164001c0c0c1180c2e180c034102d10001e90350350320688 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 550478462 1250 550477212 550477219
    0x6050a060e15191e0602010b1e030a0605091b0f060708070512030a060303110304121709030d11011805100e030f04090903081b0a050c01290a080f0d0c140706030902 72
    0x1e00821406d005004003181d40b680501a2003040130200c1e050300e00c600110b0702042e0305000d160103410100c2e10398010f19001e00d020401404251068824580320220142181c3c0c1c0500c5034500d14000e2560f8044c1078803c143d400c07a105544e40c03140b502e001c80c1000d54031580507400c0c0300302105001e1110402e038480c4081c0c07071007502e808040c3c142c610407c680d24005c6102d4005664001030740c500c005070032520488800c2c5003d284040c1015103610001c0c1c1058200c00207800041c110070444001c11307509000341c0d03440300c9101c1401c08940031107031601a1100e040c410901d1240c0d44500c14013000c00d03000c00454880e001c5c4030719417517120b94a034192131014201040d03003a00002d02c00408141d005070070404e4520761404c803a2030b0919100010200341e03801d403c9107528030080d541e151840c10400007600d01074040981641c10540d005401c560821501031250381200c0d0955014002038001c080000904030000c0304141800038522142d480c0403120f100b00c04202d02401c0c05101e10008466416412852003640700b20b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 550479712 1250 550478462 550478519
    0x10513020f04050607151a040507050304020f1215041b06080709031227050a1a0d150503120d0b06070b1f08070803040306050a060e1519 60
    0x2284900a0740a40a40114068000c100c00c01051030100c00400c5090f00c51060107030f040e000007440c41d0031250900b690308114689907210400c985070034816a94000386904085003176040a4010900c01100d0169150180b400d1502c0c00318200c0c02003005081e400d003241450042c070324041c90b080018440002800e40400d8180d480030aa09019a00c00b510690560307440c0034045140d6202e0341050700c0350141450611204145c0522920043e0180e40c030f50103120145596640d20302002c0c883e910b000c1d03900019800030044200c0341102749020440c0e8001c0a003000c080b5000e6900c4441d9100c180407a4002541031141d00e012090601c0703550060651105e81001c104080010038050103410f1003400c0d0010018011140001c1100c020844200107809029464952030750316080c24034030f031a2503500441d0440e40086000c10401245000d80740e03002c844100b00b8020303507103004011509614042c1c07107040044030016900049480b0210052601c1c078080010801c0955a41503120464540d52414120b20709107 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 550480962 1250 550479712 550479739
    0xc09081e030d0f0207020a210b070e090420040501120b0a020c0d201501150c0212032d0405010516060f06031101020d0509010e0301060806070503010e0a05070203030c07050f0601030b0105 82
    0x5031010740303100c000c0c074201c92300e00144c65595a0030300c900003017544d0180300f07800d050045903440744000d031803140c0c0c400d0780c80e110304030f0140790305005000c0013443c840d11840c1844014011405091011640d650b031090300c000e416261544801d0181c0201240c42d0064850080a224082c3d8421380701c1540b0003020440402c107800c1d60b08802e0310388030880003e41100056100402c01400c540c0d01c0340d400003185141c8003000000943c00102c0441c07620384201e105600114a00d03140c05c016050803480c120141d104a1a04500031381244140d0080c3d108007818050045220400900107620300e1441940c442400c000082c07a6603c02c030000d00960106072031200199035004543e500000da00515042180c0f259414580208011500c0058800b01d694065481e84000661850200012400344280352a11030300e03981060410002c1c5407005040d1041c4070705220500007015000f06c1208e4002056042e9035548a4541c1049443e0084000411031248210130000041c0304007a990941a19012154000400c0c41c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 550482212 1250 550480962 550480979
    0xa2004030201050306010f0e15030114041e0b03030d0e0109140f06010e09030f0d060e0c040b041e080307050607021002091c0201090e0a0f0c09081e030d0f0207020a 72
    0x1440c000240403407010004121190301800e410b01416110f490320115111144001c80d40160500740b0400d4405008001802504400308c2e03503540d851001c0e00c0400107080880540b61003460714000303e82c08641e0302c0b030311801951000c0c0100ca1001e000300409000701050520294001d20070044162090382150300c4135607040102080c2c102070624040001c181341d900300b10800b4030708407014201d240c080c402040480e9170782c95403401038081404844070020741149081c941140c54000200350b464034900400003400682c40340001c0d2010354560f00c254000d4203c3c15140d13400b0240c403e40203c030720b81c840030800740200840024118418001a402d4070080841704c2d80020030b0340940c50486034401d404c60b41d50401c116150400350003507401490003c00407681c0743d1303034250030b0300081d07079903001660300c420351900d8450b65801a07110303450703043c50100c0100b481c00c40416140d00c10801000c4040311050046904480c0800907506d0b041070441e81040f011042000f42c82c001e41c42044124040c031240c0000180404 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 550483462 1250 550482212 550482217
    0x180303020f0c221a03011503050106050109060f031503080f09190f031419050a030206240409030c1e02150307020c0d03050d180b28230a20 61
    0x10803029610189000b00c021410180c070382c403136030100c20410300c81854130142d50034000c548000900044002100341142032050a54070b468002506105003c8802c1010342d40c4105d0b2501b0b0303401d0301e28000921090000c0100118501584041c0c040388001c45e1052403600300780b00801601904464040450780080c044450905683c46400c040f0090b00b5400c101103900444050803006100c800d072403041c54240c1802c4003c00c2450801d48055100102040406404000b0560068442d0600c0183c01c04840d140600c844042075141e40101d403103284000806000e482c80e4030045c0d0f8402d441d40401900c84100803d01c03101920240e01c10310701240c0000000c40c0304400c5900421050f4041d000402e20003003406140700c04c1000807000c02000300000b4040307801620840100321110208002c02d042141450969070381d0207440180000050300b000c0800c640c0c05652130041085003500480c40b0085448903604808901245000b880040e9003040340c0c1d90200d80c4035102c0c1e240c841000316480f0444000b07107807050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 550484712 1250 550483462 550483489
    0x1d0d03020d050c010f050114030609030306030d0e0d02040c02010e12040b04030f080c01090b0402040f0e1c170f1f03050303070c020a1d07020c12060406020307180303020f0c 76
    0x6070000c4410030051440b4100030201c071401c1c1030000c983c1d4601e8224440440394264032219022170009800e91082ca01808055003101d00900150308608040000039242c2c0440010642442548100c86405881e4510102d0065400174403c0001c400100340181c082d02e00d92180c0f50081c0107200c0b0b42d412001007c0150340665812078846800d09081d66182e0f000510144402c2c0c0d550441070158960f440d009004121500e031045003480e401c0c1c102881030105031544100310344201410000121f090a030005a40c90f1015550460b10b61101d10106054030010852a602c110030084442086801c01c1e644c4050350040c011a04100c003145005522080401581e0000a0040d001080401d101c0c3c1d03c030b510120310050000b091400303980e650303440c80c0d4140030b00314844c001010f0084080007801901030000007006070040c2d80006c030030b2240819031615103200a1001f01815402300100b072509105064082d04e10250302c00520001e80c80342270280d9100070091915103144285183c5002c86e007003507081342020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 550485962 1250 550484712 550484717
    0x70f0209072d0c080d0207050f010207020405010b030c16110301180c050301020c030d0f02091201090308090f0c09041a100f090b010c1104091b09060504021206100c080a1d0d03 77
    0x78865142e486410303542c0602600c005c0c1540a011880c04104107211001c00a5045000181c0c2c4110798810301c01a500168007400500805000b0040c110b80c1c56021502e10940c0080c1d4441520018540a8640f5041c0d00542d501503282070514480252480c2100b0300480c0514021030b4050713542c10405007070344501d0031001368070381042c42048503c030342c00d420500451040032005401c040c8142d0102e091628603040d0b44145a45540a400c03d145e000710328140c00c10089809040f03d44040714885e030740c1d803190b240e180b4002c11207440024107100751652201e410a80c0400150f0060600d000304141e000d55038012040315142c04100003806407120b104420003010b040c0c54001a080098540012a030048184141c2054896941d000000d615520526220101d420682d0b03006042003403110032140da5800090149204001a080c004070031740010380d101c3c200300d583d10030344031072003e08854500d1031041c002c1c595440481c4240840740c00c020a61501d00134030030341016036119072081040c41d26480d0b102901 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 550487212 1250 550485962 550485977
    0xb090c0a03030f0c0b07030203011e0b03010b09010509090408030610030506090f04060e16090c020610030f0f060221060f0a09050a06050306011814040c0b070f0209072d 74
    0x902543d50902e01081c10b040c1543d0402031500d525540d001e04598490000b9400001400703400c04400000e42c81c00050002050701c1420030201041500c0706008030690300d0340c00315400a1a1388500c00b01d613035007480907101d18802e0615161a407100d4106554003031160001c0740110848a110f44941440b40310001e241c41d00b20b0712120441092840c0103402520b4454682400b500300c039404101e000004058840b4140049141200417401c45000715003040854100c01e003400036201e03141c01d004054035000269610b02c0015840c100c01112000b4000401490010606d40400320b0944000b00502c002c0d0520001e803540c0309410010071000030720640d6400128036030140040b04990b48015803025101c600000d045446000133450319100f40e0155080403d182807003546403426020f040b0550321013402421840c206665a03403c0303800a8010040c4220021408801f400030300c500481c8481d40161040e455801c1404004284442048050150b107800c8042c2c9904a0794817a5502119429540d4400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 550488462 1250 550487212 550487219
    0x7123c050c0c0a0807020d0b181e030d02030a06170c15030915040227040c14010f0509061905030f0907080a020d05070510410c1005130b090c0a 63
    0x3545d41042c2c50aa0300b15818511082c0018164080d060207050b0600240884800704145240342c1040344408101c80c5c041400f031100120000025900c1380c1c0d2184502507140da444560a00040100c2d50104050050401801000c060041255203e488040c1c8040d20482c81204441540e44402e81301c1d902075601451050840000b446401600a031008006001003070104c5004c03c07501039800500360000030200701340000c200c2c0c1c01c01d040707004195480d00000d80340003030300001c0c06004140d072009040c0440083e00703204c44e0b980c19040b10600559001040955011054010b00e1740d00101c070741c4440320300e845001c0354509400203680b90807948010018030005889030300384009031450a9003120548500400403560b913403403c0302c5c44002a902c1e0358601510603000007001404000351041d20543c3c0c5002c644801c2d9500210548200c0f840903940981da4070881402d8614200440501c41806403410081c841c00c12012440380394594040c841004160310703040030391500d900461069079032000000c0c0081 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 550489712 1250 550488462 550488473
    0x1308070506071a1f061725120915061404090803010501110a0204230a0504030f1d090403020706181202210d03200307123c050c0c0a 58
    0x5074402c80d1300442007003803c40d41100311186007085e0403c00200d002d514054584c00407107401300741e0200d020072206401f05180c20554203241301e04442c0e0340802c60200441150f00525400400a10341c0c0003404040c40640035407000014070581c0600100200c480c5003659452409014107a41c070b90b000b0107510f28603460100190b81c0f42c18260400c5200b40910802d81c0090781daa4401d0200008541480d002000f410021032444413500800c910320003442d110921000c254000901c01c4003404a041c5000800d07480401310001445c4829403a6010305007100304030405601085540880e0b40c00d8880781124041856041c4120609024415803000007884034405071902c240d50980600e101841d020110440d02900d90400c1a00204c500200703466103981b1f514014500b408128000207042c000e421030900410050240c1d140341c0710380d6001c9807035a0801032003515031080031460f051550000d0380c0d03c510016580001c04903c0c0c1c2d80d440c07403030301d0040002c01d4844100d0841380390a0070030010f480b03103030f9696656 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 550490962 1250 550489712 550489763
    0x6031b04150b030109090201110f060c09040e0f072301020307060b060408190506060103060b0910030608101e0501030812150904050606101b061a0402130807050607 72
    0x30000408008800150030baa00382c02540682201e8a010a54030b038036000150801510f60700b4450342e40d1182d181860540b0380440e0040d000b4140100c19907a840c040b03000500030b0009045408a07500034407100104d69500000c2d00b6044030090905101039440d130805086071480d40c0b080e5540581c01c10040500060019403001002c000002c118606040d21126994500018080c942c4a41c1c821000d1805c240a0100503160b0b01c41c0c800d00e01844a203081c001100101d00540800c0b41c028001d07815003020803400b9801000241c2170800448400e003801004c02c0f0b001e06648132500300707501c00c04038030140c2180c018003409059a412040c01442e28039030060143c0c0000c0e00404480c0c41000d010a1541c180e42d0302c00106025038010401450b05060200400407000c444900c00360a02c196038a00103003070302d01000c4d0490f00075040f07140040c0180d102500b000c1d2003403525441c0c5521078400214100c04d640e0038141001a102118111030300380b034451003800f56a11840b00041c0444040b0704203c0201c44251a6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 550492212 1250 550490962 550490981
    0x250b0c01110310060905060901050f0c0106030204050c0a03050a0c1e020f071706060316211416080303010e043f020d050423010215090105010e06031b04 67
    0x1d2800015000703007810741040d6072a84201c2c1404500704006039100d9540c1000c0c01d012940c403484e08052800207000c9200d441c01d100c0a0401c00b06802a00c07800a5001c8002140c01034024045031401403040f50302d56000210780c00110f46807c011440150442c402c800e03000d600b549412540031102081c034002da070102d21f010b808511a150f0703e01800c2c0005d024200c01010201001c000c0100001c10550418200400045c060f42c0078080c19462030600200480464040c00720740c2440c5240900008114094030001421001951801a22038107000680d100e41c4110140c3e00d44100792100c00980d141d120078415030401d280d4110208000c18120f00c0d8950924114898100f0700c1d8500c2d604001d049200341d0307842e0100d00074082c44180d100d601407110b42080030305440c01c20315003414401200d419884204103441260ba8810030074000780d00030454003450340d42c0b40c0100c1034203217098944240a05002d01403004001c03003001c081055400d00058061801c00524071b1010201c1c01e640901000307054482 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 550493462 1250 550492212 550492237
    0x60607081905070c061d01050d090501021201050f010206010b0d02131d04110d03050403110102070e090f210702040506061603030e0607090b0403030c0201050f040b0a02250b 76
    0x101072401144050003032030008807103480d125110103641c00c1100d4a03103450380c810002d000d103070b1403000c1320a0020800300519200034202541c07142440341500c401014000c0c40182598030000c5e41d0000a0801d40704681284d80c11a5200003440341c0b00012030300c2c3d00c002c0c461044851030601c12035184030b605401828086890b044441e0070190380b8011544190400d440c008551900070080c03009120701103402c0c1c000c8140035a00260814015540109284103d120207003040c8801018486a87c0c800d0184034002c05444642c135165013031401d580360b1a410b00d004464414442c07421501c8119010030702854103003c0803404617003030000c030b6028007002d85401045907030322201c00c2042203d032040360210101e03494000c0c2c0c1c0004c2c2c0c10245845041c41c0ca0005131251092080c0360318200b1142d000c01080703a003540c0c3d051a00302c0d01c800c0740b440107032001d018a681024a03840040380201e1440b0200c000b40c032903d00686d007101d2600740f0807070501c5400d10070080b50450850303503440d080c800525114020440b00c081c84 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 550494712 1250 550493462 550493467
    0x2070f03050325030902040e06063115080d020109020108180a05120c070e0103080301150309020d0308190515061c020703170108120a0f1b0303020a200606060708 71
    0x300f003034281064614290109655610040942c282445002c00340d4240a000b41240e05100340091039598580d41c0e901c545501f1f0030400c46540440d142060080c000120081c01802e00c80815040100154055905540310700301c998000d40c1c1c0305000701c4040e43d806031036840c62903c071300b5002c158248007040442200e210382d52408002500801c800f8511400a80046880d103500140c018203180c0d00e940282d41d40700f0003e00500100794110300f07ca045900021100ea1a440c081100342c0160043c5a800380d407051008095105040d04080583c0c8200e84442c031180703a2010314002441250001d0315803429000700c13000d68207120301b00301008044038000100860590508445191306903400b10b5011800a014a01451440300f00111006d0240124401a10440900b04600c080c05c0c022841001c08200d203401c007129038603004a00f5a0181d0f072030542c402400020508015005c0e6109150b60070024004810600300c29110602080d04d4a107520040d00322500d840e000c01c14582c00c110420350381403408 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 550495962 1250 550494712 550494751
    0x51309021e13020c03030f070c08070b07030e2d0304030609060e01141317090603101502031201150e030607110615011e050408120c1002070f030503 65
    0x344140069052406101d03010014480030520a810444009124141d40140004180448040140e0b548448203505166055440039000ca03900010803001420080b0000380d03c40c14010000504d61280d2111b0728240902e402404036155280d49580b1404003051b03250400f45800714400444900429043c81124109520f036184c0c030003120320791203007103a019075115102c00c0c10150a02a660b2003590301d004500d0145400032421ba1000040d1074000d007144240b403000201d03410305200380d64403e50042d0095860340741090052540348030a004080c8000400201c58a2691002085030080a02c00081005691820700d191030110810700c1c5203c2131003905415052592000c020f1030744070f0741103030755000b800e0a400000c29062410141110b043c00ca10b9100b00082645c20035940d04600c00070340035a41c02440411f4007140e942c000d0340c01c0b10045004842c03030908400c0203076015129501d40107058441c06814100341008034444c000009100d40c01c014000e502090290019607808440346e00c5a425131008e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 550497212 1250 550495962 550495969
    0x1050f0d0516091d0a0b0a02090109150e01090503060c1c06050402210714121f14010e19060c0c030c1511060103051e0114090f10060e0105130902 64
    0xc1d00502c0e5a01c0e0fa0341c0c1c0d1134441d280302210891202030342c00b014050a40050f101e0900c401002409000001e8000480e000d29901c142c007410003c16078040c1e228922000c2100062060080d0318050780007404602012070740b86404030341103000d4010003000c0752038a90320310b40c0319030084241020702c021555a0710002503036450fa40014022220740c01481b8200c541c00150320144100c000d800a010400d001e0f600c100c4040c00c140441d9a03a80001c510260942c1c0c910b141c0c5c40580240c00d210a81c0c5000c0140d000644200b10045076407024801d880d040c075280611030510945241c60398bd081603640396071808000c0c00f402070300d68242c00c500030b01200f000c003a101c0d2144c40000d1003540c420780d50040398280600750140d101541644051071000a0701a95145441d03143d9503110b2049510210016413501c0a60500258044006448600c20440341407402103101a2240402a140032090003040c441c190150f900b403060b64103031002412181002d0742040c0511104248001030216120313929141e00340580d9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 550498462 1250 550497212 550497253
    0x522030c050a0b0907060c1e021903050c0f04050609061c060e030a0e0609030607180f090b18070f140c2506030204030c03080c0a241401050f0d05 64
    0x74042c0c842c0f200e680c18801001c0f071411005510440c200028400400b00164100300c14403e413030302e200f00070484480680005003c80120b45d50300075004100e45030001c20082c01080100c0001c004441d940068003d070402e02003aa0b00440b40c090b8802d0b542c02c0054058a40610700c1358800385101c00020301001ea540d16001141c2e1209403244d0345500c04183e4159880c0d02601c1c06412480030340ba0751f820300c01864003084d6102c5021380810240803007080503289080d6050032450042000015490b06150780f940c000e0020700300d01d0480b50042c902d510355880d041c1d80f10000140187c48039a00c4a0100f01026002c950b46698500b101401c10004c00c84420380200c10880c030b5a000402c0d2003040a074921b241e0f44480480c1c3d05601c040103041c014081000400c00c00c80e001d40481c1e803c02c090507600d80c03040d801c45003001d1034600018542c1410400c2c442013480140050000c0c071030710300402c003c81d540040103690780a209114140d40401e00003ca43c1c2c0341c1c200a4403400800e8402c0e4215400409110584c04d1a00b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 550499712 1250 550498462 550498483
    0x6060e090604020a060504050916050903010218030c01170f0402180115020f0d14031e040c09050a090c0b0a0207090507020c0a0b030709031e02030303010306020714010522030c05 78
    0x41d4409420300c415841c00d01c0c002001442281005407401d4030707000101d11900380c0204008203006500403800c061030702402c212103c1c000c00070001c640d101008200031155000d65204c1c81c0c020321540c0110307181d0b035005000c103c0b0b1003100d80500c01115a0b4040f65280540c0300103000702d8020b141055000101042d42d09210f002c0d0002000c03400345034092000c002c0c5024100d2182e04015485034440010341c0390031010a82c41c1c416410b04041c0c2e6aa40c030160580010000504031070300c4010a0100400e000400c4802d0064800154050107162100c1c00d04100740c9803411000340c1200ca260108008079251940141650b240a00580d220103665031109003c0b1081283c40d14056004800016960b00c2c10745948006800e07010121419030804680050041e4070601005000380300b004d0220352140c040040c0710303103041c4c0c0c004c2c1146d0f0381c0e68403440c01e600030b034110807421145e50380702102400e12044180604c034030503007030800351141402140500c60480c20501c001a000e0040c00c0240d81d0100f0300a1040303c4c4034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 550500962 1250 550499712 550499731
    0x215030601030c0c0b01050d030e060d020309060112050318010309020406080f010b030307051c021015090c0503070e04050a140a0c09050a08030a050a0e04050703090302060c07110d06060e 82
    0x80303151400001d41a03800702070701d01c0c0401404003c0c081c001504002c1540c15a4019142650b010b1210f14040c2d03100083c23683c0a5921140c04104054007507880d40041d40b0800581e0252113003030b6600c5841c85108119804014101d400500260354a20944482488458030501d4042080c4282d9004142105d120741c01141254000c5580b03219800d10034000c01c0040c01c1c003503004603d0f2130850f840b1030b9107413070b044006041901e2040c01d425410034402c1080b00030200d00720004100d0001700b0200072a9042c114030940030a507040041c241100c074000c4064038822542500c41d400303615010802c01c001894010035180c440360f556081c0701c01d40041d041e8450f1141d20300f50310024040100c61005884d02e40d29500851003255000002c1c002c1620200940e0b8040c00c4070300b00300f43c0321400600262208020780c003000d41c11a15050800440c2507140d003040c51458025000e55506480700000d242d95403141e508003400b61010089890110f003010300b1141d00b0280034070000070f503c903140d54140c040000103884e135078030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 550502212 1250 550500962 550500967
    0x3308100b04030c0b0703140a170f04080306041d01060330050706091a07120e120703120e030f03040c080a0f030f02150a14010e06010507080a020106030215 68
    0x218401000414068880c80961a04051035541c840f2500b0196001c1c000580c1e07404242442094000c521704885058003600d10394640c844840010821011081c0074501601a0030200e109125216031050040360800481c038a541c0d80d4009004c0540f5464455a503081d0480c051036010300000c0c450000038500ca2141c422214481c501603004621428000399070101e40e6404032020550404100d44400d03610400c0070459030007600b011481c0342001c0a100300442e6190701005485030307010201600103000c050713007041101c000d080c0151f65038800a03012009080100030000c0824000c0824008d101030340c1c0d00c04900031035414016411504504c00b1040184000300901080100010708000a400807400905a00d141d0740c454030b800700490007014051050384904044070724424403108104400300030010b589420721b80355584c01059541c0c0b2000843c990707107001081c20303200d0008083c00340e80c05940381424490503843e0f4031104d50202195006540d6622000001a100d40d00070310000b400c118031803034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 550503462 1250 550502212 550502221
    0x9011e05190816060206190e030d051e091b0a03080a0504050a08030a2f0604120906020a0203211309090210030507090b0c010e0f0604120c0302073308 66
    0x43ca050581c20740a022030380101000e0001d658006801c0e9449026842c0000c509042040c07907100030a8041c0607241c41e0b000009450451401a4015030301401545209000300f40a03038070560030380c15059032110003170740144061046030300f40c5003500c8044c403000030181c1032600d40d2641d483c81c05034040e1700c100000c140007040420662401410200082200b14003551402c034843300028180c1e941402c0910440b004c4e02081c0c48458802030060b1840c0c49c81d60102c60460a050074922070003070403280c0410015a00072404508184080f5141c00c160b9400f80c010700300c1d000340b05011818000c00c15611070303008ca414081502110380c0141c42c3d6000705423405002031480c030366005100005d0a0301d80c2c11b005250401d01404401940314440c8002c440d5a203170300c5616044945c0c0c2c2c807405410f91a1481519100d41c4c0c885812191011421034002c0b0b1088144001c0b1a40600d41542d00114500019001d40c00600c000c00100820114580070909503000c18201c4000c02e00c8000c600510300c0c000d0a0002d8080000c10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 550504712 1250 550503462 550503479
    0xf020313120209100f05150702060a02151501020a0b04140a080a080106111f020904090602090f030c060d0f1805030d0606050f1605150108030a03110909011e0519 71
    0xc9800c404c14001d218907080c00e0040091911142d8070800f40a5121441c8294503070201d8019100c02a42c02003c0c1d80d59009040b40c02980e86030b18000210700c070b40c6800003043d03110030301c45941e020648068020b4007404c42903890358241a0802401601c445121110014440310180202010948509951503c501901c1e200402b103040503082002030108031401303031f0605000080c043c100f03c0c44249000c80070680b00b1000300c001c0d0045038805500329007081981802c00c1750076000341c0341106098a0001c4a010750744109542c0b1f81140341800e4101404020041a8640355001035060342c1074210003003002d01030081c002d1495aa060425591500003003038400c0034016901444009000f107150080c2404480c120070b940600c2010f090135011492403071042c0030800240540d00d500720060420040c10342e900d08a4070b0b1030b03503c00d4040303200180c079102c82a295000d5002c190399141401a22200d107683c280305044113480c24200f6100c0311101e80a50003c0e83e592445480da0f12110074603030100c04149480e910 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 550505962 1250 550504712 550504729
    0x270c0403050c01090302181801020c01020a11121b0a080a031a040606050412030923030f060f06040902060d0f0b01031d03030411062709010e090601060f0203131202 72
    0x2410051352007020805a600c4940080c0000c0c0c40c0120080d40340c403418910b40040c00c0c3d034003000e5915400402c08500c07240d0198050310000140e51600d42203500c00b444001c0e1035a0070b40c001041d05200921070040f031281c0700b00b040b0070449031980c00c031a59006191902c0000c0c0e00000b240c0000652a14001d0301d401000308090031110340300f03035003c0c0005410980c0281c07460144e406180d440c01c2d002030702d05080c18030800c4484014045030f186003803a451a80071407950052030908990107407241010b003540043c0300054145c40360103086101d03d02038441001300070141c07048050503640140c2c1440460f0f1800600d20580143c06062900007c0ca000c501c0000b500360b8605a00450741c80055280301e0082e40700210450b0761080e8060750604580c2d0900001a1042c0500111a5481205200320140102d001c0038007042d1041d048a4402070740c0e03603c103178000305072070300721400403040e0000801048410300840740303400c90032100c0c0181d030305048030b0400d02409038030302d0b0f1700042034041200303540015414049079 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 550507212 1250 550505962 550505983
    0x6060c060a0c1e0f03022a030a090e0c1909050907030905010f200306040e0d23272101052403070608040c050d03080f0604020414270c040305 62
    0xd014500c412043d10182200040e014210b00340b58000402d4004941501544404c05040d1400036810420f00b4044941e02d42100303440344041142c40202107080042230880c0e900c82c030042800580f81000d603d61000b40750300110008001d0040c4102c0202c0c2e10369030020046e00c07a1090b0344e8001654015030824030b094981c03407200740f5070051904904108900007075680061083c01d265840d41d6a03100c00009c40e0007499001d4540915008010400c50255403007114003102c27407100784c981d03140c0a0780110021f61a00c60321086292403100643d503040c1000404502509081008210322080c03800401d0704601007000c50700344015a55254200010800480740800814603540322007003005c00804003013a80c8005c0d41c040c04060201c1c8900040400201e61030500140c04064800c241c4038000d4a000307012030009607800364030b280340c0200103074032401e1030300c2035508880340304845000140e21a13040c0013203003010880c0024060700f4602002101c2004181a5002e1446c038521141e079a491420094100a01c0c01c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 550508462 1250 550507212 550507247
    0x42d09020d0e1005100b07110901061107144e010e01180212010b030102070308150d0c090f0e1b150708030c0a050712021c030219050306060c060a0c 65
    0x1c240000064800a170720b003600c940c10390341540d40c069824800c0c1103030707c1c0600d540d44c0182c0d4940049030b51584031004000c072101d520112080c0300d4480032a01440699809582d4001d11462600c0b110400d814604021000c1740074101e1540300b904020700e56084200c2c3c007186080003080303100804284800d2003942e286061580003004642e0440d0074880d5100300c8407101a01c50301a807c0c030042c00079403c0d0f22250030020010700855403840d00d031901401c074400c1243c0081e420101800031000c40d0408050048405500503078000a6a081030b240364010007860f41440034a81e07070f51364003940f24041000601d00b504a0b2040140ca0100d181c030801648140303840000300e400e4800e10940001078407000c01d4035000f040074500d03d07440b15071114007110305014208003d0300c16000e40013003944036500490707820440c60303400d440c507030310122031800a8080c2d11440c0c079004510903451901c2998688214041c1d030304818004c00346072030206070403906850103406484807414296030300581303001c16811040c0051541d0182 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 550509712 1250 550508462 550508471
    0x60d02130311031239071805150904080307142113110609061c060501080106021902040506010509150c01050604090b13060605040603050105040b0c042d09020d0e10 72
    0x2524140001c480003000b440110107007080c1d000e2690071400c003421002000d04c08983d81e0700e585481401da000354010024140500e4100071941d14219070321001580c200c0030308201000cbd05c4035501c401095100402c0d4000308028504400c2c40c088003000104802d146540e00139102e041000312141d400740000c0d00c20b200346030941c3c250400003030100c203d250b60a10100e500b03d40715140c400100f211440344000641c0c2100c0011030501101001e07600203400c2c0c41d02170381c2c0e120650383c0320301302a40e0b140c1c071450042c00f000034002c040f18014034180e00071690081041c0b418500388803250002c91441ca091130a10400441e0119080914180034441d4640c00301e01101c00f401101e126032180c0c0c030300c0300024003200c0344545009119002d02c90190001401058042d004200301503a9042080c000c25043d035040f104084440d020a2048420b6403d0b038054bd41070008090000e0107000c0740441c11015004841c80b0880c4450300003070160010b101402042c40781c024049519005010154140742446490907045441c0c07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 550510962 1250 550509712 550509727
    0xc18050901050d120905060c1f1a0f0f12030301080f0705060a0f0905030f07060930110d0f03110607080a0c090506040801150b0c0606060d021303110312 67
    0xa08101c2c8020f2034000c0030314244d03802c00748400ca45d281c1d1503410090300010300007000c421032040010240c110002c031040e4005d80a00a142e400c040d80cad188025103003400d41074035030511240b07084a0480301c0382070014145025841c2c0361001c2110882c1c81d1401404540000c0010010440280000c04850419030054085a42040e0014a1a0151804610402c204503440c84801c6000380801c0c8084c0c41e0040495099020408055a492140d40601e01c0043c44941e800101c1ca030982d100364101248100c0449040c01c03c941d40c03180c903142d040d003050f5000307000011240c9480c0c403440007070764449004000c800420700160030060a80c81c08c1c0441c1c00400c0d0300807030400280a901c4042d154105600b09030102e0812218001122070100710380000e54041d200080028900105522041c130344a5192481c01c0307031035560b40308c002c0e00b401298032020082d00181c0019495240540041c14100c0020701c0c01410204118101203151040380c0040340c44800d1045296402c0c60100494503044000c20302140c40d0522 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 550512212 1250 550510962 550510969
    0xe07020f031c14010e01060207050406050315040f06020f0306040c0503070c02040b03150c0a020106060507050604080901030e01020d05400f05060f04061535010c1805090105 76
    0x8103002c040d01514401400008042c0a0304045046900407694026550b11010b81c2d4820010a00c43c0c1405072180da500004c650400c0e008400c04c540c4014054001640141c00311080c03240020011140c0004078080071000640910103803500850201c946071301c9240a07424041100d0745201a10f0900200348100f01c540b507400391001e100d0540c1075501003010300890000c0b914003007000d0705036256034000c9030420800f115582c01034202400305600900829036035010070749a40c403a100c005805038206400040104d501c00b00140309840043c54005400c120806005003240c102c5420001c80346d46a03000c1c003080e000301225003c0070052001909160303415004d040100240300f844e01201400026007000103124000031041441500705003038503210b14010080c0304816400712021202070b49000d845041301080c80010b1000d5070100ca02d0403100034200d002015082c2c4504100c84126a0301113030b2603505c50000c0c080c00240c4861900d5808091352040300040646c02160401c6000309801c2d001000b80f44d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 550513462 1250 550512212 550512217
    0x11070909021819091e060f0b0109180203101502061e13030e0f0d050d11061605031015030b04050a09210203040503061003030f020f03090135010e07020f03 68
    0x2000310300c001344600080c500811400c4000c2600c0b643d0344056644a420710039541c2040140c80e01e9440f04002142042c40191001c940500603860000b0804000002c138140c20341c000d40e000401c500c2c3c40002180e440300c940744455500900301e401a0000000d1022140b0040301034100c440581c00c000c0140d01e01201e821100240c0c10202508202551076002d68a8880344041e02c410800070345010014405070a0981c3d44812030910a4001074180c07602100840c40401c1d032600419034800102507851070880304642d0b80c1c0016014581809051000055401000181c180d0000300340e100070445400c2c5a04100441700e00501ca081000c0c1440103940c0040c541a4280948030a07400701168056400c480c202d103580030700c1d008503030540700320802d21402c10300040d400030441e44039585281c01d010b440b00c0101d84070400c0b00c04900b5542c5c8140166a10f5600581454030711175030f50041c00c880742c11401840301c900c0280c0c0220000a10740c03a40188101003800b41400d51050a03400140021603c4404032036692 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 550514712 1250 550513462 550513501
    0xe010309080405040509070302010909020a080406050411120d030b01050f09064603020702180a0e161508011401031505090405100e0f06040b07110709090218 69
    0x56641a60340d040110301c205440103840c000d8010005490007010036940d950303aa020981c0401d20300040015241c00f14001c0b50004c2406a0360140c03662215030307501c0007401028208440c91401c1c950b400c9403580b00ca00030700c1c2d0140b860400502160040c18000340884642c14030745410803d040180254102c008821666041000d0b034a4a540d4800045460070030800d4246038020781e92946032030700180510080404840240e03075444052202c401030254103d1058850003508150704400a03001d814104040c540c0c0413046e40030110305944c1400e80ca600303004080341c0b00030700c035419000c0074000700038540501640e68007542010a9194100a03580c26210f0681e503880307041513140c00328401400034048048004040c003622040d450309241c68041c0c0c540081c6100387c8c50307140c50f000701e1800c2d04100241e0841e50250240c0900b910351920303103a60144100084c420028804070303401158480100304481002424590000039802c422071040118030400280b041c0290350610381485002c0328408a041c0d4007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 550515962 1250 550514712 550514717
    0x1b0616080c0111070602030a0b04021c0c1b05070e060a0e0a0c0309020a0e1902040f03080d020427061508070507020d02060d090b06030102160f170a091401020a030e01 73
    0x5441501e95918003415210b4001d44445601080d00c20401c4904e8000d10b028054004051004030392207030a0204130f008003280c81e010b141080c0c522140c1c804065000420f9040307d071501221000f0fa10186242035400f061040ba01d5074401e02c4100800c49040010300c2e0055000c98007280c4440c642540383c980c0c00809000301c5450f650b02d80c3c418400c940268007450300541c1c058004010340e036452141100c0c00c601107800c6000b0303102c0743c0349111400d11984212800d45102140001402d415602c54481c903801001e200140564200f0000c281050700c405030314030020821000e41c00c6a002c900c80e0f001542e1155004603007809409454803045900540080d82c0401c01c0c1c82c0c01510344c0d40c0d90000866840c03d501010f50007401c00251703030304806001c0e08001d0131306019084400d0b5035280c103024907080348510402c200394140c0013003514000441100f4030b41c01880c0290038060800d0b5440d205440f056206000c41004076048010402c181c0354640b070304021480c02400900540d41107903c02170b2078042c030325011504 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 550517212 1250 550515962 550515967
    0x11a180705070b070e10020d02030a030c03060f0b040302010f0903052e1e15050f090c0f120420010c0318080a0f170f04090b0f121b061608 61
    0x40541c4100269440240c00c58070381c0480b41040b44001d026004014a12401400115140c0103040c3c000205d861041c0000d600851500d099001e00700c008000f031030100c40401d40c890400007290402a440744001d04010f05c10385941740e01d14400540303d4074902d94000140082214104003240d008a80c0141c9a40380e0400c608006030703441d0b8014001d800044c90b4880707251401d0015100841425440550400101e204200030145002425501d00c12441402d40c403401440201c03a00e400c1030201036802651809005081406032090700b8040d8000780400b6850030350309410032041c082403220f0a09000a404440b0544450300c07030001303090050910b005410311445a1502d04186101840e03000148100403e13614801070301c0c03030220901c0340303000400d860400320180d0800717401c1c4c0040100c5030811455643c55150600c2c0c0111003014140d402d1815500002c0940005842e45440c0708180a5080340c8002d800b403880c1403101c2014400c00010303600c1c01800706118040044411056401c0c2c61600043c1054 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 550518462 1250 550517212 550517221
    0x20a02012403082a010501031506080304050d08040f1409060402070b04030311090a0f051005030f0a0b06041a07050f0706020d030506041803050d0507030504080a18030c120302011a18 80
    0x3130b1100004980502da9103103010380c4007038841e030650026040c0c0303204120f8680d0b040c050400b10800c2c1c4103d0300034609990000c0000300b1192a2011a010039070380f041181500b029507a00c0c408508080d140e00401440780e0303070f40c400d090b035160840d980c0794061000c9070218103080c21511020100c580c000c1001f42495503d50351800b82500120944001c60001072810090f0354540101014032249845041e024203248800241c0c2c040c000c01c2924454014a080360303030581c0e5040301900203414480465900000208404100c0041e801c40c0200300e0031920f40c01968a080c0c41c5032403031038440c2200082446070070049050208650214032200a560507140116642d1070350b01c0080d00405096540c2000081c100104008040d0480301400e00d200000710208515a503a10099059820488004088a8041040d8001c1c107008060043d2141c0998100b00310041d180c0d942d4404850721600503c040d00240281c010403da8240181c140c241d00c400501d480a42140000c204009020101100d00000041c00903 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 550519712 1250 550518462 550518487
    0x5070305031003140a06050906060906061e040609050f0102010c02060a0f0f0513030207091401030303020a111002180d20031f0b120a050637020a0201240308 69
    0xb01c000e076070010700e140410207142901300ea0300d94140300e04130751031030418001075804c0303101050261103158094840030003a0b44480c10401c1e2540401000790f90405013400c100c11200c05000a00050046515000d80c058140810040e04040c03140e0064110381c10460301c4c1c0001613004c180650006204100400e960102e0f80402e0040c2003d0382100d900030340f401d01080003886040282c103c00342d001c0d07000d0b00c2c45d0316114801041580c442c6042e4400c1c0c140351100400000c0c0c0f29074010304110650745003014800c0180c1e288141060000001d150410742c0101e10752000500e004aa4080135104a50380e00d40f400255642a070004448131402808000c07100b10307100103032030501041c8803c40d076003040c0000410703c51010b03200600c00340000a004942c0d001091040711400141905010307001402022640d442c208049410041c01448040302c610910140b2a118030400300c509501480020158488548100003400c6541c2141441c1c0768a0032410b103141000e0b0000c408000f070325000050716507200e5410884 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 550520962 1250 550519712 550519741
    0x70f201507140d0c14030124051b210c07090b0103060803070f050606091e061909020304060506010801030c060c0201020109081b1209100305061311120105040c0507030503 75
    0x5202014006043d9180039940d51146201c0042c9850f510044110701c58014400d010900136201c0312480014071f603031641c0100000400f4116540341640ca001909600d0100b240d011200b950341c5503202c10780c5013441e10040d070b00e02800c1406100c0e00e40c0c104015106425958149441803000ca540da0b81810740741a40301c1e42081015050309000c49540700410b00d0700401c1c07081200416200741c02000701003030040c41c0c00c4201a024018201b9480081c07130100044614400029200750b52015400801116140589007103900405040100585a2500d414014151840140140e04002a4500500001d02c0582246042d40c81c18a41440e0740c02a507c01130780140f26955000c2e1015001240c030715000c2034002c1800425016600a8440442d0400d07100d0700280100c050712a48460b00302c0d0070f000014846c0d80020341c441c00042020361415040c1d903482c2c1c210380d80402076000100002030210107128001c4505401004160340c1088000030b1504d0007445406007220003000c0002c00000318150b003240164 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 550522212 1250 550520962 550520987
    0xe030d08040c0e180f03030402090105061b0d050705070f030c0b0d060503010219030b01030903050d090204020d0f060e070905090c1b0706090f060e060d09050a050105070f201507 78
    0xd400065040040110446082c1302d081080c3d5881441c0d40c0d41031140000c030030f490007140d000c0c1401d03569909200800a803a0021b010040b00f001c803080300d151810310b041040c0034070b80355039803203484c0e44088030309149050a190f50030903410020542d01c104002204440d151013214601c50066881d07103484818413020303005a070700041d8103600114040800c031144101141690840c1d80f0f08200c811141c40054080e12058180500810011700181d944e142440c1c000c808a50700c024130051811008480f040d00311030040d41507484039a5100e80520203600980f9400381c00c03400d00e040001c155860040011490b15009215503048000416181107049001c90612785085200090b944c400f5100c1c04010180c017202e100354111081031280010341e450203401c038800d000c0000b030b12240ca41280703820882c0c041c4c040d40741c00b203c1620400b8107906c003207007003845528021102983c950305800c0b00f481c0f0040c081c03902c0001e8006042c62511030099034940c00110240062028080702640d07550f900c0055503031805228 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 550523462 1250 550522212 550522229
    0x40602090a090c050d0608060f010b09010512010f030b06060c06040f020f0d060c02010b0402070503042d0305060103020306160203090409141506041803021203100f03050d020d0e030d08040c 83
    0x2d0843c10303140e400038080c0201840e1443e04004041c1e0b61030030296940c00956110030203101110040c440c84880400814145030181081c0385010b0700415402031400302644040c0701c520070b541d024001c010300811007541000e8100c60301d60174014940d804030340302c07000944000c2402d4a0340c0100301c11034442000560b40400d0003003014250080702d0900300042c000c03810424005520384125003281d40f07007a109513425644c200000318201402c001c0000c3d420b0f00320350208820421821100000c0c2c6c815201448091841036028214039451481810b14080c1c002d0003115200482c6071408111542c00400e645200308100c0340415844054200040e20402d01c404c8041103006030400c144900b945140c43e10302034141564204108040340c2c200d00b08084a900d070040050300202c1038184081024800f41d60082540c20150440c1543c130f0f08109a641d000381d06c11a410740014a0001203142c05220081910625081c241c02c2c5d00b44e10340001c0e1f00c1c2d800319404003007030261400224050142e00300c01d540240a188 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 550524712 1250 550523462 550523471
    0x310050c07020f01080907180204090923010623010c14010603141c0807181202210d1119051513120f0215010b130504090209040602090a09 61
    0x21000564207074000c1405900a0203c01c28071001c0f540b1507545a0f22694000015115060504486039510701c140150401c40035002e100110311030045208404e5051302c600da884982026103601720003154140c071100304051340352603c00c00400d0301850700002001480c1c4c0000080210321401696292494000a4000c080c0c030120070301c02e420b0546c0700800b600d010b1414000c01201d0300c810543d858450704c18582c000d100003c11900114024640d094200c550b90402d4200a400007102d003414856552010b47d582c00200f1607030080d8105000442c20f104103510480c1c8030001a8444a50703034120f100146420004207650340c0400000520003011544c0c09281621061190f0f42025542e42a00d4214110003c065a011800c0950144886403a09500034445820032060b40400e50340480d410300e4410642c0160021303001d1011200006502030314103a803646448160240c0cc610040c5250307004540517603d0080302c0c0700035a490242c0d050b4059030041000d03070313500b06120105004408640c0b100f01e009041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 550525962 1250 550524712 550524721
    0x1207030501051503041a090f0d0201090606060309050c100c0b0a06090c0f17071e0f090515030402040f0605090f041b0e1501140f04090e0f07060e031005 67
    0x2640080341200c1d001c88030149030341d9042c6a81c0000c2c0c0301c2650b005102083c1091a5409503a003031000f00d070700203001010f4842c00850003000b641000009150078006035940c8400c14200040f0f40b1403040580500d140400105050b5600c2d1340d9030300b41c100c500610500d080da40c260407091151001703561041c2c2c415141d0b8024244140f0150181c2114020507010906140826200c588280042003144c200d81d035604c00010048050113900c414040c0c0100d040090a0284004640c2c900c08079845000b020b61f23030700d001164400801419640e0b5604420310a41d402658914901c0f00c1c602907a4005804840010f41005110b4140d0000c0050341d00503078001101c82c013000080f011a070344d11031003a0301035450b400030400791114103024480f40d8000c0ba002d81d200c00001c0342c030302a200c0880070071912042c10905d1b802704114800e18081c5e0040f9041c8181000d000400740520712180c041c070b4005a4400c801011a030205941c090303103e00e51030050704208030000c100142c060340d0802c41d04845164402c005c100a040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 550527212 1250 550525962 550525967
    0x31a030d05180301020f16021f0e01140f1e130b040801050f04021305151903020310020403050303061203040902040905071d060414040b10020c15041208090102031207 73
    0x800c040341003000c00d00b1079031403841e41818000c4400b91070360f4003011072920020520021420f01c900c1e0b0141d07004040c241515001d41846402c002e800115504d80340508800d1400050110359a080c00b8100400284034501c03c1c0c04215007a2121640071440101a15407030040e42280c500031a40910084240818009266510000200f040c1c8507620000d101541d19a64007085c40501070350002c0d0080003403036800c01d80d401144c3c0311981100003561144034116944000840981c60b03a0030032440d10424540400c2149020440070382001d602c08010b50510b860f60325400c2c0c8070300005107158042e407418050707004100d1051041724003808008004544858039802c004004103c101c0300b50010071140702c600800249000310703000d02c1c240000c003042d15007403e00203a02144218000d0264020740c94071400ca040e0f41d18811035485a50300d40e802081080100c40401c1020801140c545503000c20402c420300c5240c1000e9000390880340c01400c840d58640c0c0c441b004034a1032240740c091401c09034040742030211031603 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 550528462 1250 550527212 550527217
    0x31a1804050f0106030203030405011b02040e06091506091b07050d09060f020129010306081902010e010f020c010807111f150b07060f060b040e0f131101031a030d05 72
    0x40c000d908951124410071002c508a07281d902010398541c0c4180020020396204410301c1080c00c0c0c1c0e425000c18000190b0f4007160030740b0030031203901840703130081001c200d0503800810003000c2c2d00c1060001d03100305051410105074103402c00f506d24034501803d07272200304c1201c800c0720890344400d51080844413040f46200000f0124120390081d0400203081002044005205020f040b0741e15600085411050b000c6020304081e24041c0d07054641071507158800005c40751018001d00a06d200320110304507903d00c16200040c8400c520310201030611040355640c001d21540080c010100c0c45007030815016a40360000d05a80078000180c10f150b140c0b181082e095030a20680864000c20001444103000c3c442c0e0300c0d0f9600c00034000b0307030180c1c1202a8007441002c0100725590401940d401c52818000b68142d2a040c101c01e1561240d0032804051281d01c1c00d101d05440d0f00c0c820617620a0030501240391080703c0703690b03c50303030b44142613902410180c85020b007006420b401000b8074002503001b03044400000c50403802400380e4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 550529712 1250 550528462 550528471
    0x408060a020d110304030203180111030a120617031b01151502120408120d0207020402032e2706090501080706090f150518030a0602120601030e0c01031a18 68
    0x10780c00c1912410510340f00700c0c00e0b28007899040e005142010a005104041d0740d0034001014108150502d00080d000030031320040104103402d6990404402e40b00c00c0440130b5032000e502181842d1244824214418004401e407460f40b001054040300254980d84502c0c05414039005d956213107000d51000140c555680032040301c0e1079a83d5001d54444500c0d203040c11140340030f544038001c581c0d000101c1550f01490320340000c04002c1d64241c001801d0100e0f540124049801c100c0c1e21144c031200404402c44850828003075458908171400c0c1c1c420300b05003401d40c18840c0e800c000c0c800010144080e4000303c2c40d440c903504030394043c0101850801996940b002c07030710780d101031510074800030a1103054042926500e00e95400241c40e000000700072003031019a0121000d50180c0b5805510054021444000399020700c075440c880307401103101585038130505041044031400070742201c0c141031401d488a404e2017000f060b00d1640450900300080e02c4103000948480280780246031790351040c40c0014908201600d240c81e903018 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 550530962 1250 550529712 550529737
    0x1a090102060f060a1203020f0609010501230f040504030c14280b01060c1b0803030415090c05011407020d120f021f110c010218091501050301090e030408060a02 70
    0x35100e04600e02e42c4000141c541a410814048042c0316540340c0b0000c21142511910407078a540002e2000c40d03040c498192072102e00c0740d448200402c112205031038003000180001c0301c2115101c07410f20009802d1002c0c5051103004940700c04c0090b082c540540840c0c0c01e46504400e00c040310344412400144c030340003400540c176a03030145040a05008004050600c82c0d460384041c041d52264240402901c0b611415032049a200708101000204081441d1003070000300059401942c480c10285000c4c0e0088200e0b41202900c0f070701d401420306c0440c82850300041100c10a080020078400d0340b0021820501c070322540690401c000303504c4041005200170000364020380c0e680e02c08e450307401c02c80d0040b0380310501000f01c41da098000d0b0701901030541c8203a006460751542c20012910b0180c0d44143d00b42a138019040084000000c031030540c0642c14101ca680e40e01c5244840008140117803000040d01500043c068003003400c1d030740c4141c0c4405101c100211000742c28402c08a410358034114010340007941c01010403640 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 550532212 1250 550530962 550530973
    0x120605011e030b010320210c01080906070c1401020f0d0b060c0304030602030c070f032309032505031609230c0307090302130626150903041a090102 65
    0xc20182041c09000c2d83e40c80070700802c90f6485c0da1100c044030949241c9015089804001080103540d8510524403440e007034480e00c0f5080fa21100b030980c100041a1141410b02510070100406074078041041035011307c0720b04101c9003a034114106000c1d0703603c3c070680d9450a50300c0014102071707441c0c011014003000903001c9810302c1030400d810280200b41c00703004400c030101d034000c1c0f0040c070003c0c0854010390307072003030507e0107035814100d05031038100c247d0140c184150080340c60368144c01200514106482e146041000700f8070316128007a00400e0340d1301d50888901d070200102c800381c0e2401d401d000884c0c2008000040c00c48050041c42078003002e500343d881c4218085185002c01906c44541241822890071f41c10301c115400a40e6440c54841950740010034030400c001d002500800181c0e02c00d81a00d54454076050009210390516201144c41070011102c00070002c02c13840c4240d8a010005070031807000306214490541511240540c1d4a03500441c0c014107020072100d402c0b400702500c0b41e4041d01c09070b0026401c070303013 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 550533462 1250 550532212 550532249
    0x90b0906030d050306150906031305060a050f01140301060308031f090504030516020414090102031e0c0f07150c21020a2003041e050f0105030106020607030b040612060501 75
    0x580e0b80d699074081d1400b241c8144002407051030a0144443c1d40503002c0d0000c1d15100c3e07140300046886e801100c00480702c0d0600c501d01d030203000d01007284950288a1300707001c00c000c1c00c084550ba80414014821a04d1028404060fa8402e807000c0d04420300840c0d000d20b032240c807801c0c8820b81805510300c038443e003400c2007403102001510480e01d00625005c0c54050700d0701c41c600300e1140400e00f40030000c3c40e401d81e009074880c800c01e0308041c00441e02900c16101413000507240d0a01d440c50054060322000b007800380d25035050a100026a402048800c400301c0e802010b60b403481c00d0700d0f1450060034218110300f03401b850060383c800015008040e5945403401400032102e03124034034141c0022405110310300000140340b19507966400c50881980503046605100b10703410035a40d00071004122040116541450840403005c002c0c3e4180000240760002003406c015041d9814464029035a510050000081544580c0c0800c0c49407919404030002d400078001c1c9118107459800c121300940420311489107001200700d402c9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 550534712 1250 550533462 550533469
    0x3011202150a0e091b0304050105040c0807030b010b0309010b0a0e1b360a03060b0411030f13020f09070f0206071d090a1113031101030209060703200106090b0906 71
    0x1c8403002920389618010141d0f4100303010603030700002d204551001040d69400843c4131007001640c4114400c10010900340380920b010300030f06445901c2a070750340d03104000c144001010b83c900701e41034035125100141c59030b6440c0059400761003d01102c94018482c902c01240318284020304900c9420f661508002c00076810011819074402c1d40030a9204261000b4080b011155024414001c843d848440d0f9181d894a1030004c0d0758420198405c41e0113542d5081d00c04942d00306405201001612282d004d411490888114140d408004202522010036a69048115030b15070440c0d02d05c042003e84000424600310340c028029104805158000d4802c0d00000f902d42403180342c1200c0070410602440102c180c0500030700c40d4044c4054426584a5150401c568035251a0380240910300c92099501c0700b031601c0c5003424015941c21241c0e03a4105801046100d90320b03203404003200c480503070500d003032000c55008400c642c0541c00b0b0440312855a500733105001078000714507004402581000c88081446031960000c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 550535962 1250 550534712 550534717
    0x20d0204030602070323091e03100f0902180106050313050f0303010e0a1b1209030219061401060323042a090c0509030a030806011e020105100504150302060a140301120215 75
    0xc50340040c0f809039550301048d01b248181d420040140c12503c12000c148240b0742560315101c011901c45655512000551402414910a42a1842101100d035061010080c05440700034000c46480d8840c248000130408100318070b0701201d0307100b8182c0e6201c0d40c681c07107000410f600a40780a07606d0b50400742c007038081010041e15a441801a03484031080c42c01d00c2c0603e4400307000c00d0030040d400c0d8020506041111818008082d00c072038401d0704005070103840d43c41015400e18068100000301860590369100f030413054501c608622003006098140c95503149403001c00301c1c08500c4010000840c40e40081c025080c100440301c1171b40c4800d40103102c0d100c0015012103550040803a0994507910505030400482c1c054242907400800c107141c08070450540071500e40c1c00809046c22000180c1d5036504015680d5015603840e405410121001d000300700440c680d400c51003006000192045d100060203a01c164029000100f01c111901d284684030340c0c0d501c1c40c4100816041c042a030007808900f03c0354540f140d800e003c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 550537212 1250 550535962 550535977
    0x1503080c01051009021c0b0d14031207020d0203090d0c1203030504060f0e120a03090b0403080a05070503060d02120c1201090515100e041a0f16050f0d020d0204030602070323 76
    0x140c005a50350b04450001404e100544603411034048d15100001ca45079144450916041da001503a644150101f600d0f101d4400410071070131504003401210b01141d0100440f003170803404461641a00c1c65904100c40c0c49403036a80100403850499004200f01038264000314401c1703025201c00c00010044c551040b0694415640d4107184d500010800000101d00e00d010b03104169241c40e0000348010b46030354003d40d0303600a803001c1d0b0204c0d4040d0308210b040519405015400400c0d850305500350700704000810340c0d446607030710000e01c20010028880c08080341000707a1180c1400061110220019902c1c14900070558032100340c0d07480c01030081a60100081014203802100110300e40e4000c03514001010400b00b00280c007c90352030352140c015096075000040c0365030003088105042d80d203031305007a55500000b460680e964000d0140c24040740020820540a03110005250840581d0b144c140c152000024411368000401c110301c003145120030300d603002c0d6150f140609224030488914140c0c000320b41c528081d590 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 550538462 1250 550537212 550537237
    0x311220e070504030204020c0c060714070f0b0906031e240d030c02061e0a0906021606080106030b1306030501090201020607030e0705010c110d0302060627010501031503080c0105100902 81
    0xf20820043c189503008201c40001c050030380b80034100240000b5059817000e6416900024641c11840f10b40905000840083c01a00040408036290020141003801803005881c032402002c4000340c1403140b11b0b8082e00d011650501501d40b00d16200703504000c0e051218082080c44680040c6180c800e0800b190001c0f5400d4141d00e601c140c0f21101d43c208a21a4408000d00182c00503c065418084c03e00901901d208426900e13400180350406400a1401d100c2030340e8001000c0740b0700810400244c0207486c007415507059180118480d003180700803071500c24540303204241240c9030000020610106510404c032492007642500d9883c1c9039020110182d503441346003244140c0002c0302c01c1280e0340c0502203800c41d0900c0707200c00d0212544d404000505c840840b04082e00507801200070081c0f6440c0c1248440c14004251860180b4101010000245500c05026181c1815030b00c2c1c0d6520001c0c0d940f014040021944030102c15642c401c11108180071704400c0d554020070030b401c6a00424610350300d0080e00c00b40c06000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 550539568 1106 550538462 550538467
    0xc0210020109030831052113120303060306050f0106020c04020f12061804240e1b0109050301020403051c03020a0c0f02010311220e0705 60
    0x6081400841e494010b0000000f900001d081c0d420560406040d0400d81408211400d0000c1d460710410a401d0508802c00400c100081c02000c213000d007001d86490f0255011841400f40a020340518030781c54010401d010b43c80b0b2000d050740000e40a45400300384580e40c1c1e100c0104403882038401c141e0503c1c1020041c00041e40410001c1012401902d04500c0e002091201030050f0041c507180002e021585d10101d44142d6500e96002101e01c0c00d0745180e103141c1014a450380702c4a15140240701003c208580400d000e41041c81035800001d806005402100741840d00807908c00c0e4200c581c0c0f03062106100c800310340c0340c80910141c0060741c400c000410001440d4040e2454480400150104160040080500056006602d5904558440780b0641008041d100503005407000b01803904030050041034000e8111011826071f030310400c0d2010700082050b1540603031601080308840c0e1a003c24400c = true := by decide +kernel

theorem cover : BRFrame.Cov 550359712 550539568 := by
  have h0 := BRFrame.cov_init 550359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 550359712 ≤ n) (h2 : n < 550539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
