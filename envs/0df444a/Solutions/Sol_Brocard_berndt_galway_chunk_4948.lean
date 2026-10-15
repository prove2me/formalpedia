-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4948
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:15:08.894019+00:00
-- url     : https://prove2.me/submissions/a47e3d51-a7f1-46c2-acca-1fcdd97decff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 889748201 ≤ n < 889928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 889749451 1250 889748201 889748231
    0xd0f0e07090c0201050105030604080c1204060207090b03370b01030602030414120403121e0f08091605060a0e13060e06090c03160909090305120a02032413 68
    0x4911468201c14501018000d41038818080c00d8181c8a01400900c01a1510b07501c011841c1d010340001c07070b00350180d501900c41e01854580184010461540103000c0c2500b003600080880c1d00f2480014403d60055440441e42c0c02140c8056900c0c1c50310b100ca000151800c00802d40025400d10350040ca070510500021040000690195004500503105032006481341d402041c0d40d01460179040d604e400d0217100800000d1007619085a010601e840c01c0c41c0e6600f0040b803030307200c40656201c0103000b03d51000300d807109080e80030100d02c1d407041900340104004000302c28010301810302070191902401001901241a5000d210800705044026008460340281100302400034000703400b1380118400c009021403402e1030440700340c501914004003624a1078681504205030008510508401c1c03205503040000c0b0385086100d0318020034000c0c1c0703905030344035940c030602181050000c0c01e41001502c14424000c4000b00e03c2d400400d1075106d681c02e481040c00250014100115902009900c141008203000f00301d01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 889750701 1250 889749451 889749463
    0x41518030308070c41030406091202010e1c060f0c0e011d0a121109160e0a030803090706080609040f030c050a061d0c010807021b010e060c070f090209090403050d0f0e 73
    0x101c00c8181c440780e041c5c03140c00e5880307110b280b10b8000000c44414040c0320840111410b032042c00d00c141080f1021400e0200421450310302d03a80006084903091300070409003c02401059101456a0300400406559007000351030304860802c42410003001d20150300c008108000c81e00046200100003e1896585008071084d0b442c030348c1c0d030460b18000d10701c1220500d82004484c0d207000303031050900314401c5620004c04480b40f2601813225544818403950000100c1d0800005502540500c0043c142c1300b4200351020300203040c0a807503540100d02341001c00010443c03601503210041c2d41858401d18030015814100c0c0707041c040700c402070541440d200120100040d1803110142100c4e190058503034042c41600151407a10b81103c074400507800c00445101410b400003141c0482c50341c14140a030820281030080b444507042181c3c0c49186070700c0100141300112080d040c94004105004041d80340c1041070b404074401e103c0107000103061020224904550300d8150f0041c400d0b54400c0e0408000c00c0d0420300045550705 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 889751951 1250 889750701 889750793
    0xf0309060608160e04030c17130924380f2808270102340804150306150909050703061a03040215041518030308070c 51
    0x1c0c40d1940020f00c0307100130a402c2e2045070181c490b028200951303103807111011090200303010f4416042040340542ea006410000151100140000320884600c0c00040c01c0030143c1709441400740080310422002004084518124205240350600e10a00c1841442040c020900d11a641007010a16102d4147c1c0703407010f00007603a0300c400140003040100841c0c03d400d0301404044000180c80310006030704480a0425454200030240190b85404401d680407422604650b0388000760b41231007800040000c0070581c00341d44000b400035240d510311107669110580c0d44101d11810041c0540c40494101d0700c0c0c0a507000c0c90042070103061504d0056034000b00140286034600620070503520b0f24022603080c40c072900c280030a88001028440d08404810740805003500003c20880c0d01a6020103401001001c50002e8030003811a18824914840c00c403402901c0d500d0500e0000d0010460381004102080d0301804042c0c006401c3c0c108014030031100d00340748159992707480d01d092070072406600141500b03c5411003030b0114 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 889753201 1250 889751951 889751983
    0x1020910081006031404141213050405010f08031b1608210a09090b0411070b04050601080309100f200d110a0f0b182a19060f0309060608 60
    0x90345442054045802403245c0080c0c00c0c4005000800107002c010350345540212040494041c0442940000c0003641316025940104145030800c00090400b4080c0c01d02620107000700c11603050800f0902e42e034070b002d144800340030102c5201d4142c0f481d080a004a4100f1a0081c07003220b2000e888180d4581c3d644404028821007006010345446541c0c0c030041910207101d419a601c1e50400d1928151f04050282d003c1281e03405683c2c2d07145a065440300c0ba000f020000d102d070f0341d04072141c40d207418060700b40b88059104100315042003103424069030701c146800fa8440c0060804207184c4070603440488000301540d2000044001000d200385c420280000d03800004841d40c2d0300c0000310300702d03016280d48804043d8001004804407080207030004a003a05401c0d440a240b5110241c454220020b03d450a103416480b00c3c80c031120039511109000301800510101d040a80d109a21051995100d5070310791154481d1004012404900054591103a042801043e4018205001c02501e07410202e880f0b1214001c40162 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 889754451 1250 889753201 889753231
    0x30f160806010207050105210702010b01080912070f060209040e0f1e030f030c0708040b0d0b010824120102030f100f0305030a0c080c1f0506040207020604120201020102091008 77
    0x94610800e1141e210300410b034043c100b041d01d40801035450b5040a1065080f51a10102000e1041200a42d980c4a105503500200d5820318140c009000200050070324007240c0c02942410352003007807100886034581c6d445941c04012400c2c130308000009019000001e80d10a0920a0b0b154442d00c0011310700041c05010010788044680003411154802041071100d0300c19001400692003502c01c281c060361748120261490b0303140522079aa0240035502907000070b011901c01040c0310f82c4c041c141b8814214106420b0030903d009046c1042d5101103045040c4c0f000e030000c615541c1200203030b1a045070120007881103074025901c07030801e206100704481080311400c49101289100162518147c031004044a4015024500c0c0895003002212000700200b82642c81200030400c0c00c160560400102c0c0c40001c464074a00002c2480e0150300702a02e20207801d4912440c014421a00580e0344c0344202e50898a03004406003914010344010307400fa00420079540d80c0600b10480740d094050300104080c0c42095a10310800b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 889755701 1250 889754451 889754491
    0x50d18140d0e0d022202180103020315040903020c1c1203020306010c1b15021b01030213060e13060e090d0201050708060d05120310050a05060c03031b040803030f 71
    0x1544403035210506000030500c0c000b01c0ca042c14a004464201030014001103a00c20129420003e5a14003a0780e0140c180e43c00140b03002d080c02e0441c0c00309441103003460194507504000c55144002d042c50602d03a0300c6140d4030708072002018020400811080c030003502a40c7e0324021a0314200c011800040c0650b4600f00002030300092512034422244940c41c143c4600c150203030305d91141111828403501c2c1d60000b002c482004140f00405298142c450402c80d4001e000c03903282035504104170300c1740d15940b905060041c00f8080c41030403075424990a8485c103261a0404001050005001c03003120b0040741603081c81c00344003048920070180c420384100a071804880b4000001c520032400c96001b21074980000d0350361b0740030881d01c0c80c01141c8080322602540885440b401030302043c4001380d01c151080303004170a661000300000d05101200400a100403034225017801420046140c507440010560072400381031014032001140440103403006040b03444100e94403131400b100140079800050303400381220b100c40c0000c54 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 889756951 1250 889755701 889755703
    0x180506060901080f151e010e24090303130305010b09070503060d030305270d230409050921040501111b010f05041706060103060f060915050d1814 64
    0x101680c4060f501d11060b5610402c0c4402c8842025000d04c1003552807a030714032050354818280c0c0b0078107201c81040684681c060700015001800000b011030150394034204030041e420151000c00300c0000280c440c0350340c83c81e84100207415486094120105c1d188441e0010083c42015402059581d01c00c7d40e0284450711540400d551501080764840d900030060200300700001d101380c102a4128800d0941045119040d0301400e4080f40902c150884a50102e01c040c0840342d8803280c614008403031118201d0208000116003d541c0c40f0301d0142c01c00d030988610110741c000c5002c20804c02c0c9860b5030243da60048003526210340450b070080c8500d5000600010302c44c82054408141b205111400165101480c44180019104400100801d800340030060100103030031744002c030721801203c0b22013000d030256140c08030015003181c4007a00060b52000104405122080c0c1114081c410b88400c540103c030b4031802c03007104940398170034803c1180e4018109808245240444060359260504ca802c864401e84403171240c04e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 889758201 1250 889756951 889756957
    0xb03070305241909030e12060708130206070b1b04030302010c1e050d0903030609360c12050106091103101710020c010e0a0b0f010f030f081b0718050606 67
    0x80f118030031002c03041000c140c00c1da0300079000d2034841e0a0680c030061045001034000141c1900e60009900300b00100805c17580e02c0030210f1381c030421800210b90481d00c40d13008940540500f101c02842c6140038400b0500a483c0424401030045000c80c006550385d8403890001e01030200c034014503000c2000700e0440c2942c0c40358002c400842030200e6441909110074200300101500c1c0c1e500c000e60074140c0e250760208400c50742c0c0c00303203d04141801d41c041e414030000d800343c125445640d0300c0248421195001c2180003910801400c800c895810210102807800760500384d00404155001c011424a0843c0c1030300b50b1501c203c069880390f446000403480303a030b41d2000f081c3e80b062a821144141c640002c10f0800c419081f990203840f00000c4000001090041c141c20549480011007054910280d81001c129501d045280c0f1a8050b01100d1300510340c031451640c5410f000366016000510120020610050488408440101010f140400c071002240d6036500301d50030011001c03c003c40e140c10000000c1c5142081c03012 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 889759451 1250 889758201 889758211
    0xf0304080a0f170a0f0e010c1d19030b0403031b0e13050903040b0c07170303190b0d03080a0912080601090f0e16020f0a08030117010504051506040b0307030524 70
    0xa07243c0d2680d11100d00e4801040f00008200409030340b81910800b480d004d100303100008002e9100c03519602e848104800000c511040301510071903041c036038140b8402c40704426a040340c0e0b00100c900c405807928038064002e001c20007182426414607412040700d060380b000340c48100c1d02e020b9a0344520b0303507803010b044004d9403022074012070300707900806c02041402040001032078062400c400b60381d24587c0319601c9a40c0c000143d04080d00300d038008030900030610800200c0c9468000040c904102c0204181c0110fa280051010054207100540000030304036184e5800494400f5404014560310418000000d805440250b81540c002070080e0401300b26507890b500c884056030030b24450101e195076110100f910943c0c140d601102103009581031000702c044100000c00c1c0c2ca502c65106c0c80c1c0c880d81004080213404903802a6000580c0c108000d01001c01d50100d1200d2180b46a0420200b1031765696021801a0000400c2181c140c0f1a00e003000081c003e01003804502e0580301c19a1030f0201000c80103040c0c00343e0044d10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 889760701 1250 889759451 889759487
    0x503010504111002120409020c0616170703110c210403020d02090c0f0f04090c0906050307030b03010e0f1b030d1b0618230d050d110f0304080a0f 64
    0x1020002c149040c010010074426144100c03041c00f03054207500451a001580461003850b00854010320020301404100c4e400701c600c40018aa400356072800070445d140102d40686810fa040c0045070445210703811a490398654070300c0399030381d407a8242250795641c1507540038200080101c44290f0100c04024007241c04076138004006806401990f003c000d100280509030882407242000b40664164440c3c000d0810207240c170742030a0300c2e9490203580c142a581c6249510301007085070141481341503000340030340b03401907501c1c034000801d031441c0004039005103086a0750f80c12600c46d12541608410002454a482051a503403ca806420752028143c1d50034081e140c0c0c402041502d41002010b0720f2100000721070500a50001c1022b600a040360b825171113183c081505e42c0c0d04540f008a5a92091003806e00703035515220024401150581002080ca0140000711a41c1e00d44071614500d440302110241d8135003000468031990b0b40e0406240411059209458030000729038071700980001c00e4001c5c600c43c0380403c0002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 889761951 1250 889760701 889760723
    0x62d0e0c04060503130506043f0509030c0402130f0905100512071a07060e120313060f06090510060309050c06070f05070f06030605030a050a1e0602030c04030c0503010504 75
    0x3450554503500000c080a081011170318010b80414420001d0744c0c025801201d9514160042003520646d5403403840c81000d2070120701d480208140c00782001d9900c0c210440c07401d9512030303e0400c0002d0414180007182d6034020300100d8151440c0c8056203030041242c06650040d404560b81d045030b0800e8842c00c0b81c00b22064050308408102c217040800c1601021021041aa80c01035162007541901280c0e4501038030107500d0104649040001500c610305d071603207400c0d00420907600c00070b003402d07580e12005040340d070006c07504400d040400c1003c0e0000c80d03400400400c103012041d100c45241b402040d0440315002c0200d40c1640009a0710301038412030f241140c10001900c0441900c0d000c0c04001da00819003141d08405519519011440c01c3c40010090300800c1407103c0003a01c1d205004040c3c4080c1d0300864442d80110326081d00041c8006410910142d2203140048001084001420aa0100080036000b640004200200509031800403c152441010780c1000540c40303400349400c0314811600105004280c1c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 889763201 1250 889761951 889761959
    0xc02090c0d1d0d05070c17010f29060c0a05060901090218010e040305090d020d06050603010608072103170703020c01141e090c10030506030c06070209010b030604062d0e0c04 76
    0x1c1c001040c1c801d0081c2c1c503a19209647d0006854110403844141106955602c44c800000d44d041c0601e00c08c1c1ea004440141031030400d4500e1b0300011b20441c210074810107000039401e184d07000a000800300d068200098030460b140100c00503000c4c1c40340d40c9049100304000c00d000341c0020040d0024905840076080500c2040d600c55405881c80ea011481d6140d01091030380c20340f401a0345540c04010f82a124000105950510500745401c0d1100c079040141290442d40d0184112124003400311688041044101d45c6074046040c103407130340303014910014441c1e007041c000c102d070040d015002004440292740003007203107000034201031081e240300762081624100f4000c081c100b5468020079403a0854030300411764481c2d0b4100c00000701c485903080a9140802e448100704421403034180100c1d03e620b1300541d901450042641e0005070240414003c01d550010084045480c13919294080005040301c14400200b00c11944a00d03506910f80001c9440840440c1902280200400740c140f40203010b034210045c2400c0c24 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 889764451 1250 889763201 889763207
    0x30506012705190204030f03080a0c12110702030601080609060702010621020102010609050a0b03060903041d090f0d03021803070b1b0a081b1506060405040c0c02090c0d1d0d 76
    0x10243c00c4000071031800d02c41290001c0f0b140300901c01584190040c810a1000d40703006060184014101c00020749040364141c1080e0b000701c0e0a402c3c0c03406980c0005805001240040401c0c000d050019405200d04800801d8002d4000780180c041c0c1c62007022190303699510740c170403800d9030142d001d802134007181480c1ea19484800352080c40d10041c0305000100d2030710b8460300d4034811203000700e81040c106612941720400070304042c046550400c40040140d4039013428003444031149031407207902200c80042d00d000200c040e00d090058840704107000341500c2168002902c003c010b034020001c2c015200700354400d100b0140c50000758900490b000f5007005801d18000c03d48076018000a2202e8610a004100105000460f5039008144180f04c2001d040c10194400c080e0510301621400328595a022001c244809a0b4801c0305540c00c60f1412100400d0b1840310010403075100350b4290000f900042c010b800e00ca560f22080d4047c150480c40346000300151500448035184403200c0c080e00481a4000c0c9144184188c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 889765701 1250 889764451 889764461
    0x81e040602120a021f270f020120030c1f090b06060310050303071208100e010308030a0e0613030813080f0901110a030e012c0409110d0c0305060127 65
    0x202134015200c1c00c2420040d00b9103a041c6a11403102082c2e981c0501d0f030542880e1412410307115180a94071081e90900d1350b2007010004180b900a810b1000c6c40d1305d0343d280b4900700c8604081c00540c84007641d803110048507180d940c5078220005001c054228014201b003041c041e01c144810243c01c405282210b03141c400c01c1c4012035001808103a1000190303400441c80d07403820402010041e110780c2845011030403a44004041000140a4190301002a0410041700030242c401c1070560fa001300440c1d5490321000c1f07008000b007680120040ca10701401007040700411a07203a06500140c0170342c0700c12841c0c0e51210f030440031000044100406007442488040f18080c1110b015105001e03040c1002c45c0315541d20341c00645440780c1c3e07420440001f01007050413038455070301070300701c4600380450701d6184000803000040d00881a00404494007070750340c91724440140b240541044200c202c01402c0b02c070a00ba646d013404440c2d5003040c08140d44600c50300d40005100400e0107140a585072540d9a0540c080781003001c01d41c0900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 889766951 1250 889765701 889765717
    0xe0a02010804080d0c050310061b060b06250210020f0a03200a08071509030905010e0f040e0109050f0a0809091005100f080912090d0618081e04060212 66
    0x404e0201c9942d12045214000f81c0038401e07224540c0f02e14200c1c04243e4200d02c2504411b0411551040107201c9214144104001d0b56000e0070100700118280041107081c01100400201039502610b0034004240c0e0604112820f030095503020301c6820a000207036601c01c0d00c81e002010540c08801e401021038407542d03203900498500743ca485100300403c04a1440c0140505050300c44200001e02541044a18400c00040024544003072214407046c0d00c014007540500d11440d810300c080d4003050421940d0b1003d42110201000b4410003150024628150003402a22821078542c40740300d42c0000410710006e10030404c641d010702d40500e403421b514107100388004040c01e001d140c5010b1441c0401c403983c0310914444004100d41e101c012641d50f24400034180f4a003c2c0c2440604e070005405103500c01c44a50403102c0318101682c0d07003c003401e07413482e14100904041610600b43d182c540120b03001c20118000400d40c800c17240e00c1d05801004103100000007881940300386405a401020100d81500410700585440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 889768201 1250 889766951 889766963
    0x8010501110316110109090b0303091020010b1c0f02150d050f040c060e030607140403140a050c09101802070b070f0906020d090e040519030914040e0a02010804 70
    0x62034404a0034000d44028200b01c0d0a420828004d00255a01540f1207000740088072040c0055000342005c01d8407449402c0f01503005404428010342403500400407164903400003440a60014014441c281c02041c407100b82c50700c81d10701d1109840b0b807140c460303425001042c1c0254400404030881d5081060340d40040c0c00e42c405504050261807511003141c4102480750340600014044c5142528055014607580c1d0424030901002800c10076043e00c0c0020003960251241c00c00b0f2441e41c2900207124541c2c0a41c1c0d00c020714030849a030b001c40e0011f00104240b44200c0c401e84c00c03580754069000800a00c030300102c41c41da070107062201e010043d010b91000e543c0c15002c4902d04c01890200103843d0040003090440b800c0d0081781c0d100c005403004a80c070104150080c001880079003041032040c82e0050112042c3d10501d0038181d071880200c0d0a100d414007008045000c03101c5c1001c030390031040c540542010481e100310303141200d480c480c0740c000e82083d0241a000880210143c14441b00035030064030131240241c010f03544 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 889769451 1250 889768201 889768207
    0x604120f0b010f0f0609080c041d0f070f12031b0f0804120506060103020a020703030e0a1517010812041e0e07020102180d0c0308070f06050a050105011101050106080105011103 77
    0x410244003003240070308003c005500f0321604001d10070b42d83c0705180c2d02440c2040200b000812444101040c008506d400c202e0b004100c41c03140e440c00d150b201340644001011400380d00d5112000100000d4040e04880c800d44440016542e074406c9540e600d0004940a0040b0381c0b6401141891103504000301c2a291050b030107160340d921561180400c0d504a90040380e0000ea0035003400c018000100070840c0e2004092130250301c0e040304103000940b81c942e41d22000703060200e131000000595481c0c5440d10043d020302c02036030341c46110003e0b000f41020004009240e03014503210001c9070800000c02d2100003c49a211070510b843d1030030740d07050702d0440701c0a40c1e003040f88001200801d145139241d4129000300e050382d00142e10341107181498103420454032150780c86522890143c03800140c401c038095085039085600e80391078908604042d4440d445c0040005d2045140c1003c02440300742940c00f0030f0607102c00380da41c0c8103c40310442c0d0740c0c4e00300e031028040c031000309016100401841d031050b402c0c11039000003c416a81 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 889770701 1250 889769451 889769453
    0x140708040e041a06030109110d020d0b0708101e0303270e0a15031112030d090b07090e07090e060402040302030115140a0e0c090109030b04030206040314090604120f 72
    0x40e101c5020354045507000b441140b401c001c1c903490a10f00e50003802c110000c11903140036580d070291219181011600070580840380c1c40c1035659915a9038040740c1c000868910901e031800005110a008480b03410076203000302e13000705268100211510110080c270f0320f032446190035924191807400791010021000000400561020302d83c4003941e0008203074a0321080d4580c01c008245406545030003c102c8090f5070340c1602000440d503034200b070081c941c0741503400e60340740888020180c0c00e51140300e9080030020706080c902400c001c6008841d41c071440c035550351000c445484002e07883c15200140c4001e8006042c801050107a4000f0307000c3d0701e8200710300810040c40c140e626808242503e8840404110f6288280010030030713903480030740100402d403080b0ba58102d10f0b8280b812100405a02905041484a020400780700f00e074001d01040340a10b4001038400c501e0b1400d8074000750f9441084a044001400e01c002c1d000c4660302d05000c1e01c2d49000b0090035141050304006011407141c522840030380d409011691100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 889771951 1250 889770701 889770719
    0x60b04080c040506220c02010c0311040e100b030408130e04050618030c010e010b040e0a05061b12091c09080706080406060e0c0703030c0c080319090c0902070c090c14070804 76
    0x1003080b17081c1c400b060359006400068210b80301c80e800302090500300a001750019481408039403e481c1c0e02c0b400ba8181d03403600c0106103011680d0703070040d044144000003844140071440010b8103039510780310510034036151a101c0300ea900d0310b41658004c0c00d681c48400415621110742070f5007c40388401c14200d034101140d0a503002e0030760b001d4820606080e59a060380c00c1990605008542a0381c0c01e000003020b00c0b43d940e949280e0303039450041000598100d89a0302f41c001c03031400c3c41244c06c0400034003100d01d19800c11080443d152200310104440c00c5a4819410854030b004072030b00e00484000328043e1000d54982002940c01031030090080341c68036030342c03840440c1c0c204005100c180280720303003071050b6265651482c0240860396001c168109100c140d404902c002803103001100d0b0f120b90180941c0500305000039034031000e020300800080c9100c0c2a400041064455940178281f010302800001e02407680e074000b85c1c070131a040e001c80038001510a55030314400c14040380c0200106d5110700440e524280d41c4100301 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 889773201 1250 889771951 889771999
    0x230a0b011215170a020109030b0c0d020f0903011503232802030708151504020d090b3306030601050d05040317010e06090402010f020c13050a060b04080c040506 70
    0x81c0c5603507140c80c060042040c0f0b1a11664101d0341c04004240e603584603000a4031403940703840001d1401022900044010802c101503540308442c00d84299140c3c4106d100c404c1c07890300400d078032030301a40c0307407815101803401d1010345a4103c0e600007001000d43d00e10310600c01800815040c8042a92184901c6480880050074000108824003004d41d02c0a00d184d10415060100c2940700f02c566a01120203074403051410245240c002e00201500802c038051040031401901845004640c810300d00f03200320f814020480e44040c4502211a080040801c40419003200ca50903110041c001d15040c1110111900b0590000c5411440c1414a1070625074401c61360819101c0032a4101c0014415001b842a80c20004c00c85a0141000d461390010354507021001c55400b00703005001904004143d00034004c940d00034016241500c1d0041c148420140c0c5804040025050540c1d072207822900d494400204150444103035400da4903070714041c1102901c03030303030070803015180142c03001c0d521041c0400c500c0029001c1000c0c3d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 889774451 1250 889773201 889773221
    0x1b0901020316060e060c0c1005060f0310050613140f0709050607060606030b0109031a1b04060201060311240d0f0903020c0405160905120313060c06230a0b0112 70
    0x201003140304220752010704241000d8903406d00d2080601034141d0140c000b041050705014013001c000303900d6070707020f0020303000d040c0201c8180d0300f5024a64a420724240650051403013500190f4a0b850f282030010580e07422a1b030302c015100c12514411011500d40c8104000080d0012001e203000700b145600c800c00645c1da40d00c414412600185d0314641008a19094010401081c10074240500110310f5503c0314408000303080c141c820105801c40000321400c00d40401003024061010049442d00d03221800a4000c08150000750354a8001c0780c00381495280c00072030049250808404016078211304403251a4507004031802c0d804541d2030f4203045954814500c100308500b40690300a12041c40d5150a01007140c5025000908016800a900000d141c200040354100c3d14252145040d4504c01042d4034218003801011a403517000075003002440680c03000c034282049025840402c03913040d5119040144113507401f40185405080d8001900c408503550012003042c0c4103041c02889030540c0c0c3e0602c0221014199 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 889775701 1250 889774451 889774463
    0x150c0f0306041b18120206090d02040e0118050f0f1f020903011103040201030e0a0302060601050c031204121d091302040f1e060608041e020127030b09061b0901020316 73
    0xc1843c00f03013001e020381d510003030418038540940410f00d500880c1182c41210006c60191480034425021074841350700246240282c00020802e00c002c421103580e58110750007050b206807061500c00286c1c07000200c1c2c8408600b08000090698142c240e60152401c9014180e40080c20f86c244178660391900c0a000700000089820405641c900d070a20024040300c200502050096210040000000307030000744868010b5000d007002625200d0142040e4594881e4414140d90023959a0512040001540280e0100041030b00c80c21a1040316249641c0c00da40a140340d180d20000c107c02094103410140f02c40078100740081c002007001c000b0051150141c8460744010040305402e4405404580c0c0344d4441d01018003142d16040b501802d094071500080c3e804c1006035110300c409100c40004580c00b0340b0110448840c000c146514500b4022400c1018042c60710081d1417807010007001850194002c00c0c00f40c4100325103031452014450071000160f49400c0249000c0c1584030400084501507100800b0910301442a6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 889776951 1250 889775701 889775717
    0x207060203161115102606180703021302190f0e0315040b0a022505071203080a09060204050a0305070f052202090f0d0311150c0f0306041b 61
    0x180b0340d10200484540c0300c104001c122911114a05004036071004803080c000e0300b407860b80e01c80d49040040c00000e68440302140f84400350001d6201521594100301c02e00032026a10b4a90f92031413100f89113030080380c500c0c8180d009007030140010316040c4801c440d41d00c5011401400c1100d042201046040080704c0e1501107143e08403100521a40b00405041c0c1d10005e07000b4040c8640324540042c03036108050801040702c080c0e0400503040720700a50540340020066a60907000b0300843e80301c540003004040040d074403800384040100e285040000c0042000740e042e624480540d45d0700c20184000e0104e80401c40d5615001c1000055036583c0030042c40145006801501007140740c402d00e4038181040b81d000d00c0c021010718400c0b805900b08845400390340c0c051407502690b80d003011000038015510754030343c0381e900000130b03100b4400741030380400c1084081c0100401c48000302c00d40070044d041d542003180d9580c00040100112070340c070024400655081000548085040d070003040201c80034843e0210898009103442c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 889778201 1250 889776951 889776961
    0x3030e0316031706030f031b03070507120611031e07030b0a170714031207060b040c030207060c090323012003100b031504020705101b0212091011100207060203 70
    0x81c4220f04c0d00000200c00034520182d070428000d0300c9026488424003000302c2511034001050080c81203522150b0310505840e07005450345540228982141c4080e2822460001000000107980c1c040b6130240c918803e00004d011442900292001d100629080815482c0c0c1d2070b0103200d458122000b4017400c1307803108000d00185c0e4008070514110096000092510304000c045040351404540c2d40c90414031810100e6407207100d802c095016180c11401c5030740140c40c205c05803c0b403552583c05452204d20508061200c1316000303a0840b030b0303840d983c00042e003908040305e00c004d0103007080301d4000806031803003001141102c4001c00d0b6244103148018010303040b190006c10841e624800d00c1c415030140224950003429420301c0c00345901c260f106c0f10003003400340d83d0004804060000400ca0a144a04004003c0c000529100902200c1401d8828594054420195004416052581607680c001c0c0c010b4070500e030320180360300b0490b0141000130071601c82e030280e500b501d440881d46000410486024900159aa00b44 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 889779451 1250 889778201 889778237
    0x305010b01020f01230417040602011506020102070c05190803070f0210140f0a3006060207060c11010e12010603021915140c07060804050615030a03030e031603 70
    0x10380c2e400307510203925040c5c512601554804000c506044030070940d0020360756504c0d04038060350740c000081131385010100d0009006c55054100710303259001e240c2004589960303418185d0a0b4010010024446007071500c040c40070781002100c0500c00100c02c0411580c45542d90486d500315800172805441c1c2e040c80510705815414001d0f0300084104044c45e00706d181d0014000d0303003030582c0034144e03041806000c0000c146100318464100c0c01d007810440320f040940aa101d444010304903086019141d1050b040c41d00c0010b03814008141c0c6411111551070745500700003669107000c00280d4101d4414140300225010b285103807103551803d102c0304482d50000031054114010450340d81d00358090000b42500025050007418038102e04c20781190100c0c28103040c10044500b40743c0f01400b2b1280303002558402c5020016206030b0003075201d030065010f82c1c141e809a440c2d10350b110704030354a400078003a050383c0541178030b00000b0304c80c0d03101c0b0b00055130940981c3d007052076002c540e0b1340007540c41c0000e80000d6554061070012100c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 889780701 1250 889779451 889779463
    0x60a091a0304170d0b040e06090d0807120b130507050c12031303030e0a081306030605030102040302060f1c050109091e110118030b0103030206100605071a0402040905070305010b0102 80
    0x5900e5896401c501d802d96508542d1903221102d000030340070104074a00400a05e800c4120901801002400f10700c65240002d0358800044404c100c20344a6001d1010310340340507240381c0d4082e0f962503a1f0745018a100048010280842d25003880e006280c3d12600310344a0f40b0b6100d424040c00503a618aa9200082d4907943d00d0704d2514007002502030b5040090080070070a0105001200382d040c200401d21410744880507007441e9203110040c0207080300103240103129402c0d05000c016242c084d141040042d4460341810300300e0245000c02500420200850070308000342401400c0b0b00da20358502c4070b040611034111181552400e0b40071484080d01c80c0ca002c02002428503540d02d040100c4000e0780c103a540300740c6800000c034003004d46c0c003410300c68595903d44001c02c40b0104200034503004192144203596034900250390f201d04076952039003004c4040001c1a80d52149044030307a6281c2140703002c03400081000c26500b02d04000342c81282d0243c1c1d1501c1c15000110280300c0c400080d0700400000039186e0003a000a42009 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 889781951 1250 889780701 889780739
    0x20114090d140a1703073f020d2403031119050c2715150309070e0f07050712030b030123130203100509011404121701030302100b0609060a09 62
    0x14134103004204003590b10900521040400700b11910500c40c50007001140b00700b0000030a440c50050700001540e4220365001884007600c103040070000c01d226090350180b19a8200401880072001c007004102013807080010001680c182070075512443e066101c0c0d80c0d00d038294400c00311241e410111a0f1812454200c0d242898000c4414450050351418900f040c50010b00510324007178070991070280465900ca8400e05010002036072a001d40e01d04005100d1981c1c0c11040c4070f81c0031590a160000341d01c0720b401300042c40c0294250744419090100a80e80c0c0c0d0080c1c801c1c040a541050303038940f1440b0301e60b0740c2405158400c641e002d02c0213103981001c0c1070010b880718005008007007042c0d0801e11308005807000100c107000c660708901c0004041c0c40c0d019105025083c0140311580e419940b0081c881030000040c0d0168545005131a5141c0030070311024500107809091001070050303040594030f0030480c40e254120400039217000381078500e4100c140000400301d4025489100020b03064040a2007049880040c0d84141 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 889783201 1250 889781951 889781993
    0x11120a0b041a0c03041203021c050f070903021503071403070c030206010602010509101806020f030910050403081f0801020c0f2109011404050402030f04060c0c020114090d140a 77
    0x92416440f40c9545210280c4024140b00e9056941b20007584298141d51590664114803179001840c99855030180006590505541112101140666019042e40c3c030031244d000e440c4940907004c01a00f0542500001e016105101c001d002c81d0f00c0e0300c0621001103120300700a445140607050340781802803518505030030103025a89070006204042100055001c41200144408034248110044081100081d2400204061300110368200c018a02d14051849008100100c40129102030040c0d010703604159405070110701348401048100b2140100004191081c0315121059991540514220f034070001503000e41c1c0d00803298203005030506204001ca000022090103020248002240c000b5115450340c0c14144580442903402c080350380f070107460040034014811516450411640501c812084400b00c2e881ea2602d65600145801030b01c1c40c0c10026010303500e11044881407032907003050303030320a4048130780c000d01003500c1c00002446040c4040c0306c81020809007031089541e10306400c01c000655900529 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 889784451 1250 889783201 889783253
    0xf1a09060c07060209090c0703110703020901050603060f1305100501140318190b04020103051e061e0d050106210b06150403050607092405040311120a0b04 68
    0x201240080e03030a4000c000d10301040d6488001d440c1a60080c4504440a40c001c83c121080140100b40783d00603048440c000c0e1110381d1581280c21070640c442e031450000960001c3d40c0001030203107042150166a002401900130461030820400040c224078607034848003540c0d40c41c0c1042010004007803452100422081c203241540700c82c0c0301e031030b4102030000900e10b41c40c5412024540100100801010481c0a082c0c0a0419048020300f0115101641100c06074007080c104000f0038080807294188058102032180c3c52011900d6410401188009070f45600300700c0b4000618071035150380e825091a0480d4401c400002e4101c0ca4000032031801c24100000059504014030103e02280c41c0c44400e47e4041c0c000c0364201c2c4045854019001c45008a0700007420300c0c8110b004100020340c001c01407000740c2d0704080300203010200300310310802d80e0035100b411240007400500c02000003810056000c134100310028038504c003101c035107200145003071160601565108054824002407284554045c001d4500ea032035460340e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 889785701 1250 889784451 889784461
    0x30405060d0e070506030c0c190201020a1410020c0309090a020310090b0a2606061215040c24030c022805160f0501030b060a020703032a0f1a 62
    0x9094020300c00100907440c1c4610708002030400074420a405403400404c1c903522410314481504441d00300118907820351090030320707244d650b00200c00d2040d0801c1d816801405200416030380c904844035200c04010481c441da010844c0b000ea8030380040e001a42c1404010758503070201e401046140301016281d0701006104100b44540e0001c14400d01040e41c905d007d0120314108580b01045139030503158400301c8000703500c00b6003840c01303182c8101500039042c540d01140d0481d160b18082116200844800001f03907840440350159101d203010303406a0150142c110881c12a076200043c40c03a0708020307402c0c0055140311b9002c030801c0720f030144180c818078902e510040202c0c240c1e900da54417200c00044408100c044904400a080000800c501c541844143c1e0b42c1174205946d400030240515004e004a6000c40d0074685c0603505410050180e03500301c03800c3d900400762a032643c0c900741c841290b4240342119803c403086d010110300404000301e1f07a4141c4654249100c10340e0b1402c2140c01c41603c144002000b80b00c40c02844 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 889786951 1250 889785701 889785709
    0x90e150a092a050c1902041409060a180606060509010207060507050a03120f090605090705030a050309100c06021c0e010212071b0c030b09061b070303020f0c03070f060b03030405 78
    0x1200d030507010082c51003461601c500545450142c0c0c4c00c4246548103840d4600c03200e203075010340d42009604c02e80b403e1051301c200d601d40e50647c1d41c00310350340ca4944e40404006a0002d42c02d0f0055120080030410524070301002c0d4540000f60b82c6603070441c2011600001d100070f83c42d60304001da440103003090310300745041656542d03d003511065042c001504003d581000503681e442564000b503150314920000700506010b901d000c034003070502280d101e84c0c24024408000384038100030440602d2643d1140103545070031a803004002c2d6076600c02e600303202004070b607544202c00101c2e18401000c00080303840c1441e1540ca02a04110140d0f074690603850b0032640103006410103103101c00380035504862b25051041000100c4c800c62045078500301d6019100407802c050004c10702c059a88142d001d07550308000d84003280d5800142e00301d6401c3c03a22280d0794124007008840c021034840c0e800752042400c1e6030035007460300c0580500c1ea1700e036400004c3c080d600d0340401301c4210100300701c42c45800440c2d14144d01440c102440c2034001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 889788201 1250 889786951 889786991
    0x906040c0302093301080105010c020a05121e01200702130b040b10110d08160c0516090c1710030f02060f04080307031d0607030f090e150a09 62
    0x24003540040700410b0180400c4143c544007070307241d844d402d0807030a18102140c0003802d00600581c0814002d000103c1d0769480342103114100e94014000c203203104d18000034800d0701a580c032032074402402160340d21840109d03408100c4242d2107aa078000300701c02103420b901c010101d850201880500d84104000ca0050302d6003070340360702142d0480070005030180c880b8003ca40509804205554000a6090408003864000c04002c207180d50400894000b00880c01c8140d403940d205030b50600388880d10040901f400b83c815401d01d0203040c030030410348140780c100700000d00e51044141c115000b880d846984415404c1d40c0f144180c554503900c45108140d03070a0066240004116600018102600b105168401d640300c05e812918900f481001d101d64a940d00c2c001c064603900842002c40019145454008401818581c0c1c0b0390821002030003d80b411146035803d40b00b244401100c04148860100b0001d65001385892040c0300380c008410022985140c001081060f00e5070340c22010040b890400d40c00c903a2428402c030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 889789451 1250 889788201 889788203
    0x506010e1308030601110124090e0303010b0a020f010204090e100522020a030b16180e0a0b030f07080705030f010203012108042c0a02090907050d0e06040b010e0906040c03 75
    0x42d0380e629194000105e40f18032559015955542c20440c000684503040aa070794407080202c004040c00f0b5448481000c25100d00300c0c82c2d01010b62090005010550002d4000d25071500d0b540100e414071240c0400141c207a80046e8044041203070745000e452070307451051110760303550b22200c1020801ca250009190b64417a100e245900e036480c420003200411903d0710495907006d5500105200c9051622400248001c0003580b507040c0050320074000400551000c503412400d0700d00d00901c24070556038864000e00240b0070b850400b503052103210313040a01e01c0b10a100903000b07000100003603c43e1a05003420300d46060000c0c90001080e0303104200410549102c8152f45441c10030350000c5400219407030408041d02d020340d402c070305003142001c1401004c80390080c0225002c3d440c6052042016030b201d80b8640e0807409042000c9800c6001800060b0590f4405c800410621806e4000050070040d419161883c0c000c048404449143d095401400543c03503400c8402c2d84142d51100403d85d40c9440d80d500714202500e440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 889790701 1250 889789451 889789463
    0x40b01210e030708070602030106180609030f02040612061a0a03030905090a23070f0e030606090604060b0706021206121213051203071502211503190506010e13 70
    0x400044a07009004561040360072000e810b440b8001030a10303800039403003842403c002c2404034040c032560502a03000310003265016159105014a1500d800824074100c1100f260300c5580c4d0200815940c0392500c0aa8540b402003030300241441d042101d00c0c9217090f5a004c42446410600070030000a070b13003e0305403000c1d100269140c4106031164440c0101820039030740045111001100c4654618071904c0310746200e07007203a503900b02104e600050b056622250505405804d078100d0700002d281800c103904060f40045000c1c1c00007643c9952950700c0c8020f5000401c1c01c13036600d0b40002311000300003050800c20f904448211040032600c5032004000d65a0308540781440c1c101c150120b0001e041803020001080180f07806070151000d00ea603907a203180c407548007141c00c03195001035400c9030284404900c255110352440d5403800500c4202c0d40f0f407228545400030489510369901e203541011300d46052083c009184980501000c241246203006400c0120580012070000d90010801410040343e03c600706405400c08 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 889791951 1250 889790701 889790711
    0xb060f0c010207050a0b0f1b0d020306130c1d0a05090f091612052521170405090a0c05030f07200601150809030a050c15010803030402040b0121 63
    0x42440780680030b44100508a8000e14180b8000d02100c2c00d50680f14801d101d14030001070380d509010a034502881c80301c0e5001e44405020000740c2801d283d00554001c1d0005000e2054215100d8a400660b030440c80300d100040c0c0032a805071841c0c004109032002140303007150f03801c0203141004041105410010800c91030b005100001c6903000d03d05200c41d81028025140c01288182c035a800c604051040f15001c6569201d8000c01800d103c41407400164400054204c0b1040c0c80e1918124000b80704000044c1218400824089000a1300312035600400c0084071045a440364940300030003000900042c00001c480f82000400800c0d00d0713020045a900034407080f440900d58a070300f041182c3c40340760003000c0c80c0d00c0801c80000240141d00001c05130304960b50f61200c0c446280c88c07400c0403120064140d4207034190754010f11030103103d5070003080548250341d90b510440d4106101e480e06090000e200b030740088007035003000040c0b0081d8101400b41c204a02805e080454524295075250782c0070030004070325000d01503952 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 889793201 1250 889791951 889791967
    0x21062c0111090402070c0f26030903060424060e041b0f0902130503010e1e0703020924100c020102100203060609090601110d020705030105010e0105060703120605180907090b060f 78
    0x455250144c09254100035200d5120741548c0d6400500d40000c4181b07640c170080c8800b480000008440c000a40038004e8202910b40c0d540d003081883c00b244140c5e480fa005401c1e0340c0075003050343c4506402000398060919207410103040c44007810b110041d55662640c4421000e1001c4281d81a1940484107000e50050b511010490403d0350310070300b900095415401d0040440c508800041c01e500881528080c141700c9002015020355183c04900c0003c1d0841102d07000079400210011203c00100034541c0e03c01102d64602e800101340f14114400500458200b8100206550741040307040030071056107004525500f0040006403082c0a44043c0034801c00031480012a039034811104044c1201112080301e0f501d40c10141c010752036001b40c0c00386600940c40e007000011010100e4000d90b0483d880604010f141001c0c1c0e80302155400014024807001380d490b100001116155008006550f421401400c206820950241414402d10390701c803241c00303030401c44a807440e903540303c0889240305828508241d465042c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 889794451 1250 889793201 889793213
    0x30e07060e0a0b0307030207020f0604061413031209030b0708010509010b0901030f0c031a15070b090f060a0501080115060203090d02040b0411030919030203030121062c011109040207 80
    0x143e0014642e03001e003c000d010443d80c041d00a060064422103180310380b00f140b5820f00040740683d104140004950703449100f01344582d03000519000e007044045590283c1c0302d03296024206141105400001d000c81420802d0248001031144c0002039440c001145514010004401100c103001c0c048040310b00141414180c1e0184d44041080ca44441c000c2c8400c1e02d6000010b0010050802034404090544007001d90a00d4204601d60108103900071507810407007240c548005000b4020100c100c036108144003198001c8013004003030320444d01140003040d10341c103006810f802c1d030f4407201c06c1d1008030400c5d2500380b140c1b58010081e1264090143c540d80301d200c400b0300004010302520368a1940084c6081216861544200c000314841e501e5001103d4026103540c00034005044200c4001d00160018401400000324081956803c031120100032182c0990b2078075110121403046007018041000c3c40701005000018042440340c00a6160003048440c845c0c0120b401c040c40784030401071042d98005070702010000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 889795701 1250 889794451 889794469
    0x1270203060916110f071a130306200f1c0515042f071b031e0f0203150f06060909040b07030e0f010506090105041802010c0203030d150510030e07060e 66
    0x1a800c216540124405d01c940d4840740b440c00f940e8211154201d0440320300741c00c6400c80d4020b248031513800e002c152664540600500c0120000d009840341c0503142d5035400b11403006022181b00c07038488550f03a16426071031180010100003c901a003808d2000708142030700150744491100d2400d40300032035031944450b24560300c1008110300c41e0854190b0008481005007a4002d02401407040755141c1070820304045180ca52021031000401c02101002240ca40702c0443c1c4c250302041d840b822014078062002e0b400a4146001c001100d28403030009010800515000000d4582081d000d85078140f920740c7c90070204908440043c00034061340d40b56030101781414072961020f9440b4401505039074050680d80c1c1024042c1c00e01340c0741c4030311403500c2c24004244c91900340310b0074500101c2400040a082c84913401034800012241c0c080c0e034180400d10418111582900411580301400c1c4038040141b81850204090841481d41c40c3d8105450030410300402030300021440165001c50420018203126030001500503c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 889796951 1250 889795701 889795727
    0x406050a020405180105040c030204051f05070605130606050f0f010c1b1e140a0311040b09130c0824040f061406030609010b060a1b050601270203060916 67
    0x1500744c0c0224415502d035048118140c4400300d40a1004640c080001c8051340914000c640d40000d007400400d074030501001032507104800034102039081a659481d04812038030b04541000c0500200d08007801001594400c80c4050542201c2000482d151903005c0323000c040e00e0f2010340f41032000e14440500ad000c90540004011f20011001e81f20b500e48034903594100e40426070b00c0300c1118070242c001080303100d0b0000e00e0b40246580502540240c80c0b9580301ca40c51442038918203038100380e440001d003595860b0032007440c4c4180440c42d03126850112600e449501000c481d444003013650407110004040005408032035202580ca880164210346907803c0c246004000098000e1005141c8080039000001626130300c1d203d0001141541c40d1552400600b500740d458443c00b181d0710100400c00210070380e00516a1000c00311510411004015656483c07502d040001e0b0881000130307402091804907070711f011015402d400703503415043d0708600b8030601066042c1400390001042020310341403a08072a108000703640c002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 889798201 1250 889796951 889796959
    0x91d12091c11100c0807171e0c0f03070c0317041d270703080d1d0609011d0601090203040f0b040b0106120603211e0e01090f08060406050a020405 64
    0xc0290b40740c824000180c0b80105030050054001000c1c2190003800850311658200c00114501360b200e03940c02e002d451185041801d119000c0c8104595898030a403880c585280c15080a5503550702102624500740c101d41d035001c0b41e03134020060b210008221308035080480740d0050312203007540400b004041050149422120314043d400708042e42040000328040c0c002ea02c25514051210981e080061000c03c4008400d1503ea100300700400c0050800070040a04881d404400601c4050440300d400310141640f03400501079000c1800e02c01c9222080c42419000d0f0b1101c00c41130301824a4550702030326000140720380c14060b80d000c0700050a004aa252000340341d07500a211002c0c614051501c26450f40c1d003070103030000044400110200000d403500c0bc3c034056036001000b0120348205503081050100313600d0340060070000c2d140302d0000340c4402022581c00c29038081d21180100e00102c80010814009030340a811450181182041780d0070022036400d030850b8002c100031406a0f40c50072080064445c0341c0c446600 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 889799451 1250 889798201 889798249
    0xf0923040317011409153708010902130f090c0b0307020c030c0a0e0c1210060e030a02130f140a0605010212210403020a1b091d1209 58
    0x100740e400400da40508002544080c1c041e40ca03040c0301c0c0001c03a4800d2560b608070300180003040c20840304115140a05200802c022045c120b40310410001805614042140541d103800401d030501074403255401030b00c8820020050700704581c00003180c500106094400503603960322202e41e02050b0383c1058038502e410480556a20340c0d640e910400a90080312103200500580010300f00a02d008188a00003c1c5e0042402d200c050130303e003e140d60303420041c190b500349140c100402d40c0c04174010810984501545401000b0a81c40d060018008544410703800748213070070035441c50700141c1d80c0500903042c40030900b4000a807000322015080041c0261303031481142c4180c0500300400383c615504810242c03407080e070980d60803680d290344a070180e00a401822200a04070b0050082c1c0f1300140001d264054040e00c111002e00c00142c071025861407060288504a80d800305040c008c3c031850f4099400740c0d0b0300103d11905800c580016a603100c840d148a1101c950b0800103014441d5940d02ca43c56007601d401d90343d4066 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 889800701 1250 889799451 889799453
    0xc191202160510050105010905040c09050d081902030a0203030705031801110d060b04120803040f1a040308010b190e01030e010609021e0a091e03050f07060212040f092304 75
    0x1c110301c01180440b514451030300345072030500c0309000b514101c1354103031244007850f4145010003000d000b881c80000b04108420310001042d5803450486485140104000c1c2d50b144054031500441141200c81c0d03405543c810081c068201da400401c50340c0c0b09480745050b40c0c403521340c106a2070010262800c0d5950b55800d180c1c422050344c03c104000c00308910100e6040050541c0c80c01004814041c500ca220324040c00c0e1003d0b580452500c90040d039015100b03203882c44005c10540c2c0c400003c60110744c820f41e0341000241c02c0100b0507402440080c00341060b800383c0ca0070041000d81c2c1264410301d0407151010400a40007034120340c0d01a80100b6109880d000003400b425860f0444040250810000c1a2101c2ca407400b40e4440c0c220034004684405206a59494200b820114503402a00300d0064120800000c3d000010214409210310305aa803040000f8004c4c052902c01d00900d030a41c8004028542030042008214080700796580c0c0044404484001c10581240500041c2803480e0700020203201034001d04000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 889801951 1250 889800701 889800727
    0x31a0303130807170a0209040f0c080c130b0934080907060315090b01090f060c3810151e030c09030b090a0230060c191202 54
    0x4003510200300807610700c5559a84034201802403100c40c04103c4d00491081400340c100264000e51041c015281e01c127291009541c2c2041c001c40c035610840f41900800da0300102443d055425510b642c121620074403c1810000010f134202c100078040b98030b0185003502211101c4411043d070001c01e00000481100c6020b0114040c000403401c81d082d0103180240f00d00880c1003030091260f00c0040000100c10718486040561071401040c008250300c0c1840541c040024282908100d81d0001d0180c556076110f600c4030038680703409000d000036007400f21030b27a0322003c0c2002c60140c0c1804011242e90003100090076221182d48410350b46140c0c10102c41901c49601c0001d02c1c0303420007100301941151140f041c1680c80d2000c422012901d5440d2404005510448100003050b00d0220140c1c01415510035180010b44aa00007010800700310108620390400c000c0314210401d0440c4900c00298119000d03140c1458401046138061050342d9000746101c800c01c41010132188505100d40401030f40c0d110855642210b10410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 889803201 1250 889801951 889801987
    0x5090d15051e09120f0c0309060d090201020d08060310090f0b102603030f0a151e050a0807050d0c0e01060903060c0e0102121b15060f030a0f03031a0303 67
    0x1c0040c440c00c03400304403a5440020500c80c5130000351003131414080d031a070040d10113600001e07940c5154070040c090302d8032994400380100010a022000050b40840302c2c40007900700b0040310540c506100c000c004212040c0c4000c1148a11b00b260302a0001d81c0741003503c0d02c2807018083c00405040e10f03a4103002c004c182c0100d90702c40310554207003440c0c068605078038140501007441d2106486d00f450700280701043c48042c06480c52a0810301401c03000c40c0b01e06400d81c1c00400868542d00104000f030b41e803040e4040d030001d1620a034002c0d102c01c1c1d551a101c0da0900c0125603031103e052149034010301d0710030204070910104001070000b6200c01d5606241559407400300422a40603804161400c3d80f034205114106401004000400981070300501000045171b190452140c21542540034420070341c03014414406014003402544211a140c07000b80c0381400414408410304402003640250300c80031242e4082036140307070700b1806240c0c540703004100e003030341c0d00d41c50545000d03c80a05901844042036a282072001003801c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 889804451 1250 889803201 889803241
    0x91e04061212140307020c090403090308070b18030414060a0c1a040203120702010206060118080d0809010e0712060b04090803012607150c11031204031202010c05090d1505 75
    0x19042c1020301c508450f6010f40720a44105d0056030000301248143d05241d48038581c01070090030541059552a200d9003019071048004a44d910080e5041081162007411604021f4010030010342c03d080c2410405004505900500c910420011820b00f8a9500c110074141d6120762102403080782d40c407040c5c0e10000c0c1131420395023280700e40540700074240c5041038070007a200d1041e0164010615038407401c00559540c0d00740781104500d10034964010518510420803a00d005001d17581f61209441c080c00001d007150324250290115400400040004911300ea16500d01180c00c002e000452a8020002070010071748404c009290050200002032101401c800d04094500c1003104400c004040140407619071185004009100244001c200940c1f4400c40c410100c036480380191007600301d00700000924202c2c03800d000203d4907000040610403c0707202c130b403414821183c9000900c01090345481c00b61190003501440b9006540050f251401d0080700d10901098244071034082060b8201940b1851a10a090070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 889805701 1250 889804451 889804457
    0x319020d15060207140f0a03060504111e0f04020403080417160f1d060303030c0d0213080c1504050a0306181b150212030c030402180708100902091e04061212 69
    0x1805c220300e0306041c418451307400c00007480744407080c2c10344d66044010f203009801900ca840c6d0007401c01c14180ca40074200304030038803203203401020301c803600e400c1241c0c034140c0300b80d4140103a0052000f0400030388030b28244c0c0c09840002078540740e0082c55102d49490240c44d411000383c1c00000e02c1e000140914503031250000e2302e040840c074044030040030f001200030a80a940f0690903600030000a0402616072002d03000e4812a49005490503002506040b25480c41c3d0300300002540021481c80c849181c40d11204698121501c952818a0700d040300107514a161880090401611680c5101a86c48818604115160b009074089200c960901c548500000c1c580128240032400503002920640001013808140d4400c429052660b41c510720000416080940300701e0b04800d400842d140d40040c19090644900040e40d5081c6880c030305160b00340001c6c20550310200d48584100082e10f03d58481241d8001400144101541500000004200141a243d00031192000d407d58201c1c1080480c00000340307018210b036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 889806951 1250 889805701 889805729
    0x32d0624010507150f060e0a0606031d06040b0403090b0a02100b03010212010b0c030714100f050601020d110f0109030e0f0924150f130b0319020d15060207 68
    0x54010b66851040000c0900a549240c00300f804003649608214440c1d416401e000c5040c503520440d0007801c280c16100c1d003100d01d80b1044140100c40c2e0510541c82d81125039010b04036078030700c0c81074425121200038201507c0c0c0d10718440050b0a040c042c111040003403a80241c1e0030765542d030b80c00d4000d4a80000100754814103040100645603880c05000b41c0d01c1030602c450084095928040c104240e0b90301801c400001c80c001400342001040c041440d600d4044000b0f8007030a4084c8044124001303c804030200b001038545854203001860340d00142c140e0b003001050802d2142100382103486450320640c0940d00c2c00341d600741000361042541c000c007807068074401030300c0c1d07031413034010039410040f01c00c800300c0301d02000b025070440241c820190312515061411020b000d001e01d40d00f4818a14140c0e0707211071780920080e64002100004003000c00684401010b5060b10349045003030500303050781d80980740701c0380a0101c1e40101d1604030b40f1240398000c5400702800c2181d0400309a54a102030f454400602c10002c0c1c2400030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 889808201 1250 889806951 889807021
    0x6020604021008190e070b0c3301050d0f0c120203100c1407030306030b0a0e1908030703021e03100e070306080c310f0606020c032d06 59
    0x20700940f8080c0c820100701c40200000c1601c00e1004090f050040c2d03110f440f0302c02d000103600381c10fa0010082d03107404038050941440300c411049209840260100050800080b201c02488049d00d03269041d01c5003190080680a0142000844461010000340180100040c0002c0220000f0560660580b0070f03400d862103a080700140d101100c5407000e4203008550071410304011a00404020b0070030902c039040c0000d18035181d450310500002c1c1112082140359650350000e651100030881c00e42d1940b285034008041140595611800780406000003003403580104000d4291000000000092160744030003507100c2c1703411462030703011038002d102d00c0204001e188041541a41710b400740c40309460742480103201c480c000c64240a05548034085011349000c1580b58408407142818819001101241d000700d030415028103205e080b500c0a80c440b40c15940045098100345d04c0102e25400c4481d0f940d8161003c0b50030f400a1080010250220103001e406444100316117076614a50a00085040c0804035a41c00c00d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 889809451 1250 889808201 889808207
    0x33c0c050903070510020f010509070501090e1302060d023007020a1101080c0405041e1a0a03080f300606070803280207051b04150603050601030b0a060206040210 71
    0x41050458243e085240244040d05100e4038500000c01144101d1300448601103207503084034026201900182c010f800d0800036581c2c4610803601411804003680fa1a0618102e2040350451143d00240a9100030881030881d82560741aa00c1c001c05048190a140c3d48100d00d0140024952000c4510070b9180408105410f01c0010500d0f0a55807148540385c203a05c800e0019250318030001c05048001c5800c00021441d0b803518041c00108404104440b0000304007182d10006031480c82e00340c88041c40c40300749800495580d0001c1c001c22a40c000445940d104040c004840320392107150342c6200c40c0c0c0c01810f1440851800c00c101c500c614040e1243c601c03d1529a5000c01c8480d1165103c00343c200f01050022a80d054800b40300581c0340d0840d10410600d840e01080d018060340c0001c0402d90b00d40d00420070b0b0810300394040c200c7c48125581108c04204840080e40020031030f005a000f140d0806586800050b0564004e900a003101d86c8000d00328000e440d511180255100e8044070124050f1481c94202c440c2640 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 889810701 1250 889809451 889809457
    0x306040e06280f062606070903021c02102304030210030510030209180111041a0f07020d0f051908091909090303020408070f15033c0c05 60
    0x198188080c60003100c0c0b0750950044429203034a01039866658441c0a603414014410a001041000c1020600c0100d0750b81821001d00c1001d400f05607608034108100000e0b50220448065070390403aa002014031030783d0b0101001c5009200025007000c02c0300d242c0c5e5091600b100190154000c0700c01700d4030b01e141080440300001c3c01248002500442844c403c1d400d400c0c0642c0003264083d1000610645060f6240c000918200c02034424044424102040c002415000e01a0500003444855030924080ca0006407400340b41c2c21a41d048144400404d007140751550502c200c1c0e00e12a0000c08000511185003420f685661074040308484070710802c40300595101100d001d50075020780002c0194100302d400000c1c0600c80b5000c00e03600c0c01140102c1ea001c5160b00c100d210300355456000b83c1d40140c8907410100b06a1500e505a00304022001a021003080015404e421200d080c00e042e02d008640c2a00000080c01490440002500410425210035210b46922820341d0344a0a1245040c001840300160a944501c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 889811951 1250 889810701 889810711
    0x8030313050d180b090f090705030a140f06040e030c0109052b08010b0315090a0c080105030708030403060c0c020d11011b08120c0f041715190c030609020c030306040e06 74
    0x3080c01e490400031303a920040030b01340b10000900000c0b01040490f0004041501c2150b2480103d000841400040c0946100b009004284102c0c0d0491302d04001819903031010004014a114a890b40a46000a2418020b80c1c07643c9540d90000d006440e810300d003c0751103c209805402c401e0601021241c00950345880301000e4000350b88030000b5690a0113000704d00760b80001c4c11040142000c940301a840d44412001500c101c000070000528980e0003d802005054103030b1119200b80d208036030a002d6504080b0460342120f80c0701c400000e02400340d80c02624199099840650700402d05032b65a024040001d01c0341211100998411042425501c1403401da1024100003600b03101c000d1114103c1c0f494680c401e9908485100c0c502c81c02d007594160029001d17881604030440003116020a0786c070700300701042a1449049140c0e0400220b01d4080e035800001e07160300c106c3c00c540702d4a030147c000755940642d101030302500c204407040d9610f810040c052035072039005440b0580581d18114420380c1038200855614043d03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 889813201 1250 889811951 889811987
    0x408010c08010b18010e13060515030105090a05070c170a1103031b0702130213090b03120702010f0909060f2909060d14040b0402010329150408030313050d 68
    0x8880440c0f2513031a1688412100c1c0c0c107100d200d01c4420061764441d0415240241d280f6004100b0b40e00305414000076400341050744c00b540382e080c001809160740303030001396502c5070b0445070000d500d580f90700046070013000e0ba20010b868040b0b54480c198020010800520f100d011540300c0140e0711b0400c0203855071b00d200c121a1a03030703d4600d14000d1102174000ea801080414002425580c4880c10300038600200c0c0d010000ca003660a40130101000403520b80d00030301001e0442180039141c000214034010400d8849c0d22402810400c5520000c1d50107409640254042c001c008002c100c1039846c0d5403510705119150144507000c0c0c28200350400d00144e0300ca94014071290b100f03d014244101c00050190360380025414100c82c54480200c51011103d021046100318010041c2c00700341e0030b11f800007508840c0c403444031041c060038165903070009035824440441082d405032070810303202c40b0a0316084001c0c061508002014000082400340403020420845145070148060b5100b400210000b9241004c007000d080c02d603 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 889814451 1250 889813201 889813207
    0x1081e01060503120405090a021c0c030f1506110a0507330f0905010e10110a0503032a031014180403020d1e0507080c150c0408010c08010b 61
    0x220101111018409844500101d40151038600180c100030b00c2031030b000c9003208003090030807407458040000303a0407815540046203010b14210f40c81d01c00b000c01c202c0000904d916100003132440c51090b03110300c003c2681e44100b0080d061200440f003035034004611805001035803e4010803c0f2080104034541b40c80c0c1d2140081440c146000f045200300c1208441c042401c90000e408195441110700b02c50991180355540c421603c1d1050ba40500050095000a0304110024120341003507150342c0324811400d00342e070604298021a00008a1034048100f10041c0309000c0402132000c0d54035040800700b0500a400c0b42d5080c410201c09030b04425000441d91407002284001080020105101d01d0400803007018210207807410110001c400d40301800d55040b001a0305c142c0e015040c2e182d00031010014500130540e4511070f02d025000081207401124000307441150002552109100308000c4102c0303d8161100e566168a85000100c100d60480e1044011550030841b45410480c41008102d058890003407440b41 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 889815701 1250 889814451 889814473
    0x5070e0f0a0518060a031203021908010506120a020d060b0408010b01030209090a0506030c060403050619020a0e09131e031b2004061a070c0801090201200a02090c0306030607080108 79
    0x43d8216003d070540d1303040040400c001c00800d038061401c001c1c10419480150b568000d6916099075210ba200c9100108480940188215518101150f03106a0108140e02054440c043c4001c0244500c1000301c0c1031524109000803503864004c09031040700c404e04005c005040020006506a10501028a5000c10600002117403c1416407102e41c100002504954140f01c0ea280454080d80c40b60300b040c0e42c5503005904014034190300c1003141d2502600c103041035050031034001003e40b204100d041d40502c9141d1803030020f01c000040c002d00d60301094206195400307000941030502400c03800000250006681054100c00002c00c0322480d4020707507800804180c2c11101c82030312005d20300f80e600340c40758400e45801c1d001465250384220440c3c9154111640c9540d10414a4840341100c03850b0300c1094164109a50700c005030b07030010242030340c200e11018002662100c0741e00c2d2904090008500944c00f00b81c5405006010703c0d0000a144144e80581c00c548503510384020a448030042407040d00802c0d0b1007105000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 889816951 1250 889815701 889815739
    0x80723150310051509030d09050109141f03060e0c0c0703140c090103030e01090e040b01150c0c03080a080a090c0504020a11061302010201051803090f1305070e0f0a05 73
    0x36038082c1c1c40c400d0403110980c5902c0040c0c040c0c98454907100c034803040801c1e010150301c1c06101246601c1070034104000c00c20300c2c100020b885891103204000d002181d00b1000092603c5040155504101e0346206040c8404281c5001e401450309005d10088542c0c95000600c0420480c4100e0341420b000b0401042100e19507a28039421100c1d607601e08160380a05610400d1646079100b00d640a14030a4441000000d0814001071a000e182c1d4008150303a1450014480440c012000e00d030306580340007040070301d007e0f0b440109462942c0b14040060440704850703070000c14080d410002e04070044680e95486030b40c4d01c03060580b506071609454042d1030214445410010341c5040e9004048502e0181014003c1e0414900340e103040840450702209079240c0902400e086603428407031658130a80d100412009400c140c1c0d130081d502d02400885030302800500981008941e40d00100700561242c1d08002e0200e0f01c3e00703040c01800a08101411402902e007400c50340320342e10382210300b042074643c007515002448004072024 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 889818201 1250 889816951 889816957
    0x503030a090e151905100f05090d0c0e0f0a0b01090b09010e0f040216050d0305100e0423030c0c1c030e04020706020705150912070807030e0a08072315 66
    0x6208804440318490300c21340b01d16114050521070416452400340c900030500121160703550300f038810041d0300d08050300c0d5503030000d003a00c401c24829110003c00c4100c528044024422903000074001410781404c21000d1a18003040600c21551002d00740a180100ea00650b0503082d107001300700158405000805503544101480084440d00600d04950002c91202140403684102e00000060300100404014040308000441c1d6081183c0b40c100001e280003800c10294204901910003002d08500210301844400c07004d060750400c10400e1003600d0980504080d03900d82c411282d44455003c1c84400a081d450b2041e40f020f0b40750041c8240c00ca401c411903804550b810700d41d4514651242d82403041c2c01c041030303551000e4844584100000c0400c03504076544001080001040100c4952144450340100c1c200c500564010f0f50b441440b40744c442d25540b40039504400c8604d07209420121080c000541480c000032403404482041174040081c01d5030543d80408020f810641c2504901d1a1002d85042c0c01d0301c0000b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 889819451 1250 889818201 889818211
    0x509070806031c0306062007170a08030f150108101205120d02070c0b030c12040809090903130e0903092202071a06032a040e060a02030a060503030a090e 67
    0x190b621000e540c2c0e82895181203c0c09141c40001e54802c0300307018064000c1505500e1081c0100040c00402410407256a43c1200780100c5003c808981c40400349203404000301c40d03049030f0040f03c2030345a181048140361900011560224000004d0b0900c03603042d4014000b00d4015241e00c1d1f04514900d082c42c81030b0050304074041c01150300c1d20a50342c403200b0549503000502110100300001513a126103d00b031050003486a900915040241041070129200c1b0101c11161003c3d00c460f00200699903d0034001803502401e600c43d074000d40c1750b204011510780701100406c0140e011300440c0e6407154454480c5041c0f41811500001560b000b00000d1003246004401c50408402203401005855180380e0f07480281d8100c2c9000b113513201a26844141c146102e40541039010000383d00030082802c1002d02071844034161000c501d85910b4960444209894540005040c5081e1804542c6142070030f4003503400035481114068043e13850150040b40614000c421a4544500303540d032580080d0a000302a407000c507000e05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 889820701 1250 889819451 889819453
    0xc02011815171e0618010f0806180309041508150604110a0c0213110f0a090b070312111e030f10060f030e07150c03270e0c0d0905060403020f07050907080603 69
    0x48418030342c4014121710b010f010300c800805061498110140d141030005450500d011140644080280d5000402c0d03070101d8038201d0f00451208010f07e0829603401c5140c019002c88d00a000c07245400a5040941d84c2c0110b0040d68200881036054002c1052030207151800c400207031402110303501605c2c1c2681340744244000403000191105d0000c0032085941c1c07007807141c09020400410300908041c1c00c607822400500c2251096458103815640c010421807030ba510398080c2a80d10400580181a100181c0d8603400c5064003c0414070190030f40c8090742d07081103500c6000c10280800040c0140c850445480840c1e8072616a003c0c2407400100c03c1d00031f45507083d400500c6100d8070800041442d00e103c0c0c01c4c81098010389840c44c0346240d40c14003c0c50003d101703420030001c007655200b42482c04d0b56030f400c0704100c41304125040c032603407183c10040c0311a101d40d1200c1e94100d0305000c0903405010021810301e006a00c290210703071080c10022110f541baa20203105242d40300d01002c00103a03010b40600842c592041d0024 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 889821951 1250 889820701 889820719
    0xa0b07110f1936090f06050c040302040b0f0609060307020a0b161d1309031202030708011e06020c090411101d0901080a02010c02011815171e06 63
    0x100119204000440003840c0c00888007000300a141c80415003440d985102c3e0869654442d14503440d0080244600c40046990b81d889582d40203010302c028000300304aa0089043c0010b00b0300020754540c2c2d400c107000607880f581c503281c014900c0c0d19007840550750540001d41098142201c0c101000401d4200030599030540c0940c44034500021780e40c0044912410142e4030102c45802c000750020316070421100110b148110790910300145035104c00c0250703107030750b60b1900100e40f129aa01d4112000d5907810310304001240003006112105810500c03003410389030b0045603100051004481040038150701e00c01c1320003603004004d151005081184e8001d5005000300c4410300b02210100114503090000095000000c4489600e4100520100b09404a50f503044868510035410508074603164506420028184200145400c0469000b40d070300c071040301c3c82c610342e40c02304564850707000005e644448040300000f030b0703003c958080060703201843c64010310704500b62116241501761790700a007000150540d0780c860100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 889823201 1250 889821951 889821979
    0x1e030f140a0503040608090a020906192102030c062b092306180c12120a0e03241305012405040507020c0d0305030a0b10020a0b060a0b0711 61
    0xc002007019544202c0086640342c1c5010070080564001a00780c00d0325130005441040982e4641010f0f030b4010400b205c4e902c0d0400c02c860220b2040c04055480300a00c5040c0c51000e1004081d030801c800040c0d0b001b070f41901c6504082078200701c1c0920401070f41c40010f01e504c850382c1410290108115030301030411980021451040d460b00e181a6020a155003030800001003504004c0a0070b10900d6080300c152a003003221f0240e400c03d21529440010700c81800b514612501c20380303501d020041c1080e00d01840700d116a039a50028001401a946100300078043d03c11100c4800204100729150348004510350010307045a2102e0980048003050b409007039481390b48070710070a541c0c6080c0300304400c158640354040c03441880c07608003030009544006240c07400b55001802d1200380c0b5145c201c803101030b540c1d052420b1139aa42d940c000b15402490b805402d00d4201c40000c0245c000c090300020404ca00600440280b00681e8030700382001544c072030b6030040b00300303040081c00a4400189450040c00220000410a41120300c0e6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 889824451 1250 889823201 889823203
    0x3181006090c1d101d0a0602070305150c03040204020c01090c0f1403030403082a070303030e0105060a030c06030216060509060106090b0a080402010c08090a030305131e030f14 77
    0x6030741c014861003603980e4003402c48981c01046482e0220080d50411001a5943c4005243d0032100e0072480140100c030345103950781c1168107150800211005000040941e21400025500c3d04140011640b902c12596044203c22405420390711030381301490030915660b9550300707020203900451200c544964035450f612001440c20b282000140041d41d04a8035a68038010400f00d6440d45441ca05004e900204018000300e20b07002d00301c03003005515110130390a03224011301207440e204100c004100f45002d580c0300881056456027007546541403090081c0540d0301c0b0041000212411840014007030100d11404001003406900600a4104852208030340002282c86500503036000300d400044c0c41c0c000700300600c02c440e0042c8a000141c0909644641410242c0c0400f810050000c0d001a05004502c5440c0c020408a00c0480350841c2002e4098522503551b071030f01a00780e070017119042ca107600ca001d001003a00322a6507403600e40c40e1000b00107420101d1030340d100c00401071003510040e1403001c100031460b540780c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 889825701 1250 889824451 889824461
    0x31b06091216050607020f010c08150402030414010207080d0b0414012711070b0f0c2d070b0609151e270f01050108040f20030d020606190308031810 65
    0xc5d5a40141107103010001c10b06084a280d50315040600c1071031801c0c003542d8040c60603101502401a100141e9076100e42c00c181c42d85c15108003109840d50300001d0320340c04228006000d866003110300394082c891200180304000c01e480030910013030403024a202c0100501e199100741014640046481c0a080d244a6000901039820421101c0c4100d90006240d108001c10044926442400d18901c9015400e01c85545404c0c0d1013100d03500980300e500b030007540e0307220741040d0800d43d1070140c00000160f40354210310300340714013044c110f60052141401c80d0000f50f0200382240c3c1030816500003400c04050f2400340c0d03140501e54001c3c80909400603145425194994400380500f01c03013800001514406d40382c003076040c00c1e0303600050700264100301441302440006140d007082c0f1030f070a075404622a8110b150040c99640c00c021402100c85d854400c140d00c46d09a20340201c0c1d1180034000580e10503000341040324110044039280d20008044840800004180820ba801c0040c403050303000c0d099481d03039945580d11405840c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 889826951 1250 889825701 889825711
    0x120b120601050a09021207050f09040c0c020f040c050d050a11030103080408010b041b111005010f0305070509070f0f09050d03080105130b010801051c0212031b060912160506 76
    0x68030140c0180150f240036407a090091804000c10351170048560302e00c4c25440c102802240900c00c0216801200003081401c1da4514800500100030403510384a00030300c1d481c614081a0301940c50303013080c5881c1d0700f000d00444110082c940c0b1001d1a044243c100e400080c00f004101d04c20707080c0e44420341c60100303025000650095019030f1103291910700309803c00d801c681c1078481d19841b840c80c0c60050b1440800c0f0041e1001c03200894280710b03450003030400c48542040504d200c83c202040c54a800425400110421f0030241c03405001200c1d01c107511007050100100060380d0420105085e03611a180040c0f19415811030021945002c440656a60f0045040410006800c6012904440051245080c8a40061403d070403070740c000d0142400680001e00f5030f00040c014507004002e0a0640c031910243c44490811907640501a495081e589403601612900014070001718501c120144030480400000e5090007135030680094002c217802d15100822036400640c40f080c1c0184080003200201d00c0c140401c1c0c4c451 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 889828201 1250 889826951 889826953
    0x3070e0f0909010b01320703020c03010e010e0d030b06031302010504180f0b090601080c0c030408100501030c0b1c020d0b06030723040303170c0f030a0207030e041b120b12 75
    0x1130342d0900024041000390078110b039240c039124040d80320040007080e1041c0e54911a2a17210ba403031340c0d182012410062007500094245d030906503240d182c038005612007260f2554500560301c18a540b003c01728196600c0c0b400007544400e0034070104052140d8200742cbc3c58040d10505002c0e203881e0340d41b8958420b0003040078120306400c0c3d8807510441c880da154003e4520203001120404424a000400a00540b2000d010401907401c0490841009072041044401824000713048a0400c0071580c1540003426007400111a035140401d00041c080c540c080a030b0300d00c0340010f032402d01c18200343c1c4c02500003504400c49820482da290300031311030103846074402140100e0040c2d07240180c0b0520300d801007149281044407080e84140c10001040800c2d03001a800046001c0303130301c01e41829190b04e0f407054468000d403000007010000000c18000900c005030300405d480c038032944a00c031401102e1010071080340c040c05051103403501c4e04418500901d104028503014048156000240c9903c0c2402140240701c1801e820141 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 889829451 1250 889828201 889828211
    0xb040506160b04030908070b0c1e0708030c0f10020913050c07200f01020d02190c030b0106080124050703080403090b160b060a050d030c06200a110c01020303070e0f090901 75
    0x48601b00f0301100001e070201d2402d65243c1a4100810703950f40c1541000b151004070303046000450441c05102800040640307004590b01c0f000140100f940f103810821b8901c074a4400d006031403e07015060f0094400208004024804125001300183c000e0480240781b100c6803401006030344005440044901c00e441801d0158640c03484001c0c00b80108a03524040d00d50545d841803504207a255400510303130070f600e940200c00c001d5805440c1783c0105e48421503040106000c001c030001090807640070a205049901000c001c024800c503858104540848442c00035002810402001011a0041e00d500e81c01500c02e02d09001c905903150b40d002e00d1138000c88000701c0c0c1c03004052560028441140c1c09150040d10840382c2d0386407685013000107a1503900f00f40c80201401003a003410000c1c80301d19408400d80026202c07503010703201c544101071041a8000405540411840107075900c1a500c005480c22403400e040c0c0056145441d541401d0b0b484030618203445034024104262040162550035005008070392070000855 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 889830701 1250 889829451 889829459
    0x111010e030a0e040f11090d020307170d140a0f0e010e040c03021804020f0d0e0a211b05060613021e07030e09040f110f210d03060b040506160b040309 66
    0x8141c40701d400c2e00552007410820f040311007003401412507e8006003190881c0750303005d070351020030f0400403a6030181820b40c002e1305059105a4011039140900ca80c95034a000584680460160b0b44ac050091340714001032480c2466446580614888004500c05042c10104154081d0010b0151103a4044500000c0d4010600c400e90740c1320900210010401141d09604100342c0d441d6001c0d0303038054285030022198482d015001d001c0000d0007025001c40e002603030f14007120611502c10640039262002d18001031000820100d0010b501c0710f0341c03406c9a5005014121985030b00d800c100444171103800c1a101594200300e002d003007509500340c90200d4240010065140c2d501e50030050f11260f210f1a12138000e00021041100150300c0c610070040f1301d41c2c814651f00b0b00a441c01c0128030100c00910040f0b411400c44e00784405420318192020f1140e2600708229188820100012810748a10317125002d604a001e02091200b0314022001d0303c5d0b06400d0324a4120340e4845504d40c001600000e44099002c5048240144 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 889831951 1250 889830701 889830709
    0x406021303082106030309031b0d1e2d02040902060405060c0705090627151314060415030201260f042001050405040207170f12011707050111010e030a0e 67
    0x2031303010038110055814070303a551000c242c580e100e420381c2e4001044a140751341c1c40d0382d9a00210000701030b0005216420032401c8030094080d413034110b00945158400b80310400100380c0c0d4078076402c0000740c8044200050b9500e0383c04d11000d0300c410017040368400c40078400403a103070b22260058183c804040c401062060314080074401b4124000d0451405040c200d00003200015004da449258402c002040c5100d582d100c900e000b1900c0040044903921100401601c80560144d40003c1c0700300c0c0caa020000b0417a110101003200b2a4000780025031103a1102204002542c010892100c4014580301d4648000c03c80111703400303002c681200c801c000c00102d6402e00c0107100c3c4019044005c45901d0448180c40a00040040c00600541c0b103130754030036500040c20500300a07003420400d13010b41400207141d0b103031b10000300d070221b1340d41007802c103008100c01d01c900010782841544e9130740c98450341c0300024210440c2480011202000c904016030a41e40d01c1d030300302a00911040000f03282c80e20180d9140c000016980e8200 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 889833201 1250 889831951 889832017
    0x10306150224010303050403150e030d0b1003060e061309051015060302031012020f0907030204050114120a0c022112090c030c010531030605071403040602130308 71
    0x2602c141001c40700500009400a04407000d5036013059650421211025250300030b0801e5003a4801c035400003140d803007000011900242000328007217984c00344030350040134110f08441440c860718152081c12804101c081c00e01481410030215840301c0420166140c1d2107083c0f901130000a8070400c16078038a900c0b000c40500500e00c3c0f025214601d42589107052011511503010780a024000491041c91160811540c44a80840c0ca03103101400040191400d0040980203400500c609400b0038030250484480d1030301032017280e000402124100c4c19907110000705400400c81103d81006522481c0e0503c0d10f403141d41c1407440c4d8561420a030f15039459010000d0b4243c1e007040030b007061100c1d070304c44040d01c6011744d004669000c00050a10b051901c50450150014120b2000c5e0003490a40002d040030320545030300c60088005881c0210741c20300c0541c6070807a0449203000300d02c1844011540c10701c08600043d0440d0000d1402c49628241140404d8481d10385840c19480b150000001c05110351028030400c0c1040d0030303 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 889834451 1250 889833201 889833253
    0x70501020d1d1206040605180c1509040b120c03010b04060e1810110408011a03060a0e03070b010608040c06030c05040504021b0a0c080606040501050a03020402090103061502 76
    0x5030003404800800640004011001c1c03080b4007607140e884038030740c2e11584002001080180b044801c3d5040c00c0c20301c1c40c000e002c203803203242503030906100c0c0d800c1c003040000d01265405c9002e80b00420364500001900803580260301440c0e449600d0300d005032820b5988120841801c1d040002403c0c1c1111007070101421100340005140c040c40c1086000c00841225107101940107031410303025948a00c1d070301c0c103903400c000d02c0c1c0742c0324032005142c40f01c0211180c1d4104090002d40320258000c208a01c2c444218141d03600e0007070003069040e80105c00148105606030030444d00d804480040300c2c1040700640d10800c0450098200c01c00107480c0204000512010503804801007400341400c200154000d44001d0061166004883c05241c00240071003641805c603c000710b40104060544000b03140c4e07494030702c03000c12952007854841c1c451703440420301d503107400c0c41158103e980c001c0c08012460300e141d090201a401000b0f400f410b00d0f0b541c170000a2604035601d01c101c41c04216901600041c1007a96513000d0314000461 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 889835701 1250 889834451 889834453
    0x30a081305041a010e1906170108070803220e040809130b09060d0305070618120e0105032403251208030c0313080409020a0f020a150e03130807050307050102 69
    0x1d010282030070125032481148020310340903074a5000000400c200031010400c0c50042c6ca28040005a0700b40e210701180d54540d4010200180c0742d9840058990b91140390103034070301a40041040310740c01074040c0b51845451200c5180469144d130b4541b615045100200c5040e0360a030000100300c1d00d18a0312039032100c5050130342141040105a02d40202c0d08072400146244d0040303a13502204070a00d80102d0940300a00d621101c20300110061040040c0c0e085036110045179030001d602508240c4034001c82c9448400b460680da901d045603202810094001e040300340307000d50040c0100c1c98403207030b0f00c0901600202e100d00c9142c442040d1041c20000c070007070b44036912044609044844c840c000036041c41c01c481d080300c0b81ca4115512a01e0f8a1042d1201d032030300203070040c00401e0001303000450300300a4024224500050b140d00902c140100c0f42641c0343d280408006140c130f40310300c00200802c015035000320f000001a508590501c11540200d60058005030041138091b070140c1820401460108040b00103054284 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 889836951 1250 889835701 889835711
    0xc031b0c050703060f020d020d0e060f0912031b0c010606140a0203180a0f0305010e01141e070302091302130603061a030712180c06110d05090609030a08130504 70
    0xc1c07611a02c410440c08001e2503207840701e00307170415080f49405403620410035030011581e1341c0c0c1c003070b001c400100071a541030849401540300140c1400840d01826228100307200150002c01a64000c20926500040c030b054030004503900b2208031010742001400f000402100001011400c2034070144ca8122016141c03080740d5400c005009400b6030110070341e00465120b418040160800320300240d010a02078005c0c50840e6015203000040c844c054001005001294000700b00610541c12540c030350303007c1155202049200c094003503406104141c0c1072035016009107401410000700c00005150890711140d001c0b40c0903004280e03000310002401060000780014142000058600311051f0704030310042141010709a00400000d4030350b0b01440410350b081c0d40e0b001042007800d500b0302018941c0340703045900759040d0220310070200e940c600481102107401a050014861000303910b008030380075486203549603000034080c8260a11600c08004102050344504521910303450181680a5890841e620140c4114100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 889838201 1250 889836951 889836953
    0x1d060301060215060f030f070314060103020d03200619050907050d03120f020a081e0c091009030b0901020703171303080c160b1b09031b0a090c031b0c 66
    0x1a10400c00501102c2041d0303d9a50100010080e1901580c40d41d010300070041c20302000d00010078020156842800d007485415548980702d0f9a800b0240402900061181316000100b801681f200900030780103200310703099003010705040b0305103101550301c5140c140f1220403401000c0c415000d042c1e408444c030401407809519240000356203c80740c1c2805014020b114201401200d0303681c0002c3c040c50754405003955074a4400c0c2c0018001c1504480d00784420721005c0103040b454403007902d114001e01b0030705101420030025104103c07032081e07500c2c440030500580c508000700041803c10b18a200b03e4140c400140c4039455800d02504c21080e00740c84c000c6001044c020807040142141142c8410341c0c041c9046104c03565020f40b502414420600070307040700e0550805002c01c0140c4909020301ca41d49100031013503091300c8481d0914143c01441d0756030750700d82c000300410030030001403802d00d2003ca0b4005020841d09176840b07171040c0807a140c4c81c0d010000203850780310900682d20a00300400d140e501c03502d080e03420440340b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 889839451 1250 889838201 889838203
    0x91a042f1809060303041a040306180b070e040e07241b0b373b0a0206030702010c030c0f020303070e031606080103020301060519210804061d0603010602 67
    0x7aa91100c1c4200d2480e0082402d83c0c40400070381d00980601c00202e8000680e2801780c2c1c0444d04181b008641140c1400301c0ca4001101e4285580c0d80241c0c4500401d5a60300c80101c161150441c4040594125982d01008102404c08001c04c238020701c019140c15251408008040c0c90580c41e600f00f46084c0141c52542503900c00c00c15501002c1c064201100c034405484040140c01c5100e10540c604212483d03400140700741500800348200c186080345000c000040c0c00502100582440e00110071140040d49600850040c0c1000c003a900b14162070700391908141d050f0300140c0550820356403040143c5d95101e812030346070340500ca0710201c981036041441c650049800000d60301e100041c100420841204c1690071180c4080140c0c48041401c10081030701e043e203443d4024505c2c1024402a8802d44c2462000146414910700701c403001c2e1962030080201605003c041e00c40c5403868401c08854484a00340e0402081030341001c3d001804107a51141d5175105104a00840041da050038144104401c200402040c0d030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 889840701 1250 889839451 889839487
    0x1c0605030a0311070e070503070816020703030507020303041517010506070b0a0c0905090703021e04030215030403090f12060c02120301410a06030204050a091a042f 72
    0x5814507019203c1000b21000078104801907020b9411401e11a05010100c2d400c50701941c4502115a03912040c1d036104100d500c0d05520064100001d03070007802d402c2c0302180c4100c004208890020341182d00e401c1d03640c6441155141025462000101d0303180d01d8003c001a0340d205140100000c407074207401c2c00000d4556a40000000e809180d8466942003e049070030f008024480003004020f160100b945444030b0047d0103980000082041070440000ea401c0c92480b403410340c0d0071341e078014004002100480540e241164000b4006070305001086000060b1010040c0440c405002007a42c086a40115450108242c030f440310740d03001c01c3d50000440e2800232881481900d044603442905a040204a140c40d00d400c0e060112880c1403480704000602d5610700101c00300035211100747e0343c002049960300c1c802c504034007880c05155031201c460301c42006400c401c4e41145110000b00b81950907485c260000103812520301c1008010103041045001d86110000445400cac940303c22805145415081c44100810031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 889841951 1250 889840701 889840703
    0x14130f1a07080d090f050a030305150a03050304030b0415020703121407080a050a090204021908060603011211040608160602190c090903050705070305011a01170622020406051c0605030a 81
    0x59440e0782c104140400d101500c00486d4000301560021407083c01c00a001d00001c03155001d034421890324281d22820800e8010f0200c0b81c010340914103250865460010900004cad105803050440160620134000451004040e524400c1d154240c400c4584c40342030041c0d0707400d08403440d03100207150200204203800c290803a0748052021000a0ba40da40c004440009140c04074019400c6480403910b50142400e441c40d5802800d220f448106036580c800042002c2c0744000d014008081e0641d0140e070700003414174140d00185040040020500302c1c1c56034006480c2c181511400300c203960103c80c04011a54042c401000110103c40c02100140000c0c0c44e0b00da0900003d04c01c100809503103000320801d0502c99015240345551200548490564a0070901d0184c120342ca83e650110108214042c650341c0540c0e8200301503c4031051014450b41d80904000c1510840e00842440969015942c0c2d18031585100801c080c2407152503032621820b114840b1884d120324004a01462468894240956680012024642 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 889843201 1250 889841951 889841977
    0x305072405120a091b0b090a090905100c0e1203030a15050a1701060308040f03061b0e0405090738070804150504030516090c031b14130f1a0708 63
    0x14861900e803443d0901880310000030b011309903040c0420b16061b030300014801c010f030868030f40d41d0854540380f0407011200e4180005040341e0000c4e50300c88511006800050716211141000c10300c82c030000c0c0c080f40100080700202d824a400000400c201d202c001d2060b20011204854600405802d080200c2e0400c049030290800700b402c0d1010544a0300c40075080303a005150b102c2c0c0000d4541e0f5913420280b1842401d0300046410034100f809442402c0b40c1d14903148032441d00c40d903943d00d40b0240c0400b0322000f00009440c0c140103005048011903914040043c1c20303d500021802007411003500a0b4030300000100070030824a4280411001010545c44420b036003e540208180c0503101c951001c003500c1c1417045910003410742c010080040d055041900062044441c400c406110550581c00d04500326016001c20368088610348600c480040c0c07103250616400312907041d40078034244e0b0500110440c48115488081401c000d043c00780b059003c09602030300c0000f56060260304003130340c6a46000041c007400c5031003c91 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 889844451 1250 889843201 889843211
    0x10031104110906040f031502090105070204020f070f0302030408150118020306031009050102040f05060915090402090a090506010908070b03011e03061b14040e0a0504020a0305072405120a 82
    0x7049015011529034036002024107589558960000301c03010300503c4141c80300d40c0006120825458140229001a42c0581d50146807032050390800c0000e400c0400c40501c00c07501841400c00103240c28000c0a055402900255103031480c00720301d02d1400740010448108041c980c00100300314008a03154050b04980d0400140e00d0f9541c51010030b02d0030740e8000c40111214105950103003405010760041064074280400c0c40721041e16002031010a10030303c152260403040700511000d2a14583d03020701907000d40200003503c0c2c07003114000a004407050f9004818125910002d0107102d40e0041d01c0358000348806800b42c4a0b05107091403029171804148100002030042203d140c0c942c0c908180d581700595032140040064030030b8100c160740d08c1452000d0500c0410030600c4154207124840040e0b130304a80240c034104a45540d03880b400005010090701c101c1c0c120b500408040005801400090064030000041c40c28040c00d81e0906440e000c40c1c44007042c03d0101c100803004000303414002e481c1d4012224800424 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 889845701 1250 889844451 889844471
    0xf0405010b09010906031505070509010804020109051e040501060c030f0c020307270c09080a02040207080d0e0303150619050901141b152e05100509010810031104 71
    0x1000d00a80340721140c0c420b160000100c0c1c00030155001400307503030044061007080d1110360b41c82c408880d4103070b80040c08200e061010003040d40c41010301950051062405407032460703032000804c041d00c250601c084014444102010028181880349500400f60782c50840d103041d49039100507098106681c8a841080901441c0c8025514104105401456030500322180c0d02c1c1c42e8400e2620350714092043c2101141003107010221300d41b0503005402074a000c0c9000e0700310b41070554200300095000700c0089a1521007406100080002441050400408c1d18091580e80c54080d00718421110b441214a1140400b0f1215400c03c0d6800380d0031158643e03881c00d09940e1a8012070040c2c0d40381504030010410400c001406c096980707204608400c90307000007000c41c1c2038a01c8421000b44c401404a400311407401d14962441000204404055103a40f000342001100c50b07150070100c1c0108240340860004580c0020b00ca1350030756808444140c1c407108440080403510705582c1d03034582c07000d00046414400c0340c42f090242e0f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 889846951 1250 889845701 889845703
    0x151a0a09030f0b040201030b121e011b0807090f080d0c02010c0b0a0c0f050f09010516060c021b0303070f060c1710050301050702071a1c090f051c080f0405 68
    0x400603541040480c90340101503d00501c50f508100c0c1d08a002a080895507011070904c040603408020301d0802609000015040105000681e112602580d6407260341400d141581041e040d0992041f5688449052034064005010a40c841d072043c2d56080c160102007002040204034581a0300c03c40c600403203500780c28001290f200c41d05d40809010741401c0024008002580d1f88103500ca10b0450710703482c4a020040e041501c460140c007040d0b400107282009102441d601c100c0c020824000c810f400301290a0194076084100e400300c00442d4003507031007466010042c1e900d0f021901c607010401c4004524104c59a0340344032890030043c10083c005516a070800501a00602a03990301e004041b030144414542110b0f84405034440341314641c001e520307143c04507010903c0800d0031410384240040668010a5104030309007642c0c418140090804000800022105264040d040410703020b0100780c01c100e41c00d400c0040c01c20203170703909081180061390602034600303800a1009c0d0f40640c00d0402c524503076441d81882 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 889848201 1250 889846951 889846967
    0x3040c0608191803030f02070809092d010905010f030201051242031c0f020a061a032e020c030f1c060609031a07030e0105010810151a0a 60
    0x48034505040000c04240c20645400000183e4020341d4203021440c0701b01c000000328400e03801c001d00740b04410030100c0000e0030003c805a8200d5401c525505051558074140700e00350200030074a640040c9040700412010a0710f006507400341c212210744114040c03555001a159104400c005084600c4a400081c0070400c003c01003c45240340c00c2080000d04100b030010b03000814404942c0341c0d4032010302d613106018100001c560b0107000143c061200404084201601c2080c0480604021885100c00c4000090454018135080703e100150001e4002114030425003000325404401030542c0303000c5041008011203030313035908170407521000040c0c0d514060f1110314114410792120614451001805243c650701114015191814045040140e17646a40c403c03103c0c6179852001908514040b01ba9100c0040e107408415084070041c01c0004100c81c4180c0c0c000d00b0756009a203e90207940041d4181940172503507005400c03d00080b0504c04c0039003402c101e002020079070843d500e41650740c0d0220b600400140103141c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 889849451 1250 889848201 889848241
    0x6020339030d06030308012c04061b0c03020d0c0c090c12060608010e09010b0a0b1c1b02010c080f010b1608071b0506031302060a03150e040b01080303040c0608 70
    0x64039500c42c09444240d001d020b1910040700001c080e00300028a048104001950415095226242c0c030f0902400f51004228080d10a45480b030b40c602c00c0d043c1c56083d0a041c211000819126070103075028504019081c10241c0401e401400140f4441e0400031f480c0c203442d60152400340000040314100417400300c5049543c903540701e28203480d0400c0403a00caa04841c40318100e0749821111403480e65003c00a03401c0c1c5078040c1e0110341041180f00306208014104010781078001c24000c0024108000704001030507210810740d60b2400c1c80c607207007001c40d2660f4280902d002806130340c02c054406042a400c2c1e4290003005100f40c00b4010b0700030410a007803091544040c03400c56082801103455903124148121203100044114407080301c90900090346050030419a0f01c1040102e505600c140015024042650f200000d00010903685048141010b1030312071144014003140c03001038610340f515240c110600c02061f00034041e1b0307600600030030000582104e1600305035010f0b442c0030181d0340c658101018400016800d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 889850701 1250 889849451 889849453
    0xa0b062211130f1206050402010309120807030b19050913050708061f12020103200c0a060b31020f0325050f040302150705120a0906020339 61
    0x4118400c0c1c0701d01d40040c0c1265000304041d680100c0d40c0d98070018084085101d00014241c009481002144036544001e81c05170042c10302141c3d00342e066132019048882885158041038031201449840c91b414030906410450540c0c1c51407040c4d20b4903441d4100340070070f80b160501c40d0403090002101c94800c00640d90b60f82c2c0c1e01000f00c8140766214203003180c0386d0b0400c0f980803002c03580c002641070050098403d0082103c60103a10803807024016001180a4249400351102481103850000b404000354001044151200c030050a000030706072a00c0030986d0540020719200340311040c03c804040d03290300c501c00041c112000c2166200201c50324004041d028103c2030182403040402042140028022801010710741018011548418507209035507a020703802c1c04c1d00c84440148000d000508261200c41c10036410398003054108111940c4440c5040c0c034455052016a901254101880d80c100d07080102030b000c90700207141007820210082020010750b50076201c01c02440e000e1540d88000c007400100d03144420748 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 889851951 1250 889850701 889850711
    0x21504080a0506061906050307020f0d0509040b0301020a0f080901060e07092402030306040b040908070f0b0a1a041a09040605010f1406090607170705010605120a0b0622 74
    0x1030303200380d2200c129441c00d0310180154000550703245084c42c106015240e04559260180b42009400c4510741c2008001c00f05610540c9018032a800d410841030884d00b94680c0c030070365252043c00074042035032aa1007813980603a0040c0640d004a035006090401a000e540c0f500c0c0340641d80c0ca20400e8090100f13a40000325014551081c481c107a5441807601c0141c84001d0701c02c2c0f020050303100342c0040c1d030030862000400523002480031a200d49416003040d1944a0000c1c80400c0213800e0b521014402c2c0d01000040b2008140d082c03002c2c041060741c14035241c1c00308402c202041341e42c011001124a0303c1d031040780f4611a07a9518002c1201a1880010101d48100035040700304030320f014a0300320700820084c02101009100400d00003241c0549004003400d440c0d010380310b1402d040410040c4103180d0002c24007150004040c0040240386446200a4074540e8060300010070a6072600c03041c40b29060b8a0340c5068aa50402818000441c030240503003500004140c50a03880004e0610b801c0b207071341c541e583c0740c065042c0c207103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 889853201 1250 889851951 889851959
    0x110403060e0717060f220813090c1112070f150902010230180d060c090906031e050c0d06090506070e030d1b020d0305030406051b04050904021504 64
    0x54160548804241d030307481c420140d61099607980d030200c4049901c80b00c03080025503c54110300d01a9035a01c800c4281c00c040b0700d915580c840d01500158034031b5023000c000500400001c0030902030501004c0312070800c2e106c1810700030f140c0390b100c088c40c500c82d502c1c000c800224507007084011005a2000c0750170920b204480031401c200c95026000002c01030740144194038000c0720190031044449070022041b0500700712450350084a48986c0c10104054040c00424005034000f03813070700603402411074032900c0001a105141c0710081c01140e90340d0004c8140b503262640a00000382c101c0810300318080101d2000b06010a42d140851900303640c0f030352154000444181007010420103070082c00a0b54400c0f0306070342031a030b1428811621410f84240c81c50b49030b40100c031a03045640c000e002c00107000b00404440e40340028580c02058070140851421800204001708020620107144980c580142d4400148560343c070804140f134071075004500449120740d9520005c01c00710f54809103501d5000010451050310743e90380e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 889854451 1250 889853201 889853203
    0xe0f180a2001121527050c0c07060306060c02041d1f0e0109080f0706140103290106120f02040e0406050117010e0303160c14060912040b030a110403060e 67
    0x5442150200b004244443e42c041018065608840809101c1d540168034103d4407684002d2018840c0340000e9200d400c00c40344600d103010391031241401c0f010f0306079031f0904800303600c0c0340210650040c020180341a0050210741d40c42491805d2594040b140031030030040b890751032110740c10a9094001c8500c00c11411481c1a01082e520710300300f241c0f4243c03c206240b103501c40c040c01d035007101c440203000b003004012000c1c0c1881c81c1d201410185000e0000010580c4080b1074200c281202a0401d0351a0803080d844200b040e40740c8402000f444c0240008010760b94541003001d0305100761480011f0720385807102010b64548000358141c070000c110180d404001d0707040c6400c0c8a401044280038a01083d0911034031300401c440140200c14003400a0401945513903540f003140f40a03030300e07071055000c104101080100302288802138501c00c1c4a0042c0054403290420481c01792074182c105031074840d203410a100c2004002410011350381c1c000c4403c0e20110307048010001c4131280340300750303040240302901d0011402c0001e18 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 889855701 1250 889854451 889854503
    0x80c1903051506040510030203041704140901060f020d0503090f010504060e0c0a140906040921030605030a020d0605071808010207020f0108060f01030b130e15010e0f180a 75
    0x3807070b807001d600c00200704144050b910940c000c180d0440841c000c06150315209a00556105015014288080d00c1688881d0314a522039030203416482d02c901320954203440c0041c5140c1c01001c1c4c40c200b04a8408511401944615a03002820188100400081c1003420305208030b600d001043c40007000149458a00080140201c0302846864460040700742401d040940501c42a40c10746403004614084400c00c001d0044002448140c02a8030744261a0010703907040281300c02d170b00751904c14202903d80c0302402400c41d007041e880307107100f94002c501034070150722200a054050364101a011034241d071804002e945528000f00755100c2501c5481c0c00040c4224198064807400740b0880c0c00c03d0568004400469081d801521610703486120400c03800c2d0198000d600078100d11901500c041c0c1e8003c03401209000300d8a620b18521078581150243c030482c00e01d1000c409007d0940120410147e08001c8506c40d29001e0003000c00c1c03800d682e0301840c28217410301001002d0059600101c039501c02e581c2007602481d586 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 889856951 1250 889855701 889855711
    0x321020912150702060906131a040b0f0702071809020d1205070506060f150d0b0909010e01060905101e080106091409012d0b0a09020403140d0f080c190305 68
    0x800ca10103d040306101144507401150004000d0904e501d03a071b00c07102134400f100c1c00d04483c42d082e000b40e0317900c141c000c102840340710720b000300e401440c81e00d400300540c00c0400c0700820440c11500985828040c03880c406000e11060403400f000010200218404140514000709000c0d100c40254054107910795030040042030224468400d595841d120746090104240a05c0b440941c406030010520781070400c2c40e80a480d050000c182c02081d410b044102054400d401030f114a111651904003400601809019981c014204a0010011032034201e1344200d42e1139030780c094205100500b8101c07a0524040d1080c07a406041d41500821a0781e64840b82400201a00480a14844074030000201c0014041c07158681c0ae42100da41540529440c0405003480351b880c0702c5040c800c50b518032109040b901c40e4105900a020318520040e56581181064114010604d0a03245260b01901c1d188045c141d00c1180c0b4480002c4504198603d51120f1b02101001d000382407a00560520480c0161503483e8103400440c054 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 889858201 1250 889856951 889856983
    0x6050729100e06130527072c010302060304020a1d16020a020d110d381b0d09140c100c05031b03040819020a0b070321020912 55
    0x1c0d554804485038800401c0740c002e0b50100c0c04000c00c0c02c0c0340303980e81c0000d07600c1000d03444d0300c0c0107500c0256000b600f440c241d290b072100c199000703034010b1016001240300704103e112108004070700c150b1481400d400c2c0140c1404028003441000c4041402c40d1911080b280152140d1403040305100030700d50440e0705c2d460003218015406840b110070300401d2400800e4100519030050030741510101c090321a5501544810315140c0c11000081214001c2440c4010500d00100030401c0510064448200352507030704e000380d10031031406c2048410700515000310007041013403100c80341c41a511404201c2004e0010528070704060301c5541c80300813042c9001c13804109150103c40441d4105c062801d400c0e41100c96402001c0d009145d82e00400c0203038142c0045c1d44a4240100215003164541901d610f0190304183c0e103c3c039411103030740c04101c00c40214036104e485840030b00041c008450401c1b00b20b460042c00d1142034030090220606c101701120b100207894040712038a8101620051040e0195034040390b0b6215502000d00380 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 889859451 1250 889858201 889858231
    0x2a022103061e130b15070f06060807210809040608030a08090102030c04090e0a0f081c1107080918090d0e030106060816030906110723060106050729 65
    0x40ca118042e520a0881e5018016201d0a0600202080140450208550b00c10b10300d070181c1c80d0200a000090407620f1103030004003081d030110300d000019078007550420601604014030a015940003070100703250303818400c8902c032031040c11400d0640d07075445009c045a40140c00d046002c05d042d14000002d054802c816030310346606139a003040d40c0d4201c0c007003035418802a00301008104540c00c0c882c0c02080d080ca9880c2c09032207003a2200d541d41140d400314040100d582e00c034007140f0b00c040041080d480c601c6400700d00d40d081c070000c3c0c080d0791a00511701c150b01008100f0000840c1c41a81a120311180d06940180301401801c0c500b40003182554490509031320b9400030785c114000b007400b03043c180200d8044a1282e11035090702e49030710300300719100101000c1000405a8a104e1070001c101c0e2400340701c14580002e140c00d5a90951030900700090000304c80d1301c41e0010361b0040f60b18403410002a58504645061400c291507003204d1800588255800c2005924041030554801c00a036041c040c0030700070000303418103403e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 889860701 1250 889859451 889859479
    0x2012120601020607120e030d0c18271e0e010f0c05070b0403081e070905010f0807120b04110705010b21190f0f030f080a2a02210306 58
    0x40e0f20302c0c04a0766180007030401d00005038040c00c181c00225140c80304200b503901b40f2801600b1401110382c031042e48400100c0940740003444e9400007004802a000c084500006000442c85ca0091070b144030025014a9a8401e6074042d400142041607034080c0e0b0220080c0540c5c2c0c44410498007070850022a000e0981c0303042e034602945406034049494455012802131600e079510344040e078041000800f280b0392120062a00745600c043c0440d054801d040b0740d10b8112049040400040000000d24010810701101070305100c02141c216400c1d8046508a138008503403500300c400814040c1c03c00d102080001900031a803801040b4064010041550b0161400012002000040d0849280010b030440c0142c10810b5600c000d800154010610280180c4000d246540e4070756845140403080170081d00051940c2c5020883d46038441d0310350360800300c00d00061003094061081030082d07111182c1c07600c00c000328581c3c460540c4c078000c2c0424101051480c8d02e801d115103a41c003034035410394000c03603040d0310a41c0010345007a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 889861951 1250 889860701 889860703
    0x10120507080f0a0c090f0204050604091b052107090b040905010515091f0e10080402030c0a080c09181903030609020f0f0c010b04020f0a02010e0f0d201212060102 71
    0x5015802141d00c600c1c2500d82030011001b040c021b1081140706408201c081a01c1d100c02009000500000c0340000e00528040d071040b410202e407007642c0d006c0200800c80c0790810340c011088003001d0210303c420700c2159260140b040d80d20285030340c0304003a611004a000a80c3d02c040ba402a8100d0300c007a100c100c07045064449003800b0748a134840e196485124103060401c0414401984210801d09040030900c068085000a2034400c2900c80c840014a03e9010802141414458100158001c1c0c8020300c0d03082c10311501a46030001b40c02c105015282e20400100c2c85080205000304520640d81600d944e48015201d0f0304244080b0300095021900f046400540c1c80003e100700c1c2c0034501140c182900b13103d0302507599011540154101c011303540d04c03180c0400305559144024455403600041e615520341c855a00a400d48156429503581030b0400c1e0f04800b181d54010407140415521490245182241001201000641d101e925580d501c43e500741c400c0401d0541008058004020108441544da424012 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 889863201 1250 889861951 889861963
    0x5250213090303050c0f0415020f1b01170912071106030901142503020309030904062d180902010512040b1e07020c0f04090b0f0406052a0310120507080f 67
    0x3840950400c10041000e4280d619111289002384d2043e6008010030301c10191501c074120070120208040405441203543e0052212000301c0300700310350403e1706e1a108240325103d1000d035104c03602d207050000d2044104880c400b420f0303040b140d00600e501c0d00ca040059210b8002d208a080d822211080e07c801706181c2c0451003050418003040c10a42c40300c0c9000d01108130080e40010b00005918882400303608010303a583c3c00341e103010704030542e0012034009445502c03845101600b00c000390004200c0800b444a540383e0060842c2180c150040819440f15520040310541300f00c0d50000a071414490a210401a1842403a40514007952039041901e5501c0d46000179400255040c0d409a8003000500300b0904280781c3d076404215004100251103d500c0d10b98140e0b01d42c084981d101c600c82003500704010013070217100301ca070801c421021001c1e003003001413034030f46c090f94074040b188101150200002d5107401c640c0a41201030016010403a400552500e000b5644003068020712100c1c0c0903c142a00d505180040c1c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 889864451 1250 889863201 889863217
    0xe0a110f03070f111c1b02030c0d0201050c0601170105070f021906020f0f04031401110f0d0b040e0c01021c050f030a0605060a090f050306060105250213090303050c 72
    0x40e031440d150542c040d81c0d2015032000b120107012101050540d14141880613460405507102c1140010768103010040c503854421480e070000e0442c24070808056240042c01c000300c3e405c107a4002c40a40058001a03c030b9008a030705004151050800104103228286141240d101c00740000344015222000d09440b484945c000010040c2c1c400d5900c0001c0e400303011141c1201c039000e000c0043c50803614031240c01c41030380030100c54143e00c04006020010045003202280d180c450200c020852600540004043c0e48070b0070740c001402920110b4000c504038503aa000c110f50300c074014000c120042c0f48002a68607515103100031409409180b031440b00c0048248800c09843d80c0c1e50b610285441d5014820343d196800c00340800d0485a40c6180c0424241c840d140140700424954a03180f28042c58501001540310103034212034000d070011014861966000300030381c0c540d034031846006c80c80e00340302020b0008400d1001c10b02a512000b03413102180d4001c84c9522480606019030344c103000a03540e0800c440e600f4443d80e40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 889865701 1250 889864451 889864477
    0x150f23100e0c0a111006060237060b100c15060605190504120516080c1c05010b0d14010b03010203061309020a03081210050d170c07090203010e0a11 65
    0x541041c0c2c20350001c02418040c1d0030b02202030070384600b0f940c1c6000c2507140b03c03001d450380d02d08051100300d804003c400715140840702d15012781d00c01051a603036078481c254082c0000c0c280b10750081c0b0030403800b60446101381e20058008010403040080c0141000f00941f02510300500b44031120111914a002d0882a25116141e4920700140802e8000380302c4840c0e07030322100f0440240000724149100088081a00340984024070030f01043c0c2140c8410b40300f059202c3e00c00c0d5408003030000c0003600d401080c2060f200c0703c1c0380502070900417800c01901403c03009074061381c0100080c01a008000581d40c200c0404480305008000701d400b01c80c14503080b4132040c2c84a603030040d1000e803c0300003d031013504600300840c0302030321200c6071940e03a0b40c0340d4070079400c02400a001d06040004001803000b44d044458002c0c40b08960804000669840380501c604180302004900240060940e009450030440c1000424000d0003c640e2903075038480c41040e200c0c00740c070761264542c244036540c2004d2030103206955104d11003070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 889866951 1250 889865701 889865729
    0xf1d06010506031b1612020304080a020f040e01020a09093b0c1201020a02012919050a0602010e0706080106090b09011205070e03010b0901080703150f2310 68
    0x804001c02d9030001804181d1001c02109540c040141c130101411000c400007030311010100191400409259080021804544c07080c0701c01c0051000000e00030007011340507078070351903030846090100c2c010300f03154105440d1542c000505141c0d120381c019583c2c0221500c030070041019041c1d01c0d40c2095201c0115010b008255007210301e403078038224032510a101442c805003c44050303001c248080707100303d04851014415a54046001106d054082c002ca8811316500c00d0441c1810313120442607206801020b079a28001d8800112201d0f210100d003201c5001f400009065048060752941c000707000c0c0c94910b0000040b80038424001680d40d005110580c180d6810b900c0d4012090704003070f0520030580269079518101302a1000401b00500d0522816019900680c1c801303128020b090240f5003036825210440d0300460280004000440c000300741e16003aa6031060050f80301503200050403001e049103c4002c13004a1811440f014248400900c1ca00f68414483e20300015541d61500b0580c2d00829100d0f04c080040c0780303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 889868201 1250 889866951 889866959
    0x2d1314030f1c0e0d0917150a0504151a0112020f030105120c090f1f0b0a0c02010201110c030a120b0a03080904090c15020f12040905061c05010f1d0601 66
    0x35896042814050090006510403c45401403800043c002c0b444081007044c807003400705440c07600e11075084601c60b070003e00b078a020700750a022140d900188080206139448000c030b001c01643c600020400f0301040000c1c0044e060141060f9404003041d41d407140401d4a01c2010882c803200e0b4000c0c0c034422100c00041d1810b680c601410706c565801d810745d000c01540101c125036190b60b1707210304a45020300d1140800040c1d52401100b00c01d03100000103c03111948081304401c0007003a003c4411501000401d14004003400d15510042c1d014007082d00000345400c03404204806a030310000301801041d0030950300e480820350300709198002c83d40c040d100b1070b07046005443c090000c214020014a9641d00c0079000041c0a511600c443d40880507940040740260350300e100711071030380354104002800801c450029041a405031904c50300c0714811403007040200b9455000050032a962601405289040c202000410800501d4228000c00702c1445810020b850712200d030851141480110303500c00d90b0388000345042c0e400c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 889869451 1250 889868201 889868227
    0x18010509091014070e0d23070b03090d08011502100c05040b0a020c09011e05130912080f13320f03070b0a090b2d1314030f 54
    0x401845007540d0310800340b81621180e2a480380c81c40b8803c03680b0070100c090402c01c1c0700511001a0115941c440d030309542812011a8405510410317143c070000c3d0000d050001601041e0038a80725074003150b03c0c1040070040241ca041d007c10039001c0600d490b81c600806030f0301d6500f403800c8840d080030500010703440a00100a030142c0ba60045c2c210b065641001130800d40e4806011840382d005880d550016003004203e240c0d14205081070a024003005c0b80100c680a1590075014208500c51060901c21003050601c240c060102d6030100c040c80d5041084480c8400791031902a0241c18155800410f020708080000c14040383d040050940640c003105105c142c1c0e41d8004103400300a5010b0075044104e03402800c00000460401c0003900400200c00955280d140038105038122400007045d140c0c0d0913043c0500e0100017032507905070907071100e010510546075003145c0d4541142c81540c0740d03010100c90001401d22451400202e02c01c6c20745032090641c15000c0c102400b5240d2680102c500c0c45180c9074080c0004944104 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 889870701 1250 889869451 889869469
    0xb0403030c080403020a062c0d030c11040903051206040203041a0601030615090807080316021c15062409150e0607030908061006020d0813020d0809040b180105 70
    0x10003a40c4403410643c690700010b9002415501581c046441142c128200146251507a543c43d25480c20883e00181c82c10701098270001000c40003000c0041c41100c2100708994192454070b480009441040011290324018120f40c2c4400303040b1801070035072800a078162425008403031081c0e40c002000780d0107045451680205c41c4010742120305064480714046075075800c541c290500940643e40340701803a49070401990030542103400000c465001000650507038a105d98203a401369a06031140ca002c0711501ea8025022a01036030002c3c41c3c1440403d04540d26a400c1d040141510190b88414001c0f803001c60803030020030780041e540300218081e4681040b40385291a228034822001c1d0400b0070341d0303900950005901e0360101d10100c001c00d080001c103001200040143c207900010200c5240b414905114019594400c0100e9800421101000140c2a540340b0710303a086105a000e03110b85000f43c142c0c40c0420880d02324800c0140a280b52003d448024507013038480b0842c030710181c0c100c3d0510f039080006001c2c41003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 889871951 1250 889870701 889870703
    0x50108070b090d060e010b0a06090b030601050a021c0507060b03011a1903141b09042a05100215060d0b0105101403070806150c060f100515070605010f0b0403030c 71
    0x1d0060001400800c13070500800305a204202c0000a0300480c900400c0172401c1550802d004000b05418280102c007020001c4036009282400c040f52210380c4441d0407840c1048594600c1c40c7e1600d50050a04c0c00383c0c101026213403452003110140700e00d2802000b0300d800c8805080104039040480c285c160040d05104950a2898410628910002d80c403074440011102440c10b030200b0580c42080d416400c03424020001a0384079088500000c141844e807182c4c04142e83e10490240150313142481001d42410b0303010040010300c1c001d840101040c003d4207010f51100b901c102d03501801d840d00303800183c00f442e007000c01c4180c407a03022042c194181d00b08000e04c0300d0341c000d1680b03c1c1e09000d00701b41c5903070510a841014620a0607941c2e500c595514106082c08140e286d002c0003580d106205110903070504101103425a4806000e408002c10b40d41c94000345914413240b40d00060300024a40780b2807409400b13090090205a014800c02d001c266a5002c000c0c6940d4954410102c0c5084144001d0002a1190247e50300403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 889873201 1250 889871951 889871959
    0x7030515131101120c0c05010e03032404150305102d0203090102070813140d080d0c1404090b0906060903060106211a0108240f2d13050108070b09 64
    0x104d5805220441104d10305041640828042c40014041203824002c0810461000001d142542008881910314134609000c0c002421100911801c80d80c4669004d01100411804c07001d5149a03241805911102056501c8030040d041c0b49204100c81c00c1445400c0c061010303200449212083c1049217002500058402100c0355000c01c0a580840c2810340905881e440095000030030030300c0e0804580791041c1c3d1270740890282041d004441c0201d22140c1c15200704c00b207440000b082c0c5541103031040b95820088030300403a042c800460f002c2820100d6910000d200b034411360785103056484180c03c220280c050640f02039410b92040c0010b0150724810403810b822000b8110030380d820040c1c0e418076141074070940702440c3c034440b0780b0b000860320310760380304400395003160354140c014400320801e41e85c4840b0300192000c2a801920014040c37800c036101c5c00103100304d20f43d4801c21580d0320080349008483e00514054400e200d120044410ba000361014441e150403074404000404006203001d11001c1caa0b001115a9548 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 889874451 1250 889873201 889873217
    0xc0a03110103020d0f0504111201051308030a0b090a0e0c090408040311030a08360d0303050c09061324090905150603040606090f0b0d06020c071707030515131101 71
    0x211700b018007480c0d008501c201e0640e101030b5542400d2061444210143d22140d038101402d000254440901603221541c00250030b56484d40c0e034100748030107020290100d6030000200c4040149804d4154480902c1074035103010380e1000b04001c02004165070040e05c0c00303001b01404210030400144850700603600c40300082d040d120800507940b0703418007503002403200161030004c1d01c541c901c0301041401203800000c403001c242110000d800c40402d0004c800042c00405050360f400c0401c100c040380d441a42d440a100600055503a40c1c02d4505a401c01030b40d01c83c8091801c200c21002c3e0300c3c00b541652284058600d9a50b111000d0b20300381104002d03100250498403015400f40b165946506c6110065210f90300819011a100e0700e064840422a4130041c0a801e40915103c2140e000b5a91020311050440d0050000b580720254804034504044243d44030580b885914940e404e0201400714606084a0184064598a010f480203081c9016802c0310340725046001051400002407680030420b04641041c0341c43c0340 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 889875701 1250 889874451 889874471
    0x3060c0a0207031a040309060306030312270602041505030f0f0411060403050d1d220b030105010305100509060105090126060907140a082806020d09050c0a03110103020d 74
    0x7203051004e03040c03582c40c080b025040005050300424400010001c914042014603e1510004c00340c0100340303035103000651108103110800f40c0c4182000440d030002201c40019000d00d1410708003e50240c0700b070308a159424410099054007890580340f08000509151416684d0f0741c05020b0020b6005104840c503c5550103420245c2d01d4140142010b50f200b1002440380b61440e200181a1009180903480714405950b400003180c1c4910b1820b52000d41c0c4996001c7c1c5100d99901000c015146040101c0c0c2c06600e0f040001050003c00900a0203030f0100300310401c155100c0c20b1742c05131222004d010711a000007544004110349042c07800000040b0742ea030b0a02000051a5500c0541091015200800942d001450601111a140004420742d0804546680155240c140d405032181c22152540c541d032050301c040504005000f050801810f580144119a81e501c102460720060095000c141c50600c103a0401d451a424010842001d50b500000a15001d04441c40110702961003030380c1614455846036214a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 889876951 1250 889875701 889875713
    0xe0d05031e0c1c1202131208070312020c060f06030312040308062d04150e04061a0f01092105151b030c09060a0903080711040c09030203060c0a020703 66
    0x180e1801e0885156954841103480b07900c3c80c040f01c003410b0b801114801940321464030b41000c10310305041040100503848080302001444010701c1c40c1d0200350340da5480c9a540080260040051168600c2501e0300301400d86040c0c0c07080124001c40081c00c0c010381c049004254503800c0845140e5005000508684c5491048806200f00c110166022004203401340140001c0d840c005200d61070348084402d48140ae1140b801c21244c2d0300030840d40c0300e40a140d40b0705490715000290306c0c079107002d000802c240d01168205441c001004103600c0a4404626269280d041e02515014080105001c016590181051b00303003e01b900c520a60100c41410718822140640001101803001c1103102490025142c0c0d503142220003030303405c3e440400c00002c1c222020010064248010740640d40030001c00d4039029215807104409454010391030f0409031028402003289001c1000044203940d05c1e400a64050055440602d000c0e61040724034000298140c101d0000241150b8400014100060551041701e041c10f03500d071640 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 889878201 1250 889876951 889876987
    0xe0a1805010504060501080102270109080f0715050c0d080c160b04120e0a0e0703092003010b030309010903020621040b15190504050703111303060e06070e0d0503 71
    0x3200d032030351107504010034004544103075401411100002e4ac03501d102d41103000340c9180700c1c22240d840031040c400e07400f07090307440781040344043c0c69038a0031142486184c00c003030799075201c0700e108100b00d192003c0690300c011807060054407403508650005000003212000d0503102254002c2800d802c551050146240e001641e2110b143c10f10b0250141200d14200ba0521031001c0d2549004841802484402d0126580f5122200320031211101030690003921000f800701d0103440036042c0a4100444090740d0310035080710390001c11044000714020405020604c040c15124000c4e001c482c5c0c00710307008007020409810410020b141404154240789a1342c842044000041072080c0d40507110070f055902088050030f04251508030040302103030921900ca920f1108503041121a025040c0265203400124a18600940000f480e20790b54200094456041550510203003105e40b00598900342040e86070f4010440106a050061011fa901e0400703080a50b4244121341044100c125010301c410460290307140508904 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 889879451 1250 889878201 889878203
    0xb030f010f14011a07020108040f020a150f0206190b040f0203040501062c0c07080c1b10030515150d06180b011e12090c080a1209030302070e0a18 64
    0x100044640c01c42100700c1c0c1a9030160004d49512022482c03110800c0500d5054a4031281c1c246807113002a943d51600603410701c42180300a400c070f948804041650b800b6108040d80c0c004965a80b207c6a110280301207a4508059803004900040044c03000c403000015000511569000b40020504952080100c0700300c0e4401c0388e0035035040e59908030038800019030b4114407000c603010009800054080c41500112910080c00c01084240001340d00801c0021480985400e0410328003560045c001c43c000307012503100c1d105600340c814031010440e070015900a01c00d16024040780f401c40e90203104520140309204c0180c9002c40c1c2e20300d409008018643d40c490103000c0242c00b040ea404813000f40d44406060688100c0225141401110011415070a180c010f41000140180c076010300000c80d114040b80c01084c140c4070181510070800360105400c80d0029031401054840c0e105401076600082c800c4403900102d0100a0050300800000c02684000007000303500004050000601c103e580700b152016032a078580 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 889880701 1250 889879451 889879481
    0x807051606020c070f0b040e070c061b030e03072a26190818060f0a050306100915140f040816061d040f0f05092a0109090b030f01 57
    0x50900e60404280903450085c4401304407005403034107041d401d5200d0b000c0c60040724005000705c000211005e200d6192150916000300c8104280c508401c008048940d80d443d071b52020a05010004001d28000801c4850483c0c00c05508004404802c0f10705260302075402101c80f40c2c44201c0c60100341c0c1e00b6071410303816400c0d0882001c0d204861505401d98140060320f5101140c46a2421a41011800020481307408600f070078002d843d108903140002d4814082c40582c04d15401c40400e1303a000007908140154001d11044502c003103080001c2404880c128810702890395003d040380b544007101400784d040f50410112000a003820021840c0ca030000030340240c0e200745c2d1550b01c42c503d401400d810f41f10244014051506d0052041c0e19000c2c00704801003580814075000341c1d0b4030074090991559941c4400d98851000e002031105007040800282c1c3d0308030343c40c503003030500b000b00c0c074607582410403102c038084d0000307068503001d40140c6041e8001008005122040da01402000e4078501c0c048000c2c402c00c24405c1100c1c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 889881951 1250 889880701 889880707
    0x6130b12032a0610090b01020f06090307030831061b0e100e01020607120608330f0403050912060f090106080303060a05101211090906061306080705160602 68
    0x4019044900c0e600c003008070b000c0c1c0040c3d003030280c59107140ca4480c05641d020140413500d0b07140400100d00e003424805480101d80590402c5c4a43d2000100041040e6070007941e1b10703840f80c0c0707900c442c500c040040030038401003500883d1644040d0500d96110f100056028071000070300007a401c5603421035500740e00c0d15800020500042801c081c5048540c41240c5103080c604a00b40e69040380000c1e64920020384060b00340001a41c40c088501e40d81d40065024100007000e50f0056420144200d4510407051400461104018460080b034040d00360158464658044030054076110f68400752600d0744040305c0560000c7c000030511407400c004100340d070f00484a198001c810307440c02c41515803c648042c2c101c00402d410410500036260395840200040e5030045a03110703400710f241c0e28152030f01d40511441904c0c2c04e040022038810f000c190702c0505070026003a9a8544980e55201c10429a0b10841b0200300e0380d070140141c2804000c3c8500c1c1c800d82c1c04009410010700e1700f04005500350040550040407140c0d15000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 889883201 1250 889881951 889881997
    0x50705090f1512100f0c11030a0906050d090503160203061e0103061109360606030a050901061703032a070b0a021605011b050306130b1203 61
    0x1400c8255004264039442240c0d400e00340e107210a02018100140d10031443c0140800070303403606004904404840303038010800c1007200080c003806400400181404a002c1034519040e00e800482111204526a503d0b5465603043c860140d407640c0010341440c01180c1c1d01c2d0129800180c0800c000e04203420340015122041d6040e2041500d40040180201c1d180b8124a1001411614190009040d20b504c0000030a034a091051240c10300c0c018170000c0c9510008a41c0000c0701c400011210002c0d0740607407141a80141508030300640c11440950342c00303030442c0c420400104942032a07440a9000340810002240e9150303100d0f40b0049040008e0184d2200d50400000c1c05118940394140c505190a020b401e848190303480c5005035200d000b08a00500340d1a9880d0008500e5036442c1c0c111b80d60412403240c000966809030070001d00070030380503084900482a94030317441401800b400580348140c0008003802c002d9200141320401805008510310b4004040607a4284e900109101520f2214201048001460b0340 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 889884451 1250 889883201 889883209
    0x50d0303150b0c120904020c12120a0209060a05071401151e06020a0b100e0408031f03020618030c042d09020a03110303070f080405010e01110a021507060504050705 72
    0x10701d50211528000820a41c031112101140d42d0f01801544140182c07181c80c4000450045d1091007010032050055042900c800d07030b00314016040080700f0f1000b000241d500c10501000b28070803031280f03546c0b11006003c100c800758031030b40080c80058800e00629030030b00180c4050900355000603c0c4c07021402030f4003400f4005503110300c142c12280c0911001c030b050344625104000c0d488408649001c5c080c0035400000425200c44400c4280042c2101865004a80b4003420025210f8005a8800c2c0130380c08142680420760a0b80b031641010b40360010306040c6001000c03d145101d1061141085405003d40f000341e0740d00e40d0ba14031501400e19520041d2110424090480d80598034401c6030050451b848e0103d5400541ca81c14482c2040c1c1c0d0740200c0f504c0d0051744c0840064954080c2c20303c01404012040660010452031720050001c9540a0322940020311642c80151500601c01c0004c444c158004c1100d50058681a4606201101252101860a00b06071254070540701c0c1201c0546090744140c40800440c10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 889885701 1250 889884451 889884491
    0x218040615150f05040b18030703150c09060806090105011206050d050a032309060322030e04060f06080a02030c07050d02010519020c150403120f140603010c090e10050d0303 76
    0x841380b4100f49024240040d02c4071900501002d0342e5102c1012801d4003903074a04001c040040d6400a21800c0034045005105018000c101080000600030303400006505000303484160144070001c1103403005a0a2800440d051441d55020010381601d03004009219100c15110b106c256000d04041c2c6416540f904029007091101402c10134503240480300e14049050000503180382c80811100307241c0c2c070703200c0c802c0c0e0711a10504c2a00c40030f082d841e0b000b8904201a0403900104040c081960f0501803035030383d094100884d059610030007012483e8040003e4210b1900c0e4010f56016240c01c50040c10480b146e1071305032800000c0d00009002d43c0d5110140040981541902445900341d02001c2d441d03c41100b043d2900d807034014a5008400c0444c0002c101054007803001d251940c5144681006503200c1948002d018207141707640040210304d0100862013504040c06a2b944800f03258648640861402c0802424000001c11400300c0843c42d03c000301d0b450746e81c8441c124909009075008201511035040310b82c5a12 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 889886951 1250 889885701 889885727
    0x5130b130c18240f181205060106050405210f06070f08090a2409140c0406080307050c100c080f0414040b010f1b0b010806040510020403021804061515 66
    0x10303841c0d010290b402806030100100651142c504410b81280354601910178032920b00d06903011000a00020414507108100c1c20525401282201c0c013030b990b541410317103051180307024540d04825800034040c02041c40030820341c6084070346000c0350707560006040603d00740501500c1e1480081c00103c0415181640512810b820503440ea020f800028502d566264000380c1c0100c840c113076803005da40d41070058a41c03a8404070480c0d8000000e40680500814007988502580103414821440c000000c80c1c4c201c000415104a654802c0003003403916880401c02030305200c44503a50041122040c92400000c4003031014000e44075601c1d84044d01c41d800d00641a0b4007100000880d03000c0c0e80b4100314030311142e03030009401030060401c0c18010b001c014440c0c41c01308a9203c4843c05842d80c40d540740005050140003480c1480307030307004000703807070400c44100c000d00160300c280c1c4006944800c5001502d8904040500b0242e00a8840c0302c000600e0000000200e100c143c8a52046490b610844040d1139142e400040d190504 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 889888201 1250 889886951 889886969
    0x30d0c02031b01020a02090c1215030d2a050a050f0607080903070b0a050a02040306091208011a03010e180f010504140f190204090b13030e04020405130b130c18 70
    0x410b2600004c1d42d842c0800d41c043d04c074004207408a24045040f80c1213030131500034115034200324501509895440014454064000d200301c10301d640c1c5083c4580b0f0f42d0800072910000c5030724048031940040d504011044015134040c080d036812000068800c00c0ba81d0812040200940454506a00d01400408005040c11a0381e0010845000010158003540364000e15140c0001107513201e0220761382c024001c030303040100721500c0c20b9445824403480152185d07500d012aa03400c60160380368524200e8802070801e000301030040500050050344801e80f0309660107100040e58800e01d00360350030428503180c00031510848030303550b41c0c0c280410f00070200d002c5e08903210b015004200c01c801c81c068259440654251041842d0040f88101c411581c85070080142c00740c0250301221241441d0500d5503600400c0401100810590341c80070700d01c2d003050b0003520200c5000408144003012184868000791984009296000401400c20060f00c10988102d10600c1c0345030351151001c00c2e101c942409001c2c41030300003900c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 889889451 1250 889888201 889888243
    0xf0510030e0a140f1603060606110304090b01183f14030d150608060a0518340806042a0207080601060309150e06070302090f030d0c0203 60
    0x280080014492407443e4030145201e6040c00244005052540040903001e00e4011611101070b4004200f00c0001924003904003044400e543e0642503c0c10414a074140c12140c0047c4410082c00d034061380410210070060512070b0303480c41089011f10b003c044039000b1200380c442032800d4080c00c1c1c7c00040c1d0303c1e030740302181160340c4181c504403910304244410200340244a01d10041d0803c441403414003c2d83e8410410380b00c18414451845000d0310005100d000300000a4001800202103180100c402412680003a1044666481c4e5140c580c030107401c0103019146c0848080703e4030340802c544104800102080180c4d42100c801d031400300070811407010f0200791180d030503c1c0001000044e603a100715134800380958007002812800c41c1c00d81c1010895030212040e400348000000790150076411480c205071007421061501d070704841f441c0c0c0403a2208040404251710010015000074080e50003054062401013250b8010044140000d15141c1c20b82c0c1803400244585030b0b0b42086060401c880800001810034000d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 889890701 1250 889889451 889889471
    0x1f1a04110904110403150504050613210e100206060301110c070e0613150509090d140d2d0e0303010602030d0c03180b100f0f12060b0a0f051003 63
    0x2028041e496019220b15520100c4582d08039811040b28020341e80086815510550645410010503080b035080e5103602034600040c0c20040415a440c3d4441c1d403000c80000b140010f0480900d00c00e074003030741802c140b0104240b50143e990f038180f540110244594000c04680c80c0180600d0300f96081284901c0d2034103c00d01080c4d1031400c0c04550b000c15a441ca81d0005056038503c00000c0007403d503402c000401500e00006501c1c10010804044191a420764480b4003584503002c0c4da07962880441044030004e0611803000141c060760701300421441c070072a81c000c25400d00110041032410540800c03100c55503441420302d1035124860080c602d0040c4c500002d18290340c90068083c0d00d0348070b500080000c00b6076450903580031030300a90044100d0b540e82403400200800901e030140f02c0101c180e8400740e213a01e10b201300250300e2480030b0544055179241e2560550940c40d0201c60081103940c0d00d42214650303220704902c4440d45850b401000100380406a03c0c2402e86800144441c081804c645001018105500c0304 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 889891951 1250 889890701 889890731
    0x519020903071202010201140a0603020306012c090705040606020c03010606021c0e0d08070305220501090b0304051c02071d010b03060925020c0f030c030d050c1f1a04 73
    0x10085071a00700d20f0702d26407801c2e403004034018442840b03600500042d09060203112200d5510007001e4a10170303000c68207240d032640f00590301030710035410a074258051060749140c1e40400e05801a041007084045510b1107858800103402d490315030b084040182d01480c1000c4a40c502405924002c04040c009003440d000505115015000000090f0007441000c1800c1c1000e41c6440315166800360b00009140c1c0c80f0b001078a00148940d025007100c505c8000714a49da5150408640500021a0360586407200c1c5903207001c0c154140c0b40c00041003504c0c54000c080315101406980c1c00c000010510a07806080b9007814801001e071716440080c4d14101070300c4002e00512600103400200c2c0d821041c03c0b11b290030260b480400c60225003400360003250f0f20201e880220094183c0003d4060740f001c000701d0761300e884030821209056a6021420302c4590580c032542c4100c2e0310602400082c0006050314090f50114140480303549124000b0001d004642c43d500c0c000a40d1103c1200d81002d044501110b00f0700400e41440d1a0b8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 889893201 1250 889891951 889891963
    0x618020d0b0a0e1810060b0a08100506090d1728020604030206060609030a150606121b1404081209012604200a030f02031c0c03030903090305030d0519020903 69
    0x7103241c42842000c81004403808005280c40c640417824248007040d11000b0000f40c3d07410900206001c681050080b41c189800c80602c5d10641d00c020b071800f030400b2120b01c20800c581840000c10740c0c140b40924251100781000400a2244054420700d58808000c0054207444513210707407100c401107400c41c4003031000080d808280c003600720340200c0340c0702c0e10b41d9104800241485080c2c00001c0c0103200e1740603034443c11a901c0d04100210380b0242c44800600d110310080d041a1111100c2ea01c0c44032000000c80d40913180141e190104c0741a01141c403508103525182071314540a2016103044481034080b920680f01d603806031900485030710055070182500f140d450b95800c1103102410062001020341910310305049424070140100d10020030000f03840c0e1381d03400c4c111800041c1460a82c042d0198441c01000c40061942e4250005c00179034642d0514a829281207000700925402107082011800f8004085081040035201c03900c07001d807001502e824041401c0481044040e52081400d0060080188503640130400d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 889894451 1250 889893201 889893211
    0x60411030d0203031f0b0703031b02030f09061b102c0c12030c161806030203032d0307050c07080705153403021203060d0f0201030618020d0b0a0e 64
    0x10003414820200403d485d908035641002c5500d110101e5203800303040c1d2580100608040c1c0c40b0440b00201e50601e01241c03603201d0749403508841d203030401800f846410500020910805c60580c4113140a0b82000803d04140038110541440e039100c451131440354808403110710484005601c060003042450012684072003100c2c11041c411160003600080a01d0f0900498042d440b11109607114601251030108186480380201c06165100c7d080a22500c4083e20804054a03001001941400c40b825482903070021400c1658031080700321070f4081034a105610142d80036038071a480b00b60712014001c1c0c00c0c0d890401951311004596010580c00c03c62038444034400d8001c0030b2109900c542c3d0b0700315441a00d4070503880d01481c60b0315458001720380107014140514203040901ca0341c01d40b503408900100c861130602050714500d03405aa052141c1c00099072024001e580c017071041c103000c20b0082e9140d01401a40010703c4115140a40018483e01c0d541b00c0380c8600c8010b5001210010142030400c1088041d110340249 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 889895701 1250 889894451 889894471
    0x2190f090204151b230c09040c0e0a020409050106170a050105060a1202090d1103120406120902010314040c090b04091703040c0312051804091a1e09060411030d020303 73
    0x1c00e500440505060300031055400c04007645e20105040d890703020810103501e0208190040038041c1d038542c0741c030009860040d030b040651910114100307508610b00310009421510016130801001a0440c1d050041d28002c0c5030036242c03c42e0002d0007204104a10100a22140d00289040014041940ca6206894800c0c509280007040c6519841c1c4040081c41a1000c0350f500401c0300580740c0030461f039071440907040c000981c1502c40015031141d841c3d03418092800ba08001c10f08900032203420600d079601101c1e10500514001c524000d174180003610b982c0f0141e0b01510006038003c8180020701070f50041c6d020208013a0760800003152a6101c51800d2a00c00b403a1494a40c800004030f230031302c00c60510724030185030031460381030b01d0100c0704001404581c00b0074050541d5512107a0381a804e4a464030072156841e800450252540b0f036190603804840d80700a000e44214801061141600203a1142c5a442000190300400c550b040c24103121803400b500c19419880382d403200c02286a110381c00710540703810030354141c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 889896951 1250 889895701 889895717
    0x14151f050f0102060109021b07030804150804050607080c0721020d0507080d020f0717090a0f1518090f0f0e060c041203030b040f0f0c05270301020702190f09020415 72
    0x1070241e24501110300c00c60b034231480350f0000803051150003801041201c5d11116030183c0110f44a07425180d100c8200c80c060810b030408400949098000c2c0d01c8554001d0000c06072600d05140303035903510b446c0181d0340c00e038003500400130118020b4980c040020603003400c0c071401d019003843c900d07642d0f42c80c00c0d100311440e01154680208009855103c0c403800d0300d026036400300d003004804204110000c0143c100349400d03440303503680100c00160310f00c015900605940c2d01c500c60031610028403a055441301c86601c07078658076407085140000e450f0000d1040c3d00040e0101d00012404080003003100c3d05803910000d40142c190000c100388420010000d0886046a400380354500c0c0c0c40394a401c1c183c4c0188140c0d0000750304135043c228400030080259200c806c1d034200900c810000300850304821501409900c0e0701c0c5030240b000718109680301c201e10700c401c2005000100050b107841d100d42c4c0440e0010f0b080386c22029084002603001d00c00c9810116000c4082e040e042c0d000c50920745091f251900924192400c4401c0c0300c045 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 889898201 1250 889896951 889896967
    0xc0a05070203330a2c07212001050307110f01020a03140f04080307030f06080d180b03061e01031808040801060e1314151f050f010206010902 62
    0x388804809880c1d0700026810f691201c1030f200491034403c0c480307480c0780d8946800003400e084a61080039802610704607a0b034001c1c03603c850911600d00b5540891010380c410543d00244104034604000760918450609120342c050514003440d00410840c005034150315128800039844c0da00c0825681d01c8661032400510400011840c6404d020395205140e0055000252810340e5076016044520204101c041040c003d90361301c149144159420383d002004440b00700045002203100b60030940082c41220000115190750f440414036100c680108880807030369401c1400e030b02d082c092424000401c040c0e142d0134618940140001c1c00070707805054400c48a40a0031015000d41d00c254014000620100140205102c50781044842c94100c0d02c6003098540c240400854644410030800740034108501c100d8107543e10540d21400015032441c00300f0501e10a5100c040a2450003a807140d01855454450380710010f010a01c020032004181c02c194050601c1110388403450740e0002d132280c1180c0c1d1080e40141c1342d00803 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 889899451 1250 889898201 889898203
    0xa0b07050a170a020414091b03060a0e0916150c060c110a0c0f0909020f3106030203161503051504110405030622060e03090d05061e0c0a05070203 64
    0x40b60400440c00c00d0414204055801154014000e903907252640a8142004001700444030b00c0482d692280d0302050700c4109160389200001d142c1000c002051084c201b510340c1898045154115024180d0b64001c5507004580c3c015010034001926603640035000300c42242da8080c0200640a01c010041d6546c0c1420140c0d07284140504421081c1182c180c40402c842403d204503040c0260280d405003408554000580f900544289407019070b0207429100001108401c0182c0040444016a40391070b800c100f0280605980f04c00154490342c80c0000a1b19a0950040c18a04a5641608100103981943c144015100c0c44035005c0503071168907000c00c141da44c1985100f43d04105070320036a001400c02c46103100e4140107001030401d44206804a6815640d40002e46891449107100c084000080c1c03000c600c04110290803421340c41641c0c00c12680f52400e81c1c004103042c4076080405481030340155050020f100138024800b41d01071030200151025003854080290795100b2035000b0024023900107034000131510 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 889900701 1250 889899451 889899467
    0x150c03100e0411040509070f0306180506190e0a15150f06020a0b06040504021c0c03080d0219080405031b0703020301050f01060f02150112020f150c0c030a0b07050a 72
    0x1c0100525846400c05140025000d0300f003410061040e400c010000b40b102900090400480350310201c01803c49165480f1040100300d140d030480c0092484100c890f020800c20008103006907000444403002045c100300c8071046899402250340644c201c2100000451003541a14a031980100c000190000c00201009040c01c0c0542c0108800c0011080020310070360081624000180160172500d500d0f84d410b41044122481207500a5106801b014107401c000f941440354500240316404070607486440340c450034425041845001d03091500000c4040703202c03001c400d041c9288543c40c00c1056003810036913240741d100e001759007212050014070300040d11280400c00c0804015034014000304968244500c0c450000c1e00f09000380c40100d503c40d07000d01c83c0584000b52042840215107509012a401c1000c40c0d060120302d098180ea200f01d0b68081d8401594031401f800540702b4800750300e5640c0341200d4601a05100300d80900344d00ca60020301c20140450f00e2000d0207540042d10b840d055075030b2447d1f1002518041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 889901951 1250 889900701 889900709
    0x30e03012d0e0105101505222315030a060509040f020f12060a05060d060e0a0b01050103060b19050f210a0e0c0f030304180f050108150c0310 62
    0x2001d103248007003040010007120600c0d0004080c140086500e02c01c215003070320000d81c0c580c0d00180f0321040400c00503801c1d0400b900310001c5858010b02e0700c0840350042c0c04411841004558030110843d08004103480c208a03d036450010300d1442c4400720003440003a2500d01c5560814121590000c0001e40d0101d040e44001c010f08002030070f40001e81007509100407003442100c4204e02911045100100607e48084a041c4618802000f89800e0380c81c0c184c00f00103040003409080e04903660300c081d8000a88680903444a04c00c4450007040a42e0260400324881d44060303002d5818546031540622590b0a03e404548070fa0103000751a80c50060b08080c1110f591142c10700381d11400c580401c007103030301714108a564103070b28030a4480411152111a20f100c1207a00b41340e04221907038410a28038655041103000d41003c00342c02001e680c01d26564050380b4190840300c151450415a03202245a181885031240901620542005204104928854103030030803020346030b6041c0c014080001900c088003118180050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 889903201 1250 889901951 889901981
    0x7200d18050603160e030a0804030302030d1b0207060324030b04030206010e0f01090b0a1509230105070b040c050d060506100c11010e01030905010c0503010503210403030e0301 77
    0x44211140040c012000400844841040e03840c000840d46000c03003d40b80107500041850154511100c07090b03444010801d80150180642c81962001c5180000035000840c0281c0295649501580d80741040b9103c4004040f043c0b41c406030003c1d04280d0006920b8140c5080e818005184400c0303402c80400144030140340400d41c207001ca0007000704101c3c40141d0b4061403080d0212503070359888000309040c1d40402c135841d4003d0540341004000d940401c1e00022040c0101403c0405c506071100544080e0a090780c40c19404074402c01020401013410401e90100811010300030812000c118000034000d220f4901302a151400400124041c052400340701402410018500c400900047c50188040c02c0b0483da602d10803070007481602503d9008607001000290300c28400036141c0300c03260040d03801c200c1c0c1a00c01810140e989489100082d024840c0c2c6030f5000d065101c01d9101d6250070201841d141101211085080e00010014044036115055605480c7d15040840d14520240003103801007000c82914080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 889904451 1250 889903201 889903213
    0x3031b0c09090c18050c0906090111120a02120306060415050f0403030c02010f030504020310021b030c0a051603030f0806040905011a190501080604090c0302030d18090e03030720 78
    0x10001910030f4882210102c3c0c41c05541204400701000884204984266003031004001068091a011004010310310b0141801c80e464005502d1482c6484200440e8031402e51001800c0c5400c182c04202c01300a441c8a14035007869072a00d00c1c0481c12034043c0c2e02c01e0b40c400300c01e03412922100300d005a098079880503001d0581e580312560b81c1001000340c4440082070b400b0410800411000a21a0003224886c54014000b070000340c2c3c441c800c00f002540021144c03d440804004a0f11111005000400540703034410004c0a0948141c21715030304002504400440c10705022008000003900954108d04030001c500f000312113a80d035000460003400803010000c0495190014001c480302e81d061304885030000c20348030388100400f001c8a013100d0700303258040c0c4d80c00b00780f403c0001501403509030041e9180512a00e034980d11070b81d880c0d000c6890006181170f5000450840301080070700b0285444210000c104507034062001c0d5100c1101c0f16124030010304000b0402c156030b40b00801d00c400030340345201c00345031042c12a01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 889905701 1250 889904451 889904453
    0x403030609060509070c20060d020d0b0909061501121127060403151b020a0302060702030406080117120c010c0207081c120b03030304030e0f010903031b0c0909 70
    0x20040c4000d000c0d00024514244000c00c02c0d040504409105500940b2807072410040ca844010038003460103884a080e081e00c002c0c80f041c90b100c5a01074a0704003e0701c100580ca0700451070040341a144440d0314903004407002d204029160b000064515000920784490740400320402d00100c50062441c848041c0f528240441088210000e1004014803400714034081ca04880e500341d6443c0b101f5414180c80d0f0f01c46014032050002c1041003000c130804c16845000041d594640101400001140d00402e0001da0008c4054805050301071084550001440c409107150904100025052000601400412a0405131a2031a000c42044140070008501c0030140d20354420404071400b80409524020040c0078070903000502c1d20000482140b002403c586003242d0040304101155003c04440051101326142e50074489540c0782440258040d5010740e80750001200c40c00144540c0260000c1e0440c100114480104040703640642100301c005104090464107080c1c5003084c1c80031031119008004440d1a210440c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 889906951 1250 889905701 889905707
    0x302100c0906110606130f0204031703100603060f03060b030a0b01091a0a24020a0c0608101d06060f040503060f040210022a0a0b070308091209011403040501090b0403 73
    0x34101c800c240e80ba00000e0f5601043c4540b158000d6071401d410001c2c0d8039145181c0456a0170000d078030b05c043e00006090070342d00d49429440410b001c20f40000031800200f44400c00820701110000b130100743c00c080c041c0601e040c10105074030031580f0004e8015641c030081281c86a03070a000400352550440640003803561100d41c1e182c018013031100407281c10382040c4c412600c5414200302c0581195041d18020345044901440112301813a150b00c02401c600030150750b440040c41001903c1c0141c0301664410105150007003400c201541c6907040580c012100c260015201c0214194081d80401c046d0785054444044a070309462500850b0851941070140340c04114551807030032601740c803450003120480e0a40741c120800740e03180d8800d40041c0340903001040c2c0d001003c034548248045516800780c01c540c1d0141e624070402c0c483e0b402c4000c08030001440b81044c072107d10720410850000310441d03525a40381104000004c0c000c01c440c0860fa251412002c40083c050040070340c402817003030360400b80040c03807480e1a107801 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 889908201 1250 889906951 889906967
    0x120e0709180c090b060c06010f090c0504050f0112110706200c061308071a06011106011413020705030301030b0403080106030b060a05031005130b04110708070f0302100c 74
    0x100c1000340c03815101140c240300184100d40c074290450a90075030b541c00d21000f030015102000480303410000c1001040c0c00c811041001d1070007083c04040e400c2c1c00303508008200b8281d8100080010803c00188000c5c8801e5550b0044074030345446c2424114400b01920801c1409003010044242142002052100074010b4581283c888480d039212541c0c140303004400d43d8000c5019040d038400b01a4800400100044803900005c0c000500441e905410803c0c0c5581d40c040340402000c242419102000038440700756088044400c00c1d4400d4005046507604044ca18180d0710342c03074007015200e516141c2060694403030340c0c5d040b100c00301e4002040e030703649603140e0404d286201c2060b0ba04800043d1041c0000402034402d2203500100c0f500100301a14003448450102e44541014000c0380152901c140c00042550302c0028001e4121001c0c0008a0800354074010401150402c949514400c48200030306000140743d00111480d29502181c004400501d5080482c541100403299425152500810000403900180d03c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 889909451 1250 889908201 889908209
    0x40204090e1203011d07020f0607090303080a060b0f160c060c02090108010501140607110307030b0105040c170c1309020d0b0916020d050c0f071e0f0602070b0a120e07 73
    0x11160a445038070000b1070a40300900c20700421945040317000080350b440520700c0e0b03000043ca204039041c0001c52803001c4d0030100c081c1e80f460049a40c103801001059004441a5440121101c040280610380352a0401d0ad10400f102c410308580300049c140480c003c41d040702580d10743c00c160803003000381d110800035002200c0329030103078880c4001030000100c030380701401694180c13104001000c180e866402c1c11b000e0240c0003003c04031410032920400074450b0701d00f00071032401036002c0c41611886502d01001d100894001900340b42c108241540002018500602c44a4001064040550b5039284040c810004403125070400100746000284140c258080c0e034000c082d500d442101c020000351600000008000301208410001d40c0103900c030045014090320207050b01c4040b01e829162209501079a05080c89010b40250007280c00000280c41d9a07600210600064010900500406828520041c5d0356500a00c14241200b000095070180c0a21845008813060800300f41031203100c0c00161a030f503c4003800e0003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 889910701 1250 889909451 889909453
    0x90209102703060b1504080a060b061902070312020c0f1c0b0a05100b0c1506060d0603061a0121020a092106050c09010512060307030503031003060507050301150807020c040204090e 79
    0x3070b00482d26011001111b0031180305a0013014220a950798400280c8000c81c0c946d5407116060110b41805002400c00d41003d100b103a016000a40c00c501d0120b41c0f4076003491140046502800342c5140c641c44d00c1c5101c0020000840d1030780c42d010141c0d51680c001054581005114140000500500845a0b000f450080640d07004008070306407100701801031401101d400c000c1c0703a4011b10400715801a4002595000440a802c0c40d01d01507800c403507001904c4180d4822100248e4411070409074120b0f010101c1181002403070003140a544003201118501d001c0c80c900f925060740018000441400381089800a10680c40c80c60b20740c0004485228170011111801d84641c0d05160010b40700c1042c24040350f001c103505850f51424000503072142c0276034a00042c02540c041c4148907003c070224404101461045181a000180703880c29894039400f0b891003d480c00003030003801d10050000f1a03c5618804100d83c0d40d24052002d580c900e20202d10384030804045a0300107100140200344055647c1000c6140c00081d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 889911951 1250 889910701 889910719
    0x5010204030f03110d090b1303060509030403020901050409021f0e04060b0c01053303010609020f0306100903050a110f15040602070608040c091e1b09090209102703060b 74
    0x1030046525803014179040c10024400c00000e0020500b203a010303154442955516800c0365440b40c4d1024102d81d4141e0320079415601c049070420440c500450303071501508050b1002c0c44118120350204440e00345182050303900c09031503801c40914520030110080d8801c7c005009100c01903075013003008215805080886015405e04001501c0c90b44003840107490805280c642701c00040c14140c0003850040441c080a51654885100141002c4580090020584458105503032401e000081003001c005c48010031003403107103035401000880d01c081012082240c0050b1014071004541000818450f8401289940120b46d0681c080030001c8080242080da03646400300c5e80e600c3d0b20740c1c01c1900d0360741c4106e80042070a4800a4203101e0001a904419811103400d26260b81c0e00c100c0409036010750740d10704841d100c02d0f4a69841d802440f0342c02160a00141813000045290040d07440208011388030a4200c101880100386114550041600500300c41c1a0070803802c151494407441d1400c050103240c15607501c154100d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 889913201 1250 889911951 889911977
    0x1011151e070f140712081e0f0108010612170306060712030c032306100908120702040b0405071d01120e030408150106080a2415030f0b060901081305010204030f03 71
    0xd4116840703903070400083c5504550b205c0040300d078035034010080390100b903660450114a4848060560080c0c01d641214901076040c13491850858006502844e241d080094140d404914816024210070703c8480c000c170b513690740e4200422002e10410701d00600240031501690800d41d815845007503c0c214550f81400171a00d9007040c06101d01601203405040400c80020031950f1401d200d814500e841c4d00e051072039030155101d10b281c1c1000200c0303120303194040000503010704524291107100254101280e0410003410640001000002801d0700c41c0d81c85c240303048042c15540e018034908461541030300000d210122070300c0342c109c1d1250458400c401c11485100782c96403211100c2d00c1b1040c1078480e1a070b5904244ea48509200c0041d1080809582d66080e1502c1040b40b803010795034182015050071080550003120003c80181200e910b81c214101a62601c0071100c42c544c1c80a08843c2400401d203050b0b000ca8540a00c104d54003408048000c080e503100090000803c80b24011501d0b246020380c6070a00d000345c10b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 889914451 1250 889913201 889913237
    0x11112060a0e060f0904020a090e1c1b020d17040f03110a030302301b06090c03030405120102040e010f03030801080d0c0b22030e1011151e070f 63
    0xc01c2c0c55040e03112440c04031080c00c5060200c0c030903600500003401200c14039030301e0f02c889e01101d00c3d0202a0305580c0000d07855134591401a40300345110f4260345051080000d0109000010a010940c000d100c0c5100c1c48141013031100179200c0d0b140d950f04d40c0410a80e6150b5494280b5201a050320007100c1c0341154400550003440c1026900c0c08881e01600070382016099026103c00e400825100c02c8032079002a6010500745a42c0406017143c040d400180e42c070400e0454142074503004000701000d15541c0040d16180700b170744001c0169800c84000345c074502d00b440001c00710280a40901c1c1c000d50000e91201c80001010480d1440c018101c0f402a00c96140613600c80f0303c8985c0f00c5980a17400d1020400c0c202d0325400080002d10300507401225440381c800a080c044840300110000d10009030005054004560118a0700803c00e4200040500f0041c2c451191300354030307540310710401c0100c0d081c40700c1c850b00094403100803041c03210038000055000a030524000304040c0c0b0300107402d9500707000a400c614240345617140f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 889915701 1250 889914451 889914479
    0x415090c0f02120315060c07120212010516030507020708060915011d0c0d0f02070c1511070e090a02030d080f070e0f100e06070c0512070e0703020c011112060a 70
    0x3d81d040914590b0b40c4a045d9a5070300402c80340c075150414001c0000c01c020f2182231100f580034064841c1e200c83c40081900400940d1240e09684500c1c07a450101840b601070b03d807003850000041241000328041e91200e20580c20451103500c03100207401500100f01c1701400110b00191352802003414070030541d0b04c4510502140b141d0008903c8044070704000301d11400020400f400c0705601894010590501075481ca4050303030011304048403503580303108007404100030b0440124030007501031828502800003c12400c1d5a0003092290314803a50703e0002181013000700b0b101112485030013900312882082007d03002005418211004000820504081812103100c0d02e03090082c04002026000d038600b25404109100701421031501c14040d4117600c00005440c0c0c0d401810303015004000c0d566003075181c031080c4994404508140720658010300f805000e18621500015001040c3c1d240c01a00c500041d038410f401810701c0c0c00d841010b02000300d8580402948046118401c0006442d003a008540e00c1001546601e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 889916951 1250 889915701 889915723
    0x30c0d02071d1b0705010b13050603070806090c010809071d160804120e130519050109111608040b040b0306030c040c0909020f0d06060c030f090e0606090415090c0f02 73
    0x60700740858050751460030300c0a0f21449004000000384035187e000000e00071161000d10180190704c41042000c6858240704240041801038042d01d894504280c409407688001e080c3c0e181030080080c04100640710030030110f801340100c000540411076004245c400a408200c60340030b0343e1500c084408480c03510407843d050045500c824942d443d000d24010a44590001000803500003040740081d000580b02809401c2c01650201403075615060903202c01b034180d0390160880310586040c804010001c6011004946600d15422901030710920140343c50b440c2e03481694003d0810440101d00460400b010600940c0500400c03412109842002001d01007500c11841c0b004000c40c0300040e0070040d0541580060883c0100c58558501e884032083c086412500c19410240000b4143d070071303a90805807c0a00c00445070801c0c10104442c602d825490310108000800380c900401020502009544403900004850071300c84840c034003070036140e501307840c02000d11640107000641800400030307005001059440c410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 889918201 1250 889916951 889916971
    0x10200403050328052a06012303030702130e0304030602030907210302100e010609020f0c011d0d120e01020a020d021023090f03070302030409050114010807030b03030c0d02071d 77
    0x72071940c10400c0e55100c128038202c4d41c408242c3e1005c5011140074086140a0b10048a10321200c84030040c02401030080103801f2070227075208008540150b51082000b006c6414091400b01300f103203c0147c1d40d0700b1409243d00c02040c0e18004424009881c5010070f40b0000d9a03080100c0e103103503682002e030f0f070241200701c58405009a0010707112140d00c074409400c00e807504100380c40041011a610b400c01801c036889010351008800c400706480d40964800e005482401c4140351100007040e03e188000c1e51640c124015080c14000c0c00c0b0580521144950003506029010400854803500480b802a413a030000484200041c020041c0c5d16a440e107441c410a01d040b40e120301c00c0b90076809580c10281c00c00d0006401882c4500c40d0410040a8940c100020403c441c420750203140c55520b440d0998007078a2040e0484003000b040c4c1c181035207069a0000ea2140d02c04d14900d00440c1307004050300864194803c80030403520b9030152680360704586130001051012209441d03401c10f403c031100c103c10001000e05071044068 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 889919451 1250 889918201 889918207
    0x70b181219030515060706060e1521070e01090e060604050c0d050402030a0b01032103060608040609030315150810050f060a02070f120501150303021020040305032805 73
    0x1858403e50010b0b901424885591008075050310020f101d5401140301240c2c0c4c907443d1a001d02c80d0340a0103c0140e0070011088040c0c1d4a1052040080c2710b520041003000900080c6500f07600c0000000c000000043c07610322070094031540c40d0340c10040581440210f0b20f46034402e04021903040e040c1489a1442064022049410810070351034840c00341c10060802c1e0707898850403001d000403c0a0203542402188650061102100c0003152881c10303101403081803042c1072400d070040020642065420354071546c41040000c968504d0318068004002c3c0030546244250010008102aa5841c0305807070403034000e4492a44c5991280072200d20b5000602410b90002c00c131901111850800c1781c060069241d0500540f815151101010030110180d540702070801300e0240c00340810300c40d0a1043c40754210304c608225130610b0554501964440c203107040d50580c90f81e10b40c40295480040500385840c2c203c001280c65465549041c110799036080b07c0c0454000111941c00102500e40c64203902c5d00d03402c16511442d003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 889920701 1250 889919451 889919497
    0xa0609120305191e020d172a1c0911010e0102030c01141803130e0606070606030605100b070c0e040303181406010611070b0f070b1812 59
    0x24005030044114144002804108028180d0b8400038007860301c2e5560b51280b044505150410458400c10034130107540001000d044507613807010500495007164292064540c030f80a0104c04c1307042043d250541d003031070710400445021a00200900600c8002c21981200f42d0564a008080326015440186224a02c5007007500319400343d1084e2401d45014010b9030b042000c201001070035a00c0d025a40c21800425404011506014108003038510003020015800e006480d0700070410210700e405104001c03001000003402640e100d034115200180c0c404402d000f005c0c0d6070300e00100640415185861503a40c40440420103560003010707101c00030340040c1003a100300c6c9024941c0d4140400034105400f0076407a07840c1214488800004070500c50b12591035030040c0c1c131100b074000d814101c06800031380c108400c040046000000014000003030741d002e0030700c040e036071010703c00182d082d8420160014080714942c4100320109442034580050b0000f80380640d0302c80c8201c010810b04502c43e00b401044c01103000c400d800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 889921951 1250 889920701 889920719
    0x11310c0e06040513060b0c010603020103140402010203091e0409080d05130503030a050a0b0603270303010f061209170d06050f090f090703210e090103050c060715290a0609 75
    0x84c0388014050005011034840170044801e6001054030703140c40e912100d0820031541e241c4260118010503504869080c1080d0340000d40340c2c420914a07510422a1284440c520000d0340c80001c08004003c02c02c20592250b0314015446804c1803042c40d103564034100014a42600d5100300032100b507400b902461640d44e0700d000050040201071320090b4842d0307440b00f249103251560001140180c05045c0c048850f50009208241c1c410103c0c0c1d202c4201c1d030818001040304c504d4000c641c1c4140c5569090444000c2c960f0600c910081840501c0a001495075221840100341c1c0c100040c1041400c000040c000c498991060141c401c50211045410401c0040086c9004800501d00c2e41c111540b80140c8403000d50b40d45135421140d142c400040105c40d4040c41512415400a10458504c00e09586030030b0319600d16100c1545a01860384c0540c044e240002d440010411038407841da11245105000b0400c45d50121144200b801e4018449a4a4a00004a1a4030746010310340801110740030303a07035018031a0401e5010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 889923201 1250 889921951 889921969
    0x6171b03031617040909060605030105071403130204090605040f1203060305150901023109050c0910021509030910030b0f0f130f0e070b0c030711310c0e060405 70
    0x2045021030504c00452900b5841c003841b00b0443c0200c1c0041262401c2c84c0c101402c446001e40f84406000181806184904161050304d41c0703c00000507487c0810a1400410082d1110440c001c1c0342c1031501003040100281d40c03a22419460080145107020f203407109060703045992501016000341c2c407540d05000c1c40c2241e00390700341d800343c1c20900250400d080c5501e4120b2500105101d0074030154040314021000c1100c44d0882d0041051403001e20640c01c020b4103541a510440461600034200d90a0480d480f074001c02802e510b0346490b10b1844403500c2c0c140100d9403281c00140d400d6100310148a5401400c9200b03025104d0309020045ca2148001d248000700030181018400554000c0c401c40ca4118009006100d20900c8909200000c68100d0760005410b0520580b038028159500c8140064520280c00000ba610080d5111030001d91002e40600040d120840260240c90702c0006078800c08180e25404005400241384070100f400054565a820344501c0e104050440d00200c0502c010000b0b8038000002e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 889924451 1250 889923201 889923233
    0x30e120301140612151905060f09041107030905010305131a04170406030501092a18050a03060e061602121c0615020c180f070306171b030316 62
    0x4400d103081248154004e0414080351a14108500b1541026960401c680307440003801c021449419845d0603c1d000a040e0f02903881004c480b10804107902600ea04c469201800da00c800c48416030700d4050764038005010349000e01440e8000780c24803000c43c0040030385000d810080ba900c0715034409005291180507654100080c029162007110018403100c0e0400f0348000c1001e44086e80c0d01051a60405031a001500c0e510400f0361055143c4000320710b5450300d80c0d8a8901c20741110301d48100c012411000e8000e02203c50741042c0c3e405407010780d00204001c1e041d804441008121000c0c0c441c10303a1125503001040400d84903490150700166103810368405244010000380264030581c1524203140e07403002d000c0b41d08541011103801c08001c90f1560403501007040c210040780488540c1c000b4641c015040400420190604080c16850000f00300c00714020780215000c0c015803070519440d2070601201c650740d62640320314a00c2925909150481c541804021a464004102020a940706c41680e4032035900c204020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 889925701 1250 889924451 889924459
    0xa05010c02010e090702012c0606090a09060c091403010c051b0a050604080406090e06060d0f021e040f0f0b090609030a0c060801060e01030b010f0807120f050403030e12030114 77
    0x45010300d13900c580c0128050403d81e07000180007085c04071542402c902c01e4641c056940c0341c160156241120006245511410540d501d442e41c2d01c83e0004c21004d0712003240014189810300b03e4000702207610144800031030b014500001951300703404c0141802c0b10b28000031400000c200f00621100c1e8001101c0306694621440300320340583e00386449050400c0320035201150503880004040010032750100c07001000d0301c00000c0c0709071242400b1001404d00d22418491190b942d44075800000318009aa040c0c411045921000c0700d00c42c43e514a1f4420660701c42d028160000c02e416201140300103440389940300b80c0312042c00b851300e07081c0c000301003004030703004200079990500c500810707140007c805000c2c1100078aa2501d4103080b0354107056001d44030300307034041110b41010b290a04003066a07a110f41006006400c50802c4a03c03a2a83c0004684260030100400c14503401c0c20701000c5094010b42c401446580255000c004030100040c1a42e07c030603684005020481d4240b0060081d15180084030100b07810080c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 889926951 1250 889925701 889925717
    0x303021b100e10111c080619030f080c0d08062107050d0c21110409030e041e0903110606030a0b04150f05130c0608091f060906030c1a090a05010c0201 66
    0x2c0505103058400030b20b0300c0524226417181544c02e81c00c018000d42005080f00c000140000215032800c02502c1440f002e003c001001403100184a555030880703001240420554840940c036020141028500303031016405000381c10411001c03070312544240358218201c503010301001c0e403400c0c040000c01c0d2071814050f12109032000d000258040c0351110000040c0188640c0c9564039404e003800040c161061041d0b038019820302c2d4480000076070107070420070128811140043c84048002160007006032a05200c10094a0329424005064000ba0035440d18190001119074130340d2010309058031403e010358000e05c840c402c10b005c500094181880310760f51080c1c400000484078886617104082d16815101411010184002c1400384640260710304c020b080da900f030081c4a41812404503954014440d541048490f007203689001e0710b403d603003014005042641c1c051141940307d0400e541030b0211841405003140c00141c462204900b144192070501c6401403510141c14986001910040f84001c8228100403401c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 889928057 1106 889926951 889926977
    0x1090f0311011803030507350c090108070f020f150a0c031a040c0e030709020a0807021f0e0c04060803090307050f0a2c010303021b100e10 61
    0x500d0001200d47c0c5403d401c03200303100900900d052a03030095003001c0703038030702c8040e540050b00f202c1101c003000b10f8417038140308840b502c182c0340840d01044401000030740d1759020385410707807415a00c0e0068400600b4551400ca04203059910300c001d66105410a10219180074801c6800a920904040120a214442d0103c1449907030b18028030641c3c49a0345040107610600700841a03810140072140742689510b42d05001e0b41104400000040d510000a640c0501c0052460a003c50100038109201d40802c4640054840351006100c18410b401c20301c0c40070340325440740c0c1004041402c040c588038002601018106100303940181d00c1500f0b6600e50046030341d03402c401c00c3c00b15000841c5660040f12151580c1044404103c1c0c1c021003440c002c0000030074950003060340014195442c018941280d00d410400c185500c0b0074251500003080700c0d41c08034244c1404842e40c0b0f5000c01a00740f8400c05121 = true := by decide +kernel

theorem cover : BRFrame.Cov 889748201 889928057 := by
  have h0 := BRFrame.cov_init 889748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 889748201 ≤ n) (h2 : n < 889928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
