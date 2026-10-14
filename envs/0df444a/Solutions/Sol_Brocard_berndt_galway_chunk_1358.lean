-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1358
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:33:22.19183+00:00
-- url     : https://prove2.me/submissions/20dbcf61-31c9-42d2-a016-36f443f03eb3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 244064748 ≤ n < 244244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 244065998 1250 244064748 244064761
    0x171902030c070512070c051e041107020108010f1d0a021201090b01170c0d020d022a06100e010905070c022107061103071403070804091a09070f05031003021305 70
    0x111184860701c088400505d00f4000703440e00101d2034040d0040d41e20981520f00300080103811500ea00d003158000800421402103850540105a400280201d002c9903401d03000144030014070800c1402c90b25202da402c2c04000d0342d0110000c90100081240031681e03070a001445200c1d0060252901138200c50030005607915003c0c0000d00052541da10704030500b00c580c0100059250ba0105440000d1080840540c88141c00824100a03001c0d0481c0031101151b07801e031109003454542c031180c3d04103c00b01c040c0c41b003e031100801000c1c0c022240c0940c1150118500040015003401d51005500240ca0329090240702c507035600041454052042003c402e08031074a03042100b450074440e041c02000241001c4038503014400295071240101c1c107020b0041c00315040229100e1400340100d4096030b03440f0000390740c3e403030b2900e00344c0c802004107009040d0480f208800460440c2403034140c050040859486e640c85205000070215101e80c4002d1048403460241c030800401620303003420350003807880c0120001c80c070b034036105 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 244067248 1250 244065998 244066003
    0xf060408060423210c0c0d080d05060a0e0705090411070f0c05120c090c04030206030a0509010c08060105090909030903100608121215042703120c171902030c0705 71
    0x2100405280d40203904892510003240c656601303424030410074240c8501c400e504003400c00945850303080d00031070f060141e8030421003160020140c0c0c0e400c20104104a49508042c0000010107010300c624138400c00d404903045074090f801400341307a0701c010404102002d080050401a811512084070103c000b40010700070800d00c50030440c003500007a02c1c848035401040c0c818035030f100030396600355000303040070b10205800501070320488000d90340241c02d49075242041c0314000010300e42143d2442c62035203018440000340f803045144130b010310780581d5068109410a41007002503000500f034107600d0300c000c002d21011a1400e000020041e8000d45002a0481c60500b0f564103083c0320140318051b96208009550854061083c01c5030040e00c0d20305121010340e07030040850000c204c45450b840c940d4800010741200e900405404804a610a580d244926440c0f1054002902c84408400c1d001c20300040c2c0700c2c84441628031916500c0307512001092100a03008100d6401c9a00c192159070010340000703504d0b007d01204 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 244068498 1250 244067248 244067303
    0x40303170601110a060f1517011b1205070c0b1614040501090b2d2205031b011704030c030809061902030411040f0f0e060906060f0604080604 62
    0x2030a10300210f4039803892450b1208409131005108070307664586c42403007000c564440e070b1440282c07400400c0300c0364403501c1c41d14000b0a0803280b0240f035801c000903d200314070048542002c1c4180e5803200006100b4402c4140c0c003800c0014031034020003440d12048804101011000f50003010302101a0420000d0408001d01880d4140304103107032401c007000100003907640292003038111070844942c15250700082c040510340c4890300e4050f02c502c0c030f10507c502640c0d051f00c030001c00c2a0500740045c904080382d00036044920352058420280e068202102c580c9a20003203c148900f41e0b0414034004256000010400111190982f8150000303055100031404244d003000b030b503a401405000013003106103010340403100040d1b80c406500040c1c0d034010003c0b030b0400a42425026594030007c01c18080c280000da444e0000f403010000154216007040740342a507003000030030b8071802842d0000245c0115030b184014081c0340b003001d2440d80d40003e41044005007520b8180402c42c0103a2203000c40482e0030509501e161000e564 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 244069748 1250 244068498 244068511
    0x50c0d08010e0a05040f05030712030b0f0a0b03091504050a02041112280203091b040b01020c15091201090b070314041104111201080f120409110f04030317 68
    0xc201005006212a0240301070303000036035081c041400d40d6249080900748407a004021301a10020801c4020001d0110700c40020b28a00d0740c0c01c1014289007000c1041c62602011000d0308001042001e100c0e076440d6000441e40b28049004950380401800841074140344112420303140780d00a94400c200310701e0a40100b8800312004d46a5900300020818402d84000c009020180f4982c030f09809005034586001e00c3c20485540310000b10b4580c130701140c003a51141c0d49000d10003601c010503600520380b890144038451405c8010380c01440e601d12030009000e0051220003100c40b1800d420b210140c000d80d60004da00511180c02d0002003100b0380e0901e03082c1d200c1c08019001c1020300d42405071642a070b48802140550164003c034003260b11000040209006003030988a980408000140100011101200150407610100c0c1228406440d400b03149498403181c503519401c0301d0041008000030200c2341c100518180c1e0421000d8502480c4456105059005a0086010503200c01041240e070214031001070b030007030307 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 244070998 1250 244069748 244069757
    0x80904050a090b01090e0c040c050306040b120a0303050a0906111903110711041410050a080703030e010f051606052202090a0e03040504060602060f1b0306220c050c0d 73
    0xa0541e0703844903100f00500954072004e654a4215222a01c200402103280401920410441c0920100140140c0c022184140900c1c2012800045414010b0412041002c0300c005130146603e580e40403006050003520307400d8501d0f1982c0004001c100948900c0c243c0206519800b540c88403e46d0000c405600910304440034149002c004a00a450400c1190b41075070303121514120b103003000c400080041041c002c0c0d03480c50662500030004140700184129040d1003044440c0084242d55200c0e50f603644106000060014126032801199035010f06549100c550141c203010381041155041480d04075403602060b01c2c80c0c0c2d00c4000b40590884400c5681211854150030199010b201d87c01180c8198009000000302e05d0345d40140c900043d20a20a035005444028414007125039910030080d515042501c01014411410020030310200449107500c5000c00321440650071035070344504100700801a14180c9401e101d440c200c04e070f003d14151050542240013030b100c0d1616060381d00715071454040b0000d145810300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 244072248 1250 244070998 244071011
    0x30307030903200d091e050111010f0905010c11190b060d080d050601030507031514041118030105160c02151c1a0303090307090216050d0309050c18070c05030c0a080904050a 76
    0x80d010070360a1b099503800e080c01c0d501009040300c15401403074a04001c00c0b415141942031404c116041d0040349560a1541e5550362110b0109001c903151104585c07071624400b8040c5032100000e5000c0009548900e009050724140116034541036001c1d8421a034800ba05a6540d080002940c0c15209154108000c2e14080058a07403150b02c2c3d5203090030034005c1f128207000c00001403496070341e5604050800c00b20144015210305041544102c0030350301c0c012081c17195003094000349020442101e00d0701c101c90140c0d04d201a40106400740035011030504400802c000d01040520b81038100c101038028418422000050704184040100f5807041105003182d10a8000b046210b005a800103015001c2e102444070050ba1016800d09115258121800c024507901440507403000c065010361000704064040d030b080d15042400b00003080649c0010032001074070308480741c021880d003078405c803032058289110f40c5c01c4070b1400d0850301d141c91030410728407070843d1800c0000a652a050032b141c0075164001304210f00a1211 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 244073498 1250 244072248 244072289
    0x40606090303021e010b060703030b030c010503100315090b090f1e0d0302210403050d0f1107030c05010b03060108160e0601050406111203070c1a0108030307030903200d09 75
    0x11342c44081800c00084004110744c41c0d0000c02075108203180e0000800207a91200c0a150145c054070741201064802e005040d009c003a50f5018004070303880b4000c12589050624255a50030316442d0403451441d680a40d07941042000904180c9428010004040140104110101031914165a8040c0c00c000d0b103c244400100703c09002800741000c10b0181405616100c06810904441c0080325180700c10010030307810b1000b8150058020a018110598240400c20b01c00c0005d2064501c00d90b040030808034200511000300e8030401e60809020321800011501d0100240000d25140d801c0c0c00c1145990000340159002005440d4003500a1a020308080b0807480d0142c0080d245000d644146d02c288142070b1120b1456600500c10900c0c008d40c9103109a07144d0030850401000032000c2e071001c50740381850010b6540400255141a030494084c0d80c000c2d4615030300c0c03101c220083d01d5400411024420000d22074a04c1444912800005d100840014800580c41d05401440d00718103603c911080030100112080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 244074748 1250 244073498 244073503
    0x3070b2b06240f0e010c080a0503090d03020a08010e040f0c0b0c0c0f0f01050702030a120c1e0c090b0a0e01030b060a1703040b13120515220609060b09040302030904060609030302 78
    0x100301e40c030781048849820700c4c80040c2c1c3c290044402c0100103150004140040c0341d0840c001c1c600440e019000c540304406152000c1d000c13485420640c41c00303d885500100280e80480b200954454411903000c503a0340442d94481c00038152a801121440c100401d103494800c404210107081483c0444041c1c1c03400381e042d000302e421100380f01c01c104d0401500007110303015918100001440907504c5000d0701c2920490b008000c00500c1c448404844040d0382040a01101c1d03081120a0b00c4c540d00506494011440c000000c401083c05400503a0041400c4000040401d10800414001c40c0504d101007154949041000242c03190751304001d441c100c403210224400c1c2c10000c15101641c1810310b90a0381c070001000310720315222050740482054005030b2002c0c020490045058030300c04c0c3c1803400743d07005500c0d107900e40d00b0024204500d40190188403000c46010404a03008440694002c0078001485074080022407084001100c00741c0240c1d0000940100032305042c030502c0300400300c038940f01c0d503071a065990094 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 244075998 1250 244074748 244074767
    0x50a2405100c05060405070602120c0c040905280204050108010c02030f030406020415020c041a03121606022b02030c0a0f09050603011701061403070b2b0624 69
    0x41c014034040301e040150a000714015490703180c0010854445291500c0c00c0c95490401d0301850006000c0c06030400825408401690800103000300035041032020041484000c0100c8001540c15200b40140a042e64418515813013030004420b0303146655080e140184420740d041a80035400503031402108000040d800b00940d00c0740701c40d00d076000c0c2d960745607418482c01030301858000e001030440f008101114260001303910324001d102506d0a00101207106c14052180c034400e02840d405400604251402800c078000500310341090103ea0141c0000a440380012070300654411805480625603060703044000e03a6041c0310203203030110709600d117151480c0c02d82c00700d0007081660000c1c0800303e4545200e881c000c15140c03001e0107000e804a0303100d6a41d030a0700d903c09070b50414000301d0395280280c08181100070000f40140d006005d002424800e1810a8170402540061180c010000800d0f403015240c80044802015110640c00701150b034900341100790381d00000d923200701185206451400c074510740c0c00c140700c034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 244077248 1250 244075998 244076009
    0x2030a02060307030204030203010f1b020120130e07050304030909060303020c090606191808070308040b22030c030308070f0806040203060111061f0803031009110408030a03050a24 79
    0x100d4490310f41c2e80c8250301070b000f6500000d606d1750030404041407104466003d40d0031800000c51101d90101111802e178201c84e00c101d01080000300c0381e400395444903c004000d04082000d08031070b00070541d0312049000d9030030040e40d8100001d200081440141680060408040c0040c401d00700202499550003035603520f20400c1c510f0151072440d00195840d070b50841511582010302851072912400110000c041c4980e034122503020350400c14001c40d81c500001601c005480d44003d482d40b0b040d0030503004181607044805c5004480d0000700070342c01003025102c8130301f000f14892006c0aa00908516016001840041108081080070008421041c2c1d0080f281500040b050b41c00603502e80b14200100d800c00c0401681800500c608010301400341c01c1110309001c1c0c9041e0001100d20680c8a015190700d0340300958000c0801d9242010910446205500c41c003110074a035012203152075500c07040c03542107800444100001c01c0d03941080010070344050286003841c02e10413001c0088001640c82650f0740c004c050003130 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 244078498 1250 244077248 244077259
    0x120706021b010507020603090105040201140711090606090a03030e0109090c08060d0326011818110a050a091a03010b0d111306152a06050912040609080c0a0302030a02 73
    0x41e212030b4015403c0303818003500901250380d40c0c0b80840c0058040e00080c0c40485c00200a000e501e07108060400955050550009803800340456410030480740c1d20000d00b40c2580314804220b0900e1550b10036074040001d502c0380d110784a02c800c6410000d0242d4140d40d0041000d203007401040700d10703d030703003c0c0c59141c1c4650210394103010700c0031a0808854101c203400c11010420b40b01da07001c1012080404256040b147c41c0b40070160340c0035a41044200380c420803001c5040d15851240382030001090314480000c0b040d400303040340c01c546176a1000101800d200f907100c0c207030f4a07941d113400e6a044640316200e2400c06a0550091040c22040800315004a400d5075019080702d01007815101c0d10358942d9042000804d04003410b01c074440e110f4442420302c4800e0780141c00814441d0807041025442c0d1000c4100040501d2490382e90f48880c0c0e12120050400100000110701a651082200d8068180030300050500c076526921b400307040001081c134211256894030310584500c0b500f000140e4000a070100d9241c0c0c143c0b00d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 244079748 1250 244078498 244078543
    0x1d0f0c09091f0f060c11040204061709010902061b0105061e0111030f0d0c12060e1302031e06102414040902070b160813020907140706090212070602 65
    0x100d0b00142c881d50490b0000c0481034100040c2d0070b900a01ca443c409010703285400e0000300c88010001244528400c020128030f86400c1c1c049a201c0d8155a42e5112200c50000302d40c0380b1082c0d00040740c6601240300e00003e00035402c1e511000e91720910400c1d50000c2c00b9204c0000103004030381001140f04003c41440e04001c0407038101d0022900030b0007581c04000d2141c8101d41c032078180350443c0010740760302500790b000070b41071807000c8620740c006006801c22901541c2072a05540c8820018a1000140300d0003640c0505c21846840c6036002e500d400f407208104000041d002e9800d00088820b44450306034060025402208401c0103002038400c02c60519800c1c50030000402c5207100141c3c8690700880c0d115072001440803c9403000c0c0503501d03801610543e40e86128030840c0b000c0d03a42c140c3e011041900d10701c1754041025401401414082000d680000c0e0301e0411000e020412441c0e0006030303101204c21680e0940b120450320031030800c5010f0400e122410000b40180300e041000c001e603904100a001c4400c100d01c3c20 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 244080998 1250 244079748 244079791
    0x5070818060c090d1a011a190f0512040b010519080319020a08120f0601030218040c030209120102072010030c090504050f07021e0307020103090c1d0f0c0909 69
    0x394003410b185d4005640c00046035440603000b81120300f4840c1c440b42590841c02810300802a20440d04c81c0c0701262034901d5440040709007100d0a0480d110800e062000801000d4141080038818038407540c46800d0030716841d0304200a0003400c900540c1c3e6048581040380302880030010100a90b9001212800215030107803101200b02d1070080d070002d01030f00c45980020307120380595038090114031900c2c40f100715118a4a50000440403071103086d83c017402040b0078038a132030151300d0190003006030b5500302d24002d4204004240041c502c01d42504c10b03441c150317500051403002c2109600e0078054000d1800c0300818110520720202e0581050700c0c6c031807804c069560044002c1a4090001d100141c40302070010003141ca810b4074442c03600701007540c07108054407500d01032607001103118032803051100040c400303141094007031713170055010703290410003102d210160000c04103401a03e54019900500c3e90b481c20180307800d180c00051244100540481c0b03d441040003d01155290b0144482d042900f02400020618105 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 244082248 1250 244080998 244081009
    0x708120c030909010e0702061608010e04060f020c010b1504031a040f0501330303200307060f0c080a060317070503091206100503010207110f011e020105070818060c09 73
    0x15001c2d01e0340000300b0800803d0114240401d50700c03520b116001c03100941c4071138001c000c03007222140700380000403010300044c080a070701c03a401c0682040c440d01001c103c081c403425014050740c00180b244249a9511901e0b030380c49181c11070000c079004584002031460b0a04584650040556103401403425039070b078201040c10411807042441d082d60f0080000c002290340000d035603800c5103808200c08100c9405210a0800382001d1800390f040380c0d41034845d0441b0340d02e94168032000c0c0b1428151001c60f40018800d02c4003040391809460b0801640d0fa000081890320113034081c00700d0f98050070404540746400814000198480f0391720780003040340884181c69044034546103182d885480ca030150081400001c40f84110400103084e805640c0f4440345044031a1140149400c0380141c1d8006440c0481120680703016043c5060300c1010044189000b5903010342c4040303881403125846141d100141e64513001c2000b850341c0301c1c60361034005032000c0c0e4610300d03002c80080099403903901a00714010700d80001810480e99071034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 244083498 1250 244082248 244082257
    0x1509090501120206071416050906010516061a1504032a0e060607060212010603050603010b0303092403010b0d0506120a150209030a0f121e050a2a03030b030708120c03 73
    0x80070b080f00d000d42080203441e407e030165881458020030100011031031940c09541642c18407862080202441ea5083e1a1039018004c140300406070700342801910262915400d00c25110b0030301148409640d64550b142044001945001c0c5040c021003c0c07005214030002103083c00304a41500c980050240c41d07100c001203a51151210042c00503200041c1a00a4013070b0108082c120313500307528100400d9031201c080c0350984001c0ea41d45581030f0010408190949041d10404100c0710028801d0240321b280901085510ba0087e044140389103000300d008010502c003401216403040069840b0308020056141e403680d2007142d01c078003c0000c22051000c962104030b507416569480d0000303048400e2038540e802c02c80c0e0040c20031603040c0c4e42c15400d1007802807124061001041680d000d81c50083d0202c41c0704904440c01e800c440100400c1080003440240032090540039111a441c128151281c40202c5103000350888444c4400c07940681c01001c0100300e081d101255040c5400542d80400c3e82d51090394400c1405e510a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 244084748 1250 244083498 244083533
    0xf080c0c16090e100b010507021203090616200a09201b060f0103020f090a0b030703060507020d080709140a0506180a120804090f15150909050112020607 67
    0x400c104000b604400c540c20020816048105541034604903c04030130944524200301404614108000401424a02002c40c0054102c0007030728245039500c000034405601c1840e1000880c1600701e0f48034140700742205a480324084a000c422501ca01c00d40105030817510754810821000e0f51100200f02400400407a08200303664042e005542c0d802c886500d0388400780036041c0c00b0151040000248681c1e400c5104913041e03c0c1c008111882d04e1025000308801c01e81c00410a00c80141c55401040d82138500b003045401443c40742002003428603100400a01d400e1078440300e00d04004c810300500c101c0c1c0760001c4c00c0c0c406945240190300e01c00c00c2030310701081383c2d409a644002e400100004152008154405070710304ca0000407910850010350781c100c03003800c1c4d080051300038080700b00812080000c104180e2020145020550000c5600101c100205141086035801680000b10b04500c1e012940d9100d41501c014290180307040003039505003201020804007600c4000d00030320700000c1643c2801040c1005855260 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 244085998 1250 244084748 244084783
    0xd1e02030d0906141e1c0204032018070305060d0f0507051f0f0f090b0c0a0314130510200c030c0f1309020402090a03050312070f080c0c 60
    0x41c8400005009100c039108030400505002100702c807042800045441d1036000103000c0200015801c024850380c3e100d000c2c011007040310b801d003645a0751418000f81c40218003513511a810100f4111012000c66049180f15201c0e60001d100d0100704984060b00d5034010040f4600001d441ea920004290f00380805140034001e105c00600c042d003003250000d4404141d8900b65080400c088640f0030396412007803280520402b16024000040e0b01d548142c0100c0130540807450418642c1d030f9691401c00c4103901c045242981074201815030428107070000170020380200c0c0b00d07155074a8241402c1040750840c009016141c8074035a00c11000034903030706c5140810103040343c00240220b07038103c9251340d84e603455400d15954001c3c00b40c3c6490940b68234008034620800b641c0034040c0242c80391080806c000900c404002203a0140d0300788090700890721144a900003451140c40190740d1307290454000d44044800030a03600401002d44400c08a8940c0001030075000000c11000f181c40d2503e41c004030303007007205481c005801e01c3d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 244087248 1250 244085998 244086013
    0xa0303091d0103331d07080307030f0e030c2805060931020a080906010e070e09060a15030c1101020301120314040801051312030e1902040204050a060327020d1e0203 72
    0x280308194804174145282202c141c3c90f6210203040d03ca00580030080c0c0480c00040a090005025194200425800400b56403054030301c500000c00d5180c800c041c8800740300d200c10001c0d5800c450b102500015002c01c4403814148541c45000841d12004125640c0303188629031258249000d01020b0302903400c0c8542c000355203485030860f000f0030b4444100c0d400d80c842e205281c00055030b5400340f40024001c2c0c100e80d480200e0207210300305010540c100503082d21f0700f2020b446800a2490441c450f50400c8171401e07503020036010011a0001c20140041c40c0d42c13821644108010805034501c0f15032844244d6060401d5000240c515016400720b015a80c00107035154200340400510240351032100510328483c22042000c0b01461804034211071000d4018031003603101261412803285c1031050080c00780d10082c0058a041d850b0000304951f00c6c0d55038040e0000c41d03164040103003990616511405443d12b08600d040300c4140c96000912590a01c000c042c080312104444200544000a0340b442440d40140459113003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 244088498 1250 244087248 244087271
    0x304051c080313031d06030a0b06120c03090f0c090403030903050c010e030913050601020604020f040608100501050a06050a0e011b08031509010f0b0304080d0b0a0303091d010333 78
    0x64421240c3c00301c1c00162021400f55000d424100d4060410b00d01500050030340e0340d081c80381c40090650030000c1354403403030034841c004100400d00c1c0d142c0e1190210251658a9042c4a4003140c50000c0441420b000364010449484181c0ca51865040e40203800d0326010941030f807141070507100c0f07214140800b4842d5003801c0510b825400002300030308003e0b5040d1400fa46010240120700308461040c2c80c3d86006070003a0001c14013503e8010401c45480c00c4c02800011001c0e030310303480d0524203140c81c0500100b258036400100301510308082140020000ba003051440e2104448000f0044e1804420080c188146e0301c21200721000b40d0403a18040c0c0394820030455490030000382154071a040c03590268404c00082c80081542920840340000310f032013030007055003542c076282d540d40141d0304a03206902a0554540704010655615440140198041d80701c01c3d041a0400458201110802d1600e410150444004000103194406080c055611604010450700070a145840c05d00109a007010082403c00100f0f645 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 244089748 1250 244088498 244088521
    0x912010b01080a0e0c0904051612020f03072108120a020d0b1e090405011b20061501030b13060b040503070e010305031902070e01090207060b01030e0304051c0803 71
    0x300880c240c036454259943c254019080c0c40a920b2080807030782182d00710386035600346030044682251103901500c0c042001390300a9545850b181c0e11481c600e175006405c0b0030940c200071441e00e24000043d0302a10070305092104441e030032881a6480d10110741d507844800144000103058079605a50105e00001c03d0800000c800c02035044111a034010500e012180c42d110b00c0d1218044c0018072102c0080030207402400200070012800500c2510076548880b01a184907121050810000c6561345800c92a801c00c000c801103a80f110903000d0209510020038402681918405090032080903e00403c9038040c00c00400c2e44011045007403403910342403080c0801c15a1081000d041621419001c41c0e445d02d9560f10300b6110041e085c8005801c0d80c1003000540d50b00d40d0840d154100383c020a004850750355644403442e01020100341d104401c41e0307501040e20341c1000030a0041c0c014108003441d05000780c25440a10a880f849a4446c0707030312034240500070020030710a52000c0d4800a0b004520345490f49465070f00b200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 244090998 1250 244089748 244089761
    0x606050406030b030a110103110c0303040b041509031b0807061a1801030209011707080708010c112b0912060207140a0c0e0406060b0310030c05010e180606091201 71
    0x1800b01e0b003415030a5109042c000b40f02c0001c0d0b5000089000200030520055004207005c005541c01007604200780300641108000450044c1d01c6400000d107039141c2800c1c171001c00b180d0031032252445400c1516110120354400641300c50444060b060703940440092524070f015210700c60b0018440e84c1440d10f501e600c4090003400d05904403040d100c0740c8041200700e0b2000b148040c24000254401d4840b801400900040e6003c0103507400488100d40c5040c0d00c8260305850f1086a82c0224641c0c1e444118080c00f0035413001c10000c8a81882008203a803490075a140410102100c090441c08210410f100201900c108002c000522030b640c00c101f41010f0038244800a54400d010607035403c250301c900007100840c001003260383d40c2c0d001b00814807440c2c20461481641c1c0b1003d0410744101d6140d072000b1a10040050055000d03003036000749401c003985149815036a000c041c0d40300e5070620203980d114000d0360329582c1074005c507198050301c0080655910000180b0754003a00e980e05401007034025010b94004415030250b03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 244092248 1250 244090998 244091009
    0x60a0606110a05070902030a060324060f050906220e0319140301090902060f04180b04050705070807060914060109050c030103230a021507020108010902030c07120e0406060504 77
    0xe2034a1541c591005a9605200d01e0041c00e1383d01a80c8104618041d5601554002c148040041a11507982c0c8810f4100c04102e01c50601341001115800c54898051140030000c050300380312001e40070700e443c0015070003010051041c3e00804d074603078414000c0d901d42441ca00d4032001e1628104038841c030b01c50520790340703811128100001804020803075030124024040443c982c403050b06000d1440e0309040e22072000e4005a90100d030000703001c0c44502d82d4003806401500241003800035840d1060b1940c2c4140c42039810428549003c1c0d40740c84103201c1d890b03501204607824036400c80200d0b60364001c20b140050003808141c030050103030301034080e518602070000300e2000c5c100c842e590b800f48002c0d02d81c0c40105074644020300c0300500e0002c1411440540400340c4240ca0800c11005040d200801d10325001310b210010821104104103800156801c1150f0b04038041074003501404200b1402e600e40840b27914103038803400c000038024080c1c071004003080c2485214018030044004c2c0040c04141e03a1900050000d8000d4002d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 244093498 1250 244092248 244092257
    0x11091309050f030d0e0f0d0f02030708030f0702010b0411042303010f020a090e16270303030204050301110310120f08070b0411060918060402040801020c0c03060f04080d1d060a0606 79
    0x403015445c030000300020708160b810041e16a010f14250b050750512071f45403c143c01d50005014410100354448007542c49994000c250300d1540c500241d0003400c480c403160340c0c1c5124515015043d03100f000780506840949010320750300c451007105004400144a0115400c0c0c5e031540c00c00480315090801c603005007202c00c040d52102469a911090301c5001d421003141e0004c01200388503001e034403491180f41406890440500107000c002c60390068620881c00c0d5410950100390001410030041c1424451015261900a405070550500310b650150008851080e4103440750f031090aa800d0180340403051035030560180300f480d503e815900e01030f007070080100c600f61280e041525008409050a000300c2c0c4641c080108034650b052410910040d06030000361451b60401d5003031101140b4a4801d01c02804030f001d041c80140740000c2950f04052400342c0090038074001e80c1c40c00061200013054401502c466080c80709000c20b14015083e004d08840920042205030740c4203d40501040407160350040e0f080c1e075060342d80c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 244094748 1250 244093498 244093511
    0x6030813080331031208011e06050d0f14013803130507050d0503030a0c030204060f230d0c020705040c0507020f0a05090405030a020607020111091309050f030d 70
    0x4099103c2c001d50107100c03d400b0801c1c0609000d0f540440f02420302e490701c820802441d076100e40301d18405020440200d008030340764400503c0080c03000d00b940302c262802c01301100d40050414100030480c1c02541100306580b9182c40036102101407942101c502410340c000e031040d21b03603902c49140b01c9201c284a40e080c002480903d61911036610405000c2440b03021624151842e02d426414281c0155040c50a40d043d018141d4007284e40d0380d46890f03003050140102c004644a04001c5207072401c079203400e0740384c1c4145481040200444e541211070000c8200c55420128040c00440c0000111411450a00030a421000452007808855076100c0030606020364202d8059941b1032017030000300c035241d4203440c0209006000400051030905801005107030041d00c50800140c0e202e020415509003510103d800e80c0002ca00c00c00c200740e0400c030302c40c1d0205003480284500d1440180b0f4410031311803005603034080c031011600f0841d00089038020014040d84801100c05031002a00c255840ba0002c240914183d8140003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 244095998 1250 244094748 244094759
    0x151803090503060c03010509091c0c03121a0d0510020403032c0f040b01020109060e06010819030f030506012309030c0103050c030106030203060312130609091b050c1006030813 77
    0x110320780700c1e0101c050411701d9a42802c082024410004004942503c500c51403000c41c41030840304010114290384030400b00c07910618029200602d0401e03840b00043c906046508503070300c100d290080d401400d81c1c912101003080d040c1a414440142282801107000140000806911581262410101e043c03940c0c1000072102d02c00700c044501a002641c44800c0040c403c4440c54198810f4403403500500000510782c20030350716201521407500c40810503400140041000d504280400a1174205c1d07449014481030403550060520301031419094100f5555100055030f42c1d0040700038404a10b181c101c43d00d181440e00c0d085244035442402007074002c0c0518001952194001c5c007440d8000c5001070305140c2035a090640c200c0094200801055051084120086901c49a2001015294849d40740501280d081c00b2001e040500070750300200110740340481c601c05070f20b003800740d0300f60101031440c00603600c50080448038900030514142c080030b545010000406c0044001c01090209070249035007a0866661 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 244097248 1250 244095998 244096003
    0x30309090b0907031e0612060506010f0206040b06010912120306060c03020c0904031b060605100c050a02010f02030c072904050108010b090402070807080309120a090b07151803090503 80
    0x700146600031a48001003000e41c0c2c083d070821540e450304403080c0c1c00e140c408046054140e03001a84960b6060307900500303440900c4500d00502e0760001c801e0a100e1807841050780001e540d8a00144043e040700f0b166004101c040e13201d062500000c082c1980c007001c00d09070500b001c401c1420340d81880004645000000118039000342540307070f404d54240d00a012084508400c4c0080c50500410071400c204070310b50040310b41c0c65080f00d01545c0c01c0c042c010002e0040d09040c14040700c2803400000005020506908100098000440a141650a280085c00100b20b03100580c51030080c495994080e0154031000700e00c0512450141c01e400d10720450b8211403481104040c9000d22550081c107000640c454010b2001d01c007218014813000d000584014134000c4140c40c0c011310794000c21403c8854500010038454440030800084440c004c5554882e89070070700c0b000e00a8146076140c4a0b000000b0b80200f010001d011a010104680a8208a00b80030300c030000249200d07160480c00b41240845c0c20a003003c605030800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 244098498 1250 244097248 244097261
    0x907031509060b0309100b030a030815030a080d050603070b0904090c1512140103020105040b03090c0d030518180a0e03090a0f06120c050912010b030f030d0b0f03060402041d0a05060103030909 84
    0x2401812700f820741900c0071981450020040039421250000c000243e0320200312840b00c0c4c17400b94045545840d580c036100030a4400c05409144a50f101240c140004510081100e19504003103400003803c641d1450003403008080c1d41d1280e0010500d0034030805843ea04881c4d01c070000b0b07104020030040c1c0d0003484030000a4002c00e01002c0d000500c1844140020b042d01c40045811640c201c04888856103100002081c8a040d010b04a00040000c6030031441c2e40b01070050440d2400c3c080780c82001341d861020314000c1ca1880204844d00194640d458042040000c0c0200d070511200509403154098440c80c103800071055522a81c4002100d0340110315035007181e0310485818920980d40d0314070b004590350410100c0c4940e00e0b200d6540c1c1d503031841e06450560f41001003400400b1400007542e00d448003441c2c100c04075181030000314040c4000050410443c0d401040e01540164100c50008090a00a00703403022a008100150090310174140c008090101c0051150b04072032090313451200603900c510310802510f50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 244099748 1250 244098498 244098521
    0xa06050708060a27051f061e1b08090a050406080303091e070302010c210f0e180a02030709030f0609150e06040f1401020a0e030c09060907031509060b030910 69
    0x1102c1c0113100000b810350081900300001c1c025000000035036400c0500401c90543c455408175030f142440c40348000f14100040600507403070070510300c1c1c1559600e2400811070040b4009001c260300040c801e105a40d05101c0002412014004002160b101d5900b280d03643d1007a581306641c3d03c1886164100d03d64000c40c181000c16851000d0712107149194015a0384140c4468122032164020300580710790000301c00b0003010a021940c035980200f0416801034035aa04200c1c08038003899414000700b22004811201c503402003d00c03e001640e07076480300002c9546400540005004640d40a000e40900c08170b60045c256840c042c2d07040f41810810051100c2c1100c08480d4050502c1d084a0000390220b20940040000140928107052641c1c9030400c020f803c980c03010030b0540104071300459031103442c101003209000c1184160b50384141c074144140054050100100345200301600e42e1000a40c101c080d585000003042240c0d410320100b503c403c003000703041c0c00032034000c5894800d1180b07060b0046214000ca840209 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 244100998 1250 244099748 244099799
    0x50301060605120601021903020a170f0f0306150703020307050c19030618051606020c04020c060f040309051005210105010e0d050c03300c06060d02030a06050708060a 73
    0x10480c100703003d41004000e1000e819402012811a0000000345c66501814442c0e4007a0100b09801e00d09079a001c2e06014000c011568140032416060500d901141c400c41c0040103002d840340d5a150020741c0d652035100d00201b5910010031410704160300040038100c80d0b40700d00142d402c41404201402030191035103464141800790b01c0f0082003c6034040d4400350743c0000c00300702204164000d4491074a40b41c0705141652107050280402c0000e15814400e605903854200d0341545012808600306548450180805500b41e4a601c04034041502540c180c000800000d012100d0300c0405190140c9070b50815064000130301d46028184500514645405040c0c400585808038200d84d89010701141c0320100782d0032120340c800d090100042e035400b04a4500c0c0001d265441c2c101c0e1100040f100e241604591002a40c050b10911000795a004049541980700b10103070343c0286014a84e00010345480e40e09540500000d141800b403005065008481d031340b003448169503400b0041d40c2ca03910a811001e1480b44e80c490034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 244102248 1250 244100998 244101007
    0x10902130e0d0e13020c030d090b160c0b0402010e010c1202030a0809030a1d0f0607060207020f03031216261f0602100207060e1009030314040206030403030e0313081006050301060605 80
    0x4213540c1d0140c04480340400403641001c21218004046803040e05c4140e1701007400a04100a0201c0d034035620300c00850610341100000c3c8282d4078040c541c00043c000a0610100f44041c181d00d9104440703142489400c030b009448120101e140281d145c0d8030900000e000603400d0400240007600010440e46004081d035a42c920318008100c0c000c6230640c01c0100150b0084103414000b41c250340340c101500d5910700810005a0700c81480c1304112580a0000c0154043e8000b8404d00d0a1010f2500d80198010300e24110800c4a0103103220446100700b41c01c41110300710f81d4100100c4054115070036810711600d074048070b020601a882e0860846100244202d00040e40880519186080d04c0e8005e884643d00c240300226400c4045804217003400b00107601c0140079641d41035880c0038181d05002d07900d00d140f4003a0118082c0c4c100744d0045002844000c0c4041c09058645006c8000214100115121040440c00c20003c030740d280c0320307050303100c003d512107042041c2d05040001c038281c41c1c10305c9607500300d51301900c605290 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 244103498 1250 244102248 244102279
    0xb04110627040f02070302060f010e0103230c0402040e1803190315030c1d0a06180b0a0f1d01080c03060105100903080301090e0609120901050c010902130e0d0e 70
    0x14108900740240c0054541c20f0103010443c040c00600364251003600608440c1c603020790030800b0010141e000c07a480c0d048c21001007010445003101c06c003200c0d00030042e1201c54040f0309d441c180b0301410f40d941d00d034219100040005002400c0410580a41c008540d816130803c2ca1910a0740d5a000b601999403e0207400415601018005e80c0100003488081e590b03000041d40e252aa00701c0481c050b405085460803424105a5807030682d0055030b804001c1103000c0001c1070074814031103c41920b0080c0c0e42c0c0703120743d04c0500b1074241c1d641c41100001041103815102d0317195143d0005401904a441c08000143d030f4041c00031440e1000800d14414906018000300920380c1fa1008100f100d280c9003003510107101e855440400401d119800540c06811208030109242c510f0812240c0b9200303009044900756088002521401112101150303900d09003468409e8849407140a8240108200900294086044080203a00340d620b50001a010404c690640d000c0d061404002c0d24004d40c3c921202d40d10404005440b4007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 244104748 1250 244103498 244103557
    0x1050705180a05030105091c020d02100c0e1207090b0102070e0705030705071401021b15010e0a02160f0309081605010c2d0203010c05090a05040f180b041106 69
    0xc42a000b44802c541540d20070100b821242c0035201d081403a00404d00c54040170b540001ca01841100d80e20080803400f5020400946403a90110241803060716403070a5402d0300d111300c030400e540d21002032401c125007100340d0303009a407201c1d5032254420450424807000110760000c240390b0304a40094946061036a203000341240c15900041144040c00424004480031440c0103011034074100500000503902e040c1e004a6541c1c404562003440750950044010903d485a010003160450325a00b1652800e515400c0d060070283c01000c2c0c04000e860a4030a1000504c1403010710a00094002e441e034411160b03e5164040d02c9850f02c2c032242c00c05a421a80400c0554410710500d401e040c000e0519458041e9a082d135007115140514804e0160700c0013240d60f0381545802c0c8216a440c2c101400c042d85410410f0012840040441c820144140d0f555120803049500701d800c51850b940942401d0442c3c10f503e0f1415030f624560079602507510300645c984600150400c1d2048a9071245440e9480e007101111406020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 244105998 1250 244104748 244104787
    0x908031305161205060a0908121008100204090501080a03080114010c060908190e01020705370306060609050906061b030f0705100b060f0d090f0b01140301050705 71
    0x11950312403510000c54440d2207002c00400b604107418403400c0615541461413500c2000750002020a1400c505040000c001404503100140c1240c0018019910710b2130502c0c02d40403951201c2440d0103085015a41c08043e40d006105440307140c0340c2084a81d8075540780d96613030503184034005c01040c0f070400144103242c81c101d11041160b6052600c0001d94031641d4854059075911002112008e1020405031000c010083c40c12101840c41d1030113000052009000039513460403841050300a440003030501d080c030301d03148002e280d0383c0882101c210124040d05110710490035841c801a2031442ca082c0011036064483da40150403a00c004100c1d000700d07101c502c204500b070390000621020401d0318003003d01c03140381d003880a4904142a407002c83d454a4480c10031600340230000c03122540741440c040c181d40941d90b41800fa100e900c80b5030172165488001104500c1c00070180100c02030007510007282c000c0d00304442040d0b0a0f040e242d4041c4035004410480e403c0c582a99001d80c5c900004c1442400b040d0f071024400300c5c404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 244107248 1250 244105998 244106003
    0x11446080c0d02040f08010b010f1e270501090f03020603070e040b0a091a0909030409020a091e0501030c08060d080c030f0304080301060e10170612010e0a02010207050409080313 78
    0x11442c20260b490440202c0c0e00c10340c041c5000c020000c0c001c01490340300313206170004038a00f030818003412180b50070000c0000111715901c4803507900c140403040780244241c88080e00e407011103000318218000b9680b4142010201c3c03084500140700306501140d51188640494112030f1b01134100c504503220100217890385086405403a400941d174843e00403150351103100c054010250201e00141440c0340e0001881c4103541c894440d809610580107011285a0000456048440b641401a120009104210349031040c56000000c040892445442240304c0c0b181281c003221001d803810000701c4601941510488401c50368242d00000898060000c03454440c0200590005101580e1a258502d94440c1007034005075416506542c02000500006422882c40d0100c3c10040354648500103c2c000010f00401003d2004c84002104038041062600d60701040e03422512408004d11204442c3d128160f5605c03000c00c016801072007404070000356420907201d00d00340b507034002140c9480d41d51449600b0f00f0074003108408 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 244108498 1250 244107248 244107271
    0x61403060c280c0203150106030e010b01120207051e060f0106080708070c020a1a0711040209061603020109140d0206010f05150304021504032108130f0201144608 71
    0x1c03d005990170704c43d6040881c55030f0602e5000d941050002401c50349001284181c5078940b100002c5203a030001c0c501c0311180311091026a50340e60070b19149003852405054006054007404a0b101514404114a441480c04100f01c003521380c0da5102c100c82c031038000d40700c0c000441c10131400b18429612403050580d10f640064a14024640c0e11140400081d0610108480c0e813100400c1880c2005003c42c0142c1102c0c81c1124254103248140300059414071030b508049071801c05000031b03182014000c0d0400790043e500511400001d585c0f90b92416100c40c60902c0340d0380140200700000c910076003445424002d985018059221200b03449079417600750360000d0026640400ca40100701c1100391602e0082014511941390311007000204d088408103001c140658400340074244040060800c8444000c0b0480c0b50000213484402e0024001a542d603500000c51103803807000001c0d010004000380c3c41c400d04101d01c905405c1060340c40480c1010008403840000750040f1340880c000a105071090003001c2e005207800c80e8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 244109748 1250 244108498 244108517
    0xd170c130f080c01090806060f01110a020d03052203050c0402070804050a0b131a0936070e0109030213050c0f040321031a15090301061403060c28 64
    0x12808101c1c503160302a00281c2c1c0000c04058035035a000360307544c0045c140c403030003080b00c2c2c1040c0c00040da42204003403809041080308490b800c0100d000304030304c1e11019000b0308060710541710b42c24020709552103500c03845101c0c0004c0e420300c40c00c044040000e0302100d402c08054180440610304110184d804100140c41c403007000e00020a0a40d10b40103420000e081108040b90385001100040b1081c000ea603210149a0b407142580c0101c0318100403c58028160465101062074008120248110701482c40d041618000707034803120800c40c40c2009d0034015038590300c07800d5000041200440c6c0d0307002319020003500040e455504a95040854004d41d810414408aa03400e08990201c080366a030050f52060700c90100511b0403c00b031040300c00c1440817881c103e1a01344400c80e0001500e1000204188840b0b0040c0380c010720400d900c000e003100b07070340010400400038400c0350ba48942c0d9121640c0c030400040e00c0380c0203c0000c111094000d0049071501b802012984c4800c9180c00741200605603c0c803c00828050f00d900d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 244110998 1250 244109748 244109759
    0x2010207090c0c06050c0a0206090f030702130f02031030060506011103070308011d0402060a11070f0306060312030e0613110a030302011b030b150f0f04170d170c13 72
    0x10b170500c42c2c81542d1016858488880009203846000307031807040c803a044a0940b50200002200311410a43c054541002c085403c0030210020801e44c954020641c0c0301002340208c00700451422030880d00381c24126042c0c00541100407401d0a0140c902e02c030743c510400c10bc0e10005107190400c3e580942c0c14103041d036100c15008003150846d880100210000742e806801403180710440b0f590b541845c0c0c031800303c0409a02d40313580441c150b031042544107001d02030700b1400c0c00408202000a540078002c52556008516030302e01e000405010341c0c0c08122884c852114031140a54424031031580c0a0381605c008118a4460545a401900100100b0749211603060a5190f040d114000084025846980000b552603000001c2036081140403405000b05400c00c071203041690b0704d60b00450480c880c440401a9603448040181c441d500c2044550300480c60302280c0081c1d064440f041540e00080a00c082c0d03003046001180c1103030045248c501800c3c8050003100402c024004a6015154401d100e90481214544a6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 244112248 1250 244110998 244111001
    0x170708030c0f010606020a03080c032a040512061015090902030f040b06010e0603011e091406030d0306031a0414070311010207060503090601090b0a03080d0c0809030702010207090c0c06 81
    0x40c9030300e680341d2000b40001580002442181d005050740e10141441c981c45540081030204090305a011800c008408240c42075505018000122910b800c044200f440c4d2810400494006115540c0300e41102e071148a40001d003c9011032013070350000c155444c16410040d10780701b440b408074001402c008409001160a641340d02c01076005010060082032286018989081305401c006c007074904000c20300b02c100c0316545030300c4243c9040d118002080b001e104100b03000c0c90311000e4140c1c802038119043c605041d14410248094501075401a0252105d1048403041601542e68512004184800314150501490800c05503d034000748240c101401015846045a00c0c1080302d0b0401d80e8007440049100303c00b0340c0c04110100050086d410942c1c29880e1043e20710391a2181449140e110035181c1c8000c0e820b079519054024051640a104141c8420000c50303500c00401d602e680400101e1010408220707500800002c2d0740c61194140c1c01860701905000801024041c0c2e05180020300c41c01c80c644ca80001c565 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 244113498 1250 244112248 244112257
    0xc0d080f0307050306040b0609030c01050c011107060c1106040809060a090e090c0a0909021c020f090c0309060a14151c140c090403020a0809060f1c0c1817070803 71
    0xd43d64035a140c3c00d0410030032088600074600d0503c6114100081d451072385020440003c0c4140900b8019201e00091010b140036000c207001c060880c01000861400308003e961000400031116942d0754401c0841031501c680c1d404050b240507100000904c210340891400384000c041c20042ca02c1d201a501d0350f522241344003581d050b5400825500007006204050922031444001010507032414084c2e04a103401080c8400030910040380c254034060340c0d40c015503d5295651515100143c0010380928201e40c10910b90b82094500c20070340e010f030740c002c40d250703207510f001e030780750030240c140d002c5015032115103180d04e448107040307200c03a082501c00101207e0361400c094240c4045000b103900322081c03c0400c81e61400c049041c4c20843c0301d8488d080902c00031a50000303104540e154061100c40da02c0c00c0e090300040c2c40e4050f00388201c4d0b40c0100001c2101e80260120540d1009100782a41880040510070060300c8401000070038240700c0da0341940c01c00c260401d400d01021000c200e1010b441019032902d0074941540c4c003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 244114748 1250 244113498 244113511
    0x10305010b1e01050403060203100503060f01090606050304020120010e070b130b12060915040903030c0e0907050a0f110307050c1503090a030c1401051008010f0e0c0d080f03 76
    0x152021038a050b410044030b00d45a0040d200b41400c00c003180000041d01c180114003000e841c495010000070a604c1c00c0703d4144004d0b040040440f4000c2c50b061449800000b02401604e01040c02c001c0001061400b40c0c0c1541d0043d070b8161204540300664600f007120704a407801c00159603640341c1540020101c400d004d5034014054440c001c030743e54095410340b0400c40070154417031519807504018486801600c183c020f41c000f4011149404c880c0c42e41c001c8654180313403030100554880d1600750000f04140d00755000d000543c1c000d40361740485145010800c40b01031800c883c0703c00031440410604400600c42e01407450550f01d42e08090702c049603c0d40305540b43d9040160126070503440541d01500c1490b1440d880740000603600c11883c03652405044983d100e40100d0002130921a91984500c100126601070781d1a1841540007000344c7c1c41d01840e0a24680c07414401c0c44a194a482d410b098511024000c0c1030780c50001c0001070591407940c03024070a003051301410540e007180c0c007480000c503560ba0003c0118041c01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 244115998 1250 244114748 244114751
    0x3181c0b1005030c2b140d09090e06040b07020f011a09161b0201050c010c0f0e030a020a0e10080d0c02040c080103051902130c030e0105060907050715110301030501 72
    0x1811007603924070003401da040b880c42540158811906503441c800039103a41c50340310a82034640600100e05880c191040c80700148603180c0340000f4416102c0009886001e03903000d55454081a58a43e04c00003200c0c01c1030b080440c240c1021340001c0c00300e083c00440f10380142d5284100c03040420307182c000c20308480d404030042150520080c9280c10a203001c0e059130750800d40d200448a0300880700e80c030203401d00300e11412a00800246021000c107583c0a101640c5a08911000078050300c02c170b018000341111186826030001c5040b0208020007810009581110781740e0152a0440352401c0c04041b090a200040c280d41c80c03100110004142001c041c40f945428000c951501c00c80011a40304000540d084400da92042050000041011400014102000082e100e0040c038060b0690b0000c40d020140c0700441e00c145604180d011400726600da0320a000010f140c100801c01900c5040402c94500002e60320a000982e0501490011a0605a060303642c084400c000040041c0700481c0520756403c00d9006403800c0c0d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 244117248 1250 244115998 244116001
    0x203090d03050316052a0307060606051207110a020909030d02040e01030506090111040501120b0406080a060b1c12020a0210080a0515220e0a0b090714010203181c0b 72
    0x142c141304010309001d14113007002d03400c12201d008125099159229035000520158a000c0c2206105000b100c40302c54000d601800003684505015140354000700078940043c00b15800161b00c03a00c00d03d450700e0b040010038041c0c041d840c02d035020400300b254040c15070107a5001c2008010442d50f96840103100403d004c0500304403e40c510304160b4100342000344541803c0c4d04040100080d105d02c4401c0f83c05807102400d0140c80c024000c3c01c44802003103400724154001d0700c1d014000c03a01800019018800030321808080c05010070383c400740170f80c50307468a010381c0c042c488005c800380020300c000300c80e54100200c52048402d400e00680020b40184810300f01000440c0c0d4800510812300074501605600c07014881c04008030310035880102c0c00301d4291141900d90b0404568103074190740015001108901c46040c110344a41c0c40d01e007014101c00806030b800e904603115070200001caa0340c100504080c4410140c001c0d40c1004901015294020820540c1681c00840000d075100c1e1010b043c002d082e400c60040d050000903 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 244118498 1250 244117248 244117261
    0x306091803021b03060a09240509011d06071412040b06090f04020f010807030e0601080714011b0209060607020301020304150b0a050604090905030c031809060405010b0909070203090d030503 83
    0xa060394043e252460119900b200352003500c00051a6030054503d020010f10102c2c00d0408500118201c00d480c0c000d0700d000c0e800c1940c5440140c200b1030042c0303020002005403500c0c144040b03520901c4000307450120f07080600040d01150150001034601c5003009085031618a455076181c2c400b0350100c40480d28081188180036140c14a8100b96901140085a210f132500309600081d40f61040800b5003410040c10200144100e8465004080484071010488480d941c445210399103611050007000309a03083c0e40c2814a0941c071400e200f610145001c500c9440c880c10603000e010305004000c20507a0054010080b102c01610248000d40c8554041c01200e9001c4141e020b4000661300c5083e03805210b90081d4205200b16a295001c4808442c0d805c440040c25000e545481c034194020444035024074080814410003810b1410700344261210100c41141c09991010104012a13100b0b02410521220610902040341880744105800c4101d0b40105c07410702c842040003c050305501601100000e20200a2061 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 244119748 1250 244118498 244118503
    0xe190803070212160510060803030a0c1229090103080d090f02060f130504020a120e070e0c030a060603141f0801051009051b0304150b09070503090f0c03030f0a030609180302 76
    0x180c05107903078001d2081d5072230000c0c0c1e56501e002c09030402010945c1c1e100b94051030f901409045030b82a44019003072180413612204c0010340d5129070010290803076a0301d031600062428540160580c1c4c1e11416040c107003000340f103140c8000c00456070101c1d0039140a4034914090381d200e81c0031300100c204ca80260742e62034110303103020007148410743e10444c0124014490548a245c200b24402c0005030040000070f030b040c41003030710705151400a07440740700c9030311020b002c2c090030302a0403000394030031a1408014443c546c1d0790700007102101e24981d581c1c406422824003241d40041181608004100c1d440c562005c0306440c0c07500d03d400c68506840720120041300941c100038900c0b441c0103d81c0c1c8565142400d07200b1030340d002800249440002d0000300340d01c915014480c1a054075038800901080058182441c40c900103901400e00d52098a0468180c8560054600c05010001e206080e001c005030242d0700301080c015241213550480040d200c241501c604020940c039200740308401280140c0c1899102c404803505010b0b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 244120998 1250 244119748 244119763
    0x1209030f0111031b0403020409080307080c0301060c240f05090f010605060403060e030408030406020105250e010302030a020c01020c010204030b0106082e1203090503010e1908030702121605 83
    0x9039980d042c490b03021109128002030329407100440b01c14036400ea880419040031031141d504000d40c824a480b400106102e0140302542c4a000d250b01c62200585030380950b003500e400240b26100004515100d0344001900c25640707861055140c2d0702700310481c1031030040101907400151000107203d50340d00820603011020000217101030020f100030031034241000d0105860f481207000241c03503030352940b030203410070b80040040703030001c02c0402c042d00d80303c944810000780608020349a0420304081510710320001401c4107542400c01031a0303140ea14680b0b01c58001500650001082d20b806141d0074030003401c03081c0c4280010501d4040c080001650b6505514012202545c1a080f000801243c0d80c2000b6240c0751400228100050704240403001c00b4203007003025a418500c4d0055100c2711040c42d103820805400036500e2058440460090003543c21400000e40e581c4551581e440100c103070070000d00080f0b4826401540c01c1a0301d88180c2c0d001c1100d545036047d440e884106403644020002144105225050001d01c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 244122248 1250 244120998 244121023
    0xf06010e060403080d0e0f07030303090c0e22030216120507060516030c0c03020406120506061203090f190303121a0a15030b09150108090307210e03120903 68
    0x2141443d0442e00c8500a600800707140185955403000300021181341003041403490b40b0a401111400c5449103070050142c034800c00300720748020100030302003042e11002504a00c5402060030000f070031514441410211030203880c0903029800780401200e2014034a00494000e86802d5103549511403692402e113140c944035504c410200801404612007407032107852040d042e290546804240500c0360300341041c602c1c4c2c9640c4020b40c854900080016504042c1c0000c41c1018086c1082d00c00a50348c00041c01242c912824803002e0783d400070415081c603440c100c4e01039910760401501d490b10002d41048410000c0c0312940080d004204005500d4000510380c0c06117002c1941c0d8040850980360100380170401d500742a004c0d1075034241e440c1000c002018801e60107076680a400074000c4045003000c0041141e8000094001c0d80000c5c01140010321344a000000c46041c203901502a240407440100140100d03100c80d4089000c12241c9400c14015543c100b01c207000d68110440030701d035950a620300705880d140d28001d00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 244123498 1250 244122248 244122259
    0xc0813032127030f0c0801020a11010f06030c050607060e0a030c021002070501140714010903050901020f0106050d0f03110a080909070219120c0503040f06090e090a11060c01050f06010e 81
    0x340418000c4100222507000c007a4020313907201450f2182ca5901c090308500c800d51710200f101c0018641c401040d0703e844480c00d00822004004440220a80c0e81ca4003000c2c0074040c0f446020806800c15030300400e440d9005c0c400004021016044c0e890401843e420b00f680003400505120044d031810034120b00c140c040c540000d080d614070302030000c0c02c6008508000b00710440041844024000c0302190b41c0101500c400c0200520801e501e0701070590f03001220203a00501c101c096060703502205100b15015036000800c250507141081e0380d003100c83c03000710300124200042000b46880e55181000840c2d003261103001001e0b11030806209004a03036400511000865106030344003d404000c2000c1102d80b0b039000596502c0e080c88030702041c1d0740c503259804010420300c800100045e0705030041c444202a15a5076441c03192280d40d0b801040b400dc201a9900c021039000203202d08002114040b01006a000c00782005040080c410711031400c4940403220948400c2d4100d08001581d0391007020700b1034a2804481 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 244124748 1250 244123498 244123547
    0x50709051012020f010302160c08010f18021519080405011104061d0307051002070e01050619050c01110d0203041110020304140a03020603041505010906060c08130321 73
    0x2901c0c114000c002c07001a01444900c0001070050744250121003003000da0101e0aa981f540510306072a000005100d20f509651804210385104280303400b480e01c0d0030081002c1d800d416040c61702005100c0c2a801105005500d0070800240340214600c070040d05d900300d80e01d64107854682400c0160a40b0241010345e9104082041709002c680e805c0b00b00384815046103140403100f03080c0400843e01c0d040981d00242d5001e442e2214052445600044a0041c1e60588170840c2050360b869080c00201e02460004040d0112411440b1204034400c00c045e00081c04214000300701080041030466456100d150301d20103e9400001f040180075001104c0e013070300d003020380d1100154284608025220b0045005140c2e0030640140c60740c68941c0c55103454006036400429031039490619141c4042034660060040607076500300000054171221a03c2030340100c500d5070b00c510540404a56801205600080003040403c004200c040041015100501d122505c103003d0100300e0000101b002d800c0041d4110f00c00c41d200103054 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 244125998 1250 244124748 244124759
    0x305010c080a0e030f160606030b181501030b010302060c010618090b090d0909090f0209160929030c071b1e05030d0507141914151501021203040507090510 68
    0x4040302c0309058940c4106c85e15014901d0104090540c50340060000c01085084c4221600c0507031031203254184d501f0459100300b029410440d0252801d01c809001800309500420250500d4002072900e4038800c00000740f40350311034201c0d5034004000c6282d04d0030740350703200581010810103160168006040c10f00901003000ca01038001c005000d00d00a900d400d40e01c5291b4a002c0110140c0c141246640c01800e0a406180c0390324000e01c200d82d008200c1c00011442180011000340c1d040080030441c0071880f05008141c15900b40005550002c0d0460030010020171608001c542403038102000c0520010300d0800740c40c9003200e41b81e980c44821181031100d683c01c1100304a00d580000d8410340100b150301709240c691000d410030042012030500604858080e08004c603034141d40b07011030080840d10401c400345542c485441000c0d591204142505007000303004000c01c0c101c0e2981c08032501c1c5040144122410b0004011545806400684048403079a00c0140140910300c0cac02d0040740d0b4801c86800010320013910f8070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 244127248 1250 244125998 244126027
    0xa05060f0103020a050c01060e06090106090e040f1e030206040302070906050112091a090601090c050316082d0118021204060209040908070b040b06060c1b03070305010c080a0e03 78
    0x280d161506140e400a0105070040c068020b50b091014010001c1120568032004101c00d40c1d000c40321144104201000440c100380252015020350300c049941040300d1740c035640d03004241650342400342c650701e081c045046070800d00406402502c0388207a018003640d0803d450080d2400d0340b00c1c1c000d01d00305802e242051015980c010760002d01c2440314000400c4150690030f040404068010465001d81c20b6581000504040060110304070317803c1c41810804000c05000465690000b42c3da21802ca02a80401702241e07031050002c580c12507000131611400e0301d40ca01c1920703285000e041d0b1280c2445815030042200c10f407002000740b4a100d08132402d620b803403417003004800d804c41c1c0104002c0007294013180380c040e20744456120024040d881070105594590504040c1a1014101e4003141c04000540c00a1458201941603680b4556000e00412109103c00224280c646001c1c0c200f64162044400000c041102402108412111500c88800f107041c00405602910003110102c200b0781e1042005a850b17101030b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 244128498 1250 244127248 244127269
    0x12020a0f15030f1d0d080903070803010b03060a1e0303080f090a080a020f070308030402030c0117010501031a06070308040b0705070503030601320a120b130b03190b06090a0506 77
    0x949000a560301c00781800800801070390520382455649204c1840346001c0c000317440402100151203103200c130350302d060380e69640e4428003000514000c0c0a0004115165040b80a103403c000001c2030304541c07079150100c4120100c01d003010040e40c00c5400b0800c1060540180e0550303040f109a100b06091490088101a070341c200303402e0010302e044000034641c0c003001d00c28003503030010ba082c401c140c403903580d901d081c981001e40050310243d00c2030142d210b0340203040d8007503140031040d9001510710230704c147c0ca4a0015402071044035980100d1000d194a600c1103a0780b0342000b40352151007038035001c0700c60070141003042684500514040512000700304100201700000b0650b58821024a0444410070040f00c1f110040c0d026005c40030440441c00302441040052000604090b6040e40d49045210005c40d09a1081d1903040c0e40c5103404c219120303580c405000080e041400c085a001c0d040701d613a4000d8080302c0d0790062300d030101541c0d00741d011000c0c042c01303180c03141f0f4990300107ea9407400d1006040280000c0c0301c1014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 244129748 1250 244128498 244128539
    0x1305180a050a030e19091d030702010c0b0c0702040912090501020f030d090f0516081002091f05090901090e010c0e010e010e011806080103050c10020a03052212020a0f 73
    0x4180324841c9103991045d251a0b213441100c49040303102c984d500c4080c0c4c0903040751a80b500704075540f400240c0310380381c00109961030190142c0d00c00b400c00e02c29880f6080da188020744000090b03401005840c1c090384450003100c00061180940410500001d1340050060003560403141c11504000700d4040c84000010607909807030101c400018405140b86400b00c2c642c0080c0c14010007600400903503c0f0b4405200340b84404450044040e1502e000d1160903041c228441c040312268080303111041540d484c5040c00d00c40c05007100c0f03400e0851a01400800041c00003500340c2c00042c40d1900c940038502503000c00c0c0103140861150f800c1c00c49003409000d0010b8506404861401e041060340001c0306c00c0380e0302c181006001d00ca04071088104440e200c900040101809000036180343c4110801003006003000010b02050131502e902401c1c01c607400e558116403603404074112030101c248448541001080c01180c04004010010341000d00c0c000302c3c810310114003407030361014541c10041d0004200445500f41984d50081 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 244130998 1250 244129748 244129757
    0x60605031b09040507120b0613060e0f041119080408090d15060801270506011a040b030f0402190302130213031a07090b09010c02010c020d021305180a050a03 69
    0x710300d9020358509004000003994014104130034071200e00d40154030070f55507a140f92030a10201304c0040500a540c0700d0004113403405231411034100816403080c1c1c00c064049800030403070f4400300c1c058800102500d5880603040e51007200060120740d03080310b40881855081c120304129a40d844e1030346910445000d0001802c3c010055841480104028201032458111011a042200c19102c8000c030b4028040110210001464000f0590351030305905c44c8070482d9507100008010980c2050301054245400050003041c03000d0501010444142c4003020310710840010300360b03820341d261500400ca0030008405000b04803906c01c000600150712401d49658119080398000350340c50400b2000c418111506a20107807102c400c2c00da02c03440c80c080e02201640500c1490f0340f407000340340d201d42c00601c480c031620080c80d01050907245202c1c01940160b06402000e030005000e00c07441000c6402085160003c881101e603140e96440400011101c1207083d040b42852a4000340028021560b0b002c1d42c40020741406002d11 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 244132248 1250 244130998 244131031
    0x15020a050c040b130e0106080c090412030902030a080720192106020c060114060c0a0308070c061a030d0203070c0b030405010b0a03030302031504091104240b180406060503 75
    0xa413602c07a44503021006090007000540640c00c40d4900a007624010150980a000c0c41100c041c90100716082c0034130b41002000f83e00000c00801540100384107002240c06002e05540880410b040c03102810740d65014141c100311902c00140c8100e103080c5014a414031403400b0001c5881741900c2c102d03050b010380e002c10034040c05481c0052105400e6001c0340d00010103141c0000340c0b001d09444e0100300c9a0480c0d24090290046180200402600380100c0c0184601c0c1d070300652403030010910a040580e000b00a0b400c00542090131510b90300d0a0700c9811207040271071441241d00f84c1c6a410300700001540c03008544003541c140070341c1c2d45d10101070b03608500c40c640803010003201240600c80d00303501001d01c03144000c050b5201c890350f9141c0600a90801c8038003400a500404950340103041034041c0d42e088a88c0308080b41000c040703010803c002011300540c244022000d0a00301c1c2e954100c0241e0110152294032243ea840f540d03a0540b80d0111146808003901072810014200802034000c0287c940060310500c56031810b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 244133498 1250 244132248 244132271
    0x70e030c060d0b041109060712180608040b070206010b160c0b0a18090b060304030c060902120304080f01020f0f1806030a0b0907030515010e04110703080115020a050c04 74
    0x90000040d003896004000052007050854607510040b43c0000554051240c0008040200743c2ca0040c1590140c00001c01c000000003d81f10b064001b004540d00d05060100320506200c00c00040295000400400c404509120500c210388101990144c5d00344020b00783e0358140003060041c1d010f04d100d4180301c01840c18025081201c0f41d5a020080c0c100d02c40d2194546503040c40c0101803c1c01940103c605043c0088082900f003250b008003441b0b00e0000c0c10f043d02d0758803a80c0d02150b28206080d004d0341c406584030f00d070364010780d1000102110710380c0c9000290788079818901d00a007003481c40c01c02c5405603071040010303041010318401034422410502036115100c003103102c030180030018807404141d031025001040011400d1030740d102c0300e00c2c15010b4800034038560b10400b060382154810317a01d04d005a41040001d41103984a10301900d440030303001d0030100b117011885412440303507000310004401044003c4010b0290085041d560030b2010320034401404141c000b92240d1380c680a0000700c281c0501d0b05c89040904 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 244134748 1250 244133498 244133503
    0x90507110c0a06110f060406050f090c0a06050d150b0408100501051809120c031317060c0c0a060e0d02010b18010e4c03030509190e0405160e0708070e03 67
    0x35517441c0401a80d00e43e00e844e01e04940104030458903070072a055030101058034080000340c0540c16081c0a052030381c020742400000e640e560410924000010740b5407020345103404008801c0b000a211803068151140c2c1014162810000000e000741c204030b20340801000240d40d4820340039061170000358102c4050311000000707420320317a07000c40c0c020744401c0014140700d40d510b0000084c040c0910803983c103140d842d2652002c00c0304001c103003d40c0c51646d03c5840401c50000030300d402040710040364011610740d562035035a101c083d102140c040468a40051178490b1009d03030280104d41c46440121380a00303a00240f044180300c07822042c000d0854102114001425070800805a424401000144450006c0c40c00710035050000008010a403034010000001200003e99003c200540f64961119804c0940020070b1047d4500184c82e50309500c01d042000080300340c21000e110f400303540190003920b1091400b180341807108000c1e600c00c0800070035920420191f03a80c04000030340c0103661450304e0b0700301500c201d00091 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 244135998 1250 244134748 244134763
    0x2030c0603010311131a041a1201050a0b0d020d03030b180c090316050a050409060221100b040e040f0201021c090e09070b0a0c150204090507110c0a0611 67
    0x50304804004008014007180c00e0321210342072012104440158000454031080c0c80070005e0610900e0765810b012000341c0383c550000224054846244408400241d002170141030300070300c000446940d2102032001d52411401805205a01070340c0b41544200594082a5442d02004d0b0180c1010780e610180c44107551000d40d203507038005072002c40c10710034140101c0d68000e130f03402038050500c20320486003000c0c4140905c418000c1243c0c0c00408001c2c1c11450841808050031f510402280c4040c0d081108180e208450b5015101008401c1c2d403411562a100f0000440840e86406c0359038101000e020030418000d850415591081e4854188110300c2060b02c01030b890407560035005512030040e519841c0e2282e5005850000703c520b840040195911424207080e00c554060140c6074606130101b056441d01401041c0f60741049109122040350000044400d2080ba04550006c15080380c40703d041c00200d9070700580c0c1142407180c04000d015040c00d0080019200c00e46442000c1c10300440c2007016486600601001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 244137248 1250 244135998 244136023
    0x9130209090705040603051005100f030e06090102191b02040b04140a0507030609051519090c0c060501050303210a02040b030901090201170f0126030c010903020c0d08070f0203 77
    0x10079060a0401010b405074026001d040002498a00040d01341e4004911180c102c03500640340d03861104d00c02504480308168140b000c42410340b6900110414a001c00002e4418441013000503110401600c0d4100c2509280b421b01003000489402000301040110341040e520754100d80004000e019000418064400304482103000310031441008100071702604114407544160b50708000c0345403142c800e9000c4400c20b4804600c4804005116a48c608242241c0c038000d04d0454030703410b5400c1e5128021010344110391200c000041100c880002048124003515001d000e040307014604040b1060884c1400822448640ca4003907040004200c851035203038129800f8000e01c14000b5582e14000a195002c0e1000000490000d0f644215088081c000d07000d001e03000380a4038080b100c040e441c204c030407a4024003c02400c12401c0481d1000d402c00c0e2010401498188031600000c6920f0304a030802070706001402d280d041c0900c42210042000450031001c64508036448004050000c403e4004a4a0410061200b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 244138498 1250 244137248 244137259
    0x105190308070b04021c0c1e0e010b04030203070609050603160516080c0d0320030403090e01090e0d080106170a090b010305151f05041a0301061806090209030309130209 74
    0xb41c9090205601285100342e0090703405110007041c4500d842e10401c2078a41c003510441c0c412809022010580540c440c0d00c10304201c520a40f541c596411003884042a4030103804500000340410440c14140146070040509040c960150f0b89002d01003000d42c40010010162854500b02d48000940214265000f0321103e83c1904108059071400d0100d07940580d00c40e0915104004074481e01620038090148100180010307600010b2030b01382c107001c0ca81c0025008900380010030300049000c4e80314165490003850004008508980360055071420496000c181004100c2c408005000c0c413a0084822070414503007038600d004640d2501200e800400b1030700070040c00440305800000074000002440070014a060201081c544c03a103010601038005580316416000030070000c10000e40c6801c4d030101a00499000090745038105220000e42125130135040440d00d0701048040007240d100b01d214082c0a007401d100c0031031401c1c0c0c01e980060382c1c2e4015088280e20901401c01d0704040d00030f1640548002801c003801 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 244139748 1250 244138498 244138507
    0xb0105120412110d0306061e0504030b182d0703210201020d0c0e0a060906090e0601020f06070503070e06090d23010f0501030303230106030b0612010f06081803030105190308 76
    0x4020003a01042c80f609000030140d865405030b00c440c454401c230f010b000a48030b8601c1c1c145556a4240b0401c0b0081c80d44400c01051410740c030f00b18009010700010114001340113040a84041440d52100b020750000344095800b0184c144000b40983c110110b401d00c101d0b14400d41c1c031498801c12806403107103000740d9004a0170100c5003140c442c0c100c0040b003c0c15201315000c0e119a0344401048520b580c00d80701c1c240004407440f00400c0103002143d012604140f046c81910841e05400380124a000410b9a501001038030000c10013240c181c1c444d100c141004402c489140c80c0160800019840f030680340d001400c034241c00c00612460b030345501c151441c818529802401504040d074000b10052400748001d0f00404e081c11aa0048200a69400303910501c072600822010b90801d00f00314000d1001d54442c03500700703500f048076182501d90310381981e00801402c0d11440c000c6042800c01400c03003030302030324a400c0c02c2031003200000189408010b99040d100b0a581a02c41c400ca19041410032510b181d0028060040005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 244140998 1250 244139748 244139773
    0xf061d010501110d12180b04110a051c23060a02030118020a050d3315050f041203020703060e0610050123090a030501060b0c010b010512041211 63
    0x210494101c0d6026242c0050300c1540c104240d449400382e11107100094034404456110070659440501007692503820420360b1405a95800c0c490324055500b80c3d450b02c14a450f040d41454000003040103090203507901c0c200380740d140d09459100300c060800108501d560207901c01c80161b900d811383d18500180c0089400504040c1410b5000350301c2802131040468050004061062040c002c4075001412503484918040e40c28501200501c205d044150b181c040c41180c0001070b000c0c031440010b8011070818601221460700090030800c41c0c944c0c18070f80520209010400d281e001e02d02c1502e04690003c528440144094030f4200e040510036000104081e01e442d14030402110b002074102e201e00f2003140301074107040d12000195007094101482d00f1541c07254900c6881c3e043c0556001d800c484102030305000320180c883d5501e03400d4079520741120103074540100700210302200900802c45180f03403c1c00d080307151410028001200150040000d030040340740320400c0714071034071545408105004032000e858100070841c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 244142248 1250 244140998 244141049
    0xd110a140a0c0b0d15030c360b01080604090201081603020d0911030c0d0503030c09030a060c030e070e061c02061b072c0f04030903120305060127090f06 67
    0xc44d110301540c60a1459038441036900c405200b601c0e00f0032090440285012040300da4071003201901030b08010001c84055005004501041c8500300c007502c041307514107108000410b42e041c02444548500c1c03e21071a040541d0b0440c0c803803030300601c1c1d10451231201e004189e001c1e0040c0c0302d038200a000052074000b120781804000d441f0158800c3e012016501d43c0c44111080112a4071090400b609070380040020035514084c6200810304541d0240a13240c6501564661104441094031101c000c65110001741c140d50005100c884040c0000400c0394002e818060081814030104060200c00003141d40031100555542000b9911440220180140c6500882d21a103031101c0c00351049440300f4002301c05145140300c1c3c01e11090303810210000c24142603510001c4507030f2400400340c81034051048900b00131000c20702c0a004010429075903100410b01d0309100b0001080c4602d0410a0300c0c0503603c0b0120320f034882c07840d14a038808803070314550040781c004520070380780c0c6c020032031507001c444003400d0039030400010010b4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 244143498 1250 244142248 244142257
    0x1120809060c1209040506092806080304080114090f100209040b1e0f0f0d060506150304050115050a080c040b060904060923040c062312090d110a140a0c0b 68
    0x640f01403106d41c540f2024440310810030b540e2a215102203628000e41410707818003440002011107000b05900369640c0c8180c4c250b50194000710b41c00d94441c0c031541c003c50b800b144c2c055001341d8103034010600d01c03070b090000d143c40e1100904003041040c0c00003180c09a50743d0303a8105442990f0001d00d500c8100620500c85002001440b000c1c1c0e0240f03000d07046c62400e501d8004030100c01120080c180188024140da110801030100030402a4820803004048407111800c101961145105200016240c8020080c00381071800c9070380014418941e06c0c509000c401b101049580c4d00da042501c0118801c1d8988002510f01d006524040350000c0c940100040c0791500c41c0c0000900c4a80d480d251404800b4007140b80400690440c1d025184402c00c180c100181e5108403401d003003000110140f14a60820078898000550000c1c101000884525081c421124010300c1014250503032070600e00554401c43c0d0445454564000003e001444a6190400c60590034803075002103a03406500703419903945804618950350070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 244144748 1250 244143498 244143517
    0x804110907020a03090510090b090a0b0f040906050f010504090e0703061b0e0a120206030406180c1508040506060d020a03020307270c020307110f03010c0f120501120809060c12 77
    0x40c00207031509100c0d07031f007660410703060b130710031055600304150006a0340c000320085400440312500020204003000290051a0f1828190750b9682c0c5042040c0f015500190026841502100c1024000e6a04581101c084074495507011034040d6100035594203000d4145e1014081604001d8582101000c4004c0f03041c86119540300c94108448600071300031041081e0080404002001651602504d031420107980e1040c440c01d0701140d500c01541e01071070a07003051a0122640c0040401c03c0c020700c0854018003218280909c1c000c00c540c81d10361149036451001408003409021000c41d2038003552210303c040f002840e006000c8a1549582d0407642640078800c200010403804140c403111440941c078080e134540d00e0001d500039410078856132070f40c40d9100c00c0000b5107907204c003a12405070300e1034400780030f100328080c101e480e0440743e40e2030910080c06003002a501d1450107441c0ac0018880c98243d100c2201d54035070892800c0b5281c0c010540441c038188071391080c1c2041c6201e01a910750919110340010030b42c021 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 244145998 1250 244144748 244144757
    0xe090a09121809020414010c1b0b04030b0a020304032a0221120403081905192f060f0c040803030c03040c0605190e031f0209100804050d0804110907020a03 68
    0x10f50b42e84800089000314000c1c0009090f203d01c0c1014550b100d4108806981d0040c030700d215104c0c0b1042054004003000d60300c640710514012904100303019a03000007540c4240d24200c04d40c5107280540e00200861041d4024805502d214401307403683c1140c200c00b41c480c01707038040c007842d21075030260480055a071410364814845106081c00d00440c07400401c255030807245d00c40002030415420141e100307050b0481c41007100402c07006101e88072840b0303580c0013151000d002075126407a40805520300c2c4146c0900614122010000508945403100c00001d83d142d03108091319001c0c0c0d095150002d02c90310742d114a82c0117040d688004400d0040600590005500441c03107480010b282c256201425142c82c0228159400211a5152120000360145e400d2039101d4000806039040c81022196190303403000010b200c50b0300d055002c1030642030741c03d1540607183c4914107070800d10303081d150030b5880941c1c40c0e106044040400041c1d0001c1020410156101c0c0c418003030041c0380c402c0618081100a5032441500e40640014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 244147248 1250 244145998 244146047
    0x603060c1c02030c270102071e090e0f06071d0d080a030b0a050301020d0b040e010b150a030b0a030f0201021c0206161206030605041b060e090a0912 65
    0x81821000311071031000c185041180081412481c40300035003009151045501c3d0401c500b11000c2d01c007103c1d101542c420980000c1c14100c15000091600c11980c000120542c10860030304050f14081000d0800c41c1c64204001c00c8038074603c00d201c0e085c4596040c00055910441060100c05500000740c01e81010440c041c2c0f9000b01c0f0803000b00071056403100c40c090000c580402510741503501c00c0d04204460386002d86050f403200e5884001c242280d004943c0010740c84d17070b1808082164900f5001d15034407a04204028886001c0080000f4002540848261041c0c800003401e642404e0080d044802c04290040050303814035541d0414000c0b20f589100101c4c0140501010030b08054400050b101461001d41d000b00800d6895690780c4850f0034030381c041403060118095907014801d41c0360103040301951084101007198141440e00c0109950141c4004202c440b04140901600c1d134400e507164008034045450070015282d0008e13a900803e090003000e00440c3c0d0400c4009117040c0c100d20312244c0008081e2130349101 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 244148498 1250 244147248 244147261
    0xd051902191b050a0b180304030809041509021204120c03020601060f02010204080328021506040b0a080312060f01110a12020f0f070306050c040e06240a020303060306 73
    0x101c0c400d4240824181458600d0001d0310751082400c0d100a0344a90418416107016840d194505244071001701c5170b8496042c10001c58444958118040e414503200450a1600f1a03a48020a016029615015603501c0c20066103440465100c1c0e001000c0c000340855460303043d2030403000001c604031001c1c1c0d1008003101d4250200d62049840044054056005c0c0c03060364240702044500007071110708801199000c0c0070100f5580d42c284001c1400d039461000059400350314440c0a80382c0040c0c80401010354101d107034026809195910029400202181c000501916820010700404c5854002000078030000c40c06001c1000310384c020b54090003040b2042c003100700e10f08004503264201a420a001c2e60801e0440200003002940e01100c0380040340191010074642494046c6016010810588a64808070082044c03114a00c01c050b000141c0e0134040745020305003080c1c0340c04410041e082c0d50248008898020341d46e040310a11950922011800350f98545034118029502d80054079113a102e8091000460b90 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 244149748 1250 244148498 244148501
    0x20a0b030c0d05040503091c110102010603030219031206030501050a0f0203070504031b03120906080a060e010312141b070510020a08030907030f0f0b0708280b060d0519 74
    0x11446044508500c1c000c0b40000c000007601010740112101d10050002d808150b942040c0365100c64141c8813414080f400c1405d005074a100360180c2e290540e490703c1c0d41400480e5000c143c900807038400d01c1e0b030030350044d816240850b01030700c410340d0300c1126070314204000c02001419044207001d05070150381440301ca03c0300500502284007d5400b50007280003040100700041c0a60b1880f07901030a03c0008050855032a1120310b0b102c0c51003108c800010fa010796040c00700f65001941c107a080074501c14100306550502c0e4134408192418003014001007080341e0400c81a42c4034809101c40407114410664550110350300004040a40c0d111913055402018400b02d40c82c280321005034040d000344d07801881903502e55114440c1c10b91002d42403102e140111a4044003042c01c1681200d1140d00c2804030a0401c8a641010710000c48003401000c02c01c01a40c1c1403000b5255444501c00c002404501c1c2c000c0583c0082080360300422101c8a8150480e50114002c03c0c980203a81c08544682044004241140c11071040380c1c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 244150998 1250 244149748 244149751
    0x8010203281103070c0221010b09151e030f1b04361415060a0e04050a0303050c0d0908090a0503071a07020f031506100203130b09041805010207020a0b03 67
    0x58a000d410f00024400b14890441076480310b0016003d5103d801e00b4118100400203c52141142c5a440d074005840a080251805602016075080300c0c502c5c0d4031040015964022007090b01c1c00e42c0304550000c00307103a03906011510b40300d6000811039216010880208070f54042c0411018032991402c01c0c1503d010194261146e240014005081e0450140c1d45105140d6080540150b4600103442004d0000d80420400380455800c459143c5002c3c4c07170070b041002148074454104ccd9058807203031710502c0005000007540c540f81541c541008905c6995804151800d40280c145c1b1440080c104240c85041c800000010000c1500c00d80b416407005443d1700515036501050b120b4136801c4d41f40c0d02490800510003802800d052803005040e03420310b42c1113900080c42c00030348002541c0303040404030901550385070510b8112101040c5001440c100b100029960040064510034012001000038405a00343e0b00c5501c40d00d48160403a07021041c5070000e0400c0350003500700003c202c0c040c40080f0300c0403500280c0d1401340c3c0d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 244152248 1250 244150998 244151021
    0xf01050a09050d03031b02060a050c040506070f1e0f06060902090303032a030403030509013606150303020601060206010506250542040c06180801020328 67
    0x142125403509080c0218a00c4803c1c09030101540c41c901b01080720814440c541c00f4494690050610b82003031403c040484801074025191200104000c2110762030341d5040e1401039400000319018100242004c0d10003112629401d041d10b03291170400c90800428107a5041c81d075015010411000b900c0e400004102e100d0529283e50541c8103000084d420783d8807440c2c12104001178109100301141140510106404c25101140030907101c1e02000001e0009104002000c08480703000030700d18031061801e20036100054000300d4030342100302042050004942105030005081e01070803200c0c60366401d000b52541c0c007c1c001d0310018020000000b805142160076038034502980c000d000c0d8a60b08240a090100c080b48034200ca0b2400343d40c051030000200e522108480f824405801e049150b07603c0c000c203184850180c0c0b000c404d202076a0522011424103041003041e1041e9040c8124520f0001c9582900c00b00c65502080b0340c0d41c0008100401c4052000340343c1f07000d00524011801203061007100074180e45403101c89 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 244153498 1250 244152248 244152257
    0x201060311100206040b04050f01061211030105070905060c0703020607060212180309041a150901030b0409080304020415090203091006171b0402070804120b13050d030c0e04020d05060f01050a 84
    0x3150108641b40103c0e50018070505c103d46003520024545401d6488503031001c21150031407904101848280704007150580011030003040246811038000d40003100d140a046e002d24000f26040340641e104110440217507400400b050303210445460036801075031005911690050001c2c02082c0541c0e8212500c13040804980060350518501341c1c20300005100e828602a9400fa82540c868940d071100701085200341040030110341e807200100d0006d01640d95808245005514203903810740410300f154192500319034100d4020030003220786402c0c1445000d0f0394100310101c40c400000e00114440006141b041c154851030103100055840540c0745032400c1500110000b42c0064078040940d030044110880303d0a8010001414a40340e074491780900d4015070012100900c0c0700d18003800b440303d00449a603018481440c4000c051009554a030307180c8040c0c900d604141030b00c403640d50001500415a04080c400081c03c1152140b4898803003030090142900c0c441d014030301d040709240041d4800d00884000c84615104d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 244154748 1250 244153498 244153501
    0x3030801031101090915060801060e0303030a110702180f010e0c0307030c03060b0403080d0501050a051509010306120605060f040b010f080408090303030c0c060606070f0b190204060201060311100206 87
    0x580269080a030402c450401c41c000c80c001c1003204242c441d41d14900110f10f101c840890030100c000e080004180c00610920040480e6409550760000841c0c1e406614144085100c05101622100c9401964002980080d501c002001c140100300ca8451007034014800040c56640daa80d40c0300d403030130b81c2a07528240c4050b003000000e4045000303801144031040281f60009419540702c00051a40d04160402c8420032000681c8c80340d0b42015000b0103001d000101c0307004005614100c00520030012520540d0700d0f9035000710f41088560f0080d44181e0042c51000d0f0402640d074018980390b002441d08407403982c8110501c0e005444182402c1c403c038540c010044c0c6070100361001c03881042c4c0b25042c0080003161000c0741002054002c0d10284041c1d0300070b143c202445512041080c0500e0700f00840201641d000d100c080c085030000c200740000302000207030041800182a02c4000c0b44100140510b41c90040b21800050000707201c079415401501101d003d401c8480c01c825400d030411851404c6070078110010f902100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 244155998 1250 244154748 244154753
    0x140702060313020405090a020307090b0a030f03030b04090309050301050a0908090f040e01020a02030a140306010207030b070c0f050d03060632070516150507031e090e0a150506040303080103 83
    0x50055030001c10090880002c0400307680010f0030703504105d0300620300e50044600c240450500300b0202c4054802c262080c45a800c03a030b004600f1004140c4009000110180c0700141854020752041801d0072010b4402d001e81406414041c108502c1403041a00a40c40d01d00040c51020203481903150650340180d2207440c0509610802440b0783c2d03000311082d8080e41c0d401121103100c20901c01010001015000f40d525412013420241c208003056124200c0f8000820400c1200c1c1e9001c50040f007541e078014032074081c513180c030202280c02d040c50b0f400042000d4081101e1400780000021031003484c0c01540d80900056031174440840e2240510741d4180009803520710012100304d01c000b1894940c441005c2007900740b614540b43c1c60b2a00c42014291000410002c0c020700030103440d120300d51400416400c1080c5000c0351558001e1071070311412810030002000350f11940d51036104088481c02071110001c400f225007014203820000b04140d030031708880700250075070014003820720506490071641c05481e9412268a141c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 244157248 1250 244155998 244156009
    0x2120d0f03020c01060807030b0a060803030103050a02060a030b180405010501050a060c060e03131205060c0a0e0d1104090309140d080d020d0f050f06040c050c120f040906061e140702 80
    0xb04400360f855501d601780402c901504001c3c01001314020402c0c038a0341e04120061030b048400d1a003164115400800c014004a0070016501340502c0d415078849640d4500420120006c04410300380b00d0384906d41c0803042c41d0050017101442d0155010310000c214607603a80301000340203d5584202c40104582c40e9a103004540264800e04401002100740d82c541284c030800d140125049030491454207202c000300505014080040316440070304800b20620b072000300300028103800c00e0103c5c42403150b101c81d1880020045003000d802d40300030380a0300c1130001802d28a0b0180008103280031704441c0e1505281c40f0b00180c6042540550425084603456140a00020454010f94080e014610b00341b919041143e040c4415480b4591048140014032251030800004000a0307c4048580d54200300d014010150280004103182d08940c900c00d006076529482040e6008281c0a580c1c0512451482c001001078944c2d00207030b12990645000c1d82d010416409401c1c10303208580500000c1c85074403014001600142001d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 244158498 1250 244157248 244157257
    0x5040509120f1b0d030c0c02010801030f11030303092503240204240315230f0a1502070b030108030d0b0316030c06110a080307140712050702120d0f0302 67
    0x41c098518900b2500d5203d44080001d062620070301030b80130007040c543c040d9041c400c94424070b03038501c0d01c02d00040c4640c000810002e8107000c003401401480c0100405c010301e40303481c41c1d5850005410b60380c07645001c005468a4072206001c030394803007030100c02004403a484c85c0b4844017030300d41c00100c90584908641c002880905442c003218a8540d003000302007401c0c9240c508c403440c014a20440c0401601242d1b01c01401c0d20400c04150b401620140428800d602400c2c41072245500c046d02240100e140d5500010400004c1c0c1102c650800001c4001003040a0080e04120a07140d0b16001c4a4041d556800c03440d03068403003489882000d17001842000d1303404c4510307001000c104200504644007a00e04540c0c040d01120b00da4000c81ea0f011200000f048510b8020751052102c01c0303480040c10301305140b9142d0301c4007840018031040400c2201b40440c41c122400c002590f0b00d954104802d04294031080002400c20380c030a11003a03204501c070b0481041041e000040d220b034070741d4803a0380e4260100404902135029401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 244159748 1250 244158498 244158517
    0x9020c16121202120f18040506030c0f04060b0c0a05010b01050a0e041109031c09151407060908030703271e020a15020a0c05040b0114130b0f130504050912 68
    0x59040501903c0c50401c05007080d108900e00c01030346c4524000000b00c0c2904004502c50040742480d003080141e81c1e001c5606005804281c0744207401c0e02842e4000b030003d100310b400503d500b5101242d0703108440000519141800d1207500204070004040005403920300400e10848006951001510640d0030b054200403910200304142c6070924101d280003d082143c60034030005002660004900140e50045a460040c0170410305001ca810070480001d0200040f003240c10004000000c0150410245920060134290030900361030703d0741064000100600604404092000c505504031008807164507001d074101e5a00c404103039aa1080e55240c904011150a02a6800a1155000103000c40010900018000c2d03e9000c0d019004007458000401244c0d80c2010340120724001186031541d03040b82503140011403107804a51200f1842c221840c5102d8107801002965401049440340300c0404c81c0074007942055076800440041e141d42c00e020440d08219041c020561081043e06050105071707006002422 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 244160998 1250 244159748 244159753
    0x50f0f12030a09060219081f050d081312030f020606090f070807540608090102131d060d030503012619030809070b03010b090d02040609020c16121202 66
    0x40086d031410584c00290181040410b10210800c01c400941360aa15804100889500d196030f0804c0c020a001d2101128011b02c42c2c10005031400c1c00b100c14500d00030080071803d900c4443c02d0554500104801d800c404054094850b801c013050303c9160901800c4c0c440c101f0b1812402c401e40d501042180c0644014000ca024006c641c0284621610003a0120045944600405d000300b040d03420740358000c2100c4805080400d1101190300a41c10034246050103e1f0760a141620341c0b13450309070748203009206003d070803401c0381c0c103100c0001009000d00c0d070290500000140006005e6580005000000141c140c000b00024000c00c014007100044518203551110600711002034040c451b5441d41c0751034598061203070701c0c1c160003505104141e8040b03061030340800068040d0072100d03d05884031300540810300416500990101d170020242e01c8a9411680c43e540040041c010382d035448030745000a610502d4484854000c640c88980011140714a6034212181003030441ca1904c1c19499021846003900302d09411030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 244162248 1250 244160998 244161007
    0x4080702041103070f020c090a0902011724010e010903030f1211071205130612020705030d0905010609020403020a09050a140106050d0507030605030d03091e050f0f12030a090602 78
    0x180c0351482074401e4446045400c0b9030fa8107006801400341e1951302001780842d84500350313495242e151841140d4001c1490180461400c0a80c801a80c40619204009074481100340c204441009641d03041d000307a201901070040c14000c034100441c1c04a240f0490f40380030500003d81003001910030780c10805104514500015800b030319900880554129400c80d1020210100f2070b442481001c10142041e0580303400c150380b82c190400c580070540c160354072950082c000061710f208030711100c0382c040b6540140d104080d65a06c05c1000c071030400a00e6010416181980f900d980130134611181d108a40030303a0303001800c013901c0f80e242000d050b0140c0300040a03207040c0750322603881044241041e4013080c081c09060721059120042510b0910884200421000c20541088402c001d203071000300b03444055a41030b00d0085003101817400e00c1c1c0f1803110303182c110310700a0a00e1055101400b10108400341c4403202c1e80e0a60f410100d400c840d05684050210b409500d0203000c00104411020940c811004a4810b40000d81403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 244163498 1250 244162248 244162253
    0x51b19080604111b1018060b01050d23010905070e060702030c0a0e190902090f2a0a080108070b0f071505010603020d0b090705160201090509040c290a0305040807 71
    0x41c0c0d008001e15184c0058900c0048042000c103105020f52548510400c01c0004280f40b03243d1050b0911040181c14281c0d00c030388800e0103911540480c0c03276041e042d60043c8110003249810b40d410302c00c0802c0c0c16004048000004c1011400c07400352901490303031a500e42c601017604c00200701c010342c0156000c0b03915204000d4101e040792690b8014a0003454200100b01007481c000a010555440707a080001c82d0380d15000103140182d441c11005e5401210342c618100903543e400c0c0191130841103040c0180d50740542e2580c880c454107110070060011185950750151140d13600d0590a54902c0c042c0a1001c064206202c042070244061001d410004d0040011040800c102000f00d41101c1c42a00b014001980000c1c4600840241c3e00a070f00c041c0c0700c180c4490003607140c4030100400030300a80141127030703031100030960301c0039a0701c1a504803026200082402c001c40c1400e26007401c0c04240c03445000030100c0d90b0398039032030542c407000c180214181301080744600d09020301100b01c009100003002150441c7c420b2044401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 244164748 1250 244163498 244163531
    0xb090c0a270e0108070b070b01180b0a0329250203130602060103030e060711010e0f060f0a09211704180914070b090d03020f060a051b19080604 63
    0x300003410002d500307541420200740c00c0050b680c02100301c015040043ea00000d0302d000005044800280d003540f40061036018100160254a1203507603c0840320b813000c0140842d0a151041010001580d003050503006a410941140c0450380002a902600400c4118842e020070301d00c00000648103907481c00c4000f01c1e00e2404450240c02a00069002600600c20140c1143c0d2901c0c415000729080350400c2c030706640350790010744010f01440c1080a4901c5001b444d466041e0b071402e0811008045980b1840d124400c10865000781d1a104001044650005840030386a003200c102c26089140741e00c0c9040d456180d00d103000e80c00d5000751350458400c01c000203d68540000420150440f20404580b000b09170901c1200c404001c102c84c0825000007408200717190111007200c0d2000e82c1034a4a040d44466410140d00301205a20040281d001d41000c00c1764440d015800507200f078942401d8001c08003940741e1001c01d00d000d00d14407011000c88130450305000902a400c0f241d40010010408650411100c0180b01c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 244165998 1250 244164748 244164827
    0x1b040612020306010b16150b0a0b04030809100201060b07030806150301060c0303020711040504111e030703020f04020d02030f10080703030c0b09011e06090e0105100302060f070813030203010b090c0a 87
    0xa0f0780e840123440014981951004011f0441116860400d4203540b40d848a5118815081d4803410b0a80c002d2700c03105000307410034802091020a415100c84079400c0240c8030790400c40b00f0500c05c8005a14180350b4945090a4074169030a80d554072a0010b40c2e43ea0580c029800f5040a40c0d1041c82e04030740443d16a25401303182c2c441c038031414200484005600c10b00c25280d010101ea40c02140c441c001c03881c0310b518000b07415000c40c0c0c1c0403244031480d203000c400814020700c030741d45040030a140004100801a01c40900850255121807061401943e41c1c0d0306c0349441e588a40001000540400b0004000c50a5400c055070045070b484000101e504031542e560ba168140000c45411282c0c580300304000840d030030300ca566281078031440280114984500c601c80c40a8481c04001d2045102007038130b580d5004d1103410f803004254050140c2e0b030b40709001c0e0303100346201029200480c402c1d07013010000215420062841806581c0202c980c9081000d42881a65500444043c0c00c005042c2c0e515480e504500340126103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 244167248 1250 244165998 244166033
    0x1305040f0204081903020d0c02060d05010618060507050a080c1005040b0711060f010302040c1101050106020106240909020a030e03120906011a04030803181b040612020306010b16 78
    0x6075118a4040101c1c04c002c0c810755400b002c080440070000c00b0035004030b03030b82d021250740b8034003d10400710602c00545a4091584510200703807501c40081011a0010982c0030705000c0101c00c101090b94480b82282c4a01c501c42c80248a9004a0500700001d89494064408041c803201910301000140100008496003120b0a6401c081083d0070b00815503000300030300802518490203050b0619106020043e081410b110081c0555600e01c070401c00e0311f100e07004228024071028024080c0356590b08009018200900580e041c00d00c1200c5000c030201601c10030410098010703282e0603519460a02c1c00002500301c800c988040c107842d610004502c410a00c000d00214560300b1010a09040c0b0340d0103146410b80503000300a05d0691500750f003034803480440690781100d9200d09600e50300d9880e04005807814110060800c0c082c031481562100e05038404400300c184890070344040204a50f40c110640c40e030b03036032a80042d41542151005121942c10880104010703640f201c07011404030419601c0c0603010b660f02c03000c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 244168498 1250 244167248 244167251
    0x60203041b0801111902030405031605090a05160309020301180f0507060e030a0f0201030605120303090d21090f0b0c040614071208090a0503310e0c1305040f 69
    0x1e0204561100c1d5400c0180110500030415050509059901407040301e80080f0203840103205601c1032031003081260040e01c40a015941e00e104105c414240e00840c0d40609803240d00d40c3c01c0040d121380c0345445480d00c02e800501c00205038449100080d0000c18682c002a6055521035001c01c507aa2068205e043c4014402c142c181c8981825043c5079043c1403064000344201700368283c0490035681e00007181c0c2903a50300003c000c2c1c8144801c0c40140e00814207548026041851000451b0041c240070000e94800c500240c07d4410340711240808031130b080d540748003403000c5d2031203610740d080e90704001c1d40508802c07481126856103100d0303180c65031400031104172080290b00304005001c1c485180d11401a5072150f002c0c3c40d050741850305603030f14148a125081d260800b089030341030015425600810100c00129000026255500e4842003c50b001c5000da020800380c0340302583c2c0c0221000507000d0048202c608080c0503456a4869100c441255840101c1c0c0c40481da0611501003004c0d40c5621031100104102e000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 244169748 1250 244168498 244168523
    0x908030c07021201021303021c06060b180306010501120e030d090c031203050118230a150b0c0a080901020307210801060e030a0b061c11090c04031703060a0306020304 73
    0x10400018000e0030100f003541d006104c03040c08002c0d03080e00041541e0741101c040d0591031084108130b1100c61031205c040c10480c01c1c90000035241410383c00a01c43da41d11641c030b40c8403841d004004d05580702002e1050038002910f5070900c0710b207031042c0c5d804030003856891803d591070034503d1360000c000d9540c0c20030203685e60001404204104404401d001c40c00d529a420f041c0480d6161110b0300d91440d400c9103403a204503403590050484240c0000207012990000c01d80c0c4600740c208800301c08024001207000006000740290042200252441076641000e011801082000303107640e0385008607003040001c94103500c424400500002c040d5909e8064403100403c0041c080404440001c03c0d100c0107030f1054040c054188500d01440e200410506040c6811031009069600c441e0081648850340c80400c0d1154003d00700e43c102084000c148610640d4004c40316941c0c1c41c0c8030413205200c50b215610004060f0401080c559841003611809540e10010061004c030001d9034980741d50060381d0040340c0c1103a10350542e08 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 244170998 1250 244169748 244169753
    0xb0a021e06010b0702010e10090305190b06060c1e030a020c0609010c24022206080c041202010504090617010501091125290a0524040908030c07 63
    0x3440a6040c0a20300380e40c0e50038440c4a046407a24018062035041d44000075161080d6401490b80034042e0001621145605900c0d04004158000502045840d0301518010196004024100d130315025041003204d80c9548600f003c01180368040190303400b00c1c0c096205d25100501d80030086441542c0c2034406103603071b8100800c0003400c00c400d140d00684075000601a902076641d0101c1d2095a031035202a900903280581010505810710009040b0952400000c09030540c641e805d0404032001450401d2400b9151103a13000c0e5040c6000300e0f000852620705100c2006043c2c600d401b030503001801810024a803a4030b0f00100c07030a42d84181c00c007420340308048209650b070260034480c4500509981c9400c04c240007020b11455207510418070800f20701d07110200e904076035104000160199951044440350901c002903a203a8002c2020000741c01d400c504100019110783c0b183c06003602c42c68040c00448030340c0b90f604480b1a04100030f222a55001030365a8400d00c00103032000700450140408480e107980713440d080e1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 244172248 1250 244170998 244171003
    0xb040b1602061905070e090709030303050603060714031e04060b0f12030a0509011116082a060c0118031107080a05060f0403110a15060509040b041401090c0b0a02 71
    0x20016007107500c20707400c00c01441c01150154503401c02d42c510104440d02c0e128800c4661240404005900c1000401480741464206042404413446a14140001d640e02070825840b43ca0495185021900785c104005200c1d01000c001e5034040e6842e10740c40f07005a02585980c001010849040f11010707650458407041c0c0c41c0c0750740c1d100c450381002c9403126602170700c29181548a00800d0400380600c9804150301985a0044440324840d0005a040b21000c0c0c038000b03200103103540c1a00c210007440c05503a031009103050002840d41070b151480c00490100f81c0c1c003601880080e034130503080d0070240e560b110400080c0d0a0420151103143d4040d07039501d000500700404c50ba013405017962050513540d03c96a9102c0006001103612540908004034a107003039500c60405031610415150010928001d681c5141c041202c0e540261841c040c00420401074642c640052003403400c0261405051400034500003800a2071501242c403c1c000460008900c000e0382c0e644010014556400c000500580485d02c4d02c1c5440d0304 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 244173498 1250 244172248 244172281
    0x1401050103032c0d0b130203030304050319092103050f1602010207062d05120906090c040b1c0c090f0501050f030604031b081309051008010209060901110a0b040b 71
    0x20400381240c004180700000e495000301c20802841045d02c1800600384000800c00304084580180a5a642e03150501d003190700e82d4030087e42c81c14201c003440c40c41510280301e1074140007640c0020a402070504640cce078400001e0a001c400c11070800a080001c0e885040710700c0c000d4007400c0300c00c5500001c000360601c00642002481d800013000c04c8510b00d40c07500480001c074400d4150304905015a900030140a4049446101f0110080481c0c4a9042841900d00340020600c0c441d162032030690f11040a120200420348c0d2404450a51081030844000c0b04400e600c810304d1030480c801c14a441840b50368681070000d4400180100c800305648800411440c00d1082c0b0b54980d0340c40840141103145400d0b80e002c1d11040701128500000d218012111041068031030480c0d108080d00c691107003055641d0b51030003001d00400c441d19801201058000100a0014000e0318200c4000030700789030601c03158000445240c051400500d15a20071075020320302080502003054020307405144800c0043c03900c1103036220302840 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 244174748 1250 244173498 244173557
    0x61c0e03030c0708070606080a03020a050d0516030302031504060b0901350916031101021011180402040306050901020304031d090604020d0e010510050a0b0c0d0c140105010303 77
    0x8000b00203210350300340100c4080d1a03025201030f46869003030408000030700311500410001d02c40c407030448080c183c00050040d561489034081321071901502d0404c80706809201c030040d131084400e4400c40c0c0081e0080d0042c1d640292940f010031003110300307440011f0542d600c41e0b01080c2c82c07404c0003690016650780b1110700c1099854500d0b4461400320ba20313100c0f43c03903864480010500184400e0200746111414801840791010160100340001d4403805e000103290201c07a4041c1c051b00c200c14a07901c41c4a5140a0440d10850204181e0700b4440c500c1000c00100780c6030b0201c10b41c440c1d820840800018018031070540523520300c200060b100d142030700d40030700f441e841b1060b81c0303003112045180c4143c1d1359190285035070710017016100540c59221440700840607220000f0012015420031017086405e4901384139040c21681c00700c613002045991a003d24403d44101054600d042e00014901d0200c107000384034241c80180303d4840181042c4880c0c6400342102d000b17030070450000c0c071021800100e058010054803031050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 244175998 1250 244174748 244174753
    0x6071e08040f02090702030d0510172a030717010204060e01090f0902161a0601020613050c09060111160812031303030b060c100f060f06080f15061c0e 66
    0x600e41c82c0d0500c07009600c50000d1143c60f8030400103600e180700780150b8185003403c4c80240b2841c182120f0091150038980074013855036200c0c15800b8a10480002c08401c900d0000030710811000785070f600100a505200a02740d0188101ca0001540305400d0044012581040340016101d50402000034465010007100768100940c80ca41880039070080100c06040750f20700c40300180d45040300d010380b0031800148500034210300b15410380080e00240c0748840301d10030402682610099503401c1e24000d044280c1780c0d00503183c0d5101001050b000d041030660160040f205040401d031401004268901d04148140e01c984101a400401c006a14081140000071101c12180c2170642c940400d6158010308ac5c0c0c01c001d0304060700c40803070090300c0d225802102e594a210070306032030404541e1801400641007402410201920b054400150b90250040040a030340c50340d550340740d20351035040309044145c80140a030700c403840c940824004240d44800040005050401840d481c040226000000700d8000521070440d58 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 244177248 1250 244175998 244176001
    0xf06181806150c1c031e050c0405060705101b0f031a0409020112060902090a0509040c0605030a020405031501080d0f0e01030c0203040302190314010b030307120309020306071e08 78
    0x41c1d0360200080b5600980c103190320344440389000501d1400405440c07480070b40305086444c00f210350349600201301c035a0140d950180c10300c107081e42c16812110115940c010404d4140400d0200d80fa0001c010080070b4012400c840400f15020056402c84d42403810b002c0e14040650410030702250010500c1060301d016046c100550b0550144000100340c0b0040c4144c45280d5954140381160300a8600010160b40c18a007048401e48450300702c0000d50001e13600c6485541810b00008142c41c106040c10321480e40071b000b0301c11461404e0019520350b0405000190066028003000c65151000c002889124408000081c1c1c1549002601030600d52031084100821000014401c4080e41150b40c5c072101d41c1085c40c002800c820446422415400340e42c00c025070000028200504171021080b001066a00070031014190f40b41e000310070b43c03c0764103110f000c1d42c141c0c100344140300100d0101810500e205480d400d0218516400b07900090500e01e0031111500440d02d0804e920090710300e100610030079000d039030a00f40100d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 244178498 1250 244177248 244177261
    0x17040b250b040201030504081327110406050702010c15090204050601030917130e0a020c0d05040f060309060b04140f060406060905090a0608030c0a1a011d060f061818 73
    0x1214001000a03040c15140d01c0441c08101b85401149c000c0d0302c18103020f0500b00d494100f040c0440180c0322400c402c142e001315402c040d00e443c5102d01030210400c50b00030703031a0619040341505c1035000901c0c00e0303051246903942c490206002c802c20306495000501c0c00907050761fa030310401045450140c0003904241c40c140076078002943c0000e8146144202144031501c03201a905411903401d580e82005c46091401800c0c40b40d0641e071600070348000e04508090722581d0851b410122118000d91040c001c4119a41e14100b000c14000e81c013400700ea40c05500c002c01c215801d000410140c4da0410040c0100c6640041000304155242062030f0f08001e0440c0e0610000d498a040140b00d9082409001d1051020364003003821040c281c0e11050080c1350354001d482d00c030600c505a180c0c0315482c0c0c49007941c2c0103182303000707001c040810200014103035000d88484400340101c611410000c500001c000c55000700342c01a0400d201e40d00d080141000d41d524100d40100800140103000c000a008681004545400400d00c0304 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 244179748 1250 244178498 244178513
    0x60c07080a02010314090d230a021b09040b070f03021b0c1302160602031510020706031406151e1305040f09050303180a020a03081206090106020304050d17040b25 71
    0x55640c7d9481c01034901001040100d4071104400314450400e07000040c0d010743c0300e0b0003045040803d10580d4541100d0840c150600180050480740100030442034000111000d000f00000486074038245401403c29200264203c0b64403176091980c0e85560082200100030b28244841b960341410508095003800b180012060051844a000030300c11900800010410030700c1c1c602075155000b00510180240700d6410300a502c8615501440c000281054142d0115150521440f4001c0c1c0d0094011802c501c21984201c2c440d0f00128140c6407c10b1481300d4074081000b040020b0007200403c14000c0c1c03a1145004204002c45070b05c03000304020740c5d0030400d084002c100003200f50fa50114500307a4000c0750910310012141082d00c0d44000941c800420740f404414404030901070704c02c0c8840940240c8507030315082c04001181100f48500d00050380104000d0196003081608402d8803172042c4950488407034841c49188064010780c110148941012801c003060344c0c1080c082c03600860b000e840c642303041c807a252240070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 244180998 1250 244179748 244179763
    0x70302100e0f04050709050316030506150d0b010603050105040c0c080405010e120f1005063f011a010201180b060411121e010605040602031206060c07080a0201031409 73
    0x242841090702195405031280815a109050001c0080000c0d00c1c00040141600c24103000d1345010340b2902002102840301001d640c4180d907081001001c031a0744869800c02440c9400c03c0c02600110314181240018200c18201c5020780125140030441c1c0d810801840b00311072540107944104101c00864801140b000022102a5902031900040ca00c4844000c0f80f120700080d91501103511071b510400700391031008602c60000c07101d081400e00c826101c0508210051144100e41c202c0901a01120030741e0003c47d2515810000702c0030051800c0729480d003083d500712420303c0002d812009554070f16070142d41e4280700d80d000210400b200040091840d40396050f460800070429405150b851009012540343e801c184d1380c01c02482c1c8940d180c1071a0000007200ca5a24501381d481c46030729803500100c0c6040c0180e0554064079029030007582441043c030101900036a026011075048001080a00d856210512000300680650b81c0100600141031000404442d842d42c10014420440d0b007e2019a020200f80304 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 244182248 1250 244180998 244181029
    0x1020a23210601030209060304050109030305010f08100504030e100806040509010501180b03010204030609140f01020301060f0302071a040c0608100303090603050411040509010f0f0903020a1e050709060512070302 93
    0x41e400703030b40c9800c0103030700911401081c10b50201001c005c10081001c150043c86642c2d10a0340c00340032990b0b803200c0c201c050790503a000f080d5154001c00810028040c1552003964401c0c02490201c24205c54000403489200309610b00c800024200002c02080307040c00d0103990f411a4200c0000c014540c5070207810030301007540035042e040403a100c07810380d55655400d4044c0c034081e50f0803110400520be05450144600019109035030886d00916010400914040c4280e03412160386481c2c0c2c2483e5002105c0880003503100c1c5400703c03008030307014988000b0f4040e00c40d201da214038403641c00c0340e0500c0d0070840050100c4034010700401044003128422f100181e0702441010465034141004074847c1ca03249442a10a100b40c85283c0c0c001c1c0c40c0008005003518150401c110607085e0800070020000807180c4e04040d00d64030040600941d100e5121031000602d200805540c452159820441e400c2103507880c00e080040b00e6000003540c988540c401c0c8402d1a000002003401c40000b4020445c140c5503901294289081c071411 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 244183498 1250 244182248 244182307
    0x71101050618070807020a05060c04170105040203030f1608040801021c050723090d03050d14040f0f0305070510020d0b0609010c03360f050105070c030602160501020a23 74
    0x305403014007c103ca4075806038003005503000d0307261503200c12440d50098031070200d20041d0b03413040300080354061088d680141c0d0094043c51070502030400c44c1c52180d001c03400980201002e0f12189001c0341820001e04040c00b111400540d03102200d21590680c410644031164002307140400f8451150b030000000c8101c40f18440c078005400d2100b15406010f8050060840e030001d10344c04800040541c820010140c01c0c1c403000c030400c01c4940c201c013501034a05080705e0080c03941b00607102c4000420350f40010702020301d1203803420380d14189003541c425080460406403220201c0d008948000400c1c0640074149502034240c9000b820705200c2d13000241108614640503041c041c6000a069048008007070700c1a9880c401481c031018424414000c400c00c490794862a81c03030340d0540d10041748543c0b144089903803068110722090107080c1161281002584220049251211b4090500300010001c0c0080c1480300c00d1038803090302c00c992508090581080c803120003d00f0314020030121040550750858082e00c802000c50 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 244184748 1250 244183498 244183501
    0x4050f1203180a03060e0f071a041707051009080105011403030a08091903080109050907030302251a0307080610051602180103081c02042711030711010506180708 71
    0x450a50f0500d0b4001a08150030714040c292a402c00146c1104848040ea0484800d01c3d622000301d03000c0700345d9003100302c24a0700402003002080444140052060035003010742d46110399950028048403500702d045030108440300d408010148082c410680140115028454003c0c0e00d04c00003074491080c0e441d9682401002000710307107900d10800001c80c014103104546a01b0080c82d0601500140c82407040034041414480066085040400c9003422203500d50000e1000d00400c0e010190070580d04101c0760707400b0ba445000011064aa002418512281c040b0800e03500d05102400821012380200b003070b409800c0750340d02c5096090744076003203a541414400019842d0b560904c005031000181140703409140d0410000031060110103401080c0351070400c03914031904521040d00070141e004500c100b00380000d40d01c2030402c840718850388010715013084480006003030400840d6840540c00030b43c8c58800099040c40241c04c03592007480b600380c0010b01203464038000b40041e07401c00b1030308030020310384406c000b051030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 244185998 1250 244184748 244184797
    0x180f1506091804060e01050a0e061506040b0a02420420041103090304061b02010804031413030b100e1b0a05070c06020c28090e15010b04050f1203 64
    0x45c0001c50700e0082d00c00074401410a9103400d8081c10040c0d68162032030140034041054000180b60141e10007070040c1000341024070740140040107800c40f009a805500074492614025400c1c444803d680451040103048810008101455400c0000f007007031006e0100302c42408042030360740030020707009525802c4007089068000003003405000b01a07456185e6006c0070083c0410300c88048090070581d81d039a900d2903038942041c000100c107400c0451019000c92001d60105000c64840d0041c583c026035002000c515040c0b05280d034800c240180d0340160780c0401c5403024401e500112005a0b401031040c090104000e0502c034600c41c210010b0180037941006000807070818150080d404d6420305a081500c011505d542c6800c06915401e40e003146030f00c569400514100c5410001807511454048864240300c00c40c00d21054500070004803860440901c60448901c007140000103c09010300441310b006034131a0314140030701402c0500c0c2d08a0b60320400c171001e81445c1e01d200010540305900f2040d83d12803030103540003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 244187248 1250 244185998 244186001
    0xf02040b040e01140d0b06062b0603060e28020a0b040e010f120305030402041d01111c180605060f0d030507120e01091202180f150609180406 62
    0x15808002800d4021074009250858400028103c4103005143c4007042c5141c02000ba1900101c200248040c0c081404030f0601d06010f8094184525016440054a404d40d03004200c0b8511404100300c0d15601c030b21080c030402ca2907014600c0181c941c000141440d15041c0c0000b182c0c442d060820084c0d4480340709100042d0354543c850b0800a250b000c540c0d88d82d40d6254034116404070ac0901944500c045104070001700044002d0200440c0c5e505a9586821503c8d944c0c01c01015000c40d904410708a54208030300c011010082c407400d200c070340c400d004541e50b480301c15400000d0040c56201d02d402507840c0110070580e82089000e06000598045000100c07076850000048600c800d00f05260b80100c130350606a420143c00a00412120b40180350600050403c2c8504403030000943e036815000070101e1004208001d41141a1480d640c402442801410300c10300403441007940442d0903110350050242407283c90030410b00100e206500c182c0d0024644442c640114606d41c800660050902030701c02c3c002420310106 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 244188498 1250 244187248 244187257
    0xc23041b08040812270d120209011101020a0215060307030302060c0f07060207030503011e03080405041a04020d05061002030f091309020d0501050a0f0603020a090c1101060303020303071e0806040f02 87
    0xc02501e042e40e052640c034040784140c400c1c500402d0010240c0c00c0e01704c85000041c401c07420f5081c99540c0c10080d0302811402010b5044418a203040c84015050790340510740c03e00140a1864055000b05042c0108501c114203121015007a98000d41004000744040303035001c0341159000a8003221203644501c408000c0d0018031940034081c110f2403010802000b0141d101c0c0080d8101c403010350004207445440f004103684080d42d880002e100b01d0041008100c24100740c0c1060758100c800408071403840614401142c00d03030b071040c0b02c01644155214100040c5141c403a100714030012280c40111304120a081c0c8144162250f400014480d4800c0414186000b125412a001d03240c4d01421101042c1e0681c681399020b40026203080d5007190610440141c400c1180c841d800403030741c00801a20083d850040d8100042c11000d14440c01c0000003480c04400d154240244001144607600440c0d5031700e05110000c0031410070038600402c08507114450a141c9074450071003a000b040465001608241c4842000c2c000e202d0b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 244189748 1250 244188498 244188517
    0x604150f14041d010e060f190506070f0c0605130620011a010f020f0709020f0702180601021b0f0111010f0c0302090307090e0a0b0903070c23041b080408 67
    0x10018020035030040d01441c03841d02081c3c02c00007540598030390f4003091070072000302da0460300425010101405440e0104400d5117503a840c5088008541d204d102068140e40450015034104124031089410400c4400052004042e03a18009007028140040d0301c023881450300c41c1c0c500304240e84d00c0900214001192a10000c0d40340c074020404110b52800301600030720200c80030b502150a045250500030f0010a03014090b0072910040e20100342868aa14000e40240540d0720840340d0920030140141c0b560701000401c1c004d03030b06114003640340c4074000a240c018081c1c083c3c140002d07442011041c903150144109030f181c40908284015010654082d4018403034801114007481c02d11105102498040c4d0061400e20026401e82e40803036150680f00041e10400c0c00181a19442110f280e80420b80000038641c01c0000c03001528900110b80d10707040203001c0c01d0340241c0780c40700101601c40100c0295030700e00403604209450030b1080c0090003170600c04200482c8180c6040c010400000b07010088810b0490720780c0b02 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 244190998 1250 244189748 244189787
    0x14010b0a050d02070b0402030c060405100518040c020a0507050d12030e25030c05060f032e06050301061b05060a0c03020d18050f0f062805150f0604150f 67
    0x2851741081d89540c2400e07101030703001e80164a0461414186601290103450b07000e4098103607880114000c07106d81d4007054240c4080b560036036400f10030341d0340c1d0f005200e11101503a00510b0160414100b407410003480c0c0d0312641c0b180440600c10800a1120408403a00b4411803d002a40c2c2d050304001c40c3c1460981001703185440503500b01e0b2a001c1e0b2001c0f0f0081c0c1517901030b0300548640c42c5c0300d80500039948101000340400e01c5050000503140905016682c03249880c0200d49004401084c1641d030f07c2c10165004500481c034003000600c0000e6002d5010080102480980100b000b515100c550f111203019002811407034940e44403108460013038040b1014101030f0101008030003c6400c0320b040d214400c26048800d4000c8201d0000503120010b024040c40c0a501e0103003105844107070809501d0480e243e0408100d074204055a84808220f03c642e51044a01449000f6841942400c20407500149200d451141400b4030060003001ca400c0c6429000c1d0445081c0403188480030350742602c04618002140b45101d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 244192248 1250 244190998 244191007
    0x304060c1118010f170118020904020604090c0305071b020112020306060c0307060626060c0706060b0d0b0a050411070206090303070b01270501030503030f07120204060314010914010b0a050d02 84
    0x1c03504c88200c03800300d0303104101c0d030000c2049a11280b800e0310202c01102c81d5007490742071880d0251808180058000e840145020700d070640d1b402d40300d019a0242d07403580c1c001c2660f48041000a940100303076007903090240480c1d0f00d01c0070016030010302082040d481001046602000090a6031160006c451401d119003044130307210516450000c000d41014002c401510b00c0444000e15106224002c0d030090603e040c001d1b02c429039440701d08421726007200409031290741e101d00c00011a000c840d0000c002505c040c490109584101000307002d00120543e0101d8000c3d4500942e00d2040101c2c5016075180a50440303110350349200d50310000e440c500800d6000341801010100004819204800c0805a510391403c2e00d6140720b910024241120401d00c0090160b420030000147c12002140d2050b50003059030400c541c0301500946624100d812907005440403d5503440800010b00ba00e84c18140102010001401042c0006842019104041c81180143ca5001c03e1081129021308141c8269042034842103445 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 244193498 1250 244192248 244192259
    0x510140405040204030c08070611060115051c0504030f140a1220071403030402060a120e0105090309090906150d0f080a120e01110313050f03040303020106080f0304060c111801 77
    0x9011007032041c06580e1040d400001001c9d40642e0602e05902c50b00d6001d01181d0380707000300c01d0307000011a090785410804104201043c5440d003c104508547c816900000d00e890302c0d2501501e804180c0e03500704184203c007191407041300240021030704449002c2c945a004152250509000707820101d84004c401d01c200c0c3c8004e1102c2d00703000c0c0540b1940c4d0190b220308040d150000061500d070311050343e01942008003080080c2c04140542d0807850000380078a40054032541802d001c5084540960315610030b90400184441c1e90f180c120012504650705001805040c104449150315101ca060050360050b0204500d0b001803001110545030803a40041c1400c2d607445484a00600311003410188660f00c83c80d119982410000510032180c04180341c03c602445c1d41c41c0d2000804010142d2841214240b0412010b1200702106001800007140b19800101c1c902d824800ca131402c2c000306c0c1078440015401404100120f42d813281a41c9000c9401a804907004001c42c00803443c0e48444121181204a10b00b000150 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 244194748 1250 244193498 244193513
    0xe010b1e13020c0c03210301050d03051e0307020d08101a040f080304060f021b120c0619030501060f080a0c0e03011803080106050414040f1d010204030c06050301051014040504020403 80
    0x40044090361070031010b0b00d1030003a12000d1b562955002d4a0144014405030414040c407070901030180c14241d06101088640d6003140401c2041c010360000040300f409240ca8040005400303401c0907041c403818a2810180d80400c884103441040c0c0c104021034080b01d0758180c043d040310050404007800380d102c1602c4543c00f90b40e90740948100c50002d202c1c2c100c4501740c00c0c40810208400303480c2004400e4952100302c00c11400e14607024a525a80c060030361400c0d280c1d610740c001000c2203807000c080c540040c6075004000e0300b04c440590100b42030140c10301003482d00c07940c02401f1540c0220019000600340c0015501200d030041424112170b01076103040740165403e032600d050310304401d00ca50303240001c40c0e8a40c4c0c401c4a444c0528814000041da0202c02c2c014180342c00d0f000406030500715040010403070a0410540e603a10030022440055941c0000c0900610800b81c06103009840b2a0400354030f1949400045400800c46103001e00410041c250402501e085003c00c503001452300800a5449036240c1c140b040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 244195998 1250 244194748 244194763
    0x40e0c0d0207050a2d052508070603050406150503030a050c0c0d050606130204051e04020c01050f091501030201080a09050a1704140409020f0d0309030b040605010602010e010b1e13020c 81
    0x11040710301e00318500040b00021000880d903d52040c00f03003001074450312090382c000410401c6040065510007020424023403c20040004060780e0707501056900301810300c60304070359150b03600c42818501044107000c11b403400812241807054034504680c0d904000c0e075070242003581c2c040160350701c850700514600505c1400581e1500618046035002216121026000d04034441c80c851550094030b026094443d20004890b2101d0103c2c0c043d10240c40d08000c03070fa585085520844030110460307400c509000800f11f04000c001c80908680b1500c6000307504540001e4155000207002001d400d450b0600f038000c10800744030b10b00529601010500900f07224201d02d4055400a01440c000350701041c2a51407145083d0182000d015000382c102d0b800008004180038080190280c01d5050105038a000400200d110400620403030107944005215410500000d0940c3c01605100186a0400050200a9503000078803002c80111039000b00d0304d89039000226007800f50310080105d0580c808a03842629210200d03804 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 244197248 1250 244195998 244196033
    0x1905010e01020604050726030f0403150501050d080705010e0607020d02010e0a1505070212030a0605040f05070e090712090b0411060c0a151e1e02040e0c0d0207050a 72
    0x403821034022001240c2e40d01040f600901194030682d8100201303c40d001c20030782e01c0030011030006070804c602c040d441e1540e03100d8030000d422103200003030030801c1c4400c4a02a508030100c0c030005110552618000410080403080c020381440030000f17941b070401100354401c21400c880f003829541c81d844e0000300691143c1071150741c0310265003071000d002c0203450701150300030650f0350224250171038207038501251004050081012080d44108807c0700c10340194007002e0b40c4550350700440450040d040605000c1074030280880c06d00c1460810741031180e020340182c2140e0400b202614014119500d1610480710260541359818040b46800c4101d41800b020440442c4500d018840381401c81c4c40310070030b00400384142c0101744425000b40304040001908640e6400c1880c0c891a40480d44082c8420041560042480311101407a510610741e40080010a1210070304080300c1c404605051800c40384802c03448004080444140000648200c00070481d816920b405400400310391810b90f031031805d00b0105454101c007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 244198498 1250 244197248 244197257
    0x309140616050c0a1703120402040e0a0b0403020d14031308040b04090b0f030f030307050c010917340201180b0304080322020f041505130c03050114090f15190501 71
    0x8a00c0721760614815182030b105000861900c104007140044548019000726441a21010405540d40003001070420710713809540e861031241842c0c6000b03413070540036031000c00a00c01020b0700d001c1e2030100f640649502492102890706045460301d8030f07241074031170307608404000107000c1000b280705046640848000030040d07601080f140074510415560b1024180c0d6000564010000180d11314400d00180003081104800800e0603207032503913281c18560f40c54001c0c4112450105811007400080e25201d0b09201303c0700ac2c125a01190f509100b100318584110190500110f500d60141c022803a0f03c00e5401090a0089a510785c1403501e0005d0fa280c0c816203119030100000104071002000c1d50b24220f011944c000c01e4404c09400d2641840701a2150341c40108002c070189070000f800d82c441040c20401c85003900000542a8207880e409000c489040e00401084030124031542c0080e06ca8400b0982c10021840c010b540ca50b507240080180c0114030003141341c001010114135081320031900c1c0380c84240c400981305d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 244199748 1250 244198498 244198519
    0x60903210d150e0402010507110d0821090601050103090309080a140f06010e04020409150e030307030606090e1f09060902041404090c0b09030309030304080a02090f040309140616050c 80
    0x803031458080300d03800f52444491a0700301050040d070082009000c0d1038400e00c94642800e2040b000180c0740c4141790f0044e80d540b0400224803000300d00c0c00400c5801c8154070b40007411903041c202815035550005000d03060615503113440c017005041c040c400213070003000700c0c0080790808181d80c40c00d004058449401d824491003135003070084103144e0119405061700c1c409a005515075031660200800b826080c2c00554503041128004448184103004207003644a0100c002c1d946ca00701494001c2c00c490f880c0e4403200400c444100240034483c0080d6000f500b060f0000001342408400c02a0320f2a804150b501c500344581c40e12800141c80d40d44c9401410840345002d4400450b0f400410512041d58100e20008011441c3c141052140441d80700240c403001c00040c007107d080107201400300381781d5031054000c1051984080000c004601d01329041d0795008a81e06403421880c10b01e0b607006040d45210b8000c00a205141502013482c5860704000d603540c41e0503c040e060031040b01ca0902c9a2561079038900c01d030140b6840361 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 244200998 1250 244199748 244199771
    0x6060801080d0f0302070203011a0a050a05030c040207020a120609030e04022109010204120c030c050d08120915070e04050c040602030a12020c01050103080a020d02150402060903210d 80
    0x945090480d4190301c0a40008100b03600100d40400e4020b5514007499801d00910000d41c6003441001480d503401e29401050320402c1080102a096030ba0140b889421051010b0066880104120584600070b4401584550292000883d1028241c200480304440325643c40107100301508140384060107a10f400c030400180d0b0007884140e200d580410030000c202e03411000100c2c0f031804841c9901030048400141050303255007580800c1d030702d10780082c3d8103800c0010301401807000a84400740100021564500c422600d583c0b110190b0107202e030185040700c3e841c40000d1070b0304001c0c40107500208c1912814002c17031402d828040c0000c0c0060050754040c40c540380005000c150030100f102e05641c5076400071420300440c00411200042c8052150461580034044603500003024010980614800c101680e11004e12480092500d810702e00182e04640c4102524134100c4007208005800a0301910700d030b0798400101011910700300400c003404d18801c02c202d82d0788030200e007054060002001d82c01400c0c000e006020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 244202248 1250 244200998 244201007
    0x31006080106140c21040905090328020f0604030c0605090607090b0d150305060103021003050105100c051507091e080d0f0c0501020c010903080a0510090c02010603020a17010606 78
    0xd01a44011503140014408080000c1c0301500e20340c410202202d580840048111105e1035501c1d00f41110001c020909100980b054001c6aa0091050008509004070201d840e0b000300c9800c40506a80f8120001083c8420303c01d2200045e030005280807181c0328140b03494002d104045103001558064580404180f060304c1c0818071b14042c0c2d4180d9038803c90345060012808050f07000c0318540e05025542c03d00c80c1c0c07880d0f0380040c1c0d0500950280b000341c0f40962540c014001c41c0103440000c0301c100b41c54080188420713904c2468802d0803c40c0d916188010420741d1030b0444c40c16442d54403a42e00c05001e64100038880b40c1c040c0d03104095840c5194910b18150070061920409082e41c0540812604440d940a00e402c0c816508900f02280302d20b08030300351032181d496060032680a1002d40d400d40c2d4444c841c150030b06811201c40c075040100c941081096180284400d14014814040c48a02503240c0103022034242c402d40010020f950010300ca50100d47e40c0d103405050034010940c00481759405c1030702c001002e5025 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 244203498 1250 244202248 244202251
    0x507050a1e0201090c08100630081b010c090617011401021504120311042102060409020c060411060a02071a0f030f180c030a0f06020f030c03100608 65
    0x200e07100c0644144a48441951410741c0ca0320150456590320159408282c8103540c480040c000640604a100b4011030030400b503a4039504841120000100b4120241041550100148502c280c8031000e519403841d100c000d0b4841c80d0750100c0310290640540ca40c03614198059500842582c985800300342e51800292142070611111450f8280c05200401151817402c015040d038120502c191046203010307049141318a04152025200d80840c0c6d81d20b41152601031164071010040404003500381340c60001c1054402604116607144825031541003000c64590344141d03005800c01c04815074561200c5042190750700300450301668965084445107001d400c0c41821650324444a5001c1d100c16814804800d43e01c1000c080f04030300b010705c02c01c121080d014402020b180107203c4806021401d040c0b805454500c0030200078041a1604411400042a900021070a0303120740d0102038000b1241e19030804400900641005540b0002c2c004100840c00c4031900055204113507881d003004070075440ba0804c4814120 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 244204748 1250 244203498 244203517
    0x30506010509120307021203040303020c0306010b0403140703120201020903060c040f03020108150a0311090f0c03070e04060e04061d0d08010501030504060e010c090501140c0a3909050705 82
    0x241000540b00314100807030303000300d460094070403a49071402990100d0003007020342a052006403c00704003801010f505102d4450104011002031140e035051003c00c0007944143e10004284e90136032000d83d0500901803002c40000d6820202c0c209004c02d031a04043e0107540718400c01c81c400d000d500d00081244a81400741c4007611500d5613034100007030440e0f0040d189aa4081d00481c04002003002e5000d43c1d61b18000b003500038500c901401c0500074107010500443e15070103015140d692454108100341000b6043c1500d50020391071820746511200032020600604058105170740e00c1c400b0700704000a000c00c64002860101521002c51000f140c2a84520748414598a0000c00165030300700422413584203070006e44c0c019000d10300c00940400c2518046085980080103880824400c600030803440da00b04008606e52264000568900700d05002d00c10348481c9002d000900314000030100f13450320301140744480c400c41c00c610240d0580625084840d4a800d034188a900c200714202400503d91078458410b403940c607070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 244205998 1250 244204748 244204757
    0x50105150a0b090603190501090b04180b04060c050c0609030c060106020f06041b12050c01110102040f05092802030114010f080601030509030f161103120f0a09171005060103050601 79
    0xf0481070410216910152208003035040c84214240c030750006100e654000e0840f80c41c0003503000064018081511072410702c5903088005441400007041803c41705a501551040c400030b1201d42d0704000b55074a0003130030040801c2c1d11820041002103030001008010000180c0c0480e0300d0f503a030b501c030100d17550752105c81c00303028035040307840850009240c40c0104a203e80e00300385515012601c442800c0300509003446c0994039588841c4160b0302958000511011541c10344000798981802d100080300742e101d09204144c020f000c0707000007600302e109907a07468a140300c1000c400b642d0f15804004d01000380d0130a0040400300740340c07210031400340e41c0600c5014004c0708007a12880851380e07880740158000c20000b0711000c4140810001800c00320a1180284a19840c10b0801140481142441c00c41c4141000526000740e11000c011340440410714150f6111800001c9400c0d910043d0310030844048226034007500380c070b01500c2042d10b15040c0104020001ca030303000e04d0800465465030011801d40e1000c3d02c80e0750109 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 244207248 1250 244205998 244206007
    0x604090b0301110c100606050301050f01140708030f070e0a03030909090c030212010c080a0501030c17030409112d0f070f020d0f0c0f0501050307030e19050105150a0b 73
    0x19064005000e9868000d00000d0303a0b0810960100c40d40d48800540306590b00049079541c0f604100744540b5001c3c00c5549045404e641c1094041103004c0580105603042c00211440b0350740c0310314a07100700d0704034a0380541c0d640d8490038100320003002d0760340655204c1e01007890340b400710016051005030130b000c0b650181c2d02d02292030314165a240040840210030703130f0f01a49014010000d62514481610070b0080d000002865a00c601c1005100782405020421450b0038100101b012555102c00d0760709071041c0d4100a0540282c0403810b900d03501c1141d0020401c5424418600c090440350005044030ba500d080d40c507009642030902240300511000f501910610b801d101614400d040348003e84030042c41503080c4105090a900069000d50010000301d4005200700814401c00010f50300700801026506045920f85060500207001800020108001c0540d80c000c04d802c564810043c080800c0c0303042403131088045440c14800d010740342c200c60a144c4000c40003100c16150070800030310001c5403031044555040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 244208498 1250 244207248 244207259
    0xb090312061012060b1c1109041e050a2304050a030e0102120d0516020a1205070f12020c0118050306010b03042a08060105060306010e040e01061e03110d020604 70
    0x59401440102d04100001d02e031101d940c105445840040c0040b03404980d11010140510781c80360042d00c443d0a0b0046c10100c000d200c0350000d1040e20003a5908031008a410003103031400b20700c2242c0300b0b4600c04010b810001807000f00340440d0300030142002044050018070240326400e1703441b140c003601c00801ca5800800d492011920941d00b5461084051064890078401d28030b094069420600100341c00b50f41d00c40078400544d010312a80180301c03215001420000504d901d500440a580900d0801403290018040d070400100780a1403d216907c401036031700410f07456100070740c1c8540030303000ca81c04109c1c00c885034111207030030300c91500c210b5000a00401c0603a00704000503103e03800207081141c410144047c44000f411b003014842414410541041010718681408586400010383c8040c2c0035800400a0001d141da00000846005d00251030203d100340344600110b0042038168040c1c1c4006d81d5030a03101c0c200307000a4081c04101ea0007400c441040600301030411900c1c040d6440700960041040204214 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 244209748 1250 244208498 244208509
    0x109030f02091801061707150504060c1a01080313140a0513140405030d0606030203010609121406011707090209030c130902030313030312090201050a031e02160b09031206 75
    0x748864a1070059100e03640e4403c200d400c0d1100d03900b20300d24020f4440130700790300d011003000110010700c203200d01c00030b4901310b050000e841d42c880d501450003004250782c4008113000c2d03500c1061851485c0081c100c003c66030b45d030030516100d803c0f000341c18000343e0784139100040c5802007007000d440c580001080b4100c203d18240410079032584030450b4428990712240e85801d60761a12002612850090015542e19820030008508461070354110701d00b4188148010321601da44070307070401d003540c0c101b211000214509041c040b101c0001e040059a01d0710603000040380c240c0603082e004000d840c4000450381c101c0c0c0c6855207941a0b004200c25540c05a1240c880c040c102e05d00710100c080d03684410702000400200e240c000c2811980480c2c031000d080480002c0810400d5881030a41170962a04c0100304440340a585c0001d01c288070315071502c8101a210075030b030414002041e01d40c140e0002141c0701196240300c1c0048002c188214128255048420b00000420007407000c02240e10155125441c00c01e96500c4904006 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 244210998 1250 244209748 244209751
    0x90d0e10090b030f0f0906070c0f05100c0306090b0307030b0601052a060402120606090c0f0c0a0609060629071401050a05010e150306190231050109030f0209 69
    0x108000d0070315000100d0800c1d40c1c00850040100c0c4003082001d103011540e41110640c0905440b050354000400c00c5000e0354013034000c0700310320707070200100c560490315090052800711050040101c5624040392101520703019440607044440c60303041440542581400c16454041e2480060140f00d00240005c0041d0b1140004002c004103000c0000f80c82a0790081405c0d00e5005051442c03081c0d80080140019071802c030038983c409201d80300040c040c501d4141c002c00d40001d0082d2843c2e42c0964042401d10400007603c003a40d049400010407540d4000207802c100002d000411010786184c1d140c20004035051180c0c6203100c40c141d14034003113502c2e040101c00c05c589050380131020540d0a5521404c600c010802c0c00e01606000b03583c1c00c04045001c2d41412078540c03101c0d5014041140c440c4c005605114662004207800742c0c05001001030102d0781b050000da84000e4402d02150b07903004810203010703510707036092105440d813a840e1000039286659213030310055800d244580406400301103d82011001813900001e0607 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 244212248 1250 244210998 244211029
    0x40905070c08042306091e06250b0c0301050619050d0606051803010605030d0e030a02060c160f0b07080a0c08040b0903010b060901052502060403110306090d0e 70
    0x3105420041e00c507540140c02c0b0b038000c080512008102ea01010740702481d10182c0c04d1080741d0359031a0040e480700040c1100c15240c0c0020081408840441995a070501640c2c142c45542100e020603002d03034145a982d86c281400708541c14101c020105641c86048403e40c1d058440c0509100d00d01051520340784000040c43d86244d0420000300400c4500c18960f006410081886d0b403034030b03034035203541d0015000310010052aa90180e0300d85081008641d4002403500c0c1030340414144100c4900750321012a09004180c00301a400035400036041e242031800040c5010b40954004941004544800080e2009001c034490307028144828442c2c0c0d008141201c00401c1250007508100d10640866a10009250080ea005046d9060301180441884c00d0078006e030f42985408980741482d0405020010f040d038000c141c0103141454400710b082d46a0240040c00790301064004102d1612280d480c81c0203240014101b4070180a40540d00105510a80015240700c11010725245d005542c1c4442040c81192800c000d800c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 244213498 1250 244212248 244212257
    0x17070f06021602040b041a01200f060610030603120825180504050f0a02030702120d0516230a030b0406080307020406050604030b040f1a07020a050c0102030f04090507 73
    0x11a0000d900c0384000d20070b07018405a00c82e04460b95004020440b02d618252600a80c1000791000c08007105d0f03540b08034041001d0800001038402100040c0c0c6040007040c984040707104007001c4103012000010881d2003130508460541060280796002c0b0141d4503076200050243c5000300d8070700c0c012402031051560100005032455560300485003110341890240d508640401c1c2c081e03140b1090882c5410b1248003a15080d1002c0c80b003800c081c1d109010092006042c9100303940c0c007202003843c0c1c510070f004918031440a210b0940d00d5144500c00c079001010305407680c04005040243c140c0c011400748000003007000c0d003c405020400d1581e42c8420701c5a01c10484101010343d250015a21a512886901b0240004100443e1a904244140411207001e900300ba48a003800f0b001c1080001c800c4040951f01a5124070b03000340707501c218982001904415248250300c0d4542d8010025165030001f100d50f445402001200c1c10303c0080d1005984034800c400b01004078800800c418006104560070050b00088903180 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 244214748 1250 244213498 244213523
    0x120a0b0a210b150d1212020c031c15170705120c01080414030a030615020610060e0d060e030903010b15040509090708070305030a1e0903020405040c080d020106030510091707 76
    0x141d69130481398048400040c041c6440590030b40c80b80090482810050007149000c0804c900d2603a13a0043d102c440c1034411282e4007101135110641c0000c0003181d04080031003181910b0310304039a085040e4200c9c0314003902ca80880040c2c5441c00307000b0080b501c500d290140448503002001102c40b81070040c400d940101c26000c0c1d00d801400e040000f8054511035079000180c2e242006040c00b00e0a0202c100b1404551000c0140450468001e000b1001c607209810079000219003400400d20642030b59401038282c0b0318102c42d0102d6800c1c0032000b8840c59400310001c0109160075410410f0314081603540a000c0c1030117210901884c18500d5544ea0403006500c11601c400356a50071481c035202194200b140c90307400125010100b07641007107040715400640c0c40b44da01195425000104940172520000c4d1140d901d410205050011002d9481d01a02100050701c0c0084180d00000c3d000e0800351004903658030914100200c0c1198500c20024041e40c84010300320740f03950310302022030507801c040003c2d80d50a10704070707 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 244215998 1250 244214748 244214791
    0x4050409060615030f0605030c01090501121104140f01020111030613090227070c050307151508060106020d08060d260a03050601091e0506030c120a0b0a210b 69
    0x40e604083c840255801285c00e403d90510b60056a0481c0d100030300030750110f0345c4602d10b03a8018501c5001e4030700038a0040254a10707030340e10b4005883c580f5810100d250000070b012405203241d000c030406400c001d0b0b80600040c69007000480c00c890b1407003a6940c0108080c004600c00d0314100c944045205101c00001c0b41007603080d000900c1410310821001003141d040702e21401078403404000b0b0360344094507080940e43c80d482911503540340d2280d22070003071041810106100401c80319502c80601d12913035041040300075490b54901d030350b0f071442030045901501c60703010027a100e14400c01c0024410600949000c041c00c406588200800d02d00300c85050701031a81d00c81c410030364a040806041c2009941d503010070182860703030024104084c0781e0001c1d03000711040c1500409140c480c1455401f192000d98106541c0e5984601c0d0340c041e801074039503c0c0d0b0368810318001e10034130a1003500304000e1174104803841a140340c0e803110b424580640c01d595400d43c40710010004401301c0c08071520b195104001c0c00000d14078a1740c88 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 244217248 1250 244215998 244216019
    0x60c0c0501060906031a0c161a07080103060f020f040b0a02030f0c160501080702060601140405130b030c010504030b0c0a05040b03010303081b03010503070e190501060f02010c05030c040504090606 86
    0x1a00020041070380c54104000384215040c6c00c01500100c50040d804600b80064800524443c10031120000d210450541042145640c000d00b480e600181c0c0c0142c0d28148144000c1c0481403e01c400d951403810032035840103001043c400c54004141e41d4032640c5c41e040c9803005042e800c0d0800b0102c401540824025a0b010410711002014003010b26006017800c040c0d50b440540f4a07a07c00d40125040110030001c10040c0d540025005401070000d0074500a40c00c2882c800700710f6480f070354100e21f801c04441010a104801d49800081c0350039403c800ba9090820407000450b800e002d1444060070003804000886c0a480d80840281107505a03031600c140307016116040c0165651081e84104d0020f00d601041144080d40b4030032510182c0d40041410b86107524040000e69295401d003d80c1c00e0590901001ca04010141c21a64462107110740c001c0c8060340c1d50715009004640030001071800f550034200240100d912a80071240700e1984d820125080c20705220511000b03240e92081200d003e41d8030f0602103080c1510 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 244218498 1250 244217248 244217261
    0x1803072d1a0a0b010c110d150b011727010204051905031e10020a050c010c0e030708061905091009060501140f06090402220b0a09080613060c0c0501 65
    0x5120100d40c08100310301e03442a2008000c1115210354502210320006a901020306001c0750381010341400100030340380001c0c800042203900108401d00031100a46003555a80044582d1202600c5448000101c0c8110689c4100d00322405001400b000d41e40600c406055848031036040390f00d900050801d0384a0b1f000c40c20301208142c07422085008901c1c01c001c14a01001480c0911203814001c83d5811861104517644007030a034100d4203c01d0b0085130b200d15892095041c0c0d41c140007800024442d018005034003401213440010018081d001ea22004100c075003000030b42e076018080b9000c0588945000c081354000400000e46010040d00035007014200591a600a24446138003a40c0c0c0001c440d4580f0400300f0303080101c1c0312054061440503802c00c0042c1c0d00ca03419503403a590141c9001d070b542d000520841c9000041d030810400c0300d00c80100c2c0815403030641d1016142c06202d50315480041500d650403996a50710031a81c6200c4516299101c03000960b9541002030742c0505d6080c50b45008200d03a8880707095030780 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 244219748 1250 244218498 244218503
    0x80301090510081b09070c02040906020703020d0c05030a1b0f12020606030c0d02040f0603021914040b0904030c06060810050406060603060e0703050903040b0d020901081803072d 78
    0x7156400d0010101581d0090b1004041c40401095108803000c0d10f58494024108414401e401c0345002403076a0303001c0c1162424281c0d0040041118043d9450414020b403c409801d800520650703512845050003180f440c50469001030095007858240d4008444000c4001c0d151800c4131070000701030f0b001440d0000508001d07413140303081c4100701e0310480e0000d1074410300409030303842175122003414a10b80d2100c00d040b0602c03d405071008a0b55104a4440300007804140c1e000030340010440191020f00100800d04100303480c44084840c80c203801850030401519510f41342136070f100002002160000e8020503c0c04111071255a02040440d0744141040c10441c0c85030540c41aa5213032802c001c10803a0030712a0300058001c07810100051400e050350f210300c3c1400241042c0a02da514070208503c4582002560300510701c1d121f819559004041041e00a500400709040c04210a4004600001d400d42500001091844015418014191258130740f0444401506486102c0c22520030344000c4485041c2c4122070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 244220998 1250 244219748 244219751
    0x5040330050702060c18060c120304060507090506030c03061f030c0221091504030b100e0f070e0105130819290117011806050a110702060a0503100308030109 69
    0xc880d88544015104014903403401c5400c06410001c2d08200310007a40c19050321141e42e0203940d002040442c00710311a48032215110300c1a1000c40170441c0b40f40004511580c4074000c180720070384400c0c0c3c056030000ca01c0d0103805c1d880101030001030345c18500c00004d10b034080d00040c14901c0d00d900d071080704103c41c0801c0c00080c0000b51107801400106404002004070910801280303045000d00c110706240341e0042a001031703c200c080c8081c2000d030385100c0080d100910f800980c0710409050801e90007050a8507485208890123800300010500c40c85040c0d502c3c415481c0740c498050000d0103500441d41a408400c40038282503101201150303441003006045807030380742c001d025403240d0f605080c0b1300c002454042d01089044045903400c90442d100c265890b0440b0130364240070703108000b003d0380c1c90b000d0312201d00c814040ea980c3c170303582c00c3c248185a048240500e503407400401c15820386400d4845a440780f44800ba4004004101d4050518800c9004650201c1c400500d1701800da05c030b958200e115802a84048a0035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 244222248 1250 244220998 244221077
    0xc04181506030c1205040b090f030c100903091a133804080a0f11061e0d02070b0708040201110a020a03080f0408030301060c0b010e0f180f1002070c050409020d06050403 74
    0x145041100327502d9000d01100542c02e10301400c58040c5d484180d40f9920171002e03100c4920707408050241c9081c1025010650180c2203c400d01c1a6201d20f5403c4080d12484e08210000002441900c0c0340507046e1481000319868020251000600440500540540c2010008020018040100b1300014056500c10a06110240e8039400c01080c0081d0600d00fa5204100400592080c2a841c0d5406522038247d1103065460313580d05071a006c02402940300140c45400140c3c01c02010503400300b0b0962080d8400d8803200400c604a1100c036076108109a002508402c1e075002c1071010400c0d081c090400710b43c000c403500749031988511920341107400c280e0007a004260000001d608000b005ca405074007400c14513003007003510328010040c1e8002c600090080405405030900b80001124180492240010003204943c80c0e0b42c0d084001000039488214284d40b40f4003420000300d0689842d01900a14a4004052003001620345c4c4800000f000050021020300900740d4071801900030b010f034201c0b4011400070541d0440d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 244223498 1250 244222248 244222261
    0x5030108070b0f1b1005011d0109020406091a07060204060f17070905100e030111070201120506091807050409151808030705070303060803030c04181506030c1205040b 73
    0x1403281e140c12503030000354148240446000319800b81c0d0601d4009500042032140d80d110000d043c512050b4121259070300342400420b05030542c1842400c6400d9820605070203a9032a00c8240c103c0c055801450300042080300c040210800f00300364504021000b0000b20300d8000c640e0fa60340300700c0c6d10a5001c0d401280c40f51480000864002d5007004512041e200b04000c00d03d4440760003001c8880314051580324144201c100b0210903c1107001441001c4040c00070440d024140003d59a10b40252900324001503480303004805404150140c04d010780806800144039488071a15000c4881095481c0c0c60b940c4916a0001080d42c0c480c0128000a03008649407020b80c44540c1420082e81e00c22101402007840720809100095a01c07412298024039030710f01680c13100d0369454120040c003515172081806110110500c05040760001c01401210700c82840d000043c13016030018810384518083c405821462200700b049401d00a0708070281c00701291030842141c0d12250b5140003250b1080d2426140c8500c81030801c0003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 244224748 1250 244223498 244223503
    0xb030319080f0a0c050a05031312210204031e0201121503020f0f0109050603100320040e0a03050306060307031407020a050d020703150c030e030a0c0507050a05030a24020a05030108 79
    0x400003840b0301c3c04c2c804607480c44400703041c5109080c1c5510421100100061105800707400a00009038814588618030198074030003000e24450789640004d00400c0302c80241d4070300e040d00c00c039400c403607000003000422015207194103017055411000341d0600c4410035800c0000110b41c4201c2180c2c8800d0400d8042e10742c1140140b001030821785010710f00880c00c202c8100550303178002003600200c68044684560306c0c1d843c42072031170031282e881e40014143c1130141200b900d000383e4280300710210301f020fa408110250000b0881903480d00c00e158058085841080811828280100115880740325418007040c8511032201260740d080c1c0c1120b03040300607000500072604012081c01160195803551000701300050554036000061914480741e031207055502c0c070081d04072500940085010403000416252110300130341000c0e03c1c401942c24100e0350b0713002d61140414240303484588070080c0c4001400500442109681d03110500010070201001c8143c2d0b60484102600c1d01d000420754110503554594580d4900340d102032 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 244225998 1250 244224748 244224751
    0xc0a1b0f090207150906020c0d050909090a02061207050417030714010e100e2d01050c07120e0114300610140f0f250c090b030319080f 59
    0xe4502c0c010058500400e13841c3d030301080c141045400c0018980120720307201c0d0080c465407500098a000d0f070b61095202541007030150000c80d506643c1c0120543d43c40304601c2c0c5510240304000d510203018080c01700a00c1070700700c00950021441c1003044c9807a490b00c0d000f5201c000d402c22200324070341c000500007040040000c1c80d04284182e50000340f007120034441c03c0075115864a0104051580e440c10003c5d58040d00304a040f0308480113102d0000600e2155500c0c9410150090310300c2d06079130800d80800e81144280d8120340045401002d0514400b1250341c089031681c036001b030030340e04001918113440c0a4400c00340c001c01c0000c400c2492007030041c00c564158204050002c800c3d007065003c401c20010300e91a00541c482c0d1080c03a030718100842495148425525000c0e440310f000ca4a034000c070322079039030b99007200090a05503410000309402198160a06004407030480d002444810b04503c2009003400c2ca0700071004011009054034106114441076040d12005114032000281181c0d00344142c2d80440c0e0400c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 244227248 1250 244225998 244226009
    0x406090c12060b180612011b0906110715051b060115020106050405010317031012030309020f04051b0c03040902070c05040506011e0f05070f06050a1a0f04020c0a1b0f 73
    0x4c40300c0b0503403902e1990762110000c00e0240100391700b00520301400c1003035203c8009146016648188090b02c0301c00140329000d180681c0002c550b10060b190798071280015070070121560403183c09800380030884116003940100500d4151034000b008403a038441030502000307010302030450034003181800d6990000d00351085d0394041c5008628240040c800308441001c44024400910032156494880720a0916000d40590142500b52000c402c0d00d4109585a00900e050a008440075800403848100300400c07074178107070b8881c2940c004140708003c10500480103050144958401c0c1c9003042c3c0d0750002c0c030040c0d911403c0d00304c0707001038040014031151600b841703960b412110070320b40b00302c05010b001340c45901c00c2075500321001400340c10b08900c0b540c00d11480444d440954801c1c5402c003901e009103464405044140d481c800b1803410a2241003000031242c01200500d4001058404c3c070203440c1092000039400070701100c035213008070110140491400001204400d10121111001610b041581210320754183c101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 244228498 1250 244227248 244227259
    0xc062a0d03050c0a02060f0603150403020309040501090203131202190c0312020a2d150e010e19080702040906050412030b03010b0a060810030b1008100c090e0406090c12060b 76
    0x20b0012141c0d002450351f03401a00366602480035141c41700043d00d0a500d0703410304040300500e14204000c056004c800b9200880040d01c1c28031040c0d0305d0b01402e5099000c1103403e100d052052644410205040c240346140489030341c015100c005002450310010000d0f09002561030306031107007041040040f419000301c1502098400340c070f12424941e8526144841c01181c0c250b040c0313522803114803910001c0c2d1013840d00c6a80400150329441c50404200050504000100419440c003411054005404950071890040c40f840c1099190301a5490b80819000558160303001a61038500344001415482014055802109403500100f4809001000d0301c20140300075010340d0400d500c440082d2035409261040d41e0041c104010b0039600e0026070602d00c0240e40c80a043d0407013020070f01103254040c6880034240d070098419954040602840002500c003514408400602c0c02c000401481501c000074903086440780c0c801246202d09500c95103071802c22900001c5204040300800410042c0d03e20800d0013420050781e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 244229748 1250 244228498 244228507
    0x1033b0105010f0605070507050604060809160e011703090d030306081006180e21181c0b07110f1b0906030a02010e01021609060806010f03050c062a0d03050c 69
    0x5580c0c03e03142c1d841c412403051210224452041210520050020345006032416440b540e40d040700800090040d13400001c640246407102591200403150141950800010320583e43d29111603015001d03054080d1002c1c9010501500d02640c0d682d524800703689001ea03802040703207814000440d00349400b01890811181c60844204455140740300c0007101050050400101e039080c800b283c03410304050b4a10311f0f81c402040c8085011070151070001c0e145221088010302e02940f1608280040300000410400c00c3d00308a4040c580090b141241c1d05604c501140303440d8205461010b503003483e00d68960780089541d003000c2d401c80741c170100d5800e1000315480d003201c0700b60450803c0030110351100240c4101a04101880d103d900c1903034020491101040c0300003c904000641d18600341004107a50b00030000c03c0e001d074200004010298108010640c0e4002018184c0f880c0c0c140104030081d400001d50b02201090440e481c0074100041400180340c40c42800a04844c0713540c07180c001c1c116200200315050b890420f10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 244230998 1250 244229748 244229759
    0x1060f060f0815041104050d0605090714130203040f05101415011e0306180b031506090a051902070b07020d0201110901050d3e0918040201033b010501 66
    0xc402000c43d043c16900014000c500e401d0a00c0741d4816508066006610016800204102c1d40c0c86176100300662010307100380b00d23105c00017005050580385000c0d0340210180b03210031003007070b40b5401103400500c82c61205001c2e460301d0f070300d250911070ba000c10000081d58032555040490307100e80200d42d2141940504020b00c2500301c0010f040d1013000780150070308031901084000814020360101c0f02800d40f42101d4038040c0320498124000d488603040c0c85020380039408810351001c0001061a003d2034000346980d42c0e50b5a0f4025a00c000c1400800400c40c5101c950012109118984001e00c2554007802720318106103400c00c00039103000428111401168507011058142c0180842507400c584424a04686e881c07001091307002c05812042d400e42d0000e501c07604103120400e040041c1581941542680790480c210b180780f50510750140f801d8044c0c000030404100300d050312100d40407070340c46881410006400840400016501c6070a102d4001c04e100140046a80c00b4903d004800303042fa20600080c400e960409 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 244232248 1250 244230998 244231021
    0x9050a0303081005090a09060b030c0f060315100f0e0a0320040912020a0c170316140a03020c03151504021317070f15090e09010e01060f060f08 63
    0x80c40094100040800454040b015101805005200080c0071140c0350924404400003400840340c100c4915290607040c03507032824007140910100c0d0f4014601c000b06640401800070a0344000c20307031f45141100746028141541c5032030301131080c04c1e4143d6a46040060102c400360020016001c018811108080c00b0000501c02c52030070002c060b0002c40000f180480d6802040c090408690000d101000305000c014042c0d60000f9089440f40c002c0d450b074101c203640c504c0c101500c107002c035540040c01d0308100100c06101d009003007442031541c0300c0c00c0e0483d0f801d05082c0b0340c6824031030320240440041e00441c002107140c1c40c0410542c1c1941c10f80c00040441820311880c0c0c134030440a6031034040e001d1500495030160702000750222000802c2e4540480700b0072115000540d8980410f4041c030402880e9100c0c0104641109a6071300402604940714001c41c603040004038040703040300602042582d03488940215202400307010303590042900c0764202c0307030a03800e00402600d041422981181045500d90401c402d02801 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 244233498 1250 244232248 244232269
    0x903090904061503240b010c150c05090909150a140604090309050303030406020c010606140304151e02070204141e06011412150118031106210f01060905 67
    0x2000081c840028040103c0303544495440a041c00301c0f21880001c2c40c5910721080c00540c1c2080104210b0713080b6210054511901c1804080c100e0b0003c4c2c1c0492680c5400707136000402c404420b0804505161100d00066105241125411040d4000000300c480c2044c0c00d54085410a210550610000d60002c01d02c0311001d00040496100719140d0503002c05040c014084070000d001c000c0e050f00c2c0d59140605244004e075000380c901031000d40c0781183c005146d40c828200011060446d2010341e181d9212030720b901340910543c0c01002940c2d50744142e00c031149141d0010760310354820403110168441741a8010030046501580c01c40c0c071452034240c02c122015030000030004100c04a0f40740d030705c12921090012188810300e01d0340d004004e0000109050b400b2250042d01d03116010001022014181450044a0701900007040390107403084044240006060403140300b00d01c0d20b010349040e04100703c00b1140d145400d02c4c071843d04c60b00000701d07041c010361901e04104507015054500341030b01e84c075145c0303c0482d004454 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 244234748 1250 244233498 244233503
    0xc0905091c030b040605030d0c06020f220807050316090b190906050a1406160809031b1309050706050d09060501090b0901120b0f0a022b0e060f060402071401090809090903090904 78
    0x24001800300c106c8601500383c0e00dd0b442d80d40603074400c40c0b2083e1242c2c080149a40540f4070288528500054145800152900c0000d034000c00401c15a180a1840014140d61182036510060014400c00c1c0d80c0107180105000f0000c603c00406c5491620040c442c2c1c2c21402d030400c800c0300b400c03541c088584e40c9901045503007072149810b19255a030551b0516800900802d00011b5050044d444199042d207605000c9801401d400c6800701655011036005004543c030b14800180aa0031140040100c140284080c4c40b561001040c0424440c510ba9282c0089420980158002e43d55880710240075042803c0103502401c000130100003061281d40341c003809820020589008501e0b010700051207a107103901070710070045070303e481080c08842080d448002030341d0820750501003520b445000a0f4a0700e001945a00841381d007840c0604a480d51703001d01001c0e50040344250b500380d0010240780400d60003485210107003805102d0302ca81b102d49802c2007110b007404c09041406550700c28407000110780c0d42c0d61a40364100350b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 244235998 1250 244234748 244234751
    0x509030c1801060f410409020301061706030a020118050603041202010b1014181e040b06071112030f04080c0307150e1e0406060e1206040c0905091c030b040605030d0c06 74
    0x445d680a28000c0182e16886140c01c3e280400c0c00a503440d00d40c0c0245060b12110780300c074070703050122404505120710b0480d00750380d06030701c83e10203030000d03501884002c009600c0c81800000540d488a0205003564016281224140261205003400350360a1103100d10014045401e04480b13006030400800c40fa41e1307824007058140e40003804103503620240701c03000e042100103019101d0422207184460018410800764034010f0307081210500706450b0040807104142d500110398022000c1910602000100c0d6034090402480200510386034080300074050001040c25070014a031091070903040c14103200040d0f01c581034085400c0406061250003d82c5c0b0076410030181c5052900c481c0303031001d6420990f0782184c3c450f0002e20b0302c2c4011400c3c1e035000001c400a810183c0c0c901d10180040740c58507660320000c840151943e000d90b141408916400c1e04100c0d0851030207001c9548000341503025032040c0d11600c4054004c29610f46064844e41007a008800003040b0440281c00c5a10846002404a0446020051109 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 244237248 1250 244235998 244236077
    0xf300d0e06040e07020109020d1b0906050d03050f07020d1b050402041802070609020a08070311030c0906010c110907090303080901110301060f020114040f050f0303070507030509030c1801060f 84
    0x20352017540107103c40c7d500280b01c00c0c41c01140b0300b050007281000401014282c07048078000f042003041c9001b681e08868010705003280034000d6860480e002d4000c1000601590350030041000075981e600f001e1041c141c003a40a41d5080038105003880d440007500c0e800f0a002d01d0050208210b41804e40c28500c0e0280f06240000d0798800480c64884000c000c84070000303502c000c10103400f280d030240015000050303d20640d0a007c002d07100c0c1080641da200d60002c2264020486800609154403805801003011312aa0a82c0441e6080c10001114007101300c80100004011500030024503500524403030300014900020003c82c0c0401c00b03003c003144814041ca070248071022031100f00b194030075071103405074a06e41c0c400c40000f0304280c900880ca07014090001c5d40c5a22603082000b00580c004000c803805003440fa00c4062402c000c550f002e560a405c200b1900b50b150040c0e07490054a0b889010540b521902c0c1e20301c06520b02d604103035010f400d80c00707505200b208000000c0380000d4902c1e100d060544c0040200b4044602d107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 244238498 1250 244237248 244237261
    0x19051e01090614160809040b011704020f06041701090b07031407080c0705030d0203011a0f0406180512010510090b150c1c020102070309140f0f300d0e06040e 69
    0x2500c1902180314443e0090704c03075107060100e01405802c3c0540d04480500c1b90010310001140c07d10180030001201003111808a401441e000d1940481c15002601c002c0c101913403407482240101000c0800c0320641d4590b03d80c0c108001c06480c0d11035001205040410450041d00701d000d0070080010a040203000d40100400c1005054000361071056500c0380480365102c000c13a050002030b410a1148480340c02e9248411810440024151003001c00c2000b1010705040ca0040201e5075003201c04200b0105d08240031000c10a0345070384202d004d001c440f140022800342014000c0321440368040c3d0160b502c0d10f183c08408103940d511400e044016140103810035481d0b040c0c1d2081e450030000c50000c1d4000c5100754543d40c041440d01034016051040c003a40350b20300d00030744d603d5900040d07401c40620340b40d1001a030800000d4520b40044003014000e006811144010b01c0c3c080144401c0c00410000a030043c030421402146207010410382c031500590340f800c5d03c26801d002010610500950080c10440c0c1d44403000690f2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 244239748 1250 244238498 244238537
    0x3030e0913150e030a180b19030203060a090f091106130302130e06040506160207050f280914011239120b06030610090905070519051e010906 62
    0x90015010503603903117901c0400042c01d10102c44d8050740d154088070b0f60000341b11070b0b18026103240701c00c042d141c02e41260301000c04074000d60005104640c40485c03d007022510010034800d21102a85484000418083d58106400016440222607100d1441080b0310020a4007480031a0200d0341c1c1520949010600c2140120241c6840d9031141400c0c8503460801080c084000340aa0044540350b00c008a0022400000c985032240d038010150090b604640b20149410040d50303440303158900c1e04d03100b06118051043d02460040303030380c0b0108070f00c0e40340c1c15a03d442c49040144240140611303501e44124001c140c0ea8501c080b00300d03160144211400c101400120010031405001da240c1000480b04e801352100851074109012080c20f0707440300809000907400781800200039000720b50710849110711a2821540201809054400703e03910b010342000018030b070b1104180c07100d11102c0d90560452040c10903052200307100c085030903548034110b80d05c01170400d40d800286420903600340340b40422040000724840700 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 244240998 1250 244239748 244239761
    0x9010e030f0d1b0201051b030402151605060702030318011808090d060e010c0e0d03091e0503030d02071419060c031407020705041505091603061a0403030e091315 71
    0x1010f0342c3c0120000b20303035040d44000c2c0301e44032001d203070340c02c1c1404182c41021500040720002d4004001e00d0702001c1028400c80a820300944440c14a6081040c5903035180c1442400d40d07460025a00120070f128886a00c103603484580e0300c404008100c0b80d06800c40d9a44071107040c003070140035510300040c03000c000d8842c4500c6e40c90b4a5005001130140000060b4103500a00b28405603c0000b0170142d0010240e14288100040b82c2c1e07010360f5404d90b400d007000b00b054010342c10119408031540e14141c0c00642c9440520241c5468440b1080042c0c46241d030b414040e0603013001c4080d40fa445e4100390386d10a0842480d804030100c40360040d4000500c01102131082e0006d061501c1d00c401c030a40410101b00500b03600199000c00d40b001500c0900180d0440d0100d0340e82c10905015082d4441e08140024200068580d04c00302281458640441d2269540c02a0009080c0d002130403000b00d080041d0070303c285070308148a8003400b202516496001d14001340501d03249070310604c004107100d64030f00c0c00f900040d9007038001c1c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 244242248 1250 244240998 244241021
    0x120809030a030c02090a020307020a0b0a022209060603020c0d2105040b0402190b0901180e010803040f060807050409051902030109060602070b0c030405010c05100c03021209010e030f0d 81
    0x30350710364180d03040103402080c10410032071041170303000001603110b5024002d807030049403076070001c0c6030088081c0c0d0340d10346000c002030650342d00c01e500307111203228031a2000f8a0034200402c0c09208542c14140981c00c1c0c2602c81036005101458010003a01445410001e5403648a01d050324201501b0310040c801380e980c0100004c0b40c02e0070f05003460148400e01140403081d90041d0320071904000040e00c4d5801882c2090014803607400e003404144500c802c3d40d40912050301c9000540c20340e5009180d191540140c058900b80c1110500b0390021600340030781d11945440c4009404a07040800403440c00b084014a20700c641c1c0504000d031500d1300045184490840300820100096840170f41d1a9a15003001c0d9006284911900c001403050030310000322984072004656228200e03001440c0f416003804015540305414010480717561180420002c0112036030300c506c60007035a40382d802603510b0001e01c0c0305001041c0c01515804103031740b4100d100304158000201311001035800041c030030344504284c414000100801c0e00031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 244243498 1250 244242248 244242253
    0x2120318060a0201060b0f040503150606042904031a07020f070504110903120a0207060302030123030724030c0521130203070f0503060f10050105091c0b0709150912080903 75
    0x500a58038400c805070068989c140c2c219002c00c600a0700c040d0181005454441e00b0a07000c11003030044040d403881620643c00d0080c0311442900810b80c1e000c041c0e50140c0c1c81500c408194200304400d0021000f891504a038262000301041c0900481090b10f41c3c00b80d20489100d2940c846510212010345020340c1d241400050903582c1290181c1c3c081080c030b6000d0621440140518000840e0050103842a04c1c10b848451310041300d41c0c07842007030102d030031009540c0c1c40740d15201d5180001440801030240b03800e03c0d04101c9154020510880c0c004d02030340d01d940c0000c0f040c40400d000ca203d4115004a03039820b01154034050840507258081d4022465100c508080c0d00750250980115092030f04594150469100350304554095803070071125550038006485240120080743e100f04419840340024110b82c9030014900b03101e40100c100020030200c0346503002ca403405c544000b0000310b583c0101c00c0f10b00800c074100382004584400030000704551000d0141c01480352100300c001c0103001d042401d40d095140701404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 244244604 1106 244243498 244243507
    0x140f090f09011b0507110612190b0405040b060d030e030f030301030b0901050105030d030509031204060f0b0906131d0f06092506120b031902120318060a0201060b 71
    0xc3c0b055114500340900c0c6070f030411688c140c41c05186000000c220f100320043c102816200c441c51014896440d180800011030a10390450b42d1005086410305103100c000c0c074066409401029009406224594682600000000040d41a603002c1c1c84205c000d60380e0f0440c9a400d0325024080d01c0d0b050b4000044400c211402904002e03008a1510183ca050000e103400b032243d445070880d01030301e0350b0740c0b0703000b203500070a40511030380d000d44409030f81320700f804e03d003e002198007454000e10a00c03400d80c0c0d880703180100f0f50a41c070303500816541c00d005550443c0e803404031a030758890080e10300c5201c03400b807500810341044801070100e0515107554000040240752980030780d503220012400e010f03079680b5503c030b28405940c203009513a099000000740c0710040406005005100b1101481c0003095402004001e03003500b03003140d6640d4001c104a840d01e0740c0350041002203000d044a035005000e031000204 = true := by decide +kernel

theorem cover : BRFrame.Cov 244064748 244244604 := by
  have h0 := BRFrame.cov_init 244064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 244064748 ≤ n) (h2 : n < 244244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
