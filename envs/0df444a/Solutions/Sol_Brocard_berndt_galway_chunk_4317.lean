-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4317
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:14:04.099193+00:00
-- url     : https://prove2.me/submissions/74c38b91-04dd-47ea-a5d8-c8dc12897836

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 776258992 ≤ n < 776438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 776260242 1250 776258992 776259019
    0x130c08010608060a060504092f0d0b04120201051b0c07080604030504080634031d03130b0304081b0c031603050105070801030506070e1f020d08010f0e0c0906070b0403030c200714 78
    0x2b090300e031001891140b440a0014505800e00780303440031750300282c1811641800c0030f0002e18003001d030603940105003d014880d610314005100c00c3c60443c080d40084118001e100400051540280182c4222880c803420381c7c0c003640d128018456010f080e40d90612103906800350f4064442e414107030060600c1190300300080c00208048041031207c8502000f90015840090a01901c2c420801410000d100442c0303405e041d81019640c4c40010301490f000303804681d11610209012a600704900e844041c1c2c040e090b1019400740300004c2d0003000c00e6010545e00d540c00c10010517841442141c3c3c140c1240e4114001e024a911402802c507040c5411821890344001c03200400f921000006500b07050605079600100225400c01801402070303803050784a68040c04181404020350a00c3c1101964820707640703007130591741e5a03201c8d002440c240103031100a89034400d010100001c158040e4020140e080c50780c0c54980184000c4040031190021002a0050a4010a1003000821001c811200da00c02008101c64240c5070f0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 776261492 1250 776260242 776260249
    0xc0705030903061504180503030a090c030b04060c0914010c08130915080d080433090303060503072304020a0e030a080a080705040509130c08010608060a060504092f 72
    0xc10744010352484104d0755022607503e441d00c0b035a88584000910207031a0100c54a42588a000042a4649035070312a5103010400c050b404038080550b500440500c5541440c0c102280200342c0d0003164070115411043c0800d43c1910180c00c0c80b40310707005a5507016400500d030790304030441e0002010f45281c3c200441011a1808040c090680054804e41d07007009c3c124a480c140074500300c681c0f2035003c14800580c0070720002c60306d441c522000d0740b881202483c0c06401c0700343e040205440c1d0075940705c080d545400c450804041c0d154128200300c0384100c0132200380700d0300d40d8400c07a0f64200103504103c031100302010395000390505070046d00d8260790704d0800c00340064603d0003007820704100389400c0b20790070800a0514001a0407140341030300612945841410300d41010b000c941203500141014a02c00c699403298810000301840360303000f505442009024042e42d030380c01d49070744007001d58403090b0f001d013802c102290b241000d1081c0c40b80c0e039400400580306040100c0c1c1d800015000350b0498201455400c07108000d0380c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 776262742 1250 776261492 776261503
    0xc010f090b1602131401032603040302061e10060e03030d06060f093501110a0c02031e060c030406142e050109090e010e070303020f100509060c0705030903 68
    0x60402c20282d680c035000e0310401c0000010390320402d1200d45888504002071060000036070659522990302c03614290a0445003090034a450741c0109120400800c1004155003c01c005024180040a10f001c06c0c00f0507924a903009421510b403202415100d0040040310700c00c60303440c0c140040280039a4503050485000c0019118160440c001140c040e0460417007140e030101a4000902c05070b1a01c00c070b84230040003c07030080420365100c0940400c0d0b0310005003407201d00394020f030300c0c482c1c14000941e03a402207108041c04820003034200b41d02c28081c1441008442d42c0c0701100ba204041464080d003196035540c013507011240c00180c4240c0d6000c0d515007828000c0c29031403007171314010310b11056030210000c800413010098800486010800c50800e003000c10032a60040b8044081d1100c0c4440850300403007172f6500e0381c018000036155074958031540c48c001042c56004105051000d082c0002da50700c800141c0c0d00601554070a803281c030740d40e50001c000242c2010600014001a61040c8244ca00d4003c030500003d1510 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 776263992 1250 776262742 776262757
    0x12090a03211b031d0307080d09062a0909050f07110f0f21120402040c21020306010806011d10090e18010605120712020d050a320c010f090b 61
    0x6590b4019001901980b8400d604d00c4d00c1d0f951000b0b501e03101c0d203591429102c0c016050010941621040310900700302d81500407081c803515020380e01892800061803a200c003210280b030503011030280da07000b040314010390081d60f1180c04500042e0155440c0d206c4202e0340c0000750000030820b80070310071400315401d0050003880e00c084503090003000403031505034155000042c9000034510b111000c0041641907040c0c1204264031680441d40060041d200d002d0540b54280e001c2c46295280442c0580d0411988096024501038a8281e0b104d0003a5070303400005440d81040807911404039940c0320010480c80c5814856110513017040d1521080555039404400710382c0c3c5c01901c00441c1c1a40c681400040c905092042c54010030084504040c2c0c1d18100c8681c54a84080380a8140401e42001d4030000b5500c3d210000031880d50700100300c0300f41ca046418112404168206608100c1c146200606000c0440d503c0f104c188401036800790030105c44540054641300e80e00c810100c10310000c1c25000520b08414009403042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 776265242 1250 776263992 776263997
    0x5131e23010501031e0302060a0b0a08010608011b170c0315040219080a061d1e100f1406250203010c110106090c30020703030212090a03211b 62
    0x50b5411464004071005810805c1d070030341c02c10307696168003080d0300044c6203404c0311416400149080d50000450581903550704071210035030a1a60005e0f090038150700903000464985096182108481c1c4110323543d5418829941080c40007102203480f00380b00c900215000707984200d882850049940104080e60030029514411840c020040039443d0341050100d0790291405004004207800c0910070340341c5680d8110900d000309100e00c00120035401c84e00c4619a1003d805e030803c4180d1515850010001c00ca9018914190703001d5000002c05410030b00b40422540c034000d00d11820702d801148030059404aa00a4001c5444032501100168500384916039880320a1395802800301d01202c942400d407441079114a0072189000300c0607248680c010701c40c40c0b481c0c0120b048d480c0100302e86c40010090440c00c0c024000254400582c900c101030701a030090500305000c0d15603158603660001c41c5916082941d901a02040302d622510101c110500010011aa00010700052081407400a05c03c400104d41d0341201 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 776266492 1250 776265242 776265251
    0x240a060c1b0e0a2304050304260604141b03060a1a120105060114120408030c07050312010302101805060c01020f04090e070e1005011d040c030f05131e2301 68
    0x290000a042400720510200401003070781415500d00f5601e10591144001610242704090201c0e110a034a5145160718807003122290f0134030b41000020200300840044031442110303001c02d107600018120070b0300389200070050030640d075800b2160780c00382000014484209071541c1d480c038042d5482440c1a20800c50301d03400010180340601c0050840e20480b51421140300c03050090850500d0b46140c00e99006600641054403605c880012282c1c5000d411402000740c00f0101c1d2078040700320709a040e603048a00803561a03102c1328658109840100000c0784071070740da20800d40140a80d0074004005c01c20300c2c0c1098001450700e0784451001c40c0c0c0340c1240d006203440e640c035130115102c0300b0010400c0314003605025010070404c1c01c0070140c000281a407403082c41c0c1800414840c80c9048024000b0031242d004002c0c0040c03240c80701e0744100400414000b038800c0d0b07035175117004003142403100c003034010000c1d084d408100c0c41e12451070114407000c500325900044a18030440e0884103603028140e2441d0a280c0280e400105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 776267742 1250 776266492 776266511
    0x703030c2706080a020f300103030e1804081801050c15150406060203190c020411090111120f0f040b070f1e020607080c15240a060c1b0e0a 61
    0x384043c10180135004054014001c1034070300c20080c0c040740d40e000101c0042d110645031a22600071a40700400e03c0300d400e55400b5000105164002c6012444a00b04440c85001440700c8022003100300419036004d01071a809201400c919250059410070103201418154200102040c13403501d003c0070304a5144c560005181400b02c0240383c0c6401943c090400c1342c09010090400b0002580c0e4085d204c3d40303400c1044200c0c08040d400f03020750324032000160003074401d01218027628604420b550000b02c0c04e03400916800e0310300c00c420001003554021005c94007000c1d0320b490310440d038070b1060341c020100100d01200200701c000390340342001d001089228032400f0401c135507001701d0404400d0902000b8241c00d5807680d1807152030060f501c12040390341e155488440f0f00d032180c203c030348071a2521102c0c016403c940709071079082c400c80c014a01031070601c1c500c126000740180e841000600080305482c1c0300b1000400c0d143e072181300c0001c40c1c0b44852521504100502c81c2055910940e507241000d0503162403c01542d80c02880 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 776268992 1250 776267742 776267747
    0xb160f20060c0a2c1003020415050a120615050a210605030d26090a020901320f01031e06060309021e010801170a021314060a0b0703030c2706 62
    0x802e008004401c032404c003840c1c0040c2130800008140c22642c0300e000c000c100c8828072402075066030013412500300c055501609421024005502c11040c4201050482d040c1b9607030078060307010b03c40a40b078130a00c03200c00f030034110141514190490103c81e01441084070f400700d48a4621452100c55298007080400e0341d81c0707041e00f81400c020303c402c4440b04100340307400b0800651110002c843c0720715940c0c08105a90f5500c140c082070038010141d500030752244004000142080d0507945010ba08e441c4d034413030000c2d0540c2841c00b00700c0c0c40c0f81c007050840e0030024a0802d05050344c002d40c49585c1480704010814003c2c0c072035010040490390190485004259255000d80940c00c00d0b0280c1c1d043c90070181740058031004410006001403805204203001152a600d15400d00c0e0303400d105d5012899030190075400001d5601c050348000e0b260706600b00e52054035810003d50303980303802c508002c1111240d0b6411864012070740c404901070200c0c02c84840c240801807056620103440008000d040062004d400f0003000c0c1000d100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 776270242 1250 776268992 776269007
    0x2b060e06011a04060503070c02010306120528050601120204060e0702070f060806060304170c0703060b090903120a0b0d0f080a02010606021f1a0a0806040b160f20060c0a 74
    0x81982440d0a000138450580c004040340d4001d00c4d1030800065440c401d1004070060083d50f000340034a41000185101000703000a101c4481c00704024044000404800c8401d200301e000c01e03806000c55106e040100500c40d60700c0e56080300203001400101d851529203000f500d1005080d180c850040c0c0c0300030800c02c0080c1c0f00300e43c04c0d00500340038508403030701d400d01d4030000e440b40c00003800180108983c164407298050f00d07401100c04140c800702c1914405507490400000900c0da4990171405030785800c0004098101c08000c07501c080398112248aa2522540e82c89001402c0e40480990000b110a10038404955009080c011061040700310715507400300d880000b4203499043d07010b0030941d40a503941c0d01e044248020700101460b18040300141410035a550031408004201c4902d8009414500101d0002408507170188214000c4d2002c174070f0794807460054445506120b08901c0056045261181d0042c440c2c000182990030b100c0091580910044421b070402c4c00550300c6070b00000000450801490300440c0c1d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 776271492 1250 776270242 776270279
    0x10e0906060901050934021f0c02190501090c0b09030c0307030332040821030618091507120c020304081002031b0d020310142b060e0601 60
    0x105007281e54500404a2441800034005002150ba01402c407010039001c00146c00c15985000b04820710031006844c040c0d1030f803000d207801d0108002c0d549007900e18619180103c890905c16540206451003101d4400840d50612000450b680c0d501e42050308041518400c10304017a003840c0c06250380c1e88801c40101464400c4960304280a0b40100204201007074100382001c91458030403150351035003031001e1511403d08250480814000e0f102080105040c0300001d41070690707001842d54907403000c0942d11500800c3c0012600103900209000344581c2440030380da1900d401c00c03400e000b26107802841a02c0c80191550885075a0b0004056900f5034442281501074510250b041340040e601c0d0030305000015450b060304c1c001520010350004040344c0c0410710700ca080d498000c64000390540f50441c55018401941c0305981100d03a60240103070200c1c080b104210740d240300a2004000070003910a61405020b43d5031404007819104146a41000c04a400c5004840c140c00c03065005e03024035810a509044020720145 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 776272742 1250 776271492 776271499
    0x30b011403070206060405130b040201142802010525140421020307090908250c06050307080609070c0609050c0604170601060e0306011a13063204051512010e090606 72
    0x2390b2031004542032000d001c1d04260203107030041000d03440c40401e9000707101c5d043c001c242d601e07121002c20f1a030110030032221036044d090754020720840e1140168004400030051807400c4c841c1c0c00d0007030114001c0c01819071010907040d04c0184c1c1d0426030380da00240b00558030801c3d0b65182d0480b06210504503e000e100000103005282000c111144c159250315030640902c822500017079080044002018000322103040185900280d20214980c40c0d82000f481d40d00292114008034240e6808510f192402900340b03407003000195503c0340441403030748a200140c40d161400b07607032601490346800180d86440740100301404081100340385440040702c00721f04e0400140c0c018401c210449a40c50581c1e82c008c202c80d030440c0c20140d02440d038a80407081c068801d119030300f0850358619400c54000b07407054100140745020152001540b006004080d10500085503504a00303460400411041c0500c1c40c0106841d4141c0702d5441119040045451154207100002e070400b0501c0100602044034200040100c80d81c4003a064 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 776273992 1250 776272742 776272771
    0xa090612020d08041703130f0605090405040c050301020d1508030306150f0f1303020f0a050907110304031401052205030a034205030f0706030b011403070206060405 72
    0x4009080403051240c0002e100304624190308052021400659002d401c01e0100d103205a0145e42c080383d0b5035071001c03043c0041141c140310005000c800d4003690001f10f40342500d890346448a00c40400c0020440201304441c0508035000114244d1000d00c041c09401a0340d450020311585500d4030b0100c440b16035444160f0950080040042e02d80f0f5040280d0846d1007885003041c1c070741c3c1a01d01e81c0002c0b4050070041d214000e001203035142c0d20800700300210003205c0c002d031000c640c2c1e514620188540304c200b074000c0a07040720002d0042083d141c4240c03601c2461006a80559041545070358070340260030103000300b10080e03039110000d008604010b800c0071608603140309214000f2210940d10242c0300c0c01190721800c1415500e00000142c81d041001011390b88006000618460b484248689075140c00428a2890291025800704040c140024030607103c0c0c0c0120010308001e868138404501418620000a0411140000c850381c51100000654003d104603005000289425014401150401002c031003000001c1c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 776275242 1250 776273992 776273999
    0xc0105010b030907170a260f0301090c0807020d111908130e0702070308030a140412031d07140109030b010b042c130611040b0318010522021305090109020a0906 70
    0x1641c21b901d00d5002c90780301d400740e8546800c4485000305042e20000d05800161512402c0201c00c0114141d070b1001a04002001810343d003200c0681c400c580344409680310f007070b0000040d406810200302080c152421aa6081c2e20314001d0801046801030407100c1090104a081246040802140c050f200c0055207040070300c0d003420002e56585491001400743c0c80b0020100f40c101e05280c00400302c0191416200400b0308091a011004000003003200300080d2624070f4048981484902c50b48030020580010315456080c2410552100c81c10b00c940d505002d5081d03c000005078461a1040c000c00c0030354200d9480f02c3c500b40b02c2c90340c50400c80b0300c82211481040701104d284c43e881b88043c1d80041c1c5a10703540b0340f644070516029004015003042c80f441c0502c042030001d0039001d0362004601c203000400e0b04401d41d103004c220b00c0f0b080e10802d50f9010364900c04200c11080846405100c028024001012000000031200c01c56044501c1a164016940d4580c04c240040d814501d00c894010308954204200d003915 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 776276492 1250 776275242 776275289
    0x306070e03070e070e1e0a0e0709090f0f05090303040b10030803010b0c0f07090606030f020315101803120e010915031a150306090114090f0601050c0105010b030907 72
    0xa00481c02d220180001080b132180c810700c4058060080502040402d41c6926119009504c0661000740306014031440800d10451103c5628021001d640b80c80d51440d00f0409940c000e80070209103132038200d070764004030040300ca41401180c0c001c1c11118080c6a5034109400c00f040035500043c2802c0b11407035036480410002c0c00309000c903411540b040c0c504d40c0d00d442c00039081c642001c0c1d040d82c811065104400011800712216400f1904440c00340d1000c01402488280c0001a80030444107442c0203541091072140d2800e0205008003190070514045142804d042c0400c0c074046415002501d8403010702000d01c40c0d19030803600c25211b5005c01d0a0403100c0307910b856000b12103c44260b21304801c01d502c40b4030444c2048002501142c1c1940c0c0100130802640c0b501c3c1d2100e1498201315a038a00c901910000010011100ca00a40300307010003605c2c4203202d6980030001c280b000d40140205040280400c689200200b082c46014082c100c4180240e0b83d9080c080c07185e03454a141c070f401c6041049003410405110b580c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 776277742 1250 776276492 776276503
    0x2904060809060a050f04150b2d0108090d0e03030f160308091615021f050702120f0f090109080118170a1d060f04082a010203070f06020c100b0306070e03 67
    0x503070000c1901c0f001c0d141c01f4040800307850b140b0419908003101a50b0180301c0041602c540c10b408820001a14040369070400440e00b4040c15520300030307181c10841210411600c40c016089000d0009002c4900d092001c1100c4155a841280946040384509071501c040550250308690040c08480060001902072030318a42164540d00c51910800500c50b00008203d0082c4082056600706c002e020500d0080c3c91250b03409404111350400040c013039082401110060704003641d1070440320032354032411303c1703141c070140c03d215803140e09401e041c4024818001003481090181c01c40c0f00c1859809d500c548680d900d00f60040b5404249041d4400034203020030807075154030142640c403400e1070740d0750581a00411800724109129461200540840009010903801400200c0501c02c0c1d03200720940c2e2158840107021504000368031113041c01a002082240c4c04100880100c242c010b000740001440c0600541540e8540480401d5500780540c4451602020f840e0500445134400d16a041c01b05a218a00001a4a69 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 776278992 1250 776277742 776277751
    0x2a030c032d0e0a0c0f051212030c091c0203010b01030b1005030a1410062c06071b230306010501080f070c0611071b0602072904060809060a050f 63
    0x511401c82801d00e141003500652030340342000d01a01e29040090038006070f940c115000c2d611743c03003280c02030005044c140050181140401314003d0101c0c42d46008011000d5400640000c5a00005101070a40c645d11040d0030448000d040705007081d105501d1040c942507801d441074041c10b1604c2c1c0840c00b01036440354107640b121103003035150240d0340c0d55508400c04024003480b0314041c4000b102100300001c4980e4201030314151113241c1c580d40301c0c00310403190251284265050038081d10004181200b0f89041ca800644201c62158035000140c0120030301c2c4001f844d80c6644100341d0480c011054458081e05200701d00311300310042d000b0703003910340c14400041d2220764054140d03030340544504006200c02c0c0c801d40e800c0c007a00d82d12050a2084100405d89160140c02140d0151504000384416000007220200000b04440700740c0c004e8800145411181d484003200c02c0200004000100c20180780c00741d20b540100090a0300707403285884c03418100003c5141c084011304041c15180317072030148210001c0d43c40890340d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 776280242 1250 776278992 776279051
    0x50c0a030c051201030b06011e020a0209091e0106050109170a0b04030c0c06031e0504020d02121e0105010f1a0301052707020607030f0b150304062a030c03 68
    0x40070303807101c000c40c2e1a1041034a14000000303800300100412100141080c0a588242c1c4c0f00181000c0d0030140500a4105070211800341e4802051400103060503000300380d0084a440564903108064440c03d9204421585241d601c4c0c0d640e294244410768026413400003802101c003819400d100108540340da40c1e080e002025080d1f80415001030101446194030302c001c01c0c0c1c4201815074865445c1c6024014000140380401744001d03003001031502d4103251240c40d111301d0f00140001402c0c4400d030203000841400c400d01401c14058601021a034410007024241c54281c1240005125031405a29510051080d003191038003203641040d444050380c00c0801e072815030300f0032591022110a610100b038144404502100c0101c0c82680801c0219500410307658403034841510140180754400b01880e0496040c0c0d907441e540484001c000c00712410082c0d001c3c60b401889844001011480440594420410144c1e02d407100400030801c508140d80c140114200d06c41c08d41030500c82412041c2d030741213840d40324003664080c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 776281492 1250 776280242 776280251
    0x60b04050a091a0312090307050402090d0f05030f180f120615130f02030a0b0306060604030f02040207020d1b090501050f0d020f0616050105010f0b0f0706091a1504050c0a03 76
    0x54a00c80f298008840700c0040458541c00d00f42c241200480d000583c4481c0300380620440000d143c102402103c0c0030080062800070340d15a175680b050b1406170700100640b201e1000b400b4200c4002084402010300c09481040c195500c03181104010381600e142c2d89541c000d20a0011031148a01d000030165003000502e0b40d607003408221880440c17803200500704015600390a10341c21007040d14059000354016200310609104041c0c0c5002815581c0405a59541d0070860410040020620030241420020320052000d861302203070b60005021016140d0007500d071b0103420303c50340303040404a503a5000208060101031015600d0321000078810f05480c1519800703000da4071821803c560b1182d01c2803001c200d0003031119403212207a42c2d0b00440c81c0101e4104481c190300e01800410b4401d0811500d03000c452400c545030b494900071014800343d9410009040b1a44c5403120400c4001903242034560f864020b0821540b01a89403224100c0c42000c4041040e41c0158502020712190303900c00001c0313030444a0a0700b004203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 776282742 1250 776281492 776281511
    0x40303080c070204090b01090b010e0604060f0c0b01170d0e0108010303081e0705090f010315120f06020d021c0b0a0e091516111603150e1b0301060b04050a09 69
    0x52442a400c000354013034501811101080080642d05041c0c41c00010b0030000c0308241c0300192400006800e045502000600c001c120980c8241c6000c10440110314103c40301880b2955001c01d100c80a0300a0140080d00e600d14804841c0704106056041d0024278000203810380080020700b00f4034040c0000380810030302e800000c2c0e02811044000340b048641c50320b0030f60305243c880402400c6406c40000c00384030f4a2290a54a82c40d84070b4020900710703003d45d020403031030b02d80b8010300e00c1d0150942d142c04640f006880c1440101141c0d0520240c8600380c490800540e9401072200d2550001d01c00804042e51146404020354480e11072402c00e41c1620f030003003290842074484050b02d13403070642c09554074108010301c0c10401850300c1c10003c4000e080d004544501025140c25a0388036250492198042158001c8000030004181844000303420303602c1c00580041e600e01040c5d210f900f080790307401c002c450a1702180b001d041030f401d09200c0d070300040015050203820141810005000044540f040444140c0c50b401c244 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 776283992 1250 776282742 776282761
    0x191a0f09030a0507030b07020307050715180b0a090b0708091011160e151c0206070b0106031d011e270b0106020d03060b0910020c04050c180f0604030308 67
    0x1120308050050441da149105490203070b54031030342804103c4080c02c01202207618540004261088036a0007806801c80a081240c200304412103000b010003004038622441d0b1094543c2035100b405450060950307030b52041c441602400c001402d91003050f12100402612000c071b60b00c80103a5041c0142107951944410350800c1c1100c142c40c207409507050500a0407006603440002e440c03240115007080c0212006a641c6c10b40410000b40000a05a0418104102501e505107a1460481703c3ca10090400d402d1071802e07140c00304c0c840001d07000304010a41d140c160201c1c1c00002c44200c90403440d010002e010142001e840c110380703283e002e400346c0e24035900c608150905542d200030725000e20703181102e10110351203103060a10b1015020710130000903000746030709954241e110307000e92015160042543ca1500c1c400f1810320080141414030441140601b09603a03241c0c0d5114090580102c0f00e0031079032034881d01c00701100c482000e000203403540f1070500b070000441144c84100a03a8102e98050500000b1681e568240c2c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 776285242 1250 776283992 776283997
    0x3140304141006030311010b09010510030e07060504180c020c06131802070b0f010303080c0f1e0c1b091518040803040b010b090a03110a170c191a0f 65
    0x9421082c05a41d100c00342102a9038010401c0382d000c0c1d03480c2017110241c4c0280b21f08032900150000d40005018006200c10300b018180410850010325001480e802c001c0c0c4858104903035a080800091070010741046040c107400c00045d0200c1c031855042006000d900783c0a946c1d401d664a00c1c0d1f01800010036040e2040c800c020074132001b0551950344918441342ca098110080d80030f014121400745400c00032030010300d80714800b1070599070300d903c42104a48848105007101d030040303811750340340a60402125060b80754403115401041c809040b1152203150a82e18582800e9030078801e00d089203a641c1030035000d40e9401c03441d540c10400608803508001070340c00105c0c03203071200c196a104529100c6130034001040003a500852050740030b004840c0c89d998071603603880403521500da00140d001d0f00c40c420a0012400038a059884500c005081e1a0410b40c1c50190f90784610342c041c00c968030350308200501c40711403c01203041003840411030602d00c2610700301050318404c5040e9800c4998504404500000c02c103c0d180304 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 776286492 1250 776285242 776285273
    0xf0504080703060906050c0c03030601080411041d07320d050d0e0f011704120219080d0c030509070e22150e0d020c091504022d040303140304 62
    0x741c52100d074590819602819030110200c1d9131902c0c0c000050324628a03803090720005806000510f195440da0001110561009041500c61003513125040c0003d81c5c80313124003407042e0305107402205c4240002801e00d0620015030b00100341c03065100141d2000700c8014118003001008500b19110302e02001c00130a80c0e0003d00c0300c008200d403254a01190803d03401c82261004001c0449040905440003001100e00c207031103410109401d4104400b040010304000710b002581d00580c41103600be25079a001c00009080f500505444000000a0b100700901060103007201c00c000d981420b1080342031504650ba9685003520030088051204c801050301040400c4000940c1d00c2a40c900d022706007510b0400e10a03400d0010720f540c141f07510f851500b510410001c40c1c42c002c044040c6e00501501c3d0462810300c200038400818090b040e0a45840203142550343d4805440d8440741c191a40154002040f0703000030f20540030310301c1a4400740c1030100700000b0740e006a04084264144441580342c0d201c82c54400c2591603200d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 776287742 1250 776286492 776286509
    0xd0302190c082506060f120602070f02090a0c09080a050706050c0f0714040e0105150411041502060106090f081f02270319110616060e1507050c0d0f0504 67
    0xb6280c3c0c0700030980c6180c2d41600c42c000c0004100b4a40d940c1c460125144e02886490002003840e000038003c542c50f85d001d0300d4190300900f405146c00d00070764001408403d003150102000c5583d410119075180d4449109005002603000902d0074148070740f00c0f03966440162042c40204540041c0b4a0500d150501603100d44501d52012140e5443d183d580385006807000040190107240741041c1c1110780081401194020703851000c2224580c4070300d0080c407015092500b11410409420440060806031000da15031808003c0d0340501699410040d0080215100341c3c0b111031116508101840017075004a074942c0d2004221501c5441d1055044000c07029003d504c490041ca490043e100741d540c030510441505a40408505a403500d04024488480c00030b0b101201801285070502401031505109000300000c040541c1c0c8401c03038a07080d076500b40c00d89035640c5048880c3d13005414000f80e030a844002c1d00341c1042a0713003841420102c4804050b030b07131900d1000b141000c01103001c0071642664003d40846010709110b1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 776288992 1250 776287742 776287777
    0xc0b07031107060221030f01090f0902060d020705010e07031502160503030405060403081305100f09240f02070b060f0a0b0a0315051807030902040b10030b01020d0302190c08 76
    0x1104044d4985d84001c5c1205c1052900540c541146494101228071410108140030303070603400c1075982c6000f80407090381d8007525683e448000025a8441001e0840440d0040780540e403071903207250850a641000442440f1540703c800c1c2400011184207074008080d030700040050f02c0340c000711900c55090031a0704010380280000030074001130000114249114038007035281c15007952500181c0b8030080d5448000a421074108424405200c102030304140c08440541d200812010034179200c2a0600300902c1c0c005491440c0035150402c0c0440074094002001c100081c2182040c0950701e42910345107008029621503046205039852030382e101d200f0300020700b800700300c9940c846002c20005401468401c0700482d82d40248140010700d03260a03000e1000009685171400c020b81c0f00e00e00160041c03c85940200e074060b0b10b4804808154640480c42c143c000869600802c0c4005030400180c08e0001310002030042600421028040b48450012149907000310706c1c10403810305080c102640c075801200110340c07298565 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 776290242 1250 776288992 776288999
    0x603020a030b0916060507062a020307060f0513060203090106031e020a05030a051e030712030b0f0103141504090b0a051b0301150f020f070e010f120c0b07031107 71
    0x1128400b48280c3c0c03c5411240c10121240c3c14003c0e540c82d62140d00c0028104100600001e00e05800041c10b50502c0c80c4500d40b01c820341c0c20242d0501c001c4070442d0300141e00200e00340c07050000c5400307440b43c0d039441381c0c0701040f590070070302d06401c03400c1c1841d40007901d6690000080b40c01010254000c4c002541c12103600032075044000401c0514010501c4142d202d0503107103d01080c640f801189442c0100d50040c0149018052000724030030f81007480e200c009080c0010701440003c00c40c0d41c42d0242d24816540e80014141c88032400300800b9039003000d0b105042514011040c16071944408141e6000100050058a680341e1640014094038000d04010301501c0e01ca401d0103401495904407078094409454824178401101c040031600d4082449203003140703c08049001040d500a070b01175000e22100e441034032903a003c55045c07680307000300c0342d446154010044030040211000242c02e0f0009040480d0f5070800074980303612943c40c250043c0c010070708200341c00a024401c00d0301525803c140e40d076440040d10009541c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 776291492 1250 776290242 776290253
    0x60c0509090a0f0b0f101b0b0702030a0f020d020d050f160b1803070803040308041a27010c0509040b040209030d0f021b45010f0b070309180603020a03 66
    0xf1024080011941001e00206503498601000e01410601400f240810000d4142c1140c010806140ca0483c07403a401c4009808940404a1144144050b070010740d903981c22800c00401038200384a240c41107400c4080384c0104290301003500155194289070076611240101c2c41540d00e40b040060300c106c1907000d041181c08014036800c3c2c003072043c2e000003014114040041641303601d80c41a0311009010314070810005000074011051150000c2c0100700e06400580c1d02d100075581004103403140742052200700d14003180311000707807201c01420900c50006d104440f644403001d480c41c041e03440f2040c0700342d840304540001a1602e0381034900300c45008041301c14410b620040942600c0807074003824018092014146044184082c1107142d0640180c412601002c05000c0c0070f1840801c0b54400701070600740b142601000c2550300601a098041040104a552500750307460160030890740f110100380303424010b07040802d42240b9010101c80c42c40700301342c52103101d8491f01d000030200740c3c00081d032080401001006010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 776292742 1250 776291492 776291501
    0x100e0a1506170c030f0109240902040f050a05060f1e060d0908030709120b010510200c1309050607200303190b040603020307170a0507060512070503060303030103060c0509090a 77
    0x260140d170700140810141600340d80400360042c05207103040c049014100804000c0c440e208003d81c06c00660390700c043e80080c0c185d509004d0224412600e074800c2c8030302e20342181f01e00ca030080c4003120901d002100e0400840c4ea095501c58100059040700d8503601c0c20354603000212100445148002c006c816643d1a0920f415002540c00c0c10000b2541107020555990b8030010324121504802e2034000c5a10f080300b0000380c00c03c0003141c802000743da4080c4400c1070312000c4207020240c0d00300c0f0140003d84c2c03e50b828800b5000010322a004054107108600011500c0465065000b52441c82d04200c0025a054140c20440c0841c1046196220000070402d284c1e103806082444045140303401c0c4946c44403c003c01064038400e01005e54150403c50003002040c600e210102050400003064421189240e03c1d100c0c10a1400d0780010003185000503524462041400b009910004906086040d800d041c40030070b50724001400005c1c1459541d1850006260140c0142e5400e0b4000070a044414545a003481001c0c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 776293992 1250 776292742 776292763
    0x807080601030e120a11100b13090501090c0b190311032215050117010b031222140324070e01050d0507020c0111010b0904170c03030109090203100e0a150617 69
    0x1c0c0909400d00c91f24180038010941c8488000b482188030222035013070200104440c0d542103e141d0b41c0c0d0401c5800080398010700c0d40007012900915901c03400a80e01101400310f051607110201813401e052040d000184805903a0001049811a100302c1080348004100010107107002c1e0a28403030041c491400e2000d600620b040e9002500b01e91801f243c00c181c92801e90b0001c1c44103a0741604150403480546080c1d40240540704241d1400020300440b080c2941038840b00313500311506600c00c00c100b441d41c0d82410400d10800b03525140810031014040783e00f115516101500a03c2000801104002181c0c03242082e1078120070303181410081e5050040c0041c0d901c2d0440850640400d23801c00745000300e07101c107124582c07150300003900d40e540554881d03440740036005141c407103051007500034028161100c0080015501800c0c8185000500d61142e0040520f4425111100007480e400d08070440d5280c0400700d0f8032100c2c582d00200c040c0d0a0107a81c0000030190026821103507000507403400f94800d4075400550300101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 776295242 1250 776293992 776294027
    0x50c16030303181208060307051201050a0c09081506010c080c0f070602030c100b030106030812010311030303101205070e100f0b031b07140601060c02100807080601030e120a 76
    0xb41c1c3e1010520a550301c401d40c01c00b501d12009840d8040219028001e4540d11201c0102510075140e12000042d08507482c0e01610382c800d1b9500d41c2088811101d500c10005200d50f20f0405456951901e000182c0c1d5111000c544c009680000c4c0100f4101c3c0d00400b0001e403096404001191074070034410034941c3d2500c81c115000c40e43d111b1140002050741c00030049403a104465000351500c5000c0d8000030000c0d05c80d1340545509507607070b91000004901054040c01c1e00a600314a00307a0194510300b40304900d04101d01c0641d200e03401c10020b002c06842c41e660301004503486064004c0041c0042e00705503007007810f282d0094294070868020843c003204922007200550700010400e0084a4980e044000d2a000c2115078207050120140b00883d6200002c0207004658070800c04500d90031200302e111801d200c1d0aa201101041090000204600e003074440103540241c01e140040c807a10781030000810424000d400141459a1402c0000e05268203000ca0308801222000c00d654034200c8404c020f0101d651509512034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 776296492 1250 776295242 776295251
    0x30109050412031406040c12091a070e1c0f060f020a1803170306060d020a051323130b030604050a03231c0605190e0606040315020a050c16030303 64
    0x303805029125a04145a2182d01c0611999403a01400002c1c141f040140c03040c0410b2440135103940d18a40120b41c2528415065007401000710042040428000307420300c0103006000036001c08035240c0701e04042d044551641c00e020440d9207410842d440350726840003c0c0ca07080c14100c1d11442d5804980042c088041d02d940d400380c07030800b103c0b07078945496618080100664a0204004654005d4401450304620028551031924100b00d001c01c089030301c03100001010840204181c140c25481110090082401c00241c0405c5140c82041c500c00d8400750401a00c80c2410324201e9250300283e50207412070701406412200da03418103081c4555540032810b4110002258100c68203a0034000030078698000303c01c5401c4508184000381d2001c141d641030344400300c9075a43e9600c001402c0c0ea0b0044901c001e1454074107188051400c260a20482c3c400041400b4000c3c0420001007001404d200703103102c0c0300001c2500050303c80b4401c280880b602d1080e6115003210703100fa1420320701d11a1040010100f201d203e80c50800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 776297742 1250 776296492 776296523
    0x10c09050f0618121906051b071a0a021611040615020303040f05032b0516022a040203041a09010b0609010305070903050d021608120f07080f0301090504 67
    0x50a407080d143e0408103245500c2c907005041c10640c1e8000440040d5106856a0420008040d681010200c4050315015101c1080c0400450708182d000881096171061178030700456034840c144524409001c552081c4504c90016540545650581e0780e44000302d180080310014038104440c2d40c41412159520a07490001d002a000180715840110003c80c2c1d00510f00f0f55031683c032210560010404243c800d804200702420300c0d40072000e005000700005d03c0114100e60a03440488045690080004058100a00541c1c41c2c0c0e503000121110f1000d504030f40d047d1036480c070f4182d04551050b1178023101e07003046c0040b040c8020804542003240c0c5a0725205100c02c1d580d80c411000a0a1300d82c07400d165500901d04000311503080d442600300c3c551105a0303060840c12030b075982d40e51a1500c1414503000005070001161042c0c1f05007001c2c402d40040400500030214024207151004240c80341000f181c40d4070720f00140c03203010054400c0a0b128003c105c280015102e60b51112903202500044408403000c010400e2000d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 776298992 1250 776297742 776297749
    0x2131e020c0d1b02180a140426120703050402030f0a0803070c2103020a0e010e0325150c110303031e070c050604081201060f1e03020c010c09050f 64
    0x1035141220210060008140342c0c04141c805400100c40c0c1d8010003a42c071183c0002d81c072000c41c3ca41e8001c2440191161074540030030080c0487e445c0340302c2c0c070103820600740c2070001050000c030b042d074211000b040d56680c40352003141c000e100300e01c12000c3d00606807207040104420140c0545c4440d2042c0d00990030340310b1503001c401e01d503910b41224000c0140518001d001040b030107031080218401c20791041d146034030700c01441c072002e4128a400881a10020707400040501380c2e40c0e071192071000910780a003040d10030031007914006502d490004038401c400c4000da0f03030003202c115030031540c0c9001080040070846441c0002e400007000703907460050036560300c9000e01c049001401c00104691107001005d004440c0c40d1500c1e103104042d14005400d803420000b90303e5285010072401d2100c1800740f03208084050b510100e000b17602e4200c1105a100e5001e011100c0300865140760410b4500683c02c150858281c80789141e80d506070001e0042c140c90514a6103007401d084a002d8111125506455045445000c2d209080040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 776300242 1250 776298992 776298997
    0x6010303050307030207021216050f0d020901050405100e090705011e212702090a060e2a030702030a030f0e0c09040807020603090615030c0603060d030c02131e02 71
    0x34000307981040000d5806100b035001d001107a1000703018a0812444142c46807030904003540b0000350480c840410007461520101031400100c0903a20210703202c03500d400044004405100f080d00594486000404500f0700702c0c602c20142a043e5401752003800c02c00b604e40d41d00c089a004d0b842c007044400d80c14409001002c211040d502107285e03520743c0c02d80710740e000e8002c2d480500c00004a00984414a61096030210ba21901c40403010711409507042440b401002a4554040c00022403545000340a1002d6050401d8969000103487e000390080042c11030f04842c0d020580c1054082c00700c000c410310004a5000c8020810031800f030780d00b842101088011003084501c009008100b9070301160301c1c510325080260500d50301500402e9003070b0a02c3c5d81c0c1d4012845980c000c403a00880f5400010030016444a4503601006501e0706078014114800d4a0b0302003042444064520b034032031008110100201032003840918403096015100300e1123004c5010a000c05098200015007103003d14200a2100a445209 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 776301492 1250 776300242 776300249
    0x603140f070510050702240a1704020901030f140d08070305090d12150906030302031902061506071509030f0212030c0301060509363301021f0b120601 66
    0x401c2c142c1e43c078015400d0f18035038803a62040340c0041401071140c01c0c5141d818155000300350b1124050759503002e40c23000144075a000d022141c1d841c0d076050041c40096101c2d12041030549a12160381d043d420f4103424821412692441000300502c20340740d2000c002c0c0e130300200c0180580074039101884076440c0c0500c1e050311003110080100008080344100d0403200380031382003404000c0100c50400c3c0e60035111420f14081e00e411b50010740159000186018440d07010200440d0301c00c099101a00381030820418140818020942c0c0394407a00300450440180000103000c400010302c4050104030f82e10880c0b801501d0326583c264080b02500035600c200408481103403c0b64420001c0500385441c40c0e081200a48490300100fa22580100b9078120251040c01c000c1c45441c82c403002d011455061110b0043c80d195090f07002400e901a8004591022074070181b01c0c10089495034180c0e9200c03145002c6080101c3c54141004440001150010703490039a4808030b90198084540503a50040da2031811202e41c0d991740400e21 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 776302742 1250 776301492 776301499
    0x71d060702010e2107080c1203031501030207062c0106120b040609060b0909070f0f054b030c10270f0303080a1b05180a0302040603140f0705 62
    0xa82c0f4026032602c04408040310000007074040744018080000c0e07240c11781e140c1000b4407a1740140c070008045d2404120201c3c0700120380c00154a1032910100307038200b0140004605046c1900443c4034020001e4075040703100048030724000c0d5406451a01100703902e0701d41079a01407400c1d5107043c00c081004101c0507000c180040d0894060310f2240c072190f540c10000c040e99102503503820350311052082541c1d101c107002405040010020411281048450301c03c00b0700b03652003550005c20b000d600b0406900c440088581a2070010560011101c1043c01c60100760403180d0110b5a8548040e1003410142040c004c80b15991402d03000c480026000303c0a202c0501b5241c02450085001c401c4120f800540c180d0500006610760500050860350303d40c144c00c1c041880e40c004a01060f540d8040048421691050b281d501482101107044585444070180c06841054810500240c0c69154100240c0b42c2da45203100071035018008000b45592410171041000c5521005485400b90200b200c20f12030000642c0c106448004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 776303992 1250 776302742 776302757
    0x30a090e060d0503071a07031401030f2a0e1005060403020607060b0303030f0106080916170f0d0512010e0c1c18210201051506130905071d06070201 65
    0x6a600809001001e0303541c0003614501c094005101400908001841011590100c642c01d80c1c9015403100000c005e48101450921540c6409961000d4076045980160454009040c1800d01c920711440100c1c91a5080070f4000c81c4039540c2d481010980100c8504a40078560768590966031160703040c4621540d580240e09100c24405860040014058588521300c005490401540424119041164682d21428903400108041608070307603034540c8419044e000d4092140754041400802c1d04501402a1800c000140d80c442c526041007603601d03201e8004102c4c1c03504421048011325035840220714542501c080400050002c4040008030b0282c420b40d90001d0900500301ca184602440c1c01024075441c44d21828070b222600d442c82a4401d40c240201340e01101009404100943c441181c40f04808582c076150800041c240a048400a0854201d41c2c02c2c5e80d070032a8554003c1e10140d941c00c2a0300305482c103801c0c0121290010410707450003400c0b4500c46502042001080003500a4400180c00320740f11 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 776305242 1250 776303992 776303999
    0x709021207050903030d1503060f020712050c010b0d050d031817031504140f090307030503040b0601051e0c010b0d0803070309150c0c0b06030102071a0c19051308030a09 74
    0x10b2015010340c00024040342d0803c1d114a1b030081c141d5103000d00500381614019070a0061043c14010303c406a202c180c030551410149988105500741407054410401401140d4032030b10320420f40141a81035001400f600c0195040e040242d2500030110f00c2202003031602d160a05180104040003500b11b8006640c0c140c1c01d02180d0381040a81e000034881c1010003040d10a00342150788611803203a402003806080c00c0680742100b90889007200142003550a54021f20480001950041c200c2c1e60180d07100b1809011521003c0061701d4134001d86400e8441c5140754140720010384d1003030000d0141144c05100a000c40c00421043c402c14030700206000d02040010000911040c0c040c4d000305407502d214122500103240002054011209405d8118002400c28050001444040d03080c440c2c02c1802200210716007031032a500e46058407001c0c8034140311200303440006800f618041050f00c01903140070b020400540c00e200001031082c2c2c0b000c42462092a21401d011910f50000016905e00c0b400700d41b07400100508 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 776306492 1250 776305242 776305247
    0x7050f30011d01180c0915050a060513051e154e07050c0c10050a14032505070803130b10260106030c09060f081504080a020a050a0b090709021207 64
    0x108005204000c7c844c0c10800200b540302c2500311001010315070360f00e6845802e0380e40302000030602c030b40c40584500440039a0306150280000321003c840c00885124902c40c44044204107240078120104401004031940441641101854003925034540300c0003101c081c4546400300c00542540e1907001030001c0d10400948410300800c010180200c101048652401100e0001925000a5130303003000001d90119007240c01c150009000300542d614094150f003940340c842e40300580700441c0c00c00000e1280e0410311000c2414005c90447e800c0a400100d1241d07245460070384548841490b00040364007110341c00000d0a00b09403802d240341a10741e810060114010600080b40140ad1904170a200c0c42d5a6550000000350412000c14000c0a9091002c40c01d1071170000301e40e19910f45540907401e1a0845a071051300e54044100c41540079a00c0f11107076031601c01900d4202d10f0500d04200c01030061042414800c1404000d41d142403003500060100d40350030352200703100b2041e4043c0c5880c1d82c4051382810b0203c1c10560 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 776307742 1250 776306492 776306501
    0x1e0305191a0a060f060504030f020402030c071707030917060403030c020f1506040507110a0201141b010b031014040f020409080f07020307050f30011d01180c09 70
    0x40c00341c441a100c101d694080c10a004805031036400300c1c07030b9503580c08114014040340300d400140342a08005080a1075925122290800c200740244525070000008549a48590542e44442d4000d4003080c0c5402c0003100c0702030542c3c0542c1064020414800c0300040c240b502401984643c0c6d200805402d95072510f40c0c054020b0104a0710201c158001d160ba5001405002c2050b1400742c0380c8503e10141600b40356050108550340900002c080013510740b81c01c0101240024401c83ea164280f900a03201e8419a0004019004410000700100b001e8031201200309070540000134119411002c0d590f8010542002500300c58985080c09400d4001034005800b1441044440c2000313800584041140d081c590703115449030380140710034490000c0201d40c00c0d05600b000c020f404040d040030fa90000c1e6180ca4880010ba00c822000e4020708414008800000e145081111800b504200324000340f06070310308200e6910750405450180b0a003580703840d03810174500245e841d2200420390001d40b00701c403131401c000c81c220142 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 776308992 1250 776307742 776307793
    0xa05130f110c010501050a08030a081902070c0306091a060a09020711120a030206010f0608060d03030e0d031e060609060f0201021303030804120306060203030a0e15040305041e0305 79
    0x125030300d55940a14071503950082104210704000011a58100402c1000050480c4c0050764650300070301c0341d144400e070040903440e004490b6100c00103104041c400c4142c042c0c82811001464544c015a0000802c45035406c1104801e00c1904051103241510318109840744007120666030090036010f040009803070550082541300e000340c4059a55420200204200c005501884620341d40540000018554140310090140100580e084410f034640400200000c401901c5941300b00c5c5940c4418041501980c0008200b441031800d0b5041014403600c058000e01d40c1084110a4540310601c45a600c103c910401c401d40c1c0c1e054542401440c11b03d00112122480080154103641d820424032285030183c840c914019413195a0b41682d1b49400c3c80c2c124401041092a10b09260500c1d80902070181c000c42980d50050303402500280c16440c4520082c6030130000070035006c1c17503181003051106141c0c0c0000103009880354031199884400312102030b4501c64034a4440139019400204150045004280d031680d1031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 776310242 1250 776308992 776309021
    0x121506041d0f10051521091005090309040c200615012d090902030c09040e0a02280b0c03180d050a0201080c04050907030c0801050a05030322120303020c0c0a0513 71
    0x900205850119400e114100c01d16103840106080002c203450070803023010384a0f1880801e00c03403801c12200c040e50702e0060a460300e10554960480488642c070030104001500314080702d100c00c0e540c81e07210a0f034641d0016644001c600071a0a03840e00703954010404042841c0b42808400c490101e490850112140c001440030300700001164001001c000070300146000d0000100b815a0b5000300808200813101d42c41c044940d070303411070820007001d40d49460230107034503039510a23201d80540006030424400d5442c603004106104c8020819800c0d100000003d004604c1a21800300c00400c800f10070000c94181c1d56400074940c0c0d0100c1c010b40015482015160740103003000c000383d0305041e1608005035480e6011a00d4000080d5220011010181d00801e01d50041409481515603d8107001c0400d4403881a03809803070711907070198403282c030094a0703c8a400003003505e2a9058028580c40c54001c010350302c22031400c1118828161984024502640b2200403900003c0c40c0c2504203071003030b034890090038890114111 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 776311492 1250 776310242 776310247
    0xc03020312131202010e0114090c010c0501020d06090902120f031b01090609030203072a06050f09030708061009151e15170c04050105121506041d0f100515 68
    0x48243d0395a110001e0150008900f00d40c01c2c030145801c5590718204505c80b1440b03c82403008212000c0362880d6070610a01c1c22208042c01802e0480c064404c844030508020710b06a80014110440c1d405885890f108441c0c2c40c4003654003008003644c0d02c0080010070075980040242c503040700c03140c0d4030b2424000d00038800803d081c001502c40d08100e8030110700580141e08009004401c0188404800305200d19505840b41d0004041d03922040500c2603004140510000061001815111360b060741c001c000000d04a81c1e10b940c50310f000c41c0d169842616940c95840c114200400d100340c0134000c01c86800c01520070318804d01c2c80c1c080704095810350380a0407149070030f81040120348000a030002d41d801c642c10b900c6104038502c0800300180c416030024075a0303d030210240070a102c01e030f034010f003100c803521460400c4201540722a0350642c85140c1c0310a015900c44000a030005011220340c2c500404c5000c100c40c2004195a03072030643d0f81c0000c084070300900141d400c0e14184050b203041103800000c1d60320460703540d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 776312742 1250 776311492 776311531
    0x7080a0807110a06020405091006090612090b13020108090d080705280f11030315091e040f030f110a0201031e0203040f11062106010527040501060c03020312 69
    0x40c100008040b01365612034001400340283d0504003d41030b080740c40541f00180081c940b840c01480c5241c64094002082003100c0303034036503550164008001c0603400c03111940c0300e82401c0070721688100601e941203012070ba104c00082c1200e4000314a02981e0b01d0142c407000c642d81d41c0c40400322507943c0038a08000e04503110050090301200c1c9000b0000c2010054ac82d2500c8241049601500072110090008400d900802c200b01c4449401c2e4041c00412030700381d40c00c60140e11842e100082080030040616855004501000f041c840d0032510804071902988548880c81180e120884101040c0107610003550720203004600194400e50260b861100d000222860130307800200742c00181e0344161000d03294150359030100c00900600c0800011120421907045103400007915130074558002c40200394074001001c00004841c0c2e40240e048450b00e20f01d4429040104440074082c3c40010624505640150319050012813403502807100341d440c584c2c1640045042808005906112080043c0007180807101481610f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 776313992 1250 776312742 776312777
    0x120b0601111009030e0402210c04150806190324020405030f1f060509150301180f140d0c08220807170105071d04060e09030405041107080a0807 63
    0x503041e02c0c4200c0104000c411404e00030300304560480624480e0340704200b0304101400000b4502d0003c0c0a11103901d01c55900c0d501006840d010740d82c8404920400c100c800c08140303a11480051007140201c0d0600200c51a008d600c1c1c181184601005040c1818400000540c42a24515052801c0b004c0303005860a92581c0109042050344c5c100b2414039400b60a864030a00c4180e40d13170341c4040c0700a24003085024545000564007040192151a4124180b0f400c90000d450a4210b01c0c0481c2c1010300d1032081800e14640150107881c04402520300b450100148503401d80701081500080138643d644882e009015110124180c0c007a5a44500e00ca4201d01c2d41c00d40128080c50203c000c1040c0030251441c949040200302e0350020b94135115020764584410040c0c8150043e18442d6141d00012002c0200150705000c0b07801080e058005800b951820303410800801c400000410559000380e900340304e08c1d82407061681407802039083c000d14000d805d10040c071000d44101d41c010b900c1191442d010b100e011203808032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 776315242 1250 776313992 776314003
    0x2203020f060d0b031905010e012c2404021003150b09030316050c0306010618030b0915010311010e0108040213020c070e04030201061d060d170f12100f120b060111 71
    0x145c0e94040810044000303001007886403c01c41e41c1007500a1100d00d016283c008200c00148072280820306000e0540d4500c018200aa940c1101110048192501103411290301010049400b01e20030748500c4c5144590510a0099090801249540c50002401e0804444090300510203103a0503100520501c8240402100c402014074045c0c405049515221030a050408905801c408207010318040845000005110014201d80d001402d104064584461880c02c0521260800117000d009000100510207076120051603400240c0f01c2c0b9004462200066880140407600658800700070740e501ea4006c24160000c0281c150b40b8070a40301b0441c1ca8202d440b046080c01d80701a0f00503035454101340000c1031a04c1ea9181e0703000100071800143e2030100009043d0040603030000700110840d0000e02004150748c0709803004c0d8203c0c0240c440d01d840340c509a07281160b508540b4107003103c485034030003e9a401c04500ea4003c1c2c4400c1407842407844860340fa00420030b80c0c00b030722203030400104410605000d40c05018 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 776316492 1250 776315242 776315263
    0x1030e01091a060108090f030409180609030e01090f0609090b030a08071a01090212190b060406030f0b060301030f0b091623091e090a05122203020f060d0b03 69
    0x41c2d030305a0304100e00010016500242001c1e0a03506c460400303805910000250b0b02251100100810b40e004440f40b400d04842a14000130500360801e000d0404054000301584500c28003039071030000c01583c1b1000b50743c141149128031804034540e0311040c0174060854000c0f40d0b1140c0d000c0c3c22500d42034021b0342c5101c1c035035000b803800360b54081c00c1c10000e88404511001c1540144040f18056080c8840d8694000c3d01d2440502902100c4200d01c2c0d9181c00c00700c40390451003000c00000d14043e2521360701c1d6006400340840891140c24245020408002894903005a0341a2500045400904803065480351030146020704402d210340b1812100d800311240500b41600601481100c0a10000d1444850380121680128182c030071400d480070407100c4280e02c111801e00e01088421f40c1e1154445003840c078145840090082c14902458001070078082252006081c091080c880203244440854110300341d1040a000095004480105208803407610310090035807100e403600c1c0014001207a400003480c241c0c04c1da2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 776317742 1250 776316492 776316533
    0x240702060705060c210103031418031b0102190f0f06060f090f0c02063106090305120906040503030408180d0b06040f02030c07020d172a030a0e01030e0109 68
    0x200e0f0128003520344104040424002100071003541142d50140412740d0b14038418080240104040c00d0f0003902d580030842100002d4243ca5141c54007405018411841140050140c0b01d0040d01c6069030711405402c1d01c81c142c0020000c0451360441d520460702c94a01c04083c1c511648829000c1880b1a0b10381c40a0024800040001b03505503600703050006650301c005c0460155001001000440702401481c03219002000d074160404480b85042002c0740c20b01c80030302a20b941d261084504c00c05070440028004102488404020380c0e9a20211580d603c004942c000c1c0141c20920101d000150742402034162841b04040000c4801c0296020402c14402c640302a604092100c00b0701c002c5051920401c1c480f60b80c400415032a40c034040356082524800d15a0080c06006c0320b03125282400224241e10100641d4691416a14000b0020030810302c0c501403882d000c469414003d10308030b11400811034440f0309032919208c0e440c0b02c09400547c001e10242c0c140044c15500c81c0044d400099160040000000401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 776318992 1250 776317742 776317747
    0x1050a21030f2d2703031b060906020705070b0301080d050a091d0703050a1a2b0c0303080601110a03110f0d030617120d05040c03061107020f240702060705060c 70
    0xf000003c009607070228291020881d0b0650111285000c01c40f28800d894040c00c00c003403015039852001500160184010781900d14020b10801046842d40040042a01a504413081c00361600d5440200f44428852410141e1110915100007400340d4040d200d441281d00b060300e0b501daa02c0d01258009000d9000c2d1514060b400700800c03e01d142c040c0310382500282441010450549181030a15804641c142075500c121801301c15443ca034010203a4050b11000d000099007880c100628200301c4600c220300080300480c401c0c0d00010300d41d5118656420200401000405508040d0784042d145118100705d00c5030741d8007450003c030180e01c40800c0034662403400b980c0c000039403a103443e01103842d10b68109104c07035294103c0c0b04409100c20f020420b45032031035010713080002e0b242c50703030718201180300c90a5100500d940d04240030f1104154403d4060f2200600980f00d02540d4806201006210039080a0349021610312504018450503404042d00406101411040c68410944ca03154a80002101d0503800301400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 776320242 1250 776318992 776319077
    0x112404051b1c0606080f1501091104170106090c0207081b101b0c0f0501080f0c0a0c08120412021005150906040f0e030301050a21030f 59
    0x82207141d10107490a030405a241084500040240c080b00300c0340c5070440d4216103204140070f015444100100840011a014602840321040e00e5030603401881e807541031510f000040074401801400e0258a2802c800c91402c1d041451442c20019258948084c035940c4403400308030a40c540c0300c0c0d81c1c0c41c0c1c0c00d1500204901e510f8528554038010094862588542c0520030311151a03e0f000080b020302c00d000d0070501d02c404840c21a031030b0349a6030000003800e4205142030004802e9452110703642511003e070381e19010355032041e00401e07104400707070b41c0090680b00070801481050b1241c0d0280324880d200e841810b240048035512100c00c98015101910030b030792042a04078036950108082c4070150307040d00c4244010b1a0011030f441418035804113040c0900790b004001a081c4d540c0354089450301d600d80c0d408201001a0240b0b0959a41003400b8550144408440c0402c0325003506070000c12103903e00490044440e01650100d900b035401c10503140500500056100f10303d0280304001c0000003441440c001840312 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 776321492 1250 776320242 776320253
    0x70503132109090b010903050d05032d0a050a020a0f0806030a0b0c21090319120203071d0111072c04030e19060c0308190612120f050a112404 62
    0x124840c4545c1401600c9400700000703900401c0c440ea00d1440ca007000d239209c1d41c032640068280c498660f41d00c0c802c5c3d001010201d111090b0303040e000d030181e01480da040107203607501301543d412481001084000304403003110407442c1d00d200c1d4005030340c000030181c207451110469170760744510000d0507181d680040c0b070085107401c08000f00d1400c4414581e88104c1070009802c051044a03140d1095009c450300304800c048008185a024600320082107284000840d641d16200e0b40c0141074540d4076245c2a031f1110103a2214601e580310300011091240c411010345005490502c2c0e031207040c40c45440074031000780c00d40e075800c004e0380d4100b0707055200c0c0340030351960f0030f049200301c00300014540c0020640c05032000e00501030040b10761110354002c9490345400d018086454840601d0034550703107001c400003d5400c0c2040840c450314601c6000311110303c1070504d94200030980105513074240c43d0240140c0000d00c01d02148103003501c0b8a012021f00300150050303940c41e0348001c4401c0a00d600a2018107042d0f003411060104004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 776322742 1250 776321492 776321501
    0x20c0105150109030602160b04061d0304060923030334080403080319060f03290f0a06051f1d03030a120204090e06010302130507050313210909 63
    0x300802055069800c40d00300203031501c110344c0000703041c1550105e00f1882168000541410254100d4418101441d00703103480c101412400344031095030b2025610900700204004151003e0b90010384070310350981e045c035080441c01000144044a4240d5902203081241c40920041080d42e03201806601402401324051038501403d8401d858070f074100740302c22404224180161401e8a5000040903500d46505805101301c50b011400b00f079001d80781c101c0001e4003004100a800840f0b2240030103c0c008018100080f1460a03403501140d400302500300020038054403480015880f01c5040400107140c1d44031004a2250071850000500c81034404030744000d0300b60080c0b659040781c840f00450303098800d4120f002c03c0c1c407805100c2188081c05003000d0700750b241c814182c05850240441d2801040411000c03400d0f9070f40d421080c40141c0c02042055400c607100003041c003400340316400540f5031910399202c0807041126207003107640075280c0148030030301c888501c048010050030700401030f510185c105061400040459 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 776323992 1250 776322742 776322751
    0x1030b300d0c0311030d0e031902030c0705040902150c010b2d01050310082d0613111807020c0a060c050a080705010207020a03080304120305070c0215041701020c0105 73
    0x7503002030340560341d140e030045264101682c149040a0b0010352920300e14618007401500540c1c030750504640b0040c01c64000f010b06001002e01040150b80d1424040036a26403091000e941a190014002070241c0c0c1800e41298082620181c01d00318102083c68040c04540c1100e80c0700315283e51280d24101e02482c200106c1010200c2031859000603c0c00c03025814024681d8280f40380c140300001c00041c204d0b0248001c4a001049403009540341da4a444030004001c6680640441007001c076035101049080c40018102e100e10b4000e0b50082c105040c0d500d4108411038501000f41e888400003203600900c032551501c26020f801c6039001800510954000c1062000c00d41d04000d04002c49010340e28045140018580e00c0d403600440b07c03e550320400d0905078064810568080c0d0048189280002007011480c0210702c61801f0b4031407524010540c0e602241690029550342c000114220300b00005441c084000b002e55070344003403c1502d007aaa42501145007610141181f04c141d50114885070000400e02529510 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 776325242 1250 776323992 776324089
    0x723070309051c11011101090305030f0114090103060207050c0d2102060c040b07020a360603080304020402090f0319150204151809050f1603050c030a0b01030b 70
    0x101141d01c0c00400d0083e29208025100c5021100d401c4220b03400b4a01142d00c8089140081c80300b40b00604001d41550f10a03540e40d080e82d00c940000040f190f06407200300119240040100c1c495074619100c10002c0c0d0481c0c0b40940c0c95000f51502039056a8610340e00c5480644148400d4809038046c3ca10700d620b00c444c0400d0340095401200411951042000c200d1701628071000340951181243d00202c0d41d110b01d075401002440516001811a600f10128410003914002c508183c4001d240c2001c002907640c60705c0300425160044c030100d00107250070740241150f00009015820680540c600003445c0050301141e800c240f00c04005a1400d0050384260400c0041091070300303618141c508072440421a0a8201100400c40c030204812a0310540340b1115000f8800d50000f030104c0d003000001c00642da282540c8a42c45803840c58001809980240600e6100d40451007140c0c0c10355581c001c4a0016050055800381090755500380500300c1d03500c1c0c42d010a1649003003444803000e20388007880d00040c2d000741c5039180d29 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 776326492 1250 776325242 776325259
    0x2307030b040903120c020c04060b0c0f030901142d0c010e1b10020a120504060e01081b09030a0b090a0b1b03061e0619020c060702010903020405072307030905 69
    0x4070350480d06a07820132000304000240015800822401c100040080c180e01504001c00051b56045d500c0190440f0318082055820340c26040055540da071003080d203e070780071134091902449200b2000e0043c100d0b005410304032803c000c64001024503284000b0b003208110b50000721b40b07000c00e007600b481241010b00030000103190300d00c050085044000034015485100300800c5c900c44100602c20f01030f81500a904c00c2d03000c10521400700001d040b41c6c201c1d0103801c00140d800c01485090b9841200003600566480c0c0d101c4001d51036155060a0035400f4400e600d4051048520391000111841e80e030303510a202c0e02e0301a040c555094502100714a90141082c074041d088004a20000c00b00e400480350010800c48400385030b080c06000c1c1c0c10147c08804140d0340e101002040720702a0744201040c4c40410351095003070303400d1040c943e82004068060501d0190000e201c140c024401801c2941c0300a40002103410450100c2e089080c1c400e015a40c00f00442a400f41c01280400c04c15400012500103404111017400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 776327742 1250 776326492 776326511
    0x1b0d0c02130e010b06030a0c1704080a0309060e0d020307060b06040513180b0c5404060f080606010f0c032006011e14010c08030a2307030b04 62
    0x1548800c80600c0000781a9071090102c58201c4250b1003d074004c4005020540c9034649022004010454001c0d80c601003030608881c11003c60800c0c911074400c5501900b1507042040ca070008400070510510200d42ca16528204d040c2c7c40301041003042603482c038641c000c50f9124040e05d440f00070f4614a8000c0c501556003803200b8010b80d6506e250034100000f540d203000502054642c00030169581154000d00150b24100c140003010307130b1400060400c05d4040c0740c40c103100d85944851582d002c0701c42045040000b0b810801c3d08805141e001d101400d0810308040040ba84811030008080750502c1e4442e44555800c100c040141450070700c0304980c0040d0900b000e00703410f0700c001c5c406003010714503400060030011101c8540c1121042403c490b8407054901040320307400d40c0c40b42ca46039440e003006000381c0703402e81000780c1c0012008a00c9500d09041c51040e0b482e8804d184481d910001181c2014202c9103841d521464003900b01c3d80c82c401c00c00820054860990b0150070011805000c440d00301c03d28070701960501ca1801c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 776328992 1250 776327742 776327749
    0x170427020f0403080a0302040f03030c0506060118120309090e0106150302030403021504020d150c020f0a020307050d300e0f01140a0302090d06020307351305031b0d0c02 74
    0x50b42141d40001210b50b4865240100320028401c941089000a440c1d50340407050550119014402512030802c80380c0b641c448900658000f5400403a118a00c50901d4051111603110380c41c0c41d04442c803e041c400382c0c00381c903014000b058070714500c20b84004c0e039540c0004120000c020b01c2c108010900c5410118554105501c000f91118400502c850160301d010000ca011501c604050980b40c03900031201c0201c828001c41c5250181c80d084032600018800c01034038030a11400810201b070f00030750060042c03e2180c500001c0c04404244200b0070f80d9a4a07171380100060488144500e10220071946599489118080c2e802501190109100328043d101c0b01ea501720560360400d4003020803108469149850302c850100840c082c0c410910043d40010900c89001c0c10042c1c13a4014500804654a40d00d003070f024110034503c0360890058a0b807032820300004030044800d150700c04803500f14a100c2c0c1c900215007070f652201031135680004000710600500d59200368407010140816800d511840c54542c9048441c0c1c3c002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 776330242 1250 776328992 776328997
    0x90b03070518060705010f06140a080a06050a2307023d020d150f080105060d06241508180a02010503090a0b040b09060705071e170427020f 61
    0x70b4040c1c000c450481d02c4003541c0d140b05440c402030b80100244981e5244a01260143c0482c2c4648c1d901000b4002e00c031506803618441000030390740300d1402025032030a19142e8201400e8050020014150345100c0c4e200c004501d0405003003c6030390344482c0070303440c104900000d1424011601c654407162405540d00d0b0100007445603540b03030030307401c9822040f032100c1400101c000748280003541020034580041c014150500c0700d014001c0740c080340c0304041d4466031400000d00340e810445409034010500c0e21300200059283c3d0013040c865075400382c0310001c8020100038402282042d007128800c08040880c01035500d9001000d02d6000040f4010340200030514002c060f9102c01000c0024140200400001c0c0160b008221202300d0704d400005141d40750070207081148a036101561207100a01a2000144c031617806001116100759004454000307594004103074003110707440403c0032140d081d62540c240d1000e16401c1c010b400940121101c0f0801016450300e00c03150103800e44039032410940148052022801003105 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 776331492 1250 776330242 776330257
    0x203010b22380a0207050126041506050604090b0f0a0803030c0c03090405130c090c0507020904060917032707030303020a1404030302070e060910150e03100903090b030705 75
    0x101860220980203100102002d48007406200b408114003448950001c0e0351011580280ca681014000048069413441c1c1ca018401e984485032a0108000405c040700070504000480310000325940c84100140742a4850f5014039110b5031120b025100a141039035861401404c103c403214001c2d03182140b0540c59000c01482050161030105070b20800d030105104076285507500030020041813030704890010455a5504081c1c0e500400340001048000c1c2314465140c0d00e110645501d4104a0140e00308118001d00a00480b141c6843c0c444000000c0d00c018261030548000c00b60701a00c2c0d25240c0f820503110400480403600c581130540318803a0140004c1703032280981341c0520b0050323070f11404820165038a070108440c4400071800007500105060b8045502d600340c031041c2c20055410384442081068158060390b10450101e1001410892050340c0880c440d808400e5080c4800314040490009007028420b0502c194041d844409100070140e018035000040c0c03c4181c0980d05508044400170320358080c204 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 776332742 1250 776331492 776331539
    0x6121b05090d0b100303111605060915070c031b0608060607050c0a0e150a0b0a030923032d030112021804111002070501052b0203010b22 60
    0x290600c515201c03034005aa03140d403c40000c0c8514200404080c1c14101144000c1d400208007003c4c2484100f80415407110034065200c4420840341440c00b00700c12540850410381c2d2240f06006461080f011800192402038060962043c1481c91400e0054940303005804810780080030700820f01c1744030f4105500c01e80149007540c0090b1100c410340f9106103801004c200483c0d200181c040c0004007a1142c000c003e100f05501c1c202194101505410301c602e0340d40c1c90180d0b444d40304080c41090103007807023944844a26805840a442e8169052202d00841101c440203850780e50000551101c1201100f01c0407030b1064152510950160203403010600300d400103000303641a920f09480008259038840e02c81001d400305040c148801400c003440c2250894000c003140600440508410319001800030809804841040e1900c91512034034444003401c0b107200030070164000c1c0d12002507101d40c40180c0b001d18064403004000d540e0703c4c4da82c5d0300e0040c6854001040f2460b203030030b030410600c100f03500100c0ca41c4000700c068 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 776333992 1250 776332742 776332747
    0xf0905041112160e0609010905040c1505040f120c030b1015030c300e100f02070b0a020f0403060e0c040f150f030c060c0311010c020706121b05 63
    0x92421410340c40044119036800140401c10000c1c110b004a0b0803041d8541a89410b20500e540346034001542000f100c0b56075010103100c004000d4140ca079000310341e02500c6044000c00704c41c1c50b019079803480c001c260300c158005030010505103c0441c07181507400190103460204200500183e48140003507034903000c01030030307203001402180c0201580c003d070720042e04428902002000701d5200c028002e00c040492403001980c004410388038075180c240e40003408403000504000c0030b500951500302520b06001e01204030703c209032801822403040d100c1c020b03400c8655a000360fa540aa4140b540070b00d00007801800995204201c000c0d08a00c0c04000c4a0440342e0100340400c0701700519204038117158240d0803041d002428444403a80142c6e09a211450b2400801801519503450301c004400754512408002d00d1034140040900c00300c0d0064800084541c424074103404030f0350300030442c3c3c0d080da00010800d0000da03211160a010307180d08020842d680144400c02080f001d4066107041c1f04045401e884c107820301100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 776335242 1250 776333992 776334001
    0x8070b0a140f03060f0405090d03051e010b12010602071212030b04050f040b15131808041d07030b0d0b040804120309031217040803090a0606080f010c090f0905 70
    0xe0701050002400c1880c22a071102082c0304501465881120b1140c441c01840c0c8220081b0703d030501c202402105103400a0564403010303035054008020280ca11900f41c40341e0040f106182600c2481c41d40039000a419a41d124001d11140d4411090180c00030029034010030b0741030010101d1521801e00094008012902000c2c43c1c040c01e07001070241580140c0c00c5410141040000c40c03542d014070b4021071262044007071554070351500c80d81400f5041d50080d804020b440c2c142620350b40d15000407152112000307920142c250140d607081d009034884d5001c021302ca80044104818040340300341c0d00d0f60244181c00e052140601002c002040c10244030402403102c850f620115003408584c00503100580445141e219184c00d40f41070180142800780b004807030720703008120401401c91040348240301c0010703a0074044420b6221941c801c40e030303074100402900c3d89104d0142d900c0b001c5071403809000000e00c858400780a44100310400142920f254408801c28000c0041080000f001290010b000300d4581000c00102c686a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 776336492 1250 776335242 776335247
    0x70b03070c0c230f0303211e1915030c15140a090f1e030212030c060a0605130e100906020909100e010e010e070507030e0a0e160908070b0a 61
    0xb00350b0000000d80e100a0701660f00310041c4048031121200842d0041d4105a4450400d80d60703109a0b28142454010700c2d4000301d04407500c0c0201034001c2400420b451800d0016204104e500c1d0044501c05981c10b8592407140c560191032081301c3c40000414120420725042d17480700320700c0c00b0851040382041500600035003102e52148800c01403c5100c5400659680824130b40140030940c3c0780103466036440900030014141c000314940892650700c8503564400649107808010841c0d20042050300d10780820845003240c54000d000300392140a004000140f0f20703080c04103000707205840c100da0030f41d0b0500d8115402c0d40c80000281c16441c08500c094080356000710351500b94044e01800121980052844050040000a03103489405507010724042c0c45603683da0b0104182070360000c1c031480340540914404104449d200d1402040a18000d003040c241e15021400416171281c445c0d80b2103ca5041444140184160000d02c40c2c0b50301803a5182400c410780c20302a8544c0c44651318483c0305041d1000103404401d60f030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 776337742 1250 776336492 776336513
    0xb030f0604080915032223071503062102060715060906050d0c030b07091d072d080601110a03110616080c1b0d02060a1b1d0613090b12070b03070c 64
    0x381031250312008421081400d0754441250244038003100400527008481413103031040104844025400d8102c81c04803088660351901015020703038014604005100c01310f19190692000b0b2281d11100003403641c0341502d03040417a100c9400c0a4800e8070070200b04c401080016204400707990b04030700745249648400b0300545403800300e035000c0c1441b02001650100c0c00520208103d00c03440894070b58a04440c0c00a000c071070403025507a1700c0242d902c58500303d02003880c45410072581c09041070401000020701a54181c1c5403010032141240000e901164141d0281d20a0001c0c5400c8000140c180484030800303800541110f0005001e83c81c04480414010034410704a41c8800071310700c0080a940e441c0d9100003000351503c80c00c48609150f641420300d145071000ca040b014808001d00d90740c84405007a8044480504403213101201540000240f041c01c040b07140048046000380720300ca0b00068101151420b0014010094030030b92510b411a02040240038280021039a00c017085141c4000301400f1441c2140e0081c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 776338992 1250 776337742 776337773
    0x120a18061e2604020f06030103050a11040b06070b19061818060501080604110306042a03141b030c0105190207030c0e01170601180b030f06040809150322 67
    0x30245030051401d48030b0741e44002400340340280d40b5007090084203414009240710038030008102e64000d003003007030110364810803008069000401c04a016080301001030119007000c0303810b0302d501c0c12141c240b000c40c822081d805000803041640a111242c50411002c842c16010414031025540703641a801c00d25041000d100e04503503100340108225615043e08a5aa42c0120380445004841c1008001c16103000521544103607442040c0a00d14026656540b240c4a00030f02c3c007445078041143c0220004401e096030000c442942c4004048480c440740c60710820b0011811028020380040ca1300411990780901102c5104074042c041002811a62100300d29100da142c1c0082c1c1542c400303c00220304400032101c128120780b541e510540e100c540110100391100ca0070322404040000ca400303030030110b034060f800c83c0110880c02000c1e600d001d205c01007058200782085030100d60782407000401b0b108900c1d0169503a0b0303000303ca00724001d080d072070000d81c64807004016000d400903100000300c4410401c800000841c450 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 776340242 1250 776338992 776339027
    0x16180c1b0605071103030c0904090201020c0a03060c020c0a0b030402060f0f030a0902041b0c0308180f010504020109060f170a020702120105040606060c0f12020f120a18061e 76
    0x900e603410000000c00d4207030b80d9003000a210a40e07048a003c0300000b9a4003da0540f482c0b6464900814100300c010100400102d055020b0002440c110740c2e501499100203500580002c03c0103c0b80307400090620010b540024401c1940382c500703201001c03410013075a0384180d06540c0d0594900364a0b82c01d1169000341407034440011000420441c0c240d496820241006109450038040011010900c2c202100701c0d81d06100001c1c90f24403580c020a115886054010440306510088002c2d4088141e003010f502801c8446107030344030024481156440103003800145902d140212902c035402c0720040401003440605410741c480100800c880b6403055048800b50340c2d00a00d0038424003441359a03036018003001c0341c060b101c8902d804c40019800340034200901580b6441409009aa0603640d20068003c0321407036030f8011845000c0c0c0e0109424403c10000031540f4940356010788a40061f20001c04100b0442c11080001885900400c03156800540b4032540c0390310840d1456113044c1102017100c080d00c81d1403d03c040b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 776341492 1250 776340242 776340287
    0xe0607231e070501030b01031e0f0b032a0405010602030d021e07050c0a0801180f050312010b0331080912160801150302031e01181416180c 61
    0x205114000760880407a80282c170180240394441e00150115002e16206c000c03031850440100805440f00c1c1d102e500021200b080004100c0780c62400f0a186c0000110b41000300202140701034000c120040508002c110211414041503040c602d0007500d07401041c0b100a10700d5004100da108000b0f044042c3d8071482c50806040703458402c1070804640d140d500d40c40290080d82c2c484400b0411a4041c05048002400d00701d02408000407a581c880c00e0014414041d138003804280900c03170000c40d10740d041900801b81360003120b0302c90401d040c00042090060300115510380904070440014454003042510306138004000c00e4403110401d010488000760210840540c0c0500740c01c0c007070302150b201d0030743c8296900e180080140350540801c005c000c006500021354185d200c0543c2101e4441c41c14a540c1070034a8441c00420ba40038896801055414800710444801a00c2c100c0c1104c0c4280c20084000440c0711030040001e01446e10082000c0b451300310710011080ea40715400007003186e01a451301c10004101c000c80c2203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 776342742 1250 776341492 776341543
    0xc0302030f030c0415110d1b050613021f02070312050c0d02030409060f05030303010e10090204080c101e05030702071206060501030b0a0f14011e0c030e060723 70
    0x181c0e80b060041c9100240c054900305a006d12a040f58004d0810810003400382c11103424040e1401406642403171303030b04240b24074000300040c0e00384070003030040e83c1d01d6100c4201031b60644100030340d244400d40c1e0f00508440c02d401014110744c0c0050740700c044981002b507664101d0300d0080101c030300d4454401e0020301c9101d503c20340410030b98000000d004441c5407110030894151a0100c00c0b00c2020103100e1140e143c1c2c401d00050224940d40e1803295003111503203080c041800d55070907081d4241e800c2070303112042641180b03040403083d0503d461600c1d401d00c0f8501d44909102070075056130108003c6040f501d03003001004000a00e2041c020000740c406440700c03406017080000c01d0b18102014014600a541c0024102807401c51242000586039080e18860b075035400b03005041107405407403212490270560410220501c0d2195003c044401c40041041a5844400c501e000303045c041c14808006102a014103010018040031482e080e40c4484800003054611480310b05a1809524284082103041507450000c1ca908 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 776343992 1250 776342742 776342761
    0x50c090910030b012918100914090103050a0308071b150c030b0904140106030c030f11010e060702010e031204060206010f0608130204020918130203010605040c0504060c0302030f03 79
    0x2007045a1080d4140c0500381e07203902d00013804450310245d4401c040d0001ca5001101104040074201003006520006c000c0c10700400014050807400c1c80c2c050102c0c030501c0c07040c00510b41d800c6020501000c00c2e00c04620310351569840603076405043e0340103004c2200b12400f01d288203100d480c65082010019420310901c070b210b4284840c01c00399954a048a09151000c4628240d001e8010380120400c000c069190560300c1e625070448100222540c0007555603101c0001c0000382600c10481d0240d07010305107030710105201d8500440500107082c3c1043c1800303403d81107529503030780c1c08080b18038041d030a00e4400454114000440d181900c1e0b1240043c1c11500494040340140d4000f4010b8101c4860840c0c4c01903c681c0d0320f070280e450150642d022030140700d607140002c2c09414960010500050081d0040b00e1205000120032290b14003541c0d0f4262a80200c1144030035403070b00f4044e0001400c2d00321750401503414480300c081c049105500c103143c18441c48015010505000f0b0080e1106900c44d11102c41c0d90340b606c1c0c80c10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 776345242 1250 776343992 776344021
    0xf0309050d030c1706031c090e07050309012a03110f0f2703060106081e01080c0a081216030908160905010b0a170907120503070201020d05120703050c0909 68
    0x7043c001000b4003000e074030100a1a1105008a1004d40031309038008001070012000e02020340c1000504c000d00b1f43c0002c101a898003001d00c1145643c0c0e5854423401c00030340150941e448a02c01803007820040402c48154006440205521000b40c20002100c0000c002021034a0049280456661170007007107000d0125404001043c04840d010001d80141c110305400c0c01e9502c1c07034000429015800500180034640c06818500c0d000303d122402d07004a50400c99148503482001d800001c1d143c0c00c0051074406506002e00b201e00540702190140810f10440c10b0b80c0a028040c00c04039618cd00b040c12140400c0c18003079940f2901a011a03016514400525018402c1a019510992035018509000080c0c11280082926105565030f940c80d105c1d05080310b08200702d03041c094491402e50041c0c0794005001c1c407101d15546d845900c5180030b951a941c3c2400064148500d5031074080500800700300a07080049a330898641c401114100041c0c6910b03100004065405201d108581280400e0203021100e515240c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 776346492 1250 776345242 776345261
    0x50906040b1e010302010503041104051816050d110f030303130c0911070b10050d060504060b01090b0f1608160b0108121204050c030114010f05030a030f0f0309050d03 73
    0x1d41d100c140c4801c850401c0c058088924905030300d42e10b50051005612407002503030064002d030914003e4400b2000001c00f15002503540c4400a0342e1951300c0310705410144036041c9452680582c0c945104d01d03250114050840f03107500100318600000c401c2110b6564a90002031110014003280d03164609005c20100d0350030b24a100390382d516540c82001680418a000c1c104c0308010604105040c40742d1a03586510300300c809400c07011207007981e0b24049410f031031b50000094198094000482c09040034100a03085841d420480c0b810050b03100018800c0b020500211004c11a1440d200c51780c0d901e241c0c80940780d0038901c0344001c01c50342000900010040c212190b0080e40ca00810b81012945d0340d0707200e61a038864504e00424207010301408a4000480d040da8183c1d0b2107070140c01500d021201c0d1070006403c40b100c450086a005180350014400f90545011040c003818059000f042491001d407409401481e40c4200f901c00c0200030214000f52600c02d40110102513403004c01c494842d0840d8001401a2003540d2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 776347742 1250 776346492 776346503
    0xd020a030c060204090629040f1403120f0d060806100317041203090303030e070e060f0102071a19020a17092121070803041e05030403030c11010f0e061c05090604 71
    0xd454607d160110011182119034005403000450701e4002c0030308031025103507500c03a4980a200c0610002d08141c8005080c1d16001401240e0b45000c820150700844509070010400d0768802020031020346000c408a41c03da0f038010801540c44209002c41690910030780d000a4201d03402e0364841d504040d041440f070001d0328443e860900496005c411600e0b0b4800d05442000d88407415000441c00302d04003144c4d0054540303010b10540c1c8203140c56904000b5042d040b4a15a1400d00c1e00090032104071a41040440143c09544017418400384d054503000800c9201d20300c0162070400005284009035a80000c00c18011581c0c15041402184850241d03107038409013000c41014200794036400301c940498000c44207050390141c00c0a05549681d04c580824103095100d141c10011008000400b0410801c05040298403d0742c400ba2180443d00d40f030f44500c0300d10449507041c080d007070b0810140c3c15000b180f4450600015108245ca8015031503208000e5004410103c580a1800c01401104d04011900612036802303078 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 776348992 1250 776347742 776347799
    0x140103020414100603020c0f120408150702030d1a09090a0b0112210306030807050f07171b011b050c030c010c0206040308090a0506030a0203180d020a030c0602040906 73
    0x41a0300b8101d1044500d4400007400d11018000a070190b400b8190000824044889030810303140f24600c4c0a02c0f0303080009455101141c20402240c003001450942c43d100035074440d4901b00701d080a03680303004840c00e100040c1e85801c1581d0521060340c81501d40c0090042603007455040c40c42c50151170300706d9100c0564407041880000308034007400440d00c035103150344440030380c60030040b0002e1072400c5a07118160204245e100c076400000305114502034164140104081e140b112a008481c9251141ca03034410030490280e0407004d0480140410660710040c0c0003078880c419150343c10b004075032000f608129060085030384060038060000000741003000f0b070b1082c0c0031140700107000401500c5035800000e00942c412070400003440000c1000707014150f103140c0a418240e009843e4000102a600100c1d01c0e040c40719404810804151a6820256484600c010240c6440803403000005d440707030020b181c0a0300b0301005282c0074040016070ba04450040c1213140d4108003082d180c410381124504078803503501007000319 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 776350242 1250 776348992 776349011
    0x30803040c1a040605032215061d04020d05010e0d03020c15040503071202101103091501140d110a0602070519061704060905070e0a060801020403080d0902060d1401030204 75
    0xd11594041c0c0d003600b02c0c112410b0a19202085540b940010b01c80d042003a8070307031010510082d6a55001c080503103c1d920032503481000882000855501da4440101c068210704070350302403500d5950700c81d0402d8054601405280300c1d414100e01402d1484030039138043c451201c1e84140f9a5240d40500044015813041d00c0000038800d481c01d440e50340646015140307030000c000420000c3c0b10401420411862801a6800b514510000170215100c0c047c82a400080020030403003210024008080303004408080e0303081550402c050b407400036450403044d07401a000740d8600b00602c407045600580342840181101480e91319020025107076855403060600035440000c42c503004103200d03181a03050301c0090f5180b40e508240c16008500144c0050015240700780d8400c05200800c00610546019100341940a0002d05100749448110340d4564030240340c136441480244002103190b401c40b2000003145074082024451400000c0c428880c2c0940c09a0051034552108509483c011585040b80e00899082207010b82 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 776351492 1250 776350242 776350259
    0x7031d0303042a0e0a0c090503031c0e011410050901052d0a1508010806060a1a090609030d080a0f3e0a02210403080703120f020301030803040c 63
    0x3096a00a16000102e4164002c4082c04141d81031510350143e80c1c0c1042c03990300d02d000d901908007621080b041c60789550802c007145070060340400090000703500640c42e06204e00542401241e070a1040c20030b081c1c448481d0701c4c01a009420510f00d00030841c01300906801c2c403040d215128071b40d074421207005402070400021030b440d241e892140201c02042c0c040c8284cd010408100c8103004210005520003603070100480c114002c1150b074009401e42d0307198940f880d4146542c031898058010f002c40d01c6400101c50a01038540e010100710340c22102c010741c08e032310350310628005095401881060740d010710412000168030307503106c00c1e024091454082c040040c03507115100e0700213841c00050701d070b46e90000b040c610002c0409038032800c50071a4212290011751703078011403040400da40b081c0c8603c0300607442070102c3d40407110315442a08061316903a0031145010700d56500d0040346c0c0592071015090100022044901c00700c20b42191400b100700e10411503407583c403498075840c0758006139015603141494803800705445c00d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 776352742 1250 776351492 776351497
    0x61d390702030708190b06060d02192d120603050f100507030603021804030c150b090a06140d03090e04030c1104050105031e0307050a0309051e09060409050c0907031d03 74
    0xc040d00010080d040b61322408801b0b00042d01458001c3e00c10010380ca16075400e8800f6105043e03102010b80024070010754000c040400421241c0daa542a08403010003004041a43c4d0b05900300c04e040402c40700c0840e0b90640d008142070350000d0214080c44e103400100070070100702c5106041050800300a69111f50303404030200d40d29400000d4000341d0300301c07041c04c6180d10781600950040c8203207486d010300a881c1e903803480036801040c48a00f00b02d4454184243c2441c0c81044103500048010701004082d2910308550209442c4580e23650050384444400030615102c6d040d01d0024090782154a00541017610380205441e44d204025948000d10803117051203880e0a01802d07040f40e800400911342c0c916510300107400d02a15a980d40d140d0303c4200020b200088062000300d103164003a460f102c100320f00d08418028a110f0405001407000350241014080c0d68078030100f00d820110a44001440d000c1034039005242c0740740c021145a10070041e5041081c100c0e41501709111402c4140e41d8400c3e450700000031540d1780e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 776353992 1250 776352742 776352763
    0xf150f100f0f090602100e0a230d180e04030c08070503031b091f0507020a08070812131202041e05091c020304030803040c0302130f061d390702030708 66
    0x40e048040e1000b4030450030b0301f029241300d01c2070041c0c0e00f140d4019602e803043e54210540c03d100c0642310700d6450240c54024401005980b1403810044144191500004102201e60103229801034516005c51305051140c040680a01e80c001c461907034444490402c240e0300d0f00100c0e200805040005d01c5100402c0c440310035106a03140261001130110f07104d0f140514071030702c4440103104005080c803492001d83d484001800090101401030041d25061240481c00c000c03000c0c091034001c0c181080b40c246c5032003115a00b00d04480d00040d40c4030f01284240300140c090503500c032071505521403511201451128a501c064011010304c8104c6031940100c0080044480070b00c1c00c00c80c05a00b0501003000854040d100035680b041c8178500219a003512b980c0080c00b84211800d00321901c0e60384548600c00302d209031054901404070801c0c944c00d070b003440310540455010001e0034440f01c541c82c40c0c1ca01c15641c1015030040400f81e00520704030004a07461065404079042604264401d1099500c009501007012400c00c808 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 776355242 1250 776353992 776353997
    0x1061511030d1e020406080a06050901120b04020f040501150906111504080d0c050d11030c0901120603050106140301110a1e0c0203011d0d080f150f100f0f0906 70
    0x500b1500c0e80403000425100020303003500004801000d110369014401880500155103c003200703824148408000c880c09900500d02580c40c1d100144241d03c40c6180c0c030004141d01010010950f5294404242010000c01d100ca41280c03c100000c00d018546811400e00e00300160b990841e000c0e6100700c112582030641050f02c400d40c000d400e5080601110011465205005601d03443c80d04007113000c85000c503151121410001030b00400c100c8442d00d01401894101450148150b00b10304156030002ca261242c1e00195040c0540c141511004c0051904490011034002d0001c0040541d40c40204180100705804544654604071406c0c002031001400d4a035155107da13200d9101220161080040031944050803040c4440003070b65100590742401903500d0001000480b140020351613000624010703a101c041c8050011100811a544000448603a408055034400c41250301c424008150076590500741c0917000383c0b4160410510a40100c2202035404290740d0f018400c015040003142c0c038400d680580c400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 776356492 1250 776355242 776355247
    0x20c0f0d08160905090906011806060503070509010c050609011b08100b0901140c070f080303090604031d1e120604080703080a0f0c020109021e06030c0c0a050f0106151103 75
    0x601c100100e900c10a64902c07801c00300c65241d25200003583c0c1c1881100c50500d254016001400b080036080d40c00100c9103d00e01c0280003640c01d01e10301804c00e01000f0325041c20041c0200b01d114076a0b20034107403020204d070807806407052410240306550191004610810418081d03508140202e84a0740c2c8491113800344041a030166818140c0008265002c1e22103903041040148403001036100140c01000320030380f00c0c4001c1a09038604629603c100405900c00583d541080c13040040c18240420403660250b458a40b519020015403003183c03d20f01c150f940700380c025000c801d40083e19143e40d07415000100b07040300e1041c0c1c0400e010070b030965036500807500141100c10a005100003e8052241c02d034201004290110f0040c011190300402c40d10400081c60050b916850b4030b00c15030070301e04c000c03400b2042c400704108881a2900c000c03503898400030344000440440060030f04616482884640718080d40207040e190940700c1c29803281d010b00b0780d900564242641c1405201500741c01108183d805812290240d0f0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 776357742 1250 776356492 776356501
    0x9100503030315030a080412020f060c060a0c030f0e03040e0f0402010c120201020d0c050d0c030c0203040b070c030507030c091116150b0310090c0506030702031c06090906020c0f0d08 80
    0x14103903c024021500b522444011030700040304640a40003070706181000c0041c0d198140100411517018000c42ca000300c80c100f161a083c0c0e9000308030150300003944900410038002c819012030042924140b104d489601d4040d1030094490080000c00071619006078407102c607100d10f00074515081c0181da000303000c6906008401c00040740707404144800c809600005060079804000e40c401d0710348a0202ca00002e03400200706190072034600c00d085541201b4038040101c07a8141c200a0340e02e2003603004146190b507000c61030305e082151141300d68001d140c2c0501540d400c1913807864442c6419969001d2005400c1c10b0040209402c6990425030f4103800030414154507409150700c65260f81c2c1d0640800120850311840540501c1c0c030304121501070261403103000285240c0e2410056546507507078002038881c40080062101c519400015a59400d41c0030321885078421120844000400a90340300c4445c59040c040903005220303482c0d02030201c2000074816542c5800481c07500a480b0b5488000807000320790503a002c80e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 776358992 1250 776357742 776357761
    0x50f030303160924030e2d0703050304090203090d0f05040905060319121d130c0215040317090c0108190204051203070c051801060e0d021e091005030303 67
    0x1a1641000d60625102180e01c6a480b481441e40e00d0030030200503070403844c29100150b0301d803041c4801c1515220180c401d4110140d2200070303010503c002800b400751021030301641c0600900040f0000c55101c1c0403a99180e540d89501001f940045803418070707a004000100c0181c5010380340305500b400c40741c0d03141e0b4540390401e89900001c00303000c1c0c012501845404282c0381c003580b0210040039854000c0d1503e010600e0f01000c02440000c2c14204402c000c07507141040384090700c5008200d4038402e21038501241c001190031007285801a1030a50074903041c0194140010303da0410303211300548035900e40400480c0e54200902d03580300c007000e04007400940780c0350003c5e503582c80c514840d00c80f801500c0f401500d000d5841c00020f20403200b0460504854000180b40020007100c4a4280010441607031480d5582d10380c88101400c03408144110300c1070020000e01c5038a181d03180300c2095801c41d4018540d115001d80c4021080582c40c0c4041c1c161300070100803000c9030079150411442d00072918001c0080d4596524070b80700 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 776360242 1250 776358992 776359021
    0xd1814060c130e040f060c0c140c0603010b0a1b0b091006080a020d0507230f0a1203121409010903110106050a180908070b100b09180907030203030307050d0501050f030303 75
    0x15a0180175a110810019400d801180d0002c030051303452943d8a041401c2100c81303400203405049295001c0c030304115050700c442c02a0380c1192a200840c6894142c0c400c1c09942ca580202e040780c060341000500003017002075002189006056080403210344441d81d5411004071181400b4030000366000485400040ca4038500000c81d451181040e2202c00e50b6079030101d294143c1e1500080b482034084110101581081d00c0d40c080501000c850103900140780a16444c2d01d0000040040c08103c005d030364051442c01d0316000007070725050381032880300c1034545011918020540d4100480005181e100034841d26041401180700b40d80c40104801030003440d00b1446003911060f031803481c0107030740c807005d41c2c2000c035501f00081c0040c180256000a80e501d400400342d242d8008a8000c40c2040d402844110344a440d5120280c0f00e65588450785505510b500780742c1c03440c18401d944000d500d0b100002c02c00000310b901c1000f52002d07110000013401141d88440811840d00030070000680c250344244001400c0c2e407082403d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 776361492 1250 776360242 776360251
    0x8040f0b040c09060f170d0f0507170f0309011a030d051c02030a0e100c1e030b0d150c0c0203060a0b120d02010c1205040c0b0d1814060c130e 62
    0x2180e01183e0303249102011366000350711a04403040101410071904101c21080c3c15002c0c41600646110043c910018104800c0c260320f103010058003107043d0702000014411003411414084585444459403000c0c0c44441e4012078007102d070f5500b00400302451081141613210150000ad000c0c00d2102c10158003296642c208481049601d003208400c06e0108103584015406a110402e000c640d0840c0c24000a181109120300c660a261a00e6a9008200e90103a4140c0780c000b001003440100b014440c0782200a0074001c1c00c1e0315401480450361008200410340801c1c2030440301700050248050094007a00d02d040203100203509600107900040701c1a0682d80401000c100007005085031041ca03c0013207107803480c8102c00303d0141c0e54179051400070b1608541c0c82e00c11f03518014010f000500e000c1d82d0f0125865414483c0c0700b0100c401040c0c008d102159900703e0b200c8000c0c0c58816040002080c20708008500c8070301c400300c00d14003401012411114041c4102c2d4030405014804100c914542030842540600080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 776362742 1250 776361492 776361503
    0x102190e06070f0503090a0e070507060c03020f0307091503020f03160c1707030320090d0809060c03190f0215060112020a02060f0115090302040203130503040312030c08040f0b04 78
    0x100903070020351a0f8500480ca00e0060000f035413609040c20600c860421103400061201002004000201d58080112082c40d940900c020801012000050b40603000c0c0b1404030303e1141e00401081840c5070700804a0b41110f8a2189126001894490980403440380000845568004200207524500c2c00044c3c170210351403a1418140d00d07001ca441c5c034034952111564007500e05000262840606070f160007110b120203000e8030901a051140e060721419849a891000e004485c00403050091040003029902c0188028040c2d664402542100d50303140d5201e0900c4030581d41e1030003501c1c0d0b030b143d114410030310f0b5160300754000b844038111030781e049000140000c0995041010240300c2d500310b0300301c5001a080e2030700260000d2103142840110407411a00581120710f40d0301540d80d0325040030f603114683c141181e4060f03500507601d4a0b900c15a256102003058003811501c4005000010070104004020942c04156410452500510001c0341c00040c1a40c003c1c091000d80b22280010038003c00c0c120790031034401c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 776363992 1250 776362742 776362747
    0xa1d0a120f0f05160504060f23060c030a12110318010b04090807061805210403050318090a0912050903010f05011502070602060c0d0e071d01090605030102190e06 71
    0xd80c2c4030000000300700d10807140e9402c04074901c20135a064a141c403000e0b2a04035030601542e07081c40c2c030386900c046041c8164001c108120380c00c14a80c1c6015074000c00c10000c00342000d5a03c14500046940d20b0340315a04100024035114100040d02403240f08405822403015800307803554440314070080f440c0b00062110324940d5a1501501c0761a59544240b9501c40c1c07082e1405070300c501840c24140e045403501a604a0b91000c4148103034001940443e81d078a81d456043d000c3d4401040d0b03070001b41114080c039003000b072591100003486a50318112484a844110040b9904c8416030f882e90414070655902403001002c40b90000f11a80b5a00e001e2400342c511030b00c000c4c00024019030403078030f00e10540360280d200504440000344002c5c10aa81400303801c0140034180010480340c10000012601d41c40717a4510b01000c01d5403a51050340507007041c0441c4c0010101442101e401c0000c1054450900d14207200d04508146013680004450906009480d000c8842a010072008a011034007070750302c4207058a407075600c21800c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 776365242 1250 776363992 776364023
    0x5090109080102040e0103060612052a0910080c030a03140922060302030c030316062003040c0519060c030f030209040e03040e07033612050a1d0a12 65
    0x9201130001091110030900b410351550520324201c0f81d05d604000ba2442d008429000421400940040300c004249484000c001c600c00301c4410503c900070400781c0c000700d548144800d144c41d0b0103480c0c06545d034100549450320010010580d0703c440100307000303021420001080d5101e286010180102c40340103040d0762000c110b40c88646918070300c6890103180340c0f0340d9100c0a005604080100e060801e500350300841c81e014191543e0b9200c07241500340105000d442c0c402d18104443c0c80a9080e5006200b003100c107403a41800e262800c1011513a0154034040c609508480144100f6640d8100c1200e42c1d80c0c80700d001c280d040751021682c0c4522252900c0600d0703020071030241151514407c0c5040003000740c0c059038543d41000350701080e0324000b070405006c141c20804d0f041103070550084400050103450000c140213490381c182c2d0140a0551140c06801340c403c40c0b5504101a8009004001c1c0d088a5528210701203100e20901c0b03402c04045424270b4110107400402c0c0301c1148204080c0304802d00402a515074a00c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 776366492 1250 776365242 776365259
    0x18080c030d0822050f120313020609030f030a0c030e030c010504090507030e0f0705010306090219081302100c020306060a080c0402070602220608090316060504020f030a14250605090109 81
    0x568a03802c0701c8603400750540c406200c10510070403070415601c019091650408d803802407403a000c09200640304075400106c01d03a039a581003043c0108a08240c4c03e580d12800f001c04e024004090380403094010a0b03040c00760002d03919002c2004242c43c901610386608260400d102c400003400003e204005043d84c800d10030040c00d0041194441c2007900c94001e0000c00e00b040001010741f409a805100c0d15801404030700000c0c0001d2200d855900b0491421280c26540c0c004540c214a0040d41c1c06900604005412100c03554800c5441101d54001c5d030071520161280b4041c030130b00343c1d2284500403841e000100300e00d1003850160010450345010f0b0303d02608002100800541c01042c3c41c0305200c0301c500c041402c02c411508140d40d02c0c0d21110810280d410030b25442c0c0703400211141200002d020340c5e13803000001d0455689510034403001c2c6015003140c0300ba100520b0640c00101085c07014140c1c5105468114404001c0711480048180512074061015894003009440d581c100002c114140200d001c808a09080b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 776367742 1250 776366492 776366551
    0xb0d0c0801061706160e1819180b0604151e050118030503030c0703050c0313050118120b070c0b190c14031906090c18080c030d08 57
    0x4503400001031064900f41c45540c0140e854400e02c44a40c00c04000c0000000444141800594060821011500c400000113500c0d010314640200819205420b0040001118040e0015000056401c2081003c3c0c0102400c0c4018011801400409403800040c2141082d403c25191510f181ea105802c0907100e50b0801d031784000303580611050b00d0703500ca004c1105603480500c41c00c0e81e9038214079940c80b65081d030310703401d80740d01c0020f007664295400054040c2c2018401d0040b40c2c20903803000705481c0ca440704e10000f145956654442c0a0000f06000354100401200c1141c280c1116140b00ea580003202881d03880700740c0e10400400e29001c5c040070700584000f0a0381101203520171442016a1007603001c507d0b00c2c51040b92031881d031100410412601018240f54041c0403607810404039140f1860000805078814080c12481e0041402581094240c008858010051101d040911114043e12580380c0d00a2660703002c0603402a6410307071008070708a00030f901511700a44c105d404426203030030007180013800b5039188 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 776368992 1250 776367742 776367749
    0x3050d05040e2a12040b060f060a0f020c06040e04020307051c2301060e0405120301030812060310020c010903030515010504051003020409050705070b07030506150a0e040903080906010b0316030b0d0c 87
    0x2132240b201000104031420100e01d42c8200304880c0d603010b44041502140480c060001c18100740001c50301c01c100d0f494001c0204030034003d00141800d40d19920f440c01c141d22031400742c83c01c030300900c9240d40200f5a40b41041d00c3c9000c445d145004480841d90680b113813040000a440c1d5040e000783c0ba80207a03440c0050a010712009480300788454500c9050501d4607910b42030381c0c140c0d280c280100500c010b00001d07491504807034481080c00c02c5414036481e00340c0000d0030241c800d000340240610014203940080010b412a0620718043d0314100601d40d40d015485104141d0241440c0c009481000117104d2440c01c206080410519458010704103138485003000b04590301940c0b01008104041140c5003001040640940d01c600c49240500c02401c10901007108002e401c07000540e00c00c000f03c0d0040216126807041654058020700a104c200b65505000e480e00100f030782c808170786001d104004604941d4a00403280030b8000303c45155914000148110000d00b242142550b01590301040480807401400c0141c015 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 776370242 1250 776368992 776369017
    0xf1909020417030a020307020f030309030d03060f05010302040803040e07110d02100f0209100509030a051606200703081803013611210706050403050d05040e2a 70
    0xa80307040c2030159500350b94540801c40309500400001d41c400e41c2c08400c0c0c800080d4181d1744411801d210900090175800392800f9241c0601c074410b41d00b0f084545c15080841180e40001d005c0c104142c803072004406a1049010381e0324950b004000c100081044209100e03030000e8245000d0364040e24034441c0034104000f940c100d4005034029103041400728903034440d02c0400928040214600a188001710f5081d0303519100c40014480c01181e510f1140c0c4040c0f01108289600c032007034038542200303100546550f84d510300603c0f0000350301d440c1080034044002c1c1d04005250b00380000344901407540d994045039034440d06500d15a1400f40c544207086840900813461700360001c0d0725001101030348000f00c80f42d0003506503034003258580031145036000c00d03501e0028012060058a0040c031048400c0c81c01810500c02501d0304103984500f403400200d00b41d0280240060324810000d48030f082407040000c603214040c2d03008002c0c10306000404507956244c001d803009040364240121038030b40c00c2000241c0706640c00643c034050341c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 776371492 1250 776370242 776370247
    0x1b0910020115060c0f15110c0609100509060c0c0c100e0117070e0402090a03141e030307050a050c0a0605070c02090604061202100c210e0f010e0f190902 67
    0x90400519502c031020b800d41d407404103002e001e5a140d5105203a000800039110582d01010f00d419500300b500000761081d104100e550ba48c2014003501581c07504202c850301c10340e000e59085400d0200090240d1030044004070b0050409484441e500c5080b0380c010716400038284508103006106403070744491044200d240e9250751400c850420005044454007c085091003501c080402c2045500002150052501514010384404131b00011032000c0031141c20107003451a0740c0e05290002000062400e6100154001c40f218543c241c10090f66039010948441011860034800c4c1c0d03c0c1c0c60b10500140404011100480c0e50030700342500c3d1181103400075101080081e00d43d045107015820400455030300404155410043c007881c0030691044072004141c024421900d01038001c48140c07044950a54041e00110885143c000b043c52a00070103034154010008103c506410100c0c901d0021340d41140b504040e1240355000c100e14042200000d400e105040c0e0048002e9054000d90000c440201e01a0554800059 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 776372742 1250 776371492 776371511
    0x51614120c12090d02060a0209010c1a010501020f030a090512010917030a061d07030207050307061b1b0c06390201020601050d11240a030c0e100203031b09100201 71
    0x400090001c045044903404000c40d00e11045d800039516034420b0003600c0040c0ca49100c0d800488085204920203001c02e0254000310081100e4034004504841c0240c08651540168500030f0742c590140c3d48440022038500c0008005070b0401c8c001101442d0b665600005150070103a440d01138005000c00c507030003600c2c80882040b110720990300c541c1c0e01801070050908510707044000b095100800050035841015000f08400c000c200e010401d4500315035011101340b0600283c0c282e0002c51420340c0650400250300c20389500e01c4041c4440422000f282c11070840e141c1c190500d541510a10b02c15602c0082c00c0140b0000300844090040c0e000b40302c1c0d0b840b42400d4050140c240002885c111060304202d100d07031140095000020071001004000000580302401d9080303203038108400035600080640c00840001404400042d45944421240751194030b44031800e1502c281801015503c4401020140e0310400121714144441001080311b120075144842c5031a01227004585004114500f50000d40c0d142c42462 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 776373992 1250 776372742 776372767
    0x50105010f18053303040b0f010509040201080903041a03010305060a1503140102040515090307060f0212180307120b010801051b1c110418051614120c 66
    0x481c0001c94a0002c2c5100041d00008042d40400d200e03041c4a60519400134946050b41043c0030f0b001c0e80290b8010254404c510307021662544220340c00c8070075003814800558020198254035050701c401400303030180c40e9900d900540f510100030300a140c0e2403200f840300203401c5091240c20940207540f840001c0e1603501d94a4038500d415005407000d111503003044505610032100443d01c0045a4020b40c408462000c0640e03030500a1286410043c1c1020b80d8850441d0784100d82c400074048002c081d41119802603448008480c42c103044500880183c00084d9443d1491000001030450310300d0030002d6480610900f00064640b15440c0d128034282c59102e031a400c2407184610140b8010802c05001713000303500d040c820034800c0203004a004140010041030b8030302c2102020408020b1555018400c00000a168074850102e0b00a84074001c1ca100c4040c0103008403603028011140609440c0400c00001c00141c002510200840850507003442d0041c4004041000ca01c80c03000e0041d081c100016503a400c1d01d4200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 776375242 1250 776373992 776374007
    0x30224040b0a02060a1b141e040503100507140d06090603290f04021012090818030307080711130515010f02030c060c0a260108011503151109030f0105010501 69
    0x1e0004929244040d080300c540004c050302c07018054034200d041e8540210101c003860003500c0194100c0d023001c0f070b9440c48140d0100000c0041e00c0003181180c652110340321a100542d0012104c080019004450310300c11211058050111210900d8001c100da5481c2d0880301c040310210760096980c90401c0c21190020b8445492002e18001e20703040440607480d0540801070601c0c0c010704000c0c013030f030300080d0154444c0c1d02c109141c001c80d0f0a520f1050020700d07968206800d80303802c01c440500d11000b440300c141e05e145c03030700104461005a01c00c0310b503800c1003c140c690024072064403c180d07130070030343e01d02c10f10420309494070a051090702075050303040000d40c3c0d09000605e07014100c1005015517000700240c403040708002a807641d20591030343c59156200103a0b2411101240c1d44030082c041c0480344020085001c080101c4a070690344100c000700004600414600c120240b02e11026040030905410143c01d213a842c3c2100c03003020341c5114824078150000011915240482402240d00c1e50750f50018443d56a00980 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 776376492 1250 776375242 776375251
    0x30b040b0f01121a07200a1b050a05131509090b0a0902010522080f030309120a05070602090a031e020916020c04090f080a080a050a020f0301030224040b0a0206 70
    0x401403810390080c1d8982e40741e8140c404c1444594500000002c102d10b205112001c01e0004803144080c040200450550b5284da003500308403108030341098600350a00f0f000300f1880803188010107440842d0310700021b10a0441112007840b00180c0c0740c20714480380e1207144401000a207a4008001890b01c4d260030700903076209018100d28ac81c14100820100583e9105043e96910f01c0307101c000320313038140207045400140c00c200e42c8500c441d8010000344070a40031020015602c500940700170744891104101745280c0e00c0c4500510b802c0031820a00030100803c03e10b40c098801c06401030000c10311b10351641c5500c0781d00e06203443c002241110500f040c60071030a080030000c0e082242c510055880d43c4a81d47d01035101d03000380340220b0040c0d96a426a1092000e0005500001c7d030704078414540d1502602002410800c2c100c95407003a15090a010901d820200d202301c40801c4500c600b2070341103034216401c10602282d581c118510359000e01051861009041008200500c4c1000680f96541c80000e00641803600040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 776377742 1250 776376492 776376509
    0x301060e040209010e040f091e0201032418021c0617060f060f220e0714030709020a0c150204050103201614030a0305041e0c061404030b040b0f01 64
    0x30899159802178141c0301e180908032070210301300c1a00b1041c1801010320400c05440c034070010782c0c1c114203010000d42c81080d890003131f81d060004040d040b49058401700c0b04042040c0320401e25200300814003c1200c1c511552446c002c02618082141c2c0d4203d41300010014807002d520b40c2c410381040a090745002296070703074040101604052401d0f150081c00440c0c0102114002c900c01d140f900416521800c1309a00381921f051002000039841003410001c20701103908810b58410200c011850a1821074141c20100c0010002c054050030109402e001e50440c010389018000500203810000d45d40d02915045612030781c1c0b0058559181400042c1501c078040030703070003806541801c2c1c0b0040b00344c0c000c105d03014842c082d040000e462031103240030f40010340800010b0503140400b01d0810155945604100e0250740a40021070344107030741025044c01d03107035070303d0000300300301c821103010460503002d9244000d8000821410300e00f0569680c54105000800703e800700d0f40700b0110400c015032803050b210103601508808 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 776378992 1250 776377742 776377747
    0x80417070e0901142a12041a0c031302120d0201050901050c0726070b0a0e0d05030f06010e0a090903031b0c020306010b130f090209011409101b080309030301060e0402 73
    0x83d201220280c1c098a6140e8548074101c4040c91034802c1c0429103051710600b5403880e03490010b030348800200642a0382c1180c01c640c00c280501492a0358a21b654001c015003403565245840b4003142590316548000b04a800105070104400000d23800d1207203028110303043e0004241450000560350840751300501c5030504100074020310000c00c240000ca038a00030240c602c00060b08071b01003c1c441c0240101c200092a0143d85020441a0407035908100c138130b24a100c04490005018110681c0d1a0000301c58030750041001e040000c0c0c441d84140e070244529200a40325006084e00d81d4a00030544180c8a81907000c40c0c0c81c6c91403e509001542c1200000d006c082c84d100550983c140d00007a110742d4180302d0700e8141c10f4042400200c00f8091203130705c0020007010110847d12130351601e002019402403520300c0e011a5000c623650b038aa402c508104d61070540e0061544070004944207054440f148200700c00c0b0302500040000034005003c110085d0301a0215400440c0c0ba50301d451001803400d005d1300880340c01180103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 776380242 1250 776378992 776379011
    0x12050d080604110f0309010b030d0c030e0102030301031e02040f02130e0112050703200303071104051b0a11010b0303041e08010912030e031309020901140306060301050409080417070e0901 82
    0x215000c1d13864020464010030f80c0c0c5d8540d81105805001031900301ca034113015101041c0402d0341c00c80d001450b02031080e111040001c0401b001a6100c0c0800d10000c3e0071515000b40c49000301c43c07d0001c183c40b240c0700900c0045e24135003940c1100101d8100d2040341c10440540881805950303061b5000500600e03100c110404520810b5981765154400307488018a181c98240c142480d403413031089900c82103800a41140e0b2611494100806aa00c0880495014a00d0b08000c940013480c4541d4040c000241244850720b424240c0c1c600300c41c4c803080c21030445c215542c1d462030b048003650b007440108010b10a0180c560f60b0000c440c0565142504544c1c13081802d80e2500801c28005045800c95502d040011709000481c407241600850031441506220102502c94a01c04550f8134140da000e0b148980007030340c42200914450381c282813244410f488183c0e1141c01407004005074981030300091019031040031000d0070555610f411050401c003080e40e0b03248030303080480c0900078803c0003900d07103510008900083c400c0b880c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 776381492 1250 776380242 776380271
    0x4380d0203280f0812010b03060d0b06060918010905072c060d0e06091e07090b0604080a050706020d0503041e06020f130f06030c0207060c0c12050d080604 68
    0x107400d0300080d00424000034400902c006102140003854010880068800756882c058034140e0103200c0c4207103103c0300302d0008076022042c60152403003086c000d0b0658080c0c00c0b941d200c207c5001d80081402e540400c04002c1540e2548401c007402400ea485485807800e103505001449080d601c5c010841c10400c10b4052440782d1409500d000f1420f0102422410b09414000d100450280e115145034041c2c82801c0c21036840d10304c0c500003011441500c0e070400b50760b00200c05001012802005003d035410b05c0d0700c226414441c59040d0b6011244003c0000c2480f80b50546c3e03200b04604000500e03106503025041182c0070028560144032480124803e86050ba14501d030170ba0303510401c8002840d800c60840550000351041080c41c0d81100d07200c20b2080551034440050030b50b00201d03068075002d6050f100c402088009101402406500d881200f2074010785101414100700b01c444e8202280c2c00c0e01c446000020020746180340c40e60680790755001c0c0010740844034030380d50094960000905014011807510b01c00292400c2e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 776382742 1250 776381492 776381503
    0x1b04052211030c040b0903010209090910061403071e1221030504020d0b06220e1e070b1c020f04061e0912030e0319020109270b04380d0203 61
    0x5541c17900f041d0329281d40c6000f007402801002c4006801020181c1070015000d40012002c206050349103082c401030b038948654603031858100b1090340c0c150703228210a02070140120201501c7c06c000768500c0181e03642d58000c0b4043c2c1c01c1440c81c159168000f21100c00204000c41004d450500307110b0606220904107a4080781c0545600300001e05591296400300760580d4402803541482c01c198807081c2030382991014500001c003000381b0142110301c20000429850000c1c0d40c1103150b03680c3c07140080c1010034a080a01c03a1a170f405190354a0000d01c03030f25000d854089a91015000b100d2080208c5602c80e400d150020b03140c403803a410b61515140c605c907100800725502200102c15a1012008142555014034090360f4840003104a80e5160040712244401c1401c2c101c2b8500c0d0080c000d9a6280ea040c0d070300c1c8118815049050000d07209400e00c5c1400e01110740304d43c0c1004140c078001030302c0002c009020b031520307a480c0f15007005c0c54941c02940020f00140c0243da078010006025089861003100009a0b0000360350342d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 776383992 1250 776382742 776382749
    0x1406060607060f0902090a060f0501020f030307030b120303011e0915091e0e0d030c11060f0c0c06130c0b120f0901060b0a021f050c031b04052211030c04 67
    0x90f450b00f0001039501c009070006031540e507001d0422038590900141c3c080140485000d9148260041100082c2c1984000303200c6a42c0c00711403000c3d42c916190b40e60b0850143c8142640c02e03800c640051250800f400c0c0803c0194000c1602000c1500500c2c0e0a40310b00d04500303072586c0b2182c0c0e810f08000751400c0c1c1180b602a21021100d0003840001c0440300e4803d04c440161044e01d508807032603d05100390785c810901282000740800542e90402000b882c00c04140c1d040d00780c0b4588501d040d0300910000320034509032840d003604995901030460400e441e90240c240341403c00c854424034001070310000010865281d0b88040a0311240d40b146082454050800d14607481c000c0a084a011214000c1504200298840400b81150070207056584011f4903000e5540c0c4030f0689100c0700300e400c01c0300907080e100c03080c4260340c015100c03403c95915640380c81031213a1b40c816581e000210300b100108000980c075500d14011600d2166512410300c0c003400c41c915481c0450314404200080a1410410000c1c2e110550f0304941c01e5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 776385242 1250 776383992 776384003
    0x31207080103021f0e03010f0209040c031104090203070e0907110c032107140a053306040c200a030306090501060c1b09050a14070e150901180308071406060607 70
    0x20328000400403150740c0b91100c00980c16508e00b1480304112540ca030010312a00405403001d1188070790354a021421554640d41048000704140000d1040d259141c00440c0c011f0003602d040c50503210124002480b2510a0390403201160380303401c0042c0480814001c40701c0d150030840c040c01c0c6c0301040e10300c0d004101c5550a114205681d000800e00100704550000101c2854680c003100ea5070442440d001390f95005461900c1200e41403074000300c0c0003500c10b00301942018603c100c0f00e00d280d00c6000901c0042d20800700b0a0040c00507070100c01c1c885002c5240b64041c1081d590000381b04002c054203000d002c0b40c0320740d000092004d003084014081d42d50070000c8519519401603988802c0c200050031340c00350096507080512013904201c14412220b00c250005c1042c0c3c1d00c40756179815584c84800058510031092103140e500440c80000d070b1244414501c001e8500c200060510309028058000d07007460340d02003604101e48450002c2243c00a110380310801c11210402c400041c5004d0030f142000952034010140000d01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 776386492 1250 776385242 776385289
    0x20612091c0927060e010602060c07050307080f1b011d07050307060e130507080412180b03190f0207060b010801060e060a03060905090c01030f0917030a110c03120708010302 76
    0x3c0d0084030750010781410b800780c102001099103520308643d01400070f104040c01031188601092258483d40112208198021300951a052040e82d83c1d40c0070303800040b0600c01104c000e2001c000303039805c2c0d00c0c850030030050404000101c100c031080030441c0c15030302501c4c41911a80300340f01c107001e191000a840425610103081c100c4d206000300c4009180084542c0d0400c02c128100410700400c150000e841702d000368400c0c101002c007150158811a440b01d1103100c102070003a065001003000d40404402550000d6980d00384070a00c021260144084d42c0e65001d00e940c07503a40c006180303130074010144550301c1c0400003440c0c0030190b03500d42034005220100b2583c0d11880b03204005a0090f0081c00b0303a012034000c0120f0003060055152a04500380c641c00c444240901080c101211584600c03258800c0e5660b00d60f12600e0f803120441501c801903000e0704014206000396550344241103444160002924104103441c0041d0394441c06001803400107600a8a240d0a001e0b40303500600c0140c0e5a04841564018401003250 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 776387742 1250 776386492 776386529
    0x705040f09020d0f021f0203031620070f1e0b03070e0a0605120912070f021305011716060e100e0603101a040b070f050109020612091c09 60
    0x2420009402503020210f40059001c0024030381c0b94144a600841d914042c4400400e44204210700c0c1d0610100182c20400000c0c80d100305608980421540901e480801034030984245182800d51158040ea154005c5508111145829400101502904504100155210000c0354681c9864041d000000c2c401200090070244103141d81040c83c000144841803171552035030060226449203e42c0ba0200d00c41500142c41ca000004401480507141100e0901c2c0c00c2c5143c4900c151111006000c036482484400d541c0c0c101d0703030140a0580a80002081900c0d40c0b19160152403400e0710a41020000d000942c208100507a00441c3d4045601010340b145c1c5110071001c203044544410010b150765010401006000c80050f800b4107070002d45a03450340c180e802c1c80c0490388400b01da01444c8121a24081c081043c1000551003180c8050310a214000124004010fa800a001a00607403941035501c03206508000d403034001009100843c003600100368284283c942402070056040d80907006030800070ba070811 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 776388992 1250 776387742 776387771
    0x8460c0f150c092630030106030507020f0703020121110c010e0d0f02062e0602030901031503050c1908061e010902070c0512031c20030708040615031b03120908070504 73
    0x1200041c170040304199072581c546030060010718040e070394140103104a19003070f04204800200002600c0d0146c4078030161550710040d03c00401071111221805a440c0c000d42444c1d4410700024203010060480049551110030350a2494030308140050800c01ca001d120380841c0c83d401081c820340259026a108108504042958824405103079034003100300711100e03000624030381c00310282c1598082681c0520450f005c5c0074403542d01040d075002c041d08030780004410b40324600d000c5c49030324540c5040002c0750000075030340d02030282000740885131620040707041007900d84034418440300940588000b100031401e014051300ca0320042c0c20107004460213222401c10b1280743d54820000d0703c242c4151a01a412207806004842015041005104000c4590140890046d4040d103007904c0c40b03040d0315aa040400e1780c850300c030300016145902102086540d03c01c40880468107900c10030780310981c1c0210340e100300c91852800c506e021805820900400c5074000f018881c22101054070740c221001202d01180d548e81c1c208a4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 776390242 1250 776388992 776389063
    0x103020f1806131e0501060809030f0301051c02030609100f1a010309170a12110f0a0810151d12071208460c0f150c0926 53
    0x10b44c08021502c0000701007008040d005141a1001d9136a44542e07615000d0078141e4034050842c190242136018001841141003521503441d115000c1812a0849112500446d0a00d00c1c251180049a0864100409264850301461800d04c0e0074003c1000449035030f20743c940300c0c41c6045510504040c1c8030241001803007448100d184440c415190010364580280c10041c00c0042d00c0300038030304202e0411a01c1c4e60031641a0003a5441c84903d5a000c914240390648102d844400040c00007105804040021a5004042801040222583c3c4950700804d10294400310b090400241540c41480e40034655001c4e0b00000c2211002c8070819038103980303413407454549404580500b5543c10b10200c00420b500c10307010b08603c003c2e40b07507906900c003103008080031400700703000214910300d00408190380340354a000050300c1c0c0600c2130318103000e40c2c0540080842c144c8007800303070703a07403048628001449c41c0004d101803880302618406001070421042c0900ea48138031010381b9041c1055185108185d03000701444502d407038081 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 776391492 1250 776390242 776390261
    0x30c0314100e0c0f090c030c071b060e01120533060c070f080a0206070b040305210601090803031e06010908010c021612050703061a0a030b0103020f180613 68
    0x2002c0c0803002a01c1c8550b5602c0b09071952052054440022600450400030b000b1400350306d058803002d285a035400a5909141d12118080303440c0c3c40103030140444a542102100c01805442d40d0f540441c18181c0700042085010301941c4002318988428042c6034006140540024129140007103604191000811009c100d540b0348560055030001b00886003107070100319041510403d529009809498003161139582d058808000d4010004103c01070219060741c0d1440e6019219280580c40c000340b00340b12401910200d8028400c014000091060719031304081d4040190090100940c203602c2c1c48140708840c0c0085062500c2d01c910f811001c0399459110b09281006000d05900a01c86d002868400964406c1c00816408107400b60100115400d003030708420800c03164019000f01941c0e410354032040d000b0b041ea140c00c0140c4a41300c1814601c20f803076113401c402c01103014500d9031103290701d58014001501c2030304080520500403c103d10342c4508440702d807113800010964001d500071244120f0034005003a41c0d003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 776392742 1250 776391492 776391523
    0xc02150d09110306090f030301050f121504060606020a0209060f010309020604240504080d1d04060806090705151603050706050a15050103020c03161a0108071a0301030c0314 76
    0x1ca9190920004420010240c42c040d011107142c1e60f02c225200d82c0701d6000b082e041e061030b0400c10042140d031806680500c00701c8001080c0b1300408080303582180c9440000c09041b445081810100000d101940c8103200042c152400502034061a960020b03404030780050601d44a003a400c00300c01d14036482948200c859660140565640c1c0c0c0e02d4180c44085042c07800d801100384141c140c040112641700700d007035034101c0d400c2400801d01411450400d070b805800d450428503802c2c8a030f091841566039103015420080ca140702c0500642d00340040304a090203040d4200b54003c030900110901505001c4040f6241c96010010760300200d080ca1500301c2d29446200005841c460a001c18040c504126500105140d5503e0801c1d10016944200540a030700a00c4402020f5802c14807054600e0312503107880550152240814014051003941f14072650402a0030a08040e40201400d0001e044241d1041c0390381104644030704c4c2190703d1a520003c0c10061404020224002c082c009005040108140c104051121 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 776393992 1250 776392742 776392751
    0x120b0306090604061b08010905090c0402130911040614030723030a14010602060a0e01022101082802040b01020307120f090905040519020607120503060a14010c02150d 73
    0x40142d80d10b032400d0300d095901e989410f0140d061024180e0510b082520940c8908100e40c4c6404082001404003e01c01c86182c000ca40428250740d465100500402d904100d104d5012414484a002101d1143d2724881c48600b08000c00c9c0000381c0c000151403e490340b1505c0190740d9540d418821100c0b000960720320106c00580340000005228008050b42c89141c0d105000c002000101101041c69542031040c9800f5810010124181500c40d800680d0392100b804005031414688090212007031042400d00110080e6071070040c4840d00f824031450480b1b4032401e00000204c0e1488100400300b8004600c001e200c2c5a81d174480b280203900034010740d1802a00802c0b03003100c80341410b0b0041c081420704e440041c000b0f40e242f5400700303400315984100b43c01150810700500f0115900c00545c452041c581038181d0f0b22a50902c0f0510005a25034904c03800e483c0181d841c96101d0400d98140041f14500745c001c05030543e01058030501d980d130f005803a40f09203a0120b54042c081c0280c0c4400408038070880343c070800c916081 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 776395242 1250 776393992 776394001
    0x60106081602060f0a0b0a170726031c0b1f120e15060105190314070e060723012c01020301061e092d060513030201120b0306 55
    0xa0400e4031603840d40304218061919200100e07140c88003100c00a10480034100400d00c044902d41c40108014406441d178002103444009440902076454020103059100b240b060200070b21106a000b90111805088a000349605d1803a50300d038003403058080400e03090103240c0903a60801303800109004102030b12070b4042c2881c4d08400701c910400c40b02c812001c1440c19a01040316592449080450404000500074a030f1032a244502d2020019100c01d0404c034090000220300000340c48550020101518009001490b0404a18640100034208000c0c0100c110b0010801c0d2546030464903081c1d801190341c0d03048400340383c60680c0071449140c4621958a0034540514004400c5404050f0f00d0001d0310b2284c402140744203031402c1c4c0c4001d0041e03000150b1200c0340c01ea072848441e0700c1c01809030524280756400c40c0c1c1304c030b149040f0800400111585080f20327029030201c0130984010706003d00601d1400900d0074091541c81c094040051100a04200e843c5d404082190080c3d480b050b10020003e00340c3c1e800c1c4c1003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 776396492 1250 776395242 776395247
    0x12d0b040f0b190b1209010b060f0a0225180608120702010210050c07020904060b0d060c0e010c05030a0c05030c0604030f11061302010e061e0a0909050f01120c0305060106 75
    0x8031006058018002000c1c4510440300c20301040c002c0320700c1102d5480c64003170080509511410040c11845185d034030341c40c0641c5165180801f5241e8000303441039440d202d000c54000246481d591007400c892810b620380041c40042c1c205900e01003980c05a01080c1068402c0c40c0b4214001c101c10b602900341030044c408400349c4220610001c00105000f42c2c2290118034038502c920080300c10642d492006050104a0400141040b8207003550060040e000090240010390215241042d0441c0c103c1d4110759071081071407842c1d0464001200b00c142031a14007070449450351499900d11072407000805010040e0300030000c001c001c00131103041c04020010b84001d41040d140107804611802880c001081c40001e600039030900c00100c461041104804081910b4070719001513901c01c100030400c6400180030440101c25540c5120385000c0800d0780c008140e511208810020034142058114824503170034507050211090700d12803940c0c159812500400d4002806250944107070107264001460742c01154000501c868 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 776397742 1250 776396492 776396501
    0xf1d100207060207140f100210050c0a1202030f1b040305100203060127050616020904030e09090102041d0907030c08010b03070f0e180709090807020a050102012d0b040f 74
    0x2e4098003258103080d11100c0060048080030011500701c2c0071620070703c529203000c078402030006500380152040e007540000d454041e00c4044400c008900c00000c1d91052056002000c1c50a07000303040e40860031400c000c856000701a5000d0091800c1080c6500c401d082052200c08a40003903a02c04205d5200600001d04080a90411140b460219a1182c141c54001620241e421049152041c000703140358244410080550040a00e003112490001c0d4110016191410854010740c000c2c0c60305007081c20180100301802000402640c89640144001c000b06015204105008420040101890360f21410380903c1d1051a52000e030a1b281054800a5207103410750000c2400d5100390181c40442c0d48840340c00035400510301c1780a0701c402c40200040e6128501c40380b44068400340100791055142d40780c10350320a480302d2400030b035030226001655104500c0c0100c504c0c00100405c0c002440f004105402c41d4911005c611320348800208140075200107501e01e5800945a03110003030081000d050b40c1e80d00b00c0020b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 776398992 1250 776397742 776397749
    0x20d17060f011110090b090a0210030f091505100609080d12020c01150f060201060b0d020d0603120e19051f02070f061205361c031b050a0f1d100207 65
    0x300600003081f00641c0204000881c540c010f0552005002d001e00111300034190403000b0700c0302543d240c080c60002601072440d450031403d0444040b60302e060101094559050303d0384560140b01503140200980c01f4049004040c0c11464100094401c2e505d860240191080c0c03558484d0760751900c20030a0b0f9218071030542005aa800048241506445001c180c0c01c0765124040c2d046000420321207514030b07a1080d001803423006840c6c0004124160350703503511400702030103041c0440030801d42c503404030341c07410a905505c8000649010f00c44802d80b40401040c0d0541106200d201c46216051861840900801c1588020201e0f0103940c00c0761a41c0d404000c0640c0018170928501e036003410082800c01401d0894245407000c0958500700352501c6808260462a48229046803070086070340f07001e0a02010000001481c5080d140491121900a0300f5501000c403501c00d8418008144200241540d2010106c03251600504001c0380010000a074840c0308012410b045da805040c40300310410071a0302040c0903048 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 776400242 1250 776398992 776399003
    0x30301060807020c090105040c1101050106021b0f0d0303020f13152006150301150b0d1503051f02072f041e09030509120a03020d17060f01111009 64
    0x82e031100082281c070342c201c44610a07480850381c40140414613065100c40f0301c41c40c8604000811040404c0c05074255802680300c2d9000d41c114000d030002c006104100443c1c21202251008508521040068418124041c01034201039001c6480e11b080320f1000c040b13482e0140d401d103d1007511903a540c4540d0240d030810b1580700024294285d114820103000203600a92891280074207500e58031085020b64800345403151903850b40d282c12801f4810a03d249201e4003900203050256030324004402c1120654600b88070010310070148850420120344081020203815007540c485000080490708540d0281c020500d001d041691151601c0820421001d0904100c40c504c40301c1459445440007040111241c00840c40c000307001ca4482a4a60346182d0301c0444094800c0c2802c508028110021480b8403014440242080e80101707810070038103404000c032100c092058070380840000038803d4120708401024141900465208001c201caaa0086100c070560131002310072500c4000000d48404003401361100d09941 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 776401492 1250 776400242 776400257
    0x60d08270604030f2a030b0f0601022109040f021c2708130f0b04031407060e0d0c0e0a0209041409060f1b190f0918020901051b03030106 60
    0x10a0504405071001c5a4129443d610344c61a1038541c4142c9040c2c0d0b28200450241c4807440029112000d4200b601440c0503000d2503c1d2440d28010011401002a24a81c1558064041c010306140e0300381d151580c408005d203200f5168200e40001c03030050b002d80c092021055002103058441e29124484880004480c4c881c244040d007034521a5400401440c0c903600c0c0290a00140f20020840c0740000308045904096400005c640c4e4940c040c007a503a480d0481c48425100183c01c001748046800310082405010780075140c4146400006414841d00c41c41c054007410041c1c00e00c4041c8406204843c00504500d0842211447e11000104c000d520559069100c1c518080c00007c0f816281440c462180c0e048400802031911801d51400f03040c41c1c0284190200551a01c129803011075102c09001041040300c0c046047c8801d40c08046c0c1100844102d400410030022420844015410702030950740b003026900581e12150140102e41511032008018000c98020340481c07005c0900000841c1210b409596062 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 776402742 1250 776401492 776401567
    0x605180c030109233a0c031d0a050303070b040219050a171608010f0e0304180e0a120201330504020a03060f0b0c0f150a0c03060806070806030c01050f040b03060d08 72
    0x11035200356004081c0009030741c0203020462239140c414035100070900522605090303a8a4000070718662000d2400c0302c068010310140011410088417a40d205180c1c4070401c400c0e03900300000700304203030554480d500d00460080501c00c072000050050f0f20000000200104140c0d03128081c45010b0903030703481c0c4e52104900c0e0606401c080340c0040203030f078260f682c03c1c0d4164070141147c002583c0a03050382041088640240c10148002800110541075940215000800c15402c01130079624503113031844d21004c01d40e100012503403008028050542c00d8810413500141c86042c55042140100705a801241a42d400c00102142c0340180002422030302000008903910701000d0703640703181c4903403e030321070032851480450114800c00002e03000105140800d240010701d49584400c0716113807603410b44020300820380c2c2d4010300550341030500800034050000e0824030302c1c1110400d451100c9100d103204100b0038007030200124040e50f0356603504441c2e07150046a110b88400400300c148203040040d00350650320010840d200c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 776403992 1250 776402742 776402747
    0x2a0604020a150e0405071809052d07110c100504091d0a06090519080306100504080a021c0c18200f070f0605180c030109233a 55
    0x4141070382d40d07071100c9194a280d010b00c0060080503020344241311402d801c3c50300c408102c10924004088411011803d41040c1001c1021802001d50030000100c046020055200c0000d0b11030307030822202c2c07a0110031003171003078525402d00156441c502c0d440041004003214560f4408045d105946010300104103c490b0304ac10100f06801e03001d4240c1030f60300030ba03602c0000715210b0780c003500e1250f010b40705a81b2082155160a000c250010001b02e44030200441803203041e080640300c1e20011001d50500610f014240503040d070740c0d0b100c1004020f100c1d1031186a511a0000c4140b208500e445d4040301e8221182d4a07101190b064100c1059010f08262a1225400400d0300040b5200c040364091b400c3d140c030349030040210050300c1d0301549040c0d910089680d4044001030052003502e00c0780c8600c00e2100c3d03685540070442030030f001c20305521030703c2a0304040846010409420b0102242c42200d1024010240e1120300c60341032540585107502082004503012803402c403840c090b0040400880003416181507001c005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 776405242 1250 776403992 776404019
    0x1b2307030801120c031b080c01020c01051e040b0301080a1407060c12030b0a0b0c010b0904080414011e030203010501140703090905060307210323030c2a0604020a 71
    0x150000741074200400000480503050344686005803410700c00c3c01d469890755840300c45001b80c011030304810703001c0400c005081806200500c1000b403020f008141d400c400003c2035400388144140402c4040d1110020108501c401c80c0d0080c0301e034048042d01d03580d4441c0f0454507403495038016604814450001d40d00f020300414058142d641c81d80720304560090385c1e29001c00700c85000c44c4000500d0340c2c0d1a2802c0d000c0e0b5401d4185001840c6000130941c0e1030010340d40c0305081d40c00301ca85680c050082074003808001540b42c01660306a1304010b82ca520081030103001200d01c18480b542c010500d21541000ca01007590580046041e22001e0300c9502d0751a0401686284d24403501c50082c1c0000c0c4ea18000b0720080000350425a04280d0040440e12810740700c0d10403509502402d0300d5103115100340d0030000101500f046640300001d2540c640ca2404d00b040201d6188035220051200481541c00a036640144901201325a183c2502803044070000c490a078000d90b940405480c26071003440d200000140070040e840c030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 776406492 1250 776405242 776405257
    0x8030a090603050a0204171e030906030c2d040e01060c03020c01030f150b07050106060f05070f0c1805040b01090203090d0e0d052e060b03040f02041b23 67
    0xd800030100d00c1c0103800c4005103c06461001d14070307000c1000088801400c0d10b000010655030002e400380b00020700b0244900f00307001c03c04803c1c5400900000c2e9460340c0d841d050340e600694404c100c40c0d458030080000b44e54205050319070320920404102e0350010a6429021f401610090480c80580341d0301e0754800d50b5503c080700c000130010391000780e040700154030070f810200280e003d0190100320070b455417052105500203904602d0400101003510f400784000ad000d040010110360a2000003a04e07001c0c0003c0244c031a0402c05002003103600d640500300301c0b210802500400d1a1050b502d2000e05e82401d071070292000303460544101d030600c000415518614801c90780690207060042c0f07504004c034a82520321280080c042c80c0c0c031200ca81181c80c042034040c002c42291103c1c160b400090401d0801885c0c10515101031000c103200c0c640941401001c05501c100e942068009507102201c2555200080142000303020000c074602040421007800b90304000c0c1d03040c00864083d0050152070030320231280241c1c052044d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 776407742 1250 776406492 776406497
    0x4051c05041409131e061b020106051818030c0a0c0608090106061e02030c0f01091b05130e0a050f07081005040503191b0f1205121f030203121308030a 66
    0x8681c400240400c1c200c03a10000315004039170105243c640780c0d0000c880301618400c100e81c01801c0d00c0c5560960a210720703c0540400c43ea07881400455181134640d50368028030008205100d1a0080074406042040d2225207550b031048609010a0f0301d40940340c1035a41c816900412400c0e03001c200701c00c4042c080d40003a940e42d507a9500503007030f0b4096032410700740070780c40404e003540010405000342403c18400c4100c50301088001103008803c5242c14620a6408d540d015041c40440c5400e200e265614500703590004100900032900ba2051f00d9001e08224103140010014441c1c2e4481c590300200202e42e01048510700380554080703c444403104010341e0b4041ba4000c1c0541c0080000d9040014400140018000140390001d541031000c0003103244403c141c2c405070307618a51a014803040105a01d182e454140b40ba05d0070504103001d1400102914802400749052403000070600800341c00800d100f04001c54005040b60301103c1610008040d661200ca0a0240b0b2001450040b815000000c02c65440801c1c0344d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 776408992 1250 776407742 776407771
    0x903092c16170f09120711041a0d06060609060f0504050d03050f03040f020319021003240f080606030c09160c020a08030307082d04051c05041409 64
    0x70344201c144426030704011014071002c1e21259000c1440b0b0000140300d00e00c03981c0003401c00d050011241d8600b40310240c0a03c00050708001800015a4a12030b001c07042c0b00646010907076942c2e4518220010307100e550300542102201c0d0810302071004030341201c42101c41645440c141c0c0c5845000071614420b034000d0000105000300300c01c000b5401c0ca441400501c40c0285803050070010490014411944140c1e07098071403042600721031080d45818001401c00b5010101810308105695001c00c220003000c2900304c050654900801110b0b0394080d0205070b810250310303100b83c5d2803912456100503880ca00e028800091043c2e000007040c6007400500c914400500400140340c0b0780da1401c80c6030061640100f0441000f841e20840c600507154905176001416110000d19180c0c03404240050203d54010600d4590802203a200040c80c52414005049446000d8000015a07240e084c5180b8101942411400d80f034070045180300882e5004c800303002034420f0302d110b0000325101c000411840c00001e9403081145d1710b00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 776410242 1250 776408992 776409001
    0x5073002010c08070f02031c0f0501170f0601060801181b1d120303040b0721060608060d020a0b0c0319112a130e0d02010c1710030305070507090903092c 67
    0x910300d405158102100c404501103076510020341c140c50007030333000b030139581140c0410381c1d040401840615952120880200140e615084000340b9958040c407902010351103e6001e401d40440c6074210001070030740c42d4030102107001310440040c1680b028907a1038042c2484001149198900203515104410b02413001350b007592030300d4941a10401340640342105100884541400e000015003460311111059040000ca144c58580d01504040001b0309851080c2e908070580001642e545007000151100c0303200f0b80c0d460b4144c02000e1443c1d40f160441d403078121400c00ca110341d9616880080041c2000d4200d040d03800e0f051410400411841d07402c100c9006042014804a005062116035400303050b101c45008560804616180340c100120305080100603511003903000145600320090a0341e840030007121010600d40045410303011344550000604000d400203014090120400000d006000ca8141c00c0010104e03520700500340685c01c1c4100c0301e8000b855241400d0304180c201d0710205002d520004040141d48 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 776411492 1250 776410242 776410267
    0x304020108090a1203020a030b03010b030706110c13020306032103150a170609070f0b0909070504050a0603060305100905060f090f070602060612030a05073002010c08070f0203 77
    0x10000c044103a580b08884506011540c00304503d0082d11135030b02d006070b8400580c0c00c000d09031903050000320b000e170b030621858092649000440700d0440f0303128034181c3c0c00b00403449007a60800185203400c50340300b05850b42c101c81010044d4015030140718100e08880302c0480100b250000c8842d107002c5400400001d0001645401c1d21000010550f07900a01c5202425280c080c0ca04840581440141007175002c041000400751080201d440600030300d406104145192468040241c07068030f107128010144500443c0c1000e01038425200680001000300704a0ba4489100a000f0485440182c510303110f030b660414038810341846003900b126000310140001d0b0752144044102544041d140e900e041c82280d090425020013480300002502c4264003030406820004200200c0d102000c0341940140c0041200c8040306030080121035280b640040e50b4241298116183c610b94804252000c0111b08006040021960306600100c500c410310b81b500000c64407548801c4030380da000e103480c220141e0f0041003441907280 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 776412742 1250 776411492 776411507
    0x4020a0b0d1d03090103050705130b25150f180807050c03061003032c0118080105070c1a010f05011b05070e012309040212162403050c03040201 63
    0x8114150100b01c054107a03804890118a508048030395801c08034100d501c0d507078140a4250000445e152650500740b401c0b00d41c4120040910592460800001c0c4c1d05c0c414010744941d05421900c008202c81031041c580c100044040c2010320701e01012450100701141004e01d41c0b003100310041c00319080f25030b00340c0b103507881c40c0c6560b00014041d11341e4400c0c03071034a030060f43e020000c0354420301030142c0b5850100e02d9840c002d00340d2000b091f02d01d480c07034503140074015002c0c8250110030001c00d000d10745103060840200c02c1e103103242d07980d0700280920b50800003048040b0360040080d07208644900341541030494015401c5107914001e000302c01c0c4980151804100540c880ca4115100c88100c040282c00d454180c0d560074940b401d550310401a94420800421564102d40192010b1b0b9500c0122411800e111200080468400402c004d101b008080b03807100f401c410400c896000303580112499618a62129045041608079013810010f150480d02c01080d098424080c00d4002d00d03804400301e05589581c2d0045d00c264 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 776413992 1250 776412742 776412757
    0x15080604150801020d0f0506090a150e040b0105010f0f12050a060b160623040f0309080f1c020714060c01090b07050d06050901030201050a0807050f210f04020a0b 71
    0x1a446801100260103001c002000620003040016940c1e122000d401094030100840d20010524220400c095615200d45055000a9402d000030391404901c103030640a00054101c10701e842040c100300030400600b40c408030306a500c04d885c0c81d410302019803012102100d14a500c400000c0b0641d02525800702c46402c02030300141c1016000c240c0549a4002032003580040504001d10340c1740c1a50a01400301300d00c286040c130300c02000750340d0114042200c020400500580010403c400d68400d800905201c0d50442001d800c3c5101514400200c0118041c0e50740c182c0800040e182c4901800b810542c1c0c00041c003041103908402d03005044071205010800caa0308105807044003552940302c02800500b58003240c920445041d150951212610b01c08202140e149401c01e5000e11810401400541e8004003500c004003030f149055500c0e03584800c4103d50030302a44a0302c02c28110007054118101c140301c1250a14105070300c8403115290b4034044d40041c0c81d801980c02a41209840c0010b02c580a210030081c07805 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 776415242 1250 776413992 776413999
    0x12080703030f290a05090c03070f0c0b07111516080405070f121104060608150a03380c04180b13091209030302030a0c170a0206090610150806 62
    0x9111103d280048205000c10100c0c0008190720b00ba075007610700001c1000c044c28040d1032003152450013010302640c5110203010103040c40710542040c1c1c80c07180300d00f5107401001e9015240c44507608144402409010004040d0042070013420480052032024242144c4241444031180b00e00d09034503203081d908a903000e0300c283ca0500905101058404281004000507d2100c3d01041580d010782841f07898208413040062040e030511808001d400c2d4000841500071b1540a60700810742000b000007000e01420303a06c018418211519411092081c0e1007a0000000c1c0191140c2c069403190401c0840c0003008551003126031000744030901c030ba10680c2c0303581d403412122444001291000303000001c0009245d49414a0080c0e2603020410030002001810b0040284505140c80d520341903a0b0082d4590152020000070030522401403803d000500b8603031542807035208000350b83c40101501c001d441d580111508135151051401049482c4803c595820842d401a1004c03007100c0058201200c5008010781035650 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 776416492 1250 776415242 776415251
    0x1d01083901140703050a080112050703120c050109081b01290a08100b040c02030306090103060e0c0d08070c060915080c09040c170c090a050d020402070b160912080703030f 75
    0x21400b40240080800728001d803070755a04e803200903170020404041600302080a003184c000e001c001444c005455401d0342e038050741c0000462030f447d004994004542c07001800c070358200b41400f000d110480c0004e04480d030f8880d83c180d043c48444a1000e098071030001c0c480441050b5841010303440c00c00219500143c0d80004c08000d1101c0c0e4541ca114078095101200c800001d542d01250700311881c0030700c552007504107640065420751038910b0000b003036100144005002c0c0e6440b070b81001c5808030180a10202c2d8803006120030315550385401d00c0541500010000c42c0c2c03154407010089a441d004021160858100d8882c0c00151008003008540042c0040d15808038030b801405180c0031907442d40218110310031181d0f50320b140341200407110b803541c2501500d400c040440c2080030041548542d24441c00746c90081d24100c9820b091840850001e03c980b500180840d03542d88240040b41340b4a081c0000164402e588207040c69072200400050140007450003040004104000300c0080d0207500020480d1a45550005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 776417742 1250 776416492 776416517
    0x31a0f06040306021810020105070210090308161202070b10050d1511090406061107090b0109050118080313080106082a010e03120a1713030c06061d01083901 69
    0xa46c4030800040c08409030f5107500800c00b02542c101b0083c120310b003200d0300034003c00c3d4554801030320b4044080c02001c42070142130038102d81c59000d0788c0003440c0e025000100315a1406035060402e0300321002c0e6031024844a00d000c3c0040c1c5883c064000800454220200031704580f00088081700402c24011204d01011050014a0142d900d510071440285180e894001b0350070090107401d402d010040d00028120351401b206044145d138070610b11000c0c3e50007803e00c1161a40d881068040507001d40e030205440b8072001a2002d03503525011482d00841d4007141c000e0180b20b807036401c0d890b00c4041c0c401c008200c3c48070440321600340c00c10415030f507051120181001d40d10b0741c6000c40401e0401d0404908098240c90020310030018550040302c8900ba0f0b5120344441c15282015444501c0801510b9405020041072484850030310055a10240090030482e016100d00b1317004070f5007400d4030242445468a10700074070490011150b031441d150321160b004d0301010b070700300c03901c49200d00b4a145010510074104280080d041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 776418992 1250 776417742 776417749
    0x70518071b0510020702090907060806150418020901021204080303071d0a0308180102010e032b2a020c0d060e07080f0601030b01050a060c061109040c031a0f060403060218 75
    0x34210f80309200300159492a042c0180040038a014152103880d900c0080104078403039000f55040d0700220103c3e40b20070071007541c508012590040e500842c1d464280241d00c540811b82c90750007030482e41800c0e029220074915940700755025000d144149403a5400800003d0452440f821b01d03141e007640070f12043c207141c0034114003045184030960011201d02c440025000ca00342e604808a0100d090240700130301c01100724000e01c64903030003924000022901e03102c04101c0d203a00036440410300042030178002c1107031551444c410a403a03014410700c0c000d4021103001c41041c451002c1102100050098043d100c000020380e142001050490300c02440780c05011004100c2c0c1505100e49801064011300500031341d411030800c08015001030744001e00c00e0044100030880690442d0b40d46140a42280c800a4072400c0300d644003076680f08103e101a40f040c604400c0880b000e41590021000070030022104d56081c50400030f00c602c0c901016280c5901ca00c007408200b000426a0f001403108440c64182c1c02c03100002c40c80407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 776420242 1250 776418992 776419003
    0xe0d020d140d140403030912021c150c0e2d040c0509030c01081b030417041d0106020f0c13020f0708030114060a05042c0703020903070518071b05 64
    0x11076a042d0028403590a009511103810395a200900508a1502c1c0c130b10395003d010076501e0321910706414800c0e000c06c400e656640403054199200c1c01550000190070385404210007001d01100b042c413910f01071030103500507c0341407030b500004070280c150b01c0001d14240382c403c0138503c186036a011411070305020205644079800b59040c03900c0755458035622080400c0405041c0040b03005c03040c1c10800003a04120a0200300c0c4401e081451209003034030b80d26111400c0141140e4403654048070a85800207000070205002c14407011034154940d0692036a0340ca40304103d03140e801d241c0c85014164400a040700d880d10341080d0490b00444248001494004126178540e0150800c44081c2d031154800f0004020114500707600e6080c410003107800b50b00d044410741c40036110b802940551001207984a01382801004108142d868080c1c120000000600d8078070401800384d4400d40c50280070707020308100006c0600f054200031007075504411004030182e40b03501781100d20528001c800031000c04040303614008104280701 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 776421492 1250 776420242 776420273
    0x430022413080106050f06030c07080409020403080c061501020d1d0301050c1b06010f03060902120a0b0916150f2003030105040c050309060a180506130318060e0d020d 73
    0x81201c0c415190824990071224240d020034066038140c42c210055995010031a0b03070108480c00f0041e01c50b14507043c08041405240c00041941c1c1c40082c001c01400a0400a000c440d1181c0c400c69010740d803540d09852903415112507176409030b4080394070500341c00d000d90450049503a07004410781d2800214400070b400c0d40d605590521062500141103540341804000c00c1082d207404500078601035152107a003004449541c032001d03100035a500c01160455694640750803041da002001c683d012090b90522205000080d554519184902c0040c015081703081c0c410441101d6095a0764141c84d02050402d480c04400d0000103000c10070000042030354449046884000800008000d603140c0d8100014001161054503e840500c0740c140208003905e100042c2071940710410080200703c00610500c004480d0844410042841c00303040100a00c50081c28a00c0c00c440f40a0f651741d59421030042110264081c0c203010310720004007152041d070500c2c140741844105091002d08021280b1031b598861400e0382e4607000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 776422742 1250 776421492 776421517
    0xa03033206010f050307080103030f030e010c080a06080a0f0b0a0e0d08041a090d14091329090106110a080c032d0405040f0e010e0304300224 62
    0x4007841402e50340164402824051070400da451400d00246c042e26200051100500304000314000e550064441c3e0005150f91a1020080c810103501ca0000740c01c504040311869419071406e01c00041050000400d1400b02da00030207512020002c40c8c40342200e100d00208407084c1c807a00c60216107440e00781007010b014589040d0f40c03140d00c14181894805950800c60b10b00c0b0b511607200001344290524045142c0c13961603000d0810440303c1c0c00d5126000c4c04c2d030140f10a8141e011920024100080d40c01d60030440d00d00c802d0b400201c80c10f4440b40e10340f02c5104036900d41d00e03801c62a14401400345a0003014001c1445101404a900c81c078083d542c3e031012a84484507020702900082401400101c4001c0d10042002c040c50604035400c03d001c85600140c000c621481e03105580f12860000b02c020301d03500102c0e65000750700007404601062080c003940e170fa005201c1c410744445d566507098a501044407440d01342c40d0442c03006000500a680801054907890001005a458003a80b0b4142d04c050200040000070401c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 776423992 1250 776422742 776422841
    0x1203030a0501050108040312021309150f08340306380603070e0d08070f02010f030b10030c02010b03100b15120a0519022a0a02030a0303 60
    0x31801401a00c034180d1140d8140318125041c040000e800c04000303003a9000c102030040c0c4070590b1040c07100c50078100c1d92001d03e1051070116594030313400581280100340d408007071a4051031682c866409645024180e84420001c1071449440d40140317540d41c2c15140103500c10700311011961a40c64200485e880340882c0c03c104410141010f16880c800f07126500e0452030043d90b154038498034000b0841610008ac8000100700d410f50001c070b223559070070b00707031108131608245041d8691940d80750400d040e40e485a0283c3c00308410000ca045c0c581d110740180041e001e80900a0f80515982c0c0b50240c1c040e0a003548224155501c40c1c1070301001c0c0d24200402d520110034003e010a506e922182031084810208070f520344803000802170403100f8880030b007042c0d41000111100003140d40c0c60f1102c08030343c840d01000034000a40001382d070720001121021000b50f00502a50148490411624071304e9407075605000c0250581c109120000c04240a54407020130700720300c0580c0192213030710400241000180c41200c258a508003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 776425242 1250 776423992 776424001
    0x20c07032a0602151f03051504061512030309020609190501030e1203060d030e090910060504020c060604150801020c0102190c05120d14011205010c0906050d02030a060302120303 78
    0xa03204801c01401940041c003d0f140503c42d8021000740c00600e04241d0749805210380221001d0340d04d140b401150014240c88403414032402d04c416941e4140c4090f1006814903d003140c41c00302450103801211280044121001460f9409030082c0a9540c2c0a0360302620034050850305031104820650308802154001e100e09044c0350015017203400003058140e9690044254814841500c42100e402010440781800a10f0152508541107104140d400f50400c41040520080b03160028030440340c0e17004078600340311146d02c4000384002c0707018450007405558010f2001c075036941410707449a102003c0000749034898580303419645081e40d01011003000d55070b5001a0940304046084000645100341d89007079403004201e81c0341c8558510940e00d202c80c000300c0018140308402c1031a4800310140078600302c40d40c12036a40f001030310b40c8071001c0300c4169200d50070305001034801e45c400c05040c801d8840c1e41d00d41c1800d100364115140e001b9000100102c4c00590345d030340c01001681d00c4604402c00f0070f2188005541d2440c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 776426492 1250 776425242 776425313
    0x2712070609141f020309010b030d17160807030203060409020a0f0e0c13260a0605060f010305010b040b0a1b0606051302040f061b1a0105010201200904020c0703 70
    0xb01101c0d19440f81c010b10034004a8200c1401002a07119094401580fa0349403084041c0c01002e0030000e03aa0b041c4543c4104450868000c85410079003850388980c0c690541c2c0304003400c800c007855004844000384000300001e43c81802580a9604040042c0c40012204240d5000c502c4541c2d8640281d8034401e50f180d01000300e0000303604d0003580a9503800d119030901e00300c501180d400c0300b0240210b0801c0e1103101c0c50001c0f031564a07040740070800014400c4a4580d0030030300b0b04000131301080e10400e010304038202c8101d42c99406400b0340c41c101d800145561746014030742004480150000400c240401c12080660003148808150703008a082c000d82001070324600c0c1500704024000000703011002d8a005120804c158000035503460122400303420f015414042403030550328510000d0030010503082200e001d03480e00441c4071620701d050303075000c0e0002c100c0d188910849061480d1801c49013426004104041d54140c246a005440e10000000072202650b40326550442005034010740b403061030501e15224045c815 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 776427742 1250 776426492 776426513
    0x110a0c0f0f050d080703050702060d02040308090a09090b1b09090a0c030b01110706080c09060a0305040302010b04090c0312020a0507090902011805010203120c0f0c060612062712070609 81
    0x2401c03190f0507007420199448800e00e009100015040c084c02190b25401c0d915440220750404e40e01c0c080c01c542c4c454032482e00000e1604603203c0036004400f0f911020400d40d1241c8241ca214540100c2407090a82d50980f101820805c0c0b40c2c5075810b4200d09001c0800d840e29000c10b81400b6a807148008180080c1d2450010704441c0d00880341c904218000101480207540070036034005036001460a590f0740d64501010190303d115600c40c0c550440c1c4001199502c141c1c0c91b0b0b100306c1c091846940207201400b480c00030042501c0901d08090041903070080100000b500742950100b4507402c60050341c00140d000c0d1520750522203a9070001c044151950f0461342150b03480407550542c00380c202d001d003446500b8600001d560b405407110f05110180d00c40301099954495034145e03210008147d0060341e4505110000c00d407214421b54009006141000003d4508800400e42c184a00070301050b42c0750343c00b02c004000100d81301c010481740d10703401401c1001c892400e004d4010a8000c2c003404010441c00003d02c3c1207003910 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 776428992 1250 776427742 776427749
    0x8010510020a0b0708091606020c010207091e0209030f010c090f060c11010c020f0301050709050a0807150804030e04111216140f090306010923011401110a0c0f0f 71
    0x541081040030700184003ea041030b0410442e1804d8400e42d076660f010719140c500d4600c500c00c040e0f00c580b00c2c0091981c1c3d0008c0c1c907a01b0340c50280e0030344045641e03d002413803e449803031483c40b840c0345260045d41c42e020510340c060105440000c040301c03040d00c04c02290714212010080384000154240c1018040d5910030b103503001c0204020314211820091036200c03115a4640010140d0400106000701c2c410f5554a08c01c407080c1e840020020850f0b410710050207000c0c5c000720300c54070707020b00c0d031b1341d01c000441030b20104015007203e000e07181c600050440400c0880e00e02000400450901003c0404013116490398441c105040c2100302d44590744015400c148080a4001003d41c100c0c140605600210154000f030b00c590112441040b150b00c030300a5000511103400742503a0f0070303003600c2414000503259880340c02160100d1380780ca104207180c02c841c24548903800004d00801444006c1b440c0d40c40800d502c101041d42041071000c0c1522600081c5036940c0480d4030059108141c1030700c2c03201e024400c100b81c014209005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 776430242 1250 776428992 776428997
    0x1903020102190b040b0403050c011d19080a03020901050c0a0f022d0f040f1107031b0c0e062d01091e09090320030409150e13061b08010510 61
    0x160303181643c903040c072010b00600041c1140310400104d000c041c00b52042c2c5010202510090010200d0f00300424010440d0480c0d110851103000c0a848480640e0a214001c507a04120030900c0c250b5803107800d078065440415542c0c10410b081000004884003884556075041c03080101c035200d030301c0c03074010020702e040320540510200504451041c1144110071100034541000e803103c55114100c0c0c0c0c00500108030384a03424014904201003c1500e2944e00002c0c40d270036102ea01da01361607084403002c90300300c4509544001c00d00c881c06201440b030700d4138280030154000c0c4014002902004006003550081503022105900c0000c0029040420340c3c001c030009020b00603400725032031032440050821001112a00c16100e82c03a0340c07954043d090502c40c054660020103049410306a1a80f10320626039030340c0c4188918249145420039003500c0b03016400c00c2001321503001f11040229204e03803450760400007480100300c45003940e480d88100700c401034240510309035803691243e401c07030741c075003418001e0b10504030841d17008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 776431492 1250 776430242 776430283
    0x50405060a0807050c0a1a10150503090c0a080c0108150a030f1a01152d0e0a05090a0204050307090e1c0903021c14012f07021903020102 60
    0x460312140c00351045250300e840c00441c581c071480070a640d54800c52a8031100c170f0094526035024000b810b1000300c1d4007040182110b0156403129031810301021a130060b10002c1c0079280403692030902ca00050b42c0c03c0180d010660719198548070000701404065845400c09401403405100c09607080060258801d51040080700038080343d400244907007000740002012009118580402d000a10700340d00100700d810b40c0026050b503103a0081030540c00c0c040d004400095205a55030b500b000d80c3c10318120600d80710103165514401201c000756004500010800d400c81104100091960344080186000c0c40340c0c80310040e0340704d040c0828181441d00980150000a0402d6584081d07900e00158001d42800c55a0519210400c0c01004856103d80c030b510103540942a0403040400c4104a5801c0d240a40700d216000001c1c01008003550a036541c20202518000c00d03800b00004086100c044810700c000410030032494007a160f40060b504107020b885011800c41d1450060045580400041c400616411448030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 776432742 1250 776431492 776431499
    0x21010806100513270308010e0a1a060319060905072c010c050a0c0305010f0b0f01080c1b0106031209060c11061e070302010903020706140d051f09020c0c010504 70
    0x1072034000c44081100e03403550303640103414000134000c020080703a01e8521405600400b5904004002c2d140c207004040d0b8011203140800d00d805841d121340300c0203442c210f00303044112403214100b007502d03003000705084040b209249070300c00816040e105000140c000391000140e2410a800001e20b44024084a400c490000f50003c1010f18800014040c4081d024030b0a2500d202e001e00d400c80c18920108030040016100050210070000d040d000707410540f40765201084003800c00f004110249116403101800f00300b403400810a0304140fa0020200c45050001c124100e05000c1000707400c4501c1580251014441c0c1d03007150040c01d42c000144001007810703180590a1551680b2000717444031403040c0d658881d11000402481d00442c514408183d80000c900c000d89403600d90601a01810382c03000300b20b0060140c034001264481c0142043c905060556801c5230034001c2540364031009000c043e00060301904061400395004201c00f4402003d44a8043c025803a040400402031030140800025414002c0c01d00091 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 776433992 1250 776432742 776432749
    0xc030304180e15010608070e150706091e0f050610080d0509180117060708150402030405010917040614071203020d06031506050307120302061b210108061005 69
    0x1c0895035802100190701c965140d4110b00d0003014400841e15404014000920700703811450071841101191203d0310310790103110401107220400204210180020b004860204d14a6030110400c60301c00d490fa1107501c201c110301080540d002e0102110485014100d5400b002000d102c8180c006a082e0706140c0340b6824843c040d5124200d07252404104407000c90304042a80d2211551001020701e0020480f01c0d58581070800c1d900a90021500380c18415040403401403407250108502c24131141e401e9985041303400c0e0402c070295001034026102c643d00c50034510046902600e80c0440c0c0b00c1103049581e500d41c6032800250200402030f51040340740070b0a00c0084049040315400000394015441e005941d1500c440390070b402829a40c0000e0100d00c007518a1400180440c1d00c03010a50780c084003100c142607603443c05c8414143c50050300038016048440406d554074980b104060607000c035100c55500b031250130007001c400381c800310100e2070402e151040108140342c024030540b90407284a000b440761560034217010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 776435242 1250 776433992 776434019
    0x40e0f011e052e0e0a020405040c1e051803071e12080d0203070314040c0501032403140304080313031703070207150908010e1014040b0f0a090f12020c030304 69
    0x42200da00340880c43e0003050b40040030450003910385508407942c00c3c1400f0742084001c1d0070600489000d24508014100003c0c00340c1c040360a002419105462020b8101a00700c0e030b04d4000705803841c40e4003040010300225580900000b0080c002040d031100200d02d41c42243e0050452651009000310800342c80c06001c50103002c02c56101c1500042d015070b494a0303800d8214001c00c450980a4a411074200c2071004010740110001e0440c0c500f6607090012201810085030f00b0034581c040d0040c0c040058904000040300b407096901301c0402e010960b41413a58074504181580d00288444080303101c0c8039414000c0205e0302e01c440c00c3d6540d40d08070b20740c20340c54600c002950b200f481e0300400324594252842680050300c1240da102c00f41a4000091104007907071101307542e9032460190785141c11030512026580c003000c280c00c058455500801071000c66240c0e4061003004000242201d028180c96040b0040418202412484014810700c0c4944591011000090a10303100c0030002c1c0c80ba030030401082180007a5600c0c1c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 776436492 1250 776435242 776435281
    0xa0201080c0d051602060a06060806040b06210a050109020403080a121e1b02010b010c080901020a0602040e16030e03070201032f0a02060a060b1602040e0f011e05 71
    0x2056240e07038980d280d04840c58001c11500d406a0303400c11003000045102c0810030004010203400b02c46035510380840c12000d590140c050040003565840c001601881e00381c000303241d58000509810319082c22103643c00e000d04c60500d0a100c0300c81c0310708140005c1100d9482000e0041001200442c240390855480003014031860500608004158180b0600034200c7d80c054241d940d5648490f0070040001a100c401a02c048848444040e07110307000d215100d40107000300824a501691000e040c001c0c1e5599244254108a00c43d0b8118420300483c0c800280d03082c80140058101c2c40c00c0f82501c1d240074164921030f0825103100c0e074105414940040710201e400401c2d551100d9090802240005000e5000101340e052a450345042c22003041d41006a80c3c4c2c800014550004a039083c0c8605c0c0d80d0300c0c2550f00640d40c50341b10785d28034288104101c440b0300304d41016420800c2d10003040030420440c0f020585160003042c4400300c4080e55034510418290940a09503070070a0f44145044c4528601028800601d020410 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 776437742 1250 776436492 776436497
    0x302040207230a02030114061012020c0d0e040c0f051b0f120a0906020f0d0e040209040c030501080d0c02100c051c090e010509040c0501031109030f100b060c0a0201 72
    0x7407040e0400481100c011540741c0b0340c00b400300b12180c410a16990707401080d8000c2c3d0013540784c400c00112039490103480c1c500c51a00a804c964550700c0b43c09046070701d42811041e4106496003440080782c2a54188000b5071a00d40341e5a407a0455a0703440100802c482450b802c44003448080c1c1c50401070142c2003001d8810201101900f103141c800c00d10750507810400381d80b41345c072414041e804481890805002c00340c01004003036031f074080c0304507240c40007640d54800c41d0303105801c0c5601c10015240000d03c070710000a00100e01034000341c144404000485c040c0e03050714481c803020030f44030070051003400010014000c0045c0c180c6421606001203802041c0441c0c3c1c00389000080200ca1922201444000c019045640b03003001c00c41c80640044000080003154a40250350711905910000112850544001401981c2103a082003c0e030345070100640c014100c2e080d400385807200a00841507941d40a0100308142c0a040010780380094070940070034201c9418128461240c40c0c00c0c081401100d00c0003a4007100700b5820b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 776438848 1106 776437742 776437747
    0x504050d020f030d05041e0c1503152c0c0c010612020f04051005031b0f010201060819080702100c060509032b0f050708090c0312030103020402 63
    0xb560a40d01c03950062041a0100e40f0381d911458115101e0040700e005000700015140030303455850300a031201052000700708070f6404013040a40d000b841034a82000300681d40c41e150208074030a4000c60300d05244444c0007200c1c0309008128078504642a41c4d8002540c6000503541070b02c0d5100d03620900065081035070020720300500a040210b01e550041c03040c0e00c0b44020800b03020041100520034001c9071000440020306031824400c5900043d103202210300195101d109008800b036218201904584c0f40c000f04024007a00450105140c0c0c142c0e1054959102aa05000da03042c01040700207580301080000f091112600082c07501e258034880d03003061001340c1c0e5950722070340c69000f810b900800325880c254003581200c3d10011030042d44d004603000064800042d44450b0125581120030788003007800c0e6401d111016104001492981038101c00428502580541440c15804180301c02802907402 = true := by decide +kernel

theorem cover : BRFrame.Cov 776258992 776438848 := by
  have h0 := BRFrame.cov_init 776258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 776258992 ≤ n) (h2 : n < 776438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
