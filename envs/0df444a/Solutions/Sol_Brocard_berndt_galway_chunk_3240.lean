-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3240
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:04:53.166002+00:00
-- url     : https://prove2.me/submissions/3add6c3c-b7ea-4673-94d3-f65d83c37ef4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 582553956 ≤ n < 582733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 582555206 1250 582553956 582553963
    0xf03071d0712061419050d0816061805070602031c0e0a060516080906060303070212010f09030e100f0f1805030a060506030d050304170306010215040c08010608030702100c0203 77
    0x80442c428500304680440c800ba880d08010400107002d440294508200c10f00d038004034242d078002c00b54041048407145021541c614082d14641c3c0e05102c04201c1080143da40b4000c4402c1980104004071980001c0024450107000c050000c0556001440c81c2c00c4100102240c0407154849140c5036954503d514074500ea410000582d0080c2d000303004020508007100c164180c00501c111060024421030300150603040e01282c2c2a0040034050011800c010710380d400c00c03203800b074921200b071295036940704081415415402403e0481c6d0003500c540807080522000d1151440c14120307003c0901c1040c81065030600e03803111b04405030090911f442200036524215001a0544980c4101c1c1d040c480c40c611007050014503403204d0300403042102210070719100003405803007500080354003614101c0010a1142d28800f00002564000c0052050b18412031800042921140b801c0e5401d0b07032264032491060013584400d228041c05400c02e500210304242d500d90009914646003401d40040140b003d00d414110345041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 582556456 1250 582555206 582555227
    0x5010f0c060c02010e0c1507030302030c0c0114010e06041401031202070e160f1d010c061118030d090e0a23091c14030a0c051e0304020f03071d07 64
    0x1e03038240603840e10b100d00280a4401c01c2d10002140c090310701040500e15160000120a0038808040c50070101d080d10244c0003500000e29008507007104002d145500d40003841000602400f11100e00d1955050905118440380c005141500807403810002c9e44603090003042060450b0f84c842900c9801d8004e0100480c1000029401421842070710014440303481051172220180035130030303550410216168241141c40090501052400ca01c03071990f0345c50154441c007010480e00340118000b0541072080c020790407180e406001c403074903609034540b120005860240229000307070b003451801590940c24480d075a03a1400002d05401c0c0050741d0707031800030307903445000c0040c50040d80169003c500c50302e040040c1580300e0801420302801d0316445110224105e00910942d1140c11200c3e00d51800e5960380d210070402803007031030040010b11a0030300020001450398035003101840f171022200c984908061040c001c160240051841c4280c000d00b1041c040140d07028041040131182503030518031074544038402c0d81c803094003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 582557706 1250 582556456 582556463
    0xb0903090d0c03020f060f0a1101060b072006040501020c0d110306010803130b040f0306091119050306240603070c050d03020a020d020706120906020409090f0507150905010f0c 77
    0x50046071080c002502224403c4a000380c1e40b0305e482042d40802c0001620510503904000c2c0c0f020f101c04005107100c4e00e03650810000386030000684940380c5070b40c90900c0d0072500049a00c0801e990311689131000c45201c480012005a0b0130900301802c0c0300000c2d449008401c40140a0034004c4550400c2c0400b0064410743c100024050350100e5840c2c420068581d07104010100c8100907481c0002102c003081000c0704c0c12201c940e20780c42881411a517820016000910050b5010310640140700603c0e41c2e256000319442003840895034640d4540300c1070604142e001000000f1060f00000141000340f031500203003000d03c404a0700c15689a070703284800d451351050b51401034414424101c25400164159004150f0780c40250211024502d0b0408201d9490030907006640008951036601c1512164580058070518415100503080644521404044900320344003982e50524200705002031003c01d100701c002506420398200100c400740900601020b655108090400210b80e0300ea980503482007540b00c603050391 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 582558956 1250 582557706 582557719
    0x60201180b130f061b0f0804030206150636041109010c02120f0a03081510031a03121b15010b030403140309070503010608070f1e1503050a0c1b0b090309 67
    0x5c045102d184910041c0c0075980200c1c9000032075001180c0201d520318400e96159000307140c540c0c0c6520042254460645601d030300b241d03081c07000c07011b6103104110148141c40a120000324820501c0000f45162800051440c016031625013000c500c0603016044441410003070902241081c11480407407500201c0310350303203140c50250664082e000000882d200c04924040d594644d000e40320654a081500400031050b90300c50f00616010329428000d412074070a40c0b1014030103424060a020110303040006290801c4c000344000134076182d03941040100e030ba1840e8484030042480201040c0c0d50b0709124411b00840224103000300001f8201031166203465007540c00c11801c81d171a410021881a030717621540c05018807035420b202c004580700b04001170300000c8640049004a0f01031401c018400842e1800f08070380502140c0c08408125400e0340d03200203402e0201941c0000322440c2c0380e6030341422a07000c60324510400220b0141e03445440b15035140b000000b03404c50b550701000e40781d20050703510307610901312030300d40144 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 582560206 1250 582558956 582558971
    0x100f1202031042020615031603030203070b070206010b0301030809060d06030b060a09020a0c0b0406090203031b210a080601020a0618111002210d060906060201180b130f06 75
    0x43c050084103c0031a0844803203140f511500b0360441c219141031003020300503440720000506044400c8031580d103102018096a4040c0025100440d40821a400c02d80143e400012404100003000c0903d59101180b403001d00b1495050852015440c44188006000c006011032505002d039240d00440d404581201c0c13003040348541c0d903c0e080c192041b04450b164420f401903040082c190005008503440c2c00c10641e10140c0f54881ea68600e030b1640009041680e45940d142407180050310200028204554041551104401789100702c07071a06000140d040440042007601144800d452819203161504905210000c1c2e900d510042b40340000280e0043c0020f406d008078095801c0d403482c40d1246040c040c12801c1075010100b818000840341d80c03280d00d40142e100500384030101080c19551101110300400f031500e4041c0c2c4100340820395000342c0050030f4041d6141020007003140c09100e00d071007612580c8105408048507031100742051100900309501150100d41c17605c00c0010000d05103d41540c0320390100100c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 582561456 1250 582560206 582560249
    0x303120b220e0d0f11161a07050312061c0c050103270c080106060206010e010506090d05030309010507030516080f0a1805010203062d011b1202010b100f12020310 71
    0x1e040e0003401340801c3c84507441c5205074202103245900c0d900201c3c4201e158a02e810791001c030760307030010300d07840721108091121000151090008001c92440380c08140180c0c20044108000c00c4a4208080160904207451700b0014094100502c1117820908000445019618546400d0101c89040c3e50b0f01c445a50700390000c00900a0001013610507202c000c204154031450305036680c440a000d401d002c2e4080300d0041001e4540103004140c1d9000240030940040e401c0e41c1c0d0f00b0300c1c5400a44000407180d44900800c00303120340c10310400354403d444180f02001c0301c031214400781044b0741c080d00100c01e49400c1c400103407203c40641c00252000c4043c0959100007802070a24600075001614000d10658005008030306080c1c41d9404034003440303250309550100910040055a0200004140d160320000140040d00414680310800d60b0407142a00041098101b51040010b20078101d1101002d014054104480fa998444070181880710084001a80c94803124031070a806000d581c40f07040c0800d8000f0303222058 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 582562706 1250 582561456 582561467
    0x615030b1009060801060f0504110c03030c07120309030c031d031219033e0d140c0f0d110903010e1e0a020f09060406090f02040303120b220e0d 63
    0x116145002c0030401a42c941903054280c65081c41242c45411032000240068603040d07000d508260840c9000501c1d290030b5840040c2550001c540402c2c2c41e43c004a00001800340e40b800303201ca091640e1604000d0700100c0c0d03030054481803106038003034200700d4110009103a03060140c1500000010003011500c4103070564540080e0399114800c90a03ca8500700c01c3d030041c40d4041e002d420400c0c120428002d9510540941d8601c00b25403100218a07000c000990024800c0e82c2a00280300c595510b050109000341d09143c00a0b04a42c003400010015104100981c0c4800303d0ac0103072050000801d001040004203803c55403050b0048081c255810351070030308460301000d800078040340e1511002c0884074048000211058442c0c0c01110f0280d08003440303094107102c43c03404524503580701900420000700107407a429242d08841c0f83c10701024070203a00040900c14150405484180d0080202040c000c000b00030300414690880c0c00045076589150410040319a28160068032404102c00129103c90380900b100410 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 582563956 1250 582562706 582562709
    0x31503150e010e06010308030c0304060618020408010c1701170124061701050904080c01180308091908070f03111b0a0608041101050901140301090507090e040f0615030b10 75
    0x901c2d0320f0841d08100051010413203d0499070030000241c1180d07240c3e40c6205a41c0c0c00140200c40c802c0d030365500825000342710321500a1b20500c40b0030060719141065080d500b12100b007203480040c0f090b0640c3d80c1085080c0c200c5464150b404541c2807580c2810384510301c501400324640e455070200074007001001102c031100071a004664040e559410039201141074084d01000030301a0f1038001940c14005408212642c0c0140011541c0a000103000304500064444110402c0f100f1030004403d0360078400b020000f004105182260054a0440541183c0d0350003810303c1602c0000b0a400c2104030705900341402480342402c0c0701c8861003a242240c03032103880c1c488501c0640010700e00c60021440c022032468828607000784074540c01001c0e122301980c0040152900d4001280c894100500c0c03100c038080416800001c2c500070b15006402249505044401810804254008480002400e0100804101c120416445503030304298000360b00c031066660b454401259810260000f2210007d102104807040084030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 582565206 1250 582563956 582563981
    0x20c0c010f030902041e151203031d030c0708010e03090a0504050903120f07020118050a021905041e0608030a0206010e06040b090103050f060606161e060c021b03030f0a03150315 78
    0x2c40703c05621040141c02c659405080c03804040c078200580002d000364000c2092560a9940c1010301c00be40c900240745901c0705030341d0909030704070319410000b411090048614425601c00a1402d100541000c901442c901c0e20810b8803403074030303400410b40881052013110040d8084215070b184a203451804001007240550306e8100541c07070100c3c11046d0705202515070b1039603548000a040b01141d65002c00a2900e091403069131810318441d000591030781d4912600b1000031001341e800c1c020070341242150301151584d901495040c1c004100c00304110340d01140796419100c102c0e0094241d034840d8404200104543e03050b154004040800100c01e0107000660403903410300c96011102280da801c0107119070f034001c0c02c1101500fa20b42c40b141d00c00007813130003e91030340d419102c44410445408545a14043d100070f0451540507030004240d41502c4aa00240301071603140c10350086281080742c107801121846205050340403d507591004640e0400c5842a000c000e542201c00422000607400701c2d01c1c001d05000c2c4400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 582566456 1250 582565206 582565211
    0x2030c0c06070f06050a06050303191407020303032809080c0c0a080c0105070303090606030b0f090109111002100e070f0f080c090c07200405010603020c0c010f030902041e 75
    0x8025441e20200b15640243d01045483d080c3d034a940ea80d9016140242684000759214000480c46031410400741070a000784d1818142c0221030a1409440100141d070f00c0034600000704a5403001d41c5002044130340165040900803408580d070340c8000c01c0140c1c841c0c0c08400150402c02030205100041c8080d0005070280000d4a1200c0a001d0801981041c14071400034240c2080542c50600d40c0600d02409145029003008603450380c40d0769801007264040d8200b140e01511103014011240c0c2e203041001e0307210300e07080b0080007090f10035250b10800440792400316204141c200701c004a018402c2c0550100041c8696081c40100943c10881d52602c00e0380c000da6484030381d1b441e0300080241038042100b0803142824041c00201c4004010b00c08000c20003481510201c0b42001100009401019005295000d140400440416102c2000113881044c0e0045041500501082e20340d83c201140c4d0380c143d184242065403510700400c20660203040d40c3da5000e98000c3c41c00c1c80a06152080840b5001d4402007031a04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 582567706 1250 582566456 582566473
    0xd0b180c07140d030213060f021b27040b060909060a200a0f12020405060f090a080f07140901060f0e0316120c0e0f07030b150304050c0301151203121b02030c 69
    0x200c80c2c41c88150348090058ac001803901902c00c3c1640590b0392103110141203040300c04400100030280300c451807074808189030700d04100024400000d004640000b0101c40610040c2054100b040e600c2c00d000d00720340e80c11035a5190000000c900c1c0e4a900d80e00c421031002203074888501d208050b01c00300982c1c5480000c1001e603101e800440c00031748222810b8490082c08142845401e107500080764015000990f00449411000709001c0d1042000d0002002944000c100403400c210414101602100e601405244000018040550003071502401d0000300e2618a00da0b54211000a01c1c0410070301028101044000d008181400700001c43d00f400c0b030282c4a0016266500d10780c6118143c8121407030480300350410f0100e401c2d00c0c0b01c5c0d003100c1750043e00104000f017402c1c110446904198415102110a0b5011841031078641c1020f019040600075100b40b000161072800307010303110f0102050401403c2002100420351580d4031640301c000350b900342442c80d201882c06654065a607510603010340240d072196054 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 582568956 1250 582567706 582567719
    0x72a1d06101b080c01090503041203030b040b060d05070c02100e03150907050909030c1501170703030909360b091c1d0d080d0b180c07140d030213 64
    0x20881c15001e020071040c8000303402615801c0f01034004210140c49552581c1c80c260209000f0805040541020f40400c4207141c0e8a02d0050111850000114011404c0c00811050341e512001500c0e0207002d204800700b1250340769442100c903000080b10080d803000c49000a140d41503484080d01d02155029401c46041c0c0c1e901e649191a0004115040030300c030b900c00034007400942030600210b50458070b880c086a0504031070500d4181030120541c0035108040103840101306d150842500c6a01c406048405003100c60308644000702078030f050b8081c402c20552181400380c5c0049001c2a086521580711b1006103a100c61949222195070075010246c414189690124041c0075001c105804400511031500505c03004e18401921100c0681e0000680c0410481e0100b0f016140d2662018005114164240c1d607442c154401c082240d0140d0b20f80c5000b9080305c4c2c20103054040071100c16401c800010042512a081403400f40e80340040112003035803e00403030481c3c082403605900030f84110324120201c107041d541c1b10310 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 582570206 1250 582568956 582568967
    0x9011b080420011103030103110f01051206090c13030f0302010c081005091e0718060c030e04020306060f0d0c030506180a09150204060203070c080102072a1d0610 71
    0x440c09070202d10030b00710300d01040b1070910000441c1c50040c140b100f0501000b041c514115003091f80b05968070000351040c00031901c2c10200041e002c22003402d01c0fa00307140f035480b06081c1102006028030b000ba5411004a1003041d2060151009020704071b241c3d141440d241d20b4070b501d0f488040c400c11800756007003140c80d1601c0390046004c01e12404507464080810361170201000b40000000d009524001d80800c2c060243e075000a89003842583c803515a042c0c01c00000b080b00074000c805c1d0784100300300001c0c10401d000180e404440c140141104a4015031030f5198440000c1d650700c905500ea43c48140c0004249800404030b800040800005071420401541d40310f00740800c20081d161801811010400040c0c00b601655200100050045130b0031070700c1441e1210003500f00d902035001035002d6403011812408000f2042e241e00042c000c0c81d00203500b001038590714860300948042d103951005582280c8601c45039407107404400202880d02c4101b170200d6401c40380e2402c204040d654140a4840d03055075070301490048 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 582571456 1250 582570206 582570211
    0x305010f1e0c0c06060e061011070b0c0c04290405190e0a0b07050409060803161e0605040606170a0206030c0705070f06180e0405030405010305061809011b08 69
    0x81e099010903400800200c004201c5030041c1c2c000c1c040a144490041821340c400d05001c5c041c10414120305040802c05c03c0040c07103030002e800c000c11810840c602010440420242c0c1101c050440b040e0302c409a03000c129080040382241d0a422500d4500e82c0441280880030b40d1308441600e810240f010f0441030140300c180d40c0c049412a8a005100246003d92212603000d1401028640d0a071500d4030101ea0301c1e5041405e042c2e07106c20000710041414848007945210f000024201c88004500d452150343d201c0100d020054006854840e0080404c61a04d0542d41c2e07108070103a00c98410801071900e0718081c00180b280b0700510540312194003400c105410009204817000d034000f00388904681d00c042082444da070120b40100c44e140210040020101c103180654009403042d5100c0d45410042c00c0c00c1401030504544c00100c08403644002e000110740080b045409446080c07801148a03a00e0070081407241c1d605000031100345034100200242e070340c01948010f116a100542180020081070003c44040009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 582572706 1250 582571456 582571481
    0xe1501090e0613060b040507020304170102071a0702100e030417060712050c043b101203270e0c0708040e04021f03060609051c03110f010903090305010f 67
    0xa0080f82c4541c3c452042d40d005103214400c0411408a100086402e0310410b580c0f0b1009a40082020701000b034108500c03103400200c100085003030242c1c0b92600500c0d2101d00d1070000218104401203024644240a8000007080b201824003280941003181c0e6502e83c4940300350320f45144070840d040300905011580c01d01541c2155188189403910310f0000b130040c800588104070001007003100007203483e800307a00c00d403420181ca81010207481e04041e400311001d1181004615a4031400b04010106002d000c04605a03900962104100d0b20b40340b809980803601e0708414855050000d10f81c1c2d174220342448440041c1e90059000380700d02e45070801c0f00e074402d02869200805070041030000b407000103100104181d00900080514144030850380c0030007044003000240000103500d8401c18420960011041c0300181000e6441c032024a51071007003402940d03544900241041980f4400d0200764034104400205400d0000c0204580c3c611840d008c0c020060900c000c440755420040302c0050840b01e88595150b42c00da = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 582573956 1250 582572706 582572713
    0x10305061626150d03081b13170a02090f090d03020a0c02060f1608280f0807180605070b06040207030203190302071a0103060b031f0b01050705010e1501090e 69
    0x740301c00d000c0c0e0382c14020210600706000c408071540e40d54030b00c070007004180c0c042d84030310300c882c1403d40104c250014126058000c0c0e180c20060740c0d806c181401000002c4810000d4034001c10a461000c5900b02904c0e800081c2d0300038015018003030580c1210001e240940d103981d0445c1c08407485803005a00760300482d81e8803400720327822824850160400c0c0740140381e1020780d10400341c9020f02e209441401c2e040c040f40190785040d0081007800030b0000300200100842d80720a01d080b000d214a02c40240a1304010510504110020780441d0308140104400d89500c0c1e1908081c00249072159802016504018800d03510248041c0c0803428a0600c0d00c200c820303064159014501d44110341d03111607103090394482e0102c00c042d401c2110002003802c25440f031108850000603441994918100002612084a1400d00c2034103c2e045070011590700c10800e0101120f0b031103021842c001d4a10040e551801f5182e4054015401d00c24001000e200c00b10b01d041058200301071048030b0f40d032510710f0700040320340d807108480c521760 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 582575206 1250 582573956 582574007
    0x7030809040b12280c17070f050f06070623100f0f17070e01030303060e0a021804271209120b0126030d0c08011d04060203060301020c03030103050616 66
    0x1071269400d05021480e134840490044160f4a0042d1a1200c1d400701c0b2404503108200410913405100400040056628504000e810071000401845605052a1080c14002204410402a80c004c0385071820b07014034000450b00449084151a5402c13203940002010820000c0307903a0b4041c0c0b070b040054920142000608504100098203082c140500d4a81c1c0d80c07141711400102e4817110a51035000e18070070783c0c000c11801c2c035202c00c42002c03100c05040d00103824018040c100000e00c00c203c55100c2004201c401044c4cad154001c05440c0c0e40c0065282c0c00700554000002e050911580c1281a101070189960705202207589441e0040420411a4014540c072200b42c010001059a901c03a412058080b2054029854800d04030601c0c44d0b20105d07019050b16250440c10407003a0f0130ad8070075401001000c44078610103280e907408440b1b05034006c0008180d150b01101045403a04e096040e80c0c00f030740d00038003100e0752541c40742040742d6240d0003151300042039900400007600aa1251303011040c417100d031004240014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 582576456 1250 582575206 582575233
    0x1208010807080303190e250609060c0611043303140c03040c0b0a1d030304050307060c06060509010807030c06050a0503010303030504020f030d05090306010f060e09041407030809040b12 81
    0x83c0b06130405c2a2060340702c20584905190510158030800d144074601004c442c03001c0500c1c0d074400c02652021013801481003040044c981c0281c10115a99032140700002c506040140d0501c0074060364006400740a421080b00d001c0d425006903207041c00b0300741c50458040d10741c064800c505840030b41e40600c442d034400c00b010900c401014809160014440c08135001d00d0340d240c00c04c48145400c203c0500300012101c1110038070422400c10781d54454441900918070b01810680441c1e59880b00b071080c1000c12019400500501845600403c003804000b000c8481d617582d1a01a81c0d65901103010035190581412000501d1601a00480b80c08484c1c948880f8103580c40c40d24241e0007043d000784140d81010640f8580c1041343c1d002e00c024401c5c101c840d02c030651544940b806161070314030305030061800118094800e0042c0741c0c12014190039100101e58500584c0ea0b2850403080d00c000c0704064130300340d2140e001c01208100c0008040d0000c0841a41c2c2040040c0c4100100320350342c1000720802c1c030b040d0000300565007107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 582577706 1250 582576456 582576481
    0xe090103120c081e070213090b13050111040b13233d090803070206030406111b030304060b010302090a0627080d02150f13020f06071208010807080303 66
    0x5030b0041c2d18107414040b21a2001c043c03100c80031300000b044440014071808500e08250146081c08071124200540b180540c0c8000c0c0e180d83c083e1540060030020b4402104100094100c135901062101c80c41e5241e82c0e40780051001a0031103461010f0907941450003254900305030002d18445a080e900700c900071092141406905a8029040c0820700302d240d000b450040c4000c40d24502c160703144902c1c5003545480940080028100d0340061a080d04200614000742e41c3c0c0d0401d490708103400c40000101e12400559411451082001c2c054446001400c0b0720031020f004405503214070b004901c1800100c1d90400114100c4c4518009141d11402481041c0160b51244d40109244c10391041c0e00307180280c88000c0c490102410b07600c240c0c03083c0e1060110b416010f5041c0540c0030000150201d254540c180388018503226a40245803d0070452126148420355903040060b440301400a03141c2d542e1110302c0c0c10580c0101c1403031014036010504000c00084d08400002c1d003c400c0380c400801a41c115203a1005a104 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 582578956 1250 582577706 582577727
    0xd020d120c1403100801060503150f070c0b0901050f0f0c1b0c06070f0606170307060c05040e040327060e040b0607020414010e090a021005030603011407020c010e09010312 75
    0x42009a0400c16129400c0b64020350148215064440c003aa03c0c01c0d40040c25280c0d1034005074000d80092000000d450310749051603801081e55040000c180d91041812142c45a000b100601a140c881e02440f40052040d80054024685030300180380a0b560306c0350400086100713136510b17041e6030003c00c904990201001c0c48002404d0b07025058030340d40d0a414000800f15041182c055079460202c51411040043c54490440100781104075002a01c1c0e01c681340035140d003e68030001d0506a20390b10360100203446002280c02a0810042c040d800f0705041c24020200882005440d01d9030f00c1d02000301441d00901103200b821261250b4540036030014210910000d801e282844982040040c0304840050f5120301481311400300406021845600d0301d50301c2014981302501014841e00901040e1000da10f41304160a9514032074145580d4a8031240301103030051000e05104040200308405001c004e5601013080024010241d98240081d06050f04201000e5020f100043c250490450411142801845840c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 582580206 1250 582578956 582578981
    0xc020108100503030301080705011206051c03020f01050c0c0c0102060609190906020a050304120809060a050601110a03090513150e1008030a0c03120218130603050114090d020d12 78
    0x1a0440d030398008a4130b981c0080c3c00040054200c0c0c20140000c1d644403101c840140d20709001440518500780200e0080015420031040c0d120801c21060701303160013044003500c2c0c400d1f850020006440d0201b2020501e4011018a0040e4050440103071981d61000030824050b00c4000d142892940782d426660030001e13020310a2405443c1c65200f0f80000c20224070185c1503504050f119a5642d20345807514855030341102c049181800365140600900e004d0002e500d0354030130395585c80000e003a15503900507030703040c0b0f160a15802c1c1440b50400010401d41e02420100850324150307941b040354244014007000303640300c01d0300c054410307070303c0d200100b003c0d02a007807100c0d40001c5e00c024418491901e0310400d0341190b00549000d804030320300e460440101640400308801b4050b03c0382086042c890300a456100d0084480c002d82c0c86010141e03160032074400c490b4031107001958000020072941e2006440821038142c04c9414007958080c000c030b045101400030940b500c20f5802990b80b00355090200300c60130010103505e0b40c02c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 582581456 1250 582580206 582580231
    0x10e1e0f060901090c12050a031409060706060e011205030726040905060108010f0b0324120a0506133302030c0d0c02010c020c01051b0706120501090605010c020108 72
    0x91101400074030000c1e005075541400032526441c20b090504484456078003d120040010030164080303000030441028295151a00304181c051803401d41040b4004c1d41e1b01c040c0d20250005070001000155071102d0221008100101d0f0261b07601c0644011821110300c0c00b518980040000303800040955602000164460005803007243d550b150000075500550022400745640d20305002c041e6820602450040013503425404e8000d0030a4224506030001a010401d80b0001502521076040c140040f5146404040d0100a00c000100702195603100701e02026191800361001180090700407100207807003690440d581c1e01c2ca046a00d0a1001d030072024411215286201c4504410703c40000d000443c000c900e0140f41d01e031910900d9407118115500485220705682c544420420095000305110318000401d0910603181c0312640c1c805032074211006609116801120b001241d4182c0210908e96000224401001141c1c0c076640c03244100c809a01803d800704440b45000300c0158805e141595000b20003600c403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 582582706 1250 582581456 582581473
    0x91212180604030f02070b0712051b010c23071a041e0f051005010f0501050702150403061e090503040b0322080306131b03090f080d0203040b0702010e1e 67
    0x2203420501c0580d02100050b60812a81c0b205a60400254000c2c04040e804245441540c2d9141c10080d00d211407010144080420700c181c1c101c14103012140140900e500134009200300e404000c007444949420000e040c140500c0041714001540140d404150340010807441000d03030717000105103800e0001d20450f95101000001c86548604800080c000340c80307106100c80741100b0b80b13019402c0c80c03425803821118901e41b0740100201900583c50204454080c28015501c00e01d03400070988100008094841005000500100b00001390340440d600902502661610104800c0390300d09556002c4006011507200380400d010112034070009541182d5003c000d4407009001c100085002c102102094070810340210070031280d814248030382c40e207800d540101000080c3c5592038000c00c04400076016420035070340380131010410008045c40450240c02070800350311001019580c40103940115412110304418002007002c4500500481d910384202001800d81d48441c081481d04903107040e8941101445503000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 582583956 1250 582582706 582582751
    0x30222080303011d04020906040b06130b0318031305061b0f1b0604061704020d14030c120705060f06030c040606120e0c0901060305070302040509150306091212 70
    0x800800030820000a180c496160920201074001d558881c00704402c441c904120041e914010b800d0340c06a0100d500050745100c11000ca180d6008011000c40311245050003c6a284420005984116244500469019400c00321241c90b8040d04620910000705c14000340000d1418402400300b004004045181005000d6641c620309120741c17142d18616040001c4514020240d204503440000098420b10f15113884c1001c000d003004581c0d858852921210b00c04101150b0f24010000c0015030440b080c01000e52403903a9058881e4003215030810140f003405c03001d85440d0500c41c140e035035894102c409051030307a458a00172901a1801840264580110b940461030340e96148243c0020305a81d50300d8048001c4884203030000c440b251a034404070341d48500f58640007541d43c5e80d21141900c1c41c615001c182911010400d80180c011500401c0e4009504403c00c0411002a800b040c2412806c800b250b1560b194500160303203d03454000c4460b18a10304001c01c940d0030082c00c00d101e802030102c40051032070508105 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 582585206 1250 582583956 582584017
    0x2070204060e1009020c030d02031807030c1701051012020112020c0a0b1e0610091a0307030c03150501050c0c151306050a020a02130915050a0c09150302 67
    0x2c200c01096100b690520001ea0b44603160003001c2c1c41c4155007180b0b00000c2d054220b90320b0041d0381c00c0e0f200c060b400000044007909000300c2e00b9003071503940341141c0c8da01c4c0c2c8034a000c6c55014182c1c01303000f41e59406407500090240c0140540c5008010920125070340504002c61410ba4060404059040c4403130720040080d442c3d4188020711510240070040c00c20f504080c40d0110301d1302c102a114409010700f0280c080c4031101c04d0f100311341d0081d0007103c84011144c3e050a00741c410801d658000342c171400011034114200d0740c24000440c8034000956080181003400a400d504455959010f514201d40302d00080c401540904002d044407801042100c40092402002600c240000c00c0302d0700c0c0c0701c1c201107140500301c000c00001101400343c50070450300f04070700068000c0d610340c20341304007a04c50402c0c21131a07403020109a0044e9240c680100038840c5d81000307541901d02401c4292201240c803481c049a24401502c601042819254010640082c00041c0002100030f0741007009003a520400d0024003080c0000d00c007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 582586456 1250 582585206 582585209
    0xc021606030606030606020312060405041502040303030912050c1509011113320607020d020907020f2e0507020f0a03090815040305070221010e0318010504030c06030e010207020406 79
    0x41d940481d195061040060503140755521a5080d98424450b4968010042403660b0340007000341c8002415a40b24108200c0100741d91252010341440001c0100c03e05605400c042031803130080c500090b41306071541d01114180700b850403050054015aa035201032042c2049202d0300030040e94004980501803078203041c500d43c0243c00014072101103c0040041e0402e1240590300c03803181c041d100380c056010145c009000030340595198404e90001030030104550b941c43d041120a83c015104442c3d42c5400a0007a54420400c4580444c61050074a5075954800c10115024500280048000143c82c419100c4010700005801c06040d80110041140d411001b00300b80c5c49a58000c0d9142c00003a407130074402c2402c4c900002c0201c0300e19541007040001103070b046400c40348a00c1d81074418600e005a03406240400d80c408171190304265091048a10700901c0000c0608070465001002c248078503000b80065481d0310803071200410f641e00364003080020038000e921244480031000000f600e04000e540c0020300301d5205 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 582587706 1250 582586456 582586469
    0x9060a09080910030b130e030f0a020a06110703030b060c031b07091b090f0e061909060f0f05030601060f0c0611030f04030e0f1c030e0a03050706120c050d0c0216 71
    0x30399034040d001c1c0c86c0040044030001d901140070441044582c00c103130313140c2c49414444084071030000f56a9580a1080003607400d05500014200421001e41c4540d2070725501500080d000a03003014154103003490300d401203400702814500154584080c6980c0d81e25400380f500700304000790296500004190388580540103400c5032480c5410040040c0e000b0140c40d9221a800c0071b03142c000ca54805202e1a18103400030b98000000315490380c800c0042d5a00d140e1615440e4000d030910754101440004c4100d90802c0c503100360756a54511440d89920b910906585903824454030b00007840442c500c801d100d000f16000c0200c075008540114058001d070a400c0302950082c0c8000441030f1200c010003003415844940c902103100c2c00c9070b4040c076030b004c2d10000034201a0781c40c1c14203035210750201d1072000700b41c01018102c6050f0f001400a5001507030700e00b0701544a401ca8071501010604c1019014544881c0e4070514491041c213480b00c0c1d007442c80c40e030524001040765016200946c820440b080d10380300c44100b0002c001f07049 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 582588956 1250 582587706 582587711
    0xc060a050105180105031e160602030a03060504090209060105030c04031e0c1d071416050f0d051e0a05120f01053d0903080a030e011409060a0908091003 67
    0x3400043c0440482c908801c140101120780060061380c0d000304080082d160310b00706400c01da0301c207254894241981c0b0007031803450b0b00200c0303000960180c01001906801342552020803441d5603410a0000755001000000d42c410541000602c4030740c084c1d805560040b038402c03030030390501c1d0f00c80c0d40394501d40c10101d42c851000307070010a50a0401c086441074101034080310702018041d0341c443d0301003280040c000d0143c00c1840001d070102e00402d181107042c1c072800c0040300305003030005005007801900c0c1d007450740640b00c9500a503c9644201809882154100000050354203020391a16803545c403107400c45104142001010009091301a03084410b00e0701522040020420b1545414104008100f00c5948040c1c4a0039000c18508803070303490039000640c1c500900c403a070701c0300741c40c0f540440b07001815404c01048600007154000026605074804841e002d03c640c000c01400080100c6001c8903076003120621407650259001a05100064004864203072140981c641403c85002c00a4880d050070300ba488000380d07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 582590206 1250 582588956 582588959
    0xb12010204050916050d0902010e031501050a0828031206031505060901150305061203120f06030a020d0609111309020f0d08040501110316060c0807021c0c03050c060a0501 75
    0x1d000789030301341c00100752400d185070000c2c520b070041c00d13a01400c041c3d40340040c0e80e01443c10559006125152285100800707654040d0344500100d03810300701c01e004080c0214030480011980d03c50025410765856807aa1040c50020b6084000e46850009c0d08802c0b400c01c15224a1944d84c01084d0240d07002a40c41184000e42c0d5420700316190007240d02c0140307014810300f80b91004000d00c1030441d410301c0101006240c04079560f43e4020120340c40d00000071211085100c00a041c4041000003800d56000f852606000580d07911820304065441c006075070082e611450f10101b103000608103600840509102c1c00c2d03914a01440707200002d04080204500003c81c076140c240341e00c00c5181c030303a070100c12942c0115540e02101c2003a88500c030ba28040c07400b8035030510140d800080c05810042040c1c4581b100d0208041394509058a003600140c0000140c075130100c0c250700302140e2041e0000c06e0003a451600a41108541400c4050844418002d64019018410300300b040e120390300d20500240e8410428500e0103c0d665 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 582591456 1250 582590206 582590209
    0x1a0a0e060319020a0822030e0f1c1101110106181e0e0304090b1804020d0807080708190f08041b0b0c03040e0c0705060402010c02041404060504030809011406060d0b1201020405 77
    0x286a03041a41446c615070007004800280c200042c00110441620f54041e10122030008c9424071008030100344d14080745013030030001c02c05100540d8500d0314003a03079034840f2154441c11407400e0760554000c0f61040c0f5034030740d1085034412007588070390882c8103802c2003091301d000989090800c40d001c10902c81c482c0d400009041c4001c4000f40100040d50070141c4002c0300c0351440c65070842e4000700c0a040280b00c0c078000710003e400e004283d02550800e5822400103035480556180c85041940000496502d2000c0d828181407514007640e040c6030515400d858050f0241e07919a9040f265008030800003c0c13090f00c0100c04240d2101c010050314001e201e42c4000c40d81c039414000301980c0303c400106868142401000f14900181d00442d0b102d030410303420b0921200caa503583c40060090201e611840d883c0e680258100003d20a641c0c000600650184d2143c80080e00c91001032030a81d25107454030f8019200c0040410a14107002000300381e01d0011480c0082c041d018040011a14010341d0b1078402c80c0c1c0c0d0042801e1045 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 582592706 1250 582591456 582591481
    0xc0306010609080604080a0507120e040b060301080a0213150b04030605010b0c1f2307080702060705070f080d0617011b090b1c05010b041a0a0e060319020a08 69
    0x1400042c1450010300386044102d6940c3c98000340000c1c64481c1c086280355005008000341c40d4941d0307000030707060300142c06404010212241c2c0445107100b242060103252280c24a00c00301d034142ca100c2809484196916001e201c21000030721306114443d0390383c94010084449121441c8003a0100b20281556a40385041030f905856041c4c100c915061020040c42e5002c0d80e000460903c03a23030100031030010340007240781000000c0420011907035040304007103480300c0100c3c04840c149200310702984030203920f03441c1c1500880c1d80d400201c4484001c50030801409000c940300608011485200300032070b07440c01c1e521403000c00c00d0310b05544c032045c480755120310f041411a400307000d03d00c020043e4074891004c6c25070404c40203110144070711131110860000201440c0042884172007141451081c0d6042c021540e603682d1042c2c01d50300038414400804240d28400800703411010440b586941c00d660340b0301910a400003000300c42d81c0040d0503e081d00104024041c0e06080b280082c1c00604020307101c207034140ca000b98803041c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 582593956 1250 582592706 582592709
    0x140102031305100b06041a0915090112060e01090b030c0d03080115020a0b04060506120703140c01080402031b0102030d0f0c1403070f03020309030c060c071a1015030603060c020c030601 81
    0x80f00c0d07007030480b007801580794007040c0d03400c641d8005507403209000a861920000c2c880c00c2c0040c0e070000005050444c040708000000c180c10f24083c0d8480748614048003e0304111031490240e20031101d0b03000010003c140040d00a413040c1c0200406a407004650080010104010100300b103007c1051140100301003142c80c02c0c1c01000d0342a03030000d0600100d1a0f62051110b101c01000180240d0f607440204480761101c0d000c40e00411040300881e0301030350300c1c0d0510b404982001590440350344540d030740740c0d54954410a01207000e1940074008041d040c2640e07140c09480505075400b43e0440c07105020251107a2404e0144044a8a05450004003101d8450001f4007200a00c40d00155549040007407220070b82d406485400f1034011803a00580340e4903020641f500710300c1242000c14003480b84c10240003d20100400900d80544500c036240c800380440000c1e1110600e040390700340c184108100303081165042446030170403402200d180024049407669240002c44154540c03040041c0d20ac5403618055003000c011550 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 582595206 1250 582593956 582593983
    0x140411040e031206061b0a0501050f010f03031202070206090a0e01060905060f1b1009050f010f0605091504110301090b120316170d050702060712050114010c140102031305 75
    0x10b14102c120310083d4504040071300018000c500014000d41e50031142d900c0903154882071020380d00d002d941401e00c940a080156060050f07140b01000000300b01300074185c0c050031a0b234107031103844a451403105600000c0d0402401aa0016401c0203403603520368410348440b000e840d04c3c4407102c07402e504040c0c000f0f0013070342c2d0340d0411400b96004009450340070201c8403c0d2955001510340e4110031844010101d4207010711540603115140c02d01002204001e8080355400070070003504020000094000c0760b1105440844c4a129000310601020900f42c1d81c80f0440803040903030291020618140e042207a102c070380c0c000da11506100e03075924040300803842c040e0341c0d1003594405040218101660340030300380204892000003c02c107490648809110007511004e071020f00b42c00300b004100d5840d1900000e91698006c8a4400000b81c0007003e480f540c1c0303810b100303890607608070082145c8124001da0056401540140c8242c40d030625511600c041500c1c240000c43c0709200803d01042030101c2441d01900d4484241d01c5070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 582596456 1250 582595206 582595213
    0x3120b1507170a0e100c021302120903042d03050a060603061401050a05120109060e07030b010b0406051213050706020c0f0405090c041e0c0504050a06030509061603140411040e 77
    0x11070900342c1c0403010f0b5402c4001140c0d02c179010895808191051444800000e4000741c210b14060003d80c640d5016000034090340701c40c0790386a902e41001076101d00c0349000b0103070344840407400130342000003041000c800c1340404800c000c4282d44949605113042101e041c11030700746450300c00500403c64203015240b04442009007007240b550416000850410140c081d580c0626100c840c203084100c025000b45001d90b4108004101031070009002c2c50b21264540001c3e07400b01c100e10000281250102c0c211411580981d468900705900c02d0240d411a5101402419101aa0300c0707000000ca40c05000450003824103400070201d0068000038441c07403220782d04181d8801d5250408001912101080c0c207450075104450015812210000500d11900340700d43c0d9012652400d00c120106540010082090343c400301d80702810035555640460513034104840c000705d980c10410108000800d8039518124011703250030041410101c0d02c6007803c0002c8200e80607141c1c0383c0c00720301c0d40d02c40c2e080c1342c490385010100100c00f4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 582597706 1250 582596456 582596467
    0x302030601170c09041b08130803061509040e0c03120a0c060f1401080a0201080c0703021c2304031406061c050106170609011505010c03120b150717 65
    0xe001010b40707005038801c03151400001000034000b80304840b960003004104104c958500040c140440105414000125404001003250841c0348800080155800750502e40b41d43c1c2c80d00c0511a6180120329840c0b0010401c0c00600c01640d19401800310600807031006140b00c90030881050314240400d07a0b1700b501c4240c00c02501c901954002c141d00052a04a1000314030100440c440b040142a0303129400283e03040701001064080c008908084014000d0b070306c52001d9265141c0c0c103580f902c1074074001005640001003000d258000185681001c12490030075103142d01601c41c2d84810505804080d10107078a0006050080000480c2d14415881048004150750b24040d00401c07100fa4801368020000940703044198200304c401d400c210042c042c0140c1c1000700e003000b042010350ba036100340c45111055081c500141180b00e0041200821202c05070755101d0740300c17030584041c0c4e0405001c0100c011816155244c028494666029a100c260100d210140e6030b2025801c00c48005c0f04500a21851038504015 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 582598956 1250 582597706 582597709
    0x230f0c04080d05090d080403080309010515092e141c08091e0613050f0f030606010318020306131a33090109061403150a2c1c03020306 59
    0x400c2410b0b0240350410725911507103500000c8464050100c01440c14100040110030008250041d50040b080c02c0001e1259845074110b8115124519000540050304480028444845107058103c2e0a08030390000081d030700461400c9100c50050340240c6001e83c5d40c405080c5042c01c00d0b121103c0b407900c6040c003020382c2d65002d5550341303103500c1092510341c401c070b50002400010140102d40040c140100400711a0b480031007049540c8410300034403032103200d02c001081c11205828200710994050900801514450362114019001046120b03101e4040511201c21807006840170071031640500015085000100401e00d4171404003003d281400aa442c600720030720003000c00004440c2c4004039011b450301c02c42402c103940c600100000d00601580044060000900f0400640c4403034151407424100c801c04040000a05a0b01c0300041c105c40580206603000a840881d5a444100d50900307410418800d210401c42c0d04459165000c04c4203e1500412005107802d02e84400c00d0307070340d00c038541820f40c110320300f40c070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 582600206 1250 582598956 582598963
    0x10140a05012001050708151801030206030c040503030f03271915050a0507030b03070e010509090a08211b0d0f0213030c030c0e010f0306020706230f0c0408 68
    0x214003810302a1074044104002c41407910704514100460003000300d4034000f2002020518207642c03035400400c040d0003a00da54102156283c40031600c41c80440e0043c0d103503500740081d036030005190304c0c0d140d1018000466541d500307000901c0032840803145980c49007030000301e81c411409060300c0748606040300c010f1044d24020108000503025200c41e00419041c0050a1000d842c00000e1410358035540713000104001001c00c1d40c4101d0151b2105e039010010382c0000e1091582d00c3d02103005000d5054598401000640740803203042d035103c0a18402c0c0e45009010b41d0741c05a071038129203844101003010940040c0501c072059450340c0d01c06004034a81c40304210140d4041c81d140b061506021000b901c410400300011060340483c3e13003598808400c850b4042d6241032508040e40c1030f0100310742101c40b064001070542e4040300200d050702c3c0341f0f040d10f2030101c0c60340c2c0d0bc49000b0750080c1030858440f23031035003a1907003004000000c9040074940c80b210002d4030300d800c10418201c07030303401052500c072500140010301c01c020001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 582601456 1250 582600206 582600209
    0x13091401091503080f2a0c01091404050c070501180605061f0c05250504050108010b09010b0d1b09080d03050702120d0908071a0108010203071b0201170f10140a 70
    0x803103032940d81e44417103803d9a0138410501d90240c0c0070301c07282e4003400e444d0085c44c0042c40b80e8400b00603192081044401150001510b102e984251105049982c1c450301e001d6000c0c0f904601c0c0c0421040c548107030390b9101d509540008044120b5109103030002c2d02444400c0c05180e50085c41112170190079103031134280300d06080144c1d5942d810050700000140420408204080f58031030f0051801c100302d00300403c101101102e600540740120f08000c000104890140941c1c00018030003084083c1603824444a0768045d00039881502045448824500c0400604149402d50750300641e01c52091601b040c550b1840c1c9402000303041c040514000c10001c400f82d001c100c1c4a40700001440e0550380350329009400016241d030740741c050072110700022141c007006103154803806030010300a4000f046c3d030f989100c524200d010403614080130400b01c100050b40003102c2d500c040316480c07050604607501c202d000c51001480307104580300c00100180740300b40100c0b00140340070000146071a0900c02f0014a82c04040781050016 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 582602706 1250 582601456 582601463
    0x50604030f02061e030105150304020f0111160603051008030c0604240e0105040224090d0804090f090c05060a1e0203040302100c03030612081e13091401091503 70
    0x507212071800c5544403000c540c0d030414410514526010b000c11000d40d90390080c4501c0c0e120320303504841110010710b5001030320711580c2c0040400300b4001e96000152203070340c00b801500049000c0c40c2e01000c104050b81c0502c0d000fa164950f0000380c14581690020b01100181d00200e205900511a944010300300003071580c1e00990100c0c0191410241101c079032007200100880c0c040c180d04003d0a0914610158030451181c0c0c000c0b2601d111000c000c110190382110704030070b0300b0003e01003041001c450f420051005440c05105240d218030b007079030301d0303203030404840c04442c65548203a1107149410602082c90a5480900002ca542625005800d04007900403100c07220f04142210701c800310f6000190007881903c00a5070080c02c80e00c450746a559006001d001d101c001140444d180c0403000c40d034270059440b18541164400c100034900350780c2c040ba07071060411041c0d03801c1001404210206500c014507103028000d10758004003041041060400700c2082c0c0058012902a500c0c0545400050700040c404a0443e1340 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 582603956 1250 582602706 582602723
    0x712030b031e1b09040218090a0b090d090f0510230a090e130f112b050c030321040507050a0e01080f150a0b010207030f080417010605060403 62
    0x803031501180c1070034280b440a04012a080341c0104060074041000c040c118146400021124000c00070008615070690f070182d000a021303081d400940550207081500801054201ea001004550781c044181900b00c500c0c0400d80c0102020b04000d5412554901c060295104655040f504110104000b03070750066441701005100c0c0741521140c2c249000405403800d0001003540d4600d40e000c0098040c0b010341c03250129000003040001d4010a459062007403066015000c18102c05440d11450b8136596031048c060342c4070001c010310101c034500e51947c0d0b00c41040040c06030000419503090540c20441c182080078000c0c0c01c10850b00da42c481c0d44030b00201d0071019a02c40c2d002e40d81c84604256142c80120307001240c100340210008504d4035201301c9054100c41c0300100301c0308140c40c0f202003961140e030a110031481c07507881440469070aa00c65001b4601c415410b10490f51070703030740e40d486901401e11404003c2c6c4402d040054144842c03150382c035088600b03280c0c0303100901a041c94400400c1c3c0c80e01c5640320140c144034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 582605206 1250 582603956 582603971
    0x60b041416140309010b1c050d030908120108010c030b030a111002120c0a0c060c0f11150d02070204051006050319060305030c0705030d0311040b090609030a0b1b071203 74
    0x1406588025402c4446044060b140e10348120b4080c024154188031074440c4c2400000100510482c0b41000d0341c403640080904411501301700f058002c0d00070350400f2161500244500e190107549080c215000305404800880c00442650014044402b40c104050080c0c10403e4420086520340ca08010250001c0d0b40460f41c580c59000300b2814040c10303074103800e000c1500094400b84150f0016003681901e000c0c0003030000c0b89680e00d0056a06802007000105200d000342c0e00a0b01080f50317220704000d2020043c10b1241c42d111410088c12780d5520002602e95030540c0460000c0542c2450b100b03450740040081164400301e41005030140442c00010848500816a90000c26112141e90010170007542d00c40100c0c0e8694451120303141c0c0300e1000c0d0152a01a02c03176200c1c1c1e089017510031700500b43c041c5044100186424117080708039400354010385c40c00f90030060400c1400c0054500300b240360401405280c40c600107041800b01c2000850004014001841c1d0500c0790102250040300c40801c240c020307040006030038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 582606456 1250 582605206 582605251
    0xf071404180f030207091803200717010606080405061602010b121f0c05040b0c0a0209040b0709060807080a180804060513080708060f0c04090504030c060b0414 70
    0x1070410306042240c0e0340c400101002042140c070038140e0010b2090b001d48001036191a0700f541105c0c4199254841d204042a2150100c0d0141200200324150440101408024150032914203105503001494070b1800e8410102440820b1103030300702420b01460001c806040a44811b5030f5035002030500e0010151000603411414002d60110004100240c0748400c3c04c541c2d0240c0c951642c201025540780506506691000c42c20a84206000c582007501d996041c9818040d00d003039183c00c540001c0000e48940003441002d40e44041ca224826817141e491101c6510340b40400418002c141d51220b41403100650600c0b0b035071a00294001c0d0700c668241c400103807107900b41050360000d8000304800350030980c0009021070740b15440802050f42c112000f1407110b010750380c2c4100c5556000544100c40d0250030500c04a40d0204808130619008100201300da4100398803008148115002524200d000c43e891030500402c2140c0b0f40109095000b0454040000e0611181c80c0c3c142064000c1141010768840712071090394 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 582607706 1250 582606456 582606461
    0x711011a01020c01080c0d110c010c080702030f1c050c270f0d0201050d0c09050307080703080409020a020708070801020301091107050c010e03100f05040212070f060302030c220608090f071404 84
    0x1407c0d911f001c00d00c040f0020408400c60b5501c0200c0c038990310f500748400601103c0c01410040c0c002e010a500071440c100340c0712600011508032810001da083d100018a1554440320302032507004170019168282e690313140408514168905003200118502800d003005c1303141e0b8901c56940c100d80d106035812954683ca601c01260708c2c1c0320300c81440104516103000c0441c0c0d00d42c011103410a81e0420b03021111070325122a030f041d565511911009211880421040c08040b41540162100403130390b00480e21502d442c1c600b000d0030a61543c2040303840d40e6010004000320070180c01410100306481c109185800722940b40d4644880c645450f49050080241c1c2c207a2150b01c042006040e1100340c60800c00610b101205c6a501400d400d40301607118000d400c41c409000c24000c2140d00880f01503c10b0b28030242d14042040d8080d4200900420b07079840184802c550103484440d120a140381140e10342c440c3c00c1d0403c3c1c00a452010040d060075002e80c8803050120f81c1c0f580002c2c043d81581c201459111752000480005000f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 582608956 1250 582607706 582607717
    0xb21280b0306150a06050c0c190b0309030d060504180210120e10050702010507020307030f1e0806040e0309060406050f070204021605010c031b0f03090b0711011a01020c01080c 77
    0x401d8429481000000075030011510281001110340711029642c0c0e5808841d1401403840081c129005a50029551300d0070072040302164060403100d0244c256290000313105c58200300c940418540000442960114070b603c5407401503e002c450070012030307901c4241201c444840300d10083c042c0d141520302c03503c0c4034020030045441110b450401c0c456902c00115003900c0d0801c00180385146401e000100c0e880d01d0040c0290380c45007010358015420503642d9142203c80b641c10140000c14044014140c1103446000326174a60110301e2900d1f1103030242080028803048502a0b420b020f81500305102d1202680e4501d41190215070440c5010758030307030308916841e040c28410040001d51103440054080009000305020000240c0030384000c01c09401808015015191079134800f40c143c506003025010064001d580c20281c0c28800c1c40c00051001a5544104074000300b56004400709084911018101c00d090080d07010b58580c5940398041c401c1d00c0c10000c0d60703d14440f00c0c010b0610114000094003448050241d41 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 582610206 1250 582608956 582608959
    0xe06070c0504060801060603051501080c0a0c0803040f02010e1f0e04061205060f070c0803040303020d020715060503120c12071403030109090312090c0509060f0a0b21280b 75
    0x200c15913445600c3c1340240103d115020110341081c00051003900c040c60048030f2180b042e112818142c2d115049044681e102a800206125071381082401140140303028510403441246001c00040c158000540386207800800e9034400c4200644c9602e01d40380040c58180300c46503a081100f0603424a000090203400c0c1c5400c01c4e15400c00c8038162400748000080e0841c0034004460500380750380c0f10103600320340e44800b10700b020704252000c1002c40c0010788264010b10300a400d01d82c1c018203001196451413254844030425154860712004140003030319040c042c034103001000c6000249401d100c140c080303881c0c0c00c2d0030740f54800c00c00010848000340507110074984141008030701602d0f941d603110414440201a010b406500207150007950a45414043c425003400c80c1d00040710420f114607207403c204e80790200a281a41100c1d484804040b251180b000e100068881c50015075200e00e41071402901711902c00304801d615250301c3c0240404101040c070400c8154007015189860841189041c0c0054000351103541e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 582611456 1250 582610206 582610211
    0x170702010e060901090b37091a0f09030a0905040b030313091a12060a050c160c03021f140708040f0b1c050106020c0d020a050a080d0e100e06070c0504 66
    0x3c003108074194400c4c031400d03204500a0106458081c9422292141622850340799201e0f0145c0f28042a4640c1d80749a1010350b40d48041030900c0150b03103080e41c0c0f12001c0c0140f41e406409030180b00005200748030803948000040c2c000d600341031610720b000300210080c2c401c490240303540b81d07074008050310144125821800d00c040c621800580d550f070400000e0041c100c0300b280b400700c030039050221f52500d00c15842d000762074800100341c645c4030078151000511380507110142c181000c00055801000e410841a1a18050b00d000b0310154a0760061082008242c513205052119161004900d03540280841103444864500a03494005515119615106640000c0502141080001240c0c0d0958004084814809080b8046074581d90322090546030280514409a000300403d0042810104030184085000908024860381e40d0390100d000d01c078258004008980001c07480c0c0301c2468000b41d030703442040020385a980e41110301c42001840641085180d80c4a040b00180c0e86051001c01c480441c042c28005108 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 582612706 1250 582611456 582611461
    0x20f03070c0c0e071403070c0c0602030913052203030e010203100510081005060f071223120112020609040e0706090e0f0402010e0102120d0207021f170702010e06 71
    0x6003804220000494404010a002080320f080126002d4007504d040c1d19130816828941c40e1a170443e0300010044420409425404004240040d50300070081c071064000e55518411072003403000c0c5240b0800d003049158204410705c001004c4020610521801c5207004907001c6030b5621301100500340643c0403800645c004018400c0440c2c5051709102207950481d5140321490b000d04043ea1903140884106120b0300b0300881c1006135080460050150459031200145803000c03a44c0d0f40e01c0c008103600e000c0c80000b1800001410040b0180c580c440408040c0000c50f0f00b406130055118501d4081402748641c81110545880c08540f240c0d0251044883e008000b8410102c926a480307503074050a21803070340050607100000030303141c1d00d4680c90f50080c036490000320060b5a0725001591202c40d003005550441c8100040c0c81040c4141001030003c800c950a400360b07654080b03004200b104011511620120140100034403030030b40e000f90a01c0500541000241c0e07242d500d030041a401410380d41c1c1e4090701c2e0300982c400c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 582613956 1250 582612706 582612721
    0x809190f171207060b060d1e181a061804080a0e060715021303050f010506010e010e46050a0b030601021b0f04060602011e0606202109010f050f0715020f03 68
    0x3130305180a07949179003c1281c640d996809c03401803068480701504035003a9044407a0742441e222075180d8001c0c4007401030b840f0006400501002c2100c2200d0a803080b180200745d0201440d403041c40040b10501c2210b03124142080b41c0c46081040b040d050b204100c0a034005040810b0b220092140401103070000d05070743c880f1020800d4140a8882280e2640c001645642031080035801100b0394041c01c00098400d140c02d442442505074100d090290f8040c8200b54010310019030f0800c41c681c4001040b40031081c40c10103191409000c200d038010b401805046c6800d1040002c0e69900007a104506c042100320802480484004101c0300381e110760b00141c10604003000816481d405400003055024078202c2c840d01010400c280b5001c4821600403c000180d009011628040b0340fa00144000581c010075140103600c1400d02c0f0740030f07130402520102240408100d100266801194007030144440b82025443c2c42d04e80c190885c59441962002000c5078480081d15a001c1c07402c1d41901d000c41c090202c6980d880c205a40c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 582615206 1250 582613956 582613991
    0x60f080a0302070e131103030723100219080a15060306061205070c030804030207050a030b011d0114040c120203012912040809190f171207060b060d 65
    0x203005601503c6400400502c00e80c42c820b04610441c0d03103d001c204440210303990030611601c411940c0d94144010300c081800308401d0b640d006c1c2401c0507880c0310810034951401d82c508002003001e04080d46031050054040c0141c24168404246540f880e1641990b6140010b41004111108a80c80301c800030700c40108002c1e070194488c0c025a48292650001000f162000d1010fa40040b101400010a142c4262001070b0003140c0980d00688280152008540c4a001003090004240c0c800e46200840000411011841909015054001c078030030828641c1003e41c20302400d51328106481c011070340c3da02d011444905c02c02c111080308645c240f0555072035942d0201c0712808440032925068049811290000c002505022106006145e820000b0b5950fa03940310003d598000303051142c0c000c0605c1e00c0e080080c00044010300b000d13103204450307880c003907050050318042c90300c0082882000da070050104094008002003614012a4810000328241c6140300210307019028810f088012a0b0030050040d0316401c842 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 582616456 1250 582615206 582615223
    0x9191e03080702010f1a060a0c06090b0412050a090b0f07081201090c0816050304020402090301050a14091920060a0903050111090603060d0201030e0a0f0501060b07020a1503060f08 79
    0x43d40203010781c05007488424221a50036000808440350329820b0070160400c1b80240c41001401e0600540100c15522440241c0d06000c50803584860800100070400c0024401a000c5c0ca44500d0880d084c800e082c04040c181c0443ea0281a0501c20702041c8090b01105050407206000c0c1c1c000740310f94680d44100000c40031018203002d0703c5005801d00314039500140c459040c0034418903400491044144a10741c0030794542e40f02034800d90304260200010041c1d41c03000d0080f58000c0016040020342c20f02e8515942201c2e40c40900a400c00380c01007a2100399080380a100c5845058210302960000c3e000d004000545554115a0981110000ca032101e44250400c01c1002100d000e40d009100020951240041c0c501c940e0b590254010300074400b0540303d00b40500420501441810002400418542040d291094560084840c1506408000c1c20060280a00e00003080710b0110f943c1444041e50020f42d4400da1402802d00500200014100e5240f182c2c2104005003070540150122329111611240c44040c00d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 582617706 1250 582616456 582616471
    0x1503150612010504031b0318060c1103011a040509101503201f02010e101d0d0e010807090b030f011d01182301270509191e0308 56
    0x2504800e6072030681801070074071841d030680c1c0340c0c203600c0c025161038401c031540c10703d0540410400c0c42140c07001500c10608007000e0200c3d51101d000d0031000d481c01c2600c1a9a59a20320b010780d0500c1a60040071000c869480c0c42c2a40468021401c2d9407030a410a2030028000110800982000605800e4400580b0407100382d900500d60308025008054188600180f220006600800311540303510203c4010500c030b01c0148541e1002040942c4040502e524003806505800f6006540d40c0200011541402c1610300310421140a80540c100c10440038010700304000055050020000010380701a1180030b10b4009400d2895926480741041030869a030354000340182800042269450280c0b4500d00b28464100c81a12040c503e12084d80c4c0b1035180546046c0c408902c00b04c500d222040288052208040d010745032a04070604020f01580d00200101603064211000900d490b060150010300131410f459107080e0011020001080362501c1641d1a07051a554201e00f60350f200041304041d40301480d280550403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 582618956 1250 582617706 582617719
    0x41a06071415060904020f18070e130b03070608060303040f030b15030c03070b0a03060506070f0512031012030504170a0506070e03070e0702010b030a05010f051b09010815031506 78
    0x541c0340b06919015107519070300000c0c00c03001600601e00303000c505948640c05045042010403040031503100c445c0540b81c0c1d00100b60400032411042c201550305005a0840b503005200d44009500826180c6055000340d0b4100418a40010650f840c10070403a001051003100010180d40c0e2070920310340402041d124840c03d40d0540c0901500351800241120328150010040d05d10245800800c00300d91341700340d03139030310a042d2903d5000030720355659409070041d01e004100582d00b40d1000e1034401d0610b507000c001500004810301c244440207111801d2202510b245d0700208a8144550405444c24011a4044004071001182c1c9c1280c024001c03411002d060b101b04111006a200d40350180c0700300b0044c00403190103500480c070811000d406065025001081e41c000051001030900109081c02c20301c6c0d4003070f43c1c503a4444010407a15400c038810f0302e52214030a50700031032000f041c0c007000c0983e100700d10b10710b81000103000202c0c059500540d41e0300b10000d00182155100c007450680072085807001c940c803078410076 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 582620206 1250 582618956 582618973
    0x313020a0b091c121116081c090e0a09020607020907120c0207080d12062d0801050106050901050711040f0b0f0d320102120a0c0c050c041a060714 64
    0x340640707082c11030b6407001104039000d0b004e450803144880c004150f1501845081e0344a101807a5014259029203501000340c880c1486458400d07810070061410340381040030070f0004004541000b04416001b010200001c0360701c10880c000a01b50380a03d041c003030f5000300c1c8075040c4502c5030742040300310748400c0192030140280d8250701000e903191030342c071710440c24160041c100c40641c2c58481c1080d50a40d4040450010341d0715141c1c90031407800c0c0349000310802010302d0035003940ba0807138103c0385417002040e03040c0081c09150b050140041c0030740903210106040c0400811440104806101d41620321000034004010042002480364040d12441e00d07464081c410300ea0b000c0b607141c180420104030444c0c0205000400415040d032082c1c0705100c40c1d500000081755256030161203002030000b44540c60101404600c03074108011200212008142408240190f609202000410100d00001d40600071180007984015039820200e2248800c004075500202c0003c05404224a04090111100c000e00c2100d1003203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 582621456 1250 582620206 582620239
    0x4030311130303450801060902070b09120a080702030904050c040611010506090414070e040507150e10030203090304090e01060303020601061106060f0418050a020312041a0313020a0b09 81
    0x740c10039140003040054a80d58684e812070540400d5000700704c22800d06403201c0d51144002d084800680041042e00e4000504100340701c540e045854001040d64082c00401d00380309441c208a104004504091083d00000941c070b890091040c0d40c60310700040c2c010300840c500f070101744c6401e40c0980503080110740d20b50350035069520140b1803a4030408001e46600002e40300d13500d07190082d0b241401d0140715072251400100350342052401d1a40220b02c94401480040d080103200140042d0100900d000c100030841c3d8620399958003000d85440403001e04006a8a861383c082c5103045101d10380003400d180e41051019800144154008002c0700e01950a0310310a0341c035690202e40f10066003624102aa1180001c50b0a516140180c23482c003050007440010038041c43d6080140303141742d0700819925504210912400d5040600c20101000409400d0310310b01400c0c00c10140780440c0b10ba0300c05049800c040000b480e100c0c030b4110300000c0140c0091165220b42d41e580c520040641c0425111405901088040c1400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 582622706 1250 582621456 582621497
    0x190f060314011403030403051f14042f1203041701020316030f0902090f0609070807020a030e06070501060b04080d2c0a05130b010201050c030105100804030311130303 73
    0x640020003903600350781c0d02e456a8000018190015140d15000c100300000000d4010131201446c503d0307a00750460726010080c649421100000d20a040c0b410083d82000001100325a0400c0b521510700d074900411502c0004d0f105980b202c0d284c17107076000420541c1c0b000260310004060030469405084c1207070202100c0103418242e00003514203503204030304c994081c400c060194204610342e00d20910000b4000100d500000d6000c0382c01e45503c203403e88100240440350401107a110382c400384a007490100b50822001c000c2d0b84100600300a400c100000f41001d80756a5888101e0302d2054211000b400a01e031103250040b103d40c42440340701030030b11450711100440da0080190100c07401040801e141013000c1c103881c185800c0134220301c11b170380030b100503401040b255100340100f041c00320030309800584020400d0000e0f003161406407018402c02000c0c401040705580310141002c0c04010f41c5403800e460340b0f641c50290040d04010700d41c042a064040388130005419120150760840740243d5031440081c00c00d420400c070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 582623956 1250 582622706 582622721
    0xe28060228030c030c03050c060a1d280c03140123090a060c120e06011e0b04090905160e0720060c0a0e030703050303180d0c15060302190f0603 63
    0x8a030002d002d00000c40d01070360316240c0317241c02030400310310f010300380300d00541000350880ea0f1400040d51442e500c034012181c801c641442540c0500104035400380411140c00da202000110700c58825a9441001000302c0712080100443d805130841c0c1c0010703409150240608424015100558000c001c0d03000501d06800d896170181039008041c08100034543c035804090500300c00510140194a07075a0020b916803407080c00c2e40d4501c684060012541005070540903a0741003000302d03480003610704052103284845c2c1d04840448011190029403000649003140c2080d02007444035404042104000078140f84200e5000c0c8640f0040d59410040c881d508070382090308012031044c04043d8418400662140c0c0d070744000f000e041c5002d060803008840385a000a20704909074008407516000071003880b98268105a4036026400d0315009080102e4101100800140e40000e000c1c0c0310018a8411f0400c580c10750303101001558016111480300384080c9620708100c0b4003403042c1c400748040702c1c00014031148644030301d40c1c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 582625206 1250 582623956 582623963
    0x50601091d0406090803091b0d0218040f1a010501020709021207081513020909060102070302060d050c0702060406050703020c01020f0a080c030d021209070609060e28060228 76
    0x40032031040401c01c211148020400ca4000d6603910130600828040c1000d140328091010082c05900c295000030b152041101c0492405400b4044881006985040460200070842038610400b13595a081c082d1110713015600250034006042a00c03081c020714410350a06803502a000c07070384015690340d4000100e100c0ca504040b40c8480d06e001064405200d1798810303410682c40040300a050703000100240240c070b400840d41401c42c1c0c3c000b4141000381011a00a6032111b001d00282c0b100382e140d50046034980c030410461b02c0d00303e507548001990418006056031040c0ba000340055469035141c6201800590107681c0540c050710070700c8601c09582d0304c0003840d00003400c6480c01030b0240220f40d684224098000000f158601d001c24002241448141e1020f0311301070100209a10043c181000c61038140746560700010200010030209020782e0340c0000c41e03444008400d4401e840301545010a00000e40d42c1002240344071682e00400080786540014001800c0010f104440c0700c03c0d58404010342c100c00800f000a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 582626456 1250 582625206 582625229
    0x1a010e0c090301060506030930030118020c030f070323040b0c030f07121211030112230c011419050319110a2709240b04050405060109 59
    0xd000c04144805006001d002800100d0840d8132600000d000c3d82040b0390042c102d5000881405c81800268046110003202e4144091940100940c024a40c4414001e1174103592540401106480c0558100d50400c0c80b84010350f901c40c40320001105490380034280035000503480d0208229010000b0402c42c103140e0001800b00d1030185485034409036500072140c1900680070078405180d911001d0402089410700c6003289104100090001034461303800210341540e010b1400342c8610f00c05e01c00070704032070649200400c501070115603031900f044500c0000e010900c9240f610f440c0c0200c90310340059a150310900036250312182050300c03401c443c014058855850944403d5900b51000710303000714002c5410150b0400d0b00c0511079004180b84003a03842e10681d4403000200010680840d0341c0c81b0710589401c58400030f41c1c00c0c0b00004030040c07041811150107803425440d680d01c00c00b44400050714000c0003584a0350440c2d241c85a4500d05100319410910840740140d00f4040040c010b07610407450300d030558091a503034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 582627706 1250 582626456 582626461
    0xc120e130c05040509010f081e0307110d02030d0207180908071112060c0702030d0807020a02130f11040503120703090605180a031b2903041b0b04031a010e 68
    0x20409019420100e40c1031160820002c10b0945510101703078040c00c00151150303411446e09100a28100c640c00c0305080000601544051001012049903d400d8021680118800d240d03400150305098441d0003d6061041300001c0c0f00030745e00811150201c980d0846400384603041509640e00391061088010500a010880080007944c440c01104881001030604464018021809441d01105a551143c0804042040d404500c1e040040c07151420b2031745041c1e81c49007084c01c40030b540c900522600074172854001d41d040c3c6010507682d10424443c200c80d8820712404582d000d00c005030f5803060182a0180c05489141303010007105800f21400e482d81980d070088454a0724400300c465070404403540c031012080b003220880c40e80e1280310203c05140510600b0b065000000c00340312080343d81d035000854082403104c0782c078940b950a4a220340c41c10801001c05560303661340c1c03506c0c86521940700301c889601d89120601003110f03101e04000d0402d41f842550410300c04d07070510308201c4500c4801d209004440c140d9100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 582628956 1250 582627706 582627739
    0x60801180509030910080f010b070b0601050c010b030303010f03111005030c0c0a020a0b0901080604060e011205070302030601060c121103090616060507110c04020702031e0f0307030c120e 82
    0x201c02d0380040d04906880c10040f089000450150140320100300042c54041400b60803400c02ca106401403c012400628002c640c1d565100700d50001040103040c06004544d681c031030304080d040380e2800b00f401810390ba62581c5540c085a0000f640b4002030720103000740c100c0b6030443c1c140059050054045900c50074150b1380c9905070280d15a002da11008014083c0e1104180140c40c1e45400d18054440e20203240c0d101c0c41440d000405012004010034403403400e0030401c000116900d4041415038540401404c8c5205940c00c0081c074000455200a40500c5803800005038280c0c04810030581c203110304004e01c4c0c20b00f0b4001c0704844550050441c15400c2c0c204016064852034103800800d6188040260b611034075a1a444070030840e941100c4140104119454002c1c042400780301812000c40216001c600b0f2459030380109a0f07815940012501c5511440903411100b102040803180170302c01c40c0e0440b82d9840071440c0c004c12550b074002007106d000c011443c4110013140140d2002146803006800d000500d083e400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 582630206 1250 582628956 582628961
    0xc0103020903151306060f060f0203070b06100c02061201080105160e13090b182503110307080703060e060f01050310111603030e06130b0a050406110304150606080118 73
    0x406072070000b484d40042c1c400040e2140a8038000344032200d50a8085882e004001c0c221000c1c1c11030346011500100f02900028034174010b50b5400110989400000c000309240550340c020022902951140d4080742006400c0d08a4101505940c410b4000b0b000300d4a0ba014007000036901d010550000c50319006030301c1c1681c20f02c3c0d4481804e44001e0640868406c480d5210f1518070702040d40d0b049084030100c0d6800100c00d200704009110701c0401410071104081c105a003070b05d12407603408010400d003604d181c11051075400300683ea02a2110703c0c00ea40b4500c0d5030b4070b800802803004110044403400b80c03200040c4500840501d20341243e001902a00d1a0f0100001c60001410425040c05480c1c40a0200442c0e0842c1032140385440d61003500e00060081155582926181004003681c40e807034907441040c000a01500650341c2c20075000100803942c0e464920340174001e80556540800411004003c0009201d40c07501880c42c0012203420401405881314030845551400340154500384444202030742c841655907 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 582631456 1250 582630206 582630211
    0x9020901030906020c0c0a0501090b0412140105071215050616140d02160e07022505092d0108032a03040803071a010503121c0e0f0c010302090315 64
    0x140340006510391680c3c0c1d440c0490704461110045a88424040b04030380c02e02c5007511000e402e09082201003185080b030031103650701c00c034011003946902090113001046050600c1c070803c0e0040345c00034804c5243c841d00041821507606113100490f41071001100b6039800d52030b841c409030750000e0807040c6400308400445002c1c2880c51001c840b1310350007a41030b042d08041800210088003503507001c0c114045541811805c0c5035a1608402010a007a1080c40855500058410003170f00c80c00b10b1034101c561050060003e400a25030002e60020203c2c8100500c40e103d40804100494810b5018160502801da400258840c240a030440c0b5510030402c025101484c2800000070078140b4210602c003020358803406055403c40e81c04882d4591001c03034290200f051403030342d9007108040e0100c1080744e90314010010380c0d0349250604c00780596000190140071440000c002107a407011121040c024003900901c9d40c0e50710621407a9100d01d038021030780055210361003802250a2070030300400401311800705410310500719101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 582632706 1250 582631456 582631459
    0x71401052d04110f040f06152604081908010302100807020a020616021c050c09040317070e04090309050405060d0b0105091e090a110901030302030d11130f180b03030301090209 77
    0x355503000585d4460103443c0c2a48440840030440341c0c40c0240c40250400641c1d401014000e10010403039008100d000e40da851800c8511402580d911103040481082c85040c0091142919240e44840141c0e0448003481c1241d209450304441080c1d012012619002c0603521200160006440300300035182c91409000408940c05200b0300542640e800510f650f500211403a00300103101c1100000d00c0001c1c00b01120710b60042e54203142620b45907034010422504000c4221840d003804000c80c03031440c41007103204041d40f4080e2042144001d1070034054803c0300280309440c802c0d414a0005201402c190700d03821906940141e44004ca642450101301c0113400082c0310300010104424201801a4082e1a01d0701400d1540007501e10041103040034520601c4402d0107038001c4000c1001000020f600004036442000301d16400100b00a00400300c852a00c9190185002840620008208051504040f80450320003c00c0d080c0e044110411002c155441c049074181d15400520040241f04c0e05074009140c031110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 582633956 1250 582632706 582632719
    0x2a020d0f03020409181103010b01140708070c0e06040e010614010c05010b360c03040f061e020406020601080a0f0201111213030204050601030b090714071401052d0411 73
    0x441d600100e0898031a004110300701100c42c5c241400b131107130030410f40e41080d0003500244405401400042c24840a05c6204121030000048020602501605481d03c895200d00d061406c1ca80d16040003e09410a948861180789445039044503618144200c0c1c003100d1011079130b403a004500303800664899042010030340d0380c0c1d52102600701d03055581c80f84100828410f401607034091081d190203d080d07002c060102c0450b480004050010702010401901e0744164800c030f8140080040d2310300312014055400069150b800d0449280c5174403001038002d4016201c15034200e40b600c0e070340c6800240d924400e034080030f40500320342c04038580554851003455202400b00011242041c802c0c0324007010b950302550f00170084500b08141402140b906c0c0c0101d40d0008024a411302440085100154024802400010a212210f40e4403100301040e1806d581d05203400c07500c107000c41c9182d000ca0300d02074a001c0b1410303804a12a01180d00c12903602c1b00f911a00001d45800c401c1540e501c4e0f130303144108003440e546520750040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 582635206 1250 582633956 582633959
    0xa050f06040b0f13150903080d0f1a120c180702030c10140105040209090a0b0d06050a1410080a11130905150106050f070f02060f0a032a020d0f030204 66
    0x82d100002007102c10b180e100c8150740c0754248001c4030b20100311900014060355407050800c003c01c2c1e200c802113040d41e800200c1e15030703a4078a502c03555005008800510b2441c40c00c0180e0300b4228600000c1d60011001c0c1641d524110355800b08445407500c1480089075403220007141d06100000e505824281e100d0002d0040b6844c160300801c00394030380641c40c9666103102c0d40b40d8060400400401d40301c0f03401800b09680541c20704403000c0003c0c4000714000c0806450075a550f0700b004942c5d59020a8a030300c00d8025100300210304214029102505a03804c2070007000c01c41c0d0008c00c0551002052103801c94640e4000b9008030402d90750b40d001d4211811510540c0b080d4071902000c0c81071920301c40d0880c00c1d48208010041400c0303554001a007484141c4c40031051101c1441400e550904100846000ca60311243c40c5c240c114051002960901039050341d801c9400d80854807032092078066001c00940c00b049183d440e69074841d29420691049803078035980c0141c06c107400310702e544c60080d000801880c05c02c0c1009030919 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 582636456 1250 582635206 582635219
    0xb0f030f03191803120306170a03140f04180506032d2b0f180506030c0706090b0405060606130302010c050f121b0111040b250308010303020105070e0a050f0604 70
    0x40f0041c1d0015107040c1d0f0b08403540c80080f81c0510030308005080201000003003250804426485201c525005018420072800e41c419080c14042110a041580100240c0f100c1e150301001070103001c9054002d100c14501404605949000150502d01468203e03003e681c081c1000b45100c2520342d040c1e83c07070a00d17206050355154070150903a000c03501d0110880b0340343d003081581c020042004108518450600002e150b40304840350114501d0400d4480507109541d03617854070341d108030f0688150f0002902076440c1422002c100083c0810b414080da007c1d504036019900c606080180901c254243e900035000440b00c2000154019107c6c40142030181090344c2d40310784a1450b40741880030403480d89500407800101800308a5010107000b00c0d100d910300c000c1003040000203884542d4031a5014280d01c404011941c0300948403681e103900c041d01a5014003840003030301490040c1c0707011001e0000b00c0144d401d05001030b14507446a800b03401d4103c3c004000102c840d1800c800c1c0300318001110321841d0012801c2001017140c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 582637706 1250 582636456 582636497
    0x1e09050a0203071d011b080c0601170f15060f130905070504140606180d05100606030f02030609010302130902120a030206091605061605100b0f030f0319 67
    0x103035201000580d60b031070041c000500340c2040f0b403c440030035100700356201e03c0342c0da0052401c07000c0c405544401c040a2454100746140c0e01071144104641e200b0075001050841c05100200300180c0300340300302c030b0115004191441d00e03011064580c0549180b9800050030920b050003a0158540000d0030308111141951030325026102e0001c42556680d22105c070400540c1001c0c07150306660a003207441c1e807010703080200c002501d41c0f0408a0481640480c0c51042d0005d0355aa940e50860300d9112003165802c0004001c0036001e850503100c0c10340400d191041c42c26178000310f8000c50344208801090403010380e09650810000740c50f07004100c0480741c0d44590980c0181c48030304640c03010a00340e90007002413180c9890020b2038100014040750301508007916001100058980f80c4054900440380da544036050180300c000a500c1200005d00b4920450703400c1da51040441c0c4c456038120070141c45d0840c50001a100741a9a0040c02090080540c800c0110340b61301d90b0001007845912500c2d250026402e041450311500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 582638956 1250 582637706 582637711
    0x1110092108061e0d020603040203161503111914040906030602070b0a0e030406110c0a06080901060b0901050a0302031e09030d2f0307031d1b040b0a1e0905 68
    0x10585050a00c071440c98200d056001a640e03001c007000c1003542c4200821113407411407100134000d08010010804542d800d02c030340c4c007190075006000b1490030750361440441006007030008803020925201802d482d00910f0b204440e03507101c9202d05444605020003080300e030b50020300160706900e50140400b11703071820140580b0300114041c9801680b50b00c200d003452400040040e14414030319241100d24250144007005132411603501d820003100f041c1501c000380d820100e0b0303081c0303080d8400b44903040851260b40280d503071801030030540c2c001c002030741d2180155200742c4500d0742c5803070201b1001d00001e041140309800039070380300301e00c01c06000769800300a20500384044155500c0449800201d818006540c1500c50002d050b2003040f1280c00e40c1180b002c880581040c2c881d04d000c83d0140000c0001d404078065040184039483e0072070304c0d0720002c80081005854070303039540e0f00507091030041d444a030082c0307051700034a110f00c88018400c0a18600d40343c1010911090144026440c483c02c80c00021046002d204151 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 582640206 1250 582638956 582639023
    0x306011d03101a09010f0e0a020403080a350a02090105070f0b091203041110030b0310061508150130020d05012103030c030609060b0405040c111009 65
    0x2a450007028440c683c01071004815500603400100100140300091600000b100c88294020100c1c4d10750042a40c0a44600c3e00050007403900020f481c0700d0303a40e00c10440302d11464500c00c3c20910241c4960340b8041c030000d1030504500da500e0980030903000c1c14554010104244141041031902145941d5618500c80c242d0040c1d07001d07207040c1d0401c5581d010621101c190f20240902c56455890256580c00e00211100c0c0c142e402805d9041c80803440394004c0c1c0c070801440b41d00030200c540380803007100d424003c0c1400d0300525005100e8018019081c90046503118000c40c0100d0080f48010300a40044030000d00c0d641e0308180300381401440703003000003000e5010015a0482ea00c090390310000c10f20303000d0580c2d0060707110000b54000c40101302c03207103240155003005461385440d0100d4010540141123025200341d410a149041c0382c0b9600081d0f440c0c030316005000f182e805980600c84692100b400303030340c40c02c16004c3e602c440d50810b814940c5c03610a40c0e1b010b007030801c4c850318180d5451042800902c07103941c1c0a4070b811 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 582641456 1250 582640206 582640211
    0x21302071103070303140711130c090b2a120f030109060b040b0a0f05040f0b210f070c05030f03010e04050c0f0d11040209040507120c140306011d0310 66
    0x21001c1c01840d0224503a01034058004100943c82c59500400390010742010710180c2201240070b1041122240d50b0401041c0c0043c2003999440400c9117031402050044800e6021500707044000802c0381c001e50694091040030703082030184000e601100c402107030510304510610300448001084107016031b806410b48802c1807079050340360360412030004200d038500e41250100c15000c2c80100000c20581c0b003120118141440c001982015141050701c01c0e00680c0c0044035040e5241501144291286001e007402c02910b105c120007040c0c505101c19290a0195070452604898200113020f89010b8002d0b8481c00c1d206d9411245000f4480d50000d406070400e822502424010f0310a000a000d000c21031001c008008440000343d1020700d500084100b21401c5006006841e800500840c0c2c1d542ca9041da402d00768007610034401c914100c00010045443c01035050403291501010004141c4500724401000c10540d00705891900c8020054076106496002684a807200b13403a820402d86062005081061f14407202 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 582642706 1250 582641456 582641467
    0x15180301021b071a0d02130317120c040e070c05100f0b03060711071a0c0604060204050a1205030f07151d1e07050105090604091e1116080306010903021302 68
    0x106040c59141e40c400c0c4c04010f82901c5102c1d81004500c22541800e04184005940b0b001400000300b05000701d5101401107180d81c2010814800100c1c0200421f4004c0c1d01100003ea69039505d0030030341e0107180070b0b601880143d0b134000348845008050000215010ba41100c13240c1041c84040001d45540301581ca20300c40d16003c40c0d00c0795040030803500750841003c0c1405a199000f801c040395541580b407080b0040d01d03180080c81102500b200084a04045807101031381c00b640b03040d0500d02d002c0c0d4013500c1124040c0340035000010f8210b0184c7c420b000b40700d51100245141000b0140300d807416405c1140300391030900151600000307c038800d201340c1042d401c0f0010b0340414845e020300c209082a000b0700346070043c0c80c502d51b0b82d00b401c103001040c0c0f00f06450303003400e2640c0c61b140e2580c04150305000700d40003a04200d01d001c1003c5000d0501500c04a09020418801c1c080024001415180b6008000c14480c0c038010b150148000251290050b40e4007002c10301d4280311a2360749400154020000310741d0214a107900090703 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 582643956 1250 582642706 582642757
    0x5130201031a090a0b0d231606171008030d0b010f0e010c020d0c08031c0606030603080a0309050127020316050a1a0906070602090109080601051518030102 68
    0xb000c2c900140d03040314100041d440e4010480915004000c8094240d413174030520310b02d5540046491200350480394031070b400c25071240383c0d1080c0d8044a14000140c442c01210044a0140f501d280c015210036036100204003e030341118030580305020f402c0e81403200c007251f800f01312101c041019024000c1e585c200403411000080002d0203451401001e0810891140c883d402c1ca81d03009003179080c0d01d5a05a851010300c40c45400c0c190458106a00b250201d80000106c1050540e00c40900c0d00b01130003590010010683d54050503012200f5510006200500a0001401c618001d90200d103109018200114000e100383d03410180041e110501c0b07503441c0c80e440303d808084d400c0812050203510210f06004c40414203000000c3c2602800d407082414074101c4240c68544100060166071515001800d1940c80701003600e8801c019420040041e400202c81c10300c009420880050104d0407581c0103041c40c040d800481c5032861007640808140110108404642806500d0910041c55041d000b1166105032120151 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 582645206 1250 582643956 582643961
    0x1080706054605031014030f01091209080a0c09020318070801020a0e030307020f1009090c05070203060a060b03061e090c13060201020a1d030c030708010e10021303060b130513020103 80
    0x442841003090074020001185c0701413501c5810f44140c42460100c02c00b2100010345442d1003098240d201d1350901c005d01d0708201900b104100416155203c08012940329001d880d590010100064403003c2c0b015402c0016084e250f0045420a22100300c04450b82c0180402600d000e001d0b0b440703032070180c0d8001920300038991322110040c84524110041c1d17160640c25000181c4c0c1c0c00001c00e1881c45000c4020f101440140281c43c9080100b00300401130000000c601c01c0034003103800002c81030340603020321350004184102e284500c00544080d10152815500c0351410700c0000450028840300303c1030412a01c144d10347d590900103108001d02b40c4516980d4803d0320940880414651010041d07a00602c18034110913040039000422064140019a1012001d40000e1070101905441501070161304c0000c10004c206402003a00248504200c40c44c008034034010408030b224111166120380400387d03040c400540b160300300200c3c8440003000e20782200c00c1e1401410071604140d4142e4441440b200f2100115605030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 582646456 1250 582645206 582645337
    0x9032606040614090402062b0203190c0f0e1206010e160807080403181809021f05040e0709170a02030d0903150b060408010e03030f010b030108070605 66
    0x2181c01003c1c1e90740c1c03011541e0404080c100910070030010403d040e0010386014281c02c41c3c2417030320310703005440300403604c0d58000d6005940b40c2c120308140080340c070f5103121507010741c00c0d0342c1610340d0f100d172a600041c040440300c1c0500c400715160302003180ca5004522010402403075019040f0034003c16480e06142c0c00411040500c03140d407109101801c02006031031900010034950058050130002d0740c02e0f50350303000b181c091f400325000030140006c5c00400031600d60785039008101c82807096030b140b50000b51a1124811840c402201c0341b001440400052005000c4400e4003500094141861211261500d070b04c450484a00050a44e256001514940a41c42c04021000d14a071150400001050441d00c501c0c408004451124254a8a541c1144015101e82e41240c00810b015002048aa42049100c544a82c0b040e208001e40b45140000400c5100500003264103e90030303803008024040c9440419220f9811005840300f817004500d1280782e06490310303ca110014804000000079800b904150900c05402c803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 582647706 1250 582646456 582646469
    0xe0d020d020d030506030709022205030105190f09020d0828050f1e040611010f0b012106030507030303020a02190201020c01030b1314040302060c0c10090326060406 72
    0x29285100441d40101ea50b01c0002400e29020500d0f03526080803030301e080c03016805140143e1001901c580b441c1c807031a400000150002819041440e51901050b090310301c10340d10004100e810f00140c0f4003500c02a4449450201c4980010030040a00e80000321813941c0700b0429110a5000a030041d0101c3c100c0304c01c003044c3d0b001c3c0568086001102a001001ca01400f040c01800c0c1030001584140ca01401c0f50719181101d40c5122035907613645440000307203d07031550a8040c4140d801c18550301240012401601007048042e07450110300b100b070b41d02d01004a611781404038006983d401c00800810380500c4000061400b03a05d0150795201d94800083ca00094801d050180c2175210280f80010b0381c0c040b90300d0900702c00900e80800c019002c480010076030030002000644081c5031010007100401c1020300300344210301030780984689a843c00c4a8083c5485544800d1004d50410640c15034000043c3c0c2c410382c2418000e04d05945051424150400d490300c0041040c0a20705005040080301d1500d800b81201400c0c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 582648956 1250 582647706 582647713
    0x20705101106010605070f150b010216300b07080f18150703020f070c2d05150702040207030e03210d052d04020906010912030e061306030e0d02 63
    0x100707500030707440e58018000c1104120700010b001e4240710581c010076800d0741c2c011000c001020000f4149400514440407045d01500901e04140078843c2e0031414001100d00101c7c82e034282070134050700046015000254244820110000600031840445205115800300e44411185040c414121810407400824280640705206021002000081600d02d500c07054000803c44030307156584140c000c1d0003035a00021100b10301054540c14031000800310405c4540042d4403103031348190501996a82c0d48003400780c001d114401c8400704400c2c24895000710146d54064020350601d4020350010f400e80c2d00035030040c3c0001e4490310780c4014500d414071820752607001da0728215121044400350750f5020302403c54103d61040d561400103140c0b0015100d40e002154003e40d0040401b03c50500400c500c0b2400d65090703000c1c004001c002441c03940954503203007d80c0e15415920b91004043d0758201e8510398000740701c98006005022601400034121a8080500303116200441d200102d8580c4900c0c20042c41d100c0b008560 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 582650206 1250 582648956 582648977
    0xc0f0304063911040e060a0f180f020406050402370210091e050619020301050f0f0f060c0c0f030312010302011103040806010f0e060a0501051819030302070510 70
    0x280000a02c050400601044100510710b00703012205221051210360068280b11030400805c10108485100300728902c810440200162542c1d800c490302071150308c506c0e080801d41c070f4011034428481a00f03480e20040c004200503848401140503600000c4020b85410800742a0910f40944c1c1c0039a40802e500310301c0040407245e4a0382000f50f40d404000785003428640d0b1140c0d0030050200a002c4109603200c0d40902c02c000c1c88840c035205a5885d41250307000810254884c07441c020708040d0003164101d5000420100450800204000340060404002a07101344070843c500354648038140500110810b40b800341001007041c0080c0810f90107054240c5220303410402c91804240208078405040d240c0a1038203600d49030881d1103685c614030840c1c0120940e4810304e400090f00c2d10301d600000040c0d0f509010814040d441c1d40050203000b00440c003c680c00b081c81400b80590300c04640d0151200c0460040104041d50b000707003503503c00c1d02c115030416401a040704101348010300b440203007200058880c3c1380034801039 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 582651456 1250 582650206 582650267
    0x20d0f0b1f0504180b0909060708010e010315050702010227120105040b0a051b1c140712050a0623150708070303090206070605130c09020c10020f0c0f030406 69
    0x740f2850241c00040e2482c420b08903450b010b960300480008001400c03443e02c505100280b1562400c007101c0800000f1600c03400401ea42c0c40c0640300d54100c0754000c1d503040315841c0d603500c0240913110007002c9104565080c0085042c0f1008954a401d0f4072074410000104400410103105000d40b600d40c0b40542c40c0c0c100b00910000404480302e081d0710401014000a580c3c13503952501c101e0514440304008030700d01c0420400c500c6a2101350b0100121040c4400f0001000200048101c64500300c81c14030103d14a401903812400998000d5644400c0740c4c9000900c0740d031221808403012030000b1a45002240144071030486090484440100001c4004c219081032125942c0840ea4804d00c00e000b030802d62500325143c11501c40c01d00303441109501030340a01881c5445810000c030b0300e00248003500c6100401c2c0000070100840d200b26180000c085014000d05070800c80c091010790301c40b91900507400702c10009589040030a10100c8444150b020103166a02d203040001840750044600280100c0c58010142441 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 582652706 1250 582651456 582651467
    0xb040c06021014192c15010b0306010309020321030901050f01030c1403070b0c0a0b0a0509031206060702040501030309092003060108040314130828080d020d0f0b1f 72
    0x45000c951060f4131400c943c040200c09400209080003000200d0b5000c40b064003007a4001c690038282003012502c001280081c01c108100e400e10400350110750800c04101d065200e50004100720780050121200440c5540c90015248c2101c0c01c9008060360200601141803001c0c011705800c1074000c084209154150703141c40203441d04c54486e0000405d42c00c006159152018002e0300020106088115140d40001c0c80c419124002034000700c1e001d69020000401d19070b011b01c0b41601403010040214100a900302641021060284c1210360015040c4003001c010395490013110b029500c00c3e601d04c1047c514210b248010344e00403019950000140c8405250354009020036179601aa0900e4104a079468a00b0103584107503124210a8032004002024800b2400e2961114202c0306590125441c044101c0c8080e0144007409850801010303e410101000c41d1135200074101c0041031000040c540405441503604855440040d094551340b1000404210b10b0460010340c8890280012500b45841c041c100829 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 582653956 1250 582652706 582652711
    0x50a0e030f07030e06040f030b1029070b0732031519030803011a120402061b0604050d0f2f12030103062c120d02070b040c06021014 58
    0xa0010102d40d060505214200000e01c00c803000d000b0a03075807074440c1c0039081e00911600042d11600c08403000304401c42071858000084481440c1001c112074425030b09004945111440c060040c0424080200481c2884081500805031601d6903a1098000f0310140c0389c50030910a9010f40400030201a165058168101c941c00b003110150100c680c1548400154203c0ba44140c00041003d813030702c0802003201002c01141612030f0b003010604102500310004409115034104100100d07008804540117041c0440501000c0b050070b04415003c0015031245803404004a400b51400d920001e0304100c0250000c00c0c1034000e03082ca20744103030a49841942041c9265100b01c1070360810881e24a0046589418407954402004c1c010000790f403542d49060030400f80c00410342040c0d0b04441c0215041451250103d550040c28800d4050600b105920904403a01d81260341c224680a8082141e180018602082d0310b11491088089281050815000074039000c0506840e948440c03a2901149000000c081040c0e0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 582655206 1250 582653956 582653977
    0x303100504051e07051e07050d0809010e0309040905071d070305180a030e03030903030a030510080316031803020901090905060903040f0b09151c0b060a080103260a0c06050a0e03 78
    0x399280d40059085038104086c4a11400c031b0301c4003180b0341c0308001e4089854418104203580d814002e4503091502400c8400c410110085a8001c20050703905d400c0680242400c0c42c080d0090781d1180c3e0342c030b060460250209030b02148a8078150010424503d07054403035150000500501d5081c091080c1d1002c90391800002c2020b07003440880c1c5815481030340d040045a0700e60764040c09603a140c1c2c00311200a0007404050764808010032409001182c403100000540342e0741c1c481c084050301c3c001505d4030146c83c4915400c000315200740d1822404005a21244030300e6008140c0c0c000001440d0606040050500001808402c5103400403c4100618400281c4002c1901c024283c455518440c40c80010a2030780100101524914080b40c1c1d00754102c446c0c03902c61407103880c244045c00800652010010948900009900411031801c014070105800c0b2040040305000e424059840307082c0c0110110154002c10305680c009150821141c080100c9800b842c1e42002c600388040c805d1000190900341c0328002c010411 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 582656456 1250 582655206 582655217
    0x411070b01060c0f110d150c23070305030a0e0d091d0c0418020705070305060712020c06070503180a051b030703020a05040b06041d0105101106070f09080303100504051e07 75
    0x25110754680914180140d4060030447d140514410107501074081c00c41c0b66000f25104008000c2003070a109450701040e00d182d2034031807621500e40e8040c0c8607500050701da8a0282d0b503840d02128001010042c1c030380340c007005448ae0010320703103030400844080030171000d03c0303a50103840814000f840003240d0075501a6074400046004002003102090002d006d008000f4086102e141000010300070080b03022401528a070759510300601c500b01455090380700343c4c088031115501090005500034412b03030145401071650710340c60900346955004940b5144800500783e0f443d030072901c960103038212102000d407044c400640c042c004051035500021121100d9125290289480304200e40455583c03004603009056140b095103c0d4400038140b01058003001d0050600403080c81c030407116414002c2103801c40c4040d1080043c11190394000c000ca45001185511000b840540e090214803490284090761041d03115500340b6901c03038038060070001510400b608203a241600000d60751090100c5a941035071100240c1080c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 582657706 1250 582656456 582656483
    0x105100501020a022101151217030c120618150f010e010c022803050102071b05100c23012003010605070305180a0314060a11070605040804050411070b01060c0f 70
    0x45e5805014003400d011406118010302080b1003049414140316603020340c0e007007001944c030603010400900c03050712640c003080001c0c0000705901d00030540059129401801ca850107421140300043c1800d01500c0d54034058010310103903540360811440b01403900200b442e00400c0c80350010f002800c482c5000b84003034081c0d07103400d00413000d0841000761a0060b8020106402c41d0341da480c1001c0c1e00070340024808540754519a254000c0e4052510480025503200422a46084006100a0f114064408021500031006145900595403c1c80e0140010940c0e20000b103610034104500400b40d02e2001440c0d4481c803000d000600c047e41e404010307207001c40d074141005540c440c2007686a040307201121141a50003a0350002c04020000c8400c3c00c041440000802c1b10895154040d03a28240c481c55030250396174031001d01075640840c405070070450f081409003407843e15007a112000700301501c050042291001400040c0c80c000c0101241006004056030314003403e074010203666a0b032a94900350000750084540318030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 582658956 1250 582657706 582657769
    0x12020d120e0319050a080c0405150a033c090302060c0c070902030c041e03020619091d0601081b090d1b030606080f1212040f05030c0105100501020a02 66
    0x32603d0200e1010321030640b0f142c4154000380710303031300c604807040c00944103c01003001c83c04040140c8081d918010709460024080940750285500044240c07030415880e45201c441940c1c82c400b110300101540000b1407075034404004d51000c030001c0301c00940465460003801801180d404564682c00c4040b458241c5c2e0389410034010030340b400c0c0171500100032440c4000705010107510650b00400807105002e48111019101d07038644010740045120180d0803a40403c42d900f00b40c51288041680400c003410200c01554945000031030400f21188072401c805003800c14814190303040141c00c0d9120580181e46492581d486130b16940ba40900721115005e640c803618160104484008031070840c1c2d0042035000c403d940e5a040500107094103120300c1c07096008240e000c1c003100e8400324402005a02e1804654a07044c00d244804402d144010b209030b814050300e03c0c3d21710014509200501c0d42200307520000c03500b81815880c003210505150702040c159402004890016218110741d414561070161001010189500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 582660206 1250 582658956 582658963
    0x81e04020a03240606020c010e1909020d05340f1e090306060f0501020c13060b03012714280207031e030207150f140c0712020d120e 58
    0x200001d002280d90324004405290601e1400b0120300031010500032585d5850041ea200d00c8120710b02400207040f00c1c00e0100c40d041000e500c46440341c1c0312040504090352220718070100d800c045c4102e024691210103021801000c6241a622108003101c000080c0030004405420013906441d10b8040c444148060302850b8040d1803690605140079043c10503107280610010b007003c4681c04115041d51a026000c2000d604901c1c0f130070203480047e0000c052201821003080509401c4d081548001601c44a000c1403841844014600a26444c0d5558090740c04218689050001d28000420b03480c1c500705400e001001690070301a0011441c10903210006080d00100b245084030a0b600301c42c3c0c1c2d0002a180040680c064440c1407810038a800c3c40e5402094004204d05074420b405000c2c144030080103000c00020300582c810741080000100018a49100b400d840e1801d95003120010030480000c20300000380600602e54a03000074080c409040001070f4a18051315401003110352401040d0303a00c5800355010402c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 582661456 1250 582660206 582660209
    0xf0f06030c051201061107060302030c040b070c090612110628030b0406060f1103090d0210050c0601060c020301050a0b06030a0e1e0a030f0309150504080702041416081e04020a 77
    0x43d000034042d07865080180c0040c0c00c24070b01200d24464100e001600d18424800d8a000308458603105140134034100c4a07038502c2c1c00080083d01c511402da980000c102c407407131044e00010b11480f4003030200c000381d038100107406901004a090052038100b24502c0d080d000c40e5510301c025149640d980e40e9041c040b5030124010031191203140d403c585410303030104840d6009030301c42c2034111032592040d88280c100034070b403038890113046140b5401c40030f0240e80380014505000c03404401907943c40d001c1d040445286000386007031000c1c4c1c488408260f26140903000e6040a000b800d80c0700e1082c00c0144079080320754002c140140f100074000000c59541d91024110b01c0307828003200c400300300d0741d00d81b0070518500059140c0e102d034100d40307040b004641c25000013000b1a0290246220b1107402503805014084003070019806800020011107039074000f085498010390b940c0c41542d07411401404040c100b131810f038410075000b240060503a0f0a204c9958104250b414890384030300d60a001d0b5600311304882c4c0b12440403402c05d0105 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 582662706 1250 582661456 582661477
    0xb10030216120e13050108160f0b03180303010605090109050f030c1e04140708070c03020712080f16150b09192a140403120806030f0a05010b04060f0f06030c05 70
    0x1141c0404c1400740d02a003000d0b069840141c140da042c4840b00034654812207181c0b00d21504080c405608000c2200040c018640c01311300c000c1d02001d03000001e281581568400d030044804035034045102c0c0e4803075074051280310203081d05450040e400701030580000d503100080d505c4140b0850110400c0c0b00080d082c2c00100500c80c0001e003040c403141d4002600c070300006004a80883c00200340303a0004203290301c1064171403e100d81517005000d40600300343c0c0030828006160402e407403c0004106141c0e540d5818801001c061101404a100c1e2100701d1a24402c1c007001c4403802000203003040e14030142a07039580c3c410b035004405001280e4018880701c090f180900700f0b170340050381e4141441100c004040701d0071450000402d0956101e450180ca103440f8080e0724007407800050b14a020015130384800c42e018188068001c00700604840407060300c081d140c0c0c5842c1003013004980d5039441c3d102c02c44039800d090007400c02074031200940b44880c0381004100803039080c1e00e10031f02d800c0548500100001c40d004404940d8200300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 582663956 1250 582662706 582662719
    0x71505151903021c0305041701231b040510030e0f03040b03090c0102150403030506010c021306030510060302060702061c02030f0708070e011b1407090b10030216120e 73
    0x10408001201ca410510090b4091034049442010b0f4502080c0c6450700c45903d91161800e203400d01c022001300307810108481e6030315944c2d458001c64269018410342107000848011408901d441c0598020400b603400b00318205640070710050ac074580e14661006c80903c02440c000482c0a51062a68503244080308502c4c000d00000070f002c1b806200700302c0258450035950084481d104224401265501ca214000302200c03100f110100300040d2280d040036822140500d40688e074601d941d000100380040c0c0d28500c41006507101070410030800c05201090515501c4d0004000c031900d541c012500601c5403880c0281315840010f11944400101c0181e00c0350001214811501c903e800e007284502148103403006c4010810310400540080c0c4030f920b401c1001c0006950700c140000c3c00c0902e081c1d50004514040305c1101d03038100381c490003035070810454000300014a000300300101d0340818001d552480380003003010140104404040c1c40d201224401209600600f400030320708108030102c8410b403484151551181 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 582665206 1250 582663956 582663979
    0x1709130c02011d060f190207050f010c120921090b07110a050913060b030102121f0608070c0803061c0c060e0409110d0203030c0312040c060507150515 66
    0x150305501c0340c0f00510f9600d4001e900d00001d50010b0b59201c10440300c4141d03004003400094400110701460580d140407101c009810b055a80d5103003420000040304101c480e079900d0741c00301c503907a41c07082d09420501c00c0210304002d000c0d426190081000903040480609028504400c584144035507070b420f000f007124403286500e5402901d0900040121107203400d115035803c0c03130081560f140031a011405026165445a500340b5183d440801500c00507101c15419507083c01018140001c0a8a4a01c01d1807007200071708001e03034500d0501e81d2443c266080038040210b05820440e119402c41c1c0b030007040d15001002d03140c0b00e80d15400080d0074088880102000c07550051111000c003c0c0c200d2615081e124151600510b0ba1090310501c4100c0da0361031400340080306807012025040c00d003010341c10f240313a0002e02500d01d000c031400c0b00a46540d20444d106200c003105c1d141000180b08007049140090561440d00c1032501079243c548260440140500b0081c099a072804203000c0c1c426901a513082802c090249210361 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 582666456 1250 582665206 582665231
    0x10e040203010f020a0e0d060608011508071401080c1e2a0c0105091903080f040303080a0b1f17010b0a0e0a12031b050111030105120703170913 63
    0x4050a5a04900035800c0c0f02081d90410603034002e90f240d41c0c070180d89400c4607404040401c02c00d8151114207544851340e5840c042410030b001c0c040d400b01c604004101c000d00c03900d440c484524120302584412610290801d82c82400da90150081e82c1206c0c00f82145c07601c2d441505aa5a1414494141980b040c24002052403450b200310446c0e8104000310f950865041018244160321100c0012000e400100c040084d03d20a09d0408110307410401010500800f0a0b1a0b0f907d00d04c150b4010030424030300e500c011a04108140c1d004044030341c07080c0010414841c6e0201d01c400310741240702051441680040103002c01e60a90700c917556817500310104504030413165035600c0c42000a503005040440c0007a14a09800c1a1420300400180c00c8840c1d00240c0320a004050724119074544189840c45499041e46110f800450001d02420001500741c000c0c080da41d52502e4100706c2201040c180841407030300b0584040001c140001d0781c02400544407400c00c0d50b02c56403d4001030450508101b180b8140c3d14120b07590740e82 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 582667706 1250 582666456 582666479
    0x14030a03090501150b160c090c09051302091c1a0403030203100f05060f0c07092301120c0e150409140706170c0a1422140d080a020a0b01 60
    0x1c0c540600020856800e8050700702e0001d07092402107443e0224208001400e40d480183c020460501644060004035220b60051040d0b81102c0541c900081882c00280702901d08080781c4c11111061090842c504600200403c231048403031006049518203564807030003401999241050030a12046400b00d251a2038500500290015501444c10031b4603c1804240741d4225a6507200343c5800500d02820b0200300c03014000203074048002c52030345004400d40020003000a0041071007145284040d00007240303848504c1026100164411286c070413100311150080b4001c03030f064030700340d0340d0140c200d150b00e6481c0e5488a507585404c04038960064030f010320b607405004000f0340c1d14101c1c10401d804d591031b19646810456003103400e41c01c2000014070b40c10215a122050300010b103000740860a00e00281c034452000300c1d515800c1030321031566014035011052095040c0e4021034014180e141d20340c0c2130221807600809c245800d0340c8401080034900150103c0e65a0003041500c240541c0402d0000c600c0da150800c6000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 582668956 1250 582667706 582667721
    0x60a0501090b01020f030d0f060b1903050f0c070b06030c060d0b0405010e060102060a05060f100f270e0604021303260403030f12090b10060212032214030a03 69
    0x10801c2c54440c82d180e5540c03020681404640d2260011818501c020035004020800191540d201c16920350000a0701090f0270090311098400e030501300810400031401400b942c030000d10b19071444882c04104034000303403888140da08160f00115030f10441d40d100310100346441041c405850340b00d80e0214401401241e01e80140c00402c40580c0c0c10703c440e9136507141e0f03500b100d181503403141d0150701300d100040d0f95a0b0580d4000c991080d001080054201d091f5000b04a1b0580d60184410004041010005402e81c114040089210700d03c101e543e550043e00c00c1440b14046240141d0116502d203602007070f0103664a8050303401801922100855059407484d0034156041c03144001d942c200c024504002d980b252318011b4804030ba4241e16011070b144031482040303c0c48001c242d040300f070307140c0e4400c102c001180c00b480b4820300c41d0440880e601035031410301d01c001e80b800340b00317411041607028101708004a0151440300d01102c0b4400005010030919a031801905409013090700544622001c1244003085038140c10038034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 582670206 1250 582668956 582668969
    0xc09010314071b0312020a05030f070c03050301090c0e0301241a0412210822170f0c010e070f08030a0206060f031e030703140a09050103110705060a0501 67
    0x8000c40304004001e0020807100301021401103c05031200c241410100c0803818440c0c904101d042103116119000c03078002c412458006600442002040b013003d923407958001620303090100e00b51040703a60041c102d2105000703100c0c202e81c0798a02402d00a0180c06140e0440754010001d004c2841e012940404400d040311051210704c5550707000141440c04019504080400c0e500064581410000c1580301e40242d414101c41d48040040001000380c610300e0105d404240c141d41e080e09034200a002000c1c1603c004046400c00c00c4481d4014000409d061140714043c1e8018544580350303108070489800340e000c4d800040e206542802a661081c071700100b8000c06455200300f408a0743d603180c0c08060758034040c50a1040240e03105a01043c5140f5090100070340741ca0000342205c03d03500c41881e921114440c01c180c00c074072581c8041240d0b401c03d900b0a41142c0181d2104d201c1509001c010003005000c2c0005101c3d590506a543c01401d58502c445011100c01a80002c116a03407428244450300c0142424801c55 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 582671456 1250 582670206 582670211
    0x190e0c090406020a0315061e090902120405101a300309130207030c020906130c08010e0a0c201212090f060108030a1b0501060608090c0d080a11150c090103 68
    0x50590b100d540000006941c46a5215040300d440410b003109a448948c0b580010f1004030300c00010407801c580001d01c2c161100110382034990070646000b41c42c202040603d41034144c1401d83c10203039044a0141142982e401302c074803101d43c01c031300d00b0445210340d03c8410000b440510559280034501f4004011300441000b5650040051440320b0540700724050701c1e800800084a8000c20005840c0403441d140e000761004008813a10600c078441e000440c0d00300c11060700032509100042000f0741010500c6640308401a5040c0003600c01120014103038100e6500800007600302041c540e4000b18200004140070f4800d101c4159600069034a082600d44105c0b000c01440c0300c3c0c401901c03094003020507124100c0300c2c078100442c1000010341050703506440501e003d240d0034a20340c005a0108800b4002e103402030003540c503051640d040c4202c03c2424482d0086c1400c0c0200c1c2030040602c005003044048440f801d5251402c40c0c5298001c00b0402c0c10041d010004440000300101030000828400004050491098804 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 582672706 1250 582671456 582671471
    0x203040806060303131e05060a0909050105090402060909130c121b06050f0c120a08010e0c0c10021605160501030c02010605060a0509010504080d030203041109190e0c090406020a03 79
    0xb01130341c038030880a512a000b1200c03c010403224841c100c44107415000500a040050f807140041002900603140d004000341c2a92802c10000043d8031856006d08415101007401e841c2c90b4003c01c6a510801c0c144074040d103941000a0b240c4401442a4444aa803014240e4281542c1c0d0010003510201c051050f00e01a038002c0c04080500f4001c40d05404440b015240d2a0408005240c0e0180a4124000c80c0c5014003030076a0048e6100050b0004000044490311040d00c19410700d0200462020010690704081c1e908010030801000000380071a041c0b0b201c0c1c400540c3d1200301164868004404140041041c81200a20007000c08204c0301d1a007507030307000e80c0c007046002d02d9010300b00d007a034055100d40c50308054100104c2c4015403194000300807205c0103040203460030f903484640c9403170060703841d680600095000c4280001c119007800c5040c0541d0041350001368905000c881034180d0b076000c9007940c007204c1d55000700c2e060f191014400b1f02405003009080d000e00d858a41000000381d07114200b00f100007440d100c070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 582673956 1250 582672706 582672709
    0x120f0b0a0b100e09150105070b0405340e0a0609051311010302122a030c0a1d060904090c050604080f070807080d11150108250b07062a020304080606 65
    0xe10551102c010401946921031701e43e403c51051249524604210041004501060b03c1811440c0502c0c42400144a88200407070f4401560101d1041c0200c07640d03600107005800040d09030441e0a0310310100902e0b2054803981c91203401482190b1014420600b80b404000d101100341164120050080d00840030001e80c690046040344524801c0d0200080c544c8042000e040626103140a5500300384540415001d490000ca6140e42003100c0f0004000c100090310644036a200041605030000782c1c5280c4540c1c0d4405000421501422105a014503950003a00381405075002d059001031070041c100a0b6502e8940403619101c82203115980c82c6481203000c005040480014018100c030314101c0034140c81640040c2c00c81c0e41d42d00c3d020119449201e10b0a9103003808810041d410b0003482e00a0042103800103d5600354221031120400071307000a51080e00b0000f00585a0807100620740c44400003801000c0340c000f40c0d800d00061821403201154602e0080107a030740000c002e209031b4007000111100da0341c03040c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 582675206 1250 582673956 582673967
    0xb01050a052b1823070303080406020c03071407090903210f061e0506070b04020114280305070e01080a09021309030503010305190f03030c030e0a0633120f0b0a0b10 72
    0xb1a00c4c0016488114100086031180402940043c42440301615190a0110f0207144d03400209094844509d1148044402103007005400024191400140304070340310b985001c3d014004424206026101000f1481d040c2c4283d42c6c011800030600c41400c004680e101d04e4900c15040c04441650799a032400342c8003141c0d6140240c26580041e40c4803941850030390784c640c01101d10078200751100c0c0d80c1100500c20710350740c3c81c9540d40440c0c040940145186040b036104000505440000d0302c11814003c0c5d03520100040c1c2d904c0780c1107a601100d10040130402ca4120701c00716410102c0210127000ca01e1074444000304040d40040114100c0f80030f142107816000410145422481c44400010405045201200000b9000303401401902c2d01c107050012340c5e0070700100305604264a0200845070680d44600ea20403070700105803004500744513001d601c444910100c401211415890142c21000030450580380c0402c01140c48040405070310815800750f905108030710310058402440700c03130305c5144860300d041042e07881780 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 582676456 1250 582675206 582675263
    0x1180b0429030403051c020412031e020615030a14011a1f120e0a0609060f0605090103080c0106051c030807050f0306100201060521010b01050a052b18 66
    0x1c84a149161070b10740c1d0544a540c4864003200c01e2041411903114042d400c0e00c09000140804a4001c48501ca2850000c2c02061003842148400160076004c8051560024166502c00d04030140360728501c4040c00040d141c5032082c00300500d4200e48003c0c1164566064103c00381114000165906034040c440030010f051610801c1e004ca14007846864900a40c810144035015200d1140f002401c14001072205080c480090b2003562880e0311a0302c1c003000c001d81c500c2941912541040100b00302810304000440005045c84040d0040d040428200c101e5031082d801300008180080061440090602c84210b17800b03d070b044180c0c0400c58400008444c0f0b40110103c0e5040402800c3d5907103190f8940c1d040050301c2ea503498050301199030320800816161110352a4000154514804803c04039180640d00e0a540c1061101e5042007000c0c02903510f01500a001e031038030711284040c12032f0045031701c04141501c528080c0c1008280c84c01c228159140e43c0991800508180c01124280401813203c840c5400c0745481 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 582677706 1250 582676456 582676529
    0x40b0615042411150408040e040503070c05040c0e0607080910110d050315060706090818040b040204141c0807030c031205040201021c0c0b0c0a020f190201030b01180b04 74
    0x100c68130307540c0385450000690b88980706d204440d042541320301c95448060b80441d0f040b952070744001201014400701c192020018034040380c081c020f88507140d41c0100040d4030010000e0140e03501140510800c0001c0043d601103500c003034501003105a440e1380090a00183c000c030f420f070038000c900740108424424000c5074403464100036040c609104260600009038444031007a50166520094440028030b00ea0003808022041a42105440d0f9000100400ca44a5416440c881d41c81040308204014440490b60001f90b421904032800058040520302d81021040b4018407031240020361004164011203041c107000d01941e04e050600c1e4200d40740b541252800d48020f800b43c4d01c200e030a9124406c200c00200b1420480349440003901d410b030f549159002c1410348600d55003c0005c45c58502d00340d41040924142d050f080020031107008076115071508010341d0070b8003a0402da00d444a42e14241d0040040c01c10382d80c0e5a51000c80e805a491010b034100350084d000e042e05c46104900c900302540140410300410200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 582678956 1250 582677706 582677713
    0x8121602071a19050c1e0606060c1c0c031707080a0e030c0a0c06020f1f0209010912030c170703140d0929100e040b0615042411 56
    0x1018501d80400e01601950080b003401040300c8040c1850f0200742140d1214142c0b9150344075001d414015041c442d40000604c2800150b00380484500000a56240c01030f00c04c3e00c105585080d00c260a0342131201c410000290700d0501c8100040042d80031712802d240c07600030754600c5ca46050340c3e8201e928182007500c0720380002c1c03001c1c4007140750340000b40d0019600c0c0004030708891901402c1c0103041d0a00490003410380d00880415000c0003066014841441652114405008690300d883d54174514003100350440c3e60380d6640400c45500320b03401144080302400e61000100304020407450010300c55601034104071a040c1d00d4411035044c240703580b020794460342d0b4581c9401d048061340402c0041550401c190503003125450740c11400204003500701e1a0000c200c000303010100401011134040b850440079140704c1a144140034200074100d0040205500103a021000c0c41040e241c840004014800380c040706d0010010012b00040c08a0f046010208405040c00900c100d48104980603601030038007885c0303c08180c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 582680206 1250 582678956 582678959
    0x320060403120e011206270e0d0e0105070b280501050d0303090c05090403080708060a03020d0209090c04020408070906090b061b0a150c2d03090201050409090812160207 74
    0x24003480340d500140c601071418001c2c031104041c9020a41d440c0360f1214121114800c0001416400001c0070901c01c0d1940005008d00b51800000b65515050a6449000c00034030341000d4003030342e1281d021180001e8100d0800b0003a401c000085444810342000000c40c50707c1c0d100d05054615105002d540d040f540b00800705040d060a0f510180d0150002400460340d60b07403004004600c994810110900a9009564003000c9250540c03000d0107001d805080035219130b4402a00b00010fa45548501246560580304820b82d5100c614003507103020400c41001e5801030003c2408207141c400000d5640c200c840b40d10050000303554889850301110700c01e000480e005101004014003441240c02c0136034400346000e0486100083e60b840e1403c4600705008070062036901c4c0d80c0250304840d0301c00d101e105407081030310701e0b01041c40d40000030701c2c007a0b0380311400d0750185912120018150b81c000e1042e41e0040000b08000e01c0041c46500d081c4005501c0701043c0c1ca6800800707008a02e0000222014100801c1190000d22041c1d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 582681456 1250 582680206 582680243
    0x31006051522080105090d17010501051b12130603020f03010e0403050c0d03060f080f0d080a0b06040b0901020111070809090c0c100504030210140a0c03060e010320060403 75
    0x9074402401c0c921082c0b2080c08a40c1d0408000001074010041c3c100005a0750074014401741c117190031601140304000890075080c640e000844842c43c1151000d00f002ca41c1d46050110300c02049a00d231071a0356442c0030304240e4201c1034a5002c01028603942c02d0410001540e101c82095040b80560300d03443c480407405000600104000001042c0c0090190400c1410300e500002d5003032500406000d45c10000341c03030742010171660080390080405403010201524082c4481401d050b600c000041c05241004464808250030307c1e620381c80060400005481965100c0d220421185282e002c42d01c0315005600e4038032150404911401a0b81c80700c0d0784038807410b00e00480e0300200288524050100050f0b0382042009140c1d0040c01c10441060f05000040460946800e040180c2806042e10032031b9159820300154405810450680c264400380140d000640a0040760040340245410740184a0940030a00044140105441080d1210340c800a83c2c040050707401d4188110380c0202d20000348542240d04a45104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 582682706 1250 582681456 582681499
    0x10031202061630020403021309020414090312151c0b060d02011d04020d0609330909110312031b040b0403290c040501120207050c01050d092003100605 66
    0x4000c0f03414000b500345500d0390009000240c1464a0800c4c10f5035030420401103003000e00801c04d088811041c01c0b015441c221144644a01c0780c3d24100101d1100c410014034841080380c1c0b20301c00d0340300241c403110700d059802501030540c40c010113096440614a200050062500d4100c00c1c256a03030680d600d81a045c02011304401404d016004990b11a400340811461203040d8030a0300b000741201d200c0071490102c1e64a1380d0150000700741c40080107171001169403413012006c49402c4215103001c00001445a11410315030003030700c10021443e03814040d5a80303001d1403421020146011742103001a401511400804c5074103540700c0d5100e0f80c0300e41c1c0018041003011070344040d902c1c82c02c1c004e110460800c1200e070041143c1c07502c0d01203800301002c1c40085024483c55902100c20155852203840c11031824140da100c4941c1c03010150322650402500213805c9021201c07039001049860b40c4090880300030311080b2803400013800207104c500d000388030b44d541003c2c0f007480745d0298a0803110094505466003640d0f00c0c03c01d82c0d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 582683956 1250 582682706 582682787
    0x41106030a0b09040f140705151309050406090c15021f020c010c020741130203040606033005030606070f12080612100203100312020616 60
    0x421942d600d0001c0c540d80c0740d07218218440d51041d0080d585003070342c03841c1109468413062070168490717000b240306104035281c04904803402281404503503113031000d02c03444010b2520b05400c002d0b0801e00b40000e0108200352900826015403140c0505160a03840d0109108a8501604e5800059000c131402442c0d0f441c8075198104505a922000b40c5401012503405080d070703040d0406440140e00036002001202d101307007204010031494003c01c4005192004041c00013000c1d5903200750701110282d80100c240d596403036500288014080066489213030904280780209518401035070414101003102d50025427204080011203503452280024030190442103402d600010480e0b50025002c01802c404606420782c1c04d07041e1841081a14507009001000400e100001b0f00018002c48080000384c0040b10702040b200d94461074a200140c86c0e56030109a030180b401142d00c051702c05441c1020020b003507035000c41d80b14803401070704600780560301e18014100c64000002c81d640d0301a5110113081c903004505020203c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 582685206 1250 582683956 582683971
    0x120b1b0f0d090c0302060703110709090302030d0b1c05060402090a1416091805011a040e0c0306060d0501060203031e01050117100306021204050c030a0305091c12050702130504110603 80
    0x15a440c2c6a40c04182e680d0b07c86401503001c00c55640e42c0c0b005580b401c11004010f0010010148000d0f80c0a54000e0f6503030240f40c0a85022a032110107040c880d449140c29051070340030388401c504407401942002d03900c8580c10398060740901c014130300281c0c020485015040361051080701c0c034041551603070f88100c80b001d01d2402c0c11040080c000c0e4001120091002002d00b80c1c0c10643c000a029490106003032101700d407180020300f60303900c148020001040c030540d00e2039001c0c5200c0340b0316941b542c51100196a43c0b080d546280b050794034110010503180d60010195101e152040701c3d8516581c14a165200f040d42d0922903075000a04207410003002e940d590b01900d80181c402c2c0080c41049031203640d100140c1c3c109414115000710300d04100001e0210070004c8116481e0258042c000003a81510002e00900c908803a15004500b4800b041c55600d040d80c2c4041c0101c0e810114444c02003000d5400140380d035011745400d0707200300300440c9010011180780c42501d01490740642c00e140700801203024031407a60001032002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 582686456 1250 582685206 582685223
    0xe0f0a030b1005060309010b091303091a0f0d020a0f0c050c0f04020c0a050d09151d191e140901050904020613060c02151801110304120b1b0f0d09 64
    0x650391301c40c40051070046a203480042244010b03038003404540a40284051000c4050603a41e40c04280c00410002c00e81e241010a507200c403102c3c3d082c481c4a4418408607444103000000c50351007004242c2e000c1e000c0d101d4561345228081800400c00c4032ba0038003400000e000d54005030882202e03441d16045404108801500c05030400400d5001e2a007840e0301888291500c0c1c002100340d00d5002ea000803002c024019000b00449400352602c0020020a20090340600c96040c281028645645030010000c030240440240346140d51107450103d1948840c20b89801540308005c008038005407d0159241c1a580262200010340e103840200320408001600c1a41c0150042240c0072001c52116003030310144c015902d0350032913204a403052041c6200000090000c13810103000d20f008010401020001e83d2a0904e4541c80c4d42400c190618198030503640040c201d969080f00794002c020a22241510490242c280c4109219801d6048060340c4211503180308801c008000411643c4010383c40803410f103001d011030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 582687706 1250 582686456 582686459
    0x40506012708070e040305032205030a1823190b03042105040e061306080d02071502030c06040f08090409030315170705130b03011104060e0f0a030b10 66
    0x5050441e40e090451450800003203000d01c621001041650010000800034266910f0030b40c07002480340c00050402c82c1c01c08203203090101e000131003005001c09d00d6000800c2c0c90b5a0b80800001601040404600505c018000100029803400c400e0600d01c1d12000050911a0703c44d509040018070691b4208001040c11011004680d800c0d044015500c150301c00c440c03017a40342200118264062000d540003600f0090104400c0c0a544d500000701504144140c89600c00410368841903c090103968000c0200741c401c4061080c04542c0c0081d440d000c4030240112200ba0810f002c500702e8503841401c100111a502020100340050513086400018a000d030a1035400c00d902080000c0a5410ad088242c000a45884200315404104c0d0416402408125094007162803803c5e803460325402c6e184030302c070304c20b10501340f8510b0013003040e0b040401e010900900030810b03030040d602c50300b480360054016280040c525600481c00f0f0304084981c0c800303401c030081a190003079141d030b50f03001920b400c01000980300d140b951130b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 582688956 1250 582687706 582687737
    0x712020d081602030a0806311104123e1212030f100911120a1b030e030d230a020313080912070315150515030717010e040312020c0c04050601 62
    0x400c10080d0300400da07031583d5101c08c24120780549140b48048102204c04100812824a00f600100c0d4065406007103455015190452246203d00c00b0250344800e0b400d142504003c02c40c406642d0a1500e030490380c80c982e0098800495584103070026964a20750803c00c01701e02510304140d4255801290b0004820300d031a200c2c0d400c1020b5403900d400001d022800482c06001691406558661104071b8103c02c02c961a58030440f10003200000389044181030b034516511011140c140304659448030501030900c4049000b022180e00c6111b42e12002c40da14400d403000c1800500b43e402180d0042c02d03040c011090050103501c3e501c00c6940f2051195a10031000380705d0000c411018404500298090034810307001102d1090a07070107445202c4e441141e0309104440c2445141e036078070062000705001d00003198403682d405030f05a40c038a001d131490b4043c4c1e41404d00005035081d00410690b12441c8242e0b00c140e0343d01590003a101c20303802100c0004000d03170844200303400c1a09081d4010380d4440c07014075000051001110 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 582690206 1250 582688956 582688999
    0xb1b031005150f07050705090108010e1005060a0f0f090507020a05061f1e030302010606140d0203090309030f0105070912030e15090d2303030105010903170712020d081602030a0806 79
    0x4c1c02100e040e00150f2041195103022050380b401465050001d02c24a1000070303c20751610007549a941900c1c0d600c4004c04c12540b075a00440025100e0714801100b06c0740c075684100f00c5941030b84100800c075420100050700551001c0b90341845030340d215004180e02c0e01d50311100401c01801d901a060178084d124400034212042c0a0111440b06042901c4040e4506506000b82540c42d690801424000b900c012084c00014200071142001304c84940143c0360348a81c8402801c5120f00039140e0707403520500314110035400065118a0082820ba216115150f80c0c4001d115400c0e002c603500a800b040d0134403e100702c24106001510521038850303244602d04201003000030040511a50103603400401c50b030117100d402200648400c071041443d0011400d5601d00000282400900d000c01003000003003c100b24400012501134802c030f42d034001d41207041e0f00705080000355581543c1c100440000c080e80c010401030310606640e14a2004140d0245181c0f01002d4003e540381c01c005468a0381024507207940e10341d88407841 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 582691456 1250 582690206 582690217
    0x603241f020d0504080304121103030a020610050d0308070305040606030b100e010b0c03071202031c14310c030510140705192a0b1b031005150f 63
    0xa42100c810100d02400030720344621440d1240c01c0c440e0810080c09404400029282210074160320400440c0c440d02c1c000c0c0260040c2204c1a40602c00850b002c1b1039260041805032190160303050f8407003c581d645080103c0a060302c83c000d00807403c500c0c08154414442d0300030030b52050150130081a82170313581d034442c1000c010455801c1c5c440c00341c81009101341080303400368900500c02000c207542008070714240307180c980c0b148020040400840f18602100745000380281e410b14040d02600565801c0c0400c14007011b0302c141e15268038802d000340001600e00c2c07210b810070400c50071401c111684070501445074244160300450141c0301c0821101000000900802441c0e1040c6084c00b00481d90040362a003030342d00020f024011205001c414440703d540594501c0c4034441c480541e240c820096004801c0161a20090048180c182d500d02883e1000340400780400078080c5140c40d0403905582c034000c413104150300003990341c40c03044c0301c1c4004104020f280426916028020002c0d103c1d2400700500c1c10484e5982c0704 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 582692706 1250 582691456 582691489
    0xb070201051b0a060b031005090712150c020d11061b03090703020909010e01060f08030a080a020c010f0e0c030a020d0b060418110312070b040b0702070b04030804150e060324 76
    0x121005c0d1001030405004055401d61044002e00c5a03080043c02c19850314814010018115508030b000710900c0a244440307081d249400340300b08841260b15800944402c0e4107440c0780085a8404108070301e640e80010841d10507003000c0c104442d0428444010001940003030820131161040d1103001c800b42e51240013542c02a103500000081c050040303100e2500f0b5500c2a0300911481040130350420840c007000c0100c0301a8003613480e000360140e91301c00f0403100902854455003d15880d114221810501c01c4e03000c0e410b44000041143c0d0b51402c00c10800da82c8100040d0000d410a113800e600f080040c0d42011070710b8101d2001000840c4407400e4074a8099000d80380a4156440c40008005900301e06042c00300f2602074a00840b03c0d480d01801c0d4544040d8000d010340010280c1c8003850024400074401e014800103440e04102080da107030794134208403005400ca80203103a52440f020308154660350060b4090516100040d0145085070740e020000e0300c05080c075441c103085640703600318645555170b1100717030340d4810000303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 582693956 1250 582692706 582692711
    0xd020c100509190305070f0c0b130b040b0d0b030114041a071407031b080307180b0c07120602131d09150a0902060f030c0901180b070201051b0a06 64
    0x140c0401000907180c002e401c1c1c0c01d00ba04848811580b415102482c11541901820b1040d40c403415807804610341d01500b0000340041d02e0300c00020400680350b0004029400e40c40152201c09070306c1d042071041305c0c81944260410f440041040c101056a030350000c2d83d031000005c2c00080c1070380e68003000d0320001c2404c5501b00d40c1c1c200b4055200300807200c0e400c1c4003500255603103400c455041041c2c0d40c0b8180c1d44100030004d4148030f5030b0340008003240e800b40e22070100c00341d002c049075882e81804078004e4404070b0184c00036200c02d054403901050303174440c0a05484004582a0041000314134103488140340d41020081540d030f054081029a40200110000b140189803401c0c1540c0c6014600210040c000406000102282c004200c010380c1103403186841c6802016017500024503481520000c1e0480c8940c0f0110f004c00c3c0e1021082081c2c076460100a401c6003903082e02c1d4806144003400a02480003841e000c0c9a030881418441e410141d4407840c00380002c0119101810b1000905140b49407403c400706108682c0180c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 582695206 1250 582693956 582693973
    0x70f0c050f060123090f040f050f030d0e01050f0609071b11130c08180106030203120c010e060702150c040302062d400f0f06050a0e010c080d020c 64
    0x41030140b4940c0104d5481c504a0842610b0310000340b50b02d0b50180c1010805119440840c1c148054007200480c07991340081240e80000300c1d54407c2d500e80d0484828040d00500d0242d80b0401c0f5101806624443c0ca0003807a81196580d41034200242a01c000e0060000c0180b1303413140100c2201032642c1c1000d2a400303501c40a60034681501007007480c0845081c864100b501b840c82208040350802c0900343c1192000d221405c1e2002e09500d004e00410150348060340c90320401e0803081075022000c00500c0900c90b214001c1c01640c400007115980e5075402d555220040e84003200c0d500045281d00212500009440c0595150079030b00d400083c1c0d280c0040040b800040c0b40918030107441403103528900c5044d01c4400b2078608000301941d40040115101d0b542440401e104194a000c0c2517400700b55015240c01285901c440c03d80f182c00c00110341c005405620102100c5010105015005401365030600550f03617a150b500e60301031001100c81d119049022598008144001040a100b9001034011141c6070740080942c907 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 582696456 1250 582695206 582695219
    0x60c030405100b0d020f01021c03020d050601030c0c031b0c08010212061e0402030604020d020415031a0a170a051c08150619090302030a0f02130e06070f0c050f0601 72
    0x121006082e00303003080c900082c0d41c0303258846914044ca2141c0440c1c50002030085800140d046c4100b07006801821152070181105098042d0701410001c13651060800075075580794015030407908075424401c04280039a0a031400a845240307154a03000c80e4400113240b641540d569500d1600c02500f0001c0240d4020403a60030161034200c1207130380325400721040d003c5a44a9500e001030b00400b058210700a9400100207503a6803550340455041800d001d40442d556036566040710a0401c40321840d10000e0b04103100e40070500307810b81452219060090488003094a44840a441e010031418410031a01506c1d2070440410400d10001881101c40704514840e94031417200142415001001190031085003c1c190590b501c803802641c1402d4030704020000d607034240c008155280407095100a601d0310849011070f04200f0a10300801c0300510070360340d15103401d00f007102c98401d42d048182c2e01403103039100100048a0707510403071622510020360304000350322107050f8507403a003081409203082170389500000040184 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 582697706 1250 582696456 582696463
    0xa09051603080301060315080d0c0203060a060e16030b03100e2104031707050f010606030c1110051305011a0f0108010f050d03030e0a0b01050406080c0901050402031305060c030405 79
    0x503810040844001a045a65450a501042c010402010f5444c044100100400034001026044240c02c4415400440030000c0a1440d504c908034020300034030b804a07020340808d02401017904d810030842c0610b80c0e0780401032031008a01b44006020180c4803010001292020310400d111030700b880401241915800310708131303d440c21134100d1503298030036115018820441e08050720156540301d0303414410220058021100742c0640e0078083c1c800c0c000c4640c00040b41a05510441c120398207a201400641600343c2c06580fa4a008e801e52036a40d000070b403a05100d028aa0702443e40480c0ca100c4c484902a4030340c40d01821140240141c0c060098503802070280303031070a0010840b40010910b418191036052801c18048086544a03a170f016044076003c03171041601a400503450890131808036000b1098609044054072020710900340a10328084c40460f02e1100403c0180e5030002c003400001c26a460003081c440250300003050b09070214003100524001480c1401110b00030209403d540d9120b06141c00d04900b0f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 582698956 1250 582697706 582697723
    0x130302030d051e0c0c030708060a110c0a03080402041509141609090902011b03080712020c03090d150c050309010b030a200a08061003031404260705090a0905 69
    0x307000c401c2c84248031502c080c040d64044464110300c0f050711404182c060600e4008584c852a5142c000e562000c50070040c0004d45c0c3e44603c50f2007109000410095107405854456103a2541d042e401c141c24080109010b9040503420505c05040010f40b5868030140c54140303040c58000ea0602741e214030410843c0c010a20240e9005a401c7c000042184075900c030240c88040b0b01d1003020821522504284156801902030585e02880583c212046a20510b80201200303400c84c1c030b91000c22020019500b400c0c0203807080d2030110740c03c1c00045180c2000e4804010921256200480740701c070140045582c00c1c942ca0054506280080c1c50711510790030420121802c0d14010340744140a548040011404200191100655070185143c2d062249080401040303d221241c0c2240c80e8a00c01c0100748240c40710240003400c00c5034040c1da55903114080300b4544003000d00c6948203900d50786c8503080c54803245146504a02030b0030002c1c48112908903665101048049400f01c8488180070307a6501c1c120b007800018000c084 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 582700206 1250 582698956 582698983
    0x10050109091a010f1526040203060f07091e090c0804021503040f060b030c030114090c010215010603180b0405031c02160602132112080708040303021e13030203 70
    0x2080c0e0340c104581c01c0a0301d2818031070030041040340301c1e0f81740c00706008409010b21404402a40c28940903050110711020a00361000c9009108900000740d5800c01d0b00c003c85d010b4180c55a0f180c0d030441c502040050902c00940340102c50500381c0c100014480814800c0740c6494401c3d8584808524141c0100500344d01002e950402d51a0100f080000180b141c0389401000741d4400e01c0000d42201c108007003450019080f40c0580c156280401d01c0041e1160307440f14510900556084a0302601e001c2c00498941d120038400a401620000c01484618000e030400c07001d51007020b01e004ca940200da04c0d42c440180c0700380c4043d5040e030000600e8042c00d01342401e0194512103044025031400859140100c4040703801007000d010b02c1d9002c03580c483c8081c0d2614550004141c82905004040d02000c0c61151983d256107007126068070b44007807800028022810301d44200040d8807111142d035110744090b0060750004006a4020b02078140010318901c0002c080c21030212840700c00e040860452050500d018036046420 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 582701456 1250 582700206 582700253
    0x12012003010f15030f1401080706110c090c0f0310060801060c050c041a100e0415080d08070504180507030b01140a0309050a0c120b2202060c1005010909 67
    0x501c0b50710441d410311411101d0b0700464070250701d4200400c0340103010703d1036050300349410812410114203007440e041c2d060701e14400540780400c0e0395441c1920380d2071380d804181c0407940046010500c1c40c84c004c0c004940c045080240a8900b110000010a0b40d034011682c1e05c031054481d0340306000c40e41d8051a0300e400351040b410311101000c516190ba40c0c0d034107408001940300359103548001c04142c1c2d00141500700694041c0102c0c0740309400c917001030500c402c02c603206030259213040302004001c821080074034200c0b8080c101500481c10f0700c030000c444480004080a05000c010000042c088680d815410301c01581104001454108070000034182c40d03021010904007e81d06031841c103682c01e6501101c0607900c981c00d0000d40ba45040c5042c9003054452100030b400400c00080009144480481c0d100c0c03400d10621042c80144d442080005001c803045207440e005400c114903c0c00142070520007021002c022400721110301c2c640e03103100401c0e0760090b0442c04c0600c3d11407826804011900c0400c7c80704101c0740c03c12 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 582702706 1250 582701456 582701459
    0x516080c090712020a021006060507053a020c09040605012111130b0d030f080c0a050304080f070507080f011a090c1e070b1b0c0d0302090109051201200301 68
    0x4049205000003443d01560008194030b10313900030040486d03146d0030010107000720b51b560344019026400a480941d182d008000c0740781c11101c104492108522030a03640510800502031351652087c00704513008007940b00d04410501f0660783d040740c00e44070328070a5102003620340c1449ca02c12903407024070072a0480e41d020500f8000001d42201c00140390030006642903011251045000005404000c1c00e00d904017118511003001e03d58030024000e801034036900c5201003030716011000d5649120322414800000d0302803012078002000c9000a150504031048101d003091410744800d820507685920241c1103603c42c0c80a0881a1028000c01c1c0b008101c1c02d00d00c00e4400d40703440109000107001401c4903100040062800d007894000b017903201c046401d55600b9912903105103030050003400e0594501030000215800c1d944065641e8044039240714020300500152000e841c000c0e4041e4005a07903980c180680104041007945410f8801021840c1c103400100d8410308113045000c003001514022100c1c103404200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 582703956 1250 582702706 582702721
    0xb010e010c11150408060601200a0204051801020a09030605090c09040212072301030b0406060e0108101502030306040b09010501020a032111070605241c0516080c09 72
    0x1c41a026000001000801590030000f08040c8028840d19445280410081010080000c0c240e1242c40c00703807185007001410400e0005e4103110720805640303541c030400701c940050138a90010b80e00070005a00001c000c4056800080c00da1708400c040c40c0014041c50010024844c9502405c3d40102d000800313400354901000c04521050b5005201a00490001c4180d440d15041000000000c15115090550681d421003980e25030f8084410341e503002a042c201c0c0d004003407070700d8071400e011140ca83e19a6031903a1103182c0152845e0a004207601c2d00c3c81009040050040550401600f1210445d03003d103589107040b4003000115903c581020303000e1200c5000502070b0380d07000140c100e000358140c10000c058041c041400385203007080014150410307050440311401f1181a0780a048150b00c102d4050007290351f103a4000c10b0500e0104006200c0c1d40340202900c0a0342450030300903081da00100031081c400c1c281e60320350740d00e80301c9005004c803083c0050705c0c810003c44106010801c5d1208080354940050f050041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 582705206 1250 582703956 582703967
    0xc1a010503030d02070f020409050d090b0a050d0c0c0c090903091706010501120b0d0f0201110c032a03030318061005060703030209012615041829010e04060b010e01 72
    0x10f031440690368001003010500c070a4241044000c3d9004000380449421842c120381c80c1d1314600d507040003040d5105404100794170700100f0755041c0d4109940e43d504141c4803512000191140001c10700c24012265130b00808541038410b2500a01300d1080b011640c4096403500a200340c041e684000c034210055104840c440e14003250140c1159400d103440323078652086028143c0201410341c00c1641c80f9004d041180300f00140c0e9064200b0700f80c001d03200d4252075503401e00007503154030743d18540d079a04d50006490150241e0620300b83c01420904429500003210280001c05c1c5540c0c001e40354129000c9580c80e00c40100305081240680c4030a2000760b408410b450040451058001d542e802401d02d50007195801480c0d01c0354051000820880700441e0321105100e00301ea540a8054542c0303000e03400e60741c8020b9040d082c60b00139460707030548491140701c0644160301e840b0610b0798240d04424443c2895a1042c3c03083c0b990301a0b181c040c1c00300d6440c020a80c00c01d0b1030824200c5144101c518140710302da0341000040d81c2c000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 582706456 1250 582705206 582705217
    0x6040303080c040e31050c10050409021804060b1905030c0705031c0c1403040b040c0503030301090c02011b170a060801090605090f0303040b0c0d0603120c1a01050303 73
    0x1401c0c084401d855110354100b1034041d642164246041c0c0e00c017040180c64564840c440f41d8404000b00604140d5070382c6040e40314183d00400a416035200c41078001c614100311164109118140c43c04038103003500c03a8614001e030b9100380710300d59080d8a040c0d007155541c5418403605005084d1250540c0c03401c28000748511000004d107400105110001c0001800d5003240d00854000a50003404d072039903003140309241ca00d01c0510300d504603c403610301420b01e200c03240180c51b800c400c0201c00309501e00b93307540c544d12440c0c8588010b10031230300350340700324800603440d103041010b10b001e0300e4565808100c41c2c1c030300c01c0001d007140d040c0a105801600c1c0c0c480c00304c1d001e0382c01c80e03003144a0060a0728044199a1980c3c080740c0505015406124190710b8a010390091220f154000d44c0034128400641c2c03825010140113a5503170000b520080d0821031100c011641d800f004000901d42d415241002160540ea02e8560a50060036200074602207045440c400c810407550000d2012240340644840b0025410400070960328001c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 582707706 1250 582706456 582706463
    0x3070302120717040303081b04081207051c0909111303060921030e070914070f091e1401020106080309040b010507150606020f0a1104091a010303050301050a0f0302060403 75
    0x5440301445041c0380c200350001e043d5840c4075611a0740741340091a02000325a010009000e0b23402c0e81d101c20f110003003241c0840b031620008298000180d040b0701101d6018240c2114035100d00d6a0307a1800d0700802c901c03160034015075210708803aa0300e0040c00c070059580032a030030b884c5081d0401007840f40c0c0f100000039405403904128000364001c02803078440c00c054414003142000c90b8041c0c40794188203500d9040000b01d071087c80180c0e08042d503240c1c6403800b981c8484040d03c0541111100081100c2d104d4090001d48400b10701d042c0315107030742d60306801110009085000c0342d002d00c000020300c01188215140440303a4020303c0208404c80c9800c0002e6240e001e0b02003281e21032078568100000c641c1c820b81c190391440d500140d400c40101390400008004020034400c1c0000350260b501004e03d05c080100c0ea804e9140e0308030744000047d5a2503400c2100406014800310341e06007540006030351000500c850315028510a44036180d40f5418601048041b803440c1d03101c6800d980e03042d0428401a2140411f80381201d51 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 582708956 1250 582707706 582707743
    0x303020f0a0230010e1c0201061802070503040e040503070b09060421030e0303011d010501020a21030204031509231e070312030f050105040501050321090a030b0405060903070302 78
    0xf8104150b01081c1c0da030840ca4801d9801d00c4e00d05200350201180012855964841c2c444403d01c52030001c3c0e0985030284151080a0a6403450484090f01d0380c00400381544075100b45c0b858162a1210400d075000c040c2c0701950660f00100e40a0304220221600941011480c001000c3c00d01c1c2c550b54801d035207600880c10100400002d034980040340d0180e0400051840501c003565129a101e2004009114002107100310b50000900005465400840e2107000141c00c9000321103840a0000d00d00e0783c070ba0701c05651400f0564200800000300d035001c03030080c2c070752001750002048480c001d01b04101840d2080501040300100d00007441e40780100010300d0980b03100c0c0200491400c1641c00b441c01d06041080d80060171420aa00094040d103601d944030395a101d403aa0020402a41c039441407100301d0302c090081607050350120110208010344010788038110026111400d00c1c01d6000c001080300306006038001c40d40c150f840c000380000c0100501c05141c0c484050380055040004a0324000e42c0e0700f9413802d02083c400e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 582710206 1250 582708956 582709009
    0x90a090203030d0915200304031803080301060c140606130917120a062702070f2003120a050702010c03020c030114060f040c09091a03160303020f0a02 66
    0x480510945010f810521000c0000705500d09120701c8410769505281203c61800c00034020f405130b0703c0d54489001c40c21884203800c5a03110703a016034a8048294907803011240b4a200000001c019100440c0a05055541e2820b5060580303800c201d811a117180c0070903da0002400c00c4043e031555807800c240307900c400da4040f84190160038000e03816590360f4211085240002001c0c030600000103105800b4441c08642000890341c1c406410101c0420a8a003282064840142e40520403040d005090800d009040041e05450159100007590482d03440e0340741e80164030320000c6c0740c1d4a4280681c981c428090f203e00c9280c400c900d5002803481c8107080000381441228040601810710030010000c1021018000700700d070340d240081d003041c108402c5403800c1c03103001181c4650600b03090a020744208620782d40c4480403041d00317102649000d8118254080d41c00340c8078003a000401d580800807184100d6081c110748040340e003103081c004d040c00c0404d21f508803a0740c40841c41d000141c0f01c0d0704840ca000e1644007110003d49 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 582711456 1250 582710206 582710209
    0xa08120d021201080a02030708120703050c1f0e0c0406050a0302040903050d050c030a060803091807050903010929011d04021216140d030504170a050a030203031b030105090a0902 78
    0xd0040c0e5460341d0300c0d08030700400130a40034000a4640d500034000c41c1180c4415035101000f558070320700c80138801e003600300a201d528000303400390307015092627020f44059a0f01c500c0606030303038460303619001d908140e4985c8481140c60300c0364043c855445101c0044c9c905000d86805d101c086403c0244a12009000b00e40d1540e03448107040c4600240c54061714034000610240c10059240310464105541d400001c2c0e140900010384254004121400c01c800a021f03821b2a40541d40f8281d404140200403106000301009070108550742841107001700b510a448400362004c00c00440003421000c10f81405d400041c00700180813003002c00010340d03c0d0880f0a10a100240c3c1c2e0340c80420b003241c800481420b514441e50700440605100c50344404251008502c1d4030002c41026410482c1c44035802501401041041005001c3c990701c2c0601007001d803000350b0440e0780e4186a03541e110b10745000403905400682012040c080e001240034041414280404100c0e804d550401c400243d0f050b401403d42810640e0b51204881103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 582712706 1250 582711456 582711461
    0x111302090603161809020c0705060909130302010b15070c091808090a181a011b170403021002030301180902100f1710051513030f210302180a08120d 65
    0x1c0100c4d0800d10b540407992401604041c1d081441650031071f0003900341c0403e0b2810020103035004a04010b040d04200d40b20300c05103203c100300340c12041e402c554960740c03100c4068a890413403500000e8900465039455800f410201c1e0b0100240c0c00550f00c150130014841041c0719240005100140c0100007a507407952000001070710740d034042c1e10003c61030041e960b5a060913801e5070b0000811840d5000c0b904460f918601c01142c07000c00940032440c03012076105a050200300001a1806140c0c0e20207079261803d512900040e103200110640f000c0182d000200500c540c0d110310715101c1c54400190030900400c000366000032a1281d54200c1e460812607403a44402203a8810004032030015080791509005040c455012408100980550390081143c1d8038036055420580c01102d0602c0070101c9150385c018115078543c80b58541c03901082e580d00740d401e80402c0c07404444210a280514240d100107030359428121820310031218101c002c51044540280030494180003140070b0b50403030100d42c00c8554a02074420117100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 582713956 1250 582712706 582712727
    0x9091a180703060204030b090a02011d0a120501090c06020f060114040f0e030307091211060306060d050a050f010509040c0509060409050a0c050405090303070c030c02120a11130209060316 82
    0x1610507504000280f202a42c01002621f00811100360140d54079560343e50780b215000700081c0064031700c100340700b080c0c45078940d1000d0401009000019071651100f03c0451270780031050940b400d0355500a4801007014520483c8000c0041f40003409030300b210805c003541c0302d100511585e110030380034108d0510380d561141d000c81040c8240c400200a1a009079000c56640c2e001140c2c1040410b450345c00120702501599140304040d0f038440e80f1001d00100c00803d1011540024040e103410203820f01207405084060302800d4800e8042c040c0c00035580c54024206400301a0692106024030110ba0600c00419060708201301030b104140c4000f03019446040104005040d0030001030054060454200f00b08141030500c5011100304036400d2142ea15000002500d9200580300100820b0f001103800001a00551511641e40d00003015407204c1c2002031052402d00d46105011506035522032a5420149070000400d690f102c600300b4210b081048100c0404d140b444081c0c03001000720110329102400e184201426007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 582715206 1250 582713956 582714001
    0x38090a08030411030a0f0b0a0b0a030609030228020102071d0a11040f0608010806070f1d0f040903050306010201150501020d270f0303030605040b0105030c07050727050109091a 77
    0x101c2c0d080050604a6404c030301a0303007c959100500c4007041e091401c5004555004000404030070300c031807031a0740e503038002c00c2c01900403000c0d4005c02403955007035041c6107a0504100e819910100400e506480020b0400600e40c00240c0b8a0064014100c02c2c00200303003402d9448010010b0000e00c4030080325440d801e60007180d01c000c17860b07482c070900840d940b030303210400300d040f581c01da030444109413900071082c0c80207846011240c1c000760007003c105406090755490b820000b607001d0110b05400c60700101260030741d1034060007940800c40000502406e03583c2441380a00c50003909450812860400700000d480b01355120408040140800c00c64411102d6180d1096150440c00c10003014141c1e200d000784021840c61100f40e0100b46003120004080c1890302440000020581da030926680d00c8419010190f08444802d9403503106403240803038200610100b0b203045442200c404404841914607107400e4510503009000c200c0e04001c004000a0401c1a4154500288501d003014170f075079040340d02c0c00d2604500e0f203c0d03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 582716456 1250 582715206 582715213
    0xf06042a0b0c0f010b09040209160909061421060106121401030c05030d091511010e06192711011101050f07260a0c020a38090a0803041103 61
    0x344070400210b0301e0f10710300008001e03c0595250b070200174601b001210042d40165880d00007407004202d810100807254010308240c0c00864130f0708007a004503180d07500604140d05030200c0d80180c620300010703203e24500b10000f44c800d000c0300c0303855071580302c95040c07250307c083c840810540c1600c0a61034220804212124824109a40c0c2d2400c08a82108080c0703e85400781c0550a4040151031282440c88195078084100030b00b44000720000b240c401910004c0041d42d0355a6180b01100e1940900840e4010454030040807168070b40d40c0b00768001c649205c00d981040c05540c00b02040c1e80003246003c288520303008440180c07284142401a203180d0410051640c15500e01000c00c42e00202012000380516103555902a03801c0074080c0c01c1000f80d000a41e4509415070f0140000c595003980d03005032040c1040c62040c3c426a100d0740d0341d130300041100f52108055a070490800707041540b00c1d07210082d00d0913942104066440c1803c0310b0300f60b1075890040d0082d014000c0080040d00b44200104407158151010303044 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 582717706 1250 582716456 582716467
    0x102010b060f0304110105131e0806071e0f120f0b0a23010f0e0918070902041e03021e040b090406050421211d0f0f06042a0b 55
    0xc99260340e204440840f00170200c40208240780d40701b082554001480c0d0410002c40340d04000181d004420700c8101325031003001030600031564100911116005084503181c0c0001542020401104204c0d104e030101e0070408070104140c0c03407075405521072014440032880020b000c111000504c0140c10040710040d0001070100d400500e400780602101d07402c16002289809503003100300111034091100d54034900088140200030403900d0310681068001d00b1070100c90070709545c8424a1030805055601038011298003040801000103c10001110456900058400d1a0850340000e10354001c9000c2080d10343c4041c522200c690b2155404020f107280f0041483c031003460300385050000303810100c2e021203290030b82200e28001901d00d441c0c219120003640e102d20401d0f041c00c1a4040101444504138400b0703503160103501600680c80c092401902103000050400110390101a5103050080c0402542c10744c0900108404140d40f041400760800f46a403410649620301c402c400003034030503070b0402c6281081c001503 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 582718956 1250 582717706 582717727
    0x60c020f060106080f0115020f01290a0f0b070302031c0b4605091003051b030a020f0f03100b1e0d02240301080102041d040c0b03060102010b06 63
    0xe21504802101084440c241e0721454200d030070610940d100420011807500500c10710228019034100300c45035104580960b050103207902c0c04e460700c00c1d11181041d071a1400440c6030b06100f2404032a00362058800020103441c081044020706464070402280e10804291107040620910440311000440c40035002c0c6101c41c803107000300401e4059161407181c019080440902d002d507100382418913100b2206100d0707c6c840046c5400e910342c9020300e40000c2d40d107081404225a80c0702106103000e510040381030f001440c00c40c035000c0c1c5000c080720700c440715526500c0500503c0f03940001d0240005581a0348803800c80c00319030080380c4111a14002d4590500809015001c0d4641c6503210410b15101107a0200c1e0008006050303000c000401e003e082d03000300b5081c1322000075050010031031610842003000022511501132080702d00340c200f07800c44142c0e039400003010000c1d603211040401102114510303170225810319681c2c0030a0748015110b5501c42e40000310006071a80e000b907003c1c8401030000b9003519500e800d11071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 582720206 1250 582718956 582718963
    0x50105010908010c09140406080f010e010c022b090b03070c170a090905130209160f08090a02010c03050c032a01050c03150a0510080702060105150a08090a060c02 71
    0x109030001c0c4050400191407081400703041e068015544400c0505410451071118004080141d1500030303448070b00014084004000708610404001d00014040c144c4001043c292000300150500b194000e005c040c07180050092011400c1c0704280e02c02c4190703020b1030025580e0f0780655210341010038022040081d203d8001c07184a034043e12a81f4001c0b0700100c040c0e110105402039480903000281228018080510b0980c07005400c00000e80d13001d1100b00707503580019103500c82101c90304002c00702c41c100452900e401610319007050ac42801d00c100365103090064266104c0074030b100a8100011107480303605050207441100e00700c0304004143c0703607070343c544481100d5645034111854800003402d96400009110620545004910803001e580c5141c4a15580050301c01000c2d29480c1d01c0140e4078400078440c2e460141c51400c01819032900e4929142c401006400e04405134895030144022595600c02c062890040307030980d4802d07042c030704910b84034040401d28201440000503c018130b40403002d04402e4000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 582721456 1250 582720206 582720209
    0x12061803021b04050c1215060a050a11030304030c08070c08010507020c0325030f1707060b0907020715050d090b1003150b030703030c030203070c180b01031e05040816060501 76
    0x2d000c900038a150708024041243d004a03041510010240080c071001c40c0141c0718542c101c4c0402118208207281100019001c0d80300f0191140031400005040d1b01098101708990a00401c09028500310319003038030082d00007001c4c200010440d5000040c0e080c200714414082102411070040200414500020301959030118510054403078414428005001c2c6020485c010803680140c4111425a1956039900b603500000c06040b40c0b8040341c0d014507003045080c0d40142890600582d00424581303a0a02800402d0b240a44818110f41082409004441042402d0728071280c0c01e151440c0d44041c940407010042456220041c10404103030188500b0225201c0020240ca00400b002081001c07103400c540100c1e05058086600742d0864401000401d015881c00700040d4080d0041e00d103041415500c40c820b501e060b4102542600b80e5440d01c44003041c85104041007000d003801d00300440d25042c2e650700089031213003089161983d02c4030009030810000c2d00945180802c550b000006844062620401501c0d09 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 582722706 1250 582721456 582721483
    0xe030d0b060304020f0f01050408012906090321070c1e08161503140403090f0902120103080a140d020702360a0b030f030d110705071206180302 63
    0x1803905000d51460280101ca0183d82d00805500b0b0110b98642484003052070b604019041c4003060000040d0b10b64203006440300c2070305001e12168584203500001845480310745440d40030f008280700c0c0f144140c400003013140c030a03e100d0b901c10100c00c4400001601e10712510400905a001d12440081c100c030740c045621020882c08405d14000e5501d4024072035840d13003019807400c0311441d404e2f001c00c68002103002610145400f07182c085044900300b4201d40d10400241c50803400504480d204005107124290190044c1c1702410042d4607040140100061000b0107000103001e1610004074000858000c03809141c450040810141d10354101c00507a100035081389505900500300c100000e004a0720b0450440480341c0c00c40884030040900b030f00442c50010000b021900c44c0340d035991124410350f03410001d4100400c200c500844d41c510703804815106440714900d200d4901c3c1c41c1071180c0d00001e0404a072601c16524609101a940300e25130600d50043c028881d01c0e00c6604141604400074580d0210708020044007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 582723956 1250 582722706 582722711
    0x61f0b180405012106020c030d050103051c02030309030405010e030a0b130c0b030417030406090203120417010b060a1803061b080f04110f061e120109020a140d020d0e030d 75
    0x2620301040c0011409158406044c145501205000a032540c2c0900a610035030b40403a41015016400782080f11030070707001907403150300000c1c60400303141c440d4440000c0d20401e40b02071030550a0010505a030b0b1300031070042505000c1309882498031504c00b085580300c01a04400c9012150410f0002105840c1c1d40c0c11041d5a035a60551000c00d8980040044034003580d4000d12008150768641d03415032450300080c02c11640c494a8051100c050395041190901d005041032445648a141c09203032011440c4614040035540d043c110804d505599550a56100100360300b003012030544c8100e80d0244800300c07904000c28031880c0203105500304075840620b28854941c1d031207100c42c42d00d46403506056007900f00e41c02071100803450988205820020b0540e0810600901910704000e450407030303452060821800c01145900100d001345100702d01c40501801407036410341c11841c02e40740d41001020001c50035680b90324100002000803440d80e80e641281d280b01c1d01344004206418a0f00001510380d4403001a8080d40f07030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 582725206 1250 582723956 582723959
    0x60c031107051e1206070e03011a0d020409080c0102130608071803060216150b01080c130e1005060a02011406121509120403050d0801090c02061f0b18040501 69
    0xd50001e00101569030082030000102e403080204802e032030010a019070050042c0945201d4400e042140501410041c0c403078a240c079400c0d005050071030300a201c0034040d106c91901c490220b501c5c0d25244056881e015100418003207030504000c5013610442c1c440040c1c41d0301c00222208083d05a424290645009070703200009911110300481d1102e84480c0c50417480002d0702010070001c3c03625030080146000d800c40034080c1940b1502c842110324905c0001c607a0a40d03c031510400e696130b01480d442da01809107034065080c4840c98280c044121450b009111211106d4070101d0704280e0a2030702a00200001080e56950b8480c20708001d01030a00c80103100c000c01e101c140401c0d51403400d81c81c0702c0e150200040060000e55000c00d081c056005028251003464056100414034035801d1030010700255000300018405d4499408000b06007a1050340200c4e103861404026030a0a07034080340c015040f564080c040242c4e050300e01d411296150940e480f404003000009000c0340031200c2041c0004144000b11400c10090b03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 582726456 1250 582725206 582725237
    0x210b0306042f061813060b0301090b0303030421030b0d0609050d08060d081309020c160e0708011431050612030f180904081207020c0a171204060c03 65
    0x25030700c002c8602c2c0d00000500039118103003900080c050100b80c0c01072041e00c0704a4092652000c440300384c2c02281110100000501000c03038103008803487c009054000710701e14580307a1030b40107004540a26051110300840514000203100350003c8040d541d00401209016213a0b00d8204010204200200e8603402124803080c2e103607001e0032103103114410240c4003000800c0b07143d580c11915407000030106103561020601003064016440034144040310100204032091148104070008110b40d40980d207025890802c225031581d0083e101811a03802c101c110b5131440d0b40360002800e00990804100005901d007001001c1030341c000200c107a0103070104400b0441a161b1006018414010b548400555441000381ca194002084000d107080c0c8043c16114604803001400a2861401910261108140807410404001d001989141c00405900007411108001004162080150321440c1d1066a100c00c1080c5003400c00e001c4561070184222070640d8594458901801040107020140c2c0001d559103284044d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 582727706 1250 582726456 582726533
    0x14060409020609060f16081e040501051207020c090a061505040e160207180903080a050603060105040203131e120c03021f0608031309051006210b030604 67
    0x103140e0060000c1d89010340742400c0c0461076100401044203404104a0300000030400a03840c02201d02c42c01d116561030390352821644004144a052005513030041104010b42ea0b0064116a007103039010101c51000d68130041e0030303810200050700454100480c0810004001c0c156031040c42a1140c6406c00d0001100c041c804681070301650240d804844030300c20100e88500313030b10f80113180ca1003c544112001c1f16143c0405203042d02000808160b15608d480c1c0c0c1c0c10415130005071700356200174031080400c000e1400c1400640c2d103040620400340281d60000c080b80076000d03a80c50078450f49400c0f86003000801d0030410005481c2034280b1003500c0964074840c031140d40900c144101e00341c4070740550040650a05564418002c00194402c8074840c940c6c0d803500240c180000d001038101041ea000b105e1340120310301003002c81503420040c0a0a00c40021070024000705410103400050100c1c03440b40000311034030207441d2070010106804200da152003104208401c11a6815400201503c815010b82c0c00e07070364040740810b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 582728956 1250 582727706 582727721
    0x301020a09051327060b030708060a2a141b10110702100f020304270c0207060221040545060603090a0c060c060b030a0201050421050709140604 63
    0x310031403c0e2490707943c0344c07242c400c8214001c4e00031800020182c2d4060002464801c4940c03006045030400300800124031118801c002400c150384a4800c011a041c0c0e60b030320b0b5000c0d8076a80b038800307200192200218180b802000d4458074039002120300c240d1a4000c008a50324080508072028140c00d0540c0c442418043d0825203d507203038050580d04040e10442c0e02a5207103410400c20608510081c000000c0000c141491024220040d0201d00302500710301c40392200340d4424140341c009551005404108203580000c2e842c1000020a4803d12800c00741780e516070b1240701e198000b0368014a0310074450f01c6200300740e0003a4950042c6400c007100010414103031030651440300829004103600701000800130300b0940c008591041e041c0c004c1c0e4003a4000ca0344c9848981903c7d40203480041e2034001c110042048600c80e00305901d208800401130760700c0c1540028214400ca0203081036030030000c841d08180820801c0300800040e4003c056070001d0340c0300d40e41c94004005848200903030009502c08260b041c1454400e050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 582730206 1250 582728956 582728981
    0x703050714100f0b0438220e061807050f030c1e210309010c021c0503070c140d0803090a3f210b0301020a090513 50
    0x241404180d407500181d403160140d015400e40a608080203800c0154800c00c1c8102000c3c2d0780c002070b070031103110500044441e00000c0e41c51640c0c02002280918040d07101504e5681840042c9200e18201c44011448042074040d40c07032001001203003008085115a009001c144010720102d841d19550454403020344203801c2a44881038100007800c1c000d500b40b1500340504844040e080307035400c0202c5004200c0c0412015035007050801d00d101b280c410351034407001200c039a20280c82c0c110054004103140380d840f40309104020741400310800b000b80441d11511192000442905c0e0b41d2040b184950400648039440f25408580d80b81ca010310104e92034200766808003043e4070241c80680524001d698809031f46c1d10107031900840d0310921070f809001a502d00841c840010900e0750312480e0162a807a0200800d00b0440f8100106821442410b440c0d90302c002852100b075802c0480c1c050900e0320425202c000d02da000e94482d0503500000d140710030f0b945c0050b08ad108840c1e09450002000d500700a0640881d10203034001c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 582731456 1250 582730206 582730217
    0xa1104180209010302070f061a040e060f040c0e04050309091003150915061d0f010302090408090d0804140102070b270a050402070f1b050a06030203090f01020c1b060703 74
    0x1200c00011540c0a01540201030600500e04051602c540d040360540b182d044441e1526025001c41718540f520f05480b02c004241d8003031000e1a8113035840b0341c940b9030041c445d00001d0400303400a401d208010746094010600d002d0003030b4450825041c000d88a600080410380540004408980d05400030316100003180d13007002c50b4440c41c0c10356003030381c901410035400f050311807420300324400440000c00d03c542e02c020401c3d030b0b00035865556059140f558001000f421f410340442840010400343e1101b030031450b03000d40c0c0940090350350119800003401400c21030300d015080715408140414081421008003100c00703401d03000c80c0c0c030741a61010510018864481a0510004155420600f558441d100c4880c442c0e001410800071a40b1440400c08a80066105072407200c0f0010311401030089031512070129031400f045105400341440302041203100300d4030407082010390020000d800190180030f485c0d42c0d422010002e5559501407911a42e540258030700c0031802800100c1e64240c0340c40d24034100c54916a054845 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 582732706 1250 582731456 582731489
    0xf03081501052203050d09050406050604080d050c1630031211071202060723040605070203160602030918010f06141207210c0c02190e0901050a1104 65
    0x4040c40d079026198001c8000e0000c3c8000b00002d0824000c0c0044030300d01c2e41c0c0b0b0402d103519200800007a100e0692155005035000c000c107002e01000454a1007101c1c006041060750390300c11120041c40c003100340400c2016410f05040c042880c6c4860341c0300761440710001182c0940c0801d50703800c42e0170341c0c2800000100443c4440e00924910340413078201c4404280084a044d05206998450880f060300009512005030004000c00810a802c01491000e01105c1454040b9039000c001507002c0a00c0386000303120a114020482104660b000c2080d1015440700c45107000642e03a0380d00c03029540b41c00a5106c144200740b0900ba0030440e20708243c1242c101c3c1c40c0c41007500307601c503c0c00c201500c00c0f16021200304031480c401c102e0301040c1501005101d01500540d80c03056115400b4112481481d00a20086c0582c1401c2401c0112401d900c00051010181c0407640700c60221251900c03840105480d0380705c821640214002c1204d01c01041d44044c0c400c010f0301030140007001005001c0d00345840b4074014682c0c5500101344 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 582733812 1106 582732706 582732727
    0x504050405030a03270204090c03050307060c03110702010206010b091206010b03251205181b100e030607050f1c0911090606160f020603040f0308150105 67
    0x41d142c0000c03070004909816185c4a4020388641d4940c0d00e05014890074005000055505c01c089a9a5442c986030113006080f4a64a200104e4501003038100c0d100343c0e60084036807982d0b0580c040c160584c02c0400e8100e443c0c20a22965400c8100c0403139001f0b2650027040b10b1400391030151120743e00d034508403108004d0910b028420315418500b901140e034070719070043c00d0b100d03094043c004040303010703502d00c52115101c45091020700964400d030089016038030780a155104411000361500940d1003038950b800d60340402e105826603010f40c03014000409540c030900207071090f516071419092500c19100d003003241c5009503884504102790f5950b251810040c44a0317500d90001015110701c046840c161000514034060301a450f80300c0250034100208102840702040c15007075006001c00d4403810281400c0702c00eaa1b02210803004030b1841004100c20b145860020803200030140e6882e8030301b480041c0d = true := by decide +kernel

theorem cover : BRFrame.Cov 582553956 582733812 := by
  have h0 := BRFrame.cov_init 582553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 582553956 ≤ n) (h2 : n < 582733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
