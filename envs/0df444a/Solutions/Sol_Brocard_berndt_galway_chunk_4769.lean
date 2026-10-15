-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4769
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:40:33.473472+00:00
-- url     : https://prove2.me/submissions/ad58df4a-b993-4344-89aa-3d937c0fcc36

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 857553956 ≤ n < 857733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 857555206 1250 857553956 857553979
    0x9020f0406240e03030c300403060f1404060c020c01021c080925150c0201020d12111c1b0c0b18161410051b01090503041403060f0106020c12030405 65
    0x2140401d89103070b004020154858041381c0905400747c107d21403080200445c00900041002c030b803c6130442c80e00d406a1010005011300921301104000300c040e101990180e586014600d99990100000e82410009000501c2e810780c0760404c0c2e49603c026011503104100d001030114041a908000f98141c101d900f2410651614034000e0300343d21449a0b20406508910b40314820a081740201680707041c5940681c00b4040308510204259002001c800410118a544452401c1e0100d043d0020b4040c0b00f6040d0801107680400380d09000c03c1e1640100c11940007000840c182e404290400f092485c40b0b40d0100072800d480d6100843d038520020000340e10301180c01400b603902c489080c61000c04080c0c580ca5030002c2e556426000501040d480140d6403039012500c10880070340a180028520b0f03590513044400402d0b034808655072141560081e600509001d090084d11407200d15061084030361002541d064056190701d000f00c020340c0c45030822241d9000c0c1c2a421031440c540e010510171180900340203059a01842d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 857556456 1250 857555206 857555227
    0xc0a090b0309030711060c031806130303020a02191d07020c100c0b0c031504091103030412140a0b060402070606080d0903051e1c120c0309020f0406240e0303 69
    0x1d500104044490241704945a022890407109031080000c01c0301c0218100910301c841e1500007034445505d04c1e80706005000101c031041d5900f018002851080c1c1c05850504500d205000904602070484842d0000680080c0140724400c80c1079031151000000503a007546132040164180b0351204007154003d01c074820f012220582290302c6112592003101008120303a01c00c48440c0d503900084d03800418010300100558a503141c2038015a400c24040c1c141040b04110240000707155030b0043d4041c40d9640c0c26001c0c120700380f00c0000d0b8072050f092100e00141c0326408040c1e94045850340c004210f0791040f580071034060300744804e41e80408080c001740f01c21208807164980c0c0250251090f071008903228459040c00c50f603c0b800450b0104003d8130130400604da0300d0020b54401e81e4080d01c2200c80403c110051141d5a9214103c2c0500341d40b0419540b0009041c0704280140034220089881140c0118207102080060201c502140e61300c2c0c00e0102502c0805a00202049510030500c51034036074940300101d0100006c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 857557706 1250 857556456 857556463
    0x60d020f070803060315090d0c08120a0507120204050312280e0f030c0916121a010f020c030c01260114041d06190608010c030b0108010b120c0a090b0309 67
    0x181307108600310b03a0110b0b203200c1c440000c2d06003261003007217036005609001d840078007501d241807845124517501c90078086c83c1506460300c41c3c03080350002c0a00b600d83d001d0280054100b6144134800610301c00a6180a09000c04650349402d410612104000c00040066106600b9001810b582d0140314000740a200420300c020411500ea100c41c510595075480301000a1130009583c003d0400090600030b030540d034903131403054a02c0750284400240442c03c40c60003803030304161080c846100d41000c0341e01e4040021000040c040d9491100540665004011440c8190360004100140303c0091038696615140d01c408004401a1014541c0d03106094030300100340070903180c4000e40121800c2d00c2c10014a0f640c68041020b1500c41020000e458110401161850132031154001c0c0c1654108404510390340d13a50a00c6007111040c117032007030019640b0703080000c8640c0d000ca0172500520440100906003091000b504060403000340c02c107485564005200f1516900460003500101400440c254403031504a580545 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 857558956 1250 857557706 857557711
    0x10f03030807110d171302030c10051201080106030c060809060f07030605060a0201050402240703080411150c010c0e1012110714010c050a0806121e07080c040902010c02060d020f070803 81
    0x1d8017a00ea10000d1169289000b1008080340c000b4000c02c003a982e00c1040c4141c24030410303805c0c0100b00040040d0280c006107921014020441000002141d030f02d941001e00c040321003900100f040181c488148500070500081c03240d00050740c000407103034945540034290b00405a075030005070850004150440c0301d54065010520490098980180005003030340040c61095100d02d007840e9840c0244140b5003c41d21031501c2c2544507100c2e0000c50711182440e8005076114821051600c41c0305030020341e0988651082c024024610480d08203401c0301c006803c00a038401500c40d91030320410400c0308142d5482030745600107200840f0220811543c1b07020a00b003001071007a1441401c2055801c0c1070f880540188280115031100d03d0b06d9651082d15140d030001c02005151a204060030342c400c440000794600545c100c04000916160000c101c0c0601d09540a07042151450703905104600d080d44500241c0d80020011030300075412101c035581d0f10b5055414200a00821083d01c44100c80403c003c3c0800110300019070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 857560206 1250 857558956 857558987
    0x8101404240e03041707050109180f0204091d060105150706150f0f080a11040509010e010c021b120a03081b04090b0906032a061b0303010306060e010f03030807110d 72
    0x3905c035601120541d150505d101d954000380c54171a04000020034031040759402401c0742404114907840702e01e50702c2640c1064200400607030703480c01000081d0002c000303200d0b11011712401814141d85060b00103100030041c2072059400200004801041000551042030914054210103a20075101e0141c40c0d007501183c0582c0318440c81808001c0b0f08480009500c107804e69005e011022a04480814071001e00009064a011076494200d00f08600740d0a001e40d00e091003a82d402421444100c0c0c08040c0c84a541c410b10900407002d00d03114080740100070994140c0260941080642511050031511001d403829400315a654004180411b104041d41c1100034140401c96042c00552140800c141d2205d4141c4000620700f500b20384500f161000d9209070b07408030754004000504050394240d079003c200454100781161500300200501c1040643d20621000e000290f6442d8515810300e10b0150035100240000713014040008002885070384185c0310500c00040e41c07400e580240641d900041c0000c1c10840522 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 857561456 1250 857560206 857560229
    0x90c09010803040f0603020d020c0a0302150a1e1817040812030105030606131e0f05090a0b07053f0a05060d0609020a030f080408101404240e0304 64
    0x308160000140e80644d124a840405083c0c40e182c42a0b0080d80728405000c0c28039020700c00045190014420620003038000d8001d09401011200003030001e86004140c0c613802c6207400034400400d5507071030080d60b4000b0850000a281403c0c071140916844800c440200107109044142800c03000c004054030481d0b80318030840b11001000d030021351460000340901a0564440000651a0320700f8821400078010140000580710541c120f09241d50184000410305c601e4403800c11420210541c400e407507120300b840c4050000c080303481d964a24104d0002d0400d02c104040131442a8030502208140b4004075041120f4500b0f071030b00e1400c503a0729400520000c11542c13400c3c80c0012000c0b41540070300c0d44500b90040041081c40d2090340c440000741042134040e600f108842c800880003c00c60198419200e0207508181d4071940360640b09071030003070300c3c80013401c4403424200402c1103000181c0301c1c140c110342d1140342030140400140134980c5400c08140a5403074542017049291800c1004401001510079102c040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 857562706 1250 857561456 857561459
    0xd0b180709140a05103009050c0603060a0509090c060a1d151902070b041e081207020603090a0f0606050f0a08070e07090909030f030b09190e1203090c0901 68
    0xc10452585a224039604041d005e414218980e01c81e200e0001d80c030034030500c1d5501141014280d0081504150307140044541d0b42d48840050100800941c9010f08045032020701d1803800001140c05040184905402030407000c0102d100202e0600441521400c00b070603540c0c84420244004240d0324061003100c110b0424104086114200450341e04e0760380c0c0f4a0581d16151004034010880c03a51192600b0008500917040040395011901000b000141004800794400121411859026000c294800701a69111120303c03059640c41505130341c445a011141e0715104d43c0c8540c0e601d07003402d01540c0000c001c0441c0700984000c00045600c44005c3d6101559000036145c950400c0c0642c0b94503c1c010740c0b2145d4886841004a142640043c60348607035149080d48401e556141c07500243d070120503048000c241003400c0504119854407036030101d843e04407150302c0b00e8100440d240c4d001c140156178034800903445060035602000200604d6110500d00b0390340d02d94a15154000340d03103401c15402c02c6032040880200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 857563956 1250 857562706 857562709
    0x51b032a130b0a0515090a0305070503070b1e18060a1707020c03060a05060d080a0807120c0e1020030903070605030610080907050409120305070201110d0b18070914 72
    0x68100b8000090810140c19060404010030095485800b80350b41703600300986181030701e034801108021031142008018481c144020141807200c5500441718142051011046030a2020311806001c03c4000e000c2d5629a10302c0b4900a041c0b407800061600078100281c900e100390b91000c205c0130f400c01111000d070350503110780004a07190381c850000180d1561254000c42c000f0392581e8002d50b0804001405140c1c0c2c8001340e82e4112094001020010100e1008400c01c59030030703001f000c21284031541c000d0420a6102c0080050101c810550074030b405a00c4034005803940a01502940700d61034010900a00740700380400c41e582d070b60360000012502901520340c0019182d0b001d403050380d0140c80300810520000030720300401c50702480e0040c402ca0b038612a4101c005405e440768420741180c140101d100d085221241d940107025503c01503e41000c5a00d080c2d03c0481d020000380581e0005a0700a80110b1810740c52000518011400a103001a03103047c501845031598010b001c180c1103130309960b001d00e0003000c41780 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 857565206 1250 857563956 857563961
    0x306030c030d0f03020313020423011a04090e0c0406140406090c08010e0c0403020d1103152a0405041a010f030b06070b1801050406060819051b032a13 66
    0xb806000824510301c1281042c5000c0e802455100c103c1880d04007003c03801e500085c0a5465080200915002c1141c8401c1c0e02240b00241078050092624003201029240300c44040d20720452203126011a5034414640c42000144010304d00248024402c0c0f00890b12112030181c0006818000d17440340e454413030001000b014074012291401c80c00c3c0c0302c04202e686004075080d06014010401c6020807020031010005a0340d40c80341000440c018202c4190110015040c18034180600c50003048405c0e414042140c82e0041c031000c1003000c0601050851412411550700380c0c14044c40c0c006640c0b2a050030108007062042c100c005802407801d036100c0001c402c2600c01035044887c1c00c4561900546c0400c071001c00300b0800c00c3c06641041c2607a904c6103840030505e44c0a821104151411606152114010010250308008002403d00340c4521200a02c10503a15182d54a007403942481c0041401b10074a0300a641c1407200040f0381014464600c5410aa014040b00f100e08030075000d40300e91040340d91120408501d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 857566456 1250 857565206 857565223
    0x501150612150b0c21071a15270412030b01110309190b0d0b010207080c011209141c0f0c08030a09020619030203041a070f0c1505010b0306030c03 64
    0xc180101c0500f002c1d1003190a50283d0310408a9200e404402e007250301802007040b0003980f80c00c1301d1648801c1e480c034014580584140c41a03117028600303014880344007100444007458010884e02944c0344000b920020032110105820f488810b6003047c10441401001100c240300250349540c10052205450700648030314580e4040040264400d00200c113030750030424281e408641d0318554000c0460340e101c20004007a03020001c03603c540758a45401d00d003d940c0400c04580503110718405426a1000c8900082c00c0303404103c194081d0984640510007030042c0e6114988084200205550281111441030518086400e2a02c2d0018500020b1030250611508600110580c841c000c3e80c903580303440851201501100700c2c00d903072180e42040003052180030201005c0f0384e078210b5140583c84e45420b04020340d81e50200e924010b80b0304411020051855404404c84c0060351060810600142d41c0342003000c17106ca11030010b00b07000c03460640041850103411700698400c01048046840484410043c1500c41100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 857567706 1250 857566456 857566481
    0x3d050f0a020f090402041e091a040b0604031202280f0308090c060a020a05060c040b19030f0216020f01140901050a030b04020415140f0319090501150612 67
    0x200404984050001e4005058040030a503281d402e0000150008049900a51200c4100d000c140f0040c5124524a814031004000d20f920800074507000300c0c201c000903424070b40c80038030842c0c0da14611400350780c1d01d2041e50040e6070800e811031481004484080d584201004500e080f00a248110b01c0030f6880b058078450704198405908071110300c1c11b0790241d40359030001d408201203001e8408040303090380f640f10190902d070301c80b5402130850080c142002070500f0300107040a51091010802804414035850031103003160103075500c488826010700d04c110000e02305101c3d0085028000502c1e1252022901c200e884a2130003120305041c0d015052005413100130000407580a00c0d0000e1003040f26560240d13002d85000ca6040c02c02088500400380094120b030300a810161401d81211800344010764040c0090b1ba2266110720a81d142c03403002414280c103070100030440c80c91307102e0200543c00f40ba40b4680100003041c0e400b0b0700911004200c00f030310703160121980c041c03d00015100400c40603007059a005030603c0060 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 857568956 1250 857567706 857567731
    0x1205031605010e0a080a030e1b10170109050a18020a050405073e070605030f040218040c0501080702070509011a12010e070e01110c01113d05 62
    0x10031500c4141081a58955a03407560314070311400c203000740301049204000300703507480e40100005000c807003400031600c08540c410529030414000a8140c011044401c0301c640d4440d94245904a8046d00e048550ba80401d6800000003900c50b15600034a005038000038041c0310074803030619121100d921083c1c0280d400200298100102e0820390b001941155003480d10110ba444045d0507c004c800510703000040d024034008191165818044170400f030021401d015124040c0342240041030fa000181c0184201404e90002c50110743ea0424140c0700701e10940040344491070507050031042c00d10148940b9010403484000282c21610114002003540c0004080803184d90a141024141615003024002d582030b040020100b10040718014074024980b9182000341c0d031400100040c00000c81c1c1142d2350500040b801d107056400300c0412818141007003031030035108010380108200d2a001d07048202c0d54280341074060840c4802c04054110010320000ea0b1185000206801903400f11901200c4410200d030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 857570206 1250 857568956 857568967
    0x1d030a1d0d02100210090c0e0606040302031b0f21010609060f06200303040b090d020a0b13030e130911030d0f0507050102040f0608010504050a110a0c020d050307030315120503 77
    0x240203040030030f034500d240c41154803c9800d0303035143c001c5400613001507d21040368502009440f07030500c070507a4451002d85006003054a194080380da07401c00098006054110700c55560b01c56200d28008945891004268214040f1041814030f408141005c070380d0415400c01e50b0200d00000240a400d04a0b2480031045000c00d10b4a501245c45108200305000c21404800981110a07402c201079409030340503900e000685c1c00d181800b50724101d03a4502410070f5411060051020480b09510f0316881010342c2c5140004a80c149170445150780f10510343c035400b02c0c11005e003101200e0b15a111250603403040000310050040281010f82e07400080740c2c56000182c401c58940ca00c94810005402038034801c00015092546450b0400107100890304200c00003400c0304010441481c20303014054000160106c100b2a81c0d10321880800d00e031154406250511040b07224090454070b550450320340968109003544c1d2074422528004000d0a8064201036035044940c0c3d0100d100c40104040c00b5140383d20500a51070314 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 857571456 1250 857570206 857570209
    0x5041110050d0b0a0306060801060e01210b06130c11010605060f0d0c110601090c08070e03070509180304090c030e0304060c11040902040c030506030706090803030c07061d030a1d0d02 80
    0x43c140084095005442c0e090004001205401424058102c100022480341c0c1010300a090800c0b05900441404112520035440e5115144481d0403e54001280d84459a110300c0801d0a600c01d813803079100300c2c1e403503c10503004080e8403c1103008501d00100090028503503c504018850042201c03c40c0d030032004100c600740e1b9100a50201041c2071907405e10703901c20a01d025010b800c0c000240e11550f1416191034180c0b8507154800901b0340c0c40351450034221143c183c4440440d80da00b00c9802550f008000502c040b403c540c04d121584104c003c1000100c0387d036a5103070b008a1015041064000e404203080c1307050280001800b00035a0103692041d586e06000381000d46840303189009444216070026070351100000036840318062074249c41ea4944011845041a50a00d440c0051070fa000d00204440984240211640070084a4000301c0317588020b502d03004107050002c0101003001030140c01d0305035060b082025400100241040325050b46884c115151810f000840c10300202038103ea02243c12600c002c0103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 857572706 1250 857571456 857571461
    0xd0801090b1207060503040203070b04140405070203090a0f030512120a050a1b02010231030f020303091909050714160c0f0909051908161a01060305041110050d 70
    0x902070000c15210300c040c8900300b07407414005a13070800d40004800000300019800c00300b080354010480000f50034a4980745c2144034041d80503001000303115548810102c1c0c0014401c10907280312181c01070030080744540d18604040c40003060309c02242c42d8000d0b0007150303091108030020780302c41c000380314060002d9035200700c1c20400502c0020000d11039140d0700e80d2450041c141355035202074100995000140d076400465440c1081d04500d9064241c1101d100c080d105007032a0421144003200d40c0501002141d9050f032001900b035004182040d50461040a0407203c1e030b001c04280601200c0b03482e01c0404c220345654808545800c4465400d1103800f03010080200d60030309001030002024011401102e03c50340713940d00f10b02020202d904c00e00400381c55150440a10000784034040a406004150b4114125140d80300c0c0b0311400b5403209020074403100c0340754205101700c0c00042015100b001414001940e11080050b00074041603405455200c924002c0740414208508060103000039512014100321034029000007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 857573956 1250 857572706 857572721
    0x5060f04030516110f030a151a0418150b0307060f120c0801061b0c260604051c1b0602030c04050d0501090303050c040b19050705030c0c01030606020d080109 69
    0x2040020000700b00000c2e07501d94a0030703d6034400d401c0d00740c1c003c440c881041203040220503400c0c400e4001d40b561400003032882184440401300315030301051100700008040d01814960030943e03001403c1032030141c8e02d21107035a01020f0303186c0302d01ca0200540d07a00c0b210a00407a00441c400e15015070207948280702d030074003070311810840041c3c42c94101415040000c000d016031f005c03591000003240151005100454103d403003114400d1450102c3c8000400645809006c110035100c0d08100241800c22580c2c900c03003005504003044107504c1150280c1c02c0ca03140096446076041103000c00060004281c00b00c01e407080e1656100036140038420107201905840b40d0001b544040c100107141401004005070030b40f104158000311354011400000c0b40c07000e41c100174095407030040c028000550104000d1148034000425160f111f00c80b40c60102070982c6211040c3c2c2d0a100350300c80642544008106c035000314000060805c0400020790b001e200300c541d02c1030300ba617840140500300c9022441ca500107001c80c9120780c0c0103e4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 857575206 1250 857573956 857573963
    0x50c1e07150906051006020d120e0712050631030e010315031a070e060d0902010207031502031f0501020d0c0f080c0610050d0309030b06042408070b030405060f04 71
    0x101c040040003030440444007001000c40b025900c0b0810003220000742010a402080b0500141c1413003240028014080f000b46410b40d1102a9220215103242004020724006415070030602c0e05802428207194ad51414115603501840c400c0d00180200e4048045601411101183d080c411006040e03409880d803141501060b410140d56800106550a02c42800401035000e890400c01c88401c49002d4400014006d2010007484800d04031f4030480e40710304040350000030a842c800510400a840101c0c03c00b1072651000d00503c0c0d1005682c240d04045074021401610112520000d01c8128a18800210000d206650240e00900c01032002c003030050ba0307800c409522804009150201d0744e91040c4840e0041003148150b5400041000011441c1c4c000d410080c0004035200b80c520742b60741e5030081103010740303010007000c1515180c00316005858540000c58000c07249400f03803c0c0000700c020720308900d00b203d11684000f803007880000074041c03401a00f2280910f400c040035001aa40d004241c03010002c0c040c000300e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 857576456 1250 857575206 857575223
    0x30b010507033e0f010203070813150f0f0f0605010219170a031b110604030c300212040509040f0c0306020a0309060c020d080439030303050c1e07 64
    0x20a440315059448084091144210f90440078041110b54a490140071001c01075a01c10014001e0307080c2c12880b10781d8048ac00744240c8117010328030716054218030501707030006512a041c003180d002040c0098205406000c3d00d4035042040051049123101a14458400d0750f01607000440c058400c8102d1458108016000d90420141c2903030184450714180d104001e0f003800640c0d280c04002e100d40000c50300400c4407086107040d41403402c2422201d9201c00c00034000034140b14004590382e040088405070401032030f0f6601c1103100d01c1024030a03011a5000105040301c0180112601211100c40e040196400d1701c4014003500d003260b03151303910225203590800e020b403920305a03840d0000000740d8a00042c440036940d80d60224402c45586000300c1990804a84074041d500032407071a15055500580c00e60340960040a00d8002d5104918600d61100c504186800704000601e141c008011011080c80c2c2203d10941e000c12a030b540e03100d04201c441c02802e40c903040222051400c2e006c840b4862014080041c05500f84 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 857577706 1250 857576456 857576507
    0x3100905060d2406050d0b241e0a090c0507120509030610141804062f0403050f060705040e101206090302071406120907151707030b01050703 62
    0x100f0b100800c21140380c410181c540341d048a00f4907910b015400007007600b5101c1c052000c425955600407a14014422141c001022881942041c010ba154404445014000702d44035004956180c880b500c1a4410701d01900030f401c00040e802c00c0a03c42c560b0981800c0ea0365506180c45551540c9590200c0c540440030403105000b032151550b414007841c0c0c010000c640c00220707107d00d8502621008915600f0080c0300380c01c84503000c034454143c0800d50381c1c01a41303e4800180082032000038005407140964220b0800b05a818450414070742d03000600a80740540112003400e8001c800240e079455080b01e0020000c0c00c103100820003801c6400000d90820103072185909400e80f5084408208880070780143d608d1900c80c4d4004040c1501444010064414251121100d404080200340144034038030343c1c4005c0720901000613a0501040c0a480041c100c2240c05450800d14150001c3c0048034040c80015035000364400b26a09a009218044013a5030603102c0500f800040d4030190344d10581b440d081c0340401c1ea0b1544 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 857578956 1250 857577706 857577713
    0x6040b1c290f07020c01170a05090709060b1b0a11060c21040626010b07050c03010c02030c190b0c030a021306021c0e030304050d03120c0f1403100905060d 68
    0x200301d840782010b500c0004983c07030161002440c1c035100d01d44e1729051000f11800c0c19114500018035540c00300d20401c010071641c13151005503103040c0306a03114071203607460305002003001c4450400030b1064403880101e440b000c049012200380c48a40c01d0b07000070b0915043c0c888404260802c90098845801c030042660418001c0e0200e0301c60300c4001c3c90b00c0070b010041c0050140034030350300485c903030b1041e0400418114682c130700355010400096040c060010703051000700d403110412004000c030391a1008094020b000613a440382c006503a0350441d140c264094003c0940c075201c4e451a40c400f04042c96003248005050b0307140c00c90004441c1e0b001501c500600d035020825a0807a0901d122840c0060815074024514a00240340d04100131007040044010408014900307040d90f0303000420703079041e24421a1403500242c1c0c60320b0291403290454044440c0070342000781d00c1e030000350004003105090b4820384a5901c0425120042e4025100440305001c1400075447d080c0301c42031050b4405640204050001c8071488d20644 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 857580206 1250 857578956 857579033
    0x100e01060e040c03020a0807030b0f0d06050a050609150420030709080106060e030709022d0301050307060806030a0f0503090d051e010612110a051806040b1c 69
    0x810020100392801c60408981c1081d1040c3c100ca280c040c03504604095a0240040107508003800000030540c913003ca40300303141c1d0b805404900b24800206029107414007843c00c40040e007012250989801d241400203012414030382440d44c86855a01c22003e141c841280401005128244500f8038003049507050400c1c5260040080d40101100d459140490385050389083c2591050b80002c401c216403000c09000640f400250b07041910440b01c00540c03104400040008007481152a541e850204010403910481c6024003c5050352400d50031f841d8000d890314426607649030b0649446403d540f01a400304041101d000003103c049200f20f0a80345040c100c540003039800851444291019000345c002034140c01d205482c0c0c0559412064001e1191500c3d10a2100f021000d10002810364400c680e04038060381d584007819800382c00c0041c0204085c0c00d44d02c060406010040341e07218081d510300b445442442c6040c94828805081c0080c83c0392145140d80c1d29116044d800700c1e2100004104500f5180004000c0d5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 857581456 1250 857580206 857580209
    0x90b04080309120a030b03010f0c0504090911030a031806021522050d090518010b2b140703180507060f0203092806080106080f060607171b03031e100e01 67
    0x25500811b17604100010982190007400c41c1d10b02c078625249414503019044030030388040300e030b000000180c400c00c1170514a0848919082107a418041e10700355504164200410070b100f070803107110304024149c44040999171003501d10142c0141105000c00500000004d1000440c03180341c03602003e90f440c2d40d079500c917413420044c01001004030b00b10301001d0225003002c0b91504d0121004403521a455407402a282c90301c0d1207001031100548000706080c107048100964155003074980000304000003800c004040d1040f1a0503242030000030304201300c50f2a003040c0781041d001001d402401401003103203800c805481c2d20442506250950000f405041495600c15650210300014000304403809401201001c00080080d0040300900c14200c00611000c0d50048140380c0c002e03058440400035880f03508c00110180185c8000800180d2068200c114014040b00980750b0340b44002d90080200780402510303506e9000880e6180c048425065000c2031140035406959001401d107540b0018040d180d00c0c007812020b109 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 857582706 1250 857581456 857581477
    0xc0c080a0e03010c030615091a03090f060709141905011b060218040c17070e18070e0307080109081c0605120c210d0804080f040608060a0801090b0408030912 69
    0xa441040000c01040d1140310307c010540e1a090705040d0414825904044203c07031042a00c0c98044000303240340204010b1040a1803d1601301c0d0110302d000c86005080205500824409801c400000d260a0520340a0b000c100e103590100c185e2010304050044904021b800090381c01d0200000b0344002040b01031008010094100180041d040c407407900703100a0703d250303080d0301341004110020603515038684000d103604426640340c07103101d201611001520080b0710110058094000906004820f078012229140341d0724160151000c0c103544408c03490884407410409044400204203c03e444150640c02d92041254090f0000384d450315000407820b05126000e00c007a1a60041c1101445858100845012580707420f011038000c1041c074103056100d10307201426000b40240400850100700300758007030b601107242e4908210740f500e603200f40c01404048240e4485000e05070f507140c04100c165041c090010704d07c1d0003000d50348058aaa9584040790350005101d03122500504000403400d011000003440c00011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 857583956 1250 857582706 857582711
    0x60a0819020715061215020304030c140c030c0916110f0f0601031a060609010e040f02180f040204060e060d06090f063305090409060e1509010c0c080a0e03010c03 71
    0x5000f041c12040702c1c0207422410b0051050b142c0500080c00240c01400d009006450158036600c1c1ca183c2500c3c42d4404180052a040400c840c8030354031800090b0a0030007030340c210111038011682205200700240203484c4040c0c65101c120285a04a0041c0d00c4d102a83e0100e10841e40c0300c0c4020310f11542004120340d01600d884e0051001041407040020300c01d90b46400c08901400303a41012000103465104180031203060084d0040c1440755a5550f0b03121222409640e14155614511140c42944c1110403c4291f44521701c2d4050404060030603100342e80c02d544450722280e003503400c00c03002c2081640000301c040113070700d840e42004140b444240c050300b00700210f9070501050041c10128414452000d2091480b540054444004860100c401c10900030a526041a41c1e48690071400700f0081e100740d400c01781c801410508000314a541c0020a41e1141c41c0541014106071a4407075804d00381ca030803625500c001040b101500010440700030040602c400036080464804241c07078042429101c0e82a4868042903 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 857585206 1250 857583956 857583983
    0x31006080d024e130b0309071406130b190201021c0c0e0904050a062307050f0417060402010e0a0302060301090207060207050f161202060a08190207 65
    0x601001060000c100c540050a459801111030241030300d841d0042c8940f80180c4510824111040503d00720008010082410032a5889501200783d501400c0d07042504031a9903000103801011009480c01481203001510003503140c00080941e8580c0880200d030310030760030040c40020010f1400420014240901c850307031a928004032200c880b80416070028190f900411006901800c00c4103880410901600f000400c10081001261540030b000d15840c0c2001c43c44007804244030740020290b038000d210b050103208102210002500c15000d031201e100910070100c1c04120190701400140149030810b400843c1055910031041c80c0302c120240750585075170030101c00e1106659001d2150ba0a02100f40d4150304010b00d10303408102c66100500c61900e4965001c100b00c401c20076590100c1e00d41c10303005011100051541c3d1819921a9206048441103940310000000c1c44c1c0b01d01b04038034011507001000d060030b18503462000d5905000051050780d802a0707013010005074803824030260098a0042a420800c0d9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 857586456 1250 857585206 857585219
    0x40204020913360b180f0610060311040b030405161401080901111e04030f080a030509070501090302010f0201060806010f060206011403061b13060507230303061905031006 75
    0x600781c000c5845403d200a8040c0d802200f42100e4050b800c1d40c0901c142245a551820b50155941408118581c034005c0e400c1401c03942400003442409070301130360a0540c40b19502d00707065044801c218400f0441101c10702c8200954950500955409400703241603c14544007400510300e1030166811076644800c007002502c1c0956401002c407035119010300c000304541c1d2401e00802d591805400c0701221129184201307800c0c8030703100c00c050314001c542c48400410140003514003c1c1c1250040e008503030000349890700250b20894001041001ca84040e15a6103600d400c5400440301c031000046c00b03000355034841d0000503a0307203001c04c081070090401c11441282d00d800c0900003410001c1c103900400d03102c5038014031030034a580c000c1521604a00d0880c03035084011114400124940580c4226524110150f203000070b00d542c102c0018001c045c070444a8a0b40d9910901001c40005600b0010a010758003d00000c0c02d5410714a040c03c482d00d0316403100311002651440028034041440c440c842c00d030742c0c5031507040004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 857587706 1250 857586456 857586491
    0x71a04030e120601090b0102070b1b1b13050c1c0c112109010207030c0e01030c08031602060c030d0609090311071a030406110703090f06180e040204020913 68
    0x140380e022640042c0c00b484020b078a0340c0d41c80c0b0600032000e601d6540c1c0c00107003c581c02008004000d01c50350b003440e5103617206a003802e061841a400040594000c0803903540150302a61f02c4142c0100d00101106e160000554070000200b100900306814084104070041c407212451408000d070394100000400c4418005000415800803000c10000e95031022055005042c203c841c4888440c18070f10303a0903242d092100c0101d1038849243d0010f00840710142d0080350602000c001203059a00580d01d010400d591072503690740d00e10a41354000c45000000484100521300305005103101640201144e0426840b07080c000c0840344c2507800030b08887d90707481301802010f4001c141e2220000c515005481a80d15010b240d5403045a444c00b802d000000c000f0014080121030343c080c90802d4213101080b03850700031518000e00a05814021100660004c6000040c2e15101d04d52003032080e070070382d00e64103042c2e03290114000710903001400480c0c0c040d40910580d0078940300d50914444c80b0044110215807113081035072003500d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 857588956 1250 857587706 857587727
    0x12110a120804031103030f0d0501050306070c052e0e0604060b18010b09040f1814010c020c1e15071203050103020619020a1707060e1c14071a0403 64
    0x20800d00d119610004105140c003980c048a400409400c2d107407003040000b0382580708160003445045008128a0507058856101505844094003141c030541c440e02c1041da00341400840c0140740b903016440880710728100001c8002c918042c094881c00c2080d40c84044800d46c0e4a0070720541080d4091002c000070f0080b1400f9680c10084c09a54042107001c4040d80c0400352101409511a25800007036604c4d06c5894541c4613185000100342c00304641600f42e01032007141e15148030180c40c5111041c0840003401818801c040d0b0316010b40e0020281030000c042440380d01c1c1008903a04c005e01c519404800b500c1c0c0c40c5d548140401940603600e05a8459a40ca40700d55030210b0003c10404051510005000580ba440e04481510091840c070041f00e9500c003401b02c0c94000485002040c8200000e032039491a203030b100280c10306902c00c0780b003400b04001c003004195580c80110403c3c1880f403142d0b41a0900c0034001c0e0070f048006180030150504e000055100c5408425441040036203000d5000c08100500d03500851201 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 857590206 1250 857588956 857588969
    0x140f0c1905030c060313080a120509060f060f012f1e060604020903030913020c1005040213091e110901091503060c031805010903020d020f0a12050412110a 68
    0x160300c5400d0038046a500c119801d0000c0c00340c04c001011418003214010651991503100c0802c542e01d00381c1c610f0041034071040483c04a907041c2080d0104034079550101c0c106200d041129041240366070344c4030400900c440642c0701e050520902004800f880115809030b61b01920021b1405805640490301c003620f41002c0b41d000d14081e490f000c0407421410400b050094100700c088402581303410364400043e0540c41609005644002e08011540c805070640d0049e003c00e0704007000317840b02c9070000d0b120343c803d94004a800070b40c80980c6030340e180030341156039020f441840c0c00b8100c400b02d1140304609500540c42017079010f47c0c2035030300700540f0780c41498811481401340886031001c1c450003044243e81e04102d0759078000100042c3e251030300314010910031341c044d600740d24590380b4040301d070b02c22428183c1c0200814203041d40107020f00c1221510460000481102600000e0014010360715503840c5d0004000003000140c0400800304000600c20040c40182103400d4018860f0b80300300140300c82001940c08141c7e1050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 857591456 1250 857590206 857590249
    0xf060e070e091b0a170f0106091502060f090102041214103e0a1d1008040605040f020a03050114070206070e01030e0c06030103140f011503030c140f0c 66
    0x6070340d55000a9407051400075030080d0303103800c5031250179244c4c2c98142c884000c0d540c0d421001c20180412080364070f81280c1c1d0940300c48543c144c4420104100242c1e6055050250344003002080a04c407114544c0c56102c07901c034000508140c2c68006000504559541c140c410490314510f043d4104410b000b1400e0f03048a80300c003000815041d08020942203090140244002520005411000c0044440f07054079034070120019900d40b4881c0c800340c1030501d40891040007081002810005051508076404000c810741c5a0070055a66690342001400c0000c0c01241c07070b04002100800180c803409000c0000e5480b440010800a90707091100c6000100108100300319030054083c0080b403508aa03442d046907400f0710300854001182481c0602c1c05034842c0740207400c01030000000040c001d4100910b0300d100100415565a070803420420350998518100444155644e100100000ba0144500b010710750305c41c545240b04810030244803400d201700c0507160111358000d55a44003a510300004040403018400030382 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 857592706 1250 857591456 857591461
    0xf03030f10051f0201140a1a100e09040c0305030307030b0319111207151107081f0c2006060f09161107030f0507060f03022b0f060e070e09 61
    0x540e44010a00c0040707440f00780a8a002855100390011110b851007129252401d00304100c680c8014091401c00c074003820881c0704441c4480c500fa441c4c1e01801c055075915249100000c408210000c400504215000a80c1c0303480040020014809588100400e450019a0810030310506040c80c8500e0801ca034000e40c41c07e03280b0300081409690440050050fa0b0350084ac4100c3d40f00316282010076008088200204541c115a881c0d00011000c100c0c80058290350030550348103000da90b103104514102a09035004260705240302e040d43d01403220341880b8900517001103500722480c400c0015821f07610301550000020404a03041204801814041c20350b000d600c2460300800c03454040943d040f581c01004180c00c5040c2c4010b41c10042c41001d541c010540440403001d0f49010760381ca0100b031081f0340111b002c8551841e2418004e100b40c035920300c0180d0300c0091220740c82d00d000250700e01c606a05418a070f17441c2d0003800341c13269078410380014000440802c0349505058034098001c2451181c103a100b5240d0404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 857593956 1250 857592706 857592709
    0x3090b070c0b0a1101060e0901060b0a020705150702040203040b010503010e19120207050310050703180f11011b050a050f03090a120206070611090411130e0a09050f03030f1005 77
    0x81c0c1500311406210219160b6826007030468030044640d01460340c41d8200b03040459111440d000540c040e0340c00d20020002142d807500c03081d0071802540ba502015801120040000cae091101c2207203041414000003d150111560000f0b049810941d0142c420340036000050101d0304003442180b040414030001072254445000c02070702c01c3c1320716900007800300712040009001c0d64020030006000d080c0040a48800305081042540204130466105002038200059040c01a50240581108a80000c042c0010b001261108030801400c0c0c16568100300300c181c60302c40381001c84289011118401c1000c0c21012496007062881d040321840d256500d0380042003c4a01591280701090454089900e02207028100d40001142c60140e9240900104e041113140d00c88440c02000900b61960122010411190200c002203118043d488903411110880d4a085c8000e20f124450660701020000011507003801076075916003844000c0305214241c1d840403052090400e0004c0e070056002981401900d1050319000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 857595206 1250 857593956 857593973
    0x1704080c0105090d08030f0a05130201140c1c02070602011a0105070f03020a050604151401081f0f02070f021305160806401104090c090e010b040303090b07 68
    0x40d011814842c0000d9400401d856681c01403210b9900204002c0e22403901c005039500d032140446040000740d2030003000841103003005c0f40c140c04040e010380d11001d80d006c204061245a610820317940d0342a1180d01903c80807003101881004001e011540901140c41c580040607094030020181000300c0c1001a480340c040d83d910109681c407141c0c10180c110440000c900b0305908040c840c0ba801340c440e0081c60204801c0c01140000c1d40d04111404004004030203904410a0000000b806081040d82000c4090301c4030407110a00003628250001300020000e806060f0203003280e1003120111014820303c882c10b820f5141c0401d000700001c0340ca00b800d100c80c0c030708501104250300100c1522030500c0a01c0022030843c1d12000c0b8456800c0003140c0d40e40d500ca040d50075090000c10013021081c0c0b01c3da0000c80704040c00740d0650213503007628185605e1032420103045c501e648015108840c65502088181200001c130080890b04003030081c0040d000c101e03036803429810020690380540c0c20000c0005000c0100303100089604 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 857596456 1250 857595206 857595223
    0x9020f09010f0504030606030b1012020d0602130b0c15180c1e090f1801090f0f11030d27030b060d03111209030c010903032106030c060804170408 64
    0xd1034080240b00070984141d541303000d20381000c1d0106d40340c03001c0401041030018805008203c841646c189440e030301d94103c000010351a100030740000c0c1080a050004070150098a8000c64800c1120340740e60301c8500d1018070b60448141441c05034440c10a00f214480e4851030981c100404001c40700070540c0311500190360b039205010f00b5001d01c03034065a40c0d00c42c01c2000d808520f841c1c80245070b804030341030035a00d242d42a02c099940d0258002c0e88a05484225014071038880400e6005100c244018080e456040c480804100d05413440d02c0ca82c503805885507400e100da406081c4194840b504074048039030807461a5511f5651070a0b864401010138004603521400c0160301070421540e042055507580f400715240ca00202d00e480080c491030820340416000080039101001c0305504071181ca0303007190011103218406200c00380114055080d009204100c54a480b14540c0000d100466032598a5580a1908081d0350242001400721028041080f50302140d045001d80e80081c4181024100051261a030707a10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 857597706 1250 857596456 857596459
    0x9102a0e0414041a0c090901090905010e010204060927020f0d05161e14190e1f140c07030309080f010903050f070c0314010518011434050c0709020f09 66
    0x21302d00002c030b500c1645011180c3c0d0280180100341c56581d100600c0002c3d0220307040803200c07542401c6007c0c3c0d4800e81442038800302c400f80e80c2d46000e450710f0810080144060406011003034400d15070f00d800c000c0c1040c0010580c5041e011134080d50344091a800c841151006412101c12120309049141c2903940071101c040108444103850081101c4c1f5a4292005034034010001400c2c24089200720721403107130045904c0d10442c3ca0300c800f03403003010110030000340111404103000000030422a4040491281820000090f004e03000b0350300e801000ca403440e240044036441180019240c44003070025010512250701d00076040340003404110602d0b58090f100d401410603c00950001140c15000d010181d8400c50056412090742c00724240002c4074980078240403269040c0307460b08808104441d0005210341d100b080c030000e0f0100b1041d01d540303c00d4003981200d000170402210558801c0100081504025400502035032580c99880c00e079802c2c075508200a41d84806002d6105000c1481ca00300c00404996a8280 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 857598956 1250 857597706 857597753
    0x21201051e070e0d12030f061208070309030f2f010e0f180a0218060f0d0f0902030f06010812120c0c07030503041e0e09102a0e041404 59
    0x490070411241d800140c00c0b026413040b02c82c00040188130ba545a20700610056680520003405208840f0054a1261003002c002e40303548000200840d0407200a0541540f01c2e24018501c070ba0380e500c5001c40400d1000342982c5155085851a442c2d005044c803541d1040c0704015030b10f0070212400d0000e080381c03a004010b5800307070340642010705896841e8010b6551141c035003504070180341001d104040c000d4020b1025640d000b945003600040c2407a141c000c4c3c644010702c2400007840d12001e401140301408864405011050300e80e9188801079400303110020400c00311800526140d80f5242903140b400e040b040a00340c0000c402c02038100e0007001c3e00030480c0e0000141d044682d072111492400384c50100c0c2c541c8041d21301d0102140c042210f40104c58140c05030301d101020340b41c2c0c4a85482d9007071448141940c0c22040d96019050030600c2440a801c00113403820540d0014034100313421003030001d001e100c0e0001c02d4001910842d21030310f40d1406104803080d60750664000c4a0a01c0c1960700c9154000f100600600c0404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 857600206 1250 857598956 857598961
    0x60a110d11040b0706020c06010b04180b04110a03020909060f15161a010312030501152102040b04050108130b0c07050709060b0a12111603170c07021201051e 69
    0x1d00101c212401000c800703005135920901d0341031002c000e4010720b224449a0042d03000001d00c1c02c840c070b0b007510142c1c0d80040c42c2c00341000a03500140000e0070300180b0190055100d170342040d040603602c1c001d0022000140c401680d56031508040110015008100318800c02884c903d4001030b4482904c20082495074141c80ea0303580940002c900d201116030000240946094482d02100100e00140e040c103e03842944800c18000307140605030181c800900440d141c0c18112000c80c03503014801c0070b0a40c800c09000c003010501025220110040c1da0246e00302d401080e5000804018550b0303c0762100f580300c0031001d4060b1403066950380e030f0765154801038800c44480300701143c170b4824440103200c520000c043d07c0708200011039880406c0101d5030000003a2402203240036010044100313250050680201d00811901c0c0743c40f900000c48009039164680070303010008912041050110f0a03048980170b0210641d015464000c40d104200068150003443c3d400e0f641044240503005c07400280350680101c00724480551a0f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 857601456 1250 857600206 857600231
    0x10020c070509040f0507090209090402011d090c03010f120c0303050304081c050f1503060403051b120403020f03070b092b140f0106060c021005130803040503060a110d 73
    0x2100e03034020951010201080c0000c01c41ca0144240300a84500700340e480f00d603a201f034054224081c59600750307040004200003500540c82007aa148082d040c8014861081650a010074003107107048a101e0810040000103102030012400303480010115850005040c000965440c49610920320008040c00004804501040152400d0b117044201260780300b080808010080b2019090603201c110546071071401154441c80e0044200140b050043d0080c10b90b5116540c0465481d88015103401885011074070100c0804414000400c08484e048661740d2264214010010b400002e01d5081d44a68090301d010025401901c0507660703180301c01c640a69001c1820b01050305280000c01c0904140c05400081c030041151400400301c0703c07114070085032040c900011842d0300301d48040c01074a000c511a1802c203401458592000025a8042d01d001401c18042d00002c6092001c103411030304a6400c04034050040e41030400546a114842c042c042c49117070a001c45400640c4202000c40442c40e88410100000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 857602706 1250 857601456 857601463
    0x405060706151706100f05030316050f1e1204061e020a0b16090b0a020304050f18070c051216020f221a0a0e07051813060311011110020c 60
    0x10700703c2c1c040a406148400d2005070300c0b50f104807620b00a031101040041a841602e1081c4003d60700c002c0d00440c5010280501c813948101507a804035207e04c50314464920040060040c40d44080c04160903201c2000491030050901d14030440c084850101070200300140e540c0300c4010385003120810010384009412a20407400e103600c102e006481d0345843e03014407007000e5080e03078190030850a550311003041e95140c010384021442820b02d080d0060f07200740b10038850b51615001510000c0002408000c0300c1592901522107400304a48480210301110760000c280f12041c0b1104c02204c103080c00c080c0c0b0301200844581644007011002a001f140000f0010074191504559420248003010140c1014401d00e02503901528035070002445440101210a24a0411446038825156400d0000e2501c0d65111011211508405040000400340c90b414907901d0311681c92640c5c400100010206489080d814409169801380c010076040205000060b54220002705095006074802e51015030395101086800c0d18 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 857603956 1250 857602706 857602709
    0x20306130f0308040f170405010f030b0907121d010504030807031b2114070914091b0d020315040b10020a14070503010f1d06011a0d090f0b0a0e03040506070615 70
    0x38403c05161b505501c01502e102810803030b0000d07694400d480300101402c50943d5072801c4200e40110300034003c1041c480c050040c1488840040400149941c4182020b01009441201032415650b4440600c800e05034011a419480506818140038105001c0181c1000c0800c0364032010800a09000300c8107001210309040407400060042403003001002c0c0c2c44110304400a44c0c0300000702d03a180340700040003500407150014002c40100702450a69491601050540304500c40307030031a54082161030401c00c03283c8061401a98404454004080580103020845421480b564451400e50f015040390940c000748064000da800750702040e41e105903c00c0340f880c0c80c2c040d8204952650a00c5070000c003044160b07105040d205000f000103c80406101c0070b8540714a005c0c01102d60011030351200c0c404480820b4000c8c8000aa005400585030b103440c1c548940d218a40b50080b148503e2040a100c0d16410a0007101e5403143e0740f2024520709490800015220b10418800400e000e454448121030003604e01030200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 857605206 1250 857603956 857603963
    0x10b1206060609120f07080d180b03040317010602070603060e0c0d0f061d105603040204380301090203070b0a09120206071509080c0307020306130f0308040f 69
    0x813044410317117001a84601c00c1c0d00403074005200e075a501d2145644212008945034a0303140003203144ca400c0a07886000d0f9803006009409000f001c000c04e2213811040006103000702810390140c011203041000040c00d940795a4020042190784900307002511903158120b807100884030a002400a6502000704058809a80641e1104280c04d50170180380c0602440d141c4100e00b106007186540361611000c0d00c060024107030a00e0706600907079050450082950100c01005a803000c902100d0ba45d0399000782415250100381c40c928103003c018402141094041e5407032206100482d00b02408a034034481802840d1281d514415034900d01c0144a282c50079406900b04d0b50b00501500c0301c40761504069a459407090214130005800d4003400100030b01d5034407000900540c0200b40f2850880e0071340b60882e0030804200601d41030f0f55501649800034250704020030315540d00101550f1118014010103003000002403c80300a0780c01080980d001441068402003c00d0745400e04160b640c60b181000004d012004030000c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 857606456 1250 857605206 857605213
    0x609100e06160218010806010b03070c06020a0908010f141314010e0606190503060a0f020d0f0605040b0306010e01050d080c030d051012020d26071202010b120606060912 74
    0x40031812050303861105050f0095a0540c4c0042481d82d0344a01020244140c10441c2c11860042c404000c0c68001141c010805107804e000207a05516035800700e91091740c195010403030484042291800c02e0161840442c2040001c004148000e00c00b040314004c0100000c00700c05050b4035140400200f0013421441c4120721000300a1060003400d2079070b4654080d0f030014458000f061407007100c00d200c074581406540001e03000e0809916a60110000f0341510101060741caa000d11a6501260584c4140504441d2210b8081060740c40e02c4140401c03284900c1485019411a030014003616410b084224119134052751100c04d4425a410000307424000d60304410242d002c0024095000d43c02500001d0041a2052903840019506e090011011703072079090080d0000600303407600011a0b480408401c2d80d000006890244140c80b04c0e030b42c4140e9001c107100b22460039010039080c00c5c02e0303424400e0a4a01000b0342d140c0701109459810b2556410b0000c0c10300b0702c01e1400140034a103d03250004010554120740046 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 857607706 1250 857606456 857606467
    0x90b01290705030a1701030c090903051b0a140706081902070b010b0309060a0e061f0b2106090601050d020906070f061a060a1205060f06030108060f0702030403020609100e06 76
    0x10b543c5a5020307122200000341112281c60b020202094a28100c980c40307d400d0030366500d06001400500316042056007030040a00000703d42d000c031020b00c0c00c40d51001602070216068180380504d985e28041795140b81c10b5101800030302200784c12118040e0001d0212070303822889901000480043c1c840ca03070000300711980c46c0340006203d00c02c5802075400b5000305801e84880b0f541e0901c07008102d40703103003403000c185074400c8011074990011080c1103000c1c2c8005084280c14103440e060020703202e5002a85038131030100e0002c0e60080d045034801c0d40071b4110b60100c1d44400242071442c0000d00b07a0141c50000d5a4850b80020740c58182d548803022903056951102c1c080d40042014108400102a003481d00d20400c1c22544000490b40340480031522944025181c030220303180da01e841c3d1070040c940142180e4001307006c1105115150361301e002442c02801c02e000185103500e0b0807144400c0019015210106545c4284020320040c0d03645400e846003e5410340e104144182c40d0320040b144101100b801c80d4020100050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 857608956 1250 857607706 857607713
    0x2d0406061a0c071224060e0c0903060108010c0203031b091c110d080f0c01060e0c0301080714030a20100203040f0b030907120215030106020114060301090b012907 71
    0x20b0004480e192090b2880d295903128507019903482c1d00d00080c00141c1000450f581c0360740703c5071003004009681c400055455142d508a48040300305039128100041d002c5170440051408200d05c90141805000074000940405006941d80c040035110b010361850291041d01c4200001c0d0030340303d22045c0140300030344a01c5407942d0001c008071031000964401811000083c6681010400503400540c400780c2145080312541010f16140c01c87d0702e001c0e03200c0d501c039040080c82030380c05a103490040e503000c002e0960b86d51506218030f2801d5940e41c042514101408862082e0f6907002c100101d2b10b0f90403100c6006c0c2420352041c0412002804540716600912003401c0c0c039401540000900282d80e441300030b00c1c0c3e4464845c1000c11150000726401121035000403400e00203605140c204800e02c51001d40190752000c9a01e8088031960001d82110740142c0d515682c000c003020401c0400d580000055008100c0b83c0742944071594851014045c403c41110514403e00c404083d2180d14000c013500340292903125500e514 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 857610206 1250 857608956 857609009
    0x22401060305160c080c0a05060f061c03080a0902041812120603051f180f0b01090b010815120a061e0209062b060902030403082d040606 60
    0x925001910b00400580203803004450000341d0711041d16428910040c5954005103a4000003000c09140514000000010803c100d520301078450b864280880d49049414030078104076161405038409010400000841d40055400c1d80060aa11001c0317860b1400f400810050143c80e1111038014600300c00c200c0a0101c11032150844017220740d5101c000f0400d901e03191041e1806030002808603008065151164070310007c015103464241640800c00210300820143ca52651900650302241e40070400404c02c01810411170162160b01404c103c82c2d0b101000003009400020301e00040303d405403c1c545c1d104d0361200000e5029076132a41c1183c2200c007440c46c0550150403400a14840d80c1606488a1704410f618025508140c0010b80300c1402c081c2c490804040c240349079105c03601130100d200c840034000d104600030500034141040e8096600c0c2024500200041d1004000080e00000b03800f01d2241198a02400b09999031102402c40c10b940312410f0100040405900c1101c1c1d1103001d410022a600b0f025 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 857611456 1250 857610206 857610209
    0xc0a03021c1b1205010b04051b0309190f030e0102011503081b010c110c03070302031f0b0a0f0e1e01090b0315071e090303090605030c0d050a050126030a0302070201022401 75
    0xd00c000c2c4070032643d14051005641068950218100705050090565204000556400904a00cc41e40682105200c0940720002d0a0040d107110305040703440070500d5080514445000c1c020f1008001e80c03c240c0001d11000c01481c00300501400d8001000c2c29907417003040da000d44c04440f030b2000b00300400f0071100140c19100310102d03420042c02140719140d02450702244480403690060007500c003106000380d01600408020075400c0207296141c568152035203500b002a40a001c035410009011410056204040d2034014039888080104281841510f2000d074203060440c0e22844010402007030741800a400c0480d041004424081e680041150342c540c8510b07180c440300c00d403041420200c0b2200b101110b2910040c00b01501246601d0400c0240601c11001150701100170108030741002c44094680d01030340d005641110344961a81c0c0180704001104d1401e1030003611329040101c1060110440030384038003400c0004401d06a001c6111015640280300403001500014041c01165041600c90800003800b03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 857612706 1250 857611456 857611463
    0x40501091509060e0601111f02030f0a0519180f05030a0e011404030f0f0803180d1d041d030409060e0a0204081504051c03020c0c0a03021c1b12 63
    0x5001c1c00541ca0500e403090405450b200d1040c85002e56907400113403402e0820350719a042e40d12078110f00d9101c01c001080c609484011329100544e0741d0030600c46414150341d002d414458002d18242c00c1c008203a00600d103c1144224500e00403078046060302c0540180100a4400380078640c0c1003001c101000350101c014192107040d5250300b00c42c05040e41c01105e00640584c0d01d80d9807032400708001e101040d060807050b4a03251085000038030340300c176036511070950344c00030b4500c8071002d40240c02c900b44440050010b400c0c20701d0203103005c000300c8482d1828030310740e1180100381901440c0c3e01c048280d035a2008000300440c00b00780d40101d80d85c503503585440340010400c510400c038a41203214081603842c4494001c40d0101c5204600400052180c4681c0103032007000608112114454480c00ea640d00700c07155584d0400c071080e13440041e2126803a001c00c1d4145a03030b880b4032074070400000d0814001a0b4459095620005980402d4814455580f400d50703031202c5c1880b01740c19002220140000e49005541200c05520322 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 857613956 1250 857612706 857612741
    0x50a06051209120f09090a02090d0b060d06020712031409071403011803170703021309050717090c0f030f0d050d0609060e010501030f090201050313030c0f0503041d0603030f07020d0204050109 84
    0x83d6461f44034100d0081e0144e032039100743c1c40010a0041000074007029005a00105200030002e050366401c81240c0c801c0704100c40003500b261b03e120000750948902e0010b03040c200420b070510b10b0701c42c1c1250b40301c94140c092908000055502c941407901d00354494a00001950380708070106a06040c003034440410b131000140ca290703511000800141c400d000341d49558015000010026017403070182c90240800800742c0b02080100c0c0000703c401100c4890050007440400041e060b1618010706004090724140039040c020751103940d0030303000c009002035040c1c42446c01c0e10742940c03500340006000e009405554802101b05040c080c0109541c060440304074100e640980701046403584850600050390303803614020b0301041051001a00040c01c5c03083e401c00e072a02c285880103d400d1113580300e201d201080e250656899202060a200701d048150181040d011400782c502110710f001000a40d0340d01c039250325480c20304030100c2d0145c21912090001203005900420521941d84c651801000900c0c0d442d4a05c3c42c42c04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 857615206 1250 857613956 857613961
    0x606080f07120f050c0a0b0301050a0e0c0921100501051c170a180308071415060d170c0f0c0f060301090e2103040b01050a06051209120f0909 62
    0x5400250030021030300d0041614580d10380544400302840b070f05003020303103040c01101281100340d55103140d0710002d0202c8451640e00c0f9414902442441c1e02a50850105540d4200c2401440702d41481540c4001408460440310882003941c060403007104829040218440c1e81c1955903008059004941640c0b01641c1c111032895044075030914542d100c400145c500c4a0503042201c942d603903100108128103850419803176807040403800810308aa1640192522900130440400301b0000c648082e6140001c04010400c006030403d60604101c800781156108518500090b4100000203069002c09510045480d4441c1502c02c109511120074a00c1070205009102c2c0d60381c01c03807801c0c0005c4e80c1040760107000700342113a003403402e000c1c0180a004014001032040035482180c0d2404a015010406594030391140ca07410b05191280c044c00068012a01c921200842440030355032210568014000406402d4015200c42c542c0b9070074140d0003008254500c400280704d402414015004194000082d01d90b401c490b03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 857616456 1250 857615206 857615233
    0x90906071d06030403031d0d05070c0605071a040f02090412020601052d03191208091f0c03092a08010b06091918090605070f020316050c0904060608 65
    0x140c40070040190720440a00203d00800e00c0b07944104c1c0317500f90100c4115800c0b4118102d40c0d16003072404061200140340011800d08002d591145070009102ca424030501308140e560350400d400c2e8030036400000c903000110008090041001c0451a019009810300c9245d0900c1d00305a400d00040c050564090310030000002014249149880311881c2041045140305028040700c851094005e00056810300c108020240701031034452040a04034401d2030202407403042c00d10045e2020100400800c52504404800c0c2c0c1990701d224803480d41e1500382000002c61412401d4140c006241d1080c015042068003005114210746503000c100c42c100005504032003841d40c441640342a00c02012580d504400705100c09905420610b82050031a1044210410246d40f03801c940010000031141c1c0200700b0351103080d401c003405080c0c13103402d402081030700c1c11191003615000d010396280301d01c005201e140b2800c2031016042c0101071180701d040d150010076032003880c02c060074100042c05950040e9085800340e01500c2000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 857617706 1250 857616456 857616497
    0xa1202071406090a020a38090306011a03070813050105040c090e0307050c010513090212060f09090c1302040f1401030606020604121404051c0c09020a0509040905030909090607 77
    0x1490f030050039000074501f030030f000c10b850f8440318201f8540c00c201524a4680140d00c9003c44044100c0201d4540e1201241d10405181441c1a440011400c440b4807004074030503140021290701c90180c2c03c01c40180d440702a559132528107141d1000d0144c0d441c1000303200422500d8125442154450301041c40400252000c01d62240300d06000103100798442904414694003420240c141084c00c41045a02640c1d030300ca40350160781c0000290014100100204440d41c40c1c242006d80c0600e00c11f85140c04585081000c90f941d40c1d1100640c6442031440d8445401119400d40455001d400c0004183c5402d0399030399565890007201032019400300c0e00700036001ca500d074800180113206d15009510b0b212070902c4101d05075081041502844000d400410001c10103850785050005028202403122107044e82e02e05018012010702e8010401c02401000031503034140d80329017518041130088500240b60b46440c40c00c94030b98800c2d00302664004c3c41500403c100c80b0f00c0401c08620882c86510b44c0e8142c0c0b429a51201e00d03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 857618956 1250 857617706 857617723
    0x516020d0c151b060c170f1609030302060714090a03150e06100b03070318050c03070605040828020405072304050136260318060a120207140609 63
    0x1091203001c1c94201140c91504042045501400d0a0004c3c9046c3c41c40350008000460318000f0f103103c10303070078000302041e00c2c0c0d080c2e40c1c2e4140314601010740a00710382e0029203603c406071903d410804800070401c0e0041c0240300f00d03038850f00c1c0149071030304d82c13a034a1500e00400c00070081169a0a40340c07000100c038034103020030306910440308182420b140c40d06100c0d014155410181085080603079a01c0320b61481165141c1d0005201d01910040c54a03640c9402050300c1e1251580004007040302c140f0041210500010790301d003203e01c1000310401c0000c0c4004400700000a2804c0c040d6019081400b4824a01e4112400403460303040d85480c880011185d0307411032040e03c80c1d0700c40e9500140b00250040c06040c09080304401d0a1b4403084103400b180c03030400c4081546107031500304005007440312000c401c1140442d1882c122011041016608146110054620a440d000740290203044001010140248207001c00c40700c1000101c800c54031441982403d4008030100d0150210500c10740000c03504c08100000c2505 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 857620206 1250 857618956 857618987
    0x1020703020d0c14031602100903020f0d031e032406020c120f0d05210f0c031b0408010b0f04141501030212160807140304030516020d0c15 61
    0x144103010341000c4403ea4802002907686400780300f0001e0003908140b0003082100040e40340f00614131000c1c01044501c1c01040b0303400040c050450410030042c0c0710340e158100c00c9601200d40e002040c25504003900c1c204102040b8294103802c2c0341c50a09429010390200b0ba401c1d04408170f0400d07080b00b110007100004614011480540e221110765103541c81c285010255450400050b258414101c0702d01030f1a18428109110100314017180d200044032440404802511310344040110310f080800308640300e000c004c0c018024110b40000014002140070200d44440300f003110318140e0301c0d5580c0310441c3c000c041c0b0340042445803081000954551400780901000740b000c81342174007078548a01c00c400801c0e03240d0107501c5051540078021010300200c1585420b01c07138481282042c0b80c0c00b200f080b004184240041401041c000c1c030390800c07410310501000b966031060b071605185035500003a0100b0b02c540072400b140251301c03a0300a00c4910401825005003002c84110b605401c214000c000300c01e45410072589500c2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 857621456 1250 857620206 857620213
    0xd090c08031c050c0c15010303081005091303090e0c030609070e030d0c0c05060f1c020c060c07020406030f12030608010605060f0304020a0909140d02122b0c110c030102070302 77
    0x1442c041050380090342000360380e10014070b80080b0404050800040010750b011070f03540b00c8010000d0540081d01503901c040e201c00b125401b141013500260259402802c45001d0024020a0908143c003e002110280a80c0c88101c1514a88500084002d510480d1054046e8001901140013103004016841005800030050104228090001c85408001e01420307100c00080c0b000001d500d48071480208400801c0340c000365070b246903401c082031040c00d0090304080c026104201c240300910300400c4081c1c0101000340450f0740c41083e800090042c1c01150005000200700f28004020441c0030f04c0e030f40400080584050100b155510685401c0701c425201c1c00340c022404000c075540e10511100115441380c4000e1001000c076854505c01002c688482d40d08481d5192410307068000106c04001c1088113000910040c2900285600e20890744e005928198081a0301d0540c2c41d2031058144010902400040c0000c000d0000c1c0300100500040700c1e004441d11034010840604a14101030003140c030000e4240c0c000303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 857622706 1250 857621456 857621497
    0x40b06060904110d0c0e0306070203040314030c061303021506030d030e101503021302090a030b06040f111806120c0903030c0a05010204090b0f1005090609060d090c0803 74
    0xd01005601011095510036036621805080026000103045001c00a65000603e5901000c014051100e480300c07443c800c0c1e02801c20490322a9002040314240da40c00404502181500f4158503e103000d10795540550740a401e0401105c82c0d00407066688c411b00030713070850703d4031014112084a4014182d5000f90550852000034040134084c0d00004003c00c0341c88100c4203034a9807440820202c402d4031510507a00040001c081055203040450180e600d2034a1408600d0040300f40001040b80e02c591000070700e951480d90005000f96107035448180380e1a0001c1e0180200d003001001a425940302a0343c0280254542c1d1450125040c148152042284400d03010040c2e80c0f03d07115421015040134140c0ba525210070400f050054030300f805007041d41445040003585030f80c20701210009840440700014020948200c2008555039050b8468041041c1824403643d549107000205d184c0b440b071684002c0c1c2101000840e0801510f159100c2d98901d8041c17160140c3d102c0d1600c1805440b4810210b041a40d6680c0949 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 857623956 1250 857622706 857622709
    0xd1109150301090b04020a080d21020408061302040518031b070506130e0a23060f150d0507020105040b010312024902070e1302030a2306040b06 63
    0x14000c0d0080308010800003219140c000003425280d4620088410000c44002d010850800e482120050141040909952512140010b10145400d4140c2400d82410b0710060700034021581114060041070341650b146191213a1034608900210f00220701030351600740000c144174008081041d4110707100d000745241c01000c908000121081f03c4090007107014a060001d4150358020041410701407a42c540800340b8581410a1300d003182c0100780588080c1020844945000b007008100c0750719a078032201e000300e515403d0100b0800001d0128041d00300c180d051100c1020904080500208240c1004c14030050b40e40020403400e82c0d509039801000604217100520000f5260501c0b050f088419204690785111a52201c0c2801e00180d1422404208d0300d064910480345070301042c04002e02e004080aa08441c4028025600e5546103d210070043c16100840c450380c0481d90017140c0c0c0e80c0c00400300c5440307503e1401e02010708040380d070f04140c4044016400030b55041010983c10b1081f900883c200403140d54200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 857625206 1250 857623956 857623969
    0x1020f070b0a0c05100207050a050c030c100f090b03010f05190f0e1e0f010e10050603010b0a020109020307090b030709090b010b0307031b0f1103040b030c0f1c02070606050d11 77
    0x10494413801051740410b1030080600c042c1c0510350089005000084060900d1814154450011030083c0c0103079080c0483c9458803c1d030341c0100301052403c641081044401114050701c2600f10f9580c001001000252141030301044006880e01100d045031342500080e103c21540e001c034860550308103d20703a0304000c9980e21003c1e03e036100002c0c03030b4542c21808088403111540e0904403841800b21548900601a034000041e68591041401c11803a40c00e03070405000a42d035000c1407044520642002914020307407032007074200c1410b903a40902150360550311007040c18003402404160a00030300c240310b4002490481800b03040900c5401c8200a0034a0742000c103841e41c0c42d44010100018580c44440e0120070000001c0c8202d24005280c1d00c00580000c030300002810305880c503a5038091648103000034007610054000f140c3c1c12500c041102c0e66a0f0310180485a050f02421000c1e072585400032604954503000c940090202d2445154204007064481c4100260001e824001900c4206442c01c200d0b014184038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 857626456 1250 857625206 857625227
    0x306061b030c170409050a06170a1401111207020d0507170d0212150405060f010813110d120905100c02130605040f0e010e010203070c082101090b01020f070b0a 70
    0x40042401c0303903c0c0c142d600789541c1d200340d00c0200706540d101d00304204892244100302c00303458040d2820386543c44000b6202d5580c80d01090127007090160040d1840100001d6001c2d07611080c8060700b440d03c03040b51103140121018103c4d4400c01502400d124400c0e0180304804607030600c0c0d44040d0032031384481d803509424041d8010301011045141e08006886100d212110140d105007840f03483d45041641142c140710540304040d02050081103041600001680c020150b41e601401507681d0120401c21800d019140070b11548216401c03542c0000c1032814045c40d4000462501041d45911024030341c0c403418000010b0b5080c52403000180c0d4540d90000502d010501120034148021021596607110000602140c4d2060552201581d66071105481c481e0280140100c206e03451000318227519045c1000380000a807181c000700356890000d4103004509000d50107982c110302460902e10309603100c6c6903900c001c01810304218058420350350107000c3c403000025040c1c103a6a40d120003609000c01c43d901510946004e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 857627706 1250 857626456 857626463
    0x6050f0f09060c0a05010f11040509040602040510051902060705121b04080102040914010803040302010f0212032409070509040b13141803030c030114040f110a0306061b030c 76
    0x4001c000706565901c80038002c5100043c0160032004514a882400c50700b41d18a40c81841d400c1c080740b240e14848183c2a9000c42d102078540340c3d001d0f9680e180c004000d1065801507944030203d0b84200c910350740e02c4000341104007a894106113102640e15420307aa80d030000c8512000041c4200030010a41c171000c000181c01c1141c0c1802c0c02d00d61207240c1c212031902d400c10f8200b41d13080d030340c089010840d108280c06803499004008520480307950409402c0c0340c5901c0ba60201905200245943c0b01180d4401c00c23011914106c24218141c580c10460027160702c0a01140c04486485030080c0c0030f6801c2d2501e16030a07402146a5103407036181420150502005d00f2058000d0760340410340002601c0b07000309a000f94810048200b16100f11031900b82014050a600d10300e0200c0568414020003003c0750307403042264195204024410401501280014064071041e08411070340c900700103003204024645009007403a840319480920200741c0350442201c034a42c40500c040032808018000c000171074003848041900600 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 857628956 1250 857627706 857627737
    0x1e0507020f030601080d230a1112070b1b09010e10020f100c0f0c03090603090c051e0f0f0f0909011410061202030c03061e03070602010f0f0606050f 65
    0x40d1000090400300240e00c203c1d03107504200c9448101c6a4000700741040000d011f0a03203011448810352403c4103001d03106203082441004026504248401c00000402c1140c000c46955100390528100355008425504540c0030100c80036003401c0002140d00b07941c0910410f03034030901810090802c000c0300032080c440c001d040d4001d8aa01500980091151900b01f000840c80813503000c4003010014400401d10a41e101080450221800001d42c400d860400f25203843c90003290f050754504004421600d203070700c29a40300c01260240c4940c0e0144641c504041501200e032503c4820a51b02801401c20301d041100d640107240b040f0000d42c514200100c2a0080740e40760000030044180801c000c00448141c4080d107910f84205800c04c11943e01a920180f04941002d0a41c11030403c2c42c04c6105a01001d09500d101d2116000328440f807041c00d0104088203400107048507201c940c2d4180290007007030701080c1000340c00d0400828138544101402a0401c490060703854915220007504080650381041151a02441 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 857630206 1250 857628956 857628979
    0x13060509130b2d0922060b060f040e0402030c040509150a020c03070308010f09150b18030313140306011505070807061505040f05070e010c0203010e030406080f01061e050702 76
    0x4074000807504182071106804804400c80034100844243d00a0201001280c1d03c041064040006017058100941c4150089407408040380010241d020380b1010b8104440003003400502414419940c0d8002d50080e030550b101d000414050000740c07030086840a226510800c100d10540e0200b00d0480da02010209005080518402c441400c1d0f40c800003041d00094800401880120010024000104240d9504002658840c814204454503e110b0740860420119031700c0b0441d2200d2462040701e120080030341e0780c1c403090071484202c40255406203104030ba8040340a0180350400183c4141a40c000400320441d0704581801115103501181085035180300a11550300098200d0049880d40d848a0070fa0015090800c01130104441d000700b448036009060205108109421107040d400c104020b01e41141003080070b0002c03d0140210300d055072600d21001900041d07199101c0061341c042c0803894229052070740d03038a000711803943c40c0d101d000b41200c0349210100749290042d0000c040252014202c034186a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 857631456 1250 857630206 857630239
    0x606170c1e040b18090d020a0510050721050a060503010204030c150903060e0a06050601030504020f100c14100b010504080709021c0c080a050916031b080a060213060509130b 76
    0x910940e5002d044513450f40d0520986042c2488650214881440103200c076060300e480303140d0f80e11069103507034400f45e40d82c00218000c0d52054905241003401c0a44002c40c410f451301007a00140012660900610301d401000b08591078180221412603030010b1181c44994100307407811005000e404251310a02c038580e14000b0019049001d1070038080b40341c00261005e0425418980d0684000801c0e1174101450041000016030310408905d8031181c0a94050394032412404043d2401c0d0801540a03100014115201500003000600c0c0d14108142c20790611900700c900b00152100d0140b030141140035001042e082c001405030350b002d0300c540380340c6800000203240c0010700742003100c1d01140c807500051903610400c20030040600545400c40c14000090420320300d04905448404042e0000a18000f2003c07008490365500c41c03502d00c0a0302041082d45d2b6900302500e04031000354403202d19481100024100002c595000740b00341c410b0307280c01500060303203044044200d000a00390400c500d5844004081c204022 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 857632706 1250 857631456 857631469
    0x1509090203060a120803060103060b0c21091206061302030f180102070c0e0f180304050f06130f06081e0a0f09051621030e010c030c0b040606170c1e040b 67
    0x1603406081c0171a40d80c10041d0006058407116002841034940400c24030703428010000da81c040c0801000b01800d1041c0047d080c2038020701c43e0044040d8071031254221212904000300300c0138000c4034100c0346074880480441c400303410b07404100c07500c00000314580001a0312100385003080000483c81c800044c58242960395201424141d038221841c0040c1c114104440d10056115072500101c11804100c04115120842503480c07299000303040c021210191100c64a8403090251040e5070418144c02d0301d01a20740340420340210161007101c000070700802c0420509611821840d01310340c03844001c5240744d6126190100079100303903040c008120343d4644500010403000d01111002c00000000854040e2503c0243c002c2d403481c1400e4058680169254400000d800032800300c040a02824420400190341c2019108048048001b4100b10028010081041101d50040091750301035030b140c050403501e880c2d0440c0d40306807070446c40350000ea181c00b002210701044c18416508040040000c00d4030030076400403444 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 857633956 1250 857632706 857632739
    0x1403272809091406090a02091501091502031c050f01030f020102160f1401080c0307030b0613270b030706030f0e1c030b01050304170a0c0615030303061509090203060a 73
    0x101480209a0240402400d00009405c00d24050041112480c0368000840da8000078245a500140c6000f188600b80d0241c01c4001c010181c180031114283c03001c1001a40700d5104550350299140c0e8040c00580204551140d907000700010744801d20641c0c21540c540040b01042803090741548038802c010000110811426405407030a40100d20010345020b00d442c9000030790703200032810300880d40c0801c08004084c0c003c2d40e5100c806031401050044588020640620401c40f121460364060a400301e070848510440111a0b01d07900c296160b07030481e07100c042c1c1c2114041c02c21182c0c075401480b01000a14820340028041000d44100010750a8403803401c80d1038014012510a450041284030101d0f06415208200751300c5802e09010749545003550b240c03048161700aa18009540700800e80c3d01c040c80c4034480042d2040d901440400001640c50900c8801c0c50340d41c401240040d08010000c1903000c40c24103480381c5801c0c540c80f1440907508103003265010390402025150400d800841c00188048a0082ca06 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 857635206 1250 857633956 857633963
    0xa110304060b150f0f07110604120b1501120b3010020307080a020a030605041d070503030a0e040b0d05030304210305131e140327280909 60
    0xe002424030180072125a003401240d02072103092040d104560084c00c202c88400d4540c1114954076040ca00d803000010360707980300f0300360403c0b000325010441d480036402090b4201c0c05000b903030400c1c0d60b41c19a05444101440360143c0007403048020080842603682280301c0c003850040100c0e40c0169100046900d422070400c02079003801d6580c040300d032601ca0070b200c584101c840b9048194610318040c44098080d01c00640b080c070402d50b00003040f03040c0038403940c00035000d0040208144520414088520300c46004401010054007603006c0000b517a01e0000110b89014585403102450241c540e0b0403c0003c04d594580550011100f0401d103000541c240700843c0b040d48203114100c42d10560516640540a1000400b81070614100c14010300740140003030203528540c0040c0b200f14400ca02a050081300084801c010450b502000603881503400200260490409494407201c968000c0d51400f9a2010030104d41c50300303c01b19514440c07420f0340900400751591040181503080a030b86040c6441200c5050505a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 857636456 1250 857635206 857635211
    0x1003200d0f0b09040b09070f0b07021306030c09090c030606060c140a08041a1209100c0518060f040b07030201021b0c0a061d06040f0806060904050d080a11030406 71
    0x314086151080c00310040151500b0400d1600c44004103401c10381c003902c0500011000000200721741410031880020345240150180d030715544840401c0306800c0644201d00c034511440c00d0000244480c8507400440f40c0110084841034903055101008007040362003540c41c2a00d140010011664a009490050039596280350b0150064101043c00c04a1a658000300d6040030003140d0201d20741c00103035020340d02c844403042c8611389112007600040c455404a040f001c110301c02008509940850f139180d85046102d824446001d06503000c035a039108003010100380c18176203880c18105080950103041c1410080b89003910300b070b0722152100c007603401865003200140e40008040800030440780d21128440ca080e0000c084a0342140d0001c1c081a52500074501040201030500381941d000340d00c0f03a54070382c4014000c07507552600c80f00e640e90904614010170000b4032854020801c01d0820850540c440d54005004c1d0580e064400c004440c003510141005003041e448070800c6e104a0401c60040d40a2403007201b00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 857637706 1250 857636456 857636467
    0x40c09030219091b0f140d1b02070b0408071202030a0807080408070f2102010216030609060b2d0d0b0126030f0d110d0504150501080a11100320 63
    0x103503205003010035280810802004c91064002c4000900e0b41283c2c200000d042c82d801c02d11700b000d4080d982144c044541441c0c0009001ca07880c0000d4a40d140ba16820354060a0302c03910300d1a243c0c0308078840d820403035100c0c090801142c1c0a800721500c1581c4010252000d1060b1510744180c00d4200032003c0e1221346e8001030810a8440800c5100000c001210820115900d00500203015850011040d2010302a50542104580c404c3c803050070064cc0c0348035242061916420210000d10994800300c1d0b42c10303e013000002e403918000301078400705400c0c0c410041c640c604203d142940a040e41001c141c0221442a080300020f00350103044e40603001c400341040031030000d190400302242100c907100096810802c1450f2440c0c010354215421400703078a43c0807498846684504c401c078490740c1c11040216107454240070410501d92102c80a596480300c051003140d072903581c0d00b5103a0799080c6000b488401c02a91803411400c0c459000aa0450281400100070f407030203140440d24003a204004140e0500040c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 857638956 1250 857637706 857637719
    0x17040c0b0418140c0901050c0a020402030702011d0708070302190803161101080c0f0f040302060a0201020c1209090a0f09051c0906090510032c07060906021605040c09030219 76
    0x10300c202e40c490a920040040c04c0c19802060148540c01c0e00710304000000603103483c600e4040002041055002d0821541c81c030306004020300a0102c1c0f005400b4110346410130b1600100f00080300d00907112008042d011b043d01d03603420402982c2d801d802e42c800c0f0b010440d1000581d0325007400030b01140a403628500751141c820707143c4805041c0e071600030141071240400c140203030051754000303a84c0481d00031041039642d120038000d0011180200d0340029400f07040020005500365064024107983c02102d4216859914101800303101e41c0514003444d508104444000342501041e50090f00700c0d00719810300020040c185844241c2002c41e8440000050505881d82c500c090340d22207258401803002d89001d0b16202e04180004c1d07101c0c481d0b09039010405031282c0d41d825030a0092090040515610802135040d0b9600c80581600d407119441214085400c00d10009100350001c1440450f10402520b050070786800c000800c4000d050ba4550201008540e40e404401a1912551034020008801490850515000307 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 857640206 1250 857638956 857638961
    0xa0e01090f030302071508070f050c10230f0f0f06010309050d02060403080606311e150c08070609170f031906060f030c180306020903060f010617040c0b0418 69
    0x103006c20411241c58104080154042c03204801e041e107518285503511030456a65251282174101d8000840c50064204503010711000c00c46141000e409a0102c2a03492082a00c0041421162412040d01600c0010b0070300b10f02d61100e542c050414100080c80d0310740c5880d0701e80744c03100c81601d40c00940d0201c0244000e2507003041301580d0140f4111905484e04d2081001d00c0d01040a402c00109248928050074800c0c1c1d450105410140ca441803c403070003840050490346030300d2000d10445c1d111131b040c1a540503046100c0d058106c1415003142c0d4261400c0b0103a55441e000f08800c41c8103030f03154100c816152510b25400300007490100314040300c068036800c10780c6036819403001181c680000c0f6490010200040ca03084405107448682d03a0400080982c55080d050b0341c0ea00251403600110940d4413804410001070741e000c1e144040342641110413644c1c803a102d403003891000b07010b090040ba5100c0740c1004158504203c10390701c241f20700741e124a034640d00e10321140c1d1908135030000a01e0040001c0285039880e141d2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 857641456 1250 857640206 857640239
    0x405090105010f0909050f031c0e030405060306270c09011b0c18061a07030201050a0545060108120a090501110c030d050a03110306060a0e01090f03030207 68
    0x89008200c40d5141c00100301442d64a4860400f134140c40751070300401e2200c203010344503210460900380d0ba44c840e402d41c00302d50306000e00c0708403602c12442c200e0804a00c1c00000140c030b0507130310050300051540d25080c041080e2507070079000006101c000b00c02c007401100340700000180585100e4036100c0d252a010b02c0090141d83c10310452002c4010400c4030080841c002c0001201102c20b41140590354250008040c0040c060341d81000c1c88101d00c400320702e40112903c2d00103048081c003d81c0200700688483c01800c0c03d490703043e42c0c10401d07a1f180710341031000042000c0b0030403c0c088112114500c15150340380310070240b1400d4a003810464006c00d0040081385030601c072020554408148045c0743c00c101c06806020700c011030152504100d010041d08408080802607680c1050005088030b400d951140c0000b0001d90080e440d0100003424000102c01101c582419a400ba20004204500340007902408655600b0042d40d041c3c10000e68210004844c4541e40110001c0c6010741e010381020350070b000a070f10413070182 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 857642706 1250 857641456 857641471
    0x913242309060d060509390f0d11030c040908040512030c0a0f0c090516030f0608070504020a0507080a05093a0602041a1803010203130b130c140405 65
    0x80d1080028030f60b1050400d5400325807183c0000f031103403605000e2916010603007200c000e1320801400191340c010301841ca03059640040300034070400c07812003405020440307103016070140d004185400c020f00041c00b001d10441d000800030b000c9600c4a0810340c0000c00707840001c50b068450310b10000e014031141c20700b8030901c0302080800c0020b51820510240d03a640e10081d144001d044140c0000302c000811002c0d120304001410000e400307005600700010031122031040c41c0384240c01702e4034048804002071401e000e12000c944103900942281c1d0324180610010754800103442003000030411000740050b8000014103441d45040d580d1903200c050070b605100c19a01000024003c400760700103662000001155440c208404080680900180c0391400720081d0240f80c0103940c0040c0c0044000043c815507234041c0c160a809003108a071084502e8050500b02e10065442041540d0301a5884000c544181e183c0b5401490748505242d0f505030030b44580303c88242c290400d40e946008003102c0d5405103050b0007001d40121a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 857643956 1250 857642706 857642719
    0x22b0317010b1314010509060d0c0306080c24070f14070509010e0a020711100f180303080705030c09040612031106070e1e0a06050318010209132423 65
    0x4105401c0210070085104200e8442c4c50300e0030344003082c0d124409944241d0000341c010350b00d41e0b64101081026007200038180000926290700001c02c204001501e841c0c03020050300403420700b001281110402048011908804882000b003240001c0b005011040c8403802118016029454014110f0800c43c0c6a40403c0c4181e40140c018804180c0e40c251154110380b02000045e40c3d4009882e00b071158440c0141401e81c080b00701242c0d060110b41100c42c2040d03000450b611021030684030440001d0f084103a00010300045c0c402c0e000200e03c213009800842c3c1050740b5000c207134144110500000d00340c0300d6941007031400918100207481010f03088002c1000c04900c000c090820740c50011802040043c1c4c020209118058403003c50b030780340071940c826070803091001e00401800d9480d6003000e8041d60041da083c01c0f5441d8081d1042d01e00c400103200341e4141d0303540148555900c0e000501c2c0c00e0003070f00680c8481600344210075042550b440c403942c10744000305841b40410003180c800101006130100b6001c0345902a51 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 857645206 1250 857643956 857643967
    0x80d02100605060d0923010c12020f0301050d0f06150f080d0206040618060203270a050d050a200a0c080304060813060b1002010b0a050d0b04022b0317010b 68
    0x9850f00181c56001240900c002041c800e14140710940c41410701114160500d800d2610302c411206401c07100d4205043e03183ca2029410700480141240f00d0441e508541c0368042c40180a40e1402c480355a621b02d00448595004c1411502e400c41100e05c40380b004654010300c06010420f5504100018009226010148c20000f00d80c000203510b034040104001c0465940b40008a18580ba2842004855030850011501c9150013800c07902e00300c2c3d12072500b00b20070400c0c0c61100c0728007a000800401c03641d40000502074002900000381d46e540c01802d00c42c002d11205190050f0344d02c900c12100940325030790300300030f004004c05810050790840d0741e500260f200d50030410041c89030a40000d44180c010725080c405000030005c5040c8900207004407140c5903440102c810100000360341c15000030400c20b0044541040b81030f0303104100041c4200c0c61345c000780080342c400c00141c05131034807400d00710409804011100e02103a80408158004101e018100c01246003621618070600701c2d010b40502400782c0003051031070003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 857646456 1250 857645206 857645209
    0xc0302030304151d0f100e0d11010902090411090105040c020309010c050f0106080d03050a05070e0f01090335121306060513020712020c10031a0a080d02100605 70
    0x1c1c80020000341002402d83d07a1002c04000c0d90b800030021030070480c01c101c000303e403e24200d41c95021107480300003280b04440965458031010310030200800e0485c402003411050710740e419114401900e200a111355a00d600420160700c40c103100754410752040c1d02045510015104103d0f21b40700603042140201d140c42000d50301d868001080b14441e680034248020041e2141c40c1151070021941422035440d42070407000116542c0018440d10341e161107803814420343d40d030041c031241203442c12142d04000950100c120246414440b600150810040c5010305100b0f4894583c0c100d20f100c902004180700c01145c0711029043c80260b41640d0740c05044017030034900110028017055034034000d009182c07220103c0402d0001c0000b50b9100078001e1002030003014101048200e00d038020b400021050310200410001c800300d15102190a80c1d502400525101d0310704a1008114010a99541d004d01d0204001194174140e58030301781d00d18020080800148010038001d40b0007401c1141400700c00c500c41c0d041600600c2103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 857647706 1250 857646456 857646463
    0x1118160c050d110304050a1707060c1101030f02190503070f08040b0c03060303070b0109020918100b0f04050319050c0d0309150e090403030f0b010f140d02120709080d0c0302 76
    0x8800261510740c1c00300403e45140c5007184500c0d440aa488111100009a64848a06064801541c01c0152600301c0d50303590302503408801c1448002e01c1100c4490900603590b02a912a02005110401c01800d0000d0a904c15400c8d800c411003001c0450001b0042001c1154020007080c10008240352400180c10503680e0340144e1a409003040045000c04000030742c041c0c8007001a00e01e9503401c524894041c0d43e41d18800e500035402001c4043c0211031148004401e1a404000c0710b01801d01e12000c00143c515040419145170000c1000c0c02107000304102c005900d54040050341d041c3c050710865000c07104403a00d00186404400c610349400f036245002c8840101b50010a01c1044a5079032080f510204c41d200c0c421201b4190b0415490382c818100400d00c07050690590010040750350111003084402c80800c0107507201c2a540810b0300015180c40324440210f540103015000c0344581607009410000038009000c001c6801311081c00025135109010045000104050361084003182008003070700710700e524000e48 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 857648956 1250 857647706 857647723
    0x20721020a180b0a0608091005190902130603060b0a05040e030d0b03240910020412030e0d020603040b3304022803021e030105030304030f1118160c05 66
    0x41248903242d0008944869004900e111200501000130b0941314000500780c0c00082c5c642ca02248241402d07101031103003a104050203402e02400500101c00641140005003003061001c0742c0010b410703038050164038102d006100286125140101c0d010300c002040c091030540d19841a84101c1c00c040012000c254080203c4004080301c40d00410411300b000f0110740f400340c002c001180403c402d003003c00c065440a15259000c1c0c81032100392004a000d081551041c1e00030b41c01f45107045034180f0681400039011b030b440b0b441c04000182242e80107406d01e80000340b894200300c80030b8402901d03400c100850320fa8a24080b03541c4410710b014801884044000c056a81003004409a000b1940080c2541700700d03800324a210800c4141080161217000300401c020040c0d082010f0052034508905442030006410000703490513200c0280095040c6803454a8800f424141442e040d22000228040303040340b13803a5051003076510001c1e800c54100c5820700100181300704081040c0c403001c000041060100041000c01d0170305 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 857650206 1250 857648956 857648969
    0xf0f010209100503040c120305090f011719060807080c0111071a0d0b0406180609050f060d030915051306020102090120280203060c281b03020721020a 66
    0x21344030758039460031000d8903005811070180e400c1c00d0000b51042591000060280000541321150310f80d56074001500c3c240321071608514030001c88400141c0508001c0c030003040e0f0701039605010402960300d500c06402e002c0240c00c82003407604000e020300078030b5800c00e007140d004001e4800200034080c43c010318041700b0015504200c40f22040028101b529220503000000030721f0006104201d1740750380c1d0010715082c1c4060b0010544260805000188013002c0388146032041c02c02083d0707580c82c1e0b90b5030820000c28444004048081c085400d00204000c008140074040c01480d544442e43e9500954003081e181c00e445038014021a80100b045e09103607607200140c1280350110030304114401c480d840c0c0c0e49081c00b034825002d203003070044034403c0f6900e900c801c218422520300940946002e9100c1e03d00e290058850204040d81c540c049100318221000096417140b052501403900b0000e0b00d075040440c07040c0d00443c2005030010f80c01401e09100c07280c1c1840b0030b807203145403c035540e419048580d40441c2148129200c0e14 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 857651456 1250 857650206 857650217
    0x6030b0711060c131805010e01050d02030303040215072003121603110c15030a0501050a0312080a1103071211130e09010204030206040e0907062105270f0f01020910 72
    0xd01d50401c4041c14130050038028180d03000d00541505044004d0409100c0d503079a88141000005190400315410800b841d00900514510fa40e40c0d004d2000100107050494070b001410000d14004c42c1ca6a421a40d085400e159100d0607655240c0401d85040309156115503a41380422014008905125061045035898209628110281940c0b00d0a01d412041095048040d80340046101002100218803505544004100a91b00c4009000149089010050019012042448125028203103503540a0044c4d03c020031410034504101080e0f410035204103022628800728051000c2580c001c5198000a100308142014201d007411b50324002144142062280780c42e01050103200290100c0300a10b40181c032942d540c9540744002c81500300d0440312000c40d07010321000030420307510806020501c0c1c1e4201c4c032206040b2003000010300050001030710500401c2007040e07007203440d01400e089002c00141d00304094001c0c81c3c0c001c0740b91410322200c00c0340c2c02c210307034070402c0741d04000d6440f446803060190051504 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 857652706 1250 857651456 857651467
    0x1090e04030909020301080a050709020a050406080a18032a0b07030f02040902031e0106020105070822060c020115060207050619140c010b1003020316030f090c0906030b0711060c 78
    0x1603a6102c8650800203685000000100d002900001c500f00180d104038111480b2940d60a0f04d001240101804003001131410801040028441e1043c00d41007041440c0004840300b1907000031040380a180e030200c012519018003e50a40005003002d844805201032540311007100780d903880d0f18002c0007402802450741d22000c1c03a4818001ea819200070b407c11400c2190749082c200c1c0304200d8640c40e207440020201d403110012400318810300406004600d29102c0100a8403503c001c019a00308100c080c207004140014a007020408901606002c442541c000240c100c01c4810f05811030b0340035405c05070540d0720182c010072290712100c0844808040b0450107020390b4522040440702140d0118103490842004624409030400c10344c0314840024003103542490000352820700350f05038001101c0851041e46036060110f070131402500509208101c80d48006448450341d5241d10000c4840e4000d9190300d661854140100010000d00c0d54000b0407600b0070200400c3c2c0201510703502d10001305101c001c0240841c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 857653956 1250 857652706 857652713
    0xf07140c0106120501110c030444070503010b01120c0201090f0c14010c0302191502040308070605061f0f05040f08010e010501090c0203071e020a06050307020f060601090e04 76
    0x1655440c80200e0001d01c28a580c0303a10400f0180d0b0001c2d4140c03840e500c1c05101070b055020308412940e0348050714001c2c600302440c110307107680400019034a1851075441029102d48030747c4110400d10b003c944944440007041d12400a0394134142040e00054020303894401c561540782e8100340c140d002c0d0094070301301188942d0045000c0b8090520080001e0120403804038034800c104a5942035007d465510549050411045004644923444814003a000d81c00c00d408694140752803410b0703510064085d90182d11003070740c040c007103000304c0e0700a51050340e0900c00851441c2c104080b60141c542c111344200c806040394854003200500c450000702702e01051008010500c0300c04d40c050419900208000511560703801e985040d0b00380070307280341c2542c04015464a800403070701c0411441401d500322001c1d40214145600c5a8130840b0080300b06001d0064090700002c04030050356941002405001d19560703054590500c1790b006841d0070000d860aa0050708918100070303041c0d80c09a9a0b504035074a0075581c0a69031a98113 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 857655206 1250 857653956 857653997
    0x2010608031204050309121e240414030c010b040b030c0a05060a020c10320f0d150b0a080c030412201b0a0806100b13080102070605040201170f07 64
    0x110b00b1b0b9000041c1c0c0382040c0c3d0307648010403030030200c41d0108030507140410351344c00c9903480b0300c888420340e01c80703040c0c688050010005580a41e1342c003603c9049080c00f0141c6e000b10b0203195400c901a1940203a450b0003901d42030341441d00411412502c15002800c1c9602454002072a5903154003034680280800304a24009070302c03c2042400061000c2c0040400740f2024400a1813200d0340410300304e2165010300c100d2600c031000301104121040e40d81c401410a00311003070540441d0300044204401540341e0407041d0b946010070620750014800114000e0382c6040300200a032501000410075520114103100300000b0403c1132549201c22080ca1401d0044100000c8610800c10152030700d40e403651007031568a42d54603040c0340d18881120740c2114468840c0d6921000a641c503682142c00406d01c80c00d41c80c04100c00384481000d080b088102c903c104024540f24030441d400c80e000000c05a88480e1070b40240415941c010848043d080140212003030180b42c0205440740001001d017031001084041c0c0d501d041116800d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 857656456 1250 857655206 857655217
    0x50f040b160623010e0f0f2820040609063b0306060607080d05090f030c030310050103060b031311060c06011e050a0612020d0509100c020106080312040503 68
    0x45410000c110183c0041c02c880755525100d0b6004940560001c1004012018404c0c4560316003040800c0540c0c850360510102c4002a0030220308208409100c1c400c06400703500703061102c500520002d101d82d250380c0300e41d40350b8024240001c09407004100904c1265070042400c81540c40d64144008407030030341c0f03000b500c442e0191407082c80d00c40c50345100f10321003c40c80307a51181407000031030480343c3c140c80d42e070200066442086002002e418040005000800035604201e6101150380d082e03c11007041004071a003154440741200600d90400410800b0540c4042c000d000509020702c1c08110703041c18481100818131002c0d20344c1c41c41520f41d42460b401c000700300c07850164103440034140f151600da03028485075990600f805034510104130b65081039842004010000b040b503034003e0105201e80c0c40c01c6420f0744d9103010688580d1003250200901c0011602601410340141e20100c020301c60303295070051b064121500868501d00b16414481c0800c6558000804e443d252072101d400c445441d251403410500d1032161 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 857657706 1250 857656456 857656463
    0x150f0d06090b01020f0304140f0a0e04032d081f1a0c120c0c120f16050f2d011101050c071a04050607030506030109050717010c050f040b16 61
    0xc0c1030011a448685801a07048007000707800301d0f54603204400c10b050f1a80164000c2c5102822440b001f0001442c6c81c1017452002803005d010f0a000c1522a445507001c14000c49050303000c2601045112024403100c603000001501c100a444a00e500c2514010406d60002c2c0031039104143d800d5130b0820740c81d15a9410030080481003102e0036000080e0420320065081410791155500400584580480314441240e024004c2c00300908041c904200412214400c0c03000094503e2044142105c0d106004110b01210b03040341c00c90030500d01e03282c0400c105030304101c007580c60300aa01002c1800340c01c8003580c11900294440d850042d4524006100480d10780040c800e00b06407a42c2890240f0503282c52000040c500103001c2d403000320001c0c4102e84000b400e00000c1e50014010f0344500002840316100e644a07940050000b070000c0307040809034603101c0c0b40c0000ea07040705140c10b103c8801d14010744024400d0852030400760078094240030000030741d0030441c001e0388241504040001110078480c01e0b0901c0c01d01c0301c1c951 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 857658956 1250 857657706 857657711
    0x3180126010f09050412050307021612061b20190b0f060114030a050a0e03070b15041a09060307080f0309040c0e0906042705060f0a0902150f0d 63
    0x450203002500000c0c4030300c04805000410104031180c0a003d02d40c0301e00d0700311005a4003281041e008441a0740300070315540850094042102e102d000d807000d000010030560000500440480c240700c001c5801e18100003003004004020524460b421010400e4004a9002980c0c44050a1022241000f100020740804070b040203144d40d0411010300050740c0210240b01c0f0580750f9656480056a0b4410344801f400c441c00b0050000071255010b54018691001e0f5a40d030115104840000840c0340d03400024040b02d040c048441000010503d840a030031180c0d000321001c0c4512460003240e034040306c080008403405401003000098a9131810480c12000b410114100d403072428210f00560380341e030403c6030034510680c2401f440c943c01c81d00c18120414091790044c4211400d0315150104401050030544c00500384a00c8500c584100081d006840c822902440140460380f60800000f40d14034001802070322a289440304040142c2c0311005055460010048444d50320111160924040c0c01500441d605460 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 857660206 1250 857658956 857659007
    0x9040201120c1e0807140c0a021c02150313110d02091f120b13170301180608010e030a08180712060c030501060f0f09030204050703091202030c031801 66
    0x358880a014442100104181c159894800c0100c5207680196401c00000703040c3c1c1c018052004c0c1c250300418247e68544101d810148450380032822917000c0c0f048081c4103407000c5d4070000550034140641080b00e0350400006155140c0401c090321300c00c007100405440300e03240d00404c09641d01c90700f503c0c000090b0014120f4181745807010407a8a40b00c0d40f03980383c0ca0202c0c09641d0024002072070690f000342055000821155543d611000005071550700c92054800c4074000e040c0b4660210380034000c601030949280501d5417219820001c400b43d450303903881603a05030314060303940000c540007100390b031075040580c40c2c2001c5a445040090440000300194541c19005248002072010320080d10110344600c290f0040c0404403c1c10021b80440d042403081c200407a40303148407044224414010b10803400f01c28142450311075106d80110302145d500300c441c0c83c082540c80e035075036040c0015400b030703600c0f10800d41c0b0045280140e0500415100d010b240400280c50f02e104d516501c5071380c0598904045d4144403031280341c0d1039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 857661456 1250 857660206 857660231
    0x10f050c010906090c0f120218060f1809160b04090c1809050402040b03030901020a080d020714010209010201061e1a1b0604030e010c080417150415060608010e04020904020112 77
    0x40a06d1069203200c1c00c451a00065202d400c040d51403e00360020603410010703103281400001c6000080401c0d43c009603007000414181d03244d00d0b03040c1c82c520b0508094500c500e0f052035120b107001d58552100c0100950981d08124005100d03003140c040da840440081000251120243c94107010314101024941107034601203a1100d03150b00c2144100d00031a000e21801c00c45405241e101d2040150700c50068108410030301c045083c2900a111958840c0f00c0186000c2c103d459181c011000d00c07590174104e940006019400e5039090003410701030608030806950000001d048544070300d03120710524010084090503660380901031406d030b840584509419140100c010046103403503441c120b50490104105402c0900994801d10720341018603800010107107064200081e4194030407500c2d10001c80e40c429450f07504030310201d200606000318441ca19503c0b50350400c003280001d07601103400c0642000400c200410041b4040c0c85110741050301a510040c2580343c60004031100050011044141c908083c60006078 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 857662706 1250 857661456 857661473
    0xe07060809010b0103020715050601200a0c0806160f0306031202030702190b07030513080d020a0b22230105100f0509060303070828050c0c0906010f050c01090609 71
    0x107a0446000700300800c1c405006400300d000308000a8070b130f603d24240c081c1501d0480e9000390b4020205050101c103804d21001e18a14520b00c504d9020360070b402c1102080208440030485070003078154030020b0042031500111840c1c2d10320a2018036030401c42100c10503403030036000b640400c001e1364210394000c14801c4240c02c083c0da44d40c420903040780180041c83c183c002c440b02462070390b004d40e1090b2454600c1c2c00000d0310200c4194009902650703410045540000710014100038120660300b05401500010f40300d814030142d1054001c0030018455030100c42a101030240340b90419419521202d0a0104084082003004003440d0005961840d0f01c0c00c001c0c0100485c074036481100300d07010410880748940e152018442402c2c0103844072609540144079400000d04507001410311030b1041c00500007082c2220112856034400c11b00c4d0400400c4001580420702c02080c401c0d082d0f600f0003a1140c103514240b0b880024413880b00141180c0c01c0180100e0501c040319004e401c0340443c07a07007080c0181b05008180c2080000c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 857663956 1250 857662706 857662711
    0x3071b050a09140a0902091603020c100b13090309060c2f1311041a0c01020406050a0306090b100f030f0203011e05010c0b04021306030b09010f0e0712080a02010e070608 74
    0x152010780c070000580394091350142c81c25036680174203140e01365218110203aa0b0725030360b000e00009050b0284503614250708204059038800b01c9042001c580d242d010400e000d0701856070890340c091541407088600129070003100b00f0044a410349490141c03004c2a04041154907a010000444c03c28200220180c4201c0c0401030204240211202c40707600e041c1c005d40307500f01d5807400440200c00070184400c1040d6154250a10280c400d04208586413a44450030305089a200741c200754040f41c40800e01600c120f50600c5175001400b0000320400146140d813000420600f288010300041125040d50001020f1080c1c012420902c1403c41c1036440e9616050030464806c40c0e40c03c7c100400e6210701d0001810340c402d501c001151034004103d0101d40d252038081c0002c20031000008202a600e4040000018549220a030301c1580c0610000540c4104032450740300769124046000c0055001e00da0074403c246c0c1c050301d080362295100500b50ba40d032a600009030f0161480884101e0180225000080c0312500600c2261 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 857665206 1250 857663956 857663981
    0x2030f0f160905040209031c0c031d010e0405040606050a030302060a0c0503070801060f02030702150c010e0f0c060d06030c06213c0f0b0f09040503071b050a09 70
    0x2281039440600641d1480e044004040014038400020400d03414964014507004a002e4251a00d0100c07662070510042c03010005d030300004841071070400c10b0641c44640c0006e807080c2501b50103000404200002d00400005d0400da2140c1d41d201c000c281041019030080d0003d10024141402150340e03030030040d417076076000c50f4404852803c0c0107990603c0c0b481038045a200da50300c3e4032070400a03401c1c031000300c07080b0a051031540d046d840204030002c00345e514103610b245120301170020343e9a140c1c0004851420349200b00c030112026400b5a041c1214000042031000d400003090780c07215120005000b000d03002e010190f00240c00302c1c0e00c1c42e01c081500d545c0f000110148001e440300120012080182200440311001000031a44403690030318400001d11008231100d40412446200704900d1300c01100b0101c90030001c2e0900c0a50b0b40b0700c0301801d28100004d800404c0803003121050f21070701e000d0b180d00f5201e2041c000c00070481000ca10040d00510030314030381100940005095540c078035440324000070050604802c0c61 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 857666456 1250 857665206 857665231
    0x9090c160510090b1609031b080102121504060b04060c1a09010b03061503070603050403030f1a03070806010e041b03050d0807090806060d1e0f0b070e0603101a09030102030f 76
    0x2c0d20700c01703201810220b100101d40c0d550403114a15140d02010b03400940e16807415014011002902c244240080c0205c00c28191034000c190414024440c01558500c444038021801c103801080f05545290030744048465a0526105503661403610501c400300c84404004500c031103209110b245001540000c1503070001364100ca040e81c941070307607006010b900d13200301d10360590041c0b01c00d1061920a40007542c00c14800d05003c10004c00a02c01e9030296402050403507a1040385022603122842c0030402a0700500901028200a5060040368001040c0080002d003204090400f00303001f0044075411500110f4011094600c10328940800401c0d0f0031040d10700b1000121144808642070401052060146070001e100e00030228040c2c2e01c040c3e082030300c0802032120718514a80140440c0b0010403095030301d44a09400c00c06440c0003580945900040340b10540030740420300800020600c403000f600180e038950090615200c50f0340d56020b80c107104d00803500c3d40650010041c00400f450541043e4065800203080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 857667706 1250 857666456 857666461
    0x103020f0a12032a03020604120314040f0f08030703050108070905010e160207172b050403170405060d0207060f0b03070611070b0309070e09010209090c160510090b 72
    0xc1180018140c040c941881024420520010380983c1000721010036a8001c4d00c0030400f00024100e14008241056000d604501e0800c020420702900b00001c40c1d4040c01d08006800c16440c1c0c00100c1c540080000b40014140d504110901002d607100071324050780305c00941c1d904e10346008000c3c00703010280324000b107921411034003040b0304519000d098182c0e409480703000006e50760302400504880c104411481580520703100414207440000d001e41d4125101002003c800740c1800c01d140c0c14207041300042d004601840752070b0b8940d03507012342210212030300901002d06081400e202d810f0207105650069610040c001101070351b0f03010540103003540c2c40c0110410403408039031030704d020305585c459403820b58140c100b444240318060062203186400030b5008100c4541d5600e994402c1071300d900030340f002e05e1036900130281040704102c2c9901043c2e02000400080d410074600d04080780f0550005070810b4810031010428170100c0700345c0011080d040741c1000c101d5104007a070340001801081350000540383c07103100900 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 857668956 1250 857667706 857667709
    0x28050c04020a0c03032d14091b060a0513031208130305190509030a080c070b2719060f120e15060d080a0215130510050601020109080f030103020f 64
    0x29039003444016240c00703d002d40d49980440080440e010072007402040c00c08004000507008000c0304034040612000501188031540140d141d44008060242d56404414000d201034a51004907001900980e401912619190016182c50080a0300d140740184400400018040d0290342d405001c4a952142041034548a44158001c90100783c054003080041010038200c102421140024100a290003820203862400285c01c04914800c1694140c00100c1d50300c1c8428014800c42c1c0003003000241092034500904451207650042c060380500452045840b481da54445001090400c0c0408001e4007029071580d0010b0403100c02c50a1101c00184482c0e0454a600610b00c0f80388840116880100218141c090010b010f41000402c1d1607001490010090009600f00c1c1c0540b0071034a464024140462400502c00c22402d00203140e0302007145010546004690040340c00029036160001c046299681c000050380034250784080146003031000912200741c410840c001e036060700d20132594003451110540 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 857670206 1250 857668956 857668961
    0x903050a110f0a14150a05060f01050304030f0302090424090f060f140f1905040c0509090714130b040801050702070803030a0902010c08030906090c100c080c28050c04 73
    0x20903008150301c400c00d500c3c0031a80660185480ca03024004613054280b010041c0c100c0080192a40c03240c15441c0c4091080500e040604080015400e1030300600b980340030b480092000005280c0c0d0b2007855400504984a078485400070540c2c40240200416034403100d400b4145031035103602ca0b03180d0062604102c000390203402d002d00e4003292000100303001410b08103c004902440f13040c800c01c0e40702e01c0c00e180c4690a925400300c0e1244014480b00d1a000d40340ca0324007403105640c1e08920480400c002004082010ba0f10f0114040d0400f10500d002001c0d4111006080d01c0c0b031003110b04da220881e80034100020000305c17800042c01920600700003030040d510f0b6840306076550011801008000d800600000c0e1011003684c0c4030740c144600514001d18800714a8035070580039481a145014543c111100b04900c4400800800c50302c414203560020b9010850354000703000f8110104004c003c00c400240400c0504420400c1844640380d03c54200c960041d00c001095072001020303022a61402600c0b4040028a07192 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 857671456 1250 857670206 857670223
    0xe0a050702010b0a0e18160303020d0309030c08070510020f0405150703020a030f020715050d05152209020a080604050f0f06060411120f07031404021f020304090903050a11 75
    0x103032460700145d0500e00003101c5114014103170328008100d210b41e00b1440394100480b5041d25840802c00310300b20300b9800c4c001e08140103103a00d03100b45400c180b00f0301c0c000399010505100690700502c21684810451030f10301d052001d00464000c081e800402c1e203171250a4000000d008640c8103e038401c0c403161a5036030714041c1d07006110f0080e0140e006140c00f03074040b0307000349907880c0d0300c070340c5841070350340071a201c1a0101c0846000b00e019000228080342c54039010103207114403a005440b004009603004c0d2050009103411036414401544c84d0001c00d48210301c1d4000750403500d07806d5801800c4650450b01c074090940c0d03131481110145e0b0140b1031403800001003580444c9442c00c1c8050300c00a081c0540d68801800058100c1b0f500b549460740080141160100500341810b00803500185420707a030b410301d20402015a44074001140805007154244001a40c03841c6102c50f940400440c5000b08010028003603085001c0c0340c1c000790f000c0e270900d0007181c02c241e0300074001e081d02c0c0c5a0303440d5400c00588402c0700c55982d00d0803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 857672706 1250 857671456 857671459
    0xb0a050c0703060618090809090915010b030f0106020109020a27091101170717041a07030b03061f0e150307030c031b03120806060c12190804081c02040308040e0a050702010b 76
    0x30008c140d524100350900b107500c541e8681c1100c3d0b2004484502e540480d20980c1f20260007040401440000791402001500601e80f6100910584445400040e2400c00384e119502003044154681000c00c1d201000c0300e00d26150902003044182164207290359840f81818580c1e002500e02440c0040303a442820000340558002d5542441d0103c2190402d98001c03009441541d1040c000c2c105071500600481e442d6220f0740341e580c0d0118030340341001c003814a00080a002070310f0304074482a4040300d400b83d1055034000c40c0c42602030076080e0b443c0c031608004540303101007510380c15008048000c8180002c0000380021684200c0c40e05030074400e484c0081c070068007580001003000e0741340620002200d00c201e1000e504680010b0045d858482c802003c5840c06203100c0c2150f0130a4404503012181c0c0402004000400706141004401c40c0380694412001d80315400741c60b41c110f0424001042e46d90b034940e05031001b6592240e84140c0e2541c0302d0107440b1140108a84100b04c182c14030002511991040c0500d0810450 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 857673956 1250 857672706 857672723
    0xb0703050d020705011d0d0f05042904050a0839120c061b060109050c2d0d0b0906030f06070e01030209030a030e100f0203040b0a050c070306061809 65
    0xd1403071001c03001e94802c400a8410750340fa8070014100e04d851114a07404e25000e032008040b00600b918000d081c0c484200c4541091000a11040003100811425194a034088420405c031208800c8040c8c022801160001c43d00900d000c0c1c800b140100700003074440b1a003407100c0b0302c0014641450170b8400d03002c11107d1115480418081c1c006481d4200034141e4100f000045043e50b80d6280c100002c10440c1c0c0000e0760044103c1c002c00d038982c40c1428240700c3c0b94050300720044140658509070341e11401d14400c0c11951400b101e41c1004031074969200602c440650343e10300242030f580300704182c00710b806081886c030341c3c9210b0704580d004a800d41c0340004100300101d003043d01902d995551010140d546445034050300303040c50b4003040781442954051002022140c402e03101c80421009410a0044a4800703204480500c12506c0386100002d4001003903500b152040100786a4404082204039168054042d04501a110350320703001c0100049078007c40b044e602c0d0340b0500c00e600e03158501001c042d184c2e03141c0b02034090786 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 857675206 1250 857673956 857673967
    0x516062601120b060f091510031503030e01050403080406023702010807030207050604211803110604080f07080111070f0803060409172a100903110a0305130b070305 72
    0xf120f0442d020391040004000c0c0c2c19610426000c600c0e40a02102c0e171540340504a0103040642c5803010700c0f0184101c440c0703810080c0c181c480c5141042a41140001390038050640c690114507032095048030059603010f490203840d02daa0317610203543c8100190850400694102c4a0710304076541c0319580c4617000520100320700880c0140c0040d10036507800b40047e0300b05a004c1000b003002c12000c010107070249114002ca80201c411044803910702182070b500e50402c200c1090742c9511043c101c0103110050320b03080300e0b060f0700611032000083c20394800d9130f100c2c103c680580f015040c6c101c5d0012444500321402d4100a100386030803a07c001003d4410f145000f007280855484038404181000701451703114401400001d0103200320344851080c0c10744a82d001e06880720000d09190104c188040e6010804521019405200c145005050b2500c41c0d002110b0700300c90703540c0151300c14984101034103040d905030b020654035080c0241c1001015544803204840e030170214854001100c04005045174043c0b90503607159070a14 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 857676456 1250 857675206 857675213
    0x518030a030b060c0a0515060405040213050702030702131b0816030b1813171201060e030c1f170606030612011e0f050612060c07051606260112 63
    0xc12550b05190b81000703040c40f500c42c4a81040101c040b80324060f0780106002910f8070000d001d80100285880d01642c1044140401030b1101c808d122401c082952001c9510ba80d0844102e00d140a80903000e540606090703580142444580e008413245403003c00d0480c900400f100040c4e5641c3c4c815a01481c4080c02d44072103080c01c41c4030b0b520404000c80300801d02c0d2000440300d61100b010640541c0c490280d04031162982d030407c440c001c1011211545082441d0902d040c044001004600501c0754505002416070804903559042c489000e030300d8002809084030ba035000b44102100c0203a062503001050107845c5507500c0c0500b12100c0391203520300a01803072440d9a4030050020020341e01c0b001440c29925004498100d0030307045403107080041c0004002450600aa84000984101a045a0140054001303d03004400003003482584280480201e035516036180c0713891883e101c8c145c0c1d2510310800c07607140c0202d40242e0140c800300b40702540b0640c07280540e1003507109a102c03446c2071107142104070380d20304000d000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 857677706 1250 857676456 857676461
    0x1e0801091503050a05030a0f0c0201020601060c031214070f020105040b04240608011509020717131a0a030617060a051b0310030b0a060e04060e0703080f070201030518030a03 76
    0x90740c041d8a001c0c081e601d40d100303850502400c50464460708003045070080b071644105240c041c04445d1804441c072581c242c001039141c80040c02003000300182c0030301c0503041c5030260070040b010b190308040030094080001c5225840040545d0302d03800141e802d8444074130440c41400b440f801281c002c403080da199161070b50740b10704079940e01c07103140041922003442c811072130460300c6444018400e0a0001c600052001c000d000112a9500460141782c07041c000b4501007944074200d00300d038403612245280c0c0da095040d1051805c1c0342a80c030040c1e41101c15005c2207504680e00003c0e02d40d494041d1414040c00b910380d01003183d07202c130400700001c469000000094a01026400a43d00111002074441410003040c1c8100d059900072200d408540060030b40400400002800d403941c880c400f1034007009898240441c4201c0380301e02078005448940c540070220520481800114011980300c6401e61f51110b00e2103902e44950070500003039000c00e24210000d801294108064114021108051031509800d0002a0b00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 857678956 1250 857677706 857677721
    0x1305030301120f0c121109010810110f04091d0304080a0605190c0f020d080c0a030b130507231602090406111c050a0c0c020d05011514011e080109 64
    0x1c5074030700c0410010200700641880f2024000b0b50399181d03481405030820046e00f1920021090203818104010040c1003c00700c0c011120003c41e42020a0611201810303852a00500d105502c0005001400103070001b180e501c1340030360b0440321030400302120303092002c546c43c2c0c0224800e580540d004034071020002189130b40900e912120381d941e02c00001a1880000080b102042a050003084003003603044041501000500890001460180702c3d911b040081e4055a01030008840145911400780040c00e6881484007004481d2180342001a45410a4002c1040308074030f4403403411015003070320190f05504071780843d030300c0540075409186a14096400d120703114900510651720a655400c51602407264107005100c00d41001d0004c3c444107180e40a61012603070b0140071000e80524000074511043c0d009424888150f0b01103500841c60050350030314902400a5020360541c1c04401c031000700b201c0c00f0b201d81501c501031081c0c0e039050784001d0b41c1d000301c01403042c450400c0b00440c84440c01040b080710315820034503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 857680206 1250 857678956 857678963
    0x50a12081c091101110d090b070503072a09020304030c030813200f030c030d050c07150314010b090d08030702010b031203040b0f010b030a02090109030f0308060405130503030112 78
    0x3a4145201c0780120101e404800007140d42d444112807210b401d40e881150381c064409404c010b0b0542a045280c05005400395124030307240558045a0041030010501c01da0b050150081419a0501840740e1001c448807480a2421012025031802041e002810b200b1703a403281e0b07072507107505251000c20785058500e03650080100e00c00752502c125283c0000e40f003180c141c40200c030b01004501820041c0041211100c03412018a000b603010500510301650f00103500440c074910b5052440da0380000c0d6075141c3c100065500950307802d0084c400f1014200d47e240c0d004080c0c101c9081d0301d4001c03590300e82c05c07070000074401d550901e81e104008109280126441400540c1c105110340000949581c5180c00700b0f0a20007041d04070700da070003004410082440300e52101582d00080000d456003083d81040064521804040c0a5131400c40c1c0c0807036100c0c00b0740d01801c1518003942c5c00c041070350a85489032070300400108045850601581c2408046105003030301d000f50b0340302c0690010185007560300b0f000c0e00005a103a80041a07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 857681456 1250 857680206 857680237
    0x10506160b060621011d070f1d1008060a0b090303070807020a030506040503130e09210c01140906090c01020a03030203040f171903020f0d0e1e0703030305010503030f181305070f030501050a1208 85
    0x4481c4ae9035075154200d56880f96214100e251a000d0304004044c1820740c04058081420814050380307660100858206651011465880d110240049054100280c2000b00180f18000c02d03c01849000009408030460801402403102c1d11345943c56544e0409440c1c49000354800c81d50307a210300c11140b003410740a25110804600f011001d0400b01d00351a40e105866120007071190038400c54031420310201f503100c902c0d4401071869413001e0340000c2d942c0400030740140c01c140c1e01101050410003508010206075801c44c0e07609141d84001100301d07000d54400c0c0c0d45900081c0540d0031050045010f030007035440281c06101c0450910b034843c58080c01801048034403c0f881c1c0904c0a031080d081d50078841f4541c0c00c2e0002c40c020b114090441c5805821600d0680282e4404d500501c41c90709048e05060880d480c005414aa101c5291084008510120798a189086040e804c00c000c001207982d02c0700205250301201ea40510076a680d800c1800204480ca001c0c402d010b2401d0800c48000c212980c1c001c00c1004410302c0d11 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 857682706 1250 857681456 857681507
    0x6050a090c0b09130c0f2d2012030901050f0103031209050c090c0912010b0901091d1c1d0303041a0c0f070e010506160b060621011d070f 60
    0xb5022903990501001c089900040060000d83d03202030256018805020703500c102c08031400004a811243c0c140850070481070b44200320900c3c008545031442420998102e5121022741e000c100c0d4683c20448103580558a000300244203009c07080380c0d2604881c3c01d5151a05984810950b0401034406001c00361094400d1800d1002503446503651148204a40841e064840048404010704031400700a8004668140701303c1d9842607884200c1c99044404c1e905c0c0c005030030b1500341d10f4a403110100300780741e03034850046804032000084091510780074840703150745040c0b5420a54403820004006030304c0c00d41d0103600500050100174001d0f01030711440c00c988012103060a0100d8001071404c0d2221a0800040c0c118a1003084080800036030305000d46001c5840e6420601d1a0100424210201a024201c1d417102d2010405030349401c011509a89010f000e02c0c501d0303110100d0741040e8004203204003907040c035405161414002140741e00600500565848140810b00b1503c03c481f90105160101c030b000074810071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 857683956 1250 857682706 857682739
    0x70e030c120c0406060212040933150201110d0203040f08040603090614130f0c0f0e060f031f23040b090111130b0f12010e0406050a090c0b09 62
    0x71441e441041a00034800501c45000740419958184e20003000e56021144040d44484007070161400d440c3e18400000d00384c0e020700d0b05c59003600399452140f1401d0395810302e00400103021000070001d82d00400c240e1f80900c00900d50807400c82d60164548103a080091052840392400c507001181c2240c01840c0400b0b444016448800132a40305134424030100740e868140b00104020f0f030103540c101c6100c1144030032062410343c0c03031403c0c05800d501006141d030b004040782800b00181c2501035406485040c91214507035440d4500300400d0042660341600c5090b2400c0500941d2a001403030002040100303a0040a02000341d035840f001c0c0801e2011a455105003041146418110701e024920480c060100c541c1c1c14208541e03410708440781c00f1449214100c0421140d1100e00031040300d4003c664103151280e56501d03400740c0c01c41c494000c8014410400e244400009400d15480d001c03e80600c0c0154000c228980701c01c002403003101e50f4500000c080c1e400c0807030104650f00c40300020b400110405042c42c02040c01100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 857685206 1250 857683956 857683969
    0x3070311120301180509070b042601050a0e01050121260d0506180708012702131a04050f0103050402030c0d120e010c080d0e1608010203040b0618070e030c 68
    0x204900d41c4002a08a80c2c4d14401d01401003540003016a03001d400810709100c4800214411030040c040400784200c0103086c500f1740c200241d0181c413480c900030002c034145506482e000e13182c3c01401910030340c00e100010804803541d0050120003000c0c2e9514650581d016901d803a071140320103e903218000810045030480807590002010124503014002480b03281640820205030500d00340c00703014040c0c81080002c0c0341c0e003101003203040d234440008140d40728500c01c245051021000c42412070503400822982103000c0000140815550a80f4000030300998605900c10030703004901c42c1c1c81c0e04c0103000300400c840f54000c1d07104680040c009010f031450340e0002400314500c415084400c55000c2082000711000641c4965540d05c13080382487c2c05403142c1c9550305d442205020782d4020503002030b66004c1211380150100080001c10b803000540300300c0300d075944041d28002d4004403070a4502585401c00100d2900c0c081c840d509601100b10340c40d141c1a12541c40844021442d144095010700c161030280c205a0b60b0301 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 857686456 1250 857685206 857685209
    0x1d150f062124010f18030203030d0c0f0f140306181006030c0e030c0909251505040b031f1e081905061b0426070b0306010203070311120301 61
    0xa4800c1852070070902100d501e8060001d080c282c800d00b011041140d503030707404101e2082510045c82d2140385140c1c40c1100031943c81081c0c0c0000d5051000141c05c040144094104400c0004551145000c81c2034141c0c00b07640c02184418240d0001d940210708403c100400e1000d1908030001038040449185480144d14170768100f034594403480c034140700042103035036814060749401d90301138030300b0f80c0e000005039006c42d03926070810418034030800c51000007442e040000c02c0708001a030300700c4007005800d01000300c919103000d845001c1c101c01420001c148000141c0a00100ca044488821160303246540b03902e644604422800c0300e42c50303424070a500000316490b1812040070401700071000401d0403407804040c44d1500290070050210044034006c140c001c140040f541700c2d03102d8641151100d001c0d42ca0a08200c1521464105003100ac030b5121519042e0418440005d4618402c50200c42440e621459800c100e03020840c7c0d0709005034020401d010000380700d00713100c4090541010031034068011180c4420b6907034009 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 857687706 1250 857686456 857686507
    0x50f0a120509030a050403021e060a120b0d12050a0207090c031a04050c07030c0f020604090b0306131205070501020903030f071703011410020c0d05071d150f06 70
    0x608908a4a80c8801c0c481c007900004404010351400f010b091005e01030340036611000e845800c110100c00c101781c0d030b50b441c2191301c910005c07d526650b05070a03501821007200d104004901604d0400031000c40d041680911202907080002c5000b050091201140c82e940080203800850080311000150f040a9001e81210004140c07804190803071102d0030243c8090071096074a100350b08010a00c840008038500302c90001d40c05143c4080c4026450410044294114900a4200500060000701a2b009521500000030103c003618441d40301c0c0031050319608515030002d404080c1c010340c1000064000d00040c4640c6104100160900403200006400c54100b40507194001034001200030401c003180f565034105981161400d0b0455041c00b540130300307030b0015109642c00f442140c40140c20f454000c0000c4030000b60010190405480715250940e290b01142c803800c540d02000702040152590071070790b01485011404802882c2e82d07803031020000ae090710582050b812000400c1490000d050300c40300400404034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 857688956 1250 857687706 857687717
    0x304320303090c06031303030c09030c030602030f0f040209060f010207050402120603060907030302061b0d0e01090210091d0c04030507120203100b060d091103011e0608060105060a0f050f0a 83
    0x902082d0700d030401641c01d0005109000c100200000d280704001d007584407075090701c1e00003202d404213101904c078608a40c00c0070b4200105100d0000070000340350000c6109450744144030400b0b84840820500c40e500070340f80294044002c800160640c14000e11044904d00148125071034142d41d040401d040340c0c884072146200d84010010490345003000c100554203d01c17410000c10710f86d03140d81c6009440385400781500042e10200010818008945c0c0d00340e03003c010080d603040000508200005000b0200d8680c2203014021018101d04420b0181e15254200c9440d0221540d1000442e112000959401402016500c209110110100b0810072101303020304031015000807007207840c0c01014038003508403110f203501d035007840001149074032550165a4185503e40340031504030716514180303440303021090440e0b805600c1d00f1250b00204c2c0319201e004094608030300080045586584800e071301d883c000d00406400100401900410b40c0c41013102507151060780c0341050a000c080e03050700446901070f6001c41c00065 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 857690206 1250 857688956 857688961
    0x432011b0b0a020904140a38210307020f06090a030f060207050a261309020304051e030d0f0923010204030b0c0c101b030b01050c060708090610030203030304320303 72
    0x81151049184035008e03d03803402c600050b505030601a240c2c1c4013190074001010b40c0c0d150724850b00c83c5400b52068041c1c400d04040c0f80014034004660340c0c1c104120036441130550001014660800344111074050401504040142e8196121800e001c420300e40100c1e8410b0742002500c022810130302002908a01c240a070184980f201c2203960305882c3e00110022131101700300140042240402991070840e40c11940251b160b99480c10810f0601994509025840100c007466507000d400c040002c100c021000c4c40108410247c0012190031240400c0000780781c00da400c44460342c02c1c1024030295140355002d10015282907200d40e81c40c0c0781c691098600c08030320300002c030340c14081c59814403494142eaa002481000030b0b441c0d0711100c50030b8030955081403041c140e032011760604030f900c40d004070361805000d40c089800c24100f1000041c980c440803521055170b4050400450301440b6011a20030869400500071400c40d19030392104c090742c0c40900c01b50b17841602e101000001c02444c202c08038540d100c0241c0599184d2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 857691456 1250 857690206 857690221
    0x1303030801080318040e030c060c0c0708010b090f0408041703030106080601030203042d051b0a051002070e060a030f230d0504150201020432011b0b0a02090414 70
    0x221810b070044401504240410000030b0000c5441d524103034401c55000c18042c10070a1214118455103c0300c005601074402041070005050004001c6282044225422207a840c00313914200c2e08402901d9a01140c2d4002003402d0144030343c6040e0b0030900480085140541c4c40583c610340c00c1011040d060070350408030040040d260070483c00d5500400030f0905500c0c40c9050741c0d50b44c80782041d01907590b00714008031840100300075900b806c2184143d44807040f1128410044040000a16000041889052072010100d003c0c204492000a0134200d6001803481506013203107150901f03c010685900074542e80c03000800b00e903a0341c020205840c081e151025482d6000492440702000d00c521040569002c8404c9030900ea61001c1100d0455803400e145050290240c10200d01a202d43c0c0c1c131840c002480416600045001ea40a000c1c2c3c000c000310b0385002c0034150380c0056421040c580003030300b00b02c035810002201255034065401d0303020528040c01450202d0601c0010100c551045444085890380d0080040d00c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 857692706 1250 857691456 857691467
    0xe0f01140703050c12070318050721030203030109020f0d060b0913020a090605030907170f15060d021e030d18050612063a1101032c0a08130303 63
    0x3080c81e900d000c0c40b841c94008800e41080c4140d441e5800c12542003000554014400e81c17040c2c0401c010900c940c1c80302802814410360700d08003400346550f0394241c4582c600f000120b8440043e5203da0540103942168a420b6500e03000750030543c0c00300030001081020300361030141c0c0d202e00342c007606241b102203491360109800d000007910b03400c06000089104001100407243c00403409006c0707540d6880e02566983c0e0301c500c240d0911080780c1c451001d503000341c003000c0840c610210344140101d8a0000b2140350002c2882d08001d520416201203030408103400d502070160500c040d0a003c03510b80c1d2161400482c05c0f0002181c5001e140380d15000c001800001142241024840703179074000c0c41c04450b594200146038a00380305101000c0c1c00180b04101041116044a000c010507068226400b80d403001c1a481403a84200449401c1508456503100e0b4a1003013040d6000b842040f2103071201d40c10646490440c41f007a041441c6010f010003c851007241d00900008100d070008200d080c240034136405005103035141c0030b0709 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 857693956 1250 857692706 857692711
    0xa0204090b1e04020d11070308010302010f0207030b0f040303200301060e03070509060402130b070605060a0e19051905090703060b06040e151309120906050a09180e0f0114 75
    0x803600450000240c4841c0c003519404081c0b41c120790040c0d60700c00025105000304008001c12203180e90100b115001c1c180c00c400718074100c80c000e884d010580b17a00320b00e040744c0b5943e80d0300000780802085800300d41d1801d80050f40035402031181c140001d04402480301243c481203840c3e000340c44090000014403400d64030614903e818074058008054a6007040005a405030008101d24007459020544102ca0300e8188600401403510101640d580c1d000340c20080040c02040301d40b24004e210310b01d40003402803505090241b26880c2c03014254800b01000b0130300c4000d044041d101200c403400d40111421042e01034403d0700d0042c0d203500010314100c0d2851401400752141d0885c03442c0f240400313001c10040f107085a400280d0080c002c0d4044145021004001000070b01e59024801d00a4034002d1510200840b44089180c400c0c0726854075041d099550904440910030006030f40001200ba034004c210613030388603a07101005960340202041d900c0c408242181b4010040403c002e9030307915030f0f8188c2c1820b070b0440041074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 857695206 1250 857693956 857693959
    0x6031802060c0d0905120c10050405060c010507170103240b03120304050d031b180b07140c0306090c0d0606030f0507141f0e0d0804170f0c0f010c1a0a0204090b 70
    0x454003c6d07441c40c0d50351076607200c202140c002c030443ca8064440741e00c518110790107881d000f40302c1c0e41c844089255842c0200710455000c0040f03814420455035201c04050402d0403240d018204403121824130345100c510a2820904408183d265080130340603035003e000a1003008030344401c0302e440707180a013055840c150a00c11600181841e11544030141c802c28410b0008000140c144402000b00c1158003465119056001081440b00810040b04110390030b070010205070400000c40f19044156010940c8581c1d0a50320041e00c0c0c1c0c4030182e03c0300c41d81403400c10000b0b264081d0300c0014a9075600d0b196580c280086c004202c0d00790700482d00511001e0f60141c1500c12004003961945006030b4405c4041c100c924920152805100709401c2e05081c80d40e4074500c400d20203600203600b94940d507460f000344451004083e0302c285180240f8130084520000007440d01810700f401404006e130140c221006481401c61120180c404a0020f00306018a00d080d0078003901514002d84010303500c0b481c3c180201d084801d441d4405 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 857696456 1250 857695206 857695219
    0x11030c070519020f19030c062c0a120606030b010b12010e04020102120d152907110d030c0501020307180510090312030b03100b0a050105120106031802060c0d0905 71
    0x344056184d08000c4240d031502501c042c3ca0704105804280040507465000400700c03c0080c0e004248a80d02141c1c20414103d5404100c0d802618410b00c0126005900c3c0002d400186a500800901c881460f6065400d07015070300002c0c146460740c40b0b12a140c1000d070411042081c001404446496609a000d4014520140e8640361402d069000039100c012503800300880680210702c4e4203c401035130380400502c0800c1050300200d20707a10a61000c41000031041c00c0d4444184214100201c80c800d0f0440b5107840c0e102c0c0780401200a054100020010180016010802004d0701344000680910045026034007030380740d100d0584010205607030014141e401c0780740941d01d140d0041c2c2040350484200760640e81c0c0603404010104000d00c003240184043d90303403264907104044072000c403440558003041040e00259030402d041903c420054601c0d01c15280c2103030746181e01c00010001c0c0e031f1081d03200101855404082d4200302c401c9800240681e04480a140180c1d08242c0c000801b454111042d00010481581d02 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 857697706 1250 857696456 857696503
    0x3040f031103070f0b071b030f0809030412080c0304080304031a01050a031a091629130909051011031008010c020c040504080408120301060f1e0c020411030c0705 71
    0x268031342001501d0004212050500c04104041d000d90003030b04a8001d0b45d04040501113007410020244450782c150800404c1e4600003050704a20080121025500920302c02c14074051541c0e14864107a002c0300c0d42e0415030105010101300c400e4140000c01c01103002d00001203018860402c0c00c1050081a4070640c8100b81200007000026107603070a5a0002c01c00c0c9d03001030700303640e10b41c04614103000300d000480c401d40030651408910103241490301e5260b100b201104e44904141c2c03158502c443d201d407c05002040d000803004000030f10b0b0503005903411920580542d402c10100110b890259500c3c08142080030201004104009650b02880402000400000c1c415880f071054040d488e41000100d441c0584c0d1108006414422450121130082901e0401c641288004c503201200b990828003441002030000c4001031002c3c1e100d40466201140403410414540e0760411040d10310101d070010480c0c029840d940c1180350001e0144c050b41c42000344092441c4d9a244a10340a82000c0b81c14011039900c1198006 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 857698956 1250 857697706 857697713
    0x6120e0312010501080a060f120605010806060d12110a0c05040b0a1a0f07020330040f140102100c030c091e03120c060c0905010807032310030803040f03110307 70
    0x4038504445007801c01c0000b9891b0300903460040c2c8169000f84144c0311902500181041071080c5035882d050140c8000c003c01d0740c807403e1441e00c900041d42c8040c3e00000e480144008600b081c202001d203c0d03102d0801c400e20008c0f1380541410103000c03110507180d40801803c100464181405005025801103400072034041c02c042c000c00b000e0000c021840e281c800e021484000b9030340310380111040c1540080c120381c01e10500c05404107030480f00d40107070054800e0782946c44008032540c50669007a526804c5145241508004103840425640c40b030550440c0b06d0341700360700c3c070060f11442650440481c5a030040381e806000c1c0d0001d850100c5507401640301c91070000601c050785d2039185040b02502d80c0040c2843c05003200580c11940e900d503401d0041c14a40c58100c4c10020160410240411a042078071404110307a00c3c0b01041d0201c80403820700b0306401044080000300320040002e46a40b00c210044142c00d0380e41ca94480007065001210101d400784a078403120340a01d90089160702e103501c4400000d40c5000f04665 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 857700206 1250 857698956 857698987
    0x90102090904080d0f1103011401020304080c01030b21010903021c0c14011d010f050c03090607030509070f03050c09010b072d060e01050402090603010e0a022202030106120e03 77
    0xb00081d0010802190501d5505119084a00b06441d40704c401c1c0b01008007907194020381d61080c072880303004002d0301081005a5001006541c1229a02c0b000f60042c10071040055000d0f00050512951014013142e02510308441c40607900c841c2c0506070b0001846407154903001e071030180030812407205400000340d4800c89a50043c02011500d034094030b00340d46107120314040781c05008041025004200304d0026030058500c154040300d42e00b80812020f10441e182d00c1070850181c4011b90344c100700da821500c00541403034000d4200750f130040003000441d0710040d80c441c00c10007030301c0a03a08122015008450f00031141d00e0f003402c0b49809814400b80a902d040401e84c2d400010b620340c1140c0451718090440f0088004d5460301e41e544580e40c000e9821b00018880301c980c58003c0c503086500b00c3c891400e40b8046604c40c28144a45000c001c40d0500030301c100382090702007005200c52900400420200c142e03c03010142c1c181d002850003811591244207401e01d1482c030078000c0d0b1311042c1c25030300c0903401030241016024814 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 857701456 1250 857700206 857700211
    0x8091e0918210909010612180c1401090e070c0308010806060a06142215170703180501021306021212011809020315060a08031206010315090501030b06090901020909 72
    0x102c5011180c41e034122030310b2415000740c80710aa800400348000203181a04030003140790302030552000f048207494490000045080e24035001c0c262150b42c00c420300c117065140b940398198a005040ca000385540e0380103080e0b09088100c0e20403000810034a14501010f4015103481d0143c2108005040e0314a0a64045091350090384281c0c2e00700201c0040f688505100101101c54400c20107201c0010150482804108841184101c0700f0720348221075206071180c40f858061502c05202200b101640c0c42d903090403006020318000c1603071500c4003448030f907000400902c0105150075000c03400707070700e410b14000300641050005140460101e400f0000102d030801c04401c070505581f4800340580b1040c1b10b10342d88034020301c00e100c0001d401d88280e00d82c200501d600b2188140c410401122a4180c854540c01038540b00d0050f60540010b00041c0404900c0c2513000c1c2c0c02850844100d5007941a1244e80c5040074419500203a200352000d00e0607905100c042e003031020000764841702c580002d510b0040102c012a5104100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 857702706 1250 857701456 857701483
    0x20c121605060420010e0a0e09010b04020705070f05030a05060615070b041506140901030221060a020c330402150c060a0e16090908091e0918 62
    0x10603038104620816003605440d0450111003040c039180c5004030a14001042d1801481c1c503541c4200340540c85060284d43c80038010300030744001407901c006501007071001703402c0040d59522403030301d51a251200c1c405010310390300a60090800034075000c0e0f8070320411184d400032406500a1120000854000202c164003c0c90984061f2110a1031f60300000b070500800000601c2e842c2d511040c071050015480984050106081080000d1503403452070f0320206030b40c001507507000f140002c010070151908182c02c880001200c0c0c440040740981804203414450110b803202e0100368007103180102080300308241d0081c0d81000398022004201d000c0301207241046116a58a81c4c40007200150443d110034481d02a4030390010202520344900314130083e202c0508807144080145052041c020f8100002003025500c0d0401856241060410303844070050b280c0144242d0356a10708100071851070702c8000c0c981d078000722800603c0c0755011028041058002c405800c00700542191007101d40c90707180110700130200c10003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 857703956 1250 857702706 857702743
    0x90f090c060807052b0e0a23150903160822030804090c0c14010b0108060a0b09060703090e0a06090b0405090309102319093006240801020c 61
    0xc440c0c050225031107941a10740c2520382040c0904203011b4001607000b0310a489003089803550135541d0359025401180440f0b41da42079006104206819582c480c0d0301d5080003005d001d407803420b01c070b010b600403c06010100c101c4070000002041c0241c40f8511040e034840d0080707005040c01d10740c510780f5080f4240c01b46014103103500313565a6030398041e40d0185c0303010328070070707500404001c207030304043c40c5203030080c5035510170035020440b180000f40f941d19100c40da00c010b44807950611800c2503000d40c1400800e0b00f0148044061080c1d82c0750100703100e0034032500c06200c0c00300d0810109400e414181c1e03a03000e403a00903403074901680c20007050003c484004000d440c44240b00342c40c0940807e0840c5422036010900c040b010f40c4d4403609403108140200d24100810702040f00050031040c80f42c41c1001150300c48203d1042c11609d5840e07100403a0161200e0402400494010210941030202911900200ca0b0641013007469020880c0703035610707022907240d640c60040c0b0042008508100c2580c0c0c070f8a850b03a181100250f038403070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 857705206 1250 857703956 857703997
    0x21503070203070b010f0815060a031205040f150e0d02011719050c030106020f060108071206240503160e0a02091f030f0f0b01170c04090f090c06080705 67
    0xa10800c1601d0f14942c000f4024403145d650f518694020340610f000b243c0f0580100384c0c80309056007151511900402c400380c61000301c18a19210110303c024200c2c24041044810800090091980903102003d001000500840038640700710107004084108441c90041203440c0c80040540e8112a803062015188030701c0b040340303940d800300102c900304200e0a407101161928062110780350402d005103041e140c0a07000ca414400310a102d407599400240f0131600107600003002440b600c02e14a1995040b540b086c0300204800c940010803491031780f41035007a10286a40008200241e2a08208051000181c015140603c90901d6a52101a6801855481c0c071540009030788843d52100c1455840c0d03c04a42c0000d4801c0c00040300040161142104010210b4102009025400e0300c130320603c810a10140c44442c8240032280010a510300010609489140e042c040000c81c41e156000381042150700000008100726a481d240403540d03115080b803420000b6200800c000d0682200455640003c4281541c0802 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 857706456 1250 857705206 857705221
    0x9150e01093b1b07020112020301060305061011101d01020c06010303090905010e040b060a1e050103061a07081602030102040b0c0607170703090201110d08070f0c021503 74
    0x52082d50007056815030060311041220baa101e415481c144030001d0281c00d620b40e008000c1d042d00c9090303407545861104030701105140036104000b00025481070414201880840c900c46c412a00240d1254000c04e45604c2003203440d280207520310b00042c0043c00c0071a075141500800030781e00c400400380b0380031071a9140707540e0144100e0241210034040e800002555607034503408001d034070313250280310860104103204c4020030a40204c0c0580c1d4141d5a610301c0081c003507901d50320395000005c006014207030013008030240810086082611038800e1030042041140303a615000005048940d15405845224845203402c446a0128030465425030f40200f1b002d605d030a5101d0360045c0285403400001c0d0f043d03100003000150b0681e1400905840440c8409840c496030f01c0340801d803084c9680410717000c0000b608c400081d1300d16011303502900010340185444071000800910151521500303840310f602050001d010850202c6c4d0204250b064903449107403035401070403150f003c0f48185940705200e6580c00004070009005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 857707706 1250 857706456 857706467
    0x10f0210021908070306030f020d030c050d230301120212071d01030c2304020c0102040b070b0609010512060c180904060b0310060302010914030a051c080709150e01 72
    0x314100c0d1581190780d10201106040340c88900d0a0100110b841e00e400904002c0c002e108020889403c0b0a003000b41e4581039007080602d998500046091125501e80e40c4089441084403086050b190b85445449200500400c085440c07281c901d80300e00c01c001c10042c0010805084880c41c0c466040c3c6029940740c9402070340504002184c0c00c00c454202d1071003403a03054800c0d9004c9003030407640101703d494281d5456481e01a203841c80016207803019001010b003801b80f8281980180400142c01d400103041586608000740349600188040d18034a80c0d40c0300b0300266203400340c17074140100403c031040c0c03110102202c106510740c440141103904030392020901009040a030041d46400c0c20b001400e800480c5060302c0c0ca000240380c017064890092085440341812076030640305080039681c050b19200e41c0285888050805010148079041c0c040c00b030f42c028040000c038104600e10703200040c9160145c0107030b40404003d00b03c241c020000000c01070403510070400441c40c0d01140350701240901d404445102c0520050b101c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 857708956 1250 857707706 857707723
    0xe0a0807141804030914121b010e030a03030b0405090f100c0203040e01031208091605120115060c1e02011403040204110c031b0a0201170411131d1506010f02 69
    0xc410b0020000c01c003c140e4440c1d03498042e500b4020701502c505006000340302d004008400c2110241d80514511409a10203032108071810b0742c1450030f5542c040400002c00e007010382003041140801d07151541d8940302c1c0781500a25a211215000a0190030240c40d941590345444140c2003180c40d5807001c190384c01c0c2d40300780708880240c803101c941d00301556541c0c032340200c5c1c120307018029000007001940803c81d0001c0225010001030054085000300d01d061408011404580c0d0b0340000c0c80e9942c801028041d10300b101d00c000010216a183e05000304144c2c10f2010ba40010584c000903100c4ca04550b0a0060703800104101c03c401403408059103a07520743c804070740202051010f03d41c01840c00f15804c0c2c100c3c00c000004096005540101050071407010b218250b80d242c01044c000d0100d03181404950340302116003441584103020701501c049201504012443d184000008940050703101e00c01018035aa012045941c40300341e01008241103641651800d2101c40b000d0040c5040000c488429440c40340300304880c21 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 857710206 1250 857708956 857708989
    0xc100f05030406061d01080142031a10090204030b0c070f0b0f1602070b04090222080c100215040602130302090f010504180c090b0a1805070e0a080714 66
    0x18111760b5000d01c1036000c48030900c104400c5600380840701c080410f84503c0b000c45070600351038035802c9104d026902c140070b042c1d006282004542d41d250010100c1c50116000344a0482100b2111090030702409000c141c100301d801441c41c507030041104100085c02201600e50001c03500b40d005417a040185030204c080600e08001500482100050050029070040102c0c0526900c841c0d94007180c08012041ea21002c3d28803888141e48011710082105104035001480034007492500301c481c121203444401c100444940022a85611050103402c0c81e09280c1d840b2614840c01c3d000030843c000140094032940c680041c00205074580100c2c03030340305e401f03060a400e4020f1130380100002110315004803140e43c40034092007000d204500b1700d46034190b03d07148540401c000c950001022000281030030202000380150240c0e2541152006000050301c0c06000304040c241e100c880c0300410203040c0200300401e0410581c8e042403140b0744860b0f080054450006441080718030030040d039030000e0340241c00240340b0380c200702009 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 857711456 1250 857710206 857710229
    0x12050d0902100e0108010504060e060d1b08030a030507210915090f120807050f03100b041d0c040f0317070b010f060f0815011805130e0c100f0503040606 67
    0x450119088250300c21521005e9880a001e40e985204000075101180706d130350b90300b41210b0302048650600d034600b41c003014014500034001e0031070292900e01030000d9610160860b0004551440c1d15640760140b1070300240c451801c0800056030809096074228050300300501e455a80030721804000e80310504c85000040c40004110030060f82c1480303410300c01c034840308482d03617500f00340d21044043c09a040c1a01a00041d40c0d480d0900c40002e00e07181c0e050344098251b1090f64942100052641c0c051001400035260381d008a07214000014000d4075003000150028201c1041484280050840d4841803012240c100c02545180d02c01c101446d00c4074484c0600c0076108100000020561450710070388402151358a0307441060000d41140e085030407281c10341320080048041e103002c541c5580301e0760300100b191403c7d070b20301d2110a61300d400040318060b15042071140e098440c9880c06220005018844c0881c5007500c040c000c2d504440002402c03840c04107481c0381409000b0021400b40051588510003910070034a40 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 857712706 1250 857711456 857711479
    0x609151906180906030323071e030305071d060a030b0424060206060a03060f0209031c0f0804020904061503060c09050a120f02010e0103290a0509010312050d0902 71
    0xa11500380c2e2001840341d03a03495500040d440c140e80c400d581c01c0340d805580340181042c11590400350340b1032440700030540346020310511003c1404500c080c45030100b5105241a0440145005416500014024002d000784440e41c3e040c0a50102d003083c420000468041e60f0701c038610142030b0000c142d0845075130b810600c1e2480d14080d5038844900042c0c80d0307401c0c980b5040140d559078012a690441192000d4000b011000204005602c40d0000318200c9900307034001d800e0400401c080703450411034050700c1082a420f0000004890b400082c07038990301d803051520304114130342500810310001010704002e1a1942c0d402c021100781d0f00f181103c401440d0f00810a1101e20141c1e000200035078101d00656203e0142d0302c00c00194034a820700060340865001c60761a036920101c2d001034565034011500c0e036060548501d9948110100544000003206581d40f20180402d4014180904c2d91601c0c4c001c80c1c022203c2c28014808075010080a400d010554075200b540d43c618101420050720030b08800a4028482202 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 857713956 1250 857712706 857712719
    0x1050909010e190c0b0a0e150d05190608010c1e0306050d03021501170a021909020706021902010b060301090c020c0a0308030712020910030f0b090f04060e0606091519 73
    0x442d6102680500f1100c4c2e603d640b140c841c40c11a1048084010206051240c10049801c007020712001f64422a501c07035052003c80c41a01054900c22200044019804113100800044502c035100150030300d40020030040007620406400050001500f10018011041403181507200360071150143c04003800a5000c12034030725000e0365510000840c407500305001c07400403907801b641e50076610040444070020261014180c092101e032980201011400c5120410f000c0358404050006004070362040c2c600590303030000442580c402c514090324610843e41000104c0071140d0b517150540741506c60806001605c1510361000b43c0c0760498401040707401121100c0c0c0002400b0030403002e14400c2146480e6070281c1c13145d1820321422480f894045552000041e0340a40005c0e1203540a5400749180380c000140120441000401c04074085414034a82c4c20036000b000f04100007800b50400c07a6540d070000346054100100080d1400ca0020180c61050001155002242d82d07060424114603e103906610110ba44034071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 857715206 1250 857713956 857713993
    0x4030b0910060b0d050f070c060f0f060f0302010305060a0e011703070f0b0411010824030f100e0d090b030103060207050102130e1008211b0304060503250801050909010e 74
    0x6050f1459450600013030321410006d81d40611400175075860183d015401e0f42c85400030700034042020310140c0d480c4449501d0305500d10a40000c1c010000c0420100352071480010107a075001440c03240543d210680400c5004501e84549064171000d4280491840c0d81070005440d42c043c0e18401b070041c58010703040c00f0600548511850203a07002d5035504035450259401942d0426055490815074020038401c880380040542c3c0d91010104000d0030740380e100b0301c440055450215201c0c41021030580e245402510b07079100700704503820048a0700300071a64030301d04600350382507003c1440050065a00040c0d50300c1040f10070350403140c040140030040034425440f4440c080800108032842ca13400c40502d0404540319a001500410b00c0112100080400c1d200d800c03041010381102c1d600005004400c80101e510540a002400180085954240d02d174a0f2410410800781e0110a400481051204003107003003580c840f100e00e0544030b081d9a10007060321586d69403401401d0488003000300707000c0c00d000304001c003c008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 857716456 1250 857715206 857715217
    0xf0f030a0b04110703020607050c2e05060312070210031107050106170a050c120c1002100b0f010c20030a2105120f0a0908030f071d030304030b0910060b 67
    0x242e80400240959400c444524440c1c4140036016078070090005081d00c0c4610010010b841c5400c00b83c9501c005142019115110038a10b000c09181c07414a9041c0713484903500c509a40498214018443c5d03c0383c0500a51892042e0070019004001c440e4543e00380c2030003500201039090189601907610001402c103075000b00201e0103011010001d544107000e03516000940000840c0d0070030041d14a840d00c010801410300090035601206004a450274180c69843c20100b030702201d02c07900070b0300b944c020240641048604101180f4800c840c45041204580d0344900c805c1d40182d400207920070110380c0d40d8015409800c00304030080d410310804402c0c00411004024417a100d8504035100110900d1101d41900c10380600c40c41b0204c2050618006600d041d101620250050390480000402041a840701c0c00c03d940100e604144c00700702e410511001d594810349206501190b4454000d44049000000e031316881540b001520100601002c101050b40902015001a600500802c150395441041019a4100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 857717706 1250 857716456 857716459
    0x309170102040f0308280e2101020f0d060b07030c140f070611061e040b1e041a0f0405190602091f12090309060f0309020d080309010f061a0f0f030a0b 66
    0x20100e1500300c0240030403410200000c82d07d8241c0d0309007515092060507101100070074110302d03c074101541000001e20007010b04002840711940d0709c0610355405002e60f8803a41c8008180d030300420494020903448904045003075800b41041030500040042c41d45000b1400300385040e40d01420600151203a0040c000c9014401f000c0182e40655031440054440144070f84800c0c441100080b00081c00240340c0c41140d90300502039a01e0182c00c2403000b201c0c03003801000300c804a4021610038988084501d140c150198010081d04a4821514042e40c405440303040744521903c038190345090703034070405c5519010360341c11701c00103400714648420f4114984985014013058401246401520b001000c4d610f0040340e90198064841e503980e107241c580c0071611024030000c0382003015030b180d50f4200141c0d034000001d4940e078000c0f103100c0e8803810480b940f20b0840700c420701001e0120381351000800000f40d1034601404500740b00c0411075214146d4022203104c034403d0065020301c0c0301d000000c0021003503450740081c003213000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 857718956 1250 857717706 857717737
    0x20301080106120812060312040e01030b01080307020a050405180102030406060e0c0f0412110d0f0b0c07031b0c170307060f0b090f04020a050d1103190309170102040f0308 75
    0x256409491039400f891000503013030610401c2000c0c48100c4003102c2c50b42010b8007800704c03a030a85101072000b501c1d03007150f000282e0b0742e03040c07078010410b20400c22007407405028484c005c0c603d0034041d42c0c0025640b00e6141b1616000c0e90f00d9a000803008103114200108507002d200081d90b50f41340520b4140c005100f603010383c8012108581c0850302d50582c4006070f40c01c065092580500d41400e18006161021101e00121400300c40c1d07079040c40c0191121003034130305114410f0500300ca5a00c080c1c600418a20307001405903011540501400c004250700640c0c02c0030100c503450a0f0f4401d01002e00b00791a0001c410b030002040c00882c0b04041c02c1511000000b000068041c9004200085003da4180700f0b44800c2b05240d0b51092644011a10204400aa03150001e1000301b0007080259183e011a02d07103980760406403486080e8160b44103050a060080e01c400c9484041c005c03281e288140e030042c0951529004043c892152541d9490802d04254119005814858101d0852a84d2032400464507405105178580195 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 857720206 1250 857718956 857718959
    0xf100e03030c0f0c03090a030503071104051605090f04020412030f020109150b0d12090302040f02030c07141518010e0c03060c090a0f0f050306070807020d0309051609020301080106 79
    0x10000c02502d000e181074503032051400425280036a02c6410405440000d4002080032a0240c0d41c0e14044000461251001e1500e581c2c0600388013a243d00203514140c001c43c1418108032480002c41d2345600111114102140c880361140702150904000741c088a0700107200150200d01034264075200368405120f907507104425a060802282600e0b14158018681940800b9500f264211604102c02201020740710740ba0391b411035241d2142100441c030ed02400f09400c00b1051003581810300803244e090f50b4801d401d5240d801d1000b00d602c0a80320b03c030000b6021103010903d20703000241c1800610078003800f40781020b4080c2060320045c0800040c11203800000d610303100c07140307440800c04100391205c01c000401400d082e5441d00d2009500e54491181b0030381c0200b8020000c01d1184030340340840040c10186079005d0602e23041109151802c40040e0004d020b100c0a4004c001d010b550002d11a125890a07107008901c0c5611840e120345800d41c041c0f004110114524004140c0c02026800ba50407503405034001e01405 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 857721456 1250 857720206 857720231
    0xc0e091b010c11031606051306180905070909021818101701110f040815160c0c09020d0509010c09030c120c0e1f06141c0e0f10 56
    0x2400d1821054041461080d951012400390350b0103428000004d0700703444c61179004510420031018960080c002040c004901d01000381f4000b109240605002d0800148030301c4844030742c20a00401e40318800b4426140d50000350003511502c60a801000701c09400d5403200030410020f003000540c0a010b0b0302551008046000b40458104090f01901503d0314003009107040840d0803880400808608444c1e41d22001e0240c1c41c4508076004100c00381c1401c0010303072500e042c865007504081e9040e5550303031003400701d4041c041c08004003503480005100c03074100302c8070100c01840c200e205510780f64440401d040c804200140c24800390b42185208595450081000c40c0c00e2180079915100240000389c114061100305110800482c1e450100c0140200c8d219a04181d0398540c00382201402c071140c1c0e0000030420a0004203110114880014200b1401c3c145c510800c850400f25250094580200070322140010140b001c603070070741c0700c051080340c3d840946881b0b02c0d91590541da10610084000042440c14240600d075 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 857722706 1250 857721456 857721493
    0x31e020a170c041a04052d15101d03010b04050a0f051006091403010209090c0a1409060f070f1218050d1e031b0b0403110d02100f02070c0e09 62
    0x4200355062002c40f400c03e20010b020003000d0090a00941c5200d1030318000c1d122014480043c0d1f80350354a455140d1910701900c3d03a03d1240714131681d490140c100c503480c400d011504406600306056841144c84c040201d6040081d001d00703820300388580c01501c3d260910841400d180c0209030204080c05051009880d0480207034000c3c6003c0c8034a90000c0c0c04604148014410182c000d600410014000340c28600410000307540b120b0180c83c1c0d40340b1030311300141321030002e0f400210b00c070080580501da190629103498040740461090040c1c481d103492001810318100090140c40d14462508100508204104049c0260103414071403982e416207112040001060300d41070340c1c9942d149502c00304215030703e0121491000c0000580c5003c074107200342c901d00215450760410100d12002e0240002080b00d060508000d4822008007040d21040c1d04a03c288104040d00010040c041000e800b02c00107a9024280e9408024050701030300800d1001c0340540018458100760901e80034801c82416515a50700014007a5031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 857723956 1250 857722706 857722721
    0x1e0e182502030d18020a0b0c0f07060c020d1a15040b0a0f030f05120c0d0f26101701020711030613060c03060308070c08070506040609031e020a170c04 66
    0x1a401049890207801070351308050078000d18030038103000c44096503002644154a03608100c0e1195400318034018441e004101c140300f500c4081d805845c1e1203081080041000907851006401600d00d2300040041000788000005c8095031040c0c002a03c2c2440c0c000817141f50f0081c8031840c89241021501056881c2c198001411180d41d0004a0482807450361901d0604d50f40c0d05007922140101410041181d010000070000c0703040d0f010150007040d41d0100040c00720444884050100203d0800c020300020544e82200c641c3c0c4500c107030131007017036582104e201c40030360594121b00300c4c0b4888000e0408504905402800f0228031901c002516030408806165698008942c0b00354084825001c0b107011a480d60f0051104402c50300d0301280250701c0b610f5000145d8070494003154200d0f044a4100302c202c0b07081c407807040900412100c0c03602d05031030b10703100406940f014000584001d4641c4800040b240d40301a0740405d150740a0000a1815070720142c040c0c03580417a074404d805900410050070802c0c82c2034400d000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 857725206 1250 857723956 857724031
    0x1819120f021908040f03050a0b1b0702042708040314150c0a1403011806090506010509010815180702010e071d060307030222060506030402011e0e18 65
    0x585052880100103503146482c01500c810404001c0030411665251001d00518024030041071a12800d1074030510140000301440d21489030701420645440d1000d01302c810300b58040300c0100307c1d09401042a104059020b0240c4620007004100000b0170002e60050002c903401181211412030900c00450780707030035411030304c0394080c2da85030001412010200c015200c00c8540346858040701024480780c11090380217030051170707806804000703a01010001e800381d04064000318005001e035081030000a030250140c038440d1703418000101c001540b0490a00c4906042100043c03c4044030007804201e81107810701554488e00550034003c202c0300494001416404907032003982c500c014403201000700c0c1d0100704098040c42d49401000400809641c402d00e100110003111001070811b1620025404c0464207154001802241c00b0700801c40585c2e000714104540c1c494400e04801c90701400802115250001c80440307510100c030f1071034001d03113040f50088940b01d5031404105503406203501d04804403000c0322070103a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 857726456 1250 857725206 857725213
    0x506040219080903070c12050d0e0312071415190b0d020409050c040509010621150b01050d020a08040b06190b0c0304081c0e090108070b031819120f02 66
    0x40c2820b8402d00c0e000780c2c45045541a6400c1c000c080d07030341e60400c002650040c50020000b010700000d1110502010a1099641c102100410020808a611550564031003141840086880c3d801c0c010340200c1264104010000e407420022140c0d41d812000c402035a03181580a28a280d80700820101c1c442c2c03038541c45000b0070b18032045440da401c100140c07040c00d0041f02c1034050152585070988860040038000c060000000c04e0641c02d1250200751656008000006102166500c0d00401c00e62030211000d01094003021550200c800010798640c4a052000d010042c0300003118841140d0240c402d50085100d01800040c030b44903081000f40003c0003204550221040150801042000350b00034020a4403090a0741d081550704c00069080c217610343c0051401802503903503202015845211100c00e0102152040025418140e00c80d0b07688496000c1c81031200000000b190b20409080b00120071040c4403030403149812003034000d0b001180030b61441101c000000e101c00400302800b400050307250500c154001c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 857727706 1250 857726456 857726497
    0x110f07030609140d0206070f0203040509011a221d0c0d24081c090602030708090a0314010c0f03110a080411030a05061014100f1116030605060402 64
    0x154001004420011200600190743c58088010700340030b041000710361900507150600c3c0001c4060060301c400400c010443d00100000d005c15641c11840d9415a0408242c84482d480c0c0b0003c841024802c40020003000c03207030001415010103c00d100501581c1d00c00200d01c1d481c120315100d42103001c03c16903481100f12418001d11400d940c6990048072040b155414400101d962035040000703546041e08035490540100f1541013120926000340c0e60303805034514000401c5454044001d440c0d0041e44d00080404000107041c40c940d03600c2851301c04c0551740100887d441d410752000598001d0585003100c0300072482c10f805842043d40030f4440c0740d086003050041a4075000d04d4800c1110100c000500441c1c0750012503000000741e8804000c10714006100b00e008084506001176400c2c103060155008510062070441c0030382480e20744980000781c1042c0c60402d00986420944260340302c8034200c110701882d00c22100c00b442c810390360842c400c2c101c90152004000741e441d000e05000c00d0380300b00c01c0d5202348110102c92 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 857728956 1250 857727706 857727713
    0xf030c02030c100e09090c0901051314070908160f05040b0307170109050f07080304060f1e05030a0c050708030720300307080105120f03070f03110f0703 67
    0x500100900c01030580b80316588100000d103600c03a031881803100141c00c103000401d03907051040c03180d50441c80301001400001981c00000b000742005000f51401142008001001c00c80c05400c242208040c00f000720500b454110f8000b048a007061047c54a58803540140b0a0841461403011013aa40810a10b551490500c0c1c144005840c3d44c030074680c0c140c404e01000040c0c150040d05000007000041d000400c0c801c2090800516007030211900801e5074210304801c1090410010171201107415030700300001c42102940341510103000034030f569000c030900344401c20000d80e0701000840c8034895818080241d404141d508607418016414028032100080005c0741182d40a41c440b6400b10401880c0c131269034040c809141d041507400302710500c612a07600d2501e80600034034000a81d03005200001113007545451130000306192410301c00c0034000d044903558000314920034401d000c441ca0042c0116075a50b5181d00c2c0101c1c4480c1e000800b036001405d10200107800030300109248a032443c0290050605030706685 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 857730206 1250 857728956 857728967
    0x3121d0601031407030804142103180f0303120a18050c0402030c1e040302100305070e040902130e070f060e01090e130b0a050f09010b0d0803101706090f06040f03 71
    0x941011134030904900000042d0610018005009030860ba6808141c20605005800d1245c0e800c0048080c10105880b03040d03e0000150f44011500c1030501c0000390391003003c501035030111076615070075010008099101908103003a9901910000504000c5159594041d5014401903680101542c1102c00070f034410b0b03e09078000d103401c6442e141c0e91925125030a0361601042c0000003682c18000c0010404005514211244922030b1144d400c06002e546441c4070f000b4120700c0070991a521541da551140c000759165144a19509600503038204980f07030b20011056a501c0c91449801c1e090400c0c0140414642e12030580c00031000030603150b200d040d03801c0008800482000515500c0d440340e4507100040031881c0303d1a070750b00411108000182c01c2c01c0421058114940080c58942282e0400300030405a8803800490091160420b0388079490340c80b60031a26040c02c1407070b440104000030703032a083d0880c40f101060050103130342c10b00121620000b46400c503a032075400484000d0500740d00103125001007800f80 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 857731456 1250 857730206 857730233
    0x804061701080f12250515060a0b070204050a14090304050a080a1208070509102601031110020a140606190b0405131b02060714040305030d0b0a090903121d060103 71
    0x140740e002041d44807071200c1034517052901d009440590008420404001c4122400754200005492245005052050740390081c49010402405141d9a00019412040c2540300c40c013440c1e5030b550800c1403401e00b050311660f25045801000c0c864030a1840001c0e0402000800310446a1301610640040d00507050645848070010280e00a119041000003041d998006140501c03c4140c2c490403c1107031280d40303401e008503d00c03031440c0900c6c80030030051001c100c2440f22061503040c100e605021203d1aa030040381007154245000380b42c0d0a49070b40302d042010340890f41c28402c100c140d03424541403903040c0340032001c80040c0c4286104841b08100030b202d00d003002c44080c461602d44501c08241c540078500c4000d0082108140389005802541c01d1004084d40300700c0d9240601c04007541c080c00e003421916040e84a1040a40405940395294034040880e150b007003c3e14000c5c07044030b40c1000444602d09020b07002403c08200c0501c141d1a0503034100201141c2c0c01a450b601049100924043c0c1c02c40da501c42e64900388 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 857732706 1250 857731456 857731477
    0x9151b1c030b0123030403090905131106090d0b0609060d08040504090c05180a110711041515050304210807120204080304180c050c0a0303050408070804061701080f12 73
    0xd622001104c4e0402503451500c641d4050926540c80c502810010121141600f1001c0414108030501c2211401d07c1c0225103c030340c02480189100307408000190280c425002c3e800d070441200e4410300c3c241300c4d00320b803801c1c0700700b00a4940650b07541c1c40c10304100f1000c2c000d8038000c01c0207000b88030900c0300f400c1c03036404880c05070310881000c56026142c0b00003900241c0c042c03901078486640941048580c0303a541c082c008200ca60a08c80b1420044c03540c0c0c0b40344040c041030101c2c0b8000c66036000030f44044510103117444020301ea01c4001c2180d24140000080481d40101c40560b00032400001c80e40080130b001130010b82c4103800d60340b054095101c100048404d6131448100200d0181c0a10010800391010320050005000031240f00d1401402c0c59441029034020041c140144882072108203050031021070f10415443d49450b0015955585140c8008140915800a010954003280200d06141c00454860304051042c2c0b1541007a079981d29107664030059418408210b81000c008001e186042c2c2c009002c030042c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 857733812 1106 857732706 857732717
    0x50702250303140f0f120708010e150d080a18050301090b060d05070305030a0305060f1225081203040201140901020a020607020609151b1c030b01 64
    0x19248006824007003845030030f40120607040f08583c440c0c002440f50300c1d1640361800010007260068050481035a02d40004070301664000c0002604079103806103c10341560f1002d010301c500369642c0d00307080c0e08000b0103900040002d01d104050106001304e83c0e03c082c0502061000e00103c1416603104500030b03450114407202085080101c250301c004140e901071034002c3c0c0351034214604201944007500d0303800702242c02041140d15030850341c0207400c100c40ca40b00c41d0200004004500d0b03054045007002e60321071030a0301040d1910300300400e440c001ca10b00d02c040302d580c1c440c481410642070100d0b00002c1d680000821045603008402800c0e00982e10b26920b08014010002030340e100030091020740b203040041003c1046544d0041203a00350240a0450400c0254252040d07425400ca080f00c00d0310741c644e0341c801d0701c0303100800600081d000c45505880741c07407104103c00581c01070050101035030402c01d = true := by decide +kernel

theorem cover : BRFrame.Cov 857553956 857733812 := by
  have h0 := BRFrame.cov_init 857553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 857553956 ≤ n) (h2 : n < 857733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
