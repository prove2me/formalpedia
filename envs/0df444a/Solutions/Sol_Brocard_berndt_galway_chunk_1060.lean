-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1060
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:03:44.614483+00:00
-- url     : https://prove2.me/submissions/85b9a852-ca67-46df-b660-608fd78ac20b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 190467625 ≤ n < 190647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 190468875 1250 190467625 190467631
    0x901050607030507170d2a0f02010914030a080a02070206040e040206070f05030a030b030102031014010c080d0615050702090402040209060f0f0406030e060709030b0c12270a0b04080f0f0c03120a060e 87
    0x240101c000c8c0d0800c01074401d521281c10b0740d4011105042e4140700346c140310f407643d1091081000042c040000b0924907001c503c02c6800e2254020442d80c0f0380792400c608a0f18014004000341d07030100d8180800300204080403900c18549110f00c0141d41d5409040034042c044460841e40913019030301c14410016103003a82d8048001b690302068801c501c1e40b09210049450342c03500b0400510001002c10072910074030407900008182e520962507240c0581c1140d00072603050140400c040c0d40310361a90b0128000d424a13500808600c100903013400d2034082d0b810045421035120044040d11074100180070002c05906100b05450710350780001a100c0c2d401c044000500c0c0b56803500000d040006180301040180c2d003d402110b132446201c0f00601c045190100a80380c0260001160b1654446a03001140d074400700811803a2000e5400050901e150f2910b4a0703001240c0c0010811514072002080641c0824140f880070700300f01902d05005640c1c840d2013140e00050550042c0401403e0f90400d101030200b2950f04002c564 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 190470125 1250 190468875 190468877
    0x11b090504110415080a1407023004031a060111070b090409120c110108090d05160203010905060a0e151305011d070f0b03060901050607030507170d2a 66
    0x2000441802900010f1080b60311182000703038000107442e41680c000320031500c910300198041249401141121000340b004854860040c0c0007a101483c183d409882c040d90580c01e226110388108010341d920401680c890307001500c02906aa03107580f41d5584281030140d00c80820318003d0204002010420b43d00c011500404502d40d0002c00c015a2946a030341c04403851b50b4028070660140032072950045d0400d1003485080c2d030b20041e500c00c401519401612507501401d03003d030041550b006144012241da03040194002e5808540302c0f078413000740c1e03024000e0b410139600900c081c0110b42840c0303a00008a4809491901054019120b1501c01102c6400c403d540301c0c60450400381c0300c2041303240c8140100303060008007070f003840c0e00302e01d04c60003203000a2540141ca0101d400c2c02c1809403078032010310f018041220f05070380c4259140e006100310704005010b0409681b103410301a090a101340e40304410070200140c4841644d0000c95507048018880c010040d6230a50004011140c44444800c51041041440d8100c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 190471375 1250 190470125 190470131
    0x80c0a03030f1407020607080a0201051b0316051605060906010906080a1712010303030b1912080c0715030c0906110601030212070306090b040201020706080702060a0c03060801050a060305011b090504 87
    0x1207000703603c010403142859070060032a56140d015182c894402d4014250300130042d03203444009202414081c0e0102c44034641c030740542d4110380d548d44a0b400001c0d1a06444420000b0500000c040c0701010309554070342500c104003400b0709291002c0e20b6454070344164841003545081c100304025148002c101550500c1e0018881c00c0702010a03036a240316840f0b0b0304550b903072050820000000345941540180d1301c00380229025802580503540407146103110740104205024101040400074048600528060300e2480940315202d0707a91100f4500022801c6c1c6400c0440d4646006000456009503048054001360078103000e207200040b4a190b94900c14040280900d0403500c4080e6610410010780f4000c55001600384107003102440c00e200d400c1000c0da001c9015100d8a00c02180381405400428441c01e0243e00400555482c00f0701c0c1800b800ea403030318440c10705584480204032000d0a004180c811070503801d001c07a40030b04c2c40c5006421914424844110b8021001d01a13851230752007920170045800841d408 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 190472625 1250 190471375 190471397
    0x60e010c02120a030201050703020403020f0f010c29010e0f0a050a0b030f0304030c1502031801030213031208090607141b030a0816080c1603110d09080c0a03030f 71
    0x40e503045004500203984038440d0550b24103521000035080000601c6030740207011301c0d26105425405d81c012804000e502050801c0c1203609411f000300508800201403510200344007003500d4200c8942d00d88240301040c07406d00c1d1604860440301c84045401411008a81c03901c13890000c2c1d402800300e802903c03002549481e040414801c800d9508407812104000b0240d4202e00001b00c102aa6548a844100c035481280e0000142044003120946142c00064014500e000380007480001c5c038094464003035042c9135092124080d034140c03440d920009140300741003201c0014400d00c8003410092004000d240154011020000303204d901440f03041e865134526a880d03407107000796000d1914046401c07442c08558400800d60701049540041310500407802812204441c02e0320590803206000c04440c45244040204240054054000110460b490003031500c0c00c162510305081600704005201d2080000d2840c04050010782014040b0607945030088804064661641d40c2c0680301c0341d400452201881040c2e02d003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 190473875 1250 190472625 190472627
    0xc0c071e050420360a060c080f03041514040507060c0c1503020715020705060c1b01053105060105040903050c010203040c03141912140d02030a0b0d0804060e01 70
    0x42210b481c901142c05540340c2c42c0100b0b4490303124810200e10042d4001c65031028451080121030130401500c0900108415418541c041d50b013840750300403c595451041009401c80b00e1080301075801144a0b02c034041c0321003042d5410400740d1b40e201d100544d2044044083c88001140029003000306d40c0941080c400201d420b061202100015522505803a0218141240e401e0391540c02030860030311605800b000c840001d01504200e000d00750b0020441c3e401417000c40c180e4400f1101400c141114480e41c0e515000b928510f40f403d48005848104e00e04508070f100c50344007400025101142e4040042104010900b078032020b645060622640d4050307a03440c8200402d01d4840c004803006107015500075035a0b4142071400002c2d107000b51200361980101c440d40030410b81c0700400c1c04184e0003105401c0e07035000d10071504d0701101c140c15500c801050050351900720380c03618641030242402420100c40142c83c0d18045a20710f0075a0b9140d9840c0b0300c135000000034800003581c00c200f036409a0b81c181c0f8014640c40c6013100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 190475125 1250 190473875 190473911
    0x150201020f07061b0801030c090b0f0409030819090b0408030c07050703030203030f070f02030901030b0a05041503020f060313030804050703020607080a0e0a080c1203070602030c0c071e0504 83
    0xa950740100040302428001160040c4074649190b900c0a01c00400001e01125403610a020007040400c8040e010000c0e01c506801140c240d120080c07204040c102690f002a04032101c0b2281180801c0704502080f00348a011084e081c003101c1300380014440d140172685c89408100c1d004000805140010001c5008007100d40261044103a0110071500e900b034483c140031f0361f03942046803030420821002d070000b0105031181c1041c0e00c0360b0180c1d80095040840c0c010045d4060510f04406580005e1003250000c1d65698034058001c2200741461480c08950450050000780d01541c05040e009190070002e1004502c0c11030a002c400c9501460408460740b19403400c0790600310a54006544010040740b4174052000d41002410a44819200c2d2882400c1c08400c1c06542c050a2041c0c0c6101e401c5010a41d82d02d0a1151040391444c1c042c00a4910f0102a5641c18080360401d07124400c0701d450200b41c01451400820840c0040e000000c0841d01c2a00110540701d11100c0500400e80966100c800d082031501c540c003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 190476375 1250 190475125 190475137
    0x1815040806040b1b0a09171005071d03010203060109051e061206010305070c050c0d0c15020c090f01050a031e2a14031b0d0804030c140108090715020102 67
    0x1068407100e08040c208120042010f0302e18410003020081c0401074201140c080303603010070498a451416500d030000007400c1e00035030a01102d081c010b0303402c42c000f251080e205070f502c50042d41e19010b100030502100000c00d403d15100140c000ea1041050240681e00f000d40c1d802104c404451038070340c1c109100500300c9945080214141c00c44008070348804540601064a442600b0a9030300308010307a81c0b050b003101c003000780390b401070f010390410080701500e4144015441519402440094042543e511000100d00740c41c0e0119001a00910000c8032a464001e808580090040141c00d41550514000503051031191000a000d10007a42401040500c8440c081d048690000c82c810040c001201200b015100911903400c8000800040446c2002c003040c1520441c100103002000703060210150030038026035100304607070b001988400550000f151280180301446c801d80380d0f0300d141c600c0c10000011300c21800204506028801c3c003003003800b41000612070115181c03004414601400500f00360700901c42d02c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 190477625 1250 190476375 190476389
    0xf120307090905070e090906040f08130f030506011a030f13060b04051504050106050c0303060d02040605060708190905180c0d02070503040f06050f030109241701060506181504 77
    0x83c02c0141007074005000340c580c01030950701d216840e40d54041c82e41d1a104125070081441d10191400800b003100c0d007000d070120310782c02c1c00f000c0f8540e0b40712071408144080d1070b4411030312603200b1001030100e250070315210f081400055503c1402d50a11441c1380c54527000c02400340c00c030070b410031200800f0710055402c99003441e040a4010029420441000c01a1080500107030b4082d0307003040b000045070f900c41c00c1190300d1550080051820741e240e5800300002407205c1c2d170b02668070503100c40003ca007070756612008221542c03181e03141603503030035482183c5c40340041285680780502150001c1040035840c2c4108501d404064840052540e65617000300c1e849500487c140d01d40118400315141c01009000801481030b1040700d00101c0e911a40d607e0122090300c03584c500010000020b10040185030015000051001d0100e40150001c4880d0000d18890340c400c1d501000701d9189001000071800702c01c0c82014081c0400317494042c501140300205050a4245d1915a8014640d005110b0440304800c000d070344c090152 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 190478875 1250 190477625 190477631
    0xa0c0b0a0902030d05160201050702060c060108030c0c030a02010903060c1106100503070905010f0b13051302121003052d0a050f0d0c02030a0209090307150507110f1203070909 77
    0x5044440d00a041124049000b40b0841e500242010b00800c01d950344c115211031000c00900440d401165035400c051004c0b40c01034001d01500c07071601e40c14032426010f0210b00c0001c580340c10006040b145000b0708040c0150007600326001d0540541d82c0407510105a0f80c000c0c00c00301380001003d008451030f0a00c2043e1403030070f0081c00c5c240810607084c01100c600b101c40490846110301d0312a084002182d8080c03040c2e241076192907904000042e01c0c9000741100d0300b42030f000d2004455403100440c096210942180e4400c65002402c82000c40001007071075080030085448040341403d50b42c420b5902c1c000601c003400500c03040001300440078191460307580e00c0c1c1010003c1e00d45031521803900c3e03581c1d00182e01c84019103002d08039070a107400e8401c0c040328000070b80007030003050442c1d0640c083c0500c00b18040c05084140c003040101c1404151000031010910413140000250340c6400340b03004080801c2c4401c103440c590001d101c1607192007070001c5d2080c0803002d014103680e81c0352151b0000f070b85e58080a034400c0c040142 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 190480125 1250 190478875 190478881
    0x1060c050a140d14031909020d050601031a01080a020d020103020c01060810050106080603120a180915080105070c0f0b07021507090501021608060411210a0203010f051b0a0c0b 77
    0x501143c8032007080103035180c401c00340348150342c110769a00045620002c01c80300d10f01010110701d10f0340c120b07820071030003e031199025529035259941028002d0f002074540b48802c61201c07442511900c0f6a9006000e40401342096482e1a070018031000c07117140e0041e04064011440d085100030a40c4000c0080c06034204441c800c46c030b80d0510b074025010034482d94003c120743c030001403100c1c00d0215450381c50031101d40c0c0203442c04440c05410340b1254401c00c0380b02706260801001289014003031040240b00301c0e00381e000141c0646013403601400d540c0010300e02010822007021800c0060005098424a80d5100e107103203100d07680d101c004924210724200b0b0382202c542040c05000c45260001015001d075034083c0c0c00c1c2e4060392038184203060204d0041c4220700d80c940c8100000303804034500c1c01e1000316000005018074140b6011a01070700d0381c1c07040b0309034114154001601d0b12085140034030510240301c4d0419414000382c41e1002c00312401082d07504464442090000d90b103400c5030711600c00000c00507030000a84000342 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 190481375 1250 190480125 190480163
    0x322090608010504021c0f080a0203040b03091e010b0d080304060f020307080109140705070b0702010b06040f08100e0312071101050a0c0206060108010e0a020f130b03190207020901060c050a 83
    0x100c143c1341a800341458070b4001601945909030100c0460b0040700103184101d841d6541001540080b10780021400f050002054101900c0c1c003c60007480a00001c10b9041080c00c0407000e40b250034000c500e40d503803426805040b59260040300c00c540f203401106a680301d580d5414008041c120404040c1d0305a0b10001c02c103c1966002105541038a860340402c1104d40c6040c03082c028040015241e03400070803001e000100c0062002444603522038800e20010030315506e0342e404540d150304142c1001d0900429094103200c8007001308081d00c20201c03000401d00c00941d00340410b644a00c60f812203030418a001c6400208414000c02c80860340507400c074000c00c0030b0310306a841f200c01400c2402c0c136100103010f003e000c50080c1d0310039a17107241079520016580050707444a144a00c000e500190411a100c0c03020300c01030081d01a090074000c01015001d901c9560cd1418040500d0540d0400220f41803180c0305100c3e40026845502505046d41d225007045080c585090a003039161004440d4000c1c0815003031488000d80e4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 190482625 1250 190481375 190481381
    0x120901021501171c0c020f01030e10061707050d0201030203040314070c0905570a03180b010510140d06050913030c02090628060f080603032209060801 66
    0x503209044e1154400e6443c07540805130305540c0d044001076020318078040175183c11400d4030640ca005040c0010280d0545003220700304907a21160f203806d9561088100100d880c440c031104c450500701c50192010500304000914041c0c1490400ba04141d03020001408042c001c0e001003d100b0011043e460700d40c1c1744da280c1045904010b003c0c1101040c1001c1c0403c000344280680003c084001001c0103060b500400070b8208184120740c1c0d81404100c00e145054640c4540d1202600c0300282d1600c0c10350780700101c1c00f0180603900005800e0008003000903c030808901c02c40551070540720300702c4500506100c086401c464644c201e0001074154900021400700c460030f5580700340201c44003a40c140070700e0341d80e02a103e080c400d40c104000d4082034080203400014030f00031509a6000600900255041c07041c410a524900e0103082665080c40e8a484240142038010130b00c8103549800b807030314642d00c2c500000031070b859000b02c40040030304030000d584010f50041c8a54046015000c0143c1c1004440c1c1c1d108605406 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 190483875 1250 190482625 190482659
    0x61a0d03051207051e0a0e0f0f040c0207120b04060b01020f030703110c1201140f091e0322061704030914030a02121b12030f0a02010204030605040c0303030e070602120901021501 78
    0x8a541c07e0308485490501401004410800404d031504a90b8907a0a000150103030306c2d0b4035411401494000305101c07112031200e860488c010840010780e450039140620440303600d8014207040d54002c1c0e40310780c02000000210b4402c0c9915161003942b5107881d085403072500b10300c207441d2079200220301407082c40d484055100c81c402c0441e0901c5a504c0391541e41c0e01c5003007031100341e600082c5600b0600348600c85144080c000040c41040c542140d181410300714013500001e612448965521000d90700800016505c0000c0031206181807000c9203c1e0b04081c0c4d070203080c0f00c1c054821680401112241c90500782d40900c5008401500a0400f4030050b100e4003010341c44215500b84200c0758440301100030748900f802003082c0c08881076a002549411001e0043c0c14054201c82c01540440d03400b00004400900c9038011039014034440d2900b08200790440c60090191000c4182d940a641d012650030412258005003480c3c0e80c140512417240d540b507180300100d0820200a480c01c61082040c400064242c0d601d102002c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 190485125 1250 190483875 190483877
    0x1270902070b1b160c030b100509011e150c05010f0222051e060403240b0f011413030602040e01082b0516050109061a0d03051207051e0a 60
    0x549641d07490b07000c440054440710f4a0038560402d200315424200e2010700100558011921103800550b0380c1e480752038100045943c000703c110086070810a0b42488a04280506210050002d11003581019014005403a1044a0f1320754038140340340e51020b001d05081c01100713411400911024500741c10304c9010354451410b1500c082c6c100c0010880310708100482c102511401000030301c4c00300c007a500c0e2700380d02c240b00720388240c1c0242c040000200090308400b15144e5101804a00c3c00c0550340d111403802200c0000520034041c2a29032000782e40c6030307131180f01e03086604018507800c0e84803010342d41c1640380a4800c1d0030081ca00c510000700494010800704081b81221000f000700d4101d9010300300410b010702c141c6070241001c41500204104024080d0010740514104444900ca95000c0c0d9140c80e82900c24840c0151500d039920018a824200703514a00c00101d40c080d02d00400c002442c0d64020682d102c2d0410700803001501001240006110390100c84160200ca0b8116044c00c6115540c040b1551214644c28 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 190486375 1250 190485125 190485143
    0x11130314030901020312070318110a0b03041101030905240f0a06030812040303020f0703030507080108070501020a020409050c150a021c050315010c02360112020127090207 75
    0x10252000000300c940c00b1070306a0145040a028103036040c20540e000e009034040c191208080b0f1004003400205c41c10003401041d02d10001400c650607c0100c0b0341d190402c242000003042000301089610312000104d640a01c0c00042c41d070000c1c1415400c040e1080a05081003418120380900400484491409140c840c0c0300700c001602c034200100c007100e80030f22004040c01c1d0244425800112443c1485a005000741000742c504201005c25800da0f0340001c20440110307035601c00b0700c809264803421140c0507006100003410024140b00020350303180d00f0240000e1085860f0103071401049000c1c0502d042107580a8640100203c01507040b03a140d8100540d00c4005114440b818100da010030300700219216100d488071803542d12035440d0b5581141c00340812505001c0590700d5280140c5075844070000d48044d1600d16034411100424110540345800c45a809000172040103103c0c04654980c00342e0b699509007002e40d0040f034a001c80c0010b0f601c1c00b2825000300c81c1c40705000030b507500300f640081c40e945225480711 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 190487625 1250 190486375 190486403
    0x30228140111010e07120812010e07020d020a0213020a03020405100c0b0702060f2e0e010513091502131d0a0c03051005041a03030d02071b120209040303111303 70
    0x1500302d802902103c0c04c81d901c408030822442404801086505000b038a101c0e2600c8618650040749045c281d216118010b250400c10100c1075040c0800d1603031484610103000c130040940c0000d6290800300844c141600d90019a841c00306005e503048400601d0003401106440d0304403c800f40410050103070581d00d00c5c084c200021052031000c24868030a02516000314501c2d02d4602a1001d044000c4c00c01420819410b480652009844035030540240f0108895403281d41c14801401210010803a00882c1e80e400d100200300080c050110204030b0b20b11343c520058603141d40741c6079104a902a5840501960b0403490410003100d01041c0040c401d82c12610280f06c800d0300c0c1c607002c0701140c2003207880500038109500140a01d01e0603822050001143d048030140d1448107c00107400e5078000005008116800110f40c4108003113032110b040c01040000b00042c030b0901c2c112443d4600290390000a2040450300300050800d8086c0e0312482d100f00c400c0d211644c40e00682c2c00c0c1c02e5030001d000d00003564819112511 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 190488875 1250 190487625 190487657
    0x306090f0504021804080d021b060f011401020703110409081308150c19110102042c0a0b030703081c02160b0f01080a06051b07030519020601050a0302281401 69
    0x1003540915801400c45c7e180505d011007820003504400360f01c80c10b816241162803003d450400c2180c0c01010524803401040d45014060302e68a8844c000c880e040d508148000c1021406031016200303485401d03200450007251300e02e4070104a1050811303a24500400e00b001080032000020245586102c00d0600d51302c540b544002c2c511503004a14504050303090400000c0c80b100d10403180d0740c00a8090f04005030030503480d80041a0940a460148900b050419090300706694500145c1074000c0c92461041203d40e0024003c242c48820900000c0c042d5000003d42c80404a40081103c42c0314003080011500d030941005003105018401405031501c840c00070100d2500d8515034076280c100c4606038003e00410b45566100000303448010702c2d4941125103800002c0007104103400600c040352095850a544401079000090003a000c0900300b0110b501c03c2c001401030351134001e1200700b5030390100d50188000e02c1000c08a004800c0c491092824402070540010340340c4c00d0840201c05842c02601c941d0807940c00151 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 190490125 1250 190488875 190488919
    0x30307031806230d0609021b01110a02062a2a0d02060612150703090209070c050304030f1e12030b060313020d0203030f0f09040605061e09010306090f050402 69
    0x84020406100c03140f000e41002102c001c260446001001050b500d41d1440c40404907080701340380391008945034043c0d8211110030700c10921007460068007641400c101c020025a58a0018001d18030050100a2000003944600c0300c0030280c44168a0340741e65040024400c400e00b40c80900582a00d4643c88803561843c1000c0341710250800a6030090000c2e42d45d0204110300e200040000107018041d00c8001d940829040c40704d103101c0d00c104d85020034900c0c45c501c11301c014000010110403c10000c264000c002420101c06c50341100d07004540400d03041c01c03030306221401c4441c17895440307061340450703480c0030402400b4511180e002020352801c00c02c15090100b841003a1204a0b111224483c8a000400042c1381038204020000e001504983c2041d03500f425a043c591b1015a40702c2e840f005c040f44501d4a031a2a014240c0544015901241850030031800307821031404034084a60031901c0070482503c5a40f0030b1b4006802481d4002082c45203405400c1c1c010000d00c002c4e01d0503409500013180d44064000d10300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 190491375 1250 190490125 190490147
    0x1a07020c0111150708130c08060f1303090302060d0608160302152803090206070f020f01031a01030c020c1305010f0803070c03060b0a03080301090519050603070311030a02030307031806 81
    0x41800c0d450340c5915040b0740e9164003d103441c071b80c800e0138039840002c81c0e020a00c94025010710f034010107140c03d00c0032540302e40c0c2d200108800c000d61100304003180001d906c03150138800c99506986079512000d40306821006001180c01585440c82840c0d514440c4454030040345040301c0c001d03582400c5d040c1100907005a540b04000c0031820040300030448100000d2546980d5841c0c11503454000340651056001a640d41e0200805860002100c0b000000b0351800c440100c25040c000d00303041201c083c100c04030302800d01d000080c5906065482d050030500c00e001307203d50007a101009040e050021680d062000007000c1c04c0c0a601018003e1b0403003c07030600c07800001c4940061304040c848454515603500c8802800300101d00a0b0490b42d00c21380000000c1100340514040d102703007600802c8501c0c0503c2c01c407420080030703c00022a14100300074019980c07004900c41083d246c100b0030540e407002042d40441d19204240f01e0080d050701c40003c901092540c0f168855910b44091211200015030303444089905482c04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 190492625 1250 190491375 190491403
    0x11040204210623040302010608070f0e060d0501231e010e0a18060617010902090a0b040e030a08060907020a2102010b1e030705090f01030605041a07020c0111 69
    0x14030000d0001415190703030711054490070011483c40d1460a01c0710b0014002d51941d9640e501540c1808201a020b00a4802902402000340141880d00e020865601c546229244520803c1d1011405503122280c42d8070b40715030000d0003440844805143d46090900354083d1403104440d4401149000406403030300984000040120a03180c0d080440101d44a800500200e005c281c0d81e001d0740303079215041400c20040034068100042c0c0c4034030f45480c444644250b15020650b81e40351505620042e60341000b40b5805c00446d180c00203803d182c0f80c010034000d0481c0c00424600e84030105030852201d500c6621203102d02015521702c40380d606d9100061780d8034182e0308002420204480300c14449152202c02c40242c190441c030010412443d0400030544031080d01c1a1007402942c0071034402c06604040140c60000e1006644520b500d1402108041c10400706001c002d20058a400c0031400f070258070680c000a100c070044c50741c9440d04281c1b501070344e120404a0b9482c04100d5141d1219601280400c0d00880d00a038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 190493875 1250 190492625 190492649
    0x906050d0503070b060319080a14120a0c03020403050105150301200307050a09180c0e030f0705040c02120f040503070504180f02130f060905090a0f1707080c060411040204 75
    0x140d944c2e4009528024000c503014030401490b104030b0003052510b204024024030740565140c1400344001c0001c1c00303080c4c8074a000d520400605094485401e0381d01c3d400341c04a20000740315242e80104801a22613580302505560802080c0b20581c58600c0340801081d60440081100c01c0c80360024056691314000c091074824402d10000d2422809040280100c0d181803510342d50264035079401c08480c0041407003408000d1356981102502d140c100c0303c503c221920031002401819020a0303419502c0546009440c095030b201d075614001c25008200740190085c0d40b541c02900e40b410750b82030444640291040300d209101e01100011141064401c1e11000303440c0c054454070366981501c03030003110405000c0498000c600300301544040381091269400c1d4000f882c41c04506e041c542000035080c0c54010300030603183e80020110a000503420b07031030159543d074400705078041c801c52080c0e0550140941800500602c0300050200010840071460511a031b11a104203907108050100b40b104074000c901030307441403405c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 190495125 1250 190493875 190493887
    0x9090b01030b040f02090705031807050a031415070f030b040203060109090b13050c040305010b03032b0b150a0314010b161515031a04080301120f0b0906010906050d0503 74
    0x40d40071440e42d0301501841824130500c0155000c0340d04414212074040003d9030200a0002c0c1c810b00280c6408444005c200500900c0c2c2070400050901c901440000d2030040d1450758100104020300c8800c1004121040d41c12051a250001501d011303d14901d4000091038203110454a24240c42500d00803401a500d900160f81000300080007001040c2d20158000024001400840c695020fa184030b150480d886a03203451540c0741050070b4424042c041c0741319800c18003492150385442d00c41c220141550080002070461a049076800070303c40840240d80010b007850000d00310410080040c5440045540c040141c0369100b07a030341210240a020782031034003504209003000304250130060400716000744210701d003d106030142d1071b003110b0310200606070000799100c040040c0617180c06000308403180101003403400d25140c2d80b0078a443c80140606015000380241940c28003a04610b080c1ca811b030320492500250400b103a0555544009100305502c0070304000012846050840300741c841c43c0d501c5401581001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 190496375 1250 190495125 190495133
    0x906031f091e03180f1a0c0c10050405120303010b070209040c122103090507050111100609050f090d020d0c11060d1a01020307020612070c080f0a0e090402031504240209040609090b0103 81
    0x47e0111140300c0745807150421f420055a541240b10820410035155140d03568601418010300d180c601c000c018640d00280010000007802e4012a10b515a048581c643c580c0d85610f4050350012030764000c407012403000114030082020840440311000c805645081007100351131011005d95103c160000d0051708420400c200550145003024082d6403c0015036031000e2a201030242219001e601c8201c1a540b00c0007480b925080880105420410b6103000c2c0c540c40d41d0460780695105607810000c4200a0070180000500c074050441d401d1a44d0010025561f1307030001c8408102a1041c4544007849060f181240041580000b0855201c903a01408542c1810340529007003030901c034000e104500380501100d055002482d004000d015031a20071642c2920ad40e82c1c9100205010190700c40240039002003028080565800070ba0501e04a00710707108002d040d9942c0c5081041440026102d00384250000d0054a403075a103130300a041c24040030741e010170926a942c01148192580308001034201c0740c0403c0103001003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 190497625 1250 190496375 190496377
    0x15040515040c09181a03060c1207020304030215070204050603030301230406170706080f0c030411010c0b0709061205041109070201140a0603020906031f091e03180f1a 73
    0x201070f040031100999130b2020b4090050240d001c0c3c110702c81d84e84441c1da0b20400010a4805005000c1e4000c010b01e15102c040e920007840b8840e04642c03004007501c00110118400c004842c0655400780008089070800b2001c0f400d50f400220003248540e00f06000100c942c00c00109480c12207034111031140c642c030f400700080c02c10b080110320207903040b80d110900865402840740d00d440c0900d1041004100007403030628000e003220030140c01102c1c04040003003481038107658035007900e402c25040640020700e12403020060300c0e60a01100c0040c61900038100704102c2e07540055160049503403e48503000044520710109044420441d4010040d0148109000207400c010701c03907039404003560000182c0000a8900e50004090480d116403a5540703500b000d00460031301c2e407082600319105500500008a1500002d0030b40807140b4402d1103403d590b640500c041c402d10344150400c0e2407421000700301030201410024001c01100030b0103a54500e24540020700c1016130402c50084503180c071405002142c40c0400c0803d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 190498875 1250 190497625 190497641
    0x90c1902011103040309030b0c03071e0219080c01060e0c04030f0c090e030307111501050907030609050f0106021504120807270611010903080406090222051504051504 73
    0x4542d03841c1c1d24a50414041c000441c0203a00030f4448600c020714520741a00f50ba40c00609180c0006024401d010345980c011200c0486120110758414000040280c101e03d4560007024201c066540f4007409810302ca4a00010702c66142c100c3c009001042c0c42d001d600000700020b450800001c07004000800200301c404240311038440c410b86104014580cac41d03840350705541c000320320322145400000c00d225509402c2031042040e5140b0f0710141030010215070f0702c0045902c0501c2501c0c041c443c01e2000401c00c600c00d5000310050700f1120020450303403c280c150007100301004d00401b400f41c0300b000e00421840203808403080c030580c0d100c5c9100200e41e200103c01c82d0404005442c407401d10040040c4494060f1460341500d100002d400c468030296860f00b5402045081d804040b0310103030740741c1600d41010950000f091580507030060303404034082080e8030101c2c802104080d00f200d07101d03502002054110f60f15400c800e02480f001005200601d1610b03040000701c810550700e440701c541c480d03221001e86090035003205207 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 190500125 1250 190498875 190498877
    0xc02060d0b06030705040e0f0f0406050a0f0e1605040209100c11060a0809070605190507140d0207180606300509031315020d140f12040b06090c19 64
    0x1d2041403100420401c0c3c2080d035201c804560040780500034480719400e042e030301c50000340080e03002d820700100404140d0000751014088603100d0000400d0088281c0044019010603038007002014079140d01c9030f88a4445040c01d84129005010000785d82c6441d00135100e600c20000c00307002c01302ca8105005d6031a480308510487e680030001100d104141d0300c0b00040c00c01c1c008280ca50014038a00740d4565410f22007140c00040c10b000050154119080403080d04845464190602598544490a2203403200b810000460440c0c0b1602d5060910075501003605030441d10701058201c1840401940750040d52082e006500014a2001c3d1b0100101040c0f40c003000d5440001342510083c1d4800200301c07041c0d0344116041d08140d4000943d807107401081580d0f05004003007251000c011400480d0b0025241c0d415214640c0030401c044032045c6c0d2580b842d1048911410702500e8039551100071548021050b02d08a80aa50100e040c00001e910350800c20703d280e10030480a6521450300f081a0030110f200c40c0c259401c18 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 190501375 1250 190500125 190500131
    0x303040812090c2713030f0c030509090a0e0601060c030c02010305060d020405250801120809060c010509010c030606030c020d05130512010b0301051b040b0307031107030906020f010c0c02060d 84
    0x2500e03240c10703aa103003180070000c0c4901c064164180c408420200c0181529005d16000c070b1030440442e074070200c04a0300000601c1c121461008a003400c49144c007845012952065248040c4190403c8951001c0f070b95a00103416105039030703640c0c207003511070b0b80b20a20302034042520903425100562090340820361240004081c9400182641c000c0340071501c0848061030034420603a810112002c252402420000ea2860300c51190360404e0f0000000e01d242c0c01005000d03100109508102d5540c650954000c56240030080040745040e01c230703c0d4040c01c070b85014603000c03c0c500400850741c0c0c6d2080c010800710b5012a00100400504258108c032160302c41c01c030817440ca64510801241603511026481c106070075030000414900119000c16003102d001034401f21001c0c00489036801020b81c80800c1d501191280003440f600c941ea80c43c02035000d0242c0e00350511f16400001540c07402c00d03400c401000240d44180d800c4580000c800d6050608030f4440300140d0300801c50000301135006180c03c0e0010f00d00c0d040521804 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 190502625 1250 190501375 190501393
    0x1017060607120306060801051203071121160b040605030f0a060801020c0102250209010b0901020709061d070509030a0f0c09021b102a030b0a0f090e030304081209 71
    0xb510500028840d6500003035141c0e032040104c5a030080c60702d40501000c0301c09080120144001543d80d200c0e06100400e400121440c0138019512014052120841c6008011409091180c05910f8041c01c00010340f03460480c83c00402c0c1503010100361030a442c041d0f1a142d1035600c41d10000c1c4d1144800801c2200300944800003c20005d00c20b00242c90000b0700350b0009600d4640404040c00c40750409224506440c1c03081d500b0ba8096954001c20504490b16404250380d1351200100407401c110046c1c22040c00c3d14104400040d040041c1d035243c20700f000c4000c00040079030711522003c540f588030b000f500990640c00321070040c3c04103940400f00031201d44140610b00060340e480c04407800383d03003200200e02440791240c8440c09855100b8002d00101c9075025104006051031005c00982c1c400116800000203030843c141501890301030b500101003400010580700da569640d1301d1101380c0d0412402424845804d010a52611400000035280510b5204503000d041c4a0740c22200800d403280185a51840d10901440c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 190503875 1250 190502625 190502633
    0x60103180c060f12150b0a030e06010b0406021e1b0315013f0809040f060b0309010e06090304050d1e0507150203030714030a06090e010501060e1017060607 68
    0x944010107041c0c030f6103101a208410043c0a2203d4a600f803110581066a00b0b013031a5128036114080d250428066500c0d0010018100c1c0200400d04185a00b44103850010400354118005001114615400c0329820800002070703415090001c49040c2440d4004060100c00403d03412400700045400380855848101c84000d0045003802a4001041d89122181c0340ca5050f84500c000100d0200c0a4842113200740480607005d58509100405171884401103035002c5140d80300e0b0000c1140140505051001d07603141e204403059684152840e144542c40c043d416041107401107000d03841103100341b018509083c40d29080c40704c1c40404402c21107616044010b400800c0391640380008107a0302450040c10000e00b081c0000681a500a8018041d541b0610802c00c8181d8041c1514aa489800c0c4c0000d0310b03a1542c10851016000b2500188005420950f00910128055200e1412a00c1c0f5aa6050500d10f080080c440030306048151030000031040c0080e44a000d010000c034980010018200a152840d503441d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 190505125 1250 190503875 190503893
    0x10b0c01020c160e010501170a05060111030c0d082404020702010201020408070807031709031c02010f0c0c020a1a070305030411060316090807050102031209010617070305101406010318 81
    0x70781c0b054420320703420f040c0304040e00444007134007404080c02d0510408004c06603103c0103800042904441c13075115400200c07281d00c10f8500c440c1001524081b0307915954245201507c48881c2031010000948440c0041c081c00c005215040c580d010211501c0f001790b194605000c0a54031445040e4150f6400308400500d03440104290310042100201400d90a0f04500d0103142154006030600a0050b060060744020b075030100d451881c1845800c0361944d2003251150aa01400c241240c18064038a0802411a500c1e00988a201c1040c4220b554544094680800002c0808003801030a4040014041c400009000300011074106c0d0150410640b0074562000203a9640e00440360185140807005459112a030041041c402820018010308a00b50810000130340d6809001c100302101031380a00450a02c20080d8007584c05410301a0905035002e07103200000381e840350302d481700312064441d41c42e001c4000b2910b8842c00394090340b0a8540e40c0c050311118011405400a1160500074144410301980000ca20003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 190506375 1250 190505125 190505143
    0x14010b0303092d1f0e010216060807110f010b1305010609030305030406110307050c190213020a0e03030409060503060109050f130203010b04091202190b0a0c0c05030708090a1d010b0c01020c 83
    0x4240ca0900d41306000030720a07050f00d000d150640d403000e0340c0c0d107807003891700541d420907902c851a020742c09d60b542c150100c507490441c140e04213040c0224807000c0290301041d0800c2c0c210761800d4800c0d10ba070301014640c2c041181c1c0c00340f0a480000d6107892081c030003e44504015500f150041d58042225007500c80c1c40c92803035100ba155840441d10005051211001c02c0c041e4640341031025280c501103210303940114226408030000d4004403507000401078003040c0260b41041c1036480c06400c0f00e4445880e50724020040825003d000c0c407a00c1645c1c00060703146824068a84100c904206262068035541002c121000807064101d905540301d142166040c0c50b288030b411503040c0181501d01d00c5802d4000041d08003802c6440980c902e440810409020910300c2d581140c2003000c1407000103082c4541c40049503842c0181400038428080011040240040e050241460300411900c2211881d0307940000e810190030707204d2a140419421004101c14208580507200c41c1d400c20740007614080482c2c0c100c7d030412400b4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 190507625 1250 190506375 190506409
    0x150c0f0301080a020f030a1205160b150a08071811090904060504060605030a1110170a050417030621031303050106090e0d051602030709050414010b0303092d 69
    0xc400030f074150320746040408400c00d0b00760040d001002650b00e84407501140100a40140580041c1e40050046549e200b8203000350442681c10260603d4078940d1f180240080203e031151004940c0030400100104640041f03480b0100103041301e6480c60071400180200105034041c910041c055101245ca50069040c4524800c070340000b120b00c2d1914184040384c0c542c1d041039000781d1050705100c0c00198165042144207400f129400110801c010040756242442e401d074030070b403003085002e21a0900e00e6410460096225030741d50750b81084850140103140c00101c1e01290701c208400701e0905010f05155600c1580556982921314229884d611001c2608844d40100c501d03030b40d070fa00c041048401a201e00648145031801900c5050180b4000810a008481c041c0403848010340e1444215901040b603080240190702c0700340300510b0300d424135103c0e00208440c1441c45508050100360b10f0b25000c41124800400108003c2c201c00c60301e01c1c011214145c5500300c246005542a000300e081c2e0741c000941c4214400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 190508875 1250 190507625 190507633
    0x2070b0129090303040501050d0603050a1203060503123c12060405010b07330e0f1606031d012a0e0a060c03030902090106020d0906050c150c0f030108 66
    0x1880c40d24804420740003049035540078000d840807a640441102d0480d402440c0c00394544c9800180d5000420042c7d10041c2148030355207102040080206080100e451300740c400b0802280c1c0c807001d00d0b8a03007400a40e807069954080018103440810000342034080c0711403406680c5000240703040034400c1100c01c600400740e07040101d12140721340c20040155a01c0714007550b083c02035501d04984001c0d5030141042c0180301121600c0040500d03c008070122002c0314546815000122200c0e070500c00500324840c664040e4000e2126860442a001501000300b000002851769207605e007100480003050038403c108815030020112012200c0d0034050380310543c594565035030804c0d62640070756580c01d49100e140c005112030340902010554450802c035084465034204000300440f2854201c00404d030002c40250702c003183c400003041c0d084c4d000603800c0040181ea1a0041c030035440352802d803850f001d03802e030000c201d074000c103080c0c051801c2044400c1c0d04128269051030904139824884200794201360001d00e0103501c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 190510125 1250 190508875 190508909
    0x100e102f040e0103020409021c030e09060d020102060609060d1416050904170901120213140103020708070f140f01270f020d020f04020406020c04050f060315070302070b01 75
    0x1118104001a0340000218542850681c0040b109141440301038440e0350f48a03c0c810564540052081080303071408110f503c580818078001d0700c2683c20a619034018010389000505a003401c2c1400141c83d50140c0042826581d18400c00086200060405402c1018084120005003c10310b006d5a0611944007401c0068411145d0310300084040c1d2105110311714a00600000c6114910031901070861076400c180e540030480c00607203800348401c00402ca003a10005980102034a81c812203c00e440600e041158022855401103003079010b441800b801c040d00c104440c600196401004224a510402c00040b50310300720030059060541440200c1c01c140d440b0310340881844604c0e854404410211006103080711400d48400100c10858a4020300500b012240f502c190350f140c04c180601c016006100f95500c54880b90001d4031820f40140f00341c05a802c3c000840e01d54084251218800c20340900103049040304c1019000c00007a0203455842410380c00c0010b08003290910380c00a01a000321600380d0301d024 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 190511375 1250 190510125 190510181
    0x120f120705011a15031b1612020102030717130204091a0601020319030203091204080a050c0d021f050903060103030c11030d080a0906020405041b120203010602100e10 73
    0x186070240182030a00c5402200d0409540d4007540c0d00b0740d04e60014419469507606400c2000c070040001c40001d8072500441c1c042d1120609488543d10705100f00c5000c1205908001d06909170300041e2400d00c040303a4903240d600b070740000303000199030700234110b02c00d007080c068071a00403c0071100c0342102a01c100a08440c00c1c240f41c03620a9002e50040c000f80700440c945100c25542212a440740804902015000004101048000c2280d074485030031200b0140d80da9940c98917915911890705a045031103001d83c01f218422854820600c0d110190041c2540d040300043c2403407a107290501c000740c50180441801000c50700c1d01c0030440c440c060340c0704c0c4d1690411490603060020703021446e000742c42d00c1382d805901002e4404d584180f036540c20078880c0202103140880d07807a04c0ca0181c06140c022a420603e42880448a401d0150a55845c210075441d00f503207225040c0108800d074803090143c0c40140e8842030107446e515001d58130070200c4481d174109461401c030690041c0002e8445c1b40c0b20b000704c01101024103000036 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 190512625 1250 190511375 190511381
    0x6030206160b090f10021803060a0e10060506040504051b0c0a0c0e1501031d010e010c0e1801050f040902030313230102070510020a151a01110c120f12070501 69
    0x4800e80300c0041c016110b103071140654417640c01c5542e12100b0380125410440c001195012079801c1e400809851a0385400c810560040807100c62101070791040c1007203140440340c184140010345d03201515051a00342001d0034000500300c0174007850007101c0041120341c0129417030380140c0205241c0e040505000801e0f400c001821800c1c0d604560341d1003064006101d615254035900c2c4c50000c1080c00c0202d8410301c1d81402d5042e1991009855003903500b40b401c0b20700090410b5100c50800040c075120b6a030300920f00f0082c003480d12a00601000904040c40040c0020300e0500c004158019009001090386101d40e40482c1c25504001001422617085000500140303000012090a8030190540d800b51411f070b107070000759204994030945015180e070328960441140b00f4007a0705141a04800c0d00c100303050180500b00014062014160000c0c51307100f0252a00e58807807100100d0030054440104070048021003086035603056908400c2e030500c03e52075940d0200d102070003400c0c020300808009944031062400c0035825 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 190513875 1250 190512625 190512631
    0x312030c08190c020c030d0806090915040813150f0f030e030d0e030f0a091701110306040c0e03070b090a0b030408250506040803010611060601050405010f020106030206160b 76
    0x3030056500c100034004001da034208001d000c02180114003a0003c9a090342064180c0814a415000f07486103040c12035000754a8074020b40013503801d00c2c5070783d03141c640302c13902c0304c0000c4079960700c1240383c00211300070501c003401404107007a440c2125007441d90b955078141e0030004810b65010100700d098614500268001c1d07071040b003c83c40c42c101400941c3c42c9110860b00c0303110300c941c2002455aa01ea80c10301c0c0d158200300352800e03502c00901e026503e01540f00042e2040c0413600ca1201a40301c1c00740103c1c10b109042c02201803d80e00503143c0ca0640d1556010040a0904068140e04201085042c6c0d145594104800300041400c040481d5840203d03900b0b01a003804940c2122a0a50040052000040b040b078110f4403241360341640882d080c1a40b50314441e00e04820301c0080c10b144600c4041c007003400702c001c000714101c0340180c036441c012113194283c0580398801100d039240858402d0004109a501941403d005010300b8400015001e0b106d80c00143c5942010300000700d0111800c220074108681099040e030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 190515125 1250 190513875 190513877
    0x5151303030f110f07030203040306051e0705130303081e01140f031c05090d0b01030c090e0a050c01350103020102010c09080c0d2306070905100903080a0203040f0312030c 75
    0x6082c083d90080c22030300c40c0341081501503800050320300a052092003610051644428207101c3e40c10180703140c0d104940c10314180d40344000c400d40415000c42c054022110408414110300783e40a2943e00c00707445104c0000c050300c0d0b01c0031344000d90030030040c0c5024a90780680403200143c4680000141403140c19650b81d01c40f0b50183d03208480d0802c08541c00301581120b014203152169654058030040f03800d0728000c1c400140101c03490300c008403c120300a60072809940c4030302d100300400a9584290303507a800c0c2d400b50140c1981c0000c500d1444039480303240005588960955000f1080d8000c110211a5141d5000784044520140006108640e03080c0103030f142d002e0040c60000e41c0d65042540907512a408c61180520403142261184100a6400e00050b0107010109281c48540a001c3c030740b60321620304589020020b068403c0101d83c51408003980c1d125068a0f07078800d04039504540d5550015030110320354005511050100059050503014000c01441c0704440c4e0b544440075a034009000d88203100c000320 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 190516375 1250 190515125 190515131
    0x50909210403080f0a09120b0f0a0203010b030a2d09020a05100816120504050303061807050a080408040f08070e0106140a0f0909020301061d0307080a030c05151303030f 74
    0x400f260700c1030150b62058141c2480035591781d030100b0065410b40601d43c40b00b070400c4c0d0070400950034041c211003403030b00ca1003200e65040c1c80780d929840a8001c03403000740100306800b0001d202260380300300340f07901400d0507920154076402030301d018403020b01005428003000c80c0c1c00d513110200c0701d0860a010388080002c08064402042c840c0100030b0180c0305d50001414129182d54030300c000b5011500c95642c1c10000e40780b02d03c0402c041e00305414400d17284e03407007204c40c103010308408a608400c5a41101d5842e220b040165100b50a10b512908200e50f000c1d40a0003c0d41c90460511010405541440b001c03402801d990004008240c6004039006c00080140c0c0000d0522880e40701408860f4211700c00c80d940c441280c136011030364425034142030328904101d8220050302ca1000c0004500250040c05c5007410303804500503119582c06a0b0b08156440002d40078400071a044001c80b000068020702c40c11000601c02d40656240140d645c4242c1303031a40c0f0484400c2ca00300c0c50f100440003810380503c03522082c802961014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 190517625 1250 190516375 190516379
    0x10209040f020304021c0305090607030e041b08070f0504080d020607020f010c02060415021b01050601140705030a08060a080111031e0f0402220f14130c09150509092104 74
    0x83c441300c640c040b10b280c00910b00928141018800c0080380d80c54000100b201e42c4404403410002d0020300c070dc1085600451600180c8000b0010600b080181404282d40300800c55071408012581c600840d80c030711060120500002c524684244218174084140c1d031700601607407a0090f0020b140008140c082c441d540d141421320400a0380c08101c0d81d50180d0000b8042e0407140012050710001e05c103040015400810007107203004002c0042d08440d0203490260b0300d03030780c84000d1804e5180e2540320b0030000a145e41d04c104028000340e401007042643c4001c0082180c02c245984444417800d403600000c0344000494004104080e054840e0030350078090003e40d504603507918195901c40c2c03901c0b03401b400183c800ca1a141000c3c103521b89030501203050110ba0442031040210201035840034041d0034901050024944002524074190f0030007102078039410a002852061800104100410984141d80f140a02c0102c011501d40c40e801e413128041c0d00114001c1042510381c00d0f2404627403c1000e00d18508000803c41 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 190518875 1250 190517625 190517629
    0x70305190b0c19030c050c1e0d02031305040b060f07030201020a180b1e040f121703060a060c050c100503100e0c0d02030a060806040308070201060806060a15030b04020408010209040f02030402 84
    0x80d1100340c044c140040c03001100d150940d5940200c80c3c2c0d490852148242c544201070741800c9058940092100300c902080c1d41c810709070f03142d006460b0801c42818904904002910f42a0000e2004002c041c10f0203160101c525487d0314284e100760002d0703016079000504021802c2d0303c45252580e900d4001084540c2504084a4443c540f1600c001e0032401031001158516180c031003011140101001c2e40e40854150740d850b0f140075440300780b540507200842e84d040040031048600d01240d124075030081841803403d080c00307810380740b00704684c105441900c903580300040907484202b05245240000d483e110740724035054840003042292600450480c207600d2091245100e00e202c25240480e041420142c0c503a03648801d201d00400fa507a124030000c1c0f0403407090106068104a8003030080000b075009005003511a1006943c801081c0c07092604a558001c040055240243d01c0c0c902c1400a03143c0410751a050030300103005d90704290000c40159600048030020f034a4540300307003070f02000c005206606510701600 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 190520125 1250 190518875 190518907
    0x60405190f0605040b03150a05090108010c110304120b07120c050d0e0106030c05280303050310060c0b01060c060209090c0a030b01030915050606070f0f020108010b07050601031202070305190b0c 85
    0x71140065440c2c0d04000c0c003190746c86403103c00127030002030300d1040550380d0782e80355602900e400a410804202000ea604140d14804070803101540c191194606042c003041d626203000751002400e0004210784445040c20358611401500340c03012582d644d654542c408074500f00201c8041a0550780c250f0303d0319004100150141d0303045800c4030421203044d501d042c1405014003500364030145030214240940008020981c01a0285004e0101200300094554490600391039500c000c2a0181581d440130004000d200d02ca2900850854881c1e4005030030050640d001c104500c0d01a95282d01c00000812600d07aa19454422100108801d00c2c042c0003001c00c075190100391351f08148a030281c0310303140c800041c00d6448079030803500803650021240800701d0280c184020290b81c2d006040380090a45000010390080c900d06580300d06421201414850340303540e4621640d000125107d17020b6014030340c0000301158040c405101c1c003054041084080145a00e01000001401041c0d941d240200348900f07650f041800c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 190521375 1250 190520125 190520131
    0x70e0907020714030322170a0308040204021c0e0a020405070315030609030e03070b0c150402100c0611120906101d060402070b1303020f0606060d050402060405190f0605040b03 77
    0x840040c3d180485100460b0551243c03440340071840c2d11b424541e0f40549803440d2000c0848074584107141c90070000c02d00054440c0c41019001d0300042c0c820005c6000747c941a401880034810320070b400d009207810f84c1e4803241640c10303a445a460580002c9851003c5d420203000701a80004581323010007541c0f581c0440b2445926030350002034800303a502d07094481054000d04a03208403071002011259850360700c1c0030326045a072110310b03568446e0150402c0050180707507442c2250301484d40181007001c00d0070ba40100f2140c003510000240d51041d102c0710f5003000d043c038002c0280444c103140f074001495071910340c0d4054a4550043e0001c142c24840c0340341000041151034a081d05211108281c10b01501c0da00b0004000c3e008100001d001140320b1020721010707042d40c51084485912a8081e14481024980301a4644500316070307083c1c2117001004401c410b141982c2c0300640c801d10040c8040c3c2083d48a0000c01c0417400a000b0510b840300b001101484608112030605005007494035200b8a000d00740007031285640006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 190522625 1250 190521375 190521389
    0x60c0806030c0120030d051003060c0512070806040b06030a0207141203070c11030319031b05040b0703170906010302030f03030405120a0201020705010903031b050304120804021305010e070e09070207 87
    0x780c07010f6140c040c01402161b2400031086014410341c1060036030400301810501c01207030444e01e0040f580407505e00400968850150404200700301e030b070310184207461082d4000d10055200c1e41c0c62260b8a0b841e9500300180d4001c4406040050b115506803918018900c40b0000c0b5032920f601c01e035502d6003949940011641d00c00c01c1c5140c807992903401807801c1054812003039800d030340c03601010403000c2c81e40202708211145482c4594007880030354110280e402150440f11061400540300300002e224005c90341d4000e014080c800c1c13a01824242c0d50ac0404d155001094640a0154100000400035490200040c80d0440c40d1040074514600f01030743e9682d0380c4e01428202e200303008404501c1c0b0480e41d00030f5054440c00c0390000d0082c000955070b481c00400034964020414105000e014890628501c2541a01e02c9107a004554050443c1a001c05698034400200101c3c0d00c4020700c0380149102e8207030301031076000b00151000c815060170031400c054070703c6000301905801502c4000401840755030000d0414103d8031a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 190523875 1250 190522625 190522667
    0x301090807061d060f0406140925030f08030109150e0f07030b061605100618020310050d05060105150a0f08150a03050f0c0102010204060519030b04050103060c0806030c01 75
    0x941078040c3c00700c00741c10704486590302451081112503808200410b1040317104901c00c12110b000d030351041117860001e9800c41410f900281c0032052802090040000c08000d11100c52402503580ea1484480882c03004125044500440100007640f042d02807104010000303520b02800505208168803144070042c1000390b501c0d11100401c0106001340d108968003038014050583c0c3d56480c42104091255486080303506100388000c89401480520551044d218103000428540c10f54010792000303900081e00c406000440908006965a610042d00c4446407141b00507005c503624010420207000b888650320124040100a01da14141d40304804d9040540700c4c0c204221213881b07ca03280c40c0040352504072281c000f802c05401200703000001030118400700d451022290a0209000120f082c2c0c0224443d101c081501440310b0000540607442c0318a6081251800203a40840700e00082d090b40e5080c2e005450b85036554000d40d00440c1e01540030369000006038000c1c401c803112040024800c0c4554140300708880c2c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 190525125 1250 190523875 190523891
    0x5120408120f1201080105150f0d03080c09030a030921020f19080f010906061d07050a020a020a090203071214060d0807060e07060813080d0209030102160c060e030109080706 76
    0x140e4015100c1044184024410f103684400030300d402001c00392001c12900420011003246403601440f0740100b150302814840341946d075658150740d81078001d03001182889007404001080d84081101e0600d5501958a11141c54034017000c2541000a418040d203030030681e4860345001d40c94580745201c1101c02991110650030001d8299580d001003500001039901404410948803201500045c0b04603004001c108101640c074003a103500580c100c0540a8520303410350000d06040c0c00380c0043c096641550040da214401c0f190300082c1051155048841c05036408000d1000ca50b603c2600716088016004003008848603801b52180360b0a8000c20b001d108821990388041002010000e85505980c03240e0306001079020701c02d003603032a041c00c2d0007400009a4060009816081504c066501c0e032038002151504d40002800f4031401b030b600c80c4159a030150340800542410304240028445403a0050140003859418400018000443c90050504c83d80c100026080400c200604076a4810f41c00000052080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 190526375 1250 190525125 190525147
    0x6080c090d080d15090c020102091f0903080f0d060b13030b0a0906110307030c18140a0b1b0601080d1b0606030812041205070b070c02031c0302070512040812 69
    0x4400c0000c43d030202810300b4825042c00040c000c0303002c00c2e100400b00501c43e03064800022400c074000c05a02c21b0f03012405907004161901104422003081d003030340c86d0a0307010302e0712922140c401d42d01481801500780300003d445480c403021445150050f00420743c61034034010314000721001d505031500001d400c041142001c1401c000703041e408040c0d8568480810700c00c514003900c420040740c000310b410302c02003800d0621442e8503510446408040c0310418048000d041d0600500824420001e480e0b00c1d007000c801c1002240e20021b1070003409501047c545400005c425071b918041c03d226041e0301506039070b07100c1e080c1007005075086030b0300c8684003007001c0300240000802d084c110060180ba40c00901440800074100b900f842300c2001036440790380541d24406d8030342003284003124944aa0740010b00500101008a134005214200d4032502c3d034002011603c04049415404520780c41c400c0c50040429030010700703401040300501c0b0035408983c01001160a140c9842e501645404201090892030701c0700003a942400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 190527625 1250 190526375 190526377
    0x1080709150914030106030206030412051c0b0406140d03030f1808121308030411040905030a0e030601120819090801060e07180f05060703050c0f061006080c090d08 72
    0x3048400c0d80c00d407001c079000c070010b464406076008500b1100422403140c0346030304050081c6030450707a015085030310b19a51921102440d000f072040c220100f1a04100d9a01e046c070b846d00038004541c28103200000c0e1000c11008020450340c5a5000d00661520720081240640d01c40765916a078a80504020032a42c0804410350002c0c4a0710f101a411854601031030b800303100004000d415914160191445c15454250002007035000c860303001000500704000003000200c0b90305800703840300c201502c0842c001216039685030854008507090000201c0b190303200c582c00c1c40c08000c5240108000b03104001400f40d507403113901702440741e411a0111000c2c400411840c0a11595510004180d100000c2154580f0f0313508595402009580f007000140c05d0080461404000e02c180c04121040e140706140014076003014410250010310f02a018001e0030f000d1030750001d50601c2540c072249540d0000c0c0c015441c1c130000082c940031441d08540c080090400030010442c8004c0b0031100318040c115225031510580f85020500c03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 190528875 1250 190527625 190527629
    0x909030313170409020309101b052b0b010201060b0c060609040212070602100f0b011d0a0314071517010b0306130c030b040c0e0901030204051b030103080d2901080709 73
    0x61900240024050300d141d17011798003d140010a40d02141085000142230780c0c401c0c0782d282030030503206004810140c020b5009041040001e40900c0c1c800d035945423658005201340b101505c0302034650a03c6103040d030303087c0729010250154019a038100680380103035503030b9040c00811003400b03102c00c00082029991240444200380c100c038012104170310745032400291908100400c12520a0030140345081c0e01081c0d0051020101060355440b40f02c0050324032240400441604007604001c0c031440100c04110480e175042200404400100308141c07800c101000c0503820404000c0800c8a14403c0c052000c503d100282c2c111400c220940d03860b61200320010301030300c1111003003140091900242e141c006806420045c460103088600300f0121203024400c1d81c1d100b0f13244040d40c0d0700c8004c540041c23005203000e40c04103030098a48400200c0e603484c0002081560750080e0000e44045801241c030408841c0d150040c03101002a2036103810004062030516036071070078003548044c14013140500081d00030b4821b00c00900 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 190530125 1250 190528875 190528913
    0x30201110708090a0b03090d030c110f070e0c0c1209270f0f010f0e130b040b19090b0106050c0c030d050a1205070f0c110904110f0909030313 62
    0x41d5550003032520a6940c3e00450380b050007182c0e00203002680b401c0d06802e4a00c01c40843c030113030107452048030045009000c03980784c030760511905443d0903030032041c10801807400c078802100a01d0018204410b030688108028050b4200b0042000b52481d5a0b201141040369a1034031580a612891110001b03103034950344401200c018120301c05d0000c4101503203101036010300c03504a40c2d041e0a440b01d038010200000300b405080f5182c0c000c038408000d17140038800a95840b58001030080d0080c030301669005007800d41034406031140b0005400780500703e50340708030708403400c0c01c1840c040190509a170f488481c018014803850041c41070100725000c0c003c1c028070811508100007429203014104008ac05005a0001702074a000140548010144010203100c3c06004107117644807600c950600040468001c1d1401c5130407151050b185655011300c3c0c40e8902c00034003840c4241031003140c001d0808148119060080c180750304c40c0c0c0141c81442281a804411241c01044100c0c2c58010b442c81030400b010102c0b840f01c03041d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 190531375 1250 190530125 190530127
    0x20609061e0c120a1a01021b1c0b04050f0d090e07080402010c05010c020303090d0e030a140304080601061e0305040c14040e030c010f0524061305060d0c0905030d09090903020111 78
    0x1c52040d045d813140c0404c49982c0d0b105049040c00c1c5004903981c01008448a448003900206001103203000a031180a035004c1240380002c091b060b90328440c22408c107540880300350b8030040481143e00700a01c0403615a4503185001e0040d50b180c1400a182c0702c4001c2d08070382c24040700302c002c00e05692145551000c2d15400400a1060001c00c9030300030751b0781e13100700c5602e4401e009403458140c2952080d0306540340002c0081c020008940c0300c2e01c070f01e141c00101703442c0b0a6052004020004115005000150007842d25490f040c1805500500394140c120b2240e03902c404240c0b500007008001060b03145d0850568594a001d00c0880d04010040740040980d03500110103840049000d05050805400c01c0b05201c062040a200e0f907195054080d403034088050050083d2903487d40c244085041100207841d0002c12940368000880d40c98001c84c030030350300030b500301c0c596551590400316032143c1050711940103242c02c0d0b0040c0407007003013100c0040c1400d071140a040441d9440341d00e507c0606200b50054104a00f6801c905 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 190532625 1250 190531375 190531381
    0x42102180703061409011a091305101a1204032106170a02030601090203091006062309060403110f100507060f1406060307091a0406020609061e0c12 65
    0x1444800d011500c00c00000e06041d804105804c2e40301400040300c2000e0500070130f5909042c8511100e42c1e100d0ba08603074445003072011006569814040340d03000c09072a180042c95043c4583c407071b111002c40b500704c10203140700c0500100a100d244411581068014000c1c8402da840b1807408071089000088010592034217444500c0c2c60300156409401140ca000034840108411800181c2d00c4040000001e54540c0000004106c10940b6400840d8010f05a5054800c108845042642115407035042240011450038410004203c015000d00e042c080c041145424a458040081c1c43c2c0e2280b0301004107054006403007140c05440c2c490051807212001414a614a0742580c00140182c001080940740c007414030301c61120000c0e80d4410030304141000e419030318042d501d4005010b51a0300191425003008500c120000b0070020303080b041c01800302404442903643d0300e40341000b45041005015458240c002c101071107035841d0120074032450101c034094107807540d5962620000300e40c02152059803484901c8020 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 190533875 1250 190532625 190532659
    0xa09020d0506270a0c15050708040b03010501020d020109050d0e01030207050111070c060c050703080f090405010e0a150b030403230a0c0204050903070c0918140d030c020f03042102 79
    0x4424100f1404103007880c0c8000002001c10f995503030310a00684040c10712201030058224001b48a600c00005042043c9000c03507c0d901d40015601a90005800e04808401440700750ba061221154240c2144028000b8541d15100c0b10f854541c041205010b20a042005000a9000381c0595107441e4000000300000d000c400d0b03803030b020f5a02c80881164503e850031000708000b40190304482855402c82e009020702400c0d036584040c03942c032240c2600c0039041c061059001360ba840b0300600f406090503096103070b03c41c2002408035042d0707490201500c407810500c0c401804461000d80c1540c1e84146c25140040004010142c40d243d96038400741d0414034143d0010340d201035146c00440316402140b099408001c1581c40580c10b42d16030296190052400c0c100241c100440070f802d411515080a01d0301003540d81c0901941c0b00c00c6051300344460140d403604007401001c140381e01441002c0c4081d81500240c198407003c5200e50f900c030f10a40c0903004020030b56140303089c0d01d0113007808800013695014083daa500008800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 190535125 1250 190533875 190533901
    0x1406221505180708060d020d02060d0b0a051c110109170c1f05070201030e0304080d110601050901030308180a08070501020d110c030922020f030405010507050306090a09020d0506 78
    0x80a0264540509940d01902d405002911a150756540e82e81c1988481c03081245004440400343e0740700d5655440c03040582e4455004280c120100400000c611485505001c1240740aa01851295080c0900302c00c0860301403c641d81100d178040c085007071201c0c810300140e0b0030302a0340d0401c042d240c0d10545040d990400006107000c03100c1d07048030810401802c01c0c85d1044000c10f9014880c0000d00103001c0440154040d03040030b542449101c1c183e90420b40c580003481d14288040c281000004c2d000c540c071001c900f44c01d02040703000d000e09645204043d0f05580740a0030001d0040c00c0d41031104030301441c007540388005000a03540c8030340c0b201800703503201c0960401c54040c0d004440244c41d55407034a025001400384100c1110301c0404c1c2034018508100088041040700c0380c115400160340301d0a940d0038400a801ca10080410440c5903409645a0409050860842c2c1e8001c00fa04244038081003802143e5079035810307407a481a6241030100d0700c40709901c0411600c2100060041c0540704203000d201e00c500da084 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 190536375 1250 190535125 190535129
    0x130225050606040c1403040311100b12010c02070b0c07030c0311120105090d030905010b03030415080705130b0f09090403021014010e07181e031514062215 68
    0x290803503100b5141c40c000c110444e04e0003103071a0301165288106040011000014551060081c14121070290001c000181401101c000904041ea520b001101151900920720034884160324000c025903405040042d5980700c4c580034402c419200490304444c552000c115650140d50b001e01440400e07680c0380b8240c0000303540c4c03a004910400707510400e4003412005108061040050600402480d81c0300380c020350041401580980da59522800d03550429241040100000e208280c2107244a200d80f00000344035240c017811060411400700101d00c050803040c0714130b500f9120888070141d510100502c3c205024420391602e2900b2445543c10401416008203000f00340020002c0180401d991020b508201e450007406901100012940841c000511400c90074100714502c40004050720b864590708550201c0095007984040c0007210280200580e6040003103140c0340d80001440170038038121030750f44441002802c1c00d0107000c1c2c585159001140041c0044400320304100e00300304c1c1807409101810501e43d14 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 190537625 1250 190536375 190536383
    0x5062511040e060402030a061104051f270b0a05070b0709050a090e06040f050c090103050d140703050a0c0c09020c01022106090a0506030c090c091009050f130225 71
    0x2000b440c0c0d03014140400d00300c4c0b00b41d40c020040c00d0601c40c25561a0024000842d0b40040d800301484045400d40b903d1001101055201c1c0d03202c0031000c00c00000078100c06a10b111041651003c7d40001e80e108000500d14040d500768820561b2200140c0070f0490781802440304c060301c004003000c2031080c52030b0450101c005688042d2035084d103103503c4030f4a04055849004486059611500001300441c9091000313140c00351080d015907014400d028000f0b519900e081e00203540d10b82000c08890708050f00004c1e00820120701d1003e441c241103c54070042c00c00d0040c00800002d22400e5400c0100300144046820f000d01113004085480310942110749000f5008000002900e500180700050740410f0405960b1140d0b6005100b490290381d081840005804040c04c496010f00c91b00c807207003c0c187d0b50207641703d100e1501c902c0e8076a2640c00907070412012030044525042440f60340801031090781c5620441c248003060a880342c8110080b0b5071801c1c00248511008040c41c1c480f20290b00000b80c01158245c203019000d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 190538875 1250 190537625 190537631
    0x60a090218040513050d120f1e050a060504021306020c0a0b030402060d091509030f170a0e071a040f0608010b031503010905071410090f0506251104 65
    0x545104004922400035040c1d400c0030031544190785441e2941129601080802c49041c00103081c0d55220b01d0702101e24895008107500c01c80310b003400e1400d0300c03e088192000000502440d02440072080423030b81201e0b9100c541ca41c5500000f504004103400c0302c4000c0c10040c1c000c640d940c1c2e244208050302000c3c0d01031000180581004240f440c13a02da00c03020292000458074600e0364549500700040c03a80401c0c02d840c50070b038584a05401055810050550b803080c1c3d4403002c210700c0301c90304c0c00078026061010382405001583e038001c510121507500c3c0560210546c1c3d4001420502d4044161030103a00e544100b80c00307850014000d255202c1040a401120080d1140700e0380541c4491003035030b034a1000d00448504223414400500c0484401200030304000c000303000054409040e0702c8990900105402c42140544400c4400304282000301c1d14030701d0700507a441d00f85c00380b6040101c065413074426481440d00ca130001145030f000503188a0102c4000e4034101c040c0200e60016864900c080c400401c4d8541d2080780307 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 190540125 1250 190538875 190538879
    0xf06020303151903050d030603120302120f07030b03030c0703141902040c0e09132a1a0c0706020706020606100e0904030e041e0f020a0804080c011104090203060a 71
    0x1000206880c02101036400d29000001c000b0184061a2000205483e242c060340400201280e420b01084400044a507170200c1c007542503040c443d1004c0b00c40d54520041510400480c506102c1c280840c0340c100d0003400f508100d03911071038011006400010805985030200140b104030702400001e039841160300c01d01c002c050450b40d05c0f4640b0b490300c030b020048400c40308408131b80000503e05540011000102030070b00c40b58040542c80030030480c92084070039004400e110702520091203a00c1d030300182c4204c01c034112a215452007108800540056101d2141818500c3c120360f0140c1d00c1e0301c2c0a4508880082044030803150b9100303002581d8840c18454900540520004101c0740d0421140002c02507000761250f40c1195803590a108034584002c2c0140c041141076125a803460382c490262800f0b000c0a42d40700c0d6004d5483c00884000c80e0700f441c10841d04680b0421440c401d80e50482803899129420070362142d00d07120b4108401c0e014116034900056604000200450a00ca181d806540942400da440d804695 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 190541375 1250 190540125 190540127
    0x6120606080c0a0810090501061805030313050409020a050d121403040c0e0a0f0e0709050a020702090613020c010501030b04031206030305160302010e07090207140601060e010c02040902030a0302070f06 88
    0x2801036030b41e03403403001040120243c550f0003a0b4105030400820800254200c0d82c3d940c0c000101c43c003c2e00072000255003102d03840444510300c200720000c3d1400300c01962604c2c490f1380c50101e06040342e01c0f940740240d441c0c10382e00c001c0d951603854003030041c107000e0300d0300346006518605200510120304145020601010580c4c010074140c0086d80d101d19442110b9420480c1001380c41c001101d03005004446640d02d031100300301c001095000b40064440500b0003000c03010b0070301c813000c0141d070030081c980c44035240305000080150703540d5111260081401d0f00c0d2a00743c3c09220b0070080c0070b4400d418401019601303210000003008180800f8038800c41c000d41e90b050550303500c030140700705803155407101900040c824003040440040c2c5408078004c0d18424000000d902a07884019400e0821981c0519001580860600103104d584180070640c0b6881102809141d81411310140c100d045809030030b8100a0703a2a604011034965520101e5000d40080803104404203c0c600250303aa48a8000d43e0001001c08030300180f62 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 190542625 1250 190541375 190541387
    0x60a1d0105060d2019170a05030a0e0102160f0513020a121a15120c0403050a0b07090b070c140a081908221a040302030c09150a06120606 60
    0x22040240507102d41e0740c20b921003009440090800c880300024141d02501d180e0354081c900040002e0300411440381c0c0345000d00360b9055200d00c00c0412010f0700403d587c070340060404011982c1a030120304100c500c0803210300c0101d141551028600038800c240c1c0c9004a603c40110381c9200c112517007154440f10190481d1030b200140e000780341040010603a14403c50191415035000240c10034550b1010000100c02d5800060a02c01030040209034285d00213200b8003070160001600c0c0c2e0214011480d1890a03181d80d88455648000d2580074104040103404200113501c15803152004002c841c49881c0c58000e01d0074030842044603489048054081c01480503400d007400b45255013101d040d54003412851010b40709060000401301700480e10034004220440300001090300813142c19200c1c8480400842c01c100316100c002d40781350001080038105200c04c0006942c00242c034040503000703030b451b28082e460b40c0007801c07441c50500c40d40b10350185c450100440d0090b0b014801d0460080280000c1c4a21659107a042d100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 190543875 1250 190542625 190542631
    0x4020708071101030b06130e01140607060c0c0f03050c060601080c0706020717031e0609150f13110d0b040204080316030504080a0803010509070f1e0c0203060a1d0105 73
    0x300c900900010000c14100e100c4820788000604000c2a4003980c500000c600340c2c040e400c602c105064514050224001481e4082d0150584c030b03110003c1040c08000098981c010100014900c5480b110343d0350f40d503441a9510301c0300320707409119044000c01e103241c044c0464110484400413071003000c002400382d6215246580c01915140c688501d000b515440d03140203944102810b446440168a004079604680b400031407250301980c02d030000d030046030b0981240040d03005d041180705200007001d000804460104050402408882655260200b4804504a48000c42c030040f070540c5002c90802c0b0450480c4000c00610b10400300400000041c00c042004034001ca010311001c560040c8568a0880c00406000c08141c4c041d0504a003407550711511a0700e0600c203403070103e4041c640070004222904160001a40245180c1412800803c0e402c400503c1c01566250408459064410041c18503000e06880304a6035009001d840e06c0d847d002c180c9101811420310341681c0c205c20320944181b914010722810340 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 190545125 1250 190543875 190543883
    0x30210030e010209090a0e070b09011e1b150f0212220b131e02030607050f04090501121e0f0f06020408010e010c080a09260415031a040207 61
    0x1804610160003200241101e001807242076500f0441c4d08965980e209065219148005001c202d44a44013030b040e0820110754840c202155051180c1191f981e0071241003040c49408501c10485020684000c503084008400c1a10240c48070f43c40c400c00384403804040e20308424500c94103104c80540d030510502248101301c900c2c14403c0c0c0d81c3c404600000c00a40000841400c1d07100f10600101c1151601e082c00281503075160691401e68a005040000400703003080003031265001b0212042c280d402194a49000030010400c0140c0052450664140361090301c004d001c104804012940e1203840c550031046603c0f100350754014540400350011204840e03001c80d10780c1e1020710748403005120741e0f132401141c00d100d00444030103400380008a2805001d1191400300e2450b0000819480140600a00703410b1000c0d004111540c1400c9444000c246040400311581900080c02c0c41903800400340d02800380100e8020f0440c0901c03500040401d0b40e456086030b03a000e400124a00040e080b035008100c120321600038010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 190546375 1250 190545125 190545139
    0x2010c051e0d0b1003020a0e0619360e060405010f09020a0504170c010e0307060207030206070f0c0f080d030204060f2010090b0f01060503132405041b0302 68
    0x703100d08040015102c086110b0a01080f80d041240005408074401e13240300c4006a4080340349484954060062000c00b9001c1e26591725212941915511010703d800c0c102d0240141094622040300034110801403e07a4055413010a2042012b80010b058800d0b200780c91601c2224408900c1625291203450704031085a0f0702d1050b0f007860034211030060b42100c50210280310081c480043c0114810107461000341425001c0e05009042c040050b2100e900c045940740268005031051180300e80000d0079406481c2c04031a203031384076039a610745580d85a04105000703050a20811001800340c10b113049541c19100c40c40c05413800c0005d9104128120f014510411000a060018074601c0902035014028066006040c1c0030031003004840310ba1a081114194216103940e4030200740512000d030603240d40004546088501c15490072f0720090a601000d403c00409061513000e440070020b140019a40d101c0318424140c2c40030b00345810380c40043c0021181541d6003099034441d48000e00c008840c000559600501c10 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 190547625 1250 190546375 190546417
    0x1120b010504050c190c121e020a08370302120a050f060d060f0e0309120304230a0e041110020105040f23070909050d091202060a0302041d0702010c05 66
    0x907101d040400d0300e170442030150461241010640011458003038600c2515a1540e07003241c14100004000c03800003010464014101c2c1800241c100012241c6c42c010f03080340480d001c0700800394001c0e02070b111066880108030406821007070729095006412030080310509011a66600c000c1001a05e004440169100400c00001110b41c9010421004020300800780082c920031090090340807a0000c500c821a198004100d088803483c1c0300c40003c000100d910041c505251400980c4140f204a450602c42c2c1c810002a0b4680941c68085e1680700405484040b823101d42018144803103602074020401c1c1c0141c1201d400100c1507801402001c5c0510340c000010b5072a04880e40310036042c40c010001c0b01c140f0402c44146c0034400716040003604090030720000d00080381c200c4d03403030010718240759a0780160a200d0515803c2000c40c8610400842a580580320325540c0c0301448001c0b0000c0c80355801c0b03401c40d6010b1185149103407100550035071041699800800408000310700079a0a4040c0742034041c0340c0d400603100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 190548875 1250 190547625 190547647
    0x705120a150b0d03030902190b030a090809130605130b031b040f1a03060901050709030f062007020f010306080c061305030307050d0e151204020f0901120b010504050c 73
    0x26526803a0740000009807000e05100080c00f6051095425000031303840790115800d5150103049861204100b800e407049640c9042540b02c41e9000040541280640e150204401d2020940896150384002030001c11991508007110300104024003031640118024a440301d0002e01a104050b01c00c04014000d00440851610b90001c8036110742259811503101e049050400c98903004040c0422640300e07200f101e100710740c0c0c141464020020880e5070030b130b8144410f00ad0541e800808031403d403504054800020106410b002011b44030451010b02030f80208240808020343c01405030540900c21038103240350004030f01c011004d4030250b000d00f08142e040801070b4042854035100520302500c1c411258182a03940e00d00017400c6070020b40081c2d580c0d41101c0b100090711a07020851310910602101c0607103204030141c880224500070b900c9403030703444924038010805540e5811a80c0882d440f00a010f0440c0c0e41e103621200c00c81640354841140e0042e03200e00040b40c40c3c6098000c1e9841480e104402e1420161090340d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 190550125 1250 190548875 190548893
    0x906050f090f040c020109031b020109050603070c0503030106080105040f0b010504091d070b03071205070c0602071a15040b010503060d240c02030702120309010c1104180c080705120a 80
    0x10040c2c0c08540e04000e061162203900414242d290942c00003c2c481e040c608010304403051084041d0100394040203107000603a0465400d1f016120f0030b581c01034590741c3d00ca0040e1404d4100d004050480d2101000024002d540414018140ca000395030620030103e0003c2d280c1d05507000d040605010500c18441031000c3c2e4040e80c050101240c10384000310b11070154901103800d00c0d00540100c224803000008112007250407045100082c5503a140c100040e2030304144c0241760b1201c0720030003080c017034000071030000740072a00003c0003501c6410b5a824845003171410480040402c00b10569000e1070a18051060355801070302a2489010050030401052800760348640128840c0d0320072424504503240104880d400c40e00c51003c00407004e070015590340410780100142000031207580906075104100b80305869a0101902101d25400014403e902807c100024040c0c0902c2c0030501a0101d200240c4052041e0032032644c08440c07103042500e20b050b0f118002d1000642c46094040b03050b9008849607000116072034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 190551375 1250 190550125 190550137
    0x10908240c0f0409020406030b030609030a0c030302190807030e03040806060d0c031b03060612020303070605150d03020109060e010203060a030305030903130e042d0201030e0a0516080d0906050f 85
    0x25101c145030a200c0300303241c1416003080d0060100285d002c58140080342d010302c20b030f2a000d1011002040c0524000310380503981d110314580a1704028000d80180100750081e015180c40300100b07034601c000e1941c0104000c1c0048412181900002d0070600031059000012049a007540c080c00007800490750782c04280030801015041c00c6860446004000000c54482d40410024950000c900e15900c0c1c40c60a1040913108540c00c07480505050382250340041c0d4000085456071076000b50041042d0395040c540404a07104e0406054018144192080c1051360650080303100fa48101d204201a60b02c2035010b80c201e0004442498002e41c0704001400480c1c0070f800132f980d002d00d080c5e040b20300e4800c500300d0058018401c0d07840030418212001c10701c02000400040b0100c500300344442d844012942003200790044d8108840641455512011184645d00c24485010710176008011940d040c0a4041089030b8a6514407420002e4003800d141003100798855544c4a0854a40d580c17894204007070f1440c0c0d15040d178404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 190552625 1250 190551375 190551391
    0x9080706050c0708071e360912030905060f0606040303050705011506090e09060c0f0c0c06161e0804091812020705040b06030f010902221401090824 65
    0x41e200000e01581c01c02401300585805591180300704c403001d0228613503203181d4101081000100010901c1050381f103801c03038501510700b0704400d03017440038550541c010182014042e00501005030300310521078140d0800ca20040c0300c1c008989840d43d8158909010800649002d54030230020081000441d1050002c2c00c2c070207024000014250400c092000401c40300c9a01400c0412000c0900f08045103081c0d00c0c55500c1200140a4a018600040c1648452094100004540ca03002c925441c40d40780c00c00061800090160205a80f005003a4040d518038104203000c80314803922071403445454118140241480d68031605c0a420b040c02c1a41140140802900c90750b11072282003149000b0030350000c1b598418030b01e1a005011054200414041a2082c1c82007850156030108184028140155140340c11160704003401629030300c10a00030304030340804800410804003101c001050340307400c40c07040740907466098940310381c01c43c0d9030491a911a910084c03103c2040e18071040318100038100d5584c260740180d030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 190553875 1250 190552625 190552633
    0xa0806010504090c1e181802090303120a051e07030507030923010b04021c090302030f0d061409040b0612070503010f1407020102070807081e0301030503030f0709080706050c 76
    0x111543d103000c030b4001c1e5000400181c402500200c01440d261000f02c0700b0910b514000c18020309007002901c4444083c4901b0075000b1030840240c4426100380e05440c291500107041c1c039540c0c1c80070405201001420355100007290310340004256005011801c407a030745108031010240b556501c140036001800c0042c00e01042c5512100749000140c5100180341d8000032840c540d500c1c110355032088500715442c000c4000e008520401c43e130710340702ea40d0740340002641c501080040344c0c021107860200d0540c062100644040c01c8040380705040b8a42035003001c016a6440d203003180501c110001040034480090300d01a03c20165a404900e55003000018546012032007001c0f01c0703c040d03071000460f08482600d03d074400704954800020482d03412001006420000510080d4205009501e07001504c0c480d074800103045020004028540708440c460384000c00d10b030034220a480b5a52801e200b13440703a000301c95074030700183c0c0705000a140c5402030b04000c00381e030088d0380101a07460074544140c0e20b6500800d0345140310301c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 190555125 1250 190553875 190553879
    0x10b1309050a080304050d08010e01062001060503120424050d0b041b02070602010518150a060306020a0f08061504090b01050904020a0c03110d1d0f1206011a0309030a0806010504 78
    0x3c030321801540900d01c101c0c000d241a028440b0010907051041c2c0003014400641d200400c030395903000414030040b106024a4a20030501d068810380102510b601072901802a180f008010001036070141040311012000002003003910704042d011034100c9184040411014800c0030202892644924400007010300009079840010b1000391070300031420b00c07640060f8040e2400f4400180d0a0060316003050549130486100090004d0a90b100c8490586042c00c84800364005107034800300d900300c040150381148007150381d5140304600900343c0d5103850001000c00c4141003c6616400c0000448254000720800c40d803d05040c0207408000d0007500e0ba003541040810303c03110426035141d1004058081c09601d4640c10f00f0b41c1032a028214607042030345c0d00000c1e00824040107440350840d000030400d01c070202c200d07040814202d001a181c904c49a40d10ba402c5510103403a40c5801c2c0b40020303958180c841c1c65004144000038004d0501652004494a0704c1c00c7d002840200f01e19801204000d800031414100030713007025 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 190556375 1250 190555125 190555133
    0x215131e08090f0307050f091e01030615080c0f09190612060b010f0e010804030c0614070305100f0e040c030812070807050306090f07030608030a05070203010c02010b1309050a 77
    0x111252000303a650103000a50b5100078509014882c601d807a0940190841d03074900f0001a0642da00c40c0c50b22406028404000781c00c1c5400d07442c1c4000c0140716000041200e50710790030080000d0180090303170a02a821502d000c259003200141100c81082c004008100380201030090100102e4041c1803045c407007075055100902d0f0105401030302d000d4105100500d080344010b04149056a201011090500442e00e101a800c1c0c0e9004100c580610003c1c00c182c066900c9925040b14a080800400360040d45030030100030740b000e00d0840c40e9011743c000d43e405111949641c030107240e03145500e220b80008110307102c10400c03888662099495100d8007900314040720554a40b940c44550b80000024015501e401d42000000c0e42c01109464010081b407401e40d00b0b5283c088041070740c03406c0c0500001680c08101002903072240c8250005006802820117581c1c5459041c0d202900c5900b080c03108038030a50038507401c140c0d802d205200316954100c2c020604101c0c42c10006c4458010b10035408265602d0003485602d001007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 190557625 1250 190556375 190556423
    0xc0e030a030215070e0d0b060a0e040b06090105150a03050907120b07020105100510231909120309050112060803040e07080f010f0b0a170f040210021513 67
    0x1c0c060380140041801c500a01c1284140c014080e00511409841c8204c050316204000c0445a80c031403e5105140c41d0034001402c640d94543c80144124005800c0008011316008814003421081c0c6407007507aa40c032a405c100317900043ca244000807070300500c008408181300b03400194102040f0000d039a845500e552040480030401350317090f5881000c5606004805509100b00380d40411041c55405400381010001450064010b410100f0010000e07c0c55440b00c58a15844013124500c040c81ea9030341a8140740b640001a090310b000b0040749030890001341c42c050034600002e03000d03855540e101c0c0550400c401521031b0700d514100312900582d12034001c01d01c00e20400041001d0616115070b00e00030300c0d110000600441e40148a07180429078200104000b041000c080d03029105510402a04c034100003504852218902540703003e20100b81042c003a401c2d01c0710300c07400d00980c0203650715103c3c2184544266507420b044500c8500c2013a0620001d100b072406400d60b03a13030551003400011a016540c1d2402121 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 190558875 1250 190557625 190557643
    0x50a0602061801020f090603091e060115030203042114030f0117030a0e01030c03140f01091407021506040608150603210f030c0c190201080f010b0d0c0e03 68
    0xd40c1c494814040320b1824801c41c1501000c0c9480207500d490001580260075008001c4007a00601000c404900b80400500440091041e20343d00700d120391580160703c540d101e00030f10481c01441d1a0300074904000e0320074002ca0f4401d640002d00c140f0504c54902d08401c0b0095050000b00412244810b440b103c555000000d5015030300c0305081040950500c0449640960748200c00c6805610800c009203400350001c00e4a61401c5090900041080e80301005070003038151180141400a4140e08102c1144070480e000c038107840c03507504100a1148d988030500d0f0540416181d40c00540c1c00400141740703c20005400700d41c081000340002c12500e9035600d20310b2411002c080d1216042d4800802c110a0741420000380d002c0c0003881c2c00443c04076010301c68420083c4100601c0940c0c070074002000803c2542d051048501c41003400d8100d840340d0850300724030400d000302c04800701e0020f0b41e030001040014202041c080e040e100002022450480001e68540007804a811507400744000820000d29540c2d0612100384 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 190560125 1250 190558875 190558877
    0x8060f06042111010905100e030102040504060f0306051302130b01020a080403030e0f030106060e091021171804050703060509150a0801061202010f0c08070609120804030203160c050a06 81
    0x12580d05250520b03e12642c194200d04000780e03410704004503911040311614034000b506000410542c0b00300480d0180c821600455041801e080c0000782c111050458441128050581081151a04810b05011a2040030003a5208000c09100703400380c24243d01106107040140100d60142d4040c0e6076042e0300d0303080b5500c150701280d41001050740074280315207600300e5030343c0c114003c12100303080c100c0140c80301c0342c000800d9000d219908005000c01c11202d00308005421907403407048000d1090301400382c4810b1944d07070460b00b00320f410fa80d810713000d0300d00c805036411240d910151135440c4203084244030040200600c040e08043d00c408001659440341100c241c0a42e00c4c2501e8006d51203143e8060002003061644000c1140c2e140482c10071880075542c1250b402c250342440c0001c068900d582c03046445a5a0400107060301c0000120b103410000140d21207071080b8841e0400490600d14503e0564021748216005000758108209510485100e060300d802124450300c200c007007081e11900441d103200e1941c0c01c014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 190561375 1250 190560125 190560179
    0x20313030f03060504050a0204060e040c05041a0705060907051f08062707030501090e19110a080328020a030f1b0501020301080102073513080a15051608060f0604 71
    0xc400981e01580749942f1503000d0b24240400381e90301a0080071032080d84903481803604600e103036103e41c1e00e880d0300700da4a10740c100c0c00310703810b9042c00d05259484180c20710035a40701e142d14031003004084021260540300c2203101c1e140c2005983d280b1061010b8011901c80c01c071019003580c412039400007600c4500324000d5905035000101742d81002c88403000c4440007101d150055010448484d100310001f0b07003281c840d542c0021040c00448e410400724888980c2c540114030903010114580300d81c00400b03084215210040344060030400914001030340c48405500d03020b400103e0128800500e42e010303203d290703850b00d00d0894031041e0300c0450301c60a08a030000e030001002d50350000780080c00e01c024030054010b0107000880d00c1442810322103c010015000000c903101214000c25610300e01003582c0d540c84024504401921a000010715101d075202035000480d018a920344404180130b102c800c544911010302e16180c2d0001754489004200c20381044c104420740c804010000400c0141103044143ca00300c182850758 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 190562625 1250 190561375 190561379
    0xc02040903020f010f0905030f0708070507080604261204030203090319111206040b04030c0218060108010f0602030f1c0c05030405060606030c090f0411130602010f020313030f03060504050a0204 85
    0x40f40c00d4a0600e00e00d800d8050512141c40d012540220455499143c1560015600c07204d0740380005290040d564050840d0085e4a0001005000881c03020b1199101300703c440c81c1c20360181e01416101603002019009071006101c41c1c084e00c40c54284154004d4060300499041000c03680000e46044a002da0b401e00304030419640c3d00400100041300f0307000700d80c22242c21103481041e0020f02c2c6d543c0350043c0050310712800f00c0003150506000c2c180745148541c02510181c0d0302c2e074046001c038044000503560030b0b0014140341d000144000032030342c00c6401c0d00d9266010b5407502ca15607201e0b040c0da80001c0c1400c9000d00350f60b07111440c2c16440b0700c28501000400c0e00c0782d540300d140605185040c40e900070000c40c01a80108100400c4600ca03801300d0701d010b03104490807041101a400414010701d030020141410620000d40c07144007601c00c10035030f01100d80c26030080c820310800c0b004038000d03400103a071102c0e80c80d8000d412190000340203007aa0880d00402d4500010318a81e16000103058500643d40b0202d01c1d5400102 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 190563875 1250 190562625 190562653
    0x20406090f08060f0408070210050913050402240f040e180c0307031e0606090506030d320d090602090f0108151005070219091404120503070c0204090302 67
    0x20a000030100c6504041129141c44403454580f2401842d10550070407110019080103009820341d82e1151f0058203a805046540e01c0c094800c0d440b88034028494031aa840001003d541806024030460b400b070003d2030800c0c000c4a040008220624095070140310074850948032020b000d0190005150041c143c0f095030402102e40300c87c11500c508009040d40001000d520152000a400c00c1240e0340102d20940804844098014560a03200001c2100307080050002d0072540f00d030486400307030340d0403070a54107802140740c4160b614581ca50702504507043d0220b00766115105854181c0d84046031911101c0c07400c40040b01000442d00951012603c256021802911714188442c070f030366540d403003070918291500308048110a01c02003444810f20400341528a100518072440541d00c80d5940901038076040d011100c0422400c031328034010340c0007481c644070030081c0c92070b0005032080c00345400c030030460714200025004441ca5800103129070148402c0703c403510b0040e2994411000954001e502070010b80c844092 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 190565125 1250 190563875 190563887
    0x31e09030d09050d2304060c06020903010e0a140c0a030b040606052806050c0613140109080315030a02060d0902040b0a080303090601051009090b040f05010b04080c0603040c05010c0222020406 84
    0x2101019691201003005c0340001980490302030ba44142007258400c1c05901e06007029210b5601c3c0142c040d400c0821035404c030440081d0f650445031186820310218481400381c01d54070b14400040c07941c000d068034004c101054044080c02e412a0040101082481d1140b01140d40100315906581542982c04683d0b0717402ca103c1441c40018005900d0b0040c0f0780020322003507582e02c03040903009000015145080f04d04100c0407140042c0300c0381d1018002e2000d080035003007141c01034000300c0305134140d1025100c50140030329001c6070715400d1a85c01400d071030400c807a4110b400c0082207180c07000c0780c10994030070714068660f80c0c0e01c1052000304003200003180c0da45815080c890902c0010303407225001d126140c200c0c11965401100a6040c0c6112034400218a403003d40024080c000480016003504e103000004148024000c00030300c00c0e1100c607021200300c0b808203030622840303110464010f0300c071800315171090042d98030030f08440310340d18002410f0344038200c402015865000c003050881c01d040369001800b0886190021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 190566375 1250 190565125 190565147
    0x40203090f0f0a1716050f0a020102010f0c020a201c050d030e0616091208120702060601140307111006061803020d030e03030d0606051c02031e09030d09050d 69
    0xc0a45020007503580da015139140c9907104000c1500300072517083d00d002e110000c6a42580d4005003200d902c402a0a02942c0310b07040300344180d00550806200443c10a9240179440c0c1c0340c1c0450740200540c25007038451180641c260882001501c0c520101da907044d64031030b407501e03e041c03410703441400002c42c8925001d45007455000d045400d060600d2010000100c002c5181980310724140703401000c141006804460b041000c4d04242e1503000d10b0002c030814420aa4090301c03010f44050701024894071407400c00d0780c0d00d0300202c0d481400034a811603185060a0b41201a503000310040c20b2003416420080c4501e410002130705a101d4925135545002c05c01140e00035058014280b4081c44c050540341190049644560514805024004494190000750300c0402c11903603040d00c050001c10903151a12002415a4450a140b48818200e0054451681200d108076401454944440740003842d0150354141c0d6540020325219090000340305c0e0107413a103500d01070001a14420800350030019502000075103005042 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 190567625 1250 190566375 190566403
    0x2030d0b0f09010b0a05090a14010201051b16020d02041a03010c030b060d0902031e0105070305010501050c1510180617010c021005190e0606090a290f040203090f 71
    0x181d40103154644071421400e05607804100580c0e074464102d00195840c0c8220080c654200740705c120002035805c5030030361a020701c550990090109444409140718891b01c0281c00c50607a982c00c03c0740703480d885001802c00200520140c0051300360300007070b00007404450440340d4203416035444030a66200780c0303030a12402242034200e0408104200781407000c12010700031010504106070f0f40346450010341d03404001140c440780c20032807110ba686810700e40c40741c0a0081500c00801003030600001250960080b004e4400340803a00b001841669004100c200c1400c2c0c1c041c1025070444501900401d006006142942141c0d4800c1000b1400314500404991480b03c0d20080341403603490610000e54003940070410b032240c0c002c40c8a021543d601c43c1d84d59510407030030728241400d0041c50244038119034840440c0c214441c1008072105035069440b0701c6544156400c1c107a05003824001601000d1080246424040e0586000f5001240042030600414103d1b4010f61b025899030b0b103c0e24031445002d4041105054983d04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 190568875 1250 190567625 190567639
    0x201090b0a0c14120717040b071212090f1b1a07110f0109181e1b020c060406030e0a050d03021215030a0204050414060703270c14060f03040302030d0b 66
    0x40102484d8014100c00601c0321105020682c2d8a0103010f081d200a0540c400b00c40350303100030b1442d200c201c0f442c000034444041011005034110446061041921641d00407a82c03032103d40850742e03040381c840040003480e100070159038008542041c0d03002021021a800689070340ea0340601e030510717040d200d048900d500e1054083d641d4000c4580d0388001900100c0310071752800850740c200141410046c01c4440e0462044203406002900c401c240c64005014480c0e403035032034242d241d280c5d10081744c03902c10398200190440c2080008024091080d40180038150030001036a041c40b000e9540c0b03608002480076041c1c0047c0d00401e0b1a00040d4016844a2704100f40c0c0005000d40180c0e500030a4036038000e1240031b8491039541e800103081c0400c0c0c0b83c00c46480803940040e2074551074200b1024005003000d6590404150014201c143d48028030102034003002e8100085891080c60060404035a1051031038513500f048062000040e440310510117140914460740107161500c0b500421001118400345505104d500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 190570125 1250 190568875 190568893
    0x714150306030c0609012312010617070e0307030b010b031803070f0b060609040219110d1e020307050607050c010b0406150806011b0c1403010608060c070201090b0a0c14 74
    0x20b80014041920002502c0700c54031040b080c0d0050307803080c03281200d030081102000c50080360806144001d06d00d10328800176198151b62110720440e0814103680750700640c4a07a200c040b80301280945102d0800300e01c005d00300c0c1e04040d01d0b542c81506c103110030386c01110300c04404010300600034030920f80002c00d0100c0310029410100e40317841d940e0fa8517060380c501400c10001100443c2d50741d203600c003c888040b00090401d42d502c1c0a1030000054210301c0301c03090070005650b20081e4140c1800402ca41f04e0b0920345a580603403120044000c60340940788111550158401040a0000180c0074400300d803180c42e9645500d522000301d04d410609550032408203610940c60860140500751078031140b8405501c207450949901d55403440140c0d034040e40b03003503080700000c2095406810413802d00281c1094440f145a2007610b400382906040c203841c45400b82c400b19401010008400038045405040e03010300514015500e1a62503596000a0b072100c2009400960144e40001c280aa20700358a94844503003801000003075 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 190571375 1250 190570125 190570129
    0x60911030a0b011a2506060f061d0310110403050105250807020c030f010b0f0607050c060c150f01030b07110c01050a0306031203240e0703020a110714150306 69
    0x2050500501d6282c04507004c05968130680e48042d1412400180402070202854020051081d04140012a009800c15001103520083c07010180102ca0701c640b115515220018009408004002d00007501031041140b44200004e103801105420140302d140181c0c0c4600350300306070f400d4881c01003400700000000c0d1020419034102c0304a5403182150303850716500035118088120309040804100b0359051080180e00140f03144103510005514030300321502628030b401201484810b00075800090a190040070380aa110300703140d801000e000700c03401c0995000244100c2000160203082c0c65400004d01880010710400403070100c01030300400d250602c116004250f6020750b543d54040c080850421501003520b1070080d01a0304000003450707212908243ca46050607000307004040100d900301e03a8000c0047d030100011090f058413420360301031400000035a56000000d070060341c40704041a0400c060314000104000b000c0c8034200180003528541c1c0d400701440020011502c4405d80514000e00080090020707075 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 190572625 1250 190571375 190571393
    0x10f1d06010e040c0c0506010f080d031e05060109170a060f0213031707021f020c060a0203040608130210020106090b0103020903060f0a110307050910050403020d060905010b0d060911030a 82
    0x10140865011960512000007202c1740340792440c0007130440c4a003800106040c58003001c40000c0c0e032000c2044520418108000300c064035000808030102810000700400d4201d003581126500035010f0418800e5942c2ea0003401070025500c14040305603820401909080280030b0003240040386600c64290705286044c0c41800819515200c000c04022400ea20246111150750944400a070020700207002e9801c2140c8000690601c1d00d510001800740c1082c507016444c00030296880140307203074001e41c186030901c1c3c81515207404c05012041c4446480c03c503500107964204040e00064207960010403e0b602c1c001309902642c800410b940c0c18180140441035241c3c5000840d40c1c4d020520300900d1425480b95661000203009414a2400900b4000100304620b03420000800c40018141d0b00305966124079041101d0f28080c9000007944402c189074140007284464010000c4980160b0000642c20b00e0000000c03200b80f054041111800c3d11100c8410920801d0108109800b40550183c0f032150300940d161070380 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 190573875 1250 190572625 190572647
    0x607030b06030a090302010e0f030705070e0702121602060c0f010f060515280c0b070f080f0414070602070518040228050a0e0109200f0702040b0405010f1d0601 70
    0x1030700b0341d04e0660b0301c207041c800d400c00d40000d08a0410f40c4ea6500058002589070741c8544e106845910501000140b40c0481520441c810344280d4043c0620240803d2196840d91040d41c9644a0302e8049450102503900c0c04002c01d03600c50340000a0403a00700410220b4255001e4181c18030f200ca244c5101006103480e2601c244100c5082418050b646400d600a40403d00303d07000200b03009912980f0784103100682111034001b90300d010700d0b0000382070b9995000881d0703124640c0442200180c00840800c210249519182d0f4001e8480c102400c4c000c0300d04501305140403040c0d441640160301c44481000141001000c200d031948018445010034601500807031048005200d44034100c038039000003032502c40c011001c5000030f060000d1103056030a5941c10921240303182800b80204640c0751481d40323213414510310382e04000341c025603807800d0410031642e0000015030810a403c0e80c0164442107010080d44d00d0344034190103030852402c00a4074a003050124111500000d51000c02c11610301c0c1448403a81e080904414 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 190575125 1250 190573875 190573891
    0x52e0501031e03090b031609080f0d0c150504060519020f0a180305010f32060f060d06081e0304030807061512060f0c0f0503010302061b0307030c0201020607030b0603 73
    0x359160b440c0b43c201d613160115808000082801720a024040701c101544a000003203d44d00c52805940b101c503c0d903101c161000981d83e04c0e03449603000365026030284109680c1c99004035a01e0340104500c2194400342c802c101d5007281c01c44d50703031010010040c004600001030388003608411403d0443c01450601d580c4182c01c0041f040c401f400039140480b078424042d042c0650f500c031000b4840303a00d03e81c040380701401c084a000d816500315040341803102e1103940e00090108100002d120b805845031014006696980c1440039000002001500a80740d401d00854000b040c20b44001c056111480c10380780c1800c0000d51108005800c10807042002c1400c01c000d499620b5000030b0001800c01301d45110603180000340d800900940200d1307002205120880d131005040c2c0d10304040c14801014138003021550100380540180210f00148014005803d2500c068080c0c081042c2e00d059260482069841c5140c020130000c03400a60b010140c0011564103204031500a50141004e003c1c1901440001c0d805001c0101034074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 190576375 1250 190575125 190575173
    0x1b02100b0609121014040b1305010e010c2001051e06030c090916050a050307090f090b01080a0c21080d1b030614060c03030f070903052e050103 63
    0x1400c1d600e0804031000414024154070040075140303040394592419410340b100d0030346013040c60628401120b03030581c42035511115030400381c6d0b14100401146840d288081d40c55645c1c800d620b540f274903403d2080c10b407011301540f601585000001c0180c00b40c40c00401c0e501440740d040005024050500000555000100844607907050355414007103490a00c0b00c28140e44c0c4901044107104403e500428007980108000710010081c41d103510501c0070000640c0b00341501980610310070081c00d0318660055041c0742c1c0b125400300c0c81c0040d54642c550054401c2e00103454a400c040c04050030006880081c800030641031142080600b03d24181000d0708205000103080c00400240145590600390703c6000c0c1018800c0c00c2d1940d500400d0001801050240030383d0040c10386a10000f203213481e1580030703925604541c10055266548031207070131220110107401c003010310182d844040001202404010810586d060f0b100344400c0340c11401c81c40310003880100c1c05440b480c00700140081f801c90051191000282101c1e1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 190577625 1250 190576375 190576391
    0x40b07020405060f011e050f0a110c030a03090605160b010e06030d08040317191401061101060302030604030c021507060b0a050d03171513020903010e0706080f07171503011b0210 78
    0x5035408d10426002c6203c3c10030000e42c00c11001e80000340030440e0750100302225000c012078010305640b0a00b828016020801c524010450705110328002c0608103600035002c51301d20300c25941c8084100080c3c0100072034124010030041d0070306040005c07c0002002d454402001c0c105901e02502071400030035007621400e547e40000701001204004641c00c0c1e5024a0204100c9000c1000d0101485003170142400040803002c01c000700303050501413901969002070140156807035a40d0180d45154840a089801c1200a03a025903001007020140c003031030303000d80c0021641c66868000c01000d0b41150308410300c03d425000c11440420f0344051412064442501c00d05c9058840585607801d000c01c012101e9440766904161400d40102d98024200c241d81c00e0f03000b8010110f0700780da02511034645016290001d069440020340d602d40c80282190031002c24103180302008020b40751020f10800885003204c2406103903108401c0d5090034031032145240321005260343c540c103004100030348903802501802001c907290304e54 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 190578875 1250 190577625 190577627
    0x150c03071b05090f100e040f0b04061406030f03041401110613020405060d0506040b041407080307170307140702040207232a04021305031507030b010302030c090111070308040b07020405060f011e 85
    0x1070088d5541025920700140b802d482d1000292803001c1100480ca165030001c2200760800040d19800c41c001200a98140303414205041e044943c00003c1030304212a00c031510702071200a001403030013403001040c58580ca4480b401400196070001d03103030601803c0350b0724010012550108500760440d9208042d604551207504043c440c90074503540c0c0714118010510001114070001004000307540c803400418041c0003004808050780e000c00c8400b1000b04a113502d000801044000007081c1a91000b0300050600065403201c03003038244598110402100f035021500d40c2d81c40b0030000340400c810005060055103900d4919140c010b542c0c00d41d014090f980106c0c6d04041b080b1400a013902414001d800c071003040a08065018211000b03035003480c00f10380317842000c1401c0c1d4440d0084910075011640b001b0301d007282107001115180f00c0000301100c24011200d01200040d1281d006000810a14550b5030721000e140c010001182d42c05000d4038800c404603c494140750340c01030705c18034010280b244000d41007000444 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 190580125 1250 190578875 190578893
    0x120b010b0a11070b09092d04080d3e0406030b0f120312070e0a1517070302090a0f030f020f03031902100614150c03071b05090f100e04 59
    0x100d500c040c010340c07801040c43c82a410140130700d401d00f121500680d4840300b4403124400240c540410310041070741d03011f208040c100d007806500144100d011b2031420303030b51000a90440d090003002e00c15503041c800c041d007007150703a0b804c14800180140100c061280c20f00c0440103410b01c0b0718840d031424552503030120326480d90303006014034144030003030030000c49207103c0d03e46039449600c4150102d20824004000c00c0090f4880c4c4c0c4021101d0304043c204824a6082030182c0202d81d00c500c82c0e140c10404054000d803192a071681d582d41c040e0803291805610b60a01c2000c00500009540001030b800103c004100081001c250691507460b0b0103031000030a00701d02001107804d521a0401c80e44d607002c94030980001496001811084440c0f9959003080a10340781c0a07961503100000d901ca6034040b0385060b68149102d41d00e8028002c401c046021286050040d41d03c03065400c1c1c0341d914044c140940d041c000c000500780200ea26a100056000e00e0314a480c080340c035245502c43c40e01584130814200710001e4100701c02c80e1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 190581375 1250 190580125 190580147
    0x7030b03010b1302040603111201030809060412050d110c01090b0f0f072607110112060815090105070503010803040608100e0c0a020d0e0a0509130204061509120b010b0a 74
    0xf810b1a1203180801c00004081c0d4014410240082d2400c00f544d030420561b103080d00e0a2031415461000e03d40d2079622620b0003034206000c505e42c00310080200081c5050341c154610003803441940901401c1440e843c000d0702844140d8000303403060f04011520042aa44014a041130b41c030880f5000c1e4440c000c95640000b940138140128000e200c0024803602403100d0b80300030f21083e0700007000340f41d000d00a28600032040c0c01008401841c40740c4080c01540a580103c002d03400d940f40185d000a0805c0e660b981040c500000c0c0c80750030441c0303640c036828000c116000b17000e180c0d80a2240c0c01c065185d545071600c015968030a9105d1601002020004100380410943c100c00060283d0700048256050550707001340c44e41d00884088025100d844818264503001d50004100800d004102040303191a06c02400000300c0000c20250846c0c40204440c001607549200e81c80147c10600e0301d001c0c01c0c0507000d002401501464020440d58000241e000001807a4882154152070702031003001d884070014401520810b40381 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 190582625 1250 190581375 190581379
    0x3010f21081314060f03060f0d02060301060f020606030d020c0111010b04050a020a030b010207180c0c020409080703091d01030816060912140c10020c100e060f0601030c0807030b03010b 81
    0x142c0d14145448144250b0554402040200342c05418204018181c03003010241c40c42040c0a0000070060305e0b119004586401c8007415140034089990f0008400d0351003600513501040355903040c4150a039040165540c880003d0b002071507002c81500703000e5078070b1000718074407410031252030b1a50420860a402c10100f401d0081c0003480603003001d10b140c101942203210860002407800080c81c00030341c40010908120382a0700142d2640c0240410008060b088101100d018041d0b00d010308c50041c0ca0324411081c03a980604103060300c0e04200e19004085c01c409a010300318038625050310060382e4040341c8844e81100e0340f0520242c0e5555950700800c20040b00001c01809052030100d04105101c2e4805124011103500e940b0800d1350203080341e800c4403d00882c400c541480e440081072001060841d4004d040c1c00c86044225032801041c40400000c0e07035143c0804d4440e9030401400d00c44005030420119406c80e100742000d10038000b00810041c00410001c081d4000c1640302e448c0740b403098030294003c0300c500e040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 190583875 1250 190582625 190582627
    0x605091b0d0510060f05090906040c1107030c0f0b041503020a0c0b040b0f0c1602041112010f08100905030d05061c030302090f04060f030b0601031d0a02100503010f2108 74
    0x7194409030f1900f4564450310340800d02035010200301c40d100d841110702c13603040203141c1c48042d107809062100411034001c416080c4404288600d000080401244009511070070001c1542800c0ca01c2000c4551882c1d40006011030b0240024082107641118081d00c0c5607aa180043c1c50b000d0b80c2c5400c50b201200c2400151140707400509200c180501c849107584501816111058a912010800c1641d4442c01d002400c041d03203e004203070b00526058203d0303180071640c0c0003818100800344080c1c9084000a0340840840c03c0001c00401c0700d51414850441401034825013044000000c0d1030f0b80c1d441340304d03031a407a2441650782d1000400548d00c624064401e102e00340e40320000703200386242c090f00031b41c420400a44916800402248145410701444064410b1003030402021480c65640b1001c2c410b0180025041c17507150041c0d40200701d4840581c41800045400a2156002600601101200c000b01420410600b0401484031240320b0403200102c4000c2140142204c0025a50007e014040c0030003e1000314 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 190585125 1250 190583875 190583881
    0x90603060e16060906050705071a04080111090108060613080609160f0f0e0903160c051003090503160f0f03020d0216030b010506090f0d050313090605091b0d05 70
    0x14050740120206014541202e004468485034003600c0d00b21442118000341c5008014800c0a10520143c141c17144540c00321611280c0703c2c9207a410000d11040c40c4601d41d0400310341004213407400d024045401800a0006182c1400400000e200100040885015250004860303610f00e0800040200404078102078403c54100041c0d0a522101e041f140004600700310f03040800c031582c1c0e00d45800c0442c0c6095072491201d0303190803010184400010304034100d90200780502000b907002d1080c41482c86100b5001066100d04190802c00d030740c0352130f00c40071003090319009441d17000031f00000071541c00000c4420f100c0c2e400360b070607c2c1024803100c40e400020082c43e00c0b09024020141c001445c079000e00e010b9000e8420300c003015460b01c0918a0300d032102502840b0085c0c010459414004c0082c00a54000382c0290a500385050110f4407101000700c0c00ca40700c0d40000384407100e8140341c50310300002c2d041c4500b0500c1030b43c2c5001e0008608400151140c13126803200295011400303906000c450794601648000c1c440c1c0d103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 190586375 1250 190585125 190585133
    0x6020c010608190f020a030507180c08090a02040506030a0f0c0306110c0312040812100501020616020a020906011107060228020918010e070b03041401060612020310090603 75
    0x241100a800005600704a40810b06010101c0d4000800742c03940351007040009540c8410b4030340c08014600b641c04c1700190300c0c0480490002d00041e4080d2061125441c0426a03030080d0904480c040e003201000c11000ca414443d800e04082032040100b40c04807804141522400002070404094402c014111140c2c40816802c0048891b10750003220302407103003003040310502c44000b24035100b00058001540c008000c0107a5a181e141c2d044c81c0c000e070041c8210740c208140c078880e41d10080c03026241881c484004407420429980d04000c0c403548084403070103445504480b25800b955640405c0700092003030300e41c6d030001003a0f41d00c50700301603c0009180040b101c05036a5990069201d03209010f031030701e81c401441341c6601c2c01c04052600d0002d2660141c0052075659511003d9070400d454120030882d25521011200c498034810000100030300114140203580341082d180030315080c40000040410b50b41484c0b0308014050300400718902c03c15455030f015903661b42d046010700310080c958218103101450652b0200c180 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 190587625 1250 190586375 190586377
    0x70314160819211d0306011d070e13020c010c11150903210712050103080906030405010f0f0c090f0803031308070210031d0a0203070501030c030b03060421030e030a0309080c01090602 80
    0x140354840c1d02c0b0782c6403030105014140c51b04400d00401c4100700e4102412600c51b424504459070044072440c09540310303140703400000e075011281a2000c89081d0007040f486a086002c0c461070400b0b210908200e0300c4601d010707a817079440301c13840c203055040046210001144020180300702c0e0030301d9240c1c40402c041d8151040044039054002d480c1d050002c1d4140052416080b464401c140c10380741c114000f0790410141e04100102c1e41d2008004540c0c0d13540740e03608801d40381050b001d89651812502c80206001003a400c000b09010179560014501c2895480200b201d103602104890308400c4000350845504a00c4c100400684982d1800a410100424072104290351540c011600d0840c01000078440c0009004490341c1c03140503410103545030300030b410304015a45c0290300086200c0c08900780480c0c036054180011f4101142200e059500320149540f504511a0101e0901c20680b80c0741010004160f0f00401d11b50307607000707500ba6601410344c1c841049080c800e401c0159400300114130024045c03404e0600c1c1c00c10103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 190588875 1250 190587625 190587647
    0x7050a05190c03060b06070213050a0e03071e02030304031a0f011502060a0518070801240e04030f120f2403020f040b1207031416081921 60
    0x18901a840980441c820032036030108106401c00c41d55141103056448040080005808056103c20100701c070900607200c2481e905500625100d0000d814174009030b04006603101c2c81e084481c950002c000c1940051042c0c03c500f9141901e201101c541c1511034404a0710f1031040780c1000d40b80a503000003800400c8135141c0380500c82d1000708102d84071641d0752010444142120949175015030011800940c445c16a0b070700c03d80c0d0104188034003204184180384540d080680e5500301000c01d035102c07498102031020a082407061600c00ca00c0d810340c0d00340f5200e00c00c001680b01078001130030400d5030020310300041c4c887d8541c840040180c01080068a4607083c00304000c00c208107460410710100101c550b4111080b007a1a0304481d000f0f0b01c0c80b0312282d00359040100512460000581c007401e020481c49020008020b010048d40c42460f9103001d07c1c1508070010710307013180c00000c0501d03003000000a11521501040381c00d41110494120b00044c03100b89084824000302d007408030380b115602c80f909a171f441d0f8072000b00d1107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 190590125 1250 190588875 190588883
    0xc011718030f04300605100b070606090507050c03070f02010323060a06020607120203061212030f0a0218010c03030f051501030e0c030a1202030706020703031a031f0b01020f0307050a 80
    0x104044008141100b00924040c00c0f03061324210601540201d4460f4100c55803003c41c80b50400c1505480d0740401c80c4940000c0b0098a550350754100a0005400e148039041e00321728681042e5041c410340318841552032103410070040081e40405086e50459003c0d402041c10f052807111025a6960304c04000c084640702120303075a10804204c1e03400a03c440c000301d01180201c1781c9688841e541d00030300c0310031400380d4405000c00760454299079951050803010302900000c02040ba000c1035403070906240c40c4c6c3d41c1d40b40103004214114410004008189611a100514420282810680c0031644e080680041080050864071241450b0070401c0841c2c40004140a00e4001d88040008910b03086500303590310341000750181c240e8403034035401002c140f01504507200741040380f04403454800d441e55180240e0b044000100c000c2602c888043d50039007440000c010601c2c100340c1c02001100440d02412250581c541c05003d400d582d951441d00b017591090007403403410081c00040302e95410281c9801c0341c3e0358864400a403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 190591375 1250 190590125 190590149
    0x50f0105061c06180b0108180303060111070e010b0903060108010e03091005090d05030406140310060c0f120c15020703140903010b0402040e06010806010c031e0e032d0c011718030f04 80
    0x401995080c1b08c082054030b010f070025401d649d1410019a0081c11441e1090054410344000003803186299803414040d0000074040c82d00d901da10710030b1524010040c2c120240c035905009410102d80c03800010384244050468482141c1605050207071500d00c501d40d040d41e00503007604290418004004020412181c207075650551880880d00000b03114042a60101c03005140c2540411002c1d204162051869002d8140d02e159080d0325555088003d00c9400d000000c2500e55400358144401e40142e51103011070400150701c0d100c600c1d0340080090301540c04107881c1c404041101201c6403002d40c010f840007040a0411507a03a43c4601c40c202c0c080804860481c0042e069400044140d403003188983e0142d81c0c591903131004c988441041071490710005404104004404074039a40c607a808115142001128003ca1b003c41450310a5106100301030024070100ca51041a10f81e0f0b050740d11245192710300e003012040d9011034032031103080100a1864200e01046100205c1e40c09044441100103108440c1d8001e070f04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 190592625 1250 190591375 190591381
    0x50912160b07020a0512010209030a0f030801050607030f0f02160905060906030d120b040216030c030807020d020a0816050106030804170c0f0d0f0203061306050f0105061c06180b0108 80
    0x25110612982c0802900300210040c10001814081e403949200a41500050b0034200c1c0c0030081303461700b07404072402e4130026045080d0900b81034100d40301d07a014090680340d00e40380545a407000741c05050704c0d140010800c2404030740d05103000d20034426113414104209101a04603981e6880001408040d1402c40c0321f0380545002c9541c070710700014550060111a19103090404062032202c008000d503090300c90f080703034017004016070414040350b80090152003034483c1c0c0004200c5080003861408010a04404c2d5030224aa070360306c990b000541a07441c0d550144420782d55802d150807200440b41790010041096080200200400007000301400035650640450140c41d0384200445684214440219411442c1c0541d800c00d1030810030a1000c4140c01056940c41346403459021901d4403000b181d00d04400030010b481e0307001b004031600a907604820700624880255041c400000c686204822000000c0d403400405400b1082c1240c01610040502c5500e407155180d080c5552400b620800210a0000f0b00729000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 190593875 1250 190592625 190592639
    0x4060201051f0303080a0219080a050609060f1c0510061e0f06110c030607030c0201140903040630060303080604091104020f0c0313140913060203060105091216 70
    0x90018900314240320640c228070f107460566508002a140b036440d0364081104510711b46410100d02607100a581e125a144d15045124108880c4040c2400d4891442071003848995a1826200300404008070360f1420200480402c41091924428000b402c0e8040e189004880c09480ea008a003150107014030400d1503d0000c1c6140b00d00c125601940010340441c14040c0071030703885101c50302417180200080783d6200b4000b5000a03d41b0004652200000362151881d0084950a0190311900f000007a000c82c0641402720703d0544a000764005c500820084101891021011000c50292080a2001040c681001000707200251034540000d8011074010300c0841c0850910b4455030301d290307402003504007603042c0039000c000c06076000036046c010b410020b110a4019400a00c010152298482c020704410f0b464074900c0c0d0f424030303242c4020764440d02408080002040401e90005400c3d9840305006035280e5917100144d900e402030050b480d07007203601504e4144001c04000b072810140801071b0450000e15581c0c1030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 190595125 1250 190593875 190593901
    0x1e0501080c0a0302030402010c1a0a0e07080606060306030c101106010b030c07170f04061e020c0102060a05090a080415030509060601120207020303071403070606050609420406020105 80
    0x801148440c030030002100b18901c281d0103150030505c1450710f02c10110309510707500003130b40c004043c59602c8c28002c1c09021110419100701d50740450740001400a5901c0c0290540e154000102494050140000002c020755000e2200c0e03103075000005d0403030f064900211001000a2402d0785030311110302c6100000300f188003151080d00d00c601c800300d03102c51a00900e0341c0e66070780b4900e401810b10403c080038003071074074840c40040213400035000700c0c0ea4102c00300031184e00140040c0d0802c896003083d07401504004019076070100c0e00a82c400c0000601140b17644840c0e14052a04812940c0900030303036004240031a00c60b4150710b8070070aa80e441d64080c006601c0d900b40342504c03240207880311030101d011880080f00e6403000382c01401c0e031140020141e9003404c0541d10b5050500c9003003503142c1074a8000181450800860340b10340c0000e84425503d0b1410501c1d145c0200d50703031741d00620200c01140713409800340c9150f0708444041010144101403030f20501c0404083c0340d4035500b05000344000b5508100001e100c8005241d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 190596375 1250 190595125 190595131
    0x121003060e1c05090111012906090d2d0807030f090f06110c03010501080106030201140301030312090f1403030115051c05070521061305090a0b0601050706061e050108 73
    0x44400d218441141c0300b60f4480c0e010440c0e26040c40300011a124450a007807280c888220a02406400300780d1191124100401c18508018420b1400f0f2210050680354030084403052075101c045c02105101c0b402c1850840444100384170072404003000240204204c00d0b0181c0704591282c0c555176807003442141c0944200c1c4941c05442002e034654030080260310305c500b0350160f14010060030b030b95900b4034001c0440d00b540e0090300b03c1c201680d11600c0810465a10140d408200c80901446a0440d41140e034003d00d5400500c0e0380140140e100d8107018240f154541300900c1c0a54010010034038010442d400d9601d9410900c10090100c101001c450000c03401001150325100800309551501300318500140c0040c10064292020050280181b00171381011000428200fa01c111140e082c51030f104003006000e04044c90b1024200303052506111030940005520301c12550b0140104c0426075070240100d40314000c150010340090300f0602d00140300092009224540105184c20050316a00ca60040d200400b0607 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 190597625 1250 190596375 190596403
    0x90b030606060d062d170c041505030607090503060903041d150604030302011e1107120212130e060d0c060f090306060617012c060402121003060e 64
    0x24000103849250250080c10801600000021100d4840203008000200510800704524003081118545d580000c11a401002651184284c0100c4041110303111500c03600c1e500d0085413030300d51410414100603003820141c0300160803100c4511300074074024140c598501c980c90180c09080c0c085440b01c10003000321001d4410800d0407006101d400c1d80c1c01420200d00500043c20135000c4504400c0d03e640c3da50081000314026070010601c04036403900c04e00c4000d401d48041101c64940b0a5200c842c100a600391500c02c0d41003560464116007240c0182c3c1003011140c07542c20007003000101040e415110064940035500c9425081c03900f40d50702c5040c00b107030090300040a0801030a803903080200501c9050003024402c46481c007001502d0343c80c1d94440c1940e80030740001000c102d280c207140c9010380b5070b0b020850040c002c1882c1c0c099410010f0b45406c0682c45280d42215005d83d0400004040362101d404075007502c00042210032452501d502006504100d0340800c80b0303594141980c4c0d04240074000b60100c80f200807 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 190598875 1250 190597625 190597633
    0x102191d060f07020a06020307060c0306060e0918070f0603051302010c0f03090302030303040308041a0103080f0904111813020301150804030201381e04090c03050106080313090b03 79
    0x18410401003290042c0a0008070504100b09020050300c5440b040d20003814150021912017090345081c0e400e03200b8038040341041616040003001039591005d500c607200702041c4e13100805912042c0140661140b10000308416100f40080080e011540703541e4101141c143da13a04000e1900da180216442c059009030283c00030310502504008115a5056080c08a11a00300708140982d031b94040307410354004603019404a81034404000030b02005c18860940300d1500103082c4490744c119070311354526003d0803404010012001c10510240e40300e50f07200c0c914014000854036111340345400c60018005804455900031040450400c0054146009590589803040a14000ac3c1c8400c002200c1107140140264215900c0c0c0c0d10703800e0042c2031000069030218409500c55084144510201c801100c800c407030500482c14a0114242c0d2108900316860b000000c9a0103d9280c40f07504000103050580e0700f003d4880e5181c0380000448600000080c262182c05101d01d24029580707084000450f845034640301d8250300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 190600125 1250 190598875 190598927
    0x50f0702010522030804051203030403020607120e030c1e28020d1a04140307030905040c18060809060703110304151d070e092413060e010219 62
    0x1c0200c015240d0343c0c0802d110040030003841d80d405008100c0359441a40e82020002e001d02250070064000807441031768200861070340c102560025500d11006100344c1c1003291040c0c030f10061303d079240c0050880c90045d0f822a070725041e01401407034039a072140040c1001c10b8a81c030003c05202c040800d03041018000369040c00340803403295485029141c00030b07104907071080040340e0f0b40e00012200102c55820010303034181036149240c203150032444010251098180c070790080c0012000aa030000000c4281e490680e4007040140301a003040e10300ea50851088440720811900104002d54030030001481800102c08443c421707182c40300d0540454400d0a1403005d90340007000040d0104508080b14180000385070800283c0c00c0c0750007100102c0149444109400d81c01c110341c00c102e04083c034601150040c480c0800381c0b0b0341aa00c01401280d20035642e40c540742e4210b02c1380014101c8c1010000d1300b07080035007052060100700c65107082d0030f000354410328000d000c001c19400540b42082c400c101c01158000750100c0c0504201c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 190601375 1250 190600125 190600127
    0x409140609010f0e0c03090127030306050616140a0204050f040314030f0106030c0e030d020a050c18040f06020d2d0c090603020702040b0307090c1209050d080405030904050103150606050f070201 85
    0x1a10080c41d2081f20340d200e4094a1034001a08114190080040700018172440e0a20b0010159002030380001e01c140c81c04c1c0003c40e0608881000407064036849021075841c2d50900180d10b0800e001c5800296105140c0800c118900d20b184040d141b090380700c1d030756503001023103551500079580c00195088440784031180014480940242d021550691550038548800b40c44280041d01d05580c05d100280141c0091a0800801c03504000c1c200111a0445450010301003040d45010040d00090000d818840c014030660244901d65040701d00342d142c6c130402072002c0281010820018203c00d40b2800355005030303000d6100001442e2003800c11005455407610039191030414114041c1d000440e05990180e075a15032007602c1c0e6402c104480c0248241c03040803801264031072001d00903808480344c41424074100480c040010b100841c03403000120341410043d030241c0300c50622a2071402900700302e0307030841e1400b00040240161040300b00d00006c0000001d000140c0c4a0608403082c0c0a030803010f41042409108400c019 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 190602625 1250 190601375 190601377
    0x801080d0c030e012601150f0c050a0b060a03080d05040c061106070e030705030a060b010207061b1e0b0a0b03330c220303030612031709030409140609010f0e0c 70
    0x45c4140c0d440040020a8102c400c0c4980282a84010305080342e2042100b411034003c44100308034220b80c00c00101e14211070307c0d01606d420a641005041d0700903100007072015901c54a090000d940c00407409501d90400e004083c008001c03e8509031a20030b4041800140305101d00c4005400213440c4016143e06c0e19045810303911104406101a41402100000b080e661420840286036034000c10022402c400488000381c14003c0d140c20a0080001000010486d000504180d11919601c1348400c542070b81c0c2a1640000e1712040b8074024010007002c410f200341c40c0481c0e0402084c4250403020f0f04c0d52200500386141c50303080e2808070b2401c84681000c8941c14003000b03107400b50f809104544030b0b61402800f014501c00070b101c03015003c40c007001e20140c140300b450307410b10843c0040e080014000301d46540c251030240492400c04240402d100c55600042e031040c20620943c0c00505d4211020701c13842d41e000341d065a01c072104071211030080140d0400020641e40010800302240c24401000d141d0780c039030075a80409 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 190603875 1250 190602625 190602647
    0xd050402120a1a070c050706122a200705130908070b0907050405010e010b07061b020a110306040b0627070c14070e0c0702031006060801080d0c030e01 66
    0xc4088081d88400c00711000b80038a000751480b42640042403084903807607140d045400f900d164100030309500d0700d0380002c5001078941c0580b00541040b094440e0509281c4020f04a4041540c600c0b1122303101c10030385030b1040303245540401006d40b602841c0000c0e4214169051502ca10302854980c08840100300c0c9007000400d00304020700c0c404000c030b6024480d48a5400b030b81d00500d001c581e100c40d00310401242d02030900c800c80c0a00000c540a000b59413428011650941043c0103500c440040080e004c0104403803580040c003024548204041c0701640c1030350103522440c0302eaa080d03403020211008502c8915001c14150310803584000110802d1f1250403c5c003006283d4004100070f102c000c0090101180c1c3c8945401d841440c10b42e8030521401d001c0c1c5005405030f04c0000c151000d036440220203101042c21120085c0d84a03d8020b0616141c015500004c7c0c034100090580c0020f9a282c402c1c0840c000354480002c0e4180e500100440f2841a68060215111a04440c0140000352114400e11130341d889140d140345 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 190605125 1250 190603875 190603879
    0x6121501030e10180b0405070e0c09030a12021603151805070911040f0f06030c02030702030a030f091e08240105090402060c010c02010b01030507140d0504060e0f070e0f07050d050402 80
    0x603004d001940c0b035111000003500c00351200e610800d010461540141903160340521182d401384d007005094000300360f0307440050000801a0740800f803444541403003082a45d05055400e400d81c0e03015907aa00709590044040302e2119286030070324800c03064840c100050005410f40c1f290013080c03014900103c1100070502c5c10b03040000c6140802000070708105521116010301400c1c1c8060f45828903202010301210301c40850390381950410302080d0f000d6900420307880160360701818030403641c020b04081200d031201103801c040381c41030340801c11144038a030b071401442c19070311000e040301d100610502001280140710422000000341250040c081d60078854105504540b0190265090480c3c680e6620b00b51560040390200603950351403c5042d5680c540615a0007002038103084072240d008448030013643c42642c0300341c5801071b00ca0003c00c0c20401160300075240140c0000c280c030703001c59142840c641c4030001d504c20040e0040440d07011400702480181e52500991440c0c07501850b00b1500304401c4082e01c80104140c1e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 190606375 1250 190605125 190605161
    0x7020a0e150d050d2309240c07080c181305070b0706050a06050a050d170705010c0203040807060203040e040f060e071d0f070c0803041106121501030e10 67
    0x4040307448800881142c2ea1140d0054000d4007060031000b0322900c00b4000380b48000ca8601074000d101c2002c2c00440303400840030390b500d000b060402c080150f4070a5824402a07000c0300000740c40c050300940800d2410a0310b5515090320030101800040000d01440201011640b54909001c10f40360880d031080f00441d644078100f07a410055940705000a660428802075800c1d54a500170006103445610801001e054122002c440b078508150201e8104e000300c0f2002000b481c0c0440344240c1c0c07886460f01b80c420f4213610034002e01c0070140c510b400a440e07403c1440b4000152003440d8000c6540c60011082c0c03010381d0350842c95202c8507a02c545560010310200d90301600c0403039076601090326103102840801c0c0508401640300c0f80b50064503540400b0143d0080403440882c004000f0720841c154030032900d4082d10f403c02c203200d031691074508103e10381e071401111041e030007200000c0d0300a03130a00c0b00a943d0700c41c2c0850030142070f407100100019429280d07101d0342003010f50000100c0030081091588911034085180d0919 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 190607625 1250 190606375 190606411
    0x301050901110a0807140307080f0603011406060d09080403110310020304050c01210e030c1e0a0303021e040305061008060f04021306050a0f1a0708180f040f0b03060c07020a0e 77
    0x906447d0344155580c40006800004110240c56881c10b02c40c2c003c035041d40200908629120352220305c10000d03124501c035100002d059000e43c50f10f6084807580a0b001040c039544e840e80c1b45408001420941162806401991044600e03160b007032083c0da02c126045030203842010b504600442d04080100801d8507040c0000302c3e0074005650600c107002c021380620004554802034404514a480d40200d642e809414805510841740200480d20b48040381d407600740941c95040151116aa01200e050b1007218080003140001c02d2090024000e4041c01944a04602c2c080c3c9480411361034440858000c2c1300b4002c1440420b00505000b1005040c04080003400106030741c41f40c2c0014080950360388180000d0310464400e00910440341924059014010402850300740150750b80c0c10345000c0c00e20320b808000c28154401d0019140c08000b6150000000d00401084c00383c0150000140004120217009104140018000c01041c07012103c119400a00c5d441d0322503d40601424444401802c05045481c4003c42c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 190608875 1250 190607625 190607657
    0x16050c060408120d1b081909170310030b0907090515010e0f03030c0703080714210c0a06050705070c08010204210212060f01060f020102040506041809080d06050301050901110a0807 79
    0x11034050b50350b2660307507065682044801d00d54010345c7d03130180f021001c2c904145440000e420030ba03100072042c48144000c0d2070f56103014584050f80017642c406040b000046007080320004c4040703080b1040c0ca8104008010f562901c070f1170190701d05c12100c03056021406114040040307103400c1050f10310302500282100d20f4107050030301c0035040c00090740c81107584020200300c11003000341400c14030700e110318100c0003051000a54900942c009103210854906d038407000600d40c0701c005041c0305403000705400038400d102d035003400b14000700703035920030407082c1c681800f02c0c180400d130100c042c0201c0e001c441d00c03004040c6188814440b803950605403034004a0b031081000c0e07480610820b081c0000c1d4400c6074a8037884500b0340c9800c2010700a104504280d03011644100824042c0d40ea8850548056410564040201a02100c6000010309401c200640681404512250b0301c0c41e00d43c210b41d064560071740080c880c54807106809405e0380e801e0096040010f6090002c0c842c1940300343d86841c1e01a2107468a440070001e5000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 190610125 1250 190608875 190608911
    0x81b0618120109050c0f0d020105031e13030201240b090406030c151106010b1e16060222180207020105070609030905090702030a0207141516050c060408120d 69
    0x1148110740d94540c10500140201030001d94608002506c112404180d1003002620500440c07500070b042c81030100c042102c028001400c00002100c003013004a484c10b190310091b8007844504000c42c010340c00d01e20740c9040111102c40100c090148505202c1d01c103814808050700c10f400241440b038001c0d07a689000408108500d00c0c0340028840510554800701e005c1100511622000c403000c0d8480d4001801004581051402c8030a1048111210b6402510b8071044480900c2071807450002e1215000741d00c410f200e841e90082510040c0003007003c840c00700424064175018030b28400c15485680764041c907414404107400403c86544140b401500e0b004241d41c8080490386003500590010381c0d110028402400e1030305105070002010b000860900d45032200089d6954800e01403401d0110000c1003014094983c081c40000625402c00c1050b15202028003c02c000c18a10300d06440c82d00c602201c5032424100102140c055610000160080c056100c05455a9503c080002604195251150007450301000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 190611375 1250 190610125 190610149
    0xf1e0102071514010509010b03010b0706061d100603110906070807151e06080d0c06150801050a0b0108040c09050721090201080603190b042105040e01081b0618 70
    0x100c00080e504100c0f0b8102c681d0024141c00250042c41100c0061040d40f040d030054904440040c0d003071583d19480c52a01501034541c59001c485100303147c81c0322004228103060058440c0c001030880307030f4072141d032042c007102510f20130001070205e103070304022464840c2801d82c0240701007402122484d11303044055880c1e80b00c0d001c1d8140b07184003440d0b6508030044c2c508940c4101011941895a061100c40e040500251300c5403012a8920203104103c02914200725003500004900007050101c0480c05903681040740c081c0038100c50144000380307001c06081296000d8503581c1d024542003105244001c2c00c000801c4001c0c0000742070a004c2c8400510b504100480d5a03540408802c5681d5010601c120648009408030300098681c1e4881c0c2c0060680000e94084000c1d005a9240c0001d52008241c9840c10011901d882c02c0c8559889440380e2902e003011780d038001000304102c49949171481460703a41d54501a44915207094140c50a45924451305850310b41040a40780c00b900e14120b00b8840c4001c1e0001410280b419 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 190612625 1250 190611375 190611413
    0x1406010c08071a0c07030f020c060414040e010501081605040903092711090306060411032404090602130b04060c11031e0706090504020301050a03170c1605120f1e010207 74
    0x400d17004141d40092515110f241c140000c00920040000042042c02240500d030f0444012072514402c558503600300c202c01c1c0d1640402000b86584890700d5580754141c40301548458500c0080c00601d601702840303010709080e01540c1d90351903d4180f90680d1400c11910008004030b002c0c2c02804428a01d9900c00c10204040c0e050b10781c1da0b55442007003498140000140828816444d04240544018000e0b080ba40d104818880702c94103130000b40c040602d001c08940c40b90350490310f0000007804000e1198010105050744201c0900f109588000c1080c03d44280d0041100103012820f0600010b0540103003400209001810303940000c01c030101c60001540b11a03070b44021548481010003070343d600081d0140141c10305840075480c640c10300003c244099514800100320302c044100c207590340d05030b4000756045400210282e8600b5281c00100035581e81242c01490311518840c0d012002c9602c0c0041c5a4075484141e0340034001100307020f440300705401092144e502c0b89540800032980061541110030b0f564082c6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 190613875 1250 190612625 190612627
    0xc02100e0307020109090e070314030c060f040515010b0702190b0a02060708060d0507181104030f020109320f040e03040915060804110103060b0a0509041406010c08071a0c 75
    0xd0f40001404d160f019070107032240904c1c1c504180041c030030107c2e000d001d50703800c40c65000d6003813481c1001e0f9140d031040b009100d04074061303282070011ba0b010241003140264018002c5842408060720710380048842842100f02c680e00c00c21240c801030401c2151000e0a80b180c0161040155485181c2001035001c01c0c10f040045e04044104401c0b20303000802150024020b0300d4541041842d40d0307030940d41e08103a00a1202460401111082c40e903a40d4010354bc2480200c0030690304c40380d0b01e10340110103094085040740400e4000002045c03078102091103d0058021203503060140703080c801e2000690058003482504011404d0448209440e01c2c000c0340301010105000b103a40754940400802110003003811421814204282081000d901c01c2c400e54216030041c00d901e0f802850200180c0040c8140c0e0301000200308041140c0074015080f0740078040910058400b40b1200758804500f10505c2005c13901c860100307442940400206024074090508a0710404078016001400803000c244800700b00ea8603101040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 190615125 1250 190613875 190613887
    0x120c030705010c0e0f010c0c0512030406030b040c2007080f07090e0303040503120c090d0303050105030d09080d27030c03051e0c0907050904060306051b0405090a0c02100e03 76
    0x40c003449210080c03800c0e450414042c03241303c40068080e03268020828104803400209100344104040c4c04402400700a000c1a0109019405107807244c025100d030201091614800001a050070302401d20305001c103546541906401d070301e205048144000c40e1500301c3c807a0031000300e0400001c10114003c10882002014514a0310070311109440601d030303038000650000d105003c00a030300001500c150a41c00e6144044554800e00c41d40403c4c0602c01c034040d803004a4840120505400d0350025068810981c140c0701104140c100990b0310041c0303441440ca0f140e00444950003c184035401c9010001440307a00045200c80e25a00f42200d8401c503002600d6841b21b4001c10001c010003001444511200178001e0603d01e60184500350301c44a407406e0042c00317801500009000144168100c0c0c00b00c1c04000c00c20801c003905c03810300c1320040001700c0b2081c25100721096a110010122003c1c1c80c111a40100f85042c83e030f903100c1b03444001d41030328552001035114010881103041914000c60046070f800d0001183c03258 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 190616375 1250 190615125 190615133
    0x50109050a0c021203070509030a0c06080a0f0227040f0603060506030f0f071e0806040309140102011103040f020612010b030609131101141905190806060307030905120c0307 76
    0x14080010303803041d03600c000e00010100000c001500d82c000d06d9810800e0325010b00741d01003403d140c22140b00400c82e03d0202400314005401120703460150b03140d020100603120754010098202e1042c1403068081c0c030300000e4100441d00c0c452072400040d640142001c5000d1040c040c0103c291800790700b00300c40d21615582040480d080c1041880d64008985004081061921040c0c9407958000d0166415000890b07072070643c100b40500b03500004092280c210b54252901c0e0034024860f40309800760306210015007400314095841401006c405040306051f0300d1441d221641c0f010200b40c3c280008980007070060044000c01c0e038242600300d009120321004203590307140407000c101c11420000c004280300052415104080b5a104403d40d140282c01c0c01c1000300c1d0009540015001e0148010407140d4402c10301010615645c8000a0407040445018032100720060840659000104403803d6400c40010700001d40c400784240c22121443d4021400d55100b141b5841d4800c200782d1000318240388691001403884100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 190617625 1250 190616375 190616381
    0x2d030a090503060c0702011710120602090103051f09150f060504062d050c100516080105030102070302030306190b040608540a0f15020c030405040905030d050109050a 73
    0xc600501c3d034491400c0c400346e001030416018210000410003100c0002215040d200080002504404420fa40519014900207001e54001c0c0c0c1614000b0381000c012415905e1a41c07000070811403034000d0200c19030b049c1007802c0700030b04461a4080448021b10800141c512014218202400d1195615543e403802c00c4030103400b414184100000c110009005448611032040711a62888910303e45a40e440000310000351508000003c0c000815280a040c01189107178407030f080d110306000b620341c680642c2e07039402010b00b00e01511402070003603081080000d5080c50103814580c2c0804072400b01c00f4025841c0c500070340d400c1d002034010070701046402c0d080c018440300c4980680c0c00400c80e002c0e01034100780d100d0301b04810480307005816180c40292100070700c011040301200011800f6010101c810400041c203103000075a000340700513289016a81d03446c000b80200c900844140c202c291006500c0d05287c078042c00000c20100009940c680000d00001003941d80300e004050003482c6d0715502160908012000300c1c12 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 190618875 1250 190617625 190617631
    0xc0307112d06010b040602030a1d041d010c0201110a0305190903120e031e0a030207080705010c1e080f131506080d0e13090212030703120b0d02032d030a09050306 71
    0x651340c4140802c016160307000084410300c240c0c40c41c010600a8010410740c101140f40090035902c1401e2540006450312030318000d84400344941e00900c94090003034402e070300301d0380680031609900004000706014107000e43c000c175070005503400c2c1ca080740381c024100780001c81d8484c00303048000542240d038903901a640c5006140c0b091440f400a14074003020402540c440e105a692441e0070410046072036894140240e068914580c1c0005142d0313650785440c0741c80c5008041041401d000b04048040c05c00300c041c0403040d00c500503001900d0307401c070b075031204555690300d80130003021240840c4240340c03000001082c0310048400003000e181e01080303203400c2c2001c550921a80190030420400d051444011f241d40d8400080e4a011005e240040c540d0114004101c8860240045142e140720019950301015400029100280c0304c0d0203040107602c840504212680030543c401070740c543d0211540300c1c01c3c04240e0b0103540b8965081660080340040b50006035095801041160011981d0500101f0846c2000d000c0154 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 190620125 1250 190618875 190618889
    0x90203070f06050703030b01050d020409050921030c0304150204060c020310020a020c0d02060702040603030206011d060109150c020a080304030218160f11100519050c0307112d0601 79
    0x441c0604002c0c000f011805000405800c140e10780c41c46001c0c1341d000b481114000d11401a003035549a03281e4046801800c400d6941c03902d5841401c40031031b9618091243e0082c00c07994083d0052542d26541420300350b54001410176035044020141000c03000ca401d100034001424152589007071981107004040c14900b4800001810134010044000119408030f00004040402c580d12002d81c0c201d400403a41d280600440290801e14140003c410f040c1c00040e654100c600d40170300045140540100c2120820056031140d0209205a0041c01080704c49248101114400d00e00f00307445240d140c0005100f06515404080d49400c00901401035050144008114006813070b261506810202c03590320703110040800030010030038169400442c05129200c052940c3d00020105c0324441c0485003000c1c024a0280ca2410a03007036200d150f010480c01900035103100c0c0a003584100c0c1960340d50002521100701451001000b40036040031140001c444480200f01040e0b1141e4030a8036008030a94107182c50010f8000103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 190621375 1250 190620125 190620149
    0x90e1b192006010510020a0f060617150a050c0d1b1713080a02071a18090f06060d021201081507020a08030601050d0e0604050c0901060c03120b0a1809020307 69
    0x15400c0010300b050440724181c03600940e494640c0c0c4206c0c20050002e000a082260084621040c0701c1190060010b586404140802d2014030413100c59135940b00d8a5000340703900b41d2000240c031200160303122a074440c1e0086412454006107902c01411581403500c03088031a4000a01c003544554005800600207414030310250007410311801c20031503003010a00042c43e0040000308038080510900480f002060081001c0c02170440741c50000000780c0281501d0038829400c0507210f01e00345800d00b50300d4040e2108480d43e4407191078810511425038460700d0740c24021602000400a401c0a4400090081a0040117002d01a01014804120b42c0d4050159400c642c8800103400110358184100c030b42044c03090074499a180361022414014013480070380c0c103845020f21400c01091090100c6d4075506902c0482d0b144101c2e03a215030094891101a0001500150a107100c40039003882d541c3c01009a2100240401d000381d50700d090000c003038004c0e100c80715141601d500f58642142010400400a01491050b407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 190622625 1250 190621375 190621427
    0x1090c0903020f040216230d0906080703050601020f0f0304170313090c0c0605010303050706150b0f07020d050d0c0606050402090607030503040f080f180603010303090e1b19 76
    0x3915443e014405548101d50000d034503070300a50204000c1c00700740e5004060080d000d0751103240320f024031580018450b490280c0020f60014900c600f100e0001d032003140c0c840460644038541e00b100244002004241503105103040e0003c1040302700321441100e41040001c5959508050411410f0003c1803072001d519070050100d41d140014406000050700c140310340018101452200480c0c00c034240d10303809404c4a240000100501d41d00400030144c250190b5020300460810050081140480b44591101030f00c0230301801e0121010f850050020b2400181001840142c4d6110030b41003a2640039010049000c40c27261804002150249000514003103a0450030128010301045280c45801802003c206000002a04001400c5920800150054601506c5101c01c00a444081d0301020750b1600e403210403144054903141010440f0705a0750305999929510f86080c214204001025090703002c101e40580782c0e00424003440d0050f014503524078400004248404c40d01900e51240d00d030014000c3c07c0c4034034034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 190623875 1250 190622625 190622629
    0x241305120405030f070e0408130306020406120b09010501020606010c0302011d06190605180405010e10051905090c1009090e0109060605030a02091810090804030506010501091508070e061201090c090302 88
    0x35587c0d0040e005003403d036841c0001c6c1118240300700e250308000d0000340f001c0350201d41035601129030300c411509000304000f480d03006410016070000c00d200d0a80141c1c0601c0015110b9449200000d10541c464000030603c41840c03843c1d102441d100c1c03158030308a540420204480b00342c1006810700f18503402802005441e040001144000e0300b410000215030080c2004101048000d60146100d0f0065805552040a18107101d00103000180c406103810154116138407400c440c1481a82d0140e2060b200400c0d42483c58420700400d0044805c862040c8000d4000004900301ea50196100c5181d038140001500f1036140b81c640704441c89500064020381c40032444400685405400603041551101c000080c5203588070b0781860080c0d44000b192400e418503003130b0010484100e003d8826644642c00b500ca00380e0325040110b07010505d91042c0c041c00000010010010350080010b00d8100240e80382a001180ea0500032410651140607002c016272055801004529a20301c106079588180e454141c0e42c0a1842d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 190625125 1250 190623875 190623899
    0x3110907091809020a050306092b020703020f03010e06010f030308010e0c090f0406050a0b03041403030903030c3a050a06050112020f210711241305120405030f07 71
    0x248000e0010b98a141034004d65036a0003100e00200720041c129005894000b151079241e640c90325808201240410821400506403840e45a212006a00400300c40d40303035800300590107186280541d0155a40c00c0c80e11035011090007214040d140c0d01044030f84161451800914000c0143e204a030a04910014071140440000032115143c46c12182c502510122100040080490b0303400103038881074060001820300c040901440c4207a01074644c13420b80801041c009500ca21048a041800380c204100040f21034481002400381d4100c0060148010403450001010b00b8210020480d00500c41a02642d041d14071030003040c0d0b001090070400d002541c5064006440d01c803070070005926a98001c51000840048031040d00c82c07007250f41a0015441c10501d206080c2c9440988103400000c440c0c440d19802000005040001e844903004010140c1400e0b00d011b14031204081c0c070a45a5501080c08640410000c00c0319107400884400400c1e515803400b020907203490b02d0044610341a400c003074010071003948864 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 190626375 1250 190625125 190625159
    0x80714042d0b0c0a0c0e0402010507020622090f0e01060501080105040c110d170a02031b0a02101104090605030f0604060b0307080703031d0603041709040e070311090709 74
    0x29162128010748801c0040061500700720300b4402c0105940c150350300300060310030b02d45004110003201c0e603455003504c0e109944101c0f001780c0443c030200010701c0103003083ca00a1800c1ca03001c00110414510030440c500400d0706560205000540f60462a0240c00c05803103185100040c907802040054500700c0040c001a105100c1d0380d11840da40e5215511442c0990140f0310407414110a0340c280080181025000503400118001c2c0d0860200021303205040610880703010720140140307405501c00050185840707034480c0901c141180686130100c0340c0c0d64214081c10749441c5044000ca0303111420851400106d8005500c203a00c00c1e0b100089482030458081459038000780c2002003c9001c01d0100b012a00e080310f203070b00060300da111b43c0c03400105069012040344441000001c1d44419070b0825410800316010944001c0c0c1394a1078406c2a956a0080c50000e060140c000342c80401e2a032500c1600d00e0400030705a10903280d1147c4200001140d260800020742e1140c40d0b0304000e0026800d0803d6400001c5c148 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 190627625 1250 190626375 190626419
    0x5030d170601020a0b130c06020f030403021e100314060a051806010201140f16080103030e0111070b040e0405011404030c1b050d200a0803220806010608071404 70
    0x4030204038103920a00000310303015000814103e007414565a03007501d1000901080e030b03122122240110714903201140c54500c02170801c1c000c0d820300f42542c007044100c00d51902030348d56665070001c1c00c074565100c03524800010801345c5c40018111100d40c51030749002c2c100801c0c0501c40c41d4140340a0000b0307030303610321500000c034401446c5201d03075650380700142e0040ca00000f151441000c034508000201045030a1540b00d50b104a100c210304405040082d03641c8003080c00001c000c00e1845e135142c03440d540b0070300031500c07011021000c030303401240d844120701c01d168007603001200395100c11b00c204420700809004112400501d41c6d140802c81c81c19880040c485484040000d16081507840d84403000750325490303420050000181980c03103140ca01d107024070400368804044480c81c0580b06005540d881e1102d84407080701e0401014625200440070340d421004c0d52420700c802902060a004201c4000030030480b4007908964650740034a0a250304080c083c89120540c00101c2d540c1008144903680000c8003071020340c040c1c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 190628875 1250 190627625 190627667
    0x140a020a0314040e01120606050102010b060906031902031303030608070f030b04060908120103031b0c1e08010609090b010e040804030201030203090a0b040302010b01111b0d080f0304120905030d 85
    0x202c4500c480c6101d0359102c240c2404c3c10740008a0380c40040b80340394000704c4c8140c07400c100d5a6912001a82078512002561b60301010034041d50b645070420100031340d8842103074205019140070380744034041282c009542c0403042860b0039019004064062141d17030003810f906002045102c0c908021aa81d01d221800003e0101280d04d010404000c840e400603508039520480045c1c03115082d00485441540911040e0000349820082080e4104030a0345115000e4000e14050b0301035040c03240d0044000c007003103508980c500041400080c100c0b807c1c0700d0b05028003040407010507202464140303c045080c040c1c206680c0d00803402c05210001d2007140444044950a00740543c586d907a4100c002d04082c1d000314041d01d440d070508100020168103520281076a0005d0302c59100c074080405110741d40380b96128800b0291421018066598a8400c1c946540148a00244e5251012011b240200f44c0c0041e1001c90300540e510040265107900083c82030b02401065009146c64075010400030428610344260aa032002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 190630125 1250 190628875 190628897
    0x904020708040801020f091f020606010e0d1a07030c18120609060e060106090b0702030c090c0403080703030605130e0d031d0102070f050f0102040e040b0915070c03140a020a03 77
    0x5000ca0070b450042030500003c540b160070b8804113071056400a0009445240b441000d805600322000d4068004040359000300f001f50b49403001540d180c0f041d28015544903030b0100340e600002d006648010f0030401010000c1c041c500307220001400751205088010180f26003400100060032001800b002140c1858040c84818901820300b00c0c010702030400050517003400c061641c500010000750490484059945064003a035a501d601c88181c041c495000b076060700400780b840e0701450001c0019400c450038001d8903281c0b540d250b54072000d075440058100c001c00d8488804200500c0c040481e01c105510142c4103025080401c2005a1240c2c4408500130038150b8418001c201403500561186040c1d850364000c550f601900d050009601c881003e0469081c81410340c550600d50301802071350200c82e000041d900321510b80b5900c03e07214260041c040107aa00c0790781258407507111000c000c01d0003640b8030340301c4c1000c2c2c003120b0030b0040c61800b03007680f00403902c0c20800000078401e41c00509010556050718104010f48 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 190631375 1250 190630125 190630133
    0x50d09111201140f01081906021605011a061602130e1c08090a03080408030702011e02040e060613050105070303020c010906061d0c0919030206070302060f0906091f090b0108030a110601080309040207 87
    0x2c0100c54941c1c0ca82a641c1c4e80c2c2b4001c100c8158003e800108003c0142002d080d40c0c00c0070841240305454101c0820301c4d07032001030700c0142040c0c000c40d84171418034000450603c039101c400034a0890200340300f010880310603514007492a000720b040d81c0c02201e000081e00c8011400d4802903c150320141004001c0840040050803940c400c1d8462500c0d1142c0450021081090380b85181c080e40150088038400d0452802190442ca4042c048031070009400c0400c0f03805902c0c2ca0010355240d004500250103064003003105c031000c24000c0c828040514414800001c0c5179040128003030301204c52592502100d4502130900001b00000400d0390700d480303412a645e8007141c10700b8511800045130340d80025080b410204251007019004100b46200d250b2140800003680d440c070346126991501940c08122941240c0151481280c43d02a030004000c0c10000115030301845d41d44024482c1000d03808100b41e50030100b20341c00c507d503220404941100525000704615418031660b01d40b00c0c80307078011491180b980001c0e088100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 190632625 1250 190631375 190631377
    0x70b0a0e060408031e070306080d032a02030d051e07030b0a1a0409050a0203160f080103020904080c06040c14060a0e0d0c0320011e050d09111201140f0108190602 71
    0x1040b05d4190a03207a04101201901070020303805408401d0049841201c01c9034424400c0200041d04900c04003c40c4003898a4002d010050b40801c2007140810895000009001d018890042e00141110181613003500c05071502048058000b50405043c42d0700c0307800303030781e076000a190a456038025400700e8590001074100040c0700e2a84180c0e140360400041140c04109680951b100e2500700c0ca4545800035902c00494051f4031580554020500c002c00500c050b0400f0712100e540103200303d5000f40f8018004503158030b4103008480440c0c82e0501d40401344848403211805000c20101503443d64240001c9910240c03107040c485002034090322203001114240f103418070119006542000013150103108001031040140c4003800701c14040303844c0c2e0321034001c00c0d0344022000e00c07102000d0b51001d003001ea241ca450720240222a4095807800184a456540d030b0b520b150500c21200c80c50000015120080d400701d41000c60010500c070440b10040004001108004c108150b80311000c00300b5040045040c030b468402 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 190633875 1250 190632625 190632661
    0x2040f061509140f0102060727030f02010e040209061c0b0406030b0f0f04030e04020c0a05030f0414040b03030a1103190c060e0f030f090609100302070b0a0e06040803 73
    0xc911003000c12403000740d00145000107582400b14071101038044802800034040340071840f03a0042e40940001525140314520641c3e5a8405031581000d80101c44243e03171014015400036a5501c250300c1e010b204668201c1035803582d004d4180d0301581404054800101076025190219400b0b0703010001100c2180380d07607440001c17102d00c01001007001b60345038203042d4000721003101c1400c4039024813000300f050f613074041aa140c41142d041c2e6500558201c080103200182d0415031030100b080c030503540c1ea03200180040c009041100c42c00c1120310b886038a01400307600056044030b0710700e006038a003880c01380781ca44001c070807108045680e0510518443e04d07080d02c9840d6109150100d10b100910751032002055500044081c1460700a000a006201104031031584035440c00c0381c2050300e40c2c4200064030300c540d502c002810f01400c0041066007400c00f100c0228070414034810402e400243e0000c1e04a0070001c0b000421a00144c212104000001d1f582c0c810680d196005423001d40801030200002c2c3c5926280c100400c0307 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 190635125 1250 190633875 190633889
    0x4060b0a030e10050112140a0203030a141201170c010923120f03030105090601080709060e0303040906180c080c09220e010e0d020a1a0403090806130c05010302041202040f06 76
    0x8019070b95220b0070034006e10b4409007100c2221400b00181000c10b00001c904840540003005180f4000300d106094a282c201c01c151010348000902c03151150625002d4118000c000b0701c0500c9200b007902161980c00c120703903014854140301000800340300b00d4041c1d004401904503148089a21040f281d40014507444807070444a0b42803048105000c071102011000c0c40c100e03001501c9402c000e1301c0b880015503101c03000b109c1c0c0d0000140d10141c10482544112104110198060243c91a00d0703241c511050035980290008003c20221001400e0b040f9000d20440800d00020300e0400c4036030401541504151080c2c003085441000c600d6070000071000440e110490300200444104904242031880314060714484180707070f030140a84c00844c0c0301d040c0045030306c843d010f0f0300507811020003200342e03880300070008082d000b641040f48415000c180320303804220084c00382031000f0b2988406030082c90304689410960b08241d041600510042207140007021030355070010707412500400c084250494030300007090554003200f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 190636375 1250 190635125 190635131
    0x20a030905030c030a02070605120f0402012a02030d05070804060c03022b110607020c060d060e040510061e0324180b1506070b07030902270604060b0a030e10 69
    0x641d143e0b0000003000c48020710380075140b1482c0e640909445d2402490700b40306d0314190410005440f4041805070940c410f205041c044070101c0e0308000090026225924400b19880d8600c030b02c4207502d010084030110701080d2400c20716024a99441c7c400f6801a486400c050000840156003094020f2001034925540c8186500000b4040c0703500c1c14040c003030500d0140200341c2d2a6040c2141c5600803c9251088826070028080d142c6264207109580c5c0c8100303001900745658003030101d1a0742e0600440c0d40103502840c0103003100d020041441c003c440d019071209802d01c4c0300d200503520342c3c3c003001c40c03503411203130004082d03000c00c0c0440c102c4000000911490388a42860461040c041d400060349440b01030340600301c8889141d40e0940580000804112080d5001e00207100d0f00c400207032002c04195001e061403602141040142d4041038a19000a00b00e800711948402400404000540c0c0603511501c03c94060144038500307640300c070452280c10102d5040544840308034203100707420404a0003084d1010350030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 190637625 1250 190636375 190636387
    0x7020a0b090a081801030c0e09060f0607052d0a0c170a06050118060b090310020327100e0d0c031d09090f0706020d0509041503080705060403030e070810020a03090503 73
    0x1d10303240051310204c1c0703010074541011b070300400f03208601c0203803d0400502020026101c0c50104078014a101580d51340c805010081400041e9081c02011130154140c4160010020f42c030040c1c0c8030101c02503003190480d80c4510402c00101e0301c0016600225280360340408042d210461225041040907440a0f000301d007414000160b1421124a10181283d50681040304944070890b4480740d00c1542d45066040d400510030b4002008140c0c000c0d42c101c55413040b1a00201900c460206030a020103001542c03c1c0c21130ba02c05e01c0704081d103006071042810014050140110000b0000d04055070001000e0f04010b50441c0c0d014040c101c00005441d4944018543c1685140c05401c5c10390311010f5451f5003519004115000541d5400000c3e180348166054603800d040a00100c01c1c40020440075040d80228a036900300000803c2400d030003880014000d1000e0309403458181005416900003c032124241ea1018804019242d0007103009a8110104980942c1c0c45452000880c054890f03014040e003540000610 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 190638875 1250 190637625 190637647
    0x140408030c0f0712020a0b010504200903030c19020405060a0b0711031015080d0905060703030c0c06060b03090609060105031f0e070e0108011b0c0201030b0103110c0102040501090e07020a0b090a08 86
    0x4210f0b803080b0400c0030b0581c9c13a5418841610456070350551480305a00419041c1c00d0b023a406884074120180440e400e290481c02410b1521300490924203c010f0003201c1e80095051601a00307034030480685000301b10901d08112256140320303109025040542c01240760405940030b00a0719000c3d492182d0131720410310181c0303100003820304510403510300d840361000559600f03016480d8102100d800810a50425005031819009001345450321f604014060ba2a980040d9242c441c2034050f202c00c0c3d500300d40b00e00d00304190f986404c1015200c03084903440440100140c1d500000d60300c1030745809000e07091940303103041c54039006010412400d410500a031600801c0504440d04441e04803101d02c4024030441a103d80d0300400071241c02c41c10800100032941106c0554000d8220912880303041c074000402c007610035100000c98000d20883c1d9000d94001030200510b690218481020700301c4440781200c28205004065a10211401c00910244240c0c4c0001c940090610100c007a40c2e4101003038a070303680c407103c0e2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 190640125 1250 190638875 190638883
    0x1109070512060307030c121704090b01021006080601060507050a02090703090308070e010906031a031c030605061333020d14031b03060f03011d01140408030c0f071202 73
    0x6040916403071440c0005035a0302d0001900c0040700c2e00203d800099074108800134a0b04880402c0c1641c00b203020018003948003103800f0081008013400140001d000010800080c10702181c425011300c52400d02400f401110f4012903100c0c1100c00c40d082041c0e40301c0d000e140c16400c22941280c065400600705041014450305500032903c000d21030307540c185081c8d4940300141d80d220b2814603040c0c0000c0070564140030142c020b60241199003031400d0a200d440b450740d4000791604800384540c2c5902c18034240d050090707030f0b0035001d004043c1c4812a50f06003400240c0d0f81000c00340360180301384c2070000d5040c0ca200c0500c00080c20010310456541006114030640500060b558010208103400090402c8480240e801c804400390783c0903102c500741d03141c003400c3c41c2300c691251508068011a4400b10302c6d00800500d40d001d00c581019480520f00804060a54050250071a2251802005800d03403c80030000040c16000440303900070700b5500e1064803909c480c2c240c0d00b4a4010120010600203040440c0440290001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 190641375 1250 190640125 190640137
    0x606060a11121b030c060f070903050105040f05160e0c090109080303010e040519020f10091203020a12030209030a030c0602210a1b02100b060904021309060f0605030f0411090705 78
    0x2903c107030410900700400b9503a034813800031703041401d40000d0003080b0100e10300c0c04001d800004603c0d00405054813034031202c0c00c45000391400c0302d00980e1040c0c66420028280004904464220340140c00185480d00d08846100000e06200601800280d41d00f2140e02800824000d400b080303007203c3d05c075a141d001b011004201650305569070b1007500030340142d9020070b00e008030450368060030a10f0425a0407007400070741d90301c0b80688401e0003800b0502013091042c2c01e0580300924044d5008020103025401c142003034924000c4a541014010400012756480004044030250b0f81843c1c04100080c503824240d009004954605226205150b0600413080100d9621401500504401c10280c220000c19817410000d04800e00c0c00b61b0000c142401402d0f01d1036000000054002d402075152a007804000b07012617021058183e01000340d07c1051041083c03e00c2140c01801240811500e02d0742009405803403800020a110300e40c40803000001c081211102d528030342c40202501c0e04442e8141302401401c1a0044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 190642625 1250 190641375 190641397
    0x40b0c0708010908040303030b0a05121b090103050607080702071e031e110409020a0902160c0602030c070b0c01091502180a050901030204111201140f120606060a1112 73
    0x10300d8082400c020601c10000700780c0d132085101c0e14092855405502130040415041d5104007081c1c800505a224103000000714941c1002520104400c00d080f03070126a07800e900c882c003803820080103000040300041d000d070b003100302c42c1004803560361951412460800700f50010b40034400300b07004c03607807101201c65414029070344140d26403d110f000b007a402102c544c11080b009442618120010341d12400c0590050f80c03541c2c0041d042c030344243d4542d0b0808069901c10030300d5144024058080d00244540002c00304082c0c10310b44061864602d05180007559a001805030440d00007000441144690007540007945a9a00c9548401101c2d21a42e2141c02500440194419054003400800b043e00c0c050380c10030140c403002030001d0803a90130341d0240401030100c0145189840f07010040c1108a04104800c54003d0442c052103040c01c412190038856202e40014280b4000c0c2060700e06d034030501c4008a4503940c800010f80f01141c544e0340c54070044a0840c42c1203010320180c020a0300e44105580014004c0c03070340041d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 190643875 1250 190642625 190642633
    0x3010e0114010909150506031503010e060f0f071b0501141b1608042402150f040605070210020409060e0105014e050906060303043008040b0c 62
    0x80c034452001c40061052a032800510302d45010302000320641d2098501040c0d0745962030540d17440e0b00101e0304550003078039403032200074260150340303007a1601340a50034407000440d02030031031402c4c240542103406c01c01801c401c3c5800008000034200703510070100c1c528105170600d1401250a070301d05102d8001d107481c0300342c41403408003040010038032081e4503100010194212900c42c80c15030035812603115410800801c44040008001c0022005941d4071059020000c0c80d0005c03140100548002e4903107052201d8215506048004005044a4241c0741e03c0d44203400c8032010800b5560b503d001c074140328445540016040c4080b802040b40c001c04e50180098511200207010540d03200c00c01540c2c1c1103181c01d40ca003240410a6081040c0601d0410040c0300d140e42d4000722442c00001c80d620507560400004aaa80d00e5610000c000031034604004040c0c000c2806c1d4041e5151a040618500251003107000e0700c6182c00001c3c105d805810388000700012056000300c0c41c0c0d504c968440f8040b44047c0e0001c1001c01041c46 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 190645125 1250 190643875 190643879
    0x5041b09090b0f01050303040303051c05040825020f06070c0b21010515041806030807031110090c0510050f0403050604030906020d02030a1115010e071202030c0301031b0906080303010e01 82
    0x40f041c844076058404c000d00039418240f840c1d0f400c540075030200c1259200310f80003145c4e070000d415a074000c1501652090080e80d8407100e003000044000c0d400c404d0030342c0b100380343d01103801c015072280074a80010000a5030140d07528495070a0100c0703410b80c60740c841c405950b0f00280448007120032665282c03c2560040010005903a0780080003e09070405411500b4100104410802603203003a9010503a866921008140a0b0703032901c03400d146401a1f1020340200e0184007c071024078074180030311011030b0fa05280400001056845044c1c07981b4035401018016500c24a2600c1d1960003082903485411140030010384d100e4076850055100c04007031f40c04501062041c0804a00c082c008101212220040d174020760a280c40100111203203454840da10005005202c19400d10401540c0014003074642404100058100004c008160942d18002c0301006032061084c0a612400442120b04494108446801001403200d03540c40c03100040d1302c01450305180600c001103040d00440918100c40e0352460f049296a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 190646375 1250 190645125 190645141
    0x60e0d08060f04091a040605070801120c0501110c190510020303150405060d060509010e1002070b190212090f0d050a021507020102130609050f040c0c0605041b09090b 73
    0x800166502036011560507941e02c031a04099002c1504507024024405e540031200b00203411451090724199a000d460320100921950440740483c0100b2845e850003001025680322045d03191074502840d410044069027400000004004181c0d0b0320708002c0401148140b00c1403a00700d043c1f214464940101003004081227001c0c00030040d03a1050100d6401c001010038030030208801171400071320456200320003851301008a10548291807040d41498000a00000340a45940c03400380c1c00c0340748450b5070340104561000103a00f01c40403a041115403002000160042c503011029004841e88030102d54800d108000d00554000381c2841c02c44010b0040c0c4644002c07200045401c1d104c2c2c00c210401617801811420301c15061520a29802030f80c0d0b2000508001000c00710401404850340101c000840500b818080c13440c0c840c218402c109411181008260a2060040e1525030801e1780505a00da82d0b0000034140b08000d083d0100107411079622040c0c003501c40121710010f14840c0da06590b49900c185c0014545 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 190647482 1107 190646375 190646387
    0xd0c02011401050f010f030e07031a1504060b091e031009020120061603060b040f061715060903160b04080610050a0501030b0319060e0d 60
    0x1003070701c00200040701901a00101e103c0c01d00198800702aa800c0310496003103107150305001c640c0039002c0401500705030303c030390000d0112201d40e0b843e11640b070b40c40d072507403403003085100410b407a03e140c0c4500703102c1101c3c418064400018410000c0408a190003100020010820b00840403d81800f0003c0b904040540307500c69010f6441d441c40f6001c41d070f00000d9549409908604e80f04012481460207607450030042c100c1a07a00384113a40c09508540700e0f40082001d4682400095501c1d40d4992510b010501c0c50302c10782c0002100a0f220350040c03d0385800c150301840d500803002e40c103000b1a004000085d449071a000d5410b1281d140410b503002f40241440300103060491041d078480d880d0005140c105140200340400c17a03030b09246c051180303580d00311071141503072400c2c030740052003500040110307180c0a8602c124220f2104280b1000f82000721a400414100320050142e1340e000c207001c0419140 = true := by decide +kernel

theorem cover : BRFrame.Cov 190467625 190647482 := by
  have h0 := BRFrame.cov_init 190467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 190467625 ≤ n) (h2 : n < 190647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
