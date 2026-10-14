-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1757
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:34:03.91179+00:00
-- url     : https://prove2.me/submissions/906a6a01-7c58-450c-ab4e-95e211d4b4e1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 315827338 ≤ n < 316007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 315828588 1250 315827338 315827353
    0xf0501050307260604050d0f0c03090b0306030c09100504140f04020d0501060801090b0129091507060c0809100e060f040519030807110109020a1a0d05040b040c1205 72
    0x802e403207005001510001c203c02203284140c0d9191040c4038035807199000b40c000d030900c44071210b00100002003441d08078007484030313442ca10b1000c2a40985043c06840b91000d4440d96501c600c80020326115414400300d40c096010001c20000754114100314007100da003540c090141654008010001c9902140c1c0d00540111880016000d8038140b511404414040c10000030869140c02859082d02d42da4003050f10440c4240b0010030003038034070661010711b02c1c442c405440d060a0462503026982d00c103407990700f403207084100d03105505a02d0318403c4421a03030f800002081001c0c07610744052b00e11101202d91304600e000d409981c03a0f00041c0ea002d651000d608501c0948042d42d078110b40f078009040003a00c291082e00c85c92000401e01400002e1a50201d070007516140714629007130030000c0c083c40d068800d02a00364109590800103840e1742c0030304401c2d00c40800842e1101d040400c2001468060340030124402c1341020140b2040c000c601072180c0c0164024400d04103040d40358295680c0c54940303040f008003d58031050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 315829838 1250 315828588 315828599
    0x6030c0207120618060e03030103021002030703270b0c060103060c020303010e040201081005091302360a0212130b0c031e060402161104060501080714090402210403030f0501050307 79
    0x6029a40000884d014408482120b4468504036040c1490b41a082d03400000103006600c0c0c00046240d0748240351004500c1d00005540046c6040e14000700004802e2000b1449910554031580d8940542040350100f03032640250010580d48800070322056401a1600c00030014107840031013164142c0c1d81010705523189440d08c6c0d00440c0c00c0c24005026142600d04560081040e43c0c82030111401b40d81046401945954030303004100c5140c41044000172401200c81a4620320044542d01e65000210800100010b42e140303c06580a03200b40c00c10a10b007030700840300f04012044580c69052426000d040c030640260380d400e840f07005a110540b138017030fa08810452461f09115000c1c0303449500407000f80000d400c00c00844848014802007900440f00503510403008a85410244600c00090209103030064141c24881009030980034543c039000c60000c0003342031405a2250380403100300007054203500064202c2c10360292603a100c00d072000c0380028100015070380106140d00400d4180c54005018203205807500f03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 315831088 1250 315829838 315829841
    0x70302061503070f120b01051e010305040c080d020a05060709050d110f0310060515040e16030b09040803090f06010302010504050d0c0b03090102070302070902130614070c06050406030c02071206 85
    0x2101e29410710a103040401d0280340c80410000070a02d244102d0002499450003191010058000724060416003c120404c02ea041e50540e07114482800c0000309a2954103120300402404d40041c01c892103001c0000441aa0000b40140210701800c1520b4203601e075464103d900204601c01d46070f00820340d00d00c1c9808241c8030510313101d4031070b0b004141c9100c0051050101707091084803032060030059a5000308000700d0500f0305008000e2001d4080c0f251400b4201100c2100c1c05202a109a000142180c42d00050901940c003a0452041c014160341d12031400f031400802950040702c0c50142c40c0203c21148000e9107002503000d050f294140c403100e01705070422080c0040c00c001c030b0600382c41d6044072903400100020400e0013140a040884000350707988225080182c600101c03a81b00a00d0b0318410405054052524552503090710240d1500034071160401004000381d002e10344002e441002c5034100041c0c07407500032000740111912603e040c0300c074119609090703850305010f100320b0031290310241040c400503209 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 315832338 1250 315831088 315831121
    0x170609010303121e0b040e1603030534020418050709050a020d02070503040501170411220c030501060905030a03270305120307020105130218190c0c0b09010207030206 73
    0x80e1400041c40c1c410044d6001c08852013a030380d03c103080f030b5901c00e00103960405000308103114814000400746912070140711402c540f068480a005c009000c15080c090780c0b004170781c80c81c40c003a216648109400c2514080c1e41581c110721412482545044c0160131040034050b04101440e0b0850b01900d04d59260001c03000150070000c0c800105503500b0400440d0b00311040c4007a201460040c402552074074240360024100c0303c601c0c4c814240da40e142004000c006103c5c0c101059103d0419940010041c40c907104d489007030318040c6909503070700e401d058224040b560700d9405141210340c0d42d698202c18035900d105246d141c0e83c6082c409400030703540d01e5200c0080182000e6804072803440b150502200e83e50303a02d603142022a00b6003e4007603010000244110207509000c4e158124101203c004248000c65000500e403c003000c90203030b4190b0141c1c0002701410b0305410004101c61440c90b05010882e40d2502c02400e5200e85001100e80c117505602007172495005100395418180c1c190003c01864540302c4840012509 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 315833588 1250 315832338 315832367
    0x1401180e0309180405060907050d060c020c090c072d0f02150406050304121412130611040e012102120703020a380a121416170609010303 60
    0x10001c19541e5241d18804100440320011000f03281e0519103020b90401a0181a1003070950000d07109000d641e8882244400301c2d0b521010025281c20170000c00d90401d600030240c1a0302c4515001000b90440400c030013422014400c8842103d004003a03802e1912255402c100e002280540c00415800210442c10824032240010003056171140c02901840343d03035105400c4400000d03404010311007000a20039031010403860703500700090664160310120310719000ea00244c492501107080403a2201d4480304181348510f80180e02072201145110790072649030300620907100c00c204000c00008004014010501002c0e444013200a000c00090b02084004000030700341d0b040e0b40c01003050010041e0340340d00b01100184004078828000280803003030320300d00c1c2c00c466a261111409078140c1e03c40d140d12603000c80360802001c2c2005e00c100380e00030f4090402011420301008042a01320140414164420b0045101c80c50591312800c3d81410440c810b500d032141554081d0700120448014000640600d614030b84514 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 315834838 1250 315833588 315833593
    0xc01021501120f020a0602030702120a0203120d140c0a110a08030a0e07090903180e07140f0d021b06130c121e03030b12070b04092408030406031401180e 67
    0x1c03542c00154185c540d55000708050fa000049403011400c0040c801010b114440e0040e1a488039a600171988590a24007880301c990000509412012055408031a0700c0ca040c076001303141d91400c200f0b0420183e0001c501e80b40440c80780c3c40d00c065928000584c010301c40c0d900020710380c215241e180401000c4d0030320342d42d081294080c20201007103007081881040d824078001d603182d0300b10302c0c242d40c0703d240a8811500f103c0c0040c3d6506041041032500030408a601040c880c6210b90307500c280010002007401030350b0015000c1c6000040c00b0040e00032a0042250407901c107416100b05031246401e02c25048007441005062400e07048080100345540d074090f05005028031a492424540f01a00c80c4107a0002801200403a6842c1000f01560070102282d80c83d105080006008141c1042042805da0146200b080a000d0b2644140f04007080030907a9503c040c040c00c1c05202070552682100740d02c940282c060400003e261140c0e0071040f80c54005c07014120b6034080d446402202030b5000c900c003d40200e25034660701e407 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 315836088 1250 315834838 315834863
    0x6120902011115100e060d0b07030e0a030804170703020a060c0203040f08062e03020d021203040b0d0e0a03050703081b04090204050114030f0c0a020709060906080c0102150112 77
    0x42c041c84059010780b8104400a0985400800701c801c4c044150403407010781111300304000396602d4040c41c1820b940e4001110706160390307480d0b1080380503010300190398a00d80202c114190405800813285805a407051001da102c0402c4002c840b500b0b0701603290040d005911100e0000d02140c2981d000001101c086c0c4180d0785020344882c2021406149540503041c87c0e0300c6141049071101010300103910003500b18140c44040c441c240342405455000e800041d00c00c444074504001155144003171020388101c11001c0c0c03502d440e5100008000c6401c44442d8070211420190f4940407101b020400340700c61a0305403a035a04029040e101142c0081c40103080b17030000c502c075408001140031018080c20040002e014007598075420300e4001000c0a1511f03000024181041c0140829020004a01035000d0b040300d5655460741440c4601701d1900c0b40d5a400403981500e080c00c00700d181c2e14250441000e542100084410a000c14001244d842500000d1080c111402500600041404600c2900722902406079030804 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 315837338 1250 315836088 315836117
    0x1005061206131401020a110d03050f160e090c03160206090604080a03090f050102040510080108070302040b0d120206070f0f1d0a05032410080309040c092d0803040612090201 76
    0x2282d0112a06d000401e071900542c0c13400314800c0010b03ca19030300c80d25080c4800c0c1443e40040919540203080c44800041008079003413214410400b0855400006045510030308110403606025401595200c040540c41205110741d40c1c00011000c1c06180000000c2c003043d551525000107503040000054101030315403103000003280301d02c01e5858619008100050762203142008004c00041e0410102042c4041e07440108040303940800c144044940588010a40c2984500040c0340c85100d00802416110060703150500b9681c0028000d00c02c4c45961942e40280c0c01000703003a035100d5082c5480d000011000301400d4921000542210503040001d80b40da8140e84c0c60780d000130304040784035003551001160311001407400e03408582030303d41044a1480c0c500119062001850312446103480d0140640d4540b4004401c042c0b05041c42001080155401841c014500c054002c5008411083c000b0303001d0204800300f6101000b2084908440c6143c6423107400701c551081180127080000030a170705121484064852 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 315838588 1250 315837338 315837341
    0xc0120070b04111807081612090501060e0a0209040f0b060a0e0613083406080c070f0809040c05090a170307061b030e030a091e0312021005061206131401 67
    0x7480500401032403013038503041380e0051200c20001c12403050451a8001100d10542240900c83c6c9510040000b261400d00d5080280c058440ea070b2080718500301c100c003041420499640505800c40080320107000003466540c82c8420390b0344107440594000c10402c1800071041c0550ba503000c40d2034000d89014100340d000da0360601180c03006c0e0f101c0c41c020340082041500c1e00e009020001700364444049080007a0640b142080304010050044009012000011680884984003030b0746101c0d510603680300c3c1030002c0f0b142051003a00440101400f55081441e6010000d0240054400011000c1c1c000000d1030300e400c2d0900350b08201c100c3e10200c0c5000812001c80030030320900600004180100c0d0702650010f10180041c111950114170443c1034100740100302150343d20800800480314030b81d80001c0402c00e81040b101108100da40001c141c0884060101800707038001c81c1800c100c005c01e1800300300e11b40e00d100c00d200281e41e051078507006a8101c2c0700025190062030108980c480e018442e50032021003684070417030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 315839838 1250 315838588 315838609
    0x509040311010c1706061204080f0408031c05132111060a0e0d0302030403090b090f0a1e05090f04020d1401050f0402090901020931060306020c0120070b0411 69
    0x2001030910541c03180101300d2403803c20f0f044038040c0c0c2c41615164040c01c40c0e40781b181d0040e2005004201c00500800c0d121617020664026140e82c60503256600d040c2c10741c9540ea18a162402c18110b4101000a0050721300021243c02d01c82c1c0041d480325003070f05264070103000c1c0d030344420315107040c41800c035501d4801c62000c0201e540714840b8184d00041038002e01120380d14000c80c6002c0705003058010810040080c1d4000ca0303640844203100c000e991501c942900065070602e01c845c1a6030050030f00c6400107001e0200511996400001051040d50302c2d8440c003e025000500b101c10315200e0354ac00c0041001814149185401c2a0280c0c10b6006110001c8400b54203580c0d00b1b54081080240203000e2205500e48030300701540200c1000d00851424144e0030104681c2821954034a4825410001720181c12000302c80307074050f8152384101003060940328548030000b1740128211411075071802e0550f504250200d525030b11150142804a13091642c2e40c0d03540f29042c130000744101e4000c0d410080b041e80e19111041c038072 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 315841088 1250 315839838 315839861
    0x1606060801020a1407031b0804090507020619020408070b0313020d03020f01050f04050a030c02011412040c080c0105040b07050a0b071d030118150605061606060605030103080301050904031101 84
    0x1580d18014188001d01904c0d100c840d07071303e070745904120071000a81c108952100b050640d59002ca11194107013030840075409161302024105040504006440e50b0200d0150720460340c00e100e46211903000d804c1d1a003240958051168580c2c044501171180418420203036a00050540f400c0c00d00709020b50114940da50403000881c00b50340f1028406a100c0c2007801455070103c41d80b03019604a00d06600d482da580d28a42da4040d051010a484c02d00139641700e80c0f031065070740104050b2a0340e5030040c1000001c3c1644211010750720180030240c08290410045400c00106005940380341c2007908182c510484e59012a104603160300c2650800c4000400040e40d00d8800c6da03058540204048041c1c0000101d00811000580300740d140411202107012050a207030079844c0c00019145d02c2c00742c504a10b0000b000c50780c0210703034404400b01b060390203103000c094101d00040c420b58050120384d0352114180c0e0180400c2c007000f0403007070060005200504102c180c1c1540f0038003d140030801c1c00303001041113084034660a0b54 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 315842338 1250 315841088 315841091
    0x20c0a080a1407150c11010e0f12030103030806061309050a09021e0907030e25050a17060412031401090e01150e040201030506210d0306060816051606060801 69
    0x5074086504000780c20b00203061080014540b011a98810034480c18943c9080310700e594548111030001d00c2149043e080c01c50900c0204400d0b1903440320160b40311f000404541d01481614980d43d03185500740c1c11f0381e040b0baa068542c40481e40701d400801c6260b40080203000c002c43c903518000105c000041c06880c0c002c6060440020703400d9600d006024400d00340c40103682038151150f00d04141a1950011260b215407075240004143d0845001a418506c0844900074001040b100e0341c512200c1c1c03103101208a13801218102c01c966038801651003a40441c025141c440d0700010000f801081e5140c8528114481d5440d0015048010034001c105501003030300503440b00c550350084040b004100344204210b13040c20340c1601010920349003d2090300f07000200000e0406882d030340451250388820340308400078840c1071400301e02401114444c6a40f1400f1164001c0044e080103000100f03940240d00c40341c00744502c00c0d1a00d07803403000c248040c2c0c1c00f0340c04a2440c1103407070700d80481040465864801c0074050f0400c1c400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 315843588 1250 315842338 315842347
    0xa05030709091521020d210807080c0f0705100b041a090a0905030903030304030c020109060f0c0b0411040f140106022a062104030225060e0301020c0a08 67
    0x10000d01c101c1d242c0e00150141d502d0100d01c03d950444544001c0d00f220000d0b411030380b03801d0810500c1e040d90380d40c528009401a81d0001400b0400140030303e0b1810003d201301c8100320345902c820048901d001c0503503280c008520303c900410340720505100240b62071500d80034110300e80300c4295a21803400704400034040c0d00c00c0c0e0b42c4501d80128a803d002c1d1400b8442c90401520424180703c0016000c84402307001c0b4580c142d510303101d803c200001482960754a42005050380c0c0c0307d1a00e810090000031103900120b0000700700440c0072408070b00400d0b0080c03175222180e4507980344862a50750206207000182040c1c681c02c8400b0075801180d0359501401e04014010580070075198005104080b4514040e0081000c0d5041036040d000303042035001c24242c21038003201440c80080604008a10648038810540c580001f440c000340c415020490b6015001c0da100303608983c2588030a801c020219003400145144915800c50108100c500c00c2d5004400180010f0005240c480c81481c0c0d240303440c0881d0030171240b84c83c0118 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 315844838 1250 315843588 315843601
    0xe0a021621050307020706081e040f14060c07150e160303091409060d080408070f03111005090d0c2409060806010507020d0303150e01090e1b0907020307080a0503 71
    0x800c440c1c891650a2243c11420705510103900c5029134012075040251082c00284801701d40c441245c801c500d010003a4681c2c0c03c040c02c2072540490030400c240e072549a40194001441d200180388d074031030034041d4546420b00c000c030340d500012800010703040314071661a07080d4415a900c0901c40c580d80f50142d0100c5104081c07451030060008086540b045880211600c26048242c8480c400640e00c8002100c800c10140c2061400c4010307400b403034101c84a00e20800001042118803c5100c10940380620a50081760286404002c0c60482403404140041c17010700c4000d14a041116400403410306c11035203221070948500c0813460b41c803000c0c05070300c060303501c82498030712041d41140c1101c001e0111480e0042c132038540240003910921070014000d0240f01d0404206c41414030a5000c0c130401c03240700d04100740c0c080d62080c5010080400b03004030140030380341c0906078007a400000307218a40c00c20102d14012182c641d41d03040040c03013000202918258001000198006034031100240007504031038481c40d440b807d101 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 315846088 1250 315844838 315844883
    0x9010e091002040e0601051c1802040b060c0c011b050a0f060b18011211060a0e0103150509040212071503020415090617060103020d020c0c03010f14010e0a0216 70
    0x55a8a0076042c070401050068880c40d101440e400802030a2145e0780b00d00f0701002c055540c00044032008601c1c90020b03440c017207140580510304894001c507410700c41241110108250343c0302d078900b080030b96070280d03d40d200c03154011108510300e5070304180740030310091980e07d4190525050f05c904440c8210701e41482020410244240786070a40c099074034544540718004804400d0710b0601034009485080f51100d0308002030181c055044003000f818441e20385030381e020040d01030720100840c940420f083c00e00310b01303201148401e4242200c20041c9458201c0d21a40c09001c001c022030755600d4200d019405001c580990f8020300400300c8a21303594010380c0d5600e01240781400b060180ca005041040ad00c0003081000d038014a80d0000a05600080c2c0c807544a000041c0c0081c803a206c1e0100040703001241c00301842c80d02080038050244180c1c024422003806400202c00c440c2c03141020580d01c00aa00188808040030b0201503120344000d20051a0441c052001c002c00300c01240300f00e074141c2203003040842e0003908 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 315847338 1250 315846088 315846103
    0x40603140f07020307140a060c0206040b0117070b130f0b0c0705060307050304030e010c02100306090e0102070201020717150c0c010c0309020a150e0a030302010c110a030e0609040b09010e09 83
    0x1840001c0075401c10440080d128464410b01414a10102240b005c0850080c4010384100b0760158040112000c8054041d4940c00200d0b0f0542d01e40559200010b0080c004100035030314000510f0260a5403070600c44401c0d290341141d030303c8000c0340300c40b01e00100e4032490300407680c006003520b980210346500b4650711641c94102c0a812880c0560130500c1808601c9810100b80ca4109a0509001d0f10115580340121070390050350070701070b40c0b1004100c4030101558040d070000045c2c81c064002807060070140c82d60b4500341d02c100d040c002e00607030050008000c0d0600180f0f0000c0302100311019681c441c1c41024081c0c003111001c1d034020303c02d1200003c0c4081003003400d10500100c0307101810f0a006429181d00040c0100025109030f9054810506042207868401c400c00c1030055001009640f04980320306000303000b0015208074001142c0c0c41181450f25000000740c40c039000307525554003c521101d00043c010300750021980141c00c03c1e1610340c3c0d4074041c2e4603045024040c1c0032080c01c000b041c0ca070100106140541 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 315848588 1250 315847338 315847351
    0x90603050d09080601090f020c0a061b020a0f022806030b0a060216030809011112091005040b0409020f0f070308090c0411030c09030c03031305130615030902011404060314 75
    0x58a02c420090410007140b4141100c000040024050342d9840c10034029200d040b0042c007980c020b100f101c03c01c10101c0c1d03003c88600408501c100c2c42c0121005c900340e0b1395802c6044040c00e20301c815010040140350180409e0b83c0800c001040d500e80c1007078221005040c06440d0441c9011070b4540b604103126092215140c002850684000d003c50010310920b0041c50729a40000341a03404006250740070b59014031500240a0b109178203c441c5840c00001184081d0000d0001c1c0e0720441c00f6400d1000018400c0c0c060300c066402680c00645003918101c034610080d40302064980c00c10f134040c807040f0070101c000d40241800e14020b44030800306190000c41907081503200c40720503204602d0f0031100340f040d0b900e48003601d51024203074921a41e0788200d40e0000f49030a8506070f003d617140c0f00000e40c071020914082511011500284c503c0902002c001e450710080e10701c94011030400e441c0740e82d0701b41c0d0928030036085464241d0040c1042800d20214091031062503006804c2840460f4640c00d000c1c2e403090316019415840f0b04c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 315849838 1250 315848588 315848597
    0x82a07151716020111040f0302090a0605090a050405010b12100605030f0d03020c070e1003030e090408030a091b06050c16150807110327190b0d090606090603050d 71
    0x3000e045820382040000d80540c0c840d10304035103403000c554005d40c05110b0441d52010415250380d601c24411303072520600e0004034000c2ca40040854020140c0340100e0080d00d10061840485a54004100c4000c1100410903145503403035041904446c0c4841c81d0520004c420480a0a201c4a074141c03510151a42540043d00940c0109541107400c44041081c41c600d034290300e00566500e001050f038034500300c8140c01601199503820180540c0514a42407101100d110b41c951503035540200d81000000c45044801600780182000003404810050b4840c40b8113502c100c00803078042100c2101c078603000407103810840120300300050600e030030002048054240044501070107025801c0a0304075840c0c1002322004002d0003400e001240c4030030b0003400603856030f030a00000c903a1a4240107801218602d10084100c1c80020544d051103160305000c1100b241c1c503800710480d103446515240716075205910820aa5074110303642d901600010301c41d030103401c00800b0b0048c004583c2c0e50850804508200c0060269070900 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 315851088 1250 315849838 315849857
    0x121e18040b0901050a0501030f0f06060306180902010905040b040207051221100303050309120c0d08060f1e030c1e010824060306060702060d2a0507082a0715 69
    0x285e80394641c0d0760590740e00b031a002c1840d0700c0758030341e40002d0400c409079a0310380c07414107001040740c55069200b1422500d40c1c0800115020442000c501250303034240d00640020360482d424021418a9000900c002030040c00041c0350035202d880c0e041c1454000c030307103000c074034400003880d102082000e034803a0404010440c1c0c243c806051078110014542007500c4000c003441404000a4051002444804a520950001e071941e9480c0c00260a4440001803e0f40d408261100c001c11401e00b030807284040b4861000e40220300c3c000403103e100b2103842998070740d07907031502c504081c6820030380b5141602c030800150210b404280c0083e600003d48030302d0000304490380110076041c00d503918042074051180212801e03031b41e80d81d41e074460302e0201321680310308407000e908108005226501512140e0021070725500824601c9900707050005000001c2c601c1084440000c1d80a1040ca408591054010701d020528100c8500c20140e503000c542480e9078040d1050382958001407010040d141c00b0b8119480c0c42c84040ca44403901 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 315852338 1250 315851088 315851099
    0x180d0f0206040b040c03120201150603112704020705030d05010905040503121f0806060a0611030906031302041407020d0801031e03020a200112050108121e18040b0901 73
    0x507000c004002808001c0034101207000e00c45c0034031880014541003e6130045900755803401a011b881c05c011801c4cae91a462420000359517110348245000700515959441c0303000710a05041030000c40443c4100c0c0400e0f030800d201c007030b80e40e914401060818410b001964441c032001c400f2808480c0d0580c8030040e070130b0502d410800054030200c100c0f59030001c42d900d107a5458940303540000500c18480381c2c10b5503031080c0d048007147d140000204a8400c08044030414120b036282c043c01c0341e406a4044004215a100b0b100c400e5541ca01a00510380c0401420340506001007260000b506a81111801d910403038807041c1488425070741400001425061401c0c540c1c2c481d499946c03071040ba08070b10204050803a401d104803004261017800012034081d0000000c0d0800350554100031521280aa0303100d011a030052415000c40701c440c041d15040382d04520191000d0a950312080c840d5500014001d11708205005140c3c481d004d4800142034100b40d448000300c0d0b0380e00b52905000031107030048030b030b58403603120f080c010000c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 315853588 1250 315852338 315852343
    0xa0606090503240c0909071e0c0203070b0a0309020a060306030209010f0b03070c110d03030b120a0b070c02130606200303090c04020d02210403140a0f0f0c0506180d0f02 74
    0x6400c4000108541c842c0e031002ca400c2102c2c019000301c29480a02d0f0002d0250b659803001c03d07498004501c4d02640001c24140500fa100c15002703071002034068004203800c010609114014008001c0d890801040c80c0029500040541020303030000d0011a0362000103201b13506000201d98054005501010b04060500d96138081270b000041c8241d080015609003a020001034030741c84081d006004e80408072903500c0e0f20b1301034090b105240f83c05005102c0d41ca4200e42c60b030341c00541d03110b03140d800103160070702621000c2d811a142101008166040600029168440f08142c0f013480300806041c0e903000c03034081d4040811900e640005070b058101d03a1003071050010a881c04500003210a108a40069460300102400340c041e00030b685542109040460583c0003101c0c40d45c441034800c0b0310903507410006400041c002c0d901c50042c4001d00c400510031a080e0540c541c001c05a210b01e04a46003000d020240c1180d440718078008048442e074020076a40d550703102141c0ba04002150b418100341c24904010306140030000d5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 315854838 1250 315853588 315853633
    0x3040b071d0906060702040f090b0c071509030905060f2508090f0109270b09011a03070201060e070203180108010510081005032401050103050f0a0c0e06030a0606090503 74
    0x344160099000f00786580d444004075170203294060000d02c119840320200780001c0601030400e640b0b403a401c100041400810f4021500c0c0039602c009062001049146010000d24010008030700b80145550f000c1555550103018041d2200e98240c1e1135602c0b542c03482d1591514903050001042d861700c0c012000009250001510a145000d6508010702000c40004031000f4007182e0040c103440581050343c810304000c003002c412120700291402d215004c800014051400024400d681c001503200c0304180d82441a1001150010803d03c00858440c2d00c0e82c0d00a0350511080e603051015070f00014659114407501c0d21280040142401e02c500320b5803620b40820f002c41260310b1000c0030801d14000090420221410090152801604a403840a5148061404481b000300c00c07209128444000042941c8240207191081b40d980c2d0000f806501e9801c0e07040041d1140c0d043e0b12080c01101003880c0c0e610f45800b405544030703c26001010505602e820b1015101c00c9044d005140a41c20108074042015088404607 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 315856088 1250 315854838 315854897
    0x70f2915030703060e01020c280b0c0c0d0804050d080705041203050c030d2007050a11010215040b1f050d0f020604030f060605150909060118170303040b07 68
    0x4000030010800090402c02241c000500c050710b02202d007148108154007800f0f507000d1b02d80459000c140c4038002d020351407070700f0142c082030441c01204450004141407082034011891250441c244810056980c3c00c2c078031400e605a00040c00c140400061040030881441944454103218400c3d003004500100203108a025807042805c2c4104040101841402101e004010040075280c8401d440c0b9a8000a080b1458038442c450a0940455190b42c941d6412540243e9100c2d00074070f191103065480c0d442c0710201003070392030550149640c0a0702c08100c01c2503961140b4071401d019006440c04900c114520040f40b07405494800e00e0000c24041600e031f40c0e600b01003e03034100c845c420001d242840003a80c0352190b50801009440030500e140d080240641241064034402c842d07024241800211050b210300810941a52149210011882c0e40d400b840030401d0b18204401c00204440e1500603010113442c0e2411480d06580c40001008140607014443c5c50708800301d440c20701442e00161620040003043c84041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 315857338 1250 315856088 315856111
    0x41e0506180a0606140901150f030c1b0b040311160b090d0c0f090f0b01120f0e0304080606120105070507140304090e010c020d0207061211070206070f29 67
    0x940c81c414010080042c00b107901450510040e41c03543c01c050566a08120310a001e8010300e4008038040c020070802c175020a80c1550f8210a6a650200882c044d12031403110380241700c82c911310004109804034155986a018000e89291810245002009107078913182d0160150048109900c0306030312024050101d4000342d003030580b56803842c8000f4203d040421001030414001c200f00181030311004001004498000004004000048034241c0558008091482c0062903034943c071650350201d0392043d1903007008203400248400100c00320f145194010b8206100540c06101007004c64030f008100ca01c1c8400a0034024001400e100740c01900902981034000c01c0180c085440880b940c200b0002d0b24003d00700d000c800e1120030061400b2500809000f40e50308014000c100482e0511030001629408440896541040768008109950020f10b80300200c1c0d500440100103074005a52071401030010a406034404903031007182c80c036244080b0181c2103094144034035043c1d043c000c03103144040016400040e176a42c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 315858588 1250 315857338 315857371
    0x170c090405010209030f0a03110a030818100f09111e15073008090c0112020c0a03051c060b090904061401080106150908120a05160605041e0506 63
    0x2001e0b4068051521400d4151080c0400c902001c400000c0721084540291580c15480c0c0c0800b0307800d07450344000c0c0c0010340460b50400102c0d02d072030365180c400284000c402d000c0e500103400842440007955001c054400301d40d507c1d40002070600501da000c0d8a07181008843d071003480354400e10701208414078661002d1090510310283d030740b040004c600702c1d103d5651010409450b000d00c4008003101e4448000d011780c1b2440c1000f030158155000b88545e90280d0740542c001d000207145c64004490000c08a400e04244980a002c101340b084000c1040e100340034480d864003a107696460b40f002e6401a0f100480400302d41c2011802c0040b0610f4408460f1042000d0b110007440341e8850804001070104855000c18600e81c000c000141208194004000d68080084048a240e10510200d40c008194001c00f022a005031004184500040700140700d0300d0024101a4248003205e140d00d040442d410340203503040c03a102d80420081100e024104c0012050941070704030520140e85039165180401488500d20502c11708 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 315859838 1250 315858588 315858593
    0x3021602010e211c020a0b01170f01020c07051c0c060507020a230907170a020310050607030302120a02030c07110a0b0c1c0509090f06010c0f03020a020a170c0904 71
    0x4031019419007103c1009003000b00c00803100d5a49510001000146201e0010214440380c030100c0e442e207030203070003181241c25030342003010f4250b010f000384190300600d115045146000e0b0b00c1c00e0001e0080f02e00b103000035101007072400060007850b000482d0a0301141e000340c032111002a00030078800080c0c48580c6086e17501c0c0d0240380b0100b102e60400b0b070004109560b80380c1c030004080c5182202e01c40a120203490041140c2c941520581c0c1c46048116080312040711030700010075085241e40955070185801c450f43c01250350798004511183c0c0035200030b400090f000035400c100f82030f07900701c880c0e0400342c034900c2145103245c0098400b229000f02d0400502c00b110a07809410079688068a00c1c01420640398082d5481c3c02d8103030655610082607a507280c545940c0002c60348418041c0058a42c68040034143c90401d0383c0b0607003044000dc500400d21418459010004004920204e4505503883e1180d00203000075140d60040004500300f036401020032000e54035500020400108400c0040c0a09440e0b4448584451 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 315861088 1250 315859838 315859849
    0xa0c080f030a05040311030a140c030409050c04030501060602070b04060f090803041403150405120a031104090603141b04020c0a021201020301051503070815011b11030d03021602010e 80
    0x1200d460500101009000c0c0651255110700d01551103505c50310101001407050503124084c0c44044004160740c24280621001c0000003014840c0b0703854103030781c5460b8a5222175011600e069a12000c0c209002c03d00313100300402445100040c0030780380000e0400320302c0c1210f002010321807030240e9020020148040c1030518050b2008001501c0300c002036a445549a040d5030804000c1172031064841d20035180c1a01e81c00801000349801290440c02510942001c0c04010f015588541c64000405030707a03485043e025264480984040c116121001c01c0041c0703142003a00d00d0b0070802d090480540c0040780c2841c0c6042d0309044088040209460140c1c0310750010b08258108a80c203040a50030034910048402210307010342c01581130750b0046558141c42003042e0303030002031800101c401d0303004281101c01240355002002454140480149000d00901003c90f50301b80342996800401c54241143c10740c0a01989020302544400c442d4600d000c40c20b001c1004055020107903494030103410301c52001811521a140c5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 315862338 1250 315861088 315861097
    0x2010507050d0e01020d182601060303020d09170a150e250e040816060902190905130b01150207120b060a05010306050d1401020c010c0e0906040c050a0c08 68
    0x1c4400c1d1a0015850303200038200540c000341d202d0060040c04115038080c0d000d40d004141461100e114482000c2c1408036070f25070452445500f6035500e2260328002040c0300301b402480043c61199028000103110310074080d0030b8400c1a000807103000da003000600d200460010740c0c00f61b001e42025110510012101d1100c009284c86840030155000301841002d21400c0c06500c2d209450f0581141c40510b0365940e203114484c841510b000307060300800c100c4010713040307640d140b880c200c02d000c1da800198890440d070000303042e074500300c0e142d420601c6984010451110580f00d8140e00134400c1d00075180901c5a84c0d40e0f288804414054145180c8000000e040700520030003403140078020b020340400100d901400e144500041c11210b03148036094860700802c2c154420f0043c1c90071a0b1001d4140030b0b180302c0301c0e5108011001840400f03042998203101a0601e040240100c00302c2511544800c81072654880c2402003044005003850300543c2060b00c5400c203154090110340840700705142c0340c400d40e441843d006032544103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 315863588 1250 315862338 315862343
    0x20c040b0a05041a120606280f1202031006060c060e0f060f01080c04180303020a12020f0705150403050a0c0f050d0302040e090d2c0307120b13020306011202010507 72
    0x4c2c229a5021400b0110908081c0c000115104d500c094460320250396500e8048440c1c942010802441c284560480317403401c0c280321000c1c0d0101840a40b550910180003d00303a0062082c0700c203110408040d41014089501a89910300c014000d42c1c0c01c1403005030540403001002070905940703807919a140c09080c40794500d00c1e1011400d44096007000c4000a041c0340c02802600b0044c0a00c4100c002e0b20300e8203108441f01c8000c00c03034a00900b0646910103030025005010200701340300c4400e400907641e02091005080751015080280e413214100d040051a000c1d1101e04004440081c00500020076000300940c3c0450105140c19641e200692a001c0f05031500c40c103000740345c0c0c4030700f003014034081d42c058015105941d2041509202603444010340713590341c09840e481070302040d804040303180441c180d01a64800d000400c09a8003044410700d0200b031034840281e00080d9010f00e1740446400700304d0040c40a50304040d10382004141440c564001035100c80d0184980401d03550f0701d001040c1164040c1060320340458 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 315864838 1250 315863588 315863591
    0x30c2405010519031119080a0f14010c1707050c07081c02030f03151503040602030f06030309220213080105060315090706031d03030a05041514010504050405030403120c060516020c040b0a0504 84
    0x1402850032700107030311400c58111202009032508901001c0144201122404d040d07441014840d4071a20380c80e5100b4000c0d00e014108501048028404034080021384c2c01400c2e00401011100242060424139042580150341190800c0090042c03010060094a401c0880e22010705080980c40d000111071201d10032120846440100421051103c180e000d10310600c11004041c000c0e5440008040e160300c240d6004c01d030700c0502030740f038980280c4100215010310f10901c2001440c200d064100c45400f2010b5034040b16036607464004000060074207215180c40c10a0346800740e0300c00e08048511944501c0140148003c05988140000c2c1c01e1886025034001c401c503080035030383d07641480350382080585802c81302a184a01c8236100c0b00800c035071a00c9200e00c054104070399400941d00f00340402014010280c010790309803005005c040042046100c02d061884810340f50300c01700f040e0520b03090080e10401003a035455101030749050610140c02151120381507200303c82c0010200740d500001011040207800080d00036 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 315866088 1250 315864838 315864853
    0x7090b31032306060603070c0609060b0307081e030a02030406120b04090807111507140703020312030a0b062502010306030b070201020d050a09020d030c240501051903111908 76
    0x18035542480b2941d2502003a2055a5240428000d86120a640000001e030f160500c032004603210fa8410031140c1d2043c240480c2051034032001918110003904100c5098101c1046000043c0101e0014201040903201a60420511040194036806917224071811301c803110080c8000500d803503000342c0055000038010000c0d0074072802e0200c01078204c01e4049640150040100a0510340383c1e0002c82450820340805103040d91030364966080c1003081000301010301c1014004801a80c00340304580254503100401612454113801e40425584201c200602400c01041030808091440e0f0740480c40c40410840c0c3c65034210395200480040017964009055026002c0c1803086880d410340050540d6840c041c000d00c0f01d41c42d800405000c454941c98020352010f202092200041d02803008112031a00580d8090433500c0c41e000303112809051034070200b401a545a0040c0700e540b1b07050082880f02410038910f0034410741183d03501c10900d021608200e02c10798036120703801c61144803041000301038424072003a180003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 315867338 1250 315866088 315866123
    0x2060a060312180b0a0908060901060b031501020a140c0118050d11030c0a03050c03070b0f0927010f05090a09030212030c16260a0f030510030203060403020607090b3103 74
    0x128003d900494000740100302c0460100e1105000c1c68060320b0b01404250319684580c4145144ec0c54000285030560048088600101e11401c0c1102001c00703045002e040d0b6411940001046264110080b800c0e0794852034080c015900c1d8684510034003607114019029420741600024076040c44140c40395444108100084100100410740800e000815800c80d10601e4440c021140c07640100440409066420701c034999180c03403c0035415400c0e0042a048400d004114201822600b100341c00400d03101c0f035191810005401d12050180c0d000500840400811144e80e4000703407954903011031001c0798040403000c1040214460125100102c01912000d84203605180c2414080c50304d96800c1e0100300d10811b103403501c0c80d40004440d03072150103940718000c1e0602081705030014240502094441407000c031001c401078404000d0311340518080c0e0014007807454400c100421891058002445a107418032900c900741080d00384126009560142d00407030303040800020441e0740c03215070000c0c00440ca0404001034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 315868588 1250 315867338 315867347
    0x20d080a06050904031d04020c10050a060513201207030b06090d0c090f0b010207090203040f0215030a0b1905150f0a080103030215070801170f010e0c0102060a060312180b0a 76
    0x24401b02180c04c14908000f180c1004100d00424101113a146c00451034001740440d40d0b0300c4a54415039200d00068402c1c4c0399004940c540d0041070900000590f10003402c1c41328400080890624030344d8800b82c81c6000c041d01d0400549810107010310317081c561070b109610020303540d100540c1e0306410701428407031030907209003000b608120302481110348851819008490781c21060003414511031040c4c0062140c80d1500d28010b00031740c801042654180841d40c941070041c2c0d00e846014002403140d035050b40d1039041101100c0304482c0030700e035401d104022465510b46001d070b21070568001c80e07400b100e88508104402959540394829191076601c0c000c000543e480740300c0e03009041641030300e0007642219007212200d126420070250640303000340401d85800040200803454400030180240c004103031404221448089420341e01d03046070016035504000c82000b1696410001c0345d9002c480d4003820302495203544c41c0d5003491541c17a1100c1d000c01c001c2d854180408a5095265001000c07a0068507540780e8070340c10020b1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 315869838 1250 315868588 315868607
    0x190f02090423070813080403080a08060906090c070f0c09240e01180209030f03030a0b0d020f100c0c08030721021c0908030f04030c05010906020d080a0605090403 71
    0x744500d1801c00c1440c034019058244800303640b481030396001d06440303403581990303001001880d00c504008a0714240002451a8010b040103504c5482c3c0c841e146e0000003005089a50f0080c19503009440a400700455680c1d01c060351a0407a200b07075800c82d82d070342130750804111303022400c0c0c0d01a0405560500002c0c50200507407100c5c0303003003036415410b402c0c61074010300c01c2e013200031a031003000b03141d02084006004200c0e8002400b201a200381d2401031520070641e0200f8100582000c0e01c0b81070350000300410a042c9543c1c000d03a011042c040b10303110711011403540045c0c0b81803005001c0c2801030001513a5074600500031604508403d400c01c1410340000d039102c4840b966580b281201301d4070790f807120340399010f00c0c40c1e40900b840200c209078001e008110301004410300181c0c481c03ca01c004000d440c182c0065401c0d024002040301c0b009645134681e449040d401c0c005250200c9520141c104542c4c1081008040e9000c10030301d150071200d152404207a206d03950100c02901d1281c0103e40e0001d02d0a043c04105604402c81c0c0d0f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 315871088 1250 315869838 315869857
    0xf0c030909010510080103110a05031506040606020a05070902090105121503011107030c020f06041d0406060b070510021c0f0209090105090606040306021b030318120708070b190f02 79
    0xa1942c1e0b00d500c02d01c031075107000c8400840811500801440010b1a0780e45000c860720000c0c2a21780e0240c0e03035800180c0342480c0c0c807420349068520329051140c03c3c06c15000d030034050117503030000348046240c95407103e545030954868002c081d03030b0105060312141e1254007250200480c00080a009051401030301e0303010109180720078403961800007001950201d15055403006a0151101404403007513801b400443e0b408072030b200340e200034204008501c2d030102c84d00d02000442d0750502c50255103424038103402180d08580003004000c030140600b2000440c0043d000202110755240562540c08004450300711031080c2111a00d4182455460b145040309070b40a402400d104840c159541e1b43d03a031062000640c81951410b1701b0140800041c80815a150004c0880d110103070128a144411230310000c0c00d540041e1b40c01d01e0a10500c001c25060100c00f00310035440d1540100d81d091800d120f50340c074803010f807158043c001e041103107800000340c2c0d0140c5410f00000c03403655080140005403000f48040000d5100d00c004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 315872338 1250 315871088 315871099
    0x150801021c050601140a0809120c0a23071e0302090a090204050a0605130c0507140705010f03050f04020d060b100e12030301030203120306120d090f050d150c050f0c0309 74
    0x1110740d0710408010402003036445c1c0741032034034141d90400c40d10610300030144002441040300c01e50a0b900550024002048603030082c00310041c091414000124280c1498814079060b0072100300e501502090110440c2d6148403000d1041d04400d400d20042403807680b0113507000440c0070401c62400c1e8207810840040f807084404105035aa1005003404440c4107020302d03034020500c52849079902e0b446920410140c0d1f458200b1a05225041c0e6a417441d25000850107015500418000c00c4656000102400210498102071003a460201c03d2050410302c01032000c2d2180030080301203014814594455140c1c5034010f02610414082c00c0310140600080e080301c1406410070800780708400e000071003034905927680100500115240328501e0000d40d0030141106600c8044801c0ca1303200c0c801d0805c0b043c2514a20354445038501441d0a02c0410386003811f61025025030f158129480025803803558511100703119810001d0001e0300b041d001ca440340500400e2820b9600d000480042030200000600400ca404960 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 315873588 1250 315872338 315872341
    0x20a150213051e1018090c14030f16030e03181e0105030a0f0b0607050c10090303050316030609180210022b1407060507030c0e010210150801021c05 65
    0x28003c0800c95401e02150304140d11515242900d0040f6680c1c0025000f45001600c0c0c49815845469000c602c0c1e0022441c540e55590302c9000c0da40000440c4c041c10a03035002d26080d403510705107c135040200281100200140c07111082100e40c007980c080b55500b0500c1c1d084903141c1040a8220100c1034442c072a0314414035458000104c0c003c5403003501300300390340107039540c50039521041c0600025000740c001c401c201945440c901001034a0340c00250150354011802441e01082003410b0081f11400000c2040170480100301c05d01c003003500201280d82041c080d903800528103c1e06001200140410341180202609119540c1c2c0c45d8160403107a602d506000721141c500724900c80f2001d076a501c10001c1141003e8424424400120301c2040c210511803c0500707001d00d1302128101c030744080c0e522062048031601e6503007041c4030f4090307032502c242c0c92528402c2c20320212840d04840040e50b15650140c2e4044090b4480101c0f81110b40c0d901030010003440380c1d10080d9120038108886200094011031250055031070b000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 315874838 1250 315873588 315873599
    0x40303030507140316080402040b0d05060f09010c0e060309161d0a1b0c26070b060901030b0a09050c0d0b0106020d0504060e0f061204060c020d0305060f0f01020a150213 74
    0x10440380161101c00040b05c14401040c000c0d981c0300c3c0000c07c245d1340550303541d592030303595161500c402c200303203100c4c0740500414a82a600c581d00040054102d0311315070301d001c00311458240c00c0b41a00481040403a9001d07229543c00040c0d03440d02d501d100c2081401342c2c0c6458001180104451400c07a03044840341030143d030740d0301d0004800031502120040c0010b551840c3e0011070107030149001d5010180141c0040480307688a203a940003101d8680041c0e1001000040c081e03081c4000d1010343c603045082100c104801e949191540c0c040000d0203030501000700d94420023039080000400c807000c1c45c4900035086920081d141d04100c2c00b4280248a998054050030341c014074076610650072074064034502e0301c40c000702035041e0701400700350b0b10046c40303041e0032020801580030f6400040600c40d10542c410a000f2507013212000c0004c1c18036040480c0501410704050a01810b82d4840c02c18101844003903035911810340103840100d20b0591741e5040030b0490310091242d0607902105030003c0102e1010480300c1d103001542c50 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 315876088 1250 315874838 315874877
    0x120109120f1e21150306380a08060c07030201150e0103060c030e16050a05010201020a0909020a1412010302210d14090307060c0c170307030e0312040303030507 70
    0x1400e025100000c007000b40c0b500780d0146150a1011141071260f14228074101c0500d030032035050404000c150610954108200300300c500034820606031010b5000c162075030729800108000038204a034000707080a2038004030261610b040e204c0c000c040000c212100ca0518450030100740d80100c00c144c0055007000411f6020341c5800e862602220303112032583c2070f43c2c0e18507184c20000f481c20100c00e0b01010780340ca00000780c010f0b0820004100070400c000b0300000030303c1c040030000f48604950000f0306590040c00310342c160580004200b801ca5404000c0076a035200d9024044440c01c40500b14501c5c01000440e42b46c051100c0c514805069910980b41903907000412441041c59400c8808105040d038003030301c0780304540e0780300303845619540141c42802e90800e040c0c03030002810301c080c1d9040000084e1681100e4803d0052405001c8020003012075800ca01a10b032210894a0784a08800602031110510110550761800c02c164100d0305042080c55441c1c907124a4003e000c2d01040d12078400140c00b1450855440010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 315877338 1250 315876088 315876107
    0xf06031c03050910050106020c040f0506010e0f03030904050f1b04121101020c030d0c061503050703121404030b0910270507150f1e0804060506120109120f 68
    0xc09241640c942039a0318201c01070800203011110900842041c01c000004900900c0d000e8a100d801520750043e074032090100701c8241d507001c884e4582c180400c2c4000759811644405081c5000e5079281507404d42540420b03c0c42c0b06407000e40790818680b030100318810403900c501902404441030b03022030510141460740c0b241d000324012002122801e5850900040d000a240160f100041c0113403405001400002810400303030202080200d48190302c001e00304400c0344170315a0750017846111451801d046d51150f5540e40c90300c0c0401048200280781d8100c0f4180120a9070041285066401e542c581d100c0c0f814058010040c0e5040d981403185140c41803031894140112060408020141c0c4040400742014102c030112011050711107005000700440c0b44940c4128014110300151984007960a04100c02800c10042000d019034002d02c203241504010b9102191581254200030301284546400d00090300100b00c0452064032176103000c02000800800c800514000c0549032185580c0b62940b00e01a02e40481 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 315878588 1250 315877338 315877363
    0xb031b040807300b0709061706040e030d05041a0c120604050c091806120703051002030c0c0a1a0c07080405090a0b10020c0907050408150a020f070b0f0603 68
    0x525018003a0803806440010603480d03035030b200030f605410350200041c00b00380c0100584100d0208810840020341001090004050740d1410342c40c0000c25030b0383c00401c00d40150490303200d940c4444454540708010010f65019050340001000346007050724040300040240100381107044650400200100344a4090302d0801e00c1080c1c03801d4035a551101000020301b0f00400741c2c3c403200c1d8280144500ea80324041c1707818001c00b034103190f0043c1d4180b640401112070400f4030700104c01e03403180009000040011881600521441c640503840f40c544090000c0139001d186080d804521034000d0074418000558840300d01208010548142034503205200b404605c02c09c40c02420240741084100310381d041640d0000c0d804400a00001011080741001030320b4034010390f00010040c1c0c414800940303e445e00c0f4500d0307a0000c20320300700a441c1c280740811040d1104840c25000340304501500006201102c130b60115010443c42501c210354840480c5400c0c0c681319800e079151204000d010b0000b5a19040000d0307030402e00798 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 315879838 1250 315878588 315878593
    0x3020a0e0112020f040f0504140105030316030c02060d0203180c0d0b060301060506130806010501031b0c02030c041518020a050418020f03250206100b0702040905070b031b0408 77
    0x125000042d2240d40300c114600c14515401c0001040c0641807401401c05021442035803880946400100703c00c0e1071216020083d85000540100301d507030b40000884054624002d80d08080100390b0130113849441c42a0380294100c1c00003d2903083c2c090745540290300c240340c080001c035008498011442e0780c5060301d81010340c00610804c40100454030301010158400302c000c0010821980f00c2c40480c241d60010000d42a05900d03003503050082d0030301440b680e0f001d40801e1908220b11038503480c52020186181000505002c1c113200000c1c25928144255003000300d000c0c005101012500303840c1140001d01d40707e40d003001d150307102d04200004854000c803410f184071541c40d141403504181c540e481a8400140c00e8103640d0f42002850500502e21015511688a1070381c40b980c034550721004c824500c40d44140359400c5405c00410040c0030b6030407c800d0f8090f1040780741c9503134890f4002e02c0800c4c010019414064076510a11000280601d00603000750720400c41c1c848442c0c0510b8a000452001d400b807406a01340c02d4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 315881088 1250 315879838 315879857
    0xf0204180b0a110915160503131508041104200306100e130b06040305010c02100c030513032001060e0709060206041a07090b0304050703060b0a0501050313030323070f03020a 76
    0x2450301004221242280c0309601d41b6040440e4814202c03c043d40304125807030b40002c60003400000018100030003d08020f245803403000780c130203002403009000410080421911881c20341e61603c0e254001c4113101c15120381507001d01d522040003e4985c0040b60098800d80d00707015041c6406100d07032000e14a2042c0903220180109428400001070b20304e101416410840a20000010030b009001e404034284a0350054111310b210024514281c4200d12502001c1c14101403e105d848035011034000449605450090340a105c10180141d074034111000d803409a42c2440c901142c201034006055008a80fa510f4191a02d07903500703400d0341c0b221401c460241040301e089248510000f0b198101c0c591101c2c00d481d048060302c1e204e51080c44280c10940c0e040e0355070392014009108200051191a1a0100031149008100e16001c002001840b0042107403440c00c03840351001c42010f0007508081c000b00f4060005070b0080142c5440000010821621840000c000b8629446118024404c442c896800c55813001400b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 315882338 1250 315881088 315881107
    0x120203060a05060118030609060c030204060e040908040504110301080606030a030903030309020d0804090c0306270f0905011404031715090907030c0f05030c0f030a0f0f0204180b0a11 80
    0x3042c00511050500801c00017458031401080c3d42540510702c1480300142e240f03c0b50902504480c01c0d0342600e0305051040006100c900c0d0442d81404281c002200e01240701d400760300e00403505000740d0703105640060404803210383d00040c280281d4140c0765078100712912a0340743d40400d5030f6498a880d0250101d0851802400441d21035085600d803640058560b02a290f252341c1c403d1038940c401c0c0d001105481e91814555072041e03044c0203020081c801d044180030b15200781d0103907038580f000c001c8454085682d1181c0c1c0d0340b400e8210303411503400250408002c03c2001303a61242028a030000712022800201035001c1070a0400b0040601d600a8501c502c1c2c42020300e203220248a0034070401340c10710650384509000080094272607140c2c00c025024000d14071016624000901d8500800364440c188940d0144100c244941c9001a4030306215800075000003040702c0c681450481c5d1130a025020b5001400c1c100c140c80704004201c0c0d0340b14078512400721008a956201e9440084400d07400c082d041c1ca501c01c0000c0c408 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 315883588 1250 315882338 315882341
    0x16060905060a030209030a0b0609090604020918010908190801090207121b0b160e03120d09030504080a060c08130b01140f04050405070905100b0a051602030604110307120203060a 78
    0x4141e8041c1001845c02040400003880d044c1204802c8401103504010003060f81441084030760081c03501d000405241c10542e002407903500f00104510600c46180003400c00d004802d4111b900310079080502150307a189071650f420840b982c5000c03d070022941031000024480030758400c80f034550350001002e25005035040740440300c110078185e5600c00c070702501250002092980b12030a000da00082009800188840e00c00b170511070081402a100360450311b500b40214501000722170800080a074009007548452500f50340340d001e26000300c5482d116400c072120400916600103030b040001078842034034599542c081072460070046034004100c9212080100100c010b1100110b110880041602070b6500c0c070030b4049000c9410880303043c2c40c80d511151040212141c00d01c2095041803c10044540c005d0070665100b80c2445180400e004200000840071145100341c00740181e01c1da03008040e91654100750a00802000c040c00c049480782c047c900c1e0004030358030841181c00c441580600540307503135030f40c0749150300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 315884838 1250 315883588 315883597
    0x71d090d08220c170106080708010b0a0521030706050601200a020f041803020120190e150a020d020f03190c1401090807060b040501050d020409061d0d021606090506 72
    0xf101000080030100340c411450440303440180861000041c0c8602d00340465291805560180c18107925003505c00e03d5584540e031003501a14000d46600c2442e400046020580300c0c3c0310500c90355240070200e68503082000c80e4005500501099860b0315025445025402c0d80e8045c0e9280341400f076000700c0d0040d0060604100001817040010000100d23144a02c0000311006a03d50003100182d5541030381a0420300850030804200320341140090400d00104000320303481020710311038020b02c11910314900c41c4d641c0c4c0350290186143c0c004c041ca40c66440c02c140280d550403440300e854000d0b009003048030300c0342c4000200f951041500000d88600343c0c01c0124042e41e0850325080c080d500921503800542c081e4009005030544184a12061a541d0708681040401c448099100ea8400c2d401d080041016a580c0104400d6140d0119000913030b02003c0e1404500404001d15004ca03520801035903c8008a00840d1100d2010703855002e86031040255071123070513004214020300740400c11800c0180300d50b0030190040c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 315886088 1250 315884838 315884843
    0x14011e020703020a0603062105060c03190c0c120804260909040b060901080a151d0f030a02070e01150e0a0906120c090c08150102071d090d0822 63
    0x894465469070013161894009402100c04251074613002c1040032480c1101003803c1c01d4801e10780042d190b599a4990311480054482d20403c100031002c42c2d180b00c030f072902c46022040100c0b803c0000da041c1210284c0044100503065841c000b00050068800d07000320301c4240b242c0d511000307030309171030840c1c047c8044601543c141a11000c0d0082c00006c4158503808086409140601070b4a0f60702e14011040004441e016000505d0a4010b03500d00c10002d40c4400214000e8100001c010995040004507096201070011050742030f445080307401d100d90580031005081101c1d860f800d03640080c2d103c40d1a040518002c0c4030300d07d605821201d0000c032580c13203854200d620501c010100f038000c3d56180c20301d101b80d5640741c1041c11b02d90b00515917041006148170071400102203010b81070040700e440c088080e03c00c40004143c83c01c040d81614141079160310a12400700640200602d05c00c000c48949100f4480c050100d9054010307224a44400010b6400b03a07480c00d202d2040c606403041ea0b2243c1095450781c103008030b40d08 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 315887338 1250 315886088 315886093
    0x905180105010905180a05060106031109100c030305060a06141b030c061e06030607140c120c07060201090203030304150f0e0c0405060402090a090209033414011e02 72
    0x8020000800e004860081c0010300d8046100d0070400142c220b00c5a4007012138849074407030315010300011408910941111445d003000117001c0b1035446180143e02c52400f409a220045a14000b40507070402c1010381030360700a40d82041640d86820034012001c80d94090040450300408283c1c48200700b2400400c03624141c08044c00c1e400208510091a40e0400b0b080c010f0660400c404008255682407030400029213541c00b8222a8107052021035141c25014182004010920407110140e1810341d04550144150034121022042500c56050060b0800c040e9500c00f4000c484002401c02c0c4140030341c40c0301079002000396145496a544010701c6160080180e03040984400001414441c0c0d8440d4840a2000001411a20b862401044120f0b040105a03602c41c074418801c1001035110548001d040e10381c19080107179a0004803001034948020300c081c44005a000750b2030141c000104082c5050341c1d6940306d1001515680702c2e60121021040c0f44001070006040202c0455010312840c4800640f1010740103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 315888588 1250 315887338 315887371
    0x1014091203091c1110020403120c0501060b040915080d0e01050c071a0a020d03050c0d0207050f060a02040e010b0403030e06211006120501080703080903070b04180e0102090a0905 78
    0x1042d0300d0364001ca050f280200c3d00710030018811a0007845030004181900c00300b1440e0038195a1100106220240f0403402c110b00501410100b007401d502c0003018002010406858959510a40000d428460131910390300c004d1080001c3c40690010707400606029035200d102c0c02107000401160942c004e801d010a0604c1407a20000b1324000e0f00414110341c81d45001030917178075803e40c800607180c1150b03850600e04251800c001c20480303110b00360640300080a030000140c0c0d5043c00303003407461502c1504210b50480c2d00491707003448042195503004200700c9049010600f41681d0b0b640e00c00c00c440c010b0f0300c409400f10f840c3e01d1034821103150042c020016071060000b001503920900642100b8001c0c110b40b03075a540d042e400d00a2100e42d8108002106da2860f10300140306640c1822552929070120388001010500c010440c401c541e034040c00303020094011030700780d19111982d6401d82c00d020341a14030094030301c0d450a00001e072812010300032a40c411030080c01800c803c0d86040b2403075000704002008108107a98494 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 315889838 1250 315888588 315888613
    0x5040c081b06030a02090a0f0303031a030d02070e06010c0c0810061d010317040803180130020a020705120c01030b0901030b13080d0e1b0604030b0f070306030c08101409120309 77
    0x1d01e40002d103029174bc1c00291948503034071500018400c5908207102c0d521902150a00c6980040d2000944881003200803440e1140001600c0302009000c0040c81019840f4000c640f8400003e007185103452000f038103110720359841101c0614000d65007551400300000000500114100d82c820540c0060300d8070600386403640d01c040315811500220312034441903a000205190035039109030510301000d1070804c061581d1041082004002c1c0c0880382442c50030340c01007284903000e4000d000e0600180009401e044040600c00b240031345480b00c10510a0120349001400841e905242e070301181640e91000305d0715429154103450b0752040002c4070302111100000c002c20413100785107004086c14040364030000c00390b2101c42400c440494601e400707441d0041d031040c0010800302d0b102105071074004031380180280036503c4884045010300000d401c041c0a102c02003000080b080703130005e022146590304601c01c2101240d000c039503501001003507620007034580c41100b06d90200b000a100540c0c000b100d82003203e61001010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 315891088 1250 315889838 315889859
    0x40201090e040803040204050c0906070219081609060b1206060d090206040f0512030a080f090f240a06180e0109060e0303071202130e071205040c081b06030a02090a 72
    0x215822500e0f4034003c002d00045003024007625802c000c1c500380450074600510040780b1135006040e80644a00c0000c03001780c0c402d5001c5044400a840c0310703016112034942c2c588003c00318024a1003011682d6141110000304c01c224141607030440030b06000f1841c55512020104803043d000f00000200341917035000740e500165600c20040c0003c1006200d2903c03250710b444200560040480280f80079038008012a450680e8800704c41380d4099110101c203071041e19540792180c40d00300710782906240d62203206604055407800c04000c1070380b0030342ca0610340c80d02d9581c50b8010302601c8039481074000540030744c0ca2400300b06003c1d4202e4059110100000101524240c0b140d400740c40c800d00c610a5030b03800c00030a1101082d407181c84907040c224000029403402910032034020305807001d44198500c440c80c0341c000c150200d20542220301d1481500205000500309400c1400c024030780e52050010501c99441d5201181007a0160140408001805c00741181e99052242e0040d500c841891980200c0d040e81c04074041015 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 315892338 1250 315891088 315891091
    0x1080a0e010e0f0c0603010e01031704120b04061b020601030204051b07060603030801060f140904060306020307020c01020606010e01080f0702011506020c030d030612140f03041409070c08040608040201090e 90
    0x81100074003040d40200202d0781402c00015804d402000108014411000c843c04038038116580158803918040300c98041078a00e028640100641181440a081c2031007015040180240d00a41e41000903d00c12502c0800e00020600703405c000da040400104051301e803a6114a078000c0d0b20b01c5201d880b0030301d035101140b1a035000d0041100c0166544109200741903100c04118017401d8642856501c0328214031000e090740031881c09540d40b20100041542c52503c444e08603000440d448042903460b4102030001940b50111003281c82d00520441d00001c640c3c0d8031400348018044011703110003205e82c5401d041034110500041c505025907480311440016202440440d0008007110381c041c0044540d280c00b003500b0084c80f4012602010b09200b01440550b440c0700d45002c000b58000d108607410002c51440904103445244902c140d4080420300060f081c1740d414810180308811034200d40e6030340c2d03181003c0d0355840301c40700080c288000038082402101d006a01c0036800c28014141a04520365a90808080300320 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 315893588 1250 315892338 315892361
    0x41e0c020c030f070e07080c040909051603060234030e0d0209010f0312140d050402030a0606171507050a0f0e060a1205130213020d0209040603060608060c04060e01080a0e01 76
    0x203000c10020100c0005e41d03030b90000d84a240a000c1c504117000340ca01c0303d0056019110b01c45950781c5103035007000400c1246128804140b0381020b40a0380d00d080100003900458501c2110184091038110180f12a0303451995842c00c890f42030590f031129480c103e440e0440408482c2e04141d0510860b00982d8540b00032a0003000382c5080201580d042d031038848000d20514901606120002da6504540b06000c0107031101d0075401940024690764500000c0d1a2100c1c0c504080c1500b80350403004034401c0040325900040c00a047c0c02c89007070f00b0000d0404036021358100c4102c800102d0521100204601c1080103990391980c61130a0461411045e000442c1d6038030012051010844412a090f201d54050080942c090040140052030b0b0f4407076004104d05038205144518081d0740003600079800041b0b0390585417285000f0b00200801c039140d1818000034246401032541c07511880c0700050000ca4004100c03030948030103079150446c40c800d540065030007980107013040300c0d8107071038042d1004450401d01c2061050074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 315894838 1250 315893588 315893593
    0x301060e03101b09060206042118060f020708030f090d03090902030f060a120506010b030c040f080c09060d080702010f1407110a0501030e0c060d09140109030e041e0c020c030f 77
    0x100390480183c0340020551000c000c0d0742000c003c02010583c00c008003009e004409495038a04a0760f9001211904038850001c180120196408990140c3c0140d0741da0040c42d464088881072501c2e240d03d95524020340300f0342d800c030314002c00155050381480140001d00611900340786008941701c1042d1003c2e0b03041219128406044c030410031a0902e402c1490800070581d4800e0384603440c07003136180c0a484401c1406200c201e058000003050704202864200c400038802c0e08a019075140d00c5004403900e030100b80715940d10600482c0c01258203807030300c206803420341607029680a190440e154010740340000e40388006414040545003240e08076207070380020012a4415035120035505085001c2081c600304c01d0304114101443e00308030180c016000a60318450800460710641c03640018030244000d0040c0d100001c01554040d4800d60942005401c668010740c803c1c0c54181004030504140070031038900701480d1010850ba0121f030398855403280c0c0b250301c541980313105640703401179440c01203072402c1c1d0012960002c0381d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 315896088 1250 315894838 315894881
    0xf06070f0c14010806040507020717010e010b0406080d0c1a041101080a11040e0c0702180106140901090303050a0327110d050715110717100606050301060e0310 70
    0x3160580c0302002d40b00b0903000c1c00300011a0740000b4184000181054025a41c40c03011036178050081100d98000c20802d000902248940c45105001c2c0c11007007003c031b080e50700f41340c0c1d03554642c49c2c54041c0c1130a8658150080c01c2422496000700d4084d1403000054903a02c1e0549040d0060b5100d07030100074401e038040d00d40c603201a035183e000100308140c010441c2010702e240690305103640e00030108a42c00c540b80181c1d088926190800003901c5480780e140001d51000c1030501500140c041d003c803d604030b52968889886441120f04902d003980b0401418600080041406200003030288010f0301c190304103464000b0b040000640b0340b0b648604180e64a0ba0b08400c280f00600c1041218085c403a4a080140c510440355a00c641e60b05a0300c010902a000b0140c2c41e042d42004d000780b2500c0326641a241138411544040d40c1c1c0d2005c440620a0381411203074600880300104100f800e24011001182c1a0303582d020700c1e580c6400c40460b046100f80a00641c140903445408003a030302c050103050064401c091078000d02c07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 315897338 1250 315896088 315896093
    0x706021c0e0f06010e1303050408190209180a12050d0608010615051608070f050a0b0609091b01030507020a0503043c0b2a0d08100f03060207020f06070f 67
    0x341800b41560341030070f82c4000c0c014407100d031001c00a1034103e90380c1014080c07074400c98581a0750324000c91300b004902c0c1c451449442c90200c1d000907940381960007616281d296888840d1240c4021500307880140c03044d44018070500020340d6400517201140e031503140c460300308880d80100505888a50744800c103180e440e10001d200c00b02c0120028002c1d04410b08001d46450540c240d2000740c04102c81002c3c05a600c0810403c051141e007040805086a01006a90401c4407034507102d100e200b002c0c0c40050160040000054440000090000c944001203110b00c4e400e0589800441c01b8000080506086000350140ea80001c0c1b010000b420281982d5501d1100c034201500c0d0001e10b0501141070203607075516580230b42031a41f02902d0064140c544c15002207586d04040705c09000d05483d00c0295140038040655011044580880c40c81503000d041e80c1c0b08910f980340c02800c210105800d01907a400c00342059000c10018005600a00d070b0301c0d1024003040c3c00000c0000005559400c00401500d018840004074003c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 315898588 1250 315897338 315897343
    0x1030902180f010906080a080c1e0303010e0109020c1e07120305031603110f090f060a0302211605031009050106020a1403030412110c060c0d090918080706021c0e 71
    0x150014010030000c40e45030006c480d584403485034000e44140d50028220302d0041c81407200502c030b815132240922100c1601210b030f641da80e000f449082001700d85034001061007016030080f41c1d00010b042008001140b9000c225100584601d18003410910a40300c00080468245488040441c06901d40030307205c2c0751011001c8620345040590100f0507280089281c464984003003500c0700d01c004d40c91466110b40140d008261031920003802a80d1040e804150800106c0d895001455554501d401e002d00d130308a104005a200c0000340c40141691281120107074285200b132002c4e640c0f00c40c0e9506211903265482101d8411140d00ba0443d00041c1c10410800b010b0203802c0c441e200750b170f15000780110b2441c5020b48034103802c01c4807005c00070204068800b030006140300c20003041d04034176401842d150f640d040040c0d1107036441b1070f922030840200e5001c45001402c40c2061041907030100b2007020a411000d900c0d0f83d608440d520401080300c40607401d000c500083c283c01046840203103c1c0b0400007074810030038030b9001d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 315899838 1250 315898588 315898591
    0xe37090c0c061a090f0a090c0e060102010f110d0b03030706060e07020f0610091a090109020a030f0203060907030908040f0e0609090c0f01050a1101090b27120901030902180f 76
    0x401020044106140c15110f405409074441d003071700303112006516121403040180c50741d14000307000c80394203110204a480c00d018000d80540341c01d070000c102a101c1088840150344940040b00c888070424004804c54525940008503090802010349180c94036550300d5500301c0742e85401040c03824185000300920950100402514181c28500928003880d02540c2d10503d070b11140603a40c0c0fa113071990f44840300560345070711088c8641001030958040b9030710341c00e11100079007140d00c001c0b00080c24020b0081c20904180300716802600d000d0280b0510380e650306016800303412118030858515404010005060741d501c40040090100328210140354106a0b003042105580070301951155003000d4083d0300f0301e81d94110303400003440e400c0c00c0480c2c95420b1203030b0030703110084000d00c044155401d0900c414200021182900e210340d4015800100010300a1100302070021002000c040550091071422800081d40c0041c01040c0014034010482c40150760100b520001e85070004490800c00300180030100305848182d5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 315901088 1250 315899838 315899861
    0x3150504060501050d080a0f1e0f030507090308042303060708010810020405030c090604020c030d0912030c14030402210109060605010216170c030d050a0e37090c0c06 73
    0x400a809030ba4441b0a690302c01d038000d8405102d482d424a5151a015220519240c00414620304a001440001400300402c40c445880003900c0e01c0001200c0034010740602040d40d40000543e130600c0d0400070040c40030440000c800303480d00584510083c556a003000f84620504c51643d84ca1125403400c0752851034080e814100241050040c44180010740340040c0c075190002c0111458007081d107849011900910039200b0a601d43e01000802e9030b054900c5410424000384104200d02041005440031804c4503420440f4000140b4540411500c489110b40a590802e0005064558200d20b490f00c0d0028040062055005651540021028090103110b800020402800074105c80e5091190609903400e0074018210030815400b4804032420303003089030300340050000e42100c6003d41400805003068003c400d03c2400070321510044005070502c810b8401c107081c400c4042d060101440e414a840403020404040301008520000258002490141041e10405501e03090001c0300c0c0350505e5001da5081c02900c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 315902338 1250 315901088 315901099
    0x60812070b240d02011701140306010902042103030f05041118010317070c080a0305070c141c06020904060b0409060f08030306060c1c0216080a050d180315050406050105 74
    0x1001100c076100404251400d02c01c40324075000b90600d1005942403042848032101c4241030000204841c1c14000b010a00c4410440490746540e9807264888240c0c804c0303000712a82c00181c0303031124840068001d0b000e11214820b04010449846403a001c000302e9408403410b640d05240812001f140c1d04140724051440d080c0d4001810701981552600545010032104400b961000010000706101103126070300041c05450003902d4194010382001000794001090546101080710800144045062000009440c5c06800c0c000745491701042c2841041d00c070302040d100d072a000c02852503582c1d582e1248601900200801540303443c1080c016004583c05070b001054050035140003845030742c00000541c2ea10078821100d41d9590f1101c40482c42c148883c24600f000201403034a828080c481c0c001c02da400d42d80001050310030031159911071071650740403403c1003d4900c1d04a405c100304240d10800f1303003010300d0100030a4140d1084c0e4a980302c0482c0f00354420030b610419900d07801e020411510740540750040a04458 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 315903588 1250 315902338 315902371
    0x1b120102090d11010909140106030c08390307030c02010b06040b07060e16080f15010b160c050a06021b030303071d04110315100f05070803060301060812070b 69
    0x414000055118064082030f40c0070265601a0310034040d02026201d1120240003c000d41d61401100d10030a000e4000428280307041620321610440f040ca200b11840d9048900310361098603040c00290154928110040d80350720500380c01a281c42c02140165a65600000c1c94060100024211182c90143c41d12802d410013003082521210703001e071141c1c0754220900007008100745904614100484050303054981b60700400040700c0d680030070760302005480181690b10060070303142d14811940003401350702c50f80f61081c01b00d120030030314000c0e2500b90b0328880d0340c80401050300c850008440c8182c80e405000160300401030034003079480e66808a504034400307400560440c140150003900c6940c441402408030b0b07010300c402a00650b250f40199011400b01311646503a070400c4401401107942d04c158882c007038861030b1500c0c0d0609100340f1036a204005255240e50030440c1c04d90740c4000743e80c00603001e540e06640780c140100d6010f9050107804050100c1220031592183c0342d00d071450380700070300400c11214080100d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 315904838 1250 315903588 315903607
    0x1107030c0b06090903091e0d08030a0f05060d0305090406090e0a17030108031e12040303020706180203030912010e0d02011e050106021b0103140906061c02060a18081b120102 76
    0x565840d1b0764101c0c3d1950481e03807111401c6048641e1000890740c00000121200103200c0c10741d0095000d6035010900b0b114803600a6041c0d07003a550241e8540d9007142d003582807440403074841d0b4003801003403100510202d031f0179a45550180648000001107541a04140d0822007008010580c0d06030806580070400c0c19907150030a045e840340180a00b19500d8541020050f00442908040b01e4854440d1066084941031605000b0020341107218121800307440c2000020301080b1854241c5a82580100118a028241410b00c40804c2582d11145055925031208990403881030011400c0c54140307500010f501d0a40d1608000b042101c21061000d040c5040010300c500350b4041543c01c0610040100440c0384100440101c1c01490300d02204d0403c55403c0d028044200400301e43c0501807031040b50070328910180e504e104484800c00c1240254041c40c10050441c03128054070312680502c1d0030700030703843d0b68030380ea80603060410445843c031482d41c1509e81840901441d02d60501504010250000c6007081c0301407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 315906088 1250 315904838 315904843
    0x10303111b1810150201020a0905190605130305010603050c0306130c060320030703061503110304020907020c1002010207030914242205030106050909100504061107030c0b060909 78
    0x10710302002d05036940000180114a0904500024155460040c00b400c0a02c00000d00039044000220000340e03001d070380051185041c40303107603040e484d104215199481c9800d030180c44035440206010a0210035034000000308c0c0081c86007000450142001d081c920100400701414100014010030300c0001001c44000880c540e0158031040d00d40d90704000480070411002d00c04680440d005505000d8000020407044a506400120458019600303c81c43d4a81205003542511179001300320684a1003400080c0c0541790003ca0b00c0d80140707540c01a224880440c0000c2050991a40450303001350b034000865100f09640319840400030683ca9520b171080090701e000044040743c1e00c52074000c040f280e000ca0451002048011110010f040d4201203840c076100c3c001e500030520a80c442d8500c070b9441c0c120001140c1c00d05d4441035100d200c1d400090036284004040403002442c01a00070746d0120380d121340d0009070b0300e940d42c020024540030340c072145907450707003441c14604562004203030320700884400c414041d803607000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 315907338 1250 315906088 315906109
    0x1201050a270207080904060303180e0601021209061201030305180303040e060111120d090b06060a0f0f0c0204021b0105131101030b01020c03160509070c120c080909010303111b 77
    0x401c0e0240c0e4401c068204403200f4040c41001310f0340035180403c004100b542000000c450b1008101c0c0240055070340340141144858110b03055030243c0c1024610b500e0417501e01d0020070414000a020070b041081c0ca4803145220746098004038007003600002c02e50240c941000807a540282c04130002c610309803c082c03840d06002800707007142d41031044459801d0040e007410f0041c41000c05088101588841002580380c0c050007c003e020b850040f000804180310382040c1c0e0480e40b140d8a40c0d2a048202d02580700b04131034030300c040d550075001c0001c141c81240042c3d5650008103050450505034518066500c21031a007142d0000d0001c5e1201d2010710507040004080c0c01d5100b42c06002400c0000b000318044c00141e0818070001d89450381402a84809900600b034003011005036001641c840c006507503421000d54070700100c2c0c5000f501288090742c404074414401c28000038110310074401181001d2802000c0b4040090a8108401060500c000d00d25504000c00010348522510007042070b1040000021800c841e00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 315908588 1250 315907338 315907409
    0x1707080105010b120a020909092406030a1403120903041502031c020a05040e1003110102031215010c022110090c1a3006060f1209010608031201050a 65
    0x4c0700140302d0800c9030b41a521001c0c4040c0c011036407850401290b580303a8040c140700102c5140c260204a144100050510740f1400019004005100b1030b615100d4040d011490042400e100400004001001148840303000310017190055403101d09110300443c91a681600c03407000c550040c00140f41e045040389003004c0c0902d241c140166030388403800d400c440511440d00040410f00f031942c00c1c012030844654040307007168002d030105c0c44400000300049840e031241950074403a21102e1004a65100821030009411007814142903400304d0040e0301245400c14a0152454140c60402800c03590081c10b00a0324942c010000c8100500020355507034548141440c00384e1100c101e554209209100d08103421625248403044461107001c4880b450041d15014880d03001034400302c2c040104100d81001e0042c1c0301d010300f0420303241c1e08005230142030340d880e898010040325035503485a00010b0580824802043c1c03a02c1c041f4005c0e2507641c180418080483e0099108404000724811103000140e6510041042041d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 315909838 1250 315908588 315908617
    0x1202211903140f18030319171e0f0901090b011d0a0608070902131a13050118060e030a0204020d060501020105150607150b0a060f2c06160c1707080105010b 68
    0x1403c0302182c614020007042c4101c907587c507420480f07819044510301400014960380210150713158807614001c80a03403501e2001d80100c0d100401c15045c41c42c01c003a640110190000034020b004e50b102c0030f07046082a4808148240d036668915401105007249a5004500310410301c040f41c940400319584140c10f1040501482e804901030720091a550303800130081005280d503070301400340b06407626140e500110004844801c0c000740010154090603c00c0c0c907205c0c203134142170600392401109036900d441184d070300703581801001020801a5218406400002e006490014802d410a8006421920064607080c0100d5800c2c00f8059150760302804c603000310340e2000c440310072064030240100c0a0030440c0b100326030021303c060b0007140740ca5009072000750950f1139542d04940148502a400031541c042d490301c0c1681d0b84001a48502030030600c00506031006d0101c8098122125510754801da501241c00c000c040c4044c0c6c6100408800d4200240e201070400b04000700090751501c00e04266900c2807145900360700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 315911088 1250 315909838 315909877
    0x1a010f0c031106041b14010c0204020d02190302040819120311040b0415140306032d0105010e0906010f0e1b04080109030210060f1202211903140f 64
    0x180300303009440c19041c0140488a69084c903103820800f0400380f0200b8118001c1051000030041e05440803100004010703100c540d0300c288640c00340000307544003d0384034415540801c25a42e50401022188900c0c828650f00144c0384c5040400d02801c00b4001480740000c40040303480700010400440c031030851030055040020311901c184414141c64016540300740c501f07032800b250000d07160000c016010320311644d0341d9504484440c0140714100d180000d441980c2c050344020041003020111080c0b41d1030300e0200401c1c02a5103800c0813080c0342940c0d026000f6510300c0301080f050081c00c030b0381007200c9409800c000e40c1c5d4041d41820862000780e48440207007111a0b00c00040c090009200d240740446000d48803580080c000c0450905000c1e568a05010700021b290345040b50004e0103020780c8603410f099655000070700b4840d4103181c0820030304074041c0f60b490380310081e0240b1241030410100402104c80c87c80101511840035182400340030500380c48440003024200304010320f048113800c0125040d1554a19405004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 315912338 1250 315911088 315911093
    0x6040c0e0f0a050d0f170715110d060b070215090d06091502120f0a02130302130204090203090706030f0b011e11032a0f06070c050309090c0d1a010f0c 66
    0x30080c20b6400141c014102101007020321171040d00040407580a101d038480e03031504054804446124015003c0d2000c030f40d07000101c0c01490243c11901582003200400c509011078070071000107c90740d0b41d10107031820400159010440c100340a040003c036802e91203442c100301071a404200f54102140d00108130030713640e0004008200b401e010118000241c107008541352041103017171045088040c0c0704080b40d0884040000c002040c5402105c001c101c0c2d034521115018516400e100e0201503220001501c15000d100c00300d00c0512500c0914407403514000200702d0720785000000360840e00c1440115103030300e050114504d5241d0300001a000d0035078500c1c891310260b10350408100ea00041c01210142a4080000d810102c8000b801e20424001c48541c4031410107001e00c0601c0b40c0d41d2205a012403210380080700010010380c0510f0403c0c0e8080c0c00b5100340c074a4080a800001d00c8100c0032076a81c08051000b0600410034844c0d40b150141074180340c0d6030703000502c201100103482d540080303191000300308001804408 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 315913588 1250 315912338 315912349
    0x5010e01061b030519050703111204180207080c06011e030c0b030c19020606130618020a05120705030f01050909060105090601020a0b01080c030d02031602060a09031208090606040c0e0f 81
    0x7421103080c603045d0007031420b000408540c003120713003500003d14007610526440c0000c12030032007002c0c0d180501d610b098035000307458000560031803826128582c00e1100d5004a0071003001450300b0522075002d40f81a60519080c1584d0201d4888052007520f000001880003546d002c08540941e412981425102c0ea103000e0821030511510084001221144682906154000400901411048808901c01c00000d8034941c00c595141c03080d405075522910508910300d42585c001d2201841e2031420354507249503941000909131003500e000780010030010401020b125911074040c09454201e840309458244098151b07a00d0006000d01d6102e081804041403841c0e0081120410095006125403400d41c0d650b040d00d6240c001c96000c550190003003615050b4410710100c116210054403142401d04262a6020310032250009400340040c400d02035400310114154802c021100525591440c8851500e840f116040c004080c0c8142d000d0307030a08802c04605034010300448903030b00c0306550341c11840044800042 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 315914838 1250 315913588 315913597
    0x9031403090a1502090d050c0405060102190b10030210170705160201141c060e06010905030d050702010201060f0905070306060503100b030a0b090f042a170708010f06050405010e01061b0305 83
    0x1b40c0c403528500d6544108038021038a0301201c50201e90803c041d035610401a42c1310100f55140071550810381044100040f03118800d0742c2c000d4040151452500d0320795020581c1c54012501c132001054101c05030189850004042e44d900000c90b24003141046588400000b0031a48400000e05001c0680b406c0260704d481c00c02612000280c90403910601c510303844600c00204400d0141150410a0354001f80c000e501442091048500281c0240100710001c0c40403100c030b07000f00800b01d0444d500d9200010b900380e10131074480050490010005030b2410a031101908940c5181d000c0000c0c0700c418020030180f848212000da04440082140680d6075581000c0c00d00280702e404a0540c2c00030088040c440c2280c14401301510643c805e04d0702c5281d4403a0004d00c0341981c01c8111802218144502d014851817a00826002d4800d030560100c403d00b41e1140c0b01c446c00d688800b00c059885594806c4108000d03d0a4000c0c03c1c01480c0003240070b812541030260007408005051041c80d40c50450390003501c00c06109030b0449 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 315916088 1250 315914838 315914857
    0x9050c0c03070b09010501510507020a090209030309090703110a08070e0d0803060d0f060203010f060801090e0a060b01030209040603122712050a12030f0f1e0e0f03030a09031403090a1502 82
    0x18a0010340002c01270950b42040030143d000e82d8610a000c10f082009108450380450010000c44c103000c1900c1c10006605001044c030001c040d22140f51102a4081d00003038509000705840d90038a516101c20018154190071501c3c1e03102d0000003c10340c000c0780094003180c1e004042611100c46076405414800c0003107600f40340061450788004000105412148254406d41b1240d90320002141d0fa64110b400c00c1c3d0f2001c0e01a1000c9030850054000007810070b0380214200801810058240455040010119813142d0300a6a800c1c3c08582000c0685621a800c2501104610300c408000c800885104210082501958140c800b60345201707414000100154410160700c001641a1001e00403002409010080c0ca11295141040c0e804255041107000d0342d1041c10050340c440c405c41465030790740c8000c2e25402610200301e000d6400c40b01e03810f40e800c0c40218460f40d240e07000822024414500186801c1001760501008403042c402d100c50354101040480d030060300462030703500000d0141079046c02417084000c0f4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 315917338 1250 315916088 315916229
    0x60f19030807060b01020d230315190e06031b0d02041e0209042a20030403200f0a0303180e040f111909050c0c03070b09010501 56
    0x80b4020800f15030400050407400382d0a6076060107404106440780c4004801e0000442d068160f44001c03108884013130343d441500c03070505412402d0990b010444005000203045a6114101c07002e00a40080015542e041082540200860200e20810791582c4581d48080c0717100761302c03504002e002e55549030000c04a140100e1241d100c01c190b5401107030000d50000408a0241d42444502c8058021007110f01d00e0808801740341c854b8118940404031080c50303080181c00303405c540e091900901c0031400c0016101075480b070352441c0709501c09041c2c00074084c40100c900e64440c00b070894044105072a0b070b645441c00c032981341c20181140028000150503200a076000045c4a046ca4bc0410060040c410722415080e4001c000a03400e04403d80d0034846000340c035030081c45107010700f06000c00103a00c00e03900803a80310170030648003801c02145000050841e0700c150800d5900e1000d00050045e260428071841d0b004101082a82000b0340342400030408a29421405038007055444066030200300c041a18982c40c1d071000c420 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 315918588 1250 315917338 315917347
    0x31091b06090b030408040b09010210110d150503071a0c150604140f01061103040b0301140315090c040207020f1519110717120304050102031e060f190308 67
    0x4180842506200d80c5001501616000801a002d10122070069800030b14503854541040f070440700b00d40c000780030b0038114410f8100c4644420843d120b805204e03400402d9180c1e840e10095186820350380c207104a000ca504ca84001001940d40010f100400c541060940281c401d500c0d00c0140402c2c0034032a004032040c015068001b5140f422803c0c090310503441110104421190090709d128400b0301142d400c0f0000103040014003140313020300d0f54545a2080101180d10341a2540c48a0800b5002070b400b141040348003240ea500700d4901840340c016602d1401c50503900d2443c01f5144e05a80d10346811255004590000d042c0f0250f403221010001c07448005802c051200303150000e4043c042c1c0c84080c50700400180c40e0104a105403080e0032104248003201d005010710ba040402c3d04c002921802403001c0184a21000300c04a50701c6500610300c00c0740510300050b00c034030f05404801c181d92080074901ca0140c002000300155a5241c0142d0703e00c69500f41c070f08402601000780880c2d43c5003070039080604400004207 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 315919838 1250 315918588 315918623
    0x70c0c080607031e1811131803170403080609040f02042a02010905060c0f22031106030103021819110403110306010b0d0b0f100201020307020c3109 65
    0x1040119000e0f404c4071800c1e512071000b038000341114004020300140d400c4086401000c1403100f480220704003001440114a03255400a0104891419043e98146641140c040c002c0c1508040080342c21000200412032a10b01950020701290009140c54840c21041c1c02280c1402101320114100982c041c008104e01180c0d01140c0d401c40c012040150542100d04040c04000c0380b040c05411109588103008050075100d030b505844030342d040000c0c5040220424400710248041800c24101122040b50f0f03800e01850a40c2407050001805c1c8041d6401003004100400041c0c440044050f50094000b44904240e20740c00380d0000710b240044141d82c08182410107441c5942000c40040c02103920a14000740071444d950145501c41d6024426142d0200041c4525003860649802442000c1030080103a031022149200140c929904014100300503075011080000c160b4040061140c022821981d040c2625294410141130507804180c030140c0600140ba1100b01080e1a040345808550020015400c00c1900 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 315921088 1250 315919838 315919841
    0x6040e04060b0a1a030a0213120c0902030c03070c051c09080c0a0b0f0309010902060324190603020d1d03190822030507050a11130b09070c0c08060703 66
    0x5803000d580942c03901619070640d1805986000442d14606070103250001131182424443d013004180f05400c907002c108003542d0500000000018022088040a00c40f1050418204801c9035801070b2544610400500c21900e52050650f98007441510f450303030389d000091411b1400d004046403084882e6030340e082500708207138000540c00306550344141216640c0440d03501700407400100f44076084c03182d0810080c036101d0515007001164481c2e0307040004640381807103034003080e001c0d402160040001c00c2d00303203c122150781e65119580716140080b2400e1134620103c400039580c00c08184600f409160f80080d00d10910365542d000380c2590385441605481e07201054031400c5d100da102040c205a01c804000070b100031140107441060280d1940c0514541e00102c00e11340c00c0c1c0c00c0c183c108056003406410301c0f040c400101e081048000031071103500307155400c4058a0601015440c540c900343d62032070a0801115490700c4200d0307210780c403812900d0710241433003560909444503645030f0014412401103608008081c0d406 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 315922338 1250 315921088 315921091
    0x8220b0a030e07031e080c0604030f030b04050411130b0301020d020c0c090705071b0e2a2b24141c020d0305130602010b0a050a18020c010b06040e 64
    0x161002d1101d0700340c0040142d256059030100400714250311203082481e24400b800300f812140b08100d454546070220040c10700d840800c0724102c000503800300b90406925414010703507004800556090105041507a502241841c40d40025405903030590f004c55206c91154001010600020f4000c560306c550441c1008080e620180351404103101d200c40c0c088542c101804d5151043c420760f51000d0511255130394026401c0103101500c01402c0c2c0c6504013103109151000071034065841c01c60080e0101e05641c0b0a046043d01c080b100341d40c454018480b2543c0c10076a0301130642c21051175400d0031000d00c2c60b13404910003002d000c0280e01c0c032010f10700614800c2c40d101225030001d4403e60b2719484202c08200f0108045101c001c80004228000000c00c8401401c000b00803c02c068400e04046040c00c0c001006036641e001540d002c940180e449144c0da02c6542000424200684010380c2d002d24224101103103c462103001055155285900288040890000b9030002090100c02001680d03115500c0e83c1c0c24008090 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 315923588 1250 315922338 315922357
    0x10e0103061a041d0c03181606030e0706091406070c0f12150902011b020a0515040315051510051e04050913020102060601140f07080703081e0408220b 66
    0x520340144c40080d4440030060b215030140c140a07407850b50750700400c06e075541c0c50458241d00e500c182e485d085515035400340382c00081c0c4266580007581805443e5034900e40105030f4816824031894080c00d000312807882d00072200340e150a40b0416921035280c6840c413180501644000000b0107040400b24101c00c06092031800d090043c442000500c05084242049031159003009000c5084d032880083c01d103200030300403190280000c0409950b070380c0e20b8021a01010001c0f0107440d403940002420f100700004203a004c2001c0e44159400c014078500580032440d0310600c100c0c0c489c410040c3c1ca03491416140b0400c100c5084c0c4002d003000c02da0700b203d82c000c50307a156000360184070310036995040000c4200682c85085108150140e00034030f416101d000c01915540750041d9442d149501c01c03c039548040d4028070041024600c901100c95840401c3d00f401800c041c0003a0209000082c1c0074400300541951403805504190440da07010b0351400450f12032100726030b00401c03030503d8860000300000c4407806075000d44110758 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 315924838 1250 315923588 315923609
    0xd15090f0506340210050a0b0411090d0b18011503140607020a0b06030f01061d06013b100c0302122817090d09090e0c010e0103061a04 59
    0x100d815103842c04031101980380540c5030744182d007020300d4020b0f0410902d42c42e03122401a140f50805248802c0160743c0c0031182081380b140c0b5086e0301c02c032606042c82070004289d000c01b49203040c0b410030707c00145c1c05000814064019002c4101081c4140f90401d11400f0841c1440c00070881c00da10f005556000c8030381fa100c292109640071b0a100600e00021502c0f600c00c098a80c003802d12464203581c1d0500390080506241d4151082071141c100740d400c244200b0001d0b02002e11404490326010500000b141c1d03009000740d0401403005c0601c07035a50500740f18002c040400d0109a9051202e41400e1100b0f5106120ba1950040000c048040a0740e044030014009a009070700396400841d0500400741c80c1d00c42c0c655280d00c4482c40d0105d0100c1d40501056200c00600249400415085286080d07000c1510665003c902a04102c8103010b880b038220001000900e6442400d01c00750220030300c50ba4460f142420090b060041c0d040703c200c81603200c0d038000c201400394010030342210107a12080c4c4c441354000340030385400403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 315926088 1250 315924838 315924841
    0x80709050615030124140a11070611100905010207020402031f081216020d0c0312030c020d0c03080a060509091b0301090209041410050a020307021902030c0d15090f0506 74
    0x42c2401003240c0c10f880c282c15200400040d165549140c121036041a07508004c101c3e400e0116210494005112a94039956104210341d0007600c01d42c10007100c0d60061040c89001e081c1c14030290f03c04110030003110940800000c4c40105418a240a4031072920020741c054400001c002c040720010740000d203121109d545450382c894907058040e9840042c0b4080040c1004180301c0759803481c8260712503848161010380780d0f0030720907501e0752007103810501500219110101031803110020ba0780f510410402042c01e100405001c4680c91001d0301c5c080940c20b014080207102c4000580004003600090300400c005013804004c0d10304040e4058985144e400d0908440340aa40c01c00381a150501410840b0f6400404842c800d490700e0350b071085030032881d00700140700740202800074006004900c5018860601c0000c050390724601040028280441d60b101e0313660000581e6100d001503180020700b4000c140080d650070000c1d094074103184c05004505000300c07230750900b00415071041000d084c1203440514499070840741035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 315927338 1250 315926088 315926119
    0xc0f012307030515040b0a09020a11150c1206010519080604063002010215070206040b01060314160507020d0602090103060e010303050a0c060902120c0102061b030c0a090807090506 79
    0x3c3d118252015104903168001c000014905071780500684880188042221999803c500381a0382243e81c0c4140410065071001c0080241407040c100080508020700760946401e01c1d2103070300c42c0a4000c44000341c0c000b110000c1c901d0707406201140c0804002040586c2c00c1a801480200304010482d22903010f1030034141d00099400f21103100a42c030b80309000f424116442c6031a90300b030740031010f03803002d1313046104621007074900c24040e81c6190700410700d603406490300f445c04d8108244a0081a4090000c0510741312240c2d200d03800e00c0c13070401e8104c01104100982881414401c4600b4002c0f003102070341c0180d0011100b41001038590041c44000000c0c1c03070910405030b0b56680920056024400a17000c03550821038a0156485424038600c00c0b0b10400c000039a030b03911500414410382d06c2c0218495284d11a081061039980c040291076805501041da070200d1019901d007140c3e0038040503003401e00304c5e03901040e81e081503802030700801c0c082d00c456070407a00602e80d241e040e02d010300320503036101c0d0207030b8550440c00d81e8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 315928588 1250 315927338 315927341
    0x3060b15040902030a0605120a110105121b090a0905010e160512040303090807051f06060f05031e190c0518190b0412060b030d140c0f01230703 63
    0x488541010066040c1440c02120501941c802020104000c6c3c0e00d00d80402c01d5600c044e401480410400000d00d002034440c5800c41c01960440c40d06814480c00380324080a4451100d00140d111305460008224250f6007180c9001c1070040c0002d06a2011042101040c4011541d109904a0f400500054565180e070549400c5000c0f04842410018004015141624901d000b040385c219200e842c00040d001910388403003819411241045889412202c40508035444840a4139140218140200041403409002400c0300310a10100003d0010110000d00d41c070030642c1c820788030f020403050a00c0c81440c08042143d00b058050510030703d224a49040011002d1148050703070034000403241100c40f0b03600103000b080403d2000081c1c41c4160140368401141c040d4450001d807000301a0742e540b01080250502c4e010050300d4220302010f0003030f8005440100c140e5070040c90708030126403641b0002d960350940c0c000c05003003d1011060000700c2d030921810030850349074056040c05004420000c4480c17030712030980890 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 315929838 1250 315928588 315928609
    0x1b07050a0803220317091003060f1701090b0109150807060509010c0609170301050a0e060306010501050a11060108030703110d020a080a170f01030b070f0f050703141303060b 76
    0x140c1070b40140034543d0303031040902c805114000014070b01003030255a41e03100e8a5030240183e51146000000c03c10600c10700303091010201d01040b0381001d00201d8100403040c150700c4254031400c076500c1c3ea2043e45400f604000e44c40300ca0015081544c0c08070540e1162901000b519040d0f0920000c1251401d00003074403203002c61903409803130440c2c0c1c50034034002118004440c08018a9815210141d441d060700f00020a040b50110f921003640104684070340c035203020054244019406a40c0015084040003900c0e54041960f5040d141c1c2400c01680f0383c1d428100c125181c2400103600308481c0316580020448841c000040e01d0510300c00c0c0e4486000403000a10540c844504001078000359101030007980000b40b00300058000350641349400c181400c1a0401800061820350b203250b4101e80140042c0140000ca0b500507030b100c1ea146c1040310b8103018107500140200655118082046070215841c0e04141c421381903024402d03a035104098075080d83d4810b205a500e4517201c00c8542d5803800c6221f03011801d1140045 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 315931088 1250 315929838 315929849
    0x6140714030f0c16060506090a090305040302130b1c060b1f0c080d0f050a0e0303060901030f020a0902040306020a090510020705060f09090403050c0d0c0c18090501021b07050a 77
    0xd030071a20b40103a141c8202c1d0010b06000c454180034803510000c015404070f0b030f04003e0b001d1070001c101420154103120000350080c00c011241d41c1407220900101c0e030480704480c1182e82c10342c1d070ba0400d141c8080d100c5000741020388040350700098421480c000c0d5442000c2d1280840d000702001c122103070903a0100500c054100740c400c07a22120038944001c0c010f024000703502d00d1a000d500011301d020100107201c01259480c06485c000980c2d504240888481144100882801039200440c41c40c248400000c00e107603814403005080700544c000d004115102e800322807000b440d8208041d500c8684034601940070f508181c4940e0001581d900c0001001d1409540418103000e00e5005032200b20305080920065070f21080f00402107103410810500301d9115040d0b203134401c038043c3e41e9158458800c103002900380501721b0126004c0100d0340340e001c0f010640080000003116000e0845010820040310f8450140c5903414001e0001c0d4404112000801c0480d241c2c18490194481130380c1c800b54440040003801019070042 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 315932338 1250 315931088 315931127
    0x8040b0402010c0f0b100303110f2d1b0f03060f0705070f0b07091e0e130327080c010503040b1f121505130215130306020304061407 58
    0x1003000365000b00d0041a00c103010700c1c1015025507594888010400e41078607151026510800100103065101a059629140b26806004907907681d071176144e0303101409104040000003c001c40000311227080e802c0500d1030001c0e02610864500e5003010320700d500d6040b600c0ca0180036001e4050090f4500030820174442d10710b0301c280024a48903046e04440c5500702110486501007510940c50100302c0c2035601d58441c611565a210125040120001d5141042c00300440841c0011070b05003c858003108440e030b84840080400310703815459083c2103071150380710014010703280300380d19078607601009800c011429a004902203440340c141d5800111600e00c0115406050035030100045004004c51540b000019900704150940b03041e01c0d251203090aa90f604d108681222209500c00130f0f4240c18051158450141040140031511580100f0301c512620351108840d4070380014000e0400d12440360540203503801a030115168941072500c400208107920182da00c0d040b0000c00581d0181c440c990f90002d00002510 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 315933588 1250 315932338 315932341
    0x180f0d1202070213180204090b0a14012426070f050f0d020903010905070b1801030c020c040509030d0e0102040305070503190f0303020d090602071a0c1b0705030a15050708040b 77
    0x1820008051180819810034002c40603d005031f034490041098142c020014080582401c041400480d0000341c244070040c2c0020004102c3d508550712000c0d43d16041c03c0356625402d0f141d40d01241c80803c01040c0504560301d0200e9440f01d56040c2410f18803032840794490f60031541142000382c17a01e000d444c580a000760030400ca0750040707001c81c1c1c02802911001800200703101e07181e655280d0a003402d6822004850301d0200329034080281801d401c0051090a0808100460b040d40d40252104180980c071030085807158089148084204100c984800e80c3d44000c02041d010802868081c0d4001d1000fa42d10b0711030f11030003054501e00400d00c5040814003814490441c2c030683d4414507141940301058080c15800d11071581401d6580c00740c900ca41d80310307520040c1e50b01098131782080304c00b40d461a031080d100714100802001104c00340c112100381c2c6140242d183c1d8a075907a0b640524100b001d030401c0c0e402d4081c40c0316902c20805030301d94521221103540d505004960362404225a000001c607805805c0410060 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 315934838 1250 315933588 315933619
    0x81512030a110c060f0d0b060906092107081e010c200c0a030c150e031f06080f0d080c0a0c08090f0904051f0203100509180f0d12020702 60
    0x1501140e08030b12041c0c40356440028000b44a541103501c1034000140d00040c1c2030743c40c61807841417442000c0b003243c3d00340c00c206400c0007250181c010502d5a40c05401c032040e124484a60a8100b140414051005c952203c1e45a00d815a161a010a00114441100340c4110104c45041c0209070a1070340d5a82c07115075103101d00103016103400ea0710500d0441409106841c2c2442c0d01c071320400f01e003d180200450030100e0700c3c0003079228100804454040c00c00c80000340942007075401180865075001c0f04045580c071100d0f0591890001d02256000e8003592092940300c5146100203e50f0114000540c2c841d820545e07603c1007081c1c4035200d1120941c002403502171807400040c1e120b401402030090054000d05410034004007080002100b503d040ea0950300840b5106c0c0440601c00880e20204120302040d8154140301d8212003500800703004080c8280f0001001407440090000d080301140c010a0844040495030368200d9103030b1180c6c200d2000060b20704131a00414903028000c890344154041c6c80245400000d5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 315936088 1250 315934838 315934847
    0x30c0801050321070b010e4203011103041104050112030906140c0a0c031709010e040b0103180803060f06030f040611091908070f0f060309050a060903081512030a 71
    0x795180a0086070078400302c004217201205144c041c01c10300003000c10340e00b0301030284804034000d64490324200300e0b4140015601c403d10704d0000c2440010301b00d594186511880000d0141041244a5420350320120820040c4043d5858850300c6420a4500b0011a600e511402d460501c070213802502084803054104110f40c800d1581c048002c1c0c044c4a0107081c62140d02c550b40c200000403800b40c8941030198014070520007081c84001151070b0700520343d8a082201c00c00600100d41c14550303907126564805036901d40e0390003900310034120090990b1000c4130b1002484c1c421002e1308192903603401038901601094142c100030049a006604024a401c010783da40c0e540c5202400e10001070102c0c100091150401e2600c85600c3e010f07041151038500207000d030138050501e1034426a1f921021944d4900281000048143c000202c207031205031074040384004081c00c000346040c03560000248210f151100c61001e141d4082161809100c0c0ea04000380252045401c01019a1000c03030024143d4004210214006004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 315937338 1250 315936088 315936133
    0x9090903070c120c0f06080402010314160c05070b040b0d0b042304050703020616151808070f080d02030f0f0603071502070b0c06060310060b030402060304030e10020d030c08010503 79
    0x1075094400c1540c480790001801c165580c441000b041f0840c050008540c2c041c050b55040c180c2200002d84185080c061040350300d44211091070600003201603440a001060110a0240c600b1a1415598582e54003131910a507016103542c20701186002103d002c640303803e00076150420031010084905903580c0000c404071180207002215140314240700000140c0301c3c000984072080b000406000c1030261800c080207407030001c01f040d1040900d84084403020b0f03145010618034076074101d0081900ca96142c03509014500644201600c103200109070b5154400003030700110b10a0840c000003004075101c10290310905082a28441c0d41508040b8050004020b10400c42e80c10303400b81d00c1151070740b40c0d9502c4078808541c80b58903156042d400010402c42d0a00b001c00c194103001c80b64070410048903240c070320b103180180006003000744102c40c008041410316206143c20b00c22050010b001d004c00c00c0b4800c40c06075642e14907900000210b420040c50003480d40c05042014100c64000e40030706026502c4a2030007980e60300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 315938588 1250 315937338 315937343
    0x20310110a0e130603060b030d02060c0304080f0d02040801020d060503010b01142a01051501090e01140a05030d092d0b0d14070f080c0c1b032109090903070c12 70
    0xa10143d44042c42800740140001140074000000e150f61400003803508140900345288d00790b42c0030100788a4110b01c4403084aa00940208065444a81491030b103000c40c89012066183c40d8000b00e8041a00716044d401040f000351001d4007040155910f4080c14242c81c003000c455070208240b004c81030b0f514000d0000400a035030010503004000c804440881050f0300d01c07500c50000a81d55081001003211800d0080601c0305400d00385626200c2ca400c803000112841409100d21207003010400d68219100c2201c07800145c80e0041c1a5a01e82940c0310008150780f07120f01c04d1000c0420507940c1071020290083c494182c603940300c10354500190625031200201e50107010316540080c1c3d9014000c00c0c0b2490340044901404d02903982e2071f500c920130000204011000340ca000e01402d07040001485170500050340301880400706414034540342100c40040d052890b0a90552080c4181c48198002041010001c02400008a170541c441d0f0b04c80d55101507603030040180040c42525001e500f4040701d0800f041882d0030b0362 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 315939838 1250 315938588 315938599
    0x30a030f020f0d09051017070507030306030c0e0906010603020c100e120f04080c10170405070f060302250b070c140319081f14030f1207020310110a0e 66
    0x1c0d070b08512842c04190040c0d510000f000080240300c0c13840e1412040300c03004030910744800703410310305501c50840784e201500700e90034410700003605d104160083e00320000540e000b040c2e07070302e07480d40c2c0300e440e0b0f40307800401c4032151000d0003440c0002c90428001c0c0b0aa031606c0d0100c100410044481210b241d0041242c0c03940140140708840d8001c01184d0110f00400315150081c040e140c4030380c03034410401d1401010b0000b0b1031051320115086821164081800021621103078020400c80d00c8508041c0c0c1000b52981045171020b090324808900c0507050b0300102920094030288110b0030384d06449a8a1141100400410420030900802e07002e1380b044411490050041030100c0c901c088954007030340b5541c0803c4d0810b008036400780d0f031485401d41105082d9401189801d0500c42c00290f1400701000748081d026061110401854406040d1010410074102c61030000445194140241607003456800c540c0040f444ae100c0c80320603d0b105e0310300e406103103041c16411483d14103059420740d013070300e02481004a140d0003a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 315941088 1250 315939838 315939853
    0x150b07030e120a031b0b0606030a0b0d030810050916140408070e0105040524060309010f090c210b1504020f0d06060810210816080d1a030a030f02 64
    0x242d850184490880c09200010702e520340041c900a040e00391890307a10446500100c0c05031000c110104005a404003040724079079076a564083d481402840344480450300a104400300303004054120340518010396144040e640d9407540d5108100d02c0d19000c5400340c60303201203002130740c84150054408400c8422a0003103a418036071a401036501d0118950b0089400f2510315004000383d040902c105074100385006415181c500b0f40115403001900741c09281401564004000381e4221000e45c071000303508144410510104196080c80744000c10280030b64200980d421003d56082001715140f0703440c0c03a50140003200690342d101107a002c10311001c8505600180c01700306070b440c0c502d440c20047c0380c22102060002640d6044c02c500a2200c0c000078000903040b06604014059011440c0310110300c10800d01c0b0f900d140c0e0555290001e0700c0d0084111002070040c00040400c00c2200c018058070205500f10000c0040c00c00720a070402040c01c050500c0e58243e081401d142c4003192003244000107546190040f02c401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 315942338 1250 315941088 315941117
    0x120b030a050307060f0b0d1a07051b100c02011512020604050a081b030c01050d020912070609030302060604060e15190b04091107050607180b030c0a12150b0703 70
    0x2c41d40304090440d041e9944662084940c00b07680318410902ca416510044011069640c41c0001d21080d43d0041202c04504001a00103110308101c5d400700c02203140c4c3c1c00c051040c040b502540d070380c0c4015441c1e81c0c0034200340c1c1248072184148958072181750300310b4281040c18509401c02142258484082c1d8100b1403c1102044640310446000700078490440100344e9601c60419000d20042d10226551280c4c1144a04074513580e40102551103143c111840107030345d41c001ea00001d00801c0c60b154251101c0c0075240c000640d00c0c0d080500002101e0180d02501e150741e440c0790412040700c6160044140100d034000102c0e0240058a1a15103030010103031040d18090008480b03100a040386070b00c01e40480300d0000301441002c140380a4141c1d0680e01c00c42107402c02c51142e944a4076401f00030001350411000b01c806103410b083c09140c4400500004c442541da9080080e44010700c3e50201c103040d00460840130200c0340c540079500c41d0400c1c15090140c4991124101100312541c1c0e4404a400c0e42008049800c41d0361 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 315943588 1250 315942338 315942343
    0x90a02040b0a08040209070c0804090c020705030f0d080a02030f15120703060b0a05011412040503070f081e1303062310050102011b0c1106120403030506040516120b030a05 75
    0x2c0e240450b4a032041180b500d48100485040c0080c9050204002046035a0020b4181c1003560245da04403031021600e041202d80803890706aa6901599241c81207901d45600180b000c01c013000c2c423642d9550f40808076500c040d8141f05a00c000c0d1126459429401d001030501c0e000c0800d9400030100050a50004511040b105468013225800c03d590140d9500000c00385da160803940400102401e0030900ba92141c0b00d040c144060240c0701c1c0744600443c0170000202085824000c0352101d9034803148031303c014440c40c18802c119400030314410040031101c07940744403185180029a0000c00050030142c01c80d9085a41d0b034400352562a040c0800110000d42c105884140944424811541c05542c80b02d5903282c42d000909440d40c41c42032510101c2d0303002c01204a10342c0900746958964200b42c5507900c0c2c11520020502a200d1804c2c1250220a043d040c80700b0554103800c8130340140002c94007403119840f0401080040300d103048000c400b10f50303410440811850035821800d0032004c01010384524150316280c260 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 315944838 1250 315943588 315943597
    0x90f040e010b0109081209090618010602060906010b0f07110109050406090b030118031407170f0c0c1c030c06020c1504060c17010314070801020a090303021218090a02040b 75
    0x240565110707a0724800b90350384000c0c948003c1601c07000901025001640c0d9002c644603005c0d40c180600420340020f11a030f00c509204124807a0045c4450b0f0b459a5039400080d110031041c2d8540000d4010310b0000514440c0c040181e680814100610a180007401c0d591820655018414103050010a000001e20303a59180300b0b84001701146c400114a29146204042c00c440505068221211110b0b2003e00400e41c00b00304080c44e4401007420941c0e400041c2804851140e01603c40590030300d0006000e04141009005020090318140450f01507800315020410840fa212217880d42e203044140f142070210b4414800c0003071341809540018903000c10605500d00303011402c22401204078062050004000492049040942142c645a00c00000b800e00c0314500c10f40610014189810101c40809100010300c60080280400c13002155034900c11800901015401d201c00d0b03003d402140d8603880d100240604441c2e0081402d2100202041c14404000095102a10391403200740c0c01e00022030503c80c80300040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 315946088 1250 315944838 315944861
    0x90c0a0b070303060905040c0501080a1b0f08070201060b0d02090a12030903140a080304030305090c090f0a06140303030103080c03040317190c0b0f070c080d0e0d0f05070602090f04 79
    0x5581e151007a04001d4151111540a81e0a003460201000301290b200100c2d5025103409281540031916400c150101401c1ca200150441c185641241000140c20a06034100040143c80b414256901c00d42c4c180d003214158072608009900c1013056140114040e4000c00320000014000708000c0c0e264202540c50b03552018045010600c005014028410b042c5504083c50b0034401c01444050550380e64180300313000c083c0008040c1510b400200b459640c00707000000d00040050090306591070803201c02041d010301940da98090342e180410101d0841c0c0080d030704070400e5102800841c0f441e480c41d81c942109501142400805010601001c00000c8004070007040720308040600ba0b4403811031401c030210001c01d4451500900241e40a000d000610748198181c0c020031900900845030f03100002174900920b4410300418a50000440ca102a202030303011180c400d486500f05d07105c110410805850704449407000401140e802d200d8800020031a0f0020000c212000d09000d0040c0034090120301503460b550f1a6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 315947338 1250 315946088 315946109
    0xb0f030702060603031305130209030a0b01060f23030c1b01091104060521030f0c0a05060105010e13110f0f0901030e0309010c0209040c0e04080c0f071508090c0a 71
    0x500100503410802c4076080b4204030040e514003201c241d0a03004102503841107a00031031200c41c2100304409694142c484492000c1c0641d50400003c1c504801928403d01454005c60f55020341d21036058407801c6800481102d042010701900e01900020b420794200038101108807904110f0049440e03903108103001941c1c000c10000c512100e052401c0111003071094800f0f80947d01d058010411503640c24855240c05812400301c0341006207140f48241548a44c401440a804000a640d01e400400142c0b8003103440c083d43c00c2d04c2c1140d0300c400c0111290769074003050343c3e80842d0b10007901e00725a4690b48190080c14005180c40c0c03401580302c004000d80e40140c801c4010000300440c3d298a81c1d6050f0240c50341011200016500d04031100002820301200c1940280c000d04500300017400b00080704009074042c05800c0c101e07207250700e03143c0b030080680d50110b0820441e90140140506142c1c6c00010501c042c0d494940c804d145040215808075421580100709420521031001250f826032542c03c071050148c501b0450 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 315948588 1250 315947338 315947341
    0x70512010e0a0f1a0c0d0f09050102031005011d030703120905030a0308160f210207020d08030117061b030406140f010801060e040515130804080309180402090a0e070b0f03 75
    0x2002c43d140c225000f0301500d0b8040c1301080014444480e0304807009a02242000a44136a1080000c00181a0413000801c650310000501400b02c50a060a40803104266100c030380003201c0e007030841c500c035208140b416003540c0090014030004543d0075075601c22000c0c0b850580c06140e6158006864140c180e8020340101c1d60800078403107c00421507401a0310b4115081000044030080e90003095201410101c0c000c1003030510900412030000e40440700042d800030100380703c40700207040c100e409500c288590000010007503e002640113000c18041d10564944800000d6140d200c41041da80d60306c0240200d458503945d10b0004070b2118101d00e01d42c0600180311f4805519810810320380d085425907044000c410499404010010704c0010301064000031a0307410782d00d10b48454080d20400c0001100c0140381060100d00841c210000002402c444a03007210a41001403515203a40c1007502c003036601a400600140001d9245035103504400d4804045100325001c0d1981c842c48420690000801d08032100340000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 315949838 1250 315948588 315948593
    0x15050a06050906010e0a030201050306041104080309030f16030321020c06060a120c030611130b0c060709030809040e0c0411070b0702070b122203080621070512010e0a0f 74
    0xa1540d1083e000e08000302030002080014108040742e2000030f04104002002030199100e40d040507050410300712000b505c0e180c554201c0d948a800010f40035010b03108100120044240c0000d080c04e00044582e51351450604645007142c0170150a044007081a02040300500303c0c0040e8401080c850701484003800d01800c00b002040031000e000e40c002d60744485410070010101d441c0e40701c00c038110b1303070700000018440ca0603030b110072040c0c010404e400b82c44190340440003a200544d00003c6c0150312000c410b4a1103651409025030b5031501303502018146080910500d04141810703031000d203150480008840900400100003000e0302c042c60074110554001141480800040b400204e401070110300142020504011030507015002d01e1810b05004000c071f0000c500c0041581120340301c4030503085440d5494400900b409040f640d03065a15a02131400c82c40e0310303103a5400c48910036034610380c50009005098944820461029410301c1450099581c0c0c86170b115412701c041107030741c999a11580405100352080d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 315951088 1250 315949838 315949849
    0x9020703090b040510201e1507080103150f0c0c140c090c0307140307090e09060c04090e1510050a0605090a17150703020d0605040912030915050a0605 66
    0x10b0784000080d02080c00180301c503076505192207205940c01e02e00700310101c120010b000310701c00302c500c0500b06034001d0118000c1400d071401038007210b84419804484c6045c0c0030b0000e41141007400c03101d030400a800f01c401840010000151401c1001c080c1b480480c042c095214a04222460001c44501003419507007201c0c104082c0041c1c90301c40303800c070030f0190102340d44003c041101640001c203500140c10340000056606c034040d4540c6504294107200a0341c8904d404a00505103005600480c2c01c15041d01000403100803001403403510601c090a65682068645003801c4064400f52250000d180150740d0800060900700c1c9549101e00224a0141c0d0032603d03200602100d401144c00180801c20100091041502c0d40700004003101c03040080e41c1c204000568416003040b0174040400701c028204010310881e1070f4160068603000304481000c0001c1c036130310810031044070240345008292264401600003d94000c0d80114201d034001c0301012001c6900d022014110340c0d0803900303200059601c140c24440341c02c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 315952338 1250 315951088 315951107
    0xf0f06150108040213021309020708031e15101b052401060e0f01030f090303050601021204030f062007120e0a050f0d05160609050909060423150109020703 68
    0x382002c0507282055000308440d40c1e0f807001018400f980008464450100d146125802000407040440d112445171801035416031003035407500d104030101c95800b80c1c5040351917955030140001d1312420050620800170f1004003901500380c4014032074007032a10b070240100c0740310b040c01d0288502e01908003581d500000201e820809009203a920924400603c03031541c00c4600408000000c5a07066540501080101c02030000d1881030740040d401c100030b1100f0542c040d00031a015600076020707104801c80c0102110a5030290380310243c0079610031898500030903820f60001c000d2808080041c0b62019561200c008a41d110714400c80301c10110740480e00d5007550020358000e0071003040318a0003074540f030880041c081000c420a40c51107511744000d15001c11504115800c0f02500310018060301e140e5030380014000350130b58403d4038090b0002c0c000288908502090092040b50701c0081049541e9500311030f01509031103400007034010f100e00701c11540c00c0200300d40d0a5000b03007403503000035a40303034903e1400401c080503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 315953588 1250 315952338 315952381
    0x106030b0604031127040b010e070210180209040507140405130318051f17040b042009040b0603010c0f02032b050705030603060c0c1e0f0f06 62
    0x1520140d4045a074810003254202ca800005880a5014000000300821152007415038040c800c14190019032440f10b180f030b445140170f030403480900c3ea40d80ca000303286000100c07020300c0142c03c1440345400c1f004080d801200c6104648120680d405029408150b607400305940070b403411380c0000003c2040041682000541d001d043c0c3e014000ca04000e0400b10f400c0b88078880c01020f00c103601100303d10020245c2c401d00c0080000404d481030300b143c50060b40501512004101e40046c1031030500061035880b050b03820f0f0050382e02884c4d017080da0341c13503403101c42045c60080a120700f800030000044034a40c0d5a00134441c001c0d400703024400c0c0c0c0b90415100701402c5580c84039104080c48000c0751000c0f1aa5008020b03100c00749244250516400840760f40807100382481400700324918070b810140b1100380d500c072024504c0b07100103030225200c0b42c41d0201e0806060060b600014207035400f00607121018002c040600407080007040c06c0312440b0242e814158203110740d000354074080d80c0c402820132010401e1403030000314894 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 315954838 1250 315953588 315953591
    0x210c03150f1605191719060803030c0403020f01050d0f0c0f110a03030e01060b12150a030b0601031116061b03061a07050a050307030207061d01120b0301020c0a03090509010603 77
    0x10780000c000303412402050f0100440b90014130034000f00701d0181c000d07490031541c03212103540d00349012179000310030590580b01d146a241c80c000020030720401c00002c40e401001c2c2107290504103840c2d6400c01c40039140e0710058604125092150000b0350300d45000d00210390b0204540810b11010480c401404140e4603040c2804000102a01711000540802c00c0d84070f00b6098a40481c505012031422400743c03200303900001441400040c41d42e40030380c0e4008660b0056400c00302c1001d02605e090100f0a00820902028101c2041d42d408174001d23600035800610520701000d081c6042c411892680240c206c10b00e10140c40142d21380920008a220580c9600e001800074101003201c2030808100950407100804544c0b80d94400164100c01d000c4c0c10002600225400012241d68250902c0c000352070303001c580701c0c4202003501700c41d43e20306517880702881150f080c0069442e81c03c100e8200105502410400c02c6140e01550708001040514006100e0303081814069143d07074040324030b0703e014450702c000c05034040390030503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 315956088 1250 315954838 315954871
    0x1e030512040302090604050a150303030e0c010305070504060c020f090f090d11030405010804050a0804060f020601151b030e150c0c030705030c13020f030f0a1802210c03150f 76
    0x1a584c40d8091034015406840001c2c281c0c3e02c403000e44004003040d00d42840a000c241000208259140d04500d0001304d002069880c2403c80c500150107481c400d07a0514046441403005209440c4203021005540d400181860b007584922000700e402c045069848100c0c2d0b004e14810094101810032210040c40c42515050300b41b8540445c00903200e00450054a040000282c045018844108220010580c01501c2c1c682c3d610380e9a100908841001c038288000360051b00000110041c0061128401400c1e036242c2d04503000d0307640c00461440c94007010032800d1144a04060a803a1580107120700740c000814103903640d6030742001185203401d83d0200402e211343d00440c0c0a0010f910013140038015244144c44461400005844110107801b400106006165010007000a866820500745004403c1350108216980200101c008600703401b14000e500204000201e0035420300d00c0b101410240c946206403a02843c6810010341010240b07040d0240c007180510034010810a988105a04002c0c45c64007000203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 315957338 1250 315956088 315956093
    0x218040309120606030506151503010302030349060f14011115040326100608100f0e040b010b04080721051608120906030a090206041e0305120403 64
    0xa0005006158030400042c122104010840c0c00c90b50285a2042c10798030b83e80b5002154840169071000058401d180e060902e00030316880d4400ca0341a250081c000c0d510748218404103c94503441b080c4010300d5150005041d02c1e002070544442c01d1261900c45211102030030410710b20342501e8164010b90410038403800300300800e07100740010211001c028201610320461b2101043e041c0300c140410104030000b0901080105648030360380380c1070301074550758156400ca01c1e90303200400500304440c821028a19410300b40075850051091550020350aa04600700c151070f445041e0342c0c1002c5a0045104c03d44940a000801000040c428003501e408800345042c54640003055560f8455449060714000140420151040c0241c034031509003078100c0111401a2103c580a1680402511a103180c80c0503001c8800848610b1001320b45100400400ea20300b1622412040c06c0103080c680c00407a0300440400c8005840502109148641c007040059a00e01a1a40c14203a0800c2d03d00540c5d040d44c2d02041005000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 315958588 1250 315957338 315957347
    0x2070c120303050907090b280e01080d08070c15050c040b0d0f0c020c031c17072624030f120c0c0303030105100309060f050903090f0901120f11060a030902180403 71
    0x280c01015503040040718400031203441c4550040d4100003c4842704c030340081102d04000901c0d011548565440d50720307641d07800b01c013143d0812043c0703001031102d55001d82031100500250009504960203000c850b25013503494001800c039600c01c1c0844051240c840402c011256201e00c03030241c030488240081d12204000034002900c0c1d203900d00c038100c0c450301c00c0441c40341d55a220340c601c41100512000c0b020b0307c2d4145000701800100071240d005d880400b0b000c95000440d1100c0346c616000746c40600820303001008400c0035001d044410310150390980700d01022803035004400c020480400704c0046e0040e0391122050b007000d0814204221860180d40108010844d61b200c600c80040440c0e81807800142a40e100d1501d0741c050828140c0c404a02403c00e028010340075008801041c540c00c04071150411858100280902e0800c24440c0d03180e12160200054046000103036200039040c0300342c913481d42610500000605a421691412001907a6444e1440c1181840200e2103010924221030110915060790b0080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 315959838 1250 315958588 315958609
    0xa02030a0516020402070303052a030a0c110a030c0218010e1302030c040c2708100c020a050d050d0e03130b0c0a020303040902030a110a0c0602070c120303050907090b 73
    0x10007000160411070403001c2d05140002c03d038014425036a45501d400c000300a4003040d00c01c0d19001003803100c18609100021460048411a50091425030399040c90305001030494030a9101800b1099075051440c3c5824042121010301c6034840011007100782c01406511100c00b07606aa20101ea04014800342d50080b61080d03010f00d041066052111082c408281480c0d8102c4007141c005091540401174560401500c00c4030010000010039524506a03140808880e41e1141040359000000c4900c1200e032550480c0d410300038240100c8030004030646c1e5951030403520754006030020388040341650030508580540e0074041080e80095040c5841e0072902c08803000584a40d40300844000b4000d1074080080c0824665642c00a054a40b22507803505a28043e61044a2150180e0300e421030840b04e1409860036298917440d40d40e62100c844010781d50300300081d8031103041a15510b0024000140052100e07250140c6244a03940100d0941001d8041a2400e4002d40000c4e0310359090000214040d00c8249658 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 315961088 1250 315959838 315959857
    0x21501140105071a0702060a0b010806060906070807060509060a0e0c09040302120f0405030c012606031204060f020c09010612020d0b060f04030c0503030a05162409170a0203 76
    0x4440c88018a801681c040c80f480c2c0d03000f00b50240580040046210684043c1e1003600c5640a8400a942d011652021100850a014007007800380010446034103290000d48a425400790a0500e0103e00d5150520b09400401d42142c03225100c608010300c403007050041640145428a05100040340110655104d04030707c155a03005040403400141454400c010f03030041081602c0d0459510300240725201525445400342034020b2040301615110b0354809c1c0ba84110400002d410340220301c0901482e02e0202c1406800c280c2d0500c43c03441001282c0c0850b01c024402040941c94180c00340c240c40c140a030510030842003030361084418030010012140c001410003140d08007400016600d140c1580382c1401004100143d50f013124001c10b0300036254450f20020419223004003a80c40c45150341d0350070940c1d6403042e152040c1c0001e5050201c1e030a2801400b803103500ca20b1183ca46454100e5060051104400c1903ca1804030300791208a40814081288400403041e500d04170051700d03100034214041c0d628440d41491 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 315962338 1250 315961088 315961109
    0x306060b033108090d021c110a151209050d0807030524133b0105090a0201110309130204090c03090f02090601020f060405010c030606052b06030f1401060501021501 72
    0x4406945e440c1c10190000c1a401003c26062a400c07200750b0108011000c8100c40710200ba002101240c1750010380305045500c0104c80c08014190303403904a643c06026818010459210b05402c0700144007400361050904050307036440e005280c0400010242c641c080e0100c2c030b5001080c0d0a02516803040b0707030340215400c01070345d100368100202c8060800500c0c0898401c054929582e24900d50440c1110800d28440c030340300c08060a512060345528220350060b943d645841c0e2204428030015402200b18404180103c01540e0601c02010007080002d101500000c1d480c0c0e034000380c01c0c040c2c900300c0d02c51507690500c00d280412020746250f6414080114144029100e202c6410010b10143c0c4200600d1a406d1810400e84400d800d0916290b40038002c04001e09011030701b40b080203e040d41c0700d60203941840e040c0403034080c04401e91100562504240383e200d03003012520f405011004c166501c8024055510500604c0b02d080e00c0d103803c4508581c5190480d9046400c1011a0f0400f10a214021415203103100c40c07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 315963588 1250 315962338 315962347
    0x905010510050105120402060a050d0905030c0f190209040204020d021201060210090309170109150b010e0904051c0203040807080a06061203050403060c0e091914060102120d060306060b033108 84
    0x14140c98a0090080070bc140382e0611210904100d004809000002e01e0f0000b00d90089240d02c230840d4513010402da80e4508000b0400034000589046103a03180c0040c000740c001403410750000c03c2c1e00b090742d004103aa95500308481004020480c0d04020241b501100c41c0c004108840790341c0c0e001002c00c0f00610506480091070390600c0c0c00c00c0c078294810000c0aa1051020134907100c6100220003a044140000d40441d0b85100240c2c0709003081442a032280c2d0303106000d04501c408511000100380101448801107100a1001003002a000c000500107043c1c140c0041800c15040d02d040016580550000d1f103400c41e01855010000b5002030517941a20b41c41500400c0c00e5a0b2500c04680074200150165804000c0031b0500145514920076140e20140000d801d100c1030520b0403550507050800e5030b102d401079019107440d40c3e05003800c1d009840458075541c00480c0c020760b01d84884c1c0a0740d010703400c0040e80a0f000828010541e1000f000c0700420030750001c1440c810700c500c584410500200c10009040a1000038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 315964838 1250 315963588 315963607
    0xb0f09010b0d0b03011b020717010203011d04030905030d0c0b0a0b01050405010f0302070b01030b180f030a05090a0f080610120201020d0309030201090c030501020306131104050f0a09090501051005010512040206 92
    0x100400b01000100035110300c01d0106c940c00035038410192040d40106981450001a03040e0706000f105d043e200d001d800030540c10700858031540b074200014000d9007001400d00011816035418000e80048212964a0440d899070908014051440240040c1620761621701c121001ea60080e040d00c0071103000b42440c2c624040e880d1400c2e400380c07003030640080070000b141001008109540341c4032070085000c004205880c03014100c005540e80401034140c0020340c428003401c01000d11450003082621809400411020350360308091112211030303040120690031620800c1450205c0c006800e000304034051140700906a5500042e458039130f07000b82c2c58101a02c841c0240c1c00e040c004d400000406500400483d64680d803420040c1c000d4100307484aa100d4005014040b8a60b01d0f5030203a4810f444007145403d1600749080100101d41010182d41500302c40001c5002445080d01d2080244032070148002140b9450b1403039000e0036840702904028140541848222070618a07144003548c40780e4180c070402e6441c840712 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 315966088 1250 315964838 315964841
    0x3c1b041d1305010c030903030c020a0c05061605010f09021f0f051b0303090d0908011a1e0619030606090b0d0e01020405060c0307050c060f0a031802060c010b0f09010b0d0b0301 77
    0x55074090801d40c2004440b185550345540011407641c06650100b00d0a401010201d840786021000038003280b02c080810721031803404000400f40d03400120710108150a0503502c0909581d149000c010320384e41d031000341c80d00f0340c140000c009901071608003401c1686203d01d20f01030001c0c0f514200c4401000350100b054901c0403076141e8806c201e00c103000300b2203032a03260042501e940d50790710000b4140003a02040c00005c140c030f4140140c001c3c89143c48100b041c0554210709100c840082c140e050086120307440c4128400e0f8a64a00130110a9030324a9800c141e0340036000c026003660602e03441081084001e240170002c4081c168180c84a480c5101c0e00407030000c0d82c83c1d10b0303d8064051900469489600002d0105150303070008000e003092486501642c0c20854039000300212401034102c0d00000c510b040090f100700030b10962010310b001c03580b80f03480400c0c030080e6004282c0a0b01700c0c940d010450ba5441000040c14a080b0035003000300c02c070440707166501c2e6050500702d00e10b5010310441b0416443d01c03004201c8141ea0203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 315967338 1250 315966088 315966121
    0x80906070609050d02070e10210f1a07170f061807020a03111b01050a03020f030a0204060e0f011209020607020301020c071e0503063c1b041d 62
    0x14000d00105078641407041e1a115010b031135501602c00e0f94000a4030007505001644a9201500c07079450107498440c140c41c8c1d40101d1a0034a01035030510b012440080d80713103183c241c40d49006000c407001045400d5200b510341c003005400c3e2428440e03000701d1950325814031644d441e81700380d03110482c4402c2e07200c0001162405003605080c000c1e82c05c003107040205050340001c1650503a800781c3d40310100100e0b9865800d072607041c40050419500201850181c455000d5002000c00c090203240051514401141154081d08181d507100d1601d600003c0810010742c1c0444940440c410880720041c540c1002400600824030701c1c4840003400c2d0315070100e18150366a9005841215401034000e41d5550555540e050300c42ea01030180002180b1810081022050074941d0b0030140c3d40050001d00160702d80040d54100840e0312501138400f031680481d881c519210111511a4012000e2104001824140d6111030414500500c030311001c032080c0001c020700c00b039580c4800080e40c0c0c901c881803801e80301ca05600084032036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 315968588 1250 315967338 315967343
    0x20309030715090f0605101e06030507050d051005131401090506030708060a0c080c030403080f0a022205010f050f0904020307030b100f0f090321050c01092004020a0c08090607 77
    0x2104d52000043c0070454114920464006040c00c4901d0340704c10a604d0000750b4143d1140d1040698042032080034040d502c565007100007030500da410092003048800941e60300b1240c070b4004440010003003149042001e8015881c02080c902840240240884c03048940b00505c500100d260300c0d0400301700a034506101001c042c210b081c042e164903280c030002440c00380080c2d01914001550000001d080740150304103880c05281d140d91540c40d10b44801c00d041c0740740203001c1c0641e80c4031942049000c25201c48aa80d86010640e15140c42814926060015101c0400d80174041c1c1400420840030311801d00392001c40b019400d00300d60042e106c0e01c1d510001c50040803440d00c040e0300200c0c4c51000d00116034000003083e60000d800d560b00d003d0890791900c00c40c0c10384d40e00e1000030b005401e9441403e075005400032418645404a01d0490300b04850f10b0961402e48403640401d451001d00a18003944080ca031140c1c3d07004d007000580d0194940800514024089502010060710004003c11404e48a9a40e10300701c5840d5038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 315969838 1250 315968588 315968603
    0x51b0d0915091109010f06050a120b060a03140603010510030f080702120714060702010906031d0706050c0609030f09010c030302040f0b030f060904200a03060213080f0102030903071509 81
    0x20710301c0c149441103c070010152042c100320000081000c402c801030f809589142d50381d9818050041c100350388010072256a00300c019240d01104502d40c813250040c040120165038003003000001c1030308100061ba0043e000c01c0c0664185001c00900712401511007040b2075000800c68030b0840e060030040c0103030155400003544003400c1d000f9a04c9025000a29a00f41d4a4800e0860407808005040100c18030811030005d01050801c00304001185c002d40c040f00140090051000c00320b400140340303d041524940115020800c003184a00945404000039a403008407240158a0310441034042151070140e580c20034108181a0014000c05120790103a8000300158264400d98640321090150781e41c0007120345c419091076020008076a440d202d584680519040000001d8030040355190341809001c1c0007001d0382040e0038003400400225144020141c00c110b002c2c1500196091410007410807400200c801400d038014824001e194070b0100840d00c86503031040e03e00c200301141d0900113024180f284000b03001d15 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 315971088 1250 315969838 315969851
    0x1080c1803010f02040501080c030601080a091e03020102040f1a0717041205030a0e09040b060402030a0b0d0501050106080705040308030c090a170106030b0112030905090402011b050f01051b0d0915 86
    0x7683c1035000340081c0d80b0240c8400354103654220900c2101d010407504980080c0742c00f004241e80303040035070104424900801900141540408801903c0d4048000460043c0c1d030018041009024030350454014016241c408070302e1240e014162001c074003480c0c0c0054051042e18444042c40075665017224010250010000e1154585081c199265003001c2d00104c085050914100c070545060204184110362040c0c040005850303a0003808001d410061007000020b0351800c4083c5207030741c0c01486905051003000041503940c1080001400210054641d41c28454103002c10302c00500750100f5aa402690f50f0301d01905e4070740030000512102e001e0f5001148a44030502407091020043d00520f003640c2c0030301c40381d40b05030340c0c1d440040e84001c1105d6005800600000b8007440036245c003031040f5402c507005241018040303009584420810760715040c00c444e035500003c0180140182800388580c411082458189011200011080c19204032017030f49200c1580c2e507160100f001003515000d140c018541800304a403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 315972338 1250 315971088 315971111
    0xd0615020604060c050702060d1a060c16240e01050d020f09030111090307090b0d12110c0409120507021f0e130c020a0f06060b2701020c01080c180301 66
    0x807848140d90603500350381400c00a09150b80924110b582855019216030f1074080d042c24118000d00180e9615a14900450084617840e034640010b8604a481f22020340340c9a22640c9189030281c540ba0301140e044031004404d0b003d040d03002c036022040b180003800c004200e02492001224144941c904000080d4404100c10051060a902404200c1e00560003000300e03443c60801c0703080c50b00030385600035450390048100384030b0301d0034641003882c0518001d0456951141c855480d5468511011044c0c000110490181442084104055216000151350401280d141c1c1c0d1075030181100c403c40c60000340a00052008210f46903200040131402851140903074138442501c0c01815a080d0079851885a4001e5201c00680240b0340b10b07190450303000e50020120f1000a07500c40840d04100c91040d116250360f241c001443c00071050040064808000540c0916500500c1d400003101980f1603050455106c03403940001640c108450325007001d0a00c480640714048026901020386200c0c1c4040d030194200007070b2100c2e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 315973588 1250 315972338 315972343
    0x30a02090303160203010c090b04141c05030a14030103020d0201051b0a060e0f030c1902010507060c0917010b010f050d0b1503181c0c06020403050118110a030302030706020d061502 79
    0xf0052007100203100c4d105016004442d8000180516001c0c0300c410042000801e12580b035452400c0e8020300001d050300e4221001d00b207100ca02c44003d90b5035030800130b070104140f07274030216030152a102e80691901b07650540d00030034000d408420340203040c07041c001100c1401284203107103c0074000c41c0c04111801c091003407410300b000e40800b40310744407107100d03002c0000b1800d400403083d83c11451805004106913072525400075510201010140d05004017001100007041960040140300110390711001d1901745020080000c24ada044614010781e4500b142c6030005a922003110750b0500c00f80d15001d6101d0405048000003458903c0c2d4056115020110300c000c0c0a290802442c4a031040b001c10b81716130070074454641c0d103a041c6000d03d501e041239a0404002054014400148418001e00b0010705042c1c40b50360309402c64013440c1c2c240c0c1440d842440c00c172007000303001d443c840c0300b1100644800d80c08918503500a0b640c1d0203441c00c01041c25801080401c1c81b181207901580080424061035484601d151030040d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 315974838 1250 315973588 315973627
    0x4050a081c0905010e07050315041101231c0b09040210050c0a150c0306210f0b0f041b060203040b07020d020a0b030f070e0a1715070509090a0b01090b030a02090303 72
    0x25224006d0f910001080c0c0707008030b400c0c995040c2d039080081195550395114801c0300142e040c1c2e24148500c1c41015441c18217008050304058001a138a580e0b540d1400805a0019040028552000c0c2c180b10712407a0070b0302ea040506410960689040401c1c03a03030f90006a4440c0203208980030680300f000000c90030b2028911420308000e038040c4007001000301401080341a9180c07406010b444841c0e0f00c1030403040c540280c18000115010301c18516014486a650100e0203038280c442200d0612160f0078482807060301e50303080d02c3e41800701c00d5100c451860301001a480780218860342c80011030101c2d2600035526100400e065080d8004c24400700d194607950850569001645e80d484800012000651b149024030700382a60510000c10202c509880d011155032101400210b810305030145210704400e074050b8008050040c0c2160b01d0303042d2180a1002400f000130741c000d00420020b41001e082c4002a40c10030b800c0700503600b0041c0c0c803079030325500c3d440844040d2180088040d014800014030b14484070600d04a813 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 315976088 1250 315974838 315974861
    0xf010213090501050d02030616110105071d031501060e0307030f030314010b2503120507051b06222f0406090b0f130603050601030609030f0804050a081c090501 70
    0x40059036204c001388081d582903140c0081d0507500c000040b0b11140300808450300d503d2200d1421401e40c181d210401801d4520540303000b00480d0020740690000b49035640f184103109015402040f071550300001000c580354041c81400188043d4000c00d0340d541d2800c0c40120701860b0000c081d10112000ca01d0028010b004030300850201d05000000801c07080c0495080b10190210010380d44a6640c0141059801808110048090001c40480000488214040da92241000703444243d22040e01607003151000c904020701011503001001002403514004045500c9580411181c000c0d100f4146020075800c83c002400c83c0002d0220701c1d910110042800031000e04003000c0c1c50034401c51f55500c2060043d070b00d101940c540e00880301d09602c1d40c0c038208035601c804c410200320720100710181d50351035641c1002c02c280c07c142c49241c0c031002e141f0241a0080b100e07031680c078074614140e090351409880f816141e02c0d107110010504803002401907007030840300d802e0001c0d505001c5d004125082042c500079000b840d000045 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 315977338 1250 315976088 315976091
    0x30507061b150203101d041502121305070806012403090816020307120807021c080301030f11131e150504020d020d09050604051605061207020f01021309 67
    0x800300c141c0380c10301203085007540007000700c6245040e039514001a4000034500380320080c101000245031411a1500c004440c1d2900202c07400382050300b40180c05000140c0300c168041d004100c400c0c005200c5407201a4003c503981c40302003c0000740d00d0000d017465020351141004e0b02ca201c0020440301c1d403000b5800306d23000d8100300d0551501002071007901a50101440a004008240800c440717080d090304103580d5551005058400305500c50303168000c4152030746400d03102a080403d5010860510344401c0d50389190410002030884450395480780c00f4841400010401042c0c680740000304080400c4081541d100100042d0055070346040c0ea00080070a980300c440f040c80300e000380000c0c02c00544600d94850704181020b00d0207600b8070b03040c40082e41c003041221b5501c42e030812000f140ba250b030388208841288900c2c042c0200c0d00700350030480c1c42e0440d80010030081d00300d00e020801c11665007204485841c0f20401c48601c481e990a0801d90800d801401d0b0440c41c0e500000d0104401c840740e000d4541910b5001c0720 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 315978588 1250 315977338 315977357
    0x61d010c0c09090c0806011e0f08060711010b030106120b0a060608150607020409030305061f0509010e011e0504060f0c1205030606130b04060e041505150c0703050706 73
    0x112840e00c440880a0800c440c80030080c03001d04940d82116074003a00a81511000c0c565419000d80782c0b02c026405075000c03145110341004d50326080181c0d64010540310109200c2c007410a08803944402002d0400c50034401885a0180c80e000203422440f2022402002004441da89a0442c0c1076407030f02c90030480300d4080f0900002d45000e03041c820310003500ca142d81d0b45202991144c03600180c081000116960140c401d0201000590300c038003905052501c40d5401281da82045800d000400030080018840100c05030500001e86078408103a0b182d08a0900e00a28242d440713000607520910503a00b25941050784181031060075401c03030300400440341c0b0741d0355050070351320b0704882102c0300354410500401b190b90044a000400303125202850304044020465498201824030ba070b085021030f40c2c8100b080c0080070a00f0080706400c02584141e004041c1e906001501c4a032851300c214201c43c0c000c11b031241114070016642e014681d010380300b2a0420108441c3c00070b80340d08210b556200035110301300000e602d481 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 315979838 1250 315978588 315978647
    0xa0f03030c0512070503070c06050a0b0f15030c07060f14160e030705041109101106070e09060904053c0f0d0503250f021b030d050702030c090106 64
    0x42c21500c41990300425280581c0700c43ea411111a400034150304100108500b00c0741c041551440307081d000384000c00c0001440440c40052214011152118030711030000a0a501031003186141141e61160652039002d070781d11114640b5600800c00b00d860600000d2400711009003400c501224140100d80c0080741e0100007000001c2101c1080c010fa1a0b6500340d0801f0500f0800c0c4c1c00c15800604101c40e0080889040c11080e10100d1282c90054509000251220340381e00740d0b0103000e0043d9508011245070249102090718045184100042c0405003d410803100240600400f03001020002040f40082e604145400070a0088d081c90090511212400700022a081460008600c0280c03101403001e442d41190041c41034529400082101b00d203045409580e440f142000c0d084185180000c3d00c070705c500362002100c000d241508001c20300d10385141d14001e800c11035500040c071048816032850030a98400135840072a0801c480001d86640282c200000803c509400207401c02c0d031f800d0f443c0c1e001001401e440 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 315981088 1250 315979838 315979847
    0xe040f1511040311120105070f111207080d060306021b1006080a030503070306180e010c030b01020304270f0e10020304020a15050909041407080f071509080a0f03030c 73
    0xa04285074011002c010810004250000d01000108010a079030001c1403401d0b0001d0942d0380480e5410000313810504944443c50b0000e12500380c0e003200400801c0d1194200800007e140f00703d26020302803640200321801c41503583d0f048030340615442441951150080542125003c00c1020344a01c00d020b50640140801d00c07034410b00d4112100440140003d2704203480c1540c01c0d60020f0610170070541c6804020601501043d401e01484080002c0011007680350740c0450301711402c0394000d20416040050640c0f03207a0707001043c0c1c0d090782c4100f21003241522001c0d00d40124140000c00301c85225081603030040d406103255212088009040c416610142c0c0c001a680c41244811a0000d5000104210502c010a4000210030554515041c003501d456115000909074010407241200e90000e031089d04a015881441250000d0030060014507240322111661515100b582c040d90b0841c8090400904029100b400c60034001c0c10002e051b81d5030f0807540c0c00e01d541c0c8054a010700754046810402c210032054400c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 315982338 1250 315981088 315981101
    0x10b1806030a06090507091806060503010c020d03150f08030910020304030312020702040e0102121008150103140c0a0f060807090803071101050d0c020705280605130e040f15 76
    0x1c0c064100c4038002e41d100c0004122a400c01c0c1c44511a842c2c4c0800d0007201845150302d001c001d244410800701003494001c00303580b07082c3c2040d8041e034144000380b02c3c0c21782c0018040d0148051400d000c40c0c1102c145904402d05001030b803049420721081c0c070002a1720758000c0020001501c080c0d61000e25a44a0501030740e5900c600d00c0024002031400d80e40304110071140c0d01508035144004c3c0041040200032001d5802da8211041041085068030b0600039050210074202000749261006088152a06040310500040510000e4202441c5ca0b0203070090903020f000003800381e400140100c42294031035207003445090a0f409800003284402000ca600b040c000d408207001c03a007114000314030303061f2180d5508a0220348600c4042c10301800f4000c0f1101103940f80102c1840303000b95402810342c1c034540703000c00000883c8201c490500c0c800140c0000c02004044c0012001d541b190306003150343d0b21104020442a0031130390310051072602818180410821201e5080c0c072071502a0f4601150800310040200407641d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 315983588 1250 315982338 315982351
    0x40c081605040f06120f11120108060106020a020f0a12121d13020702010216090903081303051b0304031a01060e040b100c030e0904050f060919030c02040e0f010b18 72
    0x2840d101044641e01c43d8858448108170100d001c51b0b1034018803108420750b00c518040d000b040c80041403003507000159090340e0b03005101c0100200310300e5141a41c01b07503c807103451401034050b901222600380ba503228202102d000341610200240c441d0410b0802c0c43d0700784001082003002903025481888135042c4081800b481220040c66003e140c035030003a001009601c58081241940102c8910300384030620302c41c01800420b03c030103000c104505c0c1483d00400404004089045a5508c987e010700402c0d804410307105200e01c0004800c1394000c0c0c00360064550300442e80f0080418986002200380c20180d00c40c007038121021520ba0716521f02400f0100010b0380c100d452210b8010340080700115109100b0120780580c613000b410b1103801c0c03a03407400c08564215800c8405070303060b1340101c08082070013500b00300c1d02d90b101e54040003130444015551108200c4c143d4441e0043c0800c034482d4400401d40d500c42d444400c0e82c40010080303882c0c1e140758440c4240a0420006064842c003210214880c036004103040c000c0c0300d10b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 315984838 1250 315983588 315983609
    0x615011d01121e05090c04060617010312110330090a060b040b190812070803070c0821103606080303040525061b11040c08160504 57
    0x4404101202c02004000d40c1c4003c4110107040c190301058684c400c3d140034000b17550140c05e19480a1040c8015101c140d031201081050201482500c040c040901d5030550f54000e1013100500000c6804035001903000485480d640000183c440c1032000c200102b004151440c013842c0c07803104c0310001f143c0d02200211240c2d16907420840f4a280010084e03030042c4c5005000410000d201c0f15103a005c1030561b45004004407021080041c14004407400304a55200c82110480592801c00d840c0d4914006000c0900000140008202130004001058080c0e546961074141c500c0c01e48440080c180e04000b40c25240f1800261403c0c0020500ca4000750000c0110180c99501305003030340c0c1000d001405590318010190015580d0000072034001e605000031805180181c2c001d101d550340200c1c0784403040100a07008c1d040c400c00c0c200d08200c5c980d005038080404500589060300000003d082c100200480701d045541c0c49464001207400050b00300008600691642c482e51004442041c4107840324030550040e0030248 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 315986088 1250 315984838 315984857
    0x90503060f0a0e0f06180303040201090e2a070309080309060405010c05070b19090501050405090a0903110601060306060e0301060e040233070201020f120d18050615011d01 75
    0x2001d0154040e400c610707008000286030001c030701400d0602d000c0201c8400700e900100f081c0b0840c04a03408950403260382074000b40d481c0d810f0035030019001d003407244500c3c8244002c00c0001162484a02c0da00c101420940840d080040341024419495921400f0f0490101c0d51920020076a200c1c000150342070b4034000f030003540c1f07041c0c01c1c00015104402141c608030780c00d01c00c080c0046000c806541c00707010400d000c0f048521300b994821501800d8600b103504134504000c07090004001660303c503006603070000029080024044868202154005a8007910701c000340318440000606940c03590200007124110790303401d410b00d14040708143c00d850161084011900f00c80001c2400347c684401035401e1000d00c261100b150300f10b010410000344141c01c40400000030b000c91201c055580510541c1084003c001c06010300c3d1000e5031020b00d59006a203156514156504007200300e034bc003032124650b242c40c0c00200325005458080e000401784582a04828006500003140340744002c8856021000c5900584800101 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 315987338 1250 315986088 315986101
    0x14043b0109021303050d090501020d020607170703020d0903080601031805030703030209060d090b060901080616180503191403070309050d0606030209070909061e1a0403020a091a0109050306 83
    0x2035000b0000140400b40c4992001000840406c4011000320481d01c42c030045c0e41c909400a4245080c1c10703240303025074005108020380c1c694001c0c03c1c0307441c440c2c02c0000e035000c03901c48090440090245002c4240b00340e1411510070f00341030300700c48803c0c4120300c02d90382840407c002c154038081c80000742c500141154400e124420021380240c010300110340010700310318141904c1140c480f043d1502d444055030a40044014043d481c10460006400340840100410300350130091200c20068050700d10200410600c04181d0f0102e44901000c0d000a000090403031b91040b0614080403100000e000080b206c200c0f0b000a000801100481078400468050310b99504592a11701444a01008804c049071344964030711000c0016510810f4880c01a0300c1955154082410001c01000710741d16030700f045400004944800441800101d0844c00f43da988020500b0307034203d0000c0b090154004d540000350702c09c01c0030b41c001c40c2d01201c0340c0c4102d82211002c41202c200001180040d903504004c0d015568240d088000042c41 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 315988588 1250 315987338 315987341
    0x8010e0313030f02180a050a180201020d031505061201081e0304031104060f0b1b061506090d060c0503090d050a0c0303052503150e070c1214043b0109 66
    0xb401400502145d5140c01c020f0360000803140210741007203403256207006101c002941442544507040440390101e0744c1031b10030b40010b0f684000818010040640303980081100e04801c800781402454050015030b25901240e40c142000f02090203101803d1280f03a0349001c42c100f42e6040c4480c8036440001a528103800c1d6151641c1a80c000c1c20361079003260301d840700014504103c00e41803000b0034150008a0300e800042e042445000c0950015400951140c0d05009482261464048015008035001030342c80c0403000210f851542c402d90082c20fa24544240c003802c13641c0102c0150312849400040d1144281c914806440038001c81030b01b00009180304080c003001902075880705411000401d0000d60030b001240020340340c01d107400d21110020b5110008c20f1604c3c3c40360f13240c102c00b0f00205800b4080b94504544010b000b502c424901034000b550380303007141a045004501401c60070f04080d0107a0382e40ea0b00c807154180381c040001c00c0c035a920040d4001501d1084080496910b40720720b1b43c50702c020582d01c0c1024050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 315989838 1250 315988588 315988613
    0x25030f080a020f030f0c0d080c040b07050c090702150117060601030f0b0d03120b04090f1205160c030c14031b0f040609090b01121a0a0b130608010e031303 68
    0x101540f00702039208803100d40400103441502c200103021595580c1040d0002d0503e003404d00e06405000462060111568851041d1416030f00c154900b9503d8840a04241e03150225078220150412448000d01c40c010394040754154142c0f84455440d94166a80c0301880c0200ca0100b1100b90a41c00c04000718003550702ca0b03005400220601400030944606980005005500f6614101c5c0410341ca0854104400e045010b80303030725508100c3e001c0048825079122400d0a03074050314010039104d030400404001c513001d08207a0702d46501c400300303030803a4030ba051500c40e44983d9103000a8800e2a80c00c8800141d2603400f08082042070b1002c4c000d44a401e89088019107500601c41c0d40c1c80c0e006090010700c0e401b40d201d40c0b044200601c0d45407404610100c039400d00c0800c0020603002002c00c0300c25883c01102052944651078190b403110344100c011941c540791440000c0c8070b032a03807041c1d018149031481d051035809a04144241c2d4000300007003019201c02c010450f034911843d00e15095270740c010030703042010488000070136 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 315991088 1250 315989838 315989857
    0x70e09071205180105060d0201020316020a0f03060b131a210f0a15020909040b0a0b1f120b0a09110d0203090f060c180f041d25030f08 59
    0x803440c6216940721801541e500700c0b00015035091442104011080c2400b840f1b4100c0d01c02c2d559072194603d03c0d00001d44038450002100c0741240d42c44000006c6440d6119400001e0045e59007400120b62245400710142990001891141c01c00385043c2204601d280300f07018090340484c0b0b41a586a2a075410b0000401c510003407a1070300045850b002d001090103224820100340500080d2030484c550f840d10241d01b100a0072040300003031042c40094400d48401c03000c1504550098541d01c0966210f0500c0c2c0b0207401041d032402d4000140d500e1801618a036240004003400d802e88918800e40034400900c01220070003c0a5a804040f14908201050481d403041a40e0380c00f0f60b803003a2402e5400800c0805a92041d00c4804003944106110a1010303010300c4480d41096203c0c4005190280c0c1098601c8274008641d280b41c41404036440c4808240d030740782d2016a0b4256801800d24120318420240b82e12081c1c400341c1c92421a4450109044164030312400c0000d89a00a201400c1000c6c81d4130740c11950341160048 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 315992338 1250 315991088 315991097
    0x4051e0f060a091e0e0f190f02030103060506190513021213050706022b0c051002210402030307140a0512040f0e1e06010c08040b0a08070206070e0907 66
    0x448000d600e40d400142034000d25078030b854408600d0302d110341841d801c102c9000d040413400a4024491840b11642da40e400c0594400c0c20240c50700d54081c02c4844a142080510b606441e11301030582c03040154010358101c9001e154100300f680c1d038000c14040c0090908544c641c0c2034507200014001450038940d00080980120401401c160080c1e981020400c4180d40c00000640708070400001c0200800000e400b9100b1440a40104451f508100007920361252010041c01e80848140078080e01c1090100349681c0c0080403140000d039014200e000035801441003d0395850307124000400046007030500c80c00303203074017500852400320039844988018810180d218141d0042e14100c5c1c0c04900704002008001d02c465104541e84ca1a0241c2881c00301059403014801080d4001005100a10440f80c0060070030381100310406950350340d00413144505662402130017403c0104001c50381c034000001406020400b600c65200e1a10381c0c0c0400d9965240032100c01000a26400c1500700314200300c0320441d00300215050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 315993588 1250 315992338 315992359
    0x206010509181218011701150302071b0f09020405151b030d0f06120807060f0e1006051822031407050102030601021219110f031201080c0604051e 64
    0x10107803e14103250480c0305002804240b01034190901c8001200825090030030303950144140b912100d601805200b140b00d00280e1281550b11107000750100c4a4090f0700010303a40c0042c8a559100554002c10300803035003c86141a000f007a2a1035078400c4a0680e0b40040805504241071400581c031684406c121403070300d55840c524072501300d801300050801c3da00903a10104124040400380310449445501c444400204490140007244021080f5032070b4a42041003c100f000c8107100c01d0010380041e40d8503101602c16602c11500804140e4013040079100101c0d4240101e6890f016a60480001620501d059117001900c2251701c011403020703102e41e01e12904056145480d01c00528016400c800e0054410781d40010030003e0795a03050010814000448005078241101c018402000d00b015950340d0b000c0c04040c03100b40f00d80c5c0904001260080c070b440e80c210307561030402034180068088280310b016618031500e09010f00510b450000e48003600c00103000c000d8a0003003c4407070038a4910030161260450500403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 315994838 1250 315993588 315993631
    0xf090d03050106170c0c07080304170105010501091e171e0c0a0b18030304030f021314060103020a03090b040f120c0213051f030b18150403030b15031e06030c010206010509 75
    0x7d014000c0c15070300051901d40e4903000c0e45c1035000c1c070010303035611840e450032005103c0c682c1c000b0f00303d00a454201c1d02c2c2110708101103c11071140600c0350032560074000a90078094540800082c1021010300041e00d04000190764200341e50742d0702078000c4295000c0c1148e01c051141c615420041c0000714030703490400c5034005124002c1307421584141c000b40d45c0c010031119114158200305054141e00403002800300400a03030300768040e224450240c030360345c1010703000101001ca8a100340c00843d40580c0119000702142054039120400000d078020448040c450521341e001414061184c2003440d0b034003c2c104941003010381e0000070080c00002d000c00c41c41241d45d075107040d401c0b51045003000034621544102000d0f0515000c038810b0344d88510804248c0b43e1081c100072900e400c200060070707006941410007065034422407000030011703110038a183c400c0c100b001c010040e50000d4500d018880000d4603180c0e10a989400090541710350190110700e000d60301642c01007019080c1a10010350158030714000742e504a0520 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 315996088 1250 315994838 315994843
    0x20a0f03141b0706030605061305040b190e0a140c0301032d24061206020904061a070b0601110a1b08030d050f060f0306070c1502030f090d03050106170c0c 68
    0x2e0074080003551221006000c5207425200300f03400b6240071a0301c3d0341889440da00210003056030b401090b01641c0c44141d10351554440074510341a06550a1009071042c0c1c44a0300c03500e031a00c044030700c11095402c200221210b0000d01c1c2203035006108900240307195a0030b58660340c8005c100c0b403009844841c0034004122000c501001c001031900d21403004030b40400c1e1542070902808c0e42491510071a82c1ca00b01003000019085c1c1c810400c0942d0141015071504500000a8010940ca070700042c6050103503131400020318100350050a009214a07441490340c0ca5641c01101d404000c84250880d59010b2100b6102089062020003000c1d44602610050203445100c05415500300100460b29144c81d00c05100448540c1d80d02d041c1e0040c03095030184180340701c84001075519070b805800e00e030601c1200e441403000e1004803040f020030010441419940c82c140760f5550f000705041126242458002c4520803980b031403090003554101c42c400e64522405c2180038504058490020b0324080e049501000405442c4034107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 315997338 1250 315996088 315996127
    0x307061e0c050304060e0303090309040906060b1303060e06060d02011107051002010c12050705220506180f0414071b02090a1409070602101a030f0d020d020a0f0314 72
    0x110780d01c0b20b4581c1454541039094440f00410100241c1007481004004400007003900c850510807074002c59441d4060800c2002026150000080d1490002d40045500c42e1a01c495084038801c2c034040009000450b801e5440b04000da03901588254191101c8004d58821150484100e03100000d40d500590340f100002c014014601104c00542d445107a401d481c282c010346000840c030043c1030144654900900700230124420381c0100d917006125140605844459910f02c8400f801d8040c1c249070f0398082c3c0703602107021007900803071080c80f0381c0c1c1c40110380109007005e01843c1c1c410034169440c000380b51a0365800384d07081038a643d28200100c01c1841038201607070b906404c503030041008401c001642e0081c817007048000e040003402c3d440c0700e520080c41040303a1503001030b0b0b6100041d00480001503420a0f1140300440d420950315441c1c0c50f1241300e040c0741507030002080342e04ca156007030b4003280d1358484c03401003d9842d43d04202c03001d01044c5a41c008203000c81c0c06030a1420b452078021a0542c070b000c14840140903500017 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 315998588 1250 315997338 315997361
    0x30102090a170c12060c0a090f0306060f140a03140a0501050a0e01050603120d0c0302210603011802090c0a02010b06070309060e0d082a010920120307061e 68
    0x1c0740c03034814078a40080c0000000e0342000d8880b84400f4001d400000d90717881c8060001a0303614000030390340d440203100d841c4020107020640e1026a01903501d0400304041c1920340503006104210f51400034040040100c4040082030240217002d07803d255817a40e2440310015031140e5010b00940e8030050010b1030a100c2d881c070030340f4422070008140d142a020682160310080409019071b01003149100c04c804039001b81c6a80030040741d0007060100e1065005c9003e8040c000b1300080c01c07200005c0b42880f000368a1400c40c403840c0160020440003a0894142c88400c001400286d0418083c01c082034008000070028901b50065000104006400c2c80100750254030154094002440212092002542c8400d1500068504840e540000d92160712807034100e1280f20300c005541c0d006d0070300501c041c1524102040d0891241802004900c42c10f0819402d100f80703d61046400b001c0100c440d1020f8a0140e0180c82c071400242c00450820040790354100c010401600b020322100048102048002d402e4020804d1014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 315999838 1250 315998588 315998609
    0x8010f06080c0307050d062f0a08060f010507030503220c09050a140a05040f0c08100b06040f0315090602040303050c1605030d052107050301031a01030c06030902030102090a 76
    0x524001c4554180111040d14a100350082903007086141d490b0000084015048a000a08125809150702c2c0c1c0c143e58040d411001c2c4908111103040d240282c0c0945108400307502c030410180c0e20f01c810069604059030a10703000c80d40034048503000c42e100d00702461748031040c04500781402c00300318002d04083c4400c040445002e10344071802d2210000314003506030412a1a00180645104503030115031800000b8401001140d461000900307200001c001d60340ba081e0020032510069480310000c548480c1104115403145003800c1403414242810400c9034200c3d03079031001030302041e400c1d5a0340348a40c0001d0114016640c1e01c03010300034045401131000744020352003600d4540d90761900d204914240130507407200b01003454100c803080001d9213000c03480081e640c101e07103001aa10310001e40800582c4840010220081c080c0c4810040015081030045050b00e008200034240c5004401216019482c2400001c2400e4a01ca03810442180240c1141056510003400503003010780300d80c0803d02d5898150700075140d0a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 316001088 1250 315999838 315999851
    0x3180f05011b0c1203020102090405090102040f06024c09020112020304050a0b090327121606050d140702010903030b030f06061002070302190915081b01030608010f 72
    0x5603040380050010300a044040c2c94140c01d191603881d160980341c81440003d01ca00304113641014801c1d412101e103100002d00812460405165050023900a4003039100180074194011421500000e41c20500400c1c2c1c079180032844401c141d4071806003c0c803065814810484051403042082508441c03100089510360008800c4400d000040c01071808800c1710b00ba8600c1002031001040b400300c9c46400309504443c0f01c02c110f0b160411810710b140304420001410206d0303003003101903814690b1903801d1200382c00c0710007801c00001e0302d1480d41c5808010300001030385603070740d0000c101490180c405040e003909650b0001600100c4680510480ba0086030344000503591a00c60904040c0c041c03090300310368003050f80108100090011819030b1090040c01c00382c4240c0503042c9416400740300b0040f0307070040c40e4003609074110804c018144580c0f5804074004c401110341000000c1040035900071116080381c641100070003d0400801450828000328244281055104c280c00f08107840c0901905010003810302000400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 316002338 1250 316001088 316001099
    0x2d03030103060c170c090d0c09090b0114060a021902010203070609030509040c1b1b03050a0f051203040c1806150c0203070b0f1e0702100e1009030b070c03180f 70
    0x440c407003035000c1c4613180c04c400140b000400f00300041e200b00ca141615040900111403c00b08414041507006e0078803103017040c141004201d5064003042c101d0b0300380078690440c0030408040000b2406203041120041e03000b403017003641809030005115019401801070303e1400c1910b840d078106072809104298085040050042c200341083c6c4500c00092a4604e0090241c16103545070b004402c0240a002d8951000c19111041c440b280345071001c000c641c09011146610098a4140c3d908502d080c000d5540e07002d822101c1d02c2c43ea482208503441944c0c0303d900c600c0c0c1d4504220100c5a810044104650740694440d0042182c540c00407102d20b50342e1031364640c0c50400c0392901c1054a0071105810200c0da0901c18440d80068422035419580c503528001c3c2d03080090050744400c0c040d40d01401c1c2000e94001c55450f10700032150303046501c512426101351001e1000900c054000d0394559510f100c014030144030700001402040c400c50103906514828940080710503c0031000903030400290b00585503529506004108 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 316003588 1250 316002338 316002347
    0x70504030b07080601121e060f030b01170709050c13060e030c0604230102120406080a0f050906010b0c0304030506090c01110706050d0b04020415110c0409052d03030103060c 76
    0x40c4070250303280c4034403540307030013800200300070034950000e4511a21018022241e8030038502c180d52114040b1800c0000c0c550724181009a030f84544010f5072962001c0303002058038510115101000c0303103d1002040250f2400c035081e002003000401111823003005126030090403105100b07200003060180e482035507900c500804c050034400803800c264890fa02c108410001e846030410b07408000054172a01000d00050800180d00745441c0d01900c0d801d1003000030f00800c0960704602c17164024410300030204071030800c10070044105c941c151415507142d400640100414015280242406071881c2c0c2500c0c00c155482d550640b500707000380d8002400d85c1160400310901c0d60300000e0240d4002d140000ae010b101e1401802602e140b0444413066070894071100e000c0782c00c3d100c0d0340468004214040c0324800204e0105402001d4060034441c44110707010718021a081c51820b8041c80301904c1c2c110028040990041ca551080e5a0400d104a22940d0b2282402c5180810034809035000354010b01001c00c00f41955280200b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 316004838 1250 316003588 316003591
    0x303090602011a1504030f0501150906060e0d2103021c060302330c0d02120315010804050c030105010b1201050a0e0103081b031911061312120203070504030b 69
    0x1107a25151043d010290b503841c1aa0310759100f0f030b0f980700990040e04000940e901c25904040c2184102c80e107804100300c0150b11200d89041a548454620390315005020103030f4001d44506400602501d018800b1407402840440381948641d00f0342208409142c0340f4104000c03030611400c0030940c0440c3c0a940d00ea00170703901d6980d01010020810a2034103650000c0d8048503c5410b00401c142c0d0164800040102002c100700a40078624007691a150400703059507603024442c1400300180640070008803503c10000030740e03004100241942401d104028011612920010070590f958828048404605d4030284100f5001e0260000c07000e540300c43c0704200703082c02881030b03100300e0250410420402c00d440e92445064107595101001c0daa40701142c072030b009003410340c0f40c0c019485804000380110208480071540848004152240c00c4031060340c41e401c9031104400c0740c902e0300b00703419200c0300c0001030603016805001600d1401c05065038410308043c541241c0046034054042400003d0900038400c5504100c1d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 316006088 1250 316004838 316004849
    0x9010f1509050a1b12022a0d020106060f1103070606080c1c0201020705040506060c0f07050a08010204050625051002180d022211130f0b0f190c1b030309 67
    0x20301001580c900c2140f201e02c40181d40008001001760886258910781c0c04880310a43c185104464408044c9110b15158140403000d5482c0d1142d010840c3c4214018003441045807c80e8454081c0e000c4600300580d2280c00c455a2140d25000402440000408034070802c405441c6182c02048030103114801d0107240d40c0010301e60f8405e007802880b0300c00141c2e03000948009960382543c01041548486012034030f41e0107420009d0080d80203100d001e03049400001040411204200c9040c82c66681c6d40c10003078201d106a00845400103010418103c4003160803603100c00712030441120b84000e80f2203440c2c6d41d0a10009910301c81c110b030703000101401440003440c02404d0700401250030921a180c2980082c102403400b0082c0e004404000e0005035146d115a0300084040c604400c2c442d580342d00070b02c44020038442c14016001c2ca82645034020541601e10000c1d681509581c4080510701006803400c1c0d02c1c42e00d0701c0b9011500304114180035000140414461071050032046c5002004141140b40180010380c0d180c03c00c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 316007194 1106 316006088 316006091
    0xf1704150305090613030e0909152508370c020f070e040b07031e0204030303020a02010e1908070c0306090b0a150308030f09010f1509050a 61
    0x10f12400030701c3d0583d40c980d40c41c0c0407540d48171020184090000b0341c0c01822508142032500881d0b4010009004a81841400d0255031542e100200c0703039140c0c000004241000032030500c3d65801e080e1102c2e0700301882c83e0b01e002c90100c4cc02600070114804090000420b0044400a00d060300343c0b0810f01c8842403014944142020b90f07074642d40f02800c002841150300000d10540d201c0d003418060381d444a0b6665498071900c800310301401c03404400241440035003d489001d080184010701c01188652005a1a00c41001000c0e00710342c5203200a0a441d00039a03d002071204510600301c00440d803146500381c84e44400d041a103401401600002d24661614050109020b81c01c0146d501c0f841e00c104040c80020101845241005202e02c0b000780400f006201280007030000006841d031020484000080b00c2e66941ea0310010b5a009015481d004403da071010700c0080031034090560302a0b0704c83d10 = true := by decide +kernel

theorem cover : BRFrame.Cov 315827338 316007194 := by
  have h0 := BRFrame.cov_init 315827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 315827338 ≤ n) (h2 : n < 316007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
