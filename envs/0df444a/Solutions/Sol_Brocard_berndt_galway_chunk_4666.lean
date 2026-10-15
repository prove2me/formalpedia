-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4666
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:20:51.89832+00:00
-- url     : https://prove2.me/submissions/39a33c9e-d33f-482f-8abf-ec49f45567ed

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 839028776 ≤ n < 839208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 839030026 1250 839028776 839028779
    0x1020c01111201171009060209090c120108060907030f2108040507080714011803081b060a181e062a0c020102060601030b0a0e010e07020706140702061c110301 70
    0x8040c1d140b01644400d9560784142e020b10307181c1070040348070300c81c0c031040c0303000050100b400d407900e0701c024000c203501c2d6600302d802c080810944501544c002c00c200d200003846000180e9030b54bc0007d41d9884111543d14041d04502c00420000389421903051400384522401604060703c55640e82070342d886100043c000900400500c014080140580000361400c00007825050b030400c00508040300b02c40310701170304200358006020380d03600c036282e1054080c5900280780360f03450302d030344081c1c2c0d40034a42c0c1c030144c100c50f008100c00300d03034400b55900c04c404442c444400c8803400d44c940c0d83c40e04018841d07a0a044c1c001041e203002581c0004890f0312404607000120404202c5030040c81c68511514540701c40c040013800088664200582e800003029503114a0900e004920407d5640c0070484800441e8807030745100305a0300c00403519030201e15200744900c10607402c5542c3d40d903546608544c2c0c3c1901660140070070904000801c050304004000700b10015005058001030301c85000311000300c48003041c10700c0303104001000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 839031276 1250 839030026 839030047
    0x12260f0415020705120f1c0f14010e040f03090e01060c0b06010f090e0903040306110c1612061a060d0b01094b0609050a0902070b150301020c0111 64
    0x1c0340c450101c0144802c50034a90641d6605980b0245002100100b28020031200704841400080b240704c060201a448541d074400e1008101601c0c5102403003c240f81812078211990300303c440360504a8203000c40e410310359240e5840da16104d9262000c142e040150801c404245081c1c0251420b0080151b0703560041011aa410964256640030713020504100545000c50412540407401c042540e11020014010781ca030511140c2c07461146501c020719580c107003841580303015010005080c468505d5416180403030300201c04108842000d01070703a45103d403036036035030804585164010030310303903954001c4818580b483c5800190329402201461400795141c000400043d44d00c1410400108100340303591404d1190b1845070710720100e401c803040750180c06800322140e1450f6200c0c00101c50384207101042240540350940201b92001d1809024002c4202520001c0c11201a100b2035103940c0d0400001ca00c0707611030545101c0d05001d20b03a0001c2c0c0c1503409001845072003000f8400c480081059440d021faa4050f14403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 839032526 1250 839031276 839031293
    0x8040f080d0917061503030412030e0a06020f2802090a0905010b0604050604140d06050f18030304021f02100c030f05060301090203070b03130c0603020c011812260f04 73
    0x420032200700e414059100e00c3c11200099281d008850f01c01946a282605404a49940190751110103201c840c4c410040525801c075041da01c81c08006d5840101068441e901682c0d20741f411220600706034080086803c440701446410074202e080f01c4640f401c0c2c401144c0006802036400c0e03540c55442c50707907003000004005091207800c003c65000d0b80e890703050901e050000ba2142c01144078003803050803909030700e03056a034900702400c40c0d41c2e40c0b2400800250420040c03002b0909400c8902c03000900100c00080e980d183c0c0041507030f1045600400381c00c0382c00044082445007001d0350300400154440c2401d200030705405801180c1914840e5617000035841c200100c0c2105a44010f410140aa4500341c020301c05a140400d41c03206503800c82411075a6030301c41c0b029091904c140000042c0a0710b40600c0c020038bd20b80e050f002810403141c1c0500911030205911540310303010350308400003440498140d60701c18200340201480c0305904105400c64200d0804150342c140c9520049500c2c101001e41003003040100300e00d01c07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 839033776 1250 839032526 839032529
    0x90b010e0618090601150908120c070909200f0907030515010c0c1512020a09061416061a130506191419093809011208040f080d09 57
    0x18440b41da6a0814200701626890103000c1d5510301b582051a107001940503011001c020700e0054116044949000250b0959401560f03410030140540040001e40300c00600611120b00e401482e58200c1c911700700c1000c0c402c01e0400c0d14060300088464611511507481c40240c9210305190344000c1035902c0c2101106030018841d90806041c420005180750224020b503600070300366481c0c042500f01c50440b01c1e05c00e50b80e8246030040521540e00019050700c415034000181001c42d0300544882c4040c4592081c003501a00400c186500c4100703803c0460320100d281c2e5000450103260450b94010425500c00101d4001d01e05019403040b9180c07500240b0845082443e4a44a556903468184d80260304190f610b402c02248011058841e44111038682c032140615645803006144c58039040042e440301c183d03600b04041c40c0302490220309807400d11413406511034140c1000c0c0c845005004400c41da00300600300d00c0c100000142074500f1202440040341c2001803009510203019000300a045080d0001d400814803c184d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 839035026 1250 839033776 839033809
    0xc1303051f0f0c12091a16020d03020a0203121b13210308010644010f0f0306051506120f070306030b06090403120c05070203010614030a08070501090b010e06 69
    0x60405521840c1d50040e150810310104000c042910701c0c0e1800c1408046d62607078050000e6915403020300c0444090008405030303019032502a514040c0220000303500302d000750300043d001b41c0c1003003240ca030212527908082c40c4d002048c150040711803085400300396415049651110414103840000b8819003e1a81107039841d0101580034241c11209541d0080c0701c02418400c500500c0b2540000880c244214405d202e1441240040c40c0f591031108040c0c1c020418440c95155a1044c002c0c00100341c200c1c51013185400d89030080c103940e0f9828034613540c4c2d0005100080c0034009c0701c0303038034107550744540d8070746000b0520200c44d00003440c09070414941000285070040c004d0701c01d252510f4000c00001e06031000b0715600180480e04032505558506040e40c1c6610f1010f22840101d103840840d0b141e2541000140c40101c3c02a4000c1020645491580c4081040680c510354143d00488103680040d0220b80181811845580003141000f500c0e504d01c01131010a800600c1032481708020484503090003012000d50450 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 839036276 1250 839035026 839035031
    0x3120c03011409090a0f030e010e1f0e01020712080c060a05090c1e03010903030501081002120a0b0a0e01301205160c030b1605040605030c1303051f0f 66
    0x5401012a0420600d040d0741d80103403e00c0780040d900c80700c2400314448154008003017100d28001442c0003400a004c455000f40460036202c2409440d0411030a0140240380e44441a05011b0341e24a081d0340403140052042d0440c03150101c082100074040c10752030a00b51144030a0b985440070380300e060f0b041074070003002e00201e28608000c101600000040205e8408010340e414480101001c01940ca0042c1c00c50a00780c0540c240300840d0704045e03041c0e00040c1203d140c0c2e0700351041c0102040114007607104048840e108004104003244500301a0351119180c10002001c0d09541d0341e441c4581e42094500740e0119140e5240254107880c0d20501d100c04580e601d69014500b00700c1c003100d41c0c81008000302060240100040420042080850741c0d00020300c03241c00c0307542c089419559240034018188100c2e0500e0007444044255a200703070113107050750199080b94480a045685600c111540c981081a01c41154115844004081001404240382c81c00089080c80c41032200b00c1c4c009010f40c0d00003400c03400400d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 839037526 1250 839036276 839036279
    0xf28061404231c021309020a150507021302040e0709292104050c010206060d080702011e020d022107020d0f0c06020a030801050a0b0304020402130f060203120c0301 72
    0x200c40e004540c1901c680c00c5404020400103200b032820300c0903295007560008030ba07688500842e100d01e6044030216208540006007144480303001000d0300c2481c0d40c029088118508180542c6141c0a401102005280b61041c20600c190f000103410f804101c030304140a82d400030f0f080c85190000210300b80c1c458540d081074490b1a2a02e400000c1043c0112080510001800f540c1001041c9000c21034007000d84146508007070340480c403181c0c1402502618101c615108040100445500200e0718a2040000514201008049464411701039018040407030400070140c400080c02030452041c422a81020b600501c42e90803150f00180c9899800c8202001c40c0301101503422001018108550b07060b1390664481d80c4007082032801c401081039030000109903000c00c10002c10780c030b0360000d045811180241d8071460542d1b650402d001b1250950300451921020400014015052a170000d01d1300542d00c04019503038546c2d4054440c0303003440035008100160800511075607040845007495030032640501e521403655 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 839038776 1250 839037526 839037557
    0xf010f060801030b1009020417071202030c0111030f030f160c1115040e0108010c0801170307030f051201060809011401051323070309060522110f2806 66
    0x1400512000304013a44141c0040e480c10f580c04404001000440419511940c84640d000f494050081e940c508501c01d050340041d943d074101c9510802d854003e0094000012250011685e100068002e044588020099500003000700030003107208486620b4a903602e400d24806034001040c4059000e02040314444101c40030896001089484140445e515043c1c906035050071609800380d039205d036000c03181c50800016190810341000c07a12050f5540c80707040c0c0e07a894880e440040070500c0301080c0c41c6d50051103e03000080c01035015114000395070601c1820240d07002c2d44800f00c0d1500340c12175800600f0410074802070b00303000d02460b51085008400b01c903c80d810301d0086480485c10a11180d406c98541c40040008507200301100d00440e600e0b8800300c1c5074641008046d016011a2404440892500001600c0c91190300340e15500e29100c5884075100108135241c100841c1130301025103610120728480d608103035441036000108204220102400011030051003000903d044c0c3c001c001707000d0b104000c0e0307000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 839040026 1250 839038776 839038787
    0x360907080420030c09010f05040e030a080106030f06051011010c030c080f0604060803040b04030317040f0222021c0f09081204050309040e0f0610050f0d02040e150f010f06 75
    0x10182c480e24002c040c0d001d680000c0e2800b0403050886411240640000c00d601030301d040741406507070080d40c00b44421260029900d035244200c80300f040005011b1401403010511907002215500480c3d000407810175103410000350f800c2d840c008808040344024650751a40442801228038400b0300303040401003940b8050015201003001445e0091240e00c1c180040c2c6140e94503032000e400341800504880d151a118420301a060380180000e0700401e101903143c140743c40200a8a51050398480d000b59000c009607800e110940913080c01c1748a20610980c0b030194480203610142c00740510320641c10b00401c422103580c604079680e985001207801d04204058000c12035040844d43c100d1140d0548035025a9542441400c42c0a00300f40c45a020342416485960840d00080ba038801e10303641c4040c2c800d40d07100c03d07a07200860926407154641100c808068030099103130040d00d00c600070303001410105003000c000d92494240044a43d4030b200f41c00541c014031040754020010702340505000c01c1c007040443e0030084041c10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 839041276 1250 839040026 839040053
    0x50c120a02011b210e0303040b0f1e13050a05030f0303070c140d0c020102100c0e04091707080415050711063a0e1903053609070804 58
    0x140300224403010316484a290311144090341045024503003940340c0c4804061400c040482000068003600c410342a846c1c04000c072011680c155180364901461641003031540e07004000d403c1c41c0740307070a80d44040003200750390014056404456440700c0101c3c1481c0070044981841d03005640264800c44c20103642c008000100ca4000b0080e09142c0700300460b83c0341ca4800d804404030707540c1c031500590031021403194106035446c440d135200340c00380e5044107042e60504040b501000d0594000410143e005c992509082d405041d4040c050340030000b0340d101d0120304845030f50003404210340782c90000504018101840b84400f01d94060341c07600920303011460302c07158400c0d041107034080e225480c006600c2d50703500054420f001c0c40c2d501201514007420707403500c0715042301800521900b4071030382412007011402c036001c00c840b0600544040342465821040d141110346030400440c440101c03141440c00054036505c900c0010f40440d0201c0c400d51640310050602c03c0d006005810300b014044044140300000c2c410200189 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 839042526 1250 839041276 839041279
    0x306140108040f08040902030402040507081005130e0f0a020102070609030b07051c0c02100c03090b0c0c0313080a0213022a0102041505030411091e0601020a02040e0a050c120a02 78
    0x50702c03182405448100743c3c450007452520700140018a48045070081c5106038000c480820040d510400706450408080302e500141c00034140050000f4074185c40001d01c584811480000c0100040d000c10307150540e4001d034188682e01401c0c7c5003045680c10071168014007038a181c00c8006034603650b1229824580500a0401e01c0404500c0441a06100104040e10074803d041481a880c1051019444103200c1000309907042c100000892428002d0003881c00e015400000f5200e240d4074600e29100350b42115090041c24042000104c0000b4521031140f8050700746c0030090b0064452a2040105114502d0390030084c00b4014007421881d051601d256840754541712103403071180009950600e00900c00c0c0c1c0c000c201c0507010300a88800d150342c820040d5100758800c001b494030540708041040100700040321019155010030002d0071001808400d1640c0011040c012904484604e42c006000d4813101401c002450b400017129006000b400c0240351450784081c0c1e19030340f041541d0038074191100b41002029 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 839043776 1250 839042526 839042537
    0x2a15010603020708090a09020306150a0e0f0604030c0312020609190206160b10090f02070b062b08031f150e0102150405070518090c0d150501061e03061401 68
    0x2d41400125000c4807208a4002d00c0401b8940c0ca801c0703603000a400c207070b507143d0144090a8003003c800e44060300b1100608066201c1e50100c80000040001d908804c44241307421160a1100000007480c821000c40510710512180c01c501d05c8030703d0024a003e00c02070000c0403036800000450444203201111002041d01603e146035502c60f10034a0440000a0030001801002008204403403c1c80000d0f0b00350a49814000a1001c0035a02c4015410390048440192240c07101d4008501386140c44088000d08042901c200c518000b60061032100303541c81c1540a94400030000100320320104418062900f009010315085603c505051179181101c00d00203244c424007990100c21801a0b000700304000038400622004103852800746409600e4280500c2044d000301c48099103110798100304000c00340305000107c0180350f9041d60030f0802c960002220000d595641600c080d1a501840c14001d49010303007880e0315080003c01c0052806880d800400c0401d008040c0703808024013580c2c44500009102c0502488c04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 839045026 1250 839043776 839043787
    0x60f02040303110c090115200d14040e07051b06040302030d050711070b0307090e150a08150f04060207060f0605030705030c1f1809050603120304022d0301022a1501060302 75
    0x40d1148c00d24140407080140840203001c0305100d00250342802500d0940d01c00100100d0000c05903c0303070140e4024050900c4007140002c602900c140080d000251040700380c00040c0b5200d050b00b6080c6a01600c00350016040054036450016080c041c694102c6818600500c0540e060484a503c54009004007200380800002050b20a03114054a4018001404c043c026905100c600140700d01d0020110500455070305c1e00c001084240071605034045088411465080d5449d40180c01484030000d108560b036a50911500001c42d1441c441c1c81d9124009840009209062034101403600d0403961010b442584802d51300c91140c0c81d02c1c400b24185200c61614100071070700c1c403081543c04039401301500840301d00c80540014070f407140340c205da802104190140d400c000030794510640d16103c21a00a90024440d0825079840c155034456650013440154203150345a03c1c020005e420ba90003210703d116400d040b2030b8200091181c0d00340d41c01d603030382ca03040042507088102c4d00d0f0003141403030511a10040c940d02054 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 839046276 1250 839045026 839045069
    0x10f05060304020145060207120f05120412020315010b0f0918040506100603060312180b040f0302031c020a0209150604031a090c032503060f02040303110c0901 70
    0x85c2214801000c8141e0700c15440c0d15500c0041544010480f120140d440022a2400030a200d020f48542e010349807010001a01c44810701081e1100499807480341d81d003580c40400c1c403000075001510042c01000e0800140f030041610303010340112541c4800b02e809004000e0f034418101150ba46001051055440d0301c050720005e20048a02007101d004504503d0800080000224213075205036510a03407100710769114030080301151003a00006203410746c40b581c0700e201140541028045c6144030402268040c0d04da0480c0d540f07030b030403030780c821410b84a1446081c01107150501c440d103e6100003207103190009484001c005e64400604401034020030042703000c109146a450782040c548540507150341e5513541d076841c101c00314000c0101c48203101103020000ca03052480115190084440050041000d0b0125818851010451030301721202c101e800700700000052030382d000c0c000344107102d104010780391451402c0c041c01d24045008061000d0f04400c0c4101c02c166601c103081815140d25600355501059400c5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 839047526 1250 839046276 839046317
    0x10f0506010207031421180f010f032f1b1609020319060305030414060f12042916080402010903061e0e0607140f0a141c06080d0c05070e15060a0201050609010f050603040201 76
    0x100a84080d1000d003180d00009030f8120300800c100a00c1403480d00c80301c84437601050b103c4420341a05140c00401920800062009801071504140d0044480342d8003010050250216942d1b640115000c0c0c10210381081079440b051004a0031000a031001854001e140d00120400c0c8151902c1495005885011806120100b420100c581e8000c44003e4002060410b417100030300c6c41242c04080c121002546281031602c0b80100c0c07400303554103848000d420340c2107580e260050800081310049060006d62008240c003a280a59072104000b100644414240410010901111000d1407510354008100c06d000003100601100c11110300c3d40362a00f014140c07090154081d108944004104100300c4194030880c909551201c1c0440e01d465007120b84c0ca603200300e426207586490241c0a40703d500410300c104041056000310551251030b0285101402d07030f0500020b5241d070018050000143c0d5500d0802c056403e00c0890035024000039038840001d0b5140a000400d0344c480200000d0421421b002c0c1c1049441042 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 839048776 1250 839047526 839047571
    0xc01140c210d0b0a120303090611070f06141b0c1204090b0406060e01091418101406090a03030c0f0501051602010f0506010207031421180f010f03 64
    0xc084480ea00401c034140300e085401402ca9100454036245503c00c10385803d13012107044503002c0c0038002043c10b035600d041d002061548425900180c0310203002400c11092402004030621810113403c41c800c41d420144100d4004181d00e031038820000b0180004040c00e00c8030355491440001324240d8524810303420030309100340c074002006071840120f0082200300d00350b08041145041501d007045000d03610441180e0400c44241440e0201d1030303500301030200b00003211041c0407011002d80b1140498500c1421070400e4001100d103250005415082484581c0f2401080c111132001111024104070005000591400241c8801402e00a40058050401c41040e13000102c1c260400002c000380e14103410000014140100c1707082c0154038001c1900c140d50351502c91340307001d580103038003c0030f41d01d00f5076542903003024804010b000c40d8418405000b40b051010810860f800c0800c02e030480c2c07118550116414266847c030b900d18480c03203403e441d011880c0d900c41c088020a9003103207008101424480780c2e600b03010064 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 839050026 1250 839048776 839048803
    0xe0c0a1205010b0d0b010309080d02070201020a02090412020708070e0708060d2010080c042c070c0201170403120f060308030f01030b010b12060415081507110c01140c 73
    0x204400020241c0300034010300040c184d148001c3c409054000700440480c0c21581d0001e103002414400200442210b5000d001120700c18011106076041c65000140080703402c641c00c8600e000c02d5001114555414800c200040a000006246450074010802400c140080a280c01c101492000600d07941d2101508804950403104815070002d131140d0004208002d076140c28040d000018045410318410100702d4440c0c03503034411103804d041c00c00503040250b00c1700f100046810b12064200c4001e145d00300c07045500510040c2c850141810311032001501300032428000741481440705d810400800d42005003c16842031103040014404d8411020030002c10440d0000740805001204101ea10320710360000798180c81c000d03100c08041d070b031b80c500101005100704a1107800a9804201250701c60400e1f03005211544984d591a82c055a1a000070324508810191300e00c01c1e901061080c0240541c12031814195031000c8009007803001000000030b000324101410944c0140800591601c82510500c07040d4440b585 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 839051276 1250 839050026 839050031
    0xf03051512070603050619091a0a0e0603070b0f0d0e07090908040f0504060602030a0c02061c09030f0923062b06120c171608030a180e0c0a12 62
    0x4204149590b2000b01d402850b01003443c2101080c400c0c0380c03c20f071070403040840c44520349403c2e041490040240200084103e6242c0000c2a12441d51b5586070b0003071301801c03c000e0714011514264040515040c0158440302c06001300f0040402d502c0050002c551050f07c6600c408601c0074500d086e910300d482c0e1140c0c0550341b11345c6000041c60810007104010411038920b1008228a60f032030307001708801c079001c9118410169008215001009000d20310a0701118001030201f401c180307003103a060300351215070301249405581d03887e0000d04150300a0071120740104a07240481c840da08144080d003821409480d0040f021480c80d40122241c0e480740101d47c6c60590100d00946080c1d088034001002c0584d00c1d0441d0040ba00340680469600a40d080c2d4450080d00300c0381614045207414100200c401c2031400d460300500a8408001c058034020041300010000c0700c000755900d00a0803001405a0510308509400030081c1c0b0080201000e450b4000da0400c4107410b000d992a0b801020070382d60a680025594041030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 839052526 1250 839051276 839051299
    0xc06020a0908160e0907050a17010e03040b030118060f06031802130905070608040b0a02070812010b040512011b032a080403030e03090a140103020903030d021b0d0f030515 75
    0x5000ca12400111340414824550f26107901601c107849641c1405500d40001c4415002c00a1044501030307030f081080c104000059600100d07403032074115880b0307401c83c600d0400f000004000e812a40ba441916400a032501041050304004038840b900c0c005219010405449401c00c80c082d14890401d5100d4950003070090000b25940c9103003c1c09000d802ca41036849005402c4009482e5020b5000c180c0300d5540440305400503030b1512401c40003500255000c1d00d00764018840c0d950700904d0315525601800400c0c00180c1c0b0f852a02c0c1c100000b0780308a4a071100682d0401c1c46102d0900107044d082d662503889810b012a240d418a81d081f4100e0382e04802a0080c143d240c020140b02d40d400ca410700e80105d0080e40c0034899541004503441d502d1080d45030054001710540810048460024140045004d0500d0003614081096000900e150072601000b5001540060710b40400c0c0300810b4664200c04400c4082c08114503d88e0015040702c6243c15181d05064440740054107c0c0700f440482c542c00324004080e081450b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 839053776 1250 839052526 839052553
    0x402031f031406070c0c030308070c02040903031a0a03020a15140409050609100501020a14010e03040b210c03011a0918150a0b0409090c08030c0a030201050a05070c06020a0908 77
    0x119402401c0b4031190080c0c1d0003090f0241e100e00c0800e203505402c0310f61451100d284d40e40c11075444e0401090401000319040c40031005a0b01c9001c0c48805500940d80031500c01a4600600c03098030a02034450700c204054801000141c4941d550b20702200c00d078958983e42c41030000825140007940c00c4d8402c034244c00000380841c2921855000c940642c0050758074904039540d500808440a159005450160740048034020019070b440740b0000704401d000740081801402e1034005803940d0001c0d0001d0399068804940c0b02115210300b9402c4030b0100d40701901d00100d0400080b02c031150300c0103010780030340b6480c0742440d0300308404076004039141c009c40030300700c1c000005200d0542c580140c0241c400c2c1e446280c12399910a010700d400000c03101a5070380050313858078042c039000001c8028500c2a1042b180d25118440000b5082c0c8140098a04e1041040c082c0c00703054841e1500a007101c000600000d800340ca00400d01c904194854010001607078000401a030721981111300303481e1070070691f201c3c45803446105000c8045 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 839055026 1250 839053776 839053793
    0x3060a050406060c060c051602060d0e1c17010f0b0705010b0d06060e0901051005010c05010b0a06020a021f050f160c090e0c01050c030d09020d0804081c0c03020c0402031f03 76
    0xc600400d0b0070460031b00e11100840c5d50788602d40c241181460410000b001501d0418014117118041d25400280c00703080000c070a040010008850020055110008580c0c40e04246103600d6040c018003140031a6040071b440130048030140c010103100074004039160042110943c880d2141210040c00107079408801d1500401600720750045243e08400d45020481165050003254021b880c0ba01041078014180300044901300340c03d035020303a025901e48420f50b0050311240d24000140240d640a001d900c0c0c080e0043c4503100a0b595008071419030348100300102540c1c4401955403c01000d00c540383c3d55880030369a660641400f460103002c07544010340025030b0b881143c1c003040040e50000e0a403030f00020000c0044da240d020f540703400c1c1c030103030001c201c4154031f90f00c1940119074281c4001c050b0020500d06403511103550b0481d03044840c00d980100813814100c140503000588884c440cac5050b4441899a9400a413103881a09070039020f540c001c80843d2a8101095814170f199a00400c02040c05540c0d0800484 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 839056276 1250 839055026 839055047
    0x30f2211040612020d0b0a0204090204121704060903030c150c021b030312131e140705151617070c050a0f0e0408070204021c050612030a1403060a05040606 68
    0x10840c42d10304002800800300c188070241c1038000b401c01600c1d070a41c0d282c2c01460072004140c402003c2c0d0030840850b10304090300c09040500004102a07409848a2501d02030000341d003400304011460600c42048082d5100b41c00c50256075040c0f510a89000c0030b0f1410007900d9a030018501851410034480c80074407940000c803c1070003485004c40900b0803001d0400e0541701d01c5440b01e541d01e1507900a00140c64826546028940b880c070480650b001004210702024035040d6442d01101c2c4204500d01070000c03a101007040b400a4003049070b001140e05144078800c0c005100d100c0041d81062640e528070014801070140072803d000c8a4440e440c2e49040610704803030200b805008261240034540404a014004882900e099036100819038801c1d0320349440d0040590041c820480e40a9020089030f0305200c9615500350944003d500d0108442c00e281d010000e40004202042949500900c08654150390101801090307a103038211240c0c0d2900d4645c003141130b03c2c05d29041680c0080c01d00000241e1158041c45864 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 839057526 1250 839056276 839056279
    0x1a0f0a0c0507060f2a05010501080d120c09051e0909101103010b030c180604060521091c0201140916090501050d020f06071a090d1103030f2211 63
    0xb80b0003600d81c04256810b00c01e12240100080c100c81e1aa0601500340b0704e004800125072052003601003031592040d007501c030f09810003c03c5801c0032a494000035040f59425089640d008030070300c0400c000d410700408055407441241c4c0703c2c0301860003405101d00b040e500c95070040001340c2981a1450000032150f9181002c0b84d0500410b480c21040c00c40e0804c0300003d40c0c4c1a1501d42001c41d2454607070000c4840c0a0300565900c1603000d003d01c4901f00a03996400061000748240d80340c16440da42c08444103854030410100313410340d8090031820000360308000b0603145444018141003910660242c0f8080303004240403101200b0b862541028080c140134005030705a2414042d00348580d0040d1140d40b1142074030303428803807503401c09003d10385a401440c11451340b01c5200d1000e0019800e001351a102d0403074911240c881d0031051ba511000b40a40c0030001d06c031600827400d0a00340000e4a0aa09080981c2c0f440014064400c10200402260307001031008201030590071201e13501d03036409070903003881c0d00c840c81a02c0505 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 839058776 1250 839057526 839057533
    0x4060c05092e0503090703020105030c131401030b0102010519200408250f300c030b24060a0302040302120102183304151205060117011a0f0a0c05 64
    0x4594a02c50001c8a05c130b00700041c00b421031b19203594015656908042e000181c000014010800c61080e000703000c1005050360012820307002000c0340050300301c0316403440003030441e4108020031030602034052045010821440000aa003440300114074002450b001c10034105000001c1c000030900c40008040d00c0da1024042498001c4405812801c1ca0711890304c81c041840fa0a26001c10005000200c020707520000200e01c03482c3c001b1a010903041560124000b01d907000c03c0c280007481441594040c09501000308035a224011181400c00d503a00d02000c29960321a110010701d1407040b61081e01958000d40e400341100d006000040c2946010303402c41d00d049010041d015500004c03500e42842a042c1107804650f01c0c465a07a000d00480d94105020b000c0d241f65030300308010004040d03a4040f150b00c00001180d5076041d9800c50030030070a00792040508074038100040742c07401508258804a01c00e04480e1001201c000c070600300043e500c4140244030404000b440081340c2c8012403600403404590091151094 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 839060026 1250 839058776 839058859
    0x2011101090309180507171e01120b010f0803070204020d020f0403080403150b2b021512090609031603020a0803040b150114030106030c11070602150a0b0904060c0509 73
    0x1000311a422140840040c00030034607047da4003c0c2008894101c01450280342006045000b0306081100030382c050342e104440720080b681401905031101d40907107588190081e4540c0f038001d02c20303a81c1c0a400c2d00640705550000760f103000764481e54102c40e1004c9200111940740d81d40e908101d40680c00c144400d03103030700302c1004900650401500c14000003440040602040a040134a954142e8812464800f604080041c80724003680e80c5401d01c1503508502c4808030380ea943c024a0ba2059680086c0a043e51940103a040c0b12802201100f03440803c403450240f040041c8041c2070803407820500c540e014106a40000601050140c2c1c280302c2886184070058104450790500c004641048008040800303462080c0010f1100c0ca100c0e07003144c2001da400d46420f8044c1101d081c0a0340c10306030700340e00484c00740e8048a0308912448410b910198805011034040000c10380c00c401040c00710303070010801007900e0303950004640c545000300c094a080c898054141d00c2070f074a40b040395245440c00b4180b50f000e035401c00f014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 839061276 1250 839060026 839060069
    0x30b01020d08100303050304060b0a03320c010807200d0f1803081819030c0b04080303010b13081506040609200a0e030d0e090105010305041e02011101090309 69
    0x401c83c051a040e03289001094550785040352503420141044442a4035010781e0b21442d80d401a00e54081d501401e0f02c448807900300310064441004178180402c0c00f00c00785911400808000c01c94000c400400c0c01c014200e503070340f07100882d016000d6405542143d07590f080c8401d90b008000034040000310b001c1e1140342d90040c030303000186c1d01c10340e4040d0903176030060145100340001554900034001002400c801a0942c1a03d400020000307950000b2030010030310320400c10424807021246400c01080c01c1e8400d04c3ca018102261252a48030500440040074000520300000148103680c03200280113007400c0e0340c1459449456100782c80800c0e25420700c690708040c00810042283e204445241c00c8401c40030f14942902e030b96442d40354104c0c40c820b030b00380702e020044654541c0f000d000c11964440180d03500350501d204041042030510040c0c00c102e04141c980300810000035600313001489004003480151100400c10310040300ea005d85518010007070350070300701c0c408e0406403c40e80e00c2098440e2a2145105006040d5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 839062526 1250 839061276 839061287
    0x4270605010e01120f0206091e13110a05031e01090c080f060604060c050c0916091d06221a0301050a09030c0320030f070b092a060712030b01020d 64
    0x1955282c001c1c0c54440c2001500001c5c20001041c40a010181424002030018500c0501003101d152016440480000d1078034041c1110300d0740c4201182d04000e0b1071203240321120113024080c030703540a001d0008041400321b90401d02202501d2070480c00300c1215a103503407000c0050f01603002d2038404a8240408103401c0002002c0c483d200d400c01030f01c807508203480c0030b504413484178490303909a9450240c0d06c5d84100139110b48541500c035000c089000c1c00d000024480c014607401c00b503132082d5003100b0208008111380c0c00c082032050700003004407005c0c090750b00d081c4640c140540c18a010420a10324003850f41011030a1003410f80d1248070110000c20095907040c24802c1922030b101070041c0020343c01c0300703590700190290010344410307094013410407190104c00380c5092039940210101c003012080410302074100442c0f421402d13400354440e000781c60904e81d07442d0001604250f0440400f0400070000700c40c40c0ba41c441400307480d60250044000749070ba03610740c98003800030007200315036030b00502501501c14041f50044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 839063776 1250 839062526 839062529
    0x90e31061503240f0501062610090504030512150a0b040302060a0f0c0609110a0b092b050717150c03010608060627130608030d090204270605010e01 65
    0x10450214002c8580c40083c440080441112250b994540403401c14685900ca81030190813a074407650414015000043d1800341483c510503110102d1000f0011250980c09680c400c1b01e840c0e006c08941c2d600e6500d410754580c01340104982c50300c00f00c503040201c03d00ca5060a241c0c1810150382601059444003851880c0b03109a01010f504403000708071201086105400c802c100000c2490102ca0700429032341c41c4000d441d07109000b642c51545801404c001480c0800102c0d004088212000e071400703803000c020642142455038180e5414846200000710900700c0340c14109580e9000c0140d40ea1035444106901030106512568000c501c00e038100d2001000500c0c006901500031884450b086a180c030004032000400200500e070022402d22000406420b0b03024690700818080c081e50072a400c20105000c5e1000d03030060752480080c141142003107880d00200031500c0c081007400300450264003034004034028040212001558401007140b103861054950209400f1500c00c00052080da40d07a0303003542111402c207 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 839065026 1250 839063776 839063783
    0xb011a07030c0f050c0d050703061d0a06050405010b150309070510050415020a062c01060f05040b190b03010905060f0f0105130801052a030106090e31061503 69
    0x10007075444080f4248403030008440c0d2040d41240c0650500c2070129052600a14007200d03d075004010500c10052140107002c04568018842007a0f00c48c1502140d81d0f64855007006050141d0760380c04203042c00710a41041043ea103000c1c2034050610f090541c0c00300b90742c1c01181c3d064980d02802e0408901494160341c01d17600b5001a40c0c0b100d042038100030080ca1741800c144000e80c203501c140380d10b000015105000da403042704410601d100801030004640108420414010a06645068020305c560b07002a8540703c00e03240261000035003200145e000c6002d40125581108403440b5103940000c008802070011070503150500801d20454030b917034091000041400c00015409022085000440c0d4460b502400010f00080348218516542c1c40c225400c6034010f548080301904800f10305884002151f42a812024540154030b19540c94500d001b03080324100e0003030107c10881d00e404070302d2203914811030700e84902e446100d1180d075020000031035920036941201201d107035040c0203600c8180c1207880201d8088942 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 839066276 1250 839065026 839065037
    0x6080609040f120903241508070b0c0a050312240f0d0302030d05010e100503240c1e0304021e010e0108270709110301060c0213090503070b011a0703 65
    0xd0307940d80d10030700b80d200400150801003041130010208881c03003841040c102d90b90800301d43c8442e516031400306a403014501e002e07170300c40302420030020250006056030880d420451015111121403d02904103840554003410720301c00480c000208500b0004242d0150b0100c07190750464003080d03d8180340d07020a44000c10b40c8a42491840001c601b030100085a80074441d205403031800e080d15108904856080e00700c805045130900400c070f6182d901c4096200070703220880c0203044003054061810701400c0c2050030b094440d1800170108810b41d4199054500305c92000d0b10b801c8840300d001d8030b00c405942080307905a10580701100310498400044c07032103440c003400c1a900c540c182c0c94100010740e01c01d90003800c0b507100130803d030090242d0350010100020000800b10050003406242c007031610155503010440b0311010504000400406410090303810600f6410303103508030301034846148103005101c007041c09401c0e4000050000200655040014143d4132450b4114100000001707003403038580240c2c10010007140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 839067526 1250 839066276 839066303
    0x90a0e010b03273d0902040c0e1c020a030c0803030a0f1a0409230303040b09150f0406111810020705010c03110a050f15011401051902250608060904 65
    0x30b1000310040b11540e186445242100100c03040e101c0c0715100e0600e0000c03150307605c84181d4210f00d003030300a0f001040c01307616081940c0107810000035607040c15110700c000e090800e14180411502c0704200301e40196023101da10f0400b90755401c651900c81e4412609050100e00c0c284208002d440107105070684540c9204c452501c52800c1d9082c400100701c001c0e4160b41c0340c181c0c98031120110840784800c2c0440715988028644074140303407812014401c03001e40951100d03040402442c4101041402c4558001417204510032540c4842c24810024101c00d100302401800000d03c1945060f911400e242c00c40b541900c1c50b0712a806003003402c0342c81c0c5210303002d1280051007850001c0d0100c0e100b40780c036000d601403110545000c14826a04c544c500764200e02d030340b800368021000c02551080070500d218014610f070100c54040c2149100024044d224504011700a01ea0348114032515170310800c0760351124141d000403203008030006001106254250b00c1440300080c1000000381c2c1c0784c1040c0c081680100e901803026140d12 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 839068776 1250 839067526 839067553
    0x80616050a0201240302190b0909070c1a0105010e0a0e010504111c050709090606170a1407110d1e0e0d050304030c0f050603130206090a0e010b0327 65
    0x950181ca00c1e04110341d210110f11064840c68045005010080583c5120181c59441440481a031440300355002080080c403c022501c00c40007120300042c0b0450b0510201d640b034080c1550059a00c52024055500c01c10001c403510b2007114046058a0090700c410280200100400850f80b881c0d001b580c4585131100c004020500f0142c020a011442c072021150500a80300250441c80c07090728100850181c81e403007031045650b0800a09806040d22880601a21781081d0300334024515031603441c28445844000038002d0070695001e40803c9040340955400c80c1001400182810600c0388104003070302960884081c918041e0780304c1550400b41141c0c0c03460340c25040d0015203000c000c200c00503420000c1e001c1102e00180c01030005001445c030500003071000d503052400c0e610f035900c0c080c0c10036030140c40304000b800f9800980004200300031340e040f20240d40d115100800b107103030341005601c184408040707040007046001d00e60014511803a149801582d482081c0740000540700e510041c400c105030081c90380032241 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 839070026 1250 839068776 839068787
    0xe07050405060604030b0901020307030b1c0b0a0b090a06030201020d091a030702030712021c0c081c020c07090b040b030619020d1407020312070906210f020c0303010f080616 76
    0x220400070f010034109580c0e6110b2601c8004201c07901c80242e54000100840c482d05031080d940ca02d0410740e44041080307840e000a00d41c5900c9905c001d0145410800040c04424454010310791400001d0082002c6081030315031480541031a01049000d40581281004042d1041c0a00000c07280d031040c041224868213011011260b102800002c00c5020812580d40414a01d80303007410100d800d81c0c000c01e00c0341c0390807000100d42150f0303c0e641002c0010300b061010208144800f030716800b50f651910101c0752440181440b00911032004801118081c2e180c0000f56482e06a0100c0b00e00c043c00e171010f00a01e00301030b0070592034100031102c00c21081c40c801214402d846040d40540521010000000f03a0400d800c10f410440440c115124001a03000044003502d01c0c40c81004a030300311640d4203110010606141011b000140b0385050303607802900b24044108121026000082c08000c8103004566039207040011a0700c0e42d000340515a186405004000b031300c1c0c00001205842500c42e0440410b9082521030304845 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 839071276 1250 839070026 839070031
    0xf0509191403073807211b030806010807030b12330c1b06010339090216080711031207050307020f010e0a0f1d0103050703030c03090e0901050a0f0e07050405 69
    0xb4031080c045a030000e06805207400d00d0424020281c55000c0c1b80000c001c042244100003000d480034402800d200007a0005075071034100d0b0090a052405548a00e0100d0040450300203a42d400480c2215101c407884000c503230004070038001c602c2c3c405200301300004014109550740c031f00030215a59500189000501c08080c3ca03841400894200b680f4514400c9149000e138280c1080d00c0c0c41100b540c910501311040c5910742c11100314400c0070301c8449030b10294a90480c9103807143c605804e40000d10300196010024141c2a20b81e881085543c80f2401414a80d45003a01c6107071042c0244500310301052000400c10940e44105c0d88140298541100380e402d020b548050b031a000c9052200607031010f445592403102c44030107042c5840350110750925180e00441e1007d1042822440040580010700106030042540410740e81c060030700c00d83e01c5102d841d046502520f03e03030006100603034020501208840c10b4105500401c20314106000300fa140301076840480d00c0448c0f074084140c0c040306042100342003a401050303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 839072526 1250 839071276 839071379
    0xb0f04030c060903020c040f0902010822150507020106124b110d05030301090203100e090336041104120b040b07020c010f050919140307 60
    0x103000c881950b1107105490340940b080300540c008a0b60303964a4180f5210781c1250103903503503040c0503441a076000a00140f0018003c02501400c521040c04c494402c040000400f41d4000001c451304500d02c1c01c4400201000d6852100550030f0040001c0c901c454000b0640f151500452a103899401c981ca6000000c2d00f540f940800e404d418015440c9200302c241d04290182105a100000c0010b480c9401500440c4003206144103441c00c0300c819010030700020a82e0705440d9201e00040ea2500c43d41800403449084c0d50100e00040300c40e000f0082e2041f4044054144650b055000c425201c0d101c60410301c0b682e100d8034107030100100b0005140e05500d401e0b00101d81058000045510b4191100303520345805140781000d50f802100141480104807041c00e04507030100300307440684410210000000c11600d041b44018081207400302c0d0082555680194080303444243d00d460300000ba0b0b840007540100d15032801072501c640034540d000928040d103411241410110030300250700e0b05040081c090034820f280729004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 839073776 1250 839072526 839072537
    0x80a090201140a030c080c03010605120910050903040312080114011b05061503060606091c0311030301060801080c150f0d0b19050a060518091e0c0901020115030b0f0403 74
    0x825140b8a80050034921096500030440083c0f0190103000d90710081d001112407501000100300c480d5021090324500f0b0085070036185103072140940381e440d0440343c42001d4121440d00051000c9206d0000040044920070740d00c8100710301c0050b02c142c40d800c03800d1003103101d45611224074101d50361041001d40564a4200214400e0b0040c03600d4440c03510504032000856400190f000741402d180c01c2200c680e1180088510343d01c0c0503541c8004c1148800e0401d0b500880140114a001c1007501078818840381d2048003045948a683d030304001400b1441c2131080403460b01030b0010341c0486040c03010000030300c040314031038540c0391458107020140700c5d5020144801301e25580c0c1c682c00e05150b0780c0900303481862402601c084100381c1410f0400c161a1102e5003c03509100003040900f100055070140103c81800885201c207207999021410690743c00e18101d1040444810b00800c202c86c0e8015000d44464013080e4001c001d01100114800d060718030500014101240030f60019580003500c0010a074001c1c400c1c03810 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 839075026 1250 839073776 839073797
    0x301270c0906050a11010c080a06050f0d060e2a120c030607120f240803031003150f152103091703040b072006040b0306090603010e0f0a020f0907080a090201 69
    0xf00c901f194460b00307580001a402c201071140c40720143c024400500411145401d205000300f0004000320740c010b2000300007544414031920f15600031310100c0c2d400c1440001c0707003491303082c03131100c0e203074107090700d4516038418010030384200310f420800106e500c03111102400500341a2034040b41501c85200410b07001034039a440e40803009840400c5e0140c0042c0d4008184405a0118034010001c03061290350131144003540140104110a10b91100150441e5040741c40c142580e600080c81802a002e11542c4030515403c01101c5030302641e103407011300119003180b545200c0218584480c428000c5002502400040c00d101c024003550791840c003803021310080c0c1d404076840c0c95601c420170542504800c030241d907080441804100c50071a00302082501e107204581071450182000301440c0103000181109008000300800a80240c138254045c0d640240c0c00411039583c00f9100b8159941d407000000104d009100e144503880d41800c00c00350041c0a02c0f0076440c1c4904a964185602d1700130038072140240e0401280d84023 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 839076276 1250 839075026 839075057
    0x13090501021b330c0a05120c0304050105250813020a0618050402071203090321020a02011a030c0108040c05060403080a1d0102120d060b0301270c0906050a 68
    0x1404414081180182441c1c0202140c00808407400359504503c031400000544100d0740407942503a8404403200304107444088800040710b041c0608440c940413400004141f100e0042c0e480091362050b48500006d00180e45d0b002505450311400d4007072044060180800c0500c054002d0402c190700207070540410307920007001d400042c286040d03940a000813800c1220045413a1f280002c08a028010544017907141c644940c0d00c07030540d81000500407080554428240d010507106600c2c0c0229111802c80f451081c186425100c00294468140d18000d90703c0c103041c94050b00d101070150040d001000f009403548407101001550700c4040200200d444541c4540f0109450343c5520203003020714001c0c00002d840d40711044024101200e480c10f42d1040b2900140c4122040c0c1e4005196000443c000aa4580f80c06610324410f02901d10340d005070204000120001c01e402c40600002041c00562401582c42c0c103d840d03510b4021206114805000a00101e0092108500442c006e041b000e060781307460000c107045c012 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 839077526 1250 839076276 839076307
    0x81306090602181008060f040c0215070228080d0e030706110714160605090a05040f0938150d03080403020709022a0a0c06050d14061309050102 63
    0x83c45294050b0081c90780e02e90a000d00022280d4101c0d0a00c0e802c0c5003042c200092607545019001c9228036190715031852014820300c180800c10940300440c0300070381802113000e52501c0807419401580c681203809428903145941c16034841c2c9800039905450000294210b1001c0d10b01c6541c10700d414801000004005140317480390b070080d507800c08400b5484046600d40145005c4000d49040050b901c41f000580c00a9001e40b0303070400b215001c0c01c00e16a03030941d160102c0c20158460f0b1100f5801468451109469000e80d00008956441010503c0444c810740c1e0b01040c168604c6c0d075446011016a05500c4882c0d0580c541c804d070080040c04100c030800700703902d00050105241d2503040b0005281c080500080507010858400600300c0c010040d41441418a601c000d0b48000046081d409404150140c4602c001401140f003080d03082008150880c3d1504805041c6900100f4102c000314070705140e00c9401000314030345a006880040c01d42c0741c00500351102001a044882080d9525542000341d1000c075203600b0b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 839078776 1250 839077526 839077537
    0xf0307030801030506060f0f010e0f0a0f03060506090405030a030902180c0a031109101b080c030319060e06090a11040602010606020c0a0e060622060c051c081306090602 74
    0x240e4410700d6a40c118034215040010141c46140100f20280d03a40c00d59a41720008144510f10a00c0c0100e410b0b4102c10001c1e490f030130300c1010143c011141002c00300f07001300f080410b0400d8030b00400045c04140c5898003130081c100001c9501910541044c885021410710940100c54a00e000503e070b40c0c20701c0818200c01142100c261240c0880080004a2000721034144c050034080d00070240c0580d040940313500201d21003445012089042241c08482140c0340c240e40c5444454a50300302094035100c484d040c424580e01e03401620010384800c1034400e01e10390f94000f40070b107c0550b500f02030103182d5600e6042c00d025004c2d40180216803000d403504000d00f00744201c2c001400081126030b0004c11071524011001c0d080045015202d070003082c90f11070500c0043c010340c0c14140c000000390740341651050226441b00c0141941c0304441e0b10702e10604000600940d01c10701d09000780f4091010707124004243d408031351403518503071904400b05043c5800104010040c1200400e036600400020071410f17070b1a65041c2c105c0c1e129 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 839080026 1250 839078776 839078783
    0x60b03130209060a06140924040620100b130f0203060a09020313020907050c01020c0a12020609070504050c120c0304060516020705060708070b040506061f200f0307 72
    0x3035019003040d85003582449401820541e0001400760414600400007a869000811101000141c868440d1a0888d103103000f42692400014428501c000e444402e5106120b003400040d86180d88a110240c10f0128512059008009240d00780601081c200600080306203694060382500e0004113101160007049c0650718850401662842d24401b00b0001c85126040544100d2040c010401a10340e145240500c00303404880c04400c0c0d566003401110700e0300c54400c440c42103500214810030000c20005c2c4244a142c0320324042100c47c96100300c1241d840204075241c2d801d0f076010200c200031b07a0030290701c11904400800340c4c0070700d0115241e1007098034080c1035540c802840000030400052113010300c291500301d02c0742400010314141c00d4100960780c1c1082d000b0284501000071b400c1c410462640c003140c101c03550128200e1034a240c141001c0d6210384c030881e00180509440c84558120003100d00302c0309200e8070a52107202c5941480b1101c0724025000304403205041c0f003001c5152428860800180000d00e11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 839081276 1250 839080026 839080051
    0xf0b1206090f070b0d020d18060504060b010503090c12030408031c0605040c0518010e0d050c012019060f110712020312010e15060c0c0f030d080118060b03 68
    0x38403101c540c0c90701401e020600410f4003e41c406000b102c01034411140c5d0440100c10160f2102c4080e10160300a0501d046031124550542c1c680d40100309454020f5407003940100310410480e01e21b04010b603400e2004a5904a1940010443c174101b8a170800c2e10380c0c0042c0e20481100c0c20b0544401c40145198840652088165500e0308441518003140c050140500400da90038032140d2003180000c1c02c0c034003c9002510174a020034076589401d034420076040d105800000d105c00c84a1a082c01e060b61614030008482c4d0004805d403842501480c48202400c0952205400502848c1d140c03945c00c03440a01e007c0e20480c0c92684401806600505a00030f108003500c03000741103503982c0e40e28030b007442551614403241000c2d07400138046516038400700012541121100b0000400d9942c5049003400300380b040740f94269200e000400c01180704c4000080c06020701c0c005840407001d50240004041da00e6a10303001c1e40b00001c840c0c01c014018246e07402030001a08030303201400708842d61646861101a00111940c0b010200c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 839082526 1250 839081276 839081281
    0x207030c0f0509010e07030915060513050f07050a02010b0a090e071a1e0d050108010b12011808160b0408071a250903050601030807060e0d120f0b1206 66
    0xd44890510001d08030054444412481d01001c900000014400d031100c075140c5400240301c00d4040d0708600042c0354451010142161082c1100c0001c21302030090601401c0d40c245001011405807241600450f0301c500c1070740d0180d681800840b0682e10981c00300046540b509000c091740c1d01d50441c1400131344810f03c0045046014000020314001c0c441c0d10a08036401e0f80c841d41010581f0940445c0d91399002d8500010800407100400c4c9180e06c50051803200d442e18010000038400e5040d8480e00b087ca108540344581c07484000039080c00d858800b28001e10703140c04080307d1000100c21200401c0c160105030214100b81040f91101c5102c10012241a113102e017000030087c2c00c00400a000e080c000c40704280c0748549003030050b6244080351502c00c40c00b18043c00c80305030900c481d00407007144001307640c484200c5a4640e100d24024942d9000303644102c0b0650308044052b60300c4030020400c2c807442c071000d41c0e40e9000340d50219000005406c0640150301074907030b80e2074003036400d858041071003416445c403000400c2c035030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 839083776 1250 839082526 839082533
    0x405190611060f0714040815010501030c020307080412021c080c19030e0f12031b070b04031a1f150e102304090c2c010c140a080307020703 61
    0xc091589401d00e507070440300420118400b4101c640790414281c0c5021152544200d030850281d12482e041500c0038400c1c8914100503032400384d02213058a2083e81c4c248544642d400701603940b40602d01d0000c0c0b1a07032041c41305002481d0107000440c4072500041c990803401a60020303189540202400c103461000d00080c0f908242c9104000c2840c03120030a0258045152003518020310910b2034034a00c40c45822620042d0442d40d40d03a8803642101c5085106483d600c0e00d411400140ea1000030030b548900303008044001900b04c9600c01554202c82d04180c280762500320081680507220001070501c0444d00c81c1d41c500080e1948030080c82405812181307a840f42d103404140000d8000a80f413400944501d01e461546901c041e4840c404031000380c2100a2100d1601804080e55440c4c040c43d00050725040c9000d42c201304440e03112aa00306020b1151110000125501d05803041125000445501150f6000525000a45600210b00b158003802c0181e9402101710f030340d90317006644241c0f07540005038000e84050003170 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 839085026 1250 839083776 839083787
    0xc23090d020a060507031d060a050304060b120c01090b04211401110304030314041101050702121501060906020313050d021c0803060a050d02030a0f02030f161a0a02071a04051906 78
    0x1080c2c1210701f64903101c400301c80000c68501c2050100e071304001000c8080360030440c080d0021100400300074207071411500c62040c25640c030b40700031401c80e00080b0f2400000840e9000381c0102c6054904802d80d068071a6907840c01008044e02c1038400f02c071591f0165505100001c001c0c4074401d40201440303885139407403d003400c5c001c0650b101d4500303401c612112a401d010014103500300068003180b080c28460303200e2140d400040c513041c0e035180d4401c01c0f07409405d0301c280500c1d07020a0002d05840407910341160b41500c0c2c21040341c1e28016070b2a840040740351086d00b070160740b80119000c444030340300410703981c807003110500034088003d550307171084400c2d81d0b01005014140c6040c1102a01800069401800302251f6400187d61a2035041d07003c0e000b03582c052212010340d2000c3c46400000c1229600f19482c6481064002c0c0c00d07202c0c2c0d880740014110b030a034903204403d07401030110303205e05810341d0041540c5414821070400d0458009540302c0c5070001000001242c0d2035081c0c2121841007644c501d02100c51402001910 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 839086276 1250 839085026 839085047
    0x607171905090310050c0f040801061a190e060c01020a03090302190305180a030f03080a0f050f16020c0406090b040507140711030703020409050105060102010c23090d020a06050703 79
    0x2441401d12500d00303a80c0f00010304d5600c01100310404074071601d50812000c0148682e01c0c80f00710300140000c0c045901345054005208503144c0b0280750a4041c003180f956002400781c0244401401d9203150103030b803568031407505045020002041c103880d01c9031044206089902c106903010119466110741028541c06002c0403c80100901100364042c00300d98005260380300c1e00c0b0700a081e00300b130420455002e45072205401d01655200030b80f20100c41050030003501c140022211071030700508101d0410440b0785107003c1c007400f48010b421981516154128455078039040041e242045124540900dc91344d07880c1d000c0c1d04000c00b4281c00c0092080050b01c180415120028511400d001c10303900350761800d0b2480002c0320001904404880203100d569030001c0e0174460103a00180d4009d06010a59040c040103610460041d4000d8008008898100805540904400d010280b610503540c504451202d2100003c01c100031000707154076140080c030381c00608915a55044440026004200e00c03040681007a40e101c2c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 839087526 1250 839086276 839086327
    0xf031806090f1f0e06010e10120c12022b170a050f07031b14010b0f090c0919150801140d1403070f050c0406050904080702040506060717 60
    0x74900c01001e91071503446690a0a01c40d1110324800903480000c4680c0c40f1307400f5070702104144e03030301569a0355240035100c000342e85100c0c140d0a0300c500002d840000542e55500290f10071a060380c40c9280181d8203240400345001030b41c01611110444850388001a1807900f00e803030b015109840050103040c1200c1620a07401020301c2054100940e075403142d000070684200c0908044110364034000d80c0740454a0746059071094032040c00c40c0000c54100602c3c85030300b260b60a584c00c006c001002e048400c1104429512801a0b0405004004511000c84500c0207040c800d0740585003002c208a203802221102c183c40d0320542d99000c600f240040e110ba130081100c6c1c01888407503002c4005929650016800640c203003402040310006030f400862185c01070041d90703001ca0300802e0301306440569043c45502c03401c80c1c1201c2407041d4036000d000700c3c5906c1d083e1843c50003107420212640c10240c00f0740c2800300400c0f01030301c5164025000c2c00824000303020442d00490a001c018005500c0703001d016003140c0b611900c4540310 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 839088776 1250 839087526 839087533
    0x6050316050306030a1e060e0604120e130513050303041a011502030d0903031d150603030423030a080f0408010501050105070203033a050405100509210f03180609 71
    0x10f22580c0001d803030540c068028080c0013040c0c0c1c114950b868a00511400208002e041c040b000e8085040400c0003840746000b60544050701000d1003080b41d1420000c80400d910082010784c484074206241c0c4050350240c4031030380001c100c076007a84440e89503400c00c40d02220078421202e00380c4010200c10040c00d005102e03103844100e2008200001030b460340502c05009035107546c0c0c0c0ba0a00705140c4241c02c80c03c16040800207400c41f010300086150307150141280358803880d13420003001c00c000342070000c2100e040340d002205012044641c101c0780e8668014040a06a251192840000104200c800248000070b0b0311998241daa07854a08000c0c2501c80580c0000d06003c018030030100903890200c101d4054050001a01e00f940380d41190010100f00d102e4000745181030240200f840c040b010390701044c02640038104640640d004c0e40040825503800311a11810f075009005800700c0f40d40034000603050041456041030400300c2d15043c01c10756400c11550088043c0560000300c415210a101417504824541c01a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 839090026 1250 839088776 839088781
    0x140405061614070f091a100807181202040e0109060507120501211217011e05030a08040308030709091812030504020f0d02030304180507020601080703120806010e0307060503160503 79
    0x144856100c144542411151105240171070121680a0726150080041c80c0045106207c800281035090032140031300403034081c4007a43c44180c1d05017106012182d81061180a044065081c80301034403001e40c641003075640725030484000072000d008440c801c5415a86130b5540e02920300380207007940c41c180c0c80301c84144200d000440c02c8900c000300d004035040d00019040600c0c1000102240e40300d080b8050b4a8080071180700105584690080503404411030852032011961508101a160302c640301d0000c0c5144020081000020700300405540d01c2441070a19070502a270312003101c009d85000176124405c468003030319034000f0041d80c8016008441d441d89030802c86441c1950100388a0b40103400c050744038410084a560031540c0c00c104543c00740851401401c060103074130f421000980380607a060009070144d20f0001c500180d0010b1030340700702c9802078410300c402c604681d0103807039588014010300c1c10030469a6014840d5102003210782c004005980d01c2560345c3c80c00000c0c080130300b18424010000c20500700103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 839091276 1250 839090026 839090039
    0x21209160f060804051608030a030e0c1c08250c09050402130209030a08120412182304020a17130506060907030b030d0206100506041514040506161407 66
    0x200e041560482d00f03040f0401d44450500c3c902d4403450120180c1c000c40301c00000319940401002420500080d0344040c003002440b110300645a0107204929a001070f40201e80b1402149040c0b20a210325000da10f1051520078202c03201d01110480300d8070071a030284019000780400c00510980801401182c0b0104054145540048e284402d104201c81c140e07900402c003000e00d80d80501c26640c4a40c0d010801664801d950ba40c2d07100f5150741281e00303031400f40a0202c4003000500075401a0400101000c0c0c1c0c03d08241410415401a00c030030754400e51700901142112a5911148010b01c440d28142e12801c13035540c4026244880700e5001850440e51061100d034443c0062000039820343c00500c21288294541da80c19800c800908052610035414442d014800f07034403c2e00801c4a601490f62081e861080307517140d60030b01c543c80c401c910680708200e0440442404481c4105140c001840c4403002c0c0d60729003543c4100080882e000220800316040701c0c0000b1904100e040281031403440510f00180c0181da141c40e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 839092526 1250 839091276 839091299
    0xa050715031b0e03120a0c0b010501030212040602181201051609080709020c191b2709020d080c010c2a021306050a09020c0c040912140d02120916 64
    0x40b485080c003640c90180920b079901440010040181d01d40754030348481420707100902c50041c09005407084c244450010806502ca0f008640b4408010004040035458aa035140001d5102464032501c00900401c60b4100e0707580d0070906c2c00425650b0f0000306aa05003483d05016810b44000c0030301c14490460000c00c40b02c5000709407a402c0750004100142c03240780e000710042c10041280d00d0403550410801441c0d0401ca8540e10140070a03906070010f8a4503074650311003200031800001380b80c2c0010750380d4880300c0200c1465041012098406800b04050324036555030103180d03400c000509940b9035142d98100e0403d6500082541030b00c520003850342407041c1c038154206905c1e0044030b80603001c3c8003209011060290290800703002043c0140c8000b00c0160340b1101480250891444911140110b0401c0c000c24941406890713021074006200c903a03515010726090700c0e003248081e655110000144416030690245202400c505c00e14020108128034103161868100211604201450035025505001026203003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 839093776 1250 839092526 839092571
    0x507052106090c1804020c030a110d09030b040302031c06090b0108041a091207062705060105010509040e06040b0103122d0915090f051e09040606080a05071503 70
    0x2c0c83e80e0b0fa40f01080b8604110200c0645441d070b07002400000c0c41120010000028202d60041e96103028038800018501c035298200d200c008000141080f0080c004200040003194200c0e210340100c920700040b209000074124040660600c2741a52840108821070583c0600c141c003000900c0d00e02071a141a0391803401c0e402c086483c59880c0b4334407000141103c002007058140000c0f02800c0320b07850782e80929000b0041c21490a0507500d01440c61080c022515189030707502c0c0d10382e5000703000e0320040c2c2c00c16004603a6500401c1549611035158039904d078034000f0a000181c05940617001c41038456040d800c000441142e042c4429042001410807205400d064403880d48010301106403103445141805011100c1d0a2517030088140c0d149246585650b80c0c1e0480704500031a44c0c10240020810703a0b0740100049031600c0c1840700d081c6031000f689614549004401154080e120b103000150040c3c54018a1f07103032190902c0d007124280c0c4000f00600803121281e0506460100038942032040b0ba50792509846056410b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 839095026 1250 839093776 839093791
    0x102040e130501062610020304110f012102040509010608130b040f0c060e030105180307021324060305090601050a1206110f040303030b09040506060919050705210609 73
    0x9101e40d08000c0b080d000340300100500c2e80301641d5804d810640d00b40d88600c900c40c0c031036a88120344201180d14014001e90344a2500b04130f00c0751640d469282484902d1320f03d10f030014100403400302c00e1018010300c03a0a820110408280041c0c440b07080505000d80303020103070080010b01000c0d85c20800d80341c0c52661251412a8005400d01403510b07145440f070070381d40d5440402004001c08050202c1d038942e20111452030944102c0090185881e40c00c0c20810035100f000e1b120640e0f401c10445440541070205004201840717246c000103c40d08a00c1ea00424098501102c034400c10f60a88100807069050045035000400704000c2e120ba07500d4071001440c0300e400d07481001021030000381a541440925880840340c5e07800d0b40c0025a4412036200207240c4d543c40703800214082850701d418942241000304e9400d206541c020020280740d103441c2c0c1000005036004100301c408405d141b10b040d40300f81c8180a407078004c1019842d0542c6a80d40c945d240101c8003d02c82900ca014843e20007004071030303510948101e030824007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 839096276 1250 839095026 839095051
    0x70f0914040c150c0f1208161d150a030c090b03010b03040b04080c1006080f0303161116080303040209010e06010f0e01091d0612030337051305010e0102040e 69
    0xf0160740c1561800c1c0950005000c000b8401005001c0c400201a400b101320640d03514480640e0702c442031844502e075031100c00c00000e03103041d0344c1c00401c5919886407040070f00000e00d050a0401b0282446099501000d04403000030b40b01d01031030707450030b4100c0c140d0750140001c0d071030b01400c40d0304004406259020003400600b0950b0440003040502c4a03031022107100700c80c02c2040e03500340d44101e00f44101804181c441c0c0c0072284182120b007a5004c902100b40c07801442c6422690350b07000301126007241d0002074260396440b240a00503007480b591508aa0110003445014080e644134600ba004210340504142d03c000088011202004120307a80201d28000d6422203007042101c0c00748810040b00d0303401030b50300715030498010304004c004c842110780307000e6109880c00c8031300816500440b00d5040e181d00054aa80c26000000381c8064041b4050b203001ca130809600c900740450030b580c6c1945400944070165842503400c0448003841007486820300540c0025440200294985450302d11002c11106008021540143c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 839097526 1250 839096276 839096309
    0xa0b09010b0a03051c0219202805030c18060604050d0302100b010504060c06150f030b090f150c090301150603020d1a060702060d0615181d070c14070f0914040c 70
    0x80c11551214148000949000b140303007500c4c0065595000f00d008190270030355102d2030010701490006041155840060261020a8140780d400c629030358000e003401d40d0000041c4000707c1c2070f403542901400e090b4000d80c01060b24155580101d402c85950781c0d90541045403c0205021035500810b00b810215403141001074601c54401c0d0401400b44980c1000b043c003540d481000041c014540b8005025004160568292103003182c8040d80d5034801048400592504100250101141c2005480130380b0015001241411160b80c154070001d42d5a0407a01c04641d011400a46100c203a00c07540481d18040703086e030700d4102480b0000690600441100901c0303444001000030300881f083d0407a0004002d01284000314203814038014100a10450b81c0361400307124400006031042c41c48048450540c004e00764018a91110441113602d110480d00c240c64181c0034004e01801810200b0020004141d0000810780007070802020406546805a6410034409031100f40300100315009981d0084510069401510380c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 839098776 1250 839097526 839097563
    0x9020909101128120e010c0212070203071211040207060c110703050606040b030a06090f21080406050903090a170d0311032701050a050a0c0f020a0b09010b0a03051c0219 74
    0x4602621404c612410110a003800300d10540040950101a07001d41d01c40441c050340007503841c050040041d500d98081c141c10003100f6200e94403c01554050700c040c81100d4165800300d4103990160004803400350303680c100411170950103010760814525a40180220030b04d1520303420383d115400f03801107109694401008030780d503404001c00c00146502000901000d0b620342021501ca0502d41c41c10f03514041c1c0942d0411035181c040b1100840f8580907202c1c05050381f5251104170040c900200500c2030b43c403080090096540d21340c1060710041464140d61039200d0b000501c1c4a050201081c410001d15003001800c81c18209420141d0b503210400e20800340c10707c0c9040e444e0401c0c60712047c0003590903520300414400d110b003551300b1140c803400d03604405008903081801c2c200c9259034104c4400005800c5010000c00140d000c1007580e030003000c4d210000c654599068000340c0761607403030351044031583c2c01580500200113407004400c3e1840717114000b030480240490300306240424840001400702c011100882d960 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 839100026 1250 839098776 839098787
    0x709050301061706071704110607140c0118050a1401033e071e0206091806030106060c0206030106180905011503050a06061d0409020909101128 63
    0x1010000c00a201c4155600008005100200740c03085181c014070001400440c081c5142c03c0c0c0d06003018030111401e0b030300d58403500043c80544003116800391042000c3e501003007000d00c525032450500000703842440320640c0058005103820b0882c2d2034008040c48200116130700c40d1301c0a41101c0c030361070311403051200c03d000413402880302081c0c0315481e6240440b030502c201404954460080d06e00e48100a07401c0704c030281c14180e402541070003006076090090284002c811801e11581961000e00a40c0c10082904001403a0b581e4a0f0070300142c00c9910802c01c60585024041d600c010100750410720084000c0783c0104031244014000c04003440440644455104c00b1a4031617002448007407401c201075610b41c040120a80c41034030400c0300190424012030b0760ba600c01c0c801c4108560003600d403180148440c502c030480c1000403100c45a840350b0313100010710160b1103285582e48580d0b900c030060034010115902c4d001c201c500442242c0c031000018480c060020038100702c0300001c0d040840510301484150790b0704664 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 839101276 1250 839100026 839100029
    0x30604020f04030f112418030118031707080c1c0c05091009140d050f150402091b090402030604091202030418110909070507060e0c0111060f0403080709 67
    0x25460340001e00003051003010a0035144140c85454500131705c10701041044403800600541c01640048680d032010f28018890003030240a0400c00c42d0708650106500107800c68549a001d56459040002003200300b55204452036446140004003c101e4109510018480e000c01050580c0301080080c4403503802c2d40b24003000d243c610010100b400010841e0b000109560400340e60036001e0621080c10340785441c020f009883c141c2e8802e64403203e201c2000030800100401c6410f0503545401186e0314414030a00620070310103541001c0071030007401c0c00e00d0300c103006100f400100030302c0481c0d43c810001c402d480c50242c2202c08007030084401580325120345c00007600804035008000d044010b140146e030002a0048050400c80345000019020000c9140c0345005440241100b84050541004808502e1500b2440c00c3e40150702d9151117410030105a446400320b4000034800c80d015030290802d100d1a6a0010613803485125200c00b52440c1c0c00d02c3d600c0c00c0b40d120000b0304010b09129180d0002030b0214890441c990 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 839102526 1250 839101276 839101297
    0xe06040227090304150314150d050601080d0f050307050a080c0c0604050f070609053607110c010e0913061b11061b190207051512011a0406030203060402 67
    0x41c80c02d00710107040d0380e5400362184e45211002e004031907140500038456228480c171298411402d41da00e00031204030365040c8041e02c0754414040c003102c2c0c0104200300081800b078000078006050140e20040090f0030040600c1c080420400308004200045030b106094031454851414040b1007500d58038401e1201d8010038441c4c00c40c17440b4072402c0009000c00081d40400180e191402e0300d11660301c411080310071100034040c4a422282412003c09501c0b040c81c00b1011440e811180c466071200e040100400411085c0d544800003041c9200f0b5031040d200501c0b50a014200900703080c0301c842204000b241200c030b001070081c40d190400c0c103400024409550007004400b40e07406d104040c40c40800401400050b402d14000900b0720420001032200100004198452200f000000741031080e900a208000300350500b14408600039044009003d4580092900c0a002c3c650704141c0c554030016603516408070140d0025101c800300c445014502050b1504540540302285005640c982ea004041000f038410510940c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 839103776 1250 839102526 839102599
    0x3020c12160b060418030c110d030503101508010504090f0c0f180504021c170f0c010e0a03121107020a0311030708060f16112e0e060402 60
    0x6441e0001036140441d94140305011401c881c1c0c40740070502044a40d1100300781070008103200300c00301082c02020528043c510030504d01245440e068007203903445111070710480100c0c1020052110111a91a010016004201d00b80d05401c00d04000104240010f104880c001c1d40e40d0040403040c84001c83e410700940da04030040708900d42c2e5916440f5080c82c03061003500601200d200c040340143c00c0a0103286e02458000f02200302200c440c01001e90181140c04c1e0803505c60803220303000018040c900c400b804101610b10f5034140c503042181d076401d007903469200c030388801908061680400603802a040240c0d07041e000d41c0000d4040c1a20303000c100d00c1d04c14031f040694007081d940d03000420001ca000c901c5a03a17110540680c0d420315500c1041d260ba0368403e440034500429034600044101d50008400a4030340c2c424030300031210189101c2400d04103925502c1100801c01c00015411a0111400304841e04068a01d8204076400650000e9619104003a000031300c00e18529401c044036a00039008100095034031040c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 839105026 1250 839103776 839103787
    0x8070218100906050307030228080a0506060109080f0d110f010f0b2b2d0b06090702030a0801030b07260108011112180102130e09060c0a02070603020c12 67
    0x1400c42100d460b1264880960a0107070100b910709010403c04103c9031701a00c0c56034650000494501c98440e540f0500c440700100c80c07000552060200003c40216000e68040c045500b012000140304c0c21103a0050682e0f513018411112810304005100140d0003103514000300e20400ca08000e505106011030500140c3d824842c182c4292400344c0e000e0b007a55078040f281d0811507501030261030841c0302040c1c006c59143e00240c540c400410710b23a20503800c0c01d4541403d0804181d04403401000307006d030078607030682d6100404001c00c519070611011494001307200340011820640010401440c0240501005055010400100703d0700d0b40200300c80980003900025607400d40c0c0385ca07141c565a00c00c0902ca05c1c0394540c20410001296495902102d00c0e407c40756142904d160740305c5100d0070707d00a14158040b0700759400c02000c680c100c101c20608020748184010221141002058030b40fa100b00038004540000040011021082d00003444000721951400d0250b100c1c091703041c01905200f82582c0125054400040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 839106276 1250 839105026 839105041
    0x3040b1b2205100905010c060e1f230606070f0c0806090f06150d03300b0310020c0309120c1324080d12060816150503040b0408070218 59
    0x42816614292100604842d040800704c5800344644038150102d103c070355200021807441d402c140655108281102e1510030907c801c1245011883c2482150640c0c0d0554032840648010000100b43d10740c03040c01c0c80303506003000080c0103481039400080004807050040c000f00021050004000d010701002e0303551600c0c2c0043c12544a6455440899443c098040000c0c46c0c0441c2071030224509074041d000e0082c00c440d5a40c25030b2030080010040c00545446800402c00b035030080400300d60040f04640106040c071085091518005d442e00d01d032840c0a0040c4809021080d00100f0750f8078460046070540340c400010312016043c010f100c1c0305a9001850f04545604907071254000c030400402e14242c0000711505110344108a4001c0d0146500b60342081e4910142240f00745000f403901c41c5072140002d60b0a03603e42c0014580b10075000c11400307101c3c2206003005540402c2c520014140c3d8a420000d265151590305c00e60f0a0b840284001c003201c1c404102203007035403542601000040c0c10b00780e1140d002c0c1130104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 839107526 1250 839106276 839106337
    0x5071703040f02100216032405180f0601030f082a0c09010b130b03270d08010e0408040b03071214150a060905040207110303040b1c0203040b1b 63
    0x2c1c81a4020980c605100031030fa031000038500044050700b407011803001e04554841031016011050340e802e42400d066840c0f4011007034401d2900540c5603100091004820b443c0f2141010101030403000560012401040803030b40100302c55400300d5001c0c07529591100001c00703001103c2c50b085281400054082001c03010740707800050320584440100d0350b481041c0e030303a40a209041c1c882c0d89980444280a0b41c0100001c0070300f4800f541d044405040340c520821031106e1840e404046180d008001540a80481200d046c2c0103d50345014001c0d01d85c50740554030b859110724649200300e2107031b41c2d40c1070000000202c3d034500c101604400d20b44554418440b640c1d101d83c5100b4a61000c5c1c40302c090250843e80403410f140740048005040f503020ba01c949241340c1c03400d802c200080d040801c050382c00441d488200300c00742e54140000c0002d03040da242030a45422801a41c0e0321007c544c0c0300b40d8040b89204000f8040030a4000d00600c0c0d011100c204034554080f0b80d1000400140215100608019a032100d02ca07240c4010a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 839108776 1250 839107526 839107553
    0x5070e04020406050913120e03030f03150d020d0308040c1706040606140d170c03070b011410140a0c0602040b04170a030807080408130e071211030105010507170304 72
    0x211024000141c81c0c04c100f1001c440143c034000300c005c1d41110b0040c0080e4094403002e0a0014900307042d1050414240424250f43c401c42401c2d030000c1c00002045400c0340ca1443c0a5240300b81a901c0600840385a40401c0d2540700300c1c00044d0a02c655100002c0400107001c881d0b6014140645009895403801d0810380ea8650f004e49040b100503041403004199104240d01241116400a003402c6a19450b5211054900c00181030041400310801083d075401d04100001c0030702610a0503000510761600c8251005060300d08402e511900850310081e0005900040514125640301e071000d80e03403500000184e0b82050010402880b1900209001a2040c040c0c000b90085540c0c44020781300403c03541020303075107030710340b2290040200e083c0a0100305810301c00c19820354464461440d440c503010441844c2e101c0380c40c00d0383c40a45500c0016040200150f03000b4548039540494010a03c180c144000c100055400140502410040c01007070030001c0c842502080d20b291001c480075142c0e28103080c20b040320710481704c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 839110026 1250 839108776 839108779
    0x20c061b0a0c150305101205100c0809060f090318010c0219060f0c0503161a010906170f0705010e0402070209131b0806010b09040605100f02010c0f12110705070e0402 73
    0x420201d00000ca02901803d44034507004000807111908291f101000c0c1c01d4505005d407250301c00c031a8200c0eaa00020b104074904039003542c81d10b1080e031804140203860004020b200c030b13451854240070b215118200000350348400d26105403010040170100d004841c0005132300c002a44c068411150490703044191084101622243d50317450754204105502a03a03040294032005082e03520800000ba034800b00184844002407040340010b50891a014216601110a803c907140c440c0c1e0f201d604100e12514130511801880c41c0c100a80013a42400c8a680e40700ea01ea486243d0600041c1610440103541d66412500c14035801040369402c0e0400807000305640c820007000b15030001d004d080303d540c4490152501d8040b140b000008100c913070b0030203a1458242e0044d01c001071700310752100c0d03000c40d980c3e8a42011391100d0311242c0d510901c1541d07244000303003540d15002900041c040c065118083c21a0701c41080480400202408502209803207001030040c80303040009043d41c0501c5501041c414100c010a9000b00e00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 839111276 1250 839110026 839110049
    0x21f0209011e110105070903030e090406091a01060201050a0b031c09120318120f080a1b110f010509030a030e06371803020108040f051b041a01020c061b0a0c 69
    0x42d00d1b84196100b525900028000c01c001c00d050071501d2820120180e4058828040411035102544d514a5801c450080d100f401c2d50315500144200c0e5424400d03140c0c8414004800d100d407500c05000b013502c1b1203510803080702c0c4920040e9130208041c004c142c06401403000c41041c140300091410001c00c15000d401d040d01d0801d50038203001404074290340039150b01e40d400c0f114100c813800d0a9500d900310b40c1d00400c244414800c0482e1158900544140e0403d012070244e4142040d095010081062039400003610506000d0180512030780380d100010106215645800c107203c2915210700015154020480c08507001c201c01c4c80e8194130060300740a20301010003042500e81640d5030000d0103aa000902c840016002c1c03000b020104050740c130411010b60400e0040c8003c041c03c1c00c0c140c81c0d090620350580c1080808113103220383d4841c1c80c00c0c24802c0030000011240d0b1030000445100000303468a4140050600c166004115071100c2510400552100c0704508202e900c0e551991030304801c007440c0ca01c1203405a20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 839112526 1250 839111276 839111281
    0x4111b250e1602060705030a180f03030b012c010216031406180c010f120603060b011119060c11010905060106080c1c0c020708010207060f0606021f0209011e110105 72
    0x500700002000742282c550003a01a0344d45105003100c260300001c00d8900c0c1c0a80710b110700341032140b00c1858206100d009240d42c901c0d80f0214107001d4165450401c4080c100002c1e5988071807425110641d0b4262a14102c03603841c180d00d84100100e15020480b0800801c03907030642000030421075016900382030741d45c401f42542c03840d560b8180000204a4130181e000c280703800c0703407600c0311a541c42000410091240c40c00c01a00e41e640c1d12008804540d0540c0049400700e5480d00da04c00c2941e0011040043d20328520014603a4960001000c02000000b0000420340c6848100300f09450707014a0141000000005c0200040c5043e4104642c0e11403003840740c0b002003061272020580c9030881e40c0c100e0340584442d50040f4000c0010300f90071401424039603100d2085000701d44010400100a000810455005210229200b8000c101e5001110001d91004095601441ea440a1202083c40350200340b202444010b840d00d40d072a005a410301c00704000107118501c2005a074202940003c0194060026a4020807065 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 839113776 1250 839112526 839112541
    0xf0c15010b04230f1e060c01270b130206040b0c0106090e120f180303070c0e0604020301081c270518010608042013020a0906020607021510080613050c04111b250e 71
    0xc4c0d492200542848ad105000640e032101900c0902030351031000c0c203c03518181c2e88690f05c1c20b00d0742000710b81504994450764104581122030086181952814024040290b56081c3c048494400d0a24540310742c1400f2030b40c40307800c1440c4907044405940140a40369030702c51914024030380881b00d02031015079000d245c001c030301d03603041c54401d0303e0580300700c0f50041c0300352020509910608038103204400c00b00142c0c0c440006000c02540c840e440b00d0303118031485800243c00d0204008015159800040400c400784004111300e43d40025510340240d081420b81c820080c0041c2c1c2c54803a40d911242854220114010761080364059600820201c100c9507101140c140c0c41d83d0040742c4502040d50b406005a10124007005501d006092654011025480030502c013940ca80c211810607004541b1808200c121840300024881e05016401c0544411138080204084401505501d80941e65061081390541040746900e40010070442d000358212140c1d6000b080b070180c484500e00c0c6040e0107803480341d54811010480d403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 839115026 1250 839113776 839113841
    0x161a21010f0911030601031a0a170c03010203161404090908030403120e0d0509040e0a140708010b0a090c030f0f02040f0905010b0f0c15010b04230f1e060c01 69
    0xc10000c103c0c1e549561160300044001c0d18030f1002518100d0b0303500d1005c000d583d5481408200030880008501d4040d680000078504185d10003481078003d900401c100040300c010b2103042403c900550400c001e1080446040702d08900440e04400e81903840c11950300103200800307010f03622403882a617074408041540142c840030b0310901c0400d00c02583c015503e8070706481c0288041e00c1c4045005e40300040e4000c407071801a190102011040d5003461440070007664660060020702e000d002c021000b03001903440400031a20940c05072003113050040d0398207002d41d030301071094101d0034a500c05048181b0408280348802c00c001d500610074880716401d5424001180b609034015641242c3c91013402a080900140001901c1c0d48a11300c00021070043c0c2ea940291b2880d04604540030304101d000182d103480c00c003000240c4c0e001c0613881848031101d03070386403071840f903518494800f4094800f6264041800009900c100300302d03400c001070340d86c80400401c04420610055101e10800341c1d8141c0804019008140840300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 839116276 1250 839115026 839115041
    0x2031e0a0b032116061a0a12030509042306100212071b0e04060e060109051302040e03041a07020405010501180b0708090603070206090f161a21010f09 66
    0x30940c204010000002c040b41c2c030044580700403e01d90501c0c00b8010345869007102c5000400f128841d41d51119040c10107000310318544682c01c185c1f0035001131424410b5011170030749202001800c11078001020081915242c11891140040003d00c45222500da1016007060300101e072164020112460300301c848a100040e4000510981c44c00b244c5000243d48440c1c1d02c000148a0071060003520300800501d04200e40c51840c4a075009907030004038252101103060805c50181d000300c144074104814031034200c102035450700295504580015004012168a5013540296449180324001503030303604c2d058101480c0200107041c802c032000c004036030301ca50040d10444110403800c905400302401c14801407100400a005090240c20914100a10180001c4071a44219403801c01a0458000d0182c4c20000304103000480601034054858030075104403c0c1f6400f003a070300c03900b050440907500c910541c00e01141100c3e840e15940081038050200382540c00b02003002841503207496003852100148402c80d0f440f8149 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 839117526 1250 839116276 839116279
    0xc0305061810060c0204060503060708100e10051e040e0a061113120f0b0408071e02090610030b0604090c09090b030309062a0610050d0503040501110a050102031e0a0b 73
    0xc881418a0001c42d0141c101400480c1c0041c6d590307c001c110342e64200404c1c2c1c0303c2c0c01c49544001c000e1424090240766a40d095003c081401c00130024405c0d20b01a41c1d002e5820ba4070300381c0e007450f100c1071909100c070034000220281d50f41003071400994264440d40400c8560606025910601040341c9400184030316114845003400a01010802400080c0445860300b102c50700421044c502d696913078481c3c5200038000d5408542110740043e40004110845004400800075242b41424a4540f03801140d10894000c02052045060340d0340e00c405240258060b51640c039000d40b0068449881c1d40004004110b922400c5c404200b0341c0300000340c284540d000c0c0d109003d0700030b4043c4d800e01100c1d1741032002d140c02150310309613004030b94078280307500c601001d100da0304007000e1500802046c10000d0004541c0c0380c030b80e003046008010100c4200c0c045400041141d00b103c0d800e280542800081c1401a03080c012020001480380d4000000c0c40881101d012000c55441460303400388a0307507180c007103004040701d42e4901590b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 839118776 1250 839117526 839117551
    0x1f090209190e03030f0112020a08030c06011401050309070302010e1201110a0e0a080304270504050a02040c050403080702090c0f0a020102041d0402090406110405120715080f040602030405010902040c03050618 91
    0x47c000900c148a04c10070b001d1010340b00048a40d00c4000303103400d640000c1020311165220600401190700000c2c2c444012140030b007006413a50030000441c948608480c00043d040c01031a04042c02d0680f900040c0404000b0380710000c121681442800015540c080300e1340500049030b0713802801242c540340080c2400c032071200c8019032610f490600841894400080c140d135600454001d414203108490042c140701d10321407009080565010301c104821502001486010400b080c40306100103105a400c0392405034044a8030070080c6e980d00e21001882c8a5140b811004810100d004174400d60150090f02c1595419061511015807072161540c0031081194041d61140c180d4003c500032a3f0340c0c0c1e1205451348040072505240c076480c0d00106603001c210b044544001d600c84c00b0100401c4e03003522102e0380d01c200c09141c0245542448010711034011000f03803000c3d00d800d900001050801c0401d61000410a07400b401c1440442c401807009402001c0c2103446900034440d05180f603441540091000f8071039003150008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 839120026 1250 839118776 839118779
    0x70603050a0b0913030f0e0604170304031b0305100c0c230f0703050105010e06030a0201080a0b1309060f09020a1e080318211f090209190e03030f01 65
    0x12009024003520a0404607924001c041d115203a8141e000c0c400d610443e640d5124803c01c0c603004040000011b148800c200c003c100c031060907a00c40301150708803001052a0241d40c2036201c6060309500c203e60006003000b1400024400d507003241040f200440340124264cd40300901c450129094440c00c04035207001807a0101d1290000c1d80e90441210307107210910610034a00342214655240000b5080ca040d12940b00744810400c10000b40903c0b4050314655121810900b042c501180c1d8824000b1802418840d054000581d500070f43e074000802100c008204a1b00e441600d0006002010607940036106a42403820104031038691380030b4010b4440e4050038088495240010612298501c0381182d0702042c4003640002c0e028504102505e602061400017411002444080102c24480d4040d220f418000c600b400240c100c1000c124129031000482c038104100704c0041010740101229400250f01400020922407c044007004030110003410074400c005580714241c82580e07a00048640c0111012700500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 839121276 1250 839120026 839120039
    0xa05070909050d050d020c0708061816030f1a0403051806120130110a060819051506070c060e04060e06040b030a0b0405060f100602030d0c050f0c01060f08060907 71
    0x8005c800c0f001c1900500f407a181a44850030b141071035200c8100c40e400601480072401550001040f10720740c070b0300103144c1c180b1295032140d506a4070b1320001d04140e1100303a125091148801c15900b40c0540094607000d940383c07070302e0702401350b0b0803010142c1e052441c100700080d02e0342010000c980341c01ea03141130488007581c81c3c00400643c03510000c8100495200044518401074407075000f100d1628030a01d00c13007c2a50842c02480480700b219400081002424030501003072148020403100c10a8103000086555607a0390141401c102d84940b105400100008291051009104500781501c90310360b108052042030b14100402d88940340581100d5507960004501039140581c00140620710143c03e4444603055505d804025000440d000e46180c0c01100c04c00a1159818039540c1e03005111418a4004605080300250b41f4001d03014080041c981c1c41d00b4848a85002d80280d03440140351080d0550ba070b6001541d02c0d8068041381c4103440f4a50143d006c0801c21000110f0b41c6482402250001d2075007610340302c2c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 839122526 1250 839121276 839121287
    0x8090c040e03091c02030105060603041505060102120f0d15150c1b0b0a080c1303060506030a02060a05040602100926253c051507020a05070909050d 65
    0xa07161115803204009444194443d0710401a403a070700324480d00c800c103140d80141403c0d9480107000c0351055004004110009880204c0e02d11680d001c95400540c035901e40340143c2c5070882c4000c4074224540c0219620003410041c5005100601c6000801d2002c41421815848042003034090014071071a002d200542d140c1c803c80c4201d10403130280791582003800303110211402a56113500141118400050b8030711180d41c0000d40759811007403420034123150665022500c01c101c0464040181a1a02c0e0004950650b8080000920300c1d40c00404a941e03c4d0801c2c1c202411540c0300740b085601500501100746820001440780d401007a40201d51910842c0c9500c1d1103c0d040394101d080c8d0701044806010950030350070f604241e00c000d595410006500303100f560400d10209001c00325200444081210509000180078082011402c1c1c04519401c501e140e618109042c48012445070384c0c13801c190001c20071780b01d0340020038491182c0a03c003621009a11054440140d41501d20003502c03a501a0305207038840d03841007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 839123776 1250 839122526 839122541
    0x5160c05030a320403031407030507060b0402120a0608010c08091c050d02070302010b210a0305030a0b06120723090120010c080f090c0f04020c0705030616080708090c04 74
    0x380f00035200d0300850828590000203a012980896000c80e00b0701c05c0540103001c02008541d154140e40c00e1500aa038010002e125030080288041d4440003001071940b01c035016201001c0c01c4c80c18605880c0761040d1850020480d03031051222640c2449150b86031a800385280c01e01035401d010181042a0209283c2680c500d80c1642072810000c2c20051080c080260f840540080c6100390f00201d81e040d800b03410008081040e00804114400e0240c618040f4000042c20300da115030306040058880d614449084001c003440320200350400000640d4103444407105405511440311510303120421194004403512010700034075001c0956404020001d0f507980150200d00c4c0300000c10002c5041c041c9050032031801d50392603070f640e5404588142c0130b10040b14142d40b0702c0c9500c43c21250060022581c004001178600c65070850326401a41c2c00141c2c0e0503084000c1c40141302500300542240c4450519400c607502031208002c110000981010111391218400d071021400b80d60140300400700c40b800030080000400c0310 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 839125026 1250 839123776 839123807
    0x3030f07030c02060c07080d1d01030c0917010609060902160b25030c030b010f090e13060501030308090c06070308160309061538160507030605160c05030a 68
    0x440c29142d00580e9900d0060041400d40c10140c40c0803403030801c280e0302d8800d203c40140c05000c41c022095500140d100347c031300c182003c00d19020a45811104003592605440d40024031820241c002c0b07001810415000b05040f624042010818541c0e903114810486c01520803030701c0e40d00164115070700805c1242030943e0304071620000303840b28140304001c0c00d40b060304044d800c43e0100e0b4031b45024150300c540521516100003400e003010081900b0140c40141080450301585120b0302c1d0010200d000da0880c56140380d40389a05c100108041e5849050140c924141160700c2001071180324444a880d092000035524030580c9612000c1060b00d9403d500c0741c6908804c01d500080680e550318040200700c0601414242c0700404149402c51070130108400080b420368107000d4100e400801e0070010020018041c02070300280071012588a101e0782903115a00011414058014480c0020200500c151075000c1402440c00c0308964480f2104460140c6403610030070780142454109002c0c04501d2401944640d542103030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 839126276 1250 839125026 839125037
    0x151f050702091b0307030f180309061d0a0303050405091f0e09030c101e1103070e03030d090b010509060306070c2d0f06110412030f1704030309021e03030f0703 70
    0x5410f18a0241d908101c90400000f5200c000c01c0c2415042881206160140031044c0d6000c1441501c0140180c0203500ca030200700803001c0c0750110b554034448114000010000d0882d030000f40c3e6810000e0a64101380031b020303c01c42d200030104505060204024900c041c0144527100760514040ca800440391006020081c940820000b4814100050046060504014000060704810503a144010068040c99000c03420700d0300002c007070320500807410390707500002d44d01c0c084000c6844032012034110b01a01c1030885099040030094410069560141c07030517100c0a903040c600719540c03030041603039500c4142d0341200401c2d07891084002007a414030003000d0006a041d00316659064020465121900c2d0800c1500c40031050340100080102500902c80d00300e1140b00000d04050074100488c640d1007100f00001e00780b003584140c0c01c05650003465010403003900c1d00d1850105180c2030074050003928003100101d100b140030951f1652126032281c00a80c00201c0a0002c6040000981c3d80e500721f540020742c190188023 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 839127526 1250 839126276 839126311
    0x20102062a0c160503030a140708250b0a1509090206090a060801180b06070201030f0b03120403140307170a09090c050703020d03050112030c05030f041e05041406060d0e0105151f05070209 82
    0xc00d0408136008800341d0300c80c161030b2f400c002c0c200305140b41c40141100820904001e0303081c60360f040b140b680b0b40590b100343c00000741803440ca03c0000d459100303140c0c4840d0848010400002c0c02c9401c10b800604881081d0f510312a000741c3d126982007240c1601c03042c10340c0800280a000e003d540310343c0c0705010b014203040d00010700f03408940c0000d04d0610643c004400c0c4000005080c0b04001003c8a6070441010b484000e40c2088029581c40607108002654901582c1002c00c99400581c0b1031590b2030001c160362481008040e00d81d0030010940c1e40408800c0c1d01510816000018641c800c2c41070b035040380c2901c048151048081d540440d50401994070664661005200050481441d08002e000802d160f0117010404010300075600e50b80622030b03200601c034a00c1e007600306010b000090030183d48054101c904540e900705021b4003000070700000d054100c0302c0d8a42400c00600075000880030540410458000c030b41c03a0301c0e620304090100c49003169840001d900380050f10060400c0079034103802511000b002415071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 839128776 1250 839127526 839127547
    0x9090b0409051b0a0f0b03061c06020a0c120804031b02010c0b070e2403180a051c0215060d020f010c12032304020102062a0c160503030a140708 63
    0x14002450940d50f0000303450340700519100010038000c00c080c2040140003403509107045054000105424040d01d000b40d4060704000710308140030003550740180c04548410080c9002001019002d40443d443d81c01070507109119400f0742c2040b071080e80d150790b440c2d17a640350b010703458003501030350000881c1440a48404440000c880b001d0092181d4a03a41d41c003101280070b401000125000f004803140601b000b5010070310303604c0151342240c0d408094009d4a110044c100c001c0c5034070305004018050010b0107841050b10081c46800141c0c00440b0aa0742142c114107035041455011080c195501c942c841900325240e030044c20403004400d858681410032102c8010313940c4070541d4186020004400003641c0e140b01090000c411010701d089040c04000c2078203a482c044e80003030b5443c0d0002d08030030096400180c1604402500c03040352a500410030b4403103510380c8000246070b6036615200c0741d01c84900c0007801c0003048038103000043d5104e540c039980d5024001e03c02c04496003084d500105080d20b8802c420802000344 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 839130026 1250 839128776 839128783
    0x60403031a1302190c1106030408040b0a0c02190e191409010501050411040e060f040204120302010504050f0109050304030b150a17011a0a030209060406030b090a03030e030a09090b040905 82
    0x600c558590b002d42c3e03444160102c084102c40b80c0c0f07058001e000e402d80404001c540c11000326040c030b50094074601d0362a10b481c1002c030441e0090380c0c44529403540003d11030004030392002d6000d41d400c2c82500d0a03102228031800250b030b0480c050081c40d1448074070f84001154160300c0030341c5240e81381001800207052419161020102e880486040040e691541c0041205080034030130342c604c0300e80802d40a810241050360818400304054116842402410040d0000d83c3d902d40c120303001081ca0891b0410b103440382d8074002e806014100c40660340c902480b0240d102513501030081c05c101c039500001845c0382500396034802c450200007030544061102410564449038440d68900005401500203002d400521100a0b6080d07540400c10300945400e07255940c000d540b600302c14002601d9040715100700c2d5640c5c070000b280c003c249540c8060322404040051010400c4045056000360303003ea03030300384488100d60b00069903134450800214001024018100240b410560048840c03000050002c100e8400d10f031a214907 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 839131276 1250 839130026 839130049
    0x1d0708060403090b03010e0f09120315090a09030504051e090106081602070f0501110c060a0c02030f03030f0406021b100c0908160623070b071d03060403031a 69
    0x5500c80c009000505810401c3c0b100100088891545150705180281d000d001c1c0181a0f00c81351540351000c2045c01100380440d11401044d01823841d140c1c5400c0f2203040350340001050040c0503000680214445c0c840c54003500110f1b9030143c45680c6454a850140409001800c0b04241c07076800c410380c010310035520010300724000c090030381d40d410803400d000304099601800480c008040d54003a580801440c0c2caa92240002c0b10740034209420303c540c8200115090020500d0f0055101c50000741920b20ba64001180e107240500903030445a0010700c000c0300503903900c81503822148110f158000580010001d03001421088082e4188040b0b00070090209841e101c02c1014100080743c4850503050300391f81c0954914014464000145207103100c41048944a2082d4010340d4100304481c022020103580725074070380d50121503900043d0350304e24a40c100f46800321030690b0110005480b0490000d9454280420303040100801009020a03450381e0350250002d01043c4004200c44002100d6104181d0f40d0154600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 839132526 1250 839131276 839131289
    0x60b09091e070f0e100e011101020d0e0703050d08040b06090604110705060603060a2703090b19140306011e2001020c070503070602071a1c0f110f0d1d07 67
    0x44a901003000f0340f2000c003400340c80e4001c0e02c5551404c0d10882d1b100d0306248841c0c00c01e09001c4c130680043d84510340640310360080000c003281418107015180c08002502d0b42180d00038000d54110191034031007150541007d442c05040c851154012515514220110700e0304401c0051001410000c4211891080e81080e1401d8689400200c10062a41011311480742c0c0030070f0110342000300c0b2340c00140510602c2c1158440b8007100304c0141c00c900c2010701030340446c00a01003070107000d91200802035002c7e2640b8883c81d80400040d141d0156081a05082c4055900440e41612820510b41c0c5e07055a640f034020340140740d24100642d85c12040c1442d00201d21051340c10b2070150015aa520b50090380e60f00d046074507801140240d01c8624108102903001c42c091060f0340c00380d5209a0032000c01102d00b4580d005020a5208000f40c00707610800e01d9900b07921082c1c0c5900c00038000d10000c1c03002905620203001e035100342d52033030a041000e10b0340c1a80541c230044010300c0110890b216440c0c10041d05151070308d660482c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 839133776 1250 839132526 839132537
    0xa060206040c080f1f0f060e1009063b070306030b0c0a0f0f0311040e0702150709090f0204091d060f040f14100903020d12060b09091e07 60
    0x9004000d401c41c2c024124900c000e04280215140c0b4543d100010180c12a000c00c0d4440d20039070b0b840403500310820f40d00c0100740034402d080d1260f00f00b10303522109440704655000c181c040060a002c29001e41c800325400503850142e1200088851a000031000c610844207030f403c00c1d48164044004000c06010702030a6400203104c500b9440c109188800203426194422400d01c101c1c05603683c4901c01d01a1154a843c0010308210846400d4018100c201d115202449003c1404501e00c009141c0807885140b4541c203d4100c0416040c58146240e03050340e0f02d000041c42060700303001c200b85542007000171204100b80145015039072302e21031088070f1420340301c0c2550440b0040600c0319200704021454000b000100b4014490420780e44111801c1c050030002803000c0510409881c0c0301c07400340310a058941c00c114092282c6041440c2c020f4071030040d0303038421000c00c020743c40b8801040d60611940054903080940103280100c14010083c4488008081d0783c03480640c0d803000c4c2507182414405030301403100c37038544 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 839135026 1250 839133776 839133781
    0x30621010209010f030608030d180b0103080d05070e2107051504030209010503070b04050d06020409020c0706020115080604060e120a0e04050a051306050a0b100c02030601240305070309020a060206 86
    0x40100c42034484d4841014180003040c01000400b004549080f01403510000e85209854030801443c24440c50252586400342c0000081c4a01d800081000409621040155982c3d04205907a0580c0005c0401c0d007203459200c08840c2c0c000e4113040f00440804142c200c5501030380da00c0018003440b6902e0b00c50003c413007000c03504004500f0848003040c0905001c8026080b071604100f503840088c000d070f100f0b01d4480d442c6041054240020b55044801601402d00103543d62001c00030030315a220018803810b8010743c0381c400005800f03440e034a04101036444600c0130303107040e0700c3e2501e03414040d0001c1d00403002240548280e0000350314041004200c1c945086d26404031000c0d2400810044070070080005403210304240411403010445124040f00680c00b00c00003a06490f43c0c5080001042c41e610703044c0c1c02003041200814240e80041691280f94800c0f01102d0081c0c0c0c80e24a07070608003c000b02170501c81413000c03c540c600680642c02490340b1a0103031030001010b0301950005001121280d00c41c0d00941c0040b4107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 839136276 1250 839135026 839135029
    0x71b03050c0a0320010b03060411040b0409061a0102010b0f2116210804231309020307140102030406111507030209030105180c011808061e070801060e06030621010209 73
    0x100080202054001c200248286c4080707601c6a0001344024201030b00740035000389a40d1198004550241e018008001021b81d0386003040084c14040340340e44101100c013404c200d4540c07050180c0c1000540c0030f48054403020100d010f011811050790001d0b9021121314070301c1c0d921404100700280c90001c4010a2414080c50007000c1079004182000c4404401d100c102003801092401088504681e811003242c2d04800721602c5c1040404400f030242c81d8040c8034402c0005186000b50810004180202d00f43c41e915555040f007a20700d103401d9440203000d0303002030008008150155281c030b00000034020607070f42d0000c030f01c0348440c2c01098115104000f0031b80c045640841780c02c0900c1007a40c402c084e100405e603100c46e5070b6200e40e66003108843c0c0e10704101c00c0c60803401407031170b5160141008201786d004540b62801e0070200400080149110000740c0060b0400080c0303807612482c0400d04072403a0303880320b4040419072010321070980e100928031754112118055264400078040d071032424008103000016128140c0b41c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 839137526 1250 839136276 839136317
    0xa02060f1c0c090e090114010303020f0c1e04050907120b1e040f080c070513060914010f03020405040f1b030302071d1609080f010207030e0603071b03050c0a03 70
    0x15801240e20b008082c01a254110a9207802d8945001031441030b641d41040d4a0702400e200c04847e09100a0742c80004201500040c41c40c03800f40554085d5221468400c050210703005003403e0a015100352004900c0e0079080562003182c010808106843d4515226012168403d03109441100d8640184c410807941c8003078507100c1e04252445200001d1a800d090315181011910018003a00301640042d8160f4140b008204120007000c0260050040002c84800b00700106810301c182d5041fa824007600e10402c245c4400703d541a20303c07074000444130504540a020003441c005200319894138072090791901084564010222443c00344046568860861070028105034441d03000540551603800401070301214a603802c0d601c8080450140c4590090243c12510202c643d400380d0098000c2c03110561002d0019001050024000c0c0c841c10a003818000031b01a5030700c0110780c09400a40101080e1440e4504000b42156690180ca005810204c021a55a040010900c0201c0100b81c600c80508000010b030f8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 839138776 1250 839137526 839137567
    0x90118030b0901110a05031501031b090f0b072f04111908070516020d02040e070e070c080406270b250c031b0905070305010612090809120a02060f 64
    0x113245082c2805900f201c09001c0b404040c1050101e01c4d44611500c24992081e0f115030301c0c0400d40b846e0b08032024448003003d0510342c014007544a00c18554080401c1890300502100c490590007000000005040b03d0a180c01400e071401000c41c0d43c14128862940c0e503500e002c1c0c03403000c25842c070485680d1130425508004c074403c2d0f194200107100b100340030428042e0304070040d83d01030502504855180c0c451031000a000c425030510096015141952a0344824400294001520500003071410a41c941010545d8003000210300148011800c10046c003d180c172410703a560145072555140501c0080c07a03038100c07400d08282d0b009801151008908014090726641c00e6030b070415201d942810f0803001c541c0300c3e030405131840d0001809504040302c0c06110020b500704440020030341c1e4281081176081c010002000f4040038483e10700003a00f0601310a50702c1c0114403c09400c0c5a00404a52038200c11000b4822003803842c41240b0f54900594468001580354440203003d52074200b115144c0d076180c8400f04612602030b8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 839140026 1250 839138776 839138801
    0x150603080c0105132a0305150412090f270906020a0210090503030c09120d090e1e070e18090705090c12060d080702030a0c0504050c090108010506090118030b0901 71
    0x510100e1000c510b036003851000c05000b800f80503010304100c2417400b840409961005207d40300c1c4044281c030101c550070619000341e200b002d40580490032500c0445004450f8010101858007641040084410750301d8103070104808080030020310450600d2a00807141d40b61800c2d40c2090700011084086581801080d884100d00302081040c0d10217030b19000e41c0c1c1d02005002e0803071610001802032895444400460200404c94220343d65184494001040e1903218401d464030940c90300b0200d131006503808210b0181e60010a241c90850740c800303800f1112261120715598114802000d120001a07400700f000d4072a102c00401010160f140100348100501c0003014040011410321000d07003003500181895030001c1049455020314016814000c0b828801c24100940c1845100d400c3c1040242504a4608a90b0111010800350380c540300c8000c1644204100240003540e1000184840d01d4040b000d010380c0d60041c9008816101c00b0b0208000041d900d4100382c8240c440c1c0d6041080943d400d010700490507d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 839141276 1250 839140026 839140051
    0x80c07150311040e070c02130c080618150621090d0c0201020d050f0f03011202010f020609070b03100b0a020f2404080306032814210304150603080c0105 67
    0x1a2401c2d400001e000d103000380206a405003010910b4644100d01c1d4481854000b0300407280e003620300e401140140002e6881d48003003810700340061002e00d0012540b181c0c100350203c0c01d0f0500c1e6030301d249080021003010801c0e0342c0220305105409101c1007411000e00b00b14000500e010f11400c0602d41c1900d4411140c1300c0c0001c200e0103040c03000043c0d070f0101e100c0002120071300749a61101005862220b031401041c00c41481c858001c0000612010007a00c050b40050003a00ca0184107044d00608a840b44402c492a24a44d80f103410300f0031192800c400155800041222a41c0e41240c1ba1b8038400c20725446622800c1c01640560440d8520100c00d00000d82008921b040c0c20070260404021000750581c011701c0138201050110000e2036640701403202c0365480d4495280810582c1d1002c05501c551154501c09030380c8c096031040f4400c60010001511200c19804481d0201281988103081c10540d0000f4011520700c1020301d001c01c0690441d00a0b007015521400c41c250b101c01030084000c0c00c4500003852843c2526 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 839142526 1250 839141276 839141291
    0x21060e090f070b0d0b03010f091e021e0f1906091d0a02031302030a0302031308030301030807081303060e060403260606130b030a05010f051f1b080c071503 68
    0x1002846904407489001c0444e1240c4c040c40101e00140400a03c83e50194281140c00c1885002036102c103072013610820f40801c00345c1c4400c0c0c5c0c084101744036820003500800c00b0384007030740d44501c3c01e100003030b8104006107201383c50450300d000300b46400e4112500c80001170307040c1010701043ea00003401c0c030701504c08540504801c81710884144960300d070292040c01419800004a505021624401d45c1065000f41c11201c103002c3d54a8000d5595020380c0150800b518100404203030f6030004421641203075000100281021826142c101144d48412029520701e0702c8180000001780e681d0141c003c6503801e00024010313a1030681005000701806004005048250926500402408c0158241c008900381c0741c1584800c5070594001c5174845d6500401c1d00c0600100800000381866040141aa544c0701c101c502042c1d6144180400c0408140c40c034001d6002c110084030308144140c249040c4180650301100e8803084a85a0348400c2d800f045100501d900804e03020320540c403440b44502d100402074a030410070b10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 839143776 1250 839142526 839142553
    0x204030f0303060503060c2b1407030f06030503090f1809060105030114041a10090e010b0406080706020604030305090a08030c0304020102070f26160b1c020a050904090321060e09 78
    0x1441009010194182e0780c0c40d90898078002c042240e41612301c40e540c00c01c51483d070304000a4005200f00c0790000000d042080036080d50050b4003c0390b08882d4450000c6003402036510410440885441d0080d410a42100c44411007080050001b401802c100015102950400083c5425608100042081811a1000e020004100200a103540c800441c608400d6454450080c0342c0e00303066910445032603041c807101c03a40c00722041d03105440b402401c6401b00402c5558aaa003a103c40982c8109805a0420303400180030070b010340c100c1c6030300c07505003416241d0481e42070340d03a8006a04150382219409c0404000c000c1156010031060001d0000610500441032400c1c110700c002c101c100b02044805905030386540d0351000c042160714a5184105180c0031200c0e22071124000a40042c0046158000e0707410a02c1000a15032080b00d001044079950140b40481080a100c0600403a107030440400001400e40c400c549848003096a12410b0b407000420250b10303140f0001c94060000c2c0074407000d900200e805c00d142 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 839145026 1250 839143776 839143801
    0x4050c0d020a120201030f020c15010807030c1a0f040303030f0b0301110a0516020d0f020a1403061803120c03090d08060f0d0516030c17210309100204030f030306050306 74
    0x440740002000c0c3d00318034141c80100d002d880c1c90030b029084036001046201c107100b4003082010001c4000400790045a070f94082043e605c81c40d5110240c504040311200703111036a202c400e0780354600185071126290a000700200740307081d4803a07841078002a9945c000b91b03180d80d91902541041400450092202004409010320f01e1700c0b071803050006002d00040c85940c000d607220f80d0807040c90380041c101000985c0f142051102038030300b400122310800b080a80403079000041c4011030002c403006130017010030b50f8070302544142112600c1d003400c0700d41c4420b01c48001d00152a141d0684252211071900c0c0d102e0034024051860009000700f04000c2c00020304c20845d142c2c07605140511245001c03a006040d89e0b1603810f00b0781c240010b81055a00d96050b5000100038004801c280d60100c506425880d05641d9503818805d40380c04480c000c0440c607010b084201640c0d940098040c1d034000c0004800c0d07641c5d4914000503181264015403084685421038120f42d014141c0601c0b5482c0103000c15800740000d4980300d1500d820 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 839146276 1250 839145026 839145029
    0x10c020a09050a0e0307051005130b010513090b09010f0609020909061c050f061e041a0403120606021b181b071a10050105130b0c101404050c0d020a 65
    0x1149a489002824401958100b01303400f202e50301c280d030303958042030a150340c46482080c8008482c0d4203000101e2624183d84425071b4a40350440c40103a0564203000421a401084e500c5032411f0f5a2244c03405000302c0c05034410303140104640c0d40006114000800c1e81c82c140c0301ca552100c2c40c030a10500c440701c01030701d0f58954980e02440031102112505c0018880c2c56100751003581c050454030802818045610b00090454041d54103c02540106121915411441030044400600000e202002d0007504031400301c4c9660058413a09013242600c0300b02c0f084204680032540030b2401a401001040900107101c0051044904159054503107848107004100a8900152811502c45911081090901c11040c1503401c400c0c0d01280c8401c0c1401c0442c0c260319510000c0d0340507062410010b0001806600400440303900d1440e000100c01610314180558070150080b000c920700d82c0c0218001507140060502c902d4005401035030031070125041a007401498000b61100250141c8041d14135000036079550f203180c40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 839147526 1250 839146276 839146289
    0x604060f1808121b07080601060e04090f060c0c060e0307030306080f061f091104031506030b07110a0c090203070f05071106031e041202101503032d05090f010c020a 72
    0x5540300c0b001005000d0440c3d950100102d240191300c5c4c0451400307800306036503049407115924407100700d080d03204100840d1009040102081507481008001a01c6500441204d52103810503102a40464032103c0948440d04080f0344541c1000405c10708050305403182c1d0000d000100020242c65144c801625604d910140103011f00340c0401d1a500201d841741a8440c01505174014188212040e0001040c0c440d041400101c0311a6514100407032020414030032001101d0b04101d1a042940382c01a003030302c1d0343c2d00002d4524074500610160202040e41180540b0051812410050380c03071409076802044240c06414800820504000c0200440e0180c08104c1c040754080f00c600c4e64a0b103400034400c6582083d90b104e20000e084100410040c031a983c10304003001001c039020750703000201d81e440200883d1072144448140d114280c1c02403010900c6102d0242151108403240f2108100c403503008102d035080680c0d44000194009190501818103503407002c0034040a00303000d9000070865000401113a035600541 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 839148776 1250 839147526 839147563
    0x620070c120c0906060503010906060f0c0b060a0905150103051f150923040b061e030c09030f07060306050105090d03080907090c0e0a051504120503090604060f1808 72
    0x407810b104a000c161401040c0c484401c0140c1652114060195042442125503480c0340c400c002600a00442d11002e140c0a0b594880c0c5042e02036545070038000102034210754012440340c40100c0c000703d282c80b40c14000e2401041c000c045014001c001015590700429000071410344246403a4002484a0002c05907441d01041204480c5106007c071580d140a42c01840c40ba1300c40b10700c06418041000300d41031035a03001d69051011900710001d10105205020400032800c09241c074190385601c2410103503402058040c046480d003007000780007a11708080344d90740d0038440d04206e20802120340c0510908000340805c0c200300e41026411000200b1000202a001e800c6c040d40c3c07130000303884010a1002c100034184900d0204952040710304000e00d2441d200c080d1034000c0141040124681c40c1180c0c0e60101c2074000000e6034502800c0241c01182e41d8800c01040350107201c03c0c40745580503a12113002d000034041c04c1d6181917081e010b01710300400c40c4038001c42e890304000c4016400e00104501203040ba00008080c1c000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 839150026 1250 839148776 839148809
    0xb1807030f05150708100b0903030717090613080d020105010608040803100e1f17070b0d020d051305010b10020717030415080609070e03031206060d090620070c 70
    0x9400d02032403d415000da41521001c116900340c0050129006a038029885048192a0305a100c2e00344501e0b00411340c558400d220010025403000d08401e07a120b450410181040104008110745820480ea28585915800001e0100a0040000e481d50854610080c030482d450080301901c0000060405050068004001240c503120340035044020b1000441c64081490144085103052010441080345c0c841361031000500c003c3d02043c165103030794a40b40503140c02c80c60406d070054643c3c000038515080035000e0086005020042c46418401c0b041130103942c80c06105843d10a086032a1502254421120300050722402c1d58000380b40030070341d040303070094891120381c400303180340f45010305d600407109405010200c4a00da0383c01044ae80c0030342d2003603d000103103440e441c00540b200c4032610607890700355109000c2c1d0717687e103165081501e030001c5003d055240790484a0001c0d800b078a0b42d840081c0c0d6803540300c2a0000a415016841c411000d02c040c4015080540030342d100403100b5001d109403255003016250 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 839151276 1250 839150026 839150033
    0xf0f020f09191a0f061b0708011e140115020a1401020a0207080d050f09061b0a11060906071106090907020106080d09180f020f1201030b1807030f 64
    0x8608540a0300a240500c1031415200001d0401c01c0d603a07032400200d09051101140800009000f20f40f44001824408140850014071000b50400b00a1079032920703100c04480c4008030244070f500094942031001140400450001d241c1c1c0003200c039060544645401c00000400c0c2080321100c0c15a090321024030381c610036201049250245480b00076005110344040c650b10140150b00410400c2c2c516000e8a03621a521005513440d940d210004c074000c240700f0003182c003150464000405030000010403c42c1001100346120043c8154070361300907000e1f0b10032900303081400380d41541011a1502151010302d00036141c40441d40034040d5000c010600c0d0955804015959220000c3d10415540900660114030744000000c0c0a42660f100f04490b46c0262040d8201c00d9200701d0040d0241c851126070b10540e40040110704004048100c80398205940c248040c1d20080003c0005240b440305824034410307030354110300b0311003c01c91001c0d100c10340c4000c0111907040c8840000c601d41044a03086003101c0c024051908 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 839152526 1250 839151276 839151289
    0x30b1f06020a1112030d05160804050d050706060e0702060f0603060606041703091f0f0503240d062306121203041e030c050c120705150f0a05070210020303040f0f02 72
    0x13603150a16010205020484083d1548894440c480100c10081700c4d809100301510110003e40700500181c102d8803403809814062001451030310706c54400011083e41d54000402c10250035605000140c004609010688240b02c402c40d8100c00200c1c064240d40c05d001c00003c000c0c0c07089204001502c8000e0141c40340c07000d001d0003529051000034051402e01c0b550011051202c2c9000d03595036000c2010544503840882c403d005a80c0706215014000b038030300003985035055600055204d115400066a07030840001109070040720140040c485101800c11100c0295901c1d00d100280300313074000c0307201d602048000080080c00d00a44240718051680d00d4507903041c440806a0300032f104546010302d804440d402c240d1701000010600e40a40142c9030f1042d540401c01000e01c4c0c582e0902c2d1b0160380400410300552408000e03002805440041c45803600c00245011401e58100c040c80c98086036000c5030328000e5041203d40d403003000da402d101451441c5029540c02108401e40e802c060030218007a051035003107403a0366 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 839153776 1250 839152526 839152549
    0x11100b031c03062303070603050f06040e030904090503030a0b0d0b0103032109030513140a05060c0a06060806041202070803030c09010905061218030901021c0315030b1f06020a11 78
    0x1c840c0c041070b2020509034801d0b5803603050004d41c002e100710b400c00035942c5d20030701c1681d024084c001c8240b00180c941108010251809540d901c119000030072103501c032030b9264402d00c500b19100e04007454132807811b00001000c403a0a80b070168040c04100b242640095080c9018034150b030b5050504807190303100124005200d0030007510b1401d0091601d1281c60500d07410001a003a80c5502c07680c0f462040341c070703464071080f5000e0300c4130752a405c510b141000744400e02c1c1c420040e054100c1c404080b1803801040741c94070001e640f229440001c00b6003080046c0410310044002d0f030b100e00026400100300c0702d49400e51071503a80c80001d0420020100105099032507a208410400003440010560fa0700d88600000e014001981a81d0107070450010f9211000d1014020080c0c80400350f0507005015054018090903a80c00000311416042540d44c07140d8a030300040c07e03840c400146016000c103102c10700d020300100c9121859989100d2030b02c4081c0c50308000c611303800100780b44d140c0e40c080f41449400b035544020600c2080758 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 839155026 1250 839153776 839153789
    0x3070e03101a01050a050a111009062016030c02010c020604080309130b0a030807081e0a020d0306030b01120f150c1205010608010e0903040b0a11100b031c0306 70
    0x10007a07248101c454641024031400211090311420200007001940d0300e104c2c9000b1800031a17414045800d036240a02039107a070144010042e42c075032005281d906c008442011f40111000340e641c50a061310014100341240301c1500c07201d241443d140c802c0c2c00c00418002806002010403001c5403031b0004591103a0305803110b82d9809002a5250340d240d880c03654030790304010303200d03070003260130444841c85016503024000d94610013401c41950303542162256003059004440c19600c072a0200f150a0109552950036100102d40360016500d448071000001e040c4281507400ea8101030800130309001243c8040c00080c111020840700c0c00307a030b42da14035000c0c5000c000410064103d00d0381100c500035510543d040201f405c111642c400d203038201d10f0328a4108540b0203015400000b0f800743c0050010304282904030350401c121004030307404c0030f9546056980661201c0084000904c00e0561041d00040c2004084801180307070b4001d01085483c000070030340d200d510840040114a004075582e040c24069440040544074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 839156276 1250 839155026 839155033
    0x211a0403120504120305150931050d090b0711010e040905010606180605040b18010c050102130303030b060306100513091d0618030319020c061302041118040203070e03 73
    0x900c4e040061803010066151404641088001036848000349641107200800500210391a11950b01040365420510f581050240c0040341107440040e0301c07000d01c110980710b103000f480d00040030b000040511400358812008820240701d03450009803100c901d038105035428a050001d007054030001401034103a92178042c20139480c10708082640e071f80c030643c045a904003065061004a036522400c807180d01c40c2d4840c085003948180721000180c05030400301421400e051419424020303a80c0c541508991100d00300c40220325150600b0001c154050040030300504088412a0031490002d02151500880b101d0312000c1000001d114181c0c030b000544c601c005010485002c102d000c042d1100400481c3c1150742c100010b104120001e00c40d1052010540010403e00d009103055440700c54241c0d140301c9071012150700c2140c0a00546030110010801588503003107035011038940040b540140400c03100152111200718000708400c503060740c0041a111720b0cd681c107541c01603581d80c41490031260300c051200c02544c0b41c00b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 839157526 1250 839156276 839156281
    0x160509042904050c210c0f03150a0609030201441902091809010921090e1b130504060b031504050118051005040213211a04031205 57
    0x10310785800840e6600707640c10842600c910148080900410b583d02c4955084203903045014100c8001c3c00d50407503101d141aa0500d502250034030142e030000c4410f00300d0707900c00300190410740c90310041c120b0042040d424401561402c54000034102c515440a013a0503064a40f0444000f441c00c0c2e6201048681021907680144160707405001100d1050750100c855182e00c0c20450320041281c403c403110103000a24144240407a44841c1003c201c3c0101602019562500010081040c2c40101a445007901590340e10100107588060054030003600800d40800c513000070004213640b0410190340700c801d00b01800c2d0710f80c0100c084490100307003990031403500141401e20000b680d00328003010314052503000401000c449450f60074031089035024030881c500841090003424140c04560300494010b10041e00d08004035440e0b00100d01640c0c02906e030203449100a6000300322a04925200c2e8100082c8600d810f969244c42c0e031100350020700310280802d82c80152201003010140a09a10030011280740c101f4400351 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 839158776 1250 839157526 839157581
    0x20a0c06020c0108060418120e100c0311061614130603090c15090603091a0705091302120a020f160c090509030c06160c020307121101020616050904 65
    0x60000d00e145a0200320407501164076840c1c280030701c0d10f000d003940309040b01e40c01f01038480201d0840003d0224040c80000c3e01040d038143c50b01401c04145403641d031103500d14810071340b80c000c142c56201860701145070416010700440040c15800c4034034036600e92a2442a4005107401c2c0c12492155501e1008400c01421002400d950541c00500040d40950420b40c00a40d030703540b42c0c03200e0065884d0f204e4001105c84a085c800c00707000e5800700700014020362502e100500318054000c40074101ba6020004101701103148585460174001d03000d005a205241542030100300648800444000b8100f5420707250003161540c481440501628180c8451080e100c411003402c1c10210003038072242c06070007801401e20001900034040001111b07404a042d000910065171110074421041c0d641401c03c5042109400c420400359030f0820010001d06416845605080b815240512403540041e03a1607065410040400860300c0d258124800c03c000c09080c80f991344d000303070000140100b00f00e81940c011302e600400b4a0060 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 839160026 1250 839158776 839158783
    0x11205060a0b07260c07050d0809090f1b12040b041a010b0403031404081905010608100524010203070f030e12010e0f01021c0b06040302030118050105070f1e020a0c0602 74
    0x1905200030f40c584100300050544440d901c10f070105c4022540c001407041041d0308044200c80c2a1038020741c007060070544044002115504140c1da0480f81211850511a40003001514400c81c180c031540710524180c08280c988070103513002000942154100c200041c2070101140c18804072111420141129685410710440f0682050000707500007100d01d1404503c41c0312120444082c1c44409004055081c41c1101c061005119917100b2070301c55403103220002d0b00210410409107180c207082404642032a04030b150500350414002c20327101c600000a0494100e98010084a164a0700913208800c0711085003825100e00c05841c5a168004400d001d4100720381e10190311090041710501c05a40c0c41c16180800d09090b8000c03580030b000c42070790f0300b039048109101e25480002414800b03040309060076035940000c1d0031124460044203903442c8060b80201002403c0c491540d000e00c440c14a5a0b0f80b060340c540040519003a0b00341a24000002c061050071640200450300c10f69078080b4101025a480e10340080d01d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 839161276 1250 839160026 839160053
    0xa062a050309030c0724180b0913020c15090304030b07050a02070317040e0708010f061d0a030c260a030815030a29010b1603170f190b011205060a0b07 66
    0x1010349450b41301b02e1b4802c1c4540031485e003c034650a14a50082c4c104584040707680d1205840d00e50041c10f0f00c0350700c2105104ca00160454280c002e01410051820b494030484c044801010450b4a800030401480010f2105a010f90020b0192070850786130842000203034980001e903007000d051001007003c04880410014000e00a942c0c08000b221860b0311203a200346c503808020701030240c24548000041c00018443c4282040c449840e90200e0f848045620100b21000311680041d2001c1007001d40070320018881240b240d0307440c1e4544590200c0c6d4120929810344a042c0c155004007000301103008241c0701842194504014040201a0741d80c0d03030700c0c600e851901042c0301c41c8003034200c00c01c103c01c060b910302c3c0313400141d81252040c00340585000c00009900d502418102421070921660304107480e03c0d407182641a0340310b0300c20b0307640840e060b0500c0e41c0a20b01e42911007844500240c20484e41e056666440350070008000d41c0c000b008541526a440015003410160b0844400c0c01000700341e62003800071440c02c808 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 839162526 1250 839161276 839161319
    0x30f1407150f180b0c030f03161b030905130e01050f160f0e091b04150201270212100f0f0e0a020607030f0309060e0a062a050309030c07 60
    0x40502a900e0300c10341d50b80040100c00202a28510710070401a18130800401034000c0c00800e49180203070000000f249170b0819542420380c0f003603c601c58603c954000190840ea40105c11302240000040d0b82c0050a00c54076002d100e0003114903025008c7c1030400c6422080014000000070b0100b840d081d407616118800071540760304844050440020100e021f0709042c400c060f0280d40b11807a42d6003000900c20311070342c0070b8210041e09071035000e2007445020210141000e402100700d04801c50145210090940d50884620005c25144c0c0701d0103180c45802141412002d6070648030071703204a8500e8070302030030030f503042000d03d02e190300303140d4540358918250340007070801d07020480b0070401e0441c4044010365807080041d000707410000401140300481d001f09601c240301e1000d0714002c070b21003210b0340d2410155021441c111900360720004006040203a940100b800c1102007582e15035a104501005050013003032181a40c05100c400004205c41c01d4060007282c003100c22030000c80d50919075640903c0e011255000021 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 839163776 1250 839162526 839162537
    0x105430509011d0328020306040302031c1401120516060c052103070c17040f0303110105060105091e04060b120a0209180c0c0a14010e0a0804030f140715 67
    0x602101d40c0f4103503c4001c40b440030300103002d0400b160110300c45240300b102d02d00d0181c00c01500103800503070b010802c8600c113511a50140da00d80ba8103050b80004c140381146411070690400303000380110140700135040c0c1140d14850341c0270003440300350a0950528040c000b100d01c4404e17a9100210b04190095070503000a4030450440712410211001c1f282c1842d841c10010420034420070200300c13158480d81c0010541070040d01c4d040d10742e029500c4060100d43c8103038410481c002d1420320810074160000050034080700700000a002c64500703280024094070900ea1800c4c8607412000c080e28686284080c1c1503002c00020304104046074840855060a410200d1100500308840300000c2103200c2038000c1d02c0d4204006000085404500403801003d083d0090080c20f41c2507085c010385121150030000c01d98042d003c3c40c41001003003603560b030260a40d8508200a0f02a5200b0b415440c009056401110200c03508024880c681c00380c149401d049031031034040794401500c24070901180c03140000c0c814040401e210340b0f44 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 839165026 1250 839163776 839163797
    0x715020c011106010504020f0415120c0e030c012303010b09030c01051608090117040f0201091e0e09011d0c0f0906031b03031611030f010543050901 65
    0x11181451120b8030002c1941001004000c142090b8000d4610304030501402c07030030207840d80912600641c029000c0f00024a0640d5120009002072081c02004807051420b10281e840f40c3d40401e5403410b10040c160304001c20009412076001d40140545107080d8840c0032940e907541d40b8402650a9084082c0f010720900450ba1441d58640c060822a0403d10103032400c094217038650b489450441e00110b0039681440030039980c0da00c50221403556188a648510345030b81440b0303840d0000420280d56034110194941485040d81541c2031606034800496403d41c06c10422682d411071014050105c0e0300f04801c0407c90359190009010010843c40708812041c3c42d43c990494065040081e0b0300302c10b4950640542020100e142e4203404040140b050075405801c0701d14100445807840d004245000c07054a141c80030408050b00e52030b060004580042070503000f40002c2c10b24044450310510740606480d803014441070001e01c01c40c0b000c0c6c103020318003600541d07910b1004829000502990b110304011800100c40542c1d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 839166276 1250 839165026 839165029
    0x9030706030b090a0c0c0b0a1a0603130f06270506060603060d03300f0e0f0c1909060b090306070c031b0212030301080a02091518180715020c 62
    0xc2e8045404014000d803c20340b0360352444801042c4003180001003001c1c240c4014081600014128010520b82d20000384141404035011901c542c0140c9143c881c250400034802c8112071841c14801c8030781c0040c150981c3c1150303031405c140100f403101c8006c000d00c10342d06015003040c0105903a07029028000c405076025503990100308007281c17100f12111a4403801240c0c1000c04244500003c814140e0301b4050301c0402e100da20020b80805807070a40c8254640c1e140c19400102e0413a0f03004607008100d041000381050f04142d88483e44070891011094000c034080c0822100403800303e02c92100a15102c201000040d4680b00d00500c1c2d6030000d41034034002d10640010400c0e4500c640305640386a0381540d03540e101c00c040250139110301c05c0d00c07400607a8400408108039220001c240001d50091440e42c004041514491050140c000300003806811504e41030681981c070b07034642c0454000e00c1d1090700a54038295403070341085034070030306011207604092003840c40101e400e65500681c05030040441d0200c40001e201e900 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 839167526 1250 839166276 839166281
    0x1b07030c0902091f050301121506080d03060603020304082b0e070303090e062209051603020a0b12130201110a05160503070b0d0b0d05030c01051b070308040b09071203050903070603 79
    0x144e0f560005681000100207440c2d2064032504864072400c2c4411101511400c07070700c180e5902c2c1d00911919003160110901c0e081d014802c2c10010700d0b46040542c114034054403620007a00070030031400d121804503440c0d030700c0080101c0f03124408103181d4030041200c203e0402442e03580315521300044001c545150f4012074a0791f00440f155103c0c0900a00344101400c4010000c0310350480c40c0c00012081d17845148a07400150240480b006104082160780d01862450040203000412640120888081080141a44c0f148003150580c00340122480c80c1d047c21662004851220174550030196500402c0c0e0000104074000c5104101d803a03103968840c0351103841750300301511085e07075100340d0720b02c072408000e0039121203541e80014154400c000c0201c100c011458a82074150341c000a01802585d5455080109045600c0c8075503403c20480d014190800f007060750060200c4d1405000508014030f2040000d0120000b040902c001c0c0040c03001510806083c0c0c035001d8125008210010721038002c1e41008100f044c400e1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 839168776 1250 839167526 839167579
    0x60b070f021002070b0a0305100b03100603090c030b2d0c040302040e10060b0c2103010918060f021b0a0f0b0a0e01020412060b01080601051b07030c090209 68
    0x404140d58054460782003002040308a0b00800c15400380440004459507054042c041d07840c16a2000b0075986401d1240501058654000e401c04841c103000b44140d0750030f90458201614584d080c0003503030090908080880320695880201420000e000300141d944480801001c503080100e0707402c10780c21a848407103545c024100e6903100c0ca081c0a000410141c901030308204440f1a142041d6002c03d5640e04030b5030103131146900008084507000640100311a410401842034050003081450b60342100c014510882c8410f20032000b4550300c413001001c00c07031101403d01c0f070442d5208000b007103081c4184c50301c80d010303410800c00d04c06c90002001503007030070701c2c0f010421101c4103610031582000b910056031010b031048030107000720411507580c04603901c0300ca2003440104080d0801804080300c52140349003480541d511060424104844032080c0607490341c000c82a60382a8281d0100b00741011407141d001c40c07401107264000b034103000e43c644002420201c264001d002c40740c0140c81c2d815604410070b15203480c40458 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 839170026 1250 839168776 839168783
    0x6050d05091b1e130e0d18090c11100c031d0a0605040f08130e070c05120a050c010f02120c0f0703200d0e091602120702040b090712060b07 61
    0x111880022610f006a40e034110110b102100c01e420650310310200f01c0e16140b6524900506030344500160310314104000038804240c42c2d19141d410300000c0e4071085611840c0e0701c01c0c0c1118585a40711729443ca03008220150303c071503220045402c032814212929000d05800104400030904d041203c0b4207000201c10842600f0020030010300b01402165901401010001c0041e034500444050180006145c4030051141c0701480f4030703a5502e2410701c1241d40d40740202030001420301901c0c1000c900044c170041805404603010400301602d5040c403000c1542d4521030340e0540d1600d0351a04a9401c0d0120559024000d1203ca448000300b0381d940f1417200000700e200b460240c07801e400c41403090200003031180b034170002101d8a41c40c44843c41c825060700c80d4a001d405d0141440401d0702100110210f040c9190b0041e803010f5600c00491300d9543c0c42d0390182d1103842e840743c80c81100000150950940d00e603030704030207040c4901a01c485100d140560009140c4200b20040c03a00c0d607828031100099444040c0700f80c4d02d01941 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 839171276 1250 839170026 839170063
    0xc1a04050d0206070b0c03190c0e0d0201140c03030a050601030b060414060909010312021002040621021b0303160f050a050d060314010c171515120106050d0509 70
    0x501007000041901110101da000303004102c4a0700145000d01214052116811565100c2c2407803000302e41d4003c0004610110f040c82d0102c0300e100c06034085c81003907c02c41e007a0b40405c01d030190f50004981e03060303040902942e015400590f280d80b40c10300000540c130582c0605003c000903117440c001102035800c1d128a20b82c0c4548148024041b01114505003000200001c0415180200203030100d01c100b00240c0c003d44250703080004201d07803141c040c00101700302c00304124110700d45800c1c00d0b0045c054440500480303000c0302003800c03d10094071440d41150502d25098242044084c0f1404500d942c0307900441d042c201106000c1c0000c04100d0190020795000415612243e05285080400300da15800c210752003d8540d48500001011949003121201000620f0f00089200390084001074a402c01a503009082c2c00a560108034100f00740c07085508000400b2a01d100791045840401080790003910001908a032481c000002c44541080040409520340007003404503640c1e078200c268890300d50400078040c401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 839172526 1250 839171276 839171279
    0xc050d0e06270f0d08010918021e0102030d14100e010b031513060f05010e0a0e0403390b07030e06150307080111090a050319020409061404050601030c1a04 68
    0x70640b4818180c00d40e0042c00c5482c90341c1c00e5000b0341d04d414100782d074240200c1c441c04014441c10340e4500078962482801e114440c00d000003139020408a100080b400901d0741d481440c200f8082c2c0c4244110341c080c18204000b800110b801680718041c0b05001c1c0c81d1071003108049000002c8100d9202c17281412a14900f00740c6040d80e5038100c2c81103600c050584847c2d03014844112482140290384101c0000d80320701611441d105080000240c00f80d41e20614091140c5440482045500703000010140e02c01e0740f601c1c1c00d5802c0c3c07041c0340500d41e4100c00d001403091014a00049002908251621010310030b003d0b45007134006480382901a4101c0307080c072100c0701090b00084001142d990750085950502e0704c000e011206042c0e50f0b200d240382180d0814403030040072200040c95004038500000810040c0900303c01411210300c0e942000010141c1400000340030b2910b1f05900c9041c03050380c0d40243c3d9042c0328504000d08174642481c145031201424041105c1c00315185802048102c0a048036000c0b0902d1200c0c082d01d0103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 839173776 1250 839172526 839172571
    0xa1107060506010306050d08190507020402031906090e03070f0602090616050c06030f180f0d0306030606050118090b04090b070c0b150604051e04020403031709030a05070b060f03010c050d0e06 84
    0x200480188811311004100308bc7c0180c0300c6200030b40c03142c007281d013001d500f21040550321000c0c1d6507203920070701c00305045c4000e40092043c00710840d45201d40c400d10a980090719441e00c00060b00810402c80c1e0300010110300f80c00c140c4a4810f66000300c61103003007600c0c004a00704007041b4560100b6941c0e22003108044d40014000c1d28043d10080c4184818000c40b04003135020060180b13440b030750700e034280002030f03d0301c40c10810041c4502501c00644001d080c40052448024040592000c0038403c880c0c1c1203071250b111b0b51203511141e1010703c030650410399072081031903c400054000846a03034100c4254500c0e20001d600801902000c0054103030040c09280303440e20f0001048182240301c0041000601c9403014101c032940c4900c01800118400d40750f81d20f484e00401c0b404540440700030300850300e5030030403c02000010740c0641102e82095100e5100f400646600c1d01045502100105441c0c0544c64a4900081141c00001401d82c1c3c0034045c4060181a0701d1030a03050b15100159100c0800c101c4c0d041d90003544 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 839175026 1250 839173776 839173807
    0xf170a051306060f0f050a081903090306092f01140d0605031504020108090712060f0b21190809090702120f07030806010e0d08030a1107060506010306050d08 69
    0x1a44855011514030300c141c5070034040310810f40c4551110121304004002c0d815501c14000b00400b030485140c03010342d14141489803641420044448909110342c1500300b010b01441d100c03000786800160030011444e0628005402d00742015400412100031007407940b0040702c0c1c0e008c100d065201a503070500c0070101c41e4a06039064102d82200c070489511740c100401c0a0302c04000b00d1004040403c0d20409604081c0000741c02c214000d051052180c01c400e03400d0042d02c504c002c0d89041e00b84e002d0000200c620704440048014807280340e1280d44002c2091050300e00600d031020350503251804100b03407030800c2103103140c41051200b0488001d14468081c446085035152010725540e0084003401540d4400e1307180008242d25512031040504402008036540050652000d592640044203081114220040c00001420b040c0110300060a1120000001d400014183c000412001c12450a213071108201c0c038001c13015000469203540024a01303080003446183c21900d81207042d420400c11441e18000b040075000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 839176276 1250 839175026 839175031
    0x90203100f060b1306080915010b161a10050d0f0f050118151404320a0f0605100f030809030705090f070e010f02030421050114070f170a05 61
    0x1c059910788001421000c90340080400911441a000304070b42000c0380542444005010b8400d940e010161140700d450709100c3c0365054850803442140c40e50b40388036104010340000400280107a9078440007020303207201c001034940140b0081340d044030341c1da450304140114090710600140070840095a5500480c6000c20010801e60041001280c00701c0501404040c0c610032440440301b4806050300d861000b19580309104105240c80488082402c150f160000040340140d8238004007610380c1070140c0c020010364034280300d0b14a00d105403100c004082c1400500c00b9401c0c1025031303100c1d00b0000040e40c01c441c0d510400040c1d40304020350f40145401d5840308031054104050b1950544a40d03400800d1955030001541c0c420300c2c0c2c05032030b100149480c003802801c1403594035099044c1b10015140e010969004429079041d1550000895504884450541c0c40f140700b030b400c003a107154070308018044000c170840d0f44188a0441c0362101e005002c1c1c5170b04215204800300384800c0f650100040811041401a040145c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 839177526 1250 839176276 839176301
    0x72709060b06040b07030305062e09260f0601050a210506040b04151b0f0e060403030309051e0307140a02090f06010306090e0d0e030f0607031e09020310 67
    0x81c0008215020440700e03401600b04001d2890013082400c105549030150f107511078400d980c005440541100c400101a040c011841076a4420f5507400c550319201d4421100141005d04003000300800004000034009007405c04d00b8160300039000f07400b0041c400012128102d800280088003c9458250b0f0300302e08401d940d50785420119100b08000100e14104025070040f4000c0c15818410304191a0102e442510000030400050400c400005400c030380300c02840480c00541055608404840d00449800d2895448681c2c05040481d000c0141a072661215844620500407220b070b051000300700f0510700301c8244504a06900420031480040d840951800d145503000c1c0c1180d003480001d50000344110001c030f0320b0149000324001004400d42c0d041c003848004000450003000b4210b0008040b60319120300301044014002e1006561041783c904120040b14074490400b59511350921800080c09031404c20305468550700516440405a80540706448020354003c0051105c0c1424101c940003520f1507111300c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 839178776 1250 839177526 839177531
    0x200901050c0105070e1017040201080c0408030c0609070509010e040f1128060c020105180f0d112419030204170304050301180507171606020c0307270906 67
    0x114030101d00340101402810140c03964004020584203100c4c0503100160f4000030800308190b01c0709105403100442e40c10540a20302240913980c0c3d2100301c90b513071155a01034000c41c4800581e6030155040440c40320f014500c1601599003032035a071801c01400b4034007070044400c980965004680080d132811004422503208810341488000d4003c009980740001005207203800084ca40b150500301b0800e400a00540b000c0d04040300300c80101d0300028481c3c002c0407a2421180c2c81e0a013000c0c20b0307595002c095162280300600441051110349840c0017885100c078031003801a144000720515150141500c244080c5016a40d541002c0180c11000c41c0700c0f0071410b1a40505a080101103180030740320710003200781070285000755516450030042c18211501c800c0c072250180e0744092610002200071883c0760446074081451a030608442c64901d0612440b5203a80804594416000800503004034600f814002d0841c02da401e0b0a54804007018040341140d00012209050715540e002044290f0151100d240541e000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 839180026 1250 839178776 839178787
    0x1080a050709030f0809030111180411090603190507020613030305070c0b0109020414060f0f0c0c041802030f16151205091c090302010f0e28090f20090105 68
    0x4406000200d0769003034421100005042c1c001f03040901a0030082c0920851580c44d1551404620f006800a00c05052240d61a05042a00c0710202815603045141c020b0015503242402d007000380340c1d04061000000042d003001c00040285001103400380c480d45450300801c0b0a10b4031030f60120000c1c0402800141404640e100b88004920320410710f9001e40061a00103a0fa1406c1540f40000c145084a03d548102410000460502898801e4440840c1d403020702d1901d408501c0074003400c00c442c2101c00342cac1040c546600301d00603525546007040f495000b50141c03081c0c00150802240c03a01c1304801d0041c15021001010004054001840c40b003082c0c5a2502d07402030800d1861003000c3d504169240e100c02c1c0e22450f005194441d561410441190113401e059401b41d245d83c1c00680704907040e1000c50284100c2c9400780c0655101d410480b0a0018401100320184250140d0004603103d18003030340c3c01507443d2030701d21a2603103010320664030202ea00124403120308030102c0e80f0129079401101075074100a4203001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 839181276 1250 839180026 839180033
    0x10905010507120b0d02060901260a060501032403140a140d090503150a050601030e1e011a0306010905091216110907050a0804030203190905090a090201080a05070903 73
    0x18035000d210143d55044903000b060f01c4030300c10340307035000081c9124000c1900180c005a44800c101c3e03840b120f007802c0c504010180c541d00400080d90003000c40c1010100c01e01042110625031b4070a0003510000d0f03c00b0030010b856988260080641e065103901e000b841c10030248081099455102c4041d4500c1d0225130030031041da943c2d200c10024584000c09160300400814492039080300000000e000290010482040d01da522407901610242444000c00d9480c400700707440f0303407082d00062031400c4c0200845103a00700e07419070142881200718010b417540d403921424908030342c0c960141039030f0f20320020300600c4140d0a10000f81c00518024103824154842c100e090156004071801074041e240300c40d0404c1d0311070111418a505803d4190049911800400301003001058106043d01d207100468500440c4582c1c0d5841d00303034914800c1740080a85000440300a84006038008124000e0f5a02911913a20b40d85035032150390195222000b0090229112800080f840e0f4803a50080f80d01c10b100d894200c0d0301c90f5032500e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 839182526 1250 839181276 839181281
    0x211803070f0b040e010911030a0e010939080c1201021210030b0109020316030c0207050604080304050312130509130c14030c090106140723010c020f060f011701090501 73
    0x18400600b0141c041410007490000380011801840c0ea500b0034001c0c002c80c1d5060117500d110040c000e10581d0b5440100708400e2400350b000c0c2080c69030291704141c0048101c000310304a1021441107141e00507404000520000c02c0103841c400302c0b0540300c014203002450701c081200c0d9004545048803190b60900c4a02026020301c21300d180030b41c1803018046280360660030681501003050700b000142e2401001803080ca03010344107000e0fa18540b140360000c0d1000c06040c040307080c12920f80c8100d5014102140c08038510304080001d00c12504220115440c1080c02c078000803840c0100182c0c00d52816011b00100100e090050680da070101c06030f901d440b00420350303980b200c00303d015541008400d129100d906080314241041aa80d811310111030321900742d1300d00880149000080ca0340e51b0034001003c90310004110030007a208401c030b6214451541d1044415104030700030191a0543da0051040002c0f051284101050160080b41314040c0f480180c1e00344414012059545840341c1810343da103240c034a010560a2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 839183776 1250 839182526 839182529
    0x515040f0320040c200c0337020105040306020304050307020d0606061b08040311060d090b07140c0606040b1c0f0308010b03070e0103090201200109142b050403050d0e03211803070f 79
    0x4000b02d40c00221508e4460825009004109075102d0072519090150782c000d01698100d9a0140016075a541e0320f191150443c010040000e4000d664030503204100891743e04042e081d02e0403940e031400b1103115500c000005020010005d08503a070200014008500c0f100110607a04401404052a0081003201d041c103c1c4c244c201305031046000079041c400415440b030072041c5090110055182808101000d61b074548001414040c03007983e8811806c621502c9540380d0090907034103114521090030703003410700d0002e052460b4012400644100700100e503003d01d50b0140c0340204041d5841d0040c4c9164840154024110088140d040c80071076080c241900900f02c0d0022038001c0c270700002040190491030a03415511101c100c0c502d035600020b40307d540b82d402085442400440202c010a0f00c07495030201a5694400c941014000d401020440000241c000704d829031102015000c8444010302c1c110399400e650f1481000c40c5001b0001c100b1050055001c400704918001d00509644405540d40542c08004519 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 839185026 1250 839183776 839183803
    0xc0b060f0918010b04020c1c1214090708120316120908092e050d060b0c060f0a0b1c0510051f0905010f0515040f0320040c200c03 57
    0x82c4880c42d04a0a00703008540101005a50950500004a8a80e5103400a51050900c820403801544ea15284190f540707100c04141c5980030080060065201840140100c9907600140704400c000104007070002102070503440e2110406046840b034904000c16203000c1c040340380030048440720b0034603c00c28a1107100c8455104a10700b0782d6400c105414440006d900c3d08480c544081020102d0607540141460350007038031460700d05156034110180b80c007401440e550308010091000810b010540807000184240900240175018502c0d9480440c1d031801c1d10300309c1c048a90030140140304828440d00c0031340745047c100c4c810300a50303420380444095442200d4086540410f0000d03102288003140c026444007a01820041d0014002d560510034102c1c9581c000340320710383c00340301100c018004840c3c66030191000b401c100c040b8480a84d0b0307242403101d0f94020014200fa52180405008145450701e44034518851242d5254480303103114100c00b8201d010306540b40c004540c000da02507501c0300e541c14000540d00100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 839186276 1250 839185026 839185051
    0x1061a361507061406010f1b08070b040b010b04030213020d33050103090b060603100b030109020405091501080711100e070f0b0c19020406080d03050f0a06060c0b060f09 74
    0x100b40c20190107556a41900ca1144d000400c24070800d030360f00c000030440900302c904200001c281340070003800158121348005410a000443c65004002203186900d0140703019158010381e603622510503032158441c44c440298001d4a903246060341034200d401030207108a030781000084040880d03200c00b95890914406804009001109040700d016038906000508401e28041154003c01d5a5a4068240203404503103d42030110001e045507003481c02c40000b0300404685240c89507074803d8940c010750030a0040500c0344a02d0070000c1e01013240e900100b40040d0059403040c0841d1034070101038031802071855800c103041c00351114800e40401c440c041d40e01c22982100040030140c1c5460a84040401d03203811545100100f00410010315800013045251044081141c96040c001351001900070b2125901c2802140502201001025003640c0410721071880c90300c218246940e4000c0680c00c03142103028920124804d80081c0c0003181c0702010340c41c2e0000015041141c010103c0001403041d01c02191100c1150380c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 839187526 1250 839186276 839186287
    0x309050d0c080106082a191502100209010c0f110316030203060a09050d0e0112050a05070e1f030b060d09150e010504030f0f021e01061a3615 62
    0x16824443d14004020745c07000303400786c2c10500b80d51000c2d8003e04044c0d05c0101601c980c038070025507100040b10782c02e0386403004101c065545e54046042146041701c410000740c043c19040310704c606118001c8070304841050b03542c15030305d9140d6a00c4400e10a5000010389001445503a4144030f914104100160410390086a80145c1d2440c41054580354004002259181c203291000c4002400081d4040040800d4100b0902c400004d00c01200ca0002d10740344c0d4440142400103114100c05580e00140c000d090070741d1100e415082850a01075810f00c44400d01a14036010100702c0c0c6224030a03400b098007854010038040c500210440403105480800c001540c840d0b005024003c0c00240368402d08010f08500780080c003051504d51005802080181508424400e82002c40b001240c403d0000302000040449640d00311100310340814000e0410b0300031a03e0413041600d00c020406901c07002c1d02c0008400b5450503144495104243c02c03103610400c6504088104410b56035540e5885558481c028000706075100d0721130 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 839188776 1250 839187526 839187539
    0x60204090906150506190302190903021809072102030102070b07081b0313020420030a060b030609061903060c2102071a07090302180106140f0706090309050d0c 70
    0x1109880903005598911100400c21074445e001035544002191b0400070a40e264654141d01900c02c0c0000c1300204083c10798622004c907080b602c4401072f039009541c032091a402c1405104004c00c0e083d10083c0599005a404100f503481082c0070040e20b80c0041403110368281c0f10b50120782640c002aa0403543d000218040100d05540044803540c00b02e08202440c1c0a014101130448451001070b00380c80c10031082c0071404040d910756400401a8002c944400f07150f800031072803140220b07002594070104142c202000007a00d41e0604066078080c0d003008009180071b40701d40701040410b9807401d0300340b610198250f60000c086084d9104940020302c0340c1d04e0300494141c0c1c02c2c003480c21b2402607940b0142810b206120785408170b000c44402018000450420851545540030160390000440d44001e600c9540040c01703030a41c030411015281242c000d80c455150201ca0715000494602070701a8413803c1d20010b0100c180824182c0e042407a20b83c4c040d0800d418415244c501081a10f403040005642541442d030042100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 839190026 1250 839188776 839188781
    0xc0305090706230418050609090703021503131209050a210b0903190c0b070f140a0912111302090a090e10053306121003060204090906 59
    0x8101440050420795041200240140581c1e4650000311204095049119038540c030494000d02865544082001032100441c0c1c0904001c403180ca000b2074040d0003184036400005904010741e90300a080001c1c3c840302c0459910380344c000030101c0107a0190001002c001c6907005954404240c1c96541c0d200f00d8a040c502031000e0320950f03902440320210b9a5082c40084107220030703600ca99a074411801c803220303120007800900e540952500030000800c4254141c000e1900a2442ca00003449814070907482c0e1f54420040e1841840702103480c2c00328030307c04144014071040d0300082103000c0603402e012a40c40c0d2103002843d841e1850000840ea0a0b90421003140d0711b15012108041011034910154a05031f0302c84013182e880e092a201d05003220742c90b400d50f202000b400744800268404002000c05c044c0c50140c030800330417030400c000c0a40c42e20a4101100b81d101012040905098002c0c205910b03000c240707408a01c0d00713000140850381e40c1407511300c0400050b501c0e000800060946401c0812040240d061a408 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 839191276 1250 839190026 839190031
    0xa0e040b09041209080303040b0a0b0d05010c26060307060c0303090b10080f0f0705040209010c050105040305130e0121110901061806020307020315041a09070e01080105060a05040e0f100c0305 84
    0x11180c6c0706108000000e940d00d00c84550040c080f8401080d51810440803030300042100000800650030302050300c4e4140c0d884032640c200407900e07640c4418212aa44e0482408580035103c282e091740121409000d864060031203004040d1082c60005100c807255100c0348011103068034407c0a501d002c07501000303030b80000c1041c9010b601c0041d004d07000300950380d42d00700d41d00d8656100b400e01941d00851040d246a00a4001c0714800f90410020b112601e060316008050364021000c001c4407501060000ca074803528020304a050390003031000c0030b1034010110310100200014910441e04090a601802015140c1e004254003e007140d0f116003241c46484000941028120313003110b81154014000341001d41d03000660300d200720050768180710445d1181d04060720b403c611101400740b10039869051001a0790001800400c075084045000709507602ca652aa081c3d540940b01d0642c0020100700506c15450164045403407652580300310745003d60000c40c400e003848941505160165503032000709c42d050350140181607 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 839192526 1250 839191276 839191289
    0x30612010507020606102d140c19060e030c0c010f0c05030d0e010204150e09070503010e0a050a021e190206090303071b062d05010b0a0e040b09041209 66
    0x525104400941d84c0d90010420382c4250444c00084200501078440303841c40609108050300c440c0f400300e062004003000c0c01002000248600b521030700c020046800c0d60400b803030703003000b0b4082088440c0001148140041040c0c81c8180d441c81000b1200c042000104000700c1c610300035000808640c4000b50441502e10001018045040303c1000060341c0031080380c00b41c8405003400140c02940d82c0220b4024000d541040b003402c4030036202c12076000e410003000c03c050350007103945d0b0000fa80c420400300c855020038414407800107500c13004502e5180d110742100c0d5021664030700060822004200c0012141c00c0e070480754424002c005074007500c669204110042904443c00109154104484100c1c1c0e030f031200400c0c0604000e9524000401d2110500306009803580010040c8011000042010600d40004110342c4840305180f01900c1c040c101805018100c6a424101310705010003414240c0300c440d1002440c1c0d07480740c1d03078589440c66076907000c101900540c0a40c031020001c0310801b002610010242d048036 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 839193776 1250 839192526 839192531
    0x40204111801080405010207050d0c050106081504030e010e0901090f1104030308040b1506040e15040b060a030b06130f0302030d140702040c021f20040f030f1a0c03061201 75
    0x80011007109501c01c840c0703502842c1a00155a4500f0521700900900f0002030140c0240c4204d040130990102d6110403850007040204441c03030343c41d90b6541c1c0d103c12003440010400883e01c005804a07000d0f244002a980060501c10030718082200012900ea40c260040325000f03990b4007031100c210703450b48202101c10502c0c403401481c4c60b06540300a427003480700910042c10440c5040000311038003200d41501c129140d021701503075151501c407080c0c15181c031421540800310b0740c0f00d0700c540021031a1500900041c00790142c903491074051100350840251a4010301c154000004000411548004207d61002031240c4039090340094150b104060818152011007002c20010501e60842c0700000400c664031580d0460b00080d80c0071046606900302010b03425400b0500c1640c82c1422036000198200007440c80c401158036078158100420400709010324080d4107204c0381c91600500c00211941e4014101a020710300b000d0440520200345912100111010038502001001b841005d04002542c1da8102400d000203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 839195026 1250 839193776 839193787
    0x40602010e1b120703080304051b0316170f070923010e0c1303050607020109052e150b040b0903060f090307030c020402090409060603020f010c0c06030509121204020411 74
    0x7659880312011400600c1074100750f0003510200c40c00c12001000710f83c03126106072680380a091003602e4220346014140040a40a01c24400d0f150114003203100e0861003503480d03146030800c0c280352600c004a8071100d81910074031400c10195242004500000c00e5403481c04255208880c0c2c0c1800d4413400010751211a40c250801400881203908200e5800003500442c0c1d0349800c000c2081d1860564a5440540140121410300030b82940c1034025041a900540c00c0764030411907110601d10761040080b861800d6000d000d00c401202002d50042c1503400701d107141c0050345640380c5007403202541c455030048a000100003810413803400d040c862207a100c120410402401c1c50240d060079140d119a4000808110301a4600d604658032603054401611000c1e0003040514000c0c078041008040c240400d900c0b60b0341c48140c41001e581b06000710000154800c0800b1115407030440154040d0802900313030b1406006003d0410051502031010b849a001c01e2001482c0c00d007410b006200440d048680540c041d541d08008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 839196276 1250 839195026 839195053
    0xc0d080c1b030a12120c121a0616050a0218090607020a0f08072d060b0619110703061401090b040905031606020d02030c0304031e090b0a0309051002040602010e 70
    0x1003d004030354012051207140c080c840000c031580305481022030310b1a403402e02810b203403c0e03000c9401540c5c0842c8031400c000e10301d004502c0840c4501d420b4201640800b04110000c0958500092a00b4141c4075600b102c01d50403640c0d0000d09100c03004105000c1500c041020089000000c010203600000c2034000340c51b50a00540303c240764800f40c1c0386e01901002c8002290760130082e508800c0e140501d080030f0b100180111030600d0042d10042040b080c2c40785400c01241130300d2450a4001c44a24219035003103181e08081d01201542c9911481d03000801a00034924008081091409440102c0c40340b030154104540c1000796213411104a04680382c01107203003206420010301c0000881d4940016041c010007560050f242034806803080c1114114150700110034404100004000346000314802d480d1703892600884d1141041041c0c00201d00030004030b0402d010000030301620010905603040749004603103013816403142d52800160041c8003110a86c00a010041994203100741c10080d6408005801074010846 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 839197526 1250 839196276 839196283
    0x90301020a0e09220311100603060e0c03030f120613020a0503040c0806161404050415090506060c1f0f090b040302160315180c061d040507080f0601020c0d080c1b03 72
    0x20240903125044000310001080a0315180302887e0301400381301d4407031500030045c125246815200f0710900130300b5561860080180d4020448544003d0304100c0802d03041d1f038a851026000d107410800400c40350b500d035007160000b86103180007512425528201450251403c1185a00c10f03806600700600f480030050a030300030f4fe00804903500e8483d03500507141803001d895201f035901059100f4a0012400d07241d035182d00d480c1e030843d25802c8041080b607130784800303104c0d01d0300c90b402e000a15500121050049241004145411480b82640005210b0301100030a0101c41e00040240c3d402c01f1540c042004040c2d0401109207540c201500a07200c072407955480f41100d021a5224514440d101d07041940c1040103103540b24042900075416006195440d18003414803064020111003004230010b0b0001d05080c50300503603004004960724007a0a9468070b0b031056503400c015060702c1c114008c48089404664650142d441c220340540107065030380c480c400f06540b828070b0200d62200419500c0e1194240784d034011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 839198776 1250 839197526 839197591
    0x2511090106110606131b200a0f031b060207052a062703030406050c01060f320a06090e16080403050c01150f03121e0e0303090301020a0e09 61
    0x9460010b0210303400440b00010b0207a00744e04641445d01085415078440d4441580c0d41030b010b41f00100040d61041405040d16200807640207000c044c200000030700046d11035440980100c620380013a044981050340c0d1101a40d0003140280d03040c0d801a140b181c040200c5101c20304804002c072000640c0400e0400101d010b82c00340f074450740e103107040140b00300c2c4d1401050050710024500007421f03240da49464460142031a001540d801075198071302140824400c2c08581d100080d6428444034240441c50459101442440b800000f4949840054001d849480d25140703030b00a010203441e4011051308010105803449001000413904401c14450205100d8200c1d20795a041031b014689559680e40706016503015218055007688800b02003003000490011101100080d20301c120a61500d0303040105040313541d120082200c0107080000c00088000c00d00035401281080c0010f01a80d06150750400000d007203030042d60b400000b06070480482c0c40c0c1c0f8503055a100703502c0b4101200007400d100d450707aa03540720a1b240 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 839200026 1250 839198776 839198779
    0x8070206011a0c070503010207080c06070504050a09020906070213021909051f1407030e0111210901120f0209010e060f09150d230901110706022511090106110606 71
    0x5001100f0082400aa80a00700c060003e56480001d440e05841591140034981e1240c09070070081040503203d1000c03101161001000c6090309404c00c00102d0080d400b104105502c014204010401a203030050b8080c00c0c03010000005803541002c0e055220260f00341c011040400c004020309202c0c65035404070401401e07040c02c00500c000705482d08191081e50f07061010281d10360300464090101940320700d1084040c0d00aa0300c04d0a121006546503a861a01d03000d035140765141c6801c02084002070030003500e41c100c8145071604026952003110700407200700e40d040145090700094a6440c7c1c0d600100c0d100303c075107000d40f90581780c100d80c0500340c000b40c01840c4c2171502c2068400c4c5440f5140600005407051079040303007410401e800207a0004044c9078075070107030514100011380026a950406118100f10381d24441541c070301d07000856850741300a40c44000004070900e028003000b65190308864200540511440050007811a282e040150080059105104001d20302c1d010108500c0d02203042c5400000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 839201276 1250 839200026 839200079
    0x40e1506030102090904111e01120509030f040f092a030b04111612020304061b0c0e07020604051515040f060b180f150306060d060e0c0403030807020601 67
    0x318040002d0280c441e0010f03440d40001c911040c002848580301c400304410000300d4007040003070464602020145050007400c1d01003400c411028022100a40020f41d00c40c4000b8240e83c81c0c217182500e240b15a40068103c408c40442c2c15605120414640c400c0c80c018a403581c0342c0783d21003044010700010b2000100c50340420907441c0c1030a03412940b55504200c1106040c541d075662140c030481c14025208008080c02d542c590b0389902c0e190320450010048906444c1d91360f8170080e03040141c0a0700c00c0038585410044605002c00da40014050401807103c5018100c1c0741d02401031030a050410900e460021259080340601510500818008140c4013101880091701c2c0403a5444010301c41d8002005603600071143d441c0b0010b1204d00c4c2194802c2c002c0300c020f0007190043d041e0315036130701130020f03001044000d8103440c401040410716074502075004d40300781107500302d0118055803685032464013020142c540d081c0042010806204158101c09501d034003521b14401000d0541c501420040b8465001041c420b0011 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 839202526 1250 839201276 839201281
    0x1030b07050a03060b040e040b1b04060c080903101b050307021c03091212110c0a02011128030906110601090b0a0b04120c060c050a02090604090b040b010f05040e15 72
    0x107029030001002003117441c903000c0d1210354818040540441c03c0320112150828100003a0740c008400c0184615003865802080c246820702000ba60302c01034031142603800aa090001e0302c4103940c00c00181ca109003540c940840c020b101e88500b2002c000c90782c0c1c000c034140041823003082001c55000403411178610040317046070f07101b16502c0010760040c0307102c0300d02500700010a40402c00c40c0c0d4006140b200d420000540400906030011807113012809602c151a401d500004507400156120300503004120b01e90f03000b5204154040e143e8000d540e05c408520719104100c2003034038014140c00192140003009141406020301007581e0f81643c0354241400313941501903440d91a0400e50b100d00c044032000d002c64001c0c46a44a4a03544800001c100c2c180d0100c522042c7d604000c81c00342d21401c110144107521034001d101c159690f44c20001c0144005010682182c2c2c1c400005d40031810b4019040e0165002d1840c0460550600710030b111035150a800032402281848028850401d00040d4042c05000e440001c0010381c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 839203776 1250 839202526 839202547
    0x64302010813060f060510030b0307030b0402120f07140604050906011206090c020f070b130b031905041406010f05060409020f0c0109080c21030a05130210020a02011701030b0705 78
    0x861031019100e1032900b980304600e400d0980c003034000d4440c107c41100705026407110131010b50740012480e41c4c05070840f040400010b500500d03241e8003c0d20013441c40d048050250101490100000c20030b071540d50187c00e080103c6a0340590f4030038010001c0e18140c0c40c141c00c00001c540445805841a4104004101b40580d80c400e180c3c42440a8085040140260062003000030b545821004a24406000e00e0320001120358031031040710003100d4510008512580307005403100c0c441e04010205407603818811410203000c0014422a8440c40c0304520207035103240c0d42c2004600c1c0c900160000a01c07026a000c1c10f1069030b4801c4151021262224005a640d10007400c01d4101c9000b5100d000405600300324100e0100590000500024078420b4200c44000003000c91203041e11100862060001d03c04201140803e170054004650003040c2001c10f0303016100350350115071201c0707030400f072040140c014111800466921a05009107600400843d0426505640355004261409050501400030005620812 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 839205026 1250 839203776 839203801
    0xf3a050901032a121a060c07090606030507031d06011403100c02070501142701230d110705030f0304052e0c0507030212090409020643020108 62
    0x144043e03090300c464904142942e10100d102844940224145440340e282c540114811210b0302c0708003c070240280541a404e02120307900103101c40b60b40340181c0d4000b0558141c036010301d01c01002c0f5a5000070f4580b0700020003c003100c00b260f145c254214100c8086120f00c1130001407044c10748030244890b5140b1034000d00082e00d0040c0d50640c01d00c1046c2000fa0340c403641c0d0f030081a071004850081e2600c0401c000e403003050340c40e1032141c108034403010b404070401e0116030001c1484044507200c040c14521506013102c2681d0302c2d46901d091105d0716100c000030f4105070041c2c050003020040c1480f002c0c140c0c200002d9685858590161510b0136a62a0002c00081c05101040003494403c0d01049a280d10340f003421444500b68080007441040741d241000751501c2c07214421021509040e4041d07014001c1742422a0040502d984030f211140d030701c07a407a000c00c2c00143eaa401d0051641891024000c181ca00350f004118184600c40c802d240d0908600a4601c2e00513042d015625480540c24a055030855a0700c0219140303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 839206276 1250 839205026 839205041
    0x10030c0905041a1f031401083003090d1803020d020d0f08040b030403030c0e032508030a030e070812031b040909030c020306010e0702031b07080f3a05090103 69
    0x14820141044c0700c2840c8010310b4000750b41e91460343d0074008400c0c802000c00340800e083c4203500c0a688455541a00c005d4242500313028109c401034100f403000c040c400e860f0703040d80058400d05426006030000c04c9203190080200c40500c00281c071550340b41803035500003407010100e050b0f01030302420074004c80e002003054004013005a2644140050344541c1c0b1101c24a42607002214118042454800c141408a009508598500c00010010070a21148188402c60480352140118030b140c4c104c8004101400c090000e44455051681c000640e02600c44407145000e425a12400e4250001650f8260020340d100c00c03a82c0c40000c450100d00c071a8400742c00f0400d40d00ca2035001220161405c442d002c101580320034250101c0d0b0084045038001d13622000d82d00e040000035151100542d20400524a0300e040d140ca4940011703140c03800391584030740e0322403200d03041c082003049604003608043c000e214005501441300c0400d811407041610600040310043c1d6210800140010031b0200124403488260720a410404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 839207526 1250 839206276 839206279
    0x8061938042706260313060e1906050a2d18030204150e0f0108031606090203060405060f09070305070b030411120c01020d02010b090a0506010512011410030c0905041a 73
    0x50340703943c0c0c5040280300781d01c4240e444612280c01224980c42e0000000c4d030702200c8000402060a1f032500d10195500c001d05803a1540207001c0d40003e05401000c5100c0c900200207645429035291241c0300004c0981c00115004484030710300c0d1461000c1d690317007d4021004100203040441c1040c10640c01041031050310f41c0001e40c03203420024580846440482100200c0b1805000481d040c1c23104805914020700034001c101c0d186e401488210381c44500d61400800f0580070755000569002039801190500310b013160f00f0741d00780c0d00c100d0500100441281c0070392b500c0305ca81c00103032407500e0441e5101e58540d4124861903803c2100031012400344010382c0c40000d02608010b28007051150b03081c0038251610409084c1501500135580101400f6006014039030b01c0e124000d0100c490342d65109000302c02400c002d40b102c0d0410030140238017440d0380407151003980a4a51482100c601c0007002c0100440c0c101da210b12a010103042c003200c111090780001001c020360340c007102c0102d11002e501c810902c12062480c0005d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 839208633 1107 839207526 839207531
    0x17090604020f06040302130b01090e162303040c05010305071d0607080f0c1006050a06120c030b13050901050601050c0607080619380427 60
    0x511100400035811300341c032a008200c000308084204142c80d07036111a0350355290b8001c52204002c142c128900750303a0740b901131100c0041c00754801001e014481403411094004460541c840010001503131802d40340c2c035050400c102d1828403841128042480e100200b48081d1062824820030a030481071001e050020809000441d80000360a9074440403d100c202c4684080300002d12940550400520b407180c1c00c4091001250a81c1d4081c40c4904d41c442c1c000c01c2855004010349400c070184080004800800b03139020f4014241d00880c0c542d00860030b040e24588981e059100501608000000f0030080c0c0d9030b04010345891140098040c00e552007003000034400d078840c42c3c030180d0046024088401030607071510070100701041600a038080121204000940724030401035a40c54035007045003d503604003030440140703c034481c42c050b03582d90024a9012851564049145110fa400140d808 = true := by decide +kernel

theorem cover : BRFrame.Cov 839028776 839208633 := by
  have h0 := BRFrame.cov_init 839028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 839028776 ≤ n) (h2 : n < 839208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
