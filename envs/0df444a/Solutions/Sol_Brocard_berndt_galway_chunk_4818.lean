-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4818
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:50:06.587881+00:00
-- url     : https://prove2.me/submissions/545b55d8-a30f-40e3-b849-65b4b3856067

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 866366906 ≤ n < 866546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 866368156 1250 866366906 866366923
    0xd030204180c0212032e03022701091805030a03020c0706030e0607050a03090f0309080c0f0a0303080c042301080c0304111e040e1e0a05031e09060d0e1e 67
    0x200e1315004000101021040600d8101058a050312040300700c0d644000d010700200540000c3c0d000310222001a41d20030314904042000e010b1000080d407090b420a00300c03101901404003244528161032200c90080368050005100400840c0c50069548641150086c144502075010340145840c20200e9000040c02040b000c0e031240721490040d55a4083d41c40c20760003005490000382c90782c80200400c0042640010021003526040b04c106e03050301c8001c1041111000b090560260020901a0b0030000079009580c0302c1d81000c85441403600301611800044148284100e281500c1a1741c1c81c0f0b012034039604121707440d4024180000c6640707140b400b91a10041c802e00642910300890619110b04811402995001d401e10801001489000482d102c02a030b143c0c20052074406030050b85646592003000012020045503009000c1c60038480940c140c41e400300040548036680e07580c01c214421159031307158001c1442e070039641d000094040f20030150340d150040c108103072201141a11100d031a0004001001035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 866369406 1250 866368156 866368183
    0x15090a060b24091c03030e0c0d0c05060309030f0313060c0c231e010902100801050a15030f02070302100510120f110414010611060f07030b030f0d030204180c02 70
    0x50b62025980086400351001d00707013502076000e20f409100708060b40b43d008078081103500f10407152508504410040341440002c1d00400305c5465a2040000d030a201000d168014040d0080e82d003019001807405032154001c442c00410860b004c0314004c100841751084440e4400c0341c0c030340048003807442d030307035090180080913120005844c200000c2452041c04104010b500481d07101c03030300b0030031008090450283c5942d0750304030303c02c1c0b0401360a11569071107290080d04a80c0000c060034981c61600c0d002661445022a58500301611031015014084140c00109040d61095004040321000c1d4101e40c4203c174005428558081c6c00c1c0c0e1410001d8503900c00b1a100112741001c2522030300c003924600f410005900210840e00103003449040415000c0c1302c45420304a070a0354403824010444040a07039187c07041121000386880d00080801c00045c03090740151a8104058101e42c81180d0394407000f4607250034201c40c5000a07800080c2400847c00c2c5824880c03000203549400c0c8280d07505608040d444402c02c1c030b56403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 866370656 1250 866369406 866369479
    0x4050a05160501090b090d12120b0405060622080303070903030e030a02032a0a03050109030809030307020303160c0b0109022a030301050d08210f0c03041208060315090a060b 76
    0x3010569281500f039101f4682c00340c0100040850210042c041c00220340220f11075a16100d0115010704003800361510899000308003a240c40180d29544d1a140c4d285000d0004258030170b080864107500400086000e20303500e841d0400700078558600149150841c451490007504908429401a180041c0f00d048912442d440503080d4040c254654174540305902009600904406001003401010b505c4044514001c1d0780f901d00315500c2480c00c6649100c113441d5280140e1041002880403101c199184031000d01074038081c6a41d91540c1c82c0c0030059042a00420700f43e60703001400842103080142844100040040b0351561110701c0c1810356107038007051148500540d50004c0c020100103101c0101c40091482102d009015100402ca42c016240304940c60440c44080744046562f4418600540b07100355448890b050700007036800021200f411020740b0681e0513114155400190b0a00713200c0d00741c415440f1000505090303225080010540b1200d042ca1402401d5140c580d06c41a9a0360038405010300071200d04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 866371906 1250 866370656 866370667
    0x2303191d0603151905031c0c0204180209040605150a060203030114030f120a02060a1802010c0618030c05190b0703020724020913050c09090604060e04050a05160501090b 74
    0x4000352a00f4001d181c0c1d0744645420507403280840380c501c1c1941610760070740031100700f4024141e0a05500354144061004180700080980040c60180c1000b030080401a62800702200540c1c041070000d0b0041d101185c03043d854030200b00041102403000c0740300300800c6030f60000607803034540c1c040c1d00c0e40700c107015200078030540344480000307514204041c001081001040b01c0d10034120708a0380125400951240d0014019a0301140c280302c0240244d550f0710818603001d00c0c2d01c0b98564019240204002802c541d0710707454899840d00c21310a016030303511250090f1507403a841e01081c0b0b80700341020751002901030f104607031884038804601391440082c1e20030f505040040c2d4550203801d1401d40001c0300117000c81d080342075000a1a41c0e40040d00901a89002552600d01400007042e030002a11002c441040c80b01009028141d42450000102d0ba000400034000180302e9854000040390f40004403015983d99101030103240c2003102c204042041515169000c4c1d9003d401d1000017084000240302d0501c620402144 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 866373156 1250 866371906 866371921
    0x2107030516050f030d0f020307270b0d06052e0f0e09011706071e2307290601020a020105030403021c0305060103061202060d02072303191d0603 63
    0x1007000c18035410000b00c814010803085602e03540c1d80b16101d001c80c02800c242c001345400115000392402001076445d8200c5203c4c908440c0340b0b8181405180c00820030750030f50009030741c4814500170030f220f0445540200314681002d007400038013815054801840460340c410340001d12903903108492038003564030345000141c4410104542e02000001e02aa0201100000180c007045544a0280c02400e4000756086a43c0701d51f070a0300e8010b4070740840c0c1c0e4000c60408050982501c2446164034403102c5110210141c03840107944401074102e060304940341c45100d00c610030700c0201100c85186201c1c5c02c8029840e0f038a000350000352170310521071000b4140f00b0040042400c00d8000c1c0310245c4c040c2210810056401070043c00100600410786400f80801c1c54858003080601d01101107110098010309010b02d2710ba90600000b0081d0b000d00b009441c0e40c0f141c01a900d000c1500480d43c0000010b225000315101d081072103503600b08820f0703003800e841030100c420344070f2500c51211801108000003c8480c0707030322582c0da1030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 866374406 1250 866373156 866373187
    0x6140604121a150a0611100f0f1e060b190c03140c0d2006190b0d0f03090e06100f0306053606060d0903030605150c21070305 55
    0x20003201400a1042041c2c20803c0d424031802210b080b43c1820305103540d240c00751140c1201e810000b000d0b07000440d280e034500103190010281182621070004140b242c1c0a0310034100e9428811446554840001c1c10305c24110a005000181450445103440c00c0071003c00f8802015482c5242820311448291070802e0501800407800300008444a165490f032508515640f10b541506101d8080307140380d10720399284042c00e80c03269209460400189910b403510210b40100d04545203401003001d403104144096603e0b00081c00207107620070310301030058125502d0013910030082a00706050054544e4200005a03840395802001c2c148281081c52030442c01400c110050301481c0c02540d0807403071a1483c41440280c164500800090412007004003c11800507c0c410071402d40350b0342d5018005001103000c0c60100e60003000c1a43c844c1c04c0003d030389075440b00410f0849051b024140000000455001da41c40e1007070100d5401c400110041d00100c0d142d0101c07a03203040c010000d01408021020070307070b8000340728002c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 866375656 1250 866374406 866374433
    0xb040609090201030f15030609050307020d051515090703021e040f08010515033d0207030f0311160203160b0306100e010509041116060b040614060412 66
    0x500280521521614008040c08141d40c0480c002460070b001c00e40c46100c14400c44070028500048810050b246446d80130240c1805882503c19000030050301c3d00581c7d03403034900341ea5241700d20054402c246c1c04201c42c41c1c1d800801882d001c0c0303642008a01d41040d651360f034a50b40d405106800d0042c5c884644001d80f8114090510919041542c0000c2c01304805642600300340480c3d8252009200750340c0d030083ca50400001c019a80d581541c0003071600854814150080c0e03200301c1035062841d8032540344603020041076100c56910b6001d0f40d4001682d0050640c02403003140e508000342824001700b01440100b107050302c2034461001440741c01c00380f180c04641d4180902c0c0351003502409200c2c4065116005427546510a0710058802c05810243d4042240035820600e17a60005845040c20440e24505100141c404202203403540001004512217407040c0b4500c00d00070070302034100000c02c214800c082c4000c64070b0b2900981143d40d15103c03c510360b551a04116016035043c0c080380c1c082c4410619200e0800d5040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 866376906 1250 866375656 866375659
    0x601030312182f0415060806010203070501050123030f0d03020a26060a080f0601030f032f060106182c07120c080402030a06091e0b09010506040213090506040b 70
    0x2442003402c004910260f0a148800025588840304140d800030081150b80c1211001310208208000b000144c0c0a00f0310b050744184e060042d2450000503036922030840304240c004413882d0120301c1465100d0585002c0b1f5a080c14400d078000d180d2507411840b119a0780c80f0050800c420950009401c6404034811b50042e2451680d000c1140c104070542c003130070707130700340d082201c146000c0c460040000480890005001c4540388081d8003074440d9909641b0b03911745071241c03140180c0512004040801010f1404c1d40c4086448151222408000410782001401c089040e4852000c001084e000c001ca01c5290140950440d10003800c003080704a08c0321010305108040b1f41c2100718078101ca0080249d003540001409241c040c0d404010411005c10340001d0350f06c50300a0714003035010360100e4000800549035038030550078140115000b1808103180650503c201d220300b042259947c640030280b220710442400b8040d0070a00846003582403420411000ca03500e0290b2044240103612072010425944555000081d0b1410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 866378156 1250 866376906 866376923
    0x4050402040f15023f0f0304060b010e0312070c15080a060902130b18030106062a0b040201050319050c040e0703090809120717060f0702060103031218 66
    0x54520742e1610b41d80062040b0f00c070141c688070750700d0559032021520010000b550107a0443c0d80000006440c08040340000e200805000142c0380d0204540d6040030746206e0840090b0f143e03680c5800d14001301610600010581407128a811503040360350b000c01c02d00740352452513510340d480c1c403540d04018000d17407040c0d4800800c5800c07010304c114503035610234215441024011001e00880b035641e801a0102d07c0340350f10124001102384010300c01c0c0d410b4007000740041c588008200c0c2156030302c240002e084454640c0300740045200d81c0b0959030444010004e030105000410480036000c4201d407510f641c6668020300080c10008000f00082a0031303452010820f6801c0d050354204010f291951407212942d200303006480003100080d00241034607110b0b020740b01c0250ba003c59041c0c203181c80b0006000140d440c41841c0351940c020008046020a170400d00c1200303001c5488021305083c14031508000d0442400b800000854010100500c046600001341c081481c1c414400087c45601c0e1002d07600e800310982d50014030944 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 866379406 1250 866378156 866378159
    0x110a0204050106090608011e0b0c010f06090c1209080306090705120106050703170631090804031b03030806060313050a050d0906030c090e060301060b071406060609030c0909030405040204 82
    0x1030713100c914001a16403d8407940141d03600ca4541525074101083d01e009110418501406000113050240c01c441440c20000300c0c101d640d0705901402d90b40960400e2032010354030b085d002801a40148100d28143e480907040111543c035403100c0c4401d100081c1114055140c2c1c0c00030811a038030400c00c41d00038a04c02807484000e56194400100554000305066002034100c007000d001190110a4580c01028001d140c10030400440d0340d807100c07405813030b090720100c3c585928889460f43c0c0f9901640f005039100d0001c1954071303411441c002040520f03007030100f01c010b1080031082c000039030802145034002404032511f070f8413a5181c062481c1d20441001d4010f01c5e0b402075498030420410000344c460001034194460408864031500b04030221500e80c48804001031000c0410401844038085041d0131000280000c520380e030315418095140e034008041100c240031800d038207021601c000c4c01402d4001c0021240e05152040490021343d031402f510345050b00c40c0000d0008122100010000c0b00c004060181041d5220b9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 866380656 1250 866379406 866379419
    0x80915040e09010b0f09060d02010302190302071703061305061f020a03021011040b07141f05010b030601140a020c031006090b0d1a09011112091615110a02040501 71
    0xa64103480e002c2542d824114110341910b403080740001200da000e090f40b68981d450908200c221010040d00780e05159003000009100c0398540b02004400c2540e450140c0c1da4902c5103824401d00d0302107800406054024814401c0d9655401088002d40d0311807840403945468101c001601040b1004140407160240081e4403442a004180010018000d40945650140806184095034007920300d242911004000600c50355003030310090800705006011b10503142c410424900d1910088420f000c43c0c1c03048050303000328040d1841c01b40c3d5014241c118245411428040000b030001d61242016040d0008045246801240700300150350615800508603501d941462503950300425040c041c1d10001c5007050310307883c80c6091102d091200c1aa00c054240b60013102c00030048a0242d0141c00e002d140d54880819071142c0c04a6009020b0200d5a02e5120b51b00d82004101e40340342c80114040c040c24a444c01d14204030400304100300340b501c00400c4c10140320a649030005141440c0c03250f0310007903015103040c0012901 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 866381906 1250 866380656 866380679
    0x60b1912140f1803030a020a02010e1e10110414030a05010c05091206040506131e120e0d051e10060308040905010501110a0221030d20130308091504 65
    0x10700c0741d6500104154458445082041d6800000002036520820101c0d0405240c2d50060000f8888d038030000482d5100c00100604100113920f0402803480000c1c2080d841400502501da04005841d0742004110b808100e20f03103840c0590300c5151000c103081a0b0140aa803018441c038a042c43e80103008021000702040b0151240e0480381015008061000c0740c144505000908030f0301858120008007450741c2c0e11310100f9982d084074502241c07030455175518102440c5101200c2d1400d40d00c11280340c4003075040b001c1b00404074840c0c0840d5511480380181608007280d408600b48c20102040c1e0765900c0203164001d0ba1a00d0548282c400c90103061030080b0000c01c3c01130300c2e0042c0050b1500c81c4070a10a41c0d0765130380112100030140e0304905440d0000c4102070010310b005a480410055500c44075011245030407003090554000e003031140380494559400c545050000b24000c0307200081c8148890605541c1c00100300d240c0c200d8040201801c0000500c1d000319074482452808100c080000b15980713035211800c0a51 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 866383156 1250 866381906 866381911
    0x60f0103050c06090d0b04081306020109060f061203440702070b160c03060e0f120301270f060303170c1e090d08030907030312060b191214 61
    0x1d03607000c0c00442c200145040404c5a154120082c01408010084e03120300000500181003210341003000c214a080340d101307015124004110741d070000540141982410019181d130050074000c842d1a140040c0420b079052190814410f0701482c0207800c40d200700e084040c0c8034403401c0c0c1c001362070ee40d00e0340e040d949440301002c8006007482842c402003080d1101d00c41130740d4a580502a0150500061105000082c0c01c0713400360150078055041c4045040d603d03202d290032142070b10b4000d00190170070701c0300130350103401003082c0d070140f0802005461841d071501c00d0500c61110015034402140901300d03100180518075800c055009040000104102030350380ca005480314400d00d12100844200000248015142809a130864018900c1c07c5408900d4941203400640c44003400551000f044541c0b00d0101d0341400107907200300510740003001c0e10350450038082c5c00d400d040d440700740340c0d00c0c00c011050241c15214016918502d036207500001140100c4101039903119908403603039000d0ba240c0303004000800d203501c110b07a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 866384406 1250 866383156 866383163
    0x1d0a081e01020301080307023304080c010e011e02120c030301030b10030c120204411608100312080610031404030f0507020d060905010e0a1709040608060f0103 70
    0x88000014414181c00e0b80024420352095410500520000d400c001051038462031441004444c481c41140c401002442415081c040032040443c042c09411401c0110720000c000034200240c5d40d880a4000a04907108812000b03403140c220300d5500f418600820603044065204480d454403048680f590300d1740c0707030024401a41c00c0b00310400414440d5000840d2003007682d820030102c0c0140c0d401c1c00101c001c59160450100d0b0440c1c1d840c80c101c00e620794540040184501107141050750041c1d1041c582540f024a010b41c241d0145070701042c8003695003400800031350b080c042d050680156950303220084d001c949550010b8140c2d00c1101562070810744c0316641c00d100d030310121030010502d210306e9021004c54a02082c100b9130340d1018000320b40440e0003280702450001d054507019107001150b5011a090b101200021110681c5070b0300301b01c1c00c0002c00c1c010b0b4010403910000a0200c1d02030760310380303503100d80011030909089600043c2009103074903140c2007071015008e00011542d840c02c0001c1c0c20341102c0424031003038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 866385656 1250 866384406 866384443
    0x323130c1a0904051b0c1b01091d0601020c130608011503081b1c050903010b09060d110d0f030f11010501060905061c090b2202010503071d0a08 63
    0x2056908000c0c0001822408440e0481d003440340c0741040c04002c10005e000e500303e200c9070341e07601c2d4404908440205000071b03009015005d200038600811080026402e0303214184101000c0901c1358051310b5240328444100384054003120745810006030700b010005512a03400c600d003201e40010300a61600110100c8010320020003051a41d0480403161200500004011501c02c20120b8690706005001100040043c3c00340d038029103c904603403005000400046002c9a004112103207035203000c0c407071407990030001e585815007890074400040c888011101c00901051091880c022251100b070004901c0030382c0031024001ca0205801e01a06030401e0000990004142d60580d28421606000e0103040f240540c4505100c02d0510040140325002010b0500300d000e070030508444160f41c42e0040300c1009000d458031801a0030079080401c42180508541255900c00303213440401030341c1c01401c60341d02048501d46044c059600b0203c55268944020026904c21060f41d030104030104003080403080c0c038441c104117 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 866386906 1250 866385656 866385659
    0x80903030724090201142209091103160b07031b080306121501050f030a0203070605040602070801060803160f05010614030d02010506030706140d02130504180c060323130c 75
    0x821043e6a45003030024006070818140c46403103180c80c40038042c007040354669074604142c4280f10151131101644400130660f21080f07607500740075081c200586c502c842070340508440700b000540c054144080e403142640c5148001140d4080c148120851204401c0426580e0920351450400b590b03280c20a640040c030880540700c1140310040000f83c0d40702d801341e0262940c2650303031134602000741c1071104512080d01402200c1e420801641c0034001e52002c1e03d419143d0584450401300000d2034020242c0089966a142650034401e180f400800d94148881a04004414000350300d00502006100c020042841d0b08266002c01c46c04c1329080b1405a01c041a8125211202c00701d000324243c8105039411a09a04280c4041c0400d505c90024902002a401d4085107066000781c0d540040f82d10550a188103882500310510503032500d070088802c0d483c4405020800c0041d580c8990000c140310307120b031801341a0743c1e410011268048543d20f000c4102004c407202c5452414401842d03000122580450321600c505a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 866388156 1250 866386906 866386973
    0x4050a0210030207150f0204240807021f0c0302040504020a1101050a06180903050c1020070b0a051b0d02070605010f060207181d1609020c0a0f0809030307 68
    0xb0360b8421343c0c2100128880345680c2c442c4a008089000c0c03038104198003044082118250b15040251811600380b4200c0e40c9510000c00070314001d005480802150811100019244485a50300c920b4148080c0001440b4032400ba06800134440e5510554000e400420b4461942c0d4020b014403580c100ca1100038441aa114684401140c1250042140048000c8480801d040d0aa884003942c00c0c82410454509070141c2c12003440c0070a180c1108c01056110070030700c105046103000081501c1403040c281420006c5554640c5403180380102001022580c0d5400a03c00c044105e100208401c00707044295920440d500d0100069131001009850305402c00c0700000b107107000d4400d10342c221440750b400351540c982411400b040254814a203628400c3c2c4031003007901e04117000345014940c0301d8014000d03c4007205001d0507030702007410381d801a555103206218050340010007080103400c0c0765000c1e000c1c440c58040c925060889019904200ba01880f010400d94208403282e0f40c1010724480d469654180c1c03048100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 866389406 1250 866388156 866388161
    0x20303010312111e300a03330f0e0708013812160f050d020c010f0501080115050a050f0d172503051204020402120a1d070518040c0b0304050a021003 65
    0x5c40400c080344100450b0041034804e612042c000f007804040030301045111503200e2900d84c0d20003004004800007240801c6802c42c0c2e092400003d1403803407200b21092a2621014020307040511580103030003c80c1236840d40341400d50020b080741030305442500f96091600d000c080d0303040d0440c80d034041c0000c14034004200401c003000c44044981255075142800421034a2040b54140c10008200d482e80380c09122001040b1400e000b4030540d12a02280060650700d080c030028203440c8a138924a42c8611000420b0015840d0000301c070082d110152900303100d94a03040e0102c1c400d0f0303100000c043c188840140298032001d85850040103002103101907420408403422242403030042e50080200404c0d000c10503402c0500782c4405660348540024401410007540004400714600c0850305000320310b5544501c1044000f04200e8040303c000500001d202c101d04000108404400450719250824403140020301082a4100030700080c00010403465103034101490300c280c0d6544219000c034418510000031a182c14404e1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 866390656 1250 866389406 866389483
    0x10c020708030903032a010c0c030314040c14031f060501140a0215060d050a06090c08030702010e0d06020c0a0c0e0a021206011d030d1d01020303010312111e 69
    0x2401303146003400701040ca041000d2070a510b1b03c4d5000c21198501c3e460102807040c860b4080942d1179101c0702c004580380080c100c0b040201000c01600340c03003003400041200341041505403498004401e00942c201000030386484020380000030f55402112210507032021541040c4200c98080c0c9500c1c0340400d25074450442401020200320050384114070034014011807000c03550300138202500203119507850b0384030103080200e0b0f600c3c1690055110410078003004040714000d401090070741c003d941450700e2a0f0009190b640d464409610031003420b030016060003c0d550440c2c144080113811140001c002c1d2901044044443c801c85503404104800a02c458000d40200d4206200d4624000c1c0035507103210044d11030b04030343e01d0031142d001c0c406042c0000545040058840d0342c501754542c04903060b0205e44160500700e6542d0254115081840101300140c20b440c02c150f0794907800d0a003611511005003405290546a40d4444554030818501039403254010400c0c00000c00802404040c10454502485102001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 866391906 1250 866390656 866390659
    0x210140f04091802131a060406020c01140405011205180115060e0105030f04120903170711060405010c0f06020d09030c020909120d0c03110304030306050907141606020c0f010c0207080309 82
    0x5e203d030001c00d5069024040e2400182c0d0848240451300c40030030741c0764001d40c0190015a2211034609625070b0030081c46000c3c100c1c43c181c142d2030541890002800c1d60702d0b07143e0100300180c503031001c90301800f9420b20105c2810740c681d0003000210201d01c08400e401798944210780100e01c0300c000c5160554843d500300c80c45480600580c0c0d01703035101e96a40142e224001000b10702000f03016080800001c40d214454194011000c807056160f4005040c40069014000741c0184244400c0104000c540d07001a0441e4241d5003000b4004103050003400c00300040e20550701e40591003032600c48810109034110f102400101c1c000c0c3c40740050303a540c0072071880c0c0e100c0c10314000c074180d00380034040703441c2200181c0c000c50030740c24280c5000308078030b41d07080500c0c0c1c0190070070ba400320301182d10303410305000c2424242819640184146004605140302c200d0f0903005201e40c070041d110011101020314140b10280c0c040300c4000d00d0900c1210010349807550344038020004c2c08900e0340140110742c0b00081d1030000000350383ca40d130030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 866393156 1250 866391906 866391919
    0x10221041e0b18061207032007230a150c2606060c07030203070b03041a0708010303052809090c022e090f050d080c03130210140f04091802 61
    0x500319014015481d51107540f03540b01c036080000344801a000b4600601400c120f0310081203446c07644150101c1139030003e01e00e0b018600700b4407464020803100c460304003a101d040101c5440400101e1011400e1040d0400d0185c80051282e28150226800381d000c0480c81c1240c0e5940c4807046410b1003a650f9499582c109400e040d42c0b4600894001d1610600906684600c1c404544005580780e02080c10100c00354894852400d010080009021103403120b60300d400c415002c14091441d0040c03028058200601010301041008207854680e4071260010380d4003003e81c510030400c1303000f0300030340104110000d004410b0103034140105001e039180001583c180c11020704405000d1015509400542d036280c0450f0402543d0312030f04a040850041c400d40e1171860300500150803007c50340040589001e4000c1c5c00307415103000c20010007640c1c44004143e885600e80c11682200342c03406110381243c0d6503030300f1070980855210000d04114002c1c0c80300002c00480b501c1220134007217801c10100c509210840c4800107174000d030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 866394406 1250 866393156 866393167
    0x10e040503400b390c0306060405100b030a15090c02010b060c0c010e0f060703020d11160501030905160603020a09080705060304120507080a050901170103051b010221041e0b 76
    0x1445030600c25450440e400c20158030300003281444d104542201400e4540c0c0162136100c00c182421b101d566441072042e03c0500ca242018051040d580200b4070521074020804408109011032603000040401c001882d48260a40c0b5260880010000341d454a00035600c0d0000d0002a03041004c10340e0300320b440007000340820080360b40041d1494500c0c0c90200398058000a0301114a030368030030203414214000c0e8010002070ba0f4500020b4002c07407296030741500d0b5074070080402190002078201201551009e19020403403000d00e1400c83d00c2c3c50031245441c1c13814a074248010614030f40c9a40036116a00c0a0b9984a1904d655020b800d0707203030b0309540250780e004881040004c000c901e080070102013258483c5031441c9040100e441c1c98150f504044800c40001340000390000c0c0c95a40701c002c0070410b04c103040c16440a5407641d6941aa0ba01c0c0000c0c586d15444021226401180e000f0f00c000045020701c003801d41381805060018403803a6100e4081c4080b00d01c0004072007103c0b801014a42c80503154125030891904 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 866395656 1250 866394406 866394427
    0x40303230f0f01180f1e021b0a15020a020f06010b0309070f05030a1704080304090f110c061501180b120718030b04020a09090b01050f01030b030303010e040503400b 72
    0x700f00254103210b5042c0c854031100182007040650306e0203180107000c01a02d906606070b0101104200804000c16a0b1024100c4e43c00b01d2954181039880500907440141d680f0092401030b030402d14458800d000501440000050440220000f540300341d90341000d880020b03440d81c19241621059000c4c05806901074802c62000407903100750600305000c100ca80e142081e9588220ba480d580c05600309900440d220501e10302000b1141c0a48060603103e07001c010b081c07088a1509903541c080060500071600030902c0d120b101c0364003940c400a203245041c900c0c0c203400c54841e1240038055101a0003086000c2842d000659018810400d418001c3c03411200c040743d035071464030392600307110340644160381c0452800e000044401c224462148200d2007001d108140d50716000c2003003e2110700a9455040c5030030607807000143d0350048201da0541d6026250b04203142c54504040f459401490340020171080601d0401c1030200360120003c01981c0560244a00310020100da00c00c0f4805c0c0d0321900c84000340070300025410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 866396906 1250 866395656 866395661
    0x61e013609120f0e1c0b0a09061b0203091302040b04081506030d050304030809031c0b0102071a04030609050712050a06050601050405010804080a11030406170a180b040303230f0f0118 80
    0x1c0d1118030300c5e0b41880c0e880139128201c0d0901c0940354510035555a2503040c003002102c3c042c00002004c001c032001101000d00d100603450384902c801c00c034030611007803800c400b110ba880e5060f540504500e142ca00c0d10380b6140c440b202c0c0d070743d032800a1360040103210703200044e09450006200d01d075a01d5240c0d95541151541d540a4a8000307016200c03501c103000600c100807005425100c1002c150349100000b14164540d13000182c1400c0311908083c416001c020b203a80c0326140c00c4401c541c1103a9008000207103020160030207074100400d0360020441c2e00245000c1a003071041c00501d035802c030360242004010075115880159501c0c4211b20070f040c0460b0040d0b0016001c10081d00c0941242113590410008040380768a801e42150700a400c000003189209500e81080b042004071b06a010310701a10810402c4003200c9000a065001280201541da41000007020507219070803103039003900c4a50a688450040084054911400311041100d40c0078903000202880882c0c2c2d03d0358100c83c2c20040d11038203c82c812200c6c0e0003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 866398156 1250 866396906 866396929
    0x120118082503050409050f06220b180415020316030903020c19060e040618051f0f09050f1302240c0f061e013609120f0e 53
    0x290581001007201c440040c85400114984a0b07a03030955541d007040000300865034050540c020f040e0510042164648400c0d0085980300064880d00030711010b40200003002e8000c0c46a1a6007200184603140e044c0c07135002001c1c42c051403044401c403201000c80b0403554120301085441c66802030b0b0200306020490701035446030070954064030507160b070b91501c90082001c80f6090703004201140c1441104218069200c212060f0321002140c060000b2031610141c02d109030f054501c0c9503641070355000450002010000c911405130f02d410801483d46555240f0007205090380e2085590f001c0c100000203100c0c25942c140584102040c810002c80c1e07070703856028484400c0c142a00e008000070010003194030401c0c441c0141100c1e5401c600200201120505140c1c104880902980007902c2c0343e410000ca039035400c40030581918000800d07503000d0b8072015104144a00011440d80385a040c4644016261038190020300086001d20a006244074050504135401c110303001043c0000b2708a150f117458603140c503100300303007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 866399406 1250 866398156 866398177
    0xb0a0203070f150e0d02070801110708130e0411010e06030c190909020c100c080402090f090c060412120915030e1513050d021b130905010c0e12011808 66
    0x109816503003c81030048850139455022a80d011000f4628a15810819480501030020080c05039651031003010200b4000d0b1000144141c0010950081901442002c04010215101e004d011820320b03007001c040c182d102c50180d50004292100d5040c1e0f500f0242d084074080c081c00c3c00010b2904081407401208161240c15440030402c000500007070025040c0060000f00e513402d0060980c541e801d41c00001103c81035840503052041070005c00016988246c0c940340d00020708140c14055540c0c0c01000b0b41004500c0d821140e1080d404200418403003921110500f019200d04001c90f8100b030084da040d0b40201d0305124a095289000c0e0040069900c80c1c1c11aa010400190880341c40301d00d5074803a20000786003152010b5a19490b2484c50042c0003080121101e1204607001420700d500440c2c09802141d540810030354041d83c900c02c040005400030340d001d008070300c0c1c0200c002c004005500b0401003034003c00b600d103280b007a942c800380c1015140c8180b0440040388894400ca0030060b20760344e1140300c180c11031318511 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 866400656 1250 866399406 866399423
    0xc020703020423060306010e0718050a0303080108010f0608070b0c150c1c0b010503161101050108031804110405151c050f07030207052d1b0a0b0a0203070f 68
    0x100580b12801169405244050b10710b125110070708002c58540b20040c00740d482680403034010045441c15007c01c0307800c0146c0d13180140b01c107401c2d0b01e4826040d280d079611440d0001003400f0000300380365104900f50306881283c0002e00451010108140030b0b280c480c041d001694010031020810f00f13a16000414000c8101402d0f61082030b440482d01186c100116042101e00c0e0380000e6900d028400030039941104407014004001c04070148000900c1400007c0600c080c0c00074a03d00401c126000d10301481c0303180d10030f1000380015a12105926101c0d003004091001c3c012800e034030006949000d0041481d00c0c44010282d9013032500d01400c112915040020054030030800300800b05040c2c96006590116814400c8007090500303003c8000f880a88005010608052042c003280000480104144c44076541044101030141542520324100d1001c2c0c005d40d01c0755200b101280e1032404c15544840c41c81c03400440b005500507540e140700e108548120400000160410083c0c08006a51340341368240c80d60003200b25 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 866401906 1250 866400656 866400659
    0xb0f100e092b090609030b040618020603040507080120070602091f030605091509041709060d05041b0b1204030207051e120f0a15090b0f0108120a120c0207 68
    0x10022041c014510250501c040b007034191480980041c07840000b004586441c038109032540d01e54031903111001d00020403c50b1120700c4103100300013603150241144d40042c2100d41e031303050038540242c0d50145881500307519401c1071000c0400d15090032a040c186580e0302c0b030781454a0480c2c0c5e643c1c0000e40c07250003c194001c0700080d200003420154402000041403640b400a005800d0804000407100024130010400700741106d10320030781e00d0b40c2d0f0f42140c2059004645d40351450050005101c240980400a03070071100200c2c10080210040e041a4003a5001310300e241501030401e042004141c5640c01034240000e01000b2641c61740d041145015449806441a0780056407507000180f08401c54081c900d1207010301d0301c1013500703d181c407903060414810040000d10005d01e00c06089900d9080000e00a0010700c200c0081c3d160360b060f40d0700410b51a40c0d01c582c9074051442c10071010300000d0403c1c0119200786c8a4241c080200c03444103402c0301c0a11141e51507400440103070340c05110141c04021210011030003060740 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 866403156 1250 866401906 866401933
    0x10f140f0a1d07080a0c050f0a03290103050f06030303130c0f0e01050319030906050a051e0304050f010203250c0b2401080f01090905070b0c0a0b0f100e09 68
    0x190302c0c1c10682140103042420300200042d40c003800080616142040c0307400d880b81c01400b1108801165110552a1040b141e0f0907401400301403107180017424200102d4860903002d0644120454090300e041105480300d0080d5150404215000d07505a401003022038980044041c580c09428402c198842c001d503141d22041c48607503607503408445000d403c40d005120301d26050003403403100d12441c0e00b01c003c4005107803002401c4101c50300c15441440b10002c1c0114100e03103c1e034200c80c2520380c040c40c0140c00c210030500d8048241d00c00c81d0142c0d018014400640d11880041c001c5a00907100c40c0198000c501c4400450506c001408580b10140a00b40c5c41e0a030001e0556a5818401d181040a102d5980309101d00c5070100e484030380704581040a420300704038501c0ca645140ca41500c0c0d040c103000071140d501d0301e4002d1500c1d03059000781d07054400106900f40302040000315280e4075840740c00180b0881d1102000192280020344600546600761142403191403810f246c00b90313010103420129002d4106112 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 866404406 1250 866403156 866403179
    0x5041107080c01090c1410030e071d0405060c0c06010603020307110d080103021903030801090b040605150a120e060609060415030807020a0f080303130f0602031e010f140f0a 76
    0x4a64603565140c61034a41404010200c0c070001b0310b070a03034400400d1010400081c00540140c1606000c1c50b0351900741a081c0385040011102801ca0888001c1142c0c2240b488100c802a0444003290103100b1800022003481111081d1103040300d601004061503400c000c429000303034100904140800c09a41203881e030f0044208910f02c410011501d40003160350441c0148484412124075030400300c00100f404100203503114400030304640814000160b80208440000c014084552145a2003100c0c03410040031a01004c1c014818149507480d10340d004007032051038038182c03000d5400d003000b55005480002e5550510030381d45980104001c0c40001c491003500100800c0c051240c005031107408010032078a045082c005a0003020341801e90401d80c0e224540304503d031742d030f200043c0b9081c400c0f551081142d04001d01d15041d0507006902110540d00c07854414031001c045d04a0749110b90000142c00000200c10351040b142d54103a49000d207030a00d10100d0b10f020300c0708070f1998501094000c0760303036400000c907406100d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 866405656 1250 866404406 866404417
    0x702060d0507141804110d020a0f031505060a030f09170414061303080c070e070e030c04050705041a0405030303040b0610091409090c0a080313140a0504110708 70
    0x44000980b820900c0e801850380d5004407201c0080e0108200344019114004070a000030203048801013031094041c0b00c004c1c402e018400c60821030a0021945800c03007900459901303140703055940c08120864030140942201d41252050f241c00440c104a5101858841d8008640301c910030324000c20483c182e42c1c1d40000d41c520301c125040d82002c0c04142880110400c03c0401070f036040448a45081812002174880d00c440c0511004000070030006602510000500905c001410302c441500340c7c900d0284d074040c041001d0010520b20a004407180c110a5103864030826000f07401a03a00c06042ca8140030510150440000a292907040144000200c2d50f400704004c620451040401207801d040c401c043c0031410170701d1400e035400d1107a10181808064070280e40e01c03080301c0782290101c1550300e5100200d81050281c802c62034102107140703804a4000380000c010001b55110200b0140c12543e5041600e0f015003405020301e510030024a0204120310701a0024440d50b00c0c04070360a841e040c955036590070f031ba5024 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 866406906 1250 866405656 866405677
    0x60f080f0f4f02130923011506020109030e0603070c14010209040e0303010e0a09060207050109030206240906040e0313060c020a05010c051c02010b0d0b1012121103070206 75
    0x5600a400c8107840b2010040240080041441c1141c1d40d030364009030b400201c101c12400b1569540da0200e046c40012010803a024400c000401654400708444501030440c4208984074450220000240c3e80c2c414442e0705101a0169140f1500780d49010401075035620151401082140c20040d20300400c4c1480c00d0307000c0b50401d24000683e50030190041c0020344c1d265580d580080e40062004022104181911952000e040ba10009050216203421802400b0745080038100750b213080c1310f000400d1b80000c1d195004107513652a500c02810031003191550501800c0b4420703003001240c00820040d044c81c0d0010a9091041c1050702d04001104602c2007082c1c1c41540400d0000e80e4900c10b100c01e40c1002c10f94500075010078604500544115200c1503622884400524407010455021560303d9201b035000b851000d20040c081142101141032105013503030155550b07601100c040703000181c080d0700c03003661100c0c8a42c006444688021f0031141035415810102a14900303001c10010100165180c0d002232030b40c1c40c42d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 866408156 1250 866406906 866406991
    0x7120e0316050a06110a0605070c0b090c1306050d1103013b0106060c11131a010305131208041b03200d08030117030d0e07060f080f0f 59
    0x2d05403c000b80000503a100c84180140c00404140c52800810b8445485803c15004039054071030302c108840019100e8406810403140c0d90a20012150121720007000003022501c40480303000341c418000c03c035200d5220382039110030b685034440d00044825000c10a140e00003000020352650448000c1c0504426401c1307036200b00800b03002c00c1d400b80d150031540800288104004c004c00c90911b10058540f26014501902d4190f02c0c1160580710344c0c03814001a0180d60003001800000151a802403646d030081103001e010a0070200010101c0c2c0309685038011458100044900302903800800b500c5005000e07105641c0520170180390310780c90548250b4a80194881d00d112540c2c0d030710305d819486000645440c024401e170400c000c0300010071610703020b803415503040c66101120400e0341c02c3c00034a1813082c030190304c2d003580c241517407500340e048042091000c90722141c130340d5010401d4260342200c03440c3c002c131402d8800e41030010114490b03807050450a584050301010008080150074807140c51024245441c000a04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 866409406 1250 866408156 866408159
    0x31902130f06110d02030a2106091e020f030609220506060405071d062212060c14070b0a0e15040309060212040302060c160b0702100e0607120e0316 65
    0x50b4490290924201c08101501200d21324180082d12442810141c004100c80515801080406071104883d00e019001c020099960385032000030160074443e26884e003c292070160400201040d00071203810000d0309184a01c0c543d00c05041251551000e40140301000c8440390300e02c19400d1011002c209240600d000703120500d00f140800080d5400100f240b01004120441c81100e0240004080302c1001c00b290341540381c51241c4003900500d280785100105011841d4800501d8081c91100e0541542c081c1c0d01c14801e000c2c41c0758040d1500101068a52a0402c0030000d6601081d520340c9416000010010086113000b02c40003814a8070380b034a1100740d80c1e10b88c8a000e00003016046900103000704440d0020f406031001c01011501c2600803448081c1c003232080043e940c12812030a00c0744807504402d650a10a81d903407214110b4410317030040e0204034040c6410071041c0c1c601c140200414600c240c0300500c4036103000e0055407220300c6c60300c0100c2c8040500400741c0450700150b40910056006640d400c03040050503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 866410656 1250 866409406 866409419
    0x19060f030b010e150906090403020f1002031608040816230606100801060e09100b2809030c140d02030d0201020717030601050307080c0702030a08180109050303031902130f 75
    0xc940540020000113503204400440d481300c45500780d2240d402c4400c80110340d00c9080a0f0b00344280701000071300c103001d0000b01c0c9002c0d103243d0b03018600501010000d9038a10781c004001b601e110f9001d4401808020091105011110502201c3c02000e413142162000015104102091020702140c03408060b40100741048036070b091003101100b149040345081c8aa6514016004d0a0700d03034842016030088014800103500c5c8408410880014819007810703031341d14071480c00141c5a880d000001301c4410b40c4c42a0b08016014483c0d110304007642d400184402403d480d250150320a0000c000103150410800704010026036002d00054a0000841e000580d0320105031819618460414001c2c080142e000c0c001e01c10166802002d803a840b840c14103200c031141e05c8000c1c5000942c000c5030720003507241c41000448020040840050074032110300c1100600c051040000644155803580511a0075520030310008410a03062464a0742d8038010f4040140350203c1480c0605050103690003001c842c008100040005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 866411906 1250 866410656 866410679
    0x901030506030d1e0e0a03032d121d0105042a12030c0201090308040603020d0b3705040f0603140f0a17040b0309010f0510050919060f030b01 62
    0x1c0022006400d100802d081c018084d4800c000783c030354944900f40b04668109002e04042c20240100070004042542d0300c3c50018100203022241c0382d00248030182c0046502d00b038040c401c40101203611101d041014100c102c00082c010682208001613403120034a440c02400e214541c021303030148100c000d009201d5100e8a40c01003030400003041220740c040c0104240000680e50103155589807919291061007070004031001c18082d0000b8015020000c0c000480755015030007001c1901100074140804a42401084400780101c82da03100251182d45c1030707000d640ca03400000305401e4102040c3d11b035200d442c2c0c808a002c03030b0408c07004081056a242024024072001004058040480c08018404031408094298031007004200c000d00030142d0900d04c512416048090364060000036003119124035002c00140e01038507503074400340122841d01c008210800c00d081241400d07200042c08040c000d850f151445101e0001c0610a00103195440501051500c0d4186041006601904981e415541042030002a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 866413156 1250 866411906 866411911
    0xf0504030b1f06050f030411060c0f0616030e030a030c020106080f0a05010506030a020a0e0406090602031608010b0c0706050c16030302031e040e07030e1507020a230618101109010305 80
    0x20b002c2c05005e00402c2d20141000c995109a02c50301070820002c04401040e070f036001d0303854125120b000f40c1c4d07a6111001000508548140c252415441200d000060140c0450b03403111801d912981042155816540c0a80c100c880c00c820244000540695110785082c1031000c45840d482d401e030031560786a801c1c04403d009a6420140880c040d22181e480c42d4000303040d0441900c500088581c00350005000e001d800d074050a1400e030801415942d900e082899151010306c0250800086a41a40041080040401500c83d91002034006001e490b090803001e1341c1c180c118072052101413003000c0026000e5210100c002c00110310940003141c55800d4080d00c55468040d02c440c0c10315004040c0810401c80c200041080c0d0040041e00f0000390452440225505040140017001c080c00201010b005806600040710b90000c1e009609030a508400915606542800384500d80c032141c0c412808107600500081524003c11080300c1150001c0400f203207000c0030b55607860f001400056000c00c1c5101556054050321380e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 866414406 1250 866413156 866413169
    0x5090a14010c030f1202310303120b120717060f040203100b032a0a0e06061213050f0606010906020a0b0c03060a0506030c03071704050d0f0504030b1f 66
    0xc000240500002c000c03000d4140090208000036a20240c410f0207000102203099040c1002c0d9912103d492000161820f40c16900000b8052118209480103880b42000e09490b403540da403196181d441031190019100b40b880c669845114400c1c04800c4807000c1281c0d00083c0011643e60b0614a0403d503041d04061000700301f8841519210304000050340c0108041d80b000c04100c9002038400344203000b0a10f880403a131019140c07000c3e110340424101429800408419004480444400b91110b05c0d2076807514059642e2074000c071080c00071419203040b241c4082ea1000c926034541604860546810b1f241020711107880c8801d4200d44248078081d41e00000c1540500050300007803400c0100766441003610107005102c84100580030021810715030350500754900801d002040c090316801c04442080c05940300b070b07032604c01086051410510111798031304818865600540680303061004080300350344041c0800110400c002c0b00b00000700c0091101c066042c000c1001644030349001284101c810002c82320307600a00e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 866415656 1250 866414406 866414429
    0x906010e0f070c06020f0706060504060504020702060d0b06120c030603060f07120f0b03070306020903190804090b040b0a080d1106090d14040305011b03051509010e101505090a 77
    0x21070030003980c10215402034000d02d0308440d92422410260024050300e0503005078080c0c005154401d00500e90864002da490844007080082c2d550300c00c0200324401c13084029080b00d028481e1400e40012a1b00401010401034020703450030403000d60364104150100d85001061101100f8802542020401541e02c542c4154a62502d0308020001030541c4090b11044564142c0710848140c0840392500f106111013406022120034070b80364074120019404c03248981d4000c2c45905038041d5841c06010303010300d000303400c91085881c1500b06450380e07001e018000c0720507400545036603000380c0c0750300c0b8104044000d01815014000b0b903051204000e0124141c2c0c01840d0959000d0741c2800b1003610701241034520b01c00c660801041101d118412040640144e0380090b00c203510302910941c5c5c07400101d04001c11070406907010070959884000d900003a400f603426090b001401c090042c00401c01014145400c9007494a4071403605694030641188502c41a501900040c0085503c00c15401e014221a02074140c00000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 866416906 1250 866415656 866415661
    0xa031b05060702060d020c010b03060712050603010209060a2a0803150108150d0c0302030106081c050c0c010f1101051006170112030806120d050a09050103020309070b2a060906010e 79
    0x96520b01420101c0c00745d480e80000d03a51002c0d50258000e4802c0311004d0161021440c002401a00c1680030701c0124000604081c0000c51030b00d018400c8880800006120b541800418002215140e0a525092100341140b001e0b10141c0406001c00c000b015104c1c0c2005a503e10b0107070f60740c540300d20b05482591b0500448034188107007412044405101c1c41000da501420b0044e450900e0007801000b41d1019405501e0070a001c074107040d01150860f0044005010442c013401084411107891140d1610040c4079000080b8429896104400c01c04007145e040c50200820b851100ac8103084603801c0d00c0110083c4000981000101d40150340f43d0601c4009d072040101d1585070840ca405071418103c0d00608003da2003000901540c0c0303c0f01d1070120b00e400710701101c410f040d030380c1000750503079200c03514290104d1080b0030001400d42c41b90088034400d4914001400f00b0728030382041440d9035004215000400740612026070000f5104c0c10f9064178250004000703002e0f42c2001e881c8a8100303901a0085003045691604 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 866418156 1250 866416906 866416909
    0x60c110a0201081f051504050a0807060909051308130311040908030a0c1416170c1c03110f0d0e010606021e010603020409050c010207170c0d020a03020a031b05060702 73
    0x1405500c032a010865507413201c040d81c0c1d0400f140c5165040142e1240c451040c00c40c0307000b0910040c005503502540c8103403031651501c18a41d52244188110400100340c0003003800b0240700381e0011900a0082e260b080c014140a036513031f0705c07076420000903032841c044403103810814031001d801818a20f850a0310100800b00c01521010b80502c0001d1074400c10540b140c07a8658207520414084580c81c0300e40142c03544911201d565001039020741c0c00e040c0c034003d03107074400b0035051285d0300f040350781280b6003d004000c0141d140704a0192040c0e00003404003455600e81d01801040d0404c40100004442504111765a10f0800a040112005150b50006aa1401501f40116a00010f011011816403000ea40c1241101c440e0503014202c0394000a4103e414800003400300080050700c0303500c01c0800d80954100341c0e25611840c04100c90030b482851564010610100107082280c0b10300c1545001424910b01c850f2a5008101420403650003190203540100c850074040180099140140c00d04a0b41c15103080c07400e40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 866419406 1250 866418156 866418167
    0x705060f1e09070b071b0803030f04030f0e03030a0509010318050d120b031906140403020c01050d0906060b1309110306011d0307080c0301150e04080304050f010504060c110a0201 78
    0x9a118400c2984020408a034020007650000b41124021260b95200c1440c15003249070982072289421001c001007c40c00c3c8102000380da1043e4500c0181a8083d80ca54078112105201032161502388003050101c2d5880d600c050004103520305803500c0b80d40c1d540030a41c0c001002c56844401180d460480300c2e0180c8005040030a02c0e40011640c4e1400240c0b42551015900092119055041c2c0c1841042100c02c00c041300d412130303041058022002000581348030b00001c1603e0f40c04071001001604003010b0081c3d07075070160003d000c0030f071445000020b1500755660740b40c0480b4001d420003641c0f100e020600100003601640c0203400b0300f004000c24804d424182c900b6040781e020240c003403410f00a04602c3da294407225480d000c0012140202260003403550703031107010745500585540340c0c041e509141c441d00303011529004101c1100d00c00e42c2205001d1b505c0d5250300c0100d41004e0411034660050114902c4149024040d00b402180142000208111920000303040c40030400c00106c5a90040410000580e8009 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 866420656 1250 866419406 866419441
    0x503070b180106080d0314060f060d0b030303091b121911090a05010504051303080406020a021e0d0206010f290405040c080a050c040810020d060e04080705060f 70
    0x2540005948076490144601c15880c45611410b6103448000a450342000848840d0202951010000d0b042040d6003640c990348200c41154118000c10302d02030072420030721b00070b14100007902000503c15442000180c02c651094032910100d41c400f0005044000a100d07a60b030b040a01280e41d814443e01e5a182e8540391060b06030074151582100349414240000f00010266410008003600000c1c0b42000e411001003d080c001d4a004620f8403000070a1140d4808001803a680c143d1940195a0785541e10a406541301d02c0c6124118020113039000d40c042c0031001d20f001015244000760081e9901e0074002850700720160b12200085180354400c004600f02941081d032851102100700449088240b5010001d1007164451600706180180c0c501c072141c1d02c848420b0140c1c03080001401141c4542c2b0000c01d003801517001d0791005802451b00410311828540c0104100d9080c0032001c00d10315500c2140980303070601183e040d10f8100c000034001041003000d21804e9070240c0d85c5141c2004c2810003d514642c14210b4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 866421906 1250 866420656 866420663
    0x703021005190c0f03052202090a061509030b1003020d0212160801092f1e04050109020c1e03040b0a02071a040e070302031b03190e0607140403050307 66
    0x5841c04070780503024802d500004900d00400900142c002c034880149801c11a070408000680782c100030407200d0002124000800302084d00c1000c54071180d408014000e000541003030003a650341d2400051840041c400c4881e104015120b4400301440c1d42842c1c064047d0081c010481ca200f030100a100694440c084002000d80560b030144a400c40c0d00c0b6550718001d05140c810803205001000000c074240305404c08010ba0744a91040d010100c2d07488051714290100c0d011101101d082c003a030608580c00d00b00b0181c900380c0200410000c54000304c00204084410a8101d4000240c00080c2c00c0340c9c4120401c11504481e81d0401d48201e2551454000c075104e019900640388004000a003120380d591080150401034803508104041307051078040d0000d0164014030803181644400d4000910607402032003581d200f0100d52548004c0344c141e602004901c3d9200405440c0e241c0c16080034055051000e1040060301c1c110040203007418203016038041c1805424442d04012918200024400070f54080b01340c4200030791 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 866423156 1250 866421906 866421911
    0x9060f0b09040b0316051002010e060106030b0d0b040510050f040b1f031b03120527040f180b160c06090f0b0702060f0c030c07170d0204080703060509010207030210 72
    0x460340090007601500548030350510a80d413402c002c1d03000c182c4160003160000c8030791f801000d940401c26405d89040b01e0144400340c204600404c4041e000b0380142d40030100041880001c1441d5075683e01061405584c260740710381c48503556808a060a20501d074104d192a05e4204031442c1030f680c0c02a2001005010050540003c2803c4542078201c0646501450b4080c5100c0d003403801006001036590003d200a9031800a074036141c1c58800d00940840d0044484003402600001e43e40807402d40c1500954582508550b8841500742e2100d41c610800c106040c1d008415201031207107003000400e501c006032001144400111104103d04d400c49401c11060790712030800305100300641402059159805000340100d40b50004000141d03a011030f1241c8910903c40412401c1d844810b030b140d4280c0812038810004c80010015580031807191006075200c074241c04d0b0308500d07081d010385d00da9050341c02550001441c0d501c80c0c9002c0c000c00c4100d001341e50388441d111000b18140a641c0d00c000356203031104e00d1550300403607 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 866424406 1250 866423156 866423167
    0x3030c070f171b0a15082d0c0325020606030706050301050303041208131d0a050c0328020c01140603030a0e060c0a02041b0f0e0105042612030402010909060f0b 70
    0x221102c01d204010211074000130503454011201034901d01c8100d0300e07011b460300d002c00c2c00c50791040d90f944031f203003e00ba0100200071542d903445403610ba507500180524490010350030580102074003884401c18028166409044581811000c0c185404142e40201301400320600051002c0d8a00106407021184002c0141c1850522030a00c3d8485208118041d40c004181c0000481d81540891608202e40c0300061007040c40d82d9001c0840c01114400e403458100e4250400210b4500380e04594160380c0c203103200c032881e80000c88500c0b19100700c0c0d000400502d0141d45a140d0804003040c0a5201c0b9401072042d005940341500c00b200040c0140b03403a208440c4154030200d20041008401c10408001e00d038040c10030043c00301450303184801800f0754040b041c006081c0e501012030051207420b064a0880043c4c58917804d00d800e04010302c031181e0801031200c840040480b901c48810b0010007280c5480e0000c07038055562400d2600005028001c00d410070361229003400010880407841c280310300201d40481c5906034981 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 866425656 1250 866424406 866424409
    0x18031205070309180c110703050a030503061306170f062a04181a040c0206040210181205161a03060d0b1014190314070503030c070f171b 60
    0x60000380c1004c4030107010008006039207280c603407000d00803c140b612466026400482c0e10391761010103000c0207000d80c011580f004002030242014540048008088550b60300301c04030180211400d6600c0b4285482d4040100d80c0888010b020403514144110040c044614004c21a24040b2010407519a04880440485480020414280c034081e200c0c2e40d950881401c141d03406070011784035500364043d01340f8090346a10090301d071a1168041019054000e49040d40d10b81c2c082000c0002640174803414002c00d00310300d2103050485c005030005003082110b602e5843c200e50a2961901600b440400040310103210240600404000c0819200c8410070740581c0d2a0354920100e000c20381d40c104006d082c003501d0000d2001c01000c80103000240c1d6000700c0d042156251002c10081254807040340c56a87e101e003450140041081d40626a86420f0780008903900540d444000c2881d65000d04540d040d99004002c050007001c2601201400610a48551010703100080201ca030301c80114a0b488a4600300629611445 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 866426906 1250 866425656 866425667
    0xc0c0d021f030605040606050903060402010c0c0801020c0a1217010b130e0901091103030a09050616050610060207051f200d02011a06030f010e28060303180312050703 73
    0x24403060655420400100103400b03000341c0b01c68000e040c811170411030701041c0305108400b660301c446030003801011940c50396001075071204d00582c01556021a01030340418041000d00041c070b12075001ca00141801101c03030900c0804a121034500c5410030018401c0100d1b00c40341c107070440d0305480a20301c00a60b5034a4448000d4001101a0300a0b9100c0c8103810030000c0241c010340c000f0403060301403146000000c020303100309600c9115000c0c003c00883c040716000c0c00b06003070aa014004802c00f040001501c0c8046895440c50210200c400301640e0310081c000b4080d51394107000400003003505644a654140005121042001c90b0b10901410020b551282c0380164a40a1612139084540c03c1903503a00003103448000d0113032003541c80081d02c1240c2d000700c0c1b03c0141440011280b19280c45100316820fa400c0001d5413100c407601a111071004004603002c103c0c000d0b114400d0031941c00810740b00042e418550b01d030142282d403400c081c56516001403041000401e210810b0300030202440c0c0f410700e030341d07507201d1a060b100b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 866428156 1250 866426906 866426929
    0x21071701061d090105070305010f060e03190809130b011205070e1305071404050a0515072f1008040b1801021321031b02060409021201090c050c0c0d02 66
    0x410021015a100925540d80520b0740200e141000038849681d5800d01034058400a104808081000e59002c003c01e0380b24149803246250010240c491750042001c03007134000300e0902c40c240c0f59800700003980001850160040c65204100c07940501003d614807001a0020461018512440b0345801c0021903481c8908198091101c00802070021030700024071010003020100c07012000326480d203840c501c00841e4a82aa001c5032402030ac0c0521090400b401d20030001c0a051030040000701c02e01c04a03001480c081c02010041d03441c1c4194400c0098039000900203c14001c8005000314031000c407442d04154440c0f00303558000e81240308900d0355242c555170310030001c90520f521800c6520106000000c218900302510840d1101d01d000c1c2d100190341c004001141c54403000090108022000f1084405071050041c0200390009000d64140342d50b4040100c10b80c0d000c2c95000402c0141c500c0144800f04d002d100c1e80c00328030300c00d140c02030414001c0c980710740c0c3d140c42c01380c84c9900c1010000760303007411980e4018407800c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 866429406 1250 866428156 866428169
    0xe0a11060d02071a072c0607081e1312031b0804090c030207020916020706030b15070f030f0e0d020103020c0a0c41010c0303060801060807052107170106 67
    0x28180c85040b246901c02c41d0041e14840005500d495506c081c0c8016250700e02141e800c91442a605098a41c2c20002030394001003046401d41028481070554284008000d081c00c01100b01c7d02d42d98041000c180c01072040c0c0c982001d18040840d081c0040400e03031000003805c4480100b041590185010300300880070b8001c9070b22454000c1d051049884250354075801509640d4420b50b07d580359500c8c0c9805118200303842c1d404210059000420410010780719810500325948060404000130040c3c610400803944038090036108108042c0070141095880444220095010325107410035500d00c030b0000310040c031003000c041d04142d004141d68132254818440b40d2242030340003014446283c0d643c0d180c400c00226a4840080070900200d10008041d45200640f40f815041c0a401d60481109001518071500004003a010165121030200350003d0034800c4002030001b070001018102d240804000652100c082c1c1c0820b01c0c5010091150660341c000380c6082541c1c2807040781504100918115401441207074040d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 866430656 1250 866429406 866429423
    0x91806150e010f090f02090102030a08070c0b1e0901090c06051804020309150a020c0304062a03110f0c1e01120507050d0506120735010e010e0a11060d0207 68
    0x30100d042c100c1c483c08446045609110a81c1548100400c81c040c400e0040e000d43c1003009079141c0d8a111300406580030f595400d10025410a58491080303505c4200d03581c211800301d00c4071043c6252002c04010398018541802070140b00041d13910740841c91500d01c500700a210b80410601c0c1a44407880d0080c04030301000c3c0085481c3d29240b222039980b50645e108001c1e00c142010003054000101e4000c50b60b907048854001d41c50240351003c201c4090110f4510604d154001140120030b01000454500c1c2d800c0c000c4c1d6900314240b4504c3c41540c1006040c020390602540100b80da88001c2d00c84551f4041c18005d10907010740c145c8103400c016103488003034496100300d007032500041241c10f681207400343c070b240d22081c00c0400099607031000340071250112501c41c403c558882d020030056203002c45042110745240c0f90031040c0c00650584180c8c104400b8008900f41a51908440f000c085000d11820111911400041201c41c19984508100c1201d21901ea4014000000c00d00c20218468040380c031041e6100020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 866431906 1250 866430656 866430659
    0x52106010c1b122a030b01120f0203031909080a020312090f101707141812010f0e0c03160909031b031d0f030c0d020a210309091806150e01 61
    0x48042400d81c05042c0e4413140907250000b02107400220030006030b990155084c0480c1c0d00709034584594580f654422250b454003e0359960050301c0c01e101801c9444400080100080c0f0000d0001d00744100030340045002d40d100d4200f080141c2c0d0005981c2d07118400000301580c2e9000c4a502040c41c0008068030503401c54449459850202e0340103064003044103c5e418400c0b07890300d500008031030360148074420300420201480440845468807250010072000100380224403030784014424259500c121104840c03c7d41c0f644030540d00c02061141407505142280601682c400054a060100034a80146034035603030358066000c00c043c050400303140801c0e403108185680403c2880d00522454101b00e00b40648650701541c1c407001c0c01d005146402d00c4400801501c4000925018003240c0c0c00319200c141d07031000280600080d44a00284504040708092510b207242180900b03026140741d02da40e1288203194a04001c4202d86441141c1c8081125032040000c00c20114510420803005010380185215280702c800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 866433156 1250 866431906 866431913
    0x10b1503010303090b130509060409171312034d0c03070b0d570801061b0b09011e0e0d1b0f03052106010c1b12 49
    0x345040740d01c41d035151846192108040700c0c217805200c0030700540c407070394004c03d1200789005c0305041d5006101402c0050351401d907444040c0229007030300c848a03036044001901c0440401d00620400a420018201501c0c41516070380200b09866040315828000300a200201a000101d0b5174030207055003000011103000540d0301c0d85500c80307c00d5021030b11a441404180c03102e034100403441d10225129040c90300e0518000c9003654001d0603010b081081c14182c0c40341030006071000d82844040c40c100c0b102c4803d40e182220039484003c80f51040503010348984070700d120203a443e44541c119042d260240b4088800e18907108000e4840040420000c008160580420504a005521490252005000e8080c190190354044011030f038001c1c1c9201d015800ca1000c0e145124018464505590010385c0b072008a0b41e295121035200350302c0c02d101140010f000040848482810032992260080c0a08001d281070038081c0028110780d4044100515078104002d5407204045d114250034000c2c402c0002e00065100c807845c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 866434406 1250 866433156 866433199
    0x10504080a0801050f100e0d140102190912150b06030411010e060c0c1c0206030108100b0603060d121e0809060c090607080f0708040b0c0609011b0c05010b 68
    0x81c8400944040c2c0006050301c1e01d00f1400c586290042d1030800e190380c44030b004584061019100e507402060046442000408014141c007400d050760000680301c09030500200ca461645040705401c000c40d501c1c0c01c1c8900e03400b108038000b203594400d2a4004101c2c40414100c060404a50b616504c0200801080280401c1b041c4044440b94241e8880301c181d8540800c0000074000d4070145401980103120503071140c246801500d03604440840300c8001010641c0c00034210b94800d0b007056441c1e07005059690351301c80440c01402441e80d403c50b200342c19031400308041401c0d546036401c054a0300c5441e1603002c000358051140340c1c1e014402c141e24400c1002442501030b186000a45843c2d0b240c1c89020009603401a126081e581d00b01d000806c010311b043c10644850740310307400a907029070381350790108491000038410400400c0101041400c15469140002c000d80c107010b030041500a41d83d042c402070400030b09842c4254144100b5500b01308072000e03140d081850041542c0c01c00301c0e4101c0c5002e4141012001d000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 866435656 1250 866434406 866434417
    0xe15103009051b092205070b040303110d0c03171305030c150a0203090601060c05071d090c09041e0804050a03050a021f1b03030e1b03070801021e0306030a0501050408 73
    0x8101c43d4102ca0180000c4d40c1c0e0840c1ca00d403007525203a080402c5078000b4400011258080c904541c0c1d66625540b840300264480d07442200451862350340c01040071403e0102403112207403414501c203002601c1d140500b40848094141f008031003100002841d040041400001e242d42003800c40380c0701c0d003003440055034403604000704101e01c910510014611080f0390003120301c00c1550390050b2403070383d107070280c2910200354030b0070120380c940a00040400c1c803154000c00640210740c034440c0c49669003031080c407603820070384a000428000e450307080400010503580f20407041500445804009642024141030303140b4051a0041035001121880001c20302c940080c80c0c11011380222002c2d841003d40115400840103101745940c040748086222520300b403401103142840d28020300b40480c02c0032480200034288003220002c1c040c610b00c40329034001c0c181810440200505480c200031490003030580c100c1e0030070250044810580940000c00503105840901018030700c9036103e8001d016900302483c0c0b881d11608003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 866436906 1250 866435656 866435683
    0x5091c030320030603031b10020703030b01081e0c0306120a0609060506030318010309030c0f030c0c061b020d1e0b040209070f1b05160e1510300905 65
    0x20b42034240512202d4000b02c9006440081c0210f1a0296001241080003035000f440b1f5005e000f03084084800b08064001401c450342b081e900002c03003034040301c009480100080c1003d42008000720503801551140202250045001805c558a959803040014820361021014200c039000d03000c101c000704400341d00a540300c40e102e0101441281d0340c4106143d50390107050b6041242d4048940c0c100b8081d402070703204e00d0501d0b000e07142c0401004416120100150600d403401c40004040d20907a01c00e00011501c4030f000b42410345042010300c019841c24a0054a03840350191059081000180420040c0400444004034040060802c10003c0c00c00d800e40b05002c450581c02118491f0000c0c00541c441c0307a952a000c101600c0c0c1a019012114600384070a00c04030301100c8612030450b107000305c0741d5034071294001040159240740c1585400240002c02d002c1c0c0303808050180d04203c00e1000d0154100703501ca00d12840760382480e8a65105172242c010074062944400159501d094a00c1044c07000c0030940304001c0b1807 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 866438156 1250 866436906 866436941
    0x40f1116050f010c0203120108030c0604030e0a0302040e0a020f0102030405010f140c1c090816060305040507030213021b070311151e040303020f060601050f07030c02090708060a0602030c070605091c0303 89
    0x9e036120400c0d140e110f21a01002c01d904140300040009000c0e04c0c00e500850783c054098605180c4903400b0900301d400006205406a2005600c201186880c20382c607107608070284040c50500b45040000f03407145105281c01b8052051407001c4a28900c1103000791071210140c2402c4448001c52100c512203090f07000002000001c100144c0440d60380400030b41d8001c2901e525600c20f887c64540071080700140701c050300443e04c5010700480080960b4500d080c106180c0d010510050b41c42041080786020300c402d04104031210382000004002050808405104c0c2800a81c1c03080340f504d06d6428003002522075009241405d90400c0d05a00c90940032001034010749109400700c4403c140a109020790322041103442a0019a04200340450031180f00b02030854213100c0c2c02c00f0340050900354001480d8142c101d40001c0019494400c0105034640008220000c0105002861801105140058650030503004074001d03c0000500000c0710b40300c51680e040c0c41e601501d40c201d2011440e15009003c0c1035803085410045a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 866439406 1250 866438156 866438159
    0xe0301091a060a2c0601270f0906030206070807600f0f060e0f010b040b090f0a0305061801060b0a12240e06040f1116050f010c02031201 60
    0x5100b4425a0f141000c158003201a200343d41002d02200000805a5041021003c00c2c5059080515987d0005e0390840c42021000750504d1442c0c041c918143c0c1c44400d1050401ca020009a02c0e003000b12110150050384c4103035203260301d00742103000b140d410740501000ca40c80c40000781d040303980c400a8404440900700c00391081c40c1c00100c8121408006e419940c41845005800b00007031039075032202c040e42d15101c0700814003910071980d179000c030341181e07010041d0100b0450400c110521400a4240500034a40807c1c0c140790600001001d5405104105400340308500319806d40741da580d01000c0c0003075601004940d410310f44900d25100502c07503210030010540c201180403920301c10071000c0e0352a09200d6520a046802052403e03800707400350707510f5101f8400302c42500c00e0161400c00324081c0a8000005d120b581c40c1405402d201c200e51002c62000446890500d00c0e08011951030101c4442c0c1400c8140c1010300c0c109824003a0400802c0c13084881e441d840c001c8601c400300d40110240c03168800380390240710142e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 866440656 1250 866439406 866439419
    0x40b0a091a03040203060f06031204060c060b060a0215090c0a060f1106090c130f02070c0311091e09101506030e1203041403090d1a07031401060e0301091a060a 70
    0x2d0000f034400075890307004940040c18006c0b49003078280c1d0104005040340c00c44088a200c00f116940503402c00e000142c41080fa00003800032138002c485840c10141c8065240c801c2d042802034507070130310708004500ca0761600b000ca903c0c17402c20003035100d1140700200620080ca95410020340340100c405d45480c085a1034041003103481c040800d0480c8194069006480180590404c010080342400300c0300c0b4100c0d6441c9090400400d140c4050300b03030507104d110507100703007411030902d03480c0c0d0b60304091441c1c170600c100c00401c0b819000030090652031040c10580401e1030b8440301851820900c100c0e101074141490071452265800c0b1f803a03540c0e07048400c6900c08010609552051a40b509049007144422500801c00b01d00010159144030180c91040800d0301c0c24074001000084040b03407041c0b0195503124546110b0617060f1085035941b0b8100322181003c1040c210f425522443c102d105208400c103115207560100d14503202904064501980030000710b12848010a02c6080e00c030054400d90300591141001042c50f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 866441906 1250 866440656 866440709
    0x9060f090f05190903120c050714030903100216170d061211010e121203150d151503021903050f0f07050d030e040c031e02090a0b0906040b0a09 63
    0x140e03000c43e1101c0348140103052080c01900700c440d0128104140d660030900c04040900c14102c0c50101d035030301c0903a900c0984c01c01102d0000c00c0380c01e200c2c0640007006901f4441e5400101c0d699103181c4c4200c09038580c200d5840d281c6201c0024034010b40a0740311074000d04043d04d815002002c99150240c0f0070000903447d51030181c1850955076000f0000f03141000c0440e119801110310306003089004200d074125100e81c500c440e0500c1c6a482c1c4100703c24001201f071190300550281c5181c8080404d8604241000850322041100c542d06421441c41c503640d144091000c5010400800145402401c841d800200c40c48d00102d95241074482a5094007440c1c00310f03540702c1c00c08107071103055003401001000d2240c241030400c40d800d80d41d08022018003403480310784c070701e107440e02d001e085d6a0403000e440000392145044031030f82c46407000201c504002ca04c100503000e107a6488601076010384060341180354441480d5004100d00344102d410140c03054401203140c000306030b801510302342075440807070a005a20350000d002c0a603 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 866443156 1250 866441906 866441911
    0x501050112060f03260f0702030709090b0403181e030507090507120c0e0d14010507050c030d020f0405120607020106140d02010804030c0618020108010b0f040b1309060f090f05 77
    0x3040f44440c50800120710340b03000382403140d10242c0007aa00070013464191102176108050f04000c0c40e04c0842c580f819840d0600c41300300103081d945800d00403441c040e610701c941d01070001e00040034882a000c03103c0650068a10712800b608403860203c1e2000401400c481070800240f004803440e109008020503159881d0080f207000d629a1344071094030b101c440c1c0890018100c444400002c07c40c01e28900e00e1036540d5101501040c0d40550044104490b100016909440c0c00801c1d01003400020410031140304d4000040302c400c00300f043c000580711905c000c000d28891003140d028a5203e45000c000c14005000450001e0140ca01a00200f08181d520540050b00300284451640e109000503c4030740954001c1540c2e84d4841d20903e0140c94054080c1d88181c00ca496038840c0000440a0420644c00c40d6045603855014101c83d80c89139081c2905014000301a10480c062310001c1c43d00440ca4000700049030030080094000f240d070500c0856113484000d1000711062250f4903a0f00e003056108032240c000b61240a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 866444406 1250 866443156 866443169
    0x60c0a0206041401090210090315110f0901020c0d080a090e060109060521090606030f0a20010c12030f0501150f050a1b260307020a0b28050105011206 66
    0x20700d0350b0b01c544400411480d1801d100d02d1030354036001403000517955a2180b200004440e11101e4249080d0309000c158170700090381e464103041c50001d401418a081070180c41d65120b0700a0b54594030282040100d0800d41d0b851111034001c14000b591000300320310070014060040040e0350f56410203984804034649001c096401c40c0c0419030b060b0050102d036100d070004140c1d4030880c01c151281644010800720030a00116039002e515000501801003a16050040314010314071400200424800740c2c0b2100303031108000038a031100707203c0814444001d901070300580c01159005150f101581d5840b90001c1c029000300100c2d00000e502e40300004c074900310343d46078aa40c800364980e683d06501d6010341040e50507038011070741e01042c80b410755641c42d0401c546599080032140705e03881000020741224804e5a4008100c10f1284030720205100304900254001418101c65801060344202d940307442200c107030148494003004000501004031007000a800e900006c0c102c1d1000c0eaa524940705d00c444003542141d0b6a0700508 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 866445656 1250 866444406 866444413
    0x120e011d0d032001090501060f0f120c0512060a0501122301021c060e2203120b09010e1602030c0304090b04021207020615090c0412031106070908060c0a02 68
    0x6100e81000d520044045200e0300380075803401c804401c8554844403400001c09640c2d1a071118401700130b003e01614004002651031441d0136400c040c2d1101001a003401070b0140728078481c10388024001ca4020308002410003810409074828585403442c3c40d0700c2c00722904034840b41040000606011086074400e20150420070851116240703030032141d0900d03050003004103550340038032402003c4594051481107a40c030408000540c030745400c00c41c42c8408401000650042c2d0b00340d82011345444440010306042e1740c5840c18000000c0310141c3c030002403621904484c1c020070235600102d902c2e291440e15a00400c2503144001c02c03071104800481e6030b44541034808550780c005110401403a80c1e550010700e00804020405410700aa80e040324680344011103000b00182e11050501c207030070644032440d2040784010340b0310460501d44402d51180c0e502c00c5200b080e00301108c240c0c604050611691551207408000003e070f5a80c1d0400a200804036011801461040d004803c082044c548980040341c0e0504181d4014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 866446906 1250 866445656 866445707
    0xa0507020a15021602030607030903171501050c03071b0603051803090118090c0203120703060b04030b070e0d0804050f090411090405031903020d0606032c011404120e01 74
    0x142c400b942100c0074400d107007000c02543c07000690707081c0710743ca200740300558002a40700380e41d00300104643e802ca034174030b0940341c0701809000102c040c3c0c421015001c2002c0c00c0450313840f00d40b000c46510b140302d024005000e0085141c0080c06611040240c242180d40c2c643c0d0601050b141c02c01600b049081c220750307000b00355004001580f0a54011190f07203840713580c80c44601588998926815080d41d02650705040140c20000c0c45040c240d908504040c1c012031540b40401c503050400100300c0451041b4040036210a80c2240000c080030320034810085404405821b041000b007840c41c201890360018040c1d548502448400f1698900703068841c00e20487c0c200381c03802d96840307540c2c09101d0000e602400544040c00308100703d11841016002010b030381c030260366006070707038904014401007210226004a020182080c130b2124282c0304942151408400240d031386005c5c0a10a41624018170a2407146050700e03a00c441007205015114110451807030340764607802032030141d4034011a0310070009036048640d030500742c45 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 866448156 1250 866446906 866446943
    0x1512060f0a0c090801090503040f0f0608010902090406031a150d08070f0f08041707060306031a090309030706030209041508060705091305011509092c031905030a0507020a 75
    0x2c4551034840c00c0003000c0c151a002c6860035143d0004041d58654000502044a4981002503a008104a41c040341d0403a007081001030002a06100c0c2c0601e42d50003086d40c070f1300e950319984051300540e0320850221181030303220700246c07003181c00f201e0348642261061302e804460304004161204042d40300e00c589180c100707103941c1c0e004100907501c41950103040c03803840f000004602c0300c0140090b01054807410f1041200158240c44c210540d0485420582000300820001c0d00301c048040c201c06110034900f942d5030700d0f150700300d1550041d0302c80b01d54503226680d4005005034041d4014080360b241a107007400b05085001290303041c1d440901c1151001c4d030040c000505e0035441100034000000c0700810000400c0512031401044d10003e07080a0380441500400700030352600015000001c040e01803040c00700216501c0030b810980c40e8641c2c1c0511004164142014524051003119842c2d12070030302481d505851180b000341550011110090b105141c40c01040c1c041c1d000242d0000101c1e031000c00d40030003040600c0e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 866449406 1250 866448156 866448161
    0x11190b0a0f060f18090204020c0f01050a0902090424020f09030c0402190c0602040317091804030f0f020115090c1103251a0106050a1b05061305151512060f0a 69
    0xc041012045d0754107181e0f00141d5840c00101070000741440103115964014944900b100c00140218204511b80110180180c6400c1c000c5039105401c208004141d42601d4030003e07048040307042840e0507074800902103150032000009005601016011103010040841c09d20040b44904010b11481240a071280b04945206080c0e5810a0341314140242c149aa603039101c4480070070005000c0d008040100340c06401c2d00b0140701050784480003852180090400351006001c04c0c1c0340c5e050400400c001c0740c0d59094018000d410054100d0b5866a900c8085a81d4882c0c410040018001020014040744001e010010303002055070032000c0b0368503441d20210500e00f40790103202d0b51058203c030347d10030214000000b060200304580c02006280c55955a0b4814020000d01e05000d04480c4002c64072108540d5011803400280319070b001801d0307800d011511417242007151034206940a0b01d02c400740f210080101074450070740124864103056a506c01c001c069010304680f1400100c40d01c061500c0d2030070006030004407a4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 866450656 1250 866449406 866449439
    0x90f0a0807080c030c1204030b0604090b0714090901080f0d0906050f03060a0e100e10080606090a091b0609140603070e010e0a140a06030b0303030711190b0a0f060f 72
    0x11000c492401d40d5003170441e4248040001d0b00c24918001150030014050090089584040200d81c1001651900e51b180701d46503d01404030400c00c151450801101c40240040b01c200c0b09000b05250100e603510b1910384e45c0d41041c0003094116010f0700180d0411140103040c11425240c954444d0741c28038114805084d556000180400da100c0c10552001664039000e202c194014190b88441901443c2040c80c01c43c070403c00a4050011249a940100070440010491640105003205d0340e090545a5080340b03009400001800317006215180c804000c2125080c8400089622648580f507280c2ea6071380c10440e40c2c00f441200703550850003c00025045512500440c051060141450000e46020501240000d50640c10101c4202e40c040202c40c120302c0c007400844001c0c00701e49800e200d40703421400460740300d00001e0405002d00c19510720b02100a00c052000300141768a141d498058800c49041c00034180205680707150700d903032410107407030b5035407100380100c10546491940c81c4000300d280009403c008441d2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 866451906 1250 866450656 866450677
    0xc1722060507080d090c09052e1208090d21020f030a080c0318061311090402060f03041e060203040201080f04020f01050a0306080607090602060903070b0c03060609030f06090f0a080708 81
    0x1461000300b1050782e58031911b0700031088824400d45d0270380360380307034040380d89207130480c1442150f201400401140441c040443c83c1d0550000c086502c4440708008911003040c000d000412a0b280180c50310703201d042c450b0188000050b02d0342122006116065840c0d00d9200d00030120001480f0000000c0c40840c0010003140c1100c809811b1022110340402c0d010f0070480c050340c0e1960915016812203090040030711100b503032404115549070b06828554001603541c455041c4104000034048001010b006031b62864424083e01246003004142507403809200950080744c0803804900c0c140c0200740200840316941d489141d0192003444116030110041da6103800800d950010541c4914003c10007907003d000041c02000035890f62001582070075006800e2550050828190fa80140161008908405403260300200c0b0f9550035aa01d481e9400483c455210342035000b42c04d807280640100203d140001d074140b0494801c2d0075580c0f440c46030300d00c40b91248459040640b2074941401305001140301e110081c00c0c41c020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 866453156 1250 866451906 866451923
    0x3041419081c0c0b130809131b0311090f031002030403020c0a080307030903060510120507060f08070f1b02031e070f060c0605070306030c030c14040e0d0c1722060507080d09 76
    0x100800003c1072506080d0112007030030b450b5038245100c0b2449109c00100a03449050502440c450720840040700d000d5086554803035804814551101c1d01c062209e4103c0c81810041950340349801d05019644041c0403980d280a02c0451800040c2e4200102c261104a6410342e5180d048030310f1901c58070083d02000d4110460212401d0001030b10f12041c076189041544031718058101145030032409070121700105200d00c01d002c0200b0800800c2d0b6840078581c5100303492400c1c4200d004119002f030707022180e007015000303425102ea81c2300f504000e9401c0c1c9242d895182d50104440c0d1031a2038a02c81c2184c03500510920010924501100c0c00142254101a80c800700368a400994503940b5101c200314548141d100b40d4414540900900c96440b60000712202031100b5181407240814018441d5568404c1c464510208034000860004011070f091860781594541070b099611200c041c0359288555181c42050303c195414136400140307181c099400d803900950403401150031302e250b00148101502c48058105c2e034002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 866454406 1250 866453156 866453167
    0xa060f080612151503030a20070306060608040510020a021002160609030f030f0605060702040e120408070e0a0603020105040302270f0402120a0503041419081c0c0b1308 74
    0x203010001c00500e10b66040800f105400e0416039981c2c1464243c0b00c56000350800c01212a500390004410707000715018441e40b14894800b44100c0c0d04141c01c41c0c000510f00c60070301c400080d4641d0300c850380f43c1c050ba025200f81c914550f9144880812480380036204405078100404400c6400590b40c09440c01e40122042040280301940c0c0f100c04869917058202d0224404483c4001b145a051082480955649104000150403d8009403040c010500002e1085071200c02501140005019424140c03a0050109807141d84495481751070726a903024070791401554000003201d8030074500440088907010b84660346024110b8080c80640079420744803036000001c0f00312044c12448401c0c6524800c00c0d1005200441e801c1a10412086a803c596042c0c2c05601118030800418408001c55080f10f006042c40f9001c007001e0800302e1481c40400c800302c40600c01840000800300d038007141c00000602180c0c2e80241003440e60406a40300404204098981d890140000b900c03801b0004c400030025004458150401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 866455656 1250 866454406 866454439
    0xd050106080111130b070b040204110d05040c0501020d050f041e0e070507060e01020930030d061d0c04030303020f2808010b0f0d0507111006140a060f0806 68
    0x1188070907428040b00200061201c0b01d45154030313641c40030f000284801460504152542d4a94503400740000c0d1240b42d54411002c02040c00c0d20446000c1c41c082e400034070907840e141c1000131901000c1c1c40b405e405405120740801c4207510500c101c2d040503c0388100d40342402e0412684902d41000f41c6007090004e588103401251028428114030702c242d400340e850503034071055072034000180c2d9984610100682c2c0180114103c43e5510700346003024000700c1244d030094030034040c0500207400a83c052682c05000c00901c0c01c1d4400103a410140235a1509008040210031840e1000740c0c1110854181054000c00d0100b8000240f203034000f01840e201041d0309904080e00082440315212158050700d0100000040c2010300075080010180107014500c44241400025440f10f4031301d20889455461081d940c1c0001030401d401400d020107a08013040c106e84030703002c0704014003004000c14000c1105009100c5e03002c030484c1c07402110304415150302e50b5a106074030700d6903442500c072254007902c100e50114070b6a01c0c1c00c605 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 866456906 1250 866455656 866455661
    0x1401090e0117010626120414041104170f1b011407060b040f0c0305010f29120f0114030303061f090312090608060406121401021216080f090601050d0501060801 70
    0x18240d10f000c450b201440f010185d00e241c405026800e000d20542030008203c00145a00071b8454071134191004a0700d404803500d0160940b0440c0c02020303800340c1c102c49543e400c850004041c0c1402c001030085a151041841c10702c014031110000150004a03101856074455403464058a90244540400300704107084a000406072420702d00c07080205030381d40101520a5616010300703030040042008448046051140030048486890750824022030041460024007a5440032524144001500c50342c0c0c42c01c0c288450758482ca0280b0030b40f443d000c440e1300003140300e20f0040103d0b030160000030a403400c0c6048841c0d64080c0b0318100034061090040c2c1d058000b01046504503003002041696588000140c1041009810600040d0205014526182d000d0100604500344a039820303070072a0007000312480d000c091902910540045046520046080c0300342495030152980c031031003194030b512000303659641c401c20700001c2c11140c50382e1a41c0301100400950900b24840440303a03000380c1c0003049542d1208112404d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 866458156 1250 866456906 866456939
    0x73801030308041b0609090b0d02190f08150601030e010b0d230a0809012f0706110a0f0605190e0d020705010912121709071401090e01170106 62
    0x402d00c000308220401107400e0071222030360403903003042e010305003001130082c145003841c041d2005050303a5003140052991084030354003019900501e0b000710006101400300c1e5000552003078040f02d000170340002c030f03400c0c1010580040103a040c442c0c280071a5510001140a0240011800701c1c5550703900c0c55034410f4aa5022160240340241800103015030004031010100d220070740240703000d400000d51030000a9204048500c84802482c01c0001a0700168208510300c0c0100b4014100130103184129004c00004100394045030580d495041e601d841c0000125100d89100d0401070500f544806203000207000d84c0e1203c6e400c018044002c1d440b10344003012031400c50302440d40f06540c580c450b541c8181c100d6030401950020f8402881d0162030149000714101031210115401003072034464400d8035444511400b1501c0380704840e10182c404904101c100039448840d58010031503131804003a8841c03440e5004442580c1155800780300d40050303031700e404050032608140a500980780e5407107190000307100c41c03840e01095 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 866459406 1250 866458156 866458163
    0xc13030614060a050a05032a0a12050c10050304120905060a080a0b0d050a080307030b0d141e0709110903060916150e040209010201060510050a0e0607380103 69
    0x11420b04250b4100070800c1004c0d44800d101d07241c405401d001d40d45001c5000d010102c03801042c09040d402c2140807003003001201e030056400480350040091481480c030040004a4003a13402d480b1001e4030365040c0518201c0880240c0041101003010400250f1210301c030703203403840c2e040ca0b08140d1213845900007151607016031450800110fa000a025070700c40c8910500307800c40ca040340d1580b69490980c0c0e071f00c1d40750f494404021305151030100009103014000e80000448800c01001c6595101d150303d000b40c54030329001d25030900c510811544082c0703d03100d1030b94209a02484002807041c0c40c075040f00c04000c0d1004c810b00f0882a6024000b01e08683c4081020a01900d102000b5002c07081c5048040702d52502954422104065110001c030000758001036805416501603d0241e44c0d0111040140e02500d03540d4409c1d41c114150030b804220b22030b40a00903040030f0505a484c01501c2140408114080c001c045020f04140b4494800700701021507558040c05c05614120814501881e540d400171360f0701c509074010b5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 866460656 1250 866459406 866459441
    0x6110a0803181c020a230d0324050307090b061303080a020f03090901140d020d030503160309020a0b16050a030e120a0c0506030709081614030d080c130306 68
    0x41840860074410001d0040603111080e1814070840c0e0003d603240017001001d0003041ca03100c010840c440c20b80d2046402e000b45074003201c000404200d0010014040c4922040000740903180f100d900c514200c0b110421210018010300d07055052465540c014000c0c4038080f54000820044511001a800c4030701004500440301c854880d184000c01030304001ea01209034810ba0410010f8241964a8030642415100c9003e902100d039140003001c10743c6400b00203c082e52058000415008040c0e004000307510a40712803030303c42981100700340141c1c1500c9003440001e600005c0c1101c03c3c800d034a1108098607007148607050105c400f10f100d485a03400c01c2d201070390a40000c1e442c01038410003820000324241015107400d00070910003075151507a244145903402801c2c802c01b0000041442c05200c0d20110000d03169030030503200741c20001601c00390028201e1190010b05030800b20021014603001c1105500f107030607030711160080d41c0c81400c44120340c1e01180b00420b507070907210004000301e0317044d224815a104000401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 866461906 1250 866460656 866460691
    0x9091f18080d27291005010f0f02070312020a150e210a08070e10021c11030a030507090f0608191104050607020d0b0702031207140406110a0803 63
    0xba000e80b0300402101140203109042d0003a16a01400c9000400e508030b1410741d480f8190584080e440c180341500300713102c1c000000601203c0b0149100300c0c070403a00240c851002128449405480d140e00c040d01410150b04002000c00c041111381314442e00725002072059440200c00c0365111410095045c2040510f6652100b4400002c0d900b0004070000407841c1d6142d1001e40c0c40c00e080514035119012451040240c503002085500b802489884030245000302503680740c290141000359a680418400b80500398075441e0003600381e0051622500400c480ca005d1482e107150a241070740500310251442080028052001a255120b10711010280041e5521030941c0e0a100d4201c850050300700144005070751600c0c0c9142d540581d840200e8045510582d6225101c0e800c900000d40c0c41c81812001030031001d0340008101c1956804401001508010614000203071034000084070f0a0f00000000700000b0700400003030000e07501451442c1040ca01e61411074450280356540c4088079041581c400c107020819018 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 866463156 1250 866461906 866461927
    0xf0103030e09130602070203010f0608010209150705030a0c03140f030910060e062103070602222102061905090102071406070602030417031f0509091f1808 68
    0x4290005050482c1c0100150501c144080c50000c019103004000c00c0d800502181103440a41060300c258481440802c103585c1c2c0c800a10307007c1d50004042c98814103042010074150070321403058607c410f81041c010b5080512610043d0340303011501c41c081d41440091200d010743c028030500100b41009007442141d890b03044c4290010314020001c0c010b604c2072420040300380540e001d40384a40d50b20010440c0c0b03207140e84902142c04031801d21220302070061400000345001c144000398006089035900c0d0003104180c120303400f00b0f1501110031406000c500f0f4141d103484023481d50119074041140f82c0010b201d140341c18088004061120f50311403e003004100c012440e0700345503030140440f40c01046a085070401c00340c4a200000c00b6482580c1c001000a81d0210100d414840101c2c9401800105c142c100c13941d0741403038020080700c410f800209030300c50120801c1c00b048509049000c640501840402000f03960600070101489610f0007015400c11a907c090403052802e440d81e41014042c0151035582e50f400c06d07500c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 866464406 1250 866463156 866463167
    0x2040b030709110d1d150c04090204032a180914030d060e0c040e0118021b06060a140d020907020c0a0611060108010501181806060b0d060503010506210a05060f010303 73
    0x1140e640e860700b605048070180070101c1c40384e46d08a43c94000103000c4d0345404d0004407078011340d0001e80d081d610114000c810071400e10082907088800305203594448041c55405140200c0343e010f546503068040c4080384e02150765401426440e8030401c00905001c1d500c0b0402032640d044405280d44043d01c84404204410722030303030788907004070a1507001481d02e400d180a804a0030010700c900025450244103802040c8050741c150b070b51141c00074240300c04c8440c0700b610b0385503035840c10344a0301d126240840c00050300030042d903030b00340440300050000c00c1100e030681c08020303110100034040e0703080d4080e080b2030003d944e0301d0100341406414103848505803841001c160a00d080c0d01600407203080c0e85440010b02044200007101000c4550030140400e10310352074441a081270704130040c01004942045404a0783c0f4240f00040c2c921154040c40822000790303103030201030995a050310310540103034480e40c01c11451440e4452a8082d0403c2c1c00071a0807048040ea680ca1520074100c0340b0074000d0b042840144101503210 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 866465656 1250 866464406 866464421
    0x1140a14060102030903030927040b010e01050f0f01050703111204171513050a060c050a03152624090d09030c062109061b170402040b030709110d 64
    0xf8030045051200400102e07a880c03045c01d0b1564400d017945001690002c54401840419401c0041c803020f0741d06041ca4440c2000d071003809010100d103011800407909007018041000031050042004000303070152401924564018402a130402c52488166842c2a0b0104581b005046400c10629911417504004040c0c03500104680f28203030300031a40a0717081144050103070340c000e00a0500d648d410f030524644a4a42084404010215030070b21414104080d0004040c101062240d1401e100602d18611200042d4000b801441e6001604d80c40b00700c034481e80c124503041368000500481e40c1c0c29513107900284d40407002d11184401c8441030010070160400911002d1010b2010781080d0540c581141e0321040c2401d502d000c0c0404019031129404021b08108242100d60b143d5034408101502003414040040c5c204c00704442607075200c17154200505486041226a50700c0051a0100e050300c45078200b00140c00038a0f038560f0304d44113040e80403988540902c54080060308481503140d03150304211001003650a43c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 866466906 1250 866465656 866465659
    0x13030b090c010302070b0610170f0105090a02121605040305010609050402010e0d080313021807080403081f090902030c060a0c12050304020d0605060a0f0305010f050603060106170901140a1406 84
    0x10310517000040c00c204003080c0c2124040f04e6020445d040c0783d07402c5030314400c4017023402c000b0342041007031018550410700c5039410386070152400041680c0d90407a0000340c2c0718298a9441c07111039000007850b200c4481e403100c50007455034a40149050307901c0c3c0305c850135a1345036008031801e281d4480920003191380000c03079446403980658603404814442c0c0c6601c1d0940c0401010400c0c4802180007170021552140c1101c010411070040c40e4125040c0104010b160401c01c4608801190500c40461121400041d002a02a41014078806003504201028003e404502000c036018420000c5088183e13131000003510b158151642c4a038000d403c1820900e050a8013405441d007849030030405c0c0800340e00c0c0d00711a42c902c160031031800309140e00c40340b020594218039544501010024584040b041000640281c04280c125040c1803140f912001d04041d240d120a10660300411120014a018001e0545510b0b500c000007900004850041b814145040002141c886021954400794000002d141c9040740741c02800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 866468156 1250 866466906 866466911
    0x30605041b0507060515100e01080c09032d0303071e140301050f0a17012918041e030512070306030c2304090305090a0b130b0f13030b090c0103 63
    0x1c4240c003421501c01c03254041d00c003a4035540080c46160140c100d00001d118041d203054103021034040000c000ea424184801d0008000d100440c1d0101602415141c4c618401000742c080600c24507000707a041c2003e00082d00c0e174040d09441d04111b0300c07018405540701da00340c0d03103480d88194080002007001c05040b40d0400c05100c41481c40a03c0c01c030000d0300b604c7c1990010786410005101010000d03c03041c0103540302d0300304d1581840d8071060100040d0041042490402070010714420a0039120b0f01c41140100403581203204004501300300e5280740220ae800c079005910149014100d94043c0900181c00c08054012035400200440c0c0c034500c140384140d0100c043d00d000c1040609550700c0e40c02040182c80b40f8202c51981700605121092441085004654018410040640c1528001c0c155802070300c0658801c00c0c001d180064000c188404848052421085c0c1501ca0f40c14003030070400d20b1308104c240602c5194203000c0c0107040c0740e175180d0080145004d0501d6003414680034400510308034401e41c42904150 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 866469406 1250 866468156 866468201
    0xe1207052b11010e0304060c023c1f0807091208070c0b18011202040e0a0f0506011b03080a0b06031003150c0c0b0a090c0b0406030c0c0807120905030106030303060504 73
    0x4004020351b01581d2507481c0034244440306000080d45922500ca219800d110b01245801d64161410004000c081141e20390b01441601801005440744015042117a00100340c03200081861041103419440300b03440c20031804003512196071041840210380304a43d0040006003190500c180882c900c070041920074551032403d000189000c294503901d10510f4103108060f03001002e492110340594014140e41800c0340c09500e0301c00f40c050040c004100007456198580404107082c0e510804403003100340703541c0019001c000b5469404449074a802880a203039195140c24041040e035596000310b0041001d10054010305081d81042034401e184001c0070790a0b40d241200703100720140c0184400030030070b80244484a47d41d6840040c107002c0d01d030410000703180701182c11004c00d04000c7c45000d8020343c1c030340e5542080a003490309401e0b5402c880090000d4900c0314144240300011f90001403280d02c01d6151320700300856680d914046402d50359150804c50109450341e005000a05091040201c6100c0d020507100005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 866470656 1250 866469406 866469431
    0x190209030a0b0601120f02040311030d140c0106050915040b0a050d0f080903062e03020f040b0d06050a0914060105100f030e10020a030f0e1207052b1101 67
    0x211a030a6005044680c203000280d07280e03001d40c103682400c4a817003005120180000f5803503030007540240001c40c0c82c110303500401c8009040004184007480469200c0c0801103030203090f4594260803400340d00019640341c000118950321043c480074013402d402203101041a40070002c0000341e6803d40e5400d03029a600300020416683c0d00c0c80c500d04200d030450201e00ca14465414011014801c00c00000e03007510551050181080c0d00ca806801602d2401d41c104500c522070704101c0141c2a41e071b11010b5402917000312601e90500d008c0d44040c0303000303000404400c0507603110340e240002e44108441c00c42c60140d8aa5000044c040001d4201c0d02d03c48a20001c1e090b950b040000055511001c0d2068104005a21001045250080d40000800c06154048541001001c0d10050207540280d513120002428000c8441e1755041c94010491184030003800f0340700c0d1a890104002d595004804255100d109610f8801070340c4441140030903141510385118000c03801544806003a02407141c440c107030103a03d00310011814 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 866471906 1250 866470656 866470663
    0x507020c010c020d050d08161106060609130f06050301110c100b0d050304030c030309080a051b031014040c0509040f02010c08041707050406060c0308010b03040f05120319020903 78
    0xe5080034246050100480d0020814000f00050010140d201e030700303602c0c510b49030005403243c0b0810003080c05c1e981120310184104c540b01501c0f0f4402e0728590182020402c1c6180070700c060700078480054043d203900f46010b501d00d000d4a204114000c0001d540705030510103402c00b0700811400c84042052a4500002c2c002000c0d070f9032030b03a0300c1172034100c0d5514100c1441580d1088105402d43d40c00c041243e448035100e01b8010195048d42c88201d0120741401e00c002450140030500e1018a40c01070050f05a6810700180d1030000c8226861803503040c0a005001c4514204910440080740b8400e595291a464580762500f40d42200d900310fa40b0840c0400100000944081010103000d0350a207000b40044800b894982800e00842e08803002c15280c520300c10428510010302c440460320122000d2100075a5000141d801c00003110002e00015902c00040c02410410802550014070074800c90145603219100d031414180015400182000001b05000031910a0344030750070a11360407802140781c4400940080d5033f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 866473156 1250 866471906 866471923
    0x50415050d080c0a08071208011d0f0406061511060601020102270a051012050c03060a17070f03051c0513030f060f020408070810050c0a050d18061e050702 68
    0x503164000032445840035060083c101300d59444034400340c60300460702d410720241181c0000c40b4000f45401000003281c0c680140440d15038140c0300340c011b41a4507202c03c12180d01c400200144c41c10344d101c00d00060751901c81032022100302c445a54a41440d4009050f0604000015150300c0c11603006126080003281080c020540f0305a40d4011240c5130204140400c00d000090391006030b010000d00ca2a0740c0c120340109400c100b0041d540c804000f6503541d040540501d010599106412062180e000d1008a2508444980c054a46130440b503055176240302d4035078074400c950001c4916030000a00019103420402c0c080c0840c041d60304002d030602c41031302200318401c0340c54400035090f690400e4010060022070742c032041c04000c041e03078259916074540704401c0d0382c0c4955100b100c043c1d00c00d030340f054405601c1604c2150302454039403040310302c1c25841020844d038642001388091100c642d582c1c0c0420020b05403800c0003442601c81c01010440000d5201000603001d002e41403504814208001c1080c0303664041214017 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 866474406 1250 866473156 866473163
    0x911040605071a0f06030c04060e13020415080102040f0e1b0304061d0f100e0a0f05100f0b0a050102010b0f061e12150a081c110d0801050415050d 64
    0x1600d4441c00d041c040420340c601900d1540c000e02031001d0140b10064031310340a00c900130a4007110203911400080c001200c4d401d1040c07441114094001c100009039840ba668044c50005101040c2c9109170040013203044c1496210f103a5980d8002401c002112224010200828165110000d1490601d191610200501a400f0060384000002400700b02596204000040084c2946481c00c0c80140105030b03104810032102030bc03403182203950f10051496005025000105c2c501030f044400280c0d84280e420b5800820442e664004c011489012114a00c6040d502c00e0214601080c42440c100c144800c210050700814110390420722030a80035110404000d6001c0802d842071682d840501e0080c640e00c3c0880010301c000c46000003004104031322211403042c0140281c0d03a0041221601104205050b451803040e48900d41126014010740024081410716840090401c441008000b41c0000d0a00800304c400c0000b0178a880010300c950b0030140304150980903aa203002c0c0e01941040c00081d0048007400004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 866475656 1250 866474406 866474417
    0x1e06010b0405101101022710090504020903150c0702010f17150a0b070303020309071e0611010f0203070810090c09050d060e120d050c0f0703050304030320090102060109110406 77
    0x14030f4a240b08041c882c000034055002151240040032564209130048144200c03210303002840c0013003a1500e801c980e4000c1c152903d400301d115141c00e040c00060340202c0d44003036060003290380d0101d580d055443c845129000700c410050303540c106807002416400b907411134201040b0380801d41e000d9120308011883d4101c0380da0b08085000c800c80100181238075900e504403613000031000c031308102010b0b0160061409005841e05440350729445184030001c01d81303c200f0b50500e060641204008045c0180000c01103521034100200d565560f11020324141da000b0745004000540020070043c0c2d50340840b80880250039041814405000380d060010711038911409070602c202c101412680401040f607005078003011003c000d80e1582900d00646030f103240c1150806110060600000402c0800114111640d5580005445080904c161000c844581004000b2018180c0d2070903101c090b8210310a100301d8901480c24180e07a601c00d20400241440d0069000014503824405212800c0150005075002d5481b586840c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 866476906 1250 866475656 866475679
    0x308150a081906060b033c16030c0206190c020a0f03090f06020a1e1506030c1502010612080306180c031b0a120b041d1e06010b0405 58
    0x103005960164400d444921880c12581640c0b040035500341c62240c0901c504101c80740e40c0c0c26043c4110700c07089650303100318811035440707526690049004038009010000400054155034a17411031802040c1d5032a1024600000180241d80d8540500b601892080c4060030042c104a0040d4007004e03420034400c0f080325103503402484a24070803c000e0345003076007000002110600c2410044e0840c0c215010701d260a035110303c00459068000580e40100551019581020b540b5103001c0344018541400304a52007140c6541d0099045841e0003803c001e14000c4903881102841e002c80001c41042e800281801e40e41840000c104501016442c0c0d01e80580101c2043c2d80c90f611140003400d0700b040c02e142c0d01e014054200a015000c0e4941c0055880f50084550441641208000e4a00d07a4041e582ca50000100c2e00821050754010ba81c004194001d4050070208503200c62142001141c800082145200d620120b1030000024801d0080d880c4031100074041c0c60154108103641a091040b4010340b03000300d40d001e01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 866478156 1250 866476906 866476909
    0x405070203120414160806010608150607030210050105330906190f3e0a0f0605060607171c060803030601080702010c020a060f390c030815 61
    0x222140307040b1240c1c10b100079280038a0040f400c1c00058105110ba40f2030405501d01c4a5045030180c1d00307803180c0500500300c4c0c1c2c1c6030a40c11035460b1001030104a0480c04005009100c0d1541405000e540e4401c0d000b400840b299106e0200443328141d00542c8a0007a094000c0d0f000940019168014024120201d10b0580c0c0404000c855104203040303250417001c0018500e0b0b4904920440009801941c1e503807030300080c00c210084036000980200980c8090600341c00350004600216940a428600208603c0003000d4080c01400c00401c3c2a041d61001808980503081004c03038424940e001000b01c442c1d6060590315101c0143ea003054030040c0c481405c00080c002c0c0003507044c000c20307440040142024000c1580755110340d5129041551564040344030003010910003070041c020800007410b1507000b0b160000c602c0d21040d016040250441c4803481c0c1d2100d80e00e516615034651466030001511180311841c2c28007250003611201c0c10605c8040020b0042200c000a13440350a040e0840c1c003001206008071052030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 866479406 1250 866478156 866478163
    0x70602071b030b0c030f150d0602310303020a02060a051207050a030b03011b0c170f0301031b050a0311060c06091606090806010603110d06090f0506010c030e04050702 73
    0x240c06803201c421054050501040741c49010141d0340304250a80c100e131140741140a181c00180c0300d4500300060000019180040f000c105403c680004002300350441e0705884140482e0b00003010201c518a080300d084641d0000e450105e16650380000088402500d1900d000b5102c106a1400074403034600001d05010300351085056481e001001c00442929003069503000d0b005a00c45a04c41012a0405240403418601071064403024001100c0d03d460102c04171b10304032006204000304403159402e81e600c191802c0d83e05d0015120728004100c0050b6a07504604100f440b03540c400085007003103215164244001e031030b10458034080303907030203010700419002401c0082d84a020f1440011024030482042000700200014440c40919651400001054403600c089540c062940034040d001c0e8040401001000e219a0001c0050300034501c45604203c8002c0001d0b0588503030f07030301541d8480d881d0485480d031050b15114003a0087c909091607801b40407a5a0060003505500e01d100e44110b58480c0050005070090 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 866480656 1250 866479406 866479417
    0xa060c15240f03060b0603130b0a183512070909090c0f152019050c031e0c01030c020708190b0a0c020a0b0702070f0305061803090a0308070602 63
    0x36009031000d15100c641c020b1a003140d0b807206039001410441c210b5030b00c0c2840783c1160b003e000e00600042d050001ea40750b1848804000d850300380303c1c640e52404c0c030031002030710307241c05212500c505003091b05078180c5490122220b131160b0a8100c20440034291007180c11a40d421503c081c005000d0521143c0c0d11403005448031505940168002e604040104042040004814080c0c42c07220401209107600c03074207402d19121601c4500070102d804c90350202112440c01020514440712041102d00c1a00e080c00310505010700b1023405c0301e16600509000f0b101d86010300c00441aa074200c01100c514401c162a00c84e50740241d8209241419070302c2c4800600140f0911468010701000c808940c19143d04005001c40080b0320f980982e141000c0c40c001c40c0740200e00d4003c00e010303031000c0e50082c0700a400540b54601c40503005400b401c1948640c010005448402c0311071140210b0007903000c0c00c502d2410141f96100349000340400142600208100305140c0d41d500070301400c0d00e40049400d03440e00054074054000384210b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 866481906 1250 866480656 866480711
    0x40c060f050d09150e0c1906050703080402120106060203310315060b040602160e0402090105150c190218040b07030906020d02031f08012c010b0904050304050a060c15 73
    0x410045c000f40f030030b0008044140c9881070740d0a40c05a02c007400400c907017074524003a000005001b0400e01c0e0220303100340d03882c5410500052003050407442a890a50031142c45500010158201042c018014481800c10200507650001c11004042118038008030310007180c0401401788103111902201800300d03502c02c401802c007007550b02c1d0341c40d074590801a42d0b840004601580030119107038040b0701070148001990050340d0240c050243ea900b488200415104c89051005000d1024071041c030302d40c1c10410800e00850110f0840d0051100d00340184001c1c07125460780c20384107049140500c00060320700c00342203a00842c107240001c0d4000c500d25100b800b0f0711130040280c52032800407007803000401c091302c81050f0210034488501d03441aa41d05595081c0d51044036000108090301d040308082d080907103010301a040750400005034030150240024a40c0702e0035203044d00c0b42da10109003844a41440c50060000d040070f810414104d00060b61044002c080e00c0c0a2404450b8844284c0c0c41030107d10317400b050104c3c01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 866483156 1250 866481906 866481911
    0x30c0f09200a020f0d0e030c1e0d050313090f0b0409150507050c01140109060f14060a110a0b01091a0f1c0f0803071407030e0906010212040e040c060f050d0915 70
    0x207400302c00406d21310b122403c0601c2405890365030481403400c00820302c0c1020250705091500c0c0c500714108019054417010503100350108002d00c00200c0c42018111014040703140c4005840300e00003403100704550b0704000d080d002d103140c003d4032404141c0d003080140680010715000b04503580c1d44801101d144c01581c40d030810720360900c00710704243ca40c01540389041c3c640300e1200b0809540c0d683c000c5480c070b07400b5200d240d618990a0646080c01d00b4060014192030449040a16003c280c1585c4d941c42c103c0900340c1601d1880020005000000c030b03a01034840325080c5400c003d8100400540000c1703428581c0c021841c802c0c01d040741c0352191460b0b8901440f10240d0090701d54031104070340781840c0d07003280c0c012500740700051002c60342001640c00c0102581c20b0a80c16540e2101d441800300c1c04d00019580150890741503100e4620300d80034804039080104060044541005840d00702480c0180b12100b0b20f400c424240314004850302121a032110599480201000f03001c50340131510304080e08501175404080030a2070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 866484406 1250 866483156 866483173
    0x90606040b121b161e081b0705010f020c0d1a070210050a14010e040c170309040b060f120a060302030d030c0e092401020313030c0f09200a020f 63
    0x1000301e0102449400d9415482c850043c5040c1c94080b28070800703404007411941c0c0071107100401c1c603000701c0f88030340703911410318070900541910b81c1c0e040c540140700400410641e20000e21000c94051019100400742802c01501d00418010003035203460100140c6e07401029a5941c200611034418151145904020b480007681c0c104050000d4551441c046524500350800003c40c0c400c080c103200e00b802c500703002c407051401c60342030803225091442c1c060310550b0300c0b524550000c20307511012591031410409500045a40f07961807800d00c0b064070b110b0040944034040501c03c181a40b03104008881003142000d242d4174031030b51099101d4004183e141c0000c3e4062003200c6103050500d400d0f900c0082d40900d951280c2b6000d10150041001d0350000312050405a4649401d03e55040d0006004491040b01401980d0408426062503d43e11880354400d0701c1861004104110f04000c3c1600c0300007410301034070280646500041a03090a43c0c00b0300c4115644100000c080341106c0c0300340443d00030580401e06491a11 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 866485656 1250 866484406 866484427
    0x2709030203041a1c05040b10050f01081509070504090c0905060d020a09090501091401120302120c0705130212060d05151b0d1b030c2003070506090601080d050f09090606040b 76
    0x1001c3c101e400307c0d031a43e90300c0086216041710f413078504100ca400501e08200c1d009400011500c14a010744105d0f180240394005006558030181d426206850b56aa01511186805100d400fa80c0740c04006d0801d0020200c8180805e40300e100844640750404603026940e010410000c40d01c104941e0700003c1254a49000411240c0303090b040942c2824900381203145590b22002c1d4000703281566400240580e1154400020302c40c1c04901800300d14415070b050303940c62a1f039034010801d170014034a86070b840d85a000480c5000a11419521500500140c40b208403c2d2403503501d86a072403030020151780000e44000005100d070742004080e07032001480707401902d445686900b001009020107400d030110b0070125481071264a84244542c0c0381d00016a61000702c03240e80303443c600f09401c02d1914120090700017004000c011075801c02050b406100c981c40100ba80b503140014090a011903061400300b0020208050f100c071183e918161803d40038222410000c0ea1a107400040240c4982d40c07084002c083d000c101c00a04 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 866486906 1250 866485656 866485661
    0x122105040602010b06310f09090c140d08030c091f0207090209011d121c0f0203030c03041112100c121104031502070209012709030203041a1c 62
    0x2281c040c0c0c2c0007400801c080c04200003c60281c0161240380c065000e50300c1c00340b004410180c0500c0c0e05900d0500b50001e864180c1441d60501c00d41194500d0744d00e0322045030401c004203111600400b006018280850507540000b0701c800105000680801404408204541d44034421203502c103600820a03c60700d60140c1141c803041004500e00005802511400540e901e00f170b000703ca000d004141c4d109000d00e8541030303168250045049045400c03414050803062200c00820401c10030b080c2c800b0442c000d00d21300c840018581441407011108541080c41403021102e405020b0b41d0304582d01101c0001c80c01d1031000454420050407501c00c490344500c180308043c46205901031095458240d43d883e040c0000c05402e1400d40d87d440d81a04283e030410001040801c5000c2401c0203078440b02c032005854a178803a000580742ca9000e03040b01c510b0140c20000d00304100843d0a10804070201d80006022064003924040d4503401584940c1e8a40b40341d10203c400101c00490440c0c105412007944040c4281a42c11540d00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 866488156 1250 866486906 866486909
    0x10e0405010e150a0f050115030f0b04240b04060507120201150b04090e0105090703021c150c031a0306060f030f1006080f1c030c050c10050405011b020712210504 71
    0xc0c007500e068175035031021110740603e83c1624018109066401001e2100b20000c0c5921040210215a2107908041540d10360113043c08807100941e000464950b030700300e160940525039004600c915000c00c410090b0717a4000082c0c616140e0804104c1020300c004120990240c0740d4450041d1745c40c0c03d4103c0c00b0880160307000240058030008030003049010740c244126400c0311020341c2c5055860b44070000400061901041107075140101c101001c1c41e40d2220354400581d41640920303120702680784c2c281026810343c10b128040700e8600020307101c0343c0c4080000104c0d03202d05002c2d22090140b6413110a40404d41c500f00268500342c0b0903070007255002150903000c40b0080c06c540c01401c1e800d0040d240031115030b00c0c1c00104001c0c000421442e4403c0400c480d0320550061203800546400c1c41070600c44d2450075a4103000c14134070058015800303d1945014a0075908480100e0801c003218001040740c1c2c007120354001401c1d02619540307600e0030408001030038030b1921400c0447d0294040c20040b43c3c88840990b02001800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 866489406 1250 866488156 866488171
    0x412061a0301180210140c0a12030501180b060f0f0d1d0601060f020c15030f010e010b07031209060501121502070305030a0903090509070306140303030c03010e0405010e15 75
    0x1815016480816003650040782100d4201414100c3c42401351610f00b8440b041c08442c1e0800c0f544510120f0205661034100706047c070002c0d040200c2030b00901a90180b07100f0415002e00d4100f10f2581402c0c0505002811015003054080e07a40405000781e8451408a4044203c102c40483e15030503070443c42d0070035034001605030400908246110b09542d60352481036108241c01800340c901c1d17a003800b4046540c40900259401184207007400d1781030b551030b04a50348801d02105e055140ea01e240c410041c0070040010fa000c90b50039020800104070240c03480c410ba5002e00d078180b80131030b01d481d5400050030147c40704640241515103403000008021402e090700340c03403041c4661204491010443c4d030701b8089020344d4074040c0102e1010030014884c1e500e07940c0440c0c0d1643c42410300d804401e0701e503400301d4081e0204a9484010a5841909210130005010200390b040d800310015841d500e0600d405621600061080b0b0b41c90a40302c03804101042000e4200844410b01c480403a103088008000c1c040e00000b00381c6651 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 866490656 1250 866489406 866489441
    0x201092105010e0c010c1b0e04120828090201030204090509060405061e060d03050c1203311704030618021302070c0501080606070c0e01150c0b01031502041206 70
    0x1c0400800c00311300d0b080700550507160403044c0d1280b40c4403440301c0c444641440c0032540c80c080700824a0600ca00e40c880c0582d005401840c10307000784220207041108050402d9484004080c8104c21000807461006258444184040b40d00d110502c0103030068052500122442c900b0202001280c810010340140300314011003c90741d02e43ca5107400a043c4030418080f042c0b14403000c2c80042e19509044441d2002c2e06e100f49030452402c140101003e0038542e03000c40000d00100b0000a0002d0840c668040111401201c804150700502c448120f614121680c400101420810044240c1d902d44040c261002075801003018007051080100e111000041a04103d2091654100c0f402c800103248c0300380d40d0400d41c01000700d12600c0c103000c0195510b400050009600c61010403414000442040100c2d0044c950ba80c060001941005150100d0030400100002084070403031400003c104540390b4141165040309181e08912040d2103884041c0c41745410074a0000c6c00d803001201042400e5120202e52527200000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 866491906 1250 866490656 866490671
    0x8061504060b040e0619030614070305090c130c0c050f07090513110f04150914010518160c120c02090c1e180405180609010203061c020109210501 64
    0x80d0802c501650180f01c9881c02d12000250712402c20564071461900309641205034942d480c0d03145415900b070345006a20380301c0c014060044164043c01b40907042454940540030f10040c0c840840c1081800c491000340c21034680090300000c9000d88441d0300d929400030240ca400c0315054681340d03a05d02c0c07903200e0068164a810005035080031003030303107819045a116405041c8100340804204203c001088216481581c540784042c405092980c01c0b8014401d0940c00f159000b10400351000700d16050b48014019940c00a06403003070100c0252960b070000d460405190380c0440c132030341259042c01071000200a00307900050071441c02d8101ca1200b070a24421150907019907500c00310000113016018866070400c40f111240900c1207031600140486d903501c1e000000c280024640002c007500d00958006a1001c43c40040c0c800c0f40c502444400c1c0d00105030700095146044c0040410300e91701041000c034081d180c01c07a840c0c1007107a1148898200a28043d207540150f031211b400300d064000c880c030b1421a882d600e030158 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 866493156 1250 866491906 866491919
    0x11b14030406181404020c15090106170f030a140d0c0503090f0a03021c030b03151e090601261507020d08130f02120316020f0108131203060806150406 66
    0x740f00c01d8400340500310343c1c002212402c1c0700103074103d070101d4041d03402090031840b18054208500361280d0004000802c0b51407070f02006141c501658440e260094000103196101d08000004a550189107890042420f0700c0527806240c45016602000101d40e06004071030b108268000d014600030a4a481510005038080c20503a42d500850740e00200941c000c1c0d00c07800d5031704802c86034400c01d8540d030f4100410704e45a00c0000a082c8030f020003040700e440d4108000c1c003089500301100001400c110000e0038169081900801d9a140414801c8448014040907121021030b100c0c1c4c28074459003049000c4a24900c901c101d00d44041c40215100c00042c4260071408071001e2040c60b074140a0f025136000708542d2821500c944503004070450050760014000350754551060410001070122074019080e201c01041540304200401301c150180340e0400541c2e90910a040c1110f5080280ea2507014401304e200c28a0042d0940c064651030340034504901440c0d08000c1c4910500000020803c01203804010040e01c480 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 866494406 1250 866493156 866493197
    0xa05010603122c01051c200f120415021612050703120e01020405190609120506190e01060305070306050f0f0a0c0509100507121d011b14030406 63
    0x30b00e10142110f40341c2074110324201c1d03c000b0704031061624520f8031380c4c0c0c1d41e03051501411500081c440b0545c0c07607050b0036401180c3c18420301c041040e5460380c1d00d000c2007101001494080c4201254048100b140030804000380d100b0807841c83c4c5610f80017552140300400706c000c2c40302c501800139901e035540c51081040b8a88031300c040351402549600d0b4916000194840301c0700400046900600c0d940d0308010101e015502c00348100e8a5004101c516000107040a0000349108240d50000744e01c01c440121030000140040350782e541c000120480f80c1d03540d0720f580880c0e1018004104942046500e0a1030200a0003404070740102a80e0165905000c603441c1c07000e04102011003190030406090400d00400d450441c41c0c3c01c4500d119416140c00c3e420412844005400d014050100c130010400001d000720404c20240084030b541c200c1824101d03d500c002c2040a0622100351742281d04104481111400e040240000c12044a800101c4001001e031144026035896000d4010107001c00c0f96038008000051028 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 866495656 1250 866494406 866494427
    0x60d14061b09061608040902040806070315030c0b0d0b0418170c0d05031803121905040302100b030715030e0f0d1205370e01050123030703050a0501060312 68
    0x25060f20b241403d00d000340b107051103200310116601d500800c400a1021003500281c0050140f20000d000a814030321009411654403110313001d10216440740030004114244480b41c00c5a0000100903500c0c0204415a00206031800d41264010b16120301501c0202c500c14070403060500c905130000400381520707400c01ca075020380c0d1190040ca42c402d1319a96030f080c0c400d9000d1500040440340c21031840d10780c2d440441c1150080c140c031400110314141040b2446102aa00d8075448035004001c100d20700385074030300944540f140c245500702603444424068240d2810068a4004d102c0008295540760384a40000d01802e81c0d8001441030b8070840c001000d5100c0d010680382d4a920058544100f0f046140700e004014240c01080751002c0c00325a0545986d1440c4083d901803944a031070740d00c540382510703413859104440c0c04820703402c0213a15003001400b0701e0081d52034000c111680c09030500549213292000a01d0300318581c0004207035020741c9c1455000c200381500301c001034a11900d00030b0310105c01504122140e4240 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 866496906 1250 866495656 866495659
    0x160606050112090c1a130602061e07020c0f180a050403083727050601080c01120e03091003090c0512030d1a03030c100c0c0515060d14061b09 62
    0x10134030704000d074411101035a86140f011500b2181440050710518400d40e99a5001c80c0250300305404001c0d908544048001024198216040c9242042c0038001d6036000210300060003050b000402c103000750794034000301c414040c0244070071825140c090f10000240600761800c4000c5040309000c64410214540c9203540d0600c02901c0c42c4440702c0030b038603940f01d107a0b54240e10b88900f5901c1e4014513941c212a10341c40300d00420940d0104498819140c11803400b00140e00459894000c18580290f036a44654004094040c2d42030228558140301c25040c00c5100e903c1000e07901c0940021a03040503605504403400e035a000320410004c0541c0d4605010074080691101c03102d58000b0001001e4000ca284e0120f03a819003d59240004600c401c00824595400013860116a80c0044609840003c060280e00700a903100d00e4201c00f200070f1640d4040d9941004400c241c003d40390740000404545039600300d0001030b03400424036850000841070458903404181e80b1b0a0309005c1520781c50020762072a40494824020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 866498156 1250 866496906 866496923
    0xd0503090312041a0904111602100906140f1b0703120c08070303200a030b0a050d03020304230a170610180f02090303130807080601060c0605070516060605011209 71
    0xd12101c00c10700c5900019695900a585004540c1e01f02042c02c01380108405450302e19551a01750700402040103450483c400c20061821014002e1a41c40032414036480c0244804075122000501210060300038444945814440355040d205c00140010b42039013140e01402c2c607451078035680e60084645005440014107001820044040064400e41c02803900c14510440c407407001005900348600d59105690040020761074054440046c504801440000d100c21104051403011913034004c4d48a000d2403040103240f001c520300080f8503d07050604110061001080d00c22215103420b44c400300d444148582516034400d42001409103000c640c50304007a10010010520108110714034030300039110182c491a102c1e07400b80b194000d44d072410070161180d0740300c240d1400109800d21404920306103440d8058040ca030300c5a40100310041d04003e2480c5e019400c294040380b987c0c0e85d11816243c6100300b450713520032034080b00800010b002c400e51004007580e900344d03030780c035021600d904010040d0740024070b0140500d403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 866499406 1250 866498156 866498189
    0x2102071511070b1b01110a140301030533010315140601021e0c090f0a140f06010c0c0b0712031a0303040b16021504060f052805090d050309031204 64
    0x6120019200d0310441481011030104d507014580d00751000c03040c0034260a030001c81c0c2040029080301120542c0303a5842d01c01411985503840703444e5126112440000801d00c11301004880c08034802180481000c404609201e035603403890038120702e1030003e503004255071401503800c031403541c074246041c040c400580c000e25850404d29034103030240d88000703603044031480780d00c0386412180c8400912510604030b40c20300520502c0c1280c80c2d4026a1192a98482001d42602c1002840d00010400c0b6030031503828604803810000364500f8104e00e00ca5500480d94141c004218207081261540071401d851072603a03000c0c41088020200b00366048400c1201c1c65054100340801d12201d089000501100000b501510001074100d80100b01c2c14203100d001803100d00d10002e002d000150304002071420241075490400e2500d80c03080610800c0e00305003008081100c244c0f181045007980306038261003606900800030740e5000f0041c036150350f40f41c0c8140b000e01d0003401184101030845240390141d07802c50300055035071034008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 866500656 1250 866499406 866499419
    0x10518060d030806190f15030516030504050a0b1303030c0e010c0201050d0212090304090b01020c010509041e020a0f09050a050109150207030515010504150302060d09210207151107 79
    0x850051401e90411800605617401c0c1244d40389050040000519100c0311030708001001a042015518200505040c0010f0240d691803880e000c100d012028070b8006500e844074a0700310f003004054000a021000001d080c01098802440801074031482520200b00c05440000b0036a11410394500c000c1c0450314866419015502500c020492400b43c11001032400023800710000d0201d40658031a403450b4800b05003071242010f544034144504209000030f0540c0031545000905620940d0060740c0216246e84480ca11807600c0051507d0380300c8101001d64485000080c010091050440c809000480c0088005180d0034081c1c2c00006460b01070b55041940c6082c81411402e10325110070420441c071450b040003010800030700050702e40707001c20b0000190951400041000352400000040c1c030b15a020101013006a071a403044a40003d0a9040031446400c54208058000050341904101c1e0456140d0034a4103940400d140080c1c03001104010b04200701510122112132002c81d541702a0303880804248043c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 866501906 1250 866500656 866500667
    0x90a0b040611010b131e0e0c01020f011404110f0306010b0d0c09080d05160807051506040506030d11070b0d020c0d02060705091e1017061e0603040f0203060f010518060d03 75
    0x1191071022103151b50110002d030030084a0000d014207200b1303040302d050b01d29190380c184000901e001c501d100074844441042c43c14200c100b006800148070041060070f0780000c6d00da102c070f480989000281610003940e502c0510314000c2d44100b5140844a00d031140000c800350148ce841825501040c0007042454034061042d120381d441f40000c5070300b280250061400150014004208407813041b0003400c0c3d0408041c86280e403805010300700300d100b80e041c0340400c046a01c00188800c0c02c80700c1c1d0324081a5030729920f8201801c1240c1a00082e41c24080000c40e042d60312000d070000c05c81ca1000000300c541850401100700c0e15248150f403202c0000d0001c0084942628100004440740d84c503280328040070300001c80001d2000e119185010011806265105606810516900d584104255021000b102c0072068003044020329008042c42181c0120201d400c0c00329062800603210341c0502120424140b07440700d00c0240409105680c45680b0301c4202805580480c090580125001307000ca9500f036140d0f40e0706841 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 866503156 1250 866501906 866501921
    0x607050a0f080c030d0c080a0b01020303042a090209090637051026010602100f18050708101a01030b030c0a15080f01140d08090a0b040611010b13 64
    0x6142d401400900d00c1d440080c03009001c04d042c0c8042c00100400c6002000e424003500a03c10030000e40f4007101e1500690b000300840307a02c264001d02024000c61803101c80c038142111000c0306d46104ca40080c0104102607598010210503500f203d8064080d525801005190400040285d51440340103020320068450204c8040050364400c00341210b4948034030220303004a480d0a02c0701c0000342c500d10500265404041c640244a050700341d40c101ca5810144007955440d01c600c55140f895a48091070040c2d80c01c107a2000e0701c0e240320700c03403e000c604440f0f00789965540c1150040c0b400354002d500b0650451800c611551042c403241c40346180c05481d101c8015030081c0000340b4110317054010200c941e402583c038402c2c0c82c0c02409800d228461602c0760600c0082c28000000c04000380c0e220b03038100601201c550385408004003075044840d604d0030a150f01c4e01c0f500d50b00410070b4180e040740c008003002c9112076030709002e041560211f5441d45c0b240702c0100719881c07d0300e2038484515000342c1c40d6080d04500f181c1c030b90041c41 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 866504406 1250 866503156 866503163
    0x62d092a0703030902100c060e0a12110703080c0106440a0221011103060a051909020a090e15010c0b070315030803070e030a0c050d151802040b0607050a0f 68
    0x18140801c3c5c0c002c102c03142c420091741d0340051100c05810040007000c2c4218403603e425032008100c0600c5030380d80c28a0384011105140e00b40099034500e085104820405003000c1d5500000f1141c4801d100805d040c0600814003403a5080c2c50178980346d003101114004004620301038600c1120b04c1c4c1c148081640b41104e0010504400c0380a0a00c0203405a2034030b03641354880e80303a01c100c2e8580c501c11980c4040d0855540c0d650092075280104140915603580380600402d0303450481b00c20b400b01a00d50056041d100c0f59034842e2821500208550141c250006120400c45d005406030b2010390343d50300e1949011360ba40302042804900c40241100c0451003800c41c06511200d0781c200020200007524020f02040e5069004030340710300000041201d41c80d44020380c02c0840c54103070014001c0c0d58166031002c03a00c4000b401aa401180c0910100040c03200020f000c07900340c18502010041188250710848890122510581c0947c1c00c3c88169150b50419008640b640787d0400050607440c4140d64075410748280703aa0054 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 866505656 1250 866504406 866504411
    0xb010e0403050306210d0c0b0a110702090a0608160303020d260a15090207060b09010b0d02070614040b1503032d091801030605060307050109090203062d092a070303 72
    0x22116900402001d00c0e142030136200c907ca00d40d080d203098041200000d04400caa5800e1001020b41c1c000e0010a680c100e6904550050302507444490700d0001f1f219079400045281310f2020005943d203000050501540e009500341c440c0d600d02c00105454141110400000604001f10714901602190a00b5604081d03000d4004c01c0810580145d0180c0d520541c001490096001407060f04005191080340481d0001f0b59410394150314045084800d07000350181d000400c1d400140f04010841c481d804800028540040700c08141041c1c182240e00c1c0b40219a642180403001d4000605882c0000a0360507480d0125001d900c000c5651404544034000d01035030291041040c000c101c0145e54032119400c0c0c145070100910081e42c99070804200781d40d006001140a5080344505001e80d9130b010355504140c03082c418000d6a2912804042002c1d00848056038404486400b0300c110304510091a44848c404e08941072201a2140c2c440d1820403a040080c2001001c1614246165038040310003410042c2d0290500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 866506906 1250 866505656 866505709
    0x150d061a10030e0106050d032703081809070215010621061d10140d1e030f020f2404080f0f1908061305090a0f0f0b010e0403050306 58
    0x4900c1c5000003a44500c0801c0d103a0021001c01e1600b4401d0b400203160440701d50b0f00a805a0701c024142e6848640c40030301a43d010b200c00b0b55242445d09101d002181d022810350741c0d910100f06244580f0240c10021440707010710300701081302c0d41e01c002a040007003070300110003030400c2c0d2030b01074281c5008110900b4000700b0081c20303080303140c5899a40b281c4070050640d41c9200c52034100170984142c15050003001c2401e15020781d042402008015a40350010103003d403001c0d11000d20604080c818054481c1070125071862011142c000c01d6440418248a4807550302141c10f4200c0480f02c1a840d40d2440c03c40346004494014030f84152540d8900b00c682041c0a205590310340404220825140c1d800350010142800000491002251412030508010004c43c0760503100d9040400008180b400076000081c003403074480e0086450355006000d0343c0072155108107800302c030300310500d0052200c41c0c00c0002a200750342c40300c0001a03008a0105601d03c1181e0540e03615103982e490104210704040910414003031140031030302 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 866508156 1250 866506906 866506909
    0x150f0b0603090a03090b191d04180506011d0a0b060c15070e092211031b090f01030302060103080f040e0403050d05010603020a050a11150c070b150d061a 67
    0x210b002e04540c201030520040681809841e50841e0340c401c055507082000702e0407044174005001c842072800c5140c044000c0011074140d00d40a801d0a1089510900d400440d1421400600024803420b125009889403681d0391460040003548030480ba64030450690002820300d19280e03c400d0703880304000c3c201410070010310341c0f01e440c0224010348110100b6071807060028a640100544080381c0b0704503106d1300ca40c07406800c3d018503440090405942c1801d00d50362030082080802d407020244001404a0b8421805002220f036200212082a40212500004148092030049926041c0c0390907800411142e465a9500401070f445102005500f001c1444042844030a0306041401207001f5076a150322005c51504007000c0f1070040e4040410325104101d0b413080c0700c1c0c005056408903038150810b1721a15441421035810111200507100c40b5524507000c001e1056800c80183c2655400381c4940c55031960781e2004012a804103100309580450902004000680d05e03401002501c0f18444075100d41805040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 866509406 1250 866508156 866508169
    0xa170d11042108120f0103060b190302190e1f120308130c030605040c0501030b010201060e061002030f0a050712030c12050a0b0a060305070e0301141303092c090a150f0b 74
    0x8403407481c1014178400400030302000e070150820008007100c41c45414861840400b072110740d0740c4002030103840c04000380070b08805640036180042c08411003200300c0340b0f003140417031000108448241024800c050b00206e0b0b80d40c40980c8000c03000358035807600741d00c0b9210752032920000000d58200325400c0528013000310004615004641c0114420f41909a130036050100140aaa103103e1103241161b141a004104500940c4034040c3c100c80300342c41c10081c05180712000c81c118855802d0b4080200000908a1000e0b6170080c0200403c0b4011300105e80d03001709000007103058a010600c0b9000040c6241d803141045103140c1c0c07006402003403840d070000340d2000d8140030808920b8107910031800320b6615030800840540140da9811080c000702d008205520041030b44104451001d0300d00d0441d2110f44140b0420940100d000c10f01600380f40d00d10b03103410715805003010300c4c00704900b502c00202c001d081c0226110180014030f407a4000d0780040d00380c03902055002c1d0b020050640103c2c0384103044e2644a980c080d621842c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 866510656 1250 866509406 866509411
    0x801060803031006030e0d0e0f060304051b01090f0b03060103020405090a0c08130b0c03060301060e01030b040c060e0d0204090615060e030c01020604051e0a170d1104210812 76
    0x4028640700d2070900b1103101c1c8280644e01130380038075052407071b20715901074081550702101720303503040c501c1c2141e00d200b0105400500d440307600c903042000041030005004c00081c0e217000d020080000c19140410240044551009600c10034074190421002031240c0c1c0043c2c006154410418500181026950800190f90610544018078911780c2c03907040d00345079644004007540c000c0002c3e4103800410050f545a040400c40100081c02d010000b002140075503900b900000014400024490b4955850b410325600181d8250b40846403042c01c980009803103030294005600c40e51380100b1144408000e0340a20001e07011800381140c6136959034540620580c00c08040c00d01030903059441050b004100402e252411175050509419940110104070000700001400400b04105c4052401d18074242482c82d03103010a00c22000700091041c405090001c40c011000d4444440070110034024650400b091b40c20910580c041c0407000038251500b500c86040e03140054101c58411103006181c45180421040141010b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 866511906 1250 866510656 866510669
    0x160224070e010e01020c01080414030403030503160813080702150c0d0912170d020f04090e1507140703020c090a0603051c080103110f0d030329030d05090604080106 72
    0x6140a0180166004500c07210980080c01c00030340071800c050001c1d40c0c618444081c54100b150000000341004031248200745030151120440e6207541d102e290240103a04101d40959101040100291199210f00d0145015002a00012048040646a60b001a48026001d98000800f54912102c144c5110020002107c0c0c00001c1c0140c40d40321800248190220b50003140c1c241c02ca401d035100271a0703070f0541c6132080400d58044281d407451030044c104042d000340340c074201d040d08022400041001080c0c11500e0740c4405082540c0c034100c54081410000c174000e031103400000e0f201c000c9071445030f842c000c028034006010380101c414800381c02002801c445000c45824284075110901002004410001001c060324400e50100c40d081e14054020142d080503c8090000d007405401501280c8030081c400090142c040c00c5010444424113020303014003041141c0ea54914406450001c886810304096036900d40020090080c901480c07004841e00e8000f07004442e88108200030000d6100002d00c2080000c201 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 866513156 1250 866511906 866511973
    0x130203130c060e0a050a0819020d0b04050c2704200405100e01080615010e01030b04090f050607050c0a12090b07050a05071517100b0c01061a121602 65
    0x900f0082c044800b65030340c00540109050758003030124002c04509140c10480e0b0030b407510000e50031400080c100403880e04010784543e04003424407003403000104403101d4040c0b0650340d82510700c5118401d011102c1d081491954000c00d01c01c049030002d54290719908100d0100035428030041d05000024084410544d80c140558810b400208540c003100003415005080c2480604240d06c1d000300c11103035142c01909114104020500d040c4c0440c0e00070741c000c5161400180003004020301d0303483e101003003402e9810260b038540b01d030000007412540300c0c104440e041c900318009044c6d00f2270255219032600e04450030240038001c0d9441e010035044c0c1601f000c1c04149004200a05c0c00b03c603241002400c004503a00a480561070456900208941100d840d510382200030403001e6045c0c2e074000f22881000000d4024081301400010100402d2505401c040d05030f076848540203810048a41404d40140710b81d4510034000034010f00054005502d041000c0714180c01c03801950203c0b404182062400040e0981c5800a040e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 866514406 1250 866513156 866513177
    0xc13200d0b0f01210f06090c020c03210c010204030f1b120804050105220611010f150e04050f0303240108061513080706021f0b130203130c06 62
    0x80340120661840d007a20b400011890301c03400205032516850241115510300342550f540a050b5a101e0041e000d01100200301c0140c4038010400a030100f00c081500520994054042c00d18020a541304c8042c3d09207503101c4e10401c0d10000a003250840c81c0f0007420355600b8400040811803c411240f0500e20941004049103c180382d4080079440c0741d044042d68080c0c8100c0d8100040200c002ca9081d0b038402d081c103985514280031030000c0000d146560083e030040c8100005800745d00542c0c1003880750b011000078420964003d0094003201c00c540580c03001c0042c59507040010302c103903070150350700140540301b078410100300904c4192440d40705070381d14485c541030300ea9a11070403a03540c84400c0170407600b484d0401d801d0904000090408014280210314410001109881504230400460003080c4980070340e044140d81d040c0c081d44070602000c401400030541080f025180283d44600b1070f610710014041408d588000441700001d401c0140746c04040c10151010001141070703441e0060040c401961002c00c00d8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 866515656 1250 866514406 866514427
    0x60f0403270504020d020c0a0b061305090a020105090a1203050304020f1c0605061809014713090506010311010f17060a15050307031d0c1320 62
    0x8500d02046080c108051003101c1c01071101c1030440002c4460840b000350300c9002c0c544036030001788150002010103100d402d260b034003004040b0507d94803498023103840c104029401da080c4003c2e0703503044583c852640c000ca44864015070190000e0b003c40c4001500b005c1034541c80d61511055104001c01c00d40c08031f800030080004528100a40c401c07400b03030a6a83c02c50240794104201303000c21101000601039612040001e40380d4640702051203c002090069040b41e0501c20742150080500700400b00e04044030601d0b104c00c0c118215000d03080300c0c503090721181d0f40829112240c0c824411100e006540162442c02c0d02039929000d004001c1014021000381000e54507503d07042030042c042242d6517040c0583c00c070003c002d05030030002e030038005106050580c0c1c05aa5400005101000540141b0040c400d4400d26614482d446000785200780d140e6101004140c04000b10945172040c42121036503e5072040340300000368140038440c03c502141905001c100c0c1140e8050719214400418854800c640c800304150300c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 866516906 1250 866515656 866515667
    0x40606050411161b0303050903010501050a050d030809031c0f0b0a0f090f0209090f0714030c0406120f0c051c0b0306070c030c02130606020d0f09091805060f0403 71
    0xc000841c0c0400c054031014882c401140900e00000c8004110300c0c00001c04c1c000064180700c005060002c0d040072a03501c902d006421038001c032100701d00a42c03030640045901e0803d20702d9401038070801001400070481c150f0702281c0b105001010a0414003040c0003424040c1d041d0705000d1303841280c100c4c02040000c50301240c1c108490030620034a00c40e05400d94204a45181c1c1d40254050780d00780e00011405154440b40d01c006481807404454000400d0000c01c815021883d420b940608169070341d10b0b81c10824001064101d000603503542c0d00c50101040100000d502039903041010720112880410140d18409200044400c020481d8010841c0060001e44003c401d4540c811130848001007000aa290200800e54030034000303001000744209107115031305043c00744c2c0b21800d0b5690b0040060907040e20320010701c40a049203106240142c0300380d02c1e07120980c80c0194130880f800082c0e541c401d0416450405d202c07000d400700d5a955403107aa8000d280320045503081c402640306c0c9110001d480c480e410a442c00400c0b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 866518156 1250 866516906 866516909
    0x206090601050108071805090106030204050a0b04050f0103020c0109053304150b01051312060605010f2f07090606020f0307120c0614090a050f010605181e010806040606 74
    0x9a08004010300c03090380c00130016900402145044141031080c021216641485070b08241d6000701c40c2d5000081c200e0380b50300100182e60060310280d403880e640340c41c1010079020318000c40703a21030215070311106294426409030541c02c0d0f2000001c60000e1007030300c0d95030070028105048103000040303800380306405404640341c43c00c0340100f0724500c8061500b901d851503510707180041044601d0f100c07000c410241c0e105000390341c8040391400b4002006660340c003d0078448117800348110340c1d09007094000103041d0300441d100085000c298035106801c6900c0c2503034103000100790740c0c10028250489589a0003010400140000c0c00440400165007800d0100181c94201ca84840c1b04565000b000001c000410054004004c03110328100320140304418a041d0000d000740612240c422480e5004000303102e44c0026400031111b0049094814140d009018503013aa0868050715412845207072180c24000110300103254080f440c044941640c1801c440580d90307458003a80540d545d0b80c03025040c0428008144200030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 866519406 1250 866518156 866518171
    0x1e09251116121407081606080a050601120915020f040e01050306101503111602010f0503060a051c060912080c0a090603051f0f0306050c1201260703030c030206 70
    0xc0580740b401a4450080c61401c50081400640020350340c10f1007010001c8101804d189000d032815035104000d024601c0ca03107403148a0026600001080c1064114820103002d154181e55103111500091400e1001d41110b103c1281d102c0c0c4284c0d8960340640303040c8003521035110920b00d2a80d656241c071001003500d00060700414400c0d000203050004201c0d865041b0412500c46003071854120072131035020b070010180b0a48041d070328000002c5404000968515400c000d510036205c450030100301d00030803105d601084420320b030049c0a000b024425803500c1880584881c000c01ca1118010070b450fa1a002910040c00341110441951210000417a800003103c1e81d020207110b0901d03083c00000c0d8030040030340b0094403900091607a00c502098134041c0d400202008001403100340e030150f80d520001d03c03910800d00c0c40141c0d0120301e800d011441c581c1c1030400300e811a500d0b030049401c40c4c1c2d00708030152444030461620315003003004e00040e91409450610a601c000e6010351a01d0f0700201d030301c3c20080d013403140c003c2204 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 866520656 1250 866519406 866519443
    0x5070801021b0f071d150604121209211e140607020a02090f040201020a0b040c0603110f0f0a0903051903030506040e0a1e1a060a051e092511 62
    0x340700903000c003402010b550700a0341d005071094840002e0051b403408a0040160041d80016000c201001072845c01c915091290700c0048a00c0c0181c3c80803507580046021300c1d40d0404041e004222a419640019010789014000d0034107280300486c4c0450042ca052082142c02c2c0440c544060030300308003442840e40c440d081e8000340410101d154001045050020416500f001e030000124080da4802c0009079812a8848043d0000d4285030130101c410300c0300f1313200e088000fa0030f160000140c07202034401d80711513284140740d45003400c00c2c01d200014036400012600b0108000e414001001c1402000f40c02038405180e440300d03641464a007002030640305c00820160066040840500b00204d0014520602c250001c0351461004440c2407804120512400e0140c0f0b40803644042e0300b081c298496450780500b41c01c941c00310755590b4400a04c80d02420281c07041d00307040150200481c2038140f41401c0c035131201d84c0c4c840c1c800c944003040744d030004101c4403000104c0008000c1000c43c0640741c400c1041441c1d000111028 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 866521906 1250 866520656 866520659
    0x207080f011d03040e0f2701090b06010e030a1709060706050718081005071b110f03060c030c031312020312012312192a0f0b0705070801021b0f07 64
    0x183e071745668000c0d00c0300038146a0140042c0e44941840c9004040901a4862481126032106014043c0181c85005d4079803c2c001c00c00f0a150b9805035101402140020b0050540c610007074030703200025105a2248001c0301c008101160f03099582e40010310071070f440303000002070f00d0400c400300030704940184185405d0348205900510880f41d000034440c61010400002140366514030700212403000035100e0414a07040524200000c0000c03049000e40003460a844100580072103004250b500e1000f55240e07904032504002045180c080980116402954000340b0b0314600da0680e03604d880500002d05000058102003040d07858031581c642c0315070040205011800500004400f94441100b080e08400e20403600c6154501680b00b0900800781c86a140e4405100c821403107082a42c0944602054804165143c1c070410f00303041c2441d5402e10070745040c0c0c40c401d620f10b400c001c8846803a92001c0020341d040c1c45080000110300400740001c0113410842800c614842d074442d03118601d0007241c1003540d4850f4000400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 866523156 1250 866521906 866521919
    0x30606020307150b0a0513020d0b0609240c030304060b0103200306012010020304050d03050106170604020c070f08010c05040e0601051c0603031d1801060503070207080f011d0304 78
    0x26000c01e0304083c48400203d201c1d15100045401080c0d030321040d04185009440110281aa03029124000b01c8c041c0c140900300c051001c00c0280c2c4910b440041c1c1c0800b03514082c462540d00440c044987c0c1c07082648252900c00d9154400380b0f9508212412982181c035140d40d4003003943e0600a0f5142c407042e0000c12460740782444201d42441c00b0042080b81006030380a180c001038005103d01c1032058400805440d400c903040724510010b5802110151070754403401c0700142d28076100303201c3c0c05d0489416070349140101c0309261100c2501e01020b81061350158007802900142038007489078034028a119643c0c0a1418a8154058295040c2210141c00e1000a120030801c2c1e03005c45003425400402444d150742e40e003c2482070202c0c200e05114000000700d123484004000c2503000618010603000c0e980f1440800d0040004102c1c203000a4220309248001000040018601940265410035003034010b0781c40340c1e40c1791040d19203040c001b6a461002c0d41e4460301d01c46e0f043c541818246141600f0f40e0051444c243c1000e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 866524406 1250 866523156 866523173
    0x6051203030708160e0d060c020c09041703060f09100812123103020304260309040506030f150619050603130f02220b090105031504020d050d050a030606020307 70
    0x9144136003200d14010b0013201d661254500652104009100c1791000c64039040c103000a1190700d03070702e0015101d40115401c192a24600301480b4940c800f0354000702c0d504401c5542499080a4003072030708907107c42d00002a0b66a10b0754200d100e01544400d1101551410044500d8071003000e42c42058441d0401c402c4a911280b62049580280700c003800700c03a41140f41003030b01d240d5481811503280c110f11801142e001c05501100500c02c03903400003a10441c5078082043c0765050241d0181803100b41c3d1040100d10064202608030345d600210040c02c0d11525904020081d00380b00c0386141c54410f01e2086002c02680d450590110019103709401c2d11034080d040002003501c070311019110301d040e41104c546610401c0070510085240b41c2d0b014040200f10080c1000d0081852084c4011000c0c3d0740c18881226080c2c107080d040e06048580080082030009241140c03000244c101500c1030742c01c011240002004201c04011100f03025a603555059078801c0f100c20f00030b048a0030350b0442c02c219001005100081940c50 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 866525656 1250 866524406 866524411
    0x50c130209100c02120a1203050a06060522080d0201061a030103051908040315061502010b030c040f11120601230403030f1209050102091302130b0306030f060a06051203030708 77
    0x242040d000f540424000030700d0701440510400f40610442c035180d01000b0488011103001045500d0500407500d8440416040d90401d020301400180c0c240142e01851103288176003021509841800810301da1140c44007401d0006070b031000c8026039198841001348001001c0e40302d50a56a080100341594115507580e9280c0405c1805d408007000651340000038007240b0011180190b03030118441e0300c454a518428030103440c440c4224034080c5510b00880010314010700401040010042c0a041c100050208110042020701480000b1980d640c0f40c801e140d999010040c141551000501ca0080c94440c000401030385071060001d480c400d90400005400c944401550143c0354542040d2400240c4080210307203a0140e0607818401070b0800c00194144030f410f50007850040f905841c03038142c02140200f800268490109a000c05d41440401080044044405150070060050a40d040018246c08441c07400f44c0c1510303070100e072940c0c07018200300c1890820881014110004c01542c29407a0214001d0b1101200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 866526906 1250 866525656 866525689
    0x3002011a060c07060c050f151008160501032301080304092d0b060721080117030d02090103021c02120a0c0c020103150816031b0f03030c0f080304050c130209 69
    0x2917032400020403500340440c80304440701038100d54100c02c0c08902242055001c1d150300130380d03c00010000c41c1c40c130300218900002c2c14000c01030010b0a8680001107000744168079083e20b40c5d140b081c26140480c0128500030f0f000b4186080216155030620a5600232649e200340302002c0c41d1210718540d0300c0d4055554501926491407840001c1f07407160480820aa4880e0180c018036154000e081d0554890134490940e400100c0381d5504006aa210000700303c180c507450141000c0d07940103010404c801600b540040c190135606150140c144116182c101040801c6455028060b5802080002210141da151258011b580c100180904649000040c0c41c1220710303900607041540b075a04041c54920015a03030401000040200c441c029a4080b402030400503a01080390300001205c0b900c039216550f010b81505482e854201c80c81034a00d10740d000c1da08180c030144200c4a6112040d21040880d2105000d1341c8228015000382501c000290700704034050f2804000d002207a17106000d24001e40d211030a02d2900c0030310313 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 866528156 1250 866526906 866526917
    0x50307080c09041103010e1503151e07051b0c0d0213090803160e04110904051003230709090c2319080105060315061009080303041a223002011a060c0706 67
    0x441e864214a00b210314200f06001000d08000d00330000d03448001046d000d452002001c42c81801c0c00141c580f5441c04c049a154880c43d00903100e000f615101060410105003030000240401d0f5039603c0c03840030b820807070b203a001e54030b01c6441e60402940c0140215034005412a03080041c00ea41c030440079014010590030702d02599071840010742d00141219075101554016014440e1090b041958a00042840584500e03034007400c00300007040c00d514058054429801000080134a013003601d0280c501425984010000d410000c516a580e103c40c0e4148442000105040d19010b091400705030959102070311940c000ea1003101c8080e05816034942030340c1c11890440d1200034a04400204480c003000c2d58000011ba400000140801c0002c3d4043d0042c59402c00d20306d207041555900705c100901c2d0b20f642c0040c1c2184060300c1c08000055680207841c820741510314000440e4801c1d000c40b111591100c0f481040241c0e40d103840c41208900c03200c0d0300c414503000407689580f61222401030f407510340106200394402e101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 866529406 1250 866528156 866528161
    0x1a0919030512090303060a050a050a0e130c0b0403020103060806090607050a17010b030115050a05160c36060303050915070f050706120c050307080c09041103010e150315 74
    0x5100d01d00b19104840107854140582c1450710071191642d10640e191403059540700800101da0600120b040201c0d2801000b400e4250f05d412032884203884014002c01c40e40c0c2c0645403107000902c1c0071001c14044c2c81c0e2420310b00c0d115411f40c80007500715200303034004420541c016000c00004080010303038254804800c0c50920b481d4280104156a245100d410021681c000c040011070b24143d020007450403550101c42515942c062140c0548040c482c4460b03c0d00000e00400c0405030941c00541c0040c44280b290380c014082690312107048420218500040a00714800300e0030b04461140182c500b20080141d0f00100301280c5150707005015413103482006800b40812191a28003481040700307035114690000209241d000351890800c2e2a240180240710200e1040c2c044800e030030440348103605401080d17459503842c0d0744a2070410b950703103000103000c860110b008220728401078480b8021512400d8101d0401922541858404940c5039001048448000c05008074103007282d4000810701003007102d0600703001054 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 866530656 1250 866529406 866529413
    0x80306060d3c020c0a12140a032406090e0c04050d050312010f0b04170c0a06021c0e2b08210f13201f021504150b04020d05131a0919 58
    0x1d00590b400c1d0301944004a232003030304190986c0012080015242030f100c030301100c0f00241c50f2340307402600803170b0006240c10070300748942010700b03482a81000018000c5401c09660b00005020004200001c031540d0f08042807107a03241e111011000d0250011201c0005654104040076a9900480c032030030190342041140c0380c641c10800d000000703640d8001350020070100d4445c20007039925003001c0355602503164001e0480c00c2c014070803540404c10003401006031a2203414201805034011131003494a040111603071500e000250420014520100f41b04402c0b10241070145084176040343c01031080151150f5041041408020460102e40c2a540007104008001c0702150001d407051443c40c00030b41052100d080342d07038848120f4049c44403000c3c451b030071221440d5215070744108801c0701b0b94008180c00e0301030703400600704140d940100700ca03010050001801c041c0a5280d100a586098806070340020030248050140802030200c07035079001700140c000750103090860001da5540d4150301e00d858503200007616102013 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 866531906 1250 866530656 866530667
    0xb030c040f0609091b0905010b0f0702120604240e0a0b0711032a0102091305072f010b01020d05040e04110414060319080306060d3c020c0a12 62
    0x1d00101d03c0c04002d51810b9240651004640440503110340d048680300084210b603c3c0502c1d4141c07105016107504040741c42030800026003040d0000c80c3d2086047c2c0f030300174025204000c0c0302c0c03007140102c0c148514419110880d40151054450815902d802c11482403552030001801007441d9a2100305a175042d662402c084900c40c40151851225010000e0410030400c148644058070001008485440c00200e0803100d080b03204050740c0780c3d0010404000000050415030090340e00000504000652800c00404039100000300b080c0020000c030901e840c0e04405201b48500001a9004e0005104203a1040b02c058441c1c0690b105880241060310f001404101f400c9110114a10002e04140880407400c050440c40900485001c0d0082c49401e903508c005c2c0c00c88900300341c1c640c0d803c00001442e580780c4500f48490755020000c401c1071180c40d0080c1074652019181c2a0b140c5154120020600074000ca44141c60418400d40c0513440358014050107000c00000300b14140041e921020301c0c0c68414240200b62607 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 866533156 1250 866531906 866531909
    0x40515030a0b0307151e0c021e10170906010b071401021c05040b1f140a080a0f12050301030206160f0204020c0d08061005040513090501020d09150b030c040f06 70
    0x1014001c4c21000200c0410040440b408410582c481c56072041030310301860001b111101031140020b9400d0101805820000c200070009021030071303007081c00182c0301e0210307004003510051100014818461216040075222110ba00f16917514003a0016525200d4140b0f12802803480c00380401d04000503030a0410030941c1210668805119920500b8100032446001410201c60070350300b00007a01e00244a0444280700030344220782004825038482e01300410709a102c0d2010700382e00d0700302c01c003c203010800b18810010b0080d40e42c1316042001c011001403401048e603261503a003540030300400f03100500050b9503060a942032841d0314040d0302c91751000c2d402c01d5800c4904484000c2d4200b07200141181d0134001c040b48042206085482d80c80003034030350310305000319652050320070340000b00c040c4002d115500e0008040302c01a915003d000c2180100c9494450880e440400704060440e901c40c03006040245400742441041100da60801814829030046500d650a40c100248903d507665880400c00480341d10060 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 866534406 1250 866533156 866533159
    0x71205120a02030411010311030a1d071502070b040302130b0f1206100602030c07120507090608070f06050c0a290103110411031b0708042d050402040515030a0b 70
    0x10107810318601c00340c0250700030b0b02c066400e1000c900000000d035019001c0c0031610000c03004040d1a596814225000802201c030f40443d81c0d144114110001040400560002d40308040258410383d400040c041d140a0f400da00c5000d240b0f9050204001598a507410080c400a003207001140d480803880001700c800014036261503000c4001580a0350410002642c4ca1107210001c8040a82a172075080070783c4e403401100c0c4034105591005005200c3c080111040e0389825228408076000d140c1c13200f0708401a07078085d4100b2a103543c4501010403059a40b0070004004000301c0c140140b40040201d01585c444030406009040191300e01050f2054101014a101000c2c3d844203980203a561079251144040040800140c892030030301c0000d212101a101c21a40614052803601c007103c003242000110302d41003098141c980700424880004c001080c91402031a810a44400c1c040d25500140b40106a16075038120a000c1c034810301080c00740751103035194131403000e40640c2c00035225a00c010114000d04401000c95 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 866535656 1250 866534406 866534437
    0x501111f29100e0a0b0a020106080a14010b090103151a03030f21060303040e04170307020c3307140102070305300705070c0e13051005060105071205 65
    0xe814030051007101003008011034048080340180728085845068202c0d00c40d134000c00703990080000d9059400100369208150001150300c59442c11000c2c101040c0040c282c070010660607200081403001e11500303c8400007121801e45035419611a158154080c1b141102c901e5560000745c00c12840058402082079001000c499980d00042592042600140314001000b60b07102d84802240c0748803000340303214410140042d810546003903841e200759180900151140d8007101141b50000c07081c04002c0d48605150b03001030401100010070701000b6250154080c41040c00e0703035403141a50b01140d01588407a000fa5000759180e034140e05200614039144a030403041503200082000402d40c2201c05000c4142134450300407841c4031009408400000d0860240114160000c002a0200d00803000742007058041c0c098070300e890b0b41b42d40c0060a00c9000751a6284a0050480b0003c1004410044458085036401e801e0241d800e0000019259016061004106241201000e4501403045007070703540c02050f09110 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 866536906 1250 866535656 866535701
    0xf040c0503060f13063b0708030a050a050d060914130c05010e1519080a1a06070f02030a0b180a0c0302120a060519230a0506030c180703060501111f 65
    0x16540340c0494091b0240c81040d902150f07015007030000c40d0a500b242e1403200070790304d0502c001e1011921640310000c0101031040601c4104100303107031403207034501800130340700002900301c40c0c061a100319090041100a01070201e042d130750000340e102d440c0e2500700c0f04203003003065003100b0a00000d000315034604035415407010003180301a007407801c3e0050143d0600064030340580d5515001a840306031601c0b040809a03102d50f0701c898400b04c3c00c0440c0101040d9004a00701865001c1a90001342489552001926900901d201b8003007280024410340c1d541801020080078109411b5640d1400c200785840b019103e01f080e0764120200c04024000601070550000d020001460030075175241d046880109a1840c403450000f044c208a42030b8005642c02d0340000b1144146039035014260005000010101a05401000b031080b05648a45207400d4003540c004d0f20500491070211401411110b80358400380c10007040e85a204040c507400b00d046694803c402c14600c00e007401d5100c180d00a405450380301c107480a2764881 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 866538156 1250 866536906 866536961
    0x91110120e100e0d0c030e131b0e06090906060c121b0c010c1a0702031b01020418050115050a0302040f080d0f020609100f0902090f040c0503060f1306 66
    0x160801e600c580b11404016541c21007400981d281e444104074400702d281d100d05100464051400c0d444201c20041c01c080036600885400f00a0310000c40381c112804014881c1c905059400c110b80c410304480940d211802c2c600c58a0019030101006084640504400500300c68010000c0c032005001c01e8494580e59944c11048051268020201d07000074130030b00480250314403c3d8450a619210b5580100c2d0b0300d40081c41810010b265510f0240600003584800c20140c52481c0d9040c4400c3c2c42d15601200050321580760010403400e9051413081071001602d4040144090b28411a8411180007246485138a5800048050f4000d00c16034202003480f031410714000a0341c0c080000c1188440540d03594446600c0300806007030303030f40d1a000c0d9001c9907607400400707015901c00c02c0380d40b06030b03c030310b924590220309044d80d034001c030301102c500b0340381c1c44030301c01c80a0304002c2404801010f1100815094009101c140b4184118100381d61025185030751001e0482c03000e034280b225680004011404041c1c001950807408003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 866539406 1250 866538156 866538163
    0x70c030803010e250f0903150605090603160b18030618011506080105011412070503100608040302120d0b030d0806040f090c05040c050412050c01090801091110120e 72
    0x310760798540c03c8000014800481d01420001c1c4c0b02c0d5034485480246001c40025580d80e000400003c0400c501c021001002c2a404584d00d0901c1d0110b140c0022810300b40014880f0406005205034040e0b440401500040120001d2503402c650403d07288a0300c81704201e00180c03050384c18850003540b5110b18024050b1a409900824145981d01002044858070b54003103400b44c0c010901c20740010440e141c0041241c3e5001e03800004140c0c0c8607001c4145003102c003200c041c40500e01a601040080e0010041003015507602900380080c2c18103050410b480d15156a00965175071001541a850036404a040f1082400c9608500c0325014002d0a03a030074a040054021326100040b100f00d40315074140740c1943c0d180c0e0340b10b20540c40f001e6080340300d000190f0b00b4001400013408031312075040c042100c01c00000810609038007201c44900c0c03144028ac806031101200041070a00250031030000b903458a4010301c000340304100c40180b010341c00e86d5442d000c0c0111800640320400c03500c14a180617401d0000104c00340d02c010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 866540656 1250 866539406 866539409
    0x120a0b01050a090e0a0305090103022101060f0c05030a0f03110c060a05060a03050709020304080c060405030702031b0d030f1e0c02090c0406020a031826011b020a17070c03080301 78
    0x90b529405026500e8002e001925400c050900c07403508200d143c803000c40d200314000d049259040c14007500c1d0203800a915038020840300c1034a4414600da200510150740d2281107a004804580f910810118244e120162030380714016529081c0b19403555401c204034000c0d04120301e03030170f4600212a15602c0e5070b00b5442c1c50b120100c0707013082100d1601001130140c0c500480210107403034100c0024580e10307040900020003036001a0059410172010f11048040c00340c100601c0344905d2040010355220070161041c10715000d80031140380c1d08016641d40d492800d80f0b69141c1940360301d80510b04030000c804c602d5019201480424801c4031020404102d80c25195000003101450768400e0b1603420030b6544610355506a4080c5002e68801038014000d01404280b00d1f03902c0190b00c2d20018001c0b0540340d078503030f0b071a5188403180920407a54900a003000541400c20f01c2000c2d40b0219850b0b03980c0c2c01d0b000c0e8800003910707113400b50b05c000c0c0500e07480d85104e03800280d01d40c140e480d4541e0003100203c0b6140c0b40e003041d484c1d54009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 866541906 1250 866540656 866540659
    0x60503090c0303040609090207082a0d03090209070f0c0b10050a170a0213060503101a0301050609070f050904050a021321080306040f09111503090318120a0b0105 71
    0x4542601001e401c0000071501201c505540b034207441401c0200741d002a500c841404c0c2c40c3e00000b07201401096600500102104a54041007051104007100c810706202c0000c01d92010705103402d5a140258894480c00c5600c42e802c1d1600f480048400c40c07060740c90290042c000341006440104009504400c84400c8040d01d20031688803ca190380c542190700c44038510120040fa5800c1804484c0c0103051039250141c080824500c0865200d4944000c40e14184011104429154171a9107107082881d80c900700c40340c18031044e00240194600a40410390402c0051300e000200503e80481c016158491410380b640400b00800600039400c00001e0480a90006044400c80a904c000d001030f00c059654000d880d04c5128207a0300d040d2030801d4440e500582c000030a1941c02540780c648442508a141c814a45034071703c2500c210f10301c003003a0702c2480400100d4029103440d421080081c030481c0c07800003055400740f6030300100d0070031a5500700020400a40f0b80c2400900c040c031880002c041000450000981601e07070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 866543156 1250 866541906 866541913
    0x9141203070516141f0e0303041d040606090e0703080c160f06021e0601091e150e0703020906030c0a0c140303250e010f02010618090204110f0322080406050309 70
    0x340c800c100701642d46030000f98411704071080c4854018a0040c40002d4607080020240d905060f660045060541d80c04012085004c50705001c100402640784505405840d410400b00300d1110262000341c1d4403141400058681800858071003050355041104042e00ba070341c14150000c140e980e206003450b90000d40941400b502504840da001481c0003d46202c58020b024010140c80c4d10b032040c0c1000809484000c1360038244198581c591600d454007070715102c02929580d200225107400b900600d041c0380035012a04050041190000d40e0781c41509a07a045a0030b00102556100c01c0c0909139007042c04150300910b010000102382c12014008000b840c400d42c00c106c44091a00c2426005c444601c82100340003011521444980849502c1400c00c03e04401c1140000288c00f6294121800c9017112307088802c1e00103866401c0f18085044c40d0040d0703280c6084514890b400e00c00c86455551003804010018125114000602407400502c1b001180d0b41d2600151035603032300c0d81c84a5004115a00031a03e5001621 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 866544406 1250 866543156 866543189
    0x30d020d050c2b150f0914063d0c060b030d0210050603070302040603140705150703050705100f0603032a02060307020102120411010305092e0b06120106020d09141203070516 76
    0x4015601c451042800410624064010004180c2d00d05064890440204903048824045030f03e680b070840209d22403616469a01400d52400740107844104421074002e401031480e0f9075107150001503400c1c0070380c04508041080e640d0440400d1030705500c0e43c80607502c80e0621000000b84040007031803010702403440060b2204075486000f807242070b403803540344030040c40720401188010910400c080c01405220700c1c01d0710546140305610000740c0c0c5400b0398a030440350b1b581e00b0820425800400d00080032203074951000c00d00031a400340a14400720600040e0084400000164185100b035040380c41501d1704008010240c01c05061420782c481c4a5185580132030319000c0421a00c1c42c00040401b265400c144e00c1c0700d062558400701059004004165520342034941e16015130035038032039020700103480180400031215031500400a1420504161100078000144418040ba43da18504005405c50586407082001d0211003822b256100d81213000d0454050404000c00c4440305c060b0550481c5c102032010060b82 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 866545656 1250 866544406 866544431
    0x180b03010602060f130c0e01180506090610020f070609181b110c03030c0313060906120b0d14070e0106021617030c030d020d050c2b150f09 61
    0x244400c0c040c480150380000c0c00907035041e00d404240c030b5000c03042e00d0144881010580e0782202814154000a9131808003100511035060051510780850006c40c40a0041e42080c6000c1072103c5005015140104104060180f1080c02004400c21066000040307c1490350349076001447d07000320f07002d0304101d82c2c40221403080c4000700d8000d100965100c40404820700c0e00c002801e80706007410340100c024a010b42c100d80070990b0b034140050020403005101440ea900200c0c03413640c80c24555900910240303c0091014401d607071388001017003198034000c2000a603010700c0f0800552800000040100346104039248041180404550300049400d041c1410303643d030342c990030141d031212105180280c0d0341c0100042000b61184d01002e24011442480c141c9283c100c1c1000050b056600002c2c40d4403586400044501802c021071081652100d0000c046508006a02a942c040c91180341040100490520940100080d00354042c40061144e11102d501190391040307402c0c4034904901c01c40102c03e15003080f03404031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 866546762 1106 866545656 866545679
    0x90c080706020a050d020609030a0810090f0b0102011a15030a020c060f090f0705060316111e0c0f1503090102090901061110060b0906090d0606030318 66
    0x7007180c0e44c2407503441c21001c55403060856001d2400c000485c40080107641c3c990320300c2e02e031444d003c0e1a400c07401c1030328101d80c0d000710000c0f51510002008411584d030010040c0b02e800c3c0c009001242e4004482018010201c0805801403520000791020b019003200440e030103003040710010308241c0401181450030000729211720100e0110810311003428401c00c07290f002000d41000901c4400e00708400301d1590702020b080c801c5080416810312880c14090581031303035410008821140b626a2a81103030010388662907100407903002d5a1518005400c08640c2c1c2100302c1c8016001e00c9085507407110814203640000c100481c155420b00034802c5c4d50b91090300c03160090869544900d080340e0b40001d84e5003000d06105054044918000b020090451500b080d101e40110445038035444086490120300c0030315000200400302890000c01008242d0042041e283c03100099101c0092940c40d185040340 = true := by decide +kernel

theorem cover : BRFrame.Cov 866366906 866546762 := by
  have h0 := BRFrame.cov_init 866366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 866366906 ≤ n) (h2 : n < 866546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
