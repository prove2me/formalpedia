-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3948
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:08:33.120978+00:00
-- url     : https://prove2.me/submissions/2b7ba367-6a90-4f06-9232-e8d5a7ae56d6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 709892086 ≤ n < 710071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 709893336 1250 709892086 709892093
    0x2b1815110f12040315060311040b0d060207120f02011a1201090c061d03060f0f07111f0c0f1409120a0f06060614120a1b020d030c09030201020c0607 65
    0x44194050759005000e104062010315a0080c82220700c550300509401401d040551308650682c080100700d00070129041d032042c9080d81082140c10001402c0400c00f1015a8521040340d11500c1d007200c03441810000d030800d41d40c10004280d24410703c1d00091024500b200b410601e01010410042d116009501c0140d0a298003507022804080e805060010190384520014040200040706035041007590303640110181804204140101d10910103080e80752918610b1241840d030050401007008164201ea81e01c2c05402c11050010240c980300d10240c03480c11204a00649900441c1c0505200113a850701d04039582c405090028440941d940e6031300e80c14000c000450400b201160b004441c40b5a401220500a103100c3c010206031080c2c03020444180d660205490400c1500740c031140c030303407010b0191a010006c4101c0d401c5e071100a003980020020f40854070900300c03112501508005a006004008020b6058403c1600028190030305000c820b00e140c0c0002d594045503496180200d1001c107802c803c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 709894586 1250 709893336 709893343
    0xa08030a090f1a010e0106110309090c070b1914041a04170c03031608040b131110050306030f070f091e020415031401030b060609032b181511 62
    0xe40e0b00041040788402075143c03000c1c0e440300a000d0202c030b144400c1d000080c0d07030b4007950200c1002c000c21006103081180781001c0244404d0020000049150b0400c10a00080d85c04a07149100315080c520161007071000c0f205000c01c49504900400ca25034505042c0804034038a4202c1d074a98503801807102115a6640c581080b0b0808416070805030080c001c14592070900020002c1c61140002d00344503840001c4c1d10b4412141e0308420303180a04000c038013502140c0a49840c858220b030490145010703560100d240404555120001d4810400040e008400c0c07101501d400d01c0110041450f18000f45410b5050000c0702007101e01c130b4420303402d00315951310000d82c2e108054070100c0f2044c9100101151669510078240f20014090303c0100c000a00d004120071868681c10a900d041e00c0d0001d1014000396074003800c0c44919031041011039410704c41e032030004110b0b0025144040b4200c5100c0b05400c88082c070000050701c902014294080d05075103017203040c000304c3c80351014920711380561300d8041c11840c0c05807400c608 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 709895836 1250 709894586 709894613
    0x11011202040f03170a090e0c07080403080d0f1b0c021c030512010e070e150c010c030605040e420c0a12022a030d050a0c09080a08030a09 60
    0x2295030001c200050b0b0100b00c05542e4089038060280000c00c81444035000046104001407940840e044040610802d0756840c0400c0c3c0c0300c41c0c0f00c0c20591410b8880d4981848581040d070003266011000201100c8113001717030040103150b03281d00c1c1c0188150504460810034101c5030ba4003070300400888281403025580c406030081e80260490001002c040c4081c100203100303502803650040b000c44000300004075a8401c200084c4124800d40c0c0d0341941c3c4501e45c00300304010482d080c8000700e0308010f100581ca402401c1c40341040e084c01c40c0d140016440d144c07906120944240e0032801130301750000001c06032510400c4040310940b582c000d0281c2c0316075a5250b5015140c1c14030500084004200c5000c2192040240008081591040c2c540c4180386a00400110584c8580d800200030900c3d50040f1001a00a000728011543c140000750307420003c24405034030845408856045120f41c881c81034550741c0303030040c0c4000003622803000582008400c68541401c07900c40a421852003551f4aea03481390500128000c2c090 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 709897086 1250 709895836 709895867
    0x513020604030c06030c170403050a140307030c03060501090b090f0619030506030114160818010e0c040b06040605040e1e070e0f030316150b031f05070810031101 71
    0xd44880c0c032801c2005220707429004180109180561b105a6980100340c0e1980402c0302c3c240d520001e5407a945c2c01c6030310341c0200155805200c1a2403800d424030307110801651060009a80000d01100c036140020207688083e0f001c141404100c05091054a900c0702c12240351a1043d9002842e030070305003001c01d450340706058800341c4801c4000e841410443c1e140e00150700a4104500a01c00001c0740040c2802000c8251645548030f81000080c5405a000b20328071a070101c80284400b80d45548824030f542901c3c0e184200d00e600e03401040c502c240e1761426114021440006995003070030039080c884098410310890091005030341c481030001d0a2412070310070803040c00d090800c00c3c1940d030401e01005044103220b460654820190050555030038180002500c042280e02105021911865200d24801c110201490b034400c41d02c40d1038000ca1918100701785c03e030f01143c0e207428040061a41884030202d401c0500503104101800b824020390960381c00242080c3c03070304002050389150030b013001a10154260b00942 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 709898336 1250 709897086 709897099
    0x15030509160815100b0d050403020a06050705120f130201050f0403081218010b060a20030406020d0207080c01120218040e06090111070c060f170903031006020a0f0303051302 76
    0x8140002e0200c1d0b505482055043d46040b00d03100c03854440414031485c0503541c48414140b1150036216280d80000303400502a00580c0d00d2942292901c009030790080b80c0290210740002000040c6002440c5810b42c031460703001d0302c8020341c00c0c445070188800d011080082c0c10031002050f250402d4084404541c01581c0c0042c10954070442e070414050708400c1203408451010b0011014410610180109003580400a1001e4600700021500303880c1c00320b2100245040c4103140313241310310742d200801c02000682860b4009014240440000903d408800e800c41c0e0a01c0d003011300c0300c00d0307640d811981c0301c4110341c9502800b585a228440320560f119007492003066010303092408aa46000c1c010440b580030f0404c540080c40740c01d549040103840b0384140c880062180c074800008128991041100366001281450602401a2440e48040c0f4504081d0790995154200105201c95400448200001400140040c04d01c02d00c040d12441c1c0e440c81c0c07400000e07050503242c0001904060700724100420302c0d940103100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 709899586 1250 709898336 709898339
    0x30b092d0f0103020f0f0a0501110106050301050906090c01110c090703020904050412081518060105090d0b06010e0117070809100c0e031b0a03150219020c09010506041503050916 78
    0x140c0d0341d5003031000ba4050018084007041da030902400320004684080d00020082d0310306401101c2d004140c0d40e01c0c400c155603403c000b084964081c000d4a01502d0014001d0003e42008224542010404001c541c180f1021102c18140401c010445410008044829500507580c1000079006885035000d81c5601c18a003070200f00070400c81d250060300544150f40c2d81100b543d02c159044100c0885a00e01990011103129107590f018900c00381194880c806141c5142013000c204040b8203400600c48045030001820403c0154a5a100810096208003460301040300c00c594142c1210384140604507104101002001039202c000812125070340e111529404c0100d8406254010441340b2089a05c034420301407036100c1041400016002c0482c04030040241d1040f03880d690f14002110102c104940c9056000c0c02980490f030b4010402e079045c141d080c1c01400790301e0442c10401594003016040944282d8080c0310034004002181030f4001d01031114140001c06843e071001041c0703080008643e0b080320340b003000340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 709900836 1250 709899586 709899601
    0x1e05060a09050312070f030c1103070609020d020a0b1c051504020a140d0e0705060301030507060f090b031504050901140a0b011e030b151c0908090a0f15030b092d 71
    0xd17603c0201003650703000c1001d0a1903610440e01550b944400c0302d40c62b4820f200c02400b0892a500048041f440100003015007150b85c5d02107200007495a0040c44c5100d8081000701341041c040d410901070182910b41040710340f030700884100d641c1408140e014000c0b0303030100b81941c071180511030508001c3e00c000181600d4843d56a01c40010f0494092002d00e42e01526200182c1c4e810807109483c140e907480006880204d080840440341060040170000c01c200d820000002d44840400046000e080390700c02040401c2c4543c030500081e1580600b1121041c2e00d8010002c0c4403250f81009aa04456a600080b60405084004941801c060b0040f03501c000301c003043d02a101c076051340c40040c08040603140801c8100000380e04504e580100d0300d0741c000c2421998607a1852440076400820076034070403130195080951601c08190840019040b1405010714040d0902550042404034402083c091400b0310440c00c001c404250210b5002d0040202544402d00c04420384250034502c4070642c450350000c5425141080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 709902086 1250 709900836 709900847
    0x902130603081b010902030a0834200f09090a150e060f012412021b21070b090c0303030703230c091302091c1e05060a0905031207 57
    0x814601d80b00b82c80c002c2c043d44402060054449994004000e800e502d81e003501d50380340c03941c040410800000c90b06a10b820010421103100062202c400a08000c0080949488000c088103c05c0d1029a014000c50711501035503440c803109003610080d01c1c44c41050b01c540c102140b81840165005148a01d0310303c01806682c04c69010024007000502207810310345510f045c02044c10000e001d01c000301075008101401480c494451035200350070030314080c840c80062074001e00490f017181d40d00b500032100c480401783c0061401c01621104081010f01c03280e84103204075002201d845140c4008124401f888001180080b041c0041d103801030014059a540e0716101c2d2004005052651065105d0508441d8031036002142145191280d46064110361514129104000142c884589070100302030302040105555110050000d100214200060a91900520700341c038008c01c41443e800501285a41840d000c00d50002d5029040b6061560000c0c01c0c03e403a041060a510461010b021001010810b1040c2903a020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 709903336 1250 709902086 709902097
    0x4080d0806040c03050910021809011e091b0e060d14010305010c0c030914130606020c030c030c010503040b130c0f0e0612060114060c010f1d010b09010603090213060308 74
    0x4030750820201d14400d034181c00b1205c043da4038030b40a43c09001407112012440d4020454141030700305034401d8034174000001e0005c034000d2f04030801c4002851806d2604402441451b000703000241000d1054494020515034811141a10300301040401c050300461503c40004440440e05500c206102d81202e80080c102184420702c0200c0b0150b1815402e03480d280e10494803407414a0345985c6004801b40360841041c0e606a00e10b8015611402a11407003111003028801c3e10024912038010300011501201094180310f600a07120340203401084164101d0b03030f80201200e074403607480310120300c9540f40c607425007980c9444688000e25800d0082400326450103c40750786411030f03186000301111075407100140254030194250744841075100900500c0f02d050611030031340c1910000b4124504001014250909681e841140882856a5181011240c1840880029504001100a2017480400d00114000710014462001003640d58040ba40c00c66441d00c0002d603d01c00c80a8051000c5500ea0401c08095400b4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 709904586 1250 709903336 709903339
    0x1110020702100207060519110f060621102c0c0f190b0f0f04090507080609010e06010804020604030b0a0b1306030c0902090d0c0605091e0306130804080d0806 69
    0x1240102c80056100003600c1d03041e81d0b4990b075401d0504011400c40185841d03005c1034601170088161224951070350802c50f600391480d4001c02046035040540c140440c2811107550305d5503054000300950007002002420001d0a00d140d1070004034401443d080030100d04141c100c80d170295200740c0309210a440001142103070700c402100c074403000c004440c2c01c000700025600300180280c03107800d2003001100080400703400d000544801c4a403501201c422905115845070308028551030740c6205200c940c5a00c104144d9010070142c88044941d4146040c04240710380050020f4100f00403a0002005c42d00e070070341034500a40d4080002d004078200101c0c1c0801824500d0741e643e0007406070204031081c9400358019802101c3d00312609402c410b051003003102c065803001103100e40064243d8405000269159140320003450b05aa480f903c4044038030030055205600c1d200d00340e00d88441d052030b602c283e9020440303a03001041844001e1a500c2d02c1d25280060b4046c50303004400354001d06000765403090304209902d214100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 709905836 1250 709904586 709904599
    0x60f10020c2b140606040218091902120f130209160c1406090c0a0f030b0a0902060408030d0c050a140a03110c0c030115030506010e1503030a050d0e0606150a1110020702 74
    0x45e8401800220300035196001014889440f450049086c000500d54000c0c480814424032144406100c10a82e40304984421104042c6000c002540c5482000305402c60030151710180440403580008489502c05449443c0c00040c003c03076503009500555148040e0b5038020884441c100303405019588030725049a407500c443c0110a003500c080e1038107801c50415074110f520381060080c20b5464a10304402c000304002c03034150340e61400b80e01598600d0b0203000104001001540c0e01e1903140c0e440350030745402c918032400780007040c0a802082a0030201051582c0c95000b0120307200c0b0000701085005d465640c506142c1c3c003c0c0000c03a0302848001040e0840c0d401401d034024003004520010700740c0003a031584009045508450014000d018804580940004d01030903032001070081c0d1000241103520000164000c2080050040401d19541c094141039004c800d001c1d00715860318201048006142e401c2140d1503d2000401c0071000d800b030318a803034520114808841d242410100c591009500010303050384210b0303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 709907086 1250 709905836 709905841
    0xf020901020114090601060f1b05010c02070b1216021912020c01020307080f0702010908070e060a0b030f0118090b01030804050103200d0903050904020d05060f10020c2b1406 76
    0x1c81410f168040c110b5400140b0b0140e00e050006c450040e40c01940c8020403031605240d4004402e03c0c403489100a00500000030700b541c034a0b0001c2e181c009240d0005030220400d11912140307000c83d0840c1a400003024116020b14845103600702d08160250b500c0e000c603510201c210340709218500d20f11415030f4690fa0200c0784031040c60300040e6030724054110010300401e400c0241c2113400e2069406801c0052040c1080d08806443d80c1c44982412040d822410317000c54a00204002ca1502d41200c400170807801080c20718608044840c130001810501802010305020001308002c0043c583c444000d01d0b402690b101c05550f16850000c3e8568060300c2154002401c000b50481401011210699045201e940d0540340440740300340c5002515441c41c095051000510940665880b98002090602e82036100010b880c6003810422501007282031000340500b0304800d500c0c03143c540024602103e21803c07200c69105400c0361040c48403507142c132552190541e010600c120200b280340740301c010903900902d00b43c41999 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 709908336 1250 709907086 709907111
    0x302070b0702130b06130b0d0f02090303091e060a05030105130606020a032114041202011116050f0102190912030c020d030e04230a02070c051306090f0209010201 71
    0x90107036000180d804541c07009001e12080a07607200c00050741000c2c2005040c020320078101c0008400d10b50100140001c0015481307600300061056100001d45402d00f141002e4648000c039643e0f02508007014040d501090700300b0460790242c08000e200c44401405156a1510b503003000748030350001e00c039680c014010400e00d03144800c104e00a0384291442c95004000c480b8141d1822101c01d4202d4403020640c850f02000440e07040000d0040265886454a441c401401c0500d0640203461b0000201d504591404410141124404088658040b032024162820b18442d0410342d042004c588001521588000743c0c0070f48102c4200e82c002c4094845456240006680d01c0c120140c0001e141c1d0300a00140340c1075040e800510341445a021401d00901d02841440440e40104007200d40340758004840c0c42c107100514000440520009500116441d41542411000d0b40d8540f03007917070031303005081c03040300c8940e0a145101d920394003840c001e06602c0f006020712603e607032003074000707601c841e961500550902146c040071 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 709909586 1250 709908336 709908359
    0x6080604053106050f060108100e010b2505070e0c070c0b0c102d112a01060e100b09030a06050a0905031b01060e0705180a09020c0604030207 62
    0x1841030502815805401c1c102d1116a162003111480700e80c034003000401d0105090340702e26032095442c25000303141e90400d200090501c0c0300040000740c052202c100140160564150090704483d440f1f4511620b40c9000407550401202440d200c4414410084184050040000d120380031108000241941d607100c8644400445c46502c6018007903402c0600200048000000144010141c00c02942c0312400605000e0f82900d414048505006050302c00303554101c504003103100040c2259660030011000081800080d41c09080d28451040042d00d01c9655440c50990780b15150301d40910082100a442e185007140c0c1840503249042046007901001c41c140c94070f101100c07481c82c0014010541080c1d690f8032000071300001810840900d0b240d11500001071010005045804614200081d02410540c1d04074210b940c2e0307a00c0344001c0a1804140b001d410b80040860340606440e44003d4250301c0c0c1800441c02408990380240c080b07501c000b0703048410a102080c55405944254280c030512940c0e1008280c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 709910836 1250 709909586 709909591
    0xc0903200a0b041a070c15020c01020c0402130308030901020c100519050408071704090204091b0806011e0e060313060e0309010e04090f050303071115010f06230408070608060405 78
    0x4014020704c00003503007a034862000c1c1c020395108405180003243c90b1009090a484219038a4000d68060210fa800130760301407040500004043d1000c500b8900310070b0712401150310601c00034042c24400800f0608015080d0122041108190206d691802241c042c4a00418080f98600138030040e418841c1f02d885404c2c00780c00e000301d410012131820321010f500c0d420000d403a422005a1902d00c10400003407004820f0018100800740a0800a26000e60f90800885008407006101c1001804c1c410046180e80240b51415043d000540105030900040819130300c1d01c50740700e0042c0d4404800300030410001c542c524144034540c030919083c800081188102c45da24010341c007003079001c60381e2099411300c0d5040550103040e240c1e000d552101303650340d6103031521411a401500e030300740094101ca810041255003045540d50500c400d040f80100c6600d042680b4003850458002c0b1001c008980040c0d031032440c803111844441400c41c00081c0d82e40c0342c0e6018201c0c0e480d615403140c0c2c0003007426000011203e2410380324491 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 709912086 1250 709910836 709910849
    0x42102030403031e0210061e080703030927060323012f0409021803060907050618030c09160e0105070804060509010c0606121a04030f030c0903200a0b04 67
    0x720042e4041d9100e00c0980303107001c00046110700c1d0302c080d0180301c0c21f0007000300510401c000d030000d1196020240007502c80340c1e0010100350780f1810301000081e40c050740050413a801c001c11004050042c407001ca2a40c080201c0d6070314481d060800201c103001107d00c174030b0090001008842009101452054241d40030440c004a84003032181008140c044060745010000000324035030341c507250b20382d0030320130403608800d015488100ea0440d0781c46850800300a001c0c3c02400071001049240c0ca41400590780e4401e1104e200e500c94094220104039840c00c0000741001c000050002070545403c6610008541210300000001044204a004103501403402c84100ca6000b90f91245490f04040c0c1c142c40759401965114108030180035100042035550ac9030101511010f510240d40c0c0100d42030a902480b010090398250001140c03c2c000020740190b51808010114240030440495408065400302850741c400740c0158207441003c040c0d4440c01c5002c0d1990703207085074101e400a0f240c0e082c0c950b4500441c007989 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 709913336 1250 709912086 709912097
    0x302031b151b0c0102040807030501060501140403080f12130b1f030803090c0904151b0c060f060902070f051b061b07090903181a04030816060504210203040303 70
    0xa4245954011401c1c0b4119050030181c0c079240c90a81c0b12070880c3e101c1d0b03002d88019081f100041c03041040a019070802401709181922504e03406480002a910543c4002043d2110015241e120200040141c841e400c443c42031800300c0d441c3c1007031039104415040c2021640340b294040003034401c3c0ca1103000c1003544d45141240f0b00b02e071030450b5110100ea5001402c4aa42446581950b81540d540d03200b030f10380310354030580515501c010340000100c00c0c0d40c0c03210001c92580740d6290b400075440380d109900300105508000085001030441400100410740d64200110013400028840b050084000c2010102c0d44903008843d2401004031048042205c0509502c0d07100c08200442c8040740e00c848a1188580d05200584403c61760754610380085a01c80c00c803c40200e80200c0038400240400340400001b000d101040d06036aa24045640419208500005066107400300c2d186048150326400c004505070300076010407160525080c207074804408444880c0c1104010602521394500c0482604c0440b2b9140d100c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 709914586 1250 709913336 709913341
    0x3150324180313052b081207021c030f06050307120212030306030a0f060b0307030b040b0a0522050304030206040e09120c100c0e030d0914010905030604081c090302031b15 75
    0x800c5140f171900d01d00c200f0801c642d60410b00000400c0210390000d684525400c0780d030b0f0130300c0004c1c52060402c001c0105066400c0042d2011203202c09422009000c5000d140c00240410140c00310f800420482d040182c00d0701c903051001c140080c18102c004200d9000b04d501d001050402c03142c0a5603848111501505500100c6c1075400144829040340b80304d41c4100800329412041002281c50200f041c2e0064440300254402d05c01401018148280c201880030020300461601800000d03000350701c87d0100d0f0b001c3e01007501400c1885010300070381d17000d550f00508041d5946d80d036405a010001c004c0e2070004003801901d00ea0511003980f50219010780900d2005808056044841000101611440030003440550400000e46590a1046001c1ca40c0c4948810700860f0400100f5004946150758441c14030002000a1000781c1d000160a9800b1f075001030001e40d909400841d250b030142e070301c1c115462221b040c4554041010b4003c0007500394800301c0000b041651a004050381c0d980ca0140f244072101684d00400f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 709915836 1250 709914586 709914589
    0x807050609150903071203050307030f0e0604140c0301050a0f0506030a030804020409020406170a0501060501210203100f06120f050c0a030c14070b010f060309080315032418031305 79
    0x10f44100b1100405494105d40e071000c40c81541d16a510040300003907000800c000145805100300e0410b0341ea070341030801462000c49c20265072031304050000341c09070140d00c4440004607400c21284401c0310000e0001c0c4150700340201e00d800138002e249520380c00f0b03d09050005030f09050014001d881650543e54504c090b072074a8080c000109112070b01640c03c00c0d01c80c040459111b003482e100e01d54280000000300f182e1242424894219155a0420790400400c04030b0f4003092286250402e0220100704030041e83d90311101c0940d80116900e0344500780ca03503c1c81c000051020341003844008418405481070041d0780d4035424941c102c8000700c0d00d40580b140d080c031015041d00c3c0f0a900514070349190342042000400e9000c40394000360824407013210304070685001030180d20b0600d00218010512814180405481580c4400c280d002c02802500107860040d11440700c2d40d020010702c0101080d074401c01c96015480e142582e040981141d4610108840c220301c031282c1c1c0d000204072943c1b8914031213086041c505100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 709917086 1250 709915836 709915879
    0x10306050c0a0906140904020301060c1103011109090a090f0807050601061404030807050709051303021002160f0507030f08032502030901200d090611070806041112010609060807050609 81
    0x1e03c1d03104200080c041105c6c1c40c0c480388015400307800c2d03136212801c950115241801080c0d6803c82c80038040d9041505c1ba5050040e500240e07844c0320402c49840242d55600008400202451000078050740c0400c0d5982c014481440d008244440c001c005a4016030388035081070f250f1201c540f00d0405003485c00c00041000c41c950201622105109270103803011640d41c0c0900105840c000e03121131006501000e014001c04d5010004411952540082541480ca0405030101203e50301c180103082c54109440200800c0410320020010719030010443c4500c1015041c1070700c40782c10888002c543c04114001202d0842d00d0350303190311001e090a90055140160010046034007500341d51030400c040040c4184401180014400d5a03c0e55003146c4d0388200705840c0000080000d11245c440701420340006000340180030b0302103402c03a072181e0084000d0410a03940f20100301c3c0b1071041000d520300755180c10360101d000c0c051600700e28100d40c021402c444400d503c40b000c00961b8840e0350f00e510342c00645200754500303042c1d80c403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 709918336 1250 709917086 709917107
    0xc12090f0c011d09090f070617040b090a0b070801030b060d0209010317040f0b0c0c06130306051510020a0c09110306040b030a0c090915091109040c0503070e010306050c0a0906 77
    0x650814050f59480c00130805a200c2980d5211842c2c0040341d0800c00d0000412518005044070300e0441c00525024148844026015001411031100c0c2c60000c0d040c0130b000c11032015401d5000f400c1491516020a00410b180c10a01085440030b0040d8041603051410b554401c000c20740050030055140d10b1030b0b0300c2408000c2a62184010480b00b840000781686803144844024010f80460310b40d10310148010a007041e8813200b603640324041c00d202010030208800c140c9015294403000c0042d4540300d10b25882c8071400700b9541a40d0002d1038010003c1101c1e404113840882031302c80c481040b071141d00c0320080700980c0c40a0000040c64481400007070544d05c3c054201c10f09084000e819240d40745900c2d101e0030031070030b550b411980789030b81c884c001d56040040210400e29010700402c0c04010464040da1440020900385000c24813941c070103800b00d000c1c04015031503c3c008080c000d0891303410564a08074442009000d1105803100b52a0000041009044a0807520601e4090fa41e0000150603c0010343e1142ca00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 709919586 1250 709918336 709918367
    0xb01020f0a05010204140d24020d020c011b050906181507080c0d0306030213050601030e0f0a14010b0f010f050c060c07050c0a05101103070b0c12090f0c01 68
    0x9000040c100110140481d481450081002580e02c0782001c8003c800c01900703c5440b806a0f01c01600900843c0c0c000c01c590880c0041c80281111450580c0000d00283c040e054900191510000d0b092820200547c041144d05e88010629044603004030800c1d280ca00611003000e4001104000070003005035208020107000400401b0302084071180c0d16080e001340c0000f101150000e100080c0300d000c031402006030003209032152800780030380c80c115808120b201c10030340003543c4d28a4544010036000c2e8001e4100703003488070b10801104d0900c01103035585a5510b110310020b490300c00b60304241d2503407604107004146881d01c002d03002d00000001e4100444050030004c41c0349041000902442181c40010310940c0c1c005c284604589441710b00b80e08105042800c040041440341849540030465501d5400d41080f910015003454400f0f880a580120b080d8401d09400400130300103030301001218207590003d004d0484000700071030b06665501401c1c55907a14090260307101944a18140d9030958032480c80e841c0181e08 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 709920836 1250 709919586 709919593
    0xe1305040305191218031407051506031c09060e090c0703051b032206030504030909050601090812070303110406080103020d022e0807022b17040606140d0203100b0102 73
    0x6824808102c4424070018208a13501c00717803400a056001901c000344105c03e80c4081d01d822055a18a503442e04404c03c000411940c0400080141e9820320010303010052a02c182d04102d49004401054034201e07000381d00200c0c44034001039500c1d080c428090307880b480c0c801b02d00d1482c025180c2c40503201038001c824040209107200b00107015003c8180042c210882515801041450380150305920241480c4c200904241ca00820000440d9004d0400d40403603c6081c07002901d500c0b10001200d089545800903845407042c9461350004110303d100030f0100364003c2d0fa007008003240b4100040d2687c410351041c40c0000d5085c00c0180003610b81055421600c1e031000b001c1c11024040224109004044000c011070303043c10758280410441d80044480740d001010348003818001295106000c12541c40000d0f41060b1140c038684400c800d4003464034003c52003207800c40d1b04801d103468601a1b01401da5402156103803510400c0201160400701b0310241001c2c1d0040c00f6104581e002c104c10380007004405000d81c114803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 709922086 1250 709920836 709920857
    0xf030b061e1303080a0915050a030c05040f1d011208040315090b09060402030c0102070515160602280810060e180a1a0312120c090a060e130504030519 66
    0x1040b2080c039074025441082615100d0440880203804206030fa84100000c184520424040701e40c070008903401480c0508000a0500001c1c504541501841e00703c04181d030488900816040c82245403030f45070054003ca421034681c2c95200040501030b0f9203400070303e9180144028400201804105900d900e0840707000290178803180c0318207100719000e440c0d8a00b650400310922082d800d051100708503804081c002403054a24020100d0319880a8018203a201072011408041c2c1c80d218040b180c0103244c0150081d0f40303074010414004451080d640c00d8805800c81412580d440b02c0c05004441d124540000111200ea8a4101d0943e401c10f0f190003000c0d803004c1d0440c1c0314191403580c1c03404c640c05014030300000100341c0051069003003541c015519580c40390f0f00407086007681004140c2151000202000384a2140c0c54603901c0d01100e0154040d5a80c1c0300d142d044000c80c130185d005c0c100a13140c550450344138141c1d00e03550070701e917045800076900a400034000300464007410003480300c440e0392882c49141407400c01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 709923336 1250 709922086 709922107
    0xa030f021212060f0f060301150e0301060e0609070f0e040f02070b09010510081b06130f03051f0c1416020402030a02041514092b0309060f030b061e 65
    0x41d4072000c814000b0000020910009080c07801c40c04031003480036240704810400d050000b440c107000510502038000c40420001119910905203d0030a00c00034000703010b0307142c544150b1041d03040c04680341401044820f0000b400d040c8074119515010b02c0c19210219400d00100c144009007050340084180a03030200150000601d0303281803a44624842c0d000042c2c107051003a642d4070740342001e51000c085075021045800c0c1c8040c2c030404410407801c9c210b039902c1d601c10350b0034850081415070350712541066082c40c6000052040c08640840c042200516041c200744540e0080b0084881104000700041c8000102045140880004003c40c00c0c50312011a0140260307800103081e68400c849070241c2c190046000c100d018030500d087c1a0b0b060380c40c05c0c40c480c2e054144200100c00c1c0520360055109200104000ca16001c14401740205544c0600c8040c00709190342c20003600480340b42c03181100040808661b40c8441d0310900c070724503094000030441894000c0310644002080151448004111420090311510 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 709924586 1250 709923336 709923373
    0x41a04080d0e10030c050409150503060405010506030c0604060806010c050f0d020c030f060103240f0c110f010e190c050a120501050c2115062101050d02030a030f02 72
    0x5803441561580882c00000e0306100001075040001d81c1410f0800b00050700e440d80000545d801e584204000107261100c0d143e642c21084400d901203901409000240018000190460f80c0f0600056080f01c004912140c1404414401e903c0f40100040c46031000c20f100798818203040c0b136098040c0e022241c400f085030505a05012203900c3d0340000d0b07070004403404894101882560f01c1405407001404043d072450711501e6448803200000a00d0141c01118400035881c3c41e0b000b48490180c45404005888810501400e13070710703c0c00300303030105823142c071801a4014030f0500030b0718a11500741e0301034800704074150180812100c00b4a01120004907404000c2610744810008000504c6240c005030603e01c028141a801c444002d40461900602041500c41841607000b294814411070141c0c0b4031103070b07500010031426811041007264403060010b08210a403020415a2044010080c5040084c0e40e0b280c041142500c64414000d4242d08000a0f003804640680c41d04041b40c1b2050064035214030525422911 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 709925836 1250 709924586 709924603
    0x18050316030e06040b0901050c070801050c090918120702060702120d080a0e030405011202160804080c0a03050a0602130e01060f0e03060615130302220e12041a0408 72
    0x2118000c40c2088181580002d1800160000b40d8550703180900303290808010344290182d55060100002e503000ba420801c1203448000c1c46900001c0101d0b0501240c806150f80c040c012051007141c40201160140440500c1148802c5007400200740f4007140442e90360180d0450f01050342e001000344111005a200c4044d03c0405640d51b10140103184080b45019113108070241c805100a40b5050391680c0c9214008103c0302920b209082071403554008004240203445031418000c0402d2205d1004409c100e0a80040c105403681d003002c0c0c944200d0300d502444a95030042c400500719074000701800700811401d130b00410051422440411000b51200c140e107405240a0b8031180c009000c10410b602ca0344e1380b01c030010f4500170003203000e04180d040540004038400410740f4a800100760004817481c450402d210944021903018080e08000101e41308038003240003030300d20000249414981b168240c0c0e9000b060100d841c109080720300c0e090500745032011214003150803070011001420000403401000c104076800303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 709927086 1250 709925836 709925857
    0xd0b060a05150d0c050c0604020108060a1d071101090803061323060f010903080a030e0705121e031608070c09020d0207060606050c0a0b0a0b1f17010e0703180503 71
    0x80e0350f00a08110b40b002c075403d88403041c040113020300107000d4245012034416001a02464041041d440741780016002c05007da0050440c840403080c40449003884560452003900b4a4450890410102005d58240c0703181060091101c00c0420000e840c1c0d150030041c403202c1803850240040c11a6080303104845d0540d01c0d840603880301c0c0826003041207518024041c40c0081d2001c0c81c00d020305624641e10030415001c1c2c00051024581c0700c0d0342c01c3c000903004003c00c50003030500400003000c1b100d2070b800b1103840d4040700030403c1e402c0200d120142c410040000c21145d410518000304560080765481d900201c2d00040d40484da2903c540c1d0001905500c0c900280c410b00151803c0140d50f0803a500c0c000c422540c040e8880000e0040c144000c400c0064049524444250070084029881e9078201c0444003d00c06141704690000980400700108c0300040c103200b40c5080c20340c54142c842e00b0160310105000009200c0c440124200c1800100790510a4100300344d2040501c10b044141103c0d0342c0c84600750341248880c40d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 709928336 1250 709927086 709927129
    0xf0f03021809280c08060f031018020405010807050307050607110406060806040b010824010c020603130302060108070302100c02060d0e0607030f02030f04060e1005010303050d0c05090d0b060a05 85
    0x60500c3c001000c4148030483c840420010100d001c1c102178500130b0003e00b85482400900410090b64405000c02080103030040410441001e000311600c007400c3d00c803041a8001c0c3d01e0040003040c5035200041000036550002c00a040040c545010014a5407203068211401c3d044580c21855a8945004100c0030f0081900c49050925200044c0804c60b15803100c1d045c10800d1303400070b00c640050180318991007441100c000c0210304900300016240c801c003952000707410a05c000204101c10000b050002c040138440e03803e4844503661040c04565949441c00081d5010740010f070480005409642754401107031014180c181000616000d41c421154440c1c21003a043e040481041070341540f61054607400da40d4440f0031403c50428940e1401c1141008200600d07044c3d49420034400c440080007400c500d0344140030305000660310b92400402541164400005c5641001c14401000b4020300c00d0310340302d00c400b030031070101c0c1c1c6015143c1000141c405020607410030640c0d10041100e4440981c2242180301c0c82a64 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 709929586 1250 709928336 709928371
    0x3060507030506040c0201090b0c13031e0303051e1303090915030b0105010216140a0305030307090603140106270801110324060f0a030b040c0c02100f0f03021809 71
    0x1804180c48450171410116450820f201c8001090320502c6500411039285464039090002442c1c030308482c191f000a050031070807520074000d0365205440304000328800e5409200c1911008581010058200c84401c06e044408000032a003080303181d0700d00d1265000e86401c10301c0c1a40d882c1c60a0840e444200d40c403807884101b031014000d202c42d181509004010070b200400025000c0300390b048940da40e174014600408440b4600c3c000075a5803480141c0035542203419a81c4d41e05080c0750207402003040e44544408241861a8402c502e01e125010904031401611000d4445070400c0080d00504040201c0030b003030300c44150002c030f0514401d1090000504075424883d907030f824010850072052185109600001d0301440034001c80740c40c0e90b400c0d120710010045040b515488003a4040d806850696640e5400a00d010030708450641d0180007801c80034001e4840e10400030104804554401014070070102050100c0010846217110b0f40c01000404001d55911144210000024210311002ea9aa0104101c04280c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 709930836 1250 709929586 709929589
    0x3030c050d0e0a172515290a030809010509041409010c0908010c17190f060e0a050c1905091201050f2406160f061a0a03020319020a03060507030506 65
    0x820b4103a0000c900296828044511041c200b5a038403a17421141c503401950304542084175560400301404c521180078864022034070303902009005400b500801100c240c103014006800d06070700602c1501e8114140500d042d0308800113650550005a045800c1a0b0b00c64446003a4030800314020f0241000b28000314424040c100010525040da40044820340d140001325501160002d0150304095201c117401d40d001e039034084510004400c4424035584441c18010107001501195024100b80c4900c0b480f4202c03240c0321820120225041241c810403180c2003044070750340821640c050303042c43d40014a8210b10f084e0300303000410007230b030000c3c03c088040d85c0d110400e03c02480000c00485501c9a0343d1040042c41e910603100d064000040f07404014000c0300700080e50b1051011510a040c0440c0d08040f8405810546107090002403801c1050380b120710100c1102400945410031b0400100d80d0010000c005059203208003a1949550520407a40038045000000c0050418020303248211819100000e0914200c4d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 709932086 1250 709930836 709930853
    0x7020d060603150f140f090f0d0f0f05121906090f020301091103250521060415032105090a090c0806060319090602090411031f060c03030c050d0e0a 65
    0x80b44804d41400e060010004041c5110710a60142c000f01c05840d0f0b50b242e42040318100381344400120a90700440d1001c45015070000e4a0144002d4542d5800c0a0142e1058084449000710781014103000c2000e4081424544071092480c00484003400006046640f822003004a41e001c40100707820a401100400c5104424861101102c0001048500c0c52410400300c040764207034082c0890022284601102d41244204155621000c07402003641c80c04500781c103100c2407423204940c1d007032045050103c1101c0c41000180900704072075002c1c003080307412401d29040c4c00d06110603815801c10013509010340003c55450021341d0700280030000300080c0c001c62a40000344a580d0080c8400c3c007400e03040041c007407807658403c0140d4000c04845e0000815800303600d401c001911403544070540c000d040a09981a03400d00301d0085018289503a001c4048400c100203a505440c01c0d8410500450100e410010110307001e60401801c4842c9441c0032071409101c10075503070803550000120129603005d40c060300100300352038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 709933336 1250 709932086 709932101
    0x7060f0b090403020a0818131a0103060b120c0d020714010506090402010507030305040f0206130f0f0302010e010513080303010e0103030f111b01030f020a0c0302070f05090c07020d06060315 83
    0x680700d22580740351a840103580c81c50020001408206c0025066402d041607102040c1d0000c0003d140710a80e0a01c070b070f00c2901030b000707882240710011142054114158000d10550040b078001000d051f040031508130540d03950105c0200140c050034810031200b1851440e500c01810102e20544031840924128582c260840e10010800c9001d00340702028440580e0b00319040c1c42500340e05140109080d0350324075000030b0205040303030300079000200480c1d40d01c0342240c942986002e607150200d00040c80355880c0741c0c14120194510029000c5149a910b15043c3e5102d440207000340145407404400c49a42c41442c58a1031340240e01021080c04220014010140c2c45084407030303800c545180485121300d094081a4030383c44594029038005640c481f204c941e5074040e4001c0040000c0445046488a407111000341c00c1c0441e1200031030042c05141e50102d139000c115107440080d00c90250401e41d466460303412030750f0982e001d00000e0364000c030fa648280001815501491010b9031050441c41c0c107046190300f201d01902c569 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 709934586 1250 709933336 709933339
    0x506070206070c0b0612060720031201031b030c0909020a0b0c1c0c0c03120e01081b1303020d050109020a14090f0601110609150708010806042607060f0b 67
    0x101e41403060a660220100000c00c0e0081561303461604d502c0f0000315154801c00719007000d8040c440404c561150090503069116800c6118500c01600c80c0b410940c480c42581600c0d04c2508240005002150210286030a05028459800f80d4251240c80342000d06c8040d074880b03850a91908150700450a0a081010003032400580d441d01708440561541c1c1c541c01c02ca480c4000422903540000d540620031041009041d400c4075001e600785460b818140f141005180d0280c0c04209221340300d07070295100b21107480c401d40100341d41040220141c0e07000380301944003e82041e014a20b02740c012025a454100c103219042c403400000522100e288144030099036079901030039024041c0000031280b51240c050f11580300820180c484015512003006a400362418030360f10080388981d00400c08030000c0020030102105580c210141107550b0390b0011034031403400340140d2415800030404900010f07000310b40506180c500d00d170061b949034909141e030101c540208400340c45160b1240340c00700c618141ca00c2901e001c81130 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 709935836 1250 709934586 709934593
    0xb060301050d0f1e0f050105092404020d0b01080640140706050a030506190e060109080609011514010c0b15060415020105060a0302130905010e01090f05060702 70
    0x940300004030040b80c2c10704003074034040f07000b8001c0d010040d40540e03000c40c0510100641c540100e07507003400c01a20380c4280d01141c103980f8200208000140004090386451001c0c412911030745008403004006240240040b6080300142048400040000c004e16000e09401c600070f150625000c6640d280494042c10b07c0d0f2021554081d8040040c80c100a00a00001c1901900e54500100b40345c09030210b03c2014481d0864000c071940829a154020014000b61803141c0d404e01064072820100200030018030070500c3c00a01c1c000080040040090f0210303844041410038401043d640c41d106410054102c510074051f955600c02c1054001d541c5071400c0140c158203a0b2200164000e50018041020115001d06035440c0c8400158050043c4c0c0e20b4903075003103401361055450301e03034490754400c0c040381d00f450140c09542000d00041c01820030b08038400c2203d40040070300046280280c0d88a00800d0704010644095490f214038280d80c2400740240c0800074801c100e840014000c50803c1c1d410048042c10f840e08540 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 709937086 1250 709935836 709935839
    0x15191e2606150a1103070308071d1c0201030b03070323030c0d03020304150222140f060c070e04112425120801090605010309020603180f0f0106090b060301 68
    0x2140c18140c0419007900340d0342e40b65964092102600d09480d00304141e07044c1e12000a04d4001c00d80d110403c41e000d850681c80700e403c12480f10b8105406080840c17000c0f904101d08540c00e507035900c0c2c00840b03007032240e0042c1000101700c0070300d8020900301160b64006031000a1401000d0b011a03c0140841160f10407aa01550a280301d080390180c40d91000740c43d000405401001040510465010394a0704030344040301196070f00e00e40c401204122442e200380510743e031104e500c005540c43c20785403240b03a580d40080c00c3c1c500900300e80f0100052a0414000490b0318400d00f000814041980c131002030043c1d001380407611020703c0c054200880302c000c00b09485895410000d03201400c6190400360351004501c181004034501c89810901000015400098645402484451001d6400c4101541a160b028809110403902c950056007910417941000350000401c0001407203040d103100c41106200c04540030340301c0034100c04034810700c0c0110382e0b0000506a59518400c00a1065510075a4080c850070742d86a415507 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 709938336 1250 709937086 709937089
    0x30c090902091503070f06030b0f061c0c11101b021c140f0f03150301180212010207171201050a03030f0c0303200d050615191e2606 58
    0x244042e181e40e0310f00e4043c0c5081038090354280a050050602003202042055440f80010040c00c443d9610394090000c1c0310350503030b59040020440b1080e5071504040b260350304044801a0007883d24075011400c101d210007007020300580c140081082c3d0710704a80040b40302c00c01007140b64010307441d01900c2010b643c1b00b80300c0c0440e51580801e024071003580350b05000555100c200d140500921034400e14940b00080050b04603c0034460f0400366001e4440e40a04c070b03c1e5400490113250884001ca100c1c0302514444489110044c40c1880e08403059005030310015040c085959581004500031502c40c0044220100703d070800d0145480015004060442d495503150b0700d107403800380200e00c00003045820044c0140601087c1402074000c0c2c40003035410000807407154001030b048021034018a819595003800d09000c0784062502c2e24001e4100030070030301e00740d00d0881410f0064080f111002040707400d0044485001e180e0840b8880054015220340e254482c203000b15180500c1c415113420803004414800c40c0078820365 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 709939586 1250 709938336 709938349
    0xa0f06170f070f050706050a0e060603070f05061309020c0a03110c0d030c060b03070e060103060b030f060f1c081201121232071202030301140607030324030c090902 72
    0x400b115040141400983c6081100c0e90b20070081c1c003919103814807052059001080c0c0c0141c0d00c01071681d055580716260f00b81016240c0e4030300d10480104c0c941e00042030226140070401019a448500c81c40c055440d65003007040c06903000070b00c806800390050b032081d409042d000140c0c1c2c814140e010005d0700c56181c8040c005054810090406402c120a20709080e0420042c0da10943c030601c1e000342102d024556500c441c0a500f001250310500103070408600003440e0034081c0070780380119110a212a0541e40e88410320510140d03415201e079110800b1458000c0c2c00c155610304a000c5806918019a02c0500881c450087d51060780b0490f84001e4040c112004070b003118000700040501c502c0c04c885092070000141116401004686d06050092181542050014401031816621a0360100c01c0704d04d80441c1603850f8003091140802042440d0080282c0d4a01000204070151103801c0004103240d01e8080d550284081130348019019054680c06d1062118907060b410041103050418441507540794046000b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 709940836 1250 709939586 709939591
    0x122c040b0d0510050c070204050907090e0a170d14190606110c19090c050d06060903020a150512090c01030b150f0d0207061506030e0316030e0f0a0f06170f 68
    0x40050b90780d800305030070440c400b081b6036001e50010300030322403400c180e680f0030b17104c440c039106a2481902d0a50440c41020b004502c008060b500b06400e401c5510422940c0142c0d41c1c4094141200b06d03940c0c2012040920b00d01c0241400f401030900181c0e02c294851420300101c0d011500a802406100200c84205510000e08039a030768506a03880c05d010820741008440000c0d05421055069040c40c050000480d8080f000d0f042d0250500010b1145c56030ba80f005840d19103c50001a41040c074280060080716a0755002d4210341d0988c3c50214500200b400007051200029202c1401c0d07900400904a6290380c58003840310309100441d150b02d900e0030b200041c10340d14494050701e4114440042448919000075905640301e040e04002c040c04402c5920803110100c1915000d05e20120b86801454048031500100b510080e41140c1d44402c001b040a0310140c0d41e184c4071504446d84041c004030818041e803500b1807000020b10044100031650b0781040d90240054682d08003404104903184100148500100d2900340c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 709942086 1250 709940836 709940863
    0x20610170a050102180a050901030201090302011b120e010201151401030b0f090106050c0f0109031403090c150a1b26070b040c170613122c040b0d05 65
    0x11030224114011401c0c40111034000c0d105520200d481852500c40002144440004a5000c0310241d1140c04206640b4000e01000e800586928402e00040d402060302281040d400900c0700303c040714541e2450155002e00ca4008000b400d0300c0b442d40d2582d41c090060403280d5402c0c003461400282040704c5811220140000a4109078565840c0300761502c526042c442c2552010300150015a100c107400741455200304c0c00f1807600e20810070409500441031044a0000e903040d507551000e00001ca0091106820141c1481100d01601d452050155907505074250303c0f010700c0c000280c030b0f076400360390184c101905c0c0c4441e903090719040001c440002c2c0d0403c00f9140000d0203c00342aa0141c03003550b41d00210700030b02000400060300724040c48103000c56604d0010403901d00c010007405045500440755102d8000782c441020586225100c4000155080d0b500c0041c8415490302c400401e00016201c1d600f00c1040b128011f5205158600c91030717608050295001d000d20a9414207400d100540c0ca0340d90f07506c1c0c0034444a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 709943336 1250 709942086 709942109
    0x60702150a050c07080303071106100303030b0f031c03050109060b16110604080708061b0d0b121e010614010903080a02030d140906180a0206030402040b042a020610 72
    0x25644a006800b0b0314030300c6841d0003c1350585070301c9005099684c0d000b83c8e1848081203e0110703501c85a100000c255200b0341d070324004510703030314690b59099003c0c0c27841242d01d0768025a100300c1c11200791801c200000c540e100c0c04c14a034911035005940a412214113800c404101c60424a09001f540311180031103c0790411050881c1e8401540e0824000b22041e88900310f900200000740060070000001328181a40c044005440c841d8882400c1c4c450ba00d01c034003c81484441040c000d40000007201d50011040300c20180c450b810303008054880d90b082c49401d0460754025050701c0d07520381c0b46480900c2100080c003d0004030000403108070001811900c01884001c0030403100040780c00d011031003401a5009002c0c0f8030360070f01640b580106201400c044c101c078564003611910b400941301c0401343d078240640110400140080c2540b540a0000607400104140e0300240c59103801925a2920b11079405140f182c3c144000b24000000c031064156030440100c0000c6520080034400098090414030781210b030b180690707 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 709944586 1250 709943336 709943347
    0x340305090a0503070602061b0306010816020c0301021b01110405090408070501090506070809251404090c090b030d08040b2403060106050a020c04090f08070213050114040b06070215 79
    0xc403001855040b480d0140079900b80090311580000354140a05011940050b001b0300300a4813007071f680401c41384a40000c18030004540b05012682d10403800e42c1c854419a10706c03030040c0c401b007800c0e60700c048641c5036208515240b80c49030040a10130100d94540d14048a40340c2854040000c1c0c9460014001500114000810808000095100142d0f60303a00105540c90351030030050140c520b00c0c046820b02441c1c05100f00d003080b142050300c61802070488021f45280300a052440d03200ca0403031007001d155040f9036a0210310001c280c0b0281c1c038400601c009035000c140c00c0851024107040404260300182800001420b020011305043c0d41640c0c08090780600400c25101c0280361024044d031844840e806003d41c50000c90195803090003030400441c150221070011040409000894255400140114a40e40e81800000d0100340080002500040401c0c5200004000e000202d030b030b0a902c80d0203008407040400840e41024000c10400800448038075081c014590041000094102003200b800d18001a5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 709945836 1250 709944586 709944589
    0x307030e01090f17040e0108150f0930030108030d0b0a270f0905011a060a022109100c0204050604020315040e011803020109050f071503050a02070f060234030509 71
    0xc0d174006100162150034103581d02c0c03001307540b42c1c0655800c0ca06203c4003c0c0010f00030a4071020720a0060903210000c1840b0034190041410f500710bc032180c00e5a90681703014542d0050303e0040990302900d03500e4043c0d695180d402c2c0041d800c0340c1c010b104081c0107141b402802c0120300031142c500c818001c000c54680c3d0180d140551114002e211002105192516203004070301031003015441003610300d61320042200c4102c540400c0115501800761908016480305116000001d020100192820744a008960030b100e0240b0004010780030200982d000250442c00c00070030f43ca0140207180d0411000d48045186040c07041d0300f204401400c4841a00884e21038905100c0e18009522103201080d6039440c9640500c1c642c50000d002c0d011a070026500e41c403031802185da02a00c0420318800300c607c10707458140607222582c02034004d000014a440c010603401e220140206009001407885284540c40c0180d45000c1b454000c3c441000c210440c00940981071851a1b205009546100520390035040403525500c2e03030310 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 709947086 1250 709945836 709945883
    0x6150702012109120305090307020402132606010f050105040504050709051f080a1401060c0c050303030103060c081b1606021605070503060a0e06011502010906110307030e01090f 78
    0x34442c4000400805009814203540d0000c401148182d045812512080508800307845e0159200621b42d003040141d03800525040d401084080140c1400101a959894000014852441070f01c442c08a04540c14a1800000e1001c2130241c01c0200c000b99001c1d0134140020042c0c0998060640216a0f03000400c0c02c050040100300010b01d03000b452442d0030062000380301d040714802512039010a90760070100354400a180680032101c5107040c5034105030307803804400320703001d19204000352004818030742c010846840600c001d502850080c88042248503514600514180c4010b01104280303080c2008604c80065510860300c10060500c00c12250f4903290400d400244100f03011702000790f2115007408100070000c00c20304c08880303044007510f11550310122428180c03041a8054180c40c1c000c2c20041c4044a0920200401581c1d02e1000054401c4150f8a820889000e0300203000a80804801c00c844140c3c0360045d40030713031201c950003400480c40640e00c0b059041c02c2c1c4100280b01013090881c09292500b0b04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 709948336 1250 709947086 709947107
    0x170c01050a021510061b0b0c03071103130e0601050307170903160b0601090b0403110913080d1b020a080d02090f03060c03040c050607050316060615080105180615070201 74
    0x80611039418113240791540100c1145110310400b250b501103030070000420507401c030400c46400c25075000d0143e9440d241490340d0303440140b60109000108415241c1424104003505109001151001c0e1280c02c050100c0c1c0d0742d5000811580c108402002004407080d0710228641d46c3c076105101c28a51902c0309144c1c80d0460048150214240d81e09000c000e043c061300d6a000c0f03000b401d0a0b290801a80d8481039010403038030403800094400c143d11003080e00d1a00b09400c902d54800e10030708034242c04281543d200c0e50154803100d03200303602e81c2d11600044a0182080d110304001416400141000003442d0f8852103e4011103014400c1c0d150b02080c608095110b04540300e5059000806071205490208181480c4e40c20a80d000e99007094002c401050500703141e002c88001541280045003401c0c3c02213101d45984042240840c1c846880b207100180340d0710031b489110801550b41d224115250b0404042c048044200444e000a23302d01c0d03400c0c02082e841c1c030902215014201e8852980c1d075041400141e90b22090b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 709949586 1250 709948336 709948363
    0x1060e06180601020f0313030605060901120f05031e0a020c0118050d020f060f0c0c0a061e0c060f06050909060708041b08060a090501140103050d03020c0a060e010c0207170c01050a02 80
    0xc2c089409945003108000362381c8900800c2003591600d4045c440c07241400d01861069000070360b545400704401407100c0b5201449401202e180001d00c0550140300300c00c1c080014683c41001c2514811550140034903600b0140071b22340455601e804046145065001e0312900e8040e462503071002c015034581d2840c1010100001e88025903e8a480c0303080c1a403603203c040c82c16610700600302810030929161100d40104e8100e95108400054071841041c0702c4200c854010050001216a070000200b03a40034010380c0940340540021264a401d0521114403401015800d5607001002000130b4941c1110740590415005400c41d07001140f100380d103003040700903034100c0601442084108000b5072489e401245c0414401e0000b07000e807251000300c03106010004c2c003004045801420541d689248a6406842c44031850300c200c581190484d01d43c01d0440d201180001101c1c0d4490515802d00340d0100202401050700c0e07241c0f03c10740451b81810340e450b90328480c0541c1c1041400290101d01d40c0c400c10007210040700 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 709950836 1250 709949586 709949593
    0x5060c030c0a0f14070303201e0105060a090504080d09030c151505030a0c06030b0a1a1809010b0a031119121b1b05070e010603090501060e06180601020f 67
    0x441e42042a0000c2c0310207070498041c1c001510a41c00c01300e01040f0300303007280d606843d512420395400c49400b44203042c1508100320341c41038081c01e1103880e031242800b482005003000001407904000b82840300a88894100c83c0b0406e0414060100003610b0b80116042440180d80024409d0241d2400b16944c0d101d490004d44140d0a400031451000c499910a0f100c030b42c00607400c4001740e80c4e103405050711034a4001c1d02030010a041c0c44108091402074202402d400c43c02001588010303154100402c140e004202c10b0070b5540c001150b1241c80d80c10320b104482c2c1d00041110090100c1d890300d18070854601c03c1850300d07004c060321102440e00d41002e40054030a81006103c1e42043c414075818020310086507441c5503841c240c02c24210a204441000c000000070b10b132960740c0356400c002014403c15207c0070305400c0f211032042034400034842c00e07a00d814a000c0c2c01a82d4020a0301c228504200742900c0a582107200c403440c0b0300d02441126a074230300704210003c1070812101429654440180d00301681c04d0814034840c007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 709952086 1250 709950836 709950853
    0xd020312030c0d0b010e010e04050613060605030613060510050d11030c2a2e02030906190204050d02011112030c090102010e06130f1b0303030b03101505060c030c 71
    0xa101e001034402c0f40380102c001c00005000c440116841035035442c0305400b241031f00c2000407990805420803980014080c01d5161030f042c40e03039940002c03100c640d8440c5002542c0032003401840d191070b003460510007000b00401e208a0f0b052800003031003505140700c51428041300150320941149235401c0705e025805d0151510b52139107480f4103690015440f200c3c068252208540315a0200f10b84988642c110b000c00c000180b500c90b40d80520700000071001c20b24015031100d440424031102a0ba40019445803100c1000303400301b400c2c03210003c15040480b940020b80140144030901c260344507030349140070769902460b10402603002c945285042c001c110300600034000300001001803030280c9070000d1403040030a030300800c0100e2402c114240c6440050b81c20381d0034654074403032030400b01c0c0d0300120303e030880c60141c403500780d503d5170001c0081d911a0440e4011030221361540c0e9090020b29041c043d802d80030305218014040c5061400c0341c01040001c1d40541340c8103d9001c030b910303228000104203131458410340350111003010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 709953336 1250 709952086 709952101
    0xc13030804120b0f1b0c1015180c0509010e1c05071d010f060305060303192d080a0e0102040f03080310080d0f0f170a0c0e1c020d02031203 61
    0x41002d00155416200d14010482c1060b440040c60710684070541100c03600740340314268880c0b03544260000300d580e2050304201c0e04444c81c984034620705041201c00c00c58100b441c080010790030101d2007803581151071400034024a9a40c100c4201c600098003441d10320b440951f13603400038081101504d014001d901e2540c609000f04040044c0302410746051180441981e101c2c0503405400c030009028000c3e00444c00b000c00c10009000380c00c200d82119000f01941c0c200008800b0440031090012004800182e8140c4026602d0f00c0307440c006802503d44445a0b4000403a4040c00b8004190180450040340d41d50515890126000c0d4140c0b0007400100c1020914203940b81408005504180d80c5a22080a401700c0003510580000d0200030110b90358503241140404840181d6007a40380031f100c90203000b00161420301c200b00607411580718803030178a40003c100500e00d8000340038011041c20f0301c1c001c200310f1a00080403815951042c00035941101c0d83c0e4880d0380c0c4d0784080b03410701d1201407104d000c241c400320501040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 709954586 1250 709953336 709953359
    0x52502010c0b1612020f041505071407060e12250b040801090213020301050109210204020406022506091701060b0705100c030504020f09070c0b070507030206100b030c13030804 77
    0x1110b0540e561400707a04c0d07044c0183d0101c1c41384001c4012908010001048181000b8103500c21181041c00c00509040d02516403102000075002091410381050405000060700401000b0a0b1101500d01034a4910800d04250b130362003011205802c0b602c1074080030060380c101c1c021420042c050354407a4588656940103000e01800d5031801c100d1045204400503001d040716842587d0481d41c050f034403040281d2508031401040a8880324a40b1103520743d142d1400507031141c0c0020030017400c0c10750050540306180858031000f001d00540c004015440340c4402c00c8403650083e103c0c001c1d1400400744601c1f0b0b0180c80403140c0140816400107201500102c2c0003820701c40b010450700c0320503082c0ca0040c04100c2e1020011001c461088a00075800303100c4588021030381c14420000fa51116460400c0402960681c654007103010302101c0800c0001c00014071001099818400503400c4207101e00c45034815402d000f9402c0282c000240a003000d103070b012503003201491000c0710140c000e41d045802641d8484c0c41e14035140c1d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 709955836 1250 709954586 709954621
    0x20d020f0102180121062d05130c110105040308040c090b030304030818190503100905060a091e060203010f060f020a140c15030610052502010c0b 64
    0x5806480ca001540d02018000c40324002841e6900030490f601c800300641d9042465180c80504d403503007841c0c9001c207420320701c00c042c044c040030007500120b584070400810b494030f0801d0a04c0c882c0c0181507400c04c6991103074030308039180c841048000b00d5511803e440c2110440c00f41402403845608200a102c28141c005a42c1402140a507031455207094030344400c20155400000241c3d0154010403041001c91410b03000340c205401010042502d581c5104c002417000c2d45a81c107184e4185039424070800c120728040102803600c2e481c1c84001e001c04021920384c591a408000c20301d0340c101c0e8507505040100692403000d116500a10040c00c000f01402d0f050500094009024072100c4903070301c82004c13850718010070210004280702c0d4000c106400d4550788801d0808284104d11449228103061070160340e40d01071508044150a001e0f0b20f460f46810740c10005102540707403240c0d040c0801007107031071030310000500c1000718628540e0280d6a02c00c00791004039005e240e1000b002c1d000030003000601c171040c002c0e18068030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 709957086 1250 709955836 709955863
    0x611040e060102070f0303050f04180608190209060402070c0807060309260703031109030307030c02040c091d091002030a0c0305060901050a0e0907030c0b04081002040e0c070f021002 80
    0x501a500c1c1030043e66140994041c4003003c800981c010400039100b07030000e04046003911240c4e41802c0d503c0b14907010030108004145c0700580c0341c400900220000f080859211f54500c1800680551a50080780c500345005e46494069074000810b04188190004040001e020180440701690360ba920010300503e200f000c21280307400c0b190350000780095420050200104c1180100c0c4c035004407903800b41d0044c00742a0804031394010900004403e80d6041c405401c020f802030b1512100710b81280304000131118500d14072428481a00c03c280450314081c02d401d6040310001d0300c4041140c5070b203c6000d103017150b12150181c613640000100030104006802080600646403000d07c099120081000754408007402025000011601c04000000c840b0204a8000c000241038521040d00c0f40ca9507881c0e014690410b120385400000c00f000704103020010640001c007040000c504041c1001401114041c0c00b914045120002207000c0090061041000703020030360081683c0b02c081c844220113900c03110140b4580 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 709958336 1250 709957086 709957109
    0x1905090411162901091508060c040302040f050f0714160807060b04090503160c05090115110c1005090f13050a0f14060d0c0b0315040c11071809061104 66
    0x40c0c2e90303c402e6009800b00c11810701030005240e00f4190350500a080c0181141c469034004100000e4403103003800710303074090405154641da54500f5030041c1300076210b00f40a03103003455241c101003002030740094010b1600304000b4540031104407201140051140034011403008030928400008003000f0701840242681e40c40340704140110703401d000c100011541100030241c003903041000038041c01040b044200c500309114403500d1407999200d40101da4100426001080c8000341302c1801150341e50440001c051149604005100d20410750010510209103100843e044c0200441c020515070341c1c5144044041c00b0150441c0c045c55851030160f0080c00d0143d0b280003115103001000c131450a074078001d41500b46100d1250301368a44a0805000303440b083c0c440d042e10b0000d401403000c2061204040151300400b4040183e00f0071240344010081221003000c1c400f0140110844422a40d10380826420100c03044010360003034180d00145030300050000b001c001840301d0300e0500c120310000790034000345c0151a44480301 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 709959586 1250 709958336 709958363
    0x3020304030915201911010e09090703080d0b061303060c02010903090510050c030309030903150412080a0213030b04200315061c0605071103190509041116 68
    0x240034002025500220008040941341401814070a101100900301c4204039680c0301011100e034a000c0c01010001c90700c40d4101c9401d401c04d0342c1d100c00b20402c038440898200711282021205155034070740511000707103514000324003400d00d0b0003694040908080c015041c00e582d403030509101039841031140400c442c0a4070313062104080510500c07039043e00b10b905880b0803588500382003c0051b001c0300c41c003d140420201300400d01440400b440035502403c140002503498a080000b0181082146954483c03c0c9500c4400c21000c501d42d4082c99042c3c049500740031401340c4808801c080a44501c10354118121401d640000030030500785056407045000d51085d1902ea43e07065404110625001d211135415440001980404030b040094513070048001012521040484580c0e015011299402070342c49035610410804116004144820002007810181d0301c1c01c01030402c07003560003101301041010841c001c03d03090300300c2c0c80300d81c03002080f240c500b41050703110074854001241000400b4012941900351510 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 709960836 1250 709959586 709959599
    0xf080702071d1b041203030e07211205030f0c09010309020a150e03161e050d080901020606122d0f2d0a0209070e0a09270c0b030606040312030203040309 67
    0x2601d05845a0b484074150781095910100c0280c88c00e001c1e100e03928010b6000004050304c0b1164182240c1c440000140b02807130807403c1c03210703000d5401740c41d581c18000100100100951650084e60307014103000b00c0c0c10b4680d0b02090048000f0200140025004020050302085549560840710f080c02c032141d8440440c401440e05240e102c0980c040303000034090810300f090003421a2851802803a0120840f002843c56030b0740000f444042144800741d0311894001140c0a03596818004103510910680300c160400605015450b503d06000690510000e1541c0d515a10249031002005d00721038820212103800b20040b002913250f0855803075030032550b250006140600f01d256100840000780c900041d0484d00115028007411140081550741040410815500c2ca60380300303401d8401800c0080c800184d007098480c2c0b428030030ba1b103243c40c404a003065088e022001613880310007881986c00e1841c9803a1a5180d160119505004680006110b000c1c1219001c0c031103681603001c0c6120368020b40d180e01070191740340d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 709962086 1250 709960836 709960891
    0x60b090a0b1318020120060c070209010503010b1f1403180d08040803010608270606010e150906180a090b0120031605070504020d021803010209010f080702071d 70
    0x840f120700d14211060850240d8042c40d01e00d60380c071845145400801510350305190800d0002c4035110444070000c69038205501302000d0040c09004290002c10805450500241d0481c0c0c11036501e0005c81c1d07108021035803861041445000300c3e8102d0089035128180040240450501403001e2006071250304032510407140300c2d0280d140916000b0480030300c0c0da400d0407011160000001c1088031645404190101943c1412501e5052000100c003d8034950500c00c1c0014100d9a84c100c0080c41800d034180001114001d00089400050003159030503507840c506d07a2000400004440c0c4030794001940800060240c40c690014a08044241d894a0020071008001e000d00b00588012025649c01400152503400345440320b40c9056004d0f100700c80b09107503144001000d036804072020f00d004c1c64003c507945400d081507460303084004000328001d600307000c040e000007840d030074035808290108401c14000c40d001900a0001202a080610040740390880d40c1c19041800da20030b81d40d04000102585500905a0004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 709963336 1250 709962086 709962101
    0xb0405030606060a082e0b0c06011505090f0d02040e03031801020a1d0a0b0c0c010e040c0f180906030602030f15090c0702150c0f0d0e0307050607060b090a0b13 70
    0x2501c403941c0b1a169801002206c80580e044070700ca40042e0040c2d40580701c4a219110010041d416200d03a440c40c000c0001c070706080041c0e2050528040341054115000d070000160743c241a801d0b20390a96030f03d9460005400400c498078043d4019183c2140d0034000a07000c001144600c2100c2001c1154219982c030081c01c07881039180482c002146610824205a94003050340c00080c2c00038441030f007041d203407510500203134810044c041596101c18003100095030001f92205088200316010005918080f2002e094112900000800c0118900c11548040a010515406042854020003026459113850301c000e40c4191199441e0920711000203550010025600c410410064a030340d802c0c1c1c60b40c404000280e04603030b80c12a840b10fa140d4400c100305500002404014000388000c04000d0301004149041150002018040094045900001d030310005103038021114280d80c0d5558030f6446040060007002521500b9600860401c02d001c4403000a401007444c4410480e4a0f84408200c00300000856915 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 709964586 1250 709963336 709963357
    0x304031e02010207060f020a140c03030103061e090809010801290c01021b0706080c0307171504020a180801021c05180d0504060215070c0f0302030c01060b040503060606 74
    0xc000c048000300d0011408003480c411400058149070360340c2e0703c50090b81c0322800030b004010f0380882c1c05075081d68800c00c2d516110b810280c080d0f140c00d00c020141e81d00d038401408054600c517200d41034109004600541040c031009281002c2140325541d240c0340307c0a501c80e0f0306060002e2008000880d00d6560640c180d4410030110441810305c3c3c840d0000304013190054079080d00300b0756080c86001201d06a03406040e04400060000d0302040341441c0002c3c081900181200904620034410400b001d6000481064510b00c0040b50741d070ad40da125614442d1600c106540241c110f1b001188441890350044080901140d440341c0034254a0748500b081d078200d00078146038203810b98009540a40d107410940c0300680006894000100c28080c90561318502081c0d11108030000390b000400308050b540c103000403010b19500115144181c180130300020944103d011029203a2044030040b1070405000300201c8604040805c001c0c0105c03607590504400c15081803180038042c0c0200300c0014403030725000c42124a401c42 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 709965836 1250 709964586 709964597
    0x23030a02010f050f04030b011701020c030301120c09020d020d0e4213120201021801110708060106020318040e28050a0632010501030f0f0c05041703030403 68
    0x101900115001011502100103022040013881c2c00c07075182800600c0914003900d1040010b501d0020704c21508154007078080060791050000c020750b000b010007283c0c11522007142d6109070105508218a00c0c2d122580042d103a11f10014054030810000d8001e400c000c0031107542044100d406a1486446080c440c0c1413070303c116014400024011411162056150801020381200c02d580303490080b0b5014041d03a15044840b44d242d07140082244658078842e080845100039070400c1a100d00510f0407011880703040713060003101c2905042c00002084094010b0410704200c03501940e40d040d01a407281d1190b40c803044407080300f4a82c48040d081c6402030b203030a0030aa0004018007903d0410303e8000520844160301c424480a1034000481d40800c46144000d0140c10006059456140081070240b124001d09002c0400074022034046040644000d0440b902804c01042051000c00e20400030200601001c3c0b4052402001070411036124001d001900d03007014111504000d8500d0f40d44e94be00080b034000f0001074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 709967086 1250 709965836 709965853
    0x5030613120f0302070f0b061914010311070f060501060f021c080403051204030203031806060d021e150306010f090803071509121812052a0a06092303 66
    0xd104042c001c1d5a80003601c1c005040000c55038440520b0307100301400382c8400c119070b01401018074010700740205441c20140c1141209140a07000501038600740c402d54189581d80300e80d40314010b41442180e1900c3d0b80b000e654800107080f803070140300810f420f00603c0c0c0015840c00a400100b800011884400c1c01ca40c0c0c8582200803001004690b810780080044041001c00e000242d000003141800c2c42c0103901c01d8020b0340e02d924000c00c91f18021200074441034260b80c040e170240403444d03d44943c500c0307036140c05645800700c20035008092a00e10714110074581d000750280e182c824190030301c0000b85008110913a5540e101c2102034404840d49407480c01481c0030364204004000004001e048100c80b50b0885a17408074074032100740c0324400350080d0781000c1c40100b01d0100c40c140b03503669452121400b03042800c0440001e8146034a401d60344d00301881290190020400d4101014080100000b0103035100428101601c3e03140d42000f03240300362a1007092014448213107072031428150a0185a8040400340c020310100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 709968336 1250 709967086 709967123
    0xd0e030c09012603120901050615181f050301090b090f010b1606021c0f0e0d0e0406030f031d030105070c0602132301090801050103030507080705190b0105030613 71
    0x40f180500c1001e042c403151290b03c0c0c1820703c058480468100d26030003562415100150035260004c0902d0b1040c62449240510042c146066030000c1d015040750815480b040c00101c0c0480074520f0692a214103080c3d040c0403182c0c0d10000942c1a500c40f040c0038451a5100010300651a2054613128400c002d40070051240060090180c4407501107816860800101502c0d4001260321842d01c180e0042e080740c001102001c1603008001c0320100c0242c0420424610b8000641c94032201c1200c8010055403070700d00d0150390358580004018540041030074040c44810311340070700b40090b82607003038180022901144a45142c18801c0303038826151074441c0c0242c1c0c4d12a545140003035024003440b0a0324000703501c002c11850311581c48480c1c4a209070380a000b041507140000b40001e0426480400e4680c108401480000d5105c2f0a9a00310380d1b20001442e00e0308010b00e050b03418662f41040d104d801050350304440040c09000c0090f941224015819a4082d0b00c4642e0307000d03000750407100043c045006644108540 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 709969586 1250 709968336 709968359
    0xc0112180b0c070b0a091a040b0a0902030709050721020307080402010e030a05060f190e121c0f0519021801050d09020607050714060423150c0d0e030c0901 68
    0x3005644124518129107540e41c0c201c2400c09644442c500703552446ca1204100c3c03615658004940c0c1c90404114a1510340e58011600c4802410718000740d44480850085407420441840503000140b0148142d24081c01c009081c2c004442d60b03104540c101075a200c440b603045100304c078015112a500e10030650b41d607400640c0c103568005003003034052060562039400710700c0911806018170710010800302a8100551040684086d030003e10b04140d1402d0000080400e0018212029071081410540c41d034281c020200810980c92810110482c01c0a14008c0141e82c1c55100328450f45800481451059084501104a0240c07031800852201d0002d03920920358081c4000d0507103880d50250100f400c0003150b001c102141c014071001c40e46540030003c24005a031940f10000d120f04001c0e14081c1c00c0c1894900c551400c0150b001006100d4451506007003c6030311629076201c1e040b02c812094a40d0b444240e804580c0e594810518140000c4201d07c0009043c900460182c02008008106a510380d08106500d9035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 709970836 1250 709969586 709969591
    0xf050607080c0313091d060f07020a050d03020901030f05070c020f120d0e031c0210050c043303050c0d1806091b0b1309020a0c050f0c0112180b 63
    0x207451405100c03031044280d0410043c01c0350340c5030080e2501054580b00222050b503600d00c0000400b500c5161884884410002d9841d60111a41c00d480c0c2284e15120070603820100c041201030844c0c01414072015040d60035800a24417a00e0030380c1d003004001a22091501181c3e02034031440009806808418003525181c0c95911044100510301003001681000661402049500e0a00441c241d0f4403620b459217420f101d41800b559410715880d2443e407454000940302d10f00c000c05100750035a40c038081600808414241c0300a0503511114565072510140f0354038011142c4021201e8078503200d11400721842c46400340354040c0e10419806410141403612800c090100d40038591359180d001d00b00080400e06600909620602940241c1d54140c0703100c50b1912800b8040d0400c0b42410780402c001640c0720058845c00088600c140c800503241c11881500f155505540400030384103120300c0c00f1081410b407011908000c0c21000f40c80d20701d0140068410141500c1b4000b04c100c101502502d03603400070440820f8040c0c0e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 709972086 1250 709970836 709970843
    0x402030405100510060e040203010f0b0a0207052e110705042d02090909150c0702190602030c010b031c0507081b0105060406051f1d0a2d0f050607 64
    0x80c03040b000e0252034412164119114a4a00707078200c1c0810005420002c91038081e0010b680951556051a1a01500308027900c911111103500165003030f5818401d2003243c1c05000014042608200d0300301c06414418039404004218510709c00b401d036070b42d5000e40140d5040700d440002416209240c9030400c03008203c00284210b2a80d9582900d4405050110112441004107a001070b00e840001061082400004012031280da000302401c0d40713030741310040b2529440041030302c3c0c0d541c1e01d0b001440820000704022a03070201d801440f24000c9000d9401201501c04021303c2402002005010f07800c05540758428002400c0c030251060007940c070103100d407000b41030080c013a15000c0d14011301c03c00310f034072081010900c10555966030828000d0924103805540000e000032500b612060140020307002c00c51190307140d4101401841138a0310400340d000ca1400f0702c1c0c01001031160000d640d03603a510782180741040140710803005a603010081040d4800d019a001d0340e580c59080b010301c80c104030070301410380d001000c00d6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 709973336 1250 709972086 709972093
    0xa1205130b0a0e090c2b05040f120309020604350f01181110031e0207060606020a0803160c0c080f010b0a0b09010302030a09051c0206060d030e0402030405 68
    0x8812080d10803030312100074201801200d42d501c1d501c0d80002e00c03d40c44200c04078854880340e0180188040d043c0d00383c51b00700001e5440740100640d0044401007582c0040c3c050a00c1c039041008000c203100142124103401da0290540304034111850004078201c803403612000394801400d200074090a040e0344602ca0340c0d12001c040803001c6010f054840400c070050070291a00c542d020f0092003103400300c00e001d11105246012980c07010100541c0d604c0d440d11300b803554024081e40d00e12241c010803a2182e00224a00d1a140900b80b80101c9041d035508003075440104140c50a40c00c2c1200090135501c0080c8002c4a80d8000301c040c2e040d5181c914038100400c10007202c0c00100500003405601088520b0440c1c2c004000c4003000300b90300d1420703817a00e0782035508280074244203002c046c2c005c20810074250111003003580c007440e0041c0d5940d19810740400904040c8005082407007800742c4201c1d101180025000480c0607034084a0203951200200300070b044003105c0090000310196203125041c1010380185410070311580a4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 709974586 1250 709973336 709973347
    0x11e0203040c05032b050337060b0414033f0f0408010e010b100f121b080906040503040302121e0616032f1314040e0a050a1205 56
    0x81d240400e05d0240f441c020b05254001c00c02d51000b0300e07207590841d80300e04000d41140703024002c0c2012030038243da59041c09001070030070021b01c090899210300510740801040107800e44805220182e504280103030840c6640039654007540707207000690308035200e00070250404046c00b2140785c1c80c1201d1420015052414519424495102110f405030818010313412140307803514688140507096070f45c40e40c06180c00703900d0120045510307142c0302816070440b0424108180500702d1008101c44e01c200359030700005224a088036220208507440e1042280800c242e503103242a84408942c1520b9078400e4500074044d038400c002c20001030510504c101402c0103060141e40c1c0071a0341010210303520050b0300c0c1088440d000002017202101c5880f031a01c06101c15803804002d090803518070065242c0003284400100c40c00d4502d00c2c0201440700e0205e941000c6455080c4411550756a40100100482040e4901c0390781442050074000c40d0025020000c01e03003140040c400a04a5140c004000c171044c0000c00c20400c1c03c100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 709975836 1250 709974586 709974589
    0x3220b0406080a05060915010f090911210f16120212071b020109170123010e0705180d111009030c06090b0f030601020c180f0603011e0203040c05 64
    0x500020071594940c1d00075490580719500807100b0042c801846406d6843c00c0c0070420001c43d00380e4aa202e4207080503040103945082c1950ba00f203040d40001e0055003402031031054192003001605d01e424076004d040128000200b01c4c0344640c01e08030380790b007001003442001460108800f070f007480d16110b00c3e05080b4000a108141407050380c0c00006000803c1c42e00300203000840764082584890080c4000320318140c880c2c41e07030000740b0b0541c603845846840d04084500d07000002003075010306107076483c5051141040511721181605038031300b4416820f001c0310031000031b4901409802101c80c0e42d0314101d00281002040d40810421180900040c7d901e1141c280c02c1082c1a114050f004086580c40c1d1a5038420a00d14034140300042c03641d402000810003a4002000060402d030f040c3c0b0144044206050346a56400d0b0040380741240e5041880e40c00302014000000f40350104c081c080c007904a10700710414a41d14031081c103003a1810f4000341541c181c6880d18482e0b440d13005030f002d150032034421900b82840c20303074800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 709977086 1250 709975836 709975859
    0x22107020d0c06210209030307110a0807061707031104060c03090f0b2d030103171e0301090e0115060c030e090702060906151c02191e0b0c0322 63
    0x80003030b0003280e02a5401c94442d02d000130040d0304000e000b0401e51902d440c1350301082d00c0e070080010040c103209100c041c0c441035a40d8141c01e000600601002c4601d84c5a594000a140d0343c0e21901040300e40c008100400c0c6024880c0c01005413207000d00b1741e11403a09180600403140e4080459082e003c000301500c0204080003903215070f10040030302c86240d507100c080b10503034901200c1860550404514402d08105d00c00d00503607050b01d044030b4001d0881042c1e035100841c00c04540c03080103e0598442c101000d00b0082c0309a500207981610b5800004000c0706008103005400c8a100d00400159a55030783d9003042140e200c2c50f98801d5191182c5480b00f000d0502d100820031000c025141440540c100c6010404001e07802c11202c1e60042940d0034110040c2014408140107612402c0e0803401d5000d14124402036440b40400b008081d0f642d204040505a41c0714205400000100200d030503000c0d8035900000c0f03041e1081c081d1030040006101030342c64003482d609161500d1001d46d001c0c003001441e81400081c01044117 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 709978336 1250 709977086 709977089
    0x8151602012c0f0c30030d06060801060e1e060c0703080909100f0506031305190309050316150e0a0f030303050615270a030f0210022107020d0c 63
    0x4044054980d01640b0a0303d040c400b4440e80c0c402182c1c8030100b50480355540000203404011540c0403007000005403074512485400c600500b603828480018002420a4076a000c00f04681841e560100d0b60303602c8102c2212038600861003907903c440003040c03502010311111121029508018503c92802c2c145104082c1041c40f541c2c0141c4400801044a200c00d05114031003552203215a24914041400c0c600341111914160107000d020341c0700803001a00c0440414034185c1016001411181d02d08400e84640c520051005421000a1501400000d281c10009082d445510031400301c101a541407210b64a00c103500602c4031410040d400158007126265009d0500c00790042d040d03411580d03421401d000d0140d6034050082d60103001e2883e049660160308200380c07100d600f02c01d121020001000d034816110301d51a500100e40c0505a2403000007002903048000e0600e0303100b950500e11181044101741d8a9003e0300420781d00328400d42010702500e60a050052070711038070060064060700b000784c50721443c000b1036 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 709979586 1250 709978336 709978391
    0x50315280b180303040f0e07051204050d110f031b1509030a0e01050a0e190f0f08010f06030203060106141c020c2b050c0c041a01090815160201 63
    0xe54020b90030540125003a0003100790011403403c0d20308264201d01c0f00b000e1240b03844000203c401728000500c581e04603111030441d007900140f04d0800741000c42d1030307600039a072280105210008a407001c480108035a034503803a41c00007441c01e101d115440081e103114102904402c0740100c00c04e024440b009410f40740e000b004480029a11060000006009003032103400d99814810305102d1a4001640600d941c002050103580537447d2415420058071143c5503034214214464131003902142a030f121041003422030b603003003009000c0d0b65052003201c0121560313400301035091b0b0001c1c80148500c9010382c440a810b103100c0303030743c103454403a00c04441200042803024450078a600047e5880c0004010810501094a82c172550032440880000c000794490040700314506100000c14404410001800442c03407001000d072050154440e0b10303107403032118085600c541e8041080030b000440c0000c40010349801320350403009540342d55144c4542c2c0d202e0010f0070350000011992119072400c3c4008590b110000f0314a00d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 709980836 1250 709979586 709979609
    0x2405060c031c060806180a0311010906060305330a0b01020a0506070201090c080f0c0f010903050f0105060a1508040204020904091b06080a02180f0d020d030e030d05031528 75
    0x103090149040c505e014104120f0007000c46595502400c022540040d03007641402c1544040008807a05400f42420340d82c050101e51801800000307106001c50751100c1020024000d003001c4441d5400b007240c2c0c0c18010054010022007000040c0c001c942c03507001e0040e828050040702c00c49401560344600c0c00307000f1a00540180d45460b100410802480b030020080d0100d8000380c10407184c074081075551001c40c200001c2c030a1310f560310001e62590003851964090358100c01038801c1403414004282c080c003030695a4500609401c500041c0070245801d0001810306a5540d01e8201d8840f03400700000f80d041002001ea0003595080c0800000b020315119881c21a00704080d0340d502460400c000d0b000441c0180071040d8540100300c80300121203000048504690111503140d0707014111400b142034040c481a009400054000342e00b001d1580280d1080c64400d812070459882d07428180c0c0071a868001500d03513042466600b000c0d015546030403408100ea864420901c0390000d11607887c241c0640c00154803a031074000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 709982086 1250 709980836 709980839
    0x603040503040f0509130314090a06091403120a230301060806030115050f151e071e0215090f0405010b121b03010509150d030e042405060c031c06 64
    0x2043d226200d030080c0821518141c0900e003213044601000840000207013044a41c5049000c1031400c00262034448030050305618511340c8603280503041c01c52a00413908150416016074100385000a2241148070300c02039200d040c0307000400133071000c8450007071511005541c0203401148a4032103000d5070007441c456541540b9800e02109040c216201541c02c84464904c0c582c040c00300340c40c0d841d0340d800e07550401d50707c6120401c2201c61a181c0d40c01134004034200f08903840c0d000c0030b1140b0604050480705000f034031200c1c0611303188401c07400e10f5040e8100c0250087c0003065495030b121541006031101c0305d40941044031468115000034202d48098000020240c000b2514002481072002590b5002080120340c5d008080c0c40c82003034106010500c1707103910800c2038030005118215490074011080030058890a0041070f9450007510403441414024000c51400c07003806a585042944400c2441c55462841400d0f4245418007500703a110454621161000300004508000d0100d003180802140301400030b51030303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 709983336 1250 709982086 709982099
    0xa03020d181e170d0501030c0602030c071206020c0109260405060f030709031707140c090703020d060302090a3c0b0a050316030c0501031a040e010209060304050304 72
    0x5814000000c150900c20001c0c110001d0000c03103107065a294800701840107484103260107801c034039100100f90103000e0040f03004100d1181e103420881c16680b1407000780d020760f41c0318041240d407406030f0385131100c070307680680c83c01c201e40280400c184c0001800f881d005032802c03100c03059460a403020703201c0440350b040070485c00c0c031a20340c080c62580100402c0203d00e28a414030308030000e6540d00406803d11056400080400c1415000b00b000100859200c2158804039100750030814a40e00081016103000c1d0b403510b11280c3d00c0c5804110b8014908006281c200d07151035409045009401102401496030307034904010000d80c0d1011442e42c41882d5040d0f01290300d2141071005810364001109191f045080c5850914108454a404070501c0215901c0050322a010000145094206901240d0940a030060346905030188400d40003c0c0d03030290071148001a07480004408681081107010400059900724252600c0c05400c031602c2c04c60088005410200c5503800031703885d0750040c2c134125402e6100080c1040b00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 709984586 1250 709983336 709983341
    0x50a0b061c09080f2101050a0e150105040e04030c02040c300618060f150210150b07030f09081204180f062904050a030602030402010903060f0e120901091e09020a03020d 74
    0x9447c017920301011a62800c00b4034503084002400312010001c0040703030601240d210760705880083c0b00500040ba41e03800c090034003409020000e5003d901660401e196540a507010b0740c440103940b089035448080a5202c43c500684c007109400f0a50955511244005190703902801c40181d96a0030000018007540b608e108503030795000726400b031500421424101c01915801094001800341215400b0079212101d1007008a044819049000081c802081640034140c0c0a44103541850446e240d032070400f0349400c03011380c1c0c0d4000b02c51601644501040248111807958041c00c076124992840030550515189440c001e0355810b802130010401c0c1540721203d9805045002c1c1410030b41c042d1154901400d1001080001d07070680030103030803941c0010103d011a441841d86400454000341c003000800d12020001c0045d000c18105030845100e01e0075004001031001088a15003501615010541494440180c501c800030f502e09600100154034009244590350000380340e82038060b030380143d40fa14814014401c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 709985836 1250 709984586 709984589
    0x30e040f2409050903031603021603050a08060901080601060e01030615020c030721020f030316150c020712030c2102010f05090a050a0212010b13050a0b061c09080f2101 74
    0x4014202001d10131103650110440c0d0f0040c11414030114040042142500640325030011200c24203150341c2440c00b4150301902806160149542e40b041035102c440801c050340e8028012180380d6008600100902170140300368203040e0f00c0c107050100d01581e6540c20b00c4902c036183c506420140e0007414a0340d80324034041c000000074101445003600058245c078015641c0403c0d22070000e0003106e41c450100f840350790810a42d071024070243c0d60300c0d5281d000c520303082c0c034003a00184401e1080360501091480f11030001c6140d07025241c641a422803a0340403601e0403100c420842d04281c0d4580c182849199041400d003400d481c080c00a40c0003c10b0039040c003400c1d4000c662000340440101c0c0c20500303070300c40016070115000c22080d40407150078001d03407919140c403401014107584c0b5560246d03401503c0349100c02140c1200e4070440c010f0108111460b2030300c0c207010341c6118462910340120440314803003142e4101a03000c0c0e41d469024241803800c0600c8082c8548140e8410000c40d00c2c0c0c003885540e91880060b075a200c1c0c60 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 709987086 1250 709985836 709985849
    0x50d11040e06070e0d020406090c0c06060909020d0803100b0f07050c011d090403120c11060c070803040b0c120c03060907090f14060c0316030906051204030e040f24 72
    0x240700c3c588440010702d168071160703c8a00c5908a5608441555141c1d00810058410101c082000f0000241c025140c07004080b0111840b9041a01c00103c605c002d10580c100a031300904204e644030440da17120005503100030400c40c00d85814020104040b010300d409480d07203c50000406503980c005091061a081700c440e07802d81000b030740d008042043c00180d030794048104019108603513107407214501625103003601600752540b5461b20307070a818519442000982e1254580c825103207682c03200c1560b0303002e6100300e0801504c40b2404001040c005050407110321b9105008010040c10030390810340c0c180c1480000e84100034810f001005000c064645101c0305500400382d0b0400c0d1003010f01d8401d100c22211000e12400009040006c1d10104039103d0310100c40b8000041c500b0f0700d5403280c05940100c4d800d40c0490003075000074001b1b0404200310380600102c4958036020003c00c452035595030703011500d5400ca100356680154881c10020201071560159500b138021391130080e048262041c89140706c16010354080c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 709988336 1250 709987086 709987093
    0xa14071e05010512090109050d0909050a0e07060f0c0b040308040b0907050306061e0d030503071209030e15070b01030c06270312020f0a0606230306070315050d11040e 73
    0x1c01c81070b0b8100044440c030050034200c1041d15070768000b00c3e6004100960015101d40590f010840c2050340c018200029606140010003003916440b003600d00f103510305a030004030342e40003403010b0064034010400400304805a1800f9075904095a0ba0820000d0b0309407030441c04241024284002c01c075240c020b6a40c88003180005200036480d002c00290340314000f41c446030123140016500c051529000116400d03d0b0b801404003403d0031301903c3e000384143d2045a050380001d0505a80c0026a05070b401486000c03601692030b004889407a004100718800b0401103114504410000b81001030f0044043c00d0007140620300b08800d1524010014000380b00c10034191643e060700c2c0881d004520101c000003026207410170084c001d5080c08040903440c202030b0f8002021240b09250341d4008115441c0c10241c02d9920b240c0c01241403543e4010b0018000d425101d025515401c004001120a846684031010400c0042107581020b940c54000c03070701c0e034070b1401403e94a107491404100340c6400c06004001021080c03074002e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 709989586 1250 709988336 709988339
    0xa12030603031205101721030402180c0904050c121501091a0403080904060e150a050d03120b06160f02030c0105400e0915070909050402030a14071e 65
    0x81c0401c03200c240198440c00c8401c0042c441184030030405030703034644941841381c1074030300c2c1f000001a440e0b041114124402c210740284120441c030582d85030745c020107402c1038042c01c1251440412010702802001161301d001d05008a0608100045000f4001c6064650080c2901d014000042c0312035540d401031211040c0c8511036060180ca894100c404417608085501d49840d001c20015014203501d41c000141100340d9410310459841c04003000ea5440340c11130700c40c1c4055580f0418801d840100c4500500451288440f500400b010343e0403000303a01000800081c9081e0f94981200f8418880040c184d0716910f01c08550011414200300201602009082040c00c180e880810f4402c10a440481c1d0034104c10250a82034515405086144602ca10415403030409511004500c0b100c6808560440b000d200d058144084806044400343c0500902d540e09001070b81000c101d41c0143c00b018000300d0b05440741c2c40c1a40d000c0340010f02403100011000c1c02500c04c0a142c4200010135540e44607500c8101d1000080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 709990836 1250 709989586 709989601
    0x180605041214100213080105090d08070f09030506070314150622030206161a06091b0d060308040503100209090411010c0b16170105031e0a12030603031205 68
    0x300c0711011540a482150503488541910341000780070580c5920540c008202520307051040c194200a99500ca402000140c1e109400c50344c3c0c0d60030500da480045680d0700c001c01c00d010f01c11000f031072441040d0f0130100f10701c030707a00da5030300e4a48841110fa800000c4d58607000781e007501d00d920041070f400600a42d106552011a080024aa0300c1070314a0001e43c42e40b002ea90a100310790781c405040086030020001d68651504c5080b00c800700616444c129402d568850101c03684004138040d2900803140034040404a1703884040c11560f840e60082c0c50140c0d0482070000c11a007401d14028000554420b50800703444500d0041490b04c0c081c40d95110760300b210b00500c82c4e4151a20f400c541d4070b90041c2c21800d628860280c00006903154a0040c1014246c02c03c43d008000d4204203c1590303540304c1082c0d9030b405442a12044802c51a00c0c0203000e0941e2681040c2d00307100ccc0c0c105015007070784a02c41814013901c0c0c0c0c161066944010091130b050781d11002c20f403645010010715800c5880141e80c03800c083d03405c3c44145080340 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 709992086 1250 709990836 709990859
    0xa14190b0f1c0327050a090c0903060213050402070602281718100605090a0209060301030b041707060b010212180112021303030305060a09090f15020d090318060504 72
    0x72070350b81c1a2840001d0402494420b01031030740c900c21486001c1d40a10020900501c255280d40900c0e4000e080884000414420070301c103203008030f0078580d00c88050a0543d0b44010103540030480e02c0c03502a1b1501c00214507a540c1d071008003c0c00d03105800050780c0d501400b42ca20403d036040c0c2c29004981c800440c21030181c580100c5060040c2d04c88504c0e20365a030340c651810400d80542e44030828581c2c031920091034030f001c42d1984090292030341224071002540d01c001244099105107100300f50064814001000081c10700e4211603001407007030142e0181c007845560000701d43d0f00403160a6641c00d440d800000c0071541c040c0007080300555050540c501e0034040d041402903207861400d21034104042644040520a01c0b607069030f02ca0030f0041c4028801c180d5030700f4010b0150000303a03101842146085800103c0020b07512420041d2580180e100112074030326222185102043c12402008075000c0100703120900040c440c0c80b012500c03a48941a60703001c0005414018511500320805000c0e08000900810f020031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 709993336 1250 709992086 709992109
    0xb060f0d0537092301140a020a0c0f0f06021201030b060105090d02091009050a0e060c130b160506040308090c180127060e160503011a030a14190b0f 65
    0x14000803c0344034076031400314030262420104000d000910401908074441c107400018505522010071321850300c4601654003244104283c40d000b040070501d444002480d10340709100c400f07000e888001070080c00ca40f5030303074280d80c40a0341d61074001310b00f88018002c10040088681e0404801e2030454201450f020100d41105101310020380300c4d0040c100000c21030031103d9900c0300645980c4509216038182a5000c2001e41503000c0c40204902504002905003884030042d20040010790100750042e900d00f04407160a0f0740721400f01800400f4010045002c914200171090080384203540b1202c2d14034000000700d00301440c1083c014070031305101188000c400309412625042d20a9142c81c81c01d01100c9001c80c013580400c0007015010a41003a00000c0e14030240d180c01d1380f00c2c41e6a000e0820061100401c11207040c8400d00918440100000034203a090314003038059680400752010001c1c0012850040750b440704401c840207030519585d00300d001c8144950b80a01c821442064404112002e103410006030003640a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 709994586 1250 709993336 709993441
    0xc11150105130b1809010b060906040312020708030a0504150c0f020933090c040305150c07081305010e0604050f0411041a04290304060b060f0d05 64
    0x241e1a0380102001282e10120240f00020616501d00d141c02e503450121400c111425051940b9184445485042c0b0317200b21080300c0c9004003914070301419540c401262040b5005540b0840c07040074400328400704104003e00e80c040c1c4031703102c840d00da80c82c00101d0380c86196080c429034204021082c400d00041d1a03c260f40107015412100e40d665a40c480c5074030036230b1180100c914881c00364620b0a03190b85038403401c05200485816203140900741d4800c40005450f209511004000d94011003d0f00358006000c0740c0c80d9000410034100c203141c0501c6448620154000351803584203030381c0e01e240403c0107603004001d490030b0349015201641850b00c4c1c80009490030032200c20240c011521420507101d02500d45081728040d149201002c03200c000c03903401d00a00c039041800352985c00b107a000c200d051028403031200c3c4864840c59401861039030340c650355914081d2224605680e0007200c14840d010044099038003414003100301840c0000c1030712340310001c0c200d00c1554200d2660165840c1420001c5c1c4900205640412001c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 709995836 1250 709994586 709994599
    0x50709060c02090c16110301050601022a0112050c03100911070303022a030d151401050c0708010c02030a120516081f0611061503060601111e010c11150105 68
    0x85900382c0c00d1403441100e40905280030718a0340402001900101c6c5003503000140e0003086599144170041e640c400414104900c4c400e110116000311200f2100042004401850403000c8003034040941000e4490542d00300c030b035426001c01004028004400d20382c0041000500034412001c048440c000c0c80d12a80c100601055000500e10310482c00e601c54081c0b0070004030301000c140d81c6088182c030f47c49800034105600b290b421304000040c00c41d42c840382902640e44005c03021210b04003440056500340c0c454540c54078903000710280054141420710036020004019005543c0c0c6201641b00100320010a10200030921703d05806e00040380d54a40450840da2084c0c2400012a210101c0b500950104440d02009043c014900071800550150f0301c0780020001200b243d5190311840502d190b5490300c0c000c0d1a415610400c00682558420702c20314001060401c19115410414035120740c80c15000c0c1c80c450308913912a0341255030385134809401240da5000c00042c103100715030f034500c0d606600301c10300c5107520458 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 709997086 1250 709995836 709995841
    0xd0903030503180c130501030b01090902060406200114271c2d2025170a12020304060507030302090a0b1b0c0105070506040b130f0b0a050709060c0209 66
    0x1034204201052913500070409024a1080742d10314010744000d000890b1b0800d007000001481642ca030188030641c3c1d900404080c103050500500325550614510445084240c5071b83c481d107542c90030310a404408200c40080342d01450401020080f26900110700031400184511038118000e01040110401c21142da5200900d40107800440b814550200480a005814581041049103005014103c0711203510f407800300350f10b18541d00140b042c64141090301e07908407201b04011040001c0702c80780d4480d500001901499160640c1a0504240c2408421030340e02c00d242a00c2480011200c0748092030300c42c4021494241800b030010085d008242000b8140740e0007098160305a44c81101000c0602140000952604000b4440c0c403c00140c80341c442d0341c0c0b4003411910014552048040768011034200c0010442520781e81d98050052400500001043d451001a12300090517920741c180c04074042e0031000098100620502d0840e140541f8190500004010070817080b9040142d4a01c807035012503480240b035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 709998336 1250 709997086 709997131
    0x9090a0506011e030605011806050711040e010f02040e0c0304022b080f0307031b17041a01170d0315030807060b03010f090521030f040c0b0304030903050d0903030503 73
    0x85409070010102041d900d0b030440d0b40c1c83c0d13140c0e00182c02c541c026070302c048001e00710074900044c100e0f803030082c0130020300200980808035821031126004510094000501114040f40540c215816810f110409940018041055480c5100540c0d00403018207009440c40c185a4006001100e201281c0003045c2071191480c81516195142000410380141c40260f548000c0038142c0041d83c0304841c0240840c1c07922103540031149541c004401481d61a4907141d842d03082000000101ca0402802101c5801d81427106803400110800618020000600154002c500c200300f0b8130f00b420803501c014010186030208181001c11026600707011a60003401c0c1c2c80e540c06541c20448044c0c4466075609070107600b0500c81e146000702a500c00405107000f5815168840011401c1861000d81001d0f0940002d2080c000b0646c3c101c804000c00b604244128452251a0b581e0790f00d804080d007003150700b6808103105039402c20a0007028414a4010350851900e080703030505555000d4030a00000e441d0f0f001001c030703180310003210 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 709999586 1250 709998336 709998347
    0x10c1103010501031212050c16022d2b03030b060d06060203030105120c060406180312030204090e03030f1f050306040803011707060219060617010e07060509090a050601 74
    0x1401000380003400316684038240609a00c10302d03001d810004540800c0c540c00d0421505c91a8083c1440d190340034500062a0822803000d080c3c64001d0760b000c60080c9102050512900700c04004840d90034032000004216000c000f090541d03100c2f03040303000f80c419080000903008550041c058aa26080000f40b5400040c04542c190081c0c00094030210710300680400c000e90000099812079000301c540075140c0b1030060314161134445001525030014000d00050203818054200c00e0340e0191800e0030340803003550b01d49504000340c50342ca1a00020030340c00117003405207048501400030401d0000c0300440c55410704161000c01d000000b0b02d03124014020009032030b00c520f024403844008150060484480d420107082c4818164000c1c0304030701ca04490313030310405c038103060109041048944507000741c001e405404071104020040300c1411038507140d0b6500080381d0b03154003004c1c449030b4200903400056401d022205041c58007100303400000c01d001c4207000360301180c6c1e540035013980e104008050110360b03510b441e0016601c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 710000836 1250 709999586 709999613
    0xd0f12020c010e0709050c07050a02060f0705030f03150a0e060f0a1502060a1401050102030a0305090c0603090a020307050f2211030403020a03021c0503041211030a02150a051302010c 80
    0x41c1c0d402c1442e501d600740000a102e42c10354183d0502080247c543c1d80090711a0312404170001c00542213643e260002d45440c0e005000e0020070f10040720316144c003903983c09045620143c52007900c03040202c1408000749050b0704c02d4036004401c1d83d015502604244950400090080030a4443e081c0d084400d6102c0c3c171500031900040241c8440c0844100d80410065104e01049844145061030601c101002e281420000d030304943e01078014629080b101c440c1200500001401c88615100740300381e5007080d4035040001e610508880c8081c1c81d080360355204050508000341e00851041c4801905000255980000c0902400a003e05240c8480e240c60f80d10014014415a0b000b902e100030080005044d00483d076900b10700d200344d007602c1050310540114909800090407240c00983d0601c00100012810175803e9801d807a1400c02602c0710140c24042ca29603448040d5000040c0c008450038824003040380d00c1260442524001407000d40742282a0300d2040a41900290400c0141d240301020301c41074524089 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 710002086 1250 710000836 710000857
    0x8120901090b01151805010e0108130f1217151e0303030103030504032d0303020921280f1e0c0b12010b0c0705240310090606020d0f1202 60
    0x44041d13a407000e03a00b000c0700201c0340c03a0f00403a800e16203004981a01a9a4800b9900140c540c0b10405000c0001155090001003660844101d420311020126081106141066100c2c1c0808500700158031401030040340d56840c42100503200780300740000038903041b04440e5824002d4507407515480724a44040c0001c035950a109402d804000004403e00d50300c00c00900c03c1d0f070f0103402c845461190722100d01c281b440401c80c020742d455810007100000617129030000c040c200c00040ca840240708100c0c41e40551a00e0840e0101c0c41c03580510780e54403d22003140b21180c6c0c030001030301380c0404004868a50541208004000404101c1105240711050b00a21102c402c065001b4202e048056216840c1c42420380c400c1c5145101000000d00000301183d8003000c980504079044044c10419180c03006200441d00900e4413024400b035080348118500402d900558400d08414100341d180b9403800c0841800c80304140c00502c1190041c0861890442c2c200d1070301d40e5000750900c3c0640725408a44450802402001d9050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 710003336 1250 710002086 710002103
    0x111209062203022d010e040b102f0307080a17040303020a08010b0403030e0d0201020f030c010b04150506030f1306060803030a06050418080c10150305060a090812090109 74
    0xc8030110320034000801a42d20940e07041c0d0600b413111180c500c140c01c02100710400c4001d10310002111754031559800e44281c2024002003903981da241c00050720000d55041c00740018a5050110350100300c0c03400344e00300081d09142d480240c04101240141c891003a8100074041d9000000c3d6026142d20580e0840c6d918803891102c025141054a4014081d43c441030600e000100c0040021440510b600211000c40350b140e01e440a440440c1c100f03004020100040a90550180d41540c0100b214184010007101c0700d01000021410b403171604000c22075072900446002a890014280040d4a40720100c942108039092891310070383d180790a0174085c122558004004509000c0001513400c2c1c00400f550040004040c24409a0788034020f010071140c032a40010104080c842d80c03000450591001051002d0303031781e81600d00706901010a0001e9843e491686944440300c4403081007440800e0101d150801c0584101740104401502c0d000300e2406204800100040000081800781009510144590b07a01000701c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 710004586 1250 710003336 710003377
    0x1060210110d240807050a122f030709020f07021c0f08030a05071d0f0a24091e0311010527150c1506240703030c11120906 54
    0x2901400d01c11881d0f0306120209140c00f291900000c9206420f680c0040c0804a810740b5010a080c2c048402c640c080d14401d40c3e100844c941d03888244005140320290a08400800221030141460880e25034401c549151041c82640405081d01d0304480c0e18540481e000c1144d600d400c2068401c42c82c20110081c200e0300c3c17640200042026103005988102034058003008203544c2e4100540341440b80c0c4090183c0210400350101c030034940903a82e06c10a0340b000c0c000d0100503850380341c0301030304034141c008901251321421020381007164000141405400e0090411020840e141e01b160140501800300410004041c249104035034411410760b04501d03880000c11100c24107082e0584a82104c40510174010b804c0c80781980101d5204170229a12403040300020699100e0300c030101d5810b004040c0c10300e5445003550748081a4078844412590507040740700c61803a581d502c146000750071503101c601c44c001401598048411491000301d00c941c5004860b40405a07114042070016000b0300c00c10301503c4035035115442 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 710005836 1250 710004586 710004611
    0x251106091212041701090b060108092407080f040c053106030501060b040324021210080f0d0c0809030703020d0b19050c160203010e010c02070e010605030124090906080a020f040501060210110d 84
    0x4050050f10303b602c950b115920354049100d0500701c103c40140c40d01010b06c5041100e41001c0c0c08402d0b1800a0990800d03059900c400244001050b501e244a9903984907103050040c40300030720071a0000d21844060500d0300785107986031191016030b030789443c464543e00700c40a44600300c1c40e01201d0013114100e00e550b440b03280184040c0c540c80c40e81d0048034031510442141140d0038400040ca0452948981c482d100725401558408081d036104503807080d050301540100000588889044180700380c82940301c0c547d00d01c0c2c881c030540e41c501981180034249a08003410b0140920f602c001300c4141c80701e1803200811685040c00402d000d001a4114000726620341040540f1141e4086580800d0700da4010310728002e41d0f80d451048511f40400c0c007561024010300703100205000001000c21403059090306150b9a01a40c452400f0100ca40e40d178000d10564101682e000d0031441c0682c85400d5001044400f00550b5041407802903130361a10690f10304100d80c0e260618810240c501045c1d130450342103494180581c615100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 710007086 1250 710005836 710005903
    0x9030c040f09150b0105070818100c060c030213050d020315240f030c120c09040311010b0a0e010911130902251106091212041701090b06010809 63
    0x2e000d8610b88102446454080e100340500c0400e10816954035080c1100d0780c4072800140d00c030035250140b58840c29020b0500c2d131a46440c10b02c421f046a1206000c485060404009588190350020700700b40c41009018900cbc60801d1050f0252581500d0104000c44244086072400000c0c842c03510b6601c580d1420424840365088441c0824944507088001540e10300c81407084103404502c005915400c017141091442c244607038072191102c111021200e101441b0380200d07001180956003580004d001c024030341181002400350301d1481000b51107142d0079500e0600000e0100006004000e0300c42c1e154602e0540c002d50f5602914908104892190921a5100702450080d80301001e00c905510304507620b580300701e0b2041c1615160302d401000301e96045074584c04104160b0b015090080d80418020040400f1030001c1040c44098840b40e0415070380d450030007661070703015150309012800c035070704040709280060b24454240ea04a1402e08007240c541e101c0b0301c40d141c05c000d00701600c8400641c2a04000d400c1c4c1400c2d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 710008336 1250 710007086 710007101
    0xe0a03060f15050a03022205090c011d0102100c121109010f080c07150f020c060118150b18180a0f140f04080d0903080603010e150a0209030c040f 64
    0x80404001010702d402900300c81c102503215280e40502c40302d10402c05804e10003080c15810b14029141d400e4014982c0054044503019504403006d5404680c0000345940c00904560041042c444101c00c07240304180000c0d6035400610403071811545034804116918099000c50b00180c140c05014050b15940c1c010078801d13a00302840d4030740003c00e0300d031402211901031002c00e8043d10041010514051440d1100356180120005041883d5501c1e0104014000c03144003411b0040d08034400b86c0030551400142c80f07107000310600702e111901c1c60f01244201800041c1d04420032a0701007000e440c1c0391004e2403002000080c2503041d1681001d81282c03050042102c0c170380701d00e11400e144082002480c850030104c00c11220141c031101d078031865100202d284041100c2055a01500c1056854604000d541d9103c0580b0720a600c00c402142c000c50501040349820300a01089044140c0103040b8072405091044192801501198006500007405205a1002d2229004801018000b4803a44141c4903881e002010030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 710009586 1250 710008336 710008361
    0x402040f0b3a1511040504061205330603030d0e06010806130b010608100312020c1e0d1e050102180f0d0201050406050d1805030a020f0f1c0e0a0306 65
    0x442860446002c1c050410480c100c0d006594103600c40346070541c2100505094070380000b11002884002040c0d0703220b00840014022440e200ea05081e03851400c0c600c0c00360b22a91003006440890b803c003141241010350346444003803000c402e94146d100c61011904501c5641c414800c0181000c00b5105031410024400d81218000e004a4045035602d140500047c0c800304001040c40c024640104802d911400a01e5000910b17600b82020040c0c5d0383c2c3d26601c0204441d841c43c00907030402101c1d40030b5894140c01600c0380e070140b541c54046c0c0750005000039207400c002000052403c0c0d07070070f44514980070540c540340b8046984100215603c06803004002d12184de10641d40703104403c900625015414130fa010504410380c1a1551f0b41840c0c24581c00750740b141c1040307400c0032a40342d0740c40c00f00e80641c0c00300d00e102001d5406100075664039072003c60005e003000c0c0c00710406c0c82c085e07201c5030004000b000002811800c60b905001c0840200c4684c40040350070400d0740c0403481d4440208880842401005e03440721445841 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 710010836 1250 710009586 710009659
    0x204050607141e0307032007090c020c270c1b15090a0b01060e1801030c0e0c07080f03040c0806090706022401031203020717030a11120402040f0b 64
    0x1900c408200c04110303001000f641c2500140311080c0080c1c015030721700a075801c1ca0f130049560404100001880c1c01350703c2e8004504180c50b50848440c05805100d001c042030030680e005508844210543c00005004e16218851120580f00065660f2600c0090300c0c0b10081c0021303a0341260020140b05659011444008200200c0c1e610114078003180010301c000d491648080c4c205c04513803070104195001c10070032201039003048610709003540b154000d82d01980030318810f00741d10311128140048080c100c3d500416441444404010040c0802d000d2815a04007040c0065840d41e03d580354a040d01402810303034030901d190312443c0d00344000900007090030419034000344e080700c01c8000b90b586141444000d900e8020000480340006002003103205802900032201c40c1005840d0500356911b080c0110700ca9922807420f49400301c02c1c00074501c1e050140c8c4085500c0c1000450410b0700a00c101801c2180c0500001d124035914904000b02c51f9071900046a054001003000b503003a8101c400700724640b1080509400a1311 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 710012086 1250 710010836 710010853
    0x329010e21100b01080f0702070906061e09030b040602070c0f030809010f09050f06030c041e1503050c0a050c0a080408030702040b090c03010302061c0c050409051302011b06020405060714 82
    0x794880d6030f506510585d504d21194990b102041c50300a00a03010f1802c5000e0000301296907581405800c00600030b0343d03103003800c1c00c400d40002800503407040310b40c00030040002d004001040100b4500703500540c10540050340d42e00585000d515120b203650084000c0d00181c04000709100c0340002511180000780c80e5406100458142142c4a1000380a169404100001105100c0c18484091a400b03664030380c2c0c203031400e500d42810344031501a0894002c00c1e4002d400c000d0202e6011200c24041c2d0030642e003420701140c20328082c0c4034401e0245100f0340302041808588050611020000301000c990400442551a17403140d040c0c90b169803060710140d008a040000006d800e0070f12880161040106654003415039085a00b00285640300107000c0c108642440d1381d98198901511601d46c005119407145035aa0b0300d0300d450301003034850082240d10380f02848010100580d81054411468010102e003501d1080141e1400708004d0145030840c039000f110205180e81003003200c040d910308005d0342a04945105 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 710013336 1250 710012086 710012113
    0x2d070b0a050c0a0c021c0501060302030715090611030d0e21030105030a17070b15042406261e13051f060503060f0a06060329010e21 58
    0xc0d40305442c0d100207528100215000b89100f4101c4080c3c0c0f5200800000300008490224645d8104101081d02d890750b44c1d0000b042140b804002c154010500380c4150041c3d01d00070b9001070400440c0d4414001404042d016407481003505208035598000300740020810b0064220541c0e645100c070024030014504c200140d90b0500c9035400c103076412280014001d0170114016503d00040300200319030114914400e0050900140203145080e21414404d101c12426500d84002c210595003508100a001200e0500c424068021004030100740e844905144800c2280059090030751854610380d2a4500c540809100c3c1c090b441200440c583c80300c0d014080c19075143e50960240f0741011982c020310ba0752050000071451040c804200c007a4145412000a06594500c007003810640c0131101140d001c00c070300042000c50f10042c440d5001814803131034100304007407a404004805140e644135000b08904d1010030380c040d80c4e20400120406081c040d100d800080030303070504503018849841c20507449000302418401b45 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 710014586 1250 710013336 710013341
    0x608090307050309040902360a0204210311030c010b0a05030609030414030102070b04050c102111190f110d050d022802030702090f040c06052d070b0a 66
    0x1035540100180d86059400c81c2000300406070b03107208a0700441d605e05080c4036000c203080440154001c80389403044056043c1c4070680c040000402506000d84103000c2030064205002c202d8219201c20426520003548cd42015100200c148036083e0040c8400103102d05085019004401100c0064078092017480e202c904041c5c9990049611941e141c1c400d05c0208001f0460b0724107102d01c107001500040ca0301c8484e071144c9944402c02c0b00d01380d6a50f88020405c6881d8200b03e01b2ba08032a408514100014840c40101c0002c9c22101040f080e41240d01d03241001041c2103101c00301c0e41c041c09407180f034901620300f1380c8024002d90390744441e00c004103464050304e00b601c05001c03c804280503d55510305240065601c0c5c107500030741013460780c1c60800410040d00c501c0e030080c2c41e036202d0703055000740c000b941c4a11081c410801c1030b200040c00c02c01d60320b401d1814040042d090b40000c000781d65060604644a00820034807940710343c04400b0a405104081121038108105100203082e2980148a21211651050141e00a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 710015836 1250 710014586 710014597
    0x182a0902040b09060f0c0d03021c051621050114190f1505090a0303050d0b040938070903031b03020a080a03020d0204030b06010f0f08160c150606080903 67
    0x14100c004200c00c050340d00c3d04e04014288010101c041c98203004031140710a144c80b005000d500046a800a448001c003400d604c400001e000c14810188850f1400221f61510503900803100c00c2881001c0e000f584e03000d407880e40007040d040500e0710100420340c0c1d03554241c042d8a0f581204280180c00080c91380c0100d000300c60081041d10000b03142d19000c2071034001c2244000782a0300240382004028001350074944e0340c810500300154082e9441d01d881d81c2d0041005004c03a403400554501c40c0f0b1904a1403c00a04c8211000100501d0460145042ca6030000ca400081056000d20014208020208100f1580001e200410303640699220614080760688280211400710000340260340124000d80c00603010754010004520070b40303000750070720300c182c21050241c0e001500700f00d8032100b103d000c011095a0103040d13802400715528040c032490500e40c1c005031515102074018401b00400b085d174400703040d002d0026412041c0e40804c0d075905c1e070182c6030003640c01400c1500642d4000b600c0300000c160039580000682d07a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 710017086 1250 710015836 710015849
    0x1020a050a0b0712022a010911040506030705030d020a11040603080d05150d08040806072c060715051501050406020d0318060c02030a1205040f06182a090204 69
    0x4182401d4460950080b0028100410402641c40005450038580050500c02001070f02d0202040c0c02603410340181210844500e0461703260503050b9000c5045080060b1f140c0c0e005481c00100c54956001290a00941c1e40040b60540701d503414040c00640c0c0054460b07005405942d2050a80414204010a84080384000b034003050080c000040c0d841c50603031045400c030680e0301c40c0640440c48200803e00082100c1001c5d6801d000119040040b4142441000c0c1c0c00451480d0200c0c80900036804c440c600b00d030f09100369060070030102e107001c2141c450204840b0115084031004040d152601c3c46600038003001c442803503046e014000701c4d1050f54050416102a92040e4001e441c5050602404130000e0075540100c0181040081c82d60300424950710405256955950103580e550180d40d802611500d070300d81280c8242c519202c2040003245407844d00012455000c00003161100c8010304c15800350400e402c0c007928815041426100300c0c040e0380c00c0c0710341200c24800900015503681101c04100d00640c450003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 710018336 1250 710017086 710017093
    0x605010b18040b04090c1d01080106050a17030403081303051603120c17040305072301050a03020a0302090909010e0d020a0803011703210a050105120d08100e2401020a05 74
    0x214424030301a004443d41e801c0161000070300c2d400640300c9003481c0310355500180c07140540020281000c2010260140134150b00d9000740314103454500800d018004511810103900700042c844080080140120303001180c0015070035450b415100346a114182c503e00c01206ca034851340f6400d0080c0c0c0040007100040780e40011000314924600c0c50184d5a400913810203e50803951007422a50300c0143d41c001c1e00c0075601035001011403a01b84201409405100782c01884000fa842542d100c0c1c0da80c0c01030032a46048500c1c0360240e122103200c07174103401038000e0180850784506800e0400104200c150f01120782e001201c800c4460003003080c101680c592101d03003800303003510f0400c000500441641402d5080d440049000726464080302c105144804846078800c043c400068106105014089000e141c0c00b502044804010303102048210a03558500c15055809200540700080e44a0b103680c80000020300302d1560b04503052410303480348418203111420700082110a49000c2c04154800a81044100d1340308008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 710019586 1250 710018336 710018377
    0xc0605090f0f03060406020912030d0911010c1e0c2d09180f03170f090105160c0b07050c010207030519140f031b1908010515091215130605010b 63
    0x1b04000384d4880300705243c00806066002841080400041000b00345a11000903040390a1074420648200822914104010015400040f444e100b07450b05c5a12072605410500349400c0c601138140c411183d005008415544500e44000c680c10101100c2038a811a1461451a158003960741145e003a450301e002c4941c03243d00718200140441c450328940ba402420014102951114030040c0100e084482c0900b140001051082c101d60034040c0b60b03006070340304c1100b100d4410010001402c42c01c10003409080028480e020404250251045800c01c40d0040c0082d0340d00c0700c840c1805003050340151302c6041c8a0500c204545800f03440384080120303009802d413501d850b00e503008030b210b0b21541000d07145040342801c0039021031620b507001009008441030b108000d550303146901d00c0030f401908160300490244a00c00800045000c00d136007203d0807883c2c11604050005615040ea0b8601b801d80400c55540700e03964010703c0028129001030a250300c0c418242445580c0e215001d03290349004038585a0200000f8600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 710020836 1250 710019586 710019593
    0x1006080d0e040b0303070f11030703020915150307050705070b16421d031611040515090703020406020309060927060102010b0d0218060307030c0605090f0f030604 71
    0x720090001c5009001145981d21400020300390780c030010007142c0c0d03107025016020800100d2210008003220031006810043d2131030f000314140c1c3c03030000c0120049882c000b40c0200c1c0d560341c1c5800b2203005e20403026a15205c0c40c249070040c0a60380200d405440d14070504500080700c1e140c003030850303040c00b0400320680801c02c42e580d2410118001c0350090314150f00000101c440c09595000e001e0421180d50501030074442050301590201c485040050050101f101140c1f0310419000084482580000c440401400854140a401d00308107600d41c03a445420842440702041075904813000d070000494114015480d094815412482148141005a001400b0243c4545088030180c040064041c03c3c4d80380340400030b05003107501c85d00c00294808440803c0300b4841d07656424481d00b02e9811082e20b800600032200d40004100c4010340108280d035110a600185498030140404001581d001440c090b4064803110080c0498004441c61801020100e1030060180b6065000040c00e06014010305410f80b90b948 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 710022086 1250 710020836 710020847
    0x1120513080f0f0c030a0e0102030a0e15091306030303140f040b150d0f061a090411010c02100e0906010915030504050309060d1d1612031806111006080d 67
    0x204102c004103014000c0c6014020820014108032041c0000745139544004403000c2c0c11100034216050440d0701c140f204e4203007941c101c1c060720400141125844840081c0c40a803142d28811141640e8100e000e01d1290000c40c511504410107481c400d481c14011006642c80440380090219415605500c600000c80c000c12520f07810503801005030003096032b54200c050003141340581c5041044405007001040ca03800d00c0f109114038070aa601454046000c050303c1c0380020403a2001420141064000240010081e070085c004000155405888600603401c405400752125031079400a43c00b455581d00010f29035842051000280e0300d1610f2900e003d9441e03403d0403002003070018003c4400b813008003d540c1c03107655000301034262115203400126904000c0d2050312584d00d011040e008103948001502070284503c03040c55070940702010b442d41e498148a04045914648541d18410100004840031450691124030158407090360070455000b091704460b50011141170740301c0c0d40c0c1230b900000c041e02000391061 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 710023336 1250 710022086 710022097
    0x201090b16020724021b10032705240f0f100801020f0c1204080c060313061b020c10020c100504080601060302071704050609040908120f060112051308 66
    0x91044030a10b946a85868007159215400340710b40e60542d0f210b03404c600d03504000c00d4007024a0102c18240840300b14000c10841c0c1024a41e00c820325449a41070501210541c019031104a4051464845c8a969042094842c80742450b40b001c110340811002c401100d020f803000c0d016840c0030b0782d100b64a9449a80300d41500b80041c0c0f51141103200604002007020f82400904030002500401c01e6986241030303200f0f40f60082040c40c00300314000034001044440000306803d031109500b0360391030369241e69030310544c401c5c0300440c64000d00c0b0030303c1c01c0b0f030001038040c00b103050503aa8a015000c690500d0241b9080101d400405008100180e100c00040c81d281d08040e614948001607600700241440d1b1500300780b0341004400d13001000003e6001c61a1002c2c00380c3c20360f0901d20440c0d8200814982030404002c10004d00c00c0c4254a40115110b6141d0070411207000101ea171180700c03280710507410307041080785c014a1403401c0c0c46041c002104054203c01c00052441914090202c610111810b44182d50b40e000070390300034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 710024586 1250 710023336 710023381
    0x1b0c0b091206040b1509160e0616030903060c110c100c05010203180610060e010810120f060e0f0c09040507050a030b09010f020301080c0f040b0a060e030d0201090b 72
    0x844140703903035124040186600544c41020b6076640c038036000203c2900c0140d00c00c5400c4c840c43c50308040c42403410500c880381c5c1c0c41041c642342006501211401041c01c600c1035803203a15000007860030705401c0c075520030780c10340c1aa80f058a007844520b2020001316084010040c81c1c4c0c41c01d401c034403450080c514181220120442d010700703004048100c1900c48908a8100f01c2d01000707120464010b580c18101c05001c0c00b6841800e10100ca007200e410840c0c020100c200c0c408080d810310031003002240303030041003011882c0180800000803844143d00e16018071305141040d02211694200443e1400d03900c3d0102c0c0c0d010301c1528000043c0001c19030740c1c04100080c030010b0803d440c07600030b00c0030105440c0c69601c140c0003e1805400702012508040b10050308482568592001c0c5a10600040c00000404140c603108884100c4a14a104814030001801405405d1016038007482042c00001d9154002d1861040404103c045c2c40800d071201a040c3d00361441200014a003c01c07400002e40d102881c1420003051810 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 710025836 1250 710024586 710024599
    0x60e09071707142803022110030b0910050106090b1804060b0c0601080d020c2112031602010f02041d09010204030501020f0c100c0230030106030c1b0c0b09 68
    0x12520003810303041d07022000180a1a08019a0043d2130618003240d0110034000e20f002c5180007610600306041384140711102c4100740014000c2042a001040c86001030740d046a11503141d8100580810381d02c2000e00411341d9040d041c10700000c3c03035500034088101210f07401c44d591854603001d500c0c403a042e1106091402d52040e5100404104212500c0141c445120040700401c107a5051240c00e070700e80100542400210350150020307040d503459004000c141d01c0c8001c4007003001c0040c4518041c0c1444c00101502e40160004030402441d1032200c40e009100c4280380c3c008110f280842c140d50002e030310841c05901110300c94072203030706a96086514203991022406c00014205600da07901e05003a684900c8100380e0500021070103151682c03052280c0450303101200402c020154040c00c002c0c0d00e560000c2e4020700b1000c0000040e031260080d01000c040e60110101c8095600e6845940190081c03462900000010380c0d00c070300c1102e0000194881c2d00f1019001304881c031455142c40500a5941d01414801c1d4200702c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 710027086 1250 710025836 710025857
    0x613020102060a0e0127151b050f1204030207060f021501140604030501020301140a0b1e0307050705010e030d0501061d060d0e010c0c0b0c0f092e020304060e09071707 73
    0x6d9180c0b1810829000401c070340101d09400d030500e001c0810000b14010b10392840c00301000b8080d18000100100c041e203905110380c403010810300c580e10b64081e03400c00d0b000ba8a40303001080109540402c0780c0741560300035240c0280540c0c02e201e00f05d0f5504400f40c40c1200c1d1914035001070000401000d09030140e58402840030745840d8490b5211400d80e002170f40301d200d6000c00910141410310b881c10544001e4026071000a00781844d800e101841d200540324082101d282c000003080c3c04500c64001c07502c0c0290440000e00244d01d038200744036074940c003049103030344581d10340000458507911600415440a640e8402c4030040c410741e07010800503030701c0507a2214080c1c0d66000c04184020302805a0241100c0c19120816035070521b040844414600030a4078035034036420046620144682c80030b440344420181d4240f0410541d54401481410300c000c809030003c0042d2140c42a296800401082950641d03520301c22654404c0301403294610007900c401c130210b140e02407220800b258140c0c40a51200d81e914240c0c0100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 710028336 1250 710027086 710027111
    0x170c0c0a03020106060905040b0603040b18030f0c1c1409030723120c0d080714071e0504140c0a02010f06091d031204080a020a0b0c040501020613020102060a0e01 71
    0x310030000403030140c2d4554404000d0b0340e801200fa10000c0105503401c3c040151980b0000d151440003d000034000072440b40801d4020f190325006400140c0c5500443e50307201000c00742880329402030303025800300b80702d4200030601c1014a1030139110030701076984038017045105445804d0b03e90b0b001040303266014402d100d0001f0b001d0900e210002441540705507041805400b51003841450081c0340e051a00782ea00201e08001c0c7c9803610725852303030b00030b80060460762500d41a15050124440ba86468035041c46507040100b05888407503050780e111910080c2d0000b04a41c0c03070081c44191092200d01c1a402100c00e070005030f202500b6801031401c40101d100004000d02d0300200c141c1114015017103007070035966440c810800900d21181b0500c00c1c8440c84020740c100361000107951000381008100401540300814007000480c02040501002c6901030740201c83c2d071900449a0b00a500a40f08480c0103210b0741c80822601455600c8007501c0c00e130180e01414103a41d40c070a46c00003604080b550104a503603500c00d1108078 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 710029586 1250 710028336 710028343
    0xb041a070507030b09151012060b1513080601030b0703020904020922061e031103070b12040b0c03160f0c020913060507020f1f06091d0d020d170c0c 65
    0x746102e280200d00f14100346101031b141c503180c0f090400e40107604d06c062100180e20156007070b00b15424550f1b80d80040701c851514402501b90303540001e0300450034401e0b0501002c0c00001410040c814808000481d40d07645260381d54900c000c1c0300c00b40400d2184c40100d504035105e600102002c01004c3c201514205035040802c81c41b1200310f10754074040521104000c0320003181e02a00300203000d42621803480da00540c910306400145444000d003425820780c007401d520b440920a907001004480310300ca4403a1140c2a460030040740489045410100e110f002598040350302090f03038040ca66040041040d01d14280041d2440d200c2c0814480601c0000a140c2d8016a03908040c2c510810900c0c0c20000c0858041c41e080044c1c40d000b818107020764100d039081c070780c0140002131151403444c4210140b0040c000001440d03001480ca40e000a82914146000c000b0781c0008454030311410001441201c0100b00e044004070386445503c42c1b41000078001d161402d480c8048050440d0b04031000350340d65850f100749601513515 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 710030836 1250 710029586 710029589
    0x3020609010915092409050909070f14010f030c020d030e01151706090d0f030c031404080705060105040218060705010608030316140403020d201201150f0b041a070507 73
    0x81e8a4501484803140107940714404000d24000050070178011000074044445600607540111031a80002d14401010030014004000c1c84002e00c000720b4564640140d41d1010448103404140080614244244248185201211194060600d510160b041103000d0704002c204801c0e0366480da450340030b111300e0500c0d9140060201407000100d840d0301d090744500707001000b45408881e4100c42c100010f044c0d0000c3d08000022903a1800041258180b00240c0040018400b841c04c0480300d4030810040004d20401001d01a01403011903120707030303a140c0401003a445007054220301030850050100071418400c0c082c010f0070384140008201a5125524186190002c5034000f0001c1490619024a15046085e4692401026000514260440d00400d090a281031002040021020b400d020643c01d00c1c010001c1a0100420b80d030125902e6810700c41c00b0381609411140c0c90740c0c0071100021540320f0280c1080456445102007410f00340b4080100590704030381c81d036001810100304500b20000320240b0041c030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 710032086 1250 710030836 710030879
    0xd020d1103070c02041b09060f0306030f0b040201080901050c0904020c011811090a090218071e0306080712021c081308010504170307080a0b270901051e01030206090109 74
    0x1900e540f00d500420055400907445003008100c0b40ba101c81c41c03154043d00305410340fa0281000b1000b5201500e0480050107141d02c041d04030542403010408201c15403503803501983c000d80c1d03046041d446040c1818229002074070750000c0a0b5080041d100c45041503005480c05284490001514801c809080c403c448940e03541242e0341c0c1c1c031007030005071a0b103401c03211240c001050510403ca11b20650307000c252a9a0400c40c80907106400a000844c0a840380c40121181007032a13082c001010110800607000e05018011081c0d0b074040d20001080d05c902050986a145400410b03c0180200012249903124005481034401810403c800001c4c985454020b00c02800440d0002426240504200700c245c25409100c20326079400b002400f642d5980201950b40000b000703840007880c9a1221700140c20030031030a00c21340c410400b03100c82a580003d01e80359680b00e10305210080c8481d643e0000100302c103014121040341e4401101c0014005030900300c0150800c0301044c1003c0c4112500d5000c1c0082041211140b403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 710033336 1250 710032086 710032097
    0x51816110f070e07021e0c06030a0209060a0c03091203051c060e0c0c0d0c08070605220609060c0806010c150609020d05090115050f150f07030903050c01080c0d020d110307 75
    0x10382c455040016155165504001d03003002281494610b4584000d030700408e22400000c000700354800c90316412250b10070310040449958030140c0c400503251003e0f10405a0101d0310b4400001742c1000e12131507110701a6816542c02d89410015809000c040d18442c021b07a09460b95514080b030200d884080281c05000105038441e1030310311150f07001d860403121207500001c01462041c407400107030f600415905803d91000011400d5551000d56240412020070b02802300005242e98005124807603010031040d9004020500003076040032800d80e1500000d43e1810300080b2040f90050206840f0f2100c541d0185d50f03241c01140c007690716003460f004c0e40c008181062180d80c0c0d07034051251303002c424410038144d501005062900d00d80740400040700010306000707250040d00c164010418040485003120701501c180141c02e51180e4543c1002028000c0740d000455035881001c11080386503014540d028071403104501780503e030407000c0c0c006101942120752484000e5071621410540480d80e980a94403a41180c0d542 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 710034586 1250 710033336 710033341
    0xe0c07030302131e150512342102030705030f040501090209100611070f061416050304030510152102030129060f0901050f1b0304051816110f070e 64
    0x3105c03001192900b01405105c020000300305040d41c0b94021540c001b105520741c02402c10001c1c00d90400640000c100d500d0855407001100655402502000c1c1c180c110030b05140c2885820201034040b48401c0d1461070114505000003155400c031b004100d648180704a0010403481c01950205910001c00d0b915020601d4a00005102c9a9070080e144429a04041d00400b521403400101090441031030090004018000f06419890a0031104442452020048100b40010582082612500709001c22101c03401340c0300031502c0040c16401403440010a556000c4d500519002e00c07440b1100314680c88003d81c03c44400b0b80350140c0e80a201e200050b2000406145015902c1046030007440030120000b48901c40500016914000c180107480d0400b00a0901c00d954410000441c0c555015025641c20780000498150413840e0010010b0400c454090766900d90040d055480c400380000100c8940c0c21040342d042064044c94891403040b2510382e00b078001c1e20810084c1c410224280441c42d007001d640694070409 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 710035836 1250 710034586 710034599
    0x402030f0303070f08090604020d02041d1e06010605120f041a04030314060d03020303011a130f050418051009020114160c0e0714030403360e0c07030302131e 69
    0x10546d000178280040c20343d5140c42c1e4006940c034844c0c01e6002c2d021341d0361620b0080404c0c150703802e230201c01158001202c800c1e43d0b01c0240c5140d8980348011001040c0205000002c03054000c10980e0703145c0c01d074210940e80c1c603500d012a8900c403500080c0103903804440400b04844007010340050502450080da000704001428800f040203041c400740043d4022800c0352410000b00e80e000c02a0b90565400841051185455584030300d024042d50081d240074410987c000941030102d00500000c850f015501801004020032880d054400010030251058014031502c0c0402a86c0d503100e200c0d01441410b1070225031013102c00001980c6c01c1000c1803d45031403900c400c8810701088030240401407180354a2103c507407800803401048150a0501100300880100c08541011b000c0e51203010031000d0512500070200c03107910300700548e0b0000041e00546440388030340407861250071180607100f00d82807500940340400c00da804500039030004030942c0c10035811840100c4c2e10f200841c0303002c5881440311100382c60305003003c9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 710037086 1250 710035836 710035847
    0x7050a0c062d020c011b1713060c11040c090b0d0f0f2f0903030a05030115020d1e03090204021602120106061b030c0b0c0c0d0314010302090402030f0303070f 69
    0x1007508048440001415500c43d0703000410103070050003880d10143c0426000001c071348942c1d8085000300a14020035540c0051400440503000100c9180750407081e03565150b1003541d080803403c3c006080c544807400c2c0c462a0b820a6002841032500303d180c8041c00075a981021080342d044070003011111f58484030442c25000550280c0710980348400070400c0100b840d03400814540c103030245580041014480d50070003282d030500640c0c503000400703000d99a079001a030710014525030090060181c031752680303030840d4540ca100250080c40d02c801c503254011000c100c904002d0b001c0c0c03d00d441c54800c040e1101c0529006803120b00142440845440b000045000b1602c104101d00625414038081d685c5000d0041150b95800b00064180c81c02884a0403010ba61506044070503074000540505111284401e0000010600000703204034200d80301a40c69100c5405c80840644068900c0ea00c10381d4008070040c4003515100b40b0307043d0000d1005045a489120340c880c0343d411500115401c001107041100317000c013540e8201c0f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 710038336 1250 710037086 710037137
    0xb2409181e1b0a0f1703211e07021e030903071202100503040c120204090605100f060f020c0418050a030306030c090e1b06041a07051006051507050a0c06 67
    0x201d4400340c06506001250075500700611504034481d800700e42242c8002001d208039520011651150b8030928110107c8002071030003074600030041c1c20888460f24107404419840b501071407680c0d01414030105001c1c400384583c4054100f814440c0420401d04c2140e41d000c00c0514010b19280440322005901c9004004a4243c2503a449040c0402042003100103042c0c044101c081c0c130a03c00d6440c100a4840c008203000344100080104241c1c502006e02c40840c0a40301c1e9081142e00c2110072000e038035201c040440c0d002c038026440b140541c1c0205200c4401d0300e0507800050f1101441c0f0781e0b640d002e103010b441c0c141c9400200c00045e40807903a102c00620030300080410240c041c205c0d001c000d100044000d003e1503592451003600c0454071500c00c461210715a00c86007224010700d40002c4051120040807070500b0b1960024204a80701d1086220340041600d0030300598081f035400605042c549540c0a01d030b00e0041d0303c904000c030740c28056040b19800040c401c0035038401034092982c40100201102510703a40c0168070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 710039586 1250 710038336 710038339
    0x110c060a0f0e0a120201021e1305061303200a0314010e120301092003070906020c040506100f09030b0a0615030e030d0b120a0b2409181e1b 61
    0x20090224182c040c00180c0103840756005980d950409100c0354101d009004c1c0070b14807010350000540a2004501410281050f001c8100a08043e40d94440030010140708038040749009602c3d440040001c43d144420080c88040b1300c000121580309440005200d140d0f0070340089441054021105449500c02d2150081c0001c90030002c0004209c1031b46500e60798041440341404181e00c4120001d0f52840c038078030070310480e0003a01c001c40c1c0b24100104041e0410200d40a110014410100c5013521403903d07000e510300428014002494a00c9814411203014100c442c00c83e00384110f0750400400501d043c543c031441aa41090b00003003650400c103043c565101040800c4003018101a0340d9448044040b08031004001c0c10040080c42c0f15071000801c4008250042e400118000c0c80210021310000b85040fa110310101d448080c04101518111440c1200c00850706800429407400903071508a40385041410111104c12030b180c0c0030a120000034000721100250300f0540086080c1100318a024521700c80d80b490 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 710040836 1250 710039586 710039591
    0x3020703120f0504210203070e0106021009110108041704081e0d1403100b0c01020306120607080105012a0309030c0902090609060702280e010f140f0301110c060a0f 72
    0xb15164010142d000d1402800c2c442c3ea0030100d900f4101440c2010011226405401d4400c00c81c1d40e2015000c5000003446110090301130100c01442140303551141ca503403240e00814031380c0354480c40001120307130000040007110308030303680300c50f00103a103581c1070151004042d018003c2c42c50816110381400f800c08003030160071856101441da801c0380c0384c10060704110341d10f2000748241c0720350310708546440715401c60740702d903031207085c00181e04001c2c0c00c064000710301c908010b1300c6d020b18030502882507c2d41e601c01112200001903840740140300769841844103450f4906001d0f84101082051110340c007412014034022804640e1024081007085904041d64008203030713440e0b045042c520780001160303d80c402c00c0d40aa01c2000009076a40031580d81d0b1200d60f01900c48502011400240380e40800310b00b400030b0107148615407035080000b8066151030880401e43e06c0b507841a80041c0c400e00244140048102280e40d0302d552a41007444072045058040e02c000d031101002031416082444002c4116005040811041c90 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 710042086 1250 710040836 710040857
    0x702070605120403030504020f12030909090309090103060f020f0c03031602010c021e210a02210a03021614010902190305030a050a03060b030705070312062601180302070312 76
    0x10480340d034943c49509403c0106255590b0301c0003403c0c0910585c1c1055000000100030f4105841c000003030501c204c401c1d0382160b0241c071082c408179683c1c000c0c03640c0207920141000c0140b0000d00d8a8105c0134841802150240c240b40307074600300000980048000d180141d101004104a00d5802058001c850b80540000c11020031400802500d0b80c4030305550519003134007409100305205041003100140c140c00310a030120b80301400854041c0360700200010005104107031103140024450705480550043c418042441c2c2032505400794081d4200d00c040c20400300f06203106102050128090b0940c200c0080b0001507061001d2041107841080f80c44040b1141c2c03071070b503800d04c00030308000300306c500e00300d0141040307a12b031200d04500b18064602c60700001d00302840030081c44281c5400c9405000c1081c41703500e50001c0030000203080d404607001e85c0b0840d8400c0c6841400c2ca05202c8698515048001200c40040b48142110454100141c0300c00c0c3e0860040e405980204103118074240d55018030b0005152511100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 710043336 1250 710042086 710042107
    0x10f0c020a09020f0c1903020610061209020f090901050a06080a05030d050c040f12150c120e151f050607050c09181504030e030c1e0303160b0702070605 67
    0x2040d01e030144401d800d41c005909500c490b07000e0195134201d0314a00446080043d0048010320200a106080700948980d1000c02c1c4465400075a00d41a560b960b640c000342441459100406440c1882c0288d81008003c03444403010740342c800810340306002c614004901c500b01401c8000440c0c5180d03005911070b410400000c40003860204c119001205107030300200c0c050302c0d400340c20041449541d1100980003c20301000a0319018504c1e00080f4900841380940300184100d0807400391a0b50912140026031a00302881342c195042d4031007902c5651000407542e404c050016100c0500b44190351048001d401d130050a03208400346c080e448060042030710b41905080840d036500d6501c1d111300b10198801e204900015000ba1015031001d005020f032402100d0700b10482020003164001705071015400140700c0c1001d40164280000d0903003c0c2203010b01680c45030440700e54008038072000c21452030344c10701042240383e01a00c403425014070321600403001035141d82407405001c2e2070170843d907104d14140b040c01d120800d0340 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 710044586 1250 710043336 710043349
    0x6062301020c040c09080d03050f160c0b04170f040521030406110a1208100f0f03060519020a1e020703020f040c0c0501150527041202030706021602010f0c02 69
    0x18041a1400b00704d18259076000e5841054940040c1d086100300c407074000351290b254001174007031684848141c5a9456544001c15a2501c605004010808900825001075921540300754802d0083c9940d841e044442c502c481100e0744214003d110071030000c1001e02c2146401c580382181d01c20104000103110081058450312800f89100706018040c2c0105c46101048042c01400c1160343e20952581c01c4048020015004240c00d445112000c101c41e4400314041050105800503160030405080d00c3d245503542d0000902002050a603021942c0b20401c1407007403090029054107503c41d1900c28440200071003904041030540b89600c11940306c0c400400140e201c81266054203070703050340c01141080c800f0f12705039182e03410703240c00030501c1d031a04480c0416110695619801d4410441d1050300100740d1208807010742000d1000006803100d00da021800064444060b10a900031a006a0303040c1482912840c0403600490014881c4003282d589110440d030340241a1a03090025040c441d480d8001c580101d0a03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 710045836 1250 710044586 710044603
    0xb0f070207050d080d05040812060d230307140601060815100e2d0a050a141009170706080708370504060603050f12120c0c03070606230102 61
    0x1d18103040100041c4140c4000b00d4084179141001488581803515280410303500949840400c1c80100020840600c0c081650300345443d00a40c1054280604400d1007a02070f800c1501101315110400c01000081e40b0314022020024581b0003400b4250700d04800944035074801800c009041454201d8a42c031aa20141061420a01d81c0780400d40100450041888110580c3c540090482e0403100c140d03101d0203030208502c5c4480c0a440d54010703103a0355024000411070600490051103207602c54601c070b42c240640c1c0c5c0c40e4202d00350316144034016960180300c981d80e6194042114542c2026805000b0341790403495564010100340340c08040c602d41020301315094602d048034100b09521091030081c400d000b404a6001010413010108224209480c00d10000c1005200864103030040c441c0380751f0803620200345d44143d491040c141510304181d40b1340c1440080b1000b426a04a40810f01840000c4803041002c1c26150348510b20004065040003a48031b03103111400c204a480ca60840720310740c02642c1c0420044c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 710047086 1250 710045836 710045839
    0x90f04030f1202032401020307021c0204060f0602060709060e030309010c0c180905013606021e090f03031303061d0a051b0607080a0e12010204120b0f07020705 70
    0xc2403100104400c88036408165005600d42e8004814070400300480c1040c07191754580c0c40442240d03000ca48005980f640543d02e0003a610003100416844480c100700b299090b030a01c0208002601ca0700c5003821815064290007441c0140e004401300b0101c59000042c0202800c21820000d10400d0b90400107039480c80340030032842c100a88102d4490400180703802200150900302003079512f60b584058140c0040c407100200b41d13155030918181d03400d0b001e0124101b0f40b001e04101e8841c0380d010409d0074079510039400d99100308d07400e0b5400c0244242981981050f0210001030520040e503070a15801041018002c40389000d10139002007100b40881c10030b0207040c0701101e6004401241810b0300d40007042078200a0f1900d543d1030301407000d010b02085400b054244410425a60480264850a05100c40b0340600b841c020403811003000303e074554901604004502c000000e206101041e031501400742660025800540001020385401c8104004942c101d44d03c4044010100351602c0c00310002960b41410344100c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 710048336 1250 710047086 710047097
    0x50318071202062a030c0714010207120c050d0807060c08070503064c030504020a030b090c040905030c070608090a110d051203011502010c020709110919080606090f0403 74
    0x3c00d218803400184c070b40e200c00f0f802c08080c030400d40c1641c0142c4a502410101070b1902580001040704414800c1500c4182c0c07069009082e070500b081c24401d402090300000340d41c1031091240010351f60b5101d002c0707041d40d40e200c0c0407002e0300c6021503c1c2010541d02e20242d01c00c24490240104440a584281038951190048030b0300400020b84d01440e502c0012028214082e808551b000e82c8864681c00400070815030306060140001078540d07804604540c429140203500a03804102000070400321156190803a81c140140c406101d0041c000078200c8a009c24226910303040410701ca1011101808a40001e0950b400c2070325941c03911244c1d0b56240c0d840e40e034000300b000b12080010307246611112503071a00c0c0b03a44181100d15900f0b801504607601d0700240f113009056102080c801801e148107000300c3c1c08a00850b0002c200c0d550502c0400400350210205500441c0c000703000a19440d03407601c0360782101040f098030322004242040304545c100721005101320700942c1c200b0103002d01581a6400964840e0300761525 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 710049586 1250 710048336 710048347
    0x60603020903060613060e0f0f06010c050703121106130201030627020a05120702102304030e12070f140108250e210610060522090c05031807120206 65
    0x900003446c003508100303658050300e000c1003200312507510194081c030140d00415641e5640c640c0115040d01004200601c0340e040b036841000012200352a0040700c0c9028108029036818840342c01e0711344041101c0c060041005135002c1019560540b2400c00541070840c040001c201f002880721200705040703030302240c60b542d001400340d0303d0038411030035910040480c0a01c4109408c00100003541d07050340c11121035005280c02201203941c2031b018806e0750000c00c803101070b00d0103680b02d84094440c40c442e1107210f604010490f6a50344146014808540500260108030285a0034081449d51019050011505100a0106005020340f101303000800a5804c020010b0b2250f1344181d04841d540e4020407402d070400303240f42281c052444203100501400d0070381c04c1102c140e41d5513500600c81042c10707441030070003042c41003001141d00390b00d0a85800406214401000c003e965a41a0a04841c0c004c0100c00000308007005001d0402003207554000005404030003400a1420000080300524800c54000d00c0785400094 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 710050836 1250 710049586 710049619
    0x70b07060e07030b010e0106020105190b0a0305101d0c0a0b0d020702130c021b0f010f02030417060105010f020c100302030a0e01090c0501110115060c02030a0507080a060606030209030606 82
    0x1c4800d0940040050b10011540c80ca006201d0070760a02a0341c40b01c10325a0004914a031052044510990500300c0d103074800b031001d1400318000c0c0301256810750003171501e50001c00070407420028000ca000640800241d40d806800d082c56002e451030740007481c55005951009005d03074508904c0000c0e601401010b030b07038401c0701e084888000d07c01c01c100203402c10a002210440c002543d07200714044c20517a020b617a10038841c442d601180d44018031442c0da0200d0340c424070341001d500c10045c2940c0c5048500489141030b8807801c03c0c002010810078401829488031006121035680005450f01000b014001070030b0f0000076800180c24504450401c3d02015404000200240c4003608500c8160100400801451006041156205d1280d005250105000c040580e0107290305109440c1820f43c00f02c0e2400419080ca4001c46200701580c4060f03906104002007840414001d004540c01443c00c4801401348404c1c03813900300d0030348003039520100034540306100a90303841d00d0101302c4035448030048038403820112240c2c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 710052086 1250 710050836 710050841
    0x50c091e092d10150c0c0315020d18110108040b04060f061508010504060501110709050c070b0106211b0804031b080d06050301060b07121205161202030603070b0706 72
    0xa42c100b101000d03001c207110080302201e1018060b20b12072030301268000040341c81910407004160740107001c00f002c50010000720f01c00c0341d0040d4000160010251904840d00d601e081550383e404050301030b51504003418000c11034503020204602034203003017000035458280c403900742200000704080c0c105516603e0390f0441d95001d501104c06882c40e03402c420717500c0310741c10001005c0210901809000b01d00e8a4004101580a0503903602ea49d04208024417900e42400003501c00750030003500d03640d440700041c00030344006010550a82e010b03060690320202e0f01d000da10400ca0072090401d0503460800d107040000001101c466402130780507023036424000d44a48891404403000b161082001c000c09511500101c10403402000800c00c0c1e07016131400780304035070b2030380101400c86502d84a0912046400c105900c0024240b042000c840340c02c500300341e42e064250303020f03081c00c0e00d100320354800484104101c0b48581c9034102c000c041044c18288011425882c044000c603942d205140154020040c02241d11020810b00c0d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 710053336 1250 710052086 710052151
    0x3030b2119051c0305150919090f06021606140c090d020a0503070b0c06012c150402030a05041a07081504020705070b1b0f0a0204090510050c091e09 65
    0xf01c0400c0c043c0e0a15400500405051340d07183c200c8055007000d010b01d443c084010502403500d02210405440070380070114003c101e4000221015420310440a011030883d01c0079003407602850250b54803842d4145060301c100c51070050004400c060103020301c0b01b284c85850035a056004140d50070710101009000180140e405940003030b60501c1003500100751a0101e034007411405001b441268400d0f6201c0d4424500300d10107154031441c2040e0000400c0d511295440c0840d041003954484041e8000c10030301140a0364022180c0410003920b5101b400104000f9a040e1a0244040016048207007041d07840100402000f80084444a00c85007019600755a658101c940c001da00034201c5043ca0f07610f00b200000c580101046184140f00140d042051200105100214079416000341c04800364640c00c001c0241514142030710300d072180303880d0010305408500c606030049002c0c4205644079a105003c00000245241c44014000940d146c00e050980741c80e082c40303820114519002c3c44042800c0b00c0b00440e0b0210307 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 710054586 1250 710053336 710053363
    0xa20010c0501051f080a02541531060807170604030f0302070c080f102304110103090f03090e010e0c090114090d03030b211905 56
    0x300024442070080344107144c5079101c2403031504180c1c03950f1030380519120391000402030340043d000f08150200000c0044200034184010b000420640c0801410002600c1e2400d030070b681c42c6035047c2c19412607850030014594419044000082070500800200700052507031440864074218001400e106402604003480071f202c41444108172442da01c0d40c040d59200040d11400c00000900c0054095504001c0f40d854400c07500b54540c0d042500c04148110000d500c104025580082050307000709a00c4414820402d400161500804038400c21290760022904004540c1108141400502d45085400c0c2d00c6a90300640014001d03141070401c40c0140c0103424a004001c0c00d00d41c90441a40070160840e8040080c0c1c0e40c590b00b10a0b9aa0300c035040300201c96000c0e2199991042c05104112840d88941d1a131988012422400c07824010800d020441720009004103d000c41d8450309501c0060902e0701c00c1c015074080d42c010000a02e260180800c8d104c0385844040031503198080e4024040c01820001904080507 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 710055836 1250 710054586 710054591
    0x1015090e0a2a1a0f040806090c01110a02151207111501211b0b0d0f020a0906110118030314130809060d0609020a021c020a20010c0501 59
    0x9084062038541900300c00c21503010203039101d880c08140d0202030340c000342d01052407800d0090f400d050500b80c41044424010140c1d002c104401e100300d03046031001e40014540e2070002d000700c1c20403c810605040c20254400d0420004d01c6440542c540c0006004080c541c068807030201c41c15580c5401c60319480303080e900d04001c025000c244a24507500c510744402c00010b00e000d4540c1110b0000880341c0441c804e20408280040d01e00d040310621403d05a203035260342c8145081c05181441d20000100460303140c1c03114442c0300707020440c84201e19241c003480d5071032003000004503e400c1c80b40d0f9015001c600c0a000d03d0302004280030310742c0b00c14002580314186642201c8902484011a0300d001005459200c1c040201400f0382c201244110380b2003020103803056404014542406090414044150802035600ea101a142c050000f8013000130300c000c1c12501c040354040c4c0901c07610507400d141000303800c21044c3c04561008250b80d02041d551810901450281309003012644c810f0700040304e41003c0803001505551 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 710057086 1250 710055836 710055851
    0x602040f0305070b0301081506041803081e100b0a02030c010603110f0904031e090504050903030103031808060406090819032406080402240f030403020106090e101509 73
    0x203000d421448122031040c0201c0e003203507841d5104c0081c1404203101d00d0100e07502000007419820154401ca642c02030000c1c200290414054079144650f024500c0305401043c0600c0c1404032400b031aa185c0405a8003100f180021820403000320800610b05100781c0b960a0300109440c51800c1c800d00c201d809040f07001009000c0c5580328241245c414030321000d200d104140b860703003009840c04e0004d43c90788140d41540740c6001d030031440c030070940b07084841d48220300400c10020408201c0b42e9480c8550350060010074010340d00c0758114900030700740000301e10001005454a01c420001c210002070141e40c45036002501180406491808083c10f01030180c014003005102c0010302c0100b541603001140d120920700c58510422105084d02800045501420300000d15080c0068090705140405103d40c4a0104400e000b007105c2256005450300711800e05403041c8000028007080c15424040c1e0406000a03840401404010681c2541d4801d42405110001a01e5404420200701684407100041080b00024044103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 710058336 1250 710057086 710057099
    0x21c02030d0b0d030507020d03030b030d020f0d0203070b13060603060c050706060e01150c0510060b03070e040c050d0f060b040b1201080109020919060504020d0609180206030c0c0307060204 83
    0x81e0041e9089840d0246054208a000e241060310744141d1078050301d5031803502c00d180e0284031510301c2c640e80541c141030700e451a60b100340d2070030407620400642c654040c26030034011815041c1042c910011440031584144000800f0031095044290000c4014041e0402d0403620b140040181030309038000b6060a00d486200007140d0341100007044d44034400d00c41044281c0e01d902120390078510a010306407401d07d40700d9941100f1030182000c0c40ca400c1c02401241c21240d0048240002e403a000c0c0c102d01d00351a004000c1c003001c1a003040c5401c03102102210140916150168024914041c80e4440003000351900601211b0100a601080240844a004a85c0c407501c8003050401c5607c0030040304101e203103040002412040c1840303900140c0381c4c0149103a000e6154800c0510052604469400d4156174403607000540b0790312440142018292014040b9034503290050540445d500034840407600c0a0002c0301f0001681c805046a6018000c200031a0b101c0141c0702c1140cfc50b5000b0803900138200b03032001601003050f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 710059586 1250 710058336 710058343
    0x40b09062b0b0f030706120e2802130204030b0f040f061b2304060e190e0103020a050306040f060203150a0b070519050a0303050703020d020d06080106080a05150601021c02 75
    0xb40181903840d00082c10356042410780c2c940f030b07605c81e100000c0c141e85038030300c8800d1803034010380b07503440c11501141c41c0314071502d860382c02601c2c014000c5a01701c20030328215821130800440b08101a5a101c804504043c51a01c4400701020010841c045a6130301e40c0001d0100030080c4d11a03a0996000f5004111440780c5480c5c00c0094503040000310040303841701201d40480420034012041741524641080d0815140c050180c603010174020354036500ca614103100351103400c01c04451100528212081310119451130051020800701030300b00d2802500144200000300308203031800e406841c1c0c00840103a07079650700014695403122260015502048188000070703078074010070180007540c1c054000d4940c43d041c0304008201015503888003e010390845a02e900c0400c1c02640320a51240b010b05016140c1000c81c3c070103501300c1c1d026095040e10240c0d140c209200f601024881c030740141902e40001c16000d401c80c2c031450b0f6902070b61400607084440140000c0c80d580d100b0300802034045504400c25224014061003c2d45 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 710060836 1250 710059586 710059601
    0x40b10030f060509010b030a0c0e07031407020106030201180518040c1d18060610080702011b050705070506040501090b030417070515150d0303020d290f06040b09062b 73
    0x1a60034810800011f14011408522183d40803140d80005c80ca40840a0380b05070008011106150f607614000900c20000f081c00c074490b144a86c0001080707800c520000d4580300038020103104a848000040c0203680300c8401e0b804403840350101c5800c1c995507278503103c162821035030401c03e101e650161701b101c1000d5030300086501544101400b10f24025030342c00900d58580b030403661103501424440b804442035000d0002c1035049030304e81c1700104c1c54179280182e81c03000c0f0340780300603180000310009541000d01405112823805001e04890541c602894400001c1044800d400382c003144c40c0b00000032a081010001414005180807500b0310707155041c07030501c0303901c1b44071050780201e100ba12000052010008182c000700c801000a0919982c2c40032510101c0c0290000c940e210034150b940d2030041e640d460300a40800e060003040a841503020424400d201c1807081440303445010314014401400344185a0090300c01659050324642d0b103a00000302c0e1000700744c112140010703004204181a024008041e081080c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 710062086 1250 710060836 710060851
    0x302151209010209060a110c041a091b03011404020d05070905310207060b22151a0306180a0504030e10120c02240114030a0803040b10030f0605 63
    0x20407541c408600500341d115080c20154070640030001c0d651010b000303000c81400602d030301d07080b01d500c1c2021a01040480d1540d800d4130011030390082c507407042d40c6003400989a229030300342b00f60300703c040c0680981c15160206004420070000c4d500904503d54030703a0b5066903441c3c88129000d001d1810039400180c1245000d0051501600d003200350504605066420303886403c000000b5980b254100303e1402d002034010030812143c0315181c100304001e0755507a00d8201c820029011581003000345100200b0708441880b0014400b100c503065017008080c20203d8051050b10300301a443c0c0d41c90b502e000028100c0c02c140c00800030344509200c00d00401c100250b000a00c0785121f83c81d111646404081001030400c0c54a03d4403001905d1114207503c525030baa00b00c0c0ea001c140c140115056407501041c2c1d2284030340050060b03a001c0c8424401042486507000c0001000c20040d405031401d1107590322030402c10301c40204042c1c4141650b0001c118204425000309009607000b031825402d43d041449c02401410b000d070307002c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 710063336 1250 710062086 710062117
    0xc1614030601030803010e060a0302030d0807030f110405060c0304180e2109190b0f0d05070c020114032a0a02060109060f140d050a0302060f07031b08060a030215 71
    0x8590505000901ca41602d810040f11415a80b0340b50004488030b00081c100b9400c203162220000060720f0070410400c50030300310b4580d5200c030b140c9000028102d9050b040c0f150320745c0c0e041000c0c0c25005804041240c09032001981c0750b07695144a8200b807841c500c116400300640c00400b1081d081c141e0b103594002056404100191105a65103270440c2c819418090a40204804104280c0280d0f01e00401c01008a1500711001a4990340d503100c0030070250024a110300b070010000403a580504580e11865038042c0b00c03030414091104c0307290002025140f8151030464050000000704a00c2d9200d2044602542502400000484005c0c2c402c403038180c104e0318400015101c0e500002c611030b520307070288000b610385980200395554035043e41c540200c203d03040c03000d400043d00e07006e42e000300e6014030107010100c5c080d4008290505010003003c04c420b2004000e882014074044104080710b00341c0c10440c0804645291240c0130740c550400141c2c001519501c029800204900c1800d112061203014290686141d40c01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 710064586 1250 710063336 710063369
    0x321031104051f11060c130e010b0a051e0d0c0e010e01020d1803021305040210080f040204051f03200d02031c050f07030201050a0e0a020a0b0f0c16 65
    0x1a109402580142640301202c40f214100c8001400d076440c0a0070600d01d880ba65010000140c03070300307200c0b06031401c03142e101c4c00041310440c4946200000c0003d210b80c01e00d0403580e44c07422a42540f240910a00364040160000c2c903201340021a41c201c00c1408048c0e00c4440c0e483c0190300e1040014030791410003a02091042c03220466660180c10701504480043e0007514141d580707540121341d504082020100c82001001021000d40c40e104145698550161800039281c246401000000000244808108801e110400c101101205081b41c1c0160741918089140d480d00c4050100482c40340441000b44911240c00005116501c40e625411006d070309a4003200c041c215040c4403002c80156400307034150344881c034070404240384404400345401d5070345000707404d10348840700400c42ea43c4848010340c0142e444006201185455201e851003181d00f08005003607030601c41d0b0104001419901c2000e100e14000f2803a80c480d40301401c101e07030a1095010603100f203c40c210104900b039002a00800d004150507120 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 710065836 1250 710064586 710064611
    0x1809020906011d01260405030d15060c1506080d030b090114062a0d05210610030504030e0a03032708190206040e01090f0e030f041e032103 61
    0x100480c0d40f0001d104407480c00031041006540301c22081c404030f900154460126800359030440015070050344100040e540c8e0b4444500003000f0f4070a40c0d0b4121800140d490810801760343c2054444182507448403c1a4403074040c070040780014003c5034003001540c01820410241c2a61640c040c1044c1481210101f22a0b40c0311040d03082c00d00040d00c52030360000c1c400c00c60898202841e01030294044004140e12400b070005542060402403a0002079010940c02310302c000c4226104075111094803e03264402440f440e003240000d004400e91089282807550355004101898490303d12410950b02c040c00603202155039160040c51016052000e0709034041c15030810b5a980880308081e070071660500000c2c080f460320220305101203044040100d9019604000c00114401003c42c0306008140e81c0000007041c40311404024162000504401d0540e001004020490040d4500351410f5507400a42c00010341007021581c9012046600098540780b400000564182107903020144103440b103030b5050091f94490070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 710067086 1250 710065836 710065847
    0x80714030306010c03110c0303040f0303030f0203070507030e01120612021302031317040e0103060c080901090203030a0507060f0923012009030a20011106011a07020a180902090601 79
    0x102c1c0c241c0000c1c030110f40c24011030701c40c0c400303c2c182103000810f44050b10403060009181d035100b41c0c058120043e140307004005242e0148684814248452015844c600e080071000f055032090304d400500780140c1108035034090348034141e89252002840010400e00791252403010300e010a601c8100e100380c0c17440301d041c400203505000f628040e40004816070f1140347e90341d44103840d98030001141a840e80062100281c0c0010800d04180298083d000c006503003d0900e10003012200d0082c003d03041a03060004090050300d001044501000241c80d2003034441126150400140c00000016082c1c90705101c04041802442c0d0a2000c1e4004280c040b0442000000d035006d090fa0824500340300021f480201940446d019400104075003480101a40c01089a50b0349401cbd000078104010741c07400800390486092541c0203802d00b0105100c13100103041c250b14081601c6440035100045040201d0046403030740440d00c0e4080c08034068440602c0380302140c20191000d80040c525414280c0c0325600c5800803425030b50084 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 710068336 1250 710067086 710067091
    0xd09120f050c0a0f210804212a0e1006030506010201090212010510171b0d0501020a020c010906051201090f15030b0604110703200309190305060106023d05040807140303 74
    0x3040700340c07d0516040072000c20a43e2031201c40791222070f4200030b0000500c1c0504d03200c080d0500c000c105d1000741004010385208402a005424100e196000b03011540d0b0030303001d902d13040f1462441c02103140c1e610701d00102d02401c0300b428004c0d0460540750500b004540103400291088112640e03901c0050b64403081190400d05101d28034006402403111003950100049100003a150043d14801c0505416980c05003260b000ca400c950050304a4042c40d0b94543c1e000c101130000344000c0ca80f490601c1d102d030110604480301841140001584e804045d21001c84070f0b00078160b01c49011280d168065034034145564048002c03140325100301d2901140e1002ca03555001030b22072a540565420400c1151201c141c4034045620028210f948020303c191152962103149204001d101d981c14a40200c1c0b03980307045880c00006820400c1507402080d8841d20b00895200c568000116043ca96091401003d0180440f0b020a114101444d0b0a01d0108414040c1a500414105206810b1645100461005103441e400103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 710069586 1250 710068336 710068343
    0x5150312311e1703040909020a03020306070f083d0308040803070302060a02120c031b030a1b080610030e01060e010303110d09120f050c0a0f21 63
    0x70300000c1c1910800c20a07141440c441d02100c00c40450000300c00e03085a0000340e00522448524281428a10050b6445400285020050300d03e040c25000e202c1d075100e010705d00410303c1c4940d84804440c00c0d550380c5100301300103540282c1030380c03040d08018000030301d8646030060300404a444580070488648480943d59201c1c000342106c5c620348407000b0381110342000621030f0062203030310780031010000c5400d60000f030008007014401540c1d9008145000703402c4c01d00040c02074080e24070511000d00003401e60069140c0c8040e84004090b520f540d16842110410f404100000da00000401007200800040d4404074820030201c0340c0c07180c9030804403011103604e801120080c0d001074210008900c240c1c0a40c000820104142c000440c0d00d0342c99080300700100100b603000790b0029088808a000c03041b41448402c0c00b4055601d8a5880c660400e840203034840c2020000400c0c040d49030256409012061007842c40d2035400801054400b0354611800c824801c450182c4140d20b0001d030064007268007880700a080c0c041e031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 710070836 1250 710069586 710069623
    0xf0206090f030a031a19061d1f020a05010203041b09020a0909020c010f0912090503150606250c0e09030903060406020f092706010f0203030a0c03150801051503 70
    0x1a003070080b00501103032444a170600c2c00c81c11401c01c060f56008210803e0b440340a0024001c44c0c580000102804064803405d107181c0c585001540041e21000d20f8256884044843d110210030604c00c22890401e40070b40c06813144d40f000c014401040710540c02a64440c6c900e5108800c0d0a0710740200b030040b84152440c003004608507110401c0b41d41c1894000c3c0900034031000c000201d81140129138401c2d40c182c140304803035060340ba180e41c92007244c01683c00d2016001c2540140301c1041062805609c0322000780200b4881c030000720340d43d280d01805c041000310002c02c14200180101644c500400301200718020b021108003403000080d40001d000040e80c5855500034014000b680b525154000254054507425900c00403c2103010601c0d2161075003840700301403022f064030756414100590f0745c5101d0081d00650400c0702c9505541c666540c00020b40b43c000ca09581c00298081e2000030580003008904c0c0600c000f41050700c4000381580040d030101f48284801d9020455042c40c0104044d101e07240410076001001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 710071942 1106 710070836 710070847
    0x30706050a150e0403030b06070c1206050c03090a020d1412040801180f03030b030f12070c080105010b040e040c05030a0c0503010f11180a12030f0206090f03 69
    0x10300703042d03000201c90030259804426040900080c04140d11490012010366828084856141e4041c158400307041c0d80d00c02070402410109025500e8034601400900070011440172244280c800314081c3c45110029030804c4101007180d03800f661400c041040c441081c1c5020807204420000401a017611940b41c0030340d590035070702613042c001a0303407854aa106000880d5420684d100701d6242c00d01207010340404001c02d2800b0940c8584d99000d00c60046140c0c0701c041c03407500420289002d068056070068464080e603090340d80a200b240070000c0c1c100410000510300210f110742141c40b03208424091035a41002070f150151a0100362903014109070308000701c3c80d09220b40081030b41e1001040c850201c10b2803415845018505d84644501c2050b41504c85d2659001541c034042c2c020189101c1505c40f107410000d1002c0c04000c1294050701c01ca1022800c0403100148910030aa1100300551604 = true := by decide +kernel

theorem cover : BRFrame.Cov 709892086 710071942 := by
  have h0 := BRFrame.cov_init 709892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 709892086 ≤ n) (h2 : n < 710071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
