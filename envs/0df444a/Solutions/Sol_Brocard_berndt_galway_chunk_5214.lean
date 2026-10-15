-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5214
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:07:06.768623+00:00
-- url     : https://prove2.me/submissions/1683b57d-cad3-4e76-80f9-2e5c045879b7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 937589928 ≤ n < 937769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 937591178 1250 937589928 937589951
    0x30313240501260a0b0a0b090c040302100305070519090b04141f0503070c1106032701060b0906030a1103040b04062304110d02030102030718150c02010c0c050301090803060103 77
    0x740071042000501d180c0180e00c407800055025054690046c2c0e40c00303400300e0520102d00c001007101c01d080d9401d001040300004c0070801c5040140c103185080025040c01c10507450f05110251441c0300e103c001c600500706500a07034083c9070240000b0710280c041d8403912502c680e25410321984410000100030f101d40851103100600d10901d800042c10140c01d641d0b401c1c00c5484014054445211101d400c0310200a140c000e91115222007000d188a40400003c0c812408420281d0303192408080946940c0343c1d06045061005805440c04c8901440d02550001d550303544514079000240145a10052141c4c1c1c000240420f12940310320305806a0302603c4204080006c16040194021501c03103110f0000710204005004030700c070305440350080315002d440c14100c0c5090340d000900320b030301c11600c030703004500004409007000000100d00c0e0042d0007080015510b200070300a01810400341c15030002e040240c01082c0300c08000400707510400425025000b030240c3e200605e0807604a403c2101c010b400246000541e034175 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 937592428 1250 937591178 937591229
    0xc0307090911090112150b0d0b03060a02070201030b0d2a150203070507060509150a020a060e03041d0615030c0408100c030b04090b04020f1203030f100e0108030313240501 75
    0x10b004905035001c40481d1410034020003d800c4500068200c50f6a270030740030000e840501285201c0c9074407190050fa1801d1610000d000c66a544000501400130100240000380450400d2503d0102100d1118940304808014021406c800c3c1c211b4402051072400c09a07282d600000078040052244065560701503d8030000c0f40e00c0d01801551540c017500c2100e4402010b500a0001e000380c044a2055403c4101941c6520301641c01d000316400302544005420440c4046011101791071165840070301246051220008200070500c071200d480794000003003c95a405000c1003103d000b0b10040042d500015510100388000344822100320011905040450170300f85004d1080c0088150310100040c51502c0b940c09228168009103400f82e0041002c1c0304525900c5400c1018520030150b80200140c0e42c60604600410781c085031b032000d0000c0e604c2000500101e40d02001303a9900801c481d400042498041c01c1204103620300091046202201102c60114041c041d000305040e50320082c100c52016003e1450b900 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 937593678 1250 937592428 937592441
    0x30a080406032409091509030c140a0b04021c020a030302150a0b100309050c061b100216062a030c1e090311041b0215070f080c0307090911090112 64
    0x1034a0f8441600500040700c05902507041c050182e280c1c514144494400c1c60104d0710a0003080e004a040c0c7c8100c201004000450508201c000e44050f06110989035207134101c0100142000384229580d620580310140d200324261000b0741c009088e9001e441d52428080e45913000400c030811949651000680c0b019068060b5400b5800c1c003800e400c105c02c0328118120020551000101d07064013a030300b4400f08035914903001d0000c040c08031754800308841c419030f0800e150a806c401012001c03401030044610f24002001c005107850b412282c0450318550000d00221410340c40f00504900c00c403049540040d41d90325500c4100515500d88400d8403084c90ba06042040c00c000c0e03000e400c0000c0c0900002e10024014041001400c04060030104202540f11000c0d0902c401000280300141d00c801c910f03103004171207051811b412480a0801340003055560300000c0c4110300c01003c903c0b03101000408221000d00c564001001400044d8081240740e609114140c0268415254140082c9521506185485180c130586 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 937594928 1250 937593678 937593731
    0xb01090b0108040b070207270501050901030b0423030a120b030f030a033206010219080403030c020609031e2b0c17040902030103061a0a060815030a08040603 69
    0x104140d42da40d5034032a001d100041c011710850280c0180060034485e00d11145080c121135401d007042422000b51000100d4030f050384818402c523142c90040010030504240c954220707421221603451420002201206098044804a034512001a04a01265000c003641440410085007400402044010184d0301c0030b002009024907041000004032030f0380645d106441c1c0704400701c4619180114050754038a1110796000700702500c50300c0000c100c04c41d0703414062000031038020740307113821004455100c4074502d02030b5000040070300039143c003a4810341d0303904c00a80d075680d20010111340d040c1401001d1032654280c04400390069201e11310200d01040740d040e154207010701001d020001070842c1000221028404140107031190b00d00408040b00c80c4107404000d001508965002694951561420504a03142c8403c106981d07125007242c0b0045507903c680401c115410307898682001c1e10b4101c038000000100b5030341d80c0d5040c80b030420130b6810040c20f030024200703c0780507440401c5110450655900190b000d0500b4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 937596178 1250 937594928 937594937
    0x1b05060715020903070f0803030a0507090b04120201120f091707030c060b060f04060e01021e192102060a050901050402011b06091403071407052103070503040b070b01090b01 76
    0x503141502095805008030860013001c4031035250b96070b0140302500145802c40185500300000304281c0d1641e13401901c0d0006824509001440c2c50090381d00b1881c0988d000b03501c5100801c500050135684924080c950b440102d18041100e10000304494001b8940e415003110300c06c101044111a40d50480e058413407413900354440f104404642c1e070f42d5a00400100c1d580c130b5407001040c400b0351b94807000840940054141600c9040010b01b01000280c5404940304502414180d0309000d19620300300440d00003810190440c4c070742103010040c90200c5950b0503403070300150302608094950041690010300140105080302d000c2089803120b9900c42c0c02d8642c00c5a000c2d0201e2114019000c43c0c0c00c1c0c100030380f80c529003e55800031b40700e0b03015035076560b442c03401251080e581d40c030100303184040c4000d84000c28800400030006087c29890440881c00482214641c0c103e40b91480b107500c81103400610499414035400815a95155103480d00d10513180c0180307109031381c40c00003070001268018a903c1012601c2405844 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 937597428 1250 937596178 937596203
    0x1902030a17090a0807030801080610030c03060e0f0d030b01320c2b200c010302090609040905061b0906030f07030905010903260606040303030e0f0a1b050607 69
    0x15440c0707030030014181414a02c51500c056000c12484e1000c0c000032403081e51818101d51406d520103107482000b500c00e02168455200400c00034450505540403070341e00c45000706120352911041c601744002a0744038081c50080c0102c00100d141d05a00c40c480c0a40c003620b60100031600c0c040045000e14032121001000c1c4208041c2802c000114000303444103111544c111840420141c4141d400024603080f130306010091078840243c010b41105098000700c040c0d46d580f00018000054040d503c8140e0a1034506140e0b00041d010710316150b00d0f04464218901a0051048020710324280c5c1d81c0300d404076550030708081840c54010051030302b2000c43d400484028040380c11922400e4800050440246c4010145965042ca140000320280501c6050034003d4603084014a120828003168008615021040d000c2035000c20181c0d95680082d641566010318001440c80c0c1c007028514a86940700c00490703168402e0104e07441c02c00c807221100030304851071005001c1c1220b542300e041c0441d9000c2c40c9070003042c0405d040f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 937598678 1250 937597428 937597457
    0x30c02091618150c0f1505010f120210031107050f100c110c0103020a030617100e0304120f0f05190213020c101a040212060405010e1b030705041a1902030a 68
    0x10383c4070143d602038905030a0101c40c50361ba0b0300041c0303a1882ca81c5281901c58004002c0442064101e41c01800100f9a100094101c3c0d40000c0001039202000310074580d407004c04940143d000b009840c030b9079600204460000031401002e070394440003a8003d040079410046403015051080540b172030070284010003050110320000055019401c010300d04420555660703030010741411424000148100a100680085103d080f4075405480c0c040c200240c3d554010041000f0b840d0040b0680c0598a0b0001001003099a4500d4003101070019010064610711a840203030040c0101e0000386500075100320382c03200740c680310303029400241c0c052283c0c03902442d040b001d000d00300304216401054605180d1410720540c100110002422a041005001080e0210400b00481420a44505409044c40e00e0780b40c4101d1a00c86002c0e00c281c400000164650480400405ca06601440985018248209141214510018840a6030340181c0d800800c131500a80c0a03902050020040360704448580d079540d068080c0c0c04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 937599928 1250 937598678 937598687
    0xc051e0c0610061e0201110708181219110d050d02210901120902040c030209120c09040f0c05031b10031a040903020307080f03060a1401020309010804030c0209161815 73
    0x1c18002c029952503401141f8100c115400030074040744129003180e141e040100e250144260718078280c5004203420a44180721150021300041c00307000124240300500c640745071165505060b24852600700824000f06010440041400f200b0005168221180309003441c0c249030300008003217018400c01004004179116548180c1102030404070701200440c4400030ba034045012514409010400030340c0c0030079010b406203880601140f00f010250010b05107110400c0000350307500000740009201403030298101c4108928541703400b00501c8010b0545103250060412407031a18500030400d8070030101100c600f0240340c024810481038000b0600030440d12250041070000a2a801009a0645c4014400140002d1001c001003003000310141443d0f489007041010320010a0494010000028002c0351511559a001040c2c1e010501d003441d02100685550074140e50040c2002d0000e23400c502d0300400c00480e20f204000c82c04543c941640c80c401d80d0185681c00307045440440c01000440030020203210a8640704 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 937601178 1250 937599928 937599977
    0x203091c050f2b11100207020112090302030322330626030a050304060207230c1905010804171b0c03070b0703120c051e0c061006 57
    0x141003100c8100707188030b00c00c51600d071285200428299070703c142101800b00850b0703440b00009640c203001c11304034036151025480d01659000d45125580c00301c4e105040da8442c1c14107100074821801c0411002069050003034a03940104c3c0c2c1e0015403240080380f45181d000040d001170695803c40c219503090010f0150012011003108440c81500481c50203580c420700c0315100b1003005080c42a1402d80f00003030b0000041004410480500580d0014440001e00a40090480350300592003c40140d544c0200c0c50007903420031000348030761145614503c1000b541e4400190803030380000c2c01c44109100800820031290180002d004450000e0300c11008140010162607421201460720140c00d41810148948450700c84440b002c45074032603001c01038503440740c00c2c1801041c1c05000d000704140d00d4504107881c09003000d0300b2a0180846280d980d50310302c44080c8520305440000140c646203030804c0c50004040c5000350400070912885020303203070201e2151a50b00c100c03141200c0c0c9640700c0000240101076951200e03801d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 937602428 1250 937601178 937601183
    0x180605011d1212130e09150a021303080307050a031406010c06180203190c060305010b0406050901030f0519050c03011a160c0f030308070815040b01140f0306010f0203091c 75
    0x3003400384000c0b28050030250840c1e08404141c0c0008503e800020300c0a12170103002c10f8072035080404003a410301d100701c809643c03100ca00322015039078104000e0401915400d40d03101402c150400300501660b40c0d0301c01c00030485110f00d07503003d01c410411902962003001060750040d01103040c2c004a41d00007003031a006424660b500b040c1d11300c82514203401181c01c001600480c3c0c850207039001000720400441302c204c0c0c3e019001070300c1c0400896060075000c0d00d1070700c500e0054000340040884e0360030302607110360000b107688000d0b00001e00c200d0900126160001c032501e00e071090400e0070140012503090341003054070304942001c160421101041801c039411640180251500b40c00d01a2102011540e82084180280351b06040c001c2d1862850400420f62800500708004001c0c0c040180300303240030000e00307503514a14102d400140119082d030044c0c1d10f0030070100d480600d41c1e4011688040030084c0701c000e50301c0381d003081e2512010507490140490300c3e44501d44040c1d9010b14001c0958103101b00249000c0e13551403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 937603678 1250 937602428 937602433
    0xb07020f0d2a120c120306120b1f0e0a18050309010c080417031201090912120e1f0506150d0f0603060203040615050303070302061618180605011d12 65
    0x500030b0700c42c40d881c03603084010540411540c003013003410840d01000c007403030807165440d0800006060111544d100703030b004000500300b0241a400304910b465030801d61040b01c222009540d2915503140c0000400f84001c9400d01001c5d0710b8002909604e008200184180645c8400036620380140d540c015241924240025250b1030024400403820f08211010200310754000001191640d42d040380801c007903c0141c2062401d142082c3d0701000182d00310b0515a00118542401d038080c4090055050003000c00304100c4000e4481e07008001c0800090b41120000c41b6140311092019a4490050141076003260b02910314140040102403801003a40e4024000c0c103540e442c2c0030810b9a626103410003640c0040e00c00340d0b00740361fa1b084003d0b4500d07200702030600108411707406181815525140a0345841c401821807060003540300d01ca00145100b0201000b15052801781e00f44c00649a2032244410716211841c15007280c68020f0202c0c1c00e602800c015140040d0000070a05070310082d4040c420400d4591a0000103032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 937604928 1250 937603678 937603757
    0x2505191a150a06030504060b0a060c1101020102090d0807330903050d05040b06030f01050c0d200f0c07090207120507030c150b0906041b08041a040b07020f0d 69
    0x2d6503558400c0380180603a0b90049018140390412204446000c0300b01d0748610901442005030315000f491411300300350019000c0544500600060740a80300300000c80380d0100600d41418100a0580003900c0e019014101120302181c0c0441e4101c0e10703519030500010141c1010074520190315580e00301d800403c0c424a05036044c00c040d152504c05450041c0c90884001c40c8210030841c017420100000780d032a400540090145040c00090818103104450040f012951185000c288418000b5106101c800054203401c0e03882070600c10302a95500500c000c850340c2e0007050400501c804050094806090f000280017200c0d40b0200400d0300d095001c0d41040f0248603500300c285001c10202010308101e000c001c2c102017205204101000b00d4508020b042900c80c619182506009400094007540e2103900c500f0b0030440d40d02c840c01d00035480480079461411444c0a00100401c0141038142d02d8043c15094080301c0c0c0c01c054195600d902d42011a580c440000d1803030003d000345982038120340f60303000314406505482d03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 937606178 1250 937604928 937604971
    0x50d0f080f07030201290609151602180105010516050f011e18080301150504090203153c04020915090102070e130b04082505191a 57
    0x9604400d0041d1a2848085100c405154081c080d01905a502190814101010b00110300803250494601030042e000440c140c101e40d00c4944111916900d4848050f441d640c0590701034034940e901250880c040d113080c1b0400500c00c07144901c818140d503416103e035400c00d07681200d14102280307418000e13900d51184070000354002c6000c6c4103000c60110018035040210500802078803d9031044c6600602d442d03401480390b03001c141ca23a070603641035131440760020042450041c002c5441d8000e070381200701004d100005101c482e0700f48071902524490103841c500c0d805520105070943c18401c81d07001510002c071850300c0c1e1501180c4681500c0c1c01090050006003080c4000010174041221710b00306114000001691428641c0c040010600820070055260f440b460b089080b4107a5403440c8030f009143d1144034010504000f40102524001e14000e1044000400108503407aa10401454140c0c0c180c062050070b02032010650004000c029080100c20f500440c07038a88188040781d00801c003038112580890007030030703 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 937607428 1250 937606178 937606193
    0x603180f0c060f09050a17150c12130b130311070f0e01050a0b07030305040f0f060c08070503070c0b1e010b030a050603070303090302090a0e01020c2107050601050d0f 73
    0x1503014a070085007403801c184010700f112400c40b124005102455008000c20380d540e01c0d100c8240e0b1000d081075200e46607100d8401e89040703981c1c1c07042810035040c5000c02070082c011201800014880305c45075030040d280e0703411544020200520181c001e40540000030a0001d0125200091510a01d0903840c500c0b0b5084401e1b0401d06035401202554800c0d800030095503014102040c003500c0d0440d00d5400701490682c0982c407a12074020000e01303140e200c400003014071200c4090044027903003000c40d040b403a580c240351090041c649483e01d100460360450100d0440391151050341c0c490340300b507104d0301c40c3c10100e40c55050725010300400319030200c041504441c20500b04e0800090003132001c140095128213240c0c81010564000406560084e40200c0c81040401e0b071040d400d208807270301500c1680490b03cad481c0c50301002d00540c8802030142d40c000034900c515524001458441c00003901540d004064044440700801e114400380a012a40003a0043c0020b2801c8940500307082d11580108800002c55581d021 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 937608678 1250 937607428 937607453
    0x2041e090c120b150414012606210307080405030d084014070b070210120b040606020d1202070b010302040b0121050402012d1b06090501062d060318 65
    0x512040c43c8900400d140c1d43c0010040c00072408c40d58105183d00030700008009a554000c2400c3d01c0340301d1030380d141c02d075104001c00c1c0760640d0120304040d650345800604000034581e10503c00c0d18020b20a0094000b02548038500f114014840301c0201912105c0c02c8021340310100b001c003092406607407003807400a0300d1071154500c030807654842d5081c0d54018041241041c00c0c20701d40d83c881c2c58000c07000c015850040c0e132840c92280340444542000400112440580300037807c0500355503130003900d021404590300c0d40005036804644103035070341c0e041c425074681c003140705901406400409c000744040040c030040c035084c0c000084e5420185040541250702843c80c407044d4014103d480d6030301741e46400b44029541d0113203410344901d502d001d0010f000c0ea445d450300c1210f02940007280c000c000c2d1081c00202c4801d0304e0480c0514641d0844014001f00d1005d05255008002c0c604c220422a900030407291b420000c041e10180f0a03403c001045800146032600560240102640b2916507103102c0c08000c0002e4803030072841 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 937609928 1250 937608678 937608689
    0x102040f0801060b0309100513050f100614150c03130b040303031406130902060c030a021e010c23040317070201180f0308090a080102041e090c120b1504 67
    0x10000601e003502160031581250400c0114103030410400840100018468101210000000500303076a120313020004610001b0740100300740922448948519000201281e03110080300080040c0c5a45804101c031507a0207401c0c681c0c010140f412050603008801c0d0103802c0c1c4140391825249002d19212240480500710742002003110004601031003803644c988120303c00602c1d1903040350b02a050120001f948000482c240c204500e4852445d20119142c06058445002002d0b08403a20340384841406521412800b464506c090355280310a5181c560501403a174402c102c907203505d40d240c21800f00c441010780c240285081c1e100b500300400000140500c03504250019050319460b00e61b9058030004125240031401c1007460740d04281c0c04d001031301e1040c0101040307950000303c055883c41c856010503821585076000c0407255102040c005a02514003185e10100c01c0c103c21100d031920f03100e22141044400c0d0034020400641c400d0600c401a40d1030780d103c00703807078a03004000e101c00d410490204ec4a035803150708007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 937611178 1250 937609928 937609949
    0x90509100e0c180604030206030a1509180b090d0f18150e09130b06100c080c070503070b04030c050f040b0a26030f03060d0201170405030a110d0804060c11010204 71
    0x450468610b8000b09041441c0201c1300949044e2650300020f0031400007030302c0010764660392a40d4102100700791070303d4002400e02007820700845800c190341080b0381d50700c07150560b0b2130240303440010100c03003012035511010380d82c50704e03480c20b111107080342211b040c110444081c4040100b40030100da41c160003800140412115550f5000d4140018180100c400c000340c40f80c01814164065000020092aa01d6501c00c20645030100300300d1003120200c540c20000c54001d840a01e0025001034012000300f1120103649098084800c11a40c4401c01807681c4a644405011544001d00030301851404e08030410040c4401130020582a0104001542c60b07940d961000304142c05202860f40102c8102d0028858114400c02850420300c00c041d444490788002402c0d07a229550b41d52822045a000f000300320b591040f0503d07072110510b0a450031640e0396209103103420208440a1a9486407040003950b000c0015865680006a0b00d441d61400b010300b00045425082c03091500008c407009009102034801030415881 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 937612428 1250 937611178 937611187
    0xf0b1003150906060b0a020d1b0b10170a0b0a0b0f04050a1d0a080414061b060619030f0b0402120f0102090f031c0c080702130c0906030c090509100e0c 66
    0x14880f080310300540c01001e41d61001d1083c48201d98002c580b0080380150f80c00d20010f10f002e0a9008440c41c1c12500c03006100b0b040400500c02c484250181e600c003599034601400c0701e4801e00490310341e43c81440200c0101540081400600002990f07005028030705005007d00c1464180900010f069407002c80c0d43d12100fa5446030b0303a0800700d114403240c001c00e21091016103c03460341c0362140d089500c5140103500300700321628012032480e02c59000321001640c2400710f22805290845c410f80d16224182c400a02c58109131808010314071150704d1610490b60711440c14407440442d6070300d4101d0b245005005030390140e0f41c0711061046290900c0708040e2810110001aa10250201005001e822944209020345d02c440c1445407400142010181910f1903814180c9010543e45042091481000c0c3e000750010000c401011401025800104000c43c0d15203941080548074102141110b080032400000030384081800c00c42c40c144060303002c2e00030002d13034948d60740c45480302c0d200000303050300340c1e00716882020015 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 937613678 1250 937612428 937612433
    0x50c031303120e060601030518030d112a070e1005040f2901080903071205030a0e070905190b1e010c02120a14060709060f1115090705030a0f0b10031509 67
    0x8238981c1e01020b11a00c00c40d18214030a40030340d807406030420402d091170ba100050200c0300406802e0301c80700e10b000048404030414080d410b40700c00e41c41d400d90b4016480344101c080fa440390f045aa851140410000100c1b920740340c642040301800e540d48070b00c0300c05541d46080100c0307540907481406c0e001076040c94410501c000480010003c40c070040c9106042d400c01c1c0703d01c000241500801c10b046400a21785281c80e0344400c1c07071801c0107210281d07420000c0d100364100081d07045500c2d084980715403a003c0d141140d500c0c90781c68070002e84403040040380e1311600304801ca6060b09801020310781144410b16121030710012550118880701c10803c001c050561000041c01c5c01c120030800d8490955503c00050261810000030141c25507005000e0f500901c00d640c2c91016005d8440c0c140c030202c4540d501d048a25100c0580130010305d40c04140e80e0740c1050b025840c004640360400140c41c1207104e0744001c0700c42c41e4031980c0d1519411420060a8010944440333500000800d5004640480308403206c03000003002d241a2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 937614928 1250 937613678 937613681
    0x207021f0f0c08090f1909060614120c18060d200414100c1b0312140904022808240d140c060a050c0d0201050c031303120e06060103 58
    0x40241010007228aa98600150b4000f0955903218020741d6803149250003140050303030f445510f1004a44901240703000003a1089250040c108944094450054054010a80f007060744240842144101001c00114980c0c103600c50040c6440541e0300c1450107112502030016181e64854065800030544800a440d05000115441e50400c5110400d5034500b82c1f410505088206024441c140701305c030310700e10018240e4040c2203150911640085441c8500c0d4202c9208600d11513103002c16616a03650407041c4000602a10034003800c0803051700010306220007041040040d41c844c0ea00b50b140403d44503010501f00c46441d03800c0b03015003010744403100c6503d0700452400c01c5034124494200ca01100300301d01e10081d21141e24820350290040300c400002c9110fa000c1c02e02d051004403006400c0785000840d81c0e0265070000c060008122200142c4d0400014070384200d00765071003681d0340e05411000b000452140c500a035024600f41d0300c00e0400e45034140001d00101c04455080c0b1880f50303203802104c01c008456905 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 937616178 1250 937614928 937614947
    0xc04120506060306100f060c05030706062301020706091208040b0403050a110402031006030504050c0a0b040305011103060a12031e0305010510020a05060703090611210906060609090a0207021f 84
    0x10840c52101713145031240f20b54a210580c810482444485072141080c04414021540354982215003070000990350711036008495115507140704c4000c0031546000c0f0540c40894002d084500568400182c82d01f01008150300814440c4200d44100040000280c20740051000e80001c6000700c0143c0203020050400b0b815a41201c040e5500c224410000c210100d0110009641925034510b0f0010b001e58482c500107140c9008c0e030000310342c446ca284500040b0b4214150080003a01c5c4104c00900414003000c10782104c0340410303078145500c0030040c40c00340413000c00741c088240b1003400303131410080981c0518801d4090201000c005000642c4a00044c4428203080a594109180b00d200800190001d0f454040d00c07841d003d0100070805841d200300d1414014690032008903542d10030241541c640d5030540b5140c042c40c01076500100e901010f000070740d00d55004108280300d0071001d04014076000300c01c010451400c40080040d041d0590038003281c0003507140e00300c01d030402000d114042d88071413811101c0580038201 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 937617428 1250 937616178 937616191
    0xa1107030f050f10060f03110409050a0b0910150b0f040e07090f06020a1a1e0112020909060103050303040807080c0604062a140a030b0303030c070303061208120c04120506060306 78
    0x424004106c001005800e41c002c80c2e8110302e102403e5480031700040c024000065024116100c0c0490f600d01340141e50039050300030754444007110085001c9100e100300340c903d0310b48204c105000c0d01a04010a407030752002085003142d64505e8078036040e16450014403100007a00c18500140d6200310030302c051f140800c0514040c068a000400102503580e40710101403600d035940d02e1510540c0d101007084005041d0b614100040006501341d05076850740d40c540c2c40440d02031030a91151041d02e010801c20840420042e045c0c2e90040701944c61692981c840c040558080241100c0c1c203001040000f100b00028060795010301e20651011815030000fa020150b800e194070450b0b0480500c42403005800b9801040c0481c24240d4807410340d842c0e0525000650040550080881d00360000204004062500e8001445003910a403803c004680d210201988000113072100100240010131009800d5107072070075019840018860030038a001d440f49010502d1a071100c0044507a588008144460b03842d0074025543d000c030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 937618678 1250 937617428 937617431
    0x2010c020606091510020709020d24120b061306170d09060c1e020d080c0106080a030e041817070309080d02070b13030602031504200a1107030f050f10 66
    0x1e0134a0b49002c0d02528a0b000b512400c0d4804882c841107000b84003003c0240100c007400c54882a80c001844060f2299051745007140d81d8403d007041e5140c0c0c0c0138a103442560b00302d4001c640340b100166114103000350b01510183d0b015001c140401494410703401a04003800c98901d100d078901505141c014030702a843c1e5031480c14440d41000c140302c05079000190008098201e003c0d0308003c98110540340f8004911200a0f4001c24071094070000c0c8440c410003061100e403100002c00072950f44044091b15035508c3c840c010005204140002c81910f0540c005d002003903411050301003895120b958501401d044240c3c88100740740e01003020030605800c040f01030010b18900c0c0c0501420b680800000f0b450303600b203000d01c40702c10101041d1415841c0d00f1820b0440a103600210031550390800303003121403620300c42c20301803481036040c056900c0390014080d00328445900c0c940c00c11424080245400d40d06111180c00b6081d891242c0e03600040454481008903140340d01540250807840c2d181060036050140c2401441c4480b03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 937619928 1250 937618678 937618681
    0x1815070b15011d01031d010207030909090203070e06030f0d0e0109140d030c170304050c040614010819200a02070e01030507090510080d0807030b010c1509020103090c0602010c02060609 81
    0x5036004100711408540e01c04184501d40d840760010ba006154101c50b030390305c4d0006e00e407060040c010154014440e00f4084d4440c41c01c0546d540114005440c0c2040000703401d9005240208109198282210b03004180103050703921520a42e6102440c24024900302000204104c0f009640c5582020500014142011000781c460036000c020840725103511030014104075400c0b007240144804990843c84105840e034021b50b80b8140b904129a98444e0326020501c514070300000003a808480c2034501c043d4180603107480a580c0e481420715004424020866044540c0703c0300c9102c400380b60b07010100780b50100160915182e0b24041c4000789404c07a1038100385c501400450050001c110005030540c05c5441081010030650340d031143c13034010840107034031640040c8a48500000503542003da5541728401c2ca503070802c000c44010740111765450501b10050800c011000c4512a10303940340c2c1145034101e0060501086140d039550300e1484c0d421544d031107000143d542d100c019032029030500c002c40e001132049803d26810f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 937621178 1250 937619928 937619971
    0xf090308060f0f0910091d1e0c040c032901120209010e06070303050403110d120908070c030b0106030c031a09130506090114060a03030e061815070b 65
    0x3150009800d00b441000c03041c99100b0350340d07250910200b1007840500319010a08101042d41080441d90062500e12810062440100522404a15005101c80c00188148015903440d5080307814030180800c1240520038007075415441d00c2c0141d00c401321140d50002600100c03c03060400c803620140c602c2c0110703480c80e840c0f00c2443c1c0c1c1c0700c0000403003030701840360042c1d5a180040c0161000040d4450b52500300c00081406814184c0651000707100c3ea020b921810303109894a455203459680c1c200310b071804a108028000b40340c2086a2100303e80c1b51081304901d10702035564030746010780440ea03031044400020400060008a41c54000c0c0211603a40381014021100c200e0514490b0b080c4d4982201c1c042c41d08800010702005071240071b0242c580e0004141d0742c15050a00400303000e4682416415041d842640200381c1c0c1e414400724003000c50ba01559804400b240c030781b04215440c1d10403032515031080c00f1035244502c0341d600c0d840c210326a040b070121001e9981555252115008800400d0195140b9605208501 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 937622428 1250 937621178 937621187
    0x15080c120a020f090a180f1515090908091332040602090d170306120606030303010303051c2d09020a06030b0301090516050306061002030d0b010302071a0a0f0903 71
    0x8443d0703003200e02c030036680d841d20b4030f0700020a5011101540c0d141c0800b42613050000d900f5101700241d005107171020307001c1540e050382d00560380c1a0b035000b208603000c8074003002540fa96510a040f070911a440c1d40c1d01e80124840000c9940c6c080141c086d5419565a01802c4a1003411035112000c0c00d01d49480b0040400300d0301400e106c030310028070240810707030001919106c507075400c0b400b0300603242c4c889100c0304051002c2c1c205000c50b80045030514092101d5020700744c894000003900c0d81c898840100103602e1a0b0030350781c080740c440e00152056610400c44442d5081e041100c1e0080c0710001c1210054035030b4182c2a040e429420000120002d007025103040c900c3e4000da02d80350050307020385405007004145561b111001c40d00500204001906038010101400400131036610000c0417150110112000785d2582004c001d100306084900002503030081000d021079400340d400c60303c84d103501410010309141c05034484401e01c080003a0348190003c40a020050484a1441070742c0c20140d0707201c401c000b00c5403613030390150 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 937623678 1250 937622428 937622449
    0x70b0306013924061a0405060304260a0507110d02031c090b1308100b0603070e0102070f080f062206020304110402070c0801050a0513030507050115080c120a02 70
    0x70840769080703600006200c26540b4140c100e02a4404140c00806803c0c0010000c22050060102d5901c20502c0318080014000a403415190020002485c58503140e540c208e2450018245d600c108500e0701c1e40c814082c6149018241141060711000e5898209107001d400c804800760215102d446079001c102e003d620b0002d840240d02e8944010070480c090590000e44855001e0b6000d036510300310010b00f851500da103241c0036004444100d0101d075408098110f00743c0c00c0c2d03103003d000350707400c4a4142300240c5140d103d400e40116000043c01541c460319154804060b0441e0140c02c1040998801c0c0c98181b4801030402129502c00310710341880c08002c50701604c944141c2a0008003034038440e00070010078280500c0c1c0580b0b1041c10b038000e004541d55013040c6040c080e140846c0c41009404c1d440d00001801049441c01018031911441101c50300162090b0f0f000d480903080207406035455075940c0c1c4800044110400d100001d012544010084400040d0030012100c100c030301c2042c16900007251500c0140c40e10421302 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 937624928 1250 937623678 937623767
    0x1b1b03050a050703090e0a020408060115081314030d0b03060723090a0801231803300406061e08030904110705060f070306050603070c030f0908070b030601 68
    0x743e41c0c0c03000d0382000c030780a071a1038011801124980e4280588091280d00400c101c60200e019255180e9036000d03a452400c0c895250307030022485903030000303016400024400a071207109030031103506004071542d030620f960006030b03070218440c0c2e580c50318907080e280130092154004d42d1172030b2500c500b040c401080c003010904841c204404003800b01e0900035aa07203404020000d800e8401c02007020107000c90201c020401035850b03480003d180c2d8004641440030300c81103000c0c00803003540210324005041d031501d0a00d0088030548005501e100d404511507030302c2285000e0050b03002e410003154072400c1201524070105001072842c584048030800700240007001c019649002c90464000842e03924041c010340c001d1146004c02081405810100304198000c2c1059602803865a9810005607813a881030080502c400e07900d0f8008543c9030000400081e12840e081c45c05160540740482956a6448841740342034001e0f00540d40e50000072040052551b03000d08540c40c0079070081c041c1c1d0305003001490b114106840b0503498 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 937626178 1250 937624928 937624937
    0x2090102070e04050303040b180c01050d0f050412020f011418071806060207050114093616080708182a10021605040e0109061b1b03050a 60
    0x11044140e00a020480040116500b903890510b020301c0d040c0d803294011201152000540004942d10803070850003505290381900003841e05495020040d2a2030300503952000740c0c039840c0c21004440d050035000e400d005900c2032401c00d2498140c0301c006030070301d5005081c0703c0c020f070716240c01843d014003800c91180d0001c0402458000000f11184a1402c0004a4100e150300880354a088002c99500750701c030340219041542503c4150317444400466944001180145030036805000e40011440c010f609030490441c88840a04001100d19291200800d02545a4210319004040005041c456441c5241c0a1880c1c0740282540c502200302800d00c44025000310f20009040c0c000080221080022000c0d14401000c6298503c0d5074082a4600743e0165400300d010301c02d07820f505c014260001484149411400482603011030a00c81440300604940d0303906c21182d901e401c000408a1141c1c0315124081c00701c1c03d241007111a120b20094490b003501c020410940403170612000100754805c05403034154001740f82 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 937627428 1250 937626178 937626187
    0x14070b040611160b070504032a170109110f10120e011406010e180a0e03070b0717010e0f010b07030c05150a0c030b03070311010c08030406050123011202 67
    0x1c0440042c848090390101c040000a07150240c000038901465003c3e03c0303204080840d075141401116240120300c4028445544442c4850000b24800604043c10300150307002183c05a4800001540c01001048a0480d95541c410501401020741e0071a103544000d44400d101201d815000c598003200120003e81040001190704807214401e400400d038035541c003070091143c0c000820920341c001d1001e54406000c2011300c0d0f80b091242c2028400c2e00300d40840318460100994821100700046c0c60038036046402404104100300008a00c01201c0e4040c2e5201c1c1d0f41c440350401d24190040d410407068003d610703003080610800c00b030501030110300d03410340b1028499562a80ca0500d000da8100c0d03091b000c020181c1c00707000c4616a002c3e0285012600c100582c0c0c1061102e00180c80c1c0c06e9044402010302960941c008810900c0820583d074034070081031006150010b00600c1c1c130703140d031070554005440403100ba9480b01c004200001c07080f0701da1076004030805149010780134201d0020f003031420020301c008030098004c039 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 937628678 1250 937627428 937627433
    0x703020a23070825110109060c0f0b060d0501020708040509100b090d080d02071121070509310203010b040b010c02090c1606020702030f060105060a031a1002030c06010614070b04 78
    0x4c031203150700400048142880e884e1502e180389142480b40f081c009020000c0000e00540301e00b2401c07204a0308101c200341c0ca00e201d512015840c9800420050708115007101d604001082480145100c5c1d000303000c0c082c1c13160304103010026001400303840701c403402000709014441c0060000031214142c00c121490300e0110928541b8402034010402c080450510208948041c0300310441d19a5000d2422280724040030202c10922001e0704030410758501a80c031016050016081c004910380e040221840240750700c001351740c00390500f0040080c0342881581c5401040003182001d000740006048100c0c0c05024008903540000c14081c000507011f4070070240300d40850130b000b14400c00c0b03070050101050040c0051516081071000384d80a80c80c124045d11a420544016101c0070a000f416110000c16281c5041e03018030045024110038000c41000c510603104000d00c0340d0340e0701760300c03205002c0c580c02558a0f410748222031410940141d200806000b41000b25156a41298040b01d101550100d00041140c80d0360 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 937629928 1250 937628678 937628707
    0x6070203031206040f140a0f050c273607080f0601110f03040611030301031a10120b0603010c080702070b070804050411030402030609010e12071a0703020a230708 71
    0x105641c101e0145882d1004a181190203030b44d9111f4802c1810911200700840c641e01c040301c0040b2004085000103104a0300519100e01d8003080000410480f0302c8005944000110602ca04bd48030040d101c0e032885420f10451610380900c1010b1450140b6440c65280250018104040003440c4940e1075202d00002581c80c0e0103050b0502c40302c0300690413510220032402c101a0399620502441c0085614216454090303000001102e059a80c81260500c001840c00c4c1e070754035071340c401401005003941d41e00d00200f03080704607010500140f4000c000c440750030305002c0103050841c2d0700742c3c0e914130400c602c4104001c011600043c0c0c0404036188001c85940da0007450600d0340341d82c0140e801499000e8141491031803980742100c095400345000b281910f4440d1a40300704a422101e8103020906560405907549250144030009400e9690140c171141e0300b060001d2282c0442d1100403144e10020a50200700c10034100d5200c005e090300c817030100f50345102200550400c0100c034014018001d184582c002100c21111500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 937631178 1250 937629928 937629941
    0x3105070f032a0509010e04110d02031902031003020f0d020d08130b03090303150a030f03080c0403020301140f071d3d120c1b0201020102040518010806060607020303120604 75
    0x200003003100d02e6007030240000c0143e48030184079070008505640c07401c420b1400d40720b0142c002010725012032601c3c4410401d240603400080200d05052013038041d41a0303080d1180015403117000100744003480e1500f0340c410000e00080c8200e190307000d040c1c0760b4580d900584039a1505e60b0301c1d6800252464550700c03c00e80c2620700c00c60907040200c001c58080b050204401f4000040e5014030400e032020b0741c480712180280700845c03125104c05000426081d00c00800b19008182d19500004502d42007032900d0b84980119080d204a40341040000040004100e0011204161981c000c0901c0c64600720b401f0301c104001581961607105980b05d045407880d400007602400e80180316800c07080c0c0d104071300c11800070010f401344c4c2d403130407134100201e6400000b60190042d81e200340c65170b949103511781355926641c480104102c20044042241550360030400419560345540010381c16400c901100301c41d03503040c5080c03103040403000b0b0641070140d0740c00e00001c8010390f4040305031299003e80d0808a966661307401e00103805480ca = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 937632428 1250 937631178 937631231
    0xa1a09041b0306050412030c090e060d08040305061005150913060510121b093c050312071e06090c030f030f2a113105070f03 55
    0xd80d0710002040080640095208034000d00300204521074404e8140c06030b980000010001490540c01401501800100c3c1ca800400c050140c041505065445040a40c026001641e80d070b40110100954258107500030009010155200f4903000a2018042d126004003c011449640c01400544407540759500c488000e2070000c0c603070b06644400f40000b0f821249131980d00600282081c185c040954899040d424644100340e42e682e003241e02d840b250b1164030300c0e0040b180c0441e2076410f04038104401e440700e480400d203d0241140180d1841c0ca41010300d005080c894400da050400c0c020b0801103106200c4409081485074440ba40320031140c501440101825000141540105a4040180a09c2198008180703102c2e44480c284008250300c150b50782541c0701e04520301d490700784148032000513445002d04e90a6101e0031310300b01f16018010000d0b0b5003c045c212000040002c00141c00440c900001c001c00395003c3d51407041145003488000200701c5100740c000343e41496110f018030a2402c120761921a5007a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 937633678 1250 937632428 937632473
    0xb031002070623062803020d0203010e0d09090c0c050c120f070b19020a0c0b0c01020c0601090e01050f0c041e030206070308010603110a091401110a0302060603060a1a0904 75
    0x6481c0034141080c900f00380d902c2400790148002030185100c01c450944489007000b4040b0001c82e14580c00c200c030042c0115000c03a05035480e5a20714208000c100200120750199441d40165982414509400c80e0405580c1800b00000a140d84012610110b94000c0d1403c0503034100640c1000e441640d4a080012800402c9034400c5450001d00650040040d001d54688202c2604540e489040200d80c0c1c4d030080d9002601c44c441083c000c01010801000034400f030712a050025007000111040c290403d50243d1080030311540f5803410030f641c07520a1281c1548100c89003000421410b002200b54141c1c081c40c05503890160322000c03504070400510200c08000c43d401013100b0f544040380e01c0c009000307040a100e03560201c0d0525101025500300f081c25104003240e0782d6070f6032025600c0c1850245212480004503410b10101c144450f50b00c070310911030740701400c7c041e40081005041440c180361030700d50001c06030400309143c20422508054800700c004d0148100f1558000140c072a410492184454641c034058000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 937634928 1250 937633678 937633721
    0x1a03030708044b14060d05100f0b0d0507020d0f0f0c060203010330020c3f0d0302090f0f1809010e1212060d0302030c01020403060b10030b0310020706 66
    0x148007082c0c50351080b0707401208074499195241c0b0705070134142c3c0090040e076010b0820720041001140603840750390301c20503808490a14940e204000c0e00c130744119803c0014890000a40b5061400083c000d00350020014070050420111962008001034a80760700407013041002485030700c14502c140d01070100990011011035680d40d492401a08500310903043d10713150030900e214010000c24000210340d80b802035030003414410110408200010700e60b9418412402207201220116204952900e017443e02810315551030100180501072510b0340240c590000c00d4010010f0030040d032118034442600b2a41541c00010b03039001040010050b00c10320400d1550400c8200820003144015042150080c592009603102000200000384291251035a8022103c4084021a1060410315413461800b03000b441038904044038a1001e9007641c3c000d5005665a54464039002c1440c502521120f00d41c250300d05003013020b801d01001090300e8100045100b076865501190001c20310103107800035002c40e0901603012021 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 937636178 1250 937634928 937635029
    0x2030c12030601030c0e0907050d06090908030906130807031431050a0e06090603120d0209040605012d020309060c10181109070c0b09011a0303070804 66
    0xc5800480d2400e000178180100c80030154050703041c80d2200c1c1d6000d000c0424a540307081042e070b920380c420340035444103581d1000009107941c0184035400d80940300f41042944d0b13003000c2072124030300310707001c1d00641c0c0c02041c4409013400281c0d13000407101d64561504052800c20400c454140c80b80c000c030b04403544400c80391001e040e0b6070903c2100d810180f40018403507014840e00ca000f0b1081000c4103010700d280040003400418102d1401e05407440e03018500038210342c00d200c10760034001c013aa044003002d152007940108660003249000d0007100003410003864119103202410000b9040154100840c0d00c11900301d002007030244d44240202d84400740c0c041e0455030786851501d009941c501d6001505003a04e0701c2d000c2001e450031028001069401d070880e4002c20b41050b01410084da040000c0c15074800d100701000d5400010300c3c0001a03034483e0200c000009070a2500a02d001944d2080a1045100350030030000500003928441c255001d8408940d02003907a1034001301d41d541500c4110714070000002c61003401d52038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 937637428 1250 937636178 937636213
    0x4060c140f0c010801080c1c081303140118050a0b0601020f0a0c0305120a020d03020901020313090b030105062232071d0f040f1b0e01030e280302030c 66
    0x502042c00c0c4e8484034142e998503119600c4207a500c1341c0e15400424a000c03008202a17004200000900a41d0007900c0c08200c01450f41721140558000c94a6940e03203003410f88a05000c0c41901440764600000281901c103550b905625a00b104c2e02c0140080c03859170100f04140d10070080842d03070403600d00481d45c8050040c10000d00710800d41c4402c44a9202c0d0a030303180d28091482058a001c0e01441d00107258a0040030400c3d0040d40040380400d04500c42030008d400d603241c1034403900300180001140002e20042031001d050945400802c03460086050380f045107195500d10505c0030f81411650f40008480074411030350003011025084072003808105a8041580c640014070040c001d190984880d44078018075014941e88050358103c09521950380040c5c81d0460034260002982403480311000070b040d0303d1004660407002c65010001c800252a0010a902540c042c410259410b910500038006500518245191030003103800f1918036111002c14042018001c209440f07607501c900d03060756100c0440140e01d02 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 937638678 1250 937637428 937637443
    0x501080c0711060a020a060612051c050c10021909140418060c0906020d0e13050a200a0f210b010c0605090d09051801091a062d0f04060c140f 62
    0x641702c40c50070800180662950703c03c0c54401da2b118014000c0005081002c0b401c2084103041c10701800ba080103000c842c0a014001c3c1040071008050060b01d80c0e01030902d5010380c142c0051000144221000203004000d855810b090900c3c0040b078022440c1c030f40b00800000c0c3c5040014005109c1d0f030500710788080c0260800c3e080d100faa6403981c00c6441c079641c0b03948100c07000c01c100840103822040c2c1c009124100a11500980d50094007518045a818840d012044070f000402c0c848001d51840410800070301a030100698415100d00c0c902042d43d81407d5202641c188500c8800c0e41280d0342d1070035080314990145203602e6040c0d801a104202914201c3c20960b01d4112007480440010b2840e10085968904804081c02107951444002c00c984c0c00d0140240c01060015400c00340d0311150f560b0501c9968903040106850240f031091100c0c141504c2c00e80e0342442044280c18a1000414444800f286a441c41903a04a81640c07411901340e664a041c040c920141c0202d02c038541d0b01841501302c021010006541 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 937639928 1250 937638678 937638683
    0x2012304062a0302160b04060c0f020c0307090216021306030c06051204061d0d0513080c010206070311040e0a02030411041a0613081606180501080c0711060a020a 71
    0x41c800d05900c41030b011020a9a044105001889044000a81032090307020b0220111000520041e000280d22403e9000d41c04480c21030300749454524030740c40e42d68801d140d495403245500003800341011075400a44c03580254062a0b903200c0d8041040316282080d140c8030130700c054020785628085828040400060010740c0416140d50807080c000095445c41442203808269840410310915180e0f83e41d40b9016020112080c1440503000590b6920540c003403100040d00112070300c605a4818000c00000c000250560002030700e9005034100c0000c2d40d80100340c19902000b00d140001c0d00611280740e000107070089400000343c44103280c00300700a4030086d6000b503004134000d4580ca401e0152403c100000e45045002c00401110701e9a83c26a141c10285d028019826080107540359882e1100d9a840c58a10860070120440c440d113581080046d401c04064140020141040c0c0c0400b414200040d0550078054109000c0040010b5494244402d642c500120910000c025903a038015444009503940345400b8103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 937641178 1250 937639928 937639931
    0x13150f0c120b090f01050d1103120a08010515070b0c19030f0b0d080d0209120303270d020c0d110d06020904060f051c0302190c0611031e0a0201230406 66
    0x241180f4078003c407089104040c0d14007542070581c01d00041c000381841c40b40c4200d84003106c5900b5105680c0d82880728020000740458015112000c1440042c810031061f4409070080340d401c1d04009070f9000c2035046418480c0c0000c0800d50588904908030310610507050200310f014012142100320076815089000350840a49041c000f021801c410495074011807000189100d0040101c80344405403600034000407100101002014000e240d0f01900310391003100c1441c9001c07071809080303502c0d580f60581d03607040f580c0440080c50188552407000e55034140e92042c0c035108039150213601d0100320905980c00380040b80900346c8010100d00340340c01c0380690480321101d80300c0d90800d88003040400261700500122a8002d0400380384044001e0007425014405c2000d508600030013014001e5600701c4100d19100380d101e661b400045501d040c80050414040b8410b91041c0c1c0c0042012003c20900c00e510b5888012003071056941d5a80240010780c0180700440c80c2e140382d8000e80c0500440c144803603984901c80e40c02841e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 937642428 1250 937641178 937641191
    0x70e121015060503090d0809010f1404060c1107050f13020a0807020c0f180417070809041406033d1e020a0c0303230f04060606030513150f0c12 63
    0x400395584d002c100c44581c002d9014400907004184151100da40202100000050344082003542d501a148440e142082c2602144144810011540b1860302680c1c13141c03900c80b402c00110401c0503141d543c40c1c40348600ca11b240d142005d800c0d59400c0301160341034070540300c115920100000040c100740b004841c1c50026000380c0c8200301c41030500c1e0318101840ca00003071840d0f210560110350000b0581c0003510944001902d5680c0040703180d0000010000140034a490755260f0340300d0303001c104c11790ba03601c1e8204022010340e505000729a200040c00c020454000300e401242c03240c0d003600500181780c405200c0600b07201101c80d40c0041182070f602403200e030f46402641c3c4071289044010541a4414a840c1500040c1c01300f0084004c01c1c4130354010000303151014210507c1000c11001d010040d00103989580000e40030340280400c11410b0b1080c040200f10380c0c1814440752038488191029940301110140c844040c0c081a5044003200354040400c50340045010004054080340060509840000c0f00c8406450110b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 937643678 1250 937642428 937642439
    0xe031b0f1501050d1401020c07120c050411040909030c060612140a0b18190b060f030705030c121011030f0a140a0b01020c04050705090f0402040b03070e121015 70
    0x802941a503101a1007558441101da9800c60741034035558030013105550178402303000d440c0c0080c485040100360a03850800740c0706290402e80400b94039948914440d514040c2c00c000028220400e542c225180120f0016052040382015910600c0e03203440142114038000010030600404200200154020b256045110310340c1e4007481e503201a018005003480e1380d24000968943c000d400184090000e060541d2080c074450203280c0e070014904030017203900b641d000007048401c2c10f1000105544440c200c00410805107801c0110f03890317105000764203000e004412264030204004200b0451a042d0a40080101714a07049540129030000c1d2108103017596414041149240c45004816000721061b01800c00c0361a50103130b0b01c00a0100840c2181035009010014501d65914450144a204152122a6200c4001c0c0411110000b050025407041e84140801d01c0300c000c001c03050b45d40c00003d50900b00501e0342014000340100c500408005d845200e0314003201840303607803034101d5001803c0a00f19552082c2c0c950 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 937644928 1250 937643678 937643713
    0x6050c0a0b0a320a150e0907090506040209090a020a14070f060e030c0d0e0d0b0a09031e081308040f03060b0307140105092112070203070e040c090e031b0f 68
    0x1002028031120100c1c0116200341c88980c4103005911085440c80c031101c3c1da6146c40020a4811207800d6202c0c3c01061003080080c0036070003500d501c01ca04071401c602c0e00d04140c0005240440203481c0d8100140e0124541c1c0c485d42c01907030203a102000003a00303561954003130324100c0a0a02c803800201c0740d25040c1085030807207000000580e80000c8240c0d001c0d0500f90b48030701d03045130011542416079500c0240f000c1c03c9000b00b4610480700e80541c18a1601241207070a5080107480342100010001c00e00d071242141c020020740c0448a681c00008902c9413200a070440c0c14451082e0003140c005080b10700c0b00c81000420000d8503070051036403060075429141c036250ba4940140c000442030481c3c0d8007086041017281503d1401d8100c01c031a848039071250190f900d0401e07180510749120004000600d0b180050a44150f160400030080285100710784403806141c680d0350107000a025114000714030303407165040c00202c2800e1080d01c85405040032645415001012655500c0005040441e560b018400f581c0280b520388 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 937646178 1250 937644928 937645001
    0x40216060203071b05012c03160c0806012303010c0e06030a060e0c0a09090626030f13031a060306130c0b191d0a06050c0a0b0a 56
    0x204040860000080c0c035140041d501c014401020007043d80046600c89503508100700045010f400005204220b81c0001d28032022039078042400800185030b400ca0030b5400004441280d140002e03a2607581c00c46240c040c2c80c2e07140b40c3c4c02500180c000c1100200311000d55404007640381441e0030200e40094200d1027410308031603012401c440000e400a4820030581042401580c01c5074142c04000303134007a940c690800254406481c10b41034640b0004081c141d03141d00c641d42101500148508010f032501d0803041d01c14900b4000103020ba10020035810b1551500c0c00e00903128690042d0b030003160340b9040c55a007403950a010303000865141c403160700c060107440e18012035103203d40b10140003000641c0f04d03445600c0c0d840382040d00840d02060110404a1140c82c3c107000350034981402d0f40f480340d403410000e00292072031404034899010000360241c1e0103070b25652109641c0445040b400c1c007507a610031001d01c2038142000448040c0480100009014a2800f90380c440320710034965116842e50315904801c803ca40c0c000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 937647428 1250 937646178 937646197
    0xa091a03060a0b1e010c030804080702131d030301150f140a121118040b030f07080a030f02240a020412030e0108060103020403030c080c03070f06060305060f07120f020c07030c140402 80
    0x111545400001d02030140142c00038025984907050460533400501d21043c2c0c64081c5900c9130701c407464412218002d90101c01c105028001850842d0b0400d40e910006005182c1c580c2c0070081501c2c0b0100c0f0083c015049841b01c4464800c00640c1c41c00d0000000d040002140180440c0074500303c1007441c0c01c01080265030030a541242655824144402000b004d081c051035660351500031800140791180041161600920048002d0f1414500c41c2c10041d00c40440c014859055400c0a2000802480307002c016194800000c00040c0082d210344148200a02a64001e611609401440b074814036411580800340070030300360784904040d138820004405034010b074071000300400c082d110f000000410000103400d07081d602804603400d1070816240c2902d8403403090300c02d44d03c50340e84800070310510001740b110701e62144407002c84d0070303860800d001d00424030000c0f031002d8944156602214843c0721082c0d012500b81550704c0c81290540b640740d0a00d0b03c48400c1034403030881c12001080d035503581400c0600030b8606168 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 937648678 1250 937647428 937647437
    0xc0c0613050309130f051b0307080a090605090313091104050f040f051306060504061a07023c09060f060310120b071d0a091a03060a0b1e01 61
    0x229411008040c414040008603503a000902c4036810580312001c0c07202000c41d610704089490780c8800c0030641200c2c000b800c104840c1002d20030240c030220400c1c00322900b05c000b41c40c7c004030755036980548100038066200010420341c20182440b481e150f000004c1c0242c0300e400078040b030402d95643c940004a40c290b4101401d003640500c41081245000f4986c101e42da007010348041031140c0c1c03041c605411517070201e0b4040280400d582c0c1600071f104451040f03d010780426034007001001d040c0003480c0d082c007030000c03031000e00e92900040310800c54481020616072441044542c5003601c4902917800c201002800481200080c100a640e103e480d00007aa00c0c081d00001e000311407010807100510031560302c01002140f81038003045001568286014101e51600d011f05280702c0e440c2460480140319a40b41c045407038080150017131a580a66072240f41004030380c0c0043d8000381c0e103850710f001d4100140038145001e5041c010301c400c1003080e5105400001c081c0300b04a0f8107040c403188510444c2d4106000010241c0000d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 937649928 1250 937648678 937648681
    0xc0d0f08010506071410150b2704140f06240a05030702120f0a121419061a03060f030a150c03060504091a0601210b12070e0f0c0c06 58
    0x600f002802880240d01809031004c2140461039524980b0b0483d007042140e046d070740d1420002810036000504042e0a00000c41450420710050724110300c81180c2d50382d1b4494605048100060b41e03940c1c0301d100c10911104015031645007aa08640d07105d00c044a03064000d0311800e1070030b100134409548070b484d0304141304d00c0e0b80d0a2451401302143c45d904014050000d62094008502c1c42a1820300680700c040050ba000315600c0448038030043c4410084030440c815281042055240070b070754030350b5a0b42c1c0301d2080d40c500c4400080b24031041c0b0180c40e060f40f001c0803082400e0310342c1e4181460b000045102d41c10980340c1d00310b4500c4500a0650315980c0200c043c6c40d01d9404460380f041d003007058001c1280301c00030b454003065464403240014203c99001400b295980c0400c58200c00c240003070709407294001c00900341403443c150014941d1803440d0411001e80e00f1156151508100c590700c69101c2055400780800301e507841621186640ba0184003a07461031140c011003000a08203c40300d4044500074840c000241056 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 937651178 1250 937649928 937649939
    0x306080d1e090e010308070317130201120230010e04030c030309020d080c01050406050615070308270f06330a03081c0b040219080a0f050c0c0d0f0801 66
    0x40700003075480d110400c42203240004a6448402485001c0c1d4000c43e6030942d926410300e8040c00962500e41110400c614150400c4024050b281e48007411640a0a04000007038010704004d009202d5000310241c10168080d074880c0450600340315401c05000840b12600b0b690b2103540cbd48110b07100440703005000070020038241001920030380082801e103102a19418100405580e0b002c0a81c005a01c0b43d02160b40d1f6204100034001d03a170003103541007441610707861441c08010002d00003d1044aa02600b03002401e40031500f480301d81505546800c0900c180cc1c0e92141c0160b00c8503407aa030102442c3c40c1e0b00c4c80781202150001090300140c191541781c08051540100801c00300c00c01d03120111801f02d030f101c0503041000002c1030b00035000740402d0480416070401c5e0b0441d03000d548201c913001079119029605c140b1044462a10010071310300036141c1402c04e0f4000d56502240280070f04550070f58400d020782001c0520005491010180c404501000b00740c908114030070b101100c0b00c2481c100014005544200104003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 937652428 1250 937651178 937651217
    0x13090b1206130c080303160810080606060a050c01180b070e0f0f01020f0a150c0e090a0b0d05161a0c0d050c15100e060306160806010c02040f0c0306080d 67
    0x582d03071166503141441540c92940340d0968004503032110f4444200c0035989a0301d9840411507034030010304a20341c0001420601b010341e0f07668008088600030310002801c4d051580c011025100d40c0d030b1045000f4020b180040700180480550704104440e41c5d000100400c010074094003101c01408406030000510030010010001c01c1c1c038901108a0543c01825088000b620003840040b2030f80307001e5100070701c0041c000b10f415002c0394180414141001020780d80b036103440e0350f0802080c3d0020122000071506614a00000c4c500c6d2040010003000b512918000d030041c0c5000a0020382243d04856503541110740f124000803051044a4041d0540d4102e030300c00300c2806000c1d01c05032030441c16000440750f020b21050b03071090b140c40058401041c03411282d2000c01207180400e0340a0b0348040b041e405030045003003038516911080208c51b94002480034010010b40240d100320944024035800903c103000351552000b0001c024401c040d41d020009041c090045140c03940010010300d89131031591400803249400943d801e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 937653678 1250 937652428 937652461
    0x1404060503060f0423060316050d020609010201180c030b0f0c07021909090c080d030903020a03080403020c1e0909030a02070b031009140106030e070f1214010213090b1206 75
    0x7540903035510300d510545e41c06100030800e600c01c0013441000f241461000c05190485000340e07220b040400c06414449070320740c0525400415030584009441c0da82c0400145d01400500d24540214021320040c0001d006c0a02800c1d0112809007859011035147c140c3d042d04441e50494040603100410400b0b90014200790428625521003003100000541d150050801942c0c00d90900b075902040400051180610034041e8690b121880e060401c84082d255401a44461450340d0241c2400f00e1400007906041c0240040d009428000342030414424809000040807003000301041d004500b984000381050078000125000050560024440c0d24540b15843d510380c1d00040011000204c407041c001a400024050420701150b40f056451966051003401000c403400c02c0d050702407a034001401007000780c40050f103807010791b5090a079440c0fa51810b402d05260024031001e00d00744546c40007441580411905c0c7c002c00948107054818040c4050000410181d00300388085512135030000008101407041911800703 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 937654928 1250 937653678 937653709
    0x809010f02010605090c092b02090a18060e1c021b030307142113030303021b0d08150405090d0c03120603230609070504020c03250201140406050306 65
    0x10440548400c081171001c0c20079103002a00e0003011518407001d180074621200310108040c09841562180d200903801c41082d4007000c2e000d00325400106d00d0003104d58101c0d014565143c1040c04d012807075441c02c80001d140b10030214410f400b509100340e50a03001003000760b486020350b900078480c9842d40810105490921b0228540c1844100110000180d82e401d0343c109507030080c40a4903251b2070060f83d00507500040d207209010504100f0901c015901802c0103a03082ea078042c41c0044e21303039042141119256205a140300740300d220740c02004c0d08055011035441d11400003c06119400c2070410180015a03000f82d0348105503802540c40c06103034520074102c00c54400d010b1b10f0300e80b041c0a1410448003c072400340d0426580b800b005120b8262540b100518803140040c203400070070103864903542d41c544802580c041c080c4605c1d00004c10004144080054448880c02100780345a8031901c2004000004902101280420000740c100c0c061812540181c80c01c48441c4c0d19402e1130341d40c80400300801000b4907080c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 937656178 1250 937654928 937654931
    0xa080a050607120605120601060f050415030b210604150c120903051902071e060503061e03010f09020319230a06112d0f030414060708160201090809010f0201 69
    0x40980c4d400090031034603076421021f00701070750401c3c6009000010f038000c0314080c40010002000383c0140058090326076415403070005000044070b0000b4010301c1e01003c03050011420102c0241e000c240c00b00307400e4083c62040002d640b00c250740701281000d0384d05000c413103c00300b003640004400c0d402040e0004c0100520a1500320718002d030103122440308910509400005a01c1041c040c002060080400d03135000840d88614517080c1d1400100424a110081207180640014000505815441c04420034203003802130003402281e602d800c0c000014495040181d10034031075840b00e00401184100c42a441603080512039581d04a102c0386114100002240f00d00d90b48188815040800e45900c1400a064001c045e01541c503262803154411840c0c864841ca1284258000761b0308400c50510111910045040603d58407917480d4100b120b60300c114280ca800d9113000d0b002c200541180d004100f14400c10158402c036500b8400d0000072422030340300c40c4004100c1d8008005001817580030311708030415003099200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 937657428 1250 937656178 937656191
    0xd06030602031801180c03061e020f12010f030209040206070312090308010521031602030705030703230615012007060e01020f03280908010510050a080a05060712 71
    0x1218001ca03441151081c00d03071007051240380202e0340203005a82142211a50401388110b8a8a8001900c69984401030a03143d0700c400c40c120a03090400d443c2c0c410350b0405821074403010191500c80907a0700c440c1804c21049221070021900c0310034030560354103594025280b104660384960911945a004120503828070201c2210b443c1202c62a01498440b05d11a07a5006d204d549818240050310a03c00300359000b50a000b06aa03d115a0000559010b40e59000b060000240c56002080c1800030642010313416001c0c0c048044140204110300708216110041c0d140c000c03c9452207610f40b500001c1e149103201551401c0c1c7c1144641c030900842040e100d60096041070010001c40382450540650301282c04245520b00c03961081da0180100074440071248059403911024550038042581ca0b800c4c41c10122808424841c2240d00c11203101d00070b0f00c11304008001504140c2125568040f01d40b240c02d04c0b5019a0a000c10303042c80100f5540941580f000080445480d01d007420356481c0765031204054015034800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 937658678 1250 937657428 937657433
    0x122016080d0b01080106050a0e190b03040b0105090c04150302030709090203041406060102030408190302010212010b040807150e280b030a0e1204030828050c010f060612020d0603 78
    0x8024020910100d41c00180a01014005094a00142c1c40082400428001c0c0f404c290f40040a64810001c01c8440b01c0280500c240051060031541d00031801260300031080004200507000082d050b00d40c11205603849030b5440210940f244200d019220078100598100b40c0e41c1400781d00910b03045185c0d42050403a042e280c034108022038208650a589102c4d1a684800a000e004c1c007009402100c28800343d460141810052599480503085650040300501c4076801032520030f40c10345200502c81c07015003c42d96981c0c404c012154100d8002e40d9803134010100c0c0000e14000c1031002040014807502d9014a8080d04c03010442c000c0101080700182d081d440002000321080e011030403010f00700140c040b5450342451810f0070300f01c07040003020b01000e0f40428010060132410070150790031241d0055560366103545041c03240d12a40c920700407a040f910840b0095070039664120300900300400400c0001c0095982c003036101010764000380b0420f00821103039103142282d41e00b00d130024003d00062070030100d161562030303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 937659928 1250 937658678 937658693
    0x913020306010323060109050f0f090417040e090f010203012601060f08010f0f0905062202150a0f021c12062c0108031e0919090c122016 60
    0x380040f6913900e440b5000c0000c04d6030004040310241c43c040e02d0b901c95540700c0340041500e00f0b16804840380b14227a04000070b010401103d2003100e0103001d10410a1316a0b6844545003048501a0f404690301d0150b500310000c072407070510a42e8101c0c0c1030505240c5c001a00b58403084013405030070000354095501c030f42c0081808081c8050b92401850014000200d00c1440304565044a00c000c0c0642000b0b41081d05400c041800026560b4104a50960401d00d00e184010034209002a82000940003081c0000307000cae50008410142100701c84603242c00d1f142d0641700300200d031250100b907010000c0d00d40d203c6803803500c00e00c59507000c501500342020010304292281c2c00341d182d4203400c0c240b000c0c0c044d076a01a03441045040340c0002c0d0041180000550030688507007640080880070180b0503005450105458145036a1800c0d25a00d0707135254114440c0f001e4a40312888081c003504c02010011441803100d08903014000d00c40c202da048400d8007014503115520704032a21950010110103440d607000c43d121030104110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 937661178 1250 937659928 937659971
    0x1d090a030206152409030c01020a050604113c030102190806060705070b0702031e0703030c06060e09010905072102242d090105031f0b0d02030609010b09130203060103 73
    0x1620004c0d51600c0b5000c040600e04812040820304642102d03040714000383d000500e035a04141d00001d90400e4074103c0e4085842d000b03001280400300d00e0b841c858038000c0f0480c01d5054616034141d4030a003100058100034142030784a00b86181100e240100988200148039000981e00034100820140c504200d9455082c0f41801c0d541010082c00f50010b1290114902080040c0309800040740200240000075101616a5651312002c0e00340042c0014171010000f82c0d50088014018070040d0317517102d08210150364001e100281e421500f030b1042d1172004c503140e4980c00482244c00c241c107101011799485a400d00901d204c0030700c40d801150300e10080c88803f00010310080c2519000405103a424081101507441c1c2d4541210140400f9000170400342125980c0f1004a030f03801528841441e6504194180000040e500356002550190300803074100c20010040d00150302503c000c039400000c0342d07205c1010400c140b0411101c45e034408095000b8004015070ba40295501680504000a020300198222001c8000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 937662428 1250 937661178 937661239
    0x3120b120f07062f03120405010902120319110102040e0408030906070815063105031203011d070e1027050a0504020c161d090a03020615 60
    0x1c0800c480e8101a010060500102540d00d801035130341c0c4048180011001449050303a0482c4081521130303018190400c110b42402a009240d940c0c0c0f4502410501d0080200ea4002ca124145065215201102c000280c4080d01000c2900c43c46035001664182d07283c1090201880007035400740320005021108800d1180301e80c1c0115032140c0d80b890140c0103107050042c0140000144481d801c2408061040c1d20306800700e6020a803540ca40d540603001c124004a2545c4e90620240744107812035104120305000144106c81041d400c90303100c1c0100740c00014140c0401d001c1d0402200700b10240103901401c080f07030250030a40d01c1c1001803150b422980410b0b250b0a582c005800400c060610340c3c81c5066601085151043c401d83c01e80f600325052000040104c1094407e040c400da8021070744010000341030101c9034084881950080704941c1c0c1e88440e001e05001c5900c1ca2481003402c00015a241e1004035981e90840e034954082c0140756103454000031002c0c04040b10710303000008083c0c807854640644107148174800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 937663678 1250 937662428 937662433
    0xc09050411010f0305040309050607020612010b0a030c021506240c0d0912051509280b06010512041b030506070201060920340602030717010e0403120b12 67
    0x700d210016010000d0401c3c100f0816180c00704100120341d0104019060398012201c00390f40350001d0000840501030080c1030304c0303500c400300000125140e0a4000781003400c99602e0901200c0f500000030fa84450695200842000d1098005070107441c3c10100d030324010509003800d00716009490b000e00c6241d00260005201035002e40d014184954112241d4001007540e05404600291203907030341070312601554020024091410701041200105211030102c03052003c2c070707002d00359241d42d0758503502c04000c41c825104007440b0340c007043c8194880c800303c3d003922103a0b2100150549482e41c8095140c02c54491201c8000702070f48c00480020414060305000e0022907001103016820f04002000b180c2c80d03818080c0307142c1140419007500090303031003c0d580300c04400c5003018448050f01d030030192004043c211540c0c500c1e8407408020100106c4da80654010b0349242d51314102c5070000100d60075691030a01842600b0b031003000003d40020f208050b02ca40307082161402050207040280840e6a18603254003042180c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 937664928 1250 937663678 937663703
    0x3060507120204230102030d110417010605092d1311030309010c150e07120b1b07060b1336020603010509070504050a06051c060509130c090504 63
    0x40c0d121181d0394101c041e007a401c5241c2032a00b641600090a26980080c0e581c82080b50400c280e802841500c2044107040e2060000f206443c15440c0c56074007a00514402d40310360490300e00105014440d5405035240601400c1d11501c8007210310050342c0080c02d0354002c0d6008c10745001145200e1a09031409007880c4007d0f0080740e1075601c1d110349801d540d50400c0d07000354014031a41c40180c0c0c4c44250300f100d440e0001840c550401c00c9542540c00340201e5802d00c2039502c41d81200140d00019614079548050180c06c5a424584440304030b2100d419403443c038400304501c1800b400c00440d43d42d600000300040001c004400700ea030415900700540b00c40080e1541c0f0313800b020349806031b000c900d804a140710440301070303114100141d250b0000d0214017060007240e0082d00140009141c4034061811034004d00030080c0014225551740c84018a180d210044802014010b00b00061080c85540191425504003d180321000d6551048000004940080681d00601080700005800020b8440c2502950040c00b40a0f0700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 937666178 1250 937664928 937664941
    0x150905031215010201090b130f05010932060117030c0d090f0801051e041a0c030114010e0a03030f200c0f01050c0c1e040c020c030f0706090513060f030605 68
    0x440b081c0005003810340e410f04c4215130010f54500c01c00ca03401200003008061503030407402d200303d003201e007014024002e40c070304840b200078030103209440052140f070b000f02250154403940490702101c1410031071400507440311006000e9642240c0030100d10142040c1100e04001e00509075620700b08012000b41c02117060150284240101b161115002e040504001d02c6a800c0c21040d00342144074107005840e03000c8000300400c08110101030f00328035440f5115507090850800d41585c2805a1081c462021403004407140d106c400e5004070f080c1071040740700811a900292441d1001d950340500c20b034905d0308000642e440d0b03500181c0d0340082a0340c0040b540c4002c112001000080c0240540d0581d54141403190070300c0700300c614680c0021980e5102400340c030303900c00700c07480560701c2c40c22552200040703039100e401c01c4441803607140c2c0098540740c1100f088044a664a10702c03160240c507500107001d52800146800002e0026041034101003416950401340007400315a00c41d25107001102c0c640046800300e484070244940e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 937667428 1250 937666178 937666201
    0xc05041506020c0f0f0a03081207030519090c080706080108010f050405070b0a1202040b0901030b3a0c1806091104140d151d0a050a1509050312 63
    0x200108400c642000c00c0d0901501070341c0d5950a500340d82c0700d00e0440010a065490300128124811000303450448060307100d140c00c0c46280c1064024580e00e035108000540c4c96446402820b02880340307496100e408020514130340c00a07184152040c1e51248840700b0000c1d0050041000000408d40340e03039800703695414940c5050942d140992042c01903403c1805000c0800c801092645c1100c42c0c86074410756900c440181900d00c00340e402e4888140700e00c080382c00a07055160200400010100366400c002c0040981c0810048070207030500703682c1c002400000701005600d20700391800c801503814419205031444d036991840070308003a00110150300c1000c1c610090b0345224080c050141503500001d001e07920b000c0b90000001d0081d4810051684070a020381200c40e100d000f00080c0081d0031480c07035006c115841c00544081d08004046503504400000341c0c180e41100842d034900c1c00c951180180c00742482a45442503209544108105440e03555440d80000a00c20001041241e600c50840c21603454661176040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 937668678 1250 937667428 937667441
    0xa121b080f0933070321093c0809040903050702150f0304031413030b070f0504080d030209130c0e100201050f0a0e01021c0b09160f03270c0504 63
    0x2240c030386902c5041c1d00030610401100403000f4040c444107071101c000d4102240c5841d401000d1800c0f580070300c03041120300c0f0f003a5041482003a000b00001040c00d00c040400408040c1004c01911321070900c03400002d8055290800c0c48a40c0303014046042c00c08800ba07002804590140d141100807030700c0001d141045003880005840c412070220003441c00c00c00d20b0111141c072440001c4c8020100b00004629040d1200d0190507160200708108401310a03980700d1414030f41440341038904c0404109024201c00e8140e11a10448040d00c4149004c0c045a40702444143c01a402802450380d0040000c200e801c1c5c401c105104685552900f0f1740c1d40088812901d0078041c1c00c8502d42041d10440e410082000b100c200300030042c68205e4006000040c402070032400310350080c05840000c81580c1d00200c1c400c0c403403000640107034403141d004031750310860742e11000b504e48490783c0400008800b140d143c01c01c1240c0c0c2070080d0300c43e03040440d210a48004110300f0305c001d0202010410310440b0621200001480f03241018881c91 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 937669928 1250 937668678 937668709
    0xe0f06010906020a021c05100509010b0618060901210603030305010b1923070b1b12040b070c12441801020307050711030a121b080f09 59
    0x480c1c005040c04002902d4901052010b809a010390600c1a25690940c0f0340b0541c0e140c000742502d05100c054482c040161400b6950751901c1d40c2005002101844e00c1403c07030750030100d9800c040c180d0086103014000103402a1240d58140140842003910079201514482c4804805500000c2d005007545006021141d040e044aa80000240b003004140120806414078104103420708080c454104201c0c4131040091034041d40404001051800400a80070350007802410820108a0018050085000180102140210008045004200850a10004607800a501d441d100c2114038490b10760305034414031902e002d40020f0007451054a0304001c07000700a00e0125981802c00c80305650000600c510184180300c60840d0b00d0503011505442c1d03035500750520245400c00944d140c1c81d11010152103600241800e8920405000141d82c6d6841c0200300126200d610004c1d4180d981c0c01c16200b101d1440c00000240c5418502000210100d03209201401040c01e940348003079034034801581405121007403036258 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 937671178 1250 937669928 937669937
    0xb0a02040e01050603040c0810020901080c09030703030f0c2108070905030c1507060c08040317010f060c0609060e100e030c1023040f020414150411070203070e0f0601 73
    0xa1007031484003031060341160700032a40c00351207840f503040c88845603003164808082c6124040e0342058040060300681800c040981341d1601c2580e0b5a5050802446103030032245e49900071582c00d0000030b00840c041d8030400c10902c0c1460000f00955179007442141e002c4540306a50140e8503040d00207a0b0f01c01760055114003949010071400e1311741130120b560b80500714540e600c038030340c52400c8045000c004e400351240b0980116041c401c14204c00d00141000d20240c40680010344400050f40403e85049111812940b45999008a441c94418101c4031a00c05080031640e083c0ca4041c1c22004c607050340034400096942c04090194003421100d07803800c55098624407103403070b08280504050a0300201700761542039840d0601141e40e561649074401c110301c000c02d200c050f03800588140310a01000d10819103d061080d5800c11880118880180c00001e08980141142407200d505011b18100340d005900820340319019070341072104940c0001e080000c0c40c1c0015a010307200c4800c0284003d10f407481250019800e090 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 937672428 1250 937671178 937671187
    0x8220906030605092415060d0507081303050405011b1a06030d0c05030904020a09080d020a12030b0f0f040f0c020115090b03060403110a06020a0f0e0907170a020f0403050a0b0a02 78
    0x107a29082480c0902040310942c0c05c00001e0b020001008000a0000d0003d10031656040400c200000415054a000000520410010f6481c058586402c0074040e051303102c150a040c075180046952042d903007215a603d0a402c036010000a034408805031003061440708041c0c080c80d041c000e040c030b082da1440a19003041020001000442c0002c001c4a410b00419030b009a9142d01c40030040da0800c0e15540f080c17945120308014070303911907400310303440095a126003220050400c031507038210b094802086c00e1075807104e0400705405440c60684a040035a070400b40000c2a29a440280602140c02d05006800941d4603520009000d07000400290040c0c04451020452030210740c0110b0b503034220040c00202441810801000c807c2020000c001d01e0f1940000195174920702c9141c02000e140d604e400090200384080d09041640c03038400f501c40d03c41c603c540ea504070052414921f074a040c00d8068411100d01e942000b2112130f9050200086c4050f5004500505c045011460440c880600007442c1e182914414030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 937673678 1250 937672428 937672453
    0x12020319020c0a03030e06061020030c030406020607050702060406080603010e1603021503100e0c040803041412301228050c0f0c0f010c0e15040302030a0822090603060509 75
    0x5440e0032039027046182a050500c0381c000d416220f000311000d01031403848080b41c0c2000c0008004001e0059078503950a4031031030384409800761503a0082c00e20080d40f1041c1800706105851140500d198000340080011031096036440741c02d8100285224202c00d44011003005006604040b010000d00745005801d10340356191050030a16650307a03a0050f00341184c040004034191034a0407043d03070050b0002c07000381ca586070b9a0303c81080e07884100c044002e0013503120090440c2041004614032a900003840e006800d802c50070955280c480d049504d9030b0058107000d010318401000400b00c4c0c01c0c414840c80ba0140c0e1030006800311845148102407503110100d0811082125101003c1c05803a070030400c06d000d00d92500f075030702005424445805140e41c895880c180a01d120035502007441d620f214415030710284d1050305c40d0b60001d502d04c102d000294050f8807580100740040c0d10031000b880c40c1c1c03c40900e25103214980e41165942c21040b0361104600c0c0d625074000f442405101d03c80e50b40c000030341c24000c000006188 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 937674928 1250 937673678 937673689
    0x5220b07080903192c0306040209100e040c05031204031110120203090c130209010c1106071425080d080901020d0c1706010f12020319020c0a03030e0606 67
    0x800d03030400c00c40e070034000c151484410019142503c07a007843c424160440c0180061955400300e20301c2a50f20724241804504c0c0b200d164640780c480380050058000c0b541c0303540a22100388805409400c01901c90304e800102e500c240381e03826004501ca840c4e2455200c0c6080d040510b4034070359003152894090100001c0000450b11001204910303070941e101c80400105490503101e130026031440c0000a400007041040f010b4000c110344c03114030000c54002100f22128a9650201d010ba140810b01160b84450614080742d00d940c450304888070024015440c0000315a40d0090407110106000d209500c503e1580a220044410011000700c170100381c011002d140c20340240d610980c0142c5001405035800214114800a4040300c0080780c0b0314500340141c40c06c08500905000320201000f141d82101008221558828224015100400c4ea2100280344041003100025880a4505007000d00809031880d00b51000e4005006000c10004c007401c0e091a160034040c090394280d00c0000c0c1a81c0148040100310b0342d51 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 937676178 1250 937674928 937674931
    0x503060406090605130f0b060c0c01080907230f040905160e0c0d0906150b07030908010e0304061b12260103030815030a021816050906190513080105220b 67
    0x817403c0128414520300c141e0401404c1005289420000016500449020008880d44620000c0c4d0b11805107940d0302514544590302401401e080050340070540890003e912405504503600070300c030311141041080028122100da40003110740c1e40100341d0140d800c1d0310000c1e40000400c0200711903010f514100c69003140300d10400042d0541e075540c40d000001446000c2d0700c125460824501c121884035100e040301102a005240220001a0390b204041000c50301030288440b0007401d20021400c050a20b242a80d218903014040c85c1c0061208060341c0110741b0386041404803e0182c4c0b506448030f0b8403940da101046000443c0c1c03108083c0ba0000406c0001d900c010780c01d40c0f0546912910b0388000580001034181552607101030742c800704403000e031042e9100451045005854031001c1c001c0d0b1994004050f16030b030166885069101d6014001a0b40d8084002c1243c0340484052030700c0d501d003102d0408540142c00b4543c01c0194241c1d0740e60108100c0f403400780b1412000c44d94100c0c140320054199034410030100c10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 937677428 1250 937676178 937676209
    0x90d0e030c01141204050303190b0307050d050a12030f0f0203070c030e0f06300c0d1509050403031e060b0412020f090a091e0203030a2304060503060406090605 70
    0x1641c0101055003440f08162880303c4110061004d081c202400c0c050390320f030400e603407904020101d1500040c42800034800c1c244c0194019019240701481c0c80704000d450307900d43d48255110302508038410009111807078200c01c00b20040d2070010308d41144804000481d0f02c001400b20100d48100103108400d9006005111125898903101528090078130104202c41c69021155402c40c0b008184066803400740d08064000741040640c5088001d15451540481c0c80161000c21900e00104020800403085400804c41c16200348901c8180c2da55500e0203030300300c1d002142c0c241d0000e5640ea00c03550110503a035680243da0b1074003035400d01c201400e2201588891060388039202c3c3c0880c01203107210464850780d0014082840041c0603002c546400342250000d4004d03034200b210a0343c000707495500f02803c003542095510350054011030800108540a850340e0040c0d000342d01984400112000380041070310001d201415817036503082c0e200d00304182400169a100d07004400310740c0c00c0801c284155124409840340a00d07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 937678678 1250 937677428 937677437
    0xd0f1b15260a200c06040b06030a08070803040203160e06131e0213031208011502071d180618011a031f020702130905150f0a1d01020a08090d0e030c01 66
    0xa15032440302c191494051074003880d004130b80d105000c400800c40740e00c07880c010843e110443e40c80030109030301c50f81e480400421540080c0030f2140803407401e001440c4d0042c40601103602491203007050800c0646103030301c1602c503402a901084007500304200c86d000c101c401e80d2414401281e20740040c104503002c5031403040b074550307000c0740c0c02c0700c5c2000600c8044000c5410150b14144005040c0b40202802c900b401005800c081c1045031500d01440090b0840449141040784a44000400a89090510040c00a403105031429000b200510380520065025810b40481c0340c02c9410801d400c02d0954805d8400c40301e0700040e4005440d00f030b44021440380c0c2080c1500110340610522140820024040c80601940180d1440e800d144207030040d038030000015000d10112010b2000c11a410840400105c40c164401590703030020440c0c0d290302c0e40040501c0700d070b880850b0301c1c80f00c54140c02c00d08907003100c0c00e032500141c1d401c0244410f5000501c945404003400f1324260302110110004696900d0000c0c90550402 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 937679928 1250 937678678 937678691
    0xd0905060a05070c060507020307140105070206090316090e070e011820131a070f0212030903010f060f080303010e0c0f0921100204050d0f1b15260a 65
    0x1a8442c00c119204180c2c84089014100d888100090003900112001c0f4080d00c9240341c00304048012114411500034140d403602c0c50100103500740045904140c0d40303d50148121501000f00110b08058600a001c40400014070290500503540c50b022055000c11050486d510041c8161181850016030241e40c182d004990480c884641060341c0d001001c25004400002c664003032a4040d0356581d00448009541090740314007420b59001c020300c1a40d40c01424056014180c40041c01c2c00c03510b0142288405007a84d0070000c60f42d01282c25a0a00040050301655940041c40660305001201d00542095402941990305141c0e51120806020b41802c07240c0101158408034401203104413050450040c052080c1e2000c562518010240c1010b00165a805405068100c002d81e500c240c404807000105600601109038462502641e9a050141c0702c144c59012410b050170382c1c4411040042c0035040300c111410081540c020131032070381072403000c002e1441480307051031058542609039002201c0403030010b493f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 937681178 1250 937679928 937679947
    0xc05060c1603080423091501030e032b020307080408090a150c05010b040e0c0d150e070f050301110307030c0905120c0411090306071215090e0d020d090506 68
    0x107000c051884000c00801c4040003108100d1814090f01c115000742080180d000d801d550340c9842c0e03182450440e42c01030380304000100380c907801454060b41c441040c10005030306642079140c942194031188017560030340c2d130202d41210034012030081a500040c00308400c5042d400c2c840c1008083ca00c02910180c80400007040e001010745d40e00ca007840040a03055290f51300c00407080780250440e82d01c4101941d565181151510090809008030000405c080303011f0701011400c1410407488800640c02a20f1180d4208002c4842014510688003405850b000504082c0d02e02030080507116000e0300503030701a90500300da00003000305120a80c2e4100e25603007004241071161180031210b081a5074406540258406640c4410319008504201203400071340301842204c1c030100703405203176105942d401500b5600c007100040b105403240c03a46654031000b440012981c01008031000c0312020164001c010182c1d42c031400d62030b24030020449101c001100c1d001a1104100107400603281c11818440d49015110000d2030059 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 937682428 1250 937681178 937681183
    0x20c040c0c0b1012110f040c0f0f17042a030f0f110d1b05061306140c010e060a140609151815090105010503041e02042a03060b070c05060c 61
    0x1c2c04c04841c1014200d032142c204046450b221a151038010907541045c0280c50402d1f0080c1c0c04444501c1d203e00550060062084900c07400c0491100104003e842169540b034100540d1140103501030f02e400d03004002ca06032280c2d144030b4496401460030007481d00400000308460100c40500b604045071410000490a180320401c840303030411980310480c01462010000d1051542c0c0c5096006060940c845880341c0520800b44074854544140d03104140040043ca40b0401c994041c200e00740c41c1890070900c1000155003034441c00300410501e80c02107000c21884c403070380d449802c084c2e82609125904908211010908040010740700c0e213030110404c21802c00580700e00400003d5084144602c450600c1d01840706d802d5940c8844029110710407150000135a0b601c11303401c0d03078090360708000c040044114280780c1802c0c0060840040340c10a45543c0c56040050200c07080441c8840406110300b03c14800d00b80c0141114141d42001c51594010b1021001003065003102d001500e0003510b01c1039880482d12401c61 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 937683678 1250 937682428 937682461
    0x925031a0306070c0b07110a02270711101b1d06040306020d05070806100309030c120810050a0b0d020304080403080408030c0f21160b07020d020c040c0c0b 68
    0x10340600c941020b010883d5070000d9503800c030a006004c4180940c44a440403140110707003122802030380d4082c00702040036180011092042c0c40c0801d50030f400d025801102d92045070b1040f10560003160f488040f1000107030b4140040101403c0c00d06040040c0c0c0c65403c030300c0c4a000c0285580303070100a01041d50f40c507070451000c41610307000030040005031560798078549140a944214007404030141020003241c401805582600d004200041520701c400711404003c2300101400304040d010807021040703000201d05540d02c95106d80f50f0380c0d62403110070300e00302c1039222000d0b00aa00080c001c2860070001c2043c202c4101c1a0313400e18000690141c3e89445034100701209021790782014003071410002c4c0001c1c0d0a80004020b081607401501034840135000d0402403616590300d480030004421020404600640384d600c000c1c0b13a85011492110000c141c0c49d10303401540c035421603880015a0120b01840800c6404101440b404201250203105413030903284000c04103008004005c000b0010000407840014100400c803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 937684928 1250 937683678 937683731
    0x609030605040c0807090b040b040204031703072601081b090a2f03010e130c051c060c030e1501030515040201020f0a060c080c0c071401030b150702092503 68
    0x1c84d17500c0d40310b01ea10710040c14803800551050b4034013025031480d41801d009541c00c503034016080c0b00110b02c2c11580082c0c42d50000b8051030030402c640f0700b0155015400b0071494000350318065102c690798107100b50203140150385c591030b040180c5030004100140c2e0740c898605901c0071030400b001c01c01100e520042c40e00304000584d0b0740100300d180008515401200d001441c12108500941003150b101c61040d28050840d0000203040380c1040c4031b05000e68100300e100b0110300c030040c0608641d0307100962640c004540800c0355201c00261030303130310030a01d004040050f04404c161040400042e0b52540e51032641d903942a5803000c000c501c81c0d0000a05580c002e129150405440c4816104070304841c0c0391150061070301407400000b040419010644003003039182500d24090f180b070005d1002a00340002c00c01101c248000c042d0400da200d039103440309a1075415051480c0c0c24070614040d102c8000b4410090422001446010300d03030101002010383c1000b1200741902010036044c00244100240b0315810000d0124080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 937686178 1250 937684928 937684933
    0x70306050901110c0a110a050607051c020309031b0109080a030816170402010c06110703030603170705070303140423040c0e060f16022205070305010609030605040c08 73
    0x41809040c0e000544109540c6008000f00c05854182070014000d1085400850344101200300018a4030a4409842100108514082556400010340341d40c031030003003140c0d16041840203400c3d5000c0c80500d1118004940051405c0012441c007103540c41c83c0001116029500e2131020715926402046044040c0c04202c0c156100d44075a8200a041c884c3c0540b0103030f01410182824600c158810307000021031540744900c00190b0748580d001181c2d117820300300e4180c0d03405581d0240040c600d85c0c000b0091441e07510a480204a03207255040422107100c0560f21101e0010b420050440050070124122060f20b915051219842c00440b41041160149400c0304590340e0304209a042c44003010b11503554032400c12a000c0c00a062000d40485218000500d01c5800c00000d00000495911300c2c005031104168800c60001030542903000035007002c2607441000e44440140c58000d0350b204e0305002e46031344003849007024027141d40f61220082000e01c1074030000e40181d60316800b20f810032404200030001082613004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 937687428 1250 937686178 937686193
    0x40e01050c0c25060806010e030d020a0b01090504170c030c07060806030d1d040917220e01050306041205070605010b0a090e10030809030307060204140a170a2003 71
    0x80c01d803a2a80300c1d50342c6020703500c0b0310a005a01d40a00c03031140060710b040169402032162500009641d417420117003109040c4a440e51418840c0d03201007244030700805995005007020b0555041c02a441075040e0804410941880104004580801c00f400c43d040503082d60b1565680c41c07010f0b954118000c030f05c0e039070070580501000004c0c0d85610050700ca002c0c0700c0c1102070b595021b001220644500214070f00c0001c9007041c024820301c291515a200c06100c9000d889450005490040031041c10360046c50040c18400d14002c03504010701120301c81e40003404140142c2241c81d410700001035079851000b88002d2a4002540360040158480d07000e8550440c1e0100c820300803543c450f01c01007680d400c0080d44e14006940b01d034001800510100c6028000c07240e001d200b407000d03401c503140d04c000c0f680510f10094052200f0403000c00000e0070703840108010304004840c01d223080200070401840031348580c004503101c1c03600d003611402000003050450480707a11040400e0760541c840c0b140d0344140403990010381d040c0210072 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 937688678 1250 937687428 937687441
    0xd0f020a24080609151905030109050601091b0e13020c0609060708090a02010c14030c0609030304020103110a050a030f0b041d010b01080c04150210181a06130902040e0105 75
    0x41403014881415164030000d69190303021320103149012284900b00c004258902c1400341412000440001c0c0010030040c02c040d190004203007034840d04c560444030b43d8002001004010340e181300c0c05030154444d103001282440c41e40801003c1ca0702e010b81c5075100b0034491080c4030001034160f0461380d10140d5441540c00b10326102c500c06880f54001c843c0301b0b0118114034001148180301103400c10020781d050312070140c010480e4407000c012182032031215105200420040030000c00400040f8484d410342d00c01580d0b03d10341071000405681c0c102c80c003079200d400107014070305a06422505444070043c6d00e00d030006003482d0503038003403000c3c1111200054001d071505810001d107254502d600303031101c8070000c001c0c0084d061810044030709290031100304260900900c400d0000d00c03c01c40300001a18440d10444021521601c040000c80d10080c13900c8100d411081003030400c004101400c0800c2000014200e90b441c0340c5030740807401d619081d417070070304c09203a07942144c000f15510b0f036100d040940a208004c000d42d28000c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 937689928 1250 937688678 937688729
    0x100321021f0509120f040b03090c030712120206100e150909010f1a01170a02040e0115020f06070815130222090b01210905060403050a0314060d0f020a 66
    0x1076030300c100f0070700078040b0a890780b00303084c0d085034031050211440d2454185495a100ca07240c1014001c1101401144001d5030b02c0d40e400c01113003000c0c0c60009400312003400d4514085109409180e1a103065420220400c0360b81d030320054008040713400e1110202441e64600c184800850300f00c100860b8014211006d01240185c158003020200c40f80e214200b184d0085e11221301030202d410180325000070b8185220884410202c54180d4100f40700c04e001505044e2a01690084218260020f140b03440b21002c101510302e504210914410701620007414007030400b40300040507940f00a0180907000d001005110040d22010f240201c0400e6003c0300315180c00d04c0d001040365000303813005c41000b08031002001155030340062040035028130050f140c400e07500f03d207400908070000c800026642c00316956890200415020b10082d4420751185d0b480a90742c441c803010103001c9603150310351403048541001c01c0042640329066044d0200d6004041562150f980d0320028600111035080103041010503249807043e43c254 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 937691178 1250 937689928 937689931
    0xc0605150a050103061203050f04080607020a150e3004080703063c06031514070207030807081815040906050904030e10030f020a080f100321021f05 65
    0x116921071203642d580004605031451402100c06106800c045c49001a005100400d42581030003001420f282d603070440e440c184035085481d080540c0082024008008000d065054000c282e07001c10044034500c103020550f11300762040c026030012020010b061144030743c11031071001c01c00c43c004007517965525a03141c1900c80c915884212900d90900b8140344c486045460740d1686844462801148410340c3c1070800405100108883e003c1540c6072004000310b1120304003076006400c900d0010815001821041c886500300402c1c00c0704540292509100142c0c062088401c103640001d0705603181c2209520803901d202440c2d04043c0d00107002000340403007440d100c01030030803900214000c000350340e5540c040c002c91907400c650060000300550b50b00509440c1035640b184284460341380c002407000c4004078200c100d074801145000801c05200c1000440c140d80c0340341c1c43d0312a20f0a4030a4291030325640d59003985030b0703550f58090304469400d99030400341842007003e0316190111213104c4912000d814202e4005040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 937692428 1250 937691178 937691221
    0xe010b03010e010b0907051e07060b060a170c09010507081309151701020f09190906170f1b130905030d091406220204020f1306110d020c09070c0605 65
    0x498170014102902800aa549003400000d0004151681c211511025400003004480807030781c0c1c1007680c65513101c9501400004910b900c031040d0005407001c050941e10801003081c01c1d030700e40801c207824061364004c040c0d401c40341d840309030691200d100e0070744503402c072040c2d4020f10081441c0007158100200c80345514422a49041c0b848900a0320a0404c0e60a030f2107840c026030341e04241001066458101908504100c030262040040003988910041082c4c51544d4803400c40c0145140d00c14000480c01e000081c03282c4032200c001c25001c1d02090440301000006807203079210f801c04a05d4406a5692a0040030005602030242c0303a842038040410300003440d484c1c005881054000c42440d103200000281c00c1d003d5988101810001c0400c40d2138101d42c204454002c82e0825020b1004029102000010700301603146c08003649032050a0006c000c00d01003941a5100403580b002d058640955008520b4036040081526900120359130322106607549522020b0081c50549000308200382d45e000314008001190 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 937693678 1250 937692428 937692439
    0x90601061706010915022103090c0a035609010e062404020c0102090f030d450501020c030a020108010e0907081506032a040e010b03010e010b 62
    0x81d445012880115002c0301d01c6400303d210004240142405030000c14101e403c14811603265426031170382c4801d03002c1d1000d211401c0768404414054002c20a00030001c5132842681c3c444030300c500e10740310800500b01003520226003000008401900c0501c0c9207410341c001d445105407400700c0008400c0741042a60707810803080502070380c00c0032500004d41030080c0b10402c6001c0c001000e4940b80da80301c400c40762442100c41c0c400c000c0e90110030145915140064042c40485000050b10384440740240001d6070002001144282c0010260f0910302c0c2d04580c8400c1001d480d841d41c000b0050400407c202014075100b4103020581500c0404c03200e03221903100314010350303500b0381c00d8035200001c000900d0740e101e020303110003030110b10380c200140300391a610040158064000400c1b03038012035460620130305003200104078000c00d252060804c07005080801000c040a8842e01c2d071612070040034900003206000c56400c15104980303901070002d00100940011141400c010020090a10f404d1a414001d14080c1020341c0a03d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 937694928 1250 937693678 937693697
    0x61d070e0f0d11010306050333011a07080d05010b0c010608060915040219120c14180618010906091b050a0c080c030301151b0c0b0f090909060106 64
    0x18188a4110658031001510080081c012a556039800d9200f41c050541050f6407840006070542e41003114003141c5080000d01220912150715140a07000c0c0040c43d4201180c030380004000380111a1600800d5104644505442c4c00c0540f510000070300c0340da5a500e001030304180012892a040170010310740d4081540003003081543c2e1f002c003180c994904903030250254200720412202900001d102680c000d200074065225003c0300c2100d11034100c01e40d0800504450180c1811081181c222031801c040c100e0000d1181c800e1401100054880c06c600701c3d0309000d210480d000c03441603240c10445009080303044400c91503075078407801400000e110710300c1852000303400c0800d405120300743d1440001310364105030303655450a4200501582c2c0c5d406043c6040380d107418100500c02d0050401d0003d58042c00c0702c28540700722030800980082900700b00c4503000c02c0f0b107c05a040c41c00043c090144107821140046d04103a00e907070120b440002c2d5402100f806030b0b000140481004010b07034002c030b0000e0581e805921402e070b01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 937696178 1250 937694928 937694957
    0xf081605011409011415010c150501140118050303030112060e0105040501150605090f04180b090d0905030f10110706150305070b0304080901141c0902091f0902070303061d07 76
    0xc0f40140c81e0706d000c035a040c2e200050b45500c602582c260150150b0451a10b0481e5000d0206c1101e000f41d000841608000b200003000d580d200d00d003510300c50b0780002e0100a490405000030340b00d01c01841800000c00c0d042c0703401000c21440780c000010142160000700f1692806062a030b018000c604121090340003295401f01e00c040c056401c0d00d0396080d000d81000c2c80c058505041c00000c2140400400c045038016611070009a4000d45042c0300f41701e8074000d000c6101850700b0103085200340760007042c440d41210882000301f40c400070b101c0094001e2718030082045030324039605460310310801c4005000d95081c06803049403944c20144503800c0381c1c86039040766022a9222a001c00030b00090310000c0408108101c240c0185d8462000c0c520075950000b0034a1070035150045003650420301f40c075041c15543d290f50300310080d0328203529002d62000700c0314451b2040e1041c90b4035182c8000c080d400740700c110503030110360882410301c0303036110b503001c0c081a00100940410000e000c03681c2003802c4404400299101800034403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 937697428 1250 937696178 937696211
    0x911100e041b0207150c0b010303051215180402190b04080d0516170d05010e0a0f11250803040308181b041e0203270a0f08160501140901 60
    0x821410543c06818031900340380b28107035100e2003207411004010a601c06075000c220070002c054000c3d07100b81c03505992104200310b0124101401442000100034a0301c42c0c0c003103a00ca0340014a00c042016110050951701c40c4001140aa01e48586941d0240e00441c0881c280c03262000601c25600c240c0111803045444400c2200d0320700c140c1c2e4501030925207100d020b000051010004201980c200c40807a03040c1141c400010b012200f0980c01140303415446002d0021b6241148581c026403a42440705100c04131031050010b41500c83c088000244080c0d49044410700ca05c592050540315030322440ac10754030b0401e42001007420381e01f52210000b00080e17200940084a00040d00d00d0000981d8084181040420040000500d0400c0342038510080c2c200c4079900368201072005511504140700440716008d02d46040400100000b440c00705a42d000d000c03040041424842420710503944500c2c610b5449650441c00d00040507001c100a1103907081c0020410070401031500244039200c402c000700b01400f40450041c0c2c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 937698678 1250 937697428 937697471
    0x1803060204120c0f03020d12020106052e020a0b1501020c060a050405100c170a05092d010e0a090b1906080417030f07030b030309090c03151009090911100e04 69
    0xc3d80301c914101c7c06000a01907014410250609000000e0301e16a40d01c0406c020042201116031401040d40744140d42c405c1b1100c980c01920024801010010360f65519050804805408001030104104145006030b10801080e42c003084060003c0351074024444002e82280c015000785840703284a80385c0301c800c051007414034003801c82e0025080c1521810800b00e116469116014980402000b042814103d03118981c4071545408490340d405181c00c4a5504081000d850090041c1004000c100b07c1e0044d0b526040c0d403205680030b100300000c582d006040000c0d899221100d035050702c0c007004c0382c0000304950403400192082c0e026210500303103207040b0784400d401888110789080040048501240131103200e94030981500e01d015045038035113801c8000041040e441161860303054107001040000029207401c0300c52250300140c40d02c00d02c0008656002d0f107440b01602414900f80d941780741c1c01040c0009042c8903041d80001801e14810b6800307886004120045040f0200c0c066400d0041d2081641e5002c030486 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 937699928 1250 937698678 937698683
    0x50d050c130b121c030902011709160b03010807090b010c030806310e070b040e06040b060a03091202070518040507030c0e0a140c0304031803060204120c0f03 69
    0x140508961402084220001e031541c0e4450740b40c1e00c414460540c0ca5030704100c51404015402014065540d12544290325207045244003051308202c11040142d030400d07030045070500001d0303041c8441e664a9808524085100c8114054029a02c0c0000303021031405004505a4002d41c040d207140c5921124000d0980d51484111070028031074501200210b031080f1141c51300100300030715002d440340a5408080300ba050b00340340003228030500040c0c0101c1303109a120741244480790002811100c3c0c0381000d2160300f801548105491007100100103900307030365140e000301d800c000000c01d01901c0702c48095008005010a5004a03030200e910000007508030b000241e00e000b240c0300201150703884000018545d00040b00584200c40e18820b440307010000814602c40031000c0d00da21400c50541d031a011100c0b409817401c4142c02c45503c502c1c2030a002070740820300101d03580305802d4104a00e800b002c1c0f910303141e11b4079119400035180c144041008240c01a60004140000c0c0c01480800c83c06911202080da1041702c0b40b000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 937701178 1250 937699928 937699933
    0xd030507080901140a02100506180c0c030c030d050601020c0f1e0f0d06090b0a06182a05180303030c160f0c150306061e0e030106031713050d05 63
    0x5030014440c5002030000900600d044c00603116000914140d5801ca07100301005a000584003c8148242e40305960307119908031780b0031f822100d844400c02c02d10720707000d401d00000e034800107802c181a02c0c0070000c55140d14003003405c40381d0b540d10741d055883c000c1a00340c80b928014003980c07000c0c840d40c0c58215251043c807100100700085401d01c81016800100c0c0d440e0200b0303000041180c0d034800039aa4211800c060500441011441602a1500c01101d08004100000c1c0f546403000901903c92045180d62003d0030503880001d81d514000c42d03401e40c85465103400d21079001448403043e00c03590f204024050103909000746859403482c0c1c1041548074082241c01290480042c0000c0c40041d14040980e151140140c0b816446545c03181c0324002054030a402c11602203100f40c2c2e080098030350510030b801c02407142d40751104608000510040307900d04081e12a0742044052198000d0b00d980a600c5007006680c003040c2c0304881d580c1045100d00c070790480d10310b1010144a810b00001c80b81080352503d088079501901 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 937702428 1250 937701178 937701187
    0x1e030f0503090703020d06091208152e090e0601050c101a120a110609180a060b0a03090c060314070c0512270f030c0d050f01090f0309050d0305 63
    0x10403240c40c0c000422a0000344645500000561142d07a400d00b5040d02800300800c01410b903040450705005031152002c1000050001c0240d03940c0c1c5150303214400401261504a085508003000b05042c2d520400c0040b82e110001e81c842c0981d8204500d2811100c015608062607031350304006658600400700c1650144c0c0288818108016a07079000c05011282003140345122a06840407800042d582c10344000302d6880a200c1c042844501006034034414011943d2521300344070300c80441c8055a0307500b12496141d800f40080340400343d0540004015100052071581c4840380110001c02404071428141c1d4a1200c1800114850303203e40980c050113542a00d030781d02d0a13200d070282141c074500003a400303690b81c1c011714000000d00e4501200418441d0310b0300e054020b896040b25201048d6610700d03100940b040c000d40c201d07800da0344c4010030b00d1411034000b00c90a942c00681c1d81402c83c101005c00c2c56060455292014400c10000880b01500f4070301d0080c0e03240741c803042e181c02c28011107510000020300411414403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 937703678 1250 937702428 937702457
    0x501140d1113151b020a0b0903010e011811100203160503090d11090f0f0115090e0c0703021203010f0317090a0b270609010c030c1a01031e03 62
    0x10418030004414203a0341c0c1c6807100401100c404006550000c2c000410f00d140303007020495004444086100480c800809060459800141d40c07001d144a40e00c62802c0106000020f50b60071760007450000401c5000340003001c21284902d101e072a845900310740c11018880c00306194105000c284c50440c4494004500d800c8140c6003250b08a801c00390100c030700e88410002e00b8140d03102e500c0c245034030300d20406103641c0307451541041081000004080002c050800020040e500302e10034140303030440d0014206141c60031180d2000700c130707045100c0e04103003600d1410708144007410380341e8030040209600a6003910819840b50080d010203201c28800c810002d204d542060001c1012030304040716410b0b07480d400078940307801c810101d941905aa1712505064402260000c00000b01d9280081100100551403176403071074000001e03203d40140c001d424100039901181904140c05a40c1c022841c80c0c00c41c2d0442e281d441c000044442c2004240012110000c0320480390b600c1403010311098a445906031a8294940f40c1103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 937704928 1250 937703678 937703681
    0xc030216110a0812120702032d130806091203090a032f060603010f140c070206040302030f01050702070f06080f0709090f020d0507020c060d090c0317130501140d 71
    0x140c4160b200300380311000078a0a004119200020030000340e440c2d2121a00030f80300c00b8410700185042d055400c01c010307440302c03449040c2c1a840c3c0c0640c5d0200039a500c401e104c0e4500f00501584d41481c110310039110002c50024030006101b4803540f801c104880c880d01502403d151103002c00e6501301e00703030b91201d10b841001900a80034410100c982080e1045400d058603498101d000b8400d031301c40c1103500400103001305400d00307006168646505060a0280c111008404001c1160061046005920103c0c91004550324602110011500202151034100000030040e008203c2541d2600c090b00c01d04c64000359007040103d460003150116101e841140e82c62212802c11100003e00e03078030400c0310b0214007103a040024172a44c1100010071600580360082401c00700c080300e03009004002913520101c800360320b0707942d04800c580e40c005e00c09401180302099441c15203400d020036080103021140808035803403240034500c040c0c0038a890095104003125905d20040d5110400740301800d0500000b007110f103210040300e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 937706178 1250 937704928 937704953
    0x3100e01090602120601110d0f051c020304050601090b0f0907050a030f061806141c0c12080706050703060311060903120316020709050c07060b031f0605040c030216 72
    0xa200200350032803540d841c14100e84c800e072164281508114140700140d43d015940608201100004160890804602404120f0302c0d0500c4000c00400241c070300e040004560200b02c203006000c50664a0382801e16100c1d48400b001d0083c407860f50324104984801c4e00c0c000d4004c0c40044001b03403030b000294441e24003c5a065100781820010325444804540700300c103440c0b04450040c0f40591088160034040d00c0c001050359416405890141c60760340400004ad0790360040702c0b0b41040c0540e81c8024002851038104070030345441d070000d0540d060208018052012400003031150740d2044000700810350f540c02041d42287c106000c003510b514014038154819040c080d000b4a040e000050440c0d007110088804064241d00845001002a1f200f6a080c1d10b881e404000003000380445c11028806850301c200a46071a000e802009040140c840079200582d0f10b051200d84408000b410940303422925052481010b8a03271403140e0b6005916203a81900524424403c1d1444d140004034035102056064445800e400e86 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 937707428 1250 937706178 937706201
    0x504060311090a06050408010b2727061801051006030e0312010306090204052217090306090d26060906031207050a02090705041d0a1805030310050f0310 67
    0x70000b51580303944400400c030050007943c0e603481c2d407541000e81c402d0940303807030364810f41c003c82000118000e44141c080c52207456400e148880802503442c0101c40904450704050001e4110000d4641e040039100891814170842404603a020b2400207100c58500301d5008960318071000341e4034001848428440d811207441800c41d01d00712800c1c55004050030780500c0081e44115080e9940b6580e0300c0450411380603490b842102c0d4030885064101e56207000b00c00740b680702801081c07150408005100c180140c003e0790707401040601200e5080c94482c43c040e654200b2100b401020032100429003002c4505454400f1060100100c030008503102c480610000e0390003d0180381e81f50080000c2e03203000c5c0d0300c0a8050130a8600442c021300f042a40d50052042c000e0010707020400300a402c0205001100003406603d030616400481041d4aa031000c070307030600904030310300810300103c510a01041440b0000020394040c44003120200145a43c5404100d402c5508aa40030f4051304082034101c1c01c030146e944465801c82 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 937708678 1250 937707428 937707461
    0x3030f100b0a0201150b0306010504150504091802010201060b0a0207050105070c0902070308100819030f1107090204090f0b010e220f05040311011e1a040507020106080d0f05040603 79
    0x1e454501031405038001e007a0300801030b03650f0640d820b801000e440301040140000e0030000c4c61801c043c40002c2aa10450050b2011095090034561000e0f102e0b6007202c000b06402c40007001100300600b01882120b40c60f113400d030300660a10f600414003608141c11107618a249400402c4035034545001901e40360003100702521030b02480301c07001078444a9030006001c4035102e0303901c04146161240400e4000f13105508503440076800b540d41840d108000a4401c9101905405c00c0040c10030000812503c05500944a000714080d0244c001381e0b80c90dc5802070019945480710504c842625045440d0840d0b164030010340c0027541360940714040e414542c50b03070944680400f64200760412491a004156108201643d000541c0c4100f00400c0c10750002c55100305a414000034814903000ca6032940f101c100034140204800e568450181855030303a40e00702031110201400078400d40c41c0c000c1c0040e001749a94410914030f03001e1011008900e505c00c4a250001200980340c850400341030281c114010610300b01130141c0079 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 937709928 1250 937708678 937708711
    0x907091e0e010608012408060d05010f060e090706170a0914061005010e10080411010302070b10140108071706010522080106120203070e130818010905060c03030f 71
    0x1010038401c103010b0f01c01600c030f50751254900720300c900316609580c0407101042044c901c0c245040f680000416040b8500700c88a813800e40c1c2c1d07800e141c5e00500d840712103081503030b1070214009000080c40701900d01c58001a02503a01d12030b1b07200e0341611041040b4034103a07003071540c210000e031603030f2081d510403440c1500a800403090142601380c120700c0d141c1c0541c1c2c60800f900a0340020015582c0c8161070300714250040d40c0401286034a441e0290061384064030041c010b451046001050b43d121f80e0540b09246c1d04070000801d1410003920f01011007089010b088400c401c54009860f003940a204881c0c003642c002d07a00c0541c04540c00944080014020309010b0401c0420045001e560340400c100858100c1c0d1842d03185c8280e4031b080095821038405501040720641c48441c0d02000da68003003507020890311004c00c2c1c0fa070316560f00451030000103a80c00300203144443c0412810f00e0b4099102c203034008890300ba2113a01c00c4c280c0707520800500c0e0050041050b55a8000c100050f001031203403800b1500045e108d020880c51 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 937711178 1250 937709928 937709939
    0x7082802180a051006080601320405090108010b0904080309070b04091d0f0d08040606090204030503040f1d07210e01140c07050304050120061303030b0907091e 70
    0x81e141c5041c15051212000c0302408580c88442c840d00350441c420b18220f40041d4580b1001030054400103140740e05111103043c2204050000c0106101a0610560070580c180c001c4074407060960094010180030303504000022407050014440c0035a154001008841c1c0f550700e995510340a80e00090481c40301c1c0c0902940002c05a04a03005403003d40000d60f400f182917080c03d82e80c1000008d020098840640c8480c40e0b04000d090081a1003042c0001460700302c006035594101113000d410a588200e180d61300c001000030600202201400c2075030310601021403076503a10200301280d401560f54402d2001d840c0c6020901480c0503000300c0b1090008540e0034000110505000c2c1d084a200c514101b0700c0340d440b900280680c411510b034403540704c00c0c04c0701000d040403401c0e211340d66a4081c90085a05111414078034510304226400c049003c415400c1c120350031380c500503829103405d80200804402003418100d00c4841498002d40d203504c07a8980fa516402110701c0e0841407500f4041015a40f07114040f00c400210b403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 937712428 1250 937711178 937711189
    0x8041703091c032d050a030605030303091c022a0d02040504061a0d05070603110c01061d2a030c0d0204090606020c090c03011e08010906140907082802 66
    0x50a18510792003a800391500d05000d07003110300d0200c0d2070341000789600304001c403405950003c4d1103149a51070095201c84101006800070309007500034a40c10701c404410000c0750388001440726034055042c018921410005c03a0141ea40c0c40f0800c0142a1451015558920000301d00e54400c0c80203500820921040a80b600820129032090304c0994036961188140e1412014030b440e002d004200586010602000c2d5450f000e4a414450003500c0800d5180c014040d0400c4550701640c0e112458000208903040da10003035580a4140d1030b0743d20404014210004401c80c4003d122180f49580702555849040c04480c1c1c00b41650f17100918208001405102e845486502d1344098800303003407040300018a081c14002d001c0e2401e664124114840d000c1c480c10000b80b8101613058134111034101c040c200070215528440c50184200360003d240da03620341542c09040c0700643c0c105000c0d001e182c4140045603142d5000c25034071855203000d812120352004c03207543c440c1c107060484801a00381702c400c0180fa0001ca03600040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 937713678 1250 937712428 937712449
    0x300a0507030e0a231023090111100e0118020f0d05070f1806050628050f07081b03041413060e07080f06090f04030804051c030c09080a0804170309 64
    0x1d60a008458280c1124288000c4a5010b2100c1e82003201b50025070300003051180d002101d003059002408181800d0903402042000e0141103c00700350303909103880e4549040104031010700c3c0c601540c20710100200310000d0f0501000700b02e40240080c00d00c04446e4061006408410201f12540e101d4800009040100b00d100c510180822080401060303400706400400d0310910f4000a21803001007203851a800f2040301d203103042640145400c10000e4001006880c0780c007518888140f450800a00d0004010b0040b00070005c034100c02140c92540b10110aa503a5a40140c6c001c1c2c110501860800c04103601d048442134a0045c8a202c01007410340d190540b121001c030b4281c5124010580001c1032240352070a080107954084819105280c45290041b01c41440740c0010300040d0500460a01150500000703015484210171950304080c0341518900c0c00030010024807107a000040c0203d080465003900101c2c0c1c0c10700d01038101d0352150415051241100f81d041541071101110b2100300300c00704043d10340c05c4502 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 937714928 1250 937713678 937713719
    0x15320c0309030606030102040b12090a0b1501020d0e060a030b0310060306090309091109100302220f0801110f0c1609061a0703020a06050a0b03300a0507030e0a 70
    0x4546855100090510f0140c0280400b03100380d00511041c410003c0ba203043e2003c50200408000c107030384070440c846007446001e00000d008a022501004440090084842203441c000c1e421030b603101142c00011146e14044040141d4032000402214800a100790021845000d004044d1038012482c0740e4800700300c1340c1c960301c200c91030368540b40305400345500802100001c01d440c0c07034140040f11207404078a440d446002503051040a5410000140a209605450315500784403409480c032400c544109070015210721a0700c0900102c0440070440c000d0600900c140d45c10130b107a42d107080801b4815166002c5e0071490009955200317a0781490310003509042460018050b00b04009815820081120244400e5440003503407a1020050b407c000b0f035000500034480ca40107035000a5079120144904042c06c640c0c507002c0c0e4180302d0455410b440000c0e01010541302d00c5807100d42503032510300d544c4143c1d5078000d10800c1340204a05000c044007081c005d900b01010290024221400c082d1141001e04c0c088105aa20 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 937716178 1250 937714928 937714933
    0x7030b0f18040302011d070b07030302040504050a0902030d0f082d01090c02060c0a1d060910031d0f07140612090a050d09140d080c0109080307030615320c 68
    0x81c001895020b11405d04105c50880074134051b008030300036490382da2501d40704820000c94006045001d040c4a54141e40151800030b01c1406281444045d400240007042d905905c24050904086002130240d02c40c0843d030f0080c1c0c0c80b080001c1c1d4407640c100c3c0e0704802141141040d584e85a0107040c005015000682c06000c80400c0007500d00c5840f84000c1c5803800007080302c2080c1408000008030203030042c10340e0020101c0500c40b1448c003074a05020131024069442d030103170000200c03118490f00942507003242c0341d080c6501c001043c1a29000100c103640780380b4804210001d0704424802d1101c40002c001c80c00180381c0180102d441e1850500e0200c010034011205805181c008412005c00c000050200c0c214000040c545100e0050030800400d281c000040040c510610342d03c4200e5082150003000d41d00d41e041014000c01c80390866007480b003615802111103200007407500d1400b08104110401080c0102d1003581c07103290303442600c8540c41c549965800d001e201e0b09081804098107610a40003400c05034006c801 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 937717428 1250 937716178 937716181
    0x240609061223070810151d030a06060b070219120f060e0a030806030c030106060e040c09051503191b0309021801290405060702010e0a090c031a0906030607030b0f18 72
    0xd010340e50950740210180d030000c4040d1b00c100c654445101d0980c000c2d420200c0001046800009192012070b0300020800c1e404d0003000504980110094500280203407030300c3c491140803000130078504aaa01070700a241100303a00340d40204000781c0204d18481d2080d000001c0140006c00c61510706041e400044000408240400010382000e00400d468a50254001d2251a0070054041c014951209210303010301d940c0e940e1348403040d02c10b21080c4000d1402030b21242a401e010810040c4030792040b43e80004104a001412800303034550710a620342ca40b415441070038002540c4004801501c0c40e01800e991251908503000c200300080100d4500800bc1c4c50084885c00018041807141003040c2031100300d0340b14090104000a854080444100960910f4503540305004c41000031031440c1690425018a4900085000e03800d40640c0300107002d002600000003104100030130440c2c030b500101c40c9650980c000d4400b103034034140207030024903200c040100341d803d07030010480216402410b490f1300b8660304600c050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 937718678 1250 937717428 937717441
    0x9020403021c020f120c041b08010821070317072c0a0b0c0a150b130b0f01080a02160506220209040f152406090612230708 54
    0x480c0010780810b1007000b5098400b01e5000200300760820405035014120301444000e5090042c0400783d010f03500100100102e8050207220051600b206010002140704800040780c1b04000240072800100c02501540001250000103102d68008601c203e05200c002c1d688095200e9010754803900c28020345e076075403a124084074010522a441e1191581e808000200c922050b91030b280074120540c0d10002420b551003185c40b440510b4a001c41038081e2183c4801540c91950014070780021105043c01c0b1040016a00034042c1c44085898501e912644204000c107900099400307104000d41c07140e07156000500f0030070340e004140d0139400360000447c3d80790400d00c10000065030403c0d904003c69100e911113580f244c80c0e80e001c1a8070700c2c0040c0020340036041d03042903001000307001c40b00207020008840d000d02144080081c56400000030940322001000c00890115541784201a07110844000e036440c43e455a40a8800500501400340e09040c20086049054a1012071042c00307402100385035541600c900d800d5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 937719928 1250 937718678 937718689
    0x4021606110c0d0c020f030d02060708070206010b0a081305010c2609070308030406390201110d0c0203090a0b040314010504021302031e090303070e01090302030a1412040902040302 79
    0x1d403800d1036a41001e10070600702110000c0e08048000440c1801c2c0c891074054000070391040b040000d090f515128200b00e100c141a0f02044003405010251a80390b00354035200d4003641c0b6068240124401400184540320b0310302d00c83c8020a030841d61454905504241130340b10b1509582113824a04c2c0469080c40c0249041200c00039401d903404108140e011b03540c1814602e00c1d0700d820403032001904507a0040081403e000c0c1070341c8608000604407800d0100f10700c020500d00c0c03400c03149004000d50a02001c840c0200300c5d006002d8001e8107050140c4c0c143c80d107040b00010310001c0c03010995080c1144018000032101da11050814000340800f000031380c0d211840e51030280c1d43d007000c80d1070707100581c4d05000c1404010f8407000c0c0f40c40c695a4141101603100d50b2203010003001c507407c01422600d509210001d00455000102c01103006070040e03034031a040c80c200d02d40191480b91540c80020341541c407802c03000700030510b484d142c40c0310f462220301a1503808858040040d501d03001904052280e0364001420411407800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 937721178 1250 937719928 937719941
    0x2c0124081f060513050d02090c0702011101020703120c0503070c14010f0513060b0604030f0b040809030a030309020a0f080712080f030403050c0c040902061603030b03010e030702040e0604210c0204021606 89
    0x40b50800c28008047c1c0c085900b5450150076440811008515002103a0041c0f19003550800114021903c5601341d00f0010100054440c034281c445140101c000c1f034a912420440c1d10034021900c42c80c25100c0d0590341c1043d401d900d858140e07229540c2e0b44100310821501e0050b580105040c2595000b180a00d042003000c40f11000017540c411881000204002000700c0314141089030007070740031800f5681d2030034041744c00d116006c181a2b0602510815104250b010b50011007064002d8843d1460341d61140700203902d4141c1b0b401b8001542d444140d0820165228500d8140210b20400c0510b0030001e0144605102da0021b5030220003191000c40d010800e45010085810085811a001c1c081d146558020411911480d40020281c40d4460201e20905019800c5145c0408002e0700801003820701404043e2207400031101284904c0c10070485049030540003030542d004a4008546258619900e44800c9414500e44540c50911401d80b9003403016964903c05801030708c82d00802d10285c0d104516121003100c28 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 937722428 1250 937721178 937721189
    0x9060302090f1b160b01030605151507060b031014040b1b03040f03020a050709020403140706050f1809040303022a0309192c0124081f060513 62
    0x504410401c002d841805204003003011020794680d02c06074801c0c48074034980f45040290540c0c5c0c0707140001040183c0d0780d2000f485004103c81800421983c0c0301004603e040391071b4507500e444400c1c000746002c1107a0b03a0000c4507000004045406031030b070104c0c401c1c091307a03c010054100d5041d07402c20807017401550380410b50f000c00e0b0407480b402003c0840646009500010304043d00070582c011a800402d4000c1180c00420354000049031980c6607a8070305a80654450300041360141100f42030801e04000003e280c006485540c1c94580c2442003812800e841900030041c82901d00c0c20f0000300054035103401400c5402030303000341ea025070345a2082105100000712070128101039040c03a070100d151200040306980c0c600c0380446d208019107002108801d88456550088403001c400700b450329501d185035182d1501040300d00023900726943c0c0c1e580c13038041d012401686441c0c2100c1201c0d060389006407056040c1540b00c1c0f06a0314911003142c482c2d000d074407515503940200c00490b43c0050040c880b030010501000003000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 937723678 1250 937722428 937722451
    0x100c0506131b150e180f07020d030608030315031c020d08070804050c010f0e060d1b140d0207140f0703060e0a02030318030c03100b01030b0f0619030b06040906030209 73
    0xa03d840f002eaa00e412007550944100519400c8000841e0360b00d00f00d51883e100c0400d4014154144004040f441e09000d40e2200d001d4402d100b60380444500034010304007143c14000c0614150354400c0412100d4501c02d1048941c14050091031300e2502c0100141124201d1042c0d00600d45059614400343c12420003604038424410b05604110005500140c0703481c09002c203103001c1030204800601901c1c07441c002a4041c0c1c1c40384020500301200c506580c04050340085c1c0c5841c150300600701950550308c200c0b4440148410360390810425042812030b4000b0444541f04610304245803200030307040c5003050400040760b032481c0c21021003003050003404d00a0030391220491002e013036010542e50009690f8407070a24080c00c0548940409012958244280b00f100d020203000d591002d0248104d03000113010111860f40400d11388200a5554109a40001700051000c1c00b814a480d0160b401c0c407000c03440d030400c50070405480d050112100e803205c5000c0c1004115004022501508507c10850341c07850050540c5910b4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 937724928 1250 937723678 937723733
    0x50108182104211a01060207060309170406031d030901020c0f031905161a071b0b13050a080604020120030906040e0906070c050606100c050613 63
    0x31900455401a038540c0e9100380e189410300c08180340c40c80d00956202001500c00416128a140022203503000c20328420008818480c84624081c00441001c1c01a2030041e803001c035007401081d020f039220707091440c00703640344086c2d40140c104403000551041e0042800652550194960441001e148003d2048071001540c244490100000d41d60b800ac1d1070554841c80006040d848151020b001d10310703110840303041c505030002c41130400031f03500d6540b44405030108410100000b4114445018406070390f524401d4580340124586514101000441e03550945100c1c2c0d07000016240907030b50080241100740300900e00c4451030081080004d0065903c182c0c242c1e0481410080180c1c0d020b5007082e00d10813007600036800c1c0b80c00c081d006884c60041000c125008480040c000c170f01c103600400b00a00c51032901e400c03902d0603a96144116010486003000618561020780400c600d40b40c10148007240405500e0403155191483d1503c0c0d00d005801c2d50190082c004440200c01030004101100c01d4030700800408080d507 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 937726178 1250 937724928 937724971
    0x60c09220203010306050906090f0601090f0b0d0c06020705090c03010e090a060c0e1f141b010906090501200f0d090b160f030603081c1508010204050108 67
    0x248119105680318000c8110403042280d10401400c030503100e00001191650385030302d001d2004010a80380c410032841030782e0000350b412100107030501c40743d10720b0400b90459910b8804500050f000600d68107904a0310b843c0d00e403249403150041c44100502804110015a140c14006400c144980d080340380511115000c01204600a80c200d0381112071000800300c6995070300342c0140c2401d204071b50040405050220000c4081d50008281141c1e4208a800300c007041d06a0039235140c50b07903c1160341d10200b41965002420345c06040080e010b401d1038600c4aa40d0102d41c0902c407401c481e81d15408960f455541e41c89601801000d10803a0321300c0c2c401c1c0c00d90b03107040301e0030304003403041401824802c1c180c07100001401901418190406c020380342d40030311510018200240070400102100c0c2c942d6000900ca5610546000d1190089104072504000f46500d400d4213003202004240320b100700c0c085160340340e58143d181c240103003580c0e50050030028001070b1030f1400c0a00040449030040c3c0070041380070102090160 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 937727428 1250 937726178 937726201
    0x14040308010801020f03041118040c0f090204180c02013306081314010227101409010e030703080309070e01050102120a05030402150a0339110a1e02030f06 68
    0x40080d04564680c1e488c1c084140010000c404010001201111110910003000f00103200b44060716660380107064825124555402240550302c915040401a800300a024402c141c2c8000481d94891001003030f0444049201c41c0144811301070b0201c072a541c4100c940c50025902c1c165400b400c4289401c2c0f00c241000307a80000000f4042002911448000c0d03440000314009504032503c800f041c0c00e86000212480c00b003502c403012000c500d04c2c0030746119842800d2480c031804181400304081d90000b406c01c082c0000444041040d0704425030144102080800851083c2e000380d849032200c0c200402daa141481c1c1c02e0714600c401a845141035500001527205004130070400c4e01e458809603c0d0040e181c0d9a14000141e203c0414001e50402c0d120001e00e60f203c140d0301d40c1010810910031b0800702c29800b0000c400041104d03003c0c210034804001103900000c1d40b40b295014960702c0355041c0486003080c066480343d19a41c0301d041d81000d1150309a051f03100442c2407d00800300b1100000d00903140f5450541103100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 937728678 1250 937727428 937727431
    0x3070b03070f02030c070303050405010e0901060504090e010e0a05031e0a0c122006010518010f030b0402150c010c0e031f0221150a050d030f08040606030614040308010801020f03 78
    0x207050101039034141c40424820010f8545241da420100c4082503544e050103082039004d40140c60000c0c015030304072405810044002c41c120f070318a5503402d26203032510443d0703001021113074080700b065502c9101500c0c907002d080200f01d00700e0b0300803005166182080b0a5025181040d40c034282c6101c034081c080c0b1020107402c00d00000303c6070b410500743c00e441640d4400c100c1d01c400c4458950b005080c000c0c9051000c4040c00902c05041c0c0700300390b40b41030354020401c0741c0c406049800d104241007105400001d00001d080031901e01e811520180035108800000c0000109513042014210107a070354940503d4602a405007001420340401ea004c1d001602c0b504c105612a0003203212041109a000a4041c502200c00800180344020020b819040340c241012014401e40d01128070307510903011520040380510b04804140302c4541c0c90346842e1200d456603030040e40e50312001842507860310341e582c0001002c24124000c0039401d038041a401c00c041d00d07180c64003500d8080180c00c0b0170080d82c818081078148882500c11207 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 937729928 1250 937728678 937728691
    0x10e0a14040c0c150917130314030f070210020c0a030b060117070c0f03111212011418060619111501232103040603180c030b10050604060c050c03070b03 67
    0x10078a03469a043c03980d4203070754140c449210448001f076982161080c10b000715090302c3c40340202883e910148a07403a6528016045419055a010030030030b8014500080d041010f0400f500549008001e03103400078002c0022580155915807041d82000003540c1d00089001a01c001c8030302180c0b1a0401c800020300052180c0d0700104140c0c0c0d0b00b0049414503000384c0d50211510804411a4040490b070300d801042a0040f509184080c66880c0000c10350701c450041040d14804080c11845a8400c1450740b0f001c850005040d46411050801c000205203d4a14071000310b010240c881040c1c2000c000700544c079054081040018000700200140b184a181c0080a60720850a0b0b80c02c07400c3c18106400203420600c121003207503904109402c0d0801c8614080080e00850302c0e291000c0190249480c4441140d00d51902e004001200e04617061000903840c2c3c10058000b0312001c0814465901c034804600b155009400200116105010500820404000c1c2e94009007081c0c010702a000e1901000c0c841c20302000d010b2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 937731178 1250 937729928 937729931
    0x2010c0f200c0616031805060f0d02130f0e0a05040816081b010507020f070e07120207120e0f06161101050c011a130c0c11010e0a14040c0c15 62
    0x10140c0e901c00800c0b500c0d180b48401010f495880300509a400d04200e120b9104a004c5035400f01502840303030090184000703c1e44003400f10ba10b801045001240d40e42c1c080300040769200d50901c0043c091744918148070b4042e044074160315080b581044010000e50000a00c0350801c2406d1104110010311090190390862100c030480646c0b0002a103080c003070714090641030001c8400342e020303001e103d080e054205030b02172046a02590340c849602480d00e600c494a5000da00c3c003030382d00301c0302062980f4410000420780e1040e4200044c2042059075840c0c4a01030b099060000240426810005501e0308050600c00500115041442d240018208201e204559031018041c406500003d1140b82d003d00c0803240c48803001402003101c60030314011714a0310041040300c00d0080d03480304190640000c4504c02d001c0f14032415100c984042e1120341c1d800c2512002010074504100700c3c0280381c401a114500c01c40042d050444038106a02c8445091104940710011000e0812030401190008100410b1040d00d41c500500030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 937732428 1250 937731178 937731227
    0xf0203090d03020f0906070b01140d080a0e0d0f05011407020f0715030e030c100506061821010f0203160c0b0c0309120403030206040b090d0912060b0604060f02010c0f 73
    0x130602e080340070303041c8403e410250001e00c05c03040000003c20306060750b040d1040100300303908000c2401841030707880c1c1c4014104001003102c24100c9019155041d003054004006000116060b41d559001040e00d42e402c075984ea4440c000c3c1c20000004030110755102e1701a200030080b186002c0c200d10b60398850b51180e10710203c0e01d02c40f41401c043c8242c100880c008039020851340c0c3c404280c259a0340d1866940c510480d80351034031020800a160140c100c0301c800980c01e8030304444198a50811000554102307030000004040b010707541e4800420f01900046203d02000145c0320b1420782c420740309420004c42141d00b006401c04048001401c6200c0658100c0b41d070407680783e2240d40701d00240b840d010b15420301e00d01c80100442e0010801d50b000a107188a1403052402c030025460b580c00199071004640c03c0c0f0320114849000c14419103a400c5040300d106402148003280030100030000c070f1099481500b080b00015000f0301c0c000c100c03c0d024040c1654048243c5008a8030b1190860028a20380d16501110a072606160 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 937733678 1250 937732428 937732447
    0xc061b01020919030c0501170f151f090b04061e1403100617250309020409122c0114070c0f090c030204150e1f080a0f0203090d0302 58
    0x181600d0300500003500c140c12005100e41c04010241036844202c034942550a00401e855208403054040c4088d140c06060480e190003007980150140105800000e0740c1c0f64038945400c2e62840c520340c46000300302044038824068220001c200c121a41c119068000c000c03c0200f115030b5109146652072050008000aa0328400c0d900319941c0002148100c0c401c0804000d004441000714664070841d02552100f8407016845d108a039403401d421103503011762a4404103800e800600d944400d0b1094501440c00055041142c0d000030210f489a402c21b682c40c1400c00e404064280d080100b10302c0010488040604986204c82409072149201000a0400619004000e2802c900034141c0d150540e2203145400d2641d01c1e501b48004800e80f0348036490800b810882811b00140c000e208550540d4060b22510b1a80071403c030050f100d00e01150541d41e00300c88110384a42c6100000354600300c2a41c160f075280700c95030230021120010f82e881241c4c5242d91030701c104103000200d200003d2002000c0700c9820096102c40140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 937734928 1250 937733678 937733681
    0x509060a050430110c1f0908070807050301053d0905090615240705070b120405070e1302040507030b1e0414060904060b0d0204020d1a030c061b01 64
    0x541100200c80c0b00d549015140409180f500108003a182e50b8a1100c944400c1c0456582100702d401300e4103c00d01c0c1c0207081c00c3d9941004010303040201400d1000300284c0d13500d1428034040e01540900c845401c03030f00d001d22180c5001c1c0962070300018a8401081c40822503250310404045403007005500144a00e5500c0e103070240389651400170075034414100100e01c3c00070b02c019194402154000000b0380800150203071441c01503200e002c0e103012103001d55070554803048400c0c0603038410542600d1511030400c0024400a0a2000b030070709900c40d0a550b0300c0c505140c80e02524015145e003060001c00c030756504100104900031124020540c0440340031903d5101d4180c10f078000d080c42d00c1440c0d0028001240c400c6e0480030303011100410401034404220220146a103010030320426520554020700c44000725010921907000844c1e00c6d54018210598100c956000030108e81c490800944043c6d201c90303038441415003000c41050082c50903400303088442d00e62030020701a8071595415209020901c040160021400d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 937736178 1250 937734928 937734953
    0xf02040501031a0c2104080d1104060305010902070308070e121b011107050105070311010209040203070816080403020d03090c0b0c01140112020a0e0712050c090a090509060a0504 78
    0x6001040256102d0410010005070281c0040600740808081044804094225036600040c1420b081c0c03c211174041c188800180030f40300751010403090140c3c040d1105240302d46411104156202c2d036a80c1d03d410000750070741d04142d0081c41c941e41705100d0003011035000f22410703278031180c0c507e03004021a41d5000011300c814015144c42c0041e00c100500751440c05a480d680100c90f18003601da00701841c811b520720a03607030f000034003134240017507018440b07000041e0142d40500b881d282980b0025091000d51004502280c20881c3c0840c00100c0640a000101103010b086101c8140140340519a81c509a00d0195031080d040b075018003010b0b83c0e100350b030003403164100758400a40341d203c0a0a6940418001c101e0180218015405400150900004048800d0300085080b035a01410609039240b40144504407014001c1c0080c06211144c01c418041400d18890144503001c0c1d00701d0b407a00c6204038014000c80b6002c81d041030002d580f0785401c2c8810700800240160b44245002c4020645070795a24020220584 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 937737428 1250 937736178 937736183
    0x4050603060f1c12030b0f03120304080f1303141908030a11070602031509100b030c0c01020a11070f21141f0b06030601120e2e05010915120f 62
    0xea0050f0800c204a007005450307286100d54040c00362414950400c0724003180e00c4211641031b405000103546c490300b07c00243d58030900a94040f418642080301d4414254400c0410755180302c03a020051080060500d02401b50b00c9071040242810544c58860300000131035410050329a04010001841c101001d0b00034241d00d901c420f010039111070035850b0100c0a500103031202c1400d0a0340c500d0030740107814800752151280001000c10007120f031900109801c40d030300140456031003400c100300780b0303902c484240000e1008842c180d070b41800d55201c1c041064141062500322040408681c0700801204001281208154258100c0302c45001000d180401c841000c5409100c0180106c08243c495010324548002e8101c3c901326045c4910318840301000f0451008980d2203000c2503400419040c080a158440c0c50b407044100c04584010b180e00e040c00e06500c004013800f245500107806004404905c40c0100e81c01002c0f90300041c003202c1c0c1ca03010b1040c001059070107001a51460b254030700d001e108850034503082117038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 937738678 1250 937737428 937737469
    0x203070b040b09040b03010b13180606030305070312061a0c010e06040f050105070c03050d05090a0803091e0f0703020d030504030b0123010c0503030a0e0a05010212070f0504050603060f 81
    0x9980b40b18840d10b98010600b150302c190714040c00383d0b4a03802c040c0a02c030f00c1c5941c014403417404011039809190042000e14804030300d8410030300000d40051494030500700910300949480e61600781e1494010b140422403207082c00d0031814007400b00111284034421000d240c2d80036140303c0d21069200d0085005083c03003a610100781c4202824407043c0310f500342d1507402c100c4c0941d00030700c560f6441318415603003140c0c101002000164104000350003069540c5c0000d4020919000b940d80a18903900c441149070803d50307070003c47d5044a180c0302083c446289054150742c60141c080c2c0807140040030000c2e1504001d02c00a802a0380003202c41007010700c40d400300c0d00a16404542050743c0c0d42c49820a9491b450740e07003900c1a1002c0c400c0d400500c19801060350010256010009514541d00c94148030040c26041d6206100352040260301d0002400a0014000c616180010380c440c0d4034213441d0003031a0881c00301042c814003008100901c44c0b0f807a8441100d5014000f6203c41c1140c0e0f4011b1701103105403440c3c804440412 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 937739928 1250 937738678 937738687
    0xc0e1309051020040305061305031b25030c033e01110c2206082b11030315120d020106050406061403040b0a090c0f0f0b071e0203070b 59
    0x106254409030080000c0440341c50f500e2280100d40381d00e40303d940000350299010303034001112030003061504643c0910900036241400b10b1524801c02c80c41300f81c1c08132006a00401140950b1100f91580c4500030030700c48451035080c51640d21102c01400144c0006414a280301070181141c1144451072214640701008d1951420208008040c05150a65015002822001660b07520840c0000d84001c1c0e031038001c2156090000034144030085001f55501c0d4901d0540f50080002d5001041c0040500042101e81480c4000c00d080a0240c40c40002000201400f441e90480d851609000059a5004800901221a640244000461007401850600400c1c80b0721082c64194a0b070641110044880c2500c040c44040d03166007050300c1c5507000c81e90a030080301041c00020040340d0280300040c2c002d1584240010348000c280c0360003109040b2070300200010352461004100c1c09104c901d007500200303181d544403410071103640d0303642c1d80424640702c0028001d8201140041595018042d880c0100386001d1040d689 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 937741178 1250 937739928 937739953
    0x6030b09030301080610080c101103040b040f0506120712060308040303110601050102010b15070215130e060306220c050909070e090f0c010f0e0a120203060a0c0e130905 74
    0x200d0b80240942c8190317001d0440441c07141c0700c1042c250800e84001d034000d400c1902c100c0b4144a92808082c00420820820341c44180b1180307002e0005201a15040303089517512400c0c036000101078611640004d0140c0c2c4104610010716000140c40c503044203091411406807240401450060085900050904600000c00004050708400e12a0903031180e007041c3c0d52242ea90300300680c22034551000030b81c2c000000182e801c0e0b106007003070014429644020f094451042c5044546402038110080b03500c0c1c04400490305200c1070400c080303420781c803146c120000c0580c4d1030300d0181c055110b0b500116500038445e9511001c010010307a012244054140508103000b20b2800c40d0f41d8a03a9504a4480c2001c500302c04404101c8800d004030301a002004d0720002080d001c07071a1001142e0300d00b4089401c004220100700081401d903152250200140340c0e01c400c03641d0002080c0109400c00c1805401c4410140c0b900b01c2040e45d4580000110302e04400c212030f141c01c0c04490060b0000039181d10800245070340224170300080c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 937742428 1250 937741178 937741183
    0xd050703170903010c1106270a0f0c120206040e130b16030b01020c06030f10030f210804020f090603030702131b0207080303151305072123070306030b09 67
    0x40300c4120f0003440312001e03050050391042900300004282e50401000610702c40d6203110f401030010650058130700021114500641844520310048401c01e18800b880d03014003510307415180242c080365100340c0c0310942c56400a0f90500c1548514100c0149003000540303400000500c002105400000d216128178082680441f101340000000c40400e2502e0070f15582c075440000c010a5644015001901d10b03200e0940e40b100c0504002c00400188051030340200000d00c0351404a581359129003181d030041c01c528a01e9918400b825800482045007240800015a13121410000b8180c01075440c080f140d01d9000c0401d040d489402d40c0030307420454484c256402e000c0c40b5400f4440c0480c4c10307000610748546071002281c031032175144146902c55205101042102c1c02c4017601c0401408018141080b0400a0110b0015120204d44440208002e410640d245d2002da540420103020010800c100002410b0000b50305c009910003070440302ea0943c0c0024100f107000e540b00002540c0c001006000c0c0d460210103055 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 937743678 1250 937742428 937742437
    0x435010f0b0901090c170406060b190e010804030c2a03050a050c0d0807032601081507050405030729121603051b0a090b13032f0d05070317 61
    0xd0140c1c80c0039000148a003154420500502603554074886c05010784100044a400013500070365060755100e10005805080c05d0003071480f40620b0865050a0015103405048944848015814070520000308000264001c00342da5500e036000d07103011035208001a0940807410790307081c1e0003112040a400030051140c0000d5a540c0140312b041251440029007041c09000907a40c400109048401d208003030010b4001c0b1005400007203200c40e0308298000014001090b544213901c1020b45800c100da9545401004008442e0b10a00c5410000d1402c0e01c0c04011903036580191080221650380c048600c0d80300d041d00850112400c440c1c950781d988801046034801080001a5815440c2407808405525018024010603104081c81070854030350031212a05650f4690002400b10104020b42d80d0106120065201401d04404601d0340c50010741e080d8980031407200f900d07400380d00728061003201d40b00342d101d0141c17081b09400304140c07442442511145481840c040e216040200030150030f030040b400e0000840080c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 937744928 1250 937743678 937743701
    0x311010c02071e031109090a02040203040c060216050a1707030807030203120a0b060f28080601020f011a0f010c1a04060f0510050f130617010606050435010f 69
    0x6955140740032850034100e01c2d21303120083c4002d841c2002c000301e505c0c00b10f4031142d0000e0030b44180c4400c0507043e0b0020b000ca900440341107440c1c0c1c0c141c103428131a0960400074101280035800c0380700d00460404000800a200c03030711440c0b151300c58203402203217001400d00000d00250750044400f48c99941c40c1c58065120382101e00e201540021040c0000c1c0165614000c0050b480002b92101e40303084019044882c41342d00c00c3d40204102e2a205820800741120240d101801c003500d5a29030b1071606080000a0420f20411010003e980c10000c80341e6000264044032908a6401c070740d1407a5980340c010040e250400b000e00007804041e0780256502c40d4441015415100d144034000400c0484140d012400031104240d0303882d000c9940c03200c418403150600b00101c0500540081140b2031511414800c041074071151340101d00c90040011034021a40c0c800d003d02000b410345818158140307400c01c2e6114059103264030701c10042c9d00d0860010045050340e01c1c01c07004a0040813000344400a800000071025203140c3c1c144 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 937746178 1250 937744928 937744949
    0x603141b0901030f020f0409150b1302070503190c140f06070f0203070224070309090f020a0f0f030906020a02160609060c06113f0103031b0311010c0207 67
    0x1080c8407850982465810707a0780c008402081d0040300e80074003480f8520100059040b55a9418803030214043c404540484c1d541d03550089400c105500034443c084030502c00c00e810700d600610581000401c00b0056032111600280c4250700c00302003110454100d03e00184c042c10740c106401581e000081d02052400c01240ca0364201e460548444404035940c2c0c400d03070810300c0103800a01010700145030442740920781040582c00501c140302100315405ea00d0380024030803000f14180c2042003001d09224041c40c00300008009085040c20380030480034114016800408080102e81d4020200e4680a540050311054000c9011074032445001c20282d40c2d2031000403a0f01500080300400280c1501c92610181520a1962500914550740d581d40300942280f0000300c80049050042410f401c540c2408904c40040011603c0c0014010104201182c0c0c9a250400d0100d0980001440420381000c3c1080c1c0e204019908404440342d00d0508540d0441d98030955a800c0d4208440c0f84941c5900040400546190703540 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 937747428 1250 937746178 937746223
    0x906120906010807260c15040513020405061614030a0804111212131503050618100506391e060604020903120f180405070c15060314 58
    0x400ca64421951040d14020325901202001407403000407185e1502d81c1036130440f44401404400590f44c0700e0f5410754065402c03000710f02000b00b8030304102d1030340c40024500011803400d800d10020134503a00c542054030001e13481c03c004140410403002c1041c20600c4100f4240da40b20850030200500b42034003514143c0d41040401d804485501e0207510740072548a2110007801e03048084648020b0350341181c1828079080c0741083e00012420f4814080c2003244445a80000f2140b412408000078081c0c6e070341050046280c0300d400c12243c0d84842540c0c1083d00c4d41214520307281e0b56081c244c4a0050308154000076100400f075001440ca500c0e8843c210005000c0c44180c6545407500e40d141d141d504458000c0e185c150b402680803c005041c50b90042c10000009020b440c0703c40404985035506a0183d80349209000c80003401d051011303441d00d01001d041030110307401d102508140354010808602400f0180111141c0001c114040d4910740c0400025030380203001d108840303425045107440f55000011208845050301 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 937748678 1250 937747428 937747439
    0x120c210909010b12150a0801140702070f030308070e06040b0a020601080d180510050c0601060906032304150b1c050f0a0302061906050d0f060c02011a0f06090612090601 74
    0x81c1600c8000c000c4c42007240c0d041c1c0e50031940c42d2048030030402c02e54000c07090681c0465141001e018030000d880c0719040c0b0342001c0c10142c1000b17140c989607a110540d014122041400043e0340a2411a00140c00e07107001040c6408201c00500039202d42d5001b02c20b00400041e404401e15000310b1100c1c1240e18500c151286241d01ca2801d4070f20400c0e070024900100c05110302402985018041c0d00010842850001c0c142038000c941a454624213811190100d00084020880c0d6135043c050844809406008440010140301c1c40603030401c4054001448001c1342102d4001e83c6107240e2181c0300c4d50000030021a0388030741c0480c0140f415551000300740c0d090b0040e003c100c4546000081c8220030164141c0c002d00032a5225141100d0560b26100d41034402c640756507000886940303101401ca5403c0c051138203030319041d5451134000d0840305110702c0402564103144100302c0a035020090000049002d4030900540c201c60b00014049208840c21359601440104241518074094030299100d08441002c0314416604c40c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 937749928 1250 937748678 937748699
    0x180306100503120d0f1503120519050304060b100e150c19050c1503330613120b180309150c0a020a08030c0c010908120c21090901 57
    0x14055207405902560f4070f00d00c80b05520000349202070a4450010b4082c1d80494010151107600442006119034180c0c14024880100e10b507410b00341007400d0091904409042034010b1090f20780322801807000100001d01800410341080f40680c8005141c05650514002c1c042c1001204da6950b0b4010f1102e28141c820801c070400440c0c0103160700c0c0004100b0103001d0217035403111060b241c20885942c043d180410788542c03610307031001d52001e843d0030903540c40345015110169661100c2104110403010034000503004115010107100c1d090342960070390368404d266000e50425900603800242542d4060020340c05000c103591005004d2031401c1c6650b403000762000503041d0303039001d650b10a030b43c8000820444000340c100e040003807030451058825102c0904294000842d400700541c00f006c2c2c3ca400c0010808510304003845240840b61003424543c3c0f8480c2400d130400e6480740001541c6104086c002110404407004107c9120500400c1c414540002a10314000a5a402600c00d00703000d01043c900101e00b580c40b1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 937751178 1250 937749928 937749961
    0x13110a12060b0d0902180405060103060b030c0108010303050a0c08041e050d0c120c05060c0a02100c15151503020901080a060303051e090d0f050609121815180306 71
    0x180882c0b42441c00c01401c840080130514000c030391041440440306145840c039030019100341c0c01034000d002c8540c90f600340b12007a1031468942a02ca170300f0031200440180c3c0c1203140541580c0d05072600d1a01d0340180b00e02070f1108003ca40c00a816200301150010f401d0000203410390b03010322660720185078240e81c0c0051020320780741c280000700800302015051100603228050010a240281201e894036941c0341c0c08105654841614150141c10401c0f06a0560400b402d50300031842c03140c54030a0440541c2e484680282c0c5a03196484001c84d113500550302c17113444202d40d85028010340e86101d101c1012009003c1c0095100690290102d182c00d0002165504c6a104d114110380c2c0584502e4506601c88100b071620000008014060301030602001140e500c03600b038012401d80c496545864418001d0070200d1a10b2001442000c4650104c502d140000c40400150340c10503072a810005108140380f000201000c1c122551681041000316010802104103840c1c50394414094042d56915200c151021368000e11 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 937752428 1250 937751178 937751189
    0x1401090302030d0f020405040f090b010b09062a070b1902060106090303030c03091707230c01080403090e070f030506042009030c13050106080108060402031b13110a1206 74
    0x70500410701443c40310f801035548145400c100500d01502c2c0d030001812640305505400d1400e5417590341c103081100503120140508207140440d8200352901c0000703001c0e8800c0c0030301500d230008000d10341440011045c1d00d09035204000d0003a10b0400c3d480c0c94110000d9040013240e0000782000a0840740c60340c0c00070a5180c10784a0a580b0b100d1003c1c1591810340203054501c8001c4101580c45401c0ca01150b582c20f10703001c0b40035125841c00e59540300303410082c107018581181c40034070740394a944800300a0400980d42950fa1400e090890407566903080035581104a9440002130901d0300040140741c1c1e41c002400341039103115483c01c1019448190a001c00c03507400104032401c840c0c480f04940f5024010348080c0411410040031941c0c0c1c2189080820f5240d075a500d8641e6026072200010f05c00d03e07800032240c1d8090500d0800400300e501d00b54001079668443c407019811609841541c1b05083c2d12045804012040c1c140d5080c40442041020164654042d011700d800040017441a00201c03c41e6010722802c0350b2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 937753678 1250 937752428 937752433
    0x150301240c0f03080939030111091909050a05041a07080606030a020412050d08090316150b0619181d0a090c03030801090606090e07030e03091c1401090302 68
    0xc03d540941d110f80c409020a4554410114508030310024044200c2401d680b42d2198104a0303180030000c11322103245040940302c0d07410858403062045900c0195000108202c03040740d18041040c82c1c80516a1603a003080100d241040108103060302907400550190b441850010b119004a9030034455940c0d06540403c0000c8c5158041402490b1000186411101c1c9000c0185801e81d01c081c000d0b48180c1c0c0420440c0da503000b1600c610801604820080c1c1e00c42041c0d000741d8a068621f03100c0480f43c55040c6002800d01c00840003055000071907500988081a0240409554181c50100c0c200103182d0354107000d002455940349100c00e242c4191544040700e4400c6403021007652181c0c8642018580107103035488803950f4841c0c000104510004000c011400b135103407488954144201c00c0c0543d00c00360041414020b4410040008042414815a220796203103030001d20b58003000116419842140009644034405a180c01101003a4100044006100e80030f40d2206e41c40e0503040500342c80d41e001c0d0150243c2c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 937754928 1250 937753678 937753703
    0x3030a0c0e0d030516031119020315061003091104060611011d0d1b0b010f0f090204060509060702040b041e0506030f0a021905130f0510140609150301240c 68
    0x7540e800000f00246c82802c0030940801f114203581d1420402d1007842c4611142c03513000c4029401c041c42000511401881424421304c0c0040200c2c007013003410800c1000301a40c1c0c01030b100500c500c0e0751100300344c100d00900500800b0317982c090041c046202460090103e51800900d00c14040003111f6040c0004030000c00307800d84084242d401d84e025047c0305011030551190088940014014000c8107029084501080c0c4203542000101a003280050700401c020724030404c014000c0307a411000b503c103a58001c582c40b41d5109054401314020f40a9480d825400900f1b1001a2074010114a00180f4404404070100059034926003019915a052901415550061290030015080c2424030014a0780e001c2e0f80010340719595004200e10300000c1c000044559694001d2544400c0580103040d0410034815a043d14581016124990303c40c4103c5010f21401002980009076160b04609414658800702038980380c0d1307910500500709841c0075003c4662a0003805c1040c00b0507004901947e49030390006041013a0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 937756178 1250 937754928 937754947
    0x3011b091211060406050c0d091d0406020c0604060204090c05120c0c03041d07110309010f0f030e3f0a12020708031f0f0e0a09020d0503030a0c0e0d0305 67
    0x45840844066031059103510803070b03502d51a03510003003008101c16a581580c46d254007894500f01003403030704100104070740350400b04166801001c0940c00c50801101e14200c0da1034500d001c200070f100f218481d00c000c0c020b140400c4244100365000d84111440c1d880b0a10450b401004121100e02c603080c8040d1a2002200100c4c01403081c10000e091001c0682d000c8134585626415002141500d0300305009041c1041801c00c10603035800508031141034480030043d402c0c009690000f82a5218400c008010000d070388660031030f0319110340c110000d480400d50983d261a10104811544c810a400c650300d03c0c0708180c2c444500701d0b03c80035a0984a81d114414803414011a04400c85600c8400018481c00360340902426011030034400096006241403c0c40c3e41900007002c5115003000311981c040c4044200c003034020080d0000324082c160380812002000240c2e401140b00151742400b0f440300c0581a4400403003048800700040d40f1110701080b80740c9401300c0d2801c540080000300204810018006501400b09501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 937757428 1250 937756178 937756199
    0x15090f020a023016022d01180b041d060306010302010912030e0a0b0309010606081603090c08070b0c120406051602180a0c0813050705280b070203011b09 67
    0x140703012485002c1c0d0fa80d60035600150b02500001d03e81449281202420801c502d0500342503030701c041100907002001b1001d9000c8076003000d0345d0007529043c010640c01c110b1a014071504140c0250440502c02601c0b55151038225074651164010f00c0c81c091410008100701d850700040003412650305940701c204040c1130030750070350b80401864802c40a1080c0b242402c0c0c3c060303644d5103d000160070f04898464491600c1000a800e650403540b1400610404400380304a0001c07240c443c0f2412062402c022464281d44e1406540d40c0302c25510400803800782d0400800c86210f0b40c0010481310034401c04450210380315900c200e1051240780f03e0a00422800c000d64104c02d01e400318081c0c1d142d80000e2400d034882e0056100d04c0400002102c0e041211a5280e12040c4081d0b0443c00c010b800081e00740202056460641c5d41e203503540f85900917144a230b022180954000c0320710303030505a404803a032000d000768190b036480285080d4000a100304d109508120620144038655260003c0903031080d81d03400d401900e429207114 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 937758678 1250 937757428 937757473
    0x3060606031b27030c1509150706020307090f0b130e06042415050c210d06090915020a08060f06070c030503070b0c0307090b180415090f020a02 63
    0x141250341c01e0209004643c10b9005070300c84040c003200034050b03000c00c800c101030501680e10005841030440b0790780407920b00c1035002034034000c207425107908034040c190940940d45809102002082c00d0f000208124505500ca101401242e1400e00707101450380d03c5000d2041180a0b01e00304035241c20a01c0401c0050306a10700340c0c42d070040e601500020758420207132000c420078041805514041086070390108114940031091442100310f40c07a00740e0420044450450302d403808042c001c032401302903244001015903444100c4940c03950030842001025540c0804d000603052030641a600c0420744900000c00e00414001c0300d582026540d5031000e00e40d10b100401c070b403c11a140c0215002041400900d0000b0341105100c0c000d18020001141c48144a14010f8030600c2e00414001b000c0c10f05000b8007503c140c03c1124042580d450082d41511a00c0084d9010b40c02e0040b00510b5501031304000c0c0703910200c20380510007010f5440101c401d0200355899050901030340305507940c640c01603210320407800d80c1c803008103248e4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 937759928 1250 937758678 937758721
    0x70204020a0e060d09150204050a170102121609090908070212031c0b09100f12060209101706010207050a0e04140d0203180904110402031005100f08060306060603 71
    0x10403900b401d580104045411440101c0300c025510f240003028450200b1600034240402c0e0410b604c0c0a0403e804a651a0307030720703c00d80c1c0442030703004da0b080c1c00c096081d015104c801040d113580d4401440d000e030550b4004410740c2e0740000450b90b080000705118902e0301425140c1030b0089030241c43d20010350b09001e0003890600302107205000a04c03800c1c6a22045407003a010320b140d40703100440c010348508104840c019003d0f00d09429400e0724801041103894607085681141e160851020324581c03542401006803103160101a4000b00b0140381900554000100001c800c0c010700b8501410754460b00160380d2100035003e9a41c0c8114841810803200c00f0380361005510510030700c60600e030104050f111901d8400d40c9000880035801c0882d10000a11400d084818040021500101c8508190716020390700e0b0001007031a40201e0700080000c0c400001d200b100740050030701030700c1c0e00000c980041d0f00820505d82402c1700c0f0300240d440c1e0003262040c50005100c40c02820700070409491030b1100005143e000340070002c00e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 937761178 1250 937759928 937759937
    0x50301030b060a1a0a020c0a030b0c031f0e0a2f1c15080f211b15010911030405070b070201091703030f01091a100c05240c040308070204020a 62
    0x460340381c0c009582d13085a240d00105880d01c4100001002c0c1c02d1140e41c4440c07500404190800300b010401b000c044c01c2e0050554a4520780d69204d541100c0240406c0e103007070841e11415100c000401081c580d07901c600c1103181e5101004441004a0680c0d11000140b049903d0980080b1204103003198034401090444054030032a00301402100040007502c0f500c4011904200b020401044021424040e04036051350000c042d0140300084011070151030140c50b4058130030728010807a607414101780e501406100902404507140010b200783c0062149000f4012400c0b018180804441c040003200e094a00450b4040c010741649418a00c0d01440798100b00802d904000b0915000a164580110b092081d03262540282d0f40d2464016883e812211041c0d200601c6903180100e40d42c110340108030b80d01c688010032540c80107200164a011a25040c4014029000f13004a82198517a80c49006071a0451108000700ca41c142c4c1c2d6001105015004512018002600c20480c10006103410350082c000d01805080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 937762428 1250 937761178 937761199
    0x30902030d0e18010f0f1a04060f0903020d06060f1a04050402161209080d080105011b0303110406080a1401031716060501061d030606060f0309010e0d0f0306060f050301030b06 77
    0xf0301c24a961001ea000c050441030300070b424800000200e11040150400402c44000c0c0d541490014185210340e00c1010200690440c40c81c6040344074048040043d0b070000d040290300d441c1401e02000402e801c1c41404c0c030950300e0560004035810946088000b13086c1c4020301c6818146004144000795000010702a2265540d600040000d210b40228491109440c0c0d5040980e90411840a140c0aa00b141c0501230240b400010081c5030303402030310201c002e044055040c0b008441890254050114580c699080e48008100802c00540c02a510741c400e8403082400d202c6e6483c0e81411441c0198280400307400c002030840c0f81401d0380c0405008010101000011503944e207010317100d0000b01c80080e00018005203891000342d14419056903a0000e40000b140a0b08007820004006031480c8958600030820440200004a0404080d071100c10144801410b0328070321105030000405102c50a44d041011070325040300480d11a2188000c03890340044e030740742c9a1135a400d40d222280d83e0240100701d958004038078003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 937763678 1250 937762428 937762459
    0xe0d0f081909050f1b0a09090218090c0310050c04170f07150e0306010501082418060108011e03030302071113020409060b0705030d230903120106030902030d0e 70
    0x42840b0059003e40082d001507448103513014104a42014049292101c2460300ca90a03920b010f40380049580201c0c0000d502c0861b8404140f0580b85040c112146404140420840040204145180d21411401e8910a0b034a103201c00003260380983d6510081d44040c0000d01c48110031186401492511808903001416140c0806140c010b264100320f0210955407040c9505c42e03000043c5081008045025050f2581030100003045403070300404070014549a1041d0780c42070300c111791031840604405407004c8400e49040200521180003541c01078006042e01c0b00006040661105600385c51700d0402d00071110301e1a40d2400c42c06500440720540d070b40c1a89420091840c2e4810045881d0300302444005601d81d440c100c026030440c0d20a0348102d0100f02c0c01c00c11000002d41c040104c1350421001e64001489904100500042c00903650081170b80300018010f100c40c0c4034001020749607a40c0c211a03100b2041ea2103410032420303500c070890001e40540c8000124079041d40100360013000d145026004440000002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 937764928 1250 937763678 937763681
    0x415050402120a05030a0801060f0f1b0f06020309060705070302070b09061b07080f0a050a23030f131202030604060507180306090b010902040501050f090d02060c100e0d0f0819 77
    0x6008450503400059071403142d64001303031f28500601240c18082500e00c004d1102401034012030310b00c00100305404260f00e01c3c003407202d20780900090300011303005020499403900714020341c401e50390901d00d072044030005031141c1e200707504803840254554007a0058030301c2d000d25039043d604185062540800e003481441c13580c8103a62440350800c000b4030028082c440c076003401c55003056102c14011086410034801d490106100251025010340d20138071a10041c41001840814012803038200401030200180e2004140064000f800d403030344c0b121190b018078a03600d2101c010704c004840300c0250103400c104009404203250394040f5034400f0460501e0040403240c600400b030b03a00c3d0503400884400d980c440c42481407245121959016200c0d1500440c6070605240c0041c1407401b030300c0210064401d0020740943c8686515001c1c244940e1b001e0003c94440010b5260141c40350180f50707018a01d546444200071591400251a0131001950384424820035a55503048a9240000b0500384e280b4000c0c4a030722045070191b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 937766178 1250 937764928 937764943
    0x130c03030e150a02061009110a08090a0804060c03030b09010617091501120b150901150306050a09020705010c020c1c05010e0607030e120a09060c03020118050321041505040212 77
    0x2039400740c0170918002c1d0628032555500d402401c010341c90082040e82000388030007126031031182410188038655400b03549a02d00300703003000000d00840d00400c0008040d038121210103806442900c061194140b10310a22400f00f00910480000951503000030003c82c0c45000066004008007003544d840900181c61000382c2c99080e0f10404103c14424051003e00c80c49501068108910610040b020b210360f5000801001d8103000b200580d0f40160b001440c0d8a000b0307803142d170040038060901c0c0d0701241c0e9031718188002e4108000a84165081c0a114001c4a03c0420a80081040104044901c000d0b0010190b841101104112455942c900800940040402006110310095030300400c01010410340d81d4140680740c040c0c0d520b030302c006000f074108680e0411400c206403446440c020f40d000300517040480c05414442860651514422210380c2404030101c02001e19821000c0080e06c051113001e03a003403c0103000c80380500040081203603043c03c03c1c2c860b001a40c006000a005c0e180e90240c0c1202e15080c00c07031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 937767428 1250 937766178 937766197
    0x60103020c120322380106020a11010206101404090b0901020901030e1507180e070e090105030718020304020102240402090601090e04150f0f0f05130c03030e15 70
    0x101004100e5000e54038150301280346480d261124150b40c281d45e803140361380030000b689410b411071981560350140c02c411240a150071140e61162140d65078500194440010351000d541c80c85184c105889070b540001900c6010307030081d80b09100414070385031026001d12002400303240c0c42a107580451020405616402d4000d0001000041c4c0c0e82d10f0380400036048a11401c0c480250350000b00c9060302641c1c0101a055114000742042e40076810390414003501d400c0300f03402942c0030345018000c3c004c00c1c7e40d0110300e510300c04c0b5040d1a82c44160340c0f140304140c0e986030a40306404501c20ba0fa540241d034140150095130b082441801200c22114003103c2000d20a52522048039004404504000c250b24026180980008007800c1070f801c600d0a1080c2540089001000030f0003000b11401d84c84d00145103944504011240054200300010600100700054588d420544c81401d08080112b010120841c0c442411994048c5d07240f20404d10350b9400755500c58406203021b07032252000940c40400144a80203140560 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 937768678 1250 937767428 937767463
    0x7120e0106090b1918020c1603050c031614062d12070f17100e010b1b2b09091506110c0604120c051002060f01210b060103020c 56
    0x90140f00348100342d980d10141d11aa135442e502c0401000003416401000d07592882005a41c540040000b81d1810b9016407510751040d94089000003800004114980340c1d0394120240c800321b00381a00c4022841c0403900882c000540741c80c0c43c090283c0741500c0200318001010f040f800f0b1b01024800c040c3c501d01c5204138030500e0340700000f580107a1050204007a0350300c822903080804008a50740e07001801c28403130302c060900d00d800a80201e030b860b207000d100d094003c05d502d201c00b4001e0768642902c8551900000551070a001c1d1008040b0700c02c007000300e004008030810070061001d040211461401c00010841000203100300c9503804607541149000d01141d1004100c8950780d11031070650014403803284200383c50b1464212000c125406d5a030041140d08407041c030301405680252505007566480c80b90791000341e01c00700340920a4102e40c0c02265203441030480303c013074000700ea903540c0b58058041c070864100407500a0b0710b050600020b40c0041200d40014040c50010701300070a01003d28580031508c0c26445581 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 937769784 1106 937768678 937768691
    0x507210203040b36010c18031203020717070503070c08010b0a150e1801030b06012d05040b07030e03012d05090c060406031a0d050607120e010609 64
    0x22541c4640d40000c41d60014554001c0001d4a2654046441c0d022030b03e04515007000307c4812240c11408810480c440d0400403802940101360856012008610890801e031581c4007500c0a1403040000310360707030032050a218a11980507848200305a040251036250340c0c41b240180743c11610001c4138420840c440c08010f803511020403000641010300181c4880b07404008a014604036801021015090b44a90740111285860262883c04982d810046020407100000088c1c94020301880d00382e0400b500c2d900c01d498190320a45043d0005001268540301615084c8610008080e030481c04448142c402201101180ea48104090070075640e240040c80304d4105000c011607050005081c0303540c4940302e290180080c241c600c1b003014078100400b65034540e4202001d90840141d004030040203e070352050b00480f4024425002c1940c41900c40f190202e060809002e8480502624072000ca4078 = true := by decide +kernel

theorem cover : BRFrame.Cov 937589928 937769784 := by
  have h0 := BRFrame.cov_init 937589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 937589928 ≤ n) (h2 : n < 937769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
