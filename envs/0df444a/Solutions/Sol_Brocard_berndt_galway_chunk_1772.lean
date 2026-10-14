-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1772
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:37:17.141315+00:00
-- url     : https://prove2.me/submissions/38ae2708-c9f3-4088-a931-13ec24007078

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 318525179 ≤ n < 318705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 318526429 1250 318525179 318525223
    0x1021050615061c06090e0322060e1504150809011b140913090b07020d050c1207030c02090901230118021e0d060306060902030f06040c020f19120908 65
    0x110006104c1a4810500f45090825021074110084020070404400301d52140c10803a803c24442d83c040001c5c02500b0114481c0000c840192400903c040c003010000c00983d4034141e02d80011210040140c49201c4c0820f4040e03040c040f818000b8010003d00c2080c40705d0060005684e500000c08038120042144605a40020044480d03214180c0c00250f1741c0d01001c00340183d003003d00d052240c2c07040860702c84005002d2601c500900304d22682c211000088803038020000304400a00031721159002c104200e05020385a221040140c40740b0b40914441c58100300001480c291124130307403540010307540c0d00c0e800b010075010050084c07044540d202405048403c1005840f040010b220541d401c0c602c1404c41072100010444044504141d0000c4095174402e000c24400340b503035044503400341d00050f0f6070180c1c100007120000c5c0c0300b4103141c0d0080c41c40da012841101d9004100d20f9141d400c0c240011a032280c3c4d8407486003800103011030f4642840118040c0d181100016142c400303402d880b0f01c8401031051100d12015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 318527679 1250 318526429 318526477
    0x507020106050306162709021312140f0307030206010918050303090318040204050607020d0201030b040c050d1d070e04081207080a0b01051809102105061506 69
    0x507000002401e0040d08849041c2049022011181c03241100707000002d040d0001800c51312030038010b803e4003041e440700c0c104840c1d003021300c4c1e01c0c0603400c4a400a44030b0911648000341c070004500c40c400049000f540d07103014512000f85c41905202d22442d102449a104100c04c00c0044d42c006030807411034144100004031401e880c0580d2615032000d500103031140c0b001000f4400d01003400300c002d041c584802c100f145041c943c90320511040e80a14881c1541c81032050061101508060a10400f9207105250014401d030708003000800b12906147c2e038400090021030341105804a520505840c42460152038800c218074803501ca81e10a81030084641001c40c000c040b0302000500000e86101600d43c680090441c644864020240c4c041280c40701e00c06803d140785001c040d40200100c4420724200fa858200c1c6068440038006c10301c5c000751030240c14880e19000003400c1d00c11407810007980d01c44219850710008079803c059142c00c401a00411080461002d640384564034041200c40346202000121001d41c501 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 318528929 1250 318527679 318527681
    0xa05130e0705040e060f100302130f0608161a070803070f0e06041d1e0105040e03040504020705070f1707031101050c060103120f0816140c1615030c020606010305070201 74
    0x20350225400605042c08113085000118490348201042080c1c0c451503030f2030316080d100e5010039110107500080039195140300241c05400c42014809099400700b01c02c0ea0b6611164600b10544c2080800340f409035805001100002d07510000b9aa8001d100303e040c0703a069140c0c003029110141ca0301003880112443c070341d031140c003c001405030036100078282a191550b82c4141101900e059084d81d1035040020002500038004500c00b001d120740580b404000c9a007428180401040c02c03c0780426640b1041c0b00006842da039a00091610510503405000040d00c0c26500b07210800d02c94005034103041c2500003403140c404001030914220780d00603940d04103116140d001a1110310a444250489008810010052000c84400c03030f000c0341c81075901c00d441c3c03420850041300c0905e01a00c030031610250a24400e00e00c60f00c1590304911b080c0104d4002131802505141003403070308510f01e03c50204001c0845081046199000e1403c01d140c04906051285080d0600000c5d120300c0028407045c14169941c0204400b140300b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 318530179 1250 318528929 318528943
    0x812040215070501020304110118030b0c0403080408010b01260a0b06040902030711121e070311030301090608070b09010f080a0b040c120510050303070f1a16020c0a05130e 75
    0x4800764155942100d410081d01075801103d003503483c138201c4012800103500c9100b58060107100220703400c0000d41503644503e05400b01900d020740d00d07041031101002042480c0c00403c01032442d800001403000603c0009003490308800984c100364288102009610545504801d03403140d40c8ca08001407200e656400030b40d40f80102d0f04411032302d40c804000c100c0302d00d82100714030a800b0800c2e021941814034900c9441040d1041c5400c41004112200d00f10150074916006018068880e00305080040c19188031f140c9035810036030140d600039231200c1041101204c20302c94400501404c0e0103051500b01541d002821103132115000e4000c0111100c00144c445016500040744a10010418080b140c1100c10041c240400552101181403810f4003054503060102020301c21503001030301550030014a510b41e546000b0402005465803566085808481c0e940d100c0c07001d01c601c040000c0c080019588101c02485c02c06248006070042d4170301e0105000c183d480c0440d800924014034004070741154492030f03460410071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 318531429 1250 318530179 318530209
    0x30c09010e0a06150e010207050f060f0702280e0703020f0a0818010507050409060f03030905060c03070506011d100e0c071b060e12010504150c02241602070308120402 73
    0x102460b144c41d80c45115118109401d0b82240c07102030b00d55040010300703100404d005510041c10480b092a0207000700c042d2400c01d0000b0322000304c20f458144081500381e0104d0812040c0074a000042c0000280ca51100c1d40241c0307103150440c208100744e0f620581c94031401c04040c0601212400148500591220245100c54008001e0141e820007440150007030f040340c0200c001e0941001c1c000325604201c0440c1d401180d400d603032841c02c4180b40c0002d1214a030700a81814030240401c20464021480800400e0300a02203480c031049040c070b400140300b0300da990107000003036200d420850411020003000c4440f90001810319250751307124082c0c0750405010810182d11791840110042c0014050b41114034030300c951500382c0e42030b42800003000020742212030840300140071800b454807a20301d014590348194241031249c01169a011203d05000844815401c03003c01482e1f0103000700070103401403585108020b1800d000030220181540e48440040c0200d21a07075450159140015044d95103c0450282c01c1e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 318532679 1250 318531429 318531449
    0xc0311060918060307050f130c09150207090e010b01020c1917030406030e03070507061b15090309060c020319050c060c010b010813020f0409030525020906030c09010e0a06 75
    0x541c41046102e1000c4120780d064804e01034144c0000340e5017000f1807040083c48004142c1c1c4400041c9518001c010500d082c038440400010100c00306440102c50218107003041039800400e000343c07500b114241901c904080c080f00c1c59042c01403500036643c000610380b800000485000302d0f4081e0301d82188403960240c1e8040c05c3c400c2d80785040b0140c443d40c088014020358207a03617000c1c045002d03003480c0140c2d82d01c2042402400d5500140d01005280c0c40b03960450107410000d050403000e2103c03600d90f40c0031a400d1040c841101c5540b10030542c20142c2103c01c07207006000c1c03810b1007100c450140d00000d440f80c2460f480c0006100c0015400000c20100340840c0c04018401070489803200c00c0485024003d010402d06580031513030341d5000c0b030b14810038010b004401d181d009141c01108000c040c140405491548001c8082c420180480300081010106805002d80c07280c020f070145203098010400c0720180604014080d400c00b03203440c0d120b0740340c0d00c420a06440040d02c1800f16912050401c3c00140b00304d0340601121 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 318533929 1250 318532679 318532699
    0x2b0303110c070905010806180709051e090607030b0a0810110408070e0115032717030a02070218010e0601110a080a0512090601050319020301090f08091c0c03110609 72
    0xf442d0b441a4141c0e050513045501b165241d4108160707201e14090a50019070216104100440d4107800682c3c0c400010910500c0c40751642c0d004010885060b41d21000f550031810030066200e9261180041c140001c866001101e49030041407512041410b0201040e15124000c4a585141481c1105e0085ca2020202c0d40100c1d85d8400364005410203009007444281c08c420108026032090040440c0d5408015515103043e41c074408007240040c111100b128804010320103181f00e049031100bc1c43c440d03003240c03a0250713403600e0a2041000311040f0030414080090705d48010300040d410441a51350060080c01d055800d040e10b88282480d24071841001840c404001400c448910380c0100a09800305400c8041c40c2070744c4030865929210507090161a0b01076020240306a8440c55054502c00e055002400004219801e6141c0342200050f00d101590704a000188098981c00e201000607442c151030b5401001b4504035994401140341c0c04d20005d4111451542d1102c00c0d81c0d560421200d500c07400400388060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 318535179 1250 318533929 318533939
    0x501020d1d0f060c0607230307090e090f0607020106060e010c050c011b210f031b230309030405090105030a11090411091503061303050708180a0f052b0303110c07 71
    0xc1d0020342c00c0c00d452044d4120311100c4180045d11f00b030340d000c5c009544a040d0364070b04001381e0303400700800181100b41c1380c401d05c00300d003191080a1004500680c119400890800e040c4180901040300f50746400341040348201c904c1d070100f000803a50074442042480d00320030300004041041c4081c6102e400c0a4041c61003807203002880141c4481900f100c00329030706c40b1050210102c1c0141d040320705100c50031440010324154018250711440c582400048902500000340759400c188400e941c0007214941c0c01c56100090601043c98840320881c0141000c03001861804207e5403580050b0b9000c0311a14020360100000c14100308041e01c103882c80d4071001c0d02200c224603107090705010051107106900e00a0203444040303080c103010042d6410380544c1548840f4504a41c907502c0000325444402030804d190340303849880c4000d588500e4088010040c0c0d003080c0304024281010000044115040c0075079034032018000c520701a0407000d07c1d45c8000d0700f6040000e4041d184802668051280d021003c400c0e008411000c54 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 318536429 1250 318535179 318535187
    0x10c02060c0c04060f0501020a020f01050412030203070c08010c0f1d0418020405090f0c1309080f070b010b0703091203030603020a080a031403130b090c03060f010501020d1d0f060c0607 81
    0x28002c404803000c0c84019990b805114a001c8a4042d460040e041441c2c0300c0702604088014460195041c50714034034003a5110b208402d50300d0300140c201c0c01604001042c00910045864100c09014480e00030031044000d20009031410020b40d03040c200788158401145460311040c191400c2c0048003078400e1007055803610400008841d00c4500728800c520f40004110801d40c0021140411410140227085011640c400c010f9039a803210501c1e03c4090701c84518400194040016100200c13003100055140d41c0c1c107240c100314060050f0402414403406003c0000407d078012841400c40e02d004c202c6111100725800d003100648110340020b07401542c403113000690380b000004e5000c0034600075a07030148080300300120005e60b84000d40d240d00710098524440400304440c281090f4000c40030000700d0b00040511000b1034144201203032004000d01054004114a507014082640c89e03089524003030612103407510300e011041d01c100744207a01a00401d6060360003502d54504030b50300c07102184103e0304180b60000c0e00030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 318537679 1250 318536429 318536443
    0x602040e07020d020703080306040207050712230c0117090118030509040f09020d061503050105130c060e13020f0403050106090b030c060c060712020f030f01081c051602010c02060c 79
    0x81c0040c81019000307500b45102040c0e010580f64480080c034916100c00c400c12019411041058400d40a5030100141801d1ba02002081e40791046088a8010016031a500364040095104011641000c0b00b0749809071781c04a66203504082541d00c07000544c4a4444180c014042d134014614003100c00e148010515810202415100004603014864010b0b0f0391928015141c21030b06c025003004243c2005030000d400b03500700404100100c8030030202c05a50740c850700e094030816201010200ca0405901c0180640c0789042d0010309043e007007a4045070300003c0451061945040304800150340800d141c090500704e9421100190b800c40001d204442c0ca5000c088014000f1400c01c6100e482a10088022802c0071420345903a680280007405c3d03285c3d50584103540900169000d401c4160f801c11451101d40034003409540600d44420101c1145d60401410310300c0d101920206c00090031940d0a51805075a0000485403c080e1174051070000324014030040c0c603480e448800c0207621502c0403410420746c0000103012 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 318538929 1250 318537679 318537691
    0x10c090302130212010504110702060403030509040609050610110c03100609050601030b0d0f060b0d210315050f03100914010c05090d081809010603090201030b0f090f0a02070602040e 80
    0x40500c00240b00050708a1142c40510303010030b00104010000c41c03030300e03a00010203140101005440c12606500080981e88190000c4000c1070003c44c20700c216041500c81da4014050502c0704002c0350a00b0350005194561222002042003026280d0040c085410b0203c010044030107000c4504c54650001c2c903502400f4103000c0c0184051074103001421640c42406072995028025088482d400c070a51540e009000399041d003911040e4807440161890f4903100350040035180118124240c14100401c01c55102c0f080e600b0b46000c00d410140980300180e07615854408503442140c19401054141c4040303814000108404540d040c50032414109110121076070003050800390f0001c01400403c600140d4150042e411990307088045190b5080c0002c03a010020f000d04011014904c07421a002c100281910307a003600300400290f11903042c0411541c241c052100302941c111110081d44030704101140c080d200c000c0c03134040c0455908000c2081c0c032810381e0445a840d600120203651b20740d115410740070104000e64031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 318540179 1250 318538929 318538939
    0x90606210712201624020c0105070801060e04020706090204020705010b011808150a02130308091305010e060409080d1803111605040e010f060f0e0105031b090406020705010c090302 79
    0xc18a0008030362940f8000d40d100c440406003040c460581210011805607001c541c680e1103103c118001084e1301e503102400c0074a407003000d640c5000c1e00b110f150035100080d203d0000d001040006022160b00806035a0b010101034078010b88070405030900d04082c11040740c01a42040c800103c031020301c801904001c1c0b21060a8849084800740282400e486041c203108034007003504001070800100141122054000346400d501504040300034032040d85401e280c0d40704462206c000070740c5101c40d0502920040d0010020903040003190703d8007464009107040181254441c560724000c482c104200321054540c02c0780c1158040001c0c0740381d09044844c3d1002c42c0e40c00d40c086030b8030217090701042c44002103181218035034407020304080e0b2a01e802d00003c1c1914540940040d500d0b0201d0306171000040c1f1410004150003070b0501c80e620b08d40300075510080e0301a00828006c0e0000008062001402446a0190101512140d07125030b10390a00d20001e0041010090555007451100d0b4030036a40300c1a48400ea90080360 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 318541429 1250 318540179 318540191
    0x1d071a0d0914150f04060f0912030e07090c09150203160507060305060409052515091401020a0c060807050d05160e0901060903110d060203090303190605090606210712 73
    0x108581c003503c0440c1c0c1c0d6103a64259100090008126410419501104690100741090325985103000c1442030304508001030760307814449035107001c04c00446004114881c0200500e02e24114001c19010250042c50321306482100101c440302d10800444040f880460f08480e006c0041d864083e407640d42030302c20280002c0c1490080350340e0386044c2c8646402c0545c030100505043c19040001250400c001540282400001000241c2003128881154101c1495130f14100110708110030b4820406142e181a07045607c601e0740d600001d85200c3c00881525018104000305544081003110796101e603003400b001c298207210500c0095940002c41c902da9060584502850320804410b01c403004009204d82000140e280b40200082414400600075008011f0100300003101c1c40d0700c03000c003aa41306440c50b40c4a64030000130480c00b002502501d0400c140c100006020342850040010580d00c006000c075031054100003190480541d501c3c07a501c40c0d0705d5103096548070a1800c040090100111030401c40c9400323007060 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 318542679 1250 318541429 318541453
    0x1b170c03041401030621020d05030c03040306050f010510080a020f07032f0303070e0f0a0303090e010b0703140c0109050a06050717040519020102030417060103061d071a0d0914 77
    0x1004400c1603682e100c006d01c0320283c10014007183c5072041a8281d030082000d0150031b0105d030040c0020910f8400c280001e542e40d5245241880440d00010121000e50b0000d4006000329034441070b52b00160819403400740a9074a40400c4000207220341900c50345128400034080c820180c20441000b0303142400c81c070580c021701e800d4220724500c002d00044c580c203c4e0820400650031601604150691f0107014080039807007009400814540307030072900190040340034890200034109128403001d01400309004c0c0f0754109070056802034080c11101a8040004102107200d20540340300b5840f80c0b07186a00002162031410702403d062009103001c0c0d41200c0003403884460f03600a29441d407101c0307000e581d101c00100041b007820458031062041010080781140410040000c1c140c80c2206800900060ba40c05030100d9455845c03d4004c8845d1101102c1540f10030849082c0401404105c003c21200a660a61042122402401245e1050000340700c0d80c5403030030320040c00340300707140614568480d02170048820410543c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 318543929 1250 318542679 318542681
    0x11d071806120f11040801051303020303061c0f031205090304030b0a050406091b050f0f030d140d02040b04091a06030a092409020108070806011b170c0304140103 71
    0x111010040145000380800401d882981c0d500a80340020b000021403c0c04025044107413800c40c080c3e101507a40c0400c0c11300c01450700703204241e000100411090102121998007a4603408014292480b0f000034a10010007103500c50780c083c0311182d00c43d405900020742894090440c096180d030191810b840e10380000e9440c0c00c0001101c0c10341c2d400059909250340c80038840c001602004200b111000c0d102d80c1c80d98001140d220f91a280d800801c0071001046082c2002c4c0301090254151251041420790291250f40e10f02080d005104040361400703200303492085d012228a88141454001c0b001d2000074001401c4001101400c06d40b12440c01c00e10440483c0d00b203034003d01e5449010143e006808102103201c82e411680840903c51088160001101484003a03000e08180042c3c0046003a03240d82c208011582c0c001c50455024400f41000303011070402c1000240383c180075099204100394441070003001d014900e100d22411441081c00700c0c2c0e131210300da8409601c2c5e8204e4428084100c00d01c40021002c1d40c06 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 318545179 1250 318543929 318543947
    0xc0906081009180c0b0a031406060d02030a0b0a06030e0c060a09170f010f1a041514060d0e07051509010f0f030f0501030b01140102060c030c07020a0e011d07 69
    0x7030120300071960700700700c400801030a8600309055030224611580340015490081c440041c81d42117000ca40352074042e50090252030701e40d481d440d0a072610200300205079454809035408080c2980c001601d95440700e82d210700401040ba4416480071601c1c00014510358581c00580e54401e91006071445a4141c0081c00001e0041e40c0a072004110b02c0c0c0010322810502075015a5811030300030480d0403000e0f2062240c1d086646507081c04083d95110034106100c01110050704001c170340103840c1008004283e00511140522a00030800c400e041503100f00c0b0703250340d4202510440754920b0010840d0054103505c03590f8403405840350a000e540380035013000041c549107054400721074041e100c0100c1008800d80131110000704038611414540d8801e00b01d40204207074410140070318440c07101000c0550411081d0402d00c40e10082c43c604551142e81000003904011098982182003502095182c1c116840000c2000b02ea40d0081c0d510348003400c00000b1484c00060000290098a03150400c95427140e003c11210882 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 318546429 1250 318545179 318545191
    0x41e0c020a081e0f0d05010f050319020108151c170301030c0510140d200903031204020a03020d05011505010f02061f0807090915060612020c0c060307030c090608 71
    0x9401c0c040692070009105010f4520400040390501c0c0981c070400782e6900350094214600816035804c010b2042120310307912100038010440081c651303800520402c0c40511500000203040043c810701062800c01907070220300c0302150003000c0d030b101480341090030390fa4103106990030340e02d07500c0780c80510040f0300481c42201d040e260404d0326614580e00b40320038044d040d100b140c8030200b04081c15400d043c0550811015081035088c0ba1404a00014103000420181101403082002c42400700051400d5541c000100c460b51494084200c400340c2e6a4000030f1080f0320309a00294001030618a80d6040160641c07003d1550100041d080c140c1907203580c01181c098000407000c80140c0e00c000080f07000c46a41010765001914260340d08524652600b28850030408542e1005020716182e46c14401008855801d108110310450402c010f42442e081d0000c0101d00015441c5050f00c0d400210b80350f800806005620950401500c5186d4034140707080c1c014020841100910001408054080790b458455007070b0340d006213 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 318547679 1250 318546429 318546443
    0x30813050d05070e090a0c060816090609090906020706020708040612020304080414040902031e010e15190207050111090f0a0501121805070f03030807050421060b041e0c020a 76
    0x284c10980c0c001c8031103101400010880c41009200f40000300307040070314809449140d4900c012030511803594003003815043d80c0c0300c05115031403c0901c81103a00c024508111918218041503014079828001c000744604400504003500014804044c000404018400c50352a50380c0d242040500408480882c0401c0c3c500400f8031b0360400080245030803203001d10366508001000001c031a00aa80028500624140404101588290801c245603420b100d04800d1105220140c520440d4103400003c001400078203130310003150300410f640303030905003981a10f08203079105008120055855012441d01e400c01c2d21094032034448013041e001142000100141152010b0f1110343c2d2082c07a509260028254200301c0341d1006030400000d501040c0b08001c050003e01c0440c3c40c0d10206d508604004080700c0c8024645020b02c80200010040c81c0301c0b0b0107030260711800181c1400043e0301c0510744000600002014154054101000e80103ca480300c0c0d00c0b190504441e0004020354114003000f80d84601414001030295 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 318548929 1250 318547679 318547693
    0xd110a080901120903030605040b060414011103190914040b010f03051503030d050a050105030706020d051b0a061a0f01080f150d0b0610140315031204030813050d05 72
    0x1641000c041c081c6008141044541451055851070880d0320150094001903215a42000709003007910451840350800c2c8e401c6490141803c021104a01c3c81149450401004580840c040704090040d41d080b003015050303200b50304504100040501016005400304040d8002d1044424a4907208030307010743c0d0040c1c4803c1c280744000b01c1c05030700400c802481040c1481070006c00401564061008110b001c0a00c44006460305041010104903001600f1a601a5103c100c007801420780010f0070700b603040c0302c07480c2c829681d80c18103825088070400405039040a114200e41001000601d40011540e03040c002034181c0202104804c11040c0316200301028003050008c0b0105820321031201e0307040d030310101250050002d240c5940102d250b541c9102000c0c0c4082c10401c09120382d9280c02050070708601d41601e0a80108090f24128503042d103c00b5200d50081c100b54624403040b6107040c0100c10343c208051000545481e964107140340c3c558881c2c20100100c0e1607030304020816240c80140c5c0da80305a00a4003d00312 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 318550179 1250 318548929 318548933
    0x80708070e04090f0c050f03120c0106030c060c050f0105130f0203010912050c0705060f090409030905090c13081207030c0f08030414100515210d0f020d110a 69
    0x94080a400308007000801c0740400880d440318021448036900c0364020852600303c80c20701c0c980300001c80d000301d485800d000e21030342580c0d5000039516074001c034000d00080d038450500c540349005203002e0b4002041c15235800c1001415a03001055030000c01e008500381c51400720a103000c54200c440880d00c80740d07541d00a91000d000b04101074102503c940c4040c000240c50106501e0b501c9092812400440001c0c03400511f21101703031010b00c10340700280000d94045060a89070b100845003402000d0400b80030b5951081c111040c5441561801c00030140500945007a043c40302d0141c50a0380b180c3c40781d044003a4006000180e00d500080c0c2001342c0700c4180310f10741c00d150071580c1c00c80300166110425140e00140b4807842000c511000c0080d40136501c40d0503801800154132041c68148950f0f2161050050318100030000070300c1001c811410705c0402141c882003e82c0440540060a0498411600b50752003120b00005000b41c1082c000c0700311082d69002c0701d41141203400126190b03000c425070745205400280f01240 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 318551429 1250 318550179 318550187
    0xb0a06050903011e020415030615080606070606031103160503030d050c0d050106050909014403030a0e01270b0a0b031c030b121e0c100207031e030807 66
    0x1001e040c01400401d58502078951541d4900f45100c41c40551580086c003008801c200f200105044000c1d41010f0003602d01c1c00e449450041d442005030000c6c02510300015440e030765980103d48507540d22802c100a550703228100342080c2c4500b02c014a00900c1501a9940c0c149030b02002c000440350300034001c40c034100340c120000003c1c14000d444401d200105000905e25280c0a014003401b0780843e580700d40d114060002040091081071f4403c40049081e40940c0001051342074014850f61082d04c078500d440030710505e60200f110000940007016002c044240140d044458003d250f0200414000303004600044030020000b48141004010b0024858240030000d208070300d11030343c00300044c034001840e4132811010a0408241e00c1818203040b00c0320f1540c403c8250035200b5810380290540c1c0c62406640000301c025911441c0e480307890342e414512294a00003440c108131900112030003920060812083c080041d43c3c90502e400203d40049808050f4440c0745540045a9a195050790340e00050ba12203450550b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 318552679 1250 318551429 318551437
    0x5042901020106030c0b0a031512170903030d0617060f07030b041e1e05060a060503060d020612090d05070312051302090903090301050c1207140702180402040c030b0a0605 75
    0x941595294a4000081400f5400920081070503040c0140d84500d0581d000b022a58000c2071b601000e00880024030030305512244020846030302801c0f0078005100301c1c100c411a401022a00c1da4184800510908091000d4000400b1102141400c1c0c822803000c50840da240c105c1100c404140b9078005002030625031284d0070040c0280740140000450b407845408031080d1503c0b070383c4038190554a4030000c90403489095020901d4142e807540411003030a1250009070503401c984950801c0040101c04902c0310340e01c0c1149105400d60041602da07859841c41416140c40000300c0d8000d40e00d0007200080041d042c05001103c0c541503250350340190b0007540c011201c000304800380507440800d1400d40003800688445001500034402000216100c80305d0204050035200028607041c405401840b03049507448a5035074007904001d00c2d0401003414224403c40d10020b00a0500281d400407901c19600c1d1803203003415805009900a031010320030201010801d405a4401d590403a8000e8034105080141d188100054 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 318553929 1250 318552679 318552761
    0xf040e1216020904140d080402090613020f070c0e0705070b0a020c010e0d110d09080a0b180d090302010905040e0a110111010501080f0c090c0412061113050a0504 71
    0x10000710242500440c212040446045582c22904040840b0702ca00401c24031200701c41501c0c00103070310700c3c213a07011070750424010b03182c580283c200b031080c41d40400460701a01e0703054020004a54559101c0e041001000c0c0d481c1c41100908405c1074003003a200c51066040758a09904072403100290341728103404000135800011100c0107550303110320291490b00140442d034110002d9a0301c558140c43e52100c1c2a0074011611191030900801680401c150080460103058182d004640c20307070302d99206081700d080c100c0b40c0184e24000b4024480b292403115001468a01568001c1c0e0b588029030392298280011100c2d55615045568058481d4070002800b01d4200d107150441850a80c4181984040c81820b581003a000011150013040c850307001c443d41000020f84058048a00031180d0800010002c3c0c58480c43c010b45054506075610981070100c0364200e07556440c0c2130b101d42c6a88141420704d0001009550150900c514051080010700b49014000d4000582055251100c0784140b207003802e010890704024 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 318555179 1250 318553929 318553957
    0x1806050304080d06180e06070207080606040c0318050d08060d0201020307140106121103010c0309080403060903050f030f060a0602071a03060d02060c1b0103060f05060a0c1707020f040e12 82
    0x40400e072135500394540c6a59119440b030206200d001d00c0d06d0b017820048000d11100071035004150402c03900b400010071903000762040d100003881801070b1f80110007400d0f090301a1208030300403425440070407000140b070f640603451655a40e1000c0d1203040c06c01c000e004855001030b0040c1c0c400c0c00a000460700c1c8081d4003142c6407120f00000b40c440d0ba55010036075000e44604090300c5112900b1218025802c0a000d00d05500d2110310781001440030954138402d0501030b50001030010750782c0701940800c0500030f1040700c0e2640303c1103054584a28020003c4a071400b8111105401000385010000d4103600000f646400e03240c4003607000d820000d070946e500c500b5030001007881ba0301c000000e00d071001580b1240001c0200c01d0111000e01102c040301c1103c0002121082d1299041620300002040845190b10003402555011661641d5a4000713007411114414003003000f0f81420021200c081007045038100610441d4401c0d24400d146207802c00c200300484000115481083d0000c880807500c2d4202c8100400e080110444 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 318556429 1250 318555179 318555191
    0x6050a2615090c0a080105041707030e04140703200409110d0f02030601090e01050f1309050601170c06040b0d05190603050318100e040e03070519031806050304080d 72
    0x8840c1c16550181c40d0100e20743c0100d8100c52490074072001090141203c50000d120500301990f824040d2107491041c80b5000101148050406108888612004c0d01c002c0c8148404100c0c1c0e100c1d450448016940c4101082c5080700f01c0d1700c46900c480194901441c201c4140e03060502e007400e5013002d088124881c1c40804810003c98900749140d21400c43e40b14861030300143c803460710f8400513060300da9941052440c44458001049650b0f40d000f4007401a000540d0300400341d162101150028150440009110340100c100100300c0f05080d505480342d148442080341c01152540007400483e20541c0142100720b442040501e543c0c00c00340d00240d4102c103500b08404046400740c20b0311011208690002c80711f90f0800104031184040c1c80c00c15121040003221040030740e000c901e002614000f0303c101039900850702c0348000da00405051058410303003078004041e5130021184000c0a201660302e008114042580310319603051042034580b113281507403d2521110b01d90b44890f11a17032401d42203000c079802c40701d40b154 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 318557679 1250 318556429 318556453
    0x151d1f06080f0601030309170c010525050a03140901082d0901020315010e0303070f02040609020a170906100e06030a20030106050616020909030906190306050a26 71
    0x6000c21030340e4071000f400712075046250040c0030603102d5015151840301e4021807840d4140c00305000210344001d0801c15035520400b02640e0740000040390b0188400c1d2900c2c803c800340000070510359401d5109039a40c090440000c1d002e0740d550b000710b80420b0b00003289500010022048141c001080800c001144414820200c0009082c074500320394a0000d0394010040c4a514001210001c0c202c07002400d040b4202c0e8080c50100e5900d005110340680410210b44084041d5211580024003070040c441e420f540d1441101c1019050f000c0781c0d03405c0c40500c9805000118040c00114055009500154044694602e01155010502e00c0035147c15418065040398400107144450104079080e00851a8001c2e031082e2800c1500715030403503220303074001c6074100040700503402141101d40c40151304a43d0080c0c01e480711150580b0354001c031251950415800201c603074003201010107902040040d950180045a11907041c815501006d00c200102840149054007101c80d903000200c005004407012100321407000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 318558929 1250 318557679 318557683
    0x90f01231212071103030304021003241d0c09030703021003020d1404050d08090607140409020c0114101203050a030902030a2f0a0501050901020f060103151d1f0608 72
    0xa641c2c150100c40000441504000d10300d040d4411441e0218061401d628254010440d08090061240e04241d9510103100e0004140c541d400da203c8080c04007040a6030329010420f43c4503801d92112010044190000b50600d90641c2c21601001406030240000610703607401d0180d0544008519014503400b401020740e100910320034060511007000c041500750a16040490900ea0701c01c850b003080104240400803552800a10381707802c0521454079448034480c0f402480ba990040d600404203a82c00066400240e240541000e1141e064940e403e5120b40c0711014100310b522070358850010805416110200440d00840c00f404c1e80c290360341030104884a580c0d00107418290ba1030f41c210380455160100100100c141c035640e146002403403050044120701c0100281c80c00700c0a104150401c0000280ca0802d82d1081c004900045200c03c225566561030746020756441c8880c42030040c4a51130081c204441c08010a001504103802d0340150200c00741c0c03200c001551440040c1001d0a0948a8200050704402 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 318560179 1250 318558929 318558943
    0xd0e12100e011a0a060c0525050109080d02061506130801060e090307030801031707022101051501171015050c010c0e21120a03151401050f030916030f02090f012312 72
    0x34130b444501c0e005080c270002500030141e5401c960728603442403080441c0960000342013030f001208251440b81d000700d010001003141c810040340041502c43d81320001a11801500310b02c080d00e07100401d00c01280d540d1140d1a07a0380c09140f0b0f0280010b00f03144010404190741c1100c6030030920303c1e40300c064505151138010510040110301c00000382201c111015020f48005e226131600440c107140c0170a500c80d04980000c19100304d580c041c042003080c0b54040307288201c4610742640240381114001a54200708003000c1c3c0680c0160010003115400c04a69401d4a80300310300b48203900c10002d1002c0310f038036401103d042201500d20000f40382d42c03260040d002d50040c440d1002c1d1003003120540c1e0201e07030000c0d0005030000411131944400302c3c0280421801400d6038004040d00c100021511141c0c1e22a81c2c0c900d4018070b8401188618000d10480e04000700600c034800500d403089500a80340440d40d0303203500a0300c881d40002407007403541503102c103681e4103100c0c0600d40225400c010300030501c418661203c2412414001c13 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 318561429 1250 318560179 318560233
    0x80c100c0804020102010c031a2209050601030c09201b010213060e04050403200c150a0f08010509181c09030b01060801080d0e12100e011a0a060c05 65
    0x1d0403000704011503909001b68450005ca500d0140681d9095003001044617010a000a21400440b030f449035030340206107860000d030131214406001c40111810500d40703496003804103454411001f440401c1800c241d0107200d6845c00800c19001294001c242c410540e608107041001c0c0f0a840e592600d01492003d0019081d540a1710101804c0d051070400302a000c2c4a000ba18580110309000c200400b0903000640090203451003814403080d0841401c03101e081c516105042c56110100c20039018013141c402015100c00d0702503446200030f911300c494094901090034030407141d01c0b0042c5000a00c21200400e41c20718203d800381c0441d91070100c02d102104100e2001003100300012100e0703208100340000380329618010103503030410400d55410801440c0c1c6808244484000748481010032116070389520320000708100e003460549066140406101340030b0300e09425412100d6081489001081071068038201021100503c42c0489a1600006441d1300c500d5250070350349402504c0108135101d20b10010708078200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 318562679 1250 318561429 318561437
    0x6090f050a230115090203070908010606020601030303050f04022202040f0e040201092102090c04090513110307080a060c0203090a062a080d050a0612080310080604030903080c100c 79
    0x2c0c46544840480380d48400a85569a0400c0e00291807056102854001e49540c000c0159a994494109642961841c0d2001e0125840c103040050540c0c0c0c040f94080c1602d219540511460711ba0302d142c99083c180c20742d006580701201e0b1241900c0c0c101d01d030b003140c6401c1626500244c107081d6030745584051110380381d000045020014003000215a40080a034000e403805c141154201d6103502d500320345c00f203d00100203008117081c00100309003030309100075600284a03c1009101524058088681e5002510b10440d40444078200c082c82c18074001c00c205041c0c1e14140000d24841800d9200c0c880580070a040c40015404100918581134903a910208080c2450751281038030250f06001400c500315000c0c40800c09219201c19030310000300303203c0c201e654400320104003190540320103640800030070360365118064003aa0647d0047c10016000b0286114040001e907080155503107280b126151801194010005000c0604c00e20000e541c4c0d07405411080c0070207040312514040300d0000b504403080012080c02003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 318563929 1250 318562679 318562703
    0xf0b030102070b0405060f04050303010b07030905271005061e09100c0b01080606210f010c090503060f06150d0b030a06020711030a05100b011403010b091806010c06090f050a 76
    0x2101c410000650447d006011007562803405807078541e00e900041c014042407100006008050500c41c11004d40a407000600f24001000c0d010a0781128000d50000c40d44850031040c000344c50b03044846c0400d0129900038050380d2604142951440c6480d05000d00d441c1121018007040303d8980700e0510001e0445110317100c407024818a03050825031040140e119609550200080103840e45a0700340b24620348030f508800c001c1200d5074030041800d01c450441d42e42c4566203440014041a0780c82030f02d28040707400035003e48045484074a1600b09440040740c0040d045544250021314605440c0004c11044441050009802a01e10b00003810030091103004d560041e000b10390382040c8020340c0341040c44407000b140100324171403031544c2d40b0341c0303520007080c103a41c059541c1e24203002907900504e6204911901e01980580da50703110140442c040d005a003075940500008c0e0120440f00d00b000d0702e06400740304142c49203041d040c11581c61601601641c4000c46034060318004000025a0400030510400d100c5c41c60300030782c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 318565179 1250 318563929 318563933
    0xe01111e1218010e0102011b020606010e03150f040c12060f0e1b040c0e04051006030605010221030606091c020103110403030915180b0d0b0d0b0a0f0b030102070b04 72
    0x103030a4090040744020030040200c0020141110144940d41c00c007802c10000b003040701c1005030700408074408119640762101100c0c5441d5a80403400038031500e426250910700c592003000b1f055a55911460031022805043d011911740b40c01c500c1c600340d10610031310180c408141c513021400380701203a405048400c642c550030104550700160040c00da20384018002050550b40c1810a2121f4008000b062801142e480c1e00d009909441036500040c00d190180c0180315605220b42c0003002541f0510480c0002440d2810100d003540c0b02046080103c0e480e82600300850f60384a91140c40c83c0c3c0050b0509502c400300300840001d40d202c072516240c103800302140f9a40c050180b400050107803a900441800010300070001440001d40045000d42510f01c0c0031011504e070303d40801c050b108c43c40902079900001c1100305000609400c01e000800d8000301a10092003180034140a1118420b21804000d0a1031100d50002c1c80b160090360103045c044000e01c0c07012460741c5400e80030a089074003003101074550b1a040020441 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 318566429 1250 318565179 318565183
    0x70e18060c1608130518060108071805041503020a1d1602030904180b07091a1809090604060c0306051012090b0a021201080604020f1c08040b04051306080d0e01111e 72
    0x602c100721b200008258a00b07400002c284201c014409024081510508030040d000d0080d10005068007900401c0460614000f80c0390b58030451004a11440079100045030b0707001220307100c40c484501d0403540a001d444100c04800c2108000004808511090080e02d040355294094010194020401d08038030312001d09120030b072440010300c1d003418003107588800c026603071004101480365150140126103a10910301c07134902c0020081034440e4401e0114050041912003c240c00b4060b0f88030f0503041068400d5240290291002840386540c050140805d41940e140500c08110b006a690900000d031040c80da41c96625400701a81c0f0418095808500c80c3c0100c500c101241e40541003c9000b090749181581c0028036042da18511940540720580c54403e01a001e10300d400d075101e9200a003181c40c1c0352034826824607500540319452050305068050346800000748100380070b840c541d40140004c00030100c3c098490022820086040042c607503040c1c41300316000d00c180d5810354054007004c0c0c41402020100b42c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 318567679 1250 318566429 318566449
    0x20c1903030c020109050304090e15040b0906010602070f03020607060e01090303021e04050a12020a030503030403030b09060d03090306050613150504060e19110912070e18060c16081305 81
    0x2800751383c540f40c1e816010900000550b4221a10300802080030000300340752a05011f51070104090758200d19081c0b10400003d2102c5501c28985031084034000e80c0c2c1c98504a948105510801060b0048240309101508107613009101d481e0080300e0114160408802c03c900712081035001b43c00282d8040340c002e4001218504640ea1034402c9000e4a04241c184000600100c0307091040d003540c5482800101c085480d40d403124002141c019054a40320728090a0183c040d001d1040101d1080420030b001031040c3c600240b03c0017185070580c3e00d803000300c0c0c1503680b258014103024143e43da000304039101004100d42d481c082c0014003000c00c03240c917550902c0e1074180070030395000350061018403010a00308161103542d402c890031500204840420461b600c0c0469015074410111003640107601340303900b8100040006a002c0841e05901e82442c11950742d06d0500c800704007500d0442e08941c104001090f124416000035100211688410f40c094604941e07840740700e07500062003c2c0305280e0034101006030385001340800d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 318568929 1250 318567679 318567701
    0x819081609080606040f0b0d03030608010609020a0c021905031015060207050d0b070507080705060912090a050d110405040507060f020c1f11061e150f1201020c190303 73
    0x3203001d042c1002c141503141c12005204500490b501c88240b00340030240e40150070b0940d406030502d610101c030b508008016103054041c01020750308001002880e0b003854030848001c0d40e0309030380300181d001c0755a0030401c0400700c1d200341d075240c200c0c003803170125040d0390a00c1090807010b1003450000303800050080f42c3e514070040d50b101c07200355006041d04000548801d020070f000b081c2c0c00b4603003048641d40c501084d0380c207020700803019003502c1d8049103030002c01074001029401903c440342141c10303020054030418814411003c0c415023004d036003842002607090400510003a18032540d00b0881e030f42c04803030105e01112002c0300d098070305078010301040003006c3d0403050124401d1040d10107483d0500d43c0c1070219240307060002c81090000382440e55112501d10903d1106021040942620840d06049003c0003100521040d50100986031001088221101e03c198a0103203001420000d810701030042084400f1400e0313600707034505540030860607106440c144400005080302e9034013a01c5070121824014211080d40000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 318570179 1250 318568929 318568937
    0x70c050a030f080c030f0723210d02041d010302100903050a08090607020301110a17060f01030506130f090c0803120c1e0c06040b0f0103080301030b0408190816 70
    0x41407020459101065030202d0f000500c01d03a03680d4041d0045880c5200b83c5c0600c982d0f5100100c0c0d80010048a1210a0621100c1d00000c503110b420501c209034513409000c40d01d214a040162002a006401401505d80c2d0040b107200182455500d00d1021000d400c080c21016140301c2d000018000c500c1c04140d040080c00085c6010038a00341942c0c0d0341e695030102c034000a1304000700800e610752159110340407901c09590285c024803c4104c01035010072150000c2d0f50a5004c900792040088000d901da120283c0309000003007441c0d4a01c0c03910801507009080c042c0242e83c10044540319156a240f440c054034030801e4803414001072100b103030300300401100075540050401b130b0020060030010410302d200968010008498007940c0f080482c444c03c142d00e02ca050604000c65010030b0104e0504004501c0074032a602031440c6030802d076200401071080d54000d0200812404081c401800800c0341004003640c82407161403840c0c40d00c402a1104140c0036040c0841d14005560442000102410290742004110140c20 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 318571429 1250 318570179 318570199
    0x7120203040e130c15030c0908010225050c060c0f070b07020d0228080313090605030a0308041b0e0603010f1b05030604090611040816050105091306090501060203070c05 74
    0xb01c0005100c1000d00000400c41c2c9042d408800e000c00c2200400c01003d00800c0c030314221000800103030242540c40001070115545250004000806000702c41500f8500d8800a0b40e6004462a0080c0c07035039003401c19202880f03404582803068845000400301907100070000c0441000e001981850104983c2100000c59000c0c0240c40040c2c0b40c036128405520b9040b11020441c1c0741707140c1c00d003007641c07940441001c005e8000d150014442c0d01c040010f020001c050003890100030340700c4160109440451040381c1d00340e40104042804248608020707a040391088000d40b0300668a040c941c0072100b0036401000a0b40c02513410b111481c50300340315620704181ca180b41808403100380840b0b20070000c4101034507001e001000000032200d0343d0307941c8101c1129600040400c0200c02c1820041c509800c00e0194006920441c14001c007003448184a0300e085600580d1780310b2400381c1d51414004120810404a03001300c1c0c86180205032103845015060180c00303d98019038031421541001005140107074845806900750303030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 318572679 1250 318571429 318571439
    0x51501080106140d050109020402030705040e0c0c0312090f01020d0c021009120509040b0a080d020d020303190b190e0a06090207050309060a051204051011090f0f01230712020304 78
    0x4590003100f81012100d1060404550409038090081050002e41c0980300204000c109074010b00a44103540803207560002c0d9039103411a0012038864031500600c40e80c41403000c013802c4840503c813298444404410b0329182f08040c2101740c2aa00040031002030310744c55680352003101c1e03810050f502880021220601c403000464980308000000072000c94108070b40081d4030812a00d4503000701c41003a03030240507440b106603200c40607520b41450304a048014040c400c00c9414003131000050724002c43d02c0c80d150303803120760940108000078a80d510101d908640c12420711580352034500390b03c3c8018420412001051301c3e0014500080350130642101200c03910501842c008180c0000a0b507481310310903100d4960760300c3c0b000002e450358041c82a00c0301c01ca1011108000400c10042410700d80e512f14810240314a9080c1012101607000791100d881c0c01c411812818800c13850500b101a0034610181082d164208940d007658a8800e0341842c0841c2540300010800704103e0256580e282d4503010340302030340c1882c0c100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 318573929 1250 318572679 318572699
    0x323030f2a0906040f03140c0105030405060f13050319080606041413020c10020c010b0405090c0d03120e0304140a060c08030405070e34140f040b0403051501080106 72
    0x8041d40240120007041c5004103031220012075002e000e14210988000342c0c1d07482c041000040c03144462a41c4d01581c0ca021180e94052000c0c1c9010b5507002c00a052a5070714250520107075007004044441510b440144c400128005100424117440d10014180d558401440c014020708400307003420f4082c050421040041a02181e181984d810040380c03440410703088800035001038022411920001d0043c2e0f102410f048000d07a008020741c440d18402804a0031141003000110f80c0101c40b2694650850381000007036180207050030050300d100e820035500000c8245101c2c1d080b1203118807032084903400043c0a108d1b90301808424071801c401203407410304d05820008001e020341903c280003030100e04040041000c00c0814000040a4113001140b11401c0c42c201003488401045640b01110000c0041c0c25800480e00c080300c07a010f00840f07034580b80354400400440c610319904c07024161007900001d110124000300c500340104021405600286200004c120b0841001c03c41a0300c00c50041c4c0c500340301004421300c5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 318575179 1250 318573929 318573991
    0x1612030302090a08011b0e09010f060e010c050f070311030d0e0904030201090b0f04020108090c06030606090d20010206070e030d05070f0f06150506070f0209040323030f 74
    0x2052a0158403001c0c06804102c2c0780c0c0030303031300718000e02d500f4010780d030302c0094441d000e060420007565a0321a070f103c1e01c00c05020300341c04207014210804c24482401c0c4038550140c2c400d00e082a4041c940100b410308540c58041c101035407182c0d00605504862001c0042c0020200b91104081c0228080c0030210f0700010701421402c2903441c198007414109000400b454000e40c00030300c106405c5206494185089180e08962480807070f000c074013003441c0c00003045002d400003442d0013403848042c28092031503c40d04200314054114030103165100c00c0e031000c6207001500e0460030b18001c21290b0015807601c001c4100190603c1001000042004002c00c1010925a0005040c00a0804030b0500b1540d80019003000755030082141d0000d407611000d45041070401007254085030021b021060000f2713465840e00c00b000868031410b940503014807030100318040075181981d00650010300c82d080507038401c030b28020040ba200050713410103240c0046c08400c010140508228180c0d10810f4140c0c07482980d0701c00107104c0034110b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 318576429 1250 318575179 318575183
    0x90b09060403140f25080c0f060f090607081e160b0406060312020601050415030302070315092901151b030504090f0e0106050409080d150302060703020c01021612 71
    0x41083c03038031a4008280041480c41c070711401038480714022a0416110700d12180744445144a0b03058001400f080040f40380f000709000284501442d1001078100440c1da002081691b64020040003070340c4241d51ba00d4000c3c01042e00c60b040094030f03041030303282000303d12607807106071450000c0c1004070024050500685840c800d502c02d074441c0007922142040c8004045540006040d0a05d5002134242c503600001d41c541200c404990a001d440c803400b41c00c03d00c00c0564840140585d2000c002800081c1200025480e107496081001481081a4460301c08081c8102c01d2884030641c5104100c2c3d0741c004001086014003000901b00e5040c0901d070800805810613140d01010b12211101440101403081046400074148580c044c030044030104040f82c000c000305119201c6a610f00400040c0d54140341c0145034a542d001603006041c582200f1400010700340c8464901040710308410b010006070740e0b03140505140c5010754020aa06040c19002a1038150520081e0a00101a650410603d10400c1514030500c0d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 318577679 1250 318576429 318576443
    0x4140f090313030614010b190302070501022203030306080d080a05191a1306050a0b0c190b061002070b0d0b01021906020c10050610030b1c0b010501090b09060403 71
    0x140c0c44440490460040070740e104660311094000209006041d00142030403032030380101307540d139998940e0061918494a00f41c0c0d4001d40ca00c01420f00e9050280e80500b609a00072400980740121151203090b1050981e8440c0241c005114820f005060707040c812200946400d034018001145070300070260005000a2140c004140c503500006c1c0003001b07041684002c1c1007212402c3c03004100a0b030a07080e55071006009103005000045004000070344a0140380d00301d80d0003400c89101389050100016450348486030401e0342d813207004144d008030445203d618000e24010500d41c045802c0031350400a51f1401080c40e1021580040c0c01404640c10b1101118840e00d40c400d00000c4000030030f40142c2c01c003540034030b85c0351129445004203410b01800d0b400818108aa541c1502c0c804096900f22000716003050f140c454000040c490000c58036402540950304106006042c0c00b091800708090701c0e004141c500040b6410f0f001c031401000030f560014440e80c003401224140505119070000814900c5c0103c1c8401b415038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 318578929 1250 318577679 318577681
    0x21c090c090f0e070602030405100314180a0b090c010f0203270a050402040e041a041104110d020a030911041a0f010c050d05070209070503090d0e030f07030302150604140f 75
    0xa03402c1a48803410074107445054420f01c6585044c0179441e9003003445040c2c0141c82d0600d518011510900c60208110ba0f0719408a2903500d0307148280a40190000f0243d09078440d0b0b2045030082803c01d0182c6210300380c500001d100207004c1c100018100174a03400715406540c418482c050b1284940707021000318905070b010004568000b280000c000d8503003540b00580152000901241821800f10200d106d0f43c0250500f484d02e00e10180c0510311803104450141c880001c003800c900083c603158103e405c1c40c030003034290a82000c2c07608a0a4080364454498040070075030718000ca03400c000054024080f8404200ca040090040034040c52a048a8080c640343c82509034403131413040b60303009000d4040c19640100460b0f9060081c03040103031540d40b020400f642300d20083d03000501c41c0c82c425000c4900c04c0785048060308a809401c1d800f502c90000120307095501d80506030340d40106120810011000398069801450105c1b103280c19808014006001c003801181843e84034401d20034980901d030f8020305000d01102007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 318580179 1250 318578929 318578951
    0xe06040b0315061b010b090c160312020d051e070e030a0314041e091a0f04090201090806072d0e0d1104110702010809010c09092003040303021c090c09 66
    0x6105542c4c0707035404c80c40e140c1808012600154011b800180c41a151040780d6202d0426400b1030740140c1a460140c202440e44500000c3d100c0c015502c00c2c0b90049602504240248a5007002e0720000c407025103040c01c5d500740841e42900c402c014203810084030f003400f01300d0090038400700f600c2c1d0240700009418000c85403042c855403041d41040381d0050a00012480c0c60101d130b03401c100300010451003490a00c80c1003d2550340d0842c1e601c41c0400c800c00c4011f041150540c04841032101a02c1d00d204280c0c14002c0900c40055040f4040c00f81911803110f9581d0380780b80042c0c0c00b4408603c18903640c10054150b110703c898514042e045902d0141c03999040350341304040c040742d103800100d0010701c810148c5c00c07600b0300403003a01d00301540003d0084d140c402d03280d04d042561565401400c864800001c1400200c24040030412292941d0201c3c0d03d0500d00f000d54081e401149035000d40c01d50054030308070300080d0300081c00360108000a40550041c603280e541406000d036161580c0b440b00080740a2a04030380c1d520410009 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 318581429 1250 318580179 318580189
    0x2030d0f260115090806090a05070b0f0d0e010f050a0506012037050c121516050d020c0d1b0c06050a0302160c060905010306030c03080f0c0a0b0103030e06040b0315 72
    0x1c1178030508450345880c04201c51510383d00304100403a403078800e134100030510109041c01e407218800440d10180c20b16600e042c0fa200070342010406801c82c0d558031450311107204513a010302ca1040303034a040042800d0400c039000501141150000d020249000d5080c49002d560209440c104c00001c1c8154450142d01e800c4000d22008015108508200807201507000700b11000c203d55080900845d1428000c0440b1840181c0340c000c5415001c0075900d6a9000481581c1441c900040b85013440c030b881414001c88818403012644404880802680800468585a41d104154600c0c151901080400003140341c0c0d1420b103140d03145e000c0c0d00c1c2031080100382201c103284294151115074408080000012960b41010000300d400c60241c4000150f1544010134194000d020355002c0b281d01c03800c0300e190746186894000494022140585144a0401200e08c0c0c0c01010420404814001d00104019500d545405492040500c0c1f88900a1205010422681180c00c00781c0e5804120800500407585440300020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 318582679 1250 318581429 318581447
    0x310270c151b030e040609020f0901110f121206031504111909020304060b09010b0901110c0a0b180306071205070c060219031d061303050702030d0f260115 68
    0x180b4552101e01c0000d040c2c0c0001c000c040140700b07650030040685c030756019509910510031500340d40c400410161800b03501c9102000422b56410094905443c0c030311110608114507800e00140d0800c010400a00032340030ba01507140c0200003140186000a10b60b8040342d01a04001e001a0080d188140d44ea8556202d40d00980030106d0b070200c8040b0b0385601c0f10110f0009400070b807801d450b0b040c03420140512504000124505031404a1070b030908104070380004652210403917003e203200c0c0c022514640d481e5107401c6041c0700500285c0d030080d41c407102d0700300405100715100c110081c829070005041c010038a404c0810b000c00049100c0000c14180e403502d4050b240161181360007000c041c4000b48001c03c81a50702c4102c038401089650502001003100310701420b0351125980501e042e002140420b00e40342503d0a040380c1e55100e42000f900b01001500001d081240041640b40480c0b000c015000c00c183c3d2203190040c3c22550584200c81410442c00040d003150b00c140607000104620f14509854540104594 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 318583929 1250 318582679 318582707
    0x60b0913021e09010b07120207050a05191205030a0f022407020a050a0b0702070602060105060307030506030a0c0905040c0506120403030203090307050a1101020601080703051b010e0310270c15 84
    0x8280f0030f580d20000030005030b002d41001e076803180e010789400c00b006102084240494400038845120356080104000710302c0060b02c42005440c848030304c0007036202e00c1c103203400001d180540c0141d51210036440020b000c40b03442ca0004011500f25401c0c401403a4010300c0f86413029001c1007444be86565403824286d141030034619020703040e849141038030700c01c200c0754040c041c0c03080e00c850382622440d0380d076010213a030b445400b0702482d0792255007400012201c0c0c0c1f01398040c960005002b0203c66400445899018a88403d60000311700c03030b5150710811040c000f1907070030203000f448140c0d0002d181c403490314013920046001500082c1015000000f048101d078040041d030b40510f07008001c1c1c54940445182c02959510340480560142c01910000140700002040c030340300316034218cc0603200096014145d07a40000d00001c0030790500140d24514001074408124040f606048100d00040c01d40203103803d0703020440200044540b5441c0c0d00000d1001400310400305040b60301c1c00c4495442842100c4040e10010003000b80 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 318585179 1250 318583929 318583939
    0x509040b06031005040c091d06010315030c0f0605160209040c0f0f0e010e041a33010206061207140d050604050318060306090402060705070801110403060b0913021e 72
    0x42c040b05650f03215041d800c4540c01c54081003a40344001040d0740c014803a104401c20100c8021025402466003001c41d80c2c8580145400921f50ba0701c03041900000c5540c5d0010399440c84110301c10320410b001388024501601550405030b0070528008075900882218107002030090385100d0106040100309000034000c0c1c010940025201ca0720b46000313406013900c0348100f0f41214868400010f0303103c500d01c1d04c280600d4010180822003510b4441e1000340410140110781d040080540c24901c10010601200c0c03c2440c50030035142c40c100d41c6000a18009010f0200d0344580c024101e0180103200010354581140c215403410210385035902c1c006400c5484409029056008100c100410840040001c141e0602d00920303c0705a04401c5060000b180000c40700076800410030800300c0d0145c6000e9000d03051842c070480460350100d0f160280e042c2590f002c8500a018944040303814000c000060180065884003031704c150009107030540045207014202c040190107440f00d900318000325400305001e8000b6030700c0601 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 318586429 1250 318585179 318585181
    0x40b01181d030c07050d03080c030c0f0f03180f071701020403080a020321011a1b0115060e041e0b0a17060a05090610060806040e01090f02010228030509040b0603 71
    0x216850300c903440500b000d4054050404007242c81d11b000e0500d110300c250169035040813961280c0030080c1581c009895801c0c0a0014460b01b8500c000280092004c074401c144415240e052450000065111b298148401074205e480305810403680001c42d8003c0320000d0b40d0124224045681c0b1600a100e641c01c081c082c4400081c002c025242c0000051150003010f00c06200d03c4030701400d00120020007130140c40b07c45010a07103605140ca4124000e45440e40000c001c40500d00011b420803821184901040803550320344800420000d80c000c154054400300030b8a042c030248240c3d0361102403c281c0014403284499840004424a48590030b140000e8069450440c5807907805111142d42ca0200315040303070005046c400065007507032000c01e90070700a15106869110003400c1200568000c2c000910781508107035100e40b07001c00c3d41024080c9001a601882407010b07104039a000083c10095020340e203030f000f20f4021600c1305801c0078140302200669014035005440701000b00010780504407140101d54000300c040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 318587679 1250 318586429 318586481
    0x417180a12050606060705030d02070309051c060f02070b011a040b030405060f07090602060601031116061b03150e0a1104060815040e0c06031509010303080a14040b0118 74
    0xd00e070449100e000742d048030740c180d8981c400c201540c0f042c29030003086e0390824400801d40710283e402500c0901d1103400c01602c042d85900200324031145001d048400c2441c96210102440b41c0c038400c000c1c1d4100600c0043d440d00741992180b00318401c0601c00c011410402c207503511400e04500c010358002e0f16000702c1550f5242010b0500329640c000a80d1450828022100400c0e40d90340501310b03020032103100f500941460b03940d803001900106510045400c481100308929a140400d4107921560340c3d12802001900c0203035554940f0f00812001640d00915240103c3d4413404541c1c00e070100700300e405017950f41c4a6a82c8030031041014112514414035100408900801c81300d41000d44d40d07110b030503c442031400040d15802004252550b4403e030038950b400595540b0403d080820081d80c0c1300c82d01d0780d0b0f4a00b902081c1c60100300b000354240d1045d0001086581404181005405101341c2c644507a50300c5603031400c1544600c1c90454040c4101800c480f1043c1101b041ca40c0c1c60f400c0b03068812580340661070200450 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 318588929 1250 318587679 318587699
    0xd0c080106021203010f0b09040902061902160533040306140f04080d0207020f031203040c08120f2802060601090e1909140105012603030417180a 64
    0x207014100160040c107010038031070040002038034121000d00300140b280070700e880228103041d884820400d800540310065100540c40c1d2800408116400310f1141524580002e80281807000d0007154403091500c900c4104682c1c1e6035445506d001050060419000d88a0038115142c200c4010424032a01c002c00703d030002c20b11046501400c00d81c035000411a81a40c1d0300205180005421103008200070420300080e009142141d02401032513101500d4160300e445045c001038039000240e104408401c00010401c8100000b81c0101d100800056008283c0040d03215461505401a4818160a8000403404824284100c14a5043d281d1405035a100310324541c0e1009445480c102c0d810782c04529803890020301905080c804d180300d00005c1034601c4204200403902d101414056900760b4060030001c1603072203030b02d4081c82020f009190310350801051041201001e55040c010f00c030658031a030030078001c02000c1022064130801030000c400b0724517903510a40031031300940003400f40181e40003003002d00045504644 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 318590179 1250 318588929 318588931
    0x6050903091c051b12100e010608070609050f040f0e0609010b0d05060c0c030c070e040512030403020613020406170c0a0e16050703020705061612030501120f0501020d0c08 75
    0x109445451140c10301c6500b1007000b4032003050040c2294402d41ea00d07081c0c10a002d5402a07112001400c4800366440c142e5154601452910700c6054030740d403160200c2210000344101e2004121310000340c030010b4034041019103030414911500340201c02c900010403440e03845600c0000c007056100810003d100c411103009646083c100d03210003040d0302e825882c40741890080302d00c800445e8070800801a41d5a6070310039011a402c52490341010344000c0c800c1e080760309d00a000c1c0390040c10f00640b0060709813401d8105a49810310340e64050250b4039040090002199000c0f03403045e8800b0304860389500141c90792001c82e00601150340001c090464001d5017141d006c0010500d010b00030700440d071080300203494524001c00d02100361100880c80007400084503086004902600030640a80181d5402c1584d540c04a030240d4050b52900c4a0ac009000864041205801809901c500c40b482c0c10004c640c18460038001c0b8447c101c1c4003804030304080c0400003c0050940490f80c000d410200248a01e841041c0060a6640 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 318591429 1250 318590179 318590197
    0x28120e090a0506060d3204051c05040501110c0a060e040b0a0e010303080c13030c05040e0c010f140c100b120604050307120e09010b0310050103090215030606040306050903 75
    0x8100101c0c04160040c0112401168018042450321802c1e401050082050000c0c01280341c1443e0202d024041c440300d008000c0c8401c180019000740b0701880c0c603909142d00d0081c0b01a8001c8d10b150062415a800820345050302c5003030030040010104007c0311803030042803100a5502c54228039002c03d030290700900d003000995044d2018000f0008000800c80c401c24140500000380c0002401080485d00c200d18003a006100100a14a4000101d10000a044054005480c1d01c0707941e81c0c04011714202441806c6803140d1040c050054847c2d1480001c040d007a12403500410056040c000b001408546400c80709080d07032080c2101e070005401c00349107002c0d11010010a1007550080c0300c60a04410100d8014071541e400005103150440c65600c0c0860300b41e00190710ba0070800d4070400441107072650004c6501a201000c00c1039101c2ca4440403081020b0750035003042d4105401c05a0103c0180c44849003044a0528082e00c6a16507035458045a90340c096944007030701c002d0602c401c0c0098050302000400b5100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 318592679 1250 318591429 318591439
    0x50d06060f0207050105090f10210518010e070b090a24110706020703293409090203071e0320030106120b060c10050a1a010228120e 58
    0x76130382d08010b44240c001c0040141e004015000d813001d5924001d0240461201c5909107a08000c12140c0c4040c010400b0408a1200954071010b01c00401c03016a400b00c0500718041c020700440c4010107001742c0701d4450341300c2c903901618003051254060307840d180381502921001c0104540070885402e41700e01c40d005a0920710104002c02e040769520325020a110080d61829001002d2151942d6544103500000c0b4400000140c000140d030201c24030b1031a1400c1c00340081d111420305003d12001048031410070706907111031a000f0584900b11881c1c0100c2c030f90382115001030700140c0360b90f0382c100305845514400342c91103200d01104041034545034250b40702941c02c4d008140000c42e404160311401c00b030b0b44070038019240030840034100c0b1015888640c001000c014006806241000e2024248a190009406928004030340344e00400c1840c808603c00c4180c4aa0f04448081c0221079a000103500d65101c1d0f90520038078184621291020f085802d08503e84075400352003a00030f40341510004003611078402d0154814 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 318593929 1250 318592679 318592693
    0x3020a0b070908030a050d091a07120203150f040b0904050607020105010b12012108030109061a030105150307031b0503011d01080c01030e1216031b21050d06060f02 72
    0x70910804406040d00c0030310005510340b5041140580d80b64001501740c440342d64440500d1000070b0f5411100c02c003900c2c01c0d00050001d1b810312030409055009481001079284d481030080200700d406003060703201d54030415503641040c00107200102c0c0182900780700842d045503450040c4410810001082449070445038001c001c2c907622468404054030408041d020180680001408000040c1d091070b2102d44800070303440c16600107640d50b81c805070004d83c401c0035012b070384007000c0000350401c0940d20890711081401d98510360402c4001011641a0002012030303400200c00942898000d0740140181042c00c009d80d2005507031000000d107190b000340030b4400000c040c1c0b50702d00000c09060007014143c0700000c001c0c180445003180110020b1060021380b103031a108110000d8035409180d070080c03082e07208400254039070803003d040181c040d040520500b444900459416004130f44020f04460081d145a421481e51044101003201c0c0c0740541440f0030344040c038107180000d4080d00305045642c0b08dc69a0259100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 318595179 1250 318593929 318593941
    0xd060803040b0304140d17190c1107080703021c02030a050712060e0a1203050702071e081203010b03010302040906060306020a080105040b0a2403061a0a08061215041e03020a0b 77
    0x60314803255845000c13841041610014914001c41c0b1a88160064064280b848d400941041520a0402d030180890300c052051340c0490000e10652000c1c00b0350304000c0200c2c910f560b000c101310080113000c40c100081c2c0d12441800b15a01800b20b5411150400c0c11684101c1d04c540c4409a50160210126042450300c106901107070f07004134071411100d400c024491030681c226903040c2c0180c08001c184d0b104500801001040000340301c0d0000c4c04007100010744500c0181001c01c0380d407605003101301090765000c06000400c141302104040381d0560b58140c43c0070840080c00c1c509070307000d0019171700010555400414490289070340178001c2d0781200c00803030781440290070780401e100103051319000300d0301441200003034004d0f0213010801c072501900403880c002964035540d0782240c1001e020798a6004c200c80c80001c1c950720207648001940c2d080242201c0c0031119100011030709985002c10081e42201d0000384002405014904a01603941040040402e4a04003180340081d16448020411691454100040b80d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 318596429 1250 318595179 318595183
    0x6060d0206090324060d2a17070801060902040e04150f1103090c0f030c010810030c080a03030e06130f030201110414011e0905220f0e0d21020d060803040b030414 71
    0x8a800c0d04003c100042840c000c0c070034100c4100c501047c8569000390980012000107803403801d403140395290013800d00b09003040350305425140d1641c0805101c0340180b1080c8210f9072160480354225610052203840524158051405003d25184ca4070b149403802ca01881c000042c03100543c414290030059840162503681008954074110b41e103260550f00218040e0020350140b0703044e940100c00132003a040c90982e00d65480c1d0b003202880d044900e26030419846a02015014010014440340307a2001e417440b441c0400701004505880c001c040e0802c04e00030341507000d05001b07501c814200b01403100740c5503032030341c0380c04d01103450050034012140062a1583d5400c902d118012051034500d0295440030409031600c0200550403106001d0800301f948034600070804039450784102495007003080790104100403c001250300b0328a034520a40d09010000c283c0c8400c0446000344d00100a040040040e03e5280d8030340218003c18a5411808080c84001408038061404c100038501c50341c4140e1408001c100032030745080d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 318597679 1250 318596429 318596449
    0x8190501080c0402091f020307052a151606021903050c03010b030403140712081302030604082a0307060b180a091118010e010602030c06060d020609032406 68
    0x50303098002c254464450715160f00282000b0030002c1465800102c503000090f8000b81d072112000c0942c0c00000d031a001c000081c011030464041441e086c03031400b03203840c071b1401d281e0341c80c1c3c8030342841a60721a100401041080e01074801c04860101d59416800d030341c1c40c1c038100035480101c500700e40e810042d0060317000505c00d0250901c503040740040181183d29121303000829403c080c0c0220103208c4d845030300301110500c1102802a1a001d808403901010207407d02610b121800780c90146211004d06045001d624009183c82d005680302552943d1080144c44860340c489a503680c4002c1c3c05c0360b0f8030400c940c419000020302000740c01504108109003002d0104a0b408600c10b00c15082800a04d00207103034001e056014006860052501c41c03040750910f40001c0503e401180c130a800c1c0c055540c014007034416101003483c050070303c81c00158906124000b9103070fa203100c010415845009c004001d8021900c615040c0d601c2c100300681100d000603801501c405552421f201010941c01d01c000004400b4a001c3c5082 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 318598929 1250 318597679 318597689
    0xc011e060801020f09100311030c1207050712120b030316110d0218060d02040e03030a0501150507021203090d081e0a09120c031704090b0a0501020c1002071508190501 73
    0x2041c500740c8440240b0851b2501c200f406014195140c102d1955000000d004500c6500159045580d603140703803400b5441500003501c0c10041050503c1900001207640040c5010b000b20707820156240c0d140c1c1c00741003010300741640945805010200301c041d096048480c108014038071032003180c1c203803a101609204000042c03450207584224015640010101461446600203002074107101440c64150040f4050b604105c44230020f691002040000d03403020343c0305050142503a43e000352002c40c50054014100d00500d84040e01c1440c00d541d41903810007080045861080e00940960712b404c03070a045c2080640c114521000b201c0015001010700d09034032000f252156012900e41415981c03d061500c650070780c090000703e51900c001d91020021480c1155200c0c80e041b8091001075840d07091421690503174542002442c000c8a1580341885240e0300801c1107680544191144010200802012458241d259204d01290426040070085140e401b400c890303c501e50031030040780d04060b00d40d010401c8640910070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 318600179 1250 318598929 318598957
    0x111e180403050a1d091608060d2004020c01050906040506011e15050904140702070f0315021c060303021b0108070906030b0102150f012c010306020f0c011e06080102 72
    0x80c80b020f6000c2c4c000e80c80600032a1400303c000d41c1c04207001c00c00746501502c88600149403000d02848081d03218001692004082c0c1305419000c1065940c1c020100c032101008400c044010078400c020f49580d4140c4440b558100024007407403c0c10400d0b241c4606050b2030944060081000118841c0400e9500320714034541300c0e40204580e85040760820242e19503607540000c00030100020841540d03a030041c10a140045400c200050901e0500645040803c2e842a403a40d500e80d60200045001c2e0020070541d10041400940c0d68100100c0d1011550314812400304503501e809404810f150b40011041200030f07007006410404c0b9040401500c03000021280300d030004841540a0203100d01c69004907041c0881801140d14224040c8940000f2a600b160000746c00b82c440001000501038541403416401001c829516a109009042610551050101070410b940000741e5040745920442100d01d8001c869000b00700e08000c43c4c2021800744843d602c4600c44078200f00c40810341040c1842141d40007001181 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 318601429 1250 318600179 318600187
    0x1512040b01050a14010f09080a050610150219050106050d0b040c0b030c0901030c0212041701050112020a0e190f3611130c080a0f27111e18040305 64
    0x2004450b00c206d00300c103c0040101c603101c00161190200705445000d8400c07000f40000d80340428540c00b40780c065600c03284007807100d0159026110b401280c040c609030132400410790050007904150340980f80d0366014030303000f1100c01c0c1c480c1c06002d40759010501075807080403448203090b612844c8005600043e64801c50150080010004940c0281e001038403500040c0150742040080c1d011402054200e03130301c4901079810014907042c0b1200203100741d5025054040c020046031381141c01040c0701003014003030362800c0c80a2401244268242401c40c000542c0c041c1c10501c032000a4011040140032810038600c40500d81f4039080c0891841b6003072090400c0c030b102001c2c0384d0702e03d026100c4480c02880040a540c006400320103085980225000d070f0029000c5588404240781007010819007101c1d10040344100e09482c105180c1001340d445007401e0000c0f5603000e2942018000c0f0b04003080740344c0c243d0070f0840d80201110703040351412580807083c03480c4060842e10360000305e034030014140c00080b08403002400250100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 318602679 1250 318601429 318601469
    0x6032306040c0306050310060e0f090d081008070b040302010810140d060b09011511150133030614030109050a1403130e0105100314060f1512040b01050a 67
    0x58402840b41e0518030700402c101c0d07030b104042420b00034507000550a29440300c0d414004138111501d2035412120b100c0030040b05103041101c254131600090019001c12840102044070383c110000540c0281c01d951055400e43c43d03540102d100242d006200403804144001d00107000300304d8101c40d041c100c03500502c9a02098215601b0070812407038002003190b2a5a0700d00a06019031601403045000c0c0200d103518000840314030304050714240070040342c1801a0f1101c4071544440b1a83c141c1d8504503070285050000201a081e44a0990140c1d000030758148a40c01c00401000341d80341d00407004a421400304a1000d4041d44107060a0f078465507400f0301581c0c001c41038103001030301d41028126100c0e460801da9040510f6181c40760022a11544442d0b0401080b40040c0305610f0070011080c040d480d54203041200460040030960300e040020305041c031880e03114001c18555251030702d08403640c515030004180e95000f4220350500341c00040e941694411044000032440d820702460500a407071040b540d504410b1604 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 318603929 1250 318602679 318602681
    0x21c0c0311030408033319080307230a031d0a0f060201050415051509091f061502070e040b090102120112030e0f01090e0901110309070603230604 64
    0x5010405688041c01c4090116010140d070107503118a21a80d640e003840d5440d5824440728a4040c039041c869007054000c0e04412090000694005559002001303410312200007102285a020940ea0301000507840c1c00c010a100405a01c14019080300b404a080c6805540c0e81710320300b0f440107003c141038602da110740a00d00d00145c1d503d00001441842c200351503640200011590358030186c0036030344a20600003041011503c4891000110070200094503103403480c20140d551203010a4002c90308980450a848024451074554010541545581c0c02441c505200200f500d03100c0c40082e04901d01007402da091000c2a10000c94244d10203801c22511345442c1c20380700040251009096650800c24440c80b0000700030a00e00230311004220300701c007c91a04024228025180d1007a210380c2c3c070502108200d0b03800c4201c0380250303100307200c113184140d503a800e15500502080c81030351b010a10100410603480ca0010b220016100030b070ba000d0040e01c00305100e910705600d10070458036015100c070780040c82c00c1c00d01e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 318605179 1250 318603929 318603941
    0x6051b010902040c1101050a0b0a0e1e0117060603060103050c2b030302210403090b090604091a0109080102040b0412050a061e0b03070b161b060309060f021c 69
    0x10800000403480d8803580020101c5810b0360110340842c1c8410003040c40034500307102e40d03640300c1001042808a48001e0380003810b161218001c070019101102c011407402d480f4581c095100400102c012041c958544062841c500108044019113104040004100b4100461418101c2c0e42c404024190f0400310000c00102e144941c082d5510310350803621a03014041003404115055009840c01070351102341c02807000381e0f03030030881d0402c0c4004189414880040e5006040303908039505a07626079115500000000d10724880c580c0101021810000c0350720306401404406082e5401c241ca40c0003659036981501403d070f00840c800c1e49035940090000b040080e21011282031344610900c2a01c580c0036103545e5000403a480400f0444884940401c5008048102d1244040c0302000700d00404072903141050203000c5100c1c441100901544402d00f12003040300c104002e400340110b0301007280c4001d4452400400a0070243c01c15100340382042241d845111091003140c0e03800e452142ea600d540c1c01d1840d030310005044 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 318606429 1250 318605179 318605227
    0xc200f1018060b060c06070e01030f090302060402061c02043507060513091e0b0f033003010305010c020c040603021f120c030608070602070f0905130609080304050d090605 75
    0x40c0800880320414011b0003c81c1c8a49030545801c01d90070f448800050440d22403407400d4111914140e08403010a400088050384558100c80540e13550411001c0000311483c56024001024004540894004c0c056007000400748000000c089075082000181c1d80c000c0c0c010a011406600301c00300a02055100c1c0c0001c00f490441480300081c4541d031400a041200c0c4020414402070b44c601c0d6503401c0814490103402d95050b0226802c1340c101c1c12040029844400300c0180c2c203a02e0700110480f8024490f0040505102c03844401d00f07a0b2203681da418120301030500780c0c07a031000501442c00c106400e07142c684681c40599030040c2007002e41d083c118030605c144182d4103403d13600380070100b8182000301e002ca02502c0d00403141d6075008500280380c140c450749002d110342c21400a5400114007444160707208844103040b2590044003180a44419440002c000c04000024001c01e0410300c0c6c0c041884100390055001e10311402c111380450000c2001103a02a1040c050b50740081c0b01000000c4c6040c01c4148010780c0f5803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 318607679 1250 318606429 318606439
    0xe10141b160f020111010c050901180e0903070312020418020901030b090903070b011406072a0b0403050607020a02060a0309051e0106030b0903070c0501030c200f1018060b 75
    0xd10072402051810720840341150040ba0740d0700001c0440d41c1c841a83c2c1c000ca0301c188020700446034500e00251450042031449d6040100b8030b0008054096a2b06202c0020443c00c172051805052840c401a02da034441e0009401050350f2529000c0400401c0c82114102c40d207680030b4044082c0314600c1035010b54040c5d100c03241050f4a41e040300541390350720100c81f4040c0c0140030086a59154900c2e15001401059100070841101413160707248a8403800c00300c806641c1c1c010007031045a2181d000c240e04856410001042025032044041054141400100107803030107202120810340c0c03107000072030351401c8001c80290030103010f10641741100c0c0030f504507071540d510030810340307040d0300c8401400345d04014000395004590391582401c00c01e001410701c4d00c941180c00e40004d1841c0240c6629440c0c0e0740680740c41040c1c1019521032a088aa5200c7c05607400790300b200d0700b0200f515a0250b41d400b03507a40e1317485071500028016030200e0350341503a0a00c1441c0707425600c190151900c4089440301c0c00180003c0d0303103558000d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 318608929 1250 318607679 318607687
    0x81b12040201050c0d020606040e0c030717071503021b01020a020c0f030f03030f060f0901030f170d0c110106050f011d01090e090102040f060c020603190e010f0e10141b 74
    0x18260620400b075045d4000e6004003003034508502008180d800101280305290003044c3c503c03c6c0d80e20301207034600c00d460408803204004820280b240c1e207000d055510100f0201707010404074020b03d80c035030000c00d02560b000038201509003189000311308234882e41a45402613809172101c01540d062000c03844903008402001e90340350325075041c0c01c5802c41d40b007161800c202440d001d0810100307241510400c0c4040c40185d0b600240b80d07055544503400d4210700900039100491201c05680c2e950071607000c4640e60740180d4418011403020402c05401c069010049401d80c0d402c2450200f89410a40092005200165141f03401e282000548000245035082d425041184203080481c8680d501c00100d409615060001650303280f80c04810f00100c40950404c2b820050040046c0c2c000d680c3d03003410749411102810340034800710313030010140004212001203c00341c2c0d420a1407d448030310007640469031210742d40003a40c0081525508501c11925090301c0100725017640f1022a000c006040082c42c00490046425464 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 318610179 1250 318608929 318608947
    0x40e0c09070210060b09090c04081203060a26060a02190509030106050a060804050c0301020f120a140a0e010b0306040512030a1806050411040b060301060309020d06020d020406081b1204020105 84
    0x98920030b03049003501c5d041c0026180c8507424240949640400855440b03400d050920702000c0d159044c801c91a155444007002207a82c594419030010010040d003000242c0c0003001130000c0c9e15850304441c08022034010f060000e00d65025500888407145440c0f10100380756031140b01c00f07481da9081022010740665071a8000304250f140d150320f02000c3c02c400e458450305440c0601c0c1180c81c15071045d403624040e9005010512026110358203440142d50640310620050b071314a002c9000030728030052250148032409040c0004210076070b1100750800c0800d0000d1040320080d9061594a0400360b50060560380001c02c0a01c210010034065600302c000383d040400e040c1c083d031112091186003094241c8000360740340240000c004000780d002c031041005480a21210328a00c00041040c0014031030101850789a400e103a00319135800040400d0903611200840d224500549800d000350018010131000c100340360040b0320084c1100d80100b001560b100b198514008141710709c888400c80181c0202c0c144801072000443d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 318611429 1250 318610179 318610181
    0x5070f051009051009030903020405190528050f180712050c010e010c0b0402120a020603040b07030c05040b0304031409120a03030507030b0d12200d020705040e0c09070210 75
    0x2000010072102094489035800d00900b00722401c811440510314103401c0d100000d40220350703103007260340441d00040c01340c1c1c580c4c60030004084a049962a03c034034080401c955120030140c0e04200d4038981c070f820381c40c4011b491289000c4900540d40c036560082c400001400274000c680d800642000290180c030804c0c0d86e5540e0300d80f0904402001100d13a50814614401596802801c0410b004801d2078a0458108552200b440010700035002a000d0440110364003c26142042052080f56000d1b0005940b8540307810003103480c000603600800041e00b000030001501e8482e1040c2d505490a80f008030b465501e41c0c9e42c050711501140d036102c810881c81401444220350f1465091054603840e05c02400c2c0ba04c40300d203001000c8500080008040c5807510449001300d031205001c1940fa00e5003c01c4482c02160b6042c000d80d00d0070412180390100e59000f042c000ca04000208103404c5d6290513800b00c3e40301d0340d00d400421050301e01c2104c150520358000c0380707509890f250080d1000d0300080680195010000c084010030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 318612679 1250 318611429 318611443
    0x40b0601050405030a05030405040c0302031603090212100906181e020f0d050109140f0706050c10060308071109060d0209040c05031212010b040b1e0405090a0501060315050f0105070f05 81
    0x11ba000d402c085010001070806020705940d5242070300c0d00310728501e010b40c0d900441c160031450601c109076440800c0821502c40d601e582d006031400001322440e103158400000c001e0030b9000400c40e852414559150806184000c8602109a0101c00c0a1980e00108000168152491b1080c1c0e408009540300f024561207601c5000f030300c140204008101c00109003060a0050030403000611690b1000d0361414440300082005010350b280703850701c182c0d20004a85501d16015401541c03200c080d02d001800010000c02000a10b4100d10070340840643d06c28000400c000b40c0f404498841c3c01c41203003901c03d0014648180004c0d0301610503000350b2011510f40020924111346640781c0c4044d00000200001d0010b51807094500500e00300b01024641414510300c08901d00070000340510034800310455002c5410b100d400d8801074440a03140c1c3c5d84a1900a0120004c4c0c10300307100c3c2c1c0000c40e01d8003030040d410f284281c8a80043c0c0c0e00c080c00804111040c0801102e10394441401590a0b4940c46442800608240810 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 318613929 1250 318612679 318612683
    0xf0303050609060904152406031b0503281d24270304080a060501030201030b09060d02061e220605120106081801180303051608040b0601050405030a 65
    0x30185000c0d800e001455501038032081c0303d480540b082100041c09501e129040011421010074610040c0030b100e120180f2520318031104a0041c00c0124005505500c0150102d0651070100d00107940c07c542980c00344000e4070100f004e004070441c580401084200b2842d4200c80c1040001608010040d4500442c080040041c405800920a2224001c20245406002840001541d4280c04c10342038004032100034506a102241450034041280036080c0107903802071032203405030b6004006518204000701070034007080340400c3c81d03c00c3c04511070074000c040b644142c8c0060802c0d459023181d03800300300490700300300350030420f500c4086140c84140c0c0380d0f0b6014084c1d5032060043c4010010a101000c528411203411800821009100d415007841600f4074680c11500c079420110b000c0d440d0400044020020501e10b61a690b081c8900e0131000340d42c0d005095811400703698200103035154044400c1031808110b5a038800540c1043c00705001c944c42c01c0c0080c1c0c019105040c240c3c036141d59040801e080240710541 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 318615179 1250 318613929 318613931
    0x150c0f09061d090403030510140105030f06030a0c091e0e0307060f0f020403060203041202011b14040506030c090109050a08030702010e0a0807152d110114010b0c070807141c0f0303 79
    0xd101d6840c00c541c03100c8c3c020b0144188a2121a88444002482408010b1031812202d85000125285171010f1048041d45070700644078466843d00ced991494050444d8003c00c8071144420303013400282004034403030042410303401c00c095882d061080d03d40350301410705000304c88801c43d41d4034013400709048144020402940704510140e01d91a040c02e0403820724408140500559041a14035861641ca0944d40c04010f0100c0c1000da80808002c100820705004c4c0d50002c5400ca8000424051004141005460481c0d4240e03100700d85192110248a502c40c001d10882216510a010100c01907000c3c0902400740c5401805031541e20341c0d1504803a01d00113103940195228a10444103a1000d54095201e50381e0540640766650140360410b0001c041484c5007114600f0490404032050800e002034000800308000c0c0a980261961a0b402072030f925400020308040741c0c811448000303401140460504210b46031514002449a80340040c04428107060250390340d00d01c2031421000000702c11440c4581481d0007554 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 318616429 1250 318615179 318615181
    0x6030303050a02072312070c03060b10080c0a21021e120a2307021e0a05150709030602030408030103020915030616020a02030a150c0f09061d0904030305 67
    0x801404455001d0145401c460040049001007103001084c0d0400400030500140b0041042c1344180c140590781e03642825110f00007404c80d040c01501d803020825a8080c0508011030b107091002c105421002c03e4620001c500720b08002100450010068059540349081c0010200c2c03000d0034031136001e1607028031030360460303800b0420103003403008200a007028014421400c0c1c0340c0340307a540c460101000003c05081c1a652949002c2802074400c05866101c0348010415580b0b9040c200d6001e03407a40c8030604150b100010800c428255154000380c4069003907080307400382ca02240000b0300901301e01c4005000d8420b0010003000000018100e100541c404e50291381d911791030354114030402900b100c0103400b03406449418544019070380d40c003240d00b40e004400400c018441001101c0300340d0810119a0f00a50700d405280c07a502e0a00c59003a1800c5c006640310700e0f04001a2965a1b003d4500d47c241c5643c0400151510348140000c074002d194901c54140345140ca125400c02d03c100040790000c00300c07000c80000b40c07a50 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 318617679 1250 318616429 318616433
    0x160801060e0c04080a110d0f0609110d080706090c1203020c0102011a010f0c021f08060325150c0c060e0a05010f02030f070c08031b06160c080304060b0901090603 71
    0x3060242c00c00d5802c10094901840d103064555100c0b000800503005c002040f00380b60390340d900c05403040e406950000f9a59906121414000024101420252541401d1044005827490000d0b0b04503012903100c3d0005007041c18130303119a0700401c50042d046032100e03122000032610b43c01d800403c2004502c66030090105401840c00203007541c844c0c2c804907414041c9091303e052107a0b0040d50581071607070f02c0d13300411907031160f00001d02314900d42c1444610000b8004940b80e0050f0313004c0304103032050038281c041700e07880191044084460b89085484d0100c0d0312001c4000c0c03060020301400300a1000003450310a40030b400070b8a035000322440940c0440d01141d114544040141401c0c41c07070341d00070071090a140944130000b6001030340342d2040444d0703600307a403100140c0041040440017401c8060080701c0102da4940b4082c0840c81c20312108040076a9040c400c400008540c43c0841c3c2c2031381c11032101555442030b401c4459440709120b0f0005041200c025440b01007050880c1c841c09500781c0205000c1c1c501141d294514 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 318618929 1250 318617679 318617699
    0x90f0918050a080d14060a0905190e010b04050c0c0604020904031107060c0b0708041104020901110303090c130b2409040504050601061701151b06060906051c030c110316080106 77
    0x3170303040e415021501d80c1c2045071a83d00c01e011941103135a50100802e455854140f030000e603101000e54034401501d04030008480100542c4940c44000342603d04100e02d849000202280d800303509400c07149030f4080c400060050504810564005119082c500710030004120454201441c0b5000440059031031a103040030701c0081e421381070304011306042100707090400e604d4580c1c1c8887e84007659401070b500040d1846040c1d00c51107428040140070350643c0c2d01c80c10090b0070941c850004200c46445101d00c0b94052200006078030510600040007428080c00b03802444c0391001080410804030810482804040e00e81c0d112805520310541c0304001400d800d41c1480800350480d1038441c4000c0203041c6010040c41003040502c141c0429040500380340442948050700860b1141d11154001c045505110000a400e5019040320f020341e0406ca9140b040b681200b421400c0b021201040076000500c240d0040d8080f80c0c0312403c4952142016064400b0104280f041120720172030b40d4003804581c0c0d03554404000071054 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 318620179 1250 318618929 318618941
    0x112050405030a1e0c12020f010e0318030d08150402070f0c05090c12040206030c1308030703020d03020f1b010209180405060604060302060703052505010212010501090f0918050a080d 80
    0x4e0403007001050358006138000c01090036080002c100b888808500c280d150300801103002d1820408009001c54035000c9101e6841c1e401103803081000001582c0340d8281c614003c1003807511025a0750310f9100a6a580d80d0060b040c03900800c074075070010303420840312002c20b08802c00380c00214090583c0040441c540f1040c0010744400414845d46204280810000741800303503840340d00242c046a4650b22601d504600c081a071258210352000f0341d086800005901c00040081c010280c002d03001d03078298244282c0c068081c0e00ca5000c41603103d440400000c90303003180011500502c3d800f020001820405041c021486690340f14140c4800d0343e030390703400b04020400c003008240d40c04501618140301807450344d4003140351030151060060520601180c10800020303c140c1700c0310146254500c00155020a040c071a0003944020303500d440ba103600400100d40c9501888100040325003003800e0144d10f45c83c00c100d00c4e0003040b403004500214001003505d640030510403c071414480d07002d09071081c1c0d640c038101d82038021510 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 318621429 1250 318620179 318620207
    0xa021312110109080d0c020312031015050f04090504111002010902280b0c030c0d123b0307080703180e1b071e0311120304150b0112050405030a 63
    0x5140001484100c0000c6070009117030160f410524080c0e0124400241014001d0544003640b00000c1704004100306149203a40071a02d0484010450f440840411203a03441400c1c400030386a002003004005c052401d41c41554454010840401144076100c0090a545015007075000145c0d101d01008095140156141c00302a8000c889032101400405c800403d01c3c0c0e013403243c2c248000011402c01031100c4180101c0e0b40518110080c1d40c02c00c100303c900641820139a04000b581ca61400c1b00303407400301c1c2404808861100c454020143c205241e15010b413410120b83c1c50218080c00240100000511010040e0001c1c030710a8440d46652012014491801d0100750b0250f51042e0103136080c41001d002004a0184191120015540e14040b90030050f000f64080180700000128201d540c0043c9a4030a08240c2c40400d000191801041d0f20400360714103000a880c00307408440d10140c1c0c001030000d9580b00c0c1c0c034406018100760548460421200701241c8003114151150380000900c000810303444041425030031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 318622679 1250 318621429 318621437
    0x305030310140a091d0d05040e060108040b0f07020312160f0c1a13080d0f050117191119031203020304030e090a020c0d1e02061603050a0213121101 65
    0x15031050b000a40c940710b14450442074903551403038000149119042014011000002c98001020b9070200a02680c0303d40300e0000100c80020209241c0e43c814100140540d41010031040c151b04c901c88041030681c4003404034819880704100e030201d605200c844e140d10444600780c2c0a50b01014611001d462111203023041420410303c49804000114a942400280c1518405441c041d075070300d0b03d440b01034001010340548609404100001400880d0701300c1d00103c900300a0500040c2da03102482060031944415184d10f540120464204802060301810f1549000d007009008603080600420a50a4880b0902600002c5010305100780300002019243d0012141360031450b43ca0b02d6100108400103c00300c252140090b01c001c03441c000c2c26034041e41d102c3d595140656804010b9024040d1012100b00710306111640744420317200740d49002080c0b840c865084001d000c825100b10300001c074018000140340301d900720b500b4000e000c400a41580808040c001d01c0e618107520510380d060200c085454048598100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 318623929 1250 318622679 318622709
    0x60905090c19180504061404110306030a02040e0a0f0b180c0a1205070503012408011b11190f03080a09050d18030212010204150302160308130b010305030310 69
    0x1030044200c2c00c000c1d80103807500c800d01c004607000c2c503600303941e459100d654000e043c6000843e846844102d41c07002202d04803010403503441c0503a40014180000c55031584c1c0741e0804200c1d6405418582c0184654480c4034058400d120070a9580f11602080aa41582d20030f00740020407030f900014225004440c08810010444d461200e00021040714450060320300c60190300d0302007170070440208821000341000070000d201801d0911075014414030380000e10310b00c0a0507000b0000702c02c81c0c188100c0f6034190540d0031250300d910300600e0540f4403d42c100b058a03d03d10907140d4211034102d60110034844907114192105810629050050074034801501c0c10b24007518180c803240000b58005180c09070301c1424204200d0301802114019155069640081c0d08161981044225204190b00600035a14008404000c0000c2c0c0c210860407030103003100605a4415440c50080420f00a0b100306030701c03186e00c07085121409001c2d0b0314941d485800782d00071501a800031040c4480729454280c058003606100400303100c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 318625179 1250 318623929 318623947
    0xf05120c06040311150a0b1005030f04060b060732060f0417040b1b01050705043008070c05030705030f101104080d02070302010201200d0f020d06060905090c 69
    0x26003034042c20040611081340059140381c00b0910624203009009a40c0c2c805c0c1d844c041070254081d06d8034072002842a007914180c084894021000d490290310300100380c451666a907600c62000f0b140b10f10040740d2210060248100180132002d41c00d000704950f816034040140948540401509851400070164029101b044042c030071810704154050b03000705040341c40a5141c1882c2c0b03494801d5400c5044100c82c0010100c0c0f001c140d1071070b82544d03000200001c0041d5919240212441d02941c022082c0f5140d200c00d41111500480103c140d03040300c3e40c0703041c000000841d40e40d80f009500101c002c5030300038814241002546010b000c9a001020190050040c1d4810000131b130740c494480980580d0995928868011010403480c00e54003e024400111000d4546050b0013a68450007844201e0040d0300b04100c1c2c0d441c4c1800da041c8200c403000020b50301b9080555a076103c00c007408050380400c256a0b428003c0814012107401640300900e810f40301c901c0214100020301c070450300001e100e080c5001e070800c00418 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 318626429 1250 318625179 318625183
    0x2004020903100c05190206010302091602060a11040e04060e070504050c071b05030f030c06070f0905100e090112051e060103021e03010f0624140a0302040801090f05120c 74
    0x41c50b01c41a520015144850440580b0b803400f401d08144240e00b100344408228540024185060780c1c0201d402038181c0e0340fa524445080c0d84072514090058001d81e011440300740c1380c0d8000d00c01182c4034245050802d074840c1c10007812a038080300e01b40d4180d600c1c0c00745514240f40621400d0060b00086e04c09000902e813441c08000c0ca403003000307802030110102e02d40c10b5680e00003d468501c040c003070003016144121b42d02202156650840380c0b01186501074203010410340d50056403000100d40d51900c92041d4140f0780000c00441c681c0d01000701c41480351030b000509065940300d0085000e4000700000240c8120141040c1e481c0290204030030360304400d2511020101840000c3d090704503030f41124501e0340c25094114000c102c0100c0d0808941541c240000c004105800307822000a440c10304220044024513510100440400c50b24144041074180143c2c841100c804002011000820305000d4030b040d80e51081142140c0b00c4480a40d4400307010300c1040100281030002803615004111a28200000d8041003a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 318627679 1250 318626429 318626443
    0x15030504060c17011403120d0c09060c030207050909010f060801152709030c050f030a0e030c1318020316030303050c281b0308060907032d0605060301032004020903 72
    0xb17071a6802080c8a141d54200610107200311500c40807a00d8042c422440006040d00207107400115449450120725988501320307641e0401d415070b00800c800d924181c00e0000805014107000b519549821030400700c00d015008a000a00e184000011001c9121010000c4002d86030041260441c0c00044640f15140007100b40d0040200810001081d000c50701d020384280c0308480c0028143d005007403030142d41c588044050031910070345444070805010305004064a13400852001a40101915110304500400d540416420805410110561010740d0002460030b4050b10381e0b5200e480c41c1c49014010540d05002c1c9541001403140c505080008a00410710703510a40110300c0e034400d0451508000c003604c1044120700c00c00c2c1d0400311141c0c3c030307646080080913168100c880a010300351080110b40e00b00d1082c81005010000082c020503011100300381c1c562143c1801d0300240307200c1e03103902d804078441d40d034000194000d5204048100070201c0600a004400a000354a6403040344103009000c1141c40100c0c145c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 318628929 1250 318627679 318627689
    0x5240d020a17070c050706030635030d06090b09041e0201090f0e040308090c0604030b1008060705270901290c010c02010f230403050415030504060c1701 67
    0x250300c1d58242041200c00c034103180c501a2046060000340f0080e82c0c1c01203aa41d420501a00940c1d03000d50302c03818181c06669943c45100003203c09200780160080e658a03048e040250491004a084080c4c92182c0349103810840c00e583d40140e80780d60400010700389214211401c4401c0d5031b000c90502d815220484d4150545400c5000d00d910030008604581c480e004001c0580b0b580c3c0c081242d402e45950050f80c500c281120210086954900410411000060352140180303004044034034240c190350f00d80910070005010031808002c0d580b0040b494100900c282440349400f99142d5860f568518100c0755041413005c01125108801d2075051000c2c0c603141c60840c1074501041300e001d4403641c08626040a124003031032070080000c010035101402101900003144040d019070081c00040e000541400403100920341e00f1125001c01c004100c1420100c3c0c401a90043c0681410741c145036890200703884454611a0602c0040e50710000c020804c0124841c80313a10310600d1a20030207407030086070300391403050060040c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 318630179 1250 318628929 318628931
    0xc1110200d020d020406030e010b04141506070803150307060c020a030308070c0516091a0901141903030201051b07200f120a0215180d0c0e1005240d 65
    0x4550003441c295012121940714000c42150340e2591501d0060040040700c8501c810765003030030b42c072980074903140c010704043c03184090440001d5190780b001503150410f5005015040b6409104040c04100c82c2c0003d907100790361000c1c00700d80110050b01010b04000d2260410700071300a801643c1c0d00580c071800c240343c051b6035041c00c102a440d200c0c0e01e01968080d8100304000c20324428018220015007021614000b1208011418443c141500f01d60b40048014005074039000b00d0208010014403040c20b440c2c0003042c40180401c4100440342050b000a100b00f0741098000d0b030b4660060080700340c0c50518a49441000014450a00c001343c0d40d141c1d100603000e0b1480003050400134460309250748544802181e0300000700880c0646510300c4c0000e8407507440c0d440a07482480b1a10307417450031340b51002c200d0300b4611044101c0030301c000700203040200d0043c42d4001651500c100b1035000c0f8a2444030b9a007035000d148807004000c6014a45000c001d906041c003107215021451060000006140d140141c43e408496244 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 318631429 1250 318630179 318630187
    0x20a0503070b0d05060a03050d020d09230f0a0e0a0e07050904120815040905070f06180603050c070804120204050c090d0b09030c16060306052d130c111020 68
    0x5c0041c803450126000900640180e800c00e00f2019000664814000c0094440a1040356540c0624100c0340942903d00e090900380c3c00600c1617841c103511030303440820f401040059555203520348985211821500b404180d9034510300280c008070100b00610051074100c0d0303003207418a0969aa20580901810039200340074962004c22490740045a05080c60b0b100a0000c116071131082c20483d07911415841000b500032560540031071168410b4125003242045024003000792403a0000803070080070300030210301c42c0620030310071040083c1203030340104014043d0291144d0118a5070041004441d4041e1558249002c20030000010b40c07264096150610341001c4070303460303079510a20101c0c08d5103e13089558600b406808201000d24003000e6081058502d0703503034108441501c96003481101c1c561341140000b266000e009418440200105450048002030042410703091528940b0003510070541b400404190620200107211301c042003d1804280155024410f4081050a46a4042c203106020201d014001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 318632679 1250 318631429 318631441
    0x10509040c12110409060b030412140d0204060f0f0c020907050c03070204050f010303080a0c021c0e030601090204140904020603072f100f0219030b04060b16020a0503070b0d05 77
    0x7400400ba401001000d100419800d41600030319409401541400d500d81034000c520310903a03d043e241301d16030100c510600c2d01c00c850f000752a45102034114841030502080340f6a00701c0d0403800034100500094488009262011402801e803c05d104101d00400104400d1a00540d40d01c2910070341004d042d00700300f507880d40b0083d000d80c11442400ca02030342040c00c1406101100c8844811b4604036030096480031480d881d41c0c070440007038502d01085c0d00c0040e442481c40c82c844840741c10b001044031490b414031003151404c3d0390100e401d20209a00000318203602290800c105804100242000881200c161505261540c006a00da000141c80c0e201003104901070540f01449081070000300807111100031700e0142403c084a5600d004101c0213511590600c01813a60303c5110303000b40c1e0101c81221001c80c1c00400c2081084000700111010113a2194803204001402000040203200141c103900555140c064280140416240640c1c401406603000b0036041041c924070f10144c43d1803003c0301c80007080d0750b05e4071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 318633929 1250 318632679 318632687
    0xd0e0906060d0e0307230c010e0a1e06080903090d061d0f01050121050606010804170c1c0e010c03030911040c0809150610050c01060e070f08060d02010509040c 70
    0x442c1d007405030034605001c83d249800b001019241c040c1c401d0b001c04228203804501c82c884180001d103025403a0f030142d6102803556000d030030340103087c0c8809080702690564840305514102200c05010301c0308007441d24103000031607104004644c80400080110f2401c850040031a0f2511180c540103089603070b80e0071125014039110301d461507604110710100c038030001080311701c0c50003411300b881128418601f40c18004d00005840d18004c040c1500304025214540d2844019601c600c0f0003032003100c0880300031403542003881c415805025146d9099006142400d0582c42d5000b5154028891b40d0521200100542d031983c0d00915584c2155854500819600e4003441c0004107407010800c40ba501904203c410705a1651060440d4483c5280e081243e50710780560300760300c4020200b5500980c010a0034441030b56258083c42c000e00c9210700080001030915505e40181540d181c0540c2c0040000300c0c41e03049080360543c840102c5400010840340c007a600c205a0b80047c206c0d200307000c20340d401b072a2a0700540d1b00351401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 318635179 1250 318633929 318633937
    0x106050102160b3f0f0105061611030d03090b010801021305010c0807080a0c03030b040507050a1d030601140108013002031507110709060b0d0b0a0f0b030103030f020d0e090606 77
    0x1c85407000208100244c0600004203c03008004400e401001800700368250580c03074102c50010f4821490000480e107140101e04c00045e00b6521581e1900f8000d25540701000002501e078090790700020145071500d40f80c5810a8107a01030001c684c0103014084113103002c001030104803402404c02804c1403803145007510701fa00840c00054004503010900d0b1007280d070000320840d145446503070104a5420341d1010402250001d4840b007001420600460010a000b520000c1001c0314040e00844049501d600003072800d04240c00c00031022244400d006d0441d604000700705d01400d8055101a05030070640450480000d0304a50003081c9444500c4d901c0c29901c051107946100380c1c2c1a6413000c01481c0c41c2001800c100041505103610b03200d900b034002100e044c1c42c4200c50a55010381c8505191800101002018144050320141d026141030400a182c0f40001300c0340c00140104d4214545961550a01404501741c2111540a64010548405016520243c60301c407501d01128000002d032140d201003402805 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 318636429 1250 318635179 318635227
    0xe0d0501050406020316020d08010902130e04080405040b06121609080327060903060604020d02040e0a0c1803030e041104051207030b091212090a0b1303020106050102160b 75
    0x40707404103000600201d03030000d41c404d48885c8180b2010030304032041242d55110a40c0b16400203903401c4018055481c20ba0010103401c031388010405c40c0031b0340b100808200b001041c0c80880b4000c2000804104070304042c083e0610b145003c84843d0b0411207420040c40e08000c4c02458080034802400c14440c1c0c5601403036041024029000c1100d4640c074030650b03500c0301c85a020224080d0011800a60062480c3c40c030100c0d962208064080c0c681c1340c4451040c8006900195540a0080d0702444045180071030025454414005020b01151000701c0310000360a6440705901c2c00b00050080000b400801d8101151440d452426180010007006503086400107000e40d0700400e40c0b100012011500130300303000450074141d0740640102081d82d00e4074056643e40e0204041c000f0612281402a06100799201c900d056004103800156030170350616950b070402c0b010003100c084100780c25009450042c5a4244620400340500780020205841840c0840c01000c0c030b944500d80901400241a0700702c01c00386650b46486007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 318637679 1250 318636429 318636431
    0x7050f04060201140a2708071a041a010303051c1b020a0302011a030604021003060b030f04110405010803030a020703031401080708100b0d02100203130b0d0f0b0f010e0d0501 76
    0xea00d03044000d02034001841000d00c0c058000001ca6050805442049415030700118400f0807450400312041507040040741c2580c5071700c070030712080c0041020650019080c60300080990b0052400e80780055248905424421041007080014400241c100046908800300094040300c25699201100c014059555490014070044054040c2080d00000c14810580c4030707800903c8564810401c8890070000b03109402e9140d8005c101040150514825100407070030540f03008141c8948503814010141c4c400e456014101260342e04000520040e41c82040c1c081408440034003480d4504a48207980740000303003500d8112940015464100360090b0f0154010b000d00c1e0180061035a50b030038403c2d48603141c40c40b07408294090308035600181c814500c100254400020326079014240c5a4090120000c641c0090300d0170351104018040c8141044100503000b0210300c1a045d42d075100600c0508260b81b41480185121404d004020111742d503040b00340f0b0045802840c1c008046820600021a611022003002d0081c0d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 318638929 1250 318637679 318637687
    0xa020c0109050f010f0e0a0b070c060e160501020102090a0308160c14010e15030403120b041a04060f1d0a110703030213060903120818160305160b1207050f 68
    0x2c80480d069541d0070304031000708407203068101c000060391148020800240c06c01c040140005034034400300754008803946405007004641da51148221410010100d00c3c9504c40d100324155065500e1400000d04420310003035040040c46000310f440908503010080000d076020400c091103107480c140140340340c0d0704089d02c1d00c031407640c070702608003501c40101c0c01e540018800340d4824681d0400001d030802403010007103403510710740d5507482c1220100100d1103a022540e440c0c00141e1003503074803800742c030700f6610300950054000c8d030308441004201c40703507a803001507110b0703d0100800400949840c4130414401001000c0c20390794031110a5801000030030031581d413190b000325070f81d010f1591690191955000c041c3c01c50203103d46880058810601c1c0340310003030454500c0510501d04511440e407a0b074104280500c003202066544591900341802001d80c10f41506101200f04180007040050390101d110215504800504080003a0078034851000703117641030707040c200c00300e00414400e908036080d11003042203294407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 318640179 1250 318638929 318638933
    0x150f0a09020417010203090a080c010f050f0a0608010c021911060a2001091203020705012a03060b040b0901050c0733020d2f0601080724020c01080a020c0109 69
    0x7904140109a41003101c0301100c80c500205200703ca00072509000200505101d40c1d0302c0749c003180d011481d249950b540751013201e0f25100d034601501c2d00841542640180500d4044541c000711051680652010780c10648a003129a4000c038101280fa41d00002c030546000940c241085202143c43d26140c11030400180c400c0740343c0c0e0001076100381401d40700d030030401210045800c2c1d080c0c42c0100f402621301d042948207017894900a6000381406803041c0c0000ca143c09188071541d1114204401307500b0821396190b00d2032100355040c411000a0b0040343c1295060604016001800380101004d6038144000001d008991010400070b21004105a4040640c14000d54002d96856090304400c1546410401d44642e86240041070700304504c00303265108160940310b52917a2443c41c40103090f802e004000c40c0020b24410030203110300c4d4041c10074600104021494080d0012103255090104c86004001000035003036140e010491002c182070900e0004100d0b20780300383c044001d115154084000358a4500c1d0142 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 318641429 1250 318640179 318640181
    0x2031b0105090f03130501030f150306020306030106050405011805070215160e060a23070b090705010206090d0804110114072004060e0402060307111009020a09020c06150f0a09 77
    0x101c5040c582e410b4414401e0b185840640e2030199541507407401300946424401c0394406d501c40d0554111040012840700d82d0a540d0304421403090704251242500002000701c1b505003401407100501003a03404100c0b07036140103185200060901c0c402d03d807190712103001c0303404d40c0e1081100301d41c280e00351307039070070802c1d09141d0f80c520300c400d08074040c50000c6450500028a01c1c600141519007140c044e8503040315072103242806540503e285030101002e444180103820104044410301c1d44244501e0f40104480381c107000c00a403401e00c004212182e5644200baa504583ea1322000b09900f0035840b40c0103c3c2d00c0e0602d800180c41c1704518144d2040456000b1401d2010b00403107007400c845e03544005001c05c0d003c5001c00180700c1a96543c3c06402501c1c100c440c0400c0043c240f000055500540f545403100050b0310015003181006103e110302d98009450749186070541c80d11b0107140c1c0080c0b2103600304525000402c0011070310b0301001841c1c0d6981214141241205441c0c5641129040500411030580b90b40c4a540c1d00c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 318642679 1250 318641429 318641431
    0x1090906320a0c050307140c0a0303020d1d0a06020a0c0b0c07060614030d1409090907060225060809070509071107050307030203071e081005041118010b070302031b0105 74
    0x188140100c1c0d001c9400041a4407440780d604140795511440d56071400b0055031590049005a0700080b401c2225680006090000c440910b121365000b607900c0b040200700c00c080c1c0359106642020113110440b01c020910700021441c80065100c040980c99840c4690181d03407144100c1c001608001f00c41041000c803c00c541c0041c01107901c00c50007005655142d80d0440d01c0c096031840c4142e010740c000c0d402505810301888040350003a1005d0030707483c9810700c0c000103d1182c4100350b860800d03075409550180800c41d0140440f090b0741915022540b80003000480c07440b8508050300c215001d100e1007202103104507a060001201a2501800041141c209407400070b00b4480072031140720703280c043d4440204444c0350210300c840c01c4a400800902d08141000001051060400610b444e146a58140003c8090b410300c109601c040703045030000303060b00e002c1c240030300300000c01c100b8036103d0340a40303c20107480c1e280c111140303066400b284d0885860b0692032809a00e5445210004100e0b1031407543d0350403500005420372 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 318643929 1250 318642679 318642761
    0x6040b0702090f0702060106230d14011a030f1801110d060501050403051002090120010b010f1e05180316080f0d0f05160204050a06060305160801090906 67
    0x401c80603554080461003c480a590580050b04910010052140b0500d05854222185401a01c00140e405c0680001c0d07071290407090911925982d0700a01d1060800203103004217920104041800c0000c07401c080103100040140031051920004100054001d000c44a20081c201c4005c004880741c039050000706422101c1c803504214100a004a041c1d40301c0c0b0261003c40364010002e10000d001e00c2d903560040e4000c0c00d050340c10810412400d0350081c1c01d010a11a8100350f000000500a80142c001400c40c0e100403400e400740404221040702c0e41034090b4030001c070308a841c80c000d43c940726400e00c108425800700713110130ba0521840b00c2070060300300c20b15000340480350840210b91742440b40a109580b2102c56050890200c2d80c5480d4a000781c034082d400034800d242c5001d50740315959401c0c1c2d00107421504203a0305041816079980c42408426094441c464200141040c1c01010800f26500144101814000e841010380c44052103400c00c40710384c00058251140400b90b8003e09036031100c101c40303c0c3da58540 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 318645179 1250 318643929 318643939
    0x4181415031c0c0b060d020306180c0906100e030102041a040819030203070b0c0715050f06120a110d17071e0b2e0609052b140c06040b0702 61
    0x200480041001d00d0031140740415484501101040d44c5508004510050400345c02c4001c1d10791120040e5010b100f1140305401c40f03070000400303010680c06245840b500d136191700d0080d1914414890240c0c1c1e90211b40680c81c03410314000200341d20142c04207002e400740f5403000b40d9071021601c11030749a0b040140031b8426903110200300e13040c1400a0900e44203044a43c040030b00540c004204610114180e81038055110615546151030700240359101603080c00201c400d603c90550341c07001c2c00503000c41020503940007601103a010700c10a40b492022030320f4840c52000200200383c1100c02c00800e4944270700c0062141c0d0807160501e4640008503036010b40d03903c958001c42c0c2448400c100407241d5040c2d00040040240c2210741c02c121030350b039000072000c41e50203643d9203130300c1c8542a40c071012128a0b1444650241a1503501c201d01285030806120400403104542c404101f0300c0500b4048a41d4513194554865400854a417041070380e18510034109007425030019000500040d0100f5034410300d400412615201782e076 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 318646429 1250 318645179 318645193
    0x8030301090209190e0c070c150302071209151d040e0303040c0603060f0b0702010e0d030915030608030d0b120a03090e090f06011e050405010e090105011502030418141503 75
    0x300013144601c18043c50062041120205510908490150000a101c2d081c881b8049032108144000c00500e0540b100000f6000070303800d001c118650003080c03c08011400c0c041c2c0418200034074810710040ca90009401c00c103101410580500680d00c40056010000d4820003941098041c2291654422101600d01803040c1c04009201c5100b031203288110b5010101011040b0f060881c1e0381d0301c81e40507a00980c10041c01c042036845a80e1104100c01c002c5107e42c8540b2451458200681c001c108001585401d040ca0950b04010002000c4121150394260500008011010070300103140c1d02101c040012452152400220401d1340080148041e144001040b0000e1f54a04010030342e141b200c0701c6140340c141c2001004125951074a0700001d5040c202d40030348000c850300c0c0d0000c2021104260f002d02004d100c40001e01014480a1003543d001d0a06426203508902c1e00c480d010355a44a24030078440301e00340245d00d03100be0340d025502281001030038405001c5142801c448280d0001884c10300c0903c02d000b020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 318647679 1250 318646429 318646459
    0x9070e010912062f0708070309050603240103110313240b150a0f18120803040213140c07020d0605010b0705011401062307080a120e01050126010608030301090209 71
    0x4000000014407075600a481c10170300360b41c2c81c41d041d040050114288114500045115510507001e1442200c55401c4800c0c1c101200266044002c10f01e5001410b05240100300b00340ea0810780101c0f0740c803240104641e1f103692910f1030b2940108640c260100100a00404000c06040081e003002210040846140000040000f44441305100b1400c80c43c000c00d034409404501940104845400201d20608a00005a840002d800d03602a8060200c540510000811045103003860321040f02843c1c7c1c81c010004940030031143d0480702c00240c42125000408906c5401710359510355059001980244184400d580d00c0754110016040000111a15420070400000f0758010080e1207040720740d02d80c0c500071010207140c0445ca4041d0b020f90982000b003001c00074640441c0c6460001d25004406036160b0004508865040701251700b106480d82850341050b0042241003401d01c41215140380c4101080808450800214014241a4042101800044000a04002741d075015003040d81c0c058500c0c0b10703a21555 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 318648929 1250 318647679 318647741
    0x507140c2104090c0e0d03110f03040b040509010b0403020d1e060603060b0310150501050f090d08040303080c0309100507110d05040812040b031503070905040f1202010b09070e01091206 81
    0x1a1102581000800d00e00c0400312344501c41905801d00e980e419070303000d4500e000006046034011b81062082c4100098104002d06091400b24010078215a00074149400e56000a82d0407110171000b03069181c461030440680e000710012b2000d40e41c0d0001c170400c01c90742c2d030745004000381c903640e010780d0300c40e0103001e840320a13100e154012058048209082801058103003001507038036030401100782d00001824090040d040d120300a04140490291030000d0704c5034911f1500904103440100f24800094040c000c4c070010100c00240b0101c04815400080b5071540c4041d02124609036174041c400c810300c910806500000e0f04076006200b5180c0d10400d079541203c2818003c02d13140b180340f050104013841080007416000003038a00c1000c0300b200a080d01c0403d56030f440c4000a449060b10250b5a4400241e105410000e4400b012000780e11140003d100c0310382d00c000000c040d02d00042c02c10b401d1200305040101c441e8490108003010f450341292040041600c2d052103001000400f00300300c41640d080c4c480c01441612 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 318650179 1250 318648929 318648947
    0x3101e0501120b09150f0c070803040c0f0b040e01151e080a0e0304050d0b07050f1803010b0405040f140709022109120d0207081224040507140c2104090c 67
    0x405c01c81c510143c4949110b619110f5001b004003034420740c107009000000f040721008500590203940034031300d12400c107482000103000da980508541c2204000c108041d000c040c0401e81151103100c11002403100300c80081d2210350501e800103250f907030301d800003801246d0080b8003107001754603601c801c010003404107402a540f031084ac042e2680c03056488500f280011030107040f003540110b45180103402d21240c5030031410071b6000201070940e040005000110107080911900003049000c860511260400d500c400d0200704030581c001e07080c080113804001b420101041304000410300880115680e0032146400b14400305545aa841000c5400c404182450b000090304203600c00c10000d85442c0c200d505d10818001c0d030202800312000d400c140400d030000d400e0345a01031b125041984041140c03080301c0b07803d08915910311050760722036454002404076181d800400000c0b0998004100340d074603448030380054940901110742001000b59240d2666418020901400490b54008418800b50704610419952015 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 318651429 1250 318650179 318650203
    0x9020d02072a0936030215071b0507030503030702030403021815011b17190f020c011d03030301140a0b0f07150b0a0608090c010203070203101e0501120b09 68
    0x60110810301500e105903000c158803000c41040203042c1c019600326a50701c603d1960b8040070b1007035501404014990181f1a0aa42c0309849056010782d00d45000c0180a44100413a04140504855014010440200248030156402400700c0e9200d00d08400029501c2e40117000890281045011204460190111a5002e5001c030080c0410780403c4200443e01082250b0200054030454485600490903503000c4018603003046001070350702d1469500400700e64510900340003c00044e82d6241700095404100300307402c0003091a008041c02d50040b0b91031003c104411f4a00e600d800700000020b01c0718503085207010080425586070f4041c9a0b201c0307040180d401350f05188503a0034410044000003c44803401c101c04886004c07000034980d000503000c1180b04000740c02a0000c070300c004d001d001500804100c1101e16050920043d403900c0a16408039846010100e265210251104050103000300c2d10781c120107010421240c02c100c65079503801e188149500c1d00c2d400b0b4881d8640700303001c50581000400d1914100c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 318652679 1250 318651429 318651503
    0xc0102150402100909020d02030612030a0c12020f10091e030903080702060c0105040b0a05090115050d061b030204140d110d150c030203010503010c0e150f0409020d0207 74
    0xd41c40d0340078042e00d090f58104801c100907110f040030624910750310141c40c1c4001210001a00c91a0850505c001503001802741e5a007035105001030700585610841500000c1e50201c186041829041c1040c0d00d0030b40440401c0109016404022004070410ba2003040550300422592409517034860304400324556142c0d0140c0010980e85041c00400c2c0104010161140302034460ba150004444506003165000d54048402402c080113000c00030f80c0740d000c1d003504401178a00810100320038540e00022120701e0b1107498018000c0500d05c10501010358403124101c80d0302486090ba07600c9030b800040081d4040e0044070300342c1d112001c0849150408410107140e1560014441100e12414020000456150a0102c3d18242041c00494491034039004500c0c002c15543c60241c0c40e0f5041c0310401d403e5512400c1514100100306050114607a6052514a010021490155030700c0b801d1141d210301520581e0402820079000045629010009500030400c1c5409010200e12102103070400c00b402c440f4034903c6240361 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 318653929 1250 318652679 318652681
    0x20a0e030d03020f4e0c04301e060507020705150706060f091a0603161b0203030a120b0a080c0f03100513020a0905161b0f0b06030c010215 61
    0x100000020038016402c0114120416070030140c549960b201805d2000410210303641207052501e0341e918500303800140d8020203908043c00c01c042d503070007039031802d58a100700c10020503581002d43c8164074408030141c020007d020350851980010745e0070b40311902c08441907890480001c1d500c80c4003150600076103a004010032001b0030707038420802c41500320610640d900c41d0344020010b41d400b5100746200080610043c0424184da0b40100741980040d204451802103100300104107981140c070080884403031590401c4901250301c0340d400300c40c50196030740094061200103500072070180c010a907004200345d03214041c0440c107140300c2030050000e114412040160b0051546800c1c500e0103c2c03081c0020200a0101c804e1188121400410b42ea4241c0b1042c83c01c10346400b1120640c00c0c0755491002a0150400030302150038080160000740d400c5090060030400801f440c003003041401703100213403065007003200b0320a00306860900c0c10502c0410b51300e1500c20701c1009182c078003650010a054244410454140300a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 318655179 1250 318653929 318653947
    0x7030804020111011b030c09060311120c0f0c16090e150702030c01050a090209010b0406120c05210604050907030506010e070306080d020606010e0f13090312020a0e030d03020f 77
    0x141d6034601d0a5640c195488984102803115903405c40d4401d81d800b5900843c10b0107590f4400f1704442c1c4c042d00700504050800e20703603800400524003119025210700241d000070769200c036054a0340740a002c3c00d1a09082c00056080d6a007070300054072262507075046111440150395580f03202d08499550700d4850454018120034021005260b81a550055560060341e240504251055003103410071203582c43d001c1c2e90303180d10788103505140e003200c1c0c0503004091401d4502410148050078080035800b10780e400c0c680f00d0b044140218800da0541e42805502000003030300c18250019941d085500312800d601940c54400000e403040000502c1001302e80d0030201510701c0e41d081030020b04000c200208050b06160301d03080c0c0043c0d014010460710f03000e0301040d8040c1841b03091940006008c0404003560070705c6068180b48248055403034086001d284002c81c1d80000f04401c45260a07241c044084c0600c1c1c013164408a1410101c1d0341150f0340352420a0f0841c243c44401030030030815400c9000340300358070400440900950074 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 318656429 1250 318655179 318655187
    0x2e0305060f0a0e1008010b0108040609050c040207111504060509010c11150a021507090b0d0b150703090b0310060813021e03010533060405041a1005070308040201 71
    0x500104060140340030007003040080b580c460819030184200f1030010040107a41c000f01c0c0080009000c8001c000d120400709480024001800608060800c50342c8052440c1045002c0001561920021b0400d6481c0c02c00d40c01d01c000580350301d4020501900c074213940d0210348100c10044405540d05602c6040c01e08401000446e61300224920844d10141a05030140300342e62041e14030311000e0301c900c4e1040c1d40d031040010020300f001d08900c2e005522000b114140040c03990801210760554504602c1d45896220030903010303000d40850940c55412010200fa60341d0107503100401458410300070740b51814003582d02e03c892043c0b440102d40700080c500c00d5640621429208408490700418110000c060500d0690009540c9484001d4800460090384201018605007805507652182d161404400700d07400380b0f0012140c080480d80f603810740004881c40320009036a8101a10080c00300a0b0007000500c3d40b0601d40c1d51400c121050092141410701225044035209104840c0c40c1545582c45010a0b2142e0f40152 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 318657679 1250 318656429 318656431
    0x30302100b150c010509190803072601030c060f080118150305120301090b010e100302090d06150311090408092101140601080108010e150601030902060a02010b2e0305 73
    0x9644102210344000340c0b2100301000c2c050b00304500000044500b040346081e450300704040340030039120301220f00003000b280d82c600649501c00e0485c1482403007804000305500540c02000c000c00c0e62065404008001e001d2840c00030760a0b1085a15140042c00442e601515021000d110b50103051541d03600e4108020415001480101540740e40d8003000d586a80d2414280f6905580c90954004040010413028205000e0308560100a00300102c41c102c2030004260313070140b41102d11040c0b640000d0183d1481d200c808040d02400d40044080042000c8014034840120507480162108524500c842190303151005900303010701d501061151518059900f40003154021143c40c00c0701040840200c0303001042030140c0b8808041c43d0b00c410a4504e005000942000410303080040941c0c500440ca18003000001046109030642c0104400c2e80c0c0e42d41d100407005450a420000e401a202090701154150150402e8000080c12980e01c00a85008060544585e050f440d503004080c540340e04e51b000c11030082d4005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 318658929 1250 318657679 318657701
    0x103060216021512060904020102300a091401020f0a03141c02031905061815190f14010e0609190609050112020703020606270708061002060103030210 66
    0x18450580e655000101001144020320f2807034000040d44016001c0c454a580e17038417030320455001380c6904260700001c2d9508000b070f8603540c042d20815031306251010103400d15035240c030f40d100d2181e40d11109038000601b1211148a0305207902c1300304035180490f42c008110f07803200301a01801402803000340d490845160584212805109a08100d401e00303003441c80c0c1090300310302580e200c00742e900d042c0307489508030511468011101c560f2606040c401c56503140d8014110301308480340484044c1d203549104d40700500c0a0809031740e1020344041000350550b803001c000c00803688011200f650140e0742d0021a0040c1c4241e42e036042c000790a03c01010041d00d0640007500c4c0d4894050944102d02d2a042205d0304c0104c1c8a4102e48081000410108495a444850344290380104007041d810003c80c2e41d0085d42d2080041c24444c8990100829044200d501c04684482c041d80000c006401d0300b040704005d48512002e540c030ba8091070000036401841e6000194a078100c9905500601880c000d045000006064003610 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 318660179 1250 318658929 318658957
    0x1050d0305070305041e180605091803120403030605011b0807120c06060303030204150e0303040b030705120103060606081f0e06010c06050a0b0906031501140f030d020706080109060e01030602 84
    0x1001c00e00d0141e40540c005459030041921b402c0d28142101089150101144403140354140081800700307440b46200c43ea0410401c04610b80f4100318000060f0460103180c5203100840740030820002496456006282141d4080cac0b1540981880c09000401b42d503403000029142c0081040078100042000e8000f484005035031802d2078628003240e844000303945140c0d20560020381c0204081c480682e9000c400010b1080e0b904181c1d000641d407501090302da000c0e0784281d0310800404400150f44900a0088412001e203618800c0425a16860400000c09442c001c3c80d0001d540c840c00158405011300403003100c01001d40302c2c00c400500c2c1011140503050001c040c0f5041000d07c10712a8000b610741e0140303c1c003c194505000c2800c900380c000740440c00340c000f0b020324805c0d402509011002d0010011850540c3c100e4242290203900810224241c0c1d001c5141e01c5801d031140704c03030290800d039000c00d505043e10384559900000e40d0740c1d02450003d9400034054910348001540c01000050f41e2540184005989000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 318661429 1250 318660179 318660187
    0x302030f070204230a0e03130308090402040e0c0a0e010e011715040e0312100b190c0c030f02040c02010501211403121e0f0f042105090406050901050d0305070305 71
    0x91984c000c40a8030038a10105031010148a03d04003503025408000101c1001941084020303a014070f038503580340c440609054000240c81180391100d80444028200c26150900e0710b00381404580781d264054084d103c0080c800d55034100d003d61080c2c23142201028140e40e001b20400c51f6a40700d40074154058211003547e0886030a610711619940152038110001c00055500e81e20203010703804c4101401403050515044c110020300c0603014007019076022215200ba4059028619003050707a035081d50020140c04c3c0660400004100718580ea0244002071082d9814061141c2034001030f420394030f0a00405601c1d0f403107441810407090707155911107500c60043c0e03000500d100a981c00c41d4116030200e101d4100b4521a9000c0003d10301441d08601104580300300c503000b4070325003c40780010b0180050103070202103020402007800d001c5c54107200c2c001620f802c104643c600d9200c400107080b0340c0c00203e019000d00e080c454009018a419000c0c18104c03800644012203042c0300303070360407103440e032000101301c0c28010280 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 318662679 1250 318661429 318661451
    0x5010b121302100309061409070e070513141905240f0412050f070305100b06130b030717090a030c0201020a050f1525050c010b030a0605061009030302030f070204 71
    0x100301d90001c2c10b5280002e41040a0501d581502c000800100c0031f00303003407400d100300708000107000b0b000c55000400704101526140001c481d0b038802c1c081d0302180390400c41000300d0741d10429480102404021101051894000b80700e008040c03d161040c40c0d8000203180304040e041c9010300708140448210b4000c00d00e404403080c200d036072a41158000d05e205502888031102044030801040031044800c02c000e0035500d18580e2940d070b6862410360b00840c030a480f000180c0c0181c40718070a4507910944890790b00180c07500c0700f072801c0042d0021950803001500912950301440e00c0c00c0d444a0060030203401912aa840d180c40c1074498000d10301c0100c1c118401ca45410020502c103101046200c0326010240072400c12040c4034020680d0090580b02d011325521040315454000c0301003111500e40c0c64207006403500703c115000c50040403460401c075018040c0542080c2003144960200e1700c20341c81124504240c407c0c49000301d4800c00c031408000e0242e407080146070340e02104000685103851006002080c80303108a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 318663929 1250 318662679 318662689
    0x60a14060d0e07030326060409080903010e0c030106090c0c110105090303030a06090c0509030c211504020301111e0715020406020604122609100e070303030f05010b121302 75
    0x2054241083e08051002d10805a102561031507004038900e841041043c2607140c3c850302c110181040c2c3c4903d071b5442c442c1c0200700025058401a00c0000c000f045103d48404010752600035814000b807081d480d2000205a005692043c4080f84580e80c1d64607035020020b0381c3e8642001c0700c01900c036040c0031044c845001603540030030045104044800e0b021401c0d51410301900c082d52040142036050081c180000503954500090401d6200030440f5224120040354101121351294940112054041d881000c4000404040d000d40510300c00e07002005005520150070030707940240d00341c3c0071000c0d44085168485641c02c4014208082c0039000310300c1c5031140c0345000412a400340e804200543c0008042206001001c804050109540d0401c0071404003e203100312001d0a0340c0c40c0500c682c3c0060000b09484c0d1008103e502c4e0003226030003040001c981042d41780c0303594803038601c0114006424072001806220031401045d040f1418445002d0528080404d103140800300282610315841085014a000d655a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 318665179 1250 318663929 318663941
    0x6030106050a080d09060813020105211608010506040e2814070e030706050d111e120901020a1b02180103060614030a05030a03020a140c061509060a14060d 68
    0xb03d00410f402a005000070700f44255952041090050b85000c01640080b0040c0c004041582440c00950781e28501d241000d41a140350402c03652502c155041108070130903055210310107a031b5510f072891160b80e42c00c01c121591146000300590103182d800402e031007034140450040c9403420803141e188590941e0407502d0488140740d54580b950103071303001030204168112444c120614070590142104a040c50f2001d04544602c000800b5126034611f01d190005150101b942c1111004038030300701e0303844039004400880d030304002d0651000c007a00802058a6481c14400c40c0c64008090300c4018980d03110000e07001d144140208144c3c0c000384a150283c00252503c00103030b010303620440d0000b81305410181000310340207450a440d03000c0d4dc0b1820181c2c020940010a40701414a1f520300947d607080010300c122a0740202d10324400d4a003002080f0f00c030f080400443c05034414043c40400440e1030150404009507c0c1c0151495900000245002d004800045507840000400540814900350b00f4910020440b00c1d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 318666429 1250 318665179 318665189
    0x402100c031413090e010b0f1e03100209030c1f0e0d06050a060305160305060c030901180f02090a060b0904050a110403030309150c1d0102101805061602070e06030106050a 75
    0x1043d00c406021000d041c4c4106a1003024050003040b03200d00c0c40010881d00c18080c223505200780d5a000002201c004212000401d088001c0c0c10b880c140c4d030311140418040d4002d8201c951090041810a100b64140690701d20600603d43c00e031000040700f081800e44e081d140c0c40c4a0160499280d401100204ea030768092a80540a9840000346403441c50820f0350502000030110b220714100b040003007010900016032180c01100000c14190303642c80c0c1307020050040c0f07078060700e00c0540542000f00b8000c2c440c42d11400c41c0c02c40c0c001c1d40d1021203540c9140b0f44004559460051042500041c007440142e4202648541d0b032280550300e0000c0c1da100107014416607504660700480c000b0f83c54900810412a0801c0c0c050f031100c1448000b48018070344036001410311129640d01c0d924040d2110065800346c1e108000c6e80d40a090900c20411929480b00c10b181c2030300d44081400c0e0303000c0c8070b8080841c003c8200380c64103614080d516800707400210b0a00402081580780034103060350540d200c1d4408109652501d00c8440145 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 318667679 1250 318666429 318666457
    0x2010e0a061e18140406030506090a06051b19030902041b0228031101020f0a030603020906010806060a0e0415060c0b010b0405010f03091a010f1403060402100c0314 72
    0x11402e000c2e01001d0889084004002d030b40540400581e9651a0a1083c0c5503008401c415861096001c10010700e01540041e00503c160014014410301c08140320708400d010358024002661011340c0c805000d03140188602e08400f003040245180e0b0003c2c010b03c20103403c5413038041054011034000a00341c2d090300d020310314440340c040c15840400d03404005030400d00c07800588084241082c086855200842c1803c0a01400301c901c04200c4401c4003941128004441190659160108180700074000c1001e030004a000c1c43c01200812030a40c00b4076070f490b00c50680200030a10f4505036504c21145145042000da801a490b0030ba842c2d26100352000040240c1784550725501804001d0408021004043e4070449a001c0c040009009a0760700448540d0004058200442c040c4240d01d842c0c42612060140300f1220408000042007030a40c40c440c11044482e0710300850a600740000415482d80c0c81507400035400072000000b200d2140c01115000b210500a003040090512000d00b503841a0f230104001e05042 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 318668929 1250 318667679 318667697
    0x80a0b030a030e1305010311210102120712020306210f0a050609151b0304141902010f0314011e12080408060c03040b0a0f151805010914070c02010e0a06 67
    0x542003130303640024003840185050049515603250700ea0603d0401080500031070039250300000d20101c509481900c405081c0c000c5540d100c0e900e941c7c8102d074005a408200041381822034113482440d40c020340c0e0092000600c18003212a0154032804284000c840b46900c074051425461061f040520103014030358010700c082c10303040c5403c08086080000010352707040402650410300030711031003024030751000b603c001d562140d403a192030815691090000c01000300610075045094074038414641680e0805100b0f07258000118044a030542c01c1e01c54001400e0010100c24004201c030401e0b568001ca003201103034001b242142d845000c5203022003140c0380b080c0c03400b01002504200c0e140c000c1264503405a6443c6299045080030b0b0340c2d84021003005000c1c0043e0341d40f01c044183d00030030b090b8000ea0340c81c001084051502c550f03c01a51405004440c1005031040c41c0900004070048203008403803040c130843c1510011541c810034203840107200a50141d040111030b440c030480356224a07050700b0140aa646603c01c1c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 318670179 1250 318668929 318668957
    0x8190c090803181f0c030e0301140106020307060608060c0a0e0a120b011701110f09120d0c110301060303091a070807150b12030d0c02100c08091b01020a03080a0b030a03 74
    0x4000441544d01d104103042c00d8a02855980440d04180e000c1d172520b8020892000c60000070301520302518400260641c4200020b0000e0b000002400c1803032165805000e6584d88009440d251841190b4001c9460010000714038190710410002003400301c02451000710b2912501a041e5212020108554198010340140034159030b0421600c0507814820007444008015403405e2549d016401d064040403601050401d5070765254614103980b50a8801120b620f04403c50008061000c1c445056420b100c146a10b82901d040601452042e0394143e15400801c0c0c0c58240d80c445079130b14000c550745040300c0c00c1c080c40e000500c01310003c2c840700f0f000780c4e1030700500070003000742804480f40d40048074400c5415840003c1d00407004029508180752003040040c04880201040c1c0c20328280c0000080141d10700302d545648035400003820b03030281914100315400705d601c0010045441403045402ca0160303000b5202e03040041d00c039540302d0b584007000200105540c40030201280ca451880300c8120041502e500200b14 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 318671429 1250 318670179 318670189
    0x702010e28211409011b020d02120303150901120b07050c01020711010801090b1e060705060c070309050102030a0c0b070302070f0f1518020d1b230108190c09080318 72
    0x903804950342402444d00c1c11040010b800a002c1c6441903680c02c4850b609801990b440b400405100794001e081e444010f0b050840d140e460f40c2c0215200c2c09504215642c01009050000810303051f86c0c010240e0614002054580d407181600090125042060410500d01d000c0800e0014081e098820900044080410400074000e0381050b0080e01d00e00b481c201e5040a640c0da00d07130600c1c0400b003200c40f100d0741c4201d1a01c04160f1901c10140090000d01c00c2800340007010310400011700801c1d01075542c40040300d88541c01281c8178401e0003800c0b130000352265131060106407071130f0710070780c100365103060040c0391010b6691084e100d5011a8402e50744000c0c05030002c400e00c0406580c52100395291101003001c95040d0351181c41490140c100a402104900300c1001040300c619030074a40c02501c00900342100c0e603a10001c8254000e040d40d0701c014401c6000b507183e07065000302d80260265007414001c5c1c151800d83c2c44070000800706ca0380e03041c040206030440010240014401001440e080c504c080103030a01090900c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 318672679 1250 318671429 318671447
    0xb040b01090c0813020f0406031a0a0603020d08030a1e020a020f03030705040b03061504180e0604080412020a05091812130b030a020d0c08040501050702010e2821 71
    0x407039a40d04003550340112651044009600c1541510410320181450010030b0880307070342d41c1049800c035151200120510246030b12515002c40c02190001c10b5566000741b141c292011844000d4024988003420f900141c0810061603004a0015001a003110b80b54561440c00700d044501d0b01c51a640003500880c560f50502407107821780d5851004601d5810550230085c410b2240f0b1194040004020007c0b962941e11007900d410891a0648641cad100c0d44c41e00e0140c5c2403003a040c407241a006107007562100b00141d01044040c41344c1d070007404450030326141c0826119895545041207900500310000170410b50b44034090240100d401d441e004112a01004c18649080b18070320700d81c0d40c500c10900ca481403074002c000100003034402c5c2000c42030726a11007810707041c0a809640e841c001d0301805c03d11080003417540a20705911a501910003803206032902c02d0113030700703d0b0010019003003181c0020312034a0114203064002201c0020400880004115680743e41180d0010212102b010046214130169600c1d803103545070f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 318673929 1250 318672679 318672689
    0xc030f03051612060806010305030c06011e0e090309090f06040b090c22080d0203070606050d0b06010503091006090c170f0a09020406051e041d0303151c0b040b01 71
    0x4000340d00b0401d9103100c1c0e4005641d448010010041d09180c4100001d03000360380240762450881c0ca007540c40e403038055125005945100346a102d10000042c1986181c41e00000b06d44005828841d40c030b0501750449110700c0c0080c20590107100822551b0b443d910740144103486400400040c18031802c18104110036504008040743c030541355039042c012076031881d40c100c40c4034450948220101400301103403c04950185c2e80000c0d200d0060f00e500d203a2180e0040000c02d081403264108205854894080040304440003102170700d69588072000502c10b5000d10011500045801c0490b00b1030031107180144140c55182e004a416030380c4a5182c5030102d50800b040d0300c14240108102442c40c54551214013450f18020814401e0796100c00700328041d912190311220207800050200c0700c0354447c0d030982a001000d82d8455134041ca180c0401d6400c1800c056400010342400d032340285255172101a041d01c640c162321715120740d102c0140108003e03402400350300520340034800d02080d1060718143c00d00031040300050f800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 318675179 1250 318673929 318673931
    0x41b03080909060f0607080a090608040f061a130f050109180b130206030708160212040b03180307140615102007120203010e0a02010228020406060c030f03 68
    0x6200148046003074803041442030b150000669144000903840c0900740c290701e030b00007200084a0b070a00001d0350040a40000c80d80b94002c803244e50703150460f1914030465028003007401805110000451940000c0e00d00a0419000421a483d1000047c10000400000350081e0307518104c00141007140e0044600400010304200010700301805843e00015680030000c215111120015021180071848420101d802038030043d280d250902001e0310110054680d480f42c18000b00b5000002c6100090b80303a104480514500e0426280a904007940d8001400000f004c4128045e5084155402c0016007034140c080e850000703400034a2078840e81000806410603546444503003900762251901480103104080928002002030118a001603840840c2c0c450201a4025241e0029544bc00c1e10103034800c03e80203c000308030410303040351103d80ea07a0071000000d015030800c0c1d00d0224150b80016100d01007040b80369994064600c181c1c00202103031096008000881c0c480d8404809150303101c2800410b045407410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 318676429 1250 318675179 318675233
    0x90111010b0a0b030a061a0901113c0a030804020a1d01120204020d052508090d27030302030307030e0105060a0504020a0e04060f05240904090c03051504 67
    0x704407605001e0003424143c140000c0803a10030204c2c0d6003c20000e001180705848905050703180507a076584454095400205d0324010203082d8180400c0c0c1035903020500190343d00c1032200c6650f400c0004410720016071a0780d40000d0f808030720760041c0701c0041054030980d6034039140d00c0e0500c100580700c8070319080540c039005407002d69403100c80e00005140c1903842c0001006040742d940e100141c0688620141304440720b08181c14400c8091030003140d000042c10059504da0050700000003201c0e059800c03103410400350300051900307421502a40100221002c0120500042d00c42000c00465101c4c00b030b8006c40060344000200b00d60075a061190f20782c00320720030009200c14100800000c01c0031103a0301580380b0640d070002d01a4617081c000c41006182210140c81409030955a11a83c0c075800d00785d00c103080c000c81101c800b01031801c20300d445000301500c112903071a051909071000d02c0002c01c55080c0846040c018002c0201c0801c40c204800d04202c1541030280480380b5081c036040b1200408000f5005001c61405 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 318677679 1250 318676429 318676451
    0x804050703060b040204180c0e030f1504080c06010803030708060d030e0f1f030914010203011212140f0309070b04060903030804050319050a0305060a030309091a1509011101 76
    0x108050040365080000840d41105890006001b44103d902903000c00d01588001070070b104041c0c10144180c8499101c002e0400413020605458800301d002c402200e0b04204004086115402461030b04140102016801d0618a00301d45107007600a030451031041c0d0002c401c200d040e59000c0b4205030b00c07407401c0d01d903901c00740344556018180000041c192480340b110302841c1000c944072401107800c030041307041040060031150003000d401000600e50949581030000c42684d02c002050080368101e440c01405a4082c01081d22140c19001020050301d04014400160040c040c00c0480900110144440000d0390b03820002e5040d4031302072159001e062814014401002040d4001030010b0882c0d0f01401c1c40d40580c0d5991410324218841c802007001100c84810388204030507804400317400d501e6440c0e1410800390316045e040011625240c0300c010b00243c8001c4042c081040b04c0e800c00c00c1da240c0301040c0c0c049180c5031140081c4403403520780d1003101c1d0b4001c003040000b05581e00c05011140c020242d002080140036038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 318678929 1250 318677679 318677683
    0x91b0503030406082e0609030c0504050c03040f15050406140702010e060610021212190905061501020c031b010f030e0a020f03030d060605120a0e1510080303040c080706080405 77
    0xf0000c43c070741080000005c0804104102020300780c0344621601c451a5212040540602c00a0001342c2c0c00030020103000c00c0d1350030140704050154140b060003504641d241c0e83d501c0103441100a00300d07401c44541c0040b811507009809841d014501c40c020100300c0c0000500d04810001c00200304504580c107040480880d94004101c950300410f048e03d0503c2040202c0006070f00c1c0402c20200701c00c03460000103004030321011084080f80902c6150000b047d4130304262550100740c500b50f56014210380c01a4000c9070600360701420030300c003145040c010b9840f02c1c1000300c00242440c04031081001141a581801c0001e582e100049445c1c0c0807079420100813a00c40000c1701c903a10301c41e80034028094800161413050564080013130312031103000c0319420700c0050344038500203000340c015580c1c5010b4044020302152800e1414003d440409440000501404111100f8100c00e1040505051010036000380081840c8606000540c800d60041881c2034182c0d242050380d0f440e0900b183d01ca00100304800c800e00c0005100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 318680179 1250 318678929 318678931
    0xa0b130e0a02270105030d05030a0f1b0f0e010c0b010b0304081c2705030a0806131103090f01060515071506080f070b16080f040504091b050303040608 66
    0x1000800612a4950010a440c14201d80c501960049000700d800b0007011098280500c0e0f40021854030b050390340e942045c90380e80c8101c524140c0c0481c00900004142200030b5004d85580000560081001085215a05a40034800940700009002202c00d0740c0d00540010041c60300303013001c4c42c019605020755180c0f029081c2040c0251404214004041028401e545040c3e0361412881d110901c0c40404801c4080c000b424100180340440021040c81c0701d800b404d903141d00c4100d64000026514003d10208201c8180e1001086941d000b464500c180d064090103204100068600a039019036900303148290f98039111068003c00c0751a8145442400151192520f0746207100c003101640303484011030301d8440226141c4200e44518240380103800200315100140b0344161030050f6096800d0b060f00c0d1003801c01188900000e12640c071303d00da04980c0000c1c04050042c02e120b64180e03801410f15441c1c00000c1c06407036902c002a1201c5002188501d0302d010f09101410043c203040380194a0700c3d01c3d0160180000030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 318681429 1250 318680179 318680209
    0x2a0d03030e0109020604060206010806070203120a0b1201060f03110901061704060b03191b080c100212070b010509010b0901140a0c140105010f0801021c090c09090f0204050a0b 77
    0x1485800d06007a4107025000400b0940c2d004000945030354440750000c0d03039200248500d65180c8a0000410b0b04c050022046865034529044055030300d079600765480c0098595100c0e2941c102c2465284403003c0c03070007842000040e042201f4100001840c5042030308000e810081c03403620030918500104882500141c84100444800000758110340e21400c01c00000c3c0603d1811079010700400c0c0101c42112042203855004610404c0c11401074140c404c0702c0782d0707003814074021a1103560111030342848a252140d01c000745040984111070f00301314051070442c442e41100000321003d010081c01070103145081e40241d400340554401036814044e61900003001c60201c12003990035810006108505a88911a200c000a07006420118040c0d00202c10900a04092040c4403003207500c0303031011500450600803142d41800d5280b110702c460000749204c800a20380c1e02421505242501c200044501450280361038041c0950306e06461251b060062005039080186100c54152401801c4100cadaa200f45e62554448 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 318682679 1250 318681429 318681431
    0xe0303090906010507170d0c02060f1906030c080d0f05030c07020105090402040512060f0703060506030a150e09070602060601030903050319180c14010903150c0201021b2a0d0303 78
    0x9180c1d400140c4141c4900c85c0080c2c01c41c5074512844001c010080000c066811811000704001c40301038408030388411059401d00c1180e41c420000c1100c1d904100d0440c480920b01900000740142c2d607903105c03029a51503034811041d90b04148030043c10590008021308080e202420124035600d0003104a032140e03c00c500000b418484041004126074441e907050303c001e80708c0642283e05035038501003040e640f03107001c407040c0010b09038410010f8101d81c0300b402240100c84018080c02d0031912812141e00180080d20305600f10741d01c04600000cac82a2807041c19902032200c0c00050b00045052000007030400c60000c08540c103140c1010071103070000b81d2180c1200e91003004c18076401500100c1040007005040740c61050300003161140560014006601c03c80d102315800d48644001454403a4010342e003c600c144000ba1000003040345890781a8140d0b0080040d1000d0362000600e40080050003054005441075000c43c031b17911400c1ca1124000280c03000d0300d984070304030074540703440f100d2600000c0c4644000d0b40000c00309 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 318683929 1250 318682679 318682681
    0x6090807080a080d0c0e12011d010209030c01081906030f0c08010606090504020a171e16050a0807020a0218041a190f0f0e0d020d05181c050a03030c0f0e03030909 71
    0x1030780c410034926000d42d1008010f213001030803914005012704202004d01c01d080e030402e449450418414400c41740c0180000c0c0c0540020b0490100540790468000c050540c4002c5c0e0589545078040309101d0314019520802d01d000c2c14032010300b8130b650305a4076500300c489540c5c545031080c001e85401048440813103200b110050b0352180242c0b0100e03401c3d1240050480a02c0401b014400ca0600d88000d5039886c120140064074a80e03030342e840d81700454000301c8030007001c03440400801c0300c5144103000307050f4040180e004a84400d1049d6012911140044404843c06007006e02408100610101c2c0140808066101100b1b141441aa040141b90340c06a08810b4a5a075004402030f4011940010098205010040010022403c4295142e4108510b1030005014548800d0310716030081042e00c626241420700341080010b104280a140b2004d48600c0359000c0c4840b040c1d0001440401c13800c03508030f102c0e603004240b4141050b400f4040b944003560300700c180b00b88650103016030307200001541e041980c120740c00142 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 318685179 1250 318683929 318683951
    0xc050f0f060f090a0c080c03010b01140304030c0212030c0a0b01170d0f18030804090b010507080f03040606080d0e0a06112121060102060c07081b030d0606090807080a080d 75
    0x2404d150f82600800381c80848130f001442020110781d400d4000c41c1030340248015070708000119150580c1080340110841c040c404100420301c0b8000c8075518030710280080d50817022000b481451341d040408002c43c0f55200c00704010800554083c1513004104150601d00080317004255562070710f529180080801980d8001035071500d101d4112400c61840110881e80c0305603ca080610711a8400d0160004686c00c284422074203501c42c600304c4d886650803200140c2410100600000298006402994129201c0d080401c0001060160070b0802d0f407151503044890080c071085c0140d02c4200c0e4001003e111540004140080001c1511074a03801d281000804171910380181c02d00720300070301e030940400142a620700003020712a0403055010b10300980032952103664220100c40144544400104680340502c6055004500554400400204d04060300d040121009003001158442c0e44040c001400e800c00030880c03010140643c0c0007828140d0003a03e0900d446489580051080c51400d054031913942c050f40907 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 318686429 1250 318685179 318685183
    0x90e0607110118050309090708060a290a0503060a09050702030f070f080a05030a0e06010b07020904050a170702090a0203090d1b1208010e0a0605010806240a0c050f0f060f09 76
    0x1040c0d450115080291110f40c100a80d9a80007482035034052001071010030340e56805544080c0c03280200801d881941400d00403908143c0070840c01000109800d58114412007202d0800740820181603968180c0701d15100c801c01010404940c01156000d05d44400c1c089c40c580c1c04030071150144000000320707688186c00e00d8034440001e14450040c101c0640412204009a888802035001d03145140b401d00050018100c180c0e2190420702c030b02e41c0d4510301002180d00600301421503941c01406602919224982c644400420541c41241108082d50018100302103141003100d468010380615421819031908280580c1c0d01c243c942040400d0103282003c00c00e2584042050212040e03002c0d00000251a0041c409000313030100707026810800000c880028025807440c400c400840b40148e40303020443c3c0341c0200707101c0c0f400c850700c59030241c0c1d03413440040030301c2c8880bc00020444861281e8030703416032100342d05041d030400c030103441c0d42d5000e42c00020341d4522001e000140f00d508a80045043e5419448585680f4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 318687679 1250 318686429 318686441
    0xc0d0b2a0703020319080702060a09050c04060b04150504050604090b240d1a0d060b0a080f07080c12030702150c060a09021903080d1107020622090e06071101 69
    0x3004400000411200701907001c809050f40300800d1032080f030403111a400030748820ba01104c2807001170313005500099104065410294005001e1010b0300c540d41503080200f000d50721240c000c08601c03100050308000d04a401c0d000c0c1e8500344094a405400c06080200041c2e96100314800d140b45a13844501f64401c0b03941c1c0c948e0148a5400520411412805505030b410040c0c00c09070402d4201c0d840c21440c0ae9640702420000d58144100406d24004203499039600401052031790b1070700f0b4106e02c200b100403c0c0b1400800074443d281c0c0d07010000f41a042d18065041d40381045012050740958170300341000103147c03000000d6590550381241d40844991401c180441c0b90b020f43c40980300c0c41d20641e003e00c444205940d100c08400c60080d40c95540c0026416580100010280f10051182004009000120403da4000d206804400341540e00d05002500090816000f8403d040e55202d40d0070034403482140b00310981802040341100c00e02648002c4500643c440c038004008405001002943c1d001015082d4008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 318688929 1250 318687679 318687751
    0x304140f0613020906060c0a020904140d09090c142d1206010f030c0917030f0f0408011b0f0302210c0403050105061801050111161401020c0d0b 63
    0x9a05030b00d0300c660449400c0b08003000c168060b4030f44030003140540c280302c4115901c05141c40014840c80343c080d801c1c0100084028800c0d1048100c40303e0140f003800c000e01207094044000e80d90030f80c00e01d05002c040c0080300e9110311500207001d00310070300d24240703402c00e4181d40c602140e00320341104006060302c4442d48030b0400700c01c40703480c45000100681c0f00e241411507180545020303a5540c1d2804030740282030b411290900c0008012419840b420044424103071a03814040b0f0060b010b4904000d0b40d80b4004010350041902010000c03070200d02408008403d204407002400c0c141c8034940c8580c22002c01031301d03410418003030300c04041c0c0010b0010700c00c14070300d6009140e00b00c0c056503c0400d80352800c0d0018098105010407500c9500f03090128580349080e00d0b5020000702c01000311800c0364a85070042d20700440d1120b01c20140c0c00346103002c180e80c0340c1001b240001002d9510b0300c840480e01c520002400d00491020045c071039090807440b240418640864180d0044224050ba1201071944a0f03820080b048134441d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 318690179 1250 318688929 318688933
    0x803070203041806091a1f090306050403020f3307110a0501022505030a21020324041406190509010f0306060b0406020c04020702060d0e0706140a050304140f 69
    0x100290346555030b400101119540d0b0810402d1900c2d0300b00358106c00c5070300c41c1c43c2c9a1000044600350910645003280c2c94a090042c00c24980b9070f540c0c2e580748015150211000d90150b04400d08051003002c00344912940603542c80d01c248800404000025aa4004940700e07036600c641c48000a0b40450068046003415940300040b80c0d0113189074071b40603020398000392200c00b4001d85c800010049580245407040c009030701c040914244200b00390101c4425018a10b900c0c1031404c0d0614038021000a44029030140c03103680104408803000c080782c1200100c1c0803490740d02861070083e18001c280030f00750145401034400c451400780b0659880000c4510b4016030002d6500804c00c900000b103507199001c0f4a012640708034003c0c000c04e550b40c203142d5035500562080d0009070b002500e03030b00c4032850598014210248000c040a042c018081d00c5801140c880010550240e442020188417003600081f29080c1d9401c900300c1c40e458001c100100904c203000c00f51000f41036101802c4084942c540520480420780d0210302 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 318691429 1250 318690179 318690209
    0x819030e030a0c0317071109041e050102031006051c05250509130207050706230403060c02060c0901020d0e1201150609150804022806020c0906040e060103080307020304 74
    0x100001003e40f6072204940b510000d80c801c8500c044504103a0303100b540c002d150b0030341c0b0b400300001b4809080c800070030440345801c83c07001201d440464280d0442000303002d02e000685034540300c51145003c00040d0012030900c10248401c8060300e5801d0416401e50400d42004142e98641c1c5ca03024842e1880d41c10314150740c443c6d010100340404e501c440a81840d8030704407000300b01a048a1070980c100c0c03240c4d6001400d9500441c2040c055140112758559200d42c0d1618050078130700f040c00c001c070010341154000721800303074440d01c1c1406030035810894035802070400d082040c0b50a022000103903440d28107140400030f10010003161a525543c01c2c001c0d800c114210300003400744000f000c100041039580d40c0a031002107648160702003409101c501180b4480e03180c64a1b100681e485540070060301c00031070012044445d2510302c031044000c2280b15164002c03c9190010b01e031403050301b001c10050b330100400c1039004924140000c13000c5100040e03040d044a4025015035925203400b0f030103d085110345e400420301444450 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 318692679 1250 318691429 318691433
    0x1002030c07052104150207050d1101020d031e0e0309030307060c0f08070203030a05090a0c151d1003020901120501030803100602010c120b0a0e1806010b03010819030e030a 75
    0x40020844580320380c007901c080c10020061280d188040f5007804024040902c0284411840400d1000c081c0c007080c011611000e5403600015005101c030389013101d4010352400c55641c907580410210400072601d007014800101c2c9c5400707401e11180c5200c0f5008106844041e40b410741d0801740121141d00e0400340c2a05d81d240020f051a44c0501070507100b680004900385a400e013400d00c601006030151455902640ca5070303c1e40602c0c0c80140101a04440181c003070a609800066504807c40008141007056070b85c103204044000352034001b80d040790405211200148600a40c0d0b51140c031111450f09040c0161580040e1004840c4c266664418050a501c0c0c58008400d100e000e402451140d0034156240004503190780c812030990307405484490108000c0c40140300400d17440d401c010003082004d480f25449581c1c81e00404091034080e2050320108030400e0040da41c0301c034184001400f40006001c0c107882c40d45000c010383c1c0e490100c40400c6401d410710501e12410548500045001c01c0001011111420800c3c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 318693929 1250 318692679 318692701
    0x20f0c2214150612070c020112090308010503120c0c100309020a091b0314040b064603080a110c041a030c01090602251212080a02041406090102100203 66
    0x5070b4151289188003060080285070200444513642903004134160399440e8018259241c04101404030306016600d0f8114035014181d10401c06100c2c040d41d07640c00e03d540750006141c24403080c0030040d01c4041d01049100709420b030000c0d442d0803001c001d890001c8070340303500d01d4102c1c010154901c00035440340805100042000c000d0300700c0d102d1400140c20040d206400400164103c030000441c1000e610300003c002400b1030382c003210180d40030398042c0000aa800022420750200e642d0842c00703c40030801805101113100c480c0b0040410a4580003400b41c11508640f221001801110b02003001c0007404201c0c601c03090800e00c415014014082d00611080d101007082c003a0004001c40d08600a20821b4910001d0390320540e09001128450b8028002803009c04842c0020780c000e49151512001d00e401d8005031000803c02283d1044c1c3c002c0e6000c14481c1c10904008240b841c01401c0006014010300c014031031490320503001100c030300c0c084902c582d6a9108100503810451710001d6140c4091005c02000038031100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 318695179 1250 318693929 318693931
    0xe070f0e06030337080609010605030405010b040509010c0e0a03030509060304110402071a090703210e0319020112050106200c0915040f020f0d020307022104030308010501020f0c2214 80
    0x12100d214044d1038034038401180d60100c02c0f0703000b41e800100c030f9004025a90040c001182c21500550001c5107900c00306000c101503031300036107480429a564282d5200d500703501c48201e075401d903000c40d0700888503442c50310000c106000d11107480340f155000202090401038086030175401c002c0040c00640d240c03130440c1004145800004041c000e035154010000d40c0c44580072a481041d0380e401a00d864000d03207090707051140607019000e10000c2c070075044c41c0405640e504201001108800701b08000550b041440014442b01d2078542c007510283c100b000600500b6048040c003945070401070760500720b00d101400100e217170031243c40c3c4c469000114034007484551f0401c1c40480b440d860b800c0e1001d001007114007101200f288a15400c82c1c03d8040140490740400e00580c0046803c101c8078412254000303401d001010107160464400141054006000c10805410840440c0100300034005840d40002c603280b0940c81d1401101e01501c50404032214182d022a080f003000458400c0302c0381044803140082015811483c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 318696429 1250 318695179 318695257
    0xd060807140d020108011a09060f07170c0706080c070b090a03030605060f0d0b030114150907111015150c0b0f0c07080306030709020304060b01030e070f0e060303 71
    0x19850140d00c1d86424003000c0c072200998181d540ca03103e686851018000c4007000c1d0f961025007501000008c4003540c40c10042e04242582440a41d5a0b4100b40340c50f04450100405545c0045800d11280440041c0426450101d0f08103061450140e0b0b500850f1040e60311603514005d0801c100081072041e005800a42034410a1080d10b041090b1603e032020000c0ca4080c0707603550340c4074420801102c100000c46811001a0702c0010b000450381c1c5481044074442444101e84c0c04940044400392082d051420a1146800c481c4c82d042405180d000d0141d803540310909500f4140140d5190b410503001011007504050041a40b11814181c00c11203144c000c3c0410300c030b0041a20240002c0010844401c0c800c5513050140284444462400340c071917940c1e007150340006050560501810400081c41019130000714441c2e44920300002c2c02e5403c1c4030016044503100700d4007501c6a44048014010501c0c0c028168040c0c8034511010f0301c5954407800041c1c9184119038681c2d503034039066000d0840424041c1d00e404c2c0750351 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 318697679 1250 318696429 318696449
    0x2010f0c0c1104050114041a090103032a0b06190302030d17010e07020601180b0409030e030f01110d09020a030f0302070602070b07080a030903051204050f0d0c15110d060807 76
    0x2d12400c00708000d5036400e01030014040d0001c0b140c603c103894194001d61681852010120b030501038200060038803c400d910035400304032020440700e1100c042c1d1000c00341171280369200d80c8540c019070b241d261001c1c0009107210b01501150300c1c103070380e040071130030b014002164020700300c90310000d03a540700408807071022003060105a6030382c001240c0031100320038543c07050315280d0003402503a00c1c1c807010501880e4690102c01d46507649801e0312155468600580e410a4025180c01c448120040c06061408034056054152645001e401c208001c844100300c0d8403032003101c000407036140302c0c500004468910320b50008140501030410030b0105600400c1d58021181c0fa602600da1241da0340310300324002d11070010010000e603000c205a4140900940c04004c0650081c035026017800494101d414160380c040d50b0503901c542c081d2008100084040103041045001850040092401ca64460400d0f03071b05d9143d60b1208a8849411084480e00d000546501d5186035a051219541d10000252942050b0240e95100c3d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 318698929 1250 318697679 318697703
    0xc0807121e0c020d0308060a24090e0610030b040b04090b041b0b030c18101701350f120705061b030a2708040f120503030103080a02010f0c0c 62
    0x40c5001d60142c000d060380241c001002000c00e43c0d02120703400f500a1145500a043d001c3c0402c0d41aa4030240041c00903150400b070103114200324014021400d0741c2d100304151901c410070004039480d28a1824001607507400d01241003404000090007609541c034000e60050701e01800f00d03092041e50411240102d0040b810304880280e09512a01416a54000c44201c040104046942607403080d00800c5002000e2210750400c18200c00010070181e10300103804e0005046041a864941d0409507590050001981e42205009201c04081d0102c03208076801525040d0020f9048072440c042c81800400300c140f00640d2402040180740c01481d8000c41801e0f16076101d0040010301c0c01d148144032959903400b0845131400c0d40d84800030740002d04031003d4608200b5142c801032406e5002007500103c5c0c40c1e031041d118552128102004209442d0150b0304c151502c4801110740008268048216415079800c0304e41e1560b90405100c0590141c00c000b603000300f2040c1f60500e104407566010543d0820240310340d0800d288 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 318700179 1250 318698929 318698987
    0x70305040e0c090102281403030601080903160201030e0102041511010f021c0b0406080613030305091222050a1502010f0c05030a0b1c1b080a0f02010c080712 69
    0xc103010f0b40107290f025030b221404036003103184070300f4070004071180c8610b501c429403000b036840c04280302c407101c0035001541c030120500030a0341c0c00940c4668803d01074070095040413519003050380c512400ca90064149590351550384a281d07020f40440d80a0b01e410110101c0b03010090030010000c0d44050102040780d440c3c1003843d99052107a000302d07200c00140340c0014542524014200d4000d00e00080c038658416a21800094880010700040e03200b02108898245007214234100902074401c0200640e032990080010300c230140c81008252110407855a0030f0750110b49040c0d41901915507a44c0141d644225613401c0000c41240c4903042c3d00c010340c000d500070300031000349001d484150342d0780d80854804600c003440011004820707648100c0c841900244600c0e0100302c3d80204680d125500790090741cad07020704620190510a5004440401030007e0b800800858059884940c840d040c0075100074104005804903405202c940340544012607080010381d5140c108001015000c0007400b00000a04c0ca80e0610100c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 318701429 1250 318700179 318700201
    0x403062c0c1302030903070b01090c200703080a090b040f0518070903060506030705130606090f060c0b2d0609060406050a050d060e0f1605090919140102070305040e 72
    0xa100d20064144000c0490765034500c0041c1d00300901c1001c5c00d03c024401d0902280d003290100e40240380200700006d102c41010001840000412508014207030102110b42d10090001a4403003141d80006d051626240c1402045490b4506944040c24160b8003080c04210b000001000c04115141282c0c20246c0409440544014443c2118100c0c0400c0340c0000030000300d4020b4018a0f4440310060545150b0f43e15007000030b02880e00300b034142148a03915603041c02041c0c0c002c00800003600b0003059024800f0b02e00100200354200066006042a820300042444c2400c0b18510014511038807441c04549940c0035290f9288200483d400c034414078900b400b00756207042901ca20410380e0809000070600b581017a081c0500c1c0030900303000f101c24036a101030041c20254140074140741803007501c0240140100340c058044500505404c50382c41165460f06210041b1000034413514215600c0117110401c04181c107090050100e4030b00100f11035400015440c04040d40000148207803121411090801d0300c40c4221303c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 318702679 1250 318701429 318701443
    0x150112050c09012001020a030b0a21080c010b13020d0c0801050a0506030c25060623120a06020a2001020a0c020616020406090218030c010f140403062c 66
    0xe080d580e810040c8030425486000424144d001c10307100c0103071010591072207038226030251881000103545c40049142e03d2928041c0c40000f40f40401c9491845210220290300b2024220300080101d2400210148404130a42000f1403850001b002181c0300f890858418020f980200c00000c8250319021058210a0140e18811705079030b006071040e100e0a0074a0140085940041c0201c11242014040384030014804d03c280d000e1030031004c41020440c0750070b103486c100f6146290005251030280da520b40c0c50702031500b8407200400701c04403041d0031580c00c0710300d8080c20b2080c2600b010380340ca030000500c80f01254224200c81c42e48219a01c250b228000740e0400d0034201c0c0100010000020009a840000751900c000900b442c0ca5544560184011840d8000382c1202c0d0160300035001c080e0089500c1d01605552100786215144c268068031210200c200001c00d05141640c89070180700c000d155140c2400140d00c165001303103070b0102081212030344441504000d40000d11804001032504d20707a180c3c00490200e010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 318703929 1250 318702679 318702691
    0x308030712230105010c080904020a0c0c0e06010519030b030616090806060306041202030408100c030507030905100519051e1b03070309020d060c0905090603030406090306050604090b15011205 84
    0x1c503083d0342444011a85804031150030399000b13009201c1c02805944030700c01441c0003109a110b8011410036464083c01c014881e030711040c041481c120411003a66044412103840c068244115204284080c0054004280313244440d9010320860301007190140d0741d0b0800b605440380c3c60f195001030356038917500d0b03a540780e108403030301c035015041400464005000c0d161120020107950060302d00742a243c40210740b03008511540c1d21191929401c841c1d5420750148696078000c0b00b113203000d101c202c082e030b15030603900c00004c5100d00762a5511340019504400105080d0310188100e8030520090030160300b185000c030440300454411442480109564051255050002011107002c040c20f558402c44103070b0041043c1c1d10181e0b0030944004c1458005461b46c803a02c0400c03649516528640c2d4100428400f915800609250103a402041b040c0010354010110340c04603a44007030007191980d6008042000f4091204004040307850880030b1089000d8085900da001e14001c0e80d5803095884a0080641503c0040d291 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 318705035 1106 318703929 318703991
    0x1c02060d0c0905040c0c020907230909070e0907080907090507053103080d020705010c050a02010c0903020a0e100e070f030e030408190c0308030712 65
    0x42c015140a0300e00700f00c03c416992000d02040441a4040d01c180090000140450310414090700f40c0303010f03815012112407155120b1307402e64103d9801103100341c0b40480091503240c07154800c1802c0c020000c01d01910780c0c40b240745c2a11001c0d0041c0501d00700b4011a0b10100b000f801c140100c2e8010801c0d599015500d1076010b400c41440403030030120982c0c6000c03482c0c5c0c41c00d0022021506005a98000740c20315a03600c0510312038402032243e144001d1803542045010103046030440d010b800c034000b40d42c0091040480199046940c03c0c868000250301c10300303848007803050310441c8040f2903128402d00b146901d00c5407100e03200c99442c442100c0740d000181d050554081d0b001d80c10b01039001c2070140703070000b503050509214105031650300c009d009407501d01c40595030f0300611400040f000011500919520f65030b040051000307040d03120050310700c850b06051280034400c90309800400603080b09091a = true := by decide +kernel

theorem cover : BRFrame.Cov 318525179 318705035 := by
  have h0 := BRFrame.cov_init 318525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 318525179 ≤ n) (h2 : n < 318705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
