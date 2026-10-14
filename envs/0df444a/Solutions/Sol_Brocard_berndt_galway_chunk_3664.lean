-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3664
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:19:41.285769+00:00
-- url     : https://prove2.me/submissions/2ed597d3-8453-4859-906e-f55900321625

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 658812949 ≤ n < 658992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 658814199 1250 658812949 658812953
    0x1002011401151101090308010f05040519020a090807080d0f1d10020a060f06080c0306070e100c120906080c1810030902090103050106141c03081b041205010c020a08030a0207 76
    0x4200f104100c40c03240e009110907000c910740500504001c0c041c921020f00d082c500030a032400c040c8201c0d4460218050f03c0c0d0b600107512107a050095101904010400180300c2c800304220310204602c0005042c0c000003817842c0d240e800c100a1015010305028000c000c41a83e1001442001403002c1c2e80341501100c20b0000b111136000103030700c3c2c41c1d14107100816041c10003401d000300d0403e40d40501d08540354801500d45000e4000c080640f5130000721008030124a01e10304105407805c0100411003841d144e81020744030700b070060721003655a00069607110001541c00c0070601105500406c910340280401040750b0411200c00c9890032418601032801d4051034103160140401c510a40080700b1843d0064007a03103d55840b420018081d01c0b09024001c094140e03061408543e0900070941d01d8032020094071846a0301041c0c0c1d00300c4038068080e0140f40b81e502c6803a10411a440581e0040c0b000304130030420b500c54081280b90850940329416824000c0d9080310229101141a0a0440e40c1c000d00590005039622614 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 658815449 1250 658814199 658814207
    0x30d0b040c201f0603110d081801033308070501050d0e0a0f0506010e070507020604180b0406060e091303090b0304032a031205040c090906020702040507020309100201140115 76
    0x30300000c203003083c202d030080084082d0300c0d0b21901c1564011080700c1000366060040c0050445400001007820b102048000142440000002d034900014500440d41040d14004c104444540c0c40d0701c81c07040708001c045600002d1540044070000d00c80540940030742842c12001070140e0245c0c9000300000e50301c2c0e00f200380074000301740001c000807a400702c04010b074a0303481d04000356200700901820703400405000100e4043c60103030342514210780c0d004181524003420309010308900e08491f509110300d940c40d200721035401ea40707a000707035400380ca19690f440f00169405d40c10010031084c05041000008880d0380740030042a4465607100568148203100303941c981321880c0803142e40f0700c841e888040e84948404010303403256082c5c0e000300c00d542c005c2e961184589070072560541101e6042d1801410114480000c22040b443c80d0004d00030140118401820035200da004581681e104940005c01a0000120340b5420b280070321324240b00510510080084261b881d8a46d0712420040c01403003030019528104500107845 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 658816699 1250 658815449 658815463
    0x9150e01030b0a061e08060a0501030e0c220b0108060303121e0c0306040606050c0619020f0f0904050f0103110d14011b0e0414010b03042102030d0b040c20 68
    0x40507050480496070b03501e0003802a1405d540760082c0440303d100e50300c0210f1080700301c680207200051041264918202c0190006c16544905210501580d007510308250782e1403906244003121045003009039481c85c10490102c0f043c40d000070341486260428003000da100001500c14400f844012800d1a4035030081000000304100d9070288982e10a40412020703006d40f0b80513600800059506114a41d00d6110036102c0e40208004254603600000026440d03d080180d03001804034400d50040c03402c6000300d101c00d260340c0b080c07400c0c64680c800002d088006040034420203a002c0d410190f8101d09504594a800084035081c4d00d04c1e114035284989041030141007145020603140b400b00802017016070b03c054102c040b080082ca10007007041403200c42d08a04050103151080c1140c1440c0414aa00b00042ca050070740010300300b61000c0c15549090000c454a004100c0003280d0035030000c50b12504400700c1041941c100000f500e000e103090130b0181c0c01e290307000344840c0386400000d00c42042d099010f070742c40c03403070511 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 658817949 1250 658816699 658816721
    0xf061e03020f0705030a1b0803280c021f0e0312041e05150a1b12060e0f0121030c140c100c150b030a03140702030105040311060709150e0103 62
    0x20b000920303004000b0000020802c0207184e48440c0d030007600c1c03401403c1d046030100742c002c2d250306010000111015443e1440041d124000f10103400b540401c4442e2004442c041c860745030250744000364180e07456134901e2450610810000c018001c01101d07481c4c003600c2c1c1c02080c2e10080d240c002c440204040082e001d44580007c20000701e0190441a20f090103941c402c20342c8010030016040c1800724400c24068081c0b481500710065198081801d0181d0440314031351880002c42c20955601c802080390f9030b2804060340070340d01e05c9285982c207504081400c00a544030258400130f40000d4805000000d40100446120fa50010741038840b414405c01040d04000704580420740c04240014850300240c1c10502e0b4508060040010311030791000300b440c000840b245102c8282c1e059000700301e802c4c0028410f8207001001010040f410703040c00300c00d0380401d094a00907581140032550596208150741010014513500a20070f01e0b2003600b8031702d07043d5210380306181040e1040400000d01c4042d02507902a07001520080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 658819199 1250 658817949 658817977
    0x5010c1113060e090a1232041e03120e0103091202030c0f01050f04080327031809072016170139110f15010f061e0302 52
    0x464415107a0040c44103009440031200050040f42525000045036100e2a0b4411782d02d9140d000d5092080e2001342d01c2c1c456106020000c41c048024095104c140701420301c9030040f00d16101c03410460000d9414809084101c1522203605003000401c00c00c007040e800b80185424910000207580004a000d00310140000d460360311000d44401d00d4a90010041c800d0300c240500f555200543c1d01100c50a84200b40d442c05456400c5202040108481390300840c0c100705003e9005241e00701e0128030361604c408408d1350808503080424101000d1400d80204018840d040364510001d2420740c01c0a000c1d41d040d81108410700f0190f0400700b0418030100010120311041d0005d50810507603800c1c0d01107080b201c038500301ea07955003001e5a0301101d444240d840d03016114032414980782c068000d02050b410a840d08008020402d115401c5026070340d003440401074007c5a040500b45141546030311050348001a4403401c00303141d013030340c0401c05264070580100c0720a500c100f0301c10862100c450b086020340181d4030703900703580 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 658820449 1250 658819199 658819219
    0x90e0304090c1e231b0c0105091e180106020607171e0c09150310090204030f03051c110307110f0d0309050c0a0b03090609010209130c02210c0f010203040c05010c11 72
    0x703442d500055864845c40c10100e0381280c904070300449403809102c0e02d85812034500e2070b8020451850400b4088080c0c40580713511082c075402040d10f0f045100c203038407040160b0803c401344554503a07c0741c1d0414980700907202190407424004a010401811224041003608900000c52540101502101e9100c0c0000f40000799610507038400d02c1e8203900584503001c1e107001e88280000c242010b0f000b5141140e81001d8081540c0320030742c074242c0301d6620514080c440e01010584031a04007500d0f1040360b042d50301c0508816280c1c03410080213429680b900300303a410260304ca880ac0010000000400d501d18100d249808507820600f4a070452420910000341e9910281b107680110f40e401402c0050b61090955404031041b41c0c950102042c01c071f11945554a410000360b440e49081401c003904014410310f02d910407208204030480940d0b45c0c034141c0c1a40700070003001c0007407004c0d40e00100300b0415016034100c00085245040a0380c410020008910816050141c04450703170b802d01c40f0500035051507210140c05c41d240 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 658821699 1250 658820449 658820467
    0x1002100203150a052b0614040c0302030c0102010e0c010c0c0b180a17100218090108011a040b090a1d012408061e0c04090e0304090c1e23 60
    0x1030841c2034080d580c011140000d000480e440c01004400860004400701100310026030f107050703014214005c0c1a1445602c5405069004068006c1a8429401403000315449800c2d40704140c2442c444c010000d046a04180103404a00c00100790107400420909000780709981504c0d00c8011200705510000307010382c011032000111280009021500e0304100c0740c1300d115907298402045045445101180300f580300320040028000143d000f0304e0403440340308201c01e6404592000400800090300080c1d00d0380d4490404400140c0d200b811048407400845041c010030090f070001c11240040186075000c401d803510045c184001c07502480050690a07000213000d09a0401c12203960300c000c0c020301300c4c8801c1100780700080e00d40e00450818001e41006031039095504072007581487c007410280a08585090420000540762000e2081004258010000e1900c552034944000c044841d103185880c1841003010004031980c00c115100ca003519510301f0484000010303e800440c1001401e800314080c81c00018261030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 658822949 1250 658821699 658821721
    0xf06091506050406020d0503070c020d061a0303071a0c130b070209010b0415031e0204030f020310090201170405120d0207231203090a020a0e09061b091002100203 71
    0x10340c003104914840000d5a200d004035103900c258400d910060304814a840942e600c01c100441e04048540b4205c5c5180000d030700010b094402e0800704580701c1d0303510413a0010600c55042c00c03c021650842c0034600388502900d410f12018041f1400d44840311801c000907000c0c0044c1d50603106007000028461101d541c482d21310204a500c04035051b8401c060420000500200000c1210b050b01e4141691314000741e25128160050501c240f18641c400700704c000a05030300c0c1414406003000b18080c00c00c0750450031040c01450300300809001c5a0762402c1c1405003c00160360402c021011002503001480480e5860f406c0260501c60001100000350f44000b80c0e281a0000e00d4004d0039944e8021403904001c0c910007003603620300120034801001039403c603002c400a42c1c0f5848001e168409084001d450304941542d0000741c07454110342090020003141c1c1d090040a100400c81640d0188032043e040510420160b0a10100d0141c151094843e01c0b40700c842d00c40c1903100344020010b901001300b066449040c080c481034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 658824199 1250 658822949 658822961
    0x20121020307090e060603100e0403020a17090109090b180a090507091b020c030709110409150611010b0109090924320106051b030a0206220b0601030c02010f0609 71
    0x100c1807440130002c40d400345484012a8022100d94410a070004d00c3c02032070300c00c000c00080c420340550081d4600f210200764504008003070300100310141a514040500050413141c0c070764000c0c2074418a4003c181c0c509454568907001031468071282c030340c800d60781d06090801505000384010701303a010f0b011001800d203100b900305071084044500541d80c0c0c06103e0500700e0355501056105a8540c1c0840320410500065a00050170b44400240961409494a4461003170341c10000c0130140c4050a0340c0e003084501d501048900e5034140c80c00c001e000101030480020516030f03003030013106113560745e0b9902e400410648102ea01242c0303800340d02c031040c2909140c4200b00102141082d0100181720005050164401c803441000c0c402401e004c0a44180d0034414100c4181d000444a880c40380006074448084103000c20160070090001c2e4020b1900b4581406054400e03030001e091941050148101000016401144140e00c00428a000600e440402c44220302401010040701000c6207041c40100707800d07403250000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 658825449 1250 658824199 658824209
    0x1b0d080a020601180c080c1605060c0705010c0212040308090a180603060c0c0b180106030206070b090c011e0f12240510080411010c0210170610090302012102030709 72
    0x4c00b921109818586040e00c07000041680000c249000190700600f0f10320141405103034688580340d808070a03540b49850100d040d01ca484080c00041030003401c0040c2402100b0b07442a284c40074144801a010701283d15000364000204106e00100341440b483e102c000008004114140c0440d904c08001c00030007008151038002982c0742402c19654544450251a0400c012507118101224135929090402041d01d041c406604c0d6035525803100001591760a005001c01c0c0c3c1c007400701c0019138141803980ca8640422081c1d01818050400c010702101c400d10f0055294040341c5003000c0e0b0b00c402d010300c0c04440780035910012050451500c03200e07104502074021090b64903d00c1d5080c41c401c080d05c460401480d0700c02c0301d4590000540f40c2d07000a002502a07030f9041400c0f1018103141c0c48681c03456002038146038a000e0789000103036001201280601043c008079802030029034143c00c100540103130003440c7c01c00c00e01001c0e052085000c40b02c1c40704102003c9000d852204039208640700e041c010001019031211b4071403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 658826699 1250 658825449 658825469
    0x2032503140f040306020c0304052709010c141309050112020f0402070206030112050a0f20010f050a230c03040305070e0115120b0307091e06081b0d080a020601 70
    0x162156144000803120b52108078241c0c107041918550340c02e0041c0d07121070384070440c0d07000074840094181c071464400b0566000d00380200c0c8060480b0350035401800c200414208607a030400801c813101d543c0000f1030482c00c2544808065990381185142c000300d00345c5034040014070b0f1801c03000042e5001e0100c18921034130300c02c40b4002c00309002d0108210582c003500c840070390302c000108010020706884010800019216409440f23180040d03858203901c0001c0c0c1c800c2928500380f000c131101d510100381e0204011196003403c2680108450754030081242c01210120001c0c868407621101e41c508284008540b02e203c1500d0301962001c2d501c090325243d41252100b00c4061240400c00726024a480c0240d505942000182e0900c0c10b110441c02c48003003022070446246d91350354820041864900703000420203402c0c4400f0101d00406440080000116000d10a142c1d40b840c0c1582070104c228040703221036030604601d04484000224400080c40141c500c080100740441c002141445d1540110726a41214160302e4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 658827949 1250 658826699 658826717
    0x3070e090106080c09010504270312060509093301120308180307080d060b030a150915090c170103031206090603240e121905091e0102032503 62
    0x100740d07584c02e40400401e40c0070703292400500250529a00924a1421100300302019103009100306a8180c201a0190005101070344c2c40358102c1183d0003044014001603c046c3c9203032524584c502d840b11072540d85e0b080c10014001441418000102240705a001d502005d9402540d40e03468901103042800e0046003c5642c80002403201800300165824a0212402035850102035684407410f580c001d80c03411350032598602c40801c1526084014500c1000410f000081c40c11303c900c0640068280c035070040d5003043c00c1c40c0000d0311204100075990100d5041c0c0030007054041a41c2c1c0f040d11407044110a5801e51101d42e4000024140e1106420000003220002000f12a858a1282090f0b40050001402803107910110040704500708031781d94642449020001910303501e9500c021305000c0c0c00c18503001954000300300c0303400b1818018100811307400903040032072030800302c280802d032100c82c2e003005043d00381a200810303406a402401241d819610b0701d46406085c90700c1004100614071600c05c190001095a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 658829199 1250 658827949 658827959
    0x18040501150602071e0b0315041413080306030c1503070e1828110a030b0405100605030a0b0d0f122313120b011703030601080a021803070e090106 64
    0x1940300e0645245a0203090201d0820003000031044041d02c1c20140c0c061740392000100c103a01d0310007450044901e14030180e00950100100820380308c14a4000c43c0344090b14003484150b85680060107030555010042c0e603100e80d242c0300068204a481503009030030034202c40401d00d04041800084d03220301c100c0e407110302010f4924014882c150100304d10001c0004880d0022844100030105400a1035124400d4941d203014900d0f400c2090f6280c00d501c80e00c585031702084404200347c141c0a1381040c3d40d8159020000340ca0200f0035180c0e880c0307a6204080c01e01a00002081c51000150025140300d80043d00380c4a2619039072030607a000e91040c502c2558032545100640780300e18442e0440b402d102c014110518103903d282c103482400c1e40d102c42048035450022444c0010070b00e2503800052490380c002e520343c1103590324094104c00001c03d051a2850644c03c02c00802111740e07013003103020f600f180c1c46190050b1107801c001a1007a81d8540440740b154984503402d0005101c442583d003640c42124604001d0107440d03038032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 658830449 1250 658829199 658829231
    0x7110d050c0a060b12160906080a26070c0b0a2a02040c0923012604030309060f1b0e120604110d0b0702010b030c0108010303020d180518040501 63
    0x785804080d030481d4400c0d10100d01150000d0018a000400c403a0108400c400c2d0940f038207130400daa25014422101c802c2140e01043e00c95540104103840c041e2000e141c4559401c040e45000c011101907626904800c00504004002510883c0b40d101000b1402d02d500e90f00e03900740a4016049020000760035409550a03040310030700f20003144050700c0000c1c0f4105e1140d03003004050401244002c1c00c001780c401f00007854003032120780e1031000300b0300c06c40c003076506004400010600c0c8071020958882c84815180c520b10345410724051a03010b60140b0b40000c8500040c54040007820207150036005103820019110a402132900c00180004050344404010441c142e0600220b15003020b401680c030740003500002d020600c07246c50703403060030300050a80035565107a41d501c0c0d4a845007511403a006030741d41d08040115003010045400040300908084039190302d9903500075590403e200414080055001005600c4288204000060240100740c0c20b000c003261311108500328030841e4180d40ca5828020301840170414 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 658831699 1250 658830449 658830457
    0x501030204260309060f070c15121104050607110306011710050a1805161a030a18081813020f04050108040f060507050a031506090909020102010b0907110d05 69
    0x84a00c400b000c1c07110705210081c4094006040100030701080000d80800e81e6004001c0c0b039586c0d00000d0540d1036010a082c8121414055040407216442e9003d1803d41280c100d00301a0100221100201c1d95810401851220380035590001d90044000300c1d02d00100000b0703244440382880c0030707002c40c1d610703030f81c0ea070303e4011441c0e82101c10f50030581040340c044284602c10341225038040345100e0003007107100c00100d04080009080380190f805401010303a8804224610a000009000801042030600e5080c407184a0710311000d051880310130f0380c80800000400000201036002c54200b00c6680d00e4240b007a0202070b000f124560100c2c811901c1c10592010b10543e4800d48610300003e14402e401d26080000544071000043c00544444170004504000203061b801440d2151940307584198907003005c0e000140c103035603403103011140d0206104000c0c042158422007040c105d0f400841c020410699030300040c0d0040c846982015001b11402c07003040f45458122460380c0a6022003012118400d8034150211005d010b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 658832949 1250 658831699 658831709
    0xf080309060d24210c14030109080c0105010e011202060901030b0f030f070611071a0703110109050c0405070305060d02090a0f05100f0b04060509060310121104051003020d2306010f09060501030204 86
    0x85c00604c24170041e520321420b5000444082c0000910403038a460340311298110062100242c6c0d11080140407407501d1403d12030062a003000c0c4129a0300b4545e00141042c00341c80c1c03455040581d550b01c1080c0a5446182c11284002c01505a4800b0703088012046e4039040d940c05002c01241c00d290002c505540000380800c200c518405000c04203218082001d8041d81c45000142d0401004042840401500380310342c0c062680b00d000104060b40d0100c05000070344000030a020281480c0104120054a81c44444000558120b4105841c0c3e0b480030a81001800c0e410b08880031903250408201c01d0701101c2140c0401e4910041c042803240e41d4880d5089060320441c0a1b00300094014007150b241406d01ca409990010101d40140700034580310b0b841080c0119207040700350790042d201c18444625040510030260081ca503020800401c4d825030300415140300c2d130544e00801c1c482103014201e072032180f860520240392051005032410f0b0350359088803003100c0c0740070302428100900c0c00800040a60091007150b04881c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 658834199 1250 658832949 658832963
    0x902031207050a23030d05040201080601081312110d0903020a0b040b0a05030408210604150803070201050702031504082214061608030a02070c0f080309060d2421 71
    0x2c0740c1d50b91101c45101d49800800d84d400d00101d181101004240050441d8425611001819160500004021150191100b814081170714203004c1ca0450308520b0410144c1c11031f0b1003110b0010104001c641030788154124104901640c40803034400d5a101c0881002c4a00803156a490300361683c00b1000b15100c0e038441c0e1480b07008200442c502003070141d40039550080c090329655081c80c0c5852452003200504038005060351302d01d1000c1000b185401c2c496105c0c041103480000d00901d0a140c20315603070344241040039040c041d000c920072046650800c02e1807400d030036054200d0700c0c5041c02d107001159600140c841c402d4100302032a4441c10302603030442010490799000d42c0d0144480714082070000715480100841c0400c1c41c030303601c3d58010a041794029130142c4802c2c1d8005a64030102e00b80741009010300e170890030f51100e80300010031803940004107440400f842280c550355124880034184008005861041c2216000c040e64030007650b8410001c20308450031400f02c0d000202c0711a50080390503ca032840103042c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 658835449 1250 658834199 658834213
    0x40b09060114040503060a0219030b060d0914010219110102071a04020d0b0c0d0605060705030d27060207120f0f1812050a11010512060d020604051003090203120705 72
    0x7988540c520659149000501c60b00d000d4444012a04142045550500c11a00080d2580c85d68890703403004084c03d052490200304a00103003000600310312544426400c000d448201020900c1f031403441000d5010000c2000f155200303590150402e20002004400b00441c42e0318403807410014040c021658010f40c0074907925000007014852520075040a80183d8006d124424a1800209000341d203c0c09814402441034650b8050340090054030140d800c0b15000341c0c01400b141d80014000001ea5522081c00702001c10300b0000c085500300f041c9500c1a101050b500c01c01090383c1800295402000e480d4002c2040003401e1008103c196200500c01d0b00c6c0e400050703400410358801c0da106110b54041140c9200d0303175405003540d07448440d56200084e41c2c19603090300040f066070200410760780749110b0f8050070308040341030003404030243e0240c070340c0205050f000e8840c4c0e03a5076108550350002110301400e0010408141108120301c010300170995010308078082e22904403030049114001782a911107650001c01840c003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 658836699 1250 658835449 658835461
    0x5130510020d0f0903030603020a050429150a090905060d0506040312020c1f0e07060801120302190320280c0b07140715050f0c0705150c010506040b09 66
    0x29440300e0307080d9070300581e01c601202001c0c00034000d00070021700030b0f0360200b10542180100400e018169202512032403a000200145031140308281e02e0008501c0c4c880070034040c0090101d0a030754808001d4415000000800e0350296402500e444180c03609070000304503940d9202c040c40003c0300680c2c2c011f00168482000640028894504000e030b41c0603440d0b000d41030186e00c00c040c52030640804c5075814482014295030841031110701c0f8890201c00c04c5030050105619105003e04031140600512240101a028190505008210343ca0340400d604003515103186041c1802050280e107000c05060f200081a401c0c3c0c000ca00c000340b1600181c20005a11258004c1107000001904030160100e810301c0c03040100150a1900c50f000c1c0074440c0c01800b15080c2d19000c04d101d10f0030b10881c3c1d0454040030740403854010103654802c0c00e5a0016210302c910660311030030788115925110003584002c0d80122020b11041074a16042d02800d4680ea0300c800034001030b2074a80402069506024055400c26404000511 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 658837949 1250 658836699 658836701
    0x603191b05092701120b060409021f020102040807091b09140607060b120604030207090501061b0809030f0304140303032a19031a01110d18090609060905130510 70
    0x665540a04860b40101e9803403801d030f0340044240d00c0981a0782000d4400320030700c070000d19846c1c0e00480880f01080900c82c15070004110a1f05161500f6081612148103001c0c18001d6048030050044d0710121408103a032010184040c0200e41002d50f030450114116a444130701548907007042c0d031055600101000090350a002e055001404281c0d10140c46600094141c0c4031103941c03103160420413000d400c86140506020345014002e5105040703180c90840104103c0750b11510f04941002d003c034070021f0303180d03c2d0300345011103000d16021070b6410300074074034507a190b01800001002251001803103000d401c20b05404040c0c61b4081182d000300c3c0815000a08828114444403503200701d001403004500709040d010100c105440100320752030109a4a5a4a01060300001c80b1091755410901c0c110342c080541c800c019440315171600c9803100f84203183e2252800c00c09403d21a10140400c40f100300b040c29550000400900201e10030a0440742c0f03006c02040b0400c02c80d501e8107008541100c01010b5810b61210104 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 658839199 1250 658837949 658837969
    0x1a01120c080a03082a0c07052403150109080105090d0f140d0c090e0109050a27021221130501030603020307030807080d0509030c0c03010b0328020603191b0509 70
    0x7400817041011420b1001516000340c61805e030090300400806042009003e41440040c050b010b50119444041280054640489a0084800c1c3d80701441d0250710f0016190b9096513000540e2035401d03c1c0403c2240c0700006080301c09801030b0707503805880c19040d200a9402c6110301e10380c0d0602c4441040040d0208660790082d0b074061442d41391041c0c0d00340d66910500040042a00407501c0542c44005000400b00c0710300403410422008440d41080702c405540d400c155000150000380608541980c071789841c3c40c2448041803900c1c030b0314105400002c42c10007004540e80695200030301141d40d0100410694401d03c10b44042e41e84c05001403030400d085843d08860341c3c00003001110140d03c108002802c84030742740944c03405080840011600c440d03401e0b410302c0c241000f0320b00d202c3c0a6071500c4505120395800080480503501a410802c00103903c0e100c959080c04c4500b00041c0d0011000400e0041c120031140f0280b5502100c1c5904200d4020501c03212030483c444055507200149083c480014203103840e1104c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 658840449 1250 658839199 658839241
    0xd080913050c0304060b010504050d030e0d0503030c120a09031704170a120c0e0f0f15031e0906010f0b0c0f070303080901060e04020d06091a01120c080a0308 69
    0x803040400d03140300c44050312011a1600005240403052208001c528041d1040500b02400c3c05070404d030500340804d82120042002600308034265030301482d41c1d2209107107804200d4100055a9991410241d40301103588840e03103542954400724009031b13500003140b1580c6003550341a80d462040c2501c09000d00c1b0100e0380640700b540d00c18158040110000803003001424030300400e48418403d1079082d55101c04440b403d9400d402032015900a0142c196103c0e5038410280c0390131104203001c00d100b580030541070390072021000b440b00c8000052084007414444403015407600c002d011011940c50401643d00d405e0203124400811b46005018091502074902505054201400700c910300000d600d0203c1c50200c50f40d0050740800c01420921400c20700c00c3c0209406000304000711074590401e80d01042790b0f0440a000500784940d44d04032754080100174043c0c1c003403500324121000a1541c43d40c18074950000c5880003240c985103480b000082010020402a0000f40c158445012996600d603000d84001e120080e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 658841699 1250 658840449 658840459
    0x60f0906041710050f1603020a02071a030108010c09153009060509030a020a1104091b05011b0b0402090c041a1201061107030f030504050406060503040201021006050d0809 75
    0xc085080050003070000b0b00ca000401c014407180d00b054540310304a071400350036811101307104000c100b0f0300031082102840b000c41c2480c1c01680d0f030818140072410894650025078400060061100558813a2000345060f14040c0b00200b110800e2000b00741e0b112a2144194211245450342c0d80d11100d0044231040c89058400c00803290144090f001c2e2a00206003594414046640c0c10803807050080511500da400840c2c0c00c021817400003c01006035070741a4403640100958161404801349803195002030f010140c0c425103010281200e9102e40a180086004a81c0003440c03143c0140079142541102800c4641c01c1011011545c58035003d005103110000c1c0b4400450303800b000000b0f6070103101c2144044d04000c1d1721042e40c0b50b0300c40e07030a032485480c41030303015a04000442c05100d1909801040700c10489038001c04840c5502e0161800740d80c0303409103a220540c81485c007140040d00341e030840001d5100b14800d900b03076403180c440e141d80b5030222030580c003031a074100000785806800074910100a0000d1500201 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 658842949 1250 658841699 658841707
    0x60305040b042402030405161502070e04150603031d04020a050904090501060513061a0301050328170712080f07110a0212070303121a0108131709130b060f0906 70
    0x3840382a45e109079002c03290f682c8480704007007081a0400280000e0a200c2c03407154030a82103210001d540742c0d80c500070300302010b881c45c02003401c000100103603645482410720148801e0f9a641000381042800b510384841603042400d144000d45054800c4400c1400079882c0c203424100d409040c8002032207482c400300c07550340d80c8086c0461655600c2043d01c020780001c01c0081f036003904100c0003417580e9a0384452207a680c0c00c1400188803590780411081c1c4560711005100c40c48551042900f070030118800c0e0040d10200e50340c80d0205441c0424001066646e0141780895000c03c50000221000d103000c8910480c0410f520003c504528425405000e04074038001c111080d42d074094001400d40b000c4000d0a00ca181e0003041d0400406812020701d103000300c0d11750400c100120081c9085c840f007003000b00a0324100704030b200005a030f030f03c0004001c241d05508481d48025820290b8000c0034141c0c00588e4083c4034844801600a403038881d405030302807821000d070569042400b5030341c42d60402d81004641d10b61054bc244 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 658844199 1250 658842949 658843013
    0xf110307060921030203090303060405040c15080f01210201030b03010f02040e06090906040c03233a02030f0a1103070c1a03150d03092d060305040b04 66
    0x300628010502407005211800f00300c81c040304400c4801e6880c40c0c103160050040110303081000c001c1d02d502c400103581c04200d40c0d03243e03d0325001400c41500075002034854002d4000000ba8820019403282c40e0700e0380d2940c0c4590f00c4e078241d12200c4501c04c40b108000c0c1d00034658100194841d4000a1004c00050000304203613900c4101103050380c00680202102100c15410084286032600b0310581001000d8044e0401b4202a140c0a5a03224180806440f8401e10011441c18400e004520518442030001341d903140c42041c02c00030411105ca1070a00107494002070b60900f5102c901200350041c8095400031031a013840b50380039556a81294070300741d042c40b00d104419800b0350010300007440010300c28240914058148039405441d4003651304800b04401050007000442c2642d07101d40304484400300e46500d220440d81c50f040311a481543c1200e030300c00c10f01403891000a100305c0c075096003040b4880c0f41001d0554a0f8030080f000c440d03007128003810710ba40400c04100804c184144054400003441580301c1c16050417 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 658845449 1250 658844199 658844201
    0x7060c0e0d05100506090c040b09030c060304050a0b07081905090703060204031a0c070c050d020312040609171606050307020114070e180c04090e010b0d052104060f11030706 76
    0x2034142d640b034104010303c4810070b45510031503502810072201d074405801e05042070b005a004901620102070702c001440440c60f50100304480e40288010300c0346640c0d00e0507250554854260040883c4c03900e031044c0108403414081c11314a849419412026035100c0080803000002d8180508807840034003e07407001101140d2a40010b002840c024040040001320200c003c0f20100c10003030002c40070420034012440050000050b81c01111821030303006212000c07a00020b800c110303d200f00004620070000d00024842e40050f1103100719144070003440c07090300010201a40b20b80241c11a2940c07140e6005091202038081c0c4003443d0000e1061000190741c0703820b40100b840720407007a02c440b00412142c0c6280b032020b14080310100c0c0d500390b825840000e60300b0b11404041c0300707004070702a144041d0b440f1880320300c00b00004d52001c01c0c942c0004200444500c1641491602c60710701c030b51003a800d00040360b1800b912145001c00c0360100e5100340d459000005200c50202e6a40c441d2100c0000c140c002003004001103019 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 658846699 1250 658845449 658845469
    0x3020a0305010c1112071502090909010614010c05060a050c041a120601050913240902031503030a0915090b0c070611120904091406151305040807060c0e 67
    0x100d00c00001c1e00d500e50b0100580407001c10f04190050317911070300c10380b181041040c007501c00c04d03a44203401d13006241e11034841001034010651650340045852080000d4914150040e00494400705c034002c0840424000442c1d02c2200180007900701d50190002c9140407480f588440e80c09009240264203054864091188800a00c0c2003045043c10100b902c038000d40400755226042a424200103140080c0c60012510210130003243c08803c1d65280d107040e071540b44080070281300034606605280c01c0c940354946840250000d0752400780891685041d4262800c00004441103d002601ea900189240803111062100551701d80c20800500140000321002072030050808000110041d1064500745500103040031498001ca03540b55001c0754103000c4560710441159051481501c1c007007890103042c24040c0b040225648058a02d116003c1005982105008030102c241d40c03c0b1191099440c4803080340f41034030b006a4018061b0001000340c0c1c4002101a8090204500c0a041c8a409990968009009907103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 658847949 1250 658846699 658846703
    0xa050607031812320706080906061c20040c0f022b110708030c161a0306010f170c040305070b0c0307120302070503180405152803020a03 60
    0x120102460100b00c442c1c01403500035085000804010b11059260185444c3c0d800d0a540322036034401100c840301c0c8075801c0e042e200c6244a08100c5500c160345500007414803004580d0340c0f00c540a000d01040b5a481c028000c0161000454100440541c03079031526001d200520740003001c1c1d0541d03c00032074000d0b01c0d02e00500011401940704e0034410b00844501900b03014400721100c66042c688210b0059460450040403254500c3d45807800120804000d8035161802d00c0d0060801e0f44000300c1c1250b21000c00007008a00d010403139030203000040d5110640103940c0048500d0000c250814000100300b54031480c8114010074842c6000d0301c1d092600700307443c2c14080d42031340da050424100080c00d10030b10108201c49402001c005104604c1d0950f104025500d03400b890744000e2107201c0001120000324442e0f0141c0e40d8054210080e01e90750340289a1540102040342c4040d8012805c0c000094000001e0103400b1044030350242c00d0321ba17092655980400365a19001c96094200112071011026071128115500594 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 658849199 1250 658847949 658847957
    0x170f040e0a090f0c03021008060618030f0a1110020d1b0602070c0e1815040f050708070f05040c020d210e06041a010f03050d08071704030e0411040302090f04020a05060703 75
    0x1403c50041c0701d8a1111080c4c41d10038088c5180a00c00180c480000b282c1d8450000c008a80751407002c10000b900f0007000c40d0034a8068800c8215103418032640c074042c1c210f8800221791451032000700e004c0c01d980700c1101c0807003000804d01800b0400c5a0b4000340c8810000d06214810051800c40c26a0720b03811444051f400654030109074104110a070880320007154400d4805000806549140c284416014030005100800c91342e00c802488082081c1040820044d00c0032200380e84005440d858040032800d540d01c202c42c4560300304402051003500100d91450a000d490781c5200d0030341d0070b91860300f034064409a80001826981c0382825031510303041c0f000c54016840390030300c09211f0101200f0186c0c1010123030440c40b07800b28806420000503c0008200305003200350300b481459030b42d45001c15910340d41c0118581c1ca4000d40c6104010805600124180440d1401c86d0100042841c1c00b100050a01071800b00035000040d14006c54100028010f40941c001d00c014025840c1503141d102180c41070b005039004034041 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 658850449 1250 658849199 658849223
    0x503031216110304030212010b0d03020c03100c1d0118060206180303060303040905070915080f090129040f02160c0e040201050a0e0411040f03170f040e0a090f 70
    0x1110080c0c05103212081107107030000ca20000d802d8210b4403072240307100007841405410002407a1910030b401010802c030004004a103042018100a51100c9644241c540703c0d010b032029003044281c0301e00c1180c08100180da01da4115a28a403803034140b003050891454188480250720001c100d2500340c07204041c11310740d4042c05a03410900e8455079401e80300141000180c01c01c1c002c106060b1000801d85003101d40c07840300450a501c410314241d42e072641540140710034070845c0220303001c103036041503106004259406001600e80d0f5030300c07082800c072245034007006064044600b0319071070b45040c10403240101000400000703d017100784050404030703403003401c1ca4160091822030b00014024440003400041004800c142d6141c0b41c20b80c0000c24900c917980300c1d07006000c40400e60310b1716600c0d140c1c4045c3e1014204400d5560701c5840f0031140240c00100c1c4009c9884540741001801c000052030255000c0c80e0301002500d00b0b0a08007910180180002000c1c0704032150f942d04044041504440b12001c0140103d01c01040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 658851699 1250 658850449 658850461
    0x1c0c14010206070e101107150318031710150804110a030302070b0c03190f022a0402070f0b04081312120f14040b0a080a1505060c0304091e060608160509040605030312 73
    0xd44899103e9915036058440a550109802c18880303c0d809840b03200f425440e42d1010040d03781004260040c24219080052a9001a42001c00940140d000d2102a6915099501000340c42221404001d006130800c01c0200000300ba210007420340b00302101d00b6241440c000403203980e030350a02031854000040041401c80011601844104040780300b071303014035602c1040f070703420070880d0501c2c286c2450103940d00041c50028880c6141c0783e140282e40c8036910320007034281401c008201d81c0281d04059a01214100c0000d124120311641d5914113910582003500350603408801d80e020f49800310404103101440007880c070004102d1000304003400304841c041d601c0d080c4400c030051148a00415804009140055447d10140003170003020880300c08840305a079416180c0c10241c15030040350b04c4500498140310007410003642c0180c0845075074902e034200b0401c165503003500300d90000d016980303203108400e0701182e41c100501c103a005101d20382c006413010071540e6540d40030a00d075500c1842c91507010f680050134014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 658852949 1250 658851699 658851701
    0x9161d0a0b131a131b050f0a391407081c0306080f07060207090203010b0313020114161104091a070201060e1306050903040f050f1c0c14010206070e1011071503 70
    0x20301051030001d04241e1100702d50312092141040c3c000c14084480201050501303105410808141090302814006a40e09d130b4011180d1400d030412070302ca040c1c008841e00c90b20340010701c00341118041320050041105003541d40c024045010790083c1055110f1401248031082040032640ca92a0840200b14091404c40000d052442940200762100d00420040100c9000d02050700d40243c0041c952001130000c520041e07030300c40b51442440c6a900000311b0220a070f03010702c00d0081c01c1c050103159030781c02e586024401c0004440e000d150040115010020015900303a11080d5580d2240882c000001c040b6100d10110200d00b9080700d8101c40c0505e500c001300100101c600400e07030003220f200020350500341000204a81c0760403a004050259000c001514110b0b56500d2441c00c4100034140040050f11050030041e60302c14143c0150000e807036040d9403c032000d510010b01c1600c1820190380701044070005608000c960075400c1c54080400800c1c001203811080240b001c075006240115246089942d0543e001d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 658854199 1250 658852949 658852991
    0x12040812060118050f041401080c01090b07050601030f240507021b0303030a0207230706021501050112050a090209070f090501052109161d0a0b131a13 66
    0x20b410400114112400080c40d401d440d01500d004441203071080f4080c0c07010500400003220840d01c281e54580000528030070100f070035202880203907523400107952249280300040c41079600040981e40b000b001080860500544903012603c00c28420070005240d100c250a1044454101c03e07000e039031101805030041e01040150154403103d4076248122480100190300e900000b0720f1010042e80020342d441c03c001815a41d50311344003c1c91007104981c41c200b07103203503640c803c6405140003500c120000c04113400f80452056049a005a42e428005c00e91100890041c0c07402030700381440c1580b20a580001a550311100794440c2c03020359210f0120410802c8018071445007540a6070501200b08051000d80301c40404d946003190341c0307140001c001c0d2503800d80549449400c2c89081c2403075180303200114050101410507040300030f400044e18004d44406404c1070407605d500040d1988240d070080140441429500131011580750301803a110b0b13500c3c020380402c60300d4101144000a00365103846011601102c00e00130 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 658855449 1250 658854199 658854211
    0x16060b040b030f070603020f13030c0302181b0a09080d0809070b070308220c090618020c0c13060906080309130c05030f06060d0204061709011104030f0812040812 71
    0x7000c1c22180348440981300d00060043c1c0d0205a000108421001d203180103c1d194410564160351005950703040440c1d10014034002240300b107128208402c403009982d40d5890040201450381c01c804101d40c2c0c402c44040d0320042007501408044580010080c1051081c05011801c44c0c1310700301fa6184c00e09002d4200310041d0401c0c96403040504c1a4404668000402da5021503802051801c10190400014988032409030040540070940d0011445030308540101c411112203082110004042400c0d6006a00642e01d000c01268000c44206041d403030402c290303014142307030300b240040c180d03444402c48000c8d0740144d0047d85040c0d00000c0ca202c403905040141c2252007005138001c101140c00481d00a046c3e01c405408020b45035020804248070390ba910040316800c0d00d01c1c80c8115070f01d641d0751074040c00f482c060011109050310024000307605d4a2043c00741940c402b0b6051145494181180c0c0e400c02c800410340020340da100b405000c000803000304094242e00550080e60859140c40c030040107018001c40c01424 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 658856699 1250 658855449 658855453
    0xc08101506020c0424060c060c080601080a0c0e130b01080f011a030a0e06131101090605030a0c050c070e01180218091306060e061201051012050316060b040b03 70
    0xc2040040e5020480480110003200e000c640100c461070804c1c40712898042d00c6800d0160160001242c68001d00d0340059948501803d0000035907019042e12a81c00845030940800c2461300010807140d03080c0d1029440d18114102425000030030404510f5540c10846071000032a80d945501480c0c2da002481c0e41c2d8814060441280a0f41c140b001014019001030f44940c01260040301043c00051503402032540d01510104607031491801c91200d845405248100755504580c0c90650120b9512640400d41074400780d85900e4603546400038403078001c00124181c80f00700304060111082030030080c040d41d0b00801ca891420500c95040c40000404110074440050000340304104003605c0aa60f0000385038000c000b1201071116559440031207849039194040103280c0c525200e8085a10140104c502d4003c22003038079212500602c40315028201c8009407000e90015030303825010418414100b440300c641c58072843c1501d00300440e160b009400c0103808141141e496446100b5810f1900740f51050700c0b400101240 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 658857949 1250 658856699 658856741
    0x10303050a180503120c0a0b070305010509180a2a09020409050f070e01051303210201050601050a082a18130c0e2103070b04020f01020a030215070c0c0810 68
    0xc5d5240c21440b2150a50400856401c0c5080300a01802201d00e0b00b000c40c1604601c1c2046000303009000901400f44030315005804151040c407000e05004002824030b0060909140a03101c040c0c1e4060324205421003001441502c50309142080b11210013848490030160301c942c284803184003502c000a0405c824242c2c03c501300304225901003424514407200b800d00702c1e42c80391400f501003030b03140d50354101400380e24822808030014500440745100b40c50081c2d00070009600da08004540e148224240080050060008100003060403000c280f00c3c0801c0001d00d294020381c1c6e41c40c90f056a007000380031125903000404500c0344c90604900a1821604841c800c221005d54841d010f02000c0c4482d4000b8090825401c52040c07490410107102c940701001001c0740d445103000d1070000c0209000b1501240104c1031a0480c40183d400043d11468680d4141c029040440968821081e80200100b0701401c0200ca0850440270410f040c00c0100503040010181c15203613005201c074801d64103884100003800c81d181d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 658859199 1250 658857949 658857959
    0xd090501050906130b040809060a200c010905060904180b040c050f060a0509010309050717011503210e18011707030510020c01290a0b0a020d03050c12010303050a18 72
    0x4c404500c0da258015031901050722281002e075603d01480042c3e5822110001d818107005811801c09212510503d004850003031480d40301c1071f22900d9043d0351074046910120305000c0d80c58158080c0c0f26070304003d0800106003030501040726010319641402d40325007106400380002d02c4001d10020000c0c1106448503280840d403900840c400b480f0780102c660070400301003000c11481e0301c2500310040d00c0d608403003101c410507107075540310799800311248a1004a6103080d8000c41c9000081c2548811680c0002c544540079480031035086607040640440c40070441c0103c942d030003554501c02078101800d2100014002507052504034402c3c201e0350965824254069101003000075000106513882d9911142c016899038401e0b0102c5001d001c01c65000c0300480001213801200c000c201c885240040004c80300b04070303807540d146074543c994401c60110000581100406a81c9540a0f40042d40c00c103200c00f82c094a460142c0c58030505241003a0030460025200003420b000c00e5912516000040c005031500078102464a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 658860449 1250 658859199 658859221
    0x30c0f05130e0a050a080a09090e07140a1a030703060915030632151903110609030a060c030f15030f0203030c0d0206070201230402010e04110d090501050906 69
    0x2460050450310342d030082c0c1041100707001d00c800540e030142c01c175480e40351603280222458014603201d1001802000780080e16980d103014000302d82080c4000341210506001c000074019464204040d003003032440200103440d40d000c2400342e1b142d020b10102030f5140d08080c0002010790f00c9035480f12030725034108109000c107072039965901401c69510840010b03030061001400705040314902000d42d04915610020140d10035180483d500c159111004890050405410400092650501d400c1e9400d0441c200b0f1002528010041e400501d0050000c4d05042840340081c4ca8680c54070011104151981d0509000b15014011040302040c1003074140200e5112402c04401a00280302c00703000a00c1c2e00c0c2041080d07403030900403268181002820344032a0040310340041d5031250242d81400056203041f0340d9860106818108030074515060785040820b803501c0d001100c130701d040300300c080354031503070341c0f4500900b020b0490020000040c1440c400f03d2184050b040207421614003c1030b44025400c0201000048114 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 658861699 1250 658860449 658860469
    0x3040c080601140603060906012a021f140a020c0402071401270b060d0507030308090f16050105030603010b0301020d1a0303121f051005031602070e01170c030610030c0f05 75
    0x2090b87c109110359591001210400040c00e80c103000850b02481c01c1600003c078a1428420301d00a40b140d50352030b2202c070000c13011040d040c03541800203410321072024003001054004001c03102c60f80c4100c0c0c0091030a0b80014049a001d080110b410a100e481c0030a502d00003070165000120350000d074904400001c842d1b110038403480c903000902c4036082000151003960342e600100039154100c01242d12039500e900d4013034940582601c880505220f140148110740c040021040b2004204094950a1520b0f060055556400140c40c20340e00d5500c802800b042c07a14248080e1010f40100007010540e400c11103894a01000004170040c000e410800c034442c0c0000940302e506801c60300074101c05840104815011120b565117421865000481e0520700d580746510001850103101e0503480b401d0003a020180036a43c0e016a44592111006034000401c441c84d204501c15070b103003200c0c400395503804504500103810220103c0c0c0c3d41f48141020340e003c0c41441172890501c4060800c180a03145100d0402b4002034030048 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 658862949 1250 658861699 658861711
    0x3330907060f0302250c120503090d02060c010f15060e0f061605010204031208160806150f0c01020705010c020a030206010504230a0b102604051203040c080601140603 73
    0xa6107140d000c514860350483d036824030f0f05074a0710102620440d0a001d080012a000c0c1e81b0304031010350216040d0f0086040c13420480d40304004520b4140210280200c203131103e50182d0f40320400b0700c9555031628081c050005140c02e038120024110b58000300c40019400182c00c8007042100c6889204201d40342c04a9170744440c401120529154103100901039003840003420001d02030350020500008000100555510498294071000320a540d082840c8800c4100340c2803100c001104900030510714280301c102c0741401d8005404c803e1900a1050b00c5281c0c5900c0404002a01da500080030f0f024800300303114482d601350092024210000703194800030354483e4180a03080c440e81d45d4032031042d158211408102d40701c0e50001000500e43c074106581c0c00080101c0340d61a405050b4002441d05168840d035800b10f10905111b0750f450881c0003860b0465840c0c003008208503424443c02a1500352024401e01442c4590710403044485c4050400080d40d080060680c4175410703c006000300500d0710f50b2032006481d4000d03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 658864199 1250 658862949 658862957
    0xa090309060504051311130810050c28030e010e0c0a0602010501060206150a1a03040b01050906060d15080a050a03090806060a15270504050f06100f0e0333090706 71
    0x311100750386d001c0a00c20a100b0002903025100f00013484000410021104140d06008100f1039664128203079491081194401c884c040100c01c2030400319102e141514140312a01d00010302ca00c0060348a4219582082090380d158040b210b814624a007405036a4041c0c00d580c030003481030f5450904040d41d19030000d0581400c000491070001e0190300d5500c6a070004111510304a20903009452515010340d1043d80c0c00e5500e4580c2000104043c149000110300804000d040e0510f0315207441c0c0082c004003684940c1000510000c00f0010320b03040200414030342c0c1401040501110883e0380307005807024089034032032a00343d00b200d001c1000355610034003070300c003162945060f0351602800f0f144201d071007120f20540035049020703058036004442d0740c0e2400705058540998080080d526038000124800d40f085880ca03621649010050301403510a00716902101654146140f804079400002414a82058488103122001681c14403281d82545082010b40022641499850806002c903e888074640d0003820140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 658865449 1250 658864199 658864211
    0x6030c0105031b1c023105060a091203020102091c02030a0206090103020d0c1e030b0906120709020403290f0711120f090109230918060a0903090605040513 68
    0x8066021a031a0a03483d9010780440c03a007003a0400c0081d00b20b1146030b00c1d14499003040146c110251155048443c0c0d881ca03051180915180801400d6404488443c0400503d100b000070070035a00d41421014522940000d40c840302400c4c140020702e02e800c0c11400d80c2d941c0c03001da81c3c0e0150b100800c128050f0f03601500c107603030f40d2403c01e001a40a0f00c250061003070901c1c42d102030001140e900004c9043e2003403010040685e02280880d084041e201e1021400d0762100c400c0f00031409a14101d02d040c81c0a07912042600c000300c1d0b4031841e0100303d80140e8800e031102e050200c1034580c000f82c041644c0c84100d040c001c0301c44490030300c19801c02500500030840c100703120104c01006811002081100c9940c0030f2414841e41d51600c4010f20041600603287e00760116519000100d0340c040714a01d1054110341c00a40740a00668000810102e4080544815481c0305618000010320200740141440b5014190011502030f045240040c0070240d598004010841c0c14403090000c1d644105208901e54107901c0b01083d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 658866699 1250 658865449 658865491
    0x161106040b0a0c0317070e010207060512220209040c061206030305070201080c090d030504080105010f060c11010309060501090b0a050f10050c0c0303070b01080c04051b07151505030606030c010503 86
    0x117a041000800c0d4400c601c00f42c10807101650208001041c050700707a003950000307a5540025240c5016a8090300140c14803880004e42c140002034000c8101c41d0b07903001101c2071501580104005404c00d80302950415402442440010b40201480000300c841c50f804201d030b1031860310024503602034890001d04100f014804900000f13002c4060b1200e01d00d00400b004401d00c05490083c0141c2d029108814865081c400000b5030441118180e1003142d039203481d1a210b4500590300c1001807111408520305042d90350002e40d02280da60312916018002c2c6810004041501070204150340c0c0007980700f144201d24901108540e9201d440042140c1c8801e07003007140d210050080028245581180c0b441d4241c80007148403002d1000c00c0508c02d048598040c1580c1445102d0002d005c141c0d442211141060141e88206400c0180c50100a14459016801c500e01e4004800a40c40541e556150581c582e0544c0d00c100748014502448480d402040c200c1c0148000d9a0010000c0c0035030000038117140102400640c900f038 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 658867949 1250 658866699 658866707
    0x2030909041e060e01060603111305060c07080601060503060f031c0302161403070b010816330908010627050403050c060405061017060f13020303161106040b0a0c03 72
    0x2142d141d1102050028a51409105000f400d05105e03001c0020305010241c500b01e40702d68116190b801d07003006458140b901340310030b000040d44000c4500b1075074481c0d0000001d01c2a000d001e8203002c3d0803e40d840554a04200e410401d640421102c0e031846504110840562b03982d01071560089101c02d41030143e2031341078555100c85114902ca80241200030061042222071074040010000584074180580ba04e07602d403408250f0b1044840e07a04800b800c07441070203000040d052075400e2100010383d01030704c900c482c9006102c91010010226a808548141d01c00d0012a80a01a60001d403401421043c4120303c580911b4850a294541c0c40501541d6400401e042c5482030702168190310480b001c9560509080c5401540c8443c2240c00e400c1554110101260355800071118020b06040c0d80c00078201c80d150703110104ca001d00041c10a150039515490000c0060f14184080d29200c41c4050141d07032000c809051404041034450780e20f038411081000184150071406091341c0041403d45040c0301c80c0300480c5807e031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 658869199 1250 658867949 658868003
    0xc09140c03070e2106010f1a130302041104090c0c02030d030c020c040209030307050304170c0a0305060711011803020106090c03020306211509061009020903070e060a031a070f0203090904 82
    0x100c5800780c0382c00415181040c5030111f0440304400310444012000400c0c140103409142062000c208104908201501c5d09800041603103411140080c54a5950300e950012503101d00d1120700460030681026003503180600c0000c070900a0f07810280b000c2d03000c220000352100c882d000541e00c99a07020036a0b03041914104141e49149500c0301c2201d03580c07522400780394110001e00c152a202ea10807000d460403503007020000d880440354004000c0039603480e55001036070361a040d038039100115035950a41601c4006408050354a590084d000082c0b01e904000421098511011018050500400070704c54135031525840400c440e07509100060b070319005588414101030611611200c5601402e003072007030340940490302c107014000f040a088100390351511040140d0040b000c0140e819004110208101c401c201401c9510440007894040441d4981e6200404078a0b0440300242a0084504000740c9030303040305140c0300c0c4500d40e00046091805000029100d034000920042c03000c01c8076491844051050402d00c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 658870449 1250 658869199 658869259
    0x12090a180219021e010b010c0308040f120c05101505151204200108060604120309150302030f070e0d0303020f07050d02062a03160c0c09140c03070e 65
    0x660b44410b44008000e5071004c15000c0d01c641180d1010714008036460504c031b0741d00f0f001d0b4103031602d04524a40741c8084e0740c0c03008000c006941038000c212148001402d02d030000d40f0000800d0711001d07100016801c060340740529098200042514259200e100d80d00b403080c0715003c0700d60499900021040c002c1200070305000307003050b10300500c0c04913090004014102d214504030109a05c3c06481209616004450f00030081c0c99003601300b40f00f00b2003404400090458000c0480c02820440ca5031582d40a41460000c561101040001c2c1c0c00300600804110344c15159401c402a4903003031f0074001514000490200c1d500200605055000940410552440301510481a01700f801d13140d8521106401948a0400311070440391000c03002e110a07000c00c001400c2003104102034130039a04554801200710300791151111400240401245103400107145003240d003001d07280020003c180841d1108410307500306005000780c0010712007401000501a8040068203840004a4401c1080810101102c00090300c401c05 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 658871699 1250 658870449 658870477
    0xf111c200a09081c12051b0f04050d0c0f0f0b0327150f280b0d080c0c0a0909030f0f0909060815060103020a0504090510090f0b010212090a1802 63
    0x901140403030300351500b41c1104e5191100c0c2c1150384030000d240121a0700319a103004804046100c0300d07015030a01c000d86840000c11008a01e0306855400040241604820441d000719141005112042409803202c00800102d49000f46280c07c0002516480c04010481c440d94001e462421080250742202c0d412022410401d1b5845860106445d00d40c1000031903c0140c2c4004440121b4481c800c00c0e00f403034072100619106040324070055901c003401f90050a0b001980242c00c7c0394070001103100341000b880d09501220040c00120780040a22071080030a91003020740900c1c254118020940054041041c014203150000d040001d4440075240b14100d604402d104614102c404030b0748907400100310b4550002e00101c0c00a580d98440110180e00c2140301603000104280801c1105840340d800640d00605607003404509142c9800c82042180c1d4440c51140310103494100900076540c0600c0f0241c0039a4120101c2c9140031110b00100b012918144580b03d160808501400e410349640d80c151001d45103030381c00d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 658872949 1250 658871699 658871713
    0xe06040302060c0a020f01080112173906010e0415140c0a020c030304080307082b020901080612030315011103030403090f0e04030207050d0302010f111c200a0908 71
    0xf2000ea588009020490003150404034107043d83d8060100c0a0488000030026824543d56940700d080414184907031044100c0300348403400900c3c2030305184140702241000d90802402003040650900013042d040a20540c0091005000301c0800702c5003683c3c02500454000d502000d085244001024000303142c0710780710116008d1291240183c80117090040b0240d0840e011600c0100030151288241c1c070605020768401c110b1100000c91400280401c0703120780d100c48803210250610740170500260458041113590003d00181513607088120960004c03001d0710f21595000c3e04d20380d429564030000c2c10320501007a0400c04481c850b03105880d05203407442c0c5602942c0d02ca050500d806049024a0f0054407448008503402141d07400030400010712540d00756005128032841c1030107200100740e0100094085549980c3c040b09400d1540c05481c0e1b81844003036069a461032170a2044040d80c143c2c0402c071400604083c082041380c81c185a40c0d03225a0b000b20790081d51115489000d0f80c1d01c010311f502c001c82c0c0d4020b00c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 658874199 1250 658872949 658872967
    0x405011b0203030c0a0804051203120708070215010b040603060602030309071e1d01060908060411040507110d0905030607020a030c0210180602011a0a15080406020c0f0309040b0409120e0604030206 86
    0x700607004441c2d081d101b81080c542a2040c407504d0303004a40b118180ca5062030b0004cc4414400c0d14010341040c0c1900503208000704d10a02e104c0201000d0b0880140c0303c9001030100600c990500c500c400612217407001d5825814460b10980e05c5180500c10351448649110f07203030140390400c1d04035600400c02380000b0303002d028604000325050f2109200d03074408600100c60002d018240454454031580e4407000341d004281d440810040140703005003141080120b0003e480d900c001042045e4452001305e501d40440c035a14080800d4545040200000d0840d08040c0d48000000c0d0031420030130398164116000800384003041c00c2141e12030f0400d43c0c01c5109180c030b03000000b0815019807005230b10f020154001208560382c01d040c440602c1c817510a20108403c0c04130003014a510a01500783c0003440f42001518108058000515000e5481c01c0304010381c06c00034603060680f81030320a441411500707603014003007000c01e6100c02d080120301c8082c0c141031080540705400340e0b5030b0340000c890143d03500601141d140ea442c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 658875449 1250 658874199 658874213
    0x16020d180b1b010f02090109030f0c120f06050610020a20151e12070503040303320105240a0c020a090b010810031226090a05120405011b0203030c0a 65
    0x5101902000c0d4603000b0024002113032030088803031450041e15030248491071680c4482000401850540c2c148840c5240411002c03460890040c2250107511050585569400e0103c202c1714080c0440303100d1102c03106030750031040d000300e88452025017140352442840401e90a01103285c0d0112095513000651292034005180d0020203031000854881c04192412072001b4122100d10842504400100c150300004000900c41c00c01103034060b00c28030f404104e4182c00d11107060204a00004d2418012240e0844840815809906401000c0848440001c050950b800321101c1c124000e400701503090010304030407a03601445400040381d50103013072903448940e10b9210000604050100c0c60004480b280400c001e11000c0d0345e8241601c0e000710465407020034802041c0c0d66405035a070051601406110040d205d140100e03481c078425039a0700d0150401813140e10f003240c00e00b45030f00000c04d40910148014845a43d1001070803803481d01203c0e00c0e5440c05480c0c0002840c50143c60031844c050300c035902c4203034100009 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 658876699 1250 658875449 658875487
    0x11060f010e011203090e2703040524030a090515090105070e040e070e130f05060103061803021b060f0c07180c02190204020906040303030b0916020d180b 67
    0x210381c0d65035200e070340c0b9241c07002144a1000b8000c0c0002d64074460070b001d40b00c0c2032100d883d000b5400c00b0482c2d4030b20b178405d803a42100c030002c119406103075000441d0401c03403410042603240c3e510003001929a103d1402081c084102e01000d41000078160340ca079545010031508101ea40032485880c1004801031418030141c5001c2c00040b03440d44005a1012089222410180100303030200d14540003a0420f14140754200c1300d224001007440c4014840701c4089000704201841009a0070b0203500a0a400c1d81541032a04c182d40803884020301c0c4541040c000b002203540410380e407140a01c2240f40c410781070400740001c2e40500401a250121500001d01d818400307000040c2d180455450803d04c60303180103400c4c0c90704100e0311466940009600300e074120f00e1a1a5902070380c041814801000142414400030100d45a900260011404a590760145003024682400c85580c130141d0308110210412840d80003d4603045079200580c10f00c980412021300303041c400782941011701446a080e68486d079054402111a9034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 658877949 1250 658876699 658876709
    0x201020c0f03071106190311091c11011106042604090902090a05092104032901050d031407050a060c050904061a091012050703091b03050d0c0311060f01 67
    0x7413440c1010050704211007501d80364085072050390061910f2480907006010f101c507400310105010013003074880e41e4580c44004010306207003034002c040d5a500d06d80702200090210840d4144440a00c005598010000301d0590040d4410307400503c2c000c01b64208012401c00c1080c125104001180c04a20b404607640000081d074000c59030190180c0f20001c01d041150010765024076150082040048072903100301d01d1075151340c1508021458241e43e500c1d91000d100329280990540d0100424062207010400416405003200703d500c0f5840e401907503800f4000c1c1044840d00d128000d00491034800348481840100c804540003182840040c014040003485641310710132241c400c070314002021030404a02c2005100c0e40d20448a5145881103410030044402c1f007601d035540c200042040c01044030700f00e500400340142043c4d01c2c045400c004510f08250801c01450003400003522400d020804950002442080d041c00344c184806001c3e4141400c443c4801000440d80080c4140c60502c0701030f40400110078100c0d4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 658879199 1250 658877949 658877963
    0xa0207060506010305040b0610050403020303030106201902100c02120c010f09050f06070f050111030402040b0f010f03180209010b120612101505041506030e0304061d010201020c0f0307 81
    0x2940d142c0c019801c8520555020b05010740c4e80000036503508003510102a000078600f4558200750356540003030301c1d40d8402d030400c400040700c4e004144c000c0d5040220484108241030060000c40341c07088a682c01c0e0503191080030748201c0d1461480c01c1d52138010a521015540c02900c0d0b0050580c0c1000f416035145220280c9074000340d02e060340c044005200302e0203582980c3e0010007880c003d0100c44100040c540003500103580b514040554480040c1013445880c540a03040386119880e0300d0b20707004120441c2d01d042806801009844288056030f80e12003010340e05e221040c20000740000c1d000c3c4c1c0d6170140c1c55440400070340002a041c0081800c02810010b403240394210390036283c142e0b036500140207008400070004605540403000a50500c925500580c1810b1004107168000684e103800150640311020607803c5c10070109001130181c154140a80e42c031003144180203500d044d103041b1009040180c0300e1010403800c2d155801c039060350b1b8400c0d01110034030000e00044840c64604011016125441007000315200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 658880449 1250 658879199 658879201
    0x7051c032c1e060105041a031504020a0b18090702250302040510030f080315040603080c10180206161703010e07030c0f0e0a03080c030403030e0f0d0201050f09090a02070605 76
    0x30260000d001d01c81007444050a00f0340d00e40003d10001c3c06201072040404208040d10740c40340d40b010481c0c0c204d481d820300101b40050a15005000c0c0000c010340041c00a604100120f1011008008500440c614151024005035980f490102d00700120003080c8080c11100c0d602995024002149a0b400d4038001c941c104080e881c4c0c0458500119060710004103082c42c400b000c840418074810207180e203c24606604000c01b62890001021141503400c215581207011544c1c0c544460b0400000c8500d07005010100141e0120316101162a1811440244182c0c000038110044062110f0102704050748504454400300614201c81c1e1140c000f40200040d1007480c0d0000754105209000c3c40c4001880303501c5152440c00800d5013116540000d8180350341081d0300e220000002010080200340d18159000079613203680c114500182000000f040291203401c12a040c0a05592500200300c0306035030900b403840e52030704800341031003550103803103585548040060100500042250014110f051140d0b00822407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 658881699 1250 658880449 658880473
    0x206040f06030e070f15030603050102040b0a021b031c0521041203090f17360108161812030c060b0d0308010b0d0204030203030304150605010507051c032c 68
    0x19130035142c883c002c2c180c500180c003000811074428026240124618012550903200d40b10903080e40c0c0b00d588101110440040c03200003895041c4070a0040580d030a111400d00c046120000743d40d04004200c0b00341055504244021440c00780c800c65a08903480c4209201c04000c00750004068481180c05440210201041c0f8203140c0c80f0303105101e151540301101100c80e400f241c880031110b50000c7e40c0c4081c800c10412014503204040302d614101c03500d403120010070f0f089001e01c200500000440e055810b1000813000d0244c010306950103615000f025140c2110743c1c81d0300b42801c2440141982c0894a184076503200784003819440019081814000c44051041190503001d101c0f00c61840d10300a800500000018010b046482c00141542c0d44003480c05410540c590b000a030840e803013580c04581c0c0346d14150312514005c08601900c00280390900b0842e0030038040fa00d4181e01ca4042c600d20074610301030b0b418910550303402544200b0100d003011550b04502061020000d080c2c010300340780d16444e03204035a00194 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 658882949 1250 658881699 658881703
    0x20d05010f171203071803020d260405150a201510230a0f090203040b0903070f0627030329010905151605070603060905070503071b0206040f06030e 65
    0x2030f6030400d4460b99145a945030030448108420548001c10803428000020150350303150800038035a40200171441183c140403800c00c1030701d075045555580400050004010035038038560b402401410200a6556400491904403003122011811540c0c000c481420701c0040c0b000090800c80411541c903c03003845840f0401d282c0004021f500c1203d403640080801a0070a5809d40b0903298884c078060a000d550300c0d1111040540781003660070103400f650380401007200b8001c1d04d400349900170064001440c50f02040342c440108400402c903000d410b107611002c2e00300b810f8829903000d80b032043c0e01181e402640800342c640113024082d10300d800484290310503946600c0710a038010702050301d48141c503446c02e41854503052154175005c1c0740c14102d0024003405040c107110241181c0b580f0f103510a0001d820310728141080941114026000400d000d0320300b40030441101d40020403280c100002d400c1140c68045014220801000740000094100402143c0014503c103a1081c0750191103040e1000e02c6030030187c03c8070719 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 658884199 1250 658882949 658882963
    0x7060f0504080d0f1503151b0c210e15131401020c0315011509050406060c0506090102070b280f06090b06030c0d022218060506070b0402060904020d05010f17 69
    0x65040d543d24807040000420001c17007840180c24288002c60f4001e000c0c0d0743c01029164023004000452071818209007000502c50b141400c0c0d20541c41401c05010025078000c0c0b549103228040c5016441d5450400d651250500c25218507459070f000c03014505480e559003c0d6140d00e0340076510301600c5103440990306841d0103c6c1c0020324000c0e0f03100d80365850b0720349103a4244c07104112040c0410300851840100383c680b100e00418016144544906d005e501c0d961900702d145c014000c2c00554a64818069880050641900150490300c000c188800c90b034106550b030402641c2407602c401504d46010000003003038800744c01040803506200303020452030360400d00f40600c901c0100d5216800180400c0ce170780c2c80f01081c4d4040d10140c0c0350000c440d00c0c001008100144070b20303116044004080040d502c851070403a4a40100700c00b0341800d81c3c85ca82824071581d10101c4c62107010380b0081c4201d40110f511107007929a50305448180e00d00f0030040c0b115596039442d40b2804180e03409003884041d8200e580022000b8001107207 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 658885449 1250 658884199 658884221
    0xf1b0a020f010f050403060e1606050a02030418140a0501090e0c18130b070c0b10030f0201080a1e0213080c0307141512060a081606030207060f0504080d0f 68
    0x1515050300718400443d80d14400180c90000e2000500010010488900c030300c51515403400c0c020304410404405001c4030355119807144007009820020000144c0d1b0100603202150558690001040004410007000d40307030503200401181d0404081103002d20712034001d14121041c258040084a040404060300e441c59170701c01c0b5422040440d0001c0510342c09440141e801000f01d41044020f901d00da48101c1d80c64820340305032000038a24128a414072401104854001c0e0603200f08030381c0f0a1544d0340d0300c64a03030388000b4085d05200c0c6581c002482c1e16515003000420703441140e00340426100000821009421500c040c803040c3c08582800701710600002402421810000c00420002e850031101c0c0c0e1140082c80d0704a5009103907040640003401502c1d01428404c080e440c00131a5034904002031003101d81d2a5844000903a05c04405040c1540c3d280154505440e80c40c6005a0b60f00030368206000689403000d285041985021b04200c20310056902401d6240d0a0b10720500051318604ea200068551120078 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 658886699 1250 658885449 658885459
    0xa030e03070e0a2423061308060f1f03021012060909050c060304170c01090204020d02121b270a06020604020a090501050f04020a1803111207030b01050d0311030f1b0a02 74
    0x5200360110b4036112100c10031400031300203071907d240105821640000f5501c00d005540c0140c00748030402c0c104003070070b582c1301c1c50303d403402c000528510b40214006400c1e880080d008815801458102e980f05605120400301c3d400c200b4481c0542d07414403d4010003443c04190341c1c40c00343c0680100c40b890300104683c0035982120a1050a01c6400c2d0020b20f55071011849580b60340d0703a0440c150060700e441c0003a00c04d0300058900140c0b00c0d1141c4801c6120200d0081072121354464012010304400940019079040003605410f0401c0301c000035480001201c50b900d11540d000c0c451503400034086070300094039441544242c0300410380d01d81d034020346020340b0802c0c001ca55002484616021b40342c2410303405000420010b1a00301c0d18408a540c3c403030f4903000150401d550300c8074100c03080081814100300d01440b035080780c0000e0100d0382c0342d920b074030540300f906014051180b44010001018144204803807188601850140c0b942c84000581c0c1501592050303503071280f80d0196511040d0a9000455102d94054000d88 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 658887949 1250 658886699 658886729
    0x110304060e0304030512030a06090917030a1806060609060c0510090201050d021b010e031314060f1902011d060a0c12090b0109050c0306030a030e03070e0a24 69
    0x2a80034003401c980d0000810307500c020f01000011440400840000601c407441079a42d900b450000030042d0781040c0c02018045040c41c1c1e4180001e81c07545410310000f42c0302c80c1274a4036603d90100c48006804072040781042d16041c41041c006000040e400354049a01d03c1c0c031089406175540751700741c402d04807117070021b03169800c2640f99080d00d0142d50000340902d44140b400c0f507d00b43c03034100f45000700e811107280c41e10181c081c0e4041c1c64005034248200c1e490400588021405d1451540360606010300710f00802d00702000300003407030540361900000c0d0740b51111080382d4285c8403421440240c41c05039075840b40c00300541c01c100b00041c000509111112070a81188060031296903404410406045e00c41400d4081110600b050803e1007200c0c800e41c0030b414401c0c05c1020300742d4900072008094910261003508454410014440c6603580010144240c0364503003890305020481070000b034103081807540004414540c0c48200155004030307a00c0b043c08000d08000e0b000e080060700350064412007041c0680c04110845007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 658889199 1250 658887949 658887953
    0xd11040e0d170a0b0603070c050f0c130e12160b0f271c02010207110f031903050c0307060905150907050f1c030e1f05040b070302160602070f060201110304 68
    0x3080d10398488035442004c00c20000050200b601c40d0300840d070348000903164023424000c10506005588040d52194028401f46080c00005003006841900000101d60341d9116101c00c0101402004450007410312400e4a6098035080220b1041599104407040310403940041d08000820341d050b40100082249292826808400c604480f0141c07040e0150510a442000880b0810b444000c0c2a0194a50025845240c4ca1400f081078403008a8064421010309c010007a43e520b00080c800e00640d0045085102d82c2c13000c0c10291002d00c511400c0407541d000c00108001408082e40040403440d00c208111400c03500507114003c5401c409860000494100c00d204000b076107490a0301414040c00105640540d2407030322009042c84040600840102c3c40448503ca62454400010950b00c907010307404d98216414000700910b1845540100c042c42040401d96005041c4204140005c1c0310401108a000e25102c2c1000380d5503181c944200340d4544e03c2d10102081140c818001c1d02010180d00c2c5c8a181561526 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 658890449 1250 658889199 658889237
    0x100203071b02030c090103050106170705181b0f07020a0501020d08040303051b4b0703032405040e0102090306040b0421050a0e040c050d0b0a050d11040e0d 68
    0x281c4800d0307038144568154045580e031040c2d013040c0294801d1000040719840e0007403002c0046034104404000f038009007001c000ba40c07100c00383e82d01203040400c50014580c1e10010303517184076039501b44404100700c80440c04200301c03201c50005107585c40c0206c440f48c3c05190744200480e900d840044d03004000513120008540001e002e038000c5600000100079442d02041c118a441c0c0c3c080d0031944641c06040c012900408600c44d0100d1441d58241d600c07105a4036505c8080c00b070b01c41c1c0f1101d01c502264580000602c080c18144a0380c0801c00c0030302c400b18030040c10b1001b02c080041442d920b0042c944030b0351501c585024140814801c03280c00e07040c0a00502545d54658a030b01e0440c0c40010000e694068a411044c0c200402c02c200c2440d88500c55150141ca51b00901e0700180074803a00c03000c09004901d0201c4414120390400141d40c091a25110040707200042000801c0282020740c0c001c42c0c2140518a41c442001901e2a80041024003540d003008940415030603c1e580f8092003031208089900ea906004c420100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 658891699 1250 658890449 658890497
    0xf0201020c030a1a01151d010905060a0302030603060f16120b060307170105090f0121140106090509070f030b090102040807030b01090507021f0207020a05040f0203060310020307 78
    0x1401600e05401c14007000c203041c1188039504440041c1000d42c004407401513038640030b000d403200031000460768801e07490203800f00d803401c0c0181d040110300c905261026031043d540603010340006040705031640028200640a074100b03035211482401040d001850f05403044410300c0c40344503c0400344241c08000314043e02d035420850501d840240d00c40c065505552100d6000350b00948907035848107222004002207843c1ea80041e003099203e0741002c4d06108018000c1c6020506403906250a40039644208410b15003c0d40084c8000341180100e800b41050b802066100004a07110a0400d00540e5947c045490300e0304034601445003074402c0c2c0c0f6070500105801460f9142d1000341d60340018a484d0301e0b07110741032400c510313540101c80d2600003100501217403c0b03e00500b504090381d8002807881d04030710191080d4400400400c2e8480c180e01040c0d0006564510010300020180504104009941580104003960080b0345050003481801805183d010715031085030b00ca07030380e140e5856540782114100e140b01e01784 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 658892949 1250 658891699 658891703
    0x31b060409050108060712090203030901030c02030903011d01060503030906030a150306020f190503160e13020d05010f1a03070c02040f1805100605030a14070f08070e160c0f 76
    0x14003400081540d005030320600c0e01a000781402400b1a182c103601c018040240045d86501c0c80f03040880350b03001078a0000c16903003190f8090a02096017804c06408038914010054500da05600f0016441e901440c6c1c0a900b503070b03101c2250000d0000c26110002d05d41c2c2c910135106925000441000001c901c0903456211005021821800300ca0f0643d40791a80d109a82110403c50542c402c000381c9918442d5000c02901850038242c02c140f411071400300c0c0249884103180101300140b0141341502100390795901d9040c1788000c154101103484040991645000b040c090040547e0030680020100d04460070001c6401141d841032602c0c1e1a6503075040c000c5413410910003049802c6a2942ca00007030754419400780000e641c2420502000190302410510700c1c021901e10340d4841a4900070003030010b9200441c00001c5c0c5908888241c981e00b42a4180c0c03071801182c1e03448400c3c000045100402e595a0101d2010300302c40c0861640301d11038403007140c1200785500e071100031404a211810680000740b0202040c5400764 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 658894199 1250 658892949 658892959
    0x3110307080706120b0103060503060f060f0a0906051504081c021501150e090603070b09030a0501050106021f0b0904030c02010306090c170f0405060601051308150a0e010902031b 78
    0x281e99200c24034600011a044000400c0d16021907400d40d00d03103449416409202403a05024040c07074040481d03103c10020704088500010b1400060050f00d0741c452150303c0110103089110030b01d641d0000303080100300c1401417510035415855000a0300703894106841c265005100a0103000018440c030706a44c4411500c507009500407007101d40369400200c03000500801045610010a14602c80c004002c00103032284175100c1c5c0004410300890352000a2550207882c802403603140d46918a1000034030f091160a8014030710741c00d04001080c0319902080b419881d0700c04007080d07900a0000c815480684220140c0359801070041000100424403c0d00000f08603401130400040143d2100c1540094480e034841c240041180203100d07103403c1300c010300d203d680711552010356440c5050039607d058641230042c0c05d0300d041000125110181c5401140d0b03d0300181100411900da04420940c6102c0b8400115081400719142c00d12040303981006020790203016500030054540c0407400390400008205407084e00d9005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 658895449 1250 658894199 658894213
    0x90c12250f020f010f1e060f0902070c15090510020f1c052a0d020a02030c040b210a030f0e030d080c1303080c0105130314031305010f060509071107031103 68
    0xf480288100300c642508240041500c8021090180d0151846106010f2072480c00c44100604c401807034141c0162074000c000565204001e040005101e40301d908000300c40e1305a070040ca01201c1d04061020101c90080c1d071550342c1c218a5400a0f40c440c00380c0c126200171900000f40100e002800041800700c954807a04020381000a10040310410020300c00103505e800c40c0910b0600c000110801110b0b03200c2140740300400c203204140c0e000c03a860b240c0d071100a9000320b4981c21a0703152a0b941e0a402402401001c0601284200905129540300122201a004214240040c9078920700c202403103010085c0150003000d0380030b80520304591005004051500c050b100707100100710729005000c40030042d8041c2c0241500c0d030029103030007400c40d44050300361407020305440c005500180c1c010700e0780400080e812001541b01e6480000085844d929504004c1c2154a000c07440a041c103460b910a4096071f1060303407060025600c0504c141c542c0e03039080c007440c0b103a80d205000800c0015640c1c900d00c1c82401016042e0345c00c0f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 658896699 1250 658895449 658895473
    0x1050304210f08160909050604020412050303070e0f01020616020f0d120f060602100902040204030c0e10091815150b0c0c040203010311010305040f02090c12250f02 72
    0x4498514104100081e200201c41081280d2141c88507410120813070b0f107040d0380c1007010805402150b00c1e10420b249140c0b11400689030307a0302e9a044d6401050b011b041760944a4481c0ba00549a60085540102240c28110f034442e80f42040c620043c070802d81a0001d004c0307615140d2080320220011b5503003070114031404440600882e0b00307000c0965120180e0b210007005880d12407482041e1929603013070a03044c914044041209503800a918246501c490000043c807210500114000e132040d608094035178810318000040c052900d401d140e1049001d4804846031076154003654058402c101d220058400c1d40c4003100340443c0403024a044421260403000070243c943c42e600014800441d8081f035500c07400402c0401d002501402810311a4404030f904502d1503040d40e4845440140840703032281010b50ba8000a01004052082d4145464004001141501e008050040558040340540000c1c007217040c00300301d01e00c00348904882d03011155042601d094401c180216084100032500b081180314032501602 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 658897949 1250 658896699 658896743
    0x31c1a060409061802070506130309080d0903051e0c130207021206040c06020106030f080f1b01060807060c0b01050607051009060204050a050105090307031202010b0307090b15030f0601050304 84
    0x1000300445040443c0d020300d000194061400c54038412800f003801045404001200492004c2d841112003200b4070700100d01c0d00701154200030b6500180c030a03208490150b59404d401c480342c04212031180e400c40c1c105241e03588000100f42207485000d00c40b680409805003007881e000003480c0010400e020010700302071440d0001101c004118400304c030340350071441c00e100500c898240000090b052a00085c450385d0305d140d1320f5810203810210080c0600c940482c0a464280e07a030b50846841c80d045401c1a2050140c45d01c240e0300900342441408070a1080790000038415004440c01140260400020360b0705a1802003800940d91040104444034000c981c101d04032500140314400b5828001c150060700d640c14902401019203080e0070560520205000c00a103d9400140071001c1c0c99210702c00c2c06030081118816400b4000d5600308a074980100007000c58800c6050340700c40d90600003110000e1039404031000c41891844255908000d0100350700c006422540240700840d002072041000382001080014899 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 658899199 1250 658897949 658897957
    0x15060d0c15020c09160e030a0503040308090d06091110030b0d14030f0304060e0d110316020a1203030207170a05070b04170708030601090602030306100e0f090403020717031c1a06 78
    0x410a88503000c8820343d030306d41c440c5c002e011828055008001c2034000f0703100c0507500d000d140b0000b80708500001e184400ca4a4800d404500c855010b0000c0c400d416130303480c190848460494000d030060103059140003403140300e402407208601025000c03c2d1750723000c80d48413602401f00c0741e0812610f51104121402c2d043e441031004510440c01120001660310301264a20305042c41d0242d003208021062040c5800c8072404000caa001c101c494658054800b682e101168450100e0760000020265000001c0280b6416800400c0d80521840101015061111000d0001d02880703501c200000c1040c00030360002540300800d2600603004030010420b6882440468140e5403204500701c401c0080030003840010750304001c201c1c002e082580080c505501c1d000f4041404800112044410045150034406098861204600400d0030140000f5400d2030305007400f95a84905100d04940d984042009800300d000c08401d49900380c1706410b8040e0b4071452140000050150080c25541144244d02c80313442940d40c043c010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 658900449 1250 658899199 658899211
    0x5210108030301090f0c050f0c07030b0702030919060203091306090612141b100c020409123c0e1306060e0109050922060c0215060d0c15020c09 63
    0x1c558a40c10040c0c00e106813076400b240c0821507820010004501a009030598101800703541c44552280e0144c8a510300d4a001944050001c0912000703010601c0e5011004060060b0107a4490700c0d030100c500310540b9a400d1038070600d03005800c2800641458a8207407100781e000340d203041d800729542e40c9a400300340849007240e11804100f8200700c0c03118200400c00e01300408000c800d002800000c81092040300ce04495171440e5403140f0750101818800c0c84c040e4011060080c6c014004210b00310706442c00c12000ba90503107460300407d49000c4e4420228403641c9920800e064102140429010003100340d9024a45071805802070014403010b803035246c0c03074000a0250000061034007180c0c407490800301038811843e00040c00d040000c2c121013800715840e51a941900248031003688279188000c4a588090b5440c01600180035034240328551200703550018030501c6d40140e0800750066a124a010006068640c3c0c900401d03082c8031080800c01d200c8481c41144403e040b070b0055071044070031007000411710a4120b440d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 658901699 1250 658900449 658900453
    0x90601050a080303160e0a0305070e22030f03180f0b0a0b01020106030c0506070206040e0406050604060504021c050712060f0e070207050306010306200301030803090c0105180105210108 81
    0x108030074501821000e009160701800380d40740d800c0010510b541d004042044205000500014002c142ca4888001000310b030030800b910802d98a50100403e03600c0150b0b03014886401d001025448041400880c000d6a40c1c1a00c0c1c14805642c00c000c183c010b800e1085546640c10b400700e043c80d000c640e0015a40ba0800e200780d0f86080c41d032a200c030044003114089805a0304580c0752000a10010b150103481c4800d66004440c2603446a450340300040c1203220795003180b1441c80b8481d0902081041d10380105000303813002c403001d010598980003408105c0c022404424141e003101e891901200b61a43d00c1346400903100d10b4480400075410078284182d858075404105103402030101000202500c0318402e8112610348050039580d40303071030b0002e5030340d0206000c043e092032741d9094846141381001d4070102c110000301c1c92241d00c0f0b607034901340010660030881d0b10341101d006035650440c056110710125100c406010800c4104c0081c044011107454001030801704206000150b8081c00f1401c1016441c000d044100c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 658902949 1250 658901699 658901701
    0x3151b030f0509120717040b070f0c05030c0a330e03070e0c0304030807020319090602191e020f0310060f0b03070f0807030b120102210f1305150906 65
    0x10704401100d80c020841c2c100794100002c0880080640340498803002d030000440740035440781c40920041c40c415a40160900d80000031554100f120381c0940c030150b10f00920040d00f400307030780344185501c0349290100c156014180700c0090026014205801402d1400c0826030241d580584040f40344140c0ca800581c0701180c80289045200e1a040100d07034003034403003005165000c1c01d10280c880042e00001d440103040c0000c070000a5543d910800c21703110b0b11941c02854101c81641d509000d800d17040d1500030800140030f00070005d0340c4005210010242c159002500c0d0003082010400c0344100c018030b000c103da201002c41c4c1002d016a4080080b0403152140c00c0c4001605840c05094417840c04d40c0b5801175070155400c0c03003004503a40c0c0002d00b2242ca200369007080c1d11103179101d440c200d0041c803213400398950141c818207031503e50701015800350680322142408500102c114030540c2c8101c8504454622442d81d00380c00294919031040c5407402414860000c880e00990541000245104d0840f603c2c036850384048 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 658904199 1250 658902949 658902971
    0xf02030604060b0f0a032712080a0b01090509060102010f0f0c020c1c060908040b0703111e1c05070818040f09020904031110022b0b090103151b03 64
    0x12103020000d00304508014074100c0c03501c81c0e0350300713601a5504410905503101000d07056800902c0c00001c10420303d4020301da13203504510f00400fa000341c004201000411610005407041118400c880d000001615035001140c500410001c41520060005045540303d144980d203090b0640a68244d1900c1c00c5004a960044410024a01141d240340e6070721a003a0359115512940900350090320310360300640003061100090600700424403590340405150000025690305260703004506a44915017907085d47c05500c10081101c46514403070004017180d800c03080503c0c4415030340c890b81400880c01428014103000181e16035a0440d00300d441404c00d02da5410510002c00d1401d4881d484010401d5502000444020b030003040717400900400c010103204100301c80100401c01000101100c035181e9205541c0d50b100c20051509100e1741054020140a1845000e0347c1804c140c000c03800348000180c0f0648840c2e00e541c03600c4441c0c0600c41c1030b41c0751181e514a05141c0c4040c0601102c1012001c0e5100820700e01000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 658905449 1250 658904199 658904201
    0xa1d071410140c2107030e1f0809100c05041401030207080f160209090705030f06090c010804060207021f1805060306060c160e0402010f09051c030e03010f02030604 72
    0x11024891142038009038804100d5000b250500e181d2200c0b080c619200c2c2c00c80c0c6841031070122151020144580b444c00810030402c0207500400559120b9644c3c00c200c80c1e171080a0040c0800300c1c00f62002c40c2e80030204002c110f079202d9250140d01900b420300300e0b41d44005174115403003110285c079008000140000340a000004c690600312000e19401e2038110720307080c020348509800c0d0084032a40c1280c100006131052100c001e9400100398260001d21801305410300c0101c1956694203841214040d001d41040401d54080120b4001d2040408074040e04480c0c40c8a801118400001001140c1599090001e100541c87d50568003000f1203508014181c00425468080c28000000140804c80802c1131402d0085032501000c0e250064410796005444211483c11142003451580e0003079540caa6500d00003601002242215000c1c1e4000c0e00d4411807500a044100c0f14840c65024290300f2058150b6044907855920b02c880d00e241d40603260104030000040002400d4400d00076504003400c0c0c020050243c24509 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 658906699 1250 658905449 658905479
    0x1020403031d030c01050c01020d050108161a090d0507080a0809011b0f02010e042d1b0215062106060a060203070201020a2306070503070e1210050a1d07 67
    0x100030490940d0015610000390384104d900101410808007040d407545140094040e110940480c400c14401580c5489541e551002401d030010201c215208001818103155064030040c603030b61085c520303d00710f401018042f0300c4035400001c84961040c0d0074000380c1c480c8140006031901348552803c2c3d6861030000c0004260441c55541419200d00200d03600e000224942c0b804001c460b82030074103501840e485000580206100c80052100c44910f003085c26a00e203003000316003c4441000d13401c0140381d490804001d410074283c440400503038030074000903585281c0b40131a160b1011006101080c0200746205a001010314020b058081d80d000320117100d0507240001c0345002800312440118240036071600000e50758551050007030042000784032171482d200c1c80480c0700340040e1001c008417180d90805d014000c2580c0d2085600d040000c0710440508014a000703800800c0c014007a000910301c284100364542e005050103040344846035910741d0f01d0b685402c020042e190b881c803e403102030660a49443d010240c0e44030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 658907949 1250 658906699 658906727
    0xf071103120a090509011a03180f1b030d0305061008040813031101080a11040e04050a06050f071701060c110a051504090e0309010915111605100207050312070f0c080102040303 77
    0x488100020a4844407c050300da108022060900d11540d090900d01d0404d0984521700d41c85006070503818403c0c0e42a02004144441c0503000ca480c1c801c1d030350100700c0482d10180c0c0d020742d12982d0001580c1169105010302c1b40c000b8041c640d0103140400e074075404001006a170344115054000c00c4200e10396507811160740d40d03104030403107024094030101211031a076911440c0215081c0030400300104081c01070030408001e480b40d10000400c5503090166941d645484c040300c2c0c8070009121060184e002100281d41e841c1240c5c115251030700d10740c940781d5603140c807030f03140300406900642c4078100019036a45800c0c1c01011203c48001265991b410b020b0008140c0300300b100f5074a00b680c82009862642e0740e006140740116540038110301042d48400d141128486030040503001103104001d80350300d541e240d40d00c0700d800b1581c04440c54481882016016038403a1514428190306401591820f05604000707001404158441d0f84c10211a80b110b40c0d03400006200c0341c2105249a501250600400d0381180901540754 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 658909199 1250 658907949 658907969
    0x140a0608101119051e25020d0201030c03021c0b040e0601051804050f1501090b09100303030e150a0912020609030304023a060b060f071103120a09050901 67
    0x40c542e4120403618810000c025500c4152648200c1c0c10910400a894020412403051210694050f050491030f801c80b00d0f102004007216080c10396806501c1552060041d806070506040c2c0580760010750040985902040505400700101d0007044403414088228003500300c030018a0640e81d600b40411160300b041018aa40d00c00341c014002a500d0a41003440158051030070100f9039100d00c0c1031414800780340707035002c01071203404030900075014075483c414103840107000204440449a0308100041e801600c042502400303084041c030219104e83c200d00d400509000031520607040b404098507240078101c0d403c8545aa0f100002000c1181c41c000c40c161441c03441c8001c001c1c82c14031019483c0c44c1d1002520003841503170000c1c0c84801010342104011140389880d044088200c13850b1050300307119003900310304072503040c038046c140d100c1e0381341c4402038070301d66402d4007042401c06a540c0d6a030f801d0102c2041d080c5902d0b215080c29a520b04400000038101d0803456a503035078602c0d04d0103090003103a503810b8000c110b1071 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 658910449 1250 658909199 658909211
    0xf0f0105071b0204110f040e0f0f070e04150f0902040f1a0307080402240a0f05030903040302040f0212010303090f0503031903090201090803030106031e05090c010c06140a060810 78
    0x7904110040030510f404441c0010200104c0424041520071031000841d1078101041c00100d240690384964442c00001c4800500c5603201c02141240400c02c480001c00300b41800700d501c146040c158001c101c00168844000c1561f81c548a01044000ca07561100c0090340e0002010b00c001484540040000c08440d0170000d02208500340d6240c2d40d001c01404030040001240014082d903031011a0100944081a510122090b102007071210130303440b450303020f00070652228a01240034800d000302d910403020300e03010b035051034216400c11010380519181076052503000d01a8411261044a40c0750003107110340c450802051420b080440300d0410b03035105030304c04d400070301c070fa690140c511f80036003580d0b603800d0300d000604011640b005803005076654100036142d2101100104140d034269229288102c103911480310800300007454081035031821100e810054100c009070344080d5000300207030f00025200300008950b01c4074640f00001e11781e13001c88290f101242c48003800c01803d0000c0c0085000c1500c0081700340b00e2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 658911699 1250 658910449 658910477
    0x9110a18180f03050a03090602030114010f09151b060f02130b13090b0301020c010e03090111060603300a05130909020a050907090506070605070f0203070308070516050f0f010507 78
    0x16020742c2014042c05400201d110b40d181c0311b5070103403a5540d4460001c40d102d5031203000200c000d21007440c1d42d90100d08516189040c2c80d000e0352082c42180d0400301d011985054030101290034175500d510003880321025003d0b210005945004003034200703400d004010f8980c200f41402400222040e4010700b81408108252101d11a4010403e010b40d403440c503021a001c2c030f511011a0081c840c0020a00d190f51900307511b000c00035000320007092659000d90318444012a007920300c0d5140e141c291260356240e801181801d000c080c45c4040384491408040c1c64400007421450268110342c0310304008400508006071103d4441c981d01340460280030824020811205658003040440c001c45c00f80521400c91030700000c0003107105140d40005040b020b80031030340b03070a5039150503400750000762042004544100b40c580100d48c40081542c1e0000e0b01a900c00340140c40f0f400f41540e40381d004045110080300c4a24a00c1d020640400855811558440003400300141c0882c0c02d600b120400740c643c804018042d514150 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 658912949 1250 658911699 658911713
    0xb122205102c1011070803390d0f06080a0302030309011b0c060b060910051e03070f050309070312020d030f0510060806030a0611040303020105060904080d09110a1818 73
    0x20000d03c00000000b01d80b100100c40d00c100f809030000c0180944030020030004031310386001107180c104c004580f103644085140c090030000e00710700510080010001b840310b40c0900f40940c11510196082007000202c05880c3c02c4814201040d0300c505601590000040c0441400c09101c0d00703840c190b00c1756211a6442091038010722102c0840e00141c00603448510000760755450b441101c0030300100828240b440d81d0100d4003e08107801091442d1000e180c048102c2b41301080703113400c8134071680d0300b5610034401c4035040324280c42076000a8050481c0307109056000c030000343c01120f2510356001c55002001c00c3d0266100040c01c0c0c4074180030444c0340c0e505207014007031010420b0b0040001d50f2003500341250181d441e0404246442414100941800d0a06591070042111000113100740d274001d40c009d02c0719680b5103051009022003039130000d000390010803210000804591002807905d00c1814950b07014002c0c040029040800354024165402501482d03206101e01c41c4038010113982d000401c04d50071340b810b0312009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 658914199 1250 658912949 658912963
    0x9180b090112172a01020c19171206120d080c07060e030301061e1d0907210c090602150f1308220b122205102c 49
    0x8150500201030190403c80d102c28000548a8540c030119200c41d4580031080d4840c1e00f21242544041002000e00700c01c2c1418021240741402042c02040e030301ca9076001c251000c49480d113041d50380c01044401c11092080040041103540000f44407040107080041c1000140d274803d03045080d25910070781c00c13031452a41151303c580c2c0c40501c0c13a024544845040c206003000d00208a658000c5000000020440700c0c0c1100d00070350480a039540b90612207001547c10380e030440a1300f0902600020325105025140303000501c15900c5410741c60440b0004a201341d2940300d640740c10302d10b0102c15407640700d04034125921403031603801803503588001c0881c100032900390844020003500195070f1125100000b031f50003d00040e03a10305c540e0300840031580da0341c0b0580613542c00c00036456005100203c2c401d00042d44060141a2560f00040200082d401d480304101140789201d1101345070f40d032101802201d00030a5090040d0004810440b10200344c00441e2894803600410701118050740031900010345541d00e2001410b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 658915449 1250 658914199 658914209
    0x307020d080c0d050c0c0f030f0712050d0f14090a031e030e0a03030f1d100515150310150203041e030609060f0c030b28030503070309180b0901 63
    0x50126849060b0300c442c55100300355035061607034202030504c80700d0780340d0a0007010721a185030b09452a540301c5000958880c89642c0d1144005542800711001181280311044008100c5040051800038041d043e42c040e5911a00c00f028420f688000c00d07841c030b049a0310b1550303105038180d025100d074a000d590090035185404480a00c140c074001130011080f80280c3c04000c108480004981050507140740c0280a4095010104080741c1442c202c0e1112900c28512018542d5030302001d000070360118030b20300008120003044210880300720340e50b5034600c0c1c0300c680000c840d9010440078282d40380b070b0240b04082e10703541c81e501c0b582424585d007141140680d8044181c50942d03a0240e1500b03540081c1c0b9003814240500c54001422061410a03c4020486103034025605c213004c8c0c40301448000b800c08025400c80fa0340004007500b00d503110150f4414030f02074074100c88a5101002540100701d031643c0702d40f841d640014004a000c228086818407050f8480c0008038401c500c030000a001c4070501c1400704281d201c040c861 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 658916699 1250 658915449 658915457
    0x71a0421050f01290a4106030f0406140703020403060e030906040b1c181a06011218050f030406090e0105061902010e0d0806100801080607050f0403240f020307020d 72
    0x180ca0043d9981951403004203082c0c801051242c64030b0035009981b120700802840c1816150080c00441703624011003407203048005145500f90b80e140d000511141c0e400510440d0000c0d581e51010510b11810001607000c1d508580d8010389035425841d04201b110000c0710851501e80c42400714080d290360329004c0b44c00395101118103945940e8031415111b00c0c05d11075503001d05003500701009040100000500860340d240507000b2514003881146000c0321040701a0b8501d0300142e1589010703002d1081941115440c1001015165403402c20780d02d80d2030600f01d100030391a60303a4000042c1001195031140c402c1001e03081d0400c52151070f514000004045110b103698451514046c08030102d040c0d4001c2d48040c00030b0340d004080d03c4240080300c10007081100100c0f4410320414403050700000c0148034090060596500c10010103480d01d0b0080c0a4805c0c1e00f21040000358543e04200100c00940c40002c02c03450150040c04003500721800d085080295110300600340e0805205104100e0000e40c000341d41040c0310210b0070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 658917949 1250 658916699 658916771
    0x3032406070c03031d040c2a0c0f06080105120a0609060209090a0504140c0303031515040e070801060c030509010c06060801150503010c050309071a0421050f01 70
    0x11030310500449401418031500e0074400024545c1022041210204041e400d482c0150f1403002c00048403e012940d00001d20110545580e4450102c1420060207a42181280070300c00f43d83c0c0c00f500c015540d00169500034140e4020054150404001c82c054071007220400681e04100e150107079100d49800014128a45601503030741030214075411a1085000074281d00b8a502d000545a400303840b0503241203a1f010101610800703050000705012031440340c001e0182d8a11740781d600054800380c644480c43c2e40c1c06001028824100c0442c880200300501c2c000494100303901d09002e0203018035070143c1c884818003002d038005100280c1e014084400c011001d080240e03c1c401142081d200602b400d800c240305540c80d21142c0008840302000364821100218005d1208000c031800c102d410740810340b50180e80703511680c41400f0100d144400011000340401e100c41c203260b55002c0040d00600d12031000540640d00c40400c0c000d0182c24029100440d010b00000d0100602a42c549081900d5030380c07005002ca0400d007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 658919199 1250 658917949 658918021
    0x30317091513081c02070b06030c0a0308070809041b0f0c15020d150b071506050a0b0a020313060c02090703061401210204080d090e0601090b180a060e010207080303 72
    0x12082c0d0740004c40034070a222001080d0050407000758420350040d10030780c9211000407907926000990400c0c0041c0501517800361461991402d003540c111032811601c240080c4200f44a03078071140714200800080404481401440d80f0024042d41ca0140c000360401c964151074002090380f104492200a403031940042c1e5a01d00207102074024118021000030740785811100140003600d0380081c00415003d001c00e0361401c99100040c1080300d40341c1c4103440d048607000e0800c000b050fa82c2400b500390080c450058915202c0c501e203608011a040c0d41041e00890208000da00030750070151400c9901c401c45007401c0010314105000d80307044008011300181080148441c0301c40a69003400c40d020305441c00002075440d203441701e400303940303030406401e2040c00100002e41c001800c003c02007000e4000c000603100e03400000d0038403181c24007a0f88000c2004660064418444403180c403400d806000501030361744c030503112140b104002820110700754814607096009205000d041a008414aa0f5032070740c02c1022041d0319014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 658920449 1250 658919199 658919213
    0xf1b0504210812040317011707171510030b04052d0c040c0c0b04080306092805041e0b060f0a08070b07030c0b010e01030302070e010b0706050c13030317091513 70
    0x4005160b100c014400300000301d030340c0c2c0094400808c07640032064400d20741d10340300918020b04031b146200040d40d0000c00d003070b00341c899405001500001040a042d000c0b949940700c0e0494042c05690031543c60703100500714600e4600844071001804200c0400120030001100c0c1203a0320fa48422515102c0e0756501c02c0001c4003805001454103c40d07104144422a250506050041d5002180e02e14050181760002070100203070260010300130007031004c0860b0102910180440208801042110000e8440000120b40181d44104a82c0540309103100c24031854a0014072001265803e410383c010906040c0500115001150711416940500d02907920344035036040c1110b115801100180c040d50f890000450001840e03850705040e81c0c025001c5410017940e4003000b0140c0d4009201d0501880001d0001000048883c4c0080760400f456503025410030040d2600030401850b070341e104a010890803a800344d0b03d030801d001c110350b0152403d030290030400074030360140c003954030014203a4903017000900700c1c07500b04812 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 658921699 1250 658920449 658920467
    0x305070209180f0a140a0f170904020f09040c030e1005090a0209041b0608010614031b030a06050f120304060f050d1b02100b01050d0f1b05042108120403 67
    0x482d02155405100a40141e80310300c3d440c80252090b20f4565401c1e0600705000980d20b620540c807444a100c03035441c9450b10a01c031018001c440640070002c10070030400317603114000340c07007011080c0449580c2c8450380c80c01c10044907201d802c40001e1504000b01d003180e165010804000a0b060102c001c186690786403100390130300e00c801000940c004142d90a100601035800c0f5a08044104100100105900c8400940e40d0600900ca0300e00010396050003194903112180141d600010311401001c00d1060784010400650001c80d006882e440d03035554108002d1405228881000c203042da6191030140e15a07041a80764410740c02480d0920001c6080e0400b2103105004882e07026610060401141a130800c080c003c00c4c500d2120b402c01441219684091144039103d00840440140c40b0149400000380000c4042c2104010821006a403a030950002007401e280c01c00000070345a48455880342070011400034010510503001070140b90a074041c0028414600b1540502011100010325030b036a407404a4880329 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 658922949 1250 658921699 658921741
    0x2c1909020706020301030c30020d02040501090e0118020906040203061306090902040f0212010311030102370c05060604051302060a0c020301061a1c02090603010605040509010e01030305070209 84
    0x1200090769028003901e81d024506a0b803080e00110040c683c1c4204012138858149099080190500421500d103031992500c0c0101900c007606005803035800c0d4002804a4200740d0085c901c0c180c40c1c169038400408288211545c484035451001030122480d004510443c030000e068a003d40c1d0300202280d100d584d09290001d601e140c5907028068543c4a1140401404e1000c00c201e00a90810702100c51110780c5000341e030900c1400c0083d00806a10f981c644141049a50174040d03010f550801c4144a0300900103000c85d8901c40e03c0b01c08050694112034045441e0030003008000070488603251840000b0000300d041034100c0c4080f5004103032a15098603a2903629a81c490080d40410000340c41000c40380c104801030310503402200200074855031a4841c0c204090f00c01c0e04211480c4c82081100700d15041214111b046580031301c40181004039220124105602c28ac21100119502040c100514500ba007891344c00350810001c041419491640d01500c01d01851000901ca529444000b8803241203038907803c11210 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 658924199 1250 658922949 658922951
    0x70e0f071b0303060905010e040b041716140d0f140903012d0516020703020411071e0605010f051f11030a0c170703020606120c0307030309062c1909 65
    0x40784616001d40149107a00c9101c0c1e40a08002c0009181e00543c80450700c2141c04c500c280540343c0d030b1682c071500b09450f280019100c50105201e000c150969000149450078807031050052a001640380c2c0a1030070b007151941c0d104016500003c219017a03445240c06071301c2a500d81200341c840500d000024098403110a404010840300f03402020002d8141c01072203141c0101360390420a0b40c4401c42420b0030304192031f40000251307012640030801814294401c080003c10704d4980c1c1d0030038250780da6441c1e100c2c2030340041c1840180e0400301c0009110552007414014414003095404081c5040042084116003420b03019084082d0415440b8481c0207072540070142154030243c9036103811201d0003038a00c444c40c420503a40100c200c000c485039000315108550080780c160b00141001e642e8a800c00083c00d1110403100c41c00e004018404189450820241014520a48400342502d041c0500141590a00840071486240d149440c1d9140301310f0600072007260205660105113445000c02072010296903a211031041 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 658925449 1250 658924199 658924247
    0x702040507080604051317070f1a061009081c030f0509011a031609180605090a060c03050f04060c05090604081c08010b0d0b0a050402121602070e0f07 66
    0x1e42e41c84100c0310b100d25011141000180c0795004040c0c0105030301640101000050070508018903814005003c0c035034400d000c9a0189c00c403690b683c54040b001810201d081802110512941d80350082d0030001070013040c540034040910381407003d40c2d00c0140c5c0041e4401100d406503540c025038171940115900401018041c052428000005c0703000b020b0b120f041d501c01403800c036074036522461701103a40e000700b02c5604490403c05080414000013804170244000380124a03000c4500090618007450303101e108404094004030045060000581e40c92038042010146401c0400000d40c5a0110698016800c82070025042e045004103445034400c074940345600c10000314000850000010b46980706c4400c4c149180340e03081c10b01d0360a82d8101303000c0c025140411002e0003440d000304102d5100c00c0503980010043d01d0b00903602c0c07001c10100d9122503000212652981c040040e510902c0081e00c4542c104c0e480106042c1e850032140d00441c4001801c44034082010034041000c00c1d104061a403a0991039040740071103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 658926699 1250 658925449 658925461
    0x4020d0602070506131502040e061002010914010b04060b07031704050c041119050c06012d0611062503050a09080f120603070302011202130317040305012405010c0807020405 76
    0x200918a0b00b04880e46c0d200800e048840d00b5a9000b5103040741c0341c810341c2c80c08036241c400130002070583c003e50901c00c66590f4112600451024019015881c03aa0f1000003a8000000140025154260003c0d120702c041040020b001a40c40440c08807001601c20344c08490384c985140942c104003640c1c40250740700f030914954105a1102c07000074503402030400f50540c000308d4016000d031014000c280381e0f0320540e00901c00420516045084420014600c0c0344043c05000340411030765816103060704a000044c0c4100c0c0f040100034410840141c1080400412803d8200004400c807040107150340d400d0105902c980200e071032920716800182c18281d02080c01b0342c498040085a1000d50042441c01040441e003001254080c01c0c042140c03400e80f0740603901e01c01c006030310345103000180d0701c507000200c3d101460720000408203100481101f038000c008400199140e1075820198251009503079490b1900e002424019410b80315905080100d900070300700405500c0d1142003100c1036005500000e03410504180030000303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 658927949 1250 658926699 658926721
    0x40605041707031112031908070e180703091103071d0a05090d0c140a060b030c061204020f2d041406030a080d020c1002030a1d0604020d0602070506 65
    0x42a00c070082035140d4038100811820b0b0740c50300c40344400380c210380c401420b90400e42081202103e00b2801682200d20f80041021b6001d000f80ca805c05076000a03000e001444000d903880103141007641000c403078450740c40d2400954504031050251078003090564805086d0b080107070705d0310b0b0540f41d1180201541c1c0d0f01030b91807a102d2146113011060b440114601c5000400b1480715115060040141800400b9110b491400c150b07090040300350203440c00544841e0202c4800f50030041c40c0600e40c403a0a000c240070751441c09041c5800324000c0901c4c81410280540150035000f880b00640c05601141c584115840c0d40303001c2582c2405260003a00f54201604060310812003c001d2055440001d13541002245404043e0090000c020341d00c590f0b0603003003d500940410210340241081c894051001403405403112080c07031500180384c404848081d000700030030100c01503d1141c5100c11412002c0480d040d699403103040e03120b42000f0300c02480396082c041348100744040c0ea81540d10803548081203415500380404620 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 658929199 1250 658927949 658927957
    0x32030a060524071101090824010807060e06090a1214060a0504080712090503070806040606080601031509030903020622051507110321040e070c0209040303020d060902040605 76
    0x2500803120320101d2000c040745403003030940b01d0030411440d9040800f150b840c03d0700c00110250003810444001c401240e9040f042c050940c024160f80010707000801105001140828140d00c1001c464201001c1086116004901810780001c12115a40d980208400240c00c02c8155084039260f038081c09804030820040c031610001c02a01002120716030f0380c03107c43c5401a0b40007145e00920010060111400103004440040354280c410305010030b2140d2100c5c080b0340381c41da540e404140e0700d45c0604148000c0c03010a1003050042d014001c0030340300380d60440d110440b00610b44c0106d400c009641c0c200e40c6007858814003100000c0d550040002e99200140e801061400d0500e00494100d00b8403890001501d2508400445444200049040c1031120640700c0d03240c52121541c640341c250240041405c1c0c00d030094400041c01203415581d59840d60304204030404103800c010110400c1c003281c008a03101503602c40c6000d80c5c1c05036061801513034a814224190010b06070356030240031071030300114000c560b442d0040d000e4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 658930449 1250 658929199 658929209
    0x609180507050904110409060906021602011d09010303140409020a0c02041b120b12060403080f070c03020709020d0b0a08100c050f03070516121d03010c32030a06 71
    0x46107100d8840041101880c01030780c1c014650301c0e901c0c56441a6090540013841d00c18010900000c00ca60705171911001e0740d0002e1801d84601d0b400c04a25001c568108070420f10400c5c0e485410101850500d02182008106000103018040304041e01c014440102049802420080c0419512a104504094601c4844c02d000700c1c411820010703070444803000300d0102d9145c0300c46591029180f07035404003408014a151075070b898104030001c0310039031b4442040150310b010320311a40d01c01d150741c9000f01044030f01203409007812040002c1110b100d8040b81d030014404065030140480160303a45880e09802000f000c000d044079030414154440055500b5000c10386804004050750184100b945081003201c15204e2801401032054060000c2600c2ca4425005003295081030102826600400c1c2c9a01c40c10a00e13011140001402c410340c0050880d003403860103546140700f0740080c44521480140a029924000c00b076074154800d49044004403104840c1c441400d18031040f030b1030703a40d080c95003d04000d08614011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 658931699 1250 658930449 658930453
    0x1b030d05070e090711071d04061404030512060a080f010f06140a0b1305130c0e1c0b0c041205010605040e121204020604030b0c07060e070f06080a06091805 68
    0x16052030068480b602000e500400c00200ca60f074208080d51414011620800c003481074100208000b0482204501030620100c10405940f4192500300141c40c03c0c801843c1030340c0158414040069040b070306540030303c0c44400740d925455640502103030346007400758450402031045801542c41444194006240c80c45261400d2007129144c8000281c0803404024554202081d100708000c80342c0381401030042c05600400b02d21a25580304009030f410320035803041c001131507a00c1e134018400a8010030007072401c1109450902800212046184101d05002405400b01000300700140d000310440003224050549080320700804009414814001c208500451f4001c1d450320100c2c19043c00002102a8030b0940300404904d0205580242d20114001602c00c90f000031041c840407001986841e1028481c008162065440d0540b506201c401d80b40c070100003100c40e4111000a1102e80c02141018040d681142050382c100c0c0c944c007141d6402006182e100c100c6042c035003c2c0c481c61001b2059140d64000e405841 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 658932949 1250 658931699 658931701
    0xe0d120908120f1008030d11093d0e0907111c090e0402060a1b02100c03030c090810021c0c020f0d111504030201090b2e03080306060f1b030d05 63
    0xc0c415024417402030101c280e1042c030812003d88a60b400c0f00329088443d084680c01c10140038042074138a20302c00d002e1014140c000031000613510b0740015035404030201d440c2c01300800302d44860161143d0398082c4264004d1903940e002038801400388801c0c40c22200700008460820344980c4501c44401d100250380c0001030f102c014002040400102854091500241403520305068030b00162420340c182c00329a46105043c841c018056034440c0000d000240e225203034080c4603074082c50010200c4a403070026605001e00c03800180248580001c0080000d54034020040e503c98a4103518950601e900c000e46c0e048500703045803c540301741d0100302702d48a041c810085403d5080c00100581ea840040b9442c2030300c6901408500098071510064641c001d402400001078400d150303181c040d030104048031001d1611004103050401420b8070019800c8080d68015200a1503003195103d4195100c00341c5014850304010501600d4103c51404403559042001c2044d2a41d02400215a480350061801007805500e000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 658934199 1250 658932949 658932961
    0x110d0809100503010506160203070b070501090c060206100e091609060611190303110c0d0906020c030102041a0708040f0e060907030606320406020f0705040e0d120908120f 75
    0x140d030f0694000501e024100769007d080742c008600f58640591b41403113914000140d42401c40700070012180074400106000c07000c1d003051405e200c0540c2c00a000c40d0b100108010003810a01d020301c00f80c5200c009040030075102e402070300741b030943d003800042d00c5c3e10389011002230702003000e5001d41c1c1201d40d142c4500c01700001c8880000d4640c00c60a1004010300e20f00040c800002e4429030103d6004034603c0407640c10501280c40306403910210648540126003056400c0c029150100510402c60340120000c0d8900b80c1085d44a01000d860b0304842c040111020907003908000003041501c000d810851030340e0907850382c0c510003030f4403d103802c1d900c85010341c00e550042404540702c2e014140a48055480325038503510040c1000d01603100882c1c8aa80c09203a448860740700082e141d00900043c1656801084c2e8001c02c1c20785182481c1044c0d1040d8810f07460b16403581009200440c4031640b19465003007801c070300c115140e80407000c1c00b00800c00410f0031000295500d4040303440c0200501502d00c0d40c1e0f040105075a80c4c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 658935449 1250 658934199 658934207
    0x92c07050f040b1902030f120730110306060a0e13020a0513090209060406390b100807050907051303150b150d0e07080706020a0b07020c010516110d080910 68
    0x140480d8240c7c2410010301503a07207010040250041903510300040401b0504002ea06048043c0300070b809840c0800d901e4a0903000c0e940a120310920003082008e10394140b28001500521030b9002110a011500d2003401c11681ca0034200040c0c01380d1100c5c19503462010400082c202d5104000c0c20048035003e14001c51488424804e50720030700c4024000c10b14040c10542c01f92803441400c20b080900c08911200d8806601c4030001c2d407a80c04110641a1080d802185403101c0c00020040000c80e00381c090300402c01c111503001414500f1500191440850b41d207a00c00100d0302ca124400c5d83d07a800c0c00c000ea400008005000d03e02e042c1070703200e1030010041c450303860007008550b0301c050207041000102480722140d50b4240d81d01c160341e094161000c481c00d55070b440d80c2540c1450010741c419809030f009288803000303000c4070101060340700c04140301400506842d40300103400e9019800c410b40c64081000042d10402041c40754a8002130401800c103000c844480c038106140d0780c010003003e806401181e1403080d2080c00303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 658936699 1250 658935449 658935457
    0x3210507030f110a0f061b0e030304090c050f07110f100f120608010f050601020d0c0c0b090109030501020c0d0e0a030201090302090a110a0f092c07050f040b190203 72
    0xc5035542e035203501c0c0109021501500d41c0b09601c05280141d4100030300098510120010480c4500b0011500f0610340c05000101d65003280300340c0500111405096455901208070340c2038550201000a41902d000c00032a5103010707486029805d820005003450602000c5010703095495401c41e0f8074544c0302440030901440780c6025a107800851520742c0c41004280c010403180c5101c3c400700000254455440b4101c42c20340d489404041045030b03507403080c044156414840c000050019050108102c6c0715595140b108030440e01c60b000a0b00030109012810340e101d10030132001141c0001c000d540725075518800ca500c0d200d00000710000300d00380c0d80c07410746281084010345044075016190a0410b500c2c0d90248644c1c00360041c450001703d940c40680b844021003000140549038401e950390500032074048409401c0c0200c5030000c00408070303e01e04600c4c4c1c1c0b0500e141034640803469584204290748480600741d0305070041c0c12035445c14040100703000c140c17280d15a0282082d6441c445200c464045101e50980c0c591103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 658937949 1250 658936699 658936703
    0x8070f120c03051206030c030115090c0305010312050717030708150a1802030901230708092a030a120e03151003022205010b0403110406080d0e03010b0a03210507 71
    0xf8144440c01c2102c0c1c04824003030740014060207461170703001100c00180c210764400d107190802081190080c04207004034862001c2843d018241000f5550541d11003034204100a4649410454006400410410500014408490b14403411910f0f400c2c500806000060100d400c94040c99141d9580582481c0c00345681c41107400c46541c1d042000300815800d40a0341c00107000b90219900e40190001840300840205c0d1050360090319013102d828459001441e54401600061301544117000c80300d010f200d1801c020a98407540c00a040320300c0c2c142c0002c40c1c00c0c0307048068081c00c6112002031480384181c11502d4007202d800210b066455160030f40c0c4070110498020f854010889010140c14401400e1100181902068603404c003028024400c0450342650400d803c42ca15078440450200f0400c001451071501c080c6084074207102090616042c0c0f99a4410b0482140070072400c00120000b98800b94042080300780d02030b00104800742c80e0309042e2000f65440c0e122040035a040d1002c038a00c64454016a0f41081e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 658939199 1250 658937949 658937957
    0x4061803051605030c0d201203062101090605011d0420032506030605121b040204120803100e0f0f040c0e0a0c080105010311030c1608070f120c03 64
    0x191688802003840140200103c030540700c10448403c8111040008840442c40ca0b9540c5450740c2104240c814106499140c07119154444411140c040030b00400f0b40307600c40e0059880548030803403a248110010742140710354800c5d51810505c101405015040303141a110f0041861803000c00c0710150420f031900c00c07500a44903160300181c1c4049440d0102003802e0040c3c000f41161011011281d0b142c00c0d1000c1d10504803c8010301d1942000f100b0b802d80240801030504030741d40300d08840380058050f1501c40055001c441144d00720000700e0203503165410707280603001041101140c01910301d82400c0f6030317000b503c1809820703120040000300c1c00101c0d00e10a04c00d41d4a10f00511054517044a03803000840054401c89800c0307600c030400318580700304c250b40070b100d8241c1080101d17000328a0314014211a5040e00114101814990196213002600044036004241c200000b0b540700500d511200f09100c80b41f8008000402c006250014040c0000c51381040e1402107460b40803181000d1419100c90340c080c4002000700d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 658940449 1250 658939199 658939207
    0x109080703020f041508010615050c031206121b0a090905070b1c110d060902030702031608070512040e0f0103020d0803040212060115080c090303070b0709030209010308030406180305 80
    0x60500100b0f120300c1e02000b070004680b407001401245066991504490701a81d51000100080300340e200350040842a0360902900e0f00c042d40e0003458aa2082049540c621800300c0e011030400e4864150201404481109807030581800301500c0c01520b01007039656114680d80c443c0401c0f5104640b08004003160720000270507041d032a040c440d1a5613004020113422125482d080004085101e00400300a851784081803030342c40c91740c0c2e05402e0865034950403101d0b081d841801005501a00042126040995405040742e41f8240b49090703c0d0314410801e00800f81e01032241c5500080b8510b0010b44251030b8503181140303466a540d0110741810074240b0010b5800750382480050b012850800c011500f15001828a400d01888540b0701c0785498170030303808412000d6500b143c401c001a844106241c1109030b0098091818002030000b0b80e4034016840d024001004060100f10142c0c01a84910000d41e8084d000d0050b643e5681040520f03900202d80540303140d41003000c0c4803d014950308500c1d10303d5504d03849060030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 658941699 1250 658940449 658940453
    0x70837031b080a08010e091506220c0306030c08010b0d030c021f02030a18030b07111009050a06050a020702150c01020c010207050105070e01020d02030304063908060109080703 77
    0x95003407100c10344000103901a00071000c5010b40c1e0082c00800340b161188250b6525019000071041001051107520381c1010a5804d0710390300d182d020070303000041111880c4030840c0500b81810226451131640c049a46840529001c6c160540c0040048034010800803000587d180c80f418260f8001d64000d56000e581180d0010020303006006000c2400e0003c0c003443c00c50400000c07009110340c000030740c0d600580d1000c103458000300e501c00c0021100b2070004c4110303c02649155078207424550042d0104041c05a800c0c02d01001e0351040207040040c09680c6002d11000100e41005034581d89000000c1e1041801e03d03000403070034001b070f008a445043d40940000b0510303048014600240c0c00c4980e40340d11a5400300140c1400750824006040710350f00980000409042100002e0054410300380100e0554124284200e01d0940100c1030700d03480703900000d01181441e03801540b003890f0001c04020740030642d00c00150200075138070284a602088031980701d41e0800d46650005540713a001e5442650701d254002441800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 658942949 1250 658941699 658941707
    0x11160c15090b0d0209030d080103170f0d0515090414070605180111030405130b09090604020114090a0f06030903090e090c0f03281203020304080301050409020d0507083703 75
    0x11540510302006007040b10540c00039041800e107c00900c0055154001401845011100e0308800c04074012003914211701c0b041000e02b02c1c01040807814070555a1000100d0a0341604504c003c80900100019110700e420b03d040c10035040400c41d20303081440f92180c003241035801041241e0882ea8034420b010a40c400403401141c0d884282d0300011001c0c0020b10002072591140342580c0e0780300c2007460300401c0490b925000d1201c0244000c20014841d0b20000501c00540d03040b485284012004194a80c0d80d1302040f40841c80380750003980518501c040070880007582961552042c0a040d1180d036464244650750710703503100005815205903216400c5080b9107440f6280004d08035020a40c06026100510311080300c80300d21801d0004000381a81800c43c201e4100102e80014400c00c420f103041c110300f035090540380c02d4594001401298003c079510841d6005640c1d40511036614035a00c00100c0b941c00f62545c20454403034411801e0b1541368840000e00002503c4507104640c85000d00d480305801101c01518200c0d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 658944199 1250 658942949 658942957
    0x2100f060f0b0c0723030111070209040f05070b0301030f050d020706140c0f10060509010e0106080a0207150507030204080c0f030a0303020307120207050c1e0307051311160c15090b 79
    0x289052207095800038242c040d10314110007603035000704034103e129105c0301414207603112420786000c216400c000840059940c02d00301508140c000d00e14800084062422074500758098002036008100800000b0800400e140000c00407486441a100d0700500b11f0001c0e03a44940c0c50240101182030000b44400d007840c148060302c45860070a0031120707106591401a03003412044c8a0b560221611403000b40414286203120900411466520040940c0b51480060a118000c0c11000469400082d0001441210440c0050b2180d90b0402000f480c10000e001030001d510500c642d00c1e0314002d0030388200892905483d024003804020740a0090f203185d59800710000c0d40010041360601030900080e024000e0b65202800350300344100024070300c40380d51400300b000c0000c4083d20000d043d45000c1c60b54010742c40c00310f2494200d60007654504030381c0e80303819150405018400b92440140314042482d80614000100170480540201ca903084082d48940380c1002401c001141040422020b510070488507407080002c3c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 658945449 1250 658944199 658944217
    0x304200d02150915090a0f150c11100306090501050103021206060706090f03032406021c051b01050a051302011d010203090607030302180604050a030204051506070302100f060f0b 78
    0x246140018075000200440e6400000d40300030500440ca8000750304144c2403c05c0075040d581f5030202400c0c603014110f9805500c0441040820498030814820083c40310502106d001c801001c0d51080007410500400501851185000e0107041c40000221035001e4401c450540841c20011405548ca55061149680c414003040321030554a201e100c0121f02e440c141010918442d4ad408644800d4000940b41030340e0140c01e103210001c0464004004481d0001241100441084419000d036404941c05035202d014071070010303c43c003281984444804906601645c41111044010461364030f900c4d000113042030108900a0100b403092110048a901c0001388a1401e0014030440381f9005070500410b8894002c0da904402180d00030403040404550740c5040c0100380e030140c8019040c42e14050000d41d01d00445c1c48040d01880c2c1d07400210380b00c1c41043c905515482800341c14240d0390146403038006e6135144c10002d2144424501009184141d61a0003451b08540786005100301050510043e505240d0003181c0c1c1c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 658946699 1250 658945449 658945489
    0x180702070b090a080111120a0c1209030e03120702031207110d05030c2a030a05060a0b040617030406080c0c100c121b0905030304031e03020f0a080304200d02 69
    0x1000031314950074003454507000242c60306140c40e1411010700210103076018000c0c4401c2424072003820040c581c4a8226900d2a5015602141180b8181400e6564131101444160540500b01120392801c1c2c804000b8020305100343c0884071030a94000c1841107d0140c2038004188160003071085622b86080400903641c03e02a005403441c21090409503440c000c03c1842e030b401287c0000c0074044d007020303064a952403042820340c09002c46060300c0d030350141c940b400203000140b2031b60340f5065001c05844560040014005d84500d43d990010040d40300e070795035041846001c000a00c0500014042c24808041d214160fa0460050075020b284c103041d200908211541d4904120070501402d0014a4a0058110038100075940440c4c5000c4840010a04200f03504014020b902c108030400000700b00c42401081c000d513040010401c182a450200d040851a400007281c0e881000504428407001c1802180502e01c6604e09015641e46514600210080000000d0b8481710103007259026081000602150300c520540c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 658947949 1250 658946699 658946719
    0x103030309030203161a0a0e0c0424090515010914011218060b090c07050601090510030c080304050108150d03120204050307030c0e070e150f0d02040b0306180702070b09 74
    0x80c89550203d039030a0181e0305146c45015000c000c0c0b0102220b0ba070000200f42c0180582c00c180f105072a0748442079401680151f56803c1605500008200c4900d10b0303410310302550813481d6403040c0d100302811007070700e001d01c502c000408000460346c012406a0f04560b00720100d50103160b03801d8015507955a00006840031141c0b24942c052155901062810b40706c0d00c0307040c001807100c4a00042c4541080000c00d02e441002c8104030a0700030640009403581100c05505001ca8640e80b0100c035440303c58119407000381201c041810109001c1c0012004e40181c94003a6240314241d510b08150114003441c011103560004403c006860200380300b0b121a110705026001301500d000c0c0e0324404285490b00720340c401c3d80d9803200f44030180088003005241c5500300c1001d203040c550604204001603c000685902541d0318a400202500207540718001e48040e0300d02000c046440d642d5030298008554001c940d0b40d445181c41c61a05c910503109001418020200396000300030b620300b00202081142e04c006041b503480750900e5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 658949199 1250 658947949 658947967
    0xa02150702012c072c0105011404030206030c0405090702031803070614030a09080409061404020304170a1407060615020d020d11030412050102090a0f060c0f0609021503012c0103030309030203 84
    0x101c903070540324403085c42030074060070342d03a1744000880c4180c10041c10440e90030011003580405005423015030382c0440d01240d50b43c80e00ca1010207244a1940600c0d040407012041141c2d043d0044050300c45581404e21050403251108101601c13000d06010f05804074403454040e211111a00c8040d607403166024600290a4241d40c0314249140c105902054500b9200c0806020035515407941c000454010b4600f5421410315956900c401c11642c2c0b20340c140700402142e2080414880d8061000e4502c0c0310441540d0b442d103070300f407650142c0701078059035902000c42d1035800103072031000446504803030241c0c1c00f400d0401c1d030b24101140c200b4000d90f402001c41c4414000416168408504159454401c0c0c1c00181d0b222a240140b060308c44030750380a106540c55a100400445400c800b00311101b43e40305e15401651501454600014181e6000107904041c0041521010001c007100840c1a03a1485008941c4080d80344484031703d51803081c1c1d40905800d600c000410000b40603400100400344240180d03401c100705c3c6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 658950449 1250 658949199 658949219
    0xb030a0e0a021206070906030204120308060307031e11030d120b460e061c050d0804060b030307050a080f1b0c10031103060d0c0504020a02150702012c07 67
    0x2c90011002500b01d81c040c04801d0786c0010100c40105040d0a00307600705842c0090080c0e01045c090b201505124083c8002007880c1d03070512022014580c006010440c5000021000d1075051500108555651480000502c14500065045003001c2c4c0b903511706d04000201801840a09000c0c000c85400080d408410681c0021026500f5030414601d460004a088118000c140c400703801e141e803121000240e1020b025024100044982c05034050310346841040c40c039007080ba1b4078482e043c8041e1050140000509402d0b0780408414003960007a0f40c02d0001507191800c041e12841211402046640700200c827600040c840d43c041d080b82d00114441d02d0410f8204030020510141450000c81560000011412140f815092203290351050340390030001e003071061250041610000c2d2403148030f40003100141d020000c1e000448009814094819034482c20340980107540d9540103807409171741d107941d5400201540c0c070500c2603050b0490741440120054100b03070300811000000c1c44100d04540140300c0049031034405 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 658951699 1250 658950449 658950469
    0xb03010e0c0411030f0403050a140a030b0f0a12030804020d0c0f0815071202070203011d010c031107030905090705041d011712030c090a0f09240b030a0e0a02 69
    0x1040041c0001c0c1209000308811a00c544041040c445424030502845c5c80c04080810791255050802641d510384001007036a240380200ca400d20500300000b600021240d141d0042d40d07002d00c0070b4800020380c014030020000440d156008030380d00407802010003004244030f4004a90010b0010309800100203254860f604005105e410044c60f00c0310424041007500340421130174284442d005a5401b01e42400d41000701401000440b842d04070f500411440b0135075402398080207140384140c4800c2e200d0203071205014040c1a1494000000c0b03840c2503111910841010f0441e001c1c0c0d94160382d403c01050400d4104807100e44007403d0715007045024000460300348143c3c504109113002907003a006440d03240060070740385124200300c3c064498200303101d1601c4042e04107055903080804050309540340c0340d0060110300300c2c64803540091807801400100240141c40c80e4071940b11055a40b040d0640c441030300084044030b11f071354410700268020800c0068110b4078170b40c8c08001050380c440e050780c801010540001e1002c0c08 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 658952949 1250 658951699 658951721
    0x2007080d050a0e15040818061b010501090b04150504202701050c070b09060f030a0e0f03030705031f090524040b0d060e010e03030408040f060503130210030b0301 71
    0x43c1c3c07114000d00b4084104920348084509044d00020380c0742c5a9621451381c054010a41031101503980814851307900e1006030344400300c044040f000c5282d44100d0980c083c1c642031240580040ca40006495241080c0c050310f0195051610032460080c80c003403d10005202000c0d8552615042e40354a204003420b120003010442010341c8904080040d004805900340c4c0580400e5040c00003c01048401c00c00103e02d00302150140d10004d0f0700d4108040c0421424854078000d420a01000420040780650030f61004983d80000012640000d84003004c8650304c0c80107554600c0801c006000150489401e1507400e22110700e40e08041d81c3c480d60715524082940c40a441c4000d050000003074451150800c507210b0703140103004480038480107100360302080c001c0008a5002c0d00380b6858807002c0c2d101500135000002c40f13000c01000c69a6a03c0c040c241921250054001c100102245600c0082c0061082c01a203004031130100b0413216070540c9034204281c40f8003000448050589a96048000d65402c0c46403d0b1100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 658954199 1250 658952949 658952951
    0x30c0705030a1119020f09090f0d02210c0318031005040303020a0e03010614060304080c0d18081605100c0203073f02010c03020106030c03060f0f2007080d050a 70
    0x1c00f101c1c2c10b079061000f00d0030180305181d8041c42050161b07407400d650401a041c15680c80f400c036201d080445d402c00749040e0041e2101d00c545440c48401d00c0d0300007414492120031800c4010600701203e20082c07a8451441103c0d040d80c4140300d904400140520850070f0b25400a04544824203042102403d4038800c4038181c0109501003851445170350400f404186480c0d04030020807549082c0a5500c02184030081e110740100c00200000e000c02c010041201c01c0441428100d030680105502d0040240304403e0006120500c2814002180030000645441010340344540c03540d41c078104814070013007107a85444c410802922840440260720140014806000d0150f644600702100903000b40c490036904c40403821441e2625150b0725020000304c9408007142e42481c1c0b440d07820109003001c0380541035540015002000e4144000200321142c0d02582c04069141c800340150118a0814000c456042050300194000b81e07000c03030031a44d0000020705817140709a18032400c142c0717020302039421202d084030694030311 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 658955449 1250 658954199 658954217
    0xb090d0210210b09070905010f0309020d02040203010902251101050d1d06100501050f16020a090507030209130e0d05210103051006050d3314060f190b030c0705030a 72
    0x5030620781d01309944200503051107a0042d10b0b100009284102050b401c03401c141d66000c440013150f41d45240d0401c0c080d001001036480e540c544407440b00a5200c0301c03071075071307000c02a40800010035001a8281161038108849001c080d81e068010744403984100b0743c015416a41e206003904400b02890700d02000342c0100c0041020f46800b1b44200d603807200f69003150341808800d0090441c1c4003c080119032407540140049900701c092440890b0704e410b52900120380840c28030081101d00d940c1a4058144503804450381010350040400000841780c05071040c604030380100701c5982e02940114020b286002c5246400d544500b19402e520821070000c3e041140e40b5000190b00c01ca8800780790103100041c11045814082040f885d40d200706a80344404ca0800317260840300004117007500d0307240f00702c2c126940465050090308221110410103810450b041ca1140300441c49241d0141400500c50071045080c91144903070034200081e402c06a00014090712107c441000754800090092000d000c8401c0d00b6211401c40c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 658956699 1250 658955449 658955471
    0x150d0905060414030f03010b0d0212012c0402130b010207090c0507060e070b07031805100e040c091508040c080706080406060e0c0f0304020a03170a090b090d021021 72
    0x140071042695043c2540240410004950802c0450341102d555840d5580c0d10103030030708600080d010399101341c10b9269540000250303164403080703001386160341460000c0c00403a03200c00c00443d4503002c0ea40650407019400184000480076444046902c80500480351401e640344034001c1983d4540014100048001c01c0b400d0800015000340d1011030a22009018424105010703031100f400b40030806010030400300e90b4000b0011802040002916000d014002e40c0b08034040060100480c05180034001c5103040c09020142e4414100700094500031140e82c1d240144052044411100150060b03502d100c445c0c00005484804210040007020030b600d500f403c619141c00e20108540c441c0d4004190102040e0402040c03801348000c071401500030700d00241c4c8a44450020651a02c15600000c100702c80c2c1c880c08401e60b50a9002504000403c0ea41e0040c1717060312807540a5950090b428160340080074500e040e001881e14001d04d00e08034666142c0407403410352141401c2a601410300301098016139031055445c07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 658957949 1250 658956699 658956713
    0x60603090308060d0f17070c231203270901030303050723070807050f060901020c0d021212071b0602030103060b011716050c010608060105240702150d09050604 70
    0x1c0c0c0030308211250b02a58956850305c6030001c952020091002012030302c0c68040007032800035a0b45a607086080e0001a80e15400f20051070120501e400766080c00352807481400d0b29021051086410341b00000d182001c1c503040d00310080041d0f4054611481d480240304040989a5110050080d40655004a190304100301d0181c182401c0e20b011a250320780a52010003c031500000f201c0c5484e0b0711544c4269600114144a400c10140185803c694000d00f014001036120540103420007014000c140e840c1d4200130501642d9452051300c080248000c103003d00c1c00303003a46841140c3d038856442d051003201d00c01003205281c949425183c1c21100150b0202c0181309000e618030980100c203c1c01e090207081103140c1c41019490100040c54018003a0b074018880b0580780c4a00181d6141000050080c44075980359030f9010b49800c000d008a90080c0141d0030740105c05a20729440c5103406501c010100c3c500103054007070020010820440d000031100c10040d10000b001c1c1485199005400b1310080d15050a0600c0c02e00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 658959199 1250 658957949 658957951
    0x307060c11030307020c0d020609030f0601050a080d0228080d02030103060f0209010e04050a1104091d1c0809070e0a05090f060c0909061305011e060201020a050403081c060603090308 80
    0x74400d640140b00300010036030000303450f0a90100480743d4841d640c0f420710001d80c10b0710440f0800c5415014410007100190000500d040c10390740d080307481c180401d4580208540e1004010002c100583c051401c5068146014000300402c1c09a040004000300c403540320b51603143d000d181c00000d215400030042091001700c0c4076008070302c01422030035803030310081000090484070302c1d101645c0300f81e6454011402401059100c001c012a07110b00c00c03500c4d19551203d03134004100f5507486030004454040018040303035003ca602465800f0007000c440c225424024225155140205010403034416080c0202d100300c004151944a40166840881c03d4685511407030700301101c00c41a54159405141402284444c0005581c03020006660010090392800000341035252480c41c800055864000007290b241000702c441c01405062000340141140d851340201d00300d204100c100d0002410078001800051080801400756a1440303a0b08041e1600b10a1003074203e855030383c44107003c05d985941c071008040d0003074611 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 658960449 1250 658959199 658959227
    0x90203091e03090f040203090705040e0d031407050403080c010b060316030f06140f031c09050102060f0103020904081621170f012903011e08012013080307060c 70
    0x10b181069800c001081c000c80081500a2207650044001500f544007001044010300e0020020b00c0700c0c0d00b21449680d1214160800d4900085c2044410342002d21031075241070084d5041e9032078500d8203103141c4608000307401c40449880c0c1ca54948000480503039800c0040d6004034081c0345201031691034a0030250403a1203c0242c405103500b048000c102440c8904a140000c803402c4e1500d5a0103800800000e0070a0303620010289120441d8202a00440c1d0140c0c881040d01d130280c085400f140c0326078565268000013440020743c0900710780c0006000a510002034030203c0c41018040c40072a40b0795644034502240c1e608d000000d040c40090908445a2051004054080101418401741810348032803d011105000710b103040c2d00c0b100000c03508c980e90049500100b05007540407503105c0d61103001ca820104c05860061f0300403c4415804600d5450600c140e0050a20710104c0300c403880c03a0a504280160028003560082015051000401400c10f00080146034411000010040e0701060702070081c503013103280 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 658961699 1250 658960449 658960453
    0x6182304030504092703110f03030c030402310906091a1501090614030403270f240c17040803030603070807180f021b0a05010f200c0106090203091e 65
    0xd0b5036500c0d8031540c0b17504411609858484c062100883e01d8519050300c0004282891000104002c8408118405180120704c2120241d803000c00900780545021801051101d0301c440c44072603403000102591240340310b14032846000c07a007401c480d210721003014591000504202c0500c1c0c1002a04040080145a44407017400c107640540d0500358001e109182000c130031940380d00e0000105013454081e000080b0040482202c2000c0300003c68041070003041c8030310521304202e1601c00c02240c40c1139080d41c010600610000c202050400c0c51008503008030311880141c0d00081080129898041030000800203030091300000c541d00c3c1092028189030007250740c098400f90300110001e104203840c16104c107003d840c0238007020a12100788002e54009120311401c88070080303800c0503101c0c0740340800f0520350340c85801072008208401961464405654400191003400200d1100e401c0304032400c0d83c00341c10100111000010000e40741e000b45000c90f4030036078001030550300c81550a05030b031200d80035402e43c1803c1240 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 658962949 1250 658961699 658961741
    0x20c09070305100b031902030106110d0201181203140a090c080d020601261507030513120507050f01140609161704110406030305040512010618230403050409 69
    0x44043c00005400396034440c1c0000404035000c9442140001c0d1034243c01c04d021562940e485030050540074000c102c400707690042201d0300340018018400c5801629040d030700c00c4080c40e4241d490400e12544404080107147d51180190000150010f48503c074005040000440504504001010013030300c0e4420601c59009010700703030301c00c1d90224649046a907044218141103a48150180b00d00384000c1e81501c0d03911035100541624000c0001d042c2c054810381d102000107480388030f4a00104648401c010348221003900585241394450f0005024850042e015220711032807001c2da071403d480c48160801c00744a100410b0002c68607048910315003140d4003694824884413801405810084400745103000b94240000040501c900c56003000c1b5881c0d4002c00401485407a032801030155006802194091207c3c1000724440c100148604000d42e41c0902c170300301007150414040d0707020703112681141500200810502d000354031004040c500403032080d1115902c131410486c0031001c840f5620004142d040d0152 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 658964199 1250 658962949 658962961
    0x504061a0f0304050a12050d05012c0601050d09050304060e0d0b041e02060d0c02010b06040501020a0b070e0907050306030c0a050d111210020904110f041404140106020c09070305 78
    0x12040310349646540c0000790322540c032400c1090034074196036005000342e403016030340c0102c05911000824a120f81da80041203240d0f25070080c05408140072219407645ca0010808100500c4003002d115801001490900d00e8401c2d20881ca10559030180700c102c450382d0011500344038079900002d00b42140c80c0c040c0c0e00f950381d080185e00c4041d0b45070009440903103d8285160b07442120040501e81c00c08013a000351005c1d503901c8a210f0300c24010004015000015480e0055a0b5100c0c5041007c41d8101c0b00142e00038150135400c0e49900302c2c4910040c061009120311100d203074009444d0f240c0c1440c1301c0e0b81c460301c9141c2c903460039034245401d00c80103134007170341c4268039410051050760754a8110b00790713298205064400c1c1c1d0b0408004240348104400b003405842c46010785c103044440a540003440c0440050342c06114245400b0b28029542c0502c0420009a08040c8800d1181c00d038080070303111450400504c041120000f403e2030042c6100b00307800540c016000303420241846d0400c03403030854015105180801c0149400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 658965449 1250 658964199 658964249
    0x103033f0915111b0a0803090f1b03150924010305190b040308091f06240f050d09020a091d0606010516050a02030105070c0b0f0c300709050406 63
    0x9080c0134030010080b16400703400210100b080305030407940182d00d0b07652410681002d50b60f5556500700305403544150344032600312542414a084040c40b001c0c00030421040d0400d810702120000400d280030b49e08c50406d8440030400201c60700322024003180f04518065045080990405618000c41c202c580b180900c20000542c01c1480b86134010303014580010140c95041c101414008005190711034002080480d65074075585500c45c80c1101c070f0555010f04410000804034a85600c22100c8a0100340400094201540900010600c1d248040c00024032100280d000034085e0b0495001403105c42d1baa42c460821000c66a40700c521151080e1004100030b00e0710000080a0744034034844d4030100c00c5c1500c01303441000002c000a10603154010028040e503d40640014804000240c068601110200201d000c0254a03410705000d0004000614a003030364054500800c0c0c01403c9000c03070810502c211080b511480c690700e03d8003401e82a62a1a8024a01403c200030b6640c5908200c85080c2d0510303800c802e01d000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 658966699 1250 658965449 658965457
    0x504030311012a021e060a0504020d050a0305030a11070c0302011d0301020c03120601080f0103032001020c070302010207051c060902040b0303070f020a0e0103033f091511 75
    0x106242580e580596800315a014000324009071a08820f80030720603041a2103030000e07001d1030541d039085500209130078807140d207000042d074040040c54001d0008501c1c404000c2d041540d10030300140000040748034541d6840d181800100099000a2010085c4a0030260301d0056030101440b400c905410a2456195620011140d20000741404844c400c140610410480c0140710364a0040085440703180300d40139140c0362781c0846a59651040d100002440f251700421100d0300840c10603606000d40c1c4c0c2185d8040c2c90481c0b208000395101c00480f5140c0007030407001d0009108881011000e452210304d188006031801c0b0003a00031074840c1c2e003c40300c030703034050a03022240700c0100303410410105d00e4113032a00108004000054500e50980070010b4240140442c50a61500a84c4296100816503070780307116001600c002808003e0004500607803804003c06205070351100720900f000310039100035104040749a5420386000305d902190304c0786061400c0c0304607080141c003003c50022062005408030100701125101d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 658967949 1250 658966699 658966703
    0x15100801051e0a0b041202040f0203100e27150603030324040603020a0b03010f080604080706021b071e0807062007080a14010f090203030d020d0e06040c0e090607050403 74
    0xc04080c0840a80d0349843d0b24074000c00044815a5803181c440100d41000c0035000d00503802982031040308903d090480c42201c1c401e00661080b4a4182e0414138540200340700540740118410303c0e0541d20003003441d60030780b001301c0f02c413144020502540c07440d021200c22074000303248520940050041052800442200e40c08030248001441054500700c400100107050540019400450103040070485000c000001e40c140d0b80700c3e1120003065541d510003240e9030700085500800d1400244605c00001e04203030041c00c0d030b03004224100300e1b00c05505103285107461040d500030798074501114080310001144080c1a001741106001420712203040850140c0460700b440c6c0c0c2e141426407201c40621041d02e050280601811201042e50000380844c02e05501030b4140c40200041d075440e02d01c013030444000e14455030352440d034054060350400c1011041080203401400d00b1078001603e41101154024060008174800c5100d0315124014a042c070700868503819009041c117509600200038000c401d9003100981e012a5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 658969199 1250 658967949 658967989
    0xb030f06071b0f0506250e090c090d050106050f060c0a0b09030c0f07180b0108062206090203100f0b030f07050c010207150e0102120402061e031510080105 68
    0x2c1440d04440641c2000c042c0c06868480486044020008040340715401805d80030034040d106410740340a9001c50105c43d60f0600810000c4603c0031843c1001d07147c256100c85050007007403d12003604040345231000d103950200e03803d940d20390b4140000c1c074000c1041c4601c04010340302d55080241a07000d5039545c248202c4090b04c2200c01400148188c1d1040044420781c1c0462400c0d03d0f40410010329003a40c5000b18040d800ca1900d08c80c9100d204408030340714101c10f9040c141e4441e20161140c20921004020104e082c0c0c28425041c0350114040400d8011b280040048100040e940e2400411030700103101c964000d20340000d0f4842d0100070200038881070700d40100b240846c0b40d9007030f180c15005440c6885a02c020120315400815194148103111414010b203070704410060100ca4103c04441b4200d00c20f12031850a00401c80c4049009070400002410170411040780b03500001d04c072402581059002114030302145080074610300d520703041400000094068a00b00502694100700020310a401d038040c06d00400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 658970449 1250 658969199 658969217
    0x5060907091a0711102d051602190305071410080711031312030818030d090602090405010b0d060e0f0a0c0c0b010f06020c24031003170a02010b030f0607 67
    0x80002082d002c0c07000b6000401c40803028500013809446588a82030a411b140401041d00101e611070796040a9030840554601d481c200c01e0751051203000704000c1003641c20401464040001084450002c8091030040f0024442117150500d01c40505801c40407032030040054903460b41c8280d820048441c0c00020f9801d00f10b2860072103503003e5255010304490086271208000000501101c400c0351410502e00a136184801c99890220150194002c0d80505203250b108000750223004100381e0008140314801c103400361030b2650f050002000da500c20b810150b03100f07200040e207030384a00c1c00e071043e1001841108411480780c0340101091741c0c00e030002400218003948800d00f041c1e000d88158400e0107003d510250746d10303441d6140c500d414003c0c0c030075000d000050b10a440400307005281440315401041300d808504009803070700e800c50404c04d4101920355075026000c40e0b008400100e03084803d42800d440014085d856504141c0d00900750740345940b0180c001c0d00440000034440c00d010034080d40c401d01c1402d019080c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 658971699 1250 658970449 658970453
    0x301060801020f03130f0c0314100603021c0303020c070b0c0708161205030c1203060307120b1611070b070201091d0105041a1201020c070e280207050109050105060907091a07 76
    0x18004a14500a2841f11281008001c001c0c240c4a80e071a1040b03131000b141c000c40003021080003201c0b00c40c0400703540400d130784404a0314402d418550101c114070901c0e0140c01d100d03401844030300c1e20400c0e4224540650012a44400c8a00100074180007010900014010203800505400074462180107200703240c9104241d001c244030307040048507a0840c240382107a07011641d9040c110403a420540b00b5900c80d0140000005072440003072044160150072015100403611042c11071001c140080f0703481018400d0400850b2022a000d0003103800600301c000310b4035607801c45417000401c02c0c1902d410015000071a02203c83d6969542c60103107040d00c4040d00e0000d28400c481802260100341c03020500d40c0008006200008210103402800d5091080c8040300d007600c1d00d4058698034038000326244210014403061000711510903c4640e8401461064010320341116911860300390303400c401c0c003500d050703444409203c3c0c5401c040c045568046820718050f00c41504140418622442c61074205601d80d201140e5002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 658972949 1250 658971699 658971713
    0x50f0d05160201050c1902040e0d0e04020c1e0c0102160e0448141e1c03020105070e01090501092304091505220609030c05030a09050301060801020f0313 67
    0x802609241c00c07900b1400020308030381e0012200c020108e004600b00402d010701400e000608103402c154540713890700a4000d40050000079003004447c0071603031042d2411080740000d4009900e03200000000038210140c1494000791a0041c803c5d400340e92010311281c2004500794035110b10b900300380d2002e0b8503901c604211100d0010b034400c40381d03a102d070050940040d4482000e40e481c007118243c02940b1080d0003d5440d4200a131201108140b1274102c95000c0d124042c5000d007407070441184000801e8544500c82d2001d1041c181601c001c000c5000d42e56a20030301140d00e0700600c17501d41040c402d10340030701e45038107100c0020328644407031003890110048000b0611051003c1c0e4100d00e50204003510800c41c1c1c0b0100e041103030500b005290780c242c11500d0040400d0803118040c9201d0038503480344180400034070f0141d568000800c0c1c026410b60070400d100c01210001001400204a00b6185545078120103040c40704150071940c007503122040c244c0c410410804000712400c25254440c114910705c620340180d90a02c1c003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 658974199 1250 658972949 658972957
    0x80f0f040311030f04170604021c05070803040b0a0314010503070611030f0a0306060f020c01050f0c0309130609060f03021809070807090203160e0f1315080a050f0d0516020105 77
    0x3220038000810041c20303070342c2d861016200702c1e07000c0080c0d0100c42c1ba46c0d00794079480b050151401ba4101e100b1161075103400205404150840f84034034111050543d440000c5030461b001904400448080004d1030718090390301d40185092540c1c01e83c59330009500d4440000e035181100c1c03151000344984180e501400b40420b0040d41d189041c0282c0d103a80d00e03202071600600500c0c15000d1480800c00c44124580300c00c2c03001030b21941301d50040e1120b83c5401400081d0011071f41005013550803e200401c000c1c0301035142d100e81c0c500c001810240c04902c8a0821903c02e090b2036060308580c81600340c0075010030245e07840019038021580c90b90001d90720b44c0ca88030780c00d9041154035040b0000501c2182d00010307002c40d40380e00651080242004e4800030344038100e0308984055280d00010341c00428203042100c0f030720384030081c18140c1080000004103112091511000f202c1c0560145070303941c1161407520184401440b01600720385030107014194100d000000503049000d007c002010f406d013030303031000021640628126 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 658975449 1250 658974199 658974227
    0xa0807080c0d1b0906090e01141302120906131e0c05100908070b0f09130f060816150203030403081302130510080c0105090d02240706050601080f0f0403 67
    0x140100c1e04124140c1e803192005051100024a421400040e0103110380b580d0016200070881f00d034403e92812a141b010300c04901d40841e840303c80050034010703024003480142078850b940400c508091402a00306401c0a40040450740d0066003841a180050040540c0001109440700c110001c1070050900d8036141c0d0058100d02d40040a440040c41c1145c0c03c10116812110408125520580c41c0d1000614500a616024603884400d20600b1900c0c58003181c00c205920301030600041180e801c0d204281510f03880e03800501150480c0005003000c10320350000314041c5c81040501ca00c200002c040080d541e02c0002c201404000c50340000c210120030140c01c02ca44607400030035180c10154075062200080c801540ca00d411003c24240000d00c03094041109410b09505868447c10800418140900018404d00490b031042c00b0546103405640e03034020240691600d018482d0b214592031912504548000d40304c5410300410804110032080d0040d41aa031050b048115048240c90303502d401d032500700e048800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 658976699 1250 658975449 658975451
    0xc010c0b0915040b09011b0c0201030504060b060f040305060108030f071e152c07090b0f10020304050108011d06130e070305061005041e0c09080a050c090c0a0807080c0d 74
    0x41c40144500c13034021030f001d28901d10080080b071501503601044095101c60800108a80405880c090340c003960007940d105006140c00324101c0d081000040e01035110b0035101c1800350f000315003481071040401c096030140010780015440c1260310310b0b4080d10b502901c44018003000341704c40003541e950810030789012400e511040a81d0610550103404000c1c1103c2201c4048202c101c1000300305040142c1c5402a100724102e0240001d00d051100c060054064803140b48e400c10010081d100c11620f41074940c4030540030960195450300d0511000400104069001c3c01c100000381d85100041586405000e03007111080710b005001004151005c40608860484e48165000314000003003404004030b070f200e1044a5425440303440f03a4603002004110b40c00090001c15110020880110019050703015003450030143c144078800c59a201d812900e00312000d401201e4582111a80907054240105c0080c3c000fa07001e50450b0402c500080300078403503400103100300c0403c40c1e003501003503041081c01c040b20400c21314410 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 658977949 1250 658976699 658976701
    0x220812090604092c0c0112050603010b09040b040b060d1101030510030206160c0b13030605070212030106090807050f100305041707140607020a1e0c090e0616020c010c0b0915 76
    0x30506000049401c040b00e100303051200135284540040361040c403080058440014502d8081700b040d0080800410786500b5641c1c81c110000717540d8410820713a204bd4400c00446c0f005140c9468102e40b081e40244c000d90086903003000c0c0705c2c00540c5451480710800d50030720b80002c081e5141c0301d0020707108180b64006504103800046032a100c083d07038003906102070b00072942000415070362030000b0310b00c1c4191081c01e0310b00302d1000814400140da41d080035400c004184100c2e0f1040c0f00712004a03001c0d5101783e00c80c1c00420010303001045030034028480400180030885242990325582e00208032402c11041c944000c043d030310f50028080152035a00342c80c010754860050341d00d62040317103400c110b0b408202c41304e0b04051007464002130301c3e03510005001250540c4060b115400d81038610100448104401c4120380c8441420070201c1e12440300c1c8102c0071107841c11001011a402c203064021203401c2c0c4004404219000180d0812440c1d030010407030010031754000b0380900e0a0740c41c0141c9a0409000b11000c000c1005208 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 658979199 1250 658977949 658977971
    0xe15060a110c0603010b0f1c020c071703030705040323030a0201020703120504020d0807030c1a01180c0818070305071e1d1501170103050322081209060409 68
    0x126282401000108960a4211220400100d4007003403058503c55801000388103401f0211101906003001c2c18082c48400c0c10b41e11000c003003a80c000c514120b090394030002c42080f00e000d031030441d0607015200c20081c61441c100404001c100344294040904994150284004610301a050f403d8214101005813070b2a5000e450009010b0f40c820602500050442400101c00b105584902402994004c00c604806001580c409900707401201080d000c1c841000c486101003007501005a00140d10419461090360501c0340010150120149000c0540d240100d1610081d4001100c04c2e0441a04580c240510030300200c290f2500786207420080140c062101d00054410b84400308940d8060b08106500390561078586130040b1082c800c200c03606103240540422500180400d5812820344185400c03442001e80301d4081c0d466000a0f031003146d403680002848117901d66035040c0480b110100d04032480c1450b02d0f141c81c00381d640d00c90410101464400180d101c095039103640440300201901901400820090 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 658980449 1250 658979199 658979207
    0x31b050303071107050a0302011103130f03020a0918021c0f050c012c220507080103060f09031d041b0207050f0a03050a03200a20040903090e15060a 65
    0x2c0d9014000b0681941c5104207200021810720b00b0f4803c05882c4103403a0349580c0045400c4540103c0898440c04108242001c24070040034040140c209085002c07c1e030ba2540c4144050380c01d20742e0180400501d03081c01180c8031089004511842d035012906003c0180a807143c541544040c9000108058019101c03030040000c0807510b268031040c02d880c1c00c1802e00b88046400d0311040d100c11400c44248040d102c00116140508050b030210005070100f1030401c414440101c220b03202680c54a011610481c01001044668000d010201c45900c0d41030160459503600600030b0046000070742c60b0890a6118036171301d0b407180e0f8400c0f01c03007039090410f080303217020000c0c40691500340d6401040d00403042081c0c070340c1d001c0c01c000e0282821280c1c40401404064200d840460704800c0721b40807808107005400c06481a440100710b10507019014424101d00120011042101003043c03550711ba025909003a880c902090300302c843c007421101940d01d10555a81c0303c1101c070203201d00c00040142c0c00784020885024040e80 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 658981699 1250 658980449 658980451
    0x5281d0418110f09070c14070312030f0c0e0d1403070821010801090b060f010e04050c040608010f081e0106030b0f010914060609150c070611100902031504031b050303 73
    0x1007520005210101001400340383c1c203003103640901042076000b40c90000344a07c10006c85480c8884113480c0f000342c0303e586640c00d81201402420000b911071010099509030f6110792402d05015090994102c01d025011406c07011950f4000780903016041008000c2403000d004175549540d104055a9880401079001c020107808011281400c4003104004501e548051040045468001c81c00080030b075102c0c420844200180c80b0800c0c10061803007001c080c59155030003070714090319801c00003a480d1401c02030300510741c002c140d103ea46500035440080010007400305200c0c0d2000060f80e00301140b4030400345411b004d031480e58002410540a03000704588000b8400045060784c040d00c01c1441002500c0140030800e04d000c3d9603c5611200c201300c2c298040c641b94900b240404a03041c01030b420803007a82c4a6a0034810681c3c41480420400c1a80d000710940a010901807448805c0041255401036000b00303a55a203c80b0381c0d0078405071100c0114040c103000d442d991903045844004080c4503915072901d15101d0300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 658982949 1250 658981699 658981733
    0xe041e0b010909140f09150a1d1006050310090b040204051e091c020d021b0102010e10090302070b0f030103020f040b12010c0e010e0105030604051b0a05281d0418 71
    0x82804049040340b0804505512549140b07c240d807410784925800d080205003d84c5024050010708000d07402c0d152091050700380d4150240c500003030107407400c0145070500344d00e000d0881090340340074003100005850450712604075406840c0000c080c0c2e41c2c0c21201d060b400000c188210107800c40b4017000000c410008031051104008112043da60310482ca040e40c0c0c1d20301103030501c00940c006400356614011040f2010b0047d20381440081141142d24a190f414070b412943d41507191616112040140751b0100504c500406010740c1491501c690710740321540d1400180002031081c59642c0000c040e5640e070340c109000513100140602c10a0340f012020700c2c0240704c0c907090600401c60440c0c1110703243d0300502c1c04290018041e15258a159aaa010400107101c020b2100b0059804c0001030b40c02c110a00c009011025080d4a60940d980f000d60701142d0480b511406040b601c46023540c580e28815032002101f030034580407021550004d204000000d01030100180c0d04e080781e4410101503014440081c8402000300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 658984199 1250 658982949 658982971
    0x70810050115210e1f090b0105181605070c140a090b0a03082a0706030e0303070e0409140d0905211504210f0e041e0b01090914 56
    0x404001c1056400d102a49003000b101c034100342101100c20740f81d82254003100c102100381c91140b40d014044604034403c0b0203054000c030340d903204020208070041c058940034000c1168100980409407000e0070050000031301021006516900903c00a4005d200313031200e0b250f0103070907102542c1c2c682c9114880d05080e009514416400074030001102a610b204440c52090060007400c0340c142140c40b0340700d55600032654510000c0803d424491681006207030081d0302100200070305400c5240560003020380e40c1140f139041d01f940082040c00041d0f6000350400321500810788001c20000b144d81009445c010b0040d8104c146801805050700311661f0194000b02524400c5078054041000b40d503481e0903d100c1e08050310340039400b20400741031949050f0340d25507129118001800040d01039884800104104008483c04500c19280540c0843e400008034100101c041d00c0401c805c4c2c034154280d940061200d44004040c540c1c0c1c000d400c00300c1e441914071401070712042c5018040d04007280308003c40c5010884003201e400f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 658985449 1250 658984199 658984229
    0x40b07030c0c120e0f0a144f0e0304180e0a02011b0f05010b090708042102010e0109050714090c030f0622090c050d170c0708100501 58
    0x580c0038003045003406030040519800f0f081400b00503a0314902c1d840105501110f880e803000c60a0380e8004030070010b000c841c0c01d4500c244044c081801016564801c80d03e401303850b900319044800c42c1c20903101210005000000d1064407504034603184400b003a4000e00e8065081c090f15811083c0008000c108440c45030015264214400201c201200e4540780300d080c550700942000b501562041e0541205c01e01581c94142038194180d4900003032060b003c20072141e83c2d448190403980e03440d0101c048bd82c05060703070504100915180d5604019030204200719051103502407010181032f0b1003584442c0701c10204030000c101204d05802e240e40c0d40e0340c01e80320302403442c0b00782c04070020701d810108000f42c0104c01711000a402e603282d035000742d0114000100400d0300581e8120035640000000d480791081300083d082e00044c1c5c00c0441c180a900182c150300300138021010490583c002402c0341003c0a55551402002c1d600c80d070503000090304000081d8050021480750380c2c1814278842180e44218102c907032403180700d019 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 658986699 1250 658985449 658985471
    0xa05280f0f03022b150e0402130b010206060d03050d0c08061512010b0d141f060914090a150b0a18060c0b0403030b04022a0606060301051203090306040b0703 69
    0x2640705a0f001d01205800000a2100541c80f05445415046030110b0100315045c4065084540344065840001800c1401040c0415414500a071020710320806009004020100380044e50310500501034a000303601d0001e480090503c6581547d44c003040150044c0305800100100034050300e02550018840d15462864403003200c40402110b51810044002001c580e20700600e4203450b80280412411103a15941500001912441c420b44200903c00c40d80b20001140c00008946c0d503499041141400304500c002c2c00758031418030943c800104100c2c0d850a040e80c640c0c0314030016003a0240c000302d030601840390109100446901030842c20807155203841c0034061443d58a000d56049215040100f13038509601c0001c20710929101c0c3c0e000d070081c1804500480d148020070105d0b4840c13151449158440d608401511075410542d00015501c80000c000504202c000282248018420907108460032800025001c00a0003a03030781842c1c0050aa8503286810b0802d00c8070454101d880c00000f924148200e98 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 658987949 1250 658986699 658986701
    0xa03080a0c080403180308030106050c010b101d060d0c03020307020f190201080718031506050f0604140a0306020a02060601030e19030f05042303010c080c0a05280f0f03 74
    0x2210510565900005448944017525074000841da180e40b40510b110300440450f4030400114020801d9030b40305590b40512000f200e007181c841c03c1810b4440c074000c103205800b01d5032081b142400c0c0103030b40101d030242448100004941d440307440c0f419503406042c1080140703040d8041d80070318030880fa00d070283e59090300081d07051601c9801c8210b40c0d0141c154008903101c050b511170705003c0d9010700b050130b00010122240c000038010307180350b80c42100d0480c11a40e0703005007034829004540080c081030310b51000419521000803494000c80c060810801140c2044c081c66a841003201c41c0290f4001e2002c640e100c08010000b5141c2c20115082404a070402444a103a0075000481500e610000d0150811000c25542c0031240e070007804e072250040110071300000c0b41601d40d294504500400c2c4260000014010301705160030364400d00fa0550902c0804070402100141c050100d40c0d481e502407910596030000030b850348440700c1e480c81515260ba00104041c0103000e405c03d000030340704219601c2d0000200d100c010220 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 658989199 1250 658987949 658987961
    0x20a05030f15070e09090a0c1502030306060702030c0a03150b01080103200f0316090b09010501090e06041e02121b041205070e0c190311030726090a03080a 68
    0x20700c45921054001448120490316540c0180c0f507403402c040c1c096940f2002444008081c0d498000c0303600301004d039400b01b044161608009050b54150094051141c58002e5101d0000525090044d9000118001103603014027200f00da40000400c02004c5a03201d00308080f805019100d104880c61814005102640c01850380c0c504990f44070060b581c241000c0030302107000e80e100c000c80a401813014507900f0394a43c3d051040150001c244100602c10700c0c54a200c040c150b030300b000b842c0d9009003400d00050029907404030000e019180d1f000c120340b413280c85030404100103203094001c10107003d01020f01d0030600390b115001000113030b246a031740f507c0580340e4120b14117158401000b0302d800f52000308001c110300855588441d070580d00600c16174800e140d0310f100c46001d14000321401c1c0781c1ca0000160700b0202800004124414900c50b141c03c01006220745420080c0e84006000441031003221002c14072400c0f40045403040b55030300144010807030704098008036915002d0712012008681d200b03001501c0403c02d0b120780 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 658990449 1250 658989199 658989223
    0x52b02010b2b150209030715051905040902030403051801020c090612070909050f210403060e0a020d060519020306033a0215180c06030a020d060e04020a0503 69
    0x41c11401c0880c20100c0740b8184454010b079144140c048020404080e10030321241d40c00b01d40581d5500e00f0400305818100306030454440601c0702e603c158042c0d6480b0056803403422628030300c10120740c0c10702130aa41a000300d03408242642d0000003000101603101e0040c1a070600060420036030303c00030b4401a42c445c40c400d8180b0790071880241c0003601515250040843d808030304001c2e60740d21616802c425042d106c555000740c805600032503442e09080020030810544400c00b660b0f0b2041710702c00da10044076510540c800604015180e640150030003c00780f001c0e08090740c5c003d06c00c4483d49103038540702000e0b150480d0009050310b5844000991180c29008480c454600180a801c441e084035031101c0340d00c1000d80940041c0e0189004041c10741c0644c454500440c00a50006d002c0d4085644420010b000001d00e50320410441082c0102e50520000310041d03441d07400c036012070710380d907541700c1d20740c001c3c001c040604401e1800c12000040500301d6100320f87c040d03030084e65160400c0d0749070070134143c0e40c1c41a0045 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 658991699 1250 658990449 658990459
    0x80c12070e090108012d0b28080d020607030203060f030307030903060501060302040b0d09080913050103170c060402040e0f1203060423040825111003060620030403052b02010b 77
    0x854544843c00140d82d051108101b4001400040c10008140c0d080300003000721001c0b030a6200c500001c4210f00001000912200c1c0090617260b0040400030745407280580340006160b00030001c1402566801500650300310042e0851345c80d580e050a0052a090040c44103a4103545048004207455100b80210b4054600d94a1442e2500500c201903100409c0d6490301506c58000c00d00c1003880550f2460040b6480341900840440c003941036041080c000402080c2c0303401d080c4030400807044803910214460f035003e501140c0001d010080058440c0c1004a11781c1e0400310380c061003070032640c451840b20245026a40030b0700c0030849180c50356a440040444c030800c0010041c0c060f00094002940b100040042c01016901940072032402d100d101140c03000390314200c42012591b07070703c0d01541c2050080815181800c0c07500f40440d1b8502680900807034126590803c0050716010441c3d00c100702082180d00a42d80715085601c00107003143c580c40a140c03000e844c0311892039040d4a100a0b03500c1400380c0301c110344006103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 658992805 1106 658991699 658991741
    0x142e1806050a210609020a020a060515010203031807030c090203011e140609010c0c0f0602150708070f0210050903030703150305030406080c12070e09010801 69
    0x20250411a082c04040c10716a84400000c5540008a00c4882400c00c0400c0711070180c400398014404180c00015440701580c1d00044d0301c2d085602804040100c0c2c1c8411107003040b0211a9480f9a0042e4014000b2600f2000d010500107810907140f421a80019035942d0b801ea03c00d170f0960f105000c1301c1d5002c401080b02c40c3d000101c0240c2440d11b400854489418100d00000785070b0300d041c10350700400c0081031000044e4082c00d0005101c079081000e20b008540e680e00c800141020f60f01071400103001b04101607103c0e04040041d14000d51030303511816210380d03807950210307000e5501401140c110304c070708010a00882c60500c9580d0044110310302450342c82ca08080060251000c0c0b413254402810450000c01c003040e000310556007034806910340f002c880c1d2203554011070607020740c86042e0011450003003803040350764019908442c841019500100581c0c0d9036890399080780d0b04105100d01447c02c4030 = true := by decide +kernel

theorem cover : BRFrame.Cov 658812949 658992805 := by
  have h0 := BRFrame.cov_init 658812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 658812949 ≤ n) (h2 : n < 658992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
