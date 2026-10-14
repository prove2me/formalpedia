-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2780
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:43:26.765581+00:00
-- url     : https://prove2.me/submissions/088b8644-d9be-45e2-84d5-3bad5af471eb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 499820143 ≤ n < 500000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 499821393 1250 499820143 499820147
    0x2160e0a201e1605030d0e0607080103030e0109030c090b030c0a061704061e0c1409031f022101090605090103120309080918040b06030616050a050f28 66
    0x65100d06000351440ea241a41c403001d0003a01d0100d1610040211004201c580d000724411282c3d64a40d0307001c0c001950f69a0440110348040703c0c0d54524820250f0014820404402c1d00408542d045941504001e1080440840101c3c0c50071b151342c000038031452710740e00041005589940500743c03803a003d030101d41c0c0d80700401040103400715580c468000043d00c17490141e001d00780c000001e5900f082c8560000b241c40140c0041248100b820030380c001000720740e1071400700784a940c800038240c007070000d0600b5540f5011203580030070784030002c1c0b1408801480c0351000941d00030503140d0488020300300c402103c0101003074400496035113010038030950040c00d0070300101282610b402d00e503490480b94006418041020146401d030042d001c080001e6a040c4802c3c03182c1c80c6961140c200740c0d5220074692070362806615061500314000781c07000c2c040750302030b80c840420000b4120400405680903007103400c0141d100e95054008170f800d84100c84080c203003040c02248101541010070700e034484822604940401304208100c003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 499822643 1250 499821393 499821431
    0x501080304030507150c0f08130e01050a03080906090303040e0108060105041401091d0d02010b13020708030705180d0c091a090a0c03020d09080301080f072402160e0a 73
    0x2c05040d40e04505000c001400210b5825172490615080c54050503005807a20030202043c0801990150000928034420b400f07030104c000c0c05004025136011440d41000027103032413100c2c9400000d0200e600000c2550640c0d4904080e1000f00000508aa995079110610b8180f891020320445125116210001c02c4602d82801200490b072400308072441c1d1680f03002c10b01005080c031000d140488190702d1480501403d402c3c045908507110a80020410710000d60074000c0003081d0f490440201031061114000050710001240c2d00300e00c02d842c12503251505900400900c1c10780d0200b036a402407400f000c100401071031070f850300101e5814003020000c2d80301540c0103626500c000e04031f903580030810000040c0a4801c541c8140d0020259140050074004555014000c80341681c206172106900440100680c8c2c0c0c0800800124032079107030141088914202c1d113003090300a41c200e05404605910580a00b65208125621181015140441480f42e0720381e410030b5080c40c19a503c003d601d0404000c26400744200c04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 499823893 1250 499822643 499822649
    0x1030906020706021201090e031e0d0c031e0905030d050c2b1a09010b0c07080601081b01020d0203180d0f0b09010e16050d110d12020d1b1103010e0f0c03010501080304 73
    0x75510341484201c240d9440d80b0f4207403500450ac60144a901044559445007440100080d02e0000e41e464004a95000da20692a0320030032082c140151040010700c04406c1c1c410303660700d540d004102031b2510804007055000e46501d08801000c028500c13100840c61050340d60303041040b840d04100c01701c0d00302410011040e11001c41c9400c11500c1004000701c0150340010000c45100790240e400c22600c3c1c8104508101081e4814000c0d94000d201840c58022140803200682009000400700c1100000e00a9200e000e0607015542c90910568051341507250350a507003d1003540558060124074840c5850030302400143c1d480a059072801060a20014001800c9201c0101c03c0e032038002070a162804100caa0341031418100d4000074540c4581015448956101c1c00d12489214002407200c0040002441c04040c0d0707901c0c1c0e0811104c82c9480030030010308000b200c82d55402403404448070317001e85c0100c0d0240011a000003150300c502c1051004806002c55100309421040303009200740d90b80c41880700c7e0f0304e0190340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 499825143 1250 499823893 499823921
    0x3061211041b11070b0705070e040c1203120501090c0e120f0105190c09051309030c0b19110f0a05180a06110c0d08180103090602070602120109 63
    0x2199020205441100816200c100100081650290712026840c540b141d0720703003000450400d00e51a0000001806024040c00d88000b50320309144460701d419030b0710744a070b1080c00003030900701000c0b400307104c03a00d0b041e04068044c14241080f00c4840380b90007805890409003040a86107050000b250544050065003110803c40d070b80c40b4110362f0400c00700a8010425035600003544503401c0c00c014120740a004071882640170344010100b248e03100c00840290307010445c004040011100f0180969503070341070b0b24900d80900c4000000c03003088511b4103030366150301d685028000d0b00b1202c00700100c0740141210001348038291030701440500f04020b01031341507000310a40c1a074001001d01c40800b0141c881d40c050100ea041c100c0421000f00c2d80c0c000810480c410b00e4000c0d0000a18109159400d40810000ba01860b07806403680e10940d465500c0c1d051003409919002890088001611545607120760490b4030000c0d0051030440d03940d149442e1160003544844400c0340000b0404000251182c110720894541d00780c11 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 499826393 1250 499825143 499825169
    0x70905030c041a0301060b07031b020108041e0c0b0307020c040203040b13020a090c0c0204050603061b0a0509030609010204080d0206040c050904060609150819050709050c0c0f0604120306 82
    0x1007070400010b007210014030742c03045900c90140541d6503002d0180c2001800c0800203e0f40d2400a41001002e07a00003050a45022201160010040c0d9211900c5d940c4150802008104200300000c00d41d4a00309520010744071128203400490281c0b1250010f600515440d000c031070305e454035a0203001c16400110f030050b1450b0b02840010309551994041d00c844c041c801010301c4d05040c1c9400b0160f00300c442e800c0e41580080c0d4085585811402c1034454640c0054084000704401e285c071403100e80c0020b08856414815041c00705030b491069009205507800114000d05450151070413a9085000390424441d81a02d4812070b0403a0341e5aa0020410a0041780c010074462340090030501405200340010b8011940e0607030b900c1c030025169010707100340c0354500006510025a07a04e002d4130fa41c54005c10760078041184c0f508800820004900188031800c0720391440011409075507196034981d66000b40d401c00328880c0140d000b00c0b030081c400400ca05114134456090f01900c20400e001c100c0450f841c902070316000042c030b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 499827643 1250 499826393 499826413
    0x10e1b09090411132c07080f0c040f05010e0a0c090801062c071b020a0b07080306030d02060606091212070c1e060c03111218030705090f042a1d07090503 67
    0x704840700c0070b003200303840b086402d0144d540c07e850b0700c1c02d40d5540034610720380c00492001240345024005c500c51054240e0040c0100c2d410a1204d111a41025003000c0515035030f0345407600d205010303000581c010000100204038982c0d5980321010b50704128400e40d010030031808101c4101e0340030a904680511010754031224249044d00c83e05400d20f5002d40c1c26684900b000500082ca40640401000390038030644c015901c9040c240103052900c0b02c0c07041c000f030a54000358100095a100c0c41e050300e0b4041400c59400c90410b50100400342400e85540708114403104c0018000240143c80c640300c001c07251071841d000d05500c0c52401c01640c00101c3c0c082ca0700000c801050403070100707211b651503810445450040c0d8201a860b06210b02c3c2990086205805401c5602c5a03440c1524003402071a0080805440307103d064549000d6400c1c0702940104010905200c03081c00383c8a4906860350000b503803801e0b0310000c0c0c1040d11824040a840101851110041c8030480020515403084142c2c0040303035000b03001800c074056 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 499828893 1250 499827643 499827701
    0x60f0902090c121807080d050702030c04050402010f1d091e01090b09060409060212040c080d021516090e0712270b060402090a09060f0608010e1b0909041113 69
    0x1c0a104031403403074481c079074000c1003011b0103206c800203000c41522142d588800710700c14541000306403400948120300d000100400750f42c1140740c016800b101c1e0b01c0c00f41c1850507490040000c1420512100d42c11000e0101080602d6003824070210909130441d6802505a9840d010790043d50b480d600340c0b0ba0841c01710030200b241824281c00401c106c0f880303000050305013070311001c520340840812541660f4140c11a54204820802030143c50400341c82c5101810428032140064901e0f400080d040c030000ca03100080c64a204da03c50440c0c00301900e40800000040d081c0113038010000280540500e030006d15098150074008444041e00300050005900b2080c0c807900368840110902c40103003040d400640030400020150f503102d0f80e0310040e103144180007910b2820401030310300c4107034030350002400d00c14800014882e180064840e1a4801808009100031030303040c3d04009a00d0041c848003903046010b0741e0500080002201c0c031040c050174256180d140030007140807601c0503119040c08041d002400840d44004c0c482e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 499830143 1250 499828893 499828921
    0x60f03060408041e081915060b090d050102090d03030b151c0902011412010906300c1a0a0e030d0e010815150c0610030b071209060f0902090c12 63
    0x208455401310201e42d4405001d8102214043c00c900042c0301c500e0100200809400003440c1c0c03150710b0508000c41c03400c1c001071240910400811070321524034440403008000b000d4040390f64842e030140010704032806a00d000384c06090040f034281d105003c124800c1e0b0801c0305040555541d003007840d0000c0f081e102000d49000091a0255061381044001c00240c12413440c020300400444030b0b111a29881c540c50444840e0071078005400c242c0310a002203d0101840c1e41240d02007101b011a15140c410400c10f628001191100d80d9000d003004008031804030003918410005003d025008d0340700e40950355140c1c410562186d4071245804046194229560404e5105401c826804401c01c812004140100760004201e218482008000e249000485406001091090701d0f040100038000c5a144e41c21950380c103540e104010710036400c118002c106800088003e0300300400700c6801a0b010070400d024005124080c10000c2016402482c000c0042070000b0001422290395440e00741461540e40c1760151144025 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 499831393 1250 499830143 499830179
    0x504081606060819060e0a052e0609020702040b04140a020d0e160807060f0207060e041b050a03060f0e060d020d142b02100c050c03070605060f0306040804 68
    0x91070b40c40201040c0460200810803180e420101008140b00c618504174003606c0350307100428000e80102c4003083c001940040c0c503070f41540d10140d944042025480b0102c003407098800354001c2c0740313040000001c0c5407092540280065030094805124074182da105100a9401810020740075040070800174030001800d6000c0d00001518501c0844c0d04c406c01d1001d80d160941001808000c0021501c0070010030104103c09001007450342002d01c4496580701340030391200171500c1000d00748150424080441c0d92154080c03041c001c0c50070380c07800b00644545402081600704103000b1000c0f0341b0300b040c08a07a001480403060708032010303080e071425965110302c140121510b0b6440c00f20b8000f0360a01400000468220003028141c42c04401445485400c881140070348020001341f010390f0340c0e4813003000300169020600c11412106064040b8996070b610904a841340b1580e00c16107540c1c04003003566010011940c00c045e000c3c4804030381d0018107007488000c054603610151001084c072401080104041f0310001700308045 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 499832643 1250 499831393 499831403
    0x916140301020f030a0212060d030f05030a0e0f01060e0106031104140102030405090f0a0f050c070605151e1525060605060406020f100b1509060408032b05040816 71
    0xa0642c0d044928001d80c00540f80304c22056004507e41030341400f49940307107900080c100c6c1c08511502454030081c0c903515032000c038101001000000140c010321241c000c061102e056000700c450b105942e105046c02032000b0b00850008023030607000091010f100c0e010f02140916401c81d10340c83c0c1440c02c0354a1920340d450031445410f602050000080300e60f00c882c0f046210340c00c41020a000b500d80010808200c800c5031a074007104c20700d00030074048030a00c20019600e82e590300800000b207544a1000e8000400b0815031110390100007007403501264402d420700a20010001d5030a42c030040002040401140551102d02c001841c41c4135441e03903100050a4046c2d59103000d03010000d40c00da00e92022804070f43c0710b6045074001d0703400b03000e410032070207400c02096002a105080c100031001440d000941206036030300100b6101c0b80049070b500072644e503c104540003841044112561102c2c840340400780302401c0c0802c01c03508204030015110b00401401003031301c00c0e80e0240c1b0961604c955070742c1030010003192006c02d41d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 499833893 1250 499832643 499832647
    0x102030423030319080a020f0f07020a0302040f020d060b1612091805150f0f01030b01110a03020f0f12030a020a0e0a0308040f080f030405010c080c0706090e091614030102 75
    0x20726510188014100710160320360201d0f903c441e12801600350f40340a4044c8440318810000c0c0e071514804403040d140c44a03205510a69950024000900800134035000a58000d20303000c2c501d02003102e56402440240045c2400b0312080d91b450180c03030424007030b0417840303091f01000205003400540172003440e410a02d01810180003181c1c55003210500c030711210001c1d00082c0d40d5801400300b07000002465803488402100c41c02e0030f0016100101d81824550700e01503045c5500d0342da580c001d5a01941071706040b4900e1108076254803100d424000c2d50ba0040c400b100000d4010620b0b442c880e204040b40103000046c0740c85845203942c450030f011400075480740d0060070402c090040d004045586882d842e8008600544620703442d18244003146940c081d04c4d6005000561243c1800380c003e48000c000c0d5400c690302401c00d0049003100f1302b0140781a1141c42500d180034040c001d00860701d1500506a00c080d40c2440740c02c0051030f651144425941c400b00c031403c00000341000c1d810072468451081b0004841400740c0058 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 499835143 1250 499833893 499833959
    0x705130513080301060216090b0f120703080309030a08010b0322170324040204120f0c0315021206100c0b0601050d0c08090c0405010e0a090807020604140310060501020304 75
    0x15420f074200b03070000300050300f08103200145c90190407c0300c0c028180440382005800c51140018180b030340d040085601070092040340019000d41403000f64025500681501c1d541d2030721000c400e4880e4071080106010910550022540d5000c1e18260b034802c100c600380051030600050b4102d82030220a040440d0300350303c0034801ca084010120090744c064880e840300c1c0a503400c2e5000040c01c42940b03144240e405648140420441c010469802035540780e00700103041e44040d0303a828a16600061900080d10600005c83e45503082140c65006103903001c0da01030601110380f80c0404210706d03c00480c040c240015080c0301c100010544000060b9002603050508a1400310900c0003036093352a20f00130480410041e00821100d10800e001d6183d1000044604111660402180c0c041400000c1e04805a550f03494204000f00400d0804841c559a002418181c480340d07140c80003110104040c0d1154003d0007a00740c1c41601c00110f002c0e0701c05540b4160059410142840d92100c1142c00c609001902c00921141070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 499836393 1250 499835143 499835153
    0x27050a0b13090509190b04021008090a15090c06080708070e0f1c0c0f030308090a03021f1103010b21090c1302070f050d080c030c0306120a02030d0518030705130513 72
    0x1945d2a501c07483c0c03070314420b10701401045200c07411710000f1018401c0600400c01040d00100744405d01303d511002c0c21121107500e0142900501d0b00c1c1074002c00c60040d0302004150385810405c0c15100360825603c009641d5070b07841d01191101c030640016604101300e500070540301c1c079207814060380301f00756103c0114403586283c4074061800310326841440220422a0140141030f0f00540707543d4452030038001040441d1899400a43e0340c0480d1030010f040b1a000e90464020710056040422224144012a612540c4a0001011a901c4074201da81c0e0010400d05c040d60511450910078460101070740904681c2c0808401d100420ac4803c41d004d05d190f900300711502c00240142181c00d4a0341c010402483c202c4c407804070280400802501c440701001c01402000070664501c801c480c4e1050047d1441c40c0ca4003000180d0f18a45401c500c8000e501d8000d441007414880d9001010b1301d2001004910300039808004070a168540c521030003441d40003030300300010b583d00000d603403caa50003c0318000c002e28082030701c0d01c0b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 499837643 1250 499836393 499836433
    0x30a02120c04050a0602030c0703110307030506091606111203060f04061d0601020613030f2109210e280311030c0a05130c27050a0b13090509 62
    0x1c40400711101240601207400c02a4218020348a6030004618000581c9003160342c80803070340f000070b0200e0704203d208226070310184158801198848126001801e00603c003d80701e0b0352501c014804621301d20000214580300310411404540c0c41800740034924018410150320354001496240c024010030118250340d107481c468403009044108403131a0744241c031074071080e140c84058080b070304542c002c0c01408100c80726800d081c2000d50f450304140c803c3e001c4900059501c5001c1458605c803080d890f1860713002c0e01855802541429215011041e0081c40381c0e49070554100c00088090005010f10045440c6818402203a9064100d505403913030407031200e80501c0e5000c01c01d541003140c0d40781b401d002403800f86c141040b585031418022200c01c6081424500400c103ca44034140305c0d1001364a172043e052101e8042c1e001903810111803481840f800c9160200341c441183d00d8400c090148200d8031000507000a03103016683c030030f02801144003000e8941402040904009810301c80e8070701900200c446e0b101c6200b02 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 499838893 1250 499837643 499837651
    0x406050d030302070b0612100c0314091b0103020309151b0a0210050105040504030824191e050d0f0314120a1a030303161106040c2d0506030a0212 64
    0x40c0140c1d48100340d25050031085000b40850b401481003490709180118041052201d00795030040c00284842701c40720403405814101d803030b100c4040900d0b091251500c0041360703000c0d0908040c021140c0020010004404034442101c20041c61740003850180c0380444aa8616608900c405101450b40c1c4403020f51124281d004035014000b6910040c81c91920102c00c0c0242c134010001144c00708183d241607200989403060041c810155900490b008500d0041c0c01013509001031409450b03070714041810701001d01e00c01d0003800358160300c11061403a0102a080341c01c080c0d059503c09420080285400d507900c415030080c110301181446403988620703800d400040701404428003119290015418030021210840d0326680ca01e21201094094039141602e0000490b508142583c0405109280c15501121803038003500f92a003650003a40b0510041c801d401d4072010a0b02c5c2c5500e4038000204c081e044003180d54001d8510302117110500031080007940f5048005d550701072042e55002d0b16001c0b07080c12000b2a000308903 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 499840143 1250 499838893 499838897
    0x40801020a05040e0703180b0618010303051809041a13061104090c03021809090f030c0f0607110c0d2406030b0c070305030c0a02011e0e1209011d0406050d03 69
    0x10038100003541d104c003034071381c3c1019450900b04044420307a0020b000e4040d404401a04000b04240800c1080d11146400b4041c01012030604285507100d00e00201654000580c0d01940e9607412162803091410014581c0202c0d030100c1a440075000100780c1c1d0031030010085c00c10505061403040030002c15030034001c5c09180d070a160f242507076a60034072101c041160260003001c070030140b047c4244988035124401910103910102c07000f003c00d90f562214146840c45d52701610410b0b0001050840c941c0c00c0020f1030b90200869601903c8043c0d50b28034007190716154200d902c0c40982c1c0f0039400f444450500d1034146a00d60300411803480c518440c010803900c005840003001c48000d94450040052004007200b068109445024041c5003141c1c0d602c0081060101078081658640000ba20300c1046000354400400c03050100d4060352011260001000140301c00401080c181c01500c4008403428128411641d508030140c407903100303203044201440c88207001c900c440d9402640d01e000201d902c0e642d9581c1e00420503c65 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 499841393 1250 499840143 499840147
    0x50604031716050120040e130203070f03061409010506060313020303070c030308160509010c02060c07030f031101050708130308071403010b0a0908061302010f14030115020c03060f0a0b06040801020a05 88
    0x90440080310038090001c10150403020f000902229007c0075a0b90f0300428031980611000d91603000290604800d5800560b03840d202901c008100300d010b421102c121007002c80301e0401030b075440300c540e407c0c3c0d0402c8402c158820020030000d0101d9100980d000026030000d003c403400c0c220310740e0b6400c0c7c19012682082e400f00c0c1e520003c209041c0e107101012221a032017880e140d400c1c019600000f0307004c80c04040d8003d00c0340c8004240143d0340b0f0010044000116007010b80c00300c41c00403030701307014007005000c8210b0345065090070002040c103070248503040d01071890280c82000e0802d0a4800f1150142e01034101c404002e1544940c140342c00380e4101550280120601e2503a80704050b401c080c0c1102125800f001e02038100008010507180c413365444d403059020b00340104114241201101e896001c22400e4201440100022135040044007000200b03401a4003150402440c0d8810035179125411a010f81503141400001000c3c1511500131800b0f034000544101c1c1447c4d00c4504181c02d80e004a14094009240 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 499842643 1250 499841393 499841411
    0x2071703182b0207030308012106020a050c12030403090306090f0c06050c070501081006030e0f1f0b030102091e03071805061c0c060e2e08010603060506040317160501 73
    0xb001030a1000b04403600080c014645103580c0900b07225014403801c42c54280f451045442c4400403810060403c0d4800400c560f18056040003400c25000b003140ac1c00b8902c10420070300f190070251421603004a03050b8440c00c0a451855071480e02a081c4404201c540400c1c06544600141c0360f40c00c210060001d94540c103864a80042045192141c0c07039020504014411081c08501008201d12800762403031032a0204840520707a004c149000c1003605045010b1241c080c03024809020101d807403014040e010418044414114109404e034020070740c81c3c55100c1d0889155411500c45a80040c04071301000d0152184103540d00070400810030300d001c9035002192070700704220452802d0386880c04010010340b2460451180d54170ba035007a10071117004032000d000902c04500c8055468111900d50340e14415500c11a09200d5a51b2950418450010b2004130f10443d00110382140a40143c40c03d84030080c12031405c007031550301c510f600186100500340d9082410800b5101c01ea03032844c0034a00281c0101d00100f031305d0300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 499843893 1250 499842643 499842703
    0x91b1a090612151201110301050d230604150204080d0e19030b04110901060507080c01110406030e011505030c13060306050c0a12050705030f060f131e0207170318 71
    0x121303a402d42625924041e102c0c40c4841c3c081007503d05580d400e07111262098418a0035040d0111842c5102c0001004085180c004150001d40180b20314030640814228444c3c0c504007100340e004a00483e1440d03005400c0c1844101d20510003000c407408002c081d104065401030050b0000c9403150030907141c500192007080140b025200030600d907004144c400408541c5041001482800744000003001c011001800c0031040100350004006e900c148404555a00d07590000940182134440001203603500313148031403480d04039103e0901301b241d102901034008680364900300543c00180d03607041d0035227503a00c1d0300c04008a0401d2041d40c0c0304500ca00240d80d41d0300311005000e0500c110035100301811500b0141002105680f00301034030340100d10601a00c482d42c44880002d12071030810702e90030b50013130320030f5041560b070800c41c6e000b200c082c42031410003c010020200c1c20703401b0b910403088003810100700824010440c0c6d0f6a5802181d01000f151048241d0602042c4014245040c2c210b0703000002401c00ca600c04014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 499845143 1250 499843893 499843909
    0xf19150201022203030503040f210804021903050c0127060c0b0c03010b04120201020a0f0302101109060a112118060304020310050613020c01091b1a09061215 69
    0x8004a5181c3e00000d1441e45c0042061200400040816120b07140c46030800980b0210303282034601e8034031a83c01002d40c040c1e0040c07001c14129000e900c10a500c1c5000040a0866250310b4107407a00213020348001e0305c01200545441d101000491421107040070034010041441c048100500050790b0f0b2100c041e101030030300906500014140620200e01000104080c0c4602d60032101158a070b1440c1e40395140310303030005034245080448058401c0b0b0303203000703100101680401c0107151482c02180c2008112840b00481c015406002000c03a08074108100c806805802034101c403040c08040b00c00c0b1000d0420080c01405250088240101e000401103a04116003e4411000c51103420940e00241036191079000203981c0d081828440c403503260b4038004038405446011b00c04807080c840c1001590b941c12030001c006d00030f100c0301d201602e00b80b41981d5984801c3d0070342e0550070115500f00e5200c1418054104d25031446901680300180e00000c100040f0300d02c400440e4400b4441c0c80740d040c080503520400000d02001c9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 499846393 1250 499845143 499845187
    0x30109050f070f120221010f06030b0d0f050a08040308070c0e0c07061a120609070902070b0a152411030c0a030503190603080d0b030102090f1915020102 67
    0x400503020800082ea11054070544440d052401ca28458141d402c2c0c90002e01c01e02110382401c01e001b8101101c025411003030181260800036003c04e82c5980e83c10b08908644a01c8000c1b603100d200fa001c01030208a1040001e6001381c0140c06071220207900c1e903218030345980700d03501c111041e00300407600d001446030710169000203101103014500c1e14075040f4410384562040360b00040585640e08230312010340a4020856144600140c103e1030f12140380b074511a941c3d1000c5404560901c01c042d404540700b0801e0003a54291a400740c600319060700c0720501c540160400c5400d140e20304c0c11010300010084500c0108a800142036140e5011891150400519142007486d42c051140d000700042c01515000003004c00d0100d4141c40d044c0d17201d441713102d82d043c092641c000440c50207500b005004028014107800800000840c044200994160304041c9402d0740030701184140d10080c0080386041c2c40c248801d0611260080100e801809a1907454691400f40c03c01107000040c1c1d8041446418003440c8161301751a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 499847643 1250 499846393 499846411
    0xa060609031a091006060c0203010b0d0b060d03020a060f020c0114070207061107032001022e02160218060102100e0607051c0203011e120f1704030f0803010905 70
    0x2424110b40368150b5441025040034811401d8600007440c1802c1130010812002e411070080c000613558100060090010b82410b030b109510b4041410414130b0f01c44514408187d1111600c80f19030340d0301c003c110582403030140550641c051844403200103141d030701c540c441054445000503225402c15540c58216104004080024028081448040c0303800241c0c1000310b6021307140c04450007605003040c0e800d100943e80700a2800d10000c0d400600d0035241008007000c0c40d07083e401c1380c1c0f08025048607024081c4481c5510780715641088043d034005031042c0c0090000342c2c4c0400d0312444c2c1c2c519030f45c04100e81c0a03d4030510f041e00009442030002a6a040c032640001350f80001c000e00444526402d8603442c0c410140694091013800603c14000c0c0c4184030340d010301c42540c10f004544969440621880e114411480d000d2180840000498010a8802001d01064001000920868682c2c0c0c2e03d503412451110b000c0241ca038144000400502036003580354040d8070a40d10340c1c0c0c4a500d000300220980f2809031580d44 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 499848893 1250 499847643 499847657
    0x9020f07110d0201080402240d020d0c0c1a041a15090604020c0616020f030310060906170a11190309020f010f020d05070206071205090a05040615050702041508060a0606 74
    0x101507139105c0d03449904290100c5080c110b46c0c6001800c0c81999503180b854421014005c140c030041d40c0b056074003400d01c81d014814140052008080100c60710181010003c100003401144100748046410442e507100d40f0a2141d506070102210021103411421281842c0e40f18440040c0c0440341402c085aa03080300c01900d0540c24130001c20622919920000c006c0c410b400d5032501d05804480c420000c10307017601c1c4c2e090196940c9051100e00030480580720f001d50000305503000c2d00068030350301c920140c421144482114002e01d842d103401c6480603007004000c4440302c5205001201305484400100010070380c103501c000562248501c1880300070340008600b0b80c10b1101189003440c4007900841c1e07d1442c0391003454020b03929082c910015400303000d00074014007007200900c08001810f8200c1c00400b000c07002140e888a089030380b10104010b9408600481d00d02c00032000d10803c0460048024100442c03006201149400d84000b0401342400d803613100c4c0700e0650050381071000d0141c03544100d402421b41303890200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 499850143 1250 499848893 499848919
    0x3181101021011160f020909070e0610091421030901170402030a0312090605070c1a0106050f09010e060f030402011101110301120602070203070e0a0c020c1309080409020f0711 77
    0xf0f40180c481505600c0f41050a08041090001c80c1c48201603004044515906060100030303641e841c03501900c2c07c01d00c50080414164541407035a00384000300e581c1c48004903410020307584800405560819001400c0d400c2400ca15964100c03a40361080c0c02000071919002900e0004140301850000c0803514010b40d801d10000d42c82c0411614071468060610800c00704071413486500810803014084e0086203040207000703107558082c0801002901982d600f28142c40c0790040342008202c28450880071400030010305610010750030107807181c200c050509103641840000800c0a5030301090707000c00c038005c001041008546c0c2001043c0c42c10408074008000c524541241154170b0321060182040e03418030390303884004000c000c1d0111402c065000d07040c1c84c210f0355608050414202d055907424052802c20404040083c40094000650500103001c000107490241e00440103200800007558034200404c0f012503540d41c60b000500302c9111000801c0e40d40c52190a18540d02e03c0c0e61010365216880c9401c0913 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 499851393 1250 499850143 499850171
    0x170405030706052205070f0b0901090e090a1b080708030f030a021305130905010b011805061b120a02100207020102060f060a17011508070302010804060c031811010210 73
    0xa9004141e00034000611611402c04d101c1c040030110180200d2114150941001c0101c00702e22101140ca0380c4214240c6140c80d000480301c58020800e04600054009404004440b000c041654118884d031042d9a034040e2240c8030540d40009101400b0700b10482c46004200c900307000c008a10061180c080a1030604401c013001000600c0040c01c0d1200594000c1613003100c04810601e071100800c4002c0c0700e0307204070420089190103080310a205907815403905403244560350003170710240410184152040718031410141000183d4000c00d003820322400e03000c4807a085140b400c014880f91140c1d007550b01901c03010490b00c02031401103400c180320f04250041c000c042c0107036000030f00c2a42161400a0807041d96030384c100030482c0c2106d9640019a440e000711042400e4a006501c05c4180182c1c811b4440c040075150b800f144d5550440e8400207001807206800607003c0b40480e4840a51007249280100e00042069021804500701d14020f5071280507100c1405415a01000000c0c0847c50654013400090940b80710 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 499852643 1250 499851393 499851397
    0xd0203090306150301150905070e040501080d031a0315040b0901060f290d1505181602012a2304120c051306030b0c0306030309010302180a1517040503 66
    0x225044401070f030341c6100358030740e070a403c1030703100000c030728180403030950344d0740c0110060081a9010f0001c16014240001e1038201801114182d61102004120140120404900910383d4021424581c0f4501d81059480d6406004400b031440803024080180e04090404000e40000940808150fa2500004000b00824103840c2c208842200b202140042448251540424a614000140c1c848001000110a21f00741d005526050b40d0110030316031a51200309010103441c14040100c03075a00000300003020301055180c0804107814a1002054483c1100320368010b10101604e42d8500c0650f44013640d500d43c2d445a100410000e60052035400c3c00081c81c01c014043c031450054043c10075000c0e00d405c05101c86c04089400808000d04150301840c503042c0120014030b00750208507401d032092400b040d0901c80d240181e901415008015515024a0000540c001c0d8028650a80300e084400c0c52209640d85201401008041000c190002d0850501008042405050114000e050804107100100e640001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 499853893 1250 499852643 499852651
    0x2070302040e1507020318030f121b010c0203120c1806090d080f190f02070b07060603050109111f080609100e01170c0a0e0f15120f0d0203090306 64
    0x20700000c0b600c040302101401d1000d03448640715914159000d001190350300000501800d0350305080302245030750501c03c050300c40c0c2ca150600000790344260002d50b403444140300180304019890356113030084440d0314203250955070426030310005a00302145c03409000c1d010381030040c0e00041d014105403a00115442c440042c0e9880c2032100d003d13400101b11000b040c1c4407a254103142c5a0840141525520b07002e0030002c0390390080142c00c0301d40e07030031019005429008442d0408440304940141c0004d50910000782c0d6203420440054481640f03c10740000880c07802e114800c2c0d0140242c1c400e0450300062014030131024000d00c2c0d030b102001400841e21052030740c000d0b24140c000c0012180440aa2500e13011300d96a0100c80d000504e40c10754000001455070000420f80c0340c0844406d0941e04403131305200803c00014400c0c412400102e112500040c14008090103881d031060448840409502c01c0300d000c00c9a0b08401403040406621800c0c1042d040300c810000102c1d9820107100442c50a0160300119840700381c050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 499855143 1250 499853893 499853899
    0x3060b1c0c030e070e04050d021c18120b06010e09090703031b06140a060b1c0902041b1205061e0909070e0a1a030109052e1a03190302070302 62
    0x141c01145164402d4011940203030442040302c0c40117481d0500b1110034601600d08070340b24400d000403420164000f2400d85219600400380c114041f80e482c40c1900e01009080184030352485070b0a000c0380e036654031201820343c3e80c0511105005407520344000740030207610300003551242d502d150800050010014640054075850314006012035002c0041112900481500404e51070500002c102c0320360304040424480c2d0010321040c0845541d413035540c030ba81e1007030182d001003590a0b01303101504090700380c004002540c40a04000b070550400d9044101c24211b10703103a00f00003100020031000180450040c1a0005021102c080e98400904d030b060b1313002c100c08040a4000c5803e1b00c0003030381c031003070502c0100c000300f142c0141d4441900d002102c2d18010215100c0041d030f1001500d03449441070605100380800c20b540b010040030360000d0780801c0f12220b0b116403010440110403100c1e9040c14040e601070f507040c030140c50240c107811660501c01c15090540000420104002e08070800020032350015900c82120380513 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 499856393 1250 499855143 499855151
    0xb0a060302160f050c090f0f040308060d0b0f160e03030d090f1515120308010e0a0609020714010501050913080a0c02040c1d0a050a0e07020106080d080703060b1c 71
    0x8a40c03180c2100300325580582007540c40c510103c10f001d00481c201c00d4105e001c071030f40b000d1640c80c00d032180b08000d01500c2c40c140018810700010f002902403c10542c100300000c01c10f4600b20b000b40d49900c4980412030f0480ca00c03105082c188140c0305c00410b21840c00d94031764180303202100402004070344e40b03004440c00c031101507032240c043c1401e01500c03580020071a5003200b012407100c440c07880c103c03002e4100d0082d050f40201180e03000050b1034020b480d0071040c16905a840d1055a46441d10343c01c54040007400451a4036610b00c00000c2e078034201c0c4020720005216980c504c0010400110003800c540d070503880280a10b2460b81048411400c2c80705040c422036105289079140c010410003110100300300f601c0290054a08005c1d1000303d40c03ca0031500c2c0101c49108201c10000c020014040d50392014402e850700002c26074010b00401204a5541d40e02003098800020440d54810fa110f151000780010400070039004001d0081440e8140140341c080c201280d49035240010705242047d00c81101d4108200403540d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 499857643 1250 499856393 499856407
    0x4030914240d0617011e02040303050307080612070815090c03060a020a03060906060507050d1d010302210c220302010c02090a0f0501170705040e030306090414070b030a0e010b0a060302 81
    0x240e40814060040015007120305500c4c40266402009101c0c41c60b008564039a01c40100c00342c881c02280c3c15607615a40c0c070360542d00c441d0b1050f43e6800e0040c0c41564400d01d0b404890009203030400420004252440080000c480c11602d180f00c1c0c82006040c240a030340003c106401581c0740018120340003880d0380b0b801a0f403045483c0c42107000b80a143c1161180604003800040d400d5800380140041901440640d900b038131070150141c0b05959508048241d15151042075215907000c2d501900641000341c1c00c800c03604441c4c000c410301c015002c40d41030b02440004103d0040c02c524141c1080305000c200d420b0b400b019815a0000380091000d844001d109101e2030001900c02d41d1607400002c25020110000c0c00a546c45071046142804059030700d102074810750000264610305030040f01000c0d00400003551441d2621030a00031520001441030b03400c0100125a61420442048920300400c01c50010702e8485c14019101025100e5082c00048240c0c10501001580d60b1655108021205c00e802c0044c0d031141703 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 499858893 1250 499857643 499857667
    0x31e0109082b09110103020c100c050c061006050702060307180303030b15070c052119020f030a03082802160b18030d1109090403091424 60
    0x58480002010310310301246052038110145100210310018500c01c0905441c2c100010040350761400e0050008640d011994034154007a50090200a1a0000381c42c15400d503031403007801b03680c0502c0340c42c0700051001410841040b018010f03250020310303d18248e2402403410000514034003c411019205120010101e0b045e2401946a1015122080e51010155550b0709001e40107041d03c0e0400390048180440843ca07012204084956041c0d00c600c3c4242c210f401e080610035010642030001c80b8088140c0101045280d0422034041488041002d06a01003203d10510000030b01c5003080d980203602a20240e000640c0102d9501e0340710981034844c50200c2540c034a031062000c070310102e52000b64400107801072070112a12344444d10b14090160b414190307c85203007109111408a0007a0201c0d04140923500150240d0b421015107440005001c90401c810000054540e00c000d560850201d608401c003000150407070503e1800003481202c01e420001002d5a00715070010254480100242c4c000841401c564 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 499860143 1250 499858893 499858901
    0x60d0603060c08040311010b0603160e190302040b01170f090c0a03050601030c1410030b01020c0402120702010f051302010311070605070f141611131e140105031e01 72
    0x1904201e0a0252501030103000d808038000751401c4c1d0014442500304038949405000342606008060152440d40d503500780b00900d01c4510059070f10400500322450495582c0308600c25a0001d030710800644500e1861040104881c4c52000343d40c18000c003006d050b180c10014202040d405444103004052541c0c94201c07060800c1c61715180245d2005018034040306000001521a069912a14510080d0794440d040849541c181c01c41c010b0780009482c0c001e4452900c20b400274041d4420600442c0c510003007110000d01640c00030003184e07444401c22810001c01981c24004d11021b01c0c190700e0104240e0522000900300c041c510900641815180c040411240030b0388012101c84a81080c01044a03092140b0028070410000304400f00140610280c1a2550840000c4460015030003000040704409655146e10f800c241814055000c0100d0000da01404c2c075600442850580d503903030756001100301005401c1103600b11421000d00044000050000d5140020420505024419a0754005000300d00090240c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 499861393 1250 499860143 499860149
    0x30703090c1a0d0e15180102120a02180f0901150504030b07030504050f0606060a030e0a050a060608010f0216020f0d0501060321110c01080a0b0d0b0601030509030f0702060d06 77
    0x4051014045800c2d40d00d030002d050b11880c1801c00b44036119201c0511030b80e0b914507041c0d0804503412080410741c0c00a081c600034846107a007500241c00c00d0343c040d170044122501100c00c03000c0e15400181c0004200440c20b20752003514411075110540038982c5c00403c000b079074140038103005410094000c291850046c4180d800559010811403040d18106100a000c1e10060710701311818414502280305005001c14001d20a03040900210700380441c42c00c08401a00003202c2044641c01603c405001140c01400080c00d030314010000420410714080c91182140c008107000f06a0a106100106002c40b80f0437019500710f40445840318140202e000080d40383d000000014191761a1480003c00c11041e20025010308a022480b07980b000308000056400382000e801e800f040340c2014003421110360142d07000c150080c1034003c0025090a500004c9103400ca503042080d1000c0041c00100145582d01d4003502d076005805d01e003d1030509c40c07100310261060158020081c4500000706014035903640e264840320003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 499862643 1250 499861393 499861409
    0x2703010e070314060f0c0d0510121a091f0209060f12060a0e070516170a030b0415050901030602070215030f06040b03010506010e090a09080f19080408030703090c 71
    0x509960749403400c1c50b074284080f000c195010b220000b0703244030340e400200d03403048400e0483c0d2443c191480c542c907130051400406200c40d01501040119079400c2c60155004280d210301810904001c011488035503610000b4a074a11a0384240c00b0a4000c0300568141c3d9402d001c0e090000d62161400d0380002c07030303900424918070038220002c1104400d43e03410205c1c8a02030081601c01c50f0360386803036541d2190504400c80f03203880415400c0040080c0c4110032280700c02d0340c07030280c039000a2029403040402880c1e8850040c0174006500c501a4001916051090322a01e100010303520412902d0000450003220b014440601a16030100c0c50b02c065403540340f088420a0807080116035603144c2282591075051080e204140600d10709040314405080520405020f0507050b181c0290481d606000c00c08130314401411400c84070b86900d4440c0c0000d4114010b031030483e007145a000c0e100c08a10301d241c02c000b0320094101c801c01c0515030500003c6001c1a003201d0300580b5510f0081403442090610303a01e445000d900402c1c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 499863893 1250 499862643 499862653
    0x10180905090d03060806070903080a0c080d0218060702030706050a09031b1409060618040b0909071a12060d020d0c0f0f05120c0418050f10112703010e 66
    0x10007003001c2120842e40b21592804c2002e2903c2d84d4080da60795108440d8640400c00f03c43d024401b00d04407001030075410682c0d15005244010a6030b40e40ca154000d29040a022130b0003040400f9981c1d0444140903a2490a940340360602d407007600000c0c1d607400c29109c1c440500000182c001103245c81482d95002454200100a01c40342d007212000c401000340384168820034a0f82c0641542a02d000d52846008440080c0341d1414122000d0149500410080c8250b52041e13070340c5400503440d210884014820b4081f04064079040349000140c1b03169865001007000c070180d00704802140c1480c070990316604204c05496411030b419061001c036620392110400541041004c90b000070341c088002c0400d03000e0302c00307100c4030074102c1c0e958005004603485034440c008055041201c42101905040c0c0c0450411140d00b00c40352110041d648900b404c1010281c81c00116802440c10780d4a0b110143c02041303450621600749a00c3c00d03244000048018044400701030421a0344510300245030b4003500030842403031500b0182c178 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 499865143 1250 499863893 499863901
    0xd0b0f0402032410270507020a0f140d050304030207091e050a200f09040c20060103122a081c0504050d0810060813230f0c10180905 58
    0x1c078685081381c2031803500030a043c0100b030440c0035004404081301e0040c01d0000340512580c10300090700c0000d00c88411441a09199008500d0882021400b140070f01c01d541c0c00740010703100b01c0341004050f1030b400c020b0040070414480065800502c1d201142e10440300003550882ca00c1414100d40c650907505c0c2400350a00080c00141840c50f4032121005600300e00c0394501c0c3e4001d8102000303500408640400100d414881c0c1d40060406400c4005100c42501e0040d156007400211007007000c0d5103189190039a0b00c84001401080551000480c401c21a410855629007a00040f0200292000c0c00c000c0d040040083e05002c101044040e0390260360005803014003a40c440700110000c03c0d040304c2c1a81c0c107105010000314010302601c0014010f00003030f4000c0c40c440d410040c00b0b90b41c158020741384c07a24103400f420004010500c04039424904d41d18903d07001d9804501540002e10b0000912440b1040c0d81101040003e1030382c1f1464a10306142090800340f01c0184071031548810500c00c1d85c800c9104a040030108 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 499866393 1250 499865143 499865203
    0x9060c031209061003060e0703050102040b04030b060901051005180a080c011e0509150f042705072309030604030c1202210c030d060e0603010b0d0b0f040203 69
    0x40c1c0084541d800c0c409800c0d680d40d5040765922031040d64201c402070030010060002c50401d8200d4a803003c602c0d400c59400943c0c9544590890780302e40d02030030a46e1408103040c0300700002c5040b0540c01c82c0b8100c60420f45035040100084807038125041c00c4044c002c00050210413074801c0d022034149200d00500e1484525929000755403549420460396000442d11004540c0c0351403014a41d0480320025500c41d41010381b4132040c002c40341030040441c040003a044c460005003500c010300900c0580310038092104e44460991010b402000240204a4810b0400c0108181d156110300c01c1d8260b8070b40c84018041d00e036480031910910b07104084080340c00d4028801040241500170009600f1280315651840c199218028100d8503042207181d80c2c0803088141036958403240303101024142c405940c034180c0e86885207030642c0d2400c498040d41301072030210201d020498245000e1003206882d940c152032400c40410190365005070b4841c001c10706402052860007050079903c003049104000c10050502c05a900c81d42205 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 499867643 1250 499866393 499866397
    0x1f080708010f15060f0c0c14130218040c0c020301020301080102071106070506070507060e010c0f110f03070b04050c03060f0a150b07230d110708161a09060c03 70
    0x180c0080e039030030515056070b000214858500f0404102c4200200c840c20042c04448003004003007180d0801c4084811000441c0310800c11800802240040d10140c03c0c01c802404402a6642500d4076018414040b030b08000301c400c21070450205c811900095041954030094034003100e8103201940540c40400007086400b01580248040b0380502e01001c001c0400d07800300001c621032000c0c0104150048000b00d04080d008802a0000754809c000220303406003003001081c00c450305d10000f080040e5040b202510801d400c1181150031207150809460480c8048518030703a81d209000303009101150540010b01400700510800700490030040545404d4204004044d80f00744094651444880c90003a52440104101c801e000c11102c00203041420a82161038070103624190100d01c500c2c0c4101e81d444908039182c244110072a411032074451140241e680700c500c505e05007d5801940055205c1d16404024440e903000000c100d400b0f00220b0900f68810f0792081c0d0030380c01107064640e04181d020801000303141000c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 499868893 1250 499867643 499867649
    0x20c100f140f160228020f0a150c051c030c090602012304020d020301060f0e161202070c031221060e010314150f150d020f060703030605060c1f05010311091f0807 71
    0x100a012403880f0010000500d148c1d2084c0711211100d29101f4840900030740075819214012410b0300d9048110040010201c0192003010380003c0e40c0b000030903103a40c2c0001c12400030304110310081003485840881041503002c80009410b403144000002011562111420041c0c04e41c080c0003484072030b540d142e1650a4070f2140c010300d402d24007250005412401100411040c00c5400e076600c0f000d10302403001010081d4890041a41d5012031008040081451303500c205036603141380d2ba10300a81100e09402410060000c01406001c1c03401c0407020000f105045078901c0c15240c0002080b00414010f000c0f00345041444c904c25000810300d0010001c0c0003c076958658801c0040b040c4040960030400c0401c0000005480b0003517114202d0700d00c1060f10b04148000c0d1039034900c01d04000814036141c2c0c0001d00950040c9411621540c059a036070703090444031284c1c607480c5503e00001400385504556a050020f00a02e1456010b07000103400128920141084526840080c5c2020b4031080c0d115200c40380c9460040c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 499870143 1250 499868893 499868899
    0x30503040b0301080d030b03030d09080d09051b091005061b010c120c030b011d04151e120519060212190b0102070b0d0b0301020c100f140f16022802 65
    0x2c5010141d05d0300900654054800c020055446c19810304010070080184a1056484007000e019034100641248520b00019000d00c005051000102c05010340106d01d01c200b2a0283c3e07022814400c1e11a039549201c41130f200700b00c8070b641e254040001400899400100c2ca44507941c20481040205504902c01d41f00303c690040c0140410902c000d0250b003603030403104511f40000c111840803c801c050314401003c81c080014404a000e001a240d04c003503014054100e401300181000d00e1460001d101c0303050030002d1142c80406041d400b06070312510346072400300c1c0c81c2c107001c06102056101001300d140d0484200c0e92a140c5005c400b8200310700500c04003482c0f0705623600031500c0c001200420758000a91f5200711803100e00000d01e450844484040503001d1119050342641d001d000242000f1014000600c0c2c1005a0000203451000f041100c0d0960f10000317108161200600c1c1802100000590655440a50b442808484495095040b450154022680004004421490324003010000c800514041c021 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 499871393 1250 499870143 499870153
    0xb01180906081009031e05040801150e010f0b030403320c0d02030f0405041a09040f0606050108040308060d210f1d0117100515040e071d0d0c030503040b030108 70
    0x991001001c841c4e104201a012404404c0921040304025114481c1e524003490680d0030199600307011802e4440d10b260700b05514205030014007400002820b2036005100300102103208514000c0704904a10024002404010084e03c0d40030314031041040d5940c044110520901800c2c00e02d921000f140e41201c4009422809229014140c1a1000094649520054103d00d242a10b00800c0000501040d004811400113240441c1002d80e02d46011030301c214050940600180150300d0302a041781c2d40754000c035051060f800c0900000c29030088500b54400c0007170381c081c0c80f000180d0906545903c02090007080044c0102c02405089074064515828564113451f05200d05002180702013121034402021800100240a00404134074082d19890708056a940c0d40c5002c21b455402140c03289d558241980d41c0203d00041c00c01089800740b643c19409038581c074151051003504070b00404e61b0146022854490080726462400740725008a2400c015075004040b02c0e61032341e84480700b07400c0d0b80007445a8441c134050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 499872643 1250 499871393 499871413
    0x607020601050a151103030c0703120c0c0204090609050708010e0f120703300902010806040c120e0124050901050d05061f0306021b0c0d02130b0118090608 68
    0x1031014142ca40060100400a04041c4618110224030440c002005074402c145042070505000660244242d18850f0360381320710038140906034406010321211021700e0304d034030441100d900050b02080305904a4001c610821035060103400f4110543c80036042e030165203c002458070055200d443c800402c803042d940c1c258a6801c0054695030f4040240b008144200710030070000e807044400a60014500d042e00c43c021503200050460030b048104401c0040c1d584400c3c0c4015503070012485507100b002214240289503c1e024000c01208484882d200207545070303180440c0a020a420002000500300205103001c80c000c48016800e00035441468001c04601c0000f10b0b090500905103000a03030048024039081d250321040f00c215801ca49a0140d0014083c400800000c40700c2c0010103040d40106200d1701d110326062656410580340e8001148540c2106c0c20010058582e0318085d501c40c40c00440014440d0721000060b82c0c0c054102078002503441240d0008155080310368008019104207800b11403100d01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 499873893 1250 499872643 499872647
    0x90907060905060a17070809071a1606021c0f0e0303010b0708070606030c0314160f0e0a0902120a050601060f05030f0712150611010c090308030a02040b0711030607 72
    0x165400341200088240000b404142000c00050103c44424a46420070b40c200c4002c040709041e0540350f080c0080c0d0681c043c0030204404002880c0034040c4400e490360036018044011140c0d10890504078110340f0310f1030f8103005016050341903c29100132840140384202c0102d4000e001400101c200007401c0d031910180c41601c080c00001e90b4140c440320400585000984c0c0c0301c048031600701060885442c1c0d100c68002c40043d500300000c50055201700f5a80d034103040da09410504003074a40003600f10591048030100038000b8030790881c100f15088800300300c102d82c031000c40c01005014034a002035003042c2071140d804003890001814038001030180382615416600d0700c0081740c00600a80c20f500014a0030f10105100c0d40c0010000c640000312801c000d900600e401c1001c0003a20b5040190b243d0703602000404024158101c2049072012000d44000c0113501c2d0040700c041e002c50385500001e0034405001c40005c8480e2080e90481e4003030710a0a10203a16004c49280114405e040e48140074042d01590020a1042d8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 499875143 1250 499873893 499873903
    0x70e011a0c011506032a2f060721020a0c2d1104060806040c0e06060f0430020a0e090c0414040c060908060a0506120f010603020909 58
    0x1440d0200d50080e9480d100406041540007401c404000b03550b07a0010a141c84090f07203807040105000d032004a80501107040750017000307101904811900c151840ca416075540c1c81084000d6024070382c4502c407680462a00000542d04001103180c480344200382c18801c201d44c0140302400504907501c00d1082034074440314a01c040e4080c810010000c5410013003041d00044890602c0e05500301c02d00300005071082005038411035004841d50035285d511802c80c0c0c24503207080c28064600508007540003400203041a60f1404c1aa550600c240d1203c0d11404021070a1035503860100c565858035805416115900c4216000c481446000c406109001c2145a4641200001160a0300301e800400c035001d12807601c2d42c001d4041c0c1c0000d00e08882030240224480481d070b034070301c5403014105050b0140d00103454030f442c5c211951007150f0000c40500c00c14a1041151080000d0855071224070342c00007146036100d41c3c001c40c122059841c0d5030801401200440e06d000790341540603104881c0201c0c0c02d003a568941e86441e580320 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 499876393 1250 499875143 499875149
    0x60b031f12060f0b0622060c050615030c090c120a0515040b010e1306030210030e030712020c1201050a270204050618191506090315060305010e0708070e01 68
    0x40050003800d50220310b0079402000b00180352540400e007501100e0001d410703030b030091100b41c0da41d070100314050904100c0140c840010307100350706001c0c00803842500e603250355940080195070224010300044046403802d10070710b00012006000d050140c10320310101e00349a080410010400c0d00c1401c0083d84524481c01014000c80036940500c1d0325039005c100f1b00c40038081201500e8180108288280d0540d01e460084100000507034030001040d03820b42c03040140309100e5104100400d41429088200103201200f200c2d2220b03030048000d54100b103071080c2079042c07030310490f031941d403144062004001450064000b10711a4004490800405040c0c0016280d801c1c000309010f01014045940f200050030f0580c4803e0700207900030100c02048000c01c901c01d83e00c0a00b221070300881002861040c10152460040c840500100070b480840a42010002040c8440c40d1001404081400040440c1006c56074080400f9540100c000c0c00510b00d080141c80d0f8402c0c075486071148601c500f1130009048191048100d040e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 499877643 1250 499876393 499876409
    0x9010f090b06190b0301090605011202120c180402030c072604150207150c12080610080c0903060702070609060203190e0a0806010312090e060a05041e060b031f 70
    0x205490b140280100c1c0c5000f1101e8001884070103801250701003d03900590300902c03980c01d02103034050030040018841804603240e0301071140140481c0760446c0741c0c103684c20f50100311003c82c1c80d01d900c0408102e10365079003411540e44e0000c3c40003080c4950001400000c0c0740d014000c140000c401400c854110051514180c01c422002609000c14040818a002101c1c4a45010310440303419545500808540d00e4490103000d02141c06140b08104000c40c1072102d41100b4020f04000400d803910030082103104208421f102e080000200015141c1c207542800c2c0c9000d4800601103845510340002d0103540d80009000c0d80c400b041090000044040c40041151090900c0c41900010045940002d8502c0401c1c061010b501180052010031300745800c000482c0254042c0700b104904c0e08040001130060300d059002034181801d4541003296544400d026041110800c0d100080c10441004080481240d00107501c0f10b810304200000840380c000001643c06030f00e9002044601020000e04170b00525818411404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 499878893 1250 499877643 499877663
    0x6060e090c0903120f030103031707020c010302070206210a1a182806090612030e0d0303060b0a03091a040302121608120a110f09060c0708030a020609010f09 69
    0x2070720a0140000e460080e0020f011500310120312610f030f160a810001055920420200040051540c8000224903c540000c2680d40504044500a484049444442d4149a0001404011501d99a0880d22171218800b858542d0124145d00600308039410340c0c8142c2034a0521f04000c1c0c03c80d04000c400c800303e11000f440c207102840c8a8841c29421880240501620940000f00342e0604910010b05c00070b540c540000003600b5410460035a0032038105411030044100c17081001c10009410185144072654100e900c150803d0141c9022009001e003600160120ba002180d03a4155a406801070f1008a101d010151160780a001494020301411200600141d209801c400003600d980c500500ea000d10000301e1204803e030039200d00790320342e1040129484007001d220400001e2b40c414850341442c008040341c1c50f4500240d42c1200b10160290004c014402c1c90001003140d1103020400c002c07801011842c0560382c03109840350000c0e440d440120b0b041d8446508150003400068094852254140d51140c0210 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 499880143 1250 499878893 499878901
    0xb0c0a20060d05060303120f010806070e01140c2505031e1e0c0d0f110910090f020405032410060c140f0a080a020f0309090711250906060e09 62
    0x2e020084e084076054042040170f6801241d61480e040c0c4201a21904a00070f03500d400d060500d080f00c000c0450007000303e510840205a07a110036030382203030580d41c4c176020340354400411418103003000b107074041e0320740140040140d1a11130722160303060440d0350890545201c404100c0c004510240b04a42c04607460300007140e900d01c0c2107112074003580b41e803c010307080303801e02d19500e00070800781500c01e2011f03140e0155101d4451708108503000915072208054401a94908050b0045010154540541028a40c540c03582420511617541950000c08004007211441c0c00306070a109516509000c201c07001200e030400044407070b02c0b0000b01c04105d0b0300641e15408049943d4440b1042d80f040203080c2d0540e80a4008140d00f0304808100e1540c81a010300c4020b640d405604002a15203d03c2c12a2188150018450841e0554500360300590151250500d0150001c203044443d042c000191208445841004400351080001400e660705071445d40c04204074282d10b40805036204a1800540c07540510860009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 499881393 1250 499880143 499880167
    0xa0e0102180d05030d06080c041d150c09040f020a0306080a0816060209032406030109050c09061503070905010912050615031903120b120303070311040b0c0a2006 71
    0x7005602d40160103a80c20041d181c141d180994150f03900c9240380364400d66040c2030a2030a0b120740c040c1582d040c0c0c5600040701c100058692105115061504c01d101c2031000075480d1030034071007100e49a40340240100702551841020a009400c84400703000080e20f800750224900320002400c5500316040707550703036041800206012584800031441218496028081141aa102000302110f40c00c0c0711740d8400108c044e00400c3c03841c8102d0040100c3e100341c1c14106c40b0f4001c141c1c040743d0200303506020b0329a000c81e6540c8402095151044005d0845500400000c000820341d01520140c10b4500c07d81c0c1d0aa5400d94500c000c1c40d54800c1d820010381035800c204049140c402a0001c680700e054070140541c0c0340940b0801340450a0070300e03402c081d000b14880d004204c2a01d005840307a45500201124400741902d84510483c0d940d000c0142039401707040e9180103103441d10030302034291130080c01d10714521561140c0c2111501e0b250001a1070442d00003800820010780c801c0c140503a880c2d03d0101a0045050011080007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 499882643 1250 499881393 499881409
    0x29041a0103050a11190b03060906011b060e0307231c270e01090204090f02031012111f110706140a0e060a0c0b0c0306010e040c260a0e010218 62
    0x4603a44c4960200c0301e607620388410406079130041030700d10511612442c00b1024489c0780040141000d040100b84da80b8007590402016460802d00c0e001040000c60030b107440150742c43c2d4816500c025240d00f4502e9249038020406140020310341000c2d0342981d0081e103800080c1d00c0e001d0510103040c0b000c221404010088000302040120b91207000c005082103850b03860089230f0320b0880c01e0708000407041e0006401d12400c540c074000e6401c02c0721a104114514900000304942e08510b902a0080901000030740d2418800d07940318330003106400800c0b050821303208030480c010342c45241c604100840c00d0781c42c000c460624046080000c1300c4c110380320a40d55501c00c4581e40250303400b02d01200d050086134449841e03e0b44500c409400782c800180c64031045c04496007000944104014555402010100300b0414240d0b40103469a07141a82030b140450309100000e02030782c0b40c80b101c1c5404100c03521445043c03110002602000c1d80503414000040201080d014034048c00d034414611202c5400705902021203903401c200304 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 499883893 1250 499882643 499882673
    0xc031b0f030a0c020d0f05010e190b1308040e07090e0601080405120c120412030e1f0302070f060f09030306050a0302090f09070b13090b100804020d29041a0103050a 72
    0x18801000d02d590f03440314a480c6c00300310141c0da00d83d5520300c3c255240504200b03030307910304031001c16002c0c2c150280d5480c80717071598009010800d0001005001010030914206680c050070341416880c0307040c45c01c01c0c030052050181c0c2c4107400308101c8600106145500510303000f0f002d590003c010b03103000c0c5013034914075a0a5002000c84030892240000b150806c80611020304040c0c8200406002c2414050800034000b91003441c40ca407164503880680c0c40303041030103400e1840f04021404e0243c0c813000d5609251200c283c00107406400d0509003120f690011080754004125540b05c0c0c0c90030015680c40300c060003600803c500009400070160008102c200c003040d14541d511030440d40841e8010303515541058850341010880300c80300c103100603040c80003c03214011142c105e44155581c6100302e0351188020110100604040e020742c00114074074090000c81a4503a10030a5400302d91123803100d08200c541d0301c40e8005c40e8142c03125640c124109020810554040341242d401100410105405444040341c08964034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 499885143 1250 499883893 499883899
    0x402010509030a0f050706030c23040b030103110112050601020a02130b0d1a0a0513141203010b18040c020a120201180c060f0c05030d020c120c031b0f030a0c02 70
    0x200c101da00c80e40d410071142248030b104003120621240c1d40c3c9022840c048a6800450516007006041c00d0141d622a2101c607071203014407141c0c5114103000503000c4a0b031045400001c641400000007000740f1010f05900301c402d040aa0310150100403040c0b08000b201c006071070036030060304103444040140c0341171103084403130108a401c0015020568400618182d02100e01207480041c840b40e0604030044000c40141e000080340710501840c81c1041c030b84214a044030100030489000c4c044400e031003803010024000281e14400e03e8568a503120041c8011310782044d441800281541c24081089003401c2c041c0112031140341e0010b02c0c1891140da5540380b2170603090044d40866607142c10f5a0400c54951032000c80550140e540340003950300b040301c018203c80c8000c2d000410300044013410000034100008442131800040342c016198a005040e45e414200c0f44c01d0030040000012640d103480c00d01c00f100070484a080c240c4006001482030010b00c0d00c6000c1259444ca16400c240001010b150084800018041c801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 499886393 1250 499885143 499885147
    0x80c0316120201111606110d1b0f12030b030d03060503030406050c03130e060108130b0c0c0106050301020c0106090b24090f0301020c06090d090f0b16020a03083f04020105 75
    0x242c2d00852910480354204499110400000c01119800405140318220040050580b402301d003400501520010102c203040801c002e01120140160500703511541640400700c0c40d4042c0e1003440c024040c0c407072034852034801d014074903a83c0c1189010348218400c41c1c41c05000740d400d143c41e0800998182d00031030003003a2180800c10a854004d14148c9100d0040e01c0040c02c0d0034400d051210004021100c010000b010380686044400d0100305011000c03580041070180c82965142200e810601520381c0d50b02c50394040d03001054aa60010341904404184c0d600c00104000c9005001c007040001c200010040728419511034540c001c0181c85002000c203048003034031a510b00340c490004a400ca80c03003030303a0300500307904564188684400d082c403a649001c0141c1c07a05007a20381c18400080c200d100203104101c4410800a00c8410945524034540c41241d001400c0700c19560396810701e248103500440e1005507000705a5041c8085980103a94118200140540c460666100b1944451a038034094403ea0602c801 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 499887643 1250 499886393 499886417
    0x703090510020d0609020a120f0e070e01170d0918020f07060212061516020406081911010f0906030203070c150e2b0c03050c070e01080c0316120201 65
    0x100300030310784814584040c0180c0d61400810010100c56482e084120780500400c52240d00c2c2d50b10094020049100305030010780110300c4200e20009016007400b802c01030040110000b640c150840c000f9040b80c1781e28180d2584a41031041c080c0c0c4814120b00c21701c01143c010341060040b14111610303442c00490348000186005070a46c0c00e2001900650f504a6146800140038210703440404250bd03000071040e119400780c5400b191600b60707140520f43e82251242c01c008455829951280c000f5001800a1000da800c01c3e4046107098075410ba254006075100d0020225009855125468100c7ca00784a030303680d00b803141e041c10390031006948094584010414508400404201106031a50440071520701c00107403070301c440a0b0b041c140342103900b0004100e2080000e040d00c203115142c3c3c0c00f9414105241c4092155103a1605451a010743d10b081c0307600344200d240c00300380040034052450598043c042264a010b403003000300359540d40048464170020950f200704109590304040315915803881418100780c9400c0b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 499888893 1250 499887643 499887653
    0x328030e10020a110106050102061f0e010b071208010302060912030903070807050a1a0702040507140313060b03031903020a0e1206150108040f02010f1704030306140303130509070309 80
    0xc001c02054041590014090b04a1900040d015010241c03900c024442a45020300203511250007d04681c01c4c1c1d0f6030b81c8081c0d28204c81d1814a1406272080e9403a05500f56110b04141410b0b4000207001c59044403820b00ea02131140c024140e4a049940c0104960720303024031202400315510408003810b503503100510000301c883d9402d0104101074a10030004080d450b243c44200711140c112a8403500102c00f6030009201104152022207248640650f004030b59511090340440c1c507421014130b550680503010041c0100441c40c80f012100b00d600030308050141c010000d02b01900c80c0718149000100ca1902440c2e15441d5000e500030b040c2031080d0341410341e40302e001c080c08585400c5122483c0d0300305401c42410000100101a102a180c42e000c0c0b80210311881c0a0756070803240036400704080d0503c519026070002e0103201d81040f507400c03c001c00c1d2039245030800d441d000e00940301d10b0240c003004c00701001114540d0704001040da01c40315a8040706022440c42c00091100041010301110105038840f640c0c000811 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 499890143 1250 499888893 499888903
    0x10311011d0d150609141b040806040f060f0509060402010e0312040b0301091803091a04030611120106030c170c0c030301032d08120612010c200328030e 67
    0x140078a00301060b00502d420b10f10102c54554020051907807811000054400481050301c0d070040d000c1e074980503019a203038407074640b50181d07501c5004603100c2c850400040090015240009070b11640d814005411540d0026080e90811038200d4070302c1c0e02240c00100035621070000c01011100c0981603078070303400d0480c2c0d403140f140e03001e500482422a00080104078000080c440c000d9030084c00e404e28016440280d6004001c400c03a4420041e0b4608140015805801c81400700d40c02141c1c0040c0c20401c44100303800003d8190000031001010800d29000065000e001b4007441951500755030f90070000e2580440ea4003c072a03030262203410580024840512506000c01c011400b0b50300400702507424901080c0c28034a030300711049074284006068041e1030002080350f015540ac0e0241c110007010b085c2d440f2804100303031400916031044250309000c540305a254001c1d8800000300c071400216035000d13103ca140c580d507030300c100400008450020714072022100c614404100640c205490081110101030100d1882c1c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 499891393 1250 499890143 499890169
    0xb180a09020d0c020c121504080919030b0f0f0a02070606080303100f14092202030a140c0603010803040509090f010204080c0109080a151a0a0306020307031103010311011d 75
    0xb40d583d0242e08240540401041841c081c0845807400d0b5403507155981502c07810380f10050480a04900301203410015a1400d4582020000c0c0c2400120440711041426030f42803440262079079031101020806c50380154044500c1039011900c0c06200e6100c00700c1c60323002540003800c01d558003540c603200403e1400d02480254010801c0b078040d80a445e0408031843c1011401d607100800c00d429008109181d92110015190300c40800c0b030020310791004200d2480d83e903141507400250315000d117148007010401c4d0701041d11701340c0400504a484a54086042c003440d1700c0203019010043e07200340420411807511022160b440380303038401910070310030703940b07203940c4c2a40c01a80181c0c049810072440203400f5688100500e0003405010014a01c001d0503403514510200f03d0003044a460713445900c408010490311001c003260310805010041200d80c0c0b414148000c0d0016205480040c0c244001d00c0300218404050364141da81011584034000350038001550f561568002d07d51150203021003140341561000c0c100401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 499892643 1250 499891393 499891417
    0x509060c060a02281b02210d03060501020c0622030b010e01060f0c120c030203040510090e01171c0c0b01090209011101061a13030c0803070c0f0b180a0902 68
    0x458042034646404256048500f134010745502080f962000e41c400700c1c1082100c1c4c0950b801e10885000e002040c038075452162010140c10115003251170800e80000d40060602c0240d9041244a85500c012070b1580e20464400380e02c24000c0c0002083c0030052140501200360130440c030030b64a5070704e98400140d80001d9125210400000c80100071140e00008400313400c0d81c052038034050040155076802100308406242c0c2c4100a00712a10400305030080084601400d2f0042c650811101081e40052243c00d00c5d0040d8010411400c0000030603100c1c442c1c44c07000c404c0c00040940044240110007510306400100210104030060a0100100c0c440198150180072005c0d03000d6540c2c1c03502000503150701e54916404e12560701d40b46080011103200045145400c0fa440e82880c0c1d144050f02420113540302035040680f1418241c000040e5140340080140107252160700c4452002e5901c070700c4041404004d100300911100e040040200c08070004c0f00c48081c00c04010b02d4102c040303841e80c030100200c1c0c0001c3c0010714 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 499893893 1250 499892643 499892647
    0xf0601031401060f05150c0106080102180f18011a0910030207020423010501120f051e090a1703060d120305070e0d17070206041706061f0206070509060c060a02 70
    0x14007000a0043c14003a20891021444040c508000b02d00a03d02080401405007008140f95011520030f4005900400d9804000e6407207000c0c2261044181c04c00d024190322a43c50700705070b0002403c00c5d82044481000d902c0c400700150b84bc1c240700c81440382c950358007503095100c200f00c0d001c0b00d6540c0c009a148400d480e0f075030058032240f20b8418442168944404090015040390381d40e0003c80040305924151042840e240d90000040d5020b00301406115100011450400d0100300000c010745681238141a00e4203e01c04180e00c81d00403140e12007020f0b08014200340c4c802854030700c0e410803c0c801103402c900042c00c0444c2d070b07800c9501c0f200301c2840d0481180700020748440901a41d280c1c0020503c003040c4044482c003020580c2d0b69150709020510061112034020003250010075581d03014141ea00620303030901581b800368200d0b4480358440008441d454030640a0341c100c2c9061040e082403102c260700c4290000d00241e11411020788117600213690883e0300034410420804006010300c901401032580820244e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 499895143 1250 499893893 499893923
    0xa0b0a0e010620060411040c0903021804062d1d03033904030b040206041707050102060a0515130204080d05030109060806060a09050415060b030f061017090f060103 72
    0x80d9a5400f6900890075a01c25428000400c1554018aa546108480010b1044180c140981d0003101942c0080c2d0700206540300204180003050f4120b00c160320802d410400013410700c072107001c015203d0b080410200c0e0400080e084141040e441340580704c5103048880842d01c0c883c00d80c0341c9940e01c1103464102c002c00d00c0b0b42c0c1041c0d44844903443c0070000316100d6203044a180c00e0240d20014021132001a0502958101060942d1071300d10444028050f50608010b0032242900e85554482c03161181500520803540000c00c62041c522569000702102e800d61b40002803c4020401d01c41620003850314010f07400c100015684a0401240d00c00719515210181c403076242000728000c480050740303c1034064101104001c1785585078400300041d05c81c42d500010712900d8a042003020340841007203101120b883c069020580d6021600034520030b0606e80742c140c0e01503441d80300b0b000f0b0301c06a8441e02004550fa5048011850b00044c2d1810703400080c0500f19051041072401da41d241c180203a005461411000b2805 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 499896393 1250 499895143 499895177
    0x30212090307020f060f0a03181406011a030411010f17130221030f070807021822030801050d0f0507030b0910021602010e0301090c090f1808030a0b0a0e0106 69
    0x10b0421041202c1440c00c6c10703001c080300740c101c1c81080450404c050b941c650034908409000c41d080c080b10f400c154455081c004100e00076070b40310390a0040d50001c41c1020380100d080035084088921072640842d0034003000100d48015107144c65240210340600c11403030600004a4010141e01d80300300900e8907070010003801c600600c1401c1032150146812858100032200945000000b212120b81043e144160b13161418206401c441c0500b0800940c0b102c0202a41100d44404007106030081015022003d014100d280d0400c400300c98003a001004190460b00411a5140107901703071610502070000742500749602d9031600c2c00c103a0f07150401c0710030800c40e03000d010403010108500c0440c403c0c0c60101310324003962034102c0c40e811041070310024104550300042d81d4590318203400c08008207a02404420000c0d840304560b03000ba28261800707841c81d0786000e020031544484054001c1295030023581c21449c5440d0451182c0140811420054202c04440c10004800c590301c0c5080e4020701d605d80c0c03542d2510f0125140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 499897643 1250 499896393 499896409
    0xf0d020712150e06062b0209061c060501180b0f040b010504091103090111040806060910090509100b040c0c0b0408070206040803070b0a06060e091803041e1a030a0c03021209030702 79
    0x4074034030320340c5410142c04506d083c28480d4050660116116000e0ba60340b07400145103030300d1501c28121002c147c690380d58200407498022238160781102d10703080885410b6500751000c44c0c011468803030707111001c100012258200341d0701202160070185001440d2586030070250040d12180059218120400402c20120395028800c0d2801840b01d040c0303103468585049040c03a0f41e008040e020920a1a601011072039011207100b0714002005408005e002c0c82c070b410820301d42ca40b080010f030300080c0c3e406c0032242d401030301e8640301d4000c0c10403190301c42409030b41240d1520461004000c1c0300302c0b92000704204140c00341e9285000ba2000b00184002035586819500e80b4241140c0d026003204801c1342400310500030117801442c1c10349040401d59035201240c0d1050200f200c40007104c441e100c2030b4080041c020030b6204142c16030255001d0110400380955540d0380f44c41e11840e4142000000359075080c0301048042c0016009503904043d545005802c2945c0c406004c00c0703000c815079020000d03a200042640860074032001c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 499898893 1250 499897643 499897669
    0x11030a0f02030903030721140906060114040909080d021606141302090703060519061404060c030c0614101401020c090a0213150c050f0d020712150e0606 67
    0x310650450802c40d403c180d507804040d03c88024414100002c5411907100c00c0e440b40141426401400740c0c07411500c0c05040510161a09841c031700402c0005109540154a2807029106402100d46810301c2d00c202e403c0240305810b8115200c01080011070100204c50015004c400081c0780040070490706440d020b021074008040700c0e501000e1180420401603210882209025016191000795603201e0030100c00400060b0011503120070100030401c2c580302c2005007102a5a0340d40c4034041d01102082c800c0940340280c1c810440041c1c000c0c01d20000003407258086042c400c1c0319400200d6403004500e030584140d503003243c48004c0e4550b4103038104440601c0604100c0c0320f9000b80050403190841001040b0b49500c02400c070440303960006000c1211840c12041d00006010142008100d0141d405004090032801c035802d642c144140300508038009000300c0e4124040c1000c0e0001c00b002481c060f03408414469080003518400d0b054111342e1141010750140040a83c1d6000140070b031860b09400f00720030459011 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 499900143 1250 499898893 499898921
    0x901060c020303030408220b0301150914060a050d020d050a0f05090c06090a0306060e0f010f060203093106150f050d0f02070210050a020d0e010c060c030204050411030a 74
    0x200c024400368034044201c3e908160003004156807281c841480c0f0403c158408000795800f1040f2400113800625180a1410b07038141070b840c6080204031502c200e440c0e007002d015449842441700f80c84d801525090001700701c40142400c1060810060101c031f001244c01c0280203242140e20ba500f0846070f03c00c036114440010840b11030420040c108920341b580d41d100000c203000c1c001c1800040304c0c003290b40c4101010f4010340c0d0104050002075240d101c1c8042094042d02c2c0000803aa17a8400031508900d590a1401541c2c3c0c0c50b80110f080034070b1001081340c000d000428101501d080802c0c07952a402e64500710016001048130b0208486207492092684904801160010018080001a4290fa00104860520b9000703070010805c1b0301820480b5000b8800c50f400250300c14207601e10303211303419040005086401d2042e0241c4004d2200b645007542c040307498111050000704004912400160381d54880c5058014502c1e0050900e0307103e1001c0313003c84814080f004090721010040140d0171000f401503651880c000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 499901393 1250 499900143 499900157
    0x14070605040c0f0303021b0105040801060f0906080708190224070213060b0703030b030709090b10060302160605090f06091f0603050a0b04080f04030b0a0b010c03320705010506090106 80
    0x54500a4a401d00d042102c1c0010b1f00c0c1081c038030a079030322a0054070090041754000b0080c01c0c4d507a40c0104403260152181310b251506054000404400100703d1800b00c83d4110080c01d400000d0740b200261401070400100c0c0e104172403441c5000602064000304013803181c41c5000c903a4400b940c0c0104980060f0100303175590b101d8103015090100801d0001070715501d41c0e241c1808102c031a8a440002d082800c5d607040f0080aa15049013030703052215500e10940142c8a80c1e20840c62252654800c406903c100c003494202c01607100039042c006081c950056500c4080541a1410010101001c80c1002e50540b041d42e02c0380d001d042588131146551103841c2ca4006c01e0101001524590b41d610f9884141100c4040c107250641800a41844041c50843d0081c061041b446a5280e0b201c2c07602d0403408800b1384045643c0e80c94030a108885501441c2c40105c015010303116411038048c4205011084801e41d1040b0b80c3d1611003244a8207a4450b409c0544141d501c0b541c00400c1510300101804a803180581c8840104044 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 499902643 1250 499901393 499901399
    0x3050301140a060e0d05030c060c030105132702060d1e06080c03190314030c120a0b0d061805160503010b180c0a0e061b071403190314070605040c0f 65
    0x740b00c100600c03034151031045c0c2d50f01050801c903066002e0301032580399a001b004200f01c2a0b0003076030000d42c180c0b80100c0d15100c01420280082c0120f500c1401401c0b1080c49888102c201d0f84134050f44984003500c02000310340351014000342541501e07010075048c10314494605154001681d0b40c001c4c9005418004010316901803d0000240e0740c15000303a202441e1860000084141441010b615080e03100078514540e0340e04101c103111100c1c1e80040b9001c403002052801044149072203000e0740e01d4a650041842c500340d001074a0300401042685500705507191000381030341c00240140081399600c6094041550814604002d05081d20725070740c8840e22610403000341000f00c40e0950440d0f90040f506007100c0c0d0b1600d80c038203001c0d100203112007503041e40141c0203c1c90390700982c0000d0981202411800545070855590303100c50848464050629a0642010480c000380c29018140c522219000e85081071160b4078040e000c021a6024601c1540c07180c0d2900308100c18040c0740603488000b0408040710b00d10040c9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 499903893 1250 499902643 499902647
    0x10080a0f0204020904091e05070f061d0604080a060207060507080118200318010f0606051804060306050f040308010b0906070b1503060106051803010209030706051c0903050301140a06 80
    0x800d604024415940414480c00c203440d10351290f282030358407440981d2000341c0d104a564283c80016030440303291040341c0d03000c1814800c1c802a0b81c103c4407036448002c45408505d07840545441601d03130040d000b41081c4400240644100407407040340d40222001a510809424a0380980703800802c140c09200e03d80707004100106441084c40103544403200c00084001c045462981103420300805c07480c000c41c000c410b0200d1404100c1081241201c5a0300812041000d12100001e540e03241c41400c0103d034080c08009580c000002c51101610b41c0207000050b6a5142c0d0b0311141228029a01010a092a00204001c01d500141340c5409484401e81c0c030b500b4811102c0c0018924816040c004199031400030119011100080009448120043c2512029a100c200060250f04a40b01c11100000c1f44601c8141d242018400c0b03540520010380a08105814540e098031386502c104038007040c2d010020301070a011403052140040381446652010f55079450319081c07180c42c03c443c5202c280309800c000e2080040d55 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 499905143 1250 499903893 499903913
    0xf0305010e15012c070807030b0f240d0c0905011b0b060409020d0f12020705090c0417030720040b120604031b0b0406090327181d0610080a 61
    0x384822003e0541c400314200d540035800390550340641044601c805c2c0010140c012a0b1070b48180c2260707400300300034030040d4100304034000603081103504044150b04400041c00040255561007a581d1040c0d03207400b0108684008031910516140f001403080d04040c4074543e801030440741c842e00040440f0903520f107943c803188003201010b840180328940d00c40c0001c1c01c640b41e4403200e951054101d4808080030700e080c10300881160102030203030014064901c0204841c40d01e80402c43c055202c600703119003460700344124a40724001d0040c0c249118030040c004500000e00542078803126815410503518691080740c20f10003502c00429406100b019000780141c013000001440d1a40160036103070010080210440d02a18540c0002000e42090180f600b00b0060110b40d401940031648650789003100c0e01c07115080f0032080300f20254040c91102003a41c08218500307040d02c019541e92003402002956106440280e04000c890030039004468010030100103900100c1c000d03810041035620003400c1c0d0150301d40c0d074207007003e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 499906393 1250 499905143 499905149
    0x71505041a0d090501021309062306030a062106060605190e01180905010f120b1b09090a1a0105130902031305010c05042301090e0403180f0305010e1501 67
    0x301c010036000c0880080e03030006003900740c01100840d07940c0030054200010b0103282c011010380c1d0781400000605041005280311642c078501c4206035030341c552041040f5807940003a02c054031554076810046100b51001d624141c03080046040300d4400b02e02031802d04180c41c01d541c1310344144081800085041c100d4407a0b68940c0035900c1c5403003480c80901d0801a1000424641c1200b919044500c0c08207000e051035108c01e050320400305200e10007a5580b5081000d1541041c001068245104045100c5214032580100040c0000b2100c41c1890300d9540450860f143c2214040200741e1241410035000213140c546114091082c40c005180c8000d50301401c0c1c04800500c00c1078030302c90380000010340c285000b0008804107640000207001224228000031703c1a0401e000e00d00f861303415003041c8035080d201d00080c03c20308001a151841820310b070066880ca44d4034014001d501b4043c2c462000c0503081c180d006990050140d88008009403419402c107282103400e035140d4500664024505140c1d000c840c9085d10f411 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 499907643 1250 499906393 499906439
    0xe0906130c1205011104080a050c03160b0d140708060117011a0f04540b0f10020d171e040c030501020c01020702011409010903080d021b07150504 64
    0x100842483c1ca180100980701032030742e107084045400f00380080003003a0b85007014051000c03548031941c0e1504050325004403a184030b2042c1c5a81c00b00300181010312020380f140010010000902411007592401440c400311041c000107440c00003040310070368205281c81c80c8010900c0820096604004c5140c0f2000801ca0750350181520101303408640405010482d4041c0c000b0900c080000641003812850016608400ca041641c0c41c038110504120710254011804100b00314003111840041c8044000f058030390102504007d000b842e110598072604200c0c585c030101640100080e103612200140207003c007548a4000e2182801480000c03c10b9030003400d11140800751a04003510f07a0714190003840c003580d0005046500110380c515048030198040c00c40103000f80c846170259201846501c603036110b0340c9082408200064410310100350444081c00300d0764040e402c0189040003070190842c95024402003400d155102690920441d0b8203113a5991900c403003410801d01f080e003802840a490742841e045c0c030103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 499908893 1250 499907643 499907669
    0x60a0f05071b0615350a0309032607110406060f12230f010501031503020102100f1104081e03090913030210020c030d141614130e0906130c 61
    0x1154440310310b454001400700c0d81e001902503106001008600b050000864181788142c1003640c1d800c00042881c003800395041e40c038040300500f1036460100d0000c0100d513105496850403946100d1484c032a0080a03028000e00b1001c140320002c208200540c2d1040c2c0001080000c40001c0800c0250404036000035240184004200403c1c0321a0f032000c030f041e8076118200d90945a01c180040c0d1103520030018141e650130baa0600600040d5429104c1d08079891000a00680c01050401140705182c1d01050000c007100c800481c2c0100314151614031904250882c1009030044203640f80c0c0c0c000b440030b10714644885100a14101240c0c800042d0040600801c1209404003074615074040520274000010b85145040085450308900a04c9640e60b402c60041c24540074a80400c0700f018980d5804502d00c50000c00f50725090f10003003040c00712a00714491840c3c07030f002c0074103000300440d11545080300303c00360544240e4aa498035203810340c00d1404101034002c6062907450018440882c000140d1075060707402501100c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 499910143 1250 499908893 499908911
    0x10f0b0f060711040207140c031f1e0606120b0a050d030c05010e03030a06060e03060411010f0e090c120c181011060c040f090e0601060c080c060a0f05071b06 69
    0xc103c0e515115503441480041c40c1e004200641c4490354400000404541d01c1480020506681c0c003000340035241e010003c0031400c029042941c0098002c503c410000c5031001c21455554001d0310400c1e0090f41c00b00390000f00840301444c0b14814403207214011621240141d242c80041054240901c6000e8100540d0b9040c0e0018440250402480b4080e40411aa40d901c0c1000d5044010b02081c00f40e0b00c0019110710004009160008a16003d60b40101000004504e9031005503a000352680c10a010300100403500f2a85503030f008c00a921030000d00c030b841c83c0d482c0c0e02808041c00035940289030311309101c8144540c286024040700102c00850003a030750b80d900c40341510400d9620200360380b1091880e214480400c06241003410144c0100c85499000d256800d0312080302c641512510261980f559001c44010010284900c200c2c0d25420300904034203140c0229181060700b4a1800c45c0c101207155101c3e4201e0444403007034811035038040741d24038009041e11281c0a51805840c16040c0280066132100018 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 499911393 1250 499910143 499910153
    0x10b04050c0703140417061b03040201270306020301030b0a110a0804120306030807050d0e03010605010215060109170303010503070e0603191b1e0806010f15020c04020d020903010f0b0f0607 83
    0x198060300c91885052546c2d40b19150035030740c407001120801302c50f02007004160710402811040d01c2c000c6034142c40d50900c1440842c61404287d2855280038242c4400700d00c00804522140700641c0654000c1d410303405940f0b0259030403029182c40d0007214403a03410400c0b040c4d0a45904c103d4064000d07510400e40043d240c034407d0304030080c00040c0c0001d0a910300000300c040400c60700151050041c207407500c65030114203901040500302e64061040078003507003008840410810164284a500c854141401d1040a44a184030b0746110701500d01c1034020340c0f0000050100b4130702003001200030b010f502d844080c6403500c000070a4a5204900580d0f00c048001507181d0104249001c0030051075811865120081e684c841c0352007000c6000e010400c08a40880b072001ca02c100003c14454107030740c40c1c0094060b08900c0c1040e01380d01c9403a262a8901107001c0c1c180c10030125904c90005211024500ca405a180c40b1100109400c4074a40013501c0c1c01d885c0b41c161917015540350450031010506045071890b0b01d0312024148 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 499912643 1250 499911393 499911397
    0x806090601050a1a190e010807050310030b04210819050c1215090a020a030b03030f07030804050309040c05040510020f1b01031e0915020315060c0f070303050c010b04050c070314 78
    0x200d51040176105440d640c00ba5215007172035440e001c04d99030550180ca5141c0140c0340c610050395510484001c86e0f10500228242c00380b0310b0341080c0f14072880d4044407090403041a1a007400c61900000801440c1442008a40c50122658503c001035080005d0b00380b08010b101e561040e103000240702c114010002d010300b8003205000358100d001808010042c07400b414640e00940c04031a2010129140c1003484035242000001c0d02e5108a842920780e250850907201514401230041c801c441c20300c4100800740060701c550180b901d080710241c4034251180c0c14101041f4640f50309411060841d40030554400c2c100b03500061003c2d080c100c825007540950800030040700a4004d0221031480f00c041c0e8183c007007200c0381640c0242c0c0b581c0d000d0800071040ba00302c42c020609030b03c0b060300d100f0007114008610103018640380d0028102d4030700b00c1d030403201046e050789103450800b5501ea10a13030100e100410150310265080c0500b1055580480e01041726282c02842e001c0b0600407080c0150030001d0420150703002c4040c1c182 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 499913893 1250 499912643 499912657
    0x6080402011205010803090301110f0702150409021612020c10180e090f0d08040302060c130503010f0c0906090807120c080f24070503060f0f12070806090601050a1a 72
    0x1400c3c8150740e1a03030034030350b40c07648403030002030296103011581d500300329108083d038003440c040006c0b8030f1030710205400300002c1d001091802052101c0800000402020510041464011400004250503d18103040740c0c0d0980c910450800e54021030f020010340c7d40d03841d21210482d00641011100150704006800039203200b6005061001030f0b107010302003840030000c3c0740010800242c0488072681c110040458030107005840c0200540d010744042a00024403c01804114003074842c0015140d03601c2c0002402e40380f030170041c4540c0a036030307031164010369a00c0030304200500000c0c107144251525004c140d55445286201e51088101031018442c100500d003500000102040b10498800034000e08055450b040b0510300100c5410003070501d200d80b40f2461020f40d108002545805085999a00c01c0c4034600001c2d405081c3d05c041c0340040140c10b03a0303691404000141244000b0329550b81046586441c042d00648241c0141d40032600402c182d0340c0b940c4101c3c0030b603000d0b003007445101c5032500d9138100c0c0303402080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 499915143 1250 499913893 499913927
    0x306040905120a0305220c23090a050711060601020d120b0d1208070306050f1306350604170c0f07180c0806030c0d0f0204090b0105010807050901090608040201 70
    0x4007074441c0f69060b0041401084a540b11519036210b1101c03148808405000040850810b0796041080042c080d0017851402c2120400c50165030341d10001441034002120500c0030140e607070701444401640500704020410711000109060700f001c43c0003035a2461500c04542c10400141034031143c80119400100720a00080e0a0b403090402c6880c260000140c43c04c54100000c02d824005049030344a03014800481d10090114012000c0c030805101814149500e03a000343c42d155003000a400355000724280344031561a156881000401e054820303400e240304000801a4426800d10000c62002001e9500341c002c2d03025130070b03a104501a0707a039040100e6140c107648107008084c0300080302c00b10302240b01c02d40440301501700300022058074107445440c0180d81c44c030b400d54401c44100055003000114954428090b05c0020600c2000f45c1c001810f480341d22008941081d0300e40010001940c01020031500100903082140c02c20300001c1c0020408040fa20401c410080060302060569005901c110603440d039903 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 499916393 1250 499915143 499915147
    0x50301051309170702090708010311060c01021308010c0f080603030307390b071b0206030702070b030406060f0b03133804110102070f090203180a0b0a0b0402030c030604090512 77
    0x40340310309915404c50300e000d03805407500d80f0009043d01e10880c00c0a06a95000e1074140652000740140900c41d00400c5c0b0340e003810b6508124a2280c42d01da0450f400c01840d014001003071445134030b00000d00510010a081c8140031307000040c40700b00c0c0d50110a5030b521146918051411030600008107484281c00c6070000511051605011504000c11071081403650041c19041d0498441d40030484c1e42d061400900100041562840001442e003180207542040e2248100e40c02a070f1031b10400000da61064508542d050f64400307040001c24144c03807000c002424100d0b80641586419940c1c08200c00041078010155007003004081882440e40d00c20000060361a041c1d40e94801c0f15006140e070034242070718143c40c6035140c1501d00b5070641c800035481059444802501404038a04048800603406c054585800825188640b002c009030030070015640742d000f4080b03108a03090500c0f032501100c00051a181c01a80100200102e5021401c12242c00030000d5030300080301c1001b41003e608000c0350300380b811095800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 499917643 1250 499916393 499916423
    0x1110a090905160203090904031e0c020a09110f0d090b040605061e031f0e0f030d1401030305160201091703092d0111030c010c030615030c050301051309 67
    0x30101115080c0c42046004010907280e02000301483c94440c25080d0050b401000400d0950402a0015400510070b0402011030311442c58150070100342d850300c480005812044220541c50640503400c002c02c0701000030400312200e4150500300b481800500c26411a00003440441415550b00980d0660b0b0001010380e40c80c00c052070460301a207010759080f031103501490042d0340c0b8401940703501380c51250024004c156000756090164407500c1800020000541d44200000b51081c1c01c0c080c48030f40c080c2e150f01031075440082c0c138101400c0310f0300c081115820015080c010310000380c100e02203d0341801007881aa00d207011910040307501000c1d640044900c40c0101e80c0d500303049000000031300300d5203001319000044040c0c01004502c2d00300c1e844401c0084002d400841200650050001203501140d9000b17692502a2140310182510222010300000075550302041003092140c110201305820a460140001204220001e01900060103140d1081041000401c03206e0015030000a107113030300c40319501c98019 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 499918893 1250 499917643 499917647
    0x402090610051c060513050c090d1511031e04050c0103021b01060609150516060b0307120b060f0118031202030c011a280902030c22051306030b0a0c0201110a 69
    0xc4d4910446000b121720b40b0f41440c2c0c44a0601501e8410000010014204412041000340e020b51000d800d480c0d15810b543d5100c0256032500a0303901c030400200035207a41c6d08100441140741013102d103640010743e0b002418030000650100e61441040f40919025031030300b0708c85404660040c600190414950720303250300021529006000c0d4405c841c29421040d0064800038400c1d2002e102c0c1c80d9040700e045078082c00c643c00045a0341d000c400d45940140859003c10b855000c01c0076102070300703401074810550300b2082001078904410f10030000c100038a4040428a01c080340e0880801ca10700009016585c960310900318240300300103451444500e04028070001e00042403d5400c0c1e100081500d010b489140308242c00c29080119254110410b0303281006c016241940640080d0006041d020541108115090b052006003c6546283c42c901290320030b40c901d081c0c00c10021806105030348210300d0030447c081010401a00c001c5030701121f10800450b0304880313040124010b254443e00d400103054049003100d9910703 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 499920143 1250 499918893 499918901
    0x402040908091c0b0108030c0c12030702100801080601050f0306070309170403030c0b0703060f0312050405091509011512180219080c0307050a1401030608060123090402090610051c 79
    0xf0b80948008183c60340c070b6486042e03d07482a462000c1c91540b04149502140c104215602442c1584402340c90500c1c0041c1c0c00903d100d1440c00c600c0d070000e80c070200144040101804954010101101c040303800d4502e50000c01e84840c00144090245603035900400305202c8031080441a80b114404181d549071383741d1801411017060300030b081d0f403807508000000700d03418000d00c112025106c4000d403802c0c500d0f01d15561800d605410074000c2e000c03c8014440000c544e100d517400f882c0250000c1c220389c180410390364180040507034140e1000048e03085070b44a8005d55134200480070340d000100c1d032002c2040030001d540345500b10408000250441002d00c100c0c043d0100c410280c1f01a20108025118004044020540d943c8014020107a0000f0144001c0240b800310300354451032000c042c1000b242e01075546840f581481c1c1c09074461070001c4090318545403242e80034040a00742e80350840da480d04505085d0007180c540c4000400c030381e019240b410082803555000f031007980c00b21070102d41d0043d00018401d4001003d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 499921393 1250 499920143 499920199
    0x5040216150f1a03060402060c03041211040c03270303060302030f0607110a08030f060d02100305070e0108010e010608090f0a03090e07050c0d030b1212040e060607030503040204090809 81
    0x54a4280c4030a69084903c0b014810060000e00801035a00c444c3c0805c4542e601c10720501e0a5403008100010301d019000c41c001c00010300505040c0c01c40892101444260391812801d41d04052401c801d404070503d038420358800c03a224402c4500040005442c00741c0c010b10349a00060750610681032842e401443c002452446103405540380e5001061441401d41c0e5220100070040100405000007181903000c82003040c1d00c080001d000001001582e00414214510030000c000003070b44600400c00c9032500040703040d9000c0f20030710700281a0b40c9820460f450b07054040c050f8200300209400802d100b03c000300702685c028004001035603041d4403685400780180e0024480c0b610000d0701000003400705400ba2042d50140c0428402408010315007040480c000e01c03400990f1903118180641c44914001e081058504c60380b07030b50006690312401c003c818030301c00200402213403050508100c0380340000d9021080e260042d43c150342c00709440c4024070b002038650080307820007908451000007140b8046071395510b00c940 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 499922643 1250 499921393 499921421
    0x20106080a06090c06080f070f032d0e280602090a09050a0f0e060f0702100f140901021603031a120a11030c3114040515040c0504021615 60
    0x1e019030b1810161b03041e01084500e801d039800243d002800c59401041030682c98203ca10740003501c45441049507071080c0c0010680b6580c105590703403200c0c0b80c0c0200d00c195442c0322044401411b0a0070140c045c4000240703980e0000c1e04d40440644440d040100b0358041e5441040001e000d01c40b6540c030b80c106140101412101e000c149400c02018a00ca01c103a8071907040209680d2020308107503500c1c4201340c454803001510800c01c41c441c90401c2d2146030417174460088070210000c0040b504103c000000e22040310047c1001d1070b141d02c10000c5c814142c4030780045058456060802080300c1c0e00f00f07603410200150111031282c06c903903e0b181640c00f00001007050500c0c80c0c0304180255a400f059818036035940c0710075915075040fa4104000100e8182c0c09040720001d1590440681015005160b00c4030940c2e400064075400d081b510014003003044030070301003107200041c0401c40925518040d29880c420742c030584200c0307004a40c00100101e48040d00707030781503120940041040300f4101c0e400383e241c002404503e0303003410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 499923893 1250 499922643 499922663
    0x212011805060d0213020703020a0b07020a030e0604080a0308070e031002070218060307180f0f090b0f0c0307030c020f16060905030307050a11030f01090809010906080601021b01020106080a0609 85
    0x4224504581e44801c0d03aa000b400c2045d00c00004a003000085d4083c4074141e06600c01c1200a10000d03031544207007803088526074060305c0c0c0618185000741140003005141343c42070b0f0341440180440107000a45065494062505482075240c00400380c03036030440300d51202d40500071480b0805000ca0903400501d61980300f61a114110280e66440c3c802c0d1203400e07502030307916400200040101c501c56100c5d0300c5940c0343d02000001c448081e20f07200740442d0041700f00111910348933084074091024440000303a10075001c00c010026454510240b680c06d00c0001c00400902d41d440140c88003a40c42008094550321f040b6040344c00c0f41120608020301d1a0961103141e0029220781d0021480f418003101b034803001c0c0c0e07200d801004e0365011507583c00460103005aa903600b600c01c0b020381c590f4102090180302d050500a15200356508202d00c00140213050710b030046800c0c0300c440d200780025640d0000706203088400322030000000c1072410004038090140307a8090503152103070002c40701c14040d1700e600c0005801c1c07192036101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 499925143 1250 499923893 499923901
    0x409021305041b03111209060603012403200607050f0610050109120f0f030c02090612300c0601140d05060703020c030f07050a0c0509011a0d0212011805 67
    0x80203440c0c412a0142e060000032480c280f00a000790001d003a101d40f80050182021121090169058000c648184e980d41c404010301c84503007000e200e41000180d2100001130505030628900f102c80189100040c14528807401d0710000c004822244021554001d1069540d13134014101a035a81c11203003c000880e010703210100340d200c082c1200c01c60840b101030f10f030b0030a014078010007601c40f031135141400da41d0000d10415010002c0c100c0014491140e201c0c1e251603400d16814014008101c00040405004454440c0001c0c481200000c03201041c04040b0300100280101c1c441e4244100740001d00084200c002050503260100082201816902d4aa0382412a100641c041003000440c03003201030420740000c8040ba11251094005205070130385001228036121004200401c40c0e44400415074458000c8003842c4104140001504010401160703035040e04e506142e60b2070090500041e0080c0348040015132071510100300d4041e6500030320580e980d81d0003580d41e8070724240035110500e031961317850303162030006 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 499926393 1250 499925143 499925149
    0x4030803270313031401020c010e0f010605010504032001140a0e15121303090305032a06040b01052b0804030201170903070f110406090e010606170402010e0a08030409021305 76
    0x3e18910961580a00a02499501c42e841c3c0003004105200c059502009441c0040c0000d014954103009440c00030048540100e0b000c90031548990081030400100304800c00c0071404950b440c5981030b0710f60705020055409100165011810452400e540b03403004903003440d01c590000c1800396255800c0c0d6002510000105c13844180f8410075903910780c40c21004c00881d84068080f4a1054890b20909003502e4098a80d00c409143d900400107a45c03c902c1240303a50544111000c01d041c0d0028122001021b0909195456a07131654050042e9070241300380c00c000c9a501540c11500e410005288402c03111013280600b812500750344140010790104011110750724901900c1c402d120321030ba40c0d1002a60400485030380b51540c5040d25801605c175000c84068131107885e9030328442c10b4018122070350300043e10340d00d1000c45401d64031517a000c10180010314200084e000011303001305521a0b424030f001c00c290724403031000a803210310980001004d484042070224102d00e0070b500810100b25600c95140046a03100e00b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 499927643 1250 499926393 499926397
    0x80c1f050904050103080901030c110a0f0c030804031b050105130302010f03060f1502010e1902100909140106180302030709020702040e0a121733060705100605040203061c0602040308032703 83
    0x302f01c10391004031036102180700840c0400600388a043d020811642d0f94481d181150000d800a8070340001983e0711003131000c048030016005000a00307101d42010f4007411940d80c404039500c00a8103021401c032460300154461750102c00900a040400141a81c0300d410f005442400d01c015180998a0442001584040040c0c2c000e03483c00041d40c07030084a1580c1c0e00348083e03407204810310418071a10110210f40b0303075001e0044c03604100540580100300d61410000414a100542c06d65080c8400008280007503200402ca2405031000a070300503954504600c081001460005c00c1240603004041c00c4108002d80c1c00031118459400e40d0f100d0b140490049a40c42161109683e00e241c200b014a0800b50750b4000903c0392080b0700c0e07240c20303004071000c00880440c480d90b0107281c1c2114180c00c00094101480f0192181e80301500003034030f046041d4941403021500d1080351400c40c1c142c03440300b10310500401419404440185038000600e640341d080c001e5040d080410075940d6800d406030f040f80000401600001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 499928893 1250 499927643 499927667
    0x30d050f0d020c12030103030216090c1403040215070c090b090c030708130c320105071e0f06140a0b0f0d0611030c0310080c1f050904050103080901030c 67
    0x200851410001c058088000e60100b80303042002d00600b21300c0d00903c1c1c3c44d04080d42c000d6019402910404810501c107140c50315540d0800410246400488203038950301c0640e07008180038094a2550302e454900000e00442080045100e141c080040e0710006c1000702640703501210440002484907400000c100030502e0b0045030a03000c201014400109a5841080300c2ca401030400c00c01020942266159000200d6907900a044082003034601c07400040038034100d10025030800e42401901d80b00900000b4500d10406601821950080f01c188074004880f071608440c1d01d81c80070305007015022518120001d0003d915401c40d80c048000009003d11030f80e4081d0001001303004060701c240c0e07280c401c2000b030954001c03a001e55940c1d944d40c00b051082c000b00f80041d4000c0506018041e1645400b120002480e44150040c15454003c6812001c2545030521445c084400b1402c102d143c0901c5d801041b1410f000d01004140e0060400c4000800d000340d050007011040802c0c1e030103000e00d03c0c40700801d5641c411141c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 499930143 1250 499928893 499928917
    0xc130c08040b18072d08120c12031005180702062404050a0b0406150912080c030d0903021c090311180408040603051006050a030b040f1a030d05 63
    0x4400100040c03920050b4541c0a900c0107104203074038a40c0c0c0c0e01c452078066150450076004070b05042c241c1c04c80501c4000508907040826400c40f03a541045080e903124101c2129200c038295000c04c11102d017420a100c407000507400d600b901c540301d00d040c42c10440d10ba5254440c0c01d01483d52140035481d8000391105da52b00c40d480340d400411240d101e90383c000711503054624840646e284c0e91100e2291f1070b0380d28000c0301e018541d4ac80703002c20b0b10142c080411045403000da216100c1d1082840b81811001c4c1c00803403000c115030000c180700d00c3e8550f1a04240c80035201d9a002100c69000000b0b42841c42e40c032aa0241d05020300a60803200c502d00c401c85841c10740030030a1901030108810100c00c100154182e00c00950f1000f000c3c001e1460b01900340c00c1c07090812002e0b9003c0710080008a4184a040c5c2c0c0361080507440090308290b8186076151400c054040e200700504402016269880004540c88981000c840c030800382c08100b00d00c0307000040da08002d000b040e200c1d0b84240070f0032180d00c0015200703e056800302168a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 499931393 1250 499930143 499930157
    0xe1902192610020703020a14031c02090625121409040e010e01050c07060b01030c0c030c060e100e0105010911041203030f020304230d02030316140a020c130c 69
    0x1481c121000100900224602032007801540100544140064280b0764401d07002800d4003602d52420702c810100380481100a0761003480b0f200301140000742d40781c0d458840690700582e60044d02d40402e1351032103001108110301220180c083d21010900f039844441c6030080c015020401c9601c40300715825015100300c06020b1000b809a40c0ba90b1a02d948102031100b45000009544a4240107586c05e5689c101c44604e6000400300b010400d00000d405609200030b42482c1c100100241c48802a120100307011000e002c10524110a9080202e1030740103640b0342d904903003101d800c500c01d0721294000d004141c0c81d02400b03509040c0005103034041d42c06030003c05243c81100e01c1c00d007410446414940e00c052207040c0c0804d52141e100522100c1c0910041d40030380c1c05010202c00422010104003230200143c90070b0701495100796600000c441c1e0200540b5007102e0940004980b010054008944c013420540d00c0e0403001e000024400319040e00081e1282c8114000d5070018148200c4050075821207590246102c045058 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 499932643 1250 499931393 499931429
    0xe070509010e040e06011802070b09070515270d0b0405010203150f091b120709140d0b06060d06030b090d030c080103030212030a0612060903200c060d0e190219 70
    0xc242814140407011f5100606060494803035642c00c10058584a12a41000e1024805d605100c0e03030192200c191141d11500c1c0c07140c1448404460400d201c01e0200404820817980780e0ba42c0c03140852502103401241d00b840b6804c20f420581d0007980300b5035072005034002140401c039450429611070051b039000249050199951041e00030000c10050035813045002003040750040110061420a0044446946900041b41045400b49000107c5c01c0b030340788a1030002c1543d9001400c044030f1580e001c02c041c0c0e20a03403509010300300307803000d4081ca420007060b4031102410011241c130001001105100c2d02ea400340144480c11a0980d05007000703000c090010303000402080340c61f03603242c4000c40e0407181c02c1c80005040c56840010f4420081481022101161220b000c001410741c0031005405603510b0417040555940f004001c29510146103601d84e025070004100e0024500c8240e0204051140080c240c5141c00e00c2414001d00c087c40e0311208911074200ca00c0000e40044401355400181c0b4a0a03039407030308001e1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 499933893 1250 499932643 499932659
    0x10503040602032e0f140607060903030e010218100806030d031a06030a021e090f0103050408160804170a0c050d02030a0210030b010e0409030f080c040e070509010e040e0601 76
    0x11004190444d03141c402040004001c0a002c059845494500c015650b16814019000c4c041c404030390050f005403109034083c06084e9a480103c03584e03140d12110001303150101d0f207002c0c5c3c080c1000075104180c5500c081040e181901040301c2c840d00340a400c41c1c1d4013420302c80c900070071741d112081aa49a40c06a01026071440380d28002d034860540c1155480001e403c0d001c603000041c2003540308481d210403042d0080f4008a1000365810303015980c8603504030b42420516000042550a020b441045040644802c085030030b00c000241103480c5074500a8424003c0c01c21401c050440f03a1080c0b04103070028480c85100403100c0d00c0071030f00e03041c040d905c1410106039501d0481002280005403a080e0303810702512600000503a00d90115000000d00c540700420111224070000d42020255002c0c1030280d8244440200060344c010502c640340c460034100720789281c41d030140411440c0100c2d040840c44510003010300c5451030300440030340910360003660740c1d2403440d9112050000b0740364a1030050380356a22580040c00441 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 499935143 1250 499933893 499933897
    0x10e1204031a0a0f02270a21080408010207030c031e0815011b15060609080a031b06111903021206040b120318010807020a110f060403050d03060603051005010503040602 74
    0x143d50300004a10340d2a0200f40c1c1040380c1c440f01d00c000d041e000303032081020f1100c269444564680da085030025441031504d203600d140720b0200c01d408030910b07610094450420900718182d8010b03207100c0000310741380d03d10380c60040d0241d40181c0d410750110302d070120200d004034200e60684130740c00c84070350b00c0401030349518070f00c49090440a04090f041c0701c0190580141081c120b2030100c03c19018800f408004c07080f21a42c14102e50554110348100254540706220512000522000700d603450b2078408080042c029100c80d9107480c2c400018a414140030b5011428440140585244802c891340044101940d5209500302e01c16540300e96940c0042c80d00040c0c1d41e182a50140e106020040c0c01c09030030385006110941141d00c91489444a82000007081a03e541c0c4130b0300040d030284403070000700030302030f11500c0e501c0c1c0d40140c2c6500e82d0b21481440d84680d00c0350b00e890054500030765000c4204c41d00d0407001040034004d0f01030340c003503100042d19040020b05840040002d6200b100c0040c1c45982c51500e842c0c40d4003001e9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 499936393 1250 499935143 499935151
    0x9010f2102120d03090b07030626070f0605130603180201080606130f0305060610051207170a050f060a140d06020403171225080702010e0f010e1204031a 67
    0x2103841c0001c0c003a002d2040c015150700c00000e13076001070380038580d00e080b09180101600440c1050318100c0b05208031603101400a03c0750000150300c0d44442e116a01c82441d00105422182803840c900340300141c620703000000350207a0002403080701012512540101c04460342c2d2140cc19041c908030b0b40d080095405020074070f03000325014140c03505d420120700b0300b07a21030358140e403040403400e11b00c1c0700c04c00900c80c09200c083e801050031100c030284503c040000500f01d00a484500c1941142d140100701114004c0640030201c0401c84000742161401408560041008981020101c01c41000203100da281141004090394461103640303110f45058800c0c00410181004100c80c26a0308000110208500207940d00b0000110a4044d40e01d486030115103032030703840107812000400c106544862000081202e0a103a0440c92700d400383d10b5540d0f81c00c049000d0314a80c5201c2045005c0e900034101c0e8220103400403011000c0d400220790340c03084034948101c101c0c4143e10000d0081c0c20f2500c00404c5c0b142c5000034190308 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 499937643 1250 499936393 499936399
    0x3020c041802010f1103040602070602010605040506240403020913140606150906041806060f111507051207081509010e0a02090d140c0a0b07200a03051b09010f2102 72
    0xb01003100e0010900c6c681c4075403c00d0015030310104081255545c240622400303410251420300145c1082c4000c25060042d407101000083d007503192100612100c10281c1b030003580c00130048005401c02040180c2c4c54a0403100070340c0c0800b11040f400c10724403c0020b20034000c10340505081c1c01030f016448811100c0e0000d002e581e9002d40304001c0051909040c40c2c007a0b012860b0302100007a5149454401742591200c0c03480c440c24842d0f00c1001e50294000072540100501d2240c0041030160f8440b00e084901e807040587e20740c025071200e0140191298041e40462041515841c8071003082c2c04d050810654007030910941c07a0b142c056500140b1040c2250b000350503181c0d009800b9240381203459036400c00001642520700d0503944000004141441d00003140310040c00c203849001d21f440304d0b5071100000800203840c43c0540725001960030034a5162101e10300001c5801c1004c0e5600c00412080e21000c420490601901c00c013040c10000c2814860400340008403564100a518a84003407101d10340300014410b400c0ea4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 499938893 1250 499937643 499937657
    0x30607110c030f01020c070f1a0d2a0201060512191a04030f0305070512041106040506071a0606030601090311060d05070302071202060106050d0506030a08070b0403020c041802010f 79
    0x1c0d4540707003080f610350110600c100260700c42c00220216480d08403d5400b070303680001c03000b004018088280070204120200340c01140c0c0d035000020310700780180c0704a4900481000c03051080502180071520406511350b041d60080c40941c0d524020403500340d44600c0d0745003072500700d4030a060f4408101581c034080c0d03500c80c5401107d60700e0010080e0382e100c281150107401090340d4240e0001c41640c0340c41808d0380801141841030905800b00082d0780c0c4a0300080000341030b81610003901c0219941e80050720002c000042c8510398640b018074002c4c18000079008a100d010032104049119480c00741d09683c030840c810b9480c001c07620300d1603e400c682d494001040f40d4100404104004030700840340103040c400d100c00c0c0c03005a40c07a0b10510300254644440e03508a030454101500502426a000d003c5405901c0403840100e444c1d01c903180000e08100c01181d0007000660f00140e86030400400303070110b80c4180e01a0b0250b903550845039091006030b501a04903d015600d902c800e100066000d07800c1510001c15a1401c5030b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 499940143 1250 499938893 499938913
    0x40b0309010e0a0305072d061e150503061b0f1c140601020c030f0d0e01050f032d010501020a030807020a020d03120c0314010501030905120d0212011403060711 70
    0x103420701e401c0382810f0780014000180035051094400306e4881c035881c40040d08071907d280d03090482103000c010b80018241500d60f217030000900405600703401403207507030042080303112510380303a041052200d403040901901442d0001122501120305c0d40301c0703004446503070919201031064a0101030784543c5521145412002d0380000d52056841004105012100f1031150303420484006880c001003546d0691081d0711510001490300380101d0700c0000500c260406142c85411000107031001c2c05030524110542c40044108072800360828075100034141024001000850441031501c1c41c06001d000d0240540d10603582500068402e0342e0203680242c20f8419608006166400610704284606041d000a6030704000c0e8030740c402c0b452181c040c102d4041d041c20880c1003070f0800e522400d00d1051040605050341c3e1804c9905200e030a104204441942c814dc0b26540d90351990309400035001482240018003090380046042d07182c4540b020045000240201b4441c7d0714000121200c2d240d1074200d13015409829a50 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 499941393 1250 499940143 499940171
    0x30309061e161212090c050405070e0405040c0501090605041a03041103061806090a0c030b1308130f0603110904050a0204050307030f0b070e09042a090c09090204050105040b030901 79
    0x8040602d200b40000b204401c0300c2c0c3c01c003d0500d1001202d9070043c03480d00c100303000010510841075040340c60948012402c0d81d21f41c40242c40580f4075034903542d0040e080c40200810400f42c03034000b00a596098071074145543d16020221040e019030b02078908410301190b00030030640d05040c00340d54410700c50720302d0303840341c54501c07010a06101c022f652a07100829a03000c6500f05003003e01c4001d9210a90070010201c2c0380e0551074044410540b4800500302000c0003000c81c3c201100141807c04851f00080060340d14010240301d20070381400ca100b451a0700300010000b09800c0c0c42030045400b48000d03208203d04001c400320401000b06406016084e0155080000252035202441301c88000c50060070250351081140c01c0568807070b10300411ba10300f00000410b440400365a10204144c100b5040741c5000d00780080c0303103810b020b860780140e040e00042c004140f000554032000d810a140040c229944c0c10380c010394540c00f02c4281e00441c014a40414018042032008440e00c0020b160700181c45000418810a6000c00d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 499942643 1250 499941393 499941427
    0x10030b1512060301061e03080918130507050103060e010e070309020406060203091e010813050118080c0f0f1009050a06050a0b1f0807121508010515030309061e 70
    0x1c2145036503140c2041080c5450300780f207000010100000c03118501d05c074020000200300142c0c040207210704004121602c1030380310260706030760701441c40782a44000d04003680c68585105031514111000d114640700495a54420701a8500f11100314419000e00d9080500c12404d03040c0040421702010ba0b10300440780940c0c1c843c002d20f001414140c014654030042c100c1800385c50105590a205413820030001044c0c40d9a100a2941c0c0c008038000582e001c2c40041d01d0268007416a1405511400014051080c1071019102c0141403510800d811140340c0c02e00d4108468603040f88524510141d0004051190031003041e402603008144a00c05072a284422540d44408584090f20302d81012075803035034a4540d60420303088840b5074188102c0140007120302108000d08405004040a0070014080b00080390619260030520b00b01500707043c0f042100b45c85001050080c0b9040701c181004c1841400240510706010040b01c0c020071002c0e01003484c012411603038281414800305015038503d0100000302282d045140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 499943893 1250 499942643 499942657
    0x90a060f02040810090f06020f0409020406020705131505010f170901020403051501140415030f0609031d0a0e1806040623070c021011030f091e10030b15 67
    0x240c0141c84506210340d003441e0401c0c9403220b68500740780c5107000003c00c221080d05c2d1030783d542c840405640d461001000441500440d4468139050740081404641d01340c001c03c0c1582500c1c07013070317a9141e80903075050545c03016120080301200030225800310601080d403103100800d4500303440c2e08140501054100b90420050421070b45000316950205051007000f40a1240c1c0410002041e0018499418030100407507200261404c10310035076807546a2003481c200c140111006640006104020710f03800d082c80000b070500540c0440001308031030790301d41d0000030703c3e420701005403800380c0b0044107281070401c8485c04c490094034107035030503041c1411020604002c001440c4540e00c500804105842c80c010300d4003c0104a10012034011541e20402240f103034440400d460b029011030340c2d0141001c0c0038006644e0103043e42d00b0b9511074003000880c0022441e21200402d0710030400c0d1a11007102d07045820580d680059001c8956000351384c182c0c10503605200c0e4200006a003001805105080d42d900825200d030741c4403030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 499945143 1250 499943893 499943921
    0x5061909120f050c15010e0903040b0a0c11042301050405010b1209010605030a050a0c0b0f032e09060305070b07021c060e030313030f0c11010c03090b0c06010305190209010608090a06 80
    0x510440480c41c03503042c8c10040b08402181042c2c10402c50202d1401045060010080903c00017014010803c10000400002a10402c03c40c5607050340c503403030500489075072141c1c50070080c0001014205071142d641201e0980c4211414601c45c6440358115920140605e0360f02e40d06ca107400710780b947c0c0502c842c466240c411401802c000c0b5141c0751021100d402640103140c7c0c54024400809200750190403240e21207d402100c221342c05602e5205080e09643c0714071041e00350309001c404219424190b02070b4042c0c9004200303e80c140d40c1e1f1001008128401d581000f0340040000240d41c5004c402c2d94011001c0e603110315800718540c80503020b12403441e04100e490742107041c0102d1b03a039006d05400401c0c203c0c1d4a055460580340050040d12001b1344407100240441c100021032407020241842040d20101138101114200e07910700008018958910b428001039480d400780c0f0394418021000400d000340103660241007082c0303981c0b901000b0b41d10220020100e02c901c3c01030242c5000020a40c2c401c2d070040030460 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 499946393 1250 499945143 499945183
    0x61b03070f14121603020901020601030f060e01060f1d0907030b06030708120a0f180b1c0504050f010e070e0112060f0e0708061324090f05061909120f050c 68
    0x402404c1000402c03405500600d8030400c1102c1c1c03941d81c08201c2c0c9065039000a4140c0714445c091500f0401045c107000c01c0100c0303500c4c2540108903811083e05040403941c0012100340c84036811711407201500c0d42030380c2508031036000403c10000529002200c035070140c0014103944109546841d40c60070a0311025041c5014400081c0e04807603030350003290181003d509403801380303200a03090b010f5008440c194081c00214000220b01c0540381c80c0210b654a240c0c0c854040144001e0030545420303596508607406414581d400c01501204d4a4000a0020708440c035118000d5200d0b481d02000030f82040302c00900b0f80b4000c1d16140302c10403000c5e441c0a500080c6000100401c80280380149290a010000d4002400020701400b1400031821004448030007031465004021554007a1800303500401c1d10840051220704c0312101d0a05000303011544a11520806031601e42904014401400b00c3d82c138030301c0080c088105400100d0f182d038400c421365a0020000d0600e949800210110f4601d4a481c40c041c0d41e003885c2e10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 499947643 1250 499946393 499946401
    0x60b0f09011e0f110c0a060503060301060b0901090614190809120c1b1c050a03031107121809020c0a060e010b0f10091d010602061b03070f1412 63
    0x40038030081681c444040c0380340b0450452080042042440680580070400d200003200e00c0c501040c0081c8034582001002d1000456030f030380d0003402ca9041100c000e8441e51801000007049a0000100c2d951107030140e460717a20840c201501501d4000c0c0300700d20032040100510030003a013a24504990580c200094403030520502d05804c14518004031001141400841805a41030920000030301035a8400701e842d01c2515802d0800100c2d140205d03440356101100400d404680911401040d04041540240e8060000a4429488039120300c03503044018031580d4240c100042481c480c02c034441c0400d09294500c819180d4a43c1a4000d0b0303000740c18031b01c0240c2c0290248a0400c106803245200e110840340090004503103001c001401302120001e000e000b40705141e03c050307042e403140b03902a01030501c54842040400d80b11f00800340b0400d00340500d001520650000c100800b082d490720b2a1040d0007400140d20355510420200d1700e000c001e208000500c9126002c51042c02107086c05400c0c40414044000561300e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 499948893 1250 499947643 499947647
    0x112021c0b040c09031211010f06060c03020601081513080c0d02160905100504050606070b100501030e030c070b0a051314030601120f0803060d021806090601022e060b0f0901 76
    0x1520a400d0044c07101031201000001c41c001400700742e41c900c0707003480c40e582c0310105c4140e800751141150b4010624034120011070000d80001c500070500d030203682161000d80c1c9030202c00c3d94403054001100080c142503000129038082e2405170710038640c4038088c501d041100741c80701e041c5800c1c1e0102020005d03802542d0502c8042d403600b0780000c0184101c1c241840503007040a142e05854000d4029113000710b0719034000506076100c6000325804981c0c480c840042a241401a0f14103d0205000713050010342003030740017003808200006640001c030708400904112441c01d224050603500070640441408400c1c40301d0358120701c003503039228000c0c5002d41c48900c110b05407070304041c1080c0050b0410001c4040220503500440c4d03240381382c04200c0d039001ca040340e035a44480d000901d26502d0880000c2d8800e101052001c517002403500c4084c09407505907007504581d00c400f401079854881003100314840280404010b15900e1406a00342031544c02080c0c0018031644640c0181c138154400c40d80209030403400900703002c0c0b1303503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 499950143 1250 499948893 499948901
    0x307091214060702010b0915040b0d0b100518070c1704081608030406051909050d05011a01052508070f0b10061403010501051b011505040e011a0112021c0b04 69
    0xf100340c4020840d845106c0300045500c0d0340500411070031811600c071248591115071100c004240700602002c980035807450700c011200c4085a850741240030000002600341049000d021003600d1485002c0034a40d144181119448203601c4207861038900911496000f0240d0700003071001d0007000016048055062100c0c07a0052842d501804403640100010840303554400103440d440030b0305480050301c00f02040300450b800c0038980c1010754420407100105040090543c00345c44071036031504e4401c6030300342c9030b80040d2014022440c0c0030225941c16410055400d112036200882140309042c2c0c40d090000703603110080c1c0506e20800407030b03036460408288440125210250b01c010409480d00d02218103841c505c0d50b00e580818803c86050000c00303d0400445001c086c1c003000b00d4409000204a40025081941143c5a0905c210f0340109c0c609900f00da005d04060040c248513054016802d03080c00c1c0d001c001112818402c1c0f05884003940d003130001826071040b6060010783c0c0301c032040c030218000804604110890b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 499951393 1250 499950143 499950151
    0x90e070e01030c05060a17160806030a021e18070302042112050a0c0212061617060d030c120e180f0a0f11120403030b06070b0606030709121406 63
    0x203000c9030001000091a494121019950143c441c242c840c0040c48054a04501e00c44184c411000d0070410851402d000024a0785103200d160394a100641301c0b1420f05403204408070011f50040e07003122180c4a031064012000505a0016041c105a40b5030507400a69003901569290006900010100010715080303403002c210300080c1810f2019101c1c103030742d005000307408400301c401840786c045507540f5407a0288808031401900039200820b0086490f104035200c140031612807504402c0c1480f445074280c850f4056940c42140d40d4545801d41d116901000052010160110f0401410070070315000600300031101c8107000480c0d103450025a100b0001c0007603001010320300c4080980484100300c02d00c0c80003c90503801010703141c4002011400c42c0b90400c0500010300c03184000e90030014450f01d6270f0810032f007041e200d00d0003a5420001400300008000c124854404084d000b000c1020224000e8a0484004c40d0400d102e800c1082e03415649108012000d5052001640c901030307018800c0c0c040020a001441d44 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 499952643 1250 499951393 499951409
    0x80313020f270a0b030a05010c0f0c03021905120c030d0f0b03100e3301080f120d0f0507020307050d09080a15060e010e0a270b0916090e07 61
    0x1c22107542014420001c1008001c142c2804840c04683c200c142c0d41d200c8000840040c081d41c2c00f0741c0312400c20742d028080400541c0d00241002c4024000075228680e152103036170b0b141e03011380480428411a40d01e4560034002c00e54082c09090007203020404000002c0001005040c00b454031601c407201440700b100c13640e4005140c0b0b141407201c5918140e9011401f40c0b071000707140200040c1c041c1d10070075451070701c80d507020701c030b100d0072503641140d581c4806e10600c0c0315501080c501c0360521f44c1c0c1c0b00d040d900e80394003e4490281e210303032080c091040c00160000160908085201d00040e17052441078120342030f1041510309e100942c000240031800d004007407000110805481c1001101c503813802044a907075500003140030f00b2170042c8081c2d00e900301c440c5410403001001c007159886031950f1203200c2d016044030242d81602c01c0601d0181030030f24004400c040d1905620701c041c48400e9035007550700e41c040600c0717000701100151701138040014826401d404452010b040d4080f00007800307a010910041ca448056009854 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 499953893 1250 499952643 499952659
    0x30e150411040615020609151f08060c0417160b0f0d02130e070c11041802030a03030518010c020d0c050a0f11011d03211201030b0a110306130c020703080313020f 71
    0xd0705410b0300420316080100441642800744c2c01d44442742d10b11440e504220340e240070301002c0c030241d11140c20142094030003580d0118180861000e4480e079400100c603288c4540d41c10b016003004091a04805801c0c0e2417003613000e8034038080003448414101e07404024189540c020600c4240410042401030355032000032410f01c3e401c2e620950322174041c001d2580e604188103e495014502e00580758580140025a014041f0703032032010580b4024010f01000c50700d81c0728510421031031032084030b0140030b116070041c0250080d05408803301e0781200c00008000050b50300d4482d03403013460b0002715102082c0054030b0041440211070f0710f26800042c60030122901401d2010030301c1200000513500030a04046865144880646440055212010602610000b00e100115560001051256044150344580404041004a01c82d40d200641e9540001c3c0c407510707040701040700c83d5010724a0310341c8026401030003401210906e942d42ea41d0b4802c0c5c0e5000700e812074107540f0074130001011810503086c0c194103000d040b14245 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 499955143 1250 499953893 499953913
    0x601030c15050304050c0f0102030412080a02060c030c071101140706061401020c030c04090311151b0a081b130b040305070605040303080f13020d03050910030e150411040615020609 79
    0x20b9940c84e888100c0030f11400e42e02c1c207e40e002c2c0e070081049074010f10307440e0044100c103085410030b0341e0540c101c01400300c05401001d0025024ac0460421244540280c0302003a00b840d0598031042140784141c243c0c0c0b41801001079503445c070504864003614406100307a401103011400d00143c1600d40ba051031000c0d0641d4007000900300f00307903404101e120800300140c030006100c05617030404940d15038903100d940d88240103107595000304100b03100303146105080c06041340801102d0440c11101e00e204d64103181c0001031220300454280180003460000700e1103852400c0d0300b4140306d140712000c40001c6070300030b011802001800300104402400007a004104034140b040c109442d64601030064040201f039044007030344a00c0002d448a24450700d011800c1e4003c0e01003084511185406842c80c0d0200341950303c542908182c4c4182a4400e005050a004000300030703054492140039155100c10000c2c108403001d035a01c3c5c410340f001e51100e100e408010004e03268040c1d01ca41c140940642401e501508166541d0440e0840b1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 499956393 1250 499955143 499955153
    0x5090702031219060605070b0c070b0601080a0e0f01060e0f04051906020408010f050f0f09030a030e0c09070203040501260403050903010b1e10031b08180601030c15050304 75
    0x240e50080000c00c040020b07562140410307640300b04900c128810080ca48000840c066a000c0c010340720840c0302c1c2000390b6070740c0c0b0f9502d42c9204a028844008000704002c2d000a0b00b03551140a03010b401c00340082001c128900400500c42c10180c00341d00148880e0b42d102001c01200d00c10380c10b00d640010101a820615051030748446031604943c408441c0b10444a40c10503040184c264100c1e0003c7c03e0300c1000b040503080e846203941c081c110559070300403070341c0300240460103460a080c8054041c2c0852401107190100f05031041c3e0182c03064429400d014000d03d100104d940d1185404540301c0c000c0b42e4041c595441c1010005810508a19102210050f000e250350340403a2014073b029030010b803d0704101c0e843d601d00760700003405444828041504110301c404140d04541c1041003c601c440000c6401216080742c8a504a086035881406505002c41841c103000d401d07401203102075042003c180003159100200744107036140140a9208a03405202040d08000415200c4400c01c60043d01d03103490307072450030300d0345075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 499957643 1250 499956393 499956397
    0x30c060914190203340e060a050102011404110418050c090702061e13051009121403060f060c070611070905040305070212010b1018050303030f01030609060b060c10060509070203 78
    0xc0750310505c422070410041c40004140c40c071148888107000085194584001003040c80c4142c607441d0055000c2c0001040c20360040c065044d40d100800108011656607880310ba05419000e40100c1d006030795544961000340021550385c2e003980c01500140801d88810060000d00d440052030b04d000c5400c01c0007800b10000030b0030607101c0701c1c508080030303152503488800e4240e03a41d401185004003244035100001001088640001da00940580c503a69025070f84041c01307403041c44646000c0002d003081007000071401d1070650421039291a01a142500340031407244803a150000315040030012480014002a140a04000e0f2070007410342e000080c44203080c075036009851130082d030340024800c4100140b82c81c1207690941c4064482c100007490b4040d0892285000f401003807455620703c3c5c0183c841c0002003014100002103034016205d0302d004511030b07071031174031100e0003811140f030b0440b0402d803200c0340c461040e500d80c000340000f03040c40005002c81c591071140c80c00844109602c06030103401d010701041080ba80101c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 499958893 1250 499957643 499957663
    0x150308041d010f1a090a03060b01020717100504060605221503080d05040201030e1f05010f050307150c020607030503010512060f0a020d06081005090d0203040b070807030c060914190203 81
    0x211310101c3d8051014250130307a00480101c1c03500034106140000a001107500444e4140da0281c00b40c40ae60b80d25681488085403081120031401d50148642e4104e41089501095000b8000c020000d8003d032a00005040d10703410001c1c5c942504003840a00214080038466a041c41b003010b42102e03140c5240d687e031303070080380a5400c1c0b002c0080c1e070b58000a015a4003c0d00000b01c040c07107050035100c00818484031188991045036240300030518000c008a42c016010722080f041d03c07001001070184620b0000c00013824130351500708004000c2c085458400589450001c2c0c0039091098aa42e03031250705280910404075100806020360354080404d201240c408001802e400018404003d80d582e44070f80345840144c101341c2c1c4440b42c28411071007980a0421300782c0c4a070b40503010300800d6884840b5a42000c9949002e240502541181e08100520000b100b00004100b80c500ca4202802100055160002258046001502c60004e02802100e40300014407141000001c2040000224078441d00440d9075003040d44 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 499960143 1250 499958893 499958909
    0x130b0901080408030a020c0a0c092405060a110303070f120903121503020a081b030a111e03010e16080a080d150512011b0c02060715150308041d010f 65
    0x5c28015505601141e07800748449003102c0d0f4068480c5000480c00c004c520900540c5403a21908001c442c100c0d01184550344050080d134841942040100210b80c0d001001c0842400040204580c0524080c000345129105944803224940c03c12900a003419040310329444072545480030704000a504428141c0e1402d54a180000d0401c21800e041041001c3c15040654480c0f400013002030000d000107618006000703c2d580b01003807540f035203052598442c80d10b200203180c01074542d003038241030910391501c143d20000192507001d035140840c08a0308403101032040c40e040d0f0300300c0040742810203070b407070410300c0106100001000d003943c013038486902a02900011104403a100c2d080c80070b60428562011014000003000700034036040081010740202081482104807000c2c80e140100c403203010300f03504807815401030030b054030f41002655400c030003008143e1510082c41d5070f40c1c050340b041e108441c0b002d03001c1d500c5416207a6a403410034042180e41e20480034404442c01e412001445240031459062044860007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 499961393 1250 499960143 499960147
    0xc010b0d1208070807022a120606040e0606030304090e0102160516080304050303090f0d05060c03330d030207030b090a050601050a0f0501140d021305130c09060f020a06020d02130b0901080408 84
    0x3a07200c0e05128422031362000b23803407110140103040030400702e02804049030100301e43c0041c0c40c415034450008035515685508113100401c00c60344c0d070b50000c0705500d2028000620b80a242c40c1d0780d24840d02c0781c00c01a00e0310303408440d05908a07003030343d2640d00c064078140c07006506051400c80040c0c0d40c1d218400c0c10600628520305100180d4590b040004c60b501d50101c00c0e91403620340b801c2d0001103a002118400050003880380c0000800255501450342e4025482040b90b0035102c01003400503401910804900f14407a015001020a055280c1d5a000e147c400010b02590f00542c108140341c401c040e00000d2103413031001c2d81000401a620790000031200d083c20015007100405076180481d01484d0f44d0486540d000080c280300d810342101c41c00c015508100c5031140700c64214032152048501c0c00d440701c4040b0b44100d83c00e12032940500408402d401d07403031040341c0d050082c80e9a0501a0380013241c6c0c0c1802c081e00400d411100420342800e035406041050a42c90034882c030800004c06011001c6d0010b030840c080 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 499962643 1250 499961393 499961443
    0x2010e0a0528150509130b030d0c0515071e080c0304061d1204050108012114101b0206060d03021b010e060a090f09060506030a020c010b0d120807080702 67
    0x82c42400b240241448040e0402100f643c1c40050300990085054070302c506141200c41c60f8102c550b200b11003403050041d000700a5a50000d0040d51804100c10042c0c0707142c810b15081c2d0100d2600250007510588050f641d0440e1360022108140743e20844600130340501200302d0810102816940640e9402900300034085510040108181e460302c070b103102402c117640039096802c1c102e051441c0c018011141c007070307880070213581c1d81ea5002c86c00490b0208041d841a460100505c001c11a5040c2c10141156107900707958650920340d03544411039400d11f260021703a00040c07100000d12901403040e203a10401c01d4860020603070059500945400109410100c2c2032a03030850500282d01c40c01a0310074610b0080c15040e0303a44110b18000d44181540e00c10304409400510b40402da00c1d03003030300a080448402511860071031f02c03840300d40c0e00650001d04a2460540d81c9100314061680d071922458816030040200060307094034600000c2c8591401441d1005103c07540d82401401c640c002511690100302c0c0c4015000301031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 499963893 1250 499962643 499962709
    0x4404020406080706021f05150d080d06030c050f0108011d0901150e160f021002030903090402040320030d1b0201021f0f0605030f07060c0c0e0f0402010e0a05 69
    0x21a4100c1c00040c0f154110128a998002981e00d030010110101548a50070110b0520180c4000300c9081104180e10001d001981c1007008460f034041384100c44207818a0b100c0f0007581c0866946900655100500c3c0804001d1400e042e0b210100b256402c2ca8001515030611018584480750524500400e41480000481c844000c0d07208841616142d00f00ca4401c95540e0f20b4024031202c2070310440e0995207060175420a40b80101c10701050102c3c59009480003000c101c2c04040213420060104885000c10000c0d8800740e65207100420140d8403c071a5801c4200004020304001020003180c0d80c080d600074500368501c0d0740c00c004101c0c1c80100050b21a0b500810f107200403400c010b0120100103000040c554110450209900031540012011034100710709540e420030550b0b40e5039151581105900700e413005202e0940305108156811b4083c1c10100315030350b910607040200030401c40d854455070400381c09100071980c1c016020300040204582a9403842d0818000581040c980c1b403850060b01c2d8200e95124220b5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 499965143 1250 499963893 499963901
    0x50909010b040603150507020114060d030e0d050a031b230c13020306120309060d0228030902010801050405091507020a020d1a1308030105040906020f0a44040204 71
    0x81000c2c005125080e600d2818613110040818030002035800c003000201000e01c148516105044c1d410700301202ca07221407042c04013901070a1030031340030490012488015916120040b00c00184200c00030480d0070102d050080240c00034000144884030b80000c6ea0380440d82a07540007207001e85c0c01c0740c4010401000074a640c900117281ca400c940141d50218000e6010009034051841154140c429a20403011038a40589910400300ba456000409202a219840365a03000c2d011a2070125003034490b0f440d4844140041150030329003c400261108100401c5580c0006480c0c01020242d40904c641d06180c000503407030f41a11480b08140e0300c1e105001402c5d00d4420051814044d07005841d01086405504100000340c01322000041c440e103980020039185007187c81989060754101c00c0060450f402d180403c8040c040d03012090350b01d940c081c0002d4105031410302c003e24405410741c4804081c1c00084050800c0301d15401c051004403c011002c2d880020b080c070b032842c41d0103017020301020003c2d035492000030014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 499966393 1250 499965143 499965161
    0x21c05070f0c08060a0b061206010309020333070c120e0a0f05030c06070b0417040b04090e010b03010c0c02010513150507050f19030c060906020c0d110d0905090901 72
    0x850003009100784080300841400340c030760043c1500d01e40da0703890040c40140c46444080541000d410405e41400072002c41145402040515003c20588090b4002925190700712004c41e0100c0c095040c0c10441620400705484200510380b1684200d00e450480130317040d00300f00e03900601464220b101d8120000e110301d0810004d050002c0c80f0b500d12540300ca030f0008400700b050107198040c3c490a001030003c3e14100041e038005540c45454203a5541d1595160320030641078044244040b00e0034000411110500c2c0d025001415603a05e000030b120755281d03d19425250080ea503140203900d8155031705000b550200850008640a0030855515400c100c80c44543c04020360110a1031400b02e80d840f15190340c440300500c40d842c060710442e02d02c02400d0228076190f2082c4d00c1c40201c0f2402841a010009000f0f01c00c0407034060181d100020003000c5a21082c0a0380d000200c1c80403140c004580014201e0f401c8054208000200e000030300018410a0025003089110f001d450310600700d080c0051100d0038250001448 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 499967643 1250 499966393 499966403
    0x1c050402060f030702070b030a140f0c072409030c05010510081b1201060f06020d0809100c020a0c0e01080d0203180f061629070903060b0409060509071d0106021c0507 73
    0x140b032600f01000d070b009143c1e26040600c0100b8000204010b14070701c0a025004215020b40180340537000e50300c494200702c42c0070400889500c00c0d4101e42e1800d619124100c1424020b4a820b280080a1300d4661308403000149003120402b0f444409215206000903d0086244000c01c140c0303200c584100001c45000c0c0303a01011a19600700800480c03260840310402049031034a4007128200075402c5415115444100c642031078590284038440c1c80e1480d01d4000407081040350065450010b155101c00b880381e56107410540d0704219210040001042c200403030541c00140384082c50a140780303440580990808440014810300b443c1c4200b40a0b55200c1007120603e11803030a00f04c0b2410428580311000c0d040289032042c0344a07001802c82c00c214000751345148030380a80e030b40704400c00c0d0640e074410000b4414a0b0100c0c0e00950b450419000140341446128043c480200c000c00740036180181000035101d01a00c60340e01200b2800042002d10b800241400a2405011780c46003080c4810400b120640100350010344 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 499968893 1250 499967643 499967647
    0xb06100e0d060e0c0a18020702012a0b0c1c1a0306090d030b040605010509012a030305150409241e09020f01020c181b0f1c050402060f030702070b 64
    0x4010341da40c03010f561403514000f550708060700281040400c0805200301032200048141c00703440700c003c6900910b240343c81410603010030034840841001c00d00440800e008150200e0613400240000002015072021600149034681140c0740320022a1503070380220050705035219200c0965415095044406001000d42100c1e5146042c1411540d56515204e0280c0030a24004078002c0d103003000e00031902501c0b01a140c681c50224100c0044540112150940451855480755041804221042c141d4014000d54005ca014245680180d204550801c1200c1c4201e2400c002c090000e294112480b00c03140c501c2e1107a03c2d61784842003d24001c1d2805542c900907c0d00007c3c2c0000c60600d00f1f5000303900c058000d603a202e900c0081f4000690707541d000f0031119584030081342c4200140c0340c40c0700740301d5501c010034038407607a5400c0031251401110740000040c0c007020380c0c0c0860203048191305600e00c0b0018004025007070003e07003400e4010500340d1040766a04040200300000050806000704141070040c121010959 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 499970143 1250 499968893 499968919
    0x905120a2f030d0c03181a210402031504030e0406060306060e2b0204060b0408060117030306010e090618100501020f0606060406050c07090f09060b010c0b06100e 71
    0x104942141e042075500d525a00d4403440d10314100040c1c900d401c1000760300c0701000d000d0152000d5a424010501050b9550780700301002c60180a44d44d0445440100e40d200240c031810b1056a0800b2100383c0425400550029000c00002d40c0c2c3c0001e921a14200760007070195185c5550a049a12a810100f0140c0180c00d0100c00101150b00d540214100d406a41e22503910400e60010000010803060800003440000240d01c0030004400b41d2414046100031700c00504250346032080d14281e0041d40c010200e0b6001400101301844000b404c5d20347c00c11102e80a145146006000640340550010b1518026001140005c0141e140d061201c6022400b02100c00b0140c0303401072883c210200c9901070305e401030040c955018200c020001d14075028200080c90319041c581041001c07140c40d080b10f1100b0110388111000050003c80c1e91140058281b074036030012440808904001d003d80304400c02c4d190420080703601020206003402034454000004583d0001c036a1b1440b00101e40d00f407074016075241d200035508081 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 499971393 1250 499970143 499970183
    0x200607061e18020d110a091406030105182806090b180f071202010519050901020d05040e0612010609020a0206090105060d0203031b0312040f060605040605010905120a 73
    0x28031010005407400b4424041034000c20398100402d1840290014045100b1000040b044001d890711488081d00f151010390351101000d080e5070142208099084807281403055a04003030098560042820300760043c0c0182d92481c5650f10041c40c2040c200c01c501c2c0d48680300200304858144103589400010500081e01a818081400a8256039280c10380c65445890b03d5000d002003401d0807a500300c0b00250402520b80100c80c0390417100000124100a010000c1603501004120b652101c801690b64080e100c64481c0006441e24030916070060074002c060104100083c0040b0200b540040283c400401c5141c14114032800350500b504000c0c1200d001003000c0200a90000d012841090440024411503c0e200240041c0094614010350107800421020181c0709001c2d2030305500b41d41440450780f600c081048001c0b40701c0810384080b5204011600100e0074407841d80a408080c0504541c00c1003414503080010740181e0f0720b4400c150245007034600708051108280078060382507801a549000c00910740ca80 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 499972643 1250 499971393 499971431
    0x180b0307080708240d022706030111030105121e030a03050a0e0307020d080702030706050d0e161a0706060f15140d0203131202031305090420060706 65
    0x14040001e880c10300050345240b04040c1c4902524000302d402c1000440f40300c0c00461000450030260b0860546481c103070050b154038910310301c040f0a0b8240c05009038040000a42e80440c00b0304118401ea041110624070203041c102180e04540c4112490486024880059424000c001d40d1300703003641d6079444048400d280f0100041408054070341d010030469954198410840e001100f10800c4c0e90300c140640401400c1481c02d802045024203501030070f102e0320340d00207442c040d02c54111100040020070341c01ca40b0340d103901804c1c48204030100038048040c01d076072000710000a1407103410301c40c44142d500305110320955070446080b15009a401e00c80c203034840c025503003019080d200d1107005038220000c2d409850311515040c45480e200080040c54140c4840d000400303500b015041100010301c070a45e81c0000b410021000350708014a80186480d84404c50704291021041d5006da4000e03e407003820040003400003000c84420710380c40404030070303045d650a020810707034001e07060300034a01450256107074011350466070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 499973893 1250 499972643 499972651
    0x507080a05150405010b0a0e01090f0614040b03091f020a0c12140c0109020109061e031509020a020a02040c020c01090905180601030c0302040b010c2003011e0e06070f0c03050a180b03 80
    0x6503650354042d23510044604030030070700c85c1540703070f9038200c41c1803120313501c510080406230488940540c1450f81396586107409510aa0b1081c0043d400045814107500703e116201c2d501040c021021420040003c1e0050800c041e07003a0000d010300222224144c03190700a9403d0b90b02505020346031612019040c01c1c1e80d008107981c0320240c3c00301fa8402c1001540c180303e5010160107001e0009881024000800c065014000403844a49036140b00040458007011520140248014a83c020704498149006000c11600b40103504011504602000c0c0c507179982020300d200458010b52000030f0150b031005555147c164074a080f4020754042c4400000600203401e10a40039240216800c000901800c4010b499940d8040740080c00c14840d0001c00ca0740c0d0a000c08104d0300c1050150011034041d40d000d440c0003410b085a0032005829645003400c08412004100e5154007118078140b41410045901020700340e009010030040c1000070014150945c50b22656529002c85028404000d0a0740c440341c240c03190740c008031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 499975143 1250 499973893 499973897
    0xc02010e0712020315100b091309030216050a060e0108090708060c13090b0a05060a0c08030a090507090903050f0a03090f0804080f060c0d0f02130e10090507080a05150405010b0a 78
    0x200c6290513050001c440103005604041489000707d1400799504c0039500400d541da988222628a001c02c00340c40783c010000038520a501400d201d03004a52801004e80d141d402071402584188818001c10350003590100040200b42003410700380c3d540703143d003034501941900600c1d071600a020500c000135060802030700e480c00410440c10f080ea40c54903188400c0b01c2d0003035a000e0b405916150f04104505060000b003108209070702c1d080110300c0440e1920a05684240e074192072039070307990110cc01030000901c060030103081815400c0c0048801070310020f005000e20400280c00c080000390040400e4042e500443e013042c1c0c049892070059003941082c050a400c640308186542c0a404005601e809000c40c407640318111318004141004442030b507080013450300440a100c100d40c04c2003016050500010014001c2c0742101c2040103514106240c0c1c03092200982c41058841e085c00f0030b10210a0700a407200d64007011521f00001c06a0300c1d20f040d01210081110010303049450613002241407080c40005100c091215 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 499976393 1250 499975143 499975153
    0x903030603150c211b080109140906012d03030c020f030a0f060203070203090604080a03090e0106080a0209012c152b061802042102030d030c02010e07120203 69
    0x103140d07081500d0410341ea400c00120506940d01070084c0740d0b0200566400c4c0044006002610072020f80e00300c0c01c0641c100c0001c10765520040010064034011816041800440b4442c1801d19a000740d50ba01c8040c014000300507e041801c0030b48045142c071200640d00b085007000e4900c0e941c0e05028284100c151416409002d0070340007000702e4103000480101003940800b0082c610440381d01e0301c0c4025007002e0040740460004002003080c41d40c580015001030100403003e400e2400c030344c0c64094590807450340406111580d4400412040303802040841e070001c0d8850740581e076682404012070300026807008a401035406815074494070104000081200e030b000350703040c04a64101400e1032030315002c0c00441304e94020742c4500d901e101e090302819869070140141008255203495031800341d01201e20101c8640b0503640428200140601502d0b10400724080c1c07035041c0301640d403a03008280ca0703141c41d4848209054450381c551260501c00d6003c0b8140701410b009441400b42c9602d2800c980190072041a40f1a100d2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 499977643 1250 499976393 499976423
    0x3031404050108060d080c1510140306010b07150c0302120106030608030d0e01090203030f030405060a02090a210605010801020c0f0c01080f04080712030b01110a0b0109090f05010903030603 83
    0x98000c54055600503100e43d001c03542e882c1c007004002110325400301e4030407009004034450b04a04000d01000d1581c04180c0348981d181010f00450407140c1913002035200001c09c040c084036a1404105503054558480344a41e9506140c20305201c900c600c6080700070032910300250700c07580743c1e0305602511056000400c0f22501e039076110021010b0311220301a407a030a8000304114040000d01e54408100540a4400440c81c3d61594000030305540211000082512000041208110781442520380c041c1c1b10708011818aa402008100c6070000c50180710b940210307442011100b281002d10030100c140d4444010f01c500d6840d1090607020750009209076500703114401c002d0301c2e070318808a460031951106a5030401c1c2d594441c0001408aa005001614030310010000304001c10002c901c0781c1c0c106481c03034901044440c032602c00105640190351464034560400301c028000038884c07100060447d501d602002c1481045410007001003146030300c00510541ca440746c0081015055080042181d000e05860915032034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 499978893 1250 499977643 499977677
    0x50a1502031609060906121e1d060c0301120303140c090307050103091a0403110105090d140702011d040b180a1805070b07060e010f1e0204031707050a0506040c0303 72
    0x540340100c3c408900c1030038046c0702c420300c0707001140c0520703101c1000031920b0f0440c1c51000300000703e40700c3c142501e0790721440810502c0325403108002344141018000c100a03d81404602243d0006009000108546140b0441403510a4004404001e4a080d6243c45410101418040356011040e05400b80c0107202e80015158001d120350b685481e040044180c1409500141710300313584004004a003400759003220310014207000d1060511800d185801000068101c1001a000d40c02c401440c41c079904040080da00184d83c4041d2500203551b0b5044e50b038004103104400200900410030603070b0b410030000c100035040d0500b250540c900400e401e24040143c101d4940c9041e010641440c3e018041307512400d4200807030082d10004108160103407030006050b039038039040282514034100240038040c0d00c0d02078401d600b04200c04013441c1d0980000b0214602480c5549900450781030728080f00f8134040104040381403000074005107101551040a8504d546060b01c0e24414820ba5030005500107018648140a444 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 499980143 1250 499978893 499978907
    0x20d24060603151a0c07030c18020f0d0c0918090b01080a0314070512030c0a09051f0e0a080f06150a1a09010915020708060f0103031b050a15020316 65
    0x289800c860b45440e0344c10146144044c2c081e0010a0a107407404000039402c1c2d4201703010920185204101070041985232a441d150000115aa0009014410800c8148218510044802c050010440481c6164232003900b642d03910900d038424100d00c1640311040e45001079503401a001584503007040101d0341d880e07000d45a916800000b006001c00c540c091351080200c0031a020740960f51103102203a08050700320a202500b03030003c1e181e00c00800008610f034068260000840006428191410409404100c40c601e100401c450320040130700c0340c249054422503c50442e80c0e80035209800458030840322440040d81e0354001100e02550f40c00d02480c05010758a4620940002c80d07410450805850b0702143c1007600c140e200401d2a4140820304000080c803803a03601072034001d100c20750050110245030119640c108440104141c100381a10030060001039041022021401204400030783c1140d020329109252588006021b40700404040c01c41c0f680c0d1550b500118410324004c000020174801d600000c0e1400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 499981393 1250 499980143 499980161
    0x15051f0324050108040c2301020d03111e040909050705090c0702011d24031603060e0109090201020a050a290411040203060f0607050a0b0609160804020d24060603 71
    0x4075071006040009620500100380c109005400704c2210320f599005605820a12442841072107600b40804525980c0600c211007001c480d41c20148001500003070703002010320901c5d0000214100e036420303550f0b8880120054401900b24840c042068030700c941000c9507645c82c207124940c030441c629000107051941341c60940302443e5060b1240034a0042070061111100c24817000c40d9082a8101e2a129048a561110b94a44522108001e603203080c1401ea0070340018600020505042c1400410030010010808450450386880b40000b4179104a100403414110350f88000340051041001d6041441580d091002d00010341d2160b0f1041d90840035007241207110101d030064a101c2411a0a15181c1020380085921880c01040c0c1070704001540300044035a0082e031419140c0d640580200020040095000c6400640884010400c3d240652a81140307000e0400103004214440000c0350443d151500f43c0442907520900082c645a10a100200c40754040550140d4a07030a20341c000503098000d10032003c103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 499982643 1250 499981393 499981451
    0xb0301050f060c0a030e0d08120a060510050409020307050f07050304060807030b0f09070e0301020d0f0b0a0510030c12020a030c02060f01212310060806070e0415051f03 74
    0x9501c0d44c0f52030550b6400182ca1690360008088001c600000710f0000c0140035200e071202c0082401c0c1004a81341d402c5644c0d6400150080c00050a81d400141e00041910100c0311803d40c05642e990303860a08031128003e195040c040034001040d0300707040000100160017514115910f40d2101d9403445400c9013622041051541c212004c450b140400b400c0141c8800d6100900c3e04002455200300404030742285c1c825141030f5000b40c2c0d10303c0010036019071402140c82440d802c0300c1c10903000d4100700015021044820b0041c09040c3d56600102e801c5e8000c400761a030403001c50504549503d11404050040c101000304140140110000110410741641060341681c51605036000c0d158500b0a07090400500150709440d0002184403020801c0701341961100d8113940607000c4c1c0141d05041800509070b80c2c86130000c40035504100c00b04403880b80e004001c1294040100d4011030b1403504840100c5072150503401c06a0802c1c00e45030b42c40380800310400c416612031050b42d010070000303a01d1000c0305184403440304010381c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 499983893 1250 499982643 499982653
    0x9010f0e0a230402041b020a02011b05250302040204060903030825052a1e03182b0c1d0103080703180f0608070329060f040305070b0301050f060c 64
    0x940900e1400b00e6941c0248090720025000035242c2054290b00c1700068001b00681c04901441c00f156486002020440c10340c0c00050000040c69a859482d0040c2c0c602802d42401585998202075a502e1450001150007810442d40c0d02d0301c0d180c0042c0b0f0307251240002c1e808130b09400003281c1010450551415001400d03a0300050301064500110780c254800d4400d140c0c00c0300d0f00122109030000d0030a520300d10001280c010544a48980142484845001d44180c10ba8005200b8064031a1801520315100c100448408610b03842c451003624901200034841d50703000b9056100b500400c00c40d0191002910580004904e941e04034640080242009020051a40c1018010140041e004584131080c2c001000354003240180c85000509410040740c0c8504e002890010602000580500c226003071348480c2c42c1d4101d07400b02c1740c8200000301c01c1041142801080005203c0240320116003c0d02d01440d84a0296400290703203692504894000780600303481003070f0002c41881c01d407030f00c041298410440300700944 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 499985143 1250 499983893 499983941
    0x20d020a020603072c030d021c080705071a090c03030a1d360708010608070e03160f03060f0e0a060b0409020d0f03030537020909010f0e0a 61
    0x4003941010340500180b01e00380c0d00760790200900c0400042c0c5d494440750307690b1103112003d08151070304110100e0603042d90080041c400d00d03001c800342078800b0b651090500350416110b07010f045903d071040b8035015041e003203940700b021200c00d0250707040c5008030242011110010610020503840380320300c003100c40210300710442406000200a103408840751000f050700c80d6201030030340b1030710011041e54003440850041a088558440810b00400c1c1c00c4a45441c18001544c101927000d040980064013400500c094803d030000b595500300001c1200044001405d8801a41d942e1040b034404050301003100c100742810318150500400340b28030070402e516400100000d889507150341004054491526410070740b90401a005601e8903122142040e108000c030548401c4a400e008045410281c051040344600802c000340b04030740c5240752420b1109020f03440c0110b100c40390b000e000034403401c00c2c0035412958250002600b40c880e800b012044820385554024030365a01410341b412100142c0c0f034000329408080610b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 499986393 1250 499985143 499985149
    0xf0b0606032e030f08030106031a0906121002190806031c08071106011d1003080d2c0a170909010306090201050d0f0b100c08090625050a03030c020d020a02 68
    0x103200788200181c00406460391111204201e0039001071702c0c0044000010401907505105503600403050309e40d10b60f10003c04000150701da02c00942910f00c14880005400916181400910701080007800708554440c1100403000454903e035003204040b442d070200240c3c4504000c500c0b1050003003480007004485a010000350740140000c1c040000300a80d6102e007440245040052078040d0880b049c00c58015522800d070b400c800139000300180010441c076141040002d09103402d070303032201e401c0003404103102109550304842150031849100403012442c44017044c0c041c000c5001d401d12806840c0020461081c0d05103402e15200e81c010550b0004600001000810701d554800110180f05241c45464002d0704241c0c002681c42d404c40e02c152180c0d444d8144a1240750009080540403501d0406154801c215120740110b40200e82e50b0071300800c000141c00b590b02c6100c40310401d0a012080d0704140340c084a09003203a85a286201c00c07004240f81100c041226800017a4100501480d603000f049280516404c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 499987643 1250 499986393 499986451
    0x306090c0d0804030b04050106090b0301020a021c030915061a030709060509010504151d0409020d02060306060408150906060109081e030d0c020a1704050d08031b070f0b060603 77
    0xc182c80700078051001000103802c008203280124090340c00420240c0c28021460102c421044669200e85e204000c08409a900400d40621500409121940569078480207402902004000a12003099161f1003d42e4500b59400542950201c2c4944900b210009994510303912007070711214089144628100032662003000200350400042c03604a04050340c801018001468400369840820503005103d151b03101c459141c051f00203c101d409021001c4c0607000b0411800720590f002e0f0040e907000000640d00d03101d1070112401050340c0d604031170401d04402a4100c69200c2a1402c09160080c580811000d61207080350b2400d0b40c0e0040c01030144404480a0100d00700703411103008490380014000d40f00740c002c061065035001c906a801030410290302c0e15102c0040201071124542900040c0030a01c4191558007554048581c0900503a5880d25200b16800b0b02c4200710603550700c0441700154031420440040304440b103207849607802800944600c41000094081103803032441d880c1004241149081c05245 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 499988893 1250 499987643 499987669
    0x10f0b0913110409030324140405040c03080307090f05060f0f1605120d0e0106141002010e03030c0d051014040906091205070309060e0d151d0c010e0306090c 69
    0x190480b8900c00740008507050301c1c2d5142c1c064002c650f1360781d05e0300c61148410000c400507461040d5501c4106040544090782103001c3c03800d06005a5640c8c001404102000c00720102454114208640360700d05848010805400ca02036952406981c58000800d03091010036a02c84182d0510341034186206920080440c3d0001b0b0300e4003052426072a8002c01090040c00b400000d80d407002403440d40d40d03d05816030340031385040b01042d0009078904981088001e000001e000c501d400200c501e0043e410444c001280904212030102010b40000018084c1000c030030030003025240d84095007800f00b9138914a080705100594442c0c502e0443c0c100d02c40641c1440e1951101851500c03940d40000c20702059103480ad2140740c2e08401c0070101c0d10002d801028190800780000c0148030034500f403802c034416900810f920910141000305000d0303015007241d0442c0d023660883c07070752424411100041c0007864140c441e565050f1401c2140440c6c00391012a090b0309000c9a058810015680104080e040e4801070205c5800004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 499990143 1250 499988893 499988903
    0xe061903020a210212060108010c0503010f0e040302070317090f010c020a0306200304060c0315060e1014031f05270a090b070507050d0e0321160b09010f0b0913 70
    0xf1038880060340e821400c82030b100c00200013805190305003c0c4c0076084a10030540d5400b84541400100048207d948000b001d07100d6640d90415143c85500d4280d00c3c2a106070002006038034010604400040004090300703074114200c0312007145d83c60900040d541c0741e641000194021074070042c107101064241d0490040060042096208030b022070b481100d0139041510126030560321050355156040c3d00d40200100b002401d00505912450300300b000e0441c0070076404441c01194003101241c0c00b103014916900c480b9003541e9115507a844c1003244001040b000d0b080d100524041c007200454075040124109040040e1061144a80301c8502c00b40040c06070001c0954515a40741c00c0c29400041e01090061b025110580701c2545800d81c515005003003a4031a000d58007005402c042c10300083c1d8000504146940350002241400c54150180c1c1d18540f240380c68000783e90390450021010002610342c81c51081d003000703008008803100c0d507410606482c0c014640d907a000081e20041500300001c000d0816085100d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 499991393 1250 499990143 499990199
    0x3020f030a080411030f031b07091a030f06270c22060e061e01030b210c030f0706121812020105071707030917040e061903020a 56
    0x12454034a164401c1d414030380000d0404041c081046806003150240001c200c019040c881c5003c4035071366480c0901c034942c40340c48000c5252132484802c1400034602920301c0e540c003404241080040700900718084d4031118000e100c0c00c030041071105c8000c5011809410720075450b4601142d44040751210922172000c42d0302c2c1e8040d103a0100d62552350340200400e04d100164544c0400008091b0500888080d5800501210307408000c20986540d20b480c2c03100380c151000f080b030319013004000048000b410620b03a095040611104014a50841d00d034448a030070399010300701c0300d1683d203400501d521459107001c181d010360b10441d03040c40018010800d0011707820000c040014139144c0109180c00e82c1001a07c01e40d8460300210504a900340e0a00034654001d5190030505000510406006038104d00107002604060740d80005200304507585107600c01000c0d0040074142c846495a01640c1200c03802e4441500c241c412821403190801034103507031011203800078041218545800c0c2e80140414010360101224210703 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 499992643 1250 499991393 499991413
    0xf0f010311030106020601051e01051b150a0b0f041802150d02040b1806090f04020d1404080d05010e0405030706020307050c010e0d091a0d0209030c3609060f040302 72
    0x401c00246009024503030041000e940b620091044104103420f1503803440d02c0c0c0c000b40382040d90b0444110b683c40701d140c103083d1402101c103000703650030001c10408152070300f1121418410340102a42000d500500c044a60740d408100b460100310846094103400303410030780c0100b0140003501d00b07454801c8111a0a0000c46e103449001c1d6907040c00c981c010b800075900c024010035910b0307100041080e4030903090b03402c2d17455501c0c048410703000400041c00035103030600c035030380000e944003183c071180d04400103504000d120800d89003481d00e0517610540280d00c102c1003552400d800000c0c0c0d6480d08000714000c58004000d140fa00b541c070b40750900030754030040c9050280501005a20003800091045640c00f80304800649415105804000d003010400d074131512406000c030302c000300d1003080d00341115280e05540b500140c0e1926100d001c01c1c14151003c9905500004000d10502c501082d11a0880b00103e1045800900a40d61044013001d01e01980c8403041e550241000a40d0744002103034007500300340a80101d90070554 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 499993893 1250 499992643 499992671
    0x109031205090f0718020c070308070303110f0d15270e01050f070315150203030702011a0a050420070c06030e03130524190905040903140a030b03070e0f150f0f0103 72
    0x2080c1c9e00440341e04100258080600d60b052207806054425000c040c0d20b031480511020401d8040c0d601900c60b01551051445c11001030501510001d040b064a0b419010300c2c06000265007521221078405d00608008600d03640103010f1040302d01c66410540ca04245031a5994200c00506518003060585040000041000008500540d819018540c01907a9034680114001c1c20349100750400d1403204000b42c9402c600359940545c80d0240e40c0180c070002011850742540c4050b20181d54400d800b038070000100034007070106070b040c2a4180c4055071006d201c0d6000d4111a1aa07034405e00ea419035248400070006d10007454000c4140c00c1d11141e8031f008034100107008a03482407540c003c640b10603d0300d09100c2d041c2c24854001c43d2010040c041200c00300301301c004640380504801c010164003154103000040b6002c03550300a502c084584c00307001c1c08403842c2c2a290400c424080405441441d0340c07a21030710003e44042d800e07104544078150054044082c1100b00d0050200c0c03009401d1990b8103143c2c40e440304010042c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 499995143 1250 499993893 499993903
    0x210d06030c1212020a0503190212030a060303020706091212020c090703060501020c01080c0301090209030a05160f05040b100e040e031305120a030203040b030601110109031205090f0718020c 83
    0x32000d2081c10040300300710f02d85888100600d0940505541210301d06801041d8080181c5500803281c03405e20b91020403186e4100d091540c9190000b04600b03010060120140c196030184003a2803094085400b041c1d1201c03010348003910301d80f0502031600315121400c000103180030a8180348070f6a0740122041c003a554400200104c0c0c0490340040040c2d41c46108100303560381000040c0d2218030a0034050064100344869030b19512050080d1a03000703800188245003501c1c2007101c1903105400500303503064546040c40c484a00c00e81e40c4034003600103a8000c000f140519181c40381252081c0f00a02d02c00240d03413540c0090b11544040740049038059503a03130302c14034606000e0008080955403240c1c0105031504007401c014210b08203002c90449540640030742d01c0000c1e0000120b60540e4402d21403d034803a030701c03800101c4400c81030f01f4200e441d65003400b07103140415030424a111541110300d84180282d5035002641c0e0354036a0440c003a050030303510808003044400c500c4503d80680e11401c840261030400a400590702d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 499996393 1250 499995143 499995149
    0x12080c01090f0209060d0201080f0403020f0d12050a0501050105121b1c061202090406052508060a050f031513080703091403031e0d060e01080717210d06030c 69
    0x1100d82c290b800382103281c01228254040e108403491402d05420341c0000303029613030082800740640c0f24040400d013414001c10107504c00c110300c04100c8000c401a18002015031214400100c441410640401c075640da01d4014941070b550107070350740ba041481180c1003020a2030040c0c0f80802d5070862a48034200c00b146003004042c20405000300640c000c081c4200d020441e035059100f28103c0b180041e00c240180d6401c0402034205400040c081841e84039000f454049001e240181c40300c4030911002ca21250b500501c5241c0b1a050171221080d0090b600d40500522064280303403203905801c0381000a888000140310360f9000030a01540d400c0c4403140b40c0d00e001c6154400c000640c00300781c201d0000c0040c08880c00391416100c3c3c2c1a4055410280513003907414500380003003940f64a81f100070450b04001c084541c05000100301600c00a211943c1d54108141c56881078014840c0556050300f4442400b80c00282d01002a44415480d1881030616a001035640c0c10603200025181d1b00c414000000c00c20030b542d11409 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 499997643 1250 499996393 499996403
    0x31a190f0209090c030601300f050405060906060603011809021306080717060601030c0e1e030c040204080601060c1b060509041a01090302040c03021e03060a06021612080c0109 77
    0x25809030340d0100000f082004010000d588020403c003e01c50764421050840841a6521120410300c440340038031400c6030354144065842d1a22040c0c0d481c43c90941c01690046004206850054450031103050722038004454407034216108100410143c0c181c02d01981c1c40a02c0b200d40004c0c500c61682c0000c0b0903010746c4c40304080b010f403100d9007070259200900c8100c0c020162031401c8400f12501c2c042164031400001c0009041c1aa40d1072180721042c000c41020400c010010501c06001c071100f58030300050480c10301a40d0207413107400301815540c101403080383c083c0d07031a00c4002c0c42503a00e05201211301d01c05818003114110380b00195180071b90140c84122000c0e02803074441a403212401c1d070601049954650200e00024144000346003181d0f006440e86041da501a100402d441005683c1940a4407076207a01d180410820134808030100000c5001d5070103008200c403110141c554030402243c0e540e1a4010401410104441c00c00c010004c070300340326000340d10540100b03050090741d100e05401c64604507015a4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 499998893 1250 499997643 499997647
    0x90203030c011a01050301030f0204020f042115020c0303040b09150702030d05060a03080a230403050703050606010201060608130201020a0c0810272603160801050a031a190f02 77
    0x80444000210f8800c1010031310307106085600d581c072028140300502c03401a00456001074000c000580c0002100d000e8500384030100f80310041c00900c1036180b205503400340c0e005004500107800c07070310490003242e030813004c0340d0000c5003107458a88032154480c40c09400c056841c45032040c50026600400c04040c40780516402035901c1d50741040e400c10580f50001d001f58030400310307001d0a10004900303c050301d9240da118a0028940c041c0f00c3d048601d901c2104803401034010010800004101c0000f841070b0589201d0001e0303c0450701c50b0390040e4280d4031035001d0385e0040343c5484d0000e901c0540312090490841e005104071122201c0c0c0741c0328980e000e201500604a180c12480a001d600a00350090300030383c0002d40285441c5246044001c4141c04c458807000300500c02c40440d07660b2280c05041d040d03540902c105403c5549051980e1100f085070b89244070310000c41c1e6140f00004482c5000400c10040366003000000c90b100460080c1c500400341e004100c09041d29182640002494075440b451407840c0120100503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 500000000 1107 499998893 499998911
    0x6081003051f0b060c0a0308280e0d022821020d090803030f06060a03090b0405030301080f03040f05041d0a0f0b0705070b0c030a090203030c01 63
    0x5021403082c0500102c0d03180441112040032280e0000802c080038840c0140090f50050781400d0b52550010f05010000c00d000b01003e5600c150400d00220005010110b040c135074140103c101c406066a891540c00d1502c1c042003040d42456603400101000302d5107c81700b071515042c04460f2b801c1904440042401c03c19004800184560b00203040c481502d114003001f507990002d207038594000740504000040c100004400c4030b004100c0300492255a0f9a80707030a00126510600400301019911b03100c2c400030074221044640214401d501a659952401540f06c2c6413641c42c20b60764080740c10400c410440195401c1480b0200c035000e84002c1038490710300700380c0100c4c00341ca1902214940604100d0100f00042d9052945d402807154100028a03265100102c80713901034402d00400d68040d90010642024042c0059607104c06c0300c590200e1422056400b003400c603005949600c5903691500010 = true := by decide +kernel

theorem cover : BRFrame.Cov 499820143 500000000 := by
  have h0 := BRFrame.cov_init 499820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 499820143 ≤ n) (h2 : n < 500000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
