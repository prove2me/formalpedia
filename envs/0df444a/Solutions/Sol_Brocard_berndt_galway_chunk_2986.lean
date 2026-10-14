-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2986
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:19:38.605404+00:00
-- url     : https://prove2.me/submissions/d9a28a82-d07c-4495-b28d-adfd32002c0a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 536870503 ≤ n < 537050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 536871753 1250 536870503 536870513
    0x15060405240f070b0106021b060c0f0a060c020c0909070b03100b0f0306040513020d110409080d060e010e10050108190e070f050a050109030b06060c07030308090d08070804020d02030118 81
    0x81c02e43c4501441066030390381d0345d0301401d036190b40b00d9413022042e904071066504098201a00284403400c82e0000b118510640303a0046801c0c80140c010071500301e5100d1008004103941000708010380e0350102da20b440030b801c1c4040d400b6a52801d0340300d224005c3e0f00200014204031100e41c11034009040912009507103012906401d601c941c400c5a181b032080d40b8005c0480d440c54884906080c5c1d0326070151000319101000c0d1620b035092002030024650042e11040d07410b0014030204007a1524018007030003c102d80303007001000c189841c0160801180c011030741c801c01c68150120f550340301c11541c007030a100074251100716032260302982c146c0d0840081c908000e05081014800201c030400c507510034401c108215124070800c4014601e522610340014080002031011400303164146400060082c440c41c6054290f0bc460703814000f081e40283c0c0450400010006880018030541c0c111a0b6949010000e03881e00c0080945041d00c041c0010b40202ea0600f166011074400358400c81c03007220700408284030100e092030a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 536873003 1250 536871753 536871757
    0x706050901060b0f070201082206020c010c020c06270a1509050609030705090a09020414090114040c030b0402190b0414030a03090506030a090602180915060405240f 72
    0x5444940c42c148001038607290740c40555011111810a081c034201c01c0e0340046550301d101820401c50440c8a021084444207070258405a0768410340c1b016840c2c0c001512045e0864602042c41d10554003c59a60102c40c6e8424040311000407090b00b00420302c41401caa2180c50303442c8810340c139400031407000740403440503404941c601001880381d8482d08200c1c4c983d4140001402581d0b910b5405520414050117585489208158400c80d0f402001031a00d40076000617003600d20740c41d0b013072101c0000036050101080c0280200308070781c01103218451607800e07c3c0da945001058a44000340c1004198000b003011076807248660b1014000484d126010961154071042c2c8580c8140300700c40c0c200310390450886942c28041203e041680c1c168458104103407800c5c080c442d0039032000380010465503580c442200020410320251040551380c44c0042a40d000342024851445800782c6032110100e001c900008513036131000102d800740c1d4800d46081410888035140048111240d21246524080109001c0080e008040c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 536874253 1250 536873003 536873011
    0x504060501090c0216060e0d23060a051b09010513030b070216080303010905102309060d111005130e0f010b0f0703030c0905090703090506061804120212070605 70
    0x8020002615070003c10f1783c1d505c840100710229021840403c10a190042c14083d0190340c0103090b503002d44490703665001981d44c9119000c0640c5a00d1400f4490fa54010851254000d01c50070701040103050002000c6e016030f64800e00a8085500081c030100b0300d0340719100b5540500b600c00c441000854407441c066855800440c0c0c00d030010300c24201d4410380c844c01c8152080c215980c21001d9880d59003000300c1140542401004840e41d40b40000e00007404000c900241c10981c019a0040440140d0b41c0c03041094030f00d406003400d4800d9803500030a00200b4903040e02a002400c045891101d1000601d8003503505015440340240100c80d010800111918140d01107440b6071914890400e00303070b0300c50380150340c0b038022402075406440052040c01d00282c000c0c0d01845403908a41010f259582e610400036803001000c9910740e0019407200f00500402104204454114800b00d903a49009814404103042c840001040503001a41e00030000790381900a010b104022032001c0d124595940c058281100580000e032 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 536875503 1250 536874253 536874269
    0xa0533040f0213110706090c05060a030c02010f06061209031209030201020910034101090f0c1b0308060d060504120e0a0501080601030c0215070c0c0b0306010c02100c060504060501 79
    0x28081c204040d03513202e80200d441c1884078860030442d5688070352008100d85a07003180c2031200b010307000c1195541d0102801494010750781c040352040c4a00b2001f420b44500000701e020f5281014410700203650400340038218a0b00003074001800c40994101201c0131f0550100780e003881450103240009265042d0018088101c054851140f980d41004d8118201e850b058082043c51000303052800c5483e0b44040c3d241d2a418540b10300c00c10112040040b80700510307082e40002041a40d400d2151078145803400b41b01000003560800707a00b240364002c0c1e8171000d0941e858009040101d40d9000410680d1030b40d69030310b02c1d282c000c081088185042d180400e001000001507070007040744281c5101c460715215014100391032060b581d001443d281d420056014005048280040d0702031b20700380d080801d00c810b040794410303a85640c0c2c00c50504103c3c10030200701100c1c0c4d044205410410410000141d802c0b000d482056641907480c80000b11021504603034000c0d03404e20050a01e03060105110901119400c0340741601c0c820 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 536876753 1250 536875503 536875519
    0x110114041205150c16080d020310080d0c0b01060302132102310509150906060a0b0903121312110906040e0d11240103030e030a0533040f02 61
    0xd400c0e6072101841120f101d004c8400c2040801101c2c040118000481842404002c2c00c015840003100305a0700121510201074400440802c2200000c001c04800f84101e42090380b6030030926200c400200905000d41030500d41c0010340e1a1b1407443c0305100c80f006240801865201c03c0c9100c00c40049078250080582c440c804d50f104c0d820040241a68600c47c0044204110340c16560592554024210080284d01c2c90b001d40d154107040450504030041c440d03014600900b41c02e1030072008009500d145c64005500c01c0d8420304c024412170710b00050b0b21207843c00079984641c81c1e4100c109040315080c030f20f800c071040785258000036108010780140300c0c0c2c001c59811038004c44590341d1503003400100e400006440400c0e0b0302c8540c048000fa8000c2c0060701c1c1c2e0004040661782d04c0190701019003210b00040140030351203041540100141a400301212407200030440c094030072100a83c81c0e05503a050031100000f80001d08680010b0300145001c401850141c02c03c2200e10107281c9400e2601e440d1201e45426405255a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 536878003 1250 536876753 536876773
    0x2709010b150403150207080c1509010902150705011d0f0d0804020d0f060b06220e0613020f120103080a080901060501200118050706030e0d0c110114041205 68
    0x440c41007000005598142410a40380d80c444460704149224034003030710f550801058021800d403000130140c04a00600900451246094104c81a24001e1244a10764900746200c40160303162032800101e0a242c18500b9190761607070801d00d006290105040811034029044009081d10100d5145012200f03c0240e80c918610240c00303031680d240840e0001c0d0301440e054404030010725040c0d94402814043c10000940f2024a00444d880c1e6100308411b00b888801452030100800708411404003400c2500c1c0e0303101e00c90600c94045107414184100d44818240c011591990310001d072004e89450702d25200f00c2031601d503560304082c0702c10340c0b101c00e440f030024003070500140252205006c0c213000c40354107941d00109540f40354100400b403820000110069500c420b0916164401104c80b05082030003a0080c014080c80c260001e41103480c1c1c0440246560005030740c03094080d80202c201c0300a035800003000317002c640030400100c604140da81000882810041000f16000e246084031213200e0384150300311029001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 536879253 1250 536878003 536878009
    0x1080c030a03120504170c0c09370b04060b030105040c08010b0a210906061707051005030a1805060702160f09230f33040b2709010b 58
    0x3141c5000500030480c4103c04100340030742e41d804243e01030300880f504c603c03540c0502c01000f0349902c1508541c186501100d40644580782c00ca5049030000440750030118200e90425001400501945545683c6140303645000031b07161040c2c0120f1030b48500203004220507500c540084816410a02559024a26140c0320341e400394001c45415050761008416641008089a81150718000550081c007000c0740590404000240d107016000700e09201300000b09200741410001d600d81e00088282c2e641d20742c031900003004181c60f045114040c400302450200d42d60354a5080103000352070041c1d41002044001003c9005212021503214010303540ca50039201400079610317040004281c18007980005180410040018525950040c07100c0c030721000f01d1544042010301c2030504110100d65810062060703a0400c090001000788020f00038008020176410602450303003040c0405c9074040280d008599441c05420103548183d618445a0090511120650805801d80c015002c0549204d0055803c000d07070032000389 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 536880503 1250 536879253 536879263
    0x120e03010207050c060c010e060906090d090f06030b061b06101205070e04060b060a1815080f0601020c0d03090f0b03060904060f110406110607140d09022701080c03 72
    0x41e070040f000704811180102080f507184c0c001c02e1020200d42d41c1d81701031041d00c1d40c1131000c135224020441c050b141c0c62905640c09424441d0b04649202040a0350700148011001030328408150360403450002125503050001c140c030380c0324404801c4015406c4200580e8042c0e000102c1c1880703400c45910f00d41c1c94603500c402031400d1100016008205803c50300051147c0c0440d60f000c541c0c1300303001e1400401d00d009070002081c103650005551100042c0240160201c00c016210008001d2241622010300341381c1c10140201015409400042802062404504d03e81e1080040c1410040014203c00001c1e88601c1c0180c45000a48122000c043d0600c20006200b034406040c3d07813080c0806440341d9080d03a00d569800c1300402c0200c443c1e52510740e648206010801d07900e000b03000600003548030f640c25603000d20707620380c074114005140e0400c0012440d503000180c00e1403400d0f0390f40000444004201c48110b032001036a000103a0144994541101e403075a540340030b0509801d170480310b4140030340b20f410070030a040c542c44d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 536881753 1250 536880503 536880517
    0x120f041401050c071119081014071e210b1807021c090e040812060307180c090e0f0601270501081f0602030310080a0210050f0d09120e030102 62
    0x4009000240110385d038802c101d01c2c0c0c0030006089120b45101007580b10a0382c40c1542244003998405d02c00c41c004440c1070710944003803200c000d03210452031a061000a2500110290b01042c850014000c0e0080038003480d281c0041e820040c901c1043c1652252a020081c0b41602d0345910070414001c000720826546c0c01f80340e002c0e14260f40a800c81c40600e041041c910356992092a00b0000070b4000011000a408186030007a4401d142e0540da603004880e0b4502e09c0c9038042d002c0c0b4481c0e003100c0000c0003040301ea803100b4009000d800401013500445000e06443d0b12102d54013800e04080c0c04c2c5e00708114018121141d034030446091300e0f0762810409041007801070f48040da420b4500d021030040709000941c014032206520481140c43c1038103107050040001c034041503aa00c0740340503a001000784040c8403541c09030744000d40400c00003070200c1261a00020500242c1714010028040000340409000740f000f01122050300c181c070418040101c481c43d1002c5034144a000000002d205088038650500d018022600d00c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 536883003 1250 536881753 536881771
    0xc010305090304050d080f0d050f181c0e040518010509070f0315060801090b0a0506010c03021011040f060509130216151803030b090610050a14120f04140105 69
    0x429040005020014100c030310300b903a4403003043c001c1d0322070410600000d041103108e000010615007030000e052884c42d01c000c1c1110380000100054115848c0d00011222038103030000b072541040100280f82900e1400310711010300e400c1070030039040002c2c070343d10541c4460f00140c401d0300811156803418000c2d0385804072801403e0034a0589001007020542c00294801842107100b0000350701a91114803508541c5a0300d0708607451000c4e40d081084c03080e20b5100e59a40404203080000c2d450240b43d030000c1d240d054201a1070481b6a48204e0411420305800030b6a0203002d074075660101d0f29803503032000351094000c075007190b20400c45003604228401d060f0003614018007522079010400d0341c01d996284c0300514040d000014041e650352503d07286021006e9001807003402910001a001c11000070f03c9803080e00100350718060306a018030403c5003940082100c96421040c90802c001c1000941c50041d0b6105002c002c25804100c203060010040741100d00303600441c49500b006918151000304c880c280d400460f02025 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 536884253 1250 536883003 536883007
    0x6080402130507081503030d29030309130207170c0304080105070507030504030605151c0308090c0a031b05031c110106050a1202040603020a0603050708090f1207060228020c0103050903 81
    0xd40c3c40300800c80c04445c420080030340c0d040411031800c40d01101c0141901501e8042d240351081c2c0b406580221554840070107601a40c0b41644003c080f4162205c5000300c841440e03400605041801002c6c0400100300d1b50554246030365007800380c035044c0d882d0003500070348006502c0c200c0850049400341049540c001e9040d1991402c040c5541c417070000500300201503003095510050b8403204e941e15642c258402e0705d00640407042002c41818000c04010b4024101c0c26141e200600101c440d0782c8000d4140104d03680055803c00c03070104070000203400c0c00180d22a60b0140b044840c603609441098006c0070100356203550b8001a8040d910b0018203807620380c86400c0d003002808105010410040c4004003101e40098008959a41c3c0e95010808040413070384400000b039910001e1240c500d41c06880c640d082102071000303081004003204c820380c48849507440740320700d0140042c1d80b104000d1181c060710301c42c102d0000c0c03803021441035882d1400d04554010702c4600500410786c1c0a2802d6000b803203400d006d0745c08080254 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 536885503 1250 536884253 536884261
    0x5030a180f031203020c060a0213050306042001021203040c05040513120311040b0d020901030c140f030402010e030d1709010e0606040506040b030f010b0f181b130608040213050708 79
    0x3000c080414403880416801b0000d0000c002010030005000340d811070740c0181c1c1c4950f1050030341300e40e031441d4118078400d40005045c040400c1000c030030383c10310720f44124540c0514140100103030702d400c4024002c022454008030410050042c500f00720b0048684c1a502404150b0325540442c2d10072146003030091000b403a80c4e00c2c10581d0781c8250b0101c0f2070f48014000c218038098480e8460003150708820380380322085800044200c0c507942d0600451b4001e498038101441000d840200f0a10385014180c0100c00e41c01e0b012000406582c400d50307140815080145c1520441b0005080c0101000c00c2c0001e07914515006002080d00744105100b01c40243c0b41c8a00600029151365080002403d000740c21943d000b503e5072202e4680c3d0717405104004465202c10300004010200005211110411202c40c92041c1e60152000003419010410f0a6001c1c0c1c07208001940c001c2400c1070001c507070051003e00707103807070010080c045402074200300200e0042e8000c40e828600314084401c1c81c03080c0c13001208c0910000300b00c00046 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 536886753 1250 536885503 536885513
    0xa05100501111b120a2f0109030f0c0e132310050405100606111014060105030414030a021f061202011103040905240306010e19061205030a180f03 64
    0x245400000503e100049029211010310b0700544240980c0c5a0001d55088003070840528541030071242031070700a03024585506e0018102590034400070b000869513103000d034100840c1c01c0c2940094007800c9070050340350415840348140c440e8401030458070398841c0258203000782059007114a819905100900c0c00d01d5040190b1805814042c00c1210240b107040d10340c0350400414001e40e005069540d030b480c1c003100c540c61141482d0004040c10401c400789001d000d024200e04041c02c103a4071070000c2c00c115549444510300403402092941d4401018000130406066007580410054000c25140e44860902002c2c60031902c1100c0d81031040910302081810400c00550041c20f1142444142d40b0680e418192340d009000203036a41204e400091029040a1800704030321004408101c1030182e000341020340c18071284051402018008c1456065000d514201700700c8d050300700401810444202c80f421203054070b0700c0d5507250460304038000454525001102c807421034200340740484154954640500d4a10f07150 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 536888003 1250 536886753 536886793
    0x41104050f01210e0c0303070f120806060315060c07030b060429100c14010603030809030c0c040b0a0302040213030b011706040602070c050907020a060606020f0618030903060a0510050111 82
    0x5003a13503009141409040ea5020f002501030f6601600055000b110350349040c0070310380d550002e500203100e50102400142e885441c1580c0d8041610312918010315400400207500c2e0040080010240c45a00008020022007401041c060682510103021980e240c0c0e000c00d80f10356210101e85c3c2003c00d1038641020078580032400c41054451410849402085c544444041c03046280f265225a0f445080070030816510441c0d140d40146c1401c040c60034a4540c480c1c454484400920007489652201d180d1100b40d90340761840d2000751350040c021175440140c60301c607a1032600240720648040447c0783c00084e0205641000f040000d02c0140506115591552940000d4120600640b10310815840226441e240c406185004000580050015142c646414800d85034180c0014085411000070b0060300780b00000c050340c02c50700411b00706003a420000f400310b00d5401004100f50b40f600c40d0300c2c203004130220300340d1083d4020102c45640c6900162103400660700800320030103481d0a5444913012812406250f01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 536889253 1250 536888003 536888021
    0x305251e020f21070212060103110618010e010224190e060408070807080406030905010f0e2107050111030a0c090e0106080402030f01051608060a0b190509041104050f0121 75
    0x3c10142400c0340c0c1d802040c4140904101464991300400040c003c0c480c00719403030100c00c10129545464400d21202a2075240c2102c0c00c0d29060002e40c0314028810b80c000e01030b900c8082c8103100d0a08462181114082000301e060704d160426aa459000c401144294068421024103c070000c0c880ca0b22142c1d030310317081035218490903030f000481030041500080341d00005000401850340d0101b00040c284c10450b003103d0313150248840c0c00b071070300416060550010078005503c9200c9411400c0d01640890204054881c000c1c0c000e1071940b1300411a5610201d10020318003612580400304415103240030195000ea06170b004146440e044800100405445440007a0348a4805015030701070101007803105080d0b0f0401e5a5424040200f0b8424101080d8860801c50b40501c044840100c8245400c40240361440380340c40c440017400c45d03c0300c2c040b04c00e40504121035100c01c0c0130b1f0042000221005d2180029001401294131030031079001912940e40c0301c1c0050000344035001c10b40200c0000001900c0004048200c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 536890503 1250 536889253 536889313
    0x1502010204050a09060306140f0105060d0b06161202010203010807140f10090515090d0b043306091505190503100608010e0703120305251e020f 63
    0x20400ea22030a16020081c004d221000c1403003815031400c03906480071480c03401c442d60041b0040186091159810b18110380c020381c0c1c900c0d910949000a4005800b003c01e032581c0026002810b515503074a40300715150020f001d841c04500002501404070700340d03c8203124545195002601c28880300d4082080804540f42c001c240443c6002d4400102d60705107444490328004c1503080b4400c00080c240002580c901c0c0041c0ca60790361500008030001054200203031005400812400006801c0241403942020710380d01e442d480c035000c65800c005442040d4240d0f010080558203000000070315602d40e000340c8801c68601400351240a04103014400380040c80440c2a00300f410b031071720020301500e05202540d07248129410126a85060462031403c0d600b0b042e0000380654000c030b03c03c00108071036407114422081580390104e4a91104801421444500310030720041000d01410101c00c1c40d00600c80d00d8900078082d040301c0c1c0280300362030160307110300d0840031040098129212210720078140030201c85511101c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 536891753 1250 536890503 536890507
    0x4080f07051512070c3003020408071a040305030705060103150b090f060a0f090f0c17070c051501081005071d010c06111b010e0105010f0504050a0b060a020d080c0405010915020102 79
    0x41d140d84c00c400da406010800310400507031000e0300e280110789801b500d40805040071340c0790502d080e80a0b690350b1454807400c0700091000034655040854502110300650700081141e03107521490910365110352017072000301c1d0002140e2492801416040c0034102e11154028001e600c555184215141640c8000340060303031250151a020941c0342c840d9801201170f1070408000901c6440c0c406038a000c590005400c682423101e04891081c189540c0c401042d842a124500484c58050f42d2401515007070292000d201641c1d0003000201d444440040c00041c00524840240100e8954620a444525800c20340c004010304500b80c0e1a120b50107034000004152040314000740e0301c015440c1006c40c5821012410f4800c14000003c0006440c0c00d009040d5100340307440003003150354540310350716108403c0383c4103ca00598a4400203030365110503900641003409c000d00420b584181c51180251260034004c641404a502203000c41c103900e02a1055a007920381c1a140c01c000c075402c0041015810400e003d55804640d02 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 536893003 1250 536891753 536891777
    0x40501350106120201020c03011116080702040f0b012309100c0507080f06151003090501090606030b090d0e06030a022a150a0504030f11011104080f0705151207 70
    0xd02c00e4000601d1080003054148a4038400207082203000003403e07100341e041005121030740540c18101e505d90781c0d00300a103852000f024608104907000f01d941c041d5026240030b960410346119908600001c039026a18040b00402500584500b40c410b00842031140405010880882c00e001c248003408694034203200090180d140c2d40e640c5010400d03004084250820f21815406000c1040350940101c0d000f001c1c030301d010182c0c80216000980003414601059220341d000c0080c00030030740c400c00006400510030b2012a840e400c249109002c103407140c404503c10009046291841045881c00c01c1400601c2e061643c2c503201a1100603400c5403040c59504031802504142c00d031400e1218154407550b440280208255441c481101030318000c048100c0313182001d040000096215030003044400803810300c164a208580070103401000080300c81710349103800080104200f0400901c210150401d18102c4e2103080d180e00030720030105240e0060000c256020f11400440c10102c2150550200ca945852081950 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 536894253 1250 536893003 536893109
    0xa050408060a0e010b0634080d05010315090c1e270b1c02040903110d051b0304030213090203120f072a03030e0d050a03021b040501 58
    0x10940e18207991560754038a40c18a524280609180e545c0c00300e811608200c12406004048a2080708454902e14000c052102a40358000c404108982010406450307007c4501e42c04010030083c00240c0e0540d0080c1c0b5031141c034020b40d0140100455021442c004842d250005510841d0411480c83d02d8100010502113900e0024000340c0c202a074400740200d0b115035050003280c4c211541b000b48117002d52013251401c1014401c10900c01c01441c0e064800003074804150030101d581e282d0111440409006070384403c6c284036413050251801200010f90101e08841030018142e1300e101c2c921000303400000307031120032805100341d600c420704940c006420f50303084c40040d42c0b0b46040359210b814580f18030507000c11920700340701c4400c6070306070000c0c1e1020101503807000c032920580303084140d840010201f0030200b502071120780b00e050100301c0c20f50340714040740c0400f070341c5140294581950107000400c0004000e0701c489245024080d8a048884a10008614214180404d074000c540e204003d21b600c092030b40d040000070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 536895503 1250 536894253 536894263
    0x7060b0d081806090a15030f330e190b0405040c0e070207260c06032508010b0406050d14090f010b0301020c03030708090a050f0d0f051303080a050408 66
    0x107442290000d540300e00307901c800300b031145054018a0258800740014035040d01c607640d5141c00c0d12a8a140400042c0d0310800407809020341d400c0c04072072070342020b842c20300340810f8580c81c0b890020b00e12401c00c044051101410b480d01250300c6403d03440e400e6103022400b0392042240482181e407003424085980c803040e0300400c00751403003500c04880e201c500c080108815115050000c2e00700f1030750b101401c0b03d24074000151540300361521500030100440c0307403c1914140b04200b8403040a001410141d282e260640c502d003041c021904048075808a40340c42100c80c14402d40b1030f50b042c0c0300b04800309030a007400c1140c220342d603070021840450000e940780048945000c441064500c56041000203002d00e019140c541030954400c008424040e07030040c40285100380b004820f4a07440122850110f00c81d80d154500036107400c040b00400751403806541c0e01e07041c44860100312486c40d00c2e20340d1100c80c440443c503001100d1b50310503254031441c0103a000f0030904c0005e510300003c00d040449494540d05068540504500300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 536896753 1250 536895503 536895529
    0x11030304350f070303181a0606090409080c06060111030d0221090a02040c0c03120c0c0b040302011505151b0c220510030807030804020d060903360b07060b 68
    0x2205020544004050703140c05403400386ca01c2d195030b2400004080e42c0d4541050280720300400c0200c0f501c000a8a143c442d501541c10081008105004104c59802d0018a80c1e00001b040501ca020303020014803c0c0d402040200d6504003210025840c2c42101080f0742d000303401c80c06100d10280d0360940c3e408042010b4050707086c09507031098040c105d660070750302c1080b040f100006c55a00a01440042c4440400e4110061200060540c2c83c041403070545100100c4402890700d6005021100300340601c010300d0307415401480707001c01e1180d60b03019180c1c40c0d5041000c0d8a01110700002c08840c10080068440f160401d40400c2e810711000b113403010300d4001c0001304ea00d41b07140918400050300c20341516450781103004090300407408006c3c06900d1401d50f11008441d200d07011014080c0a82c160110b011500c402d00c802090300d4200c3d03000c1040c4a118580240311960340e00704c0c0213643d0304002c000f0703c9061940d0004084550030b03003041c00305103140020004a86e00082015035a15541d00d01510f840d840310030036200340b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 536898003 1250 536896753 536896777
    0x601090e04050d090929030f0d051305061c0b030a0507150801120f02100918090201021507020319020709140108160602071206020903070906061103030435 68
    0x40c0382104440245200f61960000c41d802d820f046100c8422021120886c8220005200c01080001c0d81d1007c64600342e22010451881c0c82041480011941c2c0b02d4081d01e189508403442d101000e50f940100710080c0111119500a2505640c007240e0300074465204044101014080c1d07050340b2665191141845160f91100c8082c8100740e000c01009640300401d00e001d070030b500c490100b4020660b21101d00040c0b40840090284081c0280100c1c03403406003005a004000e081036025040c4202c1e9040c41c0a0b0442007012030140c8284c0c070f0950307110a01d240030b03588941129401141021030b40c000c141e80400e015200501580110100412901494080c900307444c03401b46a8034455525080d80303246000c22440700a00c070001c0321380e8148411607011804c21304403000b400381d003000b8807040d0401030005d224a5003100e0b80f6200390080041e402c2e83c079420020807904161102c0880503403c1c0300d440d440f448110340c0101110420b84c204c0101203032950300004995120000000d0b0100d00d9006100a54080080401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 536899253 1250 536898003 536898013
    0x9050706030b100318080c07090204060c0210081506090111030c030301051008091f060b0a08061003020c06061002011401120c06050406320a030203180f03040e0601090e0405 76
    0x20b15814610404049000d80d03150421000c81c07510b42103a04162400c1000344443e50000c1e00000d1030394200f21701005041d10400843d035a5a4a00c00904201c942c52070890054000581c8a600c25000d0f4404920a15002c900200c461021a040200d964403900f03099052103035240f5094980341081001e01440000ca100455503941880208846503400c18218010001170004100c0074550104402a41800030000c1c041c54a0303961140c180902506c1d000b04183d50004201809456407109001e03005180644481c103240200303031400c030264403441011040c1d903440784004c90750714240000d08c03403d440d00500c0001341040c0d0b0076640354583c120a9201800310f641d0401090244503012200c04000c00c501e0810a00d418904a00a40101c1140d4081010308001c6110344500003020700340d18004584c2040e003259501a9083c001d00290801d882e9030031242c2c110700c420b05020000241c1c1035038440d820002035007000d00e4130790020300c4a00b00901d42410464050000117030b4900c3c1e030503468003441c410301c0070302 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 536900503 1250 536899253 536899271
    0x30622151104030803090705150a080402011b050618060c1806042408090a0201090e061302040803120901020c0303190207050a0303050103030e040501150f1103161203060f060e040905070603 83
    0x47c40e00c00ca03604420300c0b8420700d15800303210202c0c17901165442e1485090842c02d0765510b00068070611502031216146070340034007070300f020058040b0750340d4416110066802403031807035480c08950b1210111610307801e4803420010100a510a02d0103003c25460042041e85401e4950059a85402d0514038628060310000311403001c3c140c104d2801c030350102025000705000700240c0c0008156217814403440078040241404031703a543e1208421000f12050780001595a590b680034100d540703500c50100d894030741c451200400c4d040d44040c001c46a0f10300c021030085046807116101604411181c1000740d498941c00c000030400290203001d2a100b13140280c400285561450030068000d581070f880c0036104924140060000c02d602c9943c44c503000d0410303c0c1c941042d5440d0041500d850899080c94003070b500c000b00c0c000701129070100104002a20545506245c00d0900388140c007610818000c40c614200d4015080c03060520032203030859145402440401c42482540b101814000d054022000103500c500002d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 536901753 1250 536900503 536900521
    0x1260f0a1515170319020303061206011208030603030d090309090b190b0307170406150b1213030e040207030e010e03030906090409141b030622151104030803 69
    0x2000701c0d40ea00e0406100d001e0708240101ca44003254051881d002c400380c900304484003030400640760115001420300314400c0034100082c1d030f01e403c219641c82c4980025040d0005010b00494035504030343c1d4100c401e01c820525075075645d075550401840141c040c8001e1102c501000118003030001641c3c001d03114074444604142c65401500c0600c986540601c0c51114000d0200f2030b1200303004100c8d8070400c0116100d03152054210780003140c05c240c0d914411820410300052149550000140501101035800b456903680d004460380d0066901c214080842080010004840a000b44107028400d160500d5a030012900207012a08074403c10b40000e079402940b44481d5801044518501000714000c5041240800002d543d500c21444618000d94940c150881040030030019140e10008100c00d0303c051002031901c01c0c044030740600b0001c0c070901c10b941c041040c4074841d9030040024542003001c03551a100130744420b904c242040d961464615910082c00542d042c152018101a51042011541d00e00b0010b9007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 536903003 1250 536901753 536901773
    0xd1401050a02210901110c030d061403030414030c040207061a041a040902041103070503071403270a120c0201120b030c130608100c120b01050301260f0a 67
    0xd410001031041042042006101071100c5080f0902c0e000b1101c15034400042501400034001c003901c281a000c10340e190f5003d004806094140c8060000b04402541c41081040b6104a40703e120340540080105010008041401d421002000b808942c0200d42d80070100f802c81e80440700039290a9a1070802d080c5501c1d11400305109803008503018880312400748444208014215142e5109079641c131804002c540341c039041150040899100241c49207060080075050303178130803680d00b0002004400c45400c000320800550707004400640492100246000c900409103c44050b207066030700c81d9011485c001601a40308402d001441d0780d41c072400d000c02d0310025041c8a10042000d8003141007042d00011920005030544002000b1500300ba00304070240f8803c2d0040c420768020785490701504080000d03400854005100d4541d607a552120304d11859404107045030546080e041c009041000100322314100c854072540789510071001441c581d540f10640d00d18041c1501030144580e0868060001801400e401c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 536904253 1250 536903003 536903011
    0x40b090601050a0b0a02010b0307060206091218090408130f06180b0d0b01180801360803090c0a0f050406080304150f0302040806070903050601090c120504020f0d140105 74
    0x100808440d41001c2c009002d600d080d00840d00d01010100700e01d00c480b4030035004003840e1036014080e503d5603070321400c000752a59001c9071200c919100e60040c0300c0401c2d40d0b04040303030402c50301c480c00f44070144d01580401101c002c004c0d10030740d908201400318040320304032000701c0307c0103004080740001210300d801c01c06052420b003d804410b03511132400d010400c1010800848006080b400300009882e90300d0801070729884051008007480182d05d00e00820038074070544c04070310703940741038410001c2d02d46244100c1444c40d642c040c245c294010301c00d00a0b8000943e2a005141c001c2c00440c181d90103000248007250340280340c0ea10400001c260204104503d08203032140030050325013074010b9072400d4180701d01c1000c9111034820b840100310812103400b0b00d652003541a0340c05844ca42d4155486810924002070061242c0c7c0801d40d9a802010000244114a4826551200320a490346440722401d901103400610004005036017242d030ba582d8114041d69840070100c4200d2083da0300d8003280a02d044500d08440c4020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 536905503 1250 536904253 536904271
    0x7270608070c0f060917030f24010c0303090809030d050d0b0f09070f02030f040602030901020f0d120f3201120308040b0907090513031b02010504120317040b040b 71
    0x1205110201d00c0340003540f07600e02c0e04140040b416865074503161401c1c01448124620002c404014030035002c0c20b052030300e80254000c140500e42c2c008030b2800415550040d0b000346000c50000d60454000030302136008852114019610386003890700b000d0119092100391900800020000548070003228124840c0407407492055540703503d42c2d11070001103002c001c405030040c0140440980c145140502c04c00031280c2c1900c03a16203554440f40d0b9044003a60b07039002030504902501500c51750310940c400016040700006565030f90840d01a1308456018001c0040503015804243c03254400074108405500e403500303116185c5810110401c8210b00c00d00aa081a00059685440c030071071100400e602c501c1c01d60f000342d081180c3d0f411a48500e4401d80c502259648007002d00b0781050200090030310b0480b006400303980644c5442c11400c0c0d442d4602415001c10410081c007180050105100d1400c0385910510403d101c3c2c00e0180d40e1aa100340005050003044804562000b106010001000b0704450801e41008243c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 536906753 1250 536905503 536905517
    0x801020c1513170c010b060a0e1f05090402180402040806100e010e0c03090f120a030f14041209030503070b01030c0e0f06040213030b16230d02030727060807 69
    0x903070364074a03114601c195526141d00041640c2c01302d64800e5006500040c0c0060002c2d5aa01c0520320150941d240483c00503c60061480c400e8800d4454070788901180000343d645500d090b030f0301420080203401000d8040180c036080d040800081d1900c0c80100007070210f00000307007140e1400e034031b10001315081a00701810961081004014800e250130b0b0464200d00000041502d0307580340d035890382c58a640c003a44a2030a2244411032010410600000c00d030800e00ba540074042444070303480000c01e90745088240ca160b048204001000315132044200094400d0915003030741d585650351a203614580080c41c0540c0c082c01c0c00c00041003041100155000205007000c2c8050b920f03e030101d440c0e8130bc2940281950b001e2500041c81080a0079020406006035911040038541801c102c59115850307449041d8410104220103203110110394900156195403030b007800003e2409000e258001d0180d0405040b05040c0540c51922950501c942d80800c0c1060844803429030015150000080c48080041e01600503c410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 536908003 1250 536906753 536906791
    0x1005010203070f030c1401021803061003051b011806020304060e0a0b0304060e07120b1e0f0414030d0e010b0306060f06120924010e0c0415080a060801020c15 69
    0x81c80c038501000f681c050500301410a05030820580e00c40c101e4410007203035440000c6030151910500c6092420307440030740459040e41e50302e540d08250403245020180c00e40d0b010386541070303c2c05909107440030a1303541854004100540387c41b918403401031a82011000d03070008a82031121552001d240720381c0c0c010484000000600e4254030201c944409480a481c0585401c2014001d100410009004002501c10101e640ba40342c00d02081d03104003a201009908580e1080c0709081420740c80302da0190511258030400f1381c849640d440c039143e1100713040201d9030109004025850a1900c14400e10443c03580000c2410030043e01007605014008180600c03d07145003243c0c8060b515040c054900d001c2401d01d00b1201a1210a0f01619201c44002c824001240c200350640c40416280d01c014125030641c1c20b03c00039500d03440c15001c818003644c02104450300d01900c2d01074199110b000310315040900440300003242c54441c100309003a6801916422078039804143c60301ca90181150f03074280e00466402c912900042c1c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 536909253 1250 536908003 536908013
    0x30f020109150c0207050604090f06050a0e0c0703020f0d050403030201140903180418111309050a060209011107290903120307170a0f0b040213062a0b100501020307 72
    0x440882042d10607540b0400421028003c004003400b50500410460701c41d603980c9140e90142220624142c80b55040290004660420030211815140034550380c0440e5991098507100c3c640040106070114842e001e624030002200388801e03c81600720b551880d81e101d04502b000303401c0d00c11900c0540990a190020007e001402000381c98010001104040c02c40d11084c000402801000034003060800e00000301a081009601000c40320090907200d0b0000080490b40c2d00045034220540a0490b8004114507170028105600500c02c1c0d0205041002103400401c2981b4684842504892015100c500246680000410b584088180e11410721032401000d000400c0d1078142c00c0e2034030444250f010020921440c007503120403030070f1134500d4184403480ca40022964098620324001000d082d01d042c40e1303002c0605041c02101c0d003802540c42001c1005191920403115201207011b5400ea084102100081c2272201e16143e040450195a03040040d0500600191520b00f9a502850545d0300411491000903 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 536910503 1250 536909253 536909273
    0x40f0e150d0f0b07030f060b07031704200a08030a1d0a0812071106130513020a0c021311070503091f121a04090620040f1a09030d0c030f020109 63
    0x260701482c0510749483e03203a4140d000e4911203903506c0c0324074244600030038490310300d20241c10384601035610070b101b2009031301c201c6600032815180035100b644441014418000442689104a40080c00000d00303030395520b1000c1d0450b00545139810020b600e9079108100f03070203069680454180d040b1060380449142418260b990724008061416482011984070148140c40c20480302a82002e02080d07520350007134110140e811464000c452181540e5040c0d80c801d00030750300c21340d40240c1203a21440d0032824a6000c10808403d00000140301549038400e2007500c0311807a002d41080e038460401145c90b900714404000d45e11405902406642c0ca80d0b00c030700d02c42c0300e5102c0b501e00c0c40011240d100256010b4074005061808140c0409581c1203814004100e040220591000401c0320a8144a40386140c103106da0389054401c0d8400d00c0b40058103080c0508c803960b010461030b01112030300303d4904e00d0210701070007203030500c5205000c25003c5181c9800003014180c110780030010030350461000b0850010243d84e4240c480c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 536911753 1250 536910503 536910533
    0xf09060607022b0c0608090105010b0403060f150f0e060906030d1b0b010b070302010e06070e0402091306030f0302070602010504030503130203030c060405030d11070213020f040f0e150d 81
    0x2002c00c054984030b104000c0d65151603540128004012041c3c841c208604044024400c80c80041d601d00002005044184251070580c1c64420b6003501e040d2558580b480581a03000602c51030301e9840c8100010001d03014441c400805101e0f989003d154030341503206543c0341c0e005100d94059208501040025500480c00781082d02480c2081c4241c10802803031003080380404000205802c0d008000030032071510401c06011490722a0b070003400500000e001090f02d50109403044004100c6200c2640c4080c03038039401400c40f040b40038001c9007074a07044a40d8501502e149500c00d440c0744000082d86d03400c0c5a810f0010740301030482800284403070b090030b680c001d0180c031005040b0901c00d0b41e0a00000304656060045411a85002c0d040761070303901b0203040c8240c8a030f01090200d180703280f0380060000c0b00c0c1459405d5510041d0014080300758403214100c42d1029601540701c004007200c08102c0407682004030340440d00a08007100d51010103103030881c6000644011821550300c1040412200700018910b0440c0b0754074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 536913003 1250 536911753 536911759
    0x6090415080a1b060f0c080f0c060103080a031808030114040603050f010c030510080304170a021507030807030209090406240801090506070302040b030106030207020d0b150f0906060702 81
    0x44145240c040c2500481d400051a900401e2420b1092103151900281c140003030050184110340d0f11607090380c109001818040202d00c0440c4528045103104007d80000b0011401840c43e000000d2800c40c1041000d0300110f030704460100310300c6001c82e4903102d206541840d51140c506001382e183c548401e036000c144035604c65045c50303544211550302c95410040056a1100840702204010301c44103018245402001002902d480001112070103c984102d04550b40000136614207410030f040360044c18000110140c5034030072a000c681c0141c50304400c50010381c0801c01030303d44070440c43c5001130402074041c4c006810940107101180541e07642c5014150002e90200002503290b404000b419800e11185e0726246403074410080000d44440c041d008100040e208100341c843d180d4030038509804a000c0d5004000d0402d200340f00601246001c1e600801405000515007c0000308555512612900441c4c42c1e54240c204000d13a07280c6403c0c0001a2010401c044031140220316180d00458114065401c000e44 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 536914253 1250 536913003 536913011
    0x1030b040501180c2304093b2e2708210c12011a0412230313120803011a04090207080421020906060a0e04020d09050607020604020904080703051902010b030f030306060904 75
    0x30003500403c000c0e10710440318804040d030031209401c8084203d01c10384040c85c050307040101c00c030160002c0021007104658550b840c264590101e8484000bc1c1e04114120040c01030f1030901100c18241e406840c0d0303c074540140c1d142d5a01c08031129041c10010307041c0d00140062900450041903c43c580080d00c080e00c00c1941002c0c002c0c416800c104d0040b10802d0071f00410740442110301c08029502000402c1c881000c41028035034155610141c070558004800050320743e1b4420300041c8400f514226006c003241d4400452241010303141d64103013080ba0310a61701115512000101000b44401502d04048040700c4041c03085004010703600401c1c00d9400041c0804c2c402c0d60006148091240110810300d020301010b4002c545071f01c80e100c900402856002820f407214410100001e50703551000548500c10307540609140d000c3c1c0c89954030b120954016900c2181805420b02000d0120900740c1c82040311007034598008280b040480052604007815500c040c2c010703030401c004010140d2980e0007200c1c0500c1c02524001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 536915503 1250 536914253 536914361
    0x5061c030509131a0306060a0e060a1d060405011401170603010f0603050105070e0603090d0f1707030506090603070b1207020307080a0e01030b040501180c230409 71
    0x507203500c1002c070495800b4400c250b44540620840d03002c240d448440001c03040400f45180101980c0f0081103511503840349500700e0500084000e8914a604208007078500d83d8102d4540904800d100c0524441e451191030000c01c02080e40f9084c020703180148519101240c0b501c48200000300041d19060540100d8103286012401c291400d5001c80000d10840c1c030200040c070744a1074400d01901d001c0e20190001042c1a124004510380f80b000c580c000c1c00307010000c00f501e00456200762a03040341c059a050500502002901c42505043d526030b01c6001aa58000754516100382004407894001c1c005901990001c00107218081c041000c4840313407000b5001016480c0e880100403451813203212002003100d000411401c034840d400000012264a090b2400d211402c0300c8002c1c401110401d12454001aa03800780c0c5003017102e0a0383c484000020f6924200007181c81286c0c110007007018807103645240082c00681085001c445110386400c0c0b4495141008588030040c032104800800480411140000f24140f0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 536916753 1250 536915503 536915507
    0x5070206040209060f030a150c050a0f030c050d0518120c0309040b06070c08160605120402042a020304080f0106030f0b09101508100902060a0c0204090605011203110105061c03 77
    0xc45c9030706500404a80717a0f80510302d00060700c0b010210304038401d0303802c3c542d0380c000c01ca0203541a0781e50900c0702e5480c280c0780c01e01e45004070f000c2e1022a0490080c07002c10002d03030025060b20700440e4860700030015440303c05900b00740034130310b0004036085000c040141030000d101070560101c01c85da0451021200424440c07c400f00055a80c82030110007022001d90300c2c4005114440811110088118419040101e6644004c141c40510480106032400301400380004e00601c0c0940c8403841c140e4884039101b50741601528194070001008100c4070169002007001c00600c03402b000100e9509107614001e00205145540304154400c42c01c000400b44400480000d5000c03204000541860000f050f00340428120520002180c03201801961080e024100502120103e07600070b0070807142c3d000d095545400d41401c0102c03107a4040d558101d0380180c6884892001c13440601649000c0c00d142010381d03089640614003e00031a00d2100203401c035906120410181d55034115130800c1c8080d00b0113031402c04400301c2c0b40c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 536918003 1250 536916753 536916769
    0x162909121005090105040209070504290d1a03071e0b0a02030705032a150a050a02040308130509060d0302061b09190e01080f19020307050d0f02130507020604020906 72
    0x140d034030042c0c600000c000c0c545605400c80f80c050780c02515202d5403038480c000215540e100754050b401640341c0880c01d0081c0c41001c1c696181d404901100c0b52030a080201d00c40a00740d850700e6400d1004c0040d80001c480c0980780600070400140303444001041c18420042c0b07000840c0c502031007002c01150340440c18002d1603000f44102d810069009098030340c0d4581140480010100500f451500c01010a860080c0082c0000340700034040d0f54034107885150399641c2c040b18041d020081105555980074080080040e00d144050903400b002070480c030030101e0601051140101c0c00030b2030b50748240e080820440203e600825100c1c0c1040f031102d180d881200018901c41304078402d440c40c0641240b41441810f1011b00303607410020a03149100302d603503030350b9030380704042961a601d45407009000d410108403000c078154820905960188041c0c240c82a45a66400241558507480c00030303a00c41444d00050021407405260741102d17003554080c100190304112000959074680204024028841d21000c2407050f0381e8164 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 536919253 1250 536918003 536918023
    0x708250314010c0201050105090c12091c0e03010c05120c030c130617060f01021203100801060807080c010804120c022b05060f06060910050c16290912 66
    0x8540503501c161490018000c040810035907005510304400428103143c50720403180101c500309016824800784000c92141c4403401390481d50b29200d01c4281410034031421304418075070348080d00c4421411120005050a46500883d2082081020400307020440d60111015401c09a2801003540307903924140040f03064460104041d03a1603c60590002e143c9a00101440303050041c1f01d644c0072662101d40c1405030080892580c2409604484001030b140c2c00312001661348200704188040c58142e60b0341e070040c21030300a0b800c85070158004110a008400b0104400c0140003000e10340044245040e494010841c81114111801c20074181c0c270003019176581e15440300c604400b043c039450804450454107100c40e442e695046600703004140000d03050350806900e00f481a04040c0560f4941283c8004002c6150f10a040703c0781400010300540180c2c200c10000b84d01c1210b070100142070964148481c8222020031b050282585507441400020102d0318541075800d05030095654031145507042e05000c1c02c081c1510 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 536920503 1250 536919253 536919263
    0x5011407031e031e020702030c040608060a0c030b0a1e120b1914010f050a05090105090f04230c01090e07091a07061107061b2f060f0708060307082503 66
    0x1210703400701601d540e4001c1403451f100302d04450340d550903c0700784400d9030014406d2015a40243c000183c5014564121000d40c1e10507141c00100110044d001823491426600262030403610b40101810002400180c41e02410310001c8142d0311141031b64480c81c81840007041c00d44040b032030321107a80c444152074110441502020785d00101a6071030f0b8088012481c050300c03d051150711701c2c03a130000706e905144209038142c810103030074490503a6400308040710620024108441020710b413042044583c0ba000440c8540c5010030f400b9140c185d02460004146911035000903010316018818420001c4c2c00030218030440c2c04c4502c20030240c050000880030540035216026114a003403e1854222a0a44005001051042604001920100d100c11850b449040154030104440c640041d281c0c0315050303003035055112405001c00d15403405610180c00d000b4103580d00fa41e1001c44406012030942c128150030340c0540300390014107419180c18003180e900d084200307440141c0011040350100d41d00705100900e020315040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 536921753 1250 536920503 536920541
    0x10909031b050f0106090204030c0b030705091f020c090609041511040603050108120a201002040e0603061b0d0207140102030717060108040c0e1806090705011407031e03 74
    0x24107000c3d0f21081c4000100040b035103403d4001c10742100c98420703102501c1c0c1042075081d085042200017a800d80c8060140e100b40320b014402d4030301c0703581c400e005541c860b0803a240640c9110000040070385041e07001c2c0c000754800d813031020800c003ca450b0060074a0b44250010030f400c040c0c60351503440350028030f440c6904182e100340004001c01c3e40b58141c2c10060483d5001c0d4100c0c0c40800081114604c40c0c01000412400201c0955142021b00005070070806610314071002d48205400d10f1900d44102d90260303010410101e022010000743e46002d00c143c99000b0b05121030303465154240300c0003665603c00c2e44610480c1541c0441c1c08000d20044044a01e000700c00701000315500c1c00e003594060000d00c04290b00e00001c544c204001802544140d502900582c1e00030041028541810340e000c0300700f00c008215408654803018413101424041210b10b0191011174060100a03061800042c0410b030300948640124404200500010380c0c03240240034041e203606065240210345402c100d0140070403d2900d24602d103a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 536923003 1250 536921753 536921807
    0x4290d09030e130b0a0506040f12080f1804051501020d0f031b081605120a0b031015090b090105150c120403030816110d0f0201090206070b07020705060f0301090903 72
    0x81d0780d01000c2c550008450102c541c5d0707520010012648580d02a5149400d0003420401021140c6070040303001e648294080350500007055840121504070307002041c1d0440301500102c14604042c800c5982140b40080074603001d00040380080d641b0014040b204017000002c0c005a61100c0c440e038024403203802a008248070007100380400821a007002e55051001c002002c200c117580034001d0086a4140d10420314a40c0c1035502c10b50480c2c01801c003146455014000c581d00b400d0003003094400c6100c6100c205095100301d030304007099401107c91440c2da80e0300490328503005104640d900c4040305010944610241e82e200c002d191502d0420019400802a810021501104040d01f10107a1481124000c440304103002d003103c2c0444160b01c103084ea2544940113008481d011f10321030004044912090b00011584070080c4d0301241d03680d4030ad60380030f496012204051140f20b96051010b54001e244c00c8030500e051424080744606184810b20400300003d03610000c01c8100742c00740000c00d1200c03089080b40140d80342 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 536924253 1250 536923003 536923039
    0x9011e030e1c1806080103120c1a19110d050a09020306070e040b0f100818030a02100f06061209050a1a06010807020f120d2004290d09030e 61
    0x1039030304103000c08641854002007520f85450007a0048500d141d9582c4402e034a11f44507800012034030701c1c01e401085040c1c0540720200b0740c400300c807c041085075003d03d001403a00f01002d0b1841d461102c40c0c007456030700300118505411301640035910056143c480c00a40b6480e284c7d01d140060416140083d0035000d40d000300040103803c641080d860040c1980d0130310a0110301c0c0c04104a510801c03a01582c0010700349288151148680140c6610001800b1001e15000043c00124910b420414901005900690f03d860f40c1d05018001c556002e190940148486410132001810f40c2c0300081003110115602d8001c00b040c028104610300c0304a0b0442881c4031141c1d010464504500d500b203400301c0c042841e103000725007840d2000036078401c41c8510750003900403a599015101d03110b0f07020542030100561035508120030350600c8500ba00320018020440e80e550751600060b400a90011340c1c038103c01006c000c08000070804031504440c8a028003820001c4c8d0701d28503290030744081042c45142030304a10307901e915411000c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 536925503 1250 536924253 536924293
    0xd021501260c04060e0a0b040c14090f150a09080313121a0103030903050105090703080d090204060b0307180b07050d05031e04080301050a0e13030c03090b030f0f01050609011e030e 79
    0x1b09145405010f00c640840a0000746c44102e000d0800140100940d1214807100380301800a894008103500401405140001c900300550110070340b140100068148000e50081711281c0140b040304042c5040101411a103a0580d031240b2a49546541d0040d00d0001c21003200007821450700c0d103903004080e9513140e05008003429004e00044a60358a058041046070030000b54000440b0f5000e4420352030b00d1400e4070302d80c02502e45e0000481e042600c0c2d01c00810781d25103420103144a014181d0350a58551501180d4005000700c5a01034a0703495030400040010800c0842d0b18000200141455a0369031508100c001d080001c1d01c1c41c2500280341c000500c804c20561000450403901c0440301000d0903034882150b281c00a405071240390748440755221b1a80003a0080303032032580c07040c000e091450060b43e45000714032403a44210340482580300800e040041e000341c2e4100c00c502420090712030a0034150f02c80c0000e0001000c070012680541c001c503a2221150f44240c000d002d030303020400c0c142da50030315150191030142 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 536926753 1250 536925503 536925511
    0x715030203011d040c1406070605040f032705010305190509160602070f090c050f0a03090303140c1c06090c0504080d0c0503040608040213020a020d021501260c04060e 73
    0xc0900c0c1501c072100d03d4a1161094080c81d00010780d021001c2ca03086091952030b07450304a187c0c001d04144030000114801e4401c0d40d00ca07a002c4c40300c041ca4400c4507d002003d00c85485a03100c1c0303658940d0a1002145040186982662404e0a0004098642840410f41c0c0b601c8d00c051621924181405c102d0045808141083c0c4486c154488a0500d0b468800170307601c0e21f885000b61900b83d45880d60401c2140943c0d00302c940c3c46c41c03650030010302c1d054004580510a0f840550b980022035200c405501c200b42e4140304d0415a40340c800341c1c1c100c07181049900c0c044a4841c101c003080b4035403d80c96010080103003540c0400b0081030492420004585001000340640e0018411400079028071104000d296000704991034103a944000503510341802c040c001c6e6141c0360042c00c2660090b003441910340955a0a00c020309940d04103070020000da802e503080080c50100c010250704031034003041004005806040580c40c5003440b00d00001d03400c254010240c40d141046a40c0310702d078428100712002032084100b07420705000d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 536928003 1250 536926753 536926769
    0x415081c0302091c02130203180607030212040b0a0e06011e14010504051903080d020c0c010e211c09170705100e01030b090a1b030e0705060c071503020301 68
    0x44080401001d40480c05041401a0400310340080d40304a00310010360040603c1c030003841c1d8182d415800c0c2c07101d0101d800480d03143d48d0001044400d04901c4100300526948034410349001d40c5802548401d008248030007620081c805a5040c000c14200105034010158181002e812941e403583d4030b012000b80c00c500d02c1001110154101c07400305820212040c06212144103171030702807801c1c1c070f8401400303d010560310008041740c1065001000203805c1c0002003c2d0140a1000543c40c4d0864542050900950820300c605100585401010303503140d003580c40003c0000d88040400200403d4119810002d0314500c440a0f6698410000f01c200e0708191f22101380c40f400d0b6515032440690042a81d42e42c01131f8002c01707500003410800f44c141d0510a11a141c2c0d16801854042150715004002c80c21a8409890010044c1c4c2c49030703408600c1001c5408140240c50062409000f822012110a511103005000c2d413401b8000020304104c0320082080b4400080c01d4072072261514600d18240100250000e01481076 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 536929253 1250 536928003 536928043
    0x209040b01020c10050f0d0f09021203070b0610091e0e06090c0316050702030d020f010c0c0c030204050603150f0103030e060c0607080a0f06030f0b010e070f030506041508 75
    0x32a07501c000b5651158202c0605810707848141a90281c03000e030401c404803003010b241000011a401031500614517508c856a00216018185104100f0f5030545a103541c05a9441403010801049091860580055040d218014504003846040b1004400c6402c0502e6429600c81c40c91100030391400440d040340d03581e028403031b41c648801082001409055a906902c2c200a002107005040301907001b019514690900e145804850750101e400d1a0003d219540580c000c03554903035040b074007030090740ca02149070715041040c28065901c0d881401803e0001a0003a6654400030700e82c2c0e141041028140c908405800c3c42d5490000750034140f80342d0902040b000514040c1468050b030a001c001d4603601035140000e0426540d410f8402c86561760000c1c03a0401c09511002c0c03000c0903920601ca843c02460103218091f40c2e0892a0919003540c0d54184d0000085449039010080019800640c0440c2c61911b40380106082e10345000060242031001c512078050080201c3c0007460b030030700142440c030040f10444911 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 536930503 1250 536929253 536929271
    0x1110030c0507120c2103060b0301120b09010908070b0103110319020f01090915091506020d0c0c031b14030a05060c0d090503040905190606140922020904 67
    0x14180c40020000c036001c40c40600003480000d40c201e8440c00209140e181622400c496620f60032407141c00c003440c000c03425200403958080b00754940107400c05400045002441e42d45422440c4201180b030b1500504031091040215540e52000e4000d41205030300106a691100024102050150320a01c01254000214000404203060215400f000750007401049115800d65400b441124401820b18a040045032040802d004000744981b8074090002c1e041c1d8034485081c258803904441c2110f5050030b084442c0c420402005500240c0c2041030200c5207001045070041d80703042d81d216079041c0c000400405980f0610382c0c003034041c0010102122030b01c5807020b0035034080c10107040e00c82c0e0060070050655005040000e0400d108080101a90000c0080025103060140c07642411a0800e41142204039125420311086103000316802c0107401d040b00c2d04101e00c52a18002803d00c46004034a9800d107100816050516034a0090b0350380041040c401c0302d0009041203108100962045030720038402c0340741040700 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 536931753 1250 536930503 536930507
    0x522091505010f030b090a0c020c18010911030903030115140d051603050906010522020c0d0f0f050306040507030b0405040b06040e0109051504081e030103410f03071110 74
    0x10540e496001b0f001510b03142c955014081c00342011035401019481404010407040c0c480c0000c60b20041c0c0b80c51380d40203c070b50400311594240c4005600302d0501c0d42c000d005000402c040071040b0380c11205408003945c0710517102c1000b581c0c0080700788078010210b900801c02e8a81991700740c0005100360419010b80540012100041d412a0700907a020b0055a00c9407005000c5400e001b041000440120081000f142d00308800c94803e992001610a02c50341112040c803030100d0300181d44440d4030105040401c1d0410540307070000c105000c01050b9510441d12880440d0005010f948443c441c040007500602c09450541810081480203494445c015840c0c5140c00fa240a81171250101c242d501c01c0c040e120009400a03180f0060501600507115070004201080c0301c08100414401e14001d90006240c580d0314600380810503050f140c0305071030485141c0901d29481e0896690440d8449903212055611050311903040b0b1901c0d04048202c5050300c0000b4052043c88290200a940c4034411504455030210a500c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 536933003 1250 536931753 536931761
    0xc060d200f090d060b1c0b01050303160618060504080c0f0c010e0103052d0f100f1e17030c01110a0912080706050a0203070e030d0522091505010f03 65
    0x1441007040080c4528005403401081c0d0a0301c0d81c3c0501c41c0407504189410009081c1ca10b1806002e850951004801d4100300044105078010b020840203113007481d510607500400d40b030940c03000504059660360b02c0c03021042d40442d1400f80c0d50300700c0c070200014946840c100400e544000408186413149444250924000040c2c080044a043c2e403900c20300c0d07481c0d034019005094042c01ca004418506204502405100502d1307600e84456030450303840360708050600d502007090190031013202410105040c003400b503e2038101400c40e144c2400010031801c890703040d1200749203580c0202201c003000802d10302c6801800000b400061506400800c001124440342d12901d1182c038548402284680030200101322801c0d4100b00d5044c026444c0d5881c001003651341d90b003250706c01c4a221034410f50100c24000100d621500005090405030000c08005500b100068018041d803891a134100e8151084a15017010504000008100c1050180f100c1140d00704401c0240c0c5e51070007001d001402c000c15507400c00b807003402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 536934253 1250 536933003 536933017
    0xf0a02011a01051e040315020a14030105060306120a02040e06091009050c0405040305040e1f080a05120a0903021207060f08010e070c0c0302060a030b03010b06090303030c0901020c060d20 82
    0x120f0903d0100903aa080d8132040b0009110b952500050000001003000010203600041c035804005a0784e90321410040e007000c2d4050041c204445c406e10052200e0b403291f10032039822103070444800036102a80b40140d072800d501003200030340050500800340c1c08264005841802a002035080e0382885428045580840314030a4000c2d000d64010101d031002c03800c4c00da0043d40c1180c064680b2600c0c154031800e0381500c80c202565103da040840791040b114850182078541c0c00340070040c0152500940c552034482d0741d0b000392015041c2c52100000c03090201d9010706a000c00542d03016003200d00d00190225803c0c1c80e4a074034450800455610500c00c000c183c0300c1c0c02c2e464162014802100e15903110180104e6212a00150468002c0c2a000002c000740c1d239400094000004d01e40e4005c42d10458003400c0c1070a440700b403240709000312000e010550f01c1e59804070a6a41c40300c02d41903020785030300240c0c004031300d071082e28800f82d80c11010000e561903607004290800b404a458402c0d2604881002810840c07291003199 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 536935503 1250 536934253 536934257
    0x130f060215010509180604110a05012d110d030501080c040e0d0c0201020703061d01110313080702030c0d080c0d080114040507030609020a0f031109060f1309020f0a02011a01 76
    0xa4010b10462400c00e03111600030f02050117400d484079140346080d01e0814196410b0303841e42c15007411302d00907292040490703020340f0b07082c0b8103070a10082600016010140019080c0b000d121901c0003000051301c520700702e10300c248102046900c501300d41880a4001e01d428000e544050085605000c2c00b800e01e03004021005010800800b90300c81c4c07200003103c4007009058224114040c0310070010101d0284d0203000d82203547c04c54520566a04802d01c40d003191044030060782103050510400c0a465941747c4100e80340fa4012078205d0b540c0484d840081d00f460042051180d1004012005030103001a0a010f03248000d04c01d0116415446024410780b800c11007445454850600800f4021345400d00e42c02c41500700d5a903060100e28140c0329640d0384240c8e08040310b000d0000d440e040d000f5011035414003820701c43d202500c030745a2400c02c43c08003007081380c4a10301d94000840800030b004906076860000700c1c0c0007400280021501c50a030036070700d030115902484202c0015820460890760040d20070700e017890070880507 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 536936753 1250 536935503 536935543
    0xd1d06030912030c0f030f060907031116140f01020406111606050a0c12020609100506060a0f0507050a0f0b010602010e0a02010e0333090f0a0605041106130f0602 71
    0x41005100c1c41d43c401042d000032041c0500440300c0c0c3c140d0f0500a9401407051998661207480c01d1800c1c0000400010b0240c030030181052084001c618440c070407a94612041140e241c1406080d06200284085c448407141240c8038440b0446a91003040d03001c0c0c000c0d01c6955581e42c0b200b4109240e101d965100090303040c031003000a0101000b4484c011401000403c400e401c10030010041500c803a0a203240e15a40b29001da045038040001210082c40681d810150300e420030460f81c14070304d012684034050b6030380880070301515440141d400d0780aa400d50314040c0d400400c4482c9098540ba08508021054900310748003c205000482d0b8a030040c0a40e1484548440003818020340c2500112140c00619035620f070176001f040c014042e5030706040f280b180c000582808090148070300c114107094104004080c1020b81d0007010042402110108001c40c0d40c82d0040720118030390b200c9042c0b601170744240d4030120b98000400182642d00d29002c50202d002c0b034884507008403003580c1d10348040c2e850380c0840c820b05204000b5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 536938003 1250 536936753 536936773
    0x10e060406121d010911100516080d0e0613110a050d020d060f0f1a09042609090a0c090905060a0e1801020c1e070e04060f0e0d1d060309 60
    0x31591054900030343d030030385416242d82d0a0745810700310344089606551400035407002803282d00b040c14150041c1200da19120f450f04002000d0b0004050110750300a003141d13070001e04241c2115258100c90704030084001903c07502c0c06c2c074030101144a40d00481c1210743c2c80c5410794540c0c5030700c0d00e080301104a0b02c0c06008100c81542036420000c0340900408100e031030071f554002100d0801d04c203104000314019042c40005080d14076035414407030036081a070a030344500c18030310820001480100c445495018007040003c0548a2103d480a0a006100085820050840800c40d0f00c40c085d4002d0202d02a268031401011a16a101001654001c071542134010b201184208000c40d030700c000d119800924040140e80c062000319510303089e80d004030413100943d4021107130307003c0c0c402d0388900008801c5640f400070201207140c40c2848698890050010302110f0f951104a42c4100d1150000c00c018011141079489400c082d08016104a440b041030112400700a8540000ca040110869000d09000002082c0c4405 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 536939253 1250 536938003 536938037
    0x91608240c030601051e0c07050f10050901080703200910020d0206010b160b15090f160807111c1d0a1401140304081e030403080103060b0a0b0c010605010e060406 71
    0x100c806c0c000d070f480352079488000200d044030b100504900320801018100703161400342040080c40144a1480c480c000340d020341d043c1c5075042421200c10441c20708100800381c2d103006d42600105102c00a411000c820003084d200843c01240040c00e005108a03610000f040b801c8108981c1e82c62417506100c0036a20a2005001030407214024002e150810190f4843c00d05049d5200030500c0401e50b000208071000020702e0341030345000364000b80e01420080b900302c81d030300d0078070212103d54944596030400e011079540131803000c600c95070f220134260250702c08603080d1140805481449142085415001409a000b01c0d01100307840d9486485903c0b00909401c20300b8104450b02c2d82008025008074188a441e000e003a001e007160ba40075511a9000f040c1e001e8545200c03480c10000000c0607007048030100700400170800084d4000000328152500910001200301e0001d010414022194120040780e503004030341e8450201c0c5c150000010b50394281d8805080110100038850b00380103e008010125540c0300c54201c2400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 536940503 1250 536939253 536939257
    0x6030509150f060d050316121107061409031b12010603030c060e010e0f07030c0b210604023603071203030c030207060905160e0915091608240c03060105 67
    0x1801c0101070340c4c214003c99031071a1659000c0105000c0610000044509000c52500203d1300d6070781601b03054030b258170011441529a242802540140010b0340f0784141e5059005055444010000d002c44140d9450b1005c0e108917074041c0009a44505800c00c1301c11454403041c0100381c22a603144d113a0545031200341d9268000fa0140c6080401030750340e940c0801503030340c104001e06542d410351940074140d05c505604000843c0c3c881c541018880300c10400070300b01a00a5840d10000c07200701c03200025090780f0f450001034060f109001c90349008081d03e00c1c1c008151034074604101d88294440701100107010f245010305813551894421042d6800e81003000e00086802a0030485020089103401490070000c2d9840d078048400141013030f18140d210301c01190050040d8030390100580942042c0c12076074901712121658840306215205800c03400c100201310982e4041001d00881e10754110009801030f03d600740c00350f51341c05460500c81d03120745403001038400d6894880c032180154000ca16192860f6504401902c0075 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 536941753 1250 536940503 536940511
    0x204080705060d020d050106050301030312111c060308130e0603062e18020301030b0619060516290a090305190e030f030309070801020c03250605040c06030509150f 72
    0x10f9000c00501c0182081441001d019100e989c4607943c4039415420000c000d10b4a20102c00842440e2103a1012608020410b555004090703040724041903a81202405c080d1869500042c1070890101e80100604480900801901c1c019582090144c0d074407005c060380c9490945880d1401b208070590f10120400c001342c000d924540700803d1100c00740d40c442e68454200c4040c000d410300c0c6640030005104000346c0c0170f20340740c119a04682c00d0300d460018042e0018007080c0340c400d040a002000411403000310700c820401e104190844520b0310340400c117041d0030b45e00e407000040200340034101000044502140d40704030362141303400d65101c80c1019034400401030800c06203059a010300c00c984980c90000e5608202c1070030040c004501454072400c00e441c02500e0101c40c7e401080f142d03401400080209180003007929100c04540c038851203030070b103c8541032001014a0b200641118103105c2000180034103059072104403102685c08000c1903a841c580703591229100008041c50138000d0700810300d203e0304141440c0e08 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 536943003 1250 536941753 536941777
    0x10603170f04150201140f0411060c12040b090a120f06152103020c0a05031b0d050304080106080c01090305100e01020910081603111b211309020408070506 68
    0x2d05070702c8850010b0403090080450b4010317911400b040306030b2401a44000d0300041000620401d508041e9229209074906000c500d000d52000725005507504420410400480340031481a50f84684800c416801a4000341d00c039800380b06030780e900150402d0741140b1400e9007a0402c0020210036401e0750b40f4000707010005110b030492152800045400d0361514915100760b20700501c00101108035142c064104489000114032406d0700440804c11910003280e40f42040800340d0425a170400404c002030400e00010102401700e20020401180c21581541b21000f62104242100c400c1c0700c440b001194403035004d000003051604228070924071060306410400040e512000058205160b1802050410351514103800000304101e007071160269018030b82880540c06845d0a00c00b8400c03079050780e41d1510a8049080c0490718040600d11401001e00c00e4407000c000c48c4134100c1c02404e40c800c2c40361107a0030035400c3c06041d1418410000c1c450009200300c4044928010182004504e070100b00700e0203401060b10116 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 536944253 1250 536943003 536943007
    0x3071a03011a090a0b0c060702121b0109050f1e030316050304020d1b09050609070519020c10031b020c03060105060a0e0a030302030a080f10031e1406060111010603170f 74
    0x5507940e125030050016010b00104d03246c0303804104905500c0d0080140072802990424191101194400c1080703800e0310324426150129040804a003900508032100080c12500030f4503106898020089059105069150013100c0c42d2041c01740801e489100a40c1c0e0400b10a40e1102100c1300207000380e0142d94842d0004000b210f80d24071540340c07903040901035030312241d4408141303000b400001c401d441820342000c002c3d40c4060703082c91306800c040c0c000c1c410040c9000841c2810200c1202c040e2003080141d1900a0160402d80803021054014001d08900840400318062110030411000c2c0b0001d100c000491009000301416460441840070705d0b8012055881002024500c2c0c0b03030107884000d1b0340b000443c82a4020b50343c540c48110020b116a40250444003814126414008004003640d955815650001c200b0003910034041210a072580840744000c160111a4020754200c110101d4100d1050500380c80c2c0780500510040050708a51a9000c002d0910306800980d90f81c05c01100c029020034011010114 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 536945503 1250 536944253 536944267
    0x901050114121c020309100518060306120a0615290c0c03010e0c041d2a090406090c0503120f0f090a0b03010306060e090604020d02270603071a03011a 66
    0x150000041142400143c0d00024886d0b90f13900b007070504219074056501d001d40c140124100d48506030540300522030700c20540480440c56590365030052080e240c3c208011076039903440c1840c0c00c20103841c16884805024880310390000b11140b03101d040c042510030030040c40400c1007801d800d54400390400e01e01d080d01c6100304558420243ca003440b95600d110083703070003054114030100c10001a070340300d014045001580c66a4100312024001589510003100600c000001003c100d0030901840d56900e15035840071804080c0000d0103196801145440d0061041c0c2520640394800d15035143c81100f00c9425a0101304598019141d80c94054420040f566512501e4440180c00003001d0800d650403400341244000010004c106840c8540c42c010318286440c3c1c541032070003219894455100800203400780300e810000004564030110600c01003c0340100e01c07d1055a100d0142441c0130b03084800500a2050341004520551240018182050200802483d5a090090078030341c89440140c00801984288042 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 536946753 1250 536945503 536945533
    0x306050a03080711060f07060506010e0901090507030b0f06041a04030614011e0515030a091b032307150210021602041401150c050a080c0c09090105011412 68
    0x141004500640321151540184e003007140024840a1300588914001c1002d010081050320a036032045801001c0050703030703a80d258016507000c40e405908541c4203494200210342a2203981c0503500406a41c0d9007000035094010610244100f61442c5503841007080c40200f0007100c2414020011000e152102410a41d0305d40e01e040c00e80b03a1407040100013034040300040c8000c0c801819804016100c00f55040e004510700750215114250710b4008210780180000051800c4207260060f1007100e03808000c03982010303042400f46021b5042804200c0b004044449100005400c00340310b0544440700c03102610f483c605e4050200190b903048402d01e030641c0200c035000c00904c030052020300001621440b07109583e0b480c910402003191520580845c1101184006000305540d0503c0404041c0d880e05220001c0c40e01c03401c01070b02e0000c12480080c6144400140b000c50720300f01145c210512102a20211005d403a00314602d4280d44090141d005a20860183c0384054508903154401c500c5405041e038007060b0a4000f1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 536948003 1250 536946753 536946769
    0xa021c0c050927060f010303051812160509241c0302060f010501020d0807030c051c06090b0306132306090723010813026a030605 57
    0x10010240780708840346041d0300d6082c80f20140c0d207003610040d105914250552410134501800040d04211021499400d44900752400c905840320080c1501c0c0710083d003d40c25030307544c19108203410b148030fa0050002400d041ca03ea80900406012620048004031046140005036061003660303401109052fa04940b5600200d152a03118041e50140c840c500c0d0104480d003101c40b040e44443d04640c8000c203042c50b0541c0c03054610b9000015450f01140303001003410129414012080394040d142c5103510602c0e0310f405580e005a003110f020301c1d014002c03400e45c41c04054075641c04844c04103014a0300c641040005060703e5100c0c1d4200d000c40c40d10b81c1c201840c1c084640c03600400321110034043e8482541404481c07100d062109103400c4281200d41c5680700d200000741400d81c0602882c2400616160390ba0031980d03000c1000a84603580d003101001c62890030790385420710200e00318005880c001c0e080440c0d81034041a08000c980b281d140c21010b1102c4602c0d0540500f00ca5400504003010759801c00400d082d030b10899 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 536949253 1250 536948003 536948011
    0x60409080f0a090b0a050a0810090608031b010204030c0b0a05040b040b0702041a03070b2d0403060c02011109091f090b04050612120c010605030d030e0f0a021c0c0509 73
    0x650706485858180c1c02034280c0010307800c11640c1100a00040300140c6d031040813100d05500a10f4403030403030b0319020440440702c54140c0007800890300b044800300348401e002019051074129402c0341440401c01c401114203c0c4184e01007d030101a1030001446682d60a000520301e1009601d0001e1a141d50741e2102c16254100341c000401c0007800050110552030a80640c2d00d071144818000c088010407000000e0f40c62245101d08105d4000102c1c0c8070042e00c1411601e80c400345c40c031400c00340000380d0ba1048061700c2e6101d4003045a0161501a6103005580705128031300c54000440d1350103240072100c00c00c20803405d8004200346002c44501710440315400100340302d20002c00c144040403620811980400c4280c600c02088140644c0030481c0c910412000058400c0c81c1701416002250761708030300d82001340903000a4010382c1c1c1501c030b0342c11012010360b4190700003030000501000b5203151002850b0000d48480300032034041c4d485507122000b40f000286050f1175000e07092082d50700140995452000c2419241c04031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 536950503 1250 536949253 536949277
    0xa121101090b011815060e0d020a0806070f05070302101127150f0d1512030903031d010206062701031b0608040510051003080d0515040209011706040908 67
    0xb5004001c2600c401021800c140038101080c07059000220b56001000ba00e4491041045a281c00000d01398a03a440a8988290050503403801503880354a410756646050715100d001620102c80c514005100782c0c150b500069041d03018115000c409005440070300081070401c50648000c020b2810280300b07444518012004040448001030141c1c01003003c1101018800c1208400410a404410460f0000c0710f69001c400e82c1c0c001a241000342116211056581012510740781c46903441d014550003000c0b62080f00d01c00e03541d800180d0100e0b034025640f02200c45056000d0b1740b011021404505e082c00845c001c035019681100048003c1541050100c1c00030b904c144c8680d8560342503020754607004a50440500001d0502c080c2030f09060341e826079124030729060500d10590310b4010910000958400314000c0d90014020740c0c4a03500854418018803007540c9a400950501007030079007070305041c002e0341c0f0030210584a5003a1090140100c11807020001d120303552040d9140d210900045030310010740311102e183d0b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 536951753 1250 536950503 536950523
    0x316080c0f070f0906060507121403090109061107120c0602130902041503020c10020304020402040308040e060405091b091f03031707020303011a0a03060e090a050106050a080a12110109 81
    0x4540b0f4000c101540d0f800c909407a9082401c28802a03400400711800c0650185000410002c420b4080750070b41003510105e11300e048000107100d05000e054000d01c5040d400b80710308000060301d54005000500c240c62000307008440d200c1100007624054010b10a089000351400352501404841d00c0d42d810f50203410805000f0390206092151140e59039450340040c5003400d04518058000c480c2c250340d0340c2d051024100c1641c00000180441d1220b0f0160b800071603018802513141c41d110304000c26014400c81da260300852808000507480d02000902e99103001e50052082c2c51030050000380320303003090b004000c40c0d40701e403040407944d0441202c0312000c0d00541c00b80d5901481e05450a12800c4194005014401194800d00051040203a213984105070981c501418a50360240b414050b40600241d500022402a014003085640340b804203899440a119170000c20019840d50100b00c0c0d645018000c6404c2070b0701c94004040060b41006103081003180d5400e02101d0a0640e01281d801c4da802001e0442d65000c0f6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 536953003 1250 536951753 536951759
    0x1e0e030a1b0f0f060e1302130308030f09060403050319060e010806091b090126012d060e060d03021509031c0c1d011407111503090316080c0f07 63
    0x20b4400c40d80600300c4504407044040c641000208519181d0010a10a010b2440c800103510920380c110f464002d90340e040306503100d0741c2e03040c61011a042206d00ca0400c49a0100013001860042007044c8240d90646074941507849002402c424020304440a0005940c1d80c035020581d8468010b100c0d008018101c0180980c1c81d0200300c0030b00b40104088240e5000e051102c080c00550b544d1050030b4156a50428001d00c003520711680c0c144585107030588043d00d035292128040c00c01c0740c405103c540e4008124110001c202c003040203007048540c9032203801480140c82c00440e01e81c1ca005038608000b68061310440f09079580c400700c003900d40030341a14010119400041e000d008080c203c00007118034080c07a00e081001040c0220050310960101c540c8598800c1c1da254005960380c0210600304a807102c0d18a101d07180c025505c2d04141007600c00901c240300c0c2c4003074900214007400a00840344244a03620140d410580440c1d05600500540e030411a0442c8090010219207a002c004032461290820010012189 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 536954253 1250 536953003 536953019
    0x20a030f0609241a070206190e0a0b1e031015020c09070903150c27080c030c0a140f0d03020c0a050f0102070605090a0b040e161e0e030a1b 61
    0x180255034681c4444035004208641641520b0716030340400d0104c40780e03696088500c00140544601a81058003020514076a01d01a0380b10582051a071416508030560360344034002006980a10030101d0296004041d403410702c4200d40c400f4507000188640103000ca241c840000c0504884d4807060040141c0c03155003a2040f03480c2035841140c002085041c01c10586040d621178180c071044921400001d2501c0d4803284000c140700300c00d40707180ca507440051140c034400c000c03182115040c1f09100d099114464010f18844902d008112507259803001020340101924040c0000c41e00c070020030300303942d00815410f0801c90a440700030703002807850311035805441072034408007c100d880c3c445a004940202050800300342241d0f0002100b200f6922903003072880d200c81d01d2a001800e80d85440d00400414100032400044020003d11114050085e52001c0702e6100d0f00d8420442c0c101d40159241000c041541448a2001d0701958400c0d0074204064103450042d01c16490341c403504e400c00d99041d55800e80c44541001126 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 536955503 1250 536954253 536954291
    0xf07030b0a0609030f03020703050f0d09090605030712060b1c2010270609060f1112090315010e0a0c110d08090307061a010e01020f0709020a030f0609 66
    0x1403044428000703090920300000e00d401c1c2c442c00000d19003c501a8120241402081400000d40e030140c12581800d0580b80e00b617450305005212040840d407106004998844580160429a1000381c010300c0024903244a031048604c80d01002e4503000c3d0303904240242d90301c0c0d580944500002c2c0182000683d081407511040003141c0c141a070403044811046040d0640e00d0038038030800502286044843d000010030701c11420b4030070104880c0c1030441c48600250f89a0000081c808a544580702c4a580c4100c03400c0903500ca40400801c428260000306c0c0074514100c128026152200014084602d0524000603200140c2c40a8210020b00c10504d02003042c070b17400f9030180003020741c540d2902c20004011000d000355036042d0307071001400f800b00c140000340d400d41040068440c2035410000c10301052044500a0440c00036080409000480d000d81c030f038141394000a411703411080c1820080a040e85002c00b840001c1d0041c150080405845107450291312182c0d00030200a081161000184d243c12010403603134803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 536956753 1250 536955503 536955521
    0x10e271009090b07201b03060f0702030d05150303030411040e010b0f06030a0b2805090f150f04060905010503152221020c010e01030614120a0b0f0703 66
    0x21070804480c1400100c0c1000c0e11a0007584c103042c83d1405080c2892084503040c0111043d005a108031965181d2001ca10070221010320415001e4070900d84412104506440080791000e0141e4410440c0d919003d000b43d11099014400400c818140a6003000113811980107071402e40d4410800b0003800e880349024815200504c411030001c01c002c03030700980410040360403c107202c4e21441001c40054080106c1d50014107404070020100e00e000b45120442c12581c441c620307103200360301d04401d07000300740390800859940c003410024959100584c0c4590206215071203204c0050b410044140d00781246071034500400000d0601c1c0d2102003810360400c8141031801c001035200b405031442c51400c3c04503030001c81003012804200f40c082a00e0141c56410100800c02c824080440c4443c100c1d0220500107a01045500000d003090ba03410701144e100c50011402d1340d2a070b02860844540102c02c14056140c000c0c13001480c05c6103101580c00e41189510f5451006c1800c0703a0400806011808010232030750305100380360b19 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 536958003 1250 536956753 536956769
    0xb06130c12021c0207080c06010b2104020103150b07060506100c0f0303060b071121070603180204062d0e0714070219061b050c010e2710 60
    0xd45011800000c040741010850141d101c0c0d40003c9545440076461a0002600c016030803c3d5503a03507903481c01c82402d5000c0e0b189907495008a000100c0d03e403003c40b0407540b400c212401c0b072440c0140920b003007012204014200301d05155035400078040389903011400c14001e2080348005034031503140e814030740240d410080ca900e100b070125058005001e90001060000140c102880300302c2d494a07850309400605180d00404920800400c6800c10454402c0301e031007044105403078142099000c0d40f5000d99082d40080f4510590700001d4007840080e00c2030740011500c0d51036141d02d580c0c41401d40c000ca41110142c0d00300030120035001d03a0710031000480240c0c88810215030280c400441e1710b055000703107002c04003606003001c021a8420802c0120302c01000d58038803c1d001499180308070108000305240b42c44600c18880441c0b40006000700160420080f8040e042d00500609024481c180c0119800c03103002c42e516034010102c0301c090040311514481044241d218061014031401e01d21404560080700394842c0300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 536959253 1250 536958003 536958011
    0x60f0904020904060c090b03010f0609050d200a051503150102060705030417190e0a06030204050d0212010e0313030b1006050a0309080c10061a0906040e09010f090b0613 74
    0x10041c2c40d0590020f92041c3c2002000541c4440f801c8100d41c00c11700c0780e10800c404800803001003144104500002c0c1158030a480d100d070702a82e58420320480343c41c11035002c1e003036894407024103007444100035082041000041405030181c0d206c2000480a58010915103083d81c404030400c01c26026450b08090140c500340000c0c4110b01d41640000d140d440002d20050480c2d54400c0656030180d038020036107620f1107590584455882910740c4c0189a81c1007408194490505c1000005411b03001e842202c05403400a060400078401c3d5400b40701400030070b00c580d203250303658134a42030402c0c200c140007522445584a038060343e01442c5050a1403010741c0907080000031011668104046900841164902c840c00e08002c242e541e00da0802e03c0e998041c10b00210740502a6080200c4c1d110355507441a820390300480141c000d8265055802052801661070080d08000100070602011038041e02e50b03a4002413403070011402e0340504040200760741c40410300301c8402e00341038140101d510304444a00c01130344403518100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 536960503 1250 536959253 536959261
    0x30d020a050a1e0c1211010905060d050907050a0305030d050a0b0a03020f0a0801020a050c160b0406050304060b030d030b012c0d03030e0304120c0e0105101202090d0506060f09 77
    0x764690705000301c01840980c0e00d0510081c510310070003002041980116a500c8000c1e03507420b004038031805a010403907001003500d00f0150f81d50b00900c010b00555101038105820314902c04081030007004098000000380c07088590000385980c0e11104030f000386208078041d6440d0090f0000f03030790503a04064001041c407401c103041c40c6d80c20f444d0107000750704582e012184103400c4502e44001c20340c000003039041811254000540c040003150024014880c4c100444115140141d00741d4124004140d81d005980c04c810017008104500c1e03101c0c1002e5074010303000f04000545100c031480028903104020082e00d01013a00e50456180540c6c00c50a1202d150011030290050740855558803100c001c41c1c6004144104401d01c8400140361081c0c1c0030700074480282007282e54035074460445810700c520b80d10045a86050a81c004030702038081400b41412034002500c16803016075414421344400064500e40d5500366424030544801d95910310240004900075005440c2608050b42805402d00080401030300501741032041c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 536961753 1250 536960503 536960513
    0x301140c030c251b1d040f080c060c0a0914031e070b04080c010f11070b0d09020a0905090c180705070f020d03030603030e100c0f1a0408030601120506060304021e060406030b030d020a 80
    0x810f9206d68032640d82044524123140070481d43c014669640b00301c1c401d50040004104185c4002c050454568590074000d83e03503440343c1d0075071003281003c954244c3c0101d800c9285403040141003804465a031000c0c0c402c0c00d5201c402c0c13647c4907007240e0322075a4203a000f1701c1e9006003540c0010101e02031400360710b08240d4090314200282c4d91002c5070700c500842c03180c00003810001d46280743d01c0305000c40e40c0100841c00440e5241e01c0315015200c282c0712103829000b0f80f0b28905507483d0028402800300941d080c2142c0c81e6491500940d03007600701890903524405203401c00c00041c1d48034082d0814282c82501d00281d00750460130010b05c850800d421032400f48201181a040d56500520481d0728564044c41c6804248007520f007034042582c8100c159035400c021182844100305140003d14400c560a9903141d0700d60005190101c1a9030082c2c58454001c3c4041001c1405420001c3c041808034094230031015a000184020803020b84c03207a0701c0880042e0355541c03100d03c00d14041c4814a80c0707205520081100070080d4541d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 536963003 1250 536961753 536961809
    0x100207180e1e03250204110304030f181d0f0108031c021e04081b01090f030b090a0b0705040f0806060306060909010b06030a09020301140c030c251b 65
    0x1c11400b10209010410200111826100c50841412003101d0481110b1414506044124421400c003d5514501088001585e00c51500750b91054600d10092005881e51641c411a6810750301400070040303101d40f100403c605c041c807075203a00100a0300e00314000c40c41030001a0440903503038000f00450904142c412000c02c00c1e1300100c2a0043e5240340208040c40304501d40f0344511000600403c0000d262000130641c03914114103004410705044c545001101c3d510803e004400c030500320301c10b061000c95407284032076074000d24402c121084804503847e000300f2030000301c40003c001100060140540690080c04000501451000745070380c2c1490700000781c840000400d424040d03002100000d106510940100c0c00222000c0c00703141d50707402c160700040040c00c620380e000d070301035030034487d159290418504006114a00d05162907007140c4515404402030b130700104c1e0508a0050300440c811070300010142c1c0041d21032040a00c10364140780d407214502c43c8207280d4008400103005100c00c01034801d4102c9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 536964253 1250 536963003 536963023
    0x71209210c0506070e0a0f0305030909070c0206030c09031608061f0305060c03060d0b0411210607030c03150e06040e030412081b1905190f0204020d0902100207180e 72
    0x240814641745940200f10300d0102940901e5050303182100000c2817040120041604c00d10550300c00a8a982c0d01d00251105940901c000350058800c0001031480d4580c84043c111080009040d1115141019070855005809070448101034010b50b00780320a41c0c0740440700c84280701048200785012450350300ca66031510700040c031040002c10000005003582d5101070354413040603882180c402850604e400d2005000075503904036806250b01405032450521002981c0307030500b1440006000ca82d580b140110060500d1100c46403e1549410045424150455440740500350751480c0f9120b5103001c4c010401907481488521b1500d4100f0001485030b03080c1200419101034100340000c0c1d030b54000d00c4291100100c03180c9400c1150244c050f105107500000c2c07014244260041c812140a41105a02c0c000c80d420b005000500b01c4d01591503901c0181410b80142585040d1403000049104482e0046404400200300381c0b40140c002c0b40041c80700f900e1894081c0207900c07a8403003c11a01460b10039081c1e9a0030704103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 536965503 1250 536964253 536964257
    0x2c0d0219060b011e180504090230030a0c05011103010f0b0c150112050c12101a0a121a0609420909060403080103020603071209210c050607 61
    0x28007042c8441e4001c41035101015095410b02030310480c509402092044040040da400041e0810001010301c3c2c0740c0942030a803500101409400020341e03001c0c8040100c60400c1c41c40d041c043c1500140714500c00c4c8003a001c1c0308000e45410700d840381c081c509207086440000081ea0150014001405901d007281400c0080e602c6580e50280c1e00d104100800f03160064803040440099450000030500a254500050150388107004652440d60a941007018198512505100c180c2c8a141032440b0741040d034003d800c1c02450420301c0e4191550400109640d0400d54018a0b000641e02210700b00b003241c441e200c0340a108800a000800d81841d2000070342c84800900410b040c2d0f002545500500d40d03070048080070408226500c0d1841c4810846455404d003203014040c2d10a1442c1000509021030101d1800e224a42c181c1d6181460303801c643c2000341c140c01c040d1402041045281c02e000800900d0b00c1444d00440c0601001c982c1d4013042200b0080703111050815004000c0004400000035800060040c0c00c01c181d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 536966753 1250 536965503 536965511
    0x5060402130e040602271f27050306040308040201120504020105030411030f07030506180705060703140c12032401021005062704050601051905010e042c0d021906 71
    0x1800d0035070190080a890584042251b02d10100c5001d4051a8030099031058914000180000405516401841007408080740c3c0c1c011100040c0d101c1c0311a900b40f45a01c442094959984070b0010905e01801102d08902080744001480159a000b43d8041b0312060280c200f8869481e050340000c1c22400084c02c010110540b00b0f8070685a907030f040c44005070000107002192000e40d82d90620565032242501c80501680c9c00320502c0f02040404120380b0103651020380014500700f51aa004c40b0703001544130400e000c80c0740910000c00c2d8160140a0302e1180e4414408003a02d078108200b451010381c1e0009a40b0802e0300c0364800e8507a841e42c02148200004500c2d40d130000c0c2c1d41d500e0402007620307600400458030500d09035200f6001211101e5806030301440c0240100e844984e200c90a10500c20a000d0800220364a6800100665841401c0279800b440c00a00081924401c420044000c0307928070700c2e0851501000b00000b0b40340402048880346e0302c0320a1000b0000c403028640d4000d21000c01c800e01400311ba445d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 536968003 1250 536966753 536966761
    0x60507030510030305180f130504030f0e030618031c0903142d1e1201140a090c0512072303100306050c0c03030c031806060919150b0a0305060402130e 66
    0x4410f581c086000c0050700c00300a100c0c540b101230703004241c200c030110302180c28610200e403401d1061584c0c4203201d0010780200617945840d164a00381400702114114240b008005103450a2000c011040c1d00481c070035000324901d2041e29028205128042100000700002c0c0141c0e0341310503000101f108144c482100442c041e000b4a403c2a440380b207140501c0e1003600c02c01000050340320b00403005001101040340c0c200f0150b600d804003c03c4400100c65400d41c03001800000380410055544201d6410303200d400c0c070b50700d81500715880e265029412103000c00456800d10a407038544029803440070345104060001460b52070903c010390a1000d01e8000681015912800a210301c03011b80c045901c6c9000140803a82c4a1400101034405644100e840050603050380c210303100d03c801d00180150265400902d109410fa44950340343c5040c0c240c08000b52021510359800d003100100c04206200a41444041c642d5210b00d512405030640e84007903c00340c05540f04003c042502003440d100181030342c05010364503c403515 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 536969253 1250 536968003 536968009
    0x506030a050105160e03010b01080f071b14150f070e011b0c1d0403050a030c210606031d07030803040f201203070b06011110060306050703051003030518 67
    0x10030380360050242d8600300074000041490a040d1030020010340e40d01516814800606003601d02100703425010420410100d00202c40802c01d840e8410311030310b0000303100c107060316420b449503010703e00c00d943c401084070300360203a44800c1c1b001c030b4060055511904c00600302400f07105410307807000740301c041045042c0d0030343c443d50303885080020440071080707104c00c00c031004504203103200100912070030814141c15040035001d1280070706900e10581c2c00d0f444050a1a00c3e052013030303000c0d04d080d220724420012154801d100382080d05000d54240e000729000080d40c00d05000700981220b4031800305e06c4000c07010b81202241e120000a26400303803640900d540380c0702d49440c0b61803031800c4141440200104281e401030210103c80800744580b1080860f030814040030072213080c82c0c4910400c40c015001513a8180043e005500808121810100c840704139074043d08019212000c0728140d070001c86500d070701c940600001e654140079540c4c024614170300c3c11583c10324550f406042c51055002000084002d160b04000d40d039 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 536970503 1250 536969253 536969263
    0x6010e060a092601180c0915050603190e2d01110a0c210e0f151204120807080106031509020f120f090a0b060310021909080102120109050603 62
    0x20240003004401d82d1001034a101142c0d00311400c01070f540c64450f40407003803c019883c81c0e4806400c40d000840c0a030034074150101a2000d43c081c50880d8040800c0002d981d120000110300c602062002031556440b03450740c031820b450b05a6a00c011f10342c41145854404400d075240c9412000c038107004001d120640380c08090262000280400354032201284980e1210780000c51074003490f104002a551181d8103540400045c5161483c260000304809118001810154110010355100800d440c00701040f905c60f0f40c415900100d2481040004c1c40284010018030041c0c00300080c08030705000e1914030701140010f0202205219031401c15031101e0100c00301d00451400d84010b0041c000c8190b56440d035041c200042c0780d101094541712820072100140c40010070602d0b040c0941882c102500c0a40b40039220000300200261903a60b042c00740340304d058224405803000301a1600d500e010704080130440600a0268042941320080d50f074010419025071110f001d6820341035800d4100d00095940352080401c0c030741 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 536971753 1250 536970503 536970509
    0x5100906030b04180f030305010f0f050d1104050705180604060804032304030803072304140402040f0e2401021903020a020d05010626030405010c1502030a061d06010e060a09 76
    0x26084e0403400300300340550003102c490702502a880520150340c0c0e800d14000d51603151b1107143c640142d6090140528a884e0000c554154000e0703400c1c034464541ca00002d411910103403604008214005030560b02c0c400500e02d8450050000c6814504183c9440009049680c009000500300284400201140450089124400420704901079111512031401c004a50b10603111600030820813804402d0040c2820158050308020340c488609241c54030f900e502200d010403044981c025000d100102c1c85803100c42d10000140440703091001d031400e1414010a46208800000c40003130b0710010b40320000d903000103401e114041d02118040d444225420102e040504140009600541050041040c400d0541204080d1503628620035080000c1e201c002000c150368014000d015041800100400e60060345800b042e41d00030013500c9c2c2171091280039003040703900444a40e190a07036120380c288180500c85d4184caa000012141101c29400c01000180009041314620351146400280c800f41c8144150a10301c02 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 536973003 1250 536971753 536971781
    0x61d01020c0a031b120602070c090e0a060c02010204050301090f060b03060705070b0c0c0604050703330e07181a040204081504020402190305040218160e0d1e0b0105100906030b04 78
    0x1082c103645816800380d404100150b550030312070032001c01c05154ad8412880e41c410340e20010410100709603682d00191055400c28400d6550900001803203440038016051a9881807201030240c0300e4516004044070070b06405180a80c0c440720400100640100442d10519003100b07192809541c2c000c1e2294207031184000b0244240a05010300c020424001050f0040d24030913106004800c55080b0200d100250519281d42c86410040e03a42c680d06103690302406090304030030f0595600c5a202c40b091051b8100c210001d010083d540d00d01c1541e142c200c0744103c51400c000312015481c081c0313491a4240c0d1184500c89044103065101c0c049411580c0d90b90480b1141068400c007103866074503080340034005040032241a0700503200300d850310003010700c904901c611464201c19441c08000c45068122903040425802c04c0d0070036031521815000c01c000c941c0510a00151070090000141c15207440390711040180e20550003004101e9400820039004201742050310b015140c00030f00e180780040082c028018220180714 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 536974253 1250 536973003 536973029
    0x902060d0509012f0c01090b0f1006080c300c0a03060e04030504150215040b06030c010f02030306040c0513080d0f020607021e1501061d01020c0a031b 66
    0x40d05032070700414800d54550008006a25040589880042403081074a00410481c0804250040104060f1141c44000d60001440c61036503501d0801c0004192070044071100000101f0804149000031080503100511300080301742440c4030f6141490150f01c0d0015070710b001066403800144102c60b0007040074461140340c000345061150a05166620128400f00000e00701200480c0300c5088132052402036074183d4840e441d0510307008510340c101c85c0500c210011401400c2d20480f00b000d82c0f0404d2406a0301075494030006007050410945001d1104142c181804600104520220f4001c81a00d61090081e03802181c40024000c2c01c03551071241e1603940d081c6801c4807201107171b130001c0014000200d100b96201d0702000c5001000a0381d544800301d9085c00143c0c8a1100080a03581032080b102d01c88810004440c011085032803403040c0c0a00907000000002c524208160b00c2c28003501000719492028005010129a22408505140c81501000c1d0400303418852410f000c1e00242040c0c0001c00c4400c091300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 536975503 1250 536974253 536974267
    0x12030c052b0b04060b0706090f150609051f03080309030d0f0204151103030a0207020d120e030c0406030c1403030f04092906070311010f1d10110a050706090206 70
    0x70300d03984141c00e840c10100d46800400300b100c0c00c042c410740c000c0d2064501114280002983c8060281450020494000010300007910000b40d91031404640d00320a074a0120300a4100000d140465100401c0f40481010b40c02e13040d00030302401c9102d071042da078002400c1a96030b501c0440031031551258001d50004246003090000c0b01ea00c0d82e5000d272042d00c41812040d0800605500200c0d40e44202c03204010458100b00701042182d8020340c003c000f2240b0150960079a2135560311071a146001a40b030800104091103102c8141b45414010051a4841102e04220442c04c648900d07a00e584d450042000c641501081d0700d00307a80e410010f9030401148010565038440d00c0e5205200035004205207401070300c00001d44406e003a0f6000b0b803091800000504441d007040300e0340d28200d45803030400c682e1810955030f840e02061448040e0141c02903545a4080c1d02500203941501d442c9465401e41c2c0e4110480d180141b1741e010010214110340800e01507142c0b481d10303010181414030040446480003035020b00d0004401d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 536976753 1250 536975503 536975557
    0x528060b0f07211b030e0d0803040b0703021c05060f0613090b0f18060a03050f0f1b010801030b04061e0c0f0c0302121b0604110a060c12030c05 63
    0x41c9a06031007a10a11240030a00c1825000111184103043c08141c107111a0400d204084540e00c40a50007486e1242403503500c0004250400c6503004280c9150200204000510110035940c980082040c5800c42c078041c54484e810b50420646001000416180d41c0071032000c1c0c1c1c07090300030065014020400c503034805c008450084516020700c6010391003800d003918807419150203100c8518070035000c2c3c00c85c0c1c0c1c05400440c4100346e05400a00300d44c1d01c041c12600101c042001040aa000050a500144183d040d0344040b03519001440c928411031010026000d00d00d1799110258a0450354080d208058944a6180c420043c08050001340c030340b2404904100344c0300105402c0480e0b6210709840e43d40c16010b51101c2287c041c030301c111020f809a03014101c80ca204005210050201c10352450403900c4207a01e00a50b1400c045042d502a20000c01c1059040898540350300c04070020300041c1081e902200ca190f80701ca01c03031281882c03000103250b9240b03520507110f80268201c07040025040344044a9075824441 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 536978003 1250 536976753 536976757
    0x1020d050115051c27050609070902040531022b020a090b03100f0f060e0915040c09050405160f0e0102120a0c1e150528060b0f 56
    0x10310b5642e82201e981c1c0003030480c00364003298192584828403803c982160f591000180500c1000000400001c1c1d9021009010f000e04a00256104402038285410b01c414014074105039038019500c050701c10482000180c6d80ea04030010200007a88900400340380c1541152500e05d280350001407840c1c00010f02001003084044440700c010003400035680070207a0800c01130704a0041c000a640461594023003403012040050103103912036041c111035a4100d454550460703800c4201c8e803200505440201d000c0c888d058204520a200d0041911015800c0c98007041403882c0b550f054003d240596515046019113622070507440b0b014103400b0300305102504244184a40b11102003c0c0f0b01c00151141d0158201540701e001072907003005050340144140c2c0c2185952501c6540003891038000e0001d43c4003148001042d102c0c1c00165080040c3c03020b1031882d881d0914010b84080d40b030700d1242c0300b0701e040104900203410400340403600a0300c4500c01300902c503440e1000010041078001400810005c1050101080c417200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 536979253 1250 536978003 536978009
    0x1182901090e070b030405150603031b0609061506270d03020a030e0a060207050f0d12110d0201090228180b010e041a0114040b0a03061401140d090302010e01020d0501 73
    0x8210f901c41941c0310203e2040f4081550b00807c290000b111100e024151240d81c0b03500000300500740c0303290120350200c50501c10300c1c690070f80381d0a410450421081d0181072220a078403041245541260303a543c1d40014500f80b090404030442269100d8022040d5a0403503a00448000e011b4510100d07403009060103503440c0c1030701d10201c001a030312881d40d60701400d01540da0b004071601e5170014914241004c04116031340c491f0a07406c64000c81118001c04c082440c0d000b5403940c00444d9201e0140011410f0707011404c1048180f414025603041101940c0140c680ea0788090740c60541d1702c2d15100c5404900400700215200d68402140c400e0301c08081c00391042140d101c118811401d0301c8500d068a49441800f050b2100108948498840340503110140d50240b8410080114045400d40c901519541928400d81040c0780ea0740000760766071001e0101180c0301e07401c003032024802d0802444103291014546035520034080c03004119a22a0135030010075000f504a5001c5080e418025502e510313a4039844001403100348 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 536980503 1250 536979253 536979281
    0x602041509080304050f030a0b100e0a0e03040e040807060507080613050f0705030702030408070803040f091404060b040b03030403110a0b190c210807080601020118290109 75
    0x9404208400c0c090710181080701d00001c00345003050f00d0b080030807601030714800820390036015241500000400802d0701902c281c0003074403560103480c2810340c00c03880000000c00381480d0510340f19050240b0180042910210b03075030a08100044e0b55171b454607030000e000783e480003007009090030140302c0c5803038100242c60311401003540d0900208034984180010b03140d064034401c2504020b0710105119038860402903a100d156401140d241642d210045807030a485980b01c6030554001080901190401c11100341c01025000005d000034580c04d10400808000904001d00303495581c2d000da03000361183d412480303070244018284d948560380c03400c10481170035429080920440c030608010031800701d60000d50b20078040041c003000d1500014207040c0d0b0b00010501c0c0580300c50402c16031207003840240d000d0003a0740303038829940c405c02da060410014041160240c400d50659050003442031003100d400f00044039442d0080311030b40f00804181d400400c402501c220801b501031b00c0c00e0020843c4070781034000480840c501 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 536981753 1250 536980503 536980529
    0x2101202071a0604140105040c05120903040306230f0a1d070f0b04030507060e0a0e070c0311070506121509101809150f060b0c0f06090604021f09030f060204 69
    0x20401081395805c0c10200c21086040b40140007170b0401da44503203040324107400c2c400d02d0031504500c40c001c0780c7c2d011205404143c0c8009010300400555020342e031014541d040b40703620305072120038298800e0440180b02d51045405400040c030b43c503009401c09408180c00d0b90a42e014602882015501d920711402540d880004031140042e24004c54000c86040340c3d00a005041c03810708043d82101c102c0c58070104154004031b01c2e103004c0b8900140110407800342c282074640e40990f03210740c80c001d416421502c3c043c490a801a01c420099a243c210484134600c01140307240c0c0c1c01e40e454010011807450a50105500030050908205803c41007210407002e41c1e5900070311a405501000d040d406941b5241401002c0003085d40a205051502e07420410f42c0020703104001c554980c990456090710b401c40215101d81e40e00c80c1d050802850800c1c001150400040f402401c0b842c601034010580107110388030403a0524611807210881c8521a079424000755600880d2010b840d030490a103500a500540502e00c0b400d029 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 536983003 1250 536981753 536981761
    0xc0203060105032d0c041407080907030c1503091a01051203130302040c0324091508031b0f0d1d10020705040b13020c010515060a020a02101202071a 65
    0x30000da0b5000411036610031010081c4500d0284a0110b0b130000903030340c94841d611810180750b455008686040c04a5000d0280b545452640109401c8025100a2250308a5142440401e80c5080c01c04180c40e806505503100c194803031001c60051428034000740442e01d0201d0080510000708031500d04807001198107000903a2800c071901d46922400c00f400c01740724404002003005003001d4003c03c00b020040d05000400340c070443c0310000206140c1c24200c001c181c8429040c020301110384119102015001e1803025020700b1700d501d217542c910489035030080d0200410450b1480340c00400c00030381b9042c605400c0c2e0350350908201c0068142c050700c0e0100f800c40f440b16903030707000503082800310240c030f5000c142c0c000c003801d074546414440249030126880c1e0708400c2d520100f500545003800202400903202000103400d00d002d0111a2007055080b0744c0a00c500c50820601a46a500045031101d068040790188801140d02da0127965000254880322510303030000c120303201849410f82c6001c404d00d2024030b61001a0b50303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 536984253 1250 536983003 536983009
    0x1b030c0d0b12060708060120011d0d0905130b030d030e0613150905030903120408070504050c072907050714070501050706050c070206040e011805040b040b090c0a060c0203060105 78
    0x181c0100d10031003079000c0f6000405592060810a8101c1d40c1030400e00316044c0300c1100180329a407490200c074241d81d1601704d00c81407144000800300580382d0010103828003151a1400525046051007081d110303185141b4124000d0105602c05007603020020100e540e110609a0041e0141c0701c1a00d41c0c03002c2e40610000600e00c1055004900312503a842902ca5403000302065508004001c039900030f86407031109100300c40b242c1e02c040285c0c1039002e540c10700154886103060301c03d500c1c00b5203176004a4011400c3c41c0500001441d07900179100508d074820782c00400d440350704005006408410000f0042c0c1e10001d42400402038010f00100481401600c3d00780160900c60402a0b846403584507550001e582009004045140f9a00454108480104052605589030001a0180c220b0f400c05448080e401004209a2481020355004204088000e02c03261500c2e4484d100c540c2c00040c0701808482c5480d0020b00121030a12449040d040c00a0081c449591035401c01441011079801c200c1c080e10440f030002c01d043ca = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 536985503 1250 536984253 536984269
    0x301020405010c080307020a06060b04081b010c0210020a0807031d09010803030705220b1b060105030a030c050c0405041101110f060103060b060f03040b060418050d03051b030c0d0b 79
    0x201d040c1c503482d92040244d07840030b45607440185464110300070150790800040c020700070000100085c2c9546510346040609050410141c0032140c0360007d03075103c030740c0d5460b40c2084120040070b404590341e00607122004401d9041680144008103c44800a854810940c00019198201e170440c51070840952042062000545003801211003503402400041c0d00b0758030880050000706200080d14003032588c5a41034000c1c8000a401039a03880e9408100440c583c282c500d00b140e804001000140500d52420003c01d40b54100c1c460043c1c10004441200d209010042003d05c4441102410410003442c16003071905402d440d8100c41030000c2c0c036024503043c1a903000591a80c2984c0440042c0815928580e0b43c0c00081440c03110494011009205140000100300043c500c01c03800307241d4992140c940f101c10802298206240b8480c4904080103040220b94005000c9003144a1820b0000c0c5079111079085100e20050305480c0902c81000000f0046401d0151000d0020711440325401c1c030032450300400b000303100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 536986753 1250 536985503 536985509
    0x20d020a020f04090f150b011b0201050a031121060105091516170a0215191e0e100c03050c03070305040f060903020d0e040c02030904020702030106120515010503010204 74
    0x580c40580c100000d481c0241c4001020700000700001003203085503aa2182e040c1080d2025180d20441d00880d006694440c007848400d018240f80800440481001c004044000c124010341000b10106001e041035010380d004900d03400d018122a0380303a0300c2018888080c1d1172020381380d2078613414130b2001c5103165014506031440c1210040c42c0008102640500341903503000084c81c1d54031b002446039203002003401e42140d1240c1e642d241d030344240c2d03a4080c040041d1070039860081c1407900340424000c01006c045103201d4119005030120300070031101407074080c01040c031886030504100540342000c40e48001f00001000c0280c0003100c2d00602c201c100404050707003144c00440350584140e40030000511001c1c841d80c03295601500c140b0302880781507400e440e04000c0b1000350504501680c0140d20789960a50825840001c2120480d01400768800e5500c00035100d000b00d1220358000ca80103d50380301195800e412201c040c000000810300c1440881c1090760f42c0d42e05420490783c00782c17051800800c4509040c000c0b2419 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 536988003 1250 536986753 536986757
    0x81f0f0b09100f0e01120603080304081306020a11010806030f030f04030303110c03160830060d020f011b0203060405070e01081204030809010c12050406030e0705091305031c0c0f020d 80
    0x10040c2d134038005480401c0030150150f555940d03008044000380050028500881c050b6100b16194085070122401c6003006402000541d400445900300003030340c20745604032902e02031902519036282c51b00428905a032104400d0030600000c03485034440c0414001800880c1d00a540611810903980300440d040d1099044e1047c82d0b401c208502c110940600c421194440d11590490f8a003072045c00101c00911242081c1e151911b40d591144184211244000307900000212550181c03034149500042c0e0ba40a003c540605005550092000c07041d0f9510185511039000360039a07000749054600252034101070b0007090502c2e4003070400801c10800c00141c202014a00d046c015140900703544400e2003d03004000b03814100140b10900b500040c2403007400304151001615002c0d100c0741000006015034a080419450950011030100611740d109040d45402220b06903100301019070714100355055108005a442400e01f03222115601c050701d41e072062000300b410340c0d9424480400c0f100c040f611740162101d5040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 536989253 1250 536988003 536988017
    0x1a130e060424060906061202130e0603070801021809100303081b0c010f052205030304060207020411041401200318031609141303081f0f0b09100f 64
    0x685640c41da40c5070080092071040001c002000c464043d120283c00000b1010303102c00c0c04101554200180003100d5031005000d40c03c2101d449040319010065105207018140c02a010030300343d807004d02001000d42103190081d540d911081ca640420321180c0008180191042c10014512110341060341042e41c5c0d269460303c503071384c80c2e0440c1800d0743c0105500f01710f88910704110b410010007007486110a00c5010202c0031a040c502043d00e10441141540c5032160365402100203000203201200b2654000d50102c00140c0b56040d500100303005003900410140c01c450009800b1400c1d40c1098404030001c00e090b640c00740c030000394590140700c1c0c0990707418210095105100040101d02403800c9401c030340c0c0c00541180c204a06031040351380d424105500030946036940c1c94840c1c100003080040f16502024032415000e8603c40c0d554002c001c02c10040405860319030040c004079106000c07400c80c1d8001c06100c03ca010032582c031400710100961121050b20b1141c0c000c07010b41169240902e11003c03011140d52554a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 536990503 1250 536989253 536989261
    0x8100b0301140412020607111911210f2b02211b0d020d120b030109140c0d0308070c06020c0d0c1203020304050304031e061a130e06 58
    0x1408028400540c19501c500e41034004584000c140351045024020f0b20848483e0820b010742070890280c4501d0070090092440c0284000000d10110b070018202d080009481e047e041503500011a100240c1c2d0094200c04030001502d07020500480c014510000c1d54103031042141200e68456050180040308640042007403010304060708400446056130050361400580b900162250000d100740080c00d40c00c0100344c3c0004401d010a0a05241c43d0280050905104004000e90384104d03d041d00c1080140d06c50782e441d001d20054106101c0154050b000384488091880c1c440103c100c0001104201d00c103214000070649003480c0c0010050341c06850345082c03501e95141c06c43d8150303020241510659020829151003001c100a0b01c2c00030b800c19034407400103540501d8601c8190010b05020710401d0b00600511003c01e80100480b003c50381c2c080d0466899032000050490041c040d8200034010741c1c42c01201d551712402203008a0280c4104070741421810b00c030340030940c0484100c43c2d008011544454001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 536991753 1250 536990503 536990533
    0x32a05010806040203280c09060905130e0a05160e060d15020a1b0b0f01060513060e1503070f0806030706051c090f050d200a030c240204150201050108 66
    0x1940c000000c40d44209403102c101b0350034800e8003410400e10310440c0e9202d22286c00580c0c03240b010000b61007580f134440045460440020240318900f5200403c40b541c2c1c010400180d9420021185216030080541e144410b08244403207442c1410300c03031014801102c0000581b01d00d0f110b141d40911a600c02c11940c81d4505d03117124032000b50082c02405050002c90003080c0c04040d01c83c10a4402184a07440261851500d8104450303600ca040c1d025606010050164841c042001c40e0b0741c40944100b4a88600303054900d00c0002c085038255800b031103010000000307001c03000383d00c880f50760515001519400c015840b10818555584a81c2c8142000030b402449015030102c00103d070907040c4c0d4019480403c103060a6103500035026074480003114107500a04100d8809a040b0381c030821002c107000d808401084802e05c000e03440e074401c40c9006081090440f24441046110001074044440301541809910349810354400250b01900810160025028a201640e0710501a16060303030b456001070450b4074003c0c40d01c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 536993003 1250 536991753 536991757
    0x150c02100c12110322020a09090809060f181903061d0f06010815010e0402090403030f0f020403051b0f06030405212d2b020301032a050108060402 64
    0x100800b0072084460500800e90240100003140f00410f01d07440d5a418100748030022000c00d8540c0301016180760040c000907a480316a20812a0f036055400710786c1090038500b140e4140b086410362503210202083e510f01e0b01100c03030003401c0725a008010807151500064100411030504d40c0c101110440c843c9418000101d66801c80025101002c43d010740c03040a00700ca25040c2100c0ca0720000385640310400403c8000002c010100b01100010003050b4603505003140340135a0b1800500282c0250040d03070204082611030780c45a1141a20b2200812440307084082030700123540540320a580602c11031000c00d80031031080300040705d800002481081140c0c0c8003002c0c05082d800c014403d8420780078825020343c2134045128040180040c01075400d54031402c4031240078034070140619007a0302e0045d00c4c0c40058031016030030495000e10000d4038401c02a01c0e110441c10701c440d00c007085000c015400400004201303c0a0201d1040790112100104004082a012407958020314401c0b140003802c103501290b424181640 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 536994253 1250 536993003 536993021
    0xf0a0c020a080a05220f0603091b0e090d020312071107030b070f1409031203180714181003020d0f020d14100903170601030b100c150c0210 61
    0x40e5030340c81c00c441e01c032480d894215460040100c0d2000514220002a1584901403010002c500b51242414030b0326200c001c2000d4068041495500c2100c107040c480501c50607040701c00340000142d0300903203410b030000b0580f5050b07900300014424007029103000c50001c401c2e80c41401416540d124560750340d08048540c0c1d01e00c08030001160191100c003201003860aa01c81d8401d48080d02d40403000701d1919001010004420070071008920203204040705030303a001c5640703000c00d00d039401025180d4840442e102c0d00b0f803408500e042a148506400000c600c0d0304490015040d080403240d04464410320381541030302e180221030140081800c0c074030600040c035041d00e608501901440564644010300d0380070440b0844241820f88071002a45030b62030382842c04000c001003101d202181404000880e540252802d203407461206010105100040d01592196000d000c0320000100250035544440c0d0300070300381c409000d02c15500201c0540381c81d29414514004c4282843c03640c3e000b4041c21040030843c000078070b4610 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 536995503 1250 536994253 536994257
    0xa02011e0c020306040819030608151005030703140c0402040509070c0602040b0a020303090c041107020402070f0602040b0d0608060f06060711040e011d01050103030c021c050a0c14090f0a0c 83
    0xc003007140540c0341000080c1c403075441a90425515484c0d001d118a03410002d0b41200301301820800b05000a450100e0703007801c101801c2403042550749419400405012068001c160188900ca82c00420300001000381001080c1079802d6480003c10079040c0410f0748914054640c0004041020070f0740c4601c07506099604500031640107040c03a403502e60048040e400300d001100168404018000303007100a1080c4c0d242071404880c2041024a8181c088069002d10307403000c3d208540c003040c9102441260300100c06c003582c1c4518115950354940100170300303640090010108291070001c1c04910b41200003000c03400b814100300e8562090350f07034400300040e550140000b240c9090031400c071010151100d0180ca160035000c81d0012424071600e2403880946590005480071580c102401000800d804c13076010745034541c058505142010243c04200d03211303401d204e4020580c0c483c0c00004801d1100c00c08072502a20820301158a1107600340080001c0307480c0580d60b00d17804d00e0700d400100b903e0840640c04820880703054 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 536996753 1250 536995503 536995517
    0x90c0a1d0a1211010f02070915090501060c0b090c0603010b160f2f240408101a0906220e070b04030506071d1c060f0f050106020a02011e 60
    0xd0404288522180d92150031040b0b0710204031401c02101a0500c210690b00786012154026005802580c40c0f40c18801d01010907076a29548411900a00c012801707010b0810050003030b5607566500030400c45a481040e92070750b4055001c6801800b01040381c80c3d042d43e00030000c030f041d6403c2040804199101c0b604510164641205510010301c110360201300047c001c98042c0c68900300088407030400001c40a0142c40d0131f849036040c0c0300036035400040c000490a10702d4043c12040c020242c1482c14491600185814840c5402c00004401b072900901c10152211920059250700c02e018009171510503903042d98084e0000144003580004001c019012005045000c030303070700340d02e50302d2542011055082524101c000150a0003401803c204860700320f4100e107402031007608182e803141d04a155404401d031054850b10640322a646c0e4403c1481c03800ca0300075004121071010059800000c10300070880e8100c140c01c00c1c000080321130020504600d03064041e120b520300403a042803084110112a1a41c9081c8414 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 536998003 1250 536996753 536996807
    0x203180f03060a0e0c030f0a152009011e0c0624061d09040b1305031306050c0709020a091403010e1203070e3a050129090c0a 55
    0xc00c4141e004400780c08001440071060158103007024400d6110386c0c000e50141c031002d56103c0c0d00003105c05213150425518201e811580940102a00c403c11011000e501e03150120800e134540d050041801c0d030801d0300c44070b04105060f088150200c45c10100740003c5409400004041012600158070b852040c03102010a02215201107001c102d09421060018500c42c0070300d42000321800c01020407100848000b12503241c03541e11180c140c00d004004680e003000c0e00b51a107040200801c02d4904c0c8070032910922101c2525070340010102c0e003002600c3c0c0610b02c03680c0070021348a80c01e4400c41c0c01c0112907030b507216881400c000b04104030312150b00e001c981540da40c18090070b00400034000145030840004070140c0d81c0c1080d1400612001e440c44034580b282c900c40500c054403400ba066120a5404101c00c4250300e00b0b0000b4903844000d850500103032031b9509245103400390406042100340d1040d000c0d005020500303180070901a000200300c1e503c03030341160304014204155000300700001c03107840c00700425105020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 536999253 1250 536998003 536998009
    0x9092d02090c090103150b031602071d090d0918021806120613050c19030b03060103051e0105060607111c051b0301021306210e0313080a030203180f 65
    0x10220b81440c80d1200124480d4042d60341805210344034902928030102c914101100c0c125203200103000300311340c81a0b580e01510024024040000100a10400d01e40040d03c200302d5400c021104071036000c150b009005421921a026642c100d0985081480b1401d000c0d000c200480c0c000e6208100c210840c0d880001c0003c816601d0f40020400c03144205400e0361603003012410310500002c410f0540c0c030380a0501080140003488002500c12100e511002c1092101407441c058008028112445805000b0840003105000c030000315886000a001c449540e040d40310410380d07007200c0c2c00f0750701564015400c106944c0800d228040039804100300400b0000400d01c090f9140806529501d001c5616412444898200381d1000320042481070040d4025031400041104d000d070203895500402090229440c503245d1407400c0600f0603860b04c001403d08100c0c6214048016030707030b078200e04481c0010b002013040110310070034045034940520380c1c160011803c298803002540f88080300d582406800142c51030700d010044d9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 537000503 1250 536999253 536999269
    0x20c031303030201060806191e0e010e0d02150a021308062a2b020d0f0501050a060c0302060a0506030a06021602011805031906020903010c090e0109092d02 68
    0x11400c05030484645280d45000b900b03440660b4814031305604190100620504541c0310f0303c0b0810442038000980c000ca490201001c0303c1641181081545000300200080005510080441d043c0d08100c800166448200700e80e00c1c40ea40f0782c0055120301c46404035003001c1564002e0110303400030fa0030110b800e9854051032450316900712102d01c4600c450700001540b080401000080c84203118041c58a0442000120028511001200f001580094101d80c000110b141d065411020303d8044c1800800050344404016080c20700581e4400d9000840000740140035050403000ca5130700d40c0241030283c3d1020105001441e000b0310300c9030140188640b41c0d0006815200800c2c2140c281031030f2442c440c1e15030000400d00d20b03045180000b880c240036018051643e000450122040d15920100100c06140c900b0320b003c0d0003150400c9805609003449444416008401c41099510405c00c0c040c25030303070301e90380401601e10389403011300030865809000b84285840400384040f81950740d1007540c003c0103603000c1402c039 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 537001753 1250 537000503 537000517
    0x10f140d0b19050708060d0210030f020f04050f1206061207050d03050415030b2103070f060902010831020616080c010f060f050f0109080708010609051608070e0103020c03 75
    0x32181c682240074002c0750b01e10580d0303002480c40c9021001c1d0324000c008100c0f101d04d034510281c40341c810340030000510f600c2030304a592035070f425810942d02c5044031201c01362a030f04940510340c49103044981007461410310700b1001c245510840d000b800c1640f075220500c07201420f2030300036558502690102043c175403a80140c80541c00d12996826a03210310300401a00c0b4510071071000400c040c14682c0022450f650280c0200d01e0002c01e444c00035680c41c070682428a14812044c00501601003e83c0000600c01c4d2a0300690b1414000e882d002e24940e40c078031004c0050340080284860303080604603001d000c19101404100c26030f1016120714500600c3c40580f4180c000c0c00c003000c0b1007010f00001c180c0e00b1450280161074034081084402d11443c1e0401098080e905114051640550fa880984001981c8589092401441140c094892064a9002060290819000b04e940b030600b0680031900c002000004100e21000d60f95a03215242c0b00c0d00b0086030b004a0315850503042540911441d0000c00040c8014080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 537003003 1250 537001753 537001771
    0x60d0216020a05041b080a02040e0408190c0309031b0503100b0307272403050a0501110c030a030e120a080f090f060c160f1217010f140d0b 61
    0x240d1a000c0c8104a6000000e401242c0a20309144070440c1040c185240140d041540c0d003042090b60b03444404400003070045511402096440d03000307210501c05450001c002c1c410107506040201220b80400351603284c140310000340002e07803603101000854058800c0009003002d00364140320055a64000a00d4024044a002101c07540c41070310b0201480d04001c0c1274010002220b907400f8039002c000c40d807491500d0780713001d4241305500c44108940c5c0564007180410840340c45510350402030307180c1c180a559040020401c0345d0561804508041400c0f591040e01c1d2084070b507500940c6408401d150403400342000325a491158400d101d095442d058120001e440e00b6105070340c03103000074a009000b900c2d462901400c4400c07503400c9086c1c190712502010a10713590200c58102030580d5025404103460701c00c1603281c00500b864441c455441c2c108403050101030488030745c540d211b00c03045500c02c1d24030740301761001c0c030405856460707070f100c10828a40198108810781b03400030302a198814840c1c1340c0e404200011150a11 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 537004253 1250 537003003 537003037
    0xb070312020d0b0405012c0916060f0e0d0c0320060d0903090515310b0a0e010e0901090f02120717090d0804140f070602030406021b0a030201030506060d02 68
    0x2c0f05041c0f03449040d00400703000f0052112a20303d0b03640f03074a5114801041c00309004070b49000404a8034200300c0151803115010a0301e90720350755603800416400320502e6402c0040c203500e00c0a141440c0040e8015015500450b8012449155541c2c0000c0480b005000d10b101c0300305000c2c18012503a450015190645610744042140c18491070000d0081085401643c4500d1a1220f0410300786a03407001d6801610681030f008280e807000c5000c04125040e404084015000440030124681c0c140c1d1003d0544280ca50b1940a45002e00ca801074442800c0e4024140d00024a94010828400e40350001c0c04217026806c3c005181c228000e0541203004000c8a001010030007642c8038103082d85000029591010452014200c40740c0544001480000c02400c003404100101d48500301003081809501146140c1108446041e641d030100651660402c0c4984400f50144440050494030642003180352800000c09451945055900540080101424058000f07a09005001401c2c20720320041250103100c0042c25 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 537005503 1250 537004253 537004271
    0x1e18010e0304290d0207021f23030402010f120f0f050f060a15050717070c060e060c030d111603180902070506040210030b0a060c060e0708070b070312020d 68
    0x210702000c03e40d103184680c4020602009120401e001d458409014040141e50f40107140000340c002c022403840540c04000c464042da035a1508924009041401405958007035002010b00708810301085502901180ba00c03881d5410b1280f003444109280e038005200060320f0600c40000340e0841d452600d111480503600c0e024040240c90000d20f1907071000c000c4030b0248000b13044c5100c605500340110640c50600602003a648e0410801808100701100344841d420345520003400c0038180440144902d101281d032071800b4060908000c070071210744c1c1c4c01c24001145400076052038800109880080c0c0b21a081c1b0074008641032943c540c0c000840f460281c1c0d0b500c01c2402c40c0801c41102c02c40c0c07960100c62194810848400019400700d42d207035010341c044030f134000da81c180d00a080e000f034118503d03803130360042c0c22420100c4c03150b41140d0321a91741e034005c8500700305081c6580d660554512290190b020300350b00141c420040261118000d08103244a80b51481d240402c101c0c0b61001d0383c00030103c103100152204401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 537006753 1250 537005503 537005519
    0xa06030c390302010501030c050d2604050409060f0c0f0512090a0606081018020a031e0606180b03061b0d020f040f06020c090c04170c1021051e18010e0304 68
    0x3000d40f00c214ac01035120407072942c0c1c43c3c00b13460041c04030007044904005829000d07201c0c101030782c00170031000c1c000b40070f803c01c145015001440c0c0800050085490708030001c1c0b60358454595080040800c0e12200c0c58200c5402d440c03041030b28001c040344c5852041a0701c040005030107000ea07600401d920001080442849414641610781c03e003d000880c00340008890003695600f180c40c02100e8001240b08580092204c2050200007111009060f042c142000050748051071990028807424048c000c0208480340010540c8540c404d8440088800c187c0114169682d40d280040001001c0c01400502c1d2030070180c14041143c115a00a40744415a0701c0200301d011340500038a241340700c08450055180c506000100e40c20f01482c0640c168058440c50000e98500082014036400c1600510048010711020801441041121076034640003c403030f0500c82c0481c01c3c50040e10700824003010b90303c108040361118109803886c020b180518061100046488407807083c03145401c0400e00f6005903960f14185004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 537008003 1250 537006753 537006773
    0xa0f050d05090112020c160602070626010b0f0c0123010b0a0f030b01030e0a0606090b0904030c0b07090e0f0f07020c0d02060c070e10050a06030c39030201050103 71
    0x3416080c08030030460050a80e901055888400364500f20043c1c43c3c4180690403803034110a01810030382c40040c10f1000c1502500002d804085400310340d14a01e13511240480304000904203505146603521070b50044c00356003400c60140c094000c400d15681d0502a00c8003006080d901c95005e07202400d503401c0f4201e0815a03200140300c0c0903048498174140f45c407040b4880288181000044001010303a15443d462040c0e220b60803500d1422142001c8411001460500400800192040149980c45d1080000240c1040d04d101881a078043d11001624580364540740815100146001c081198200c80851841080c900300d601410740c01c5903460b100d16001e6580d0300480c5024004805540c00b84000b0992662a079540350305966040e1082501d0700003e20100e464154a50011019008048100003292511008034011103408440d80e01c0301c55031341e0005604440285128000203500d03c142000c2440341044480724040404c85100c80001c1703c0304d220300e514113030000c0450044c0d440e000100184111307480e07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 537009253 1250 537008003 537008023
    0x7031407080c0c0103270c0915050405060d0201050f0f09090f040b0901051003030e0a0e0702031c0b0901140a05031902041a01050403120302040e0115030c0f081b07050a0f05 76
    0x904000283c0149240a110b00300e16104d075006d0690f0122210400440d50304400c010650020141b000802d4074110120b40310150050740d02551a000000f109032401022611141780c0613101e95241c0300030700c0201e0200c1e6000106080a204003040b4410310303038540c40ca1b103511409005403012410309041c075000c0b0781c1d49030144c00002c10784c0c1088280500d12840c000304404036549414207130345803114440801d2a0b0400765002c18030341c1491004100145401200a001181039610b0390807100340c04810b1441201c2c41200259002480c0c40d0052003507000252000003500320040c4141c18003503403900003a1030100c441101c102206010b800c4841141005c0c05012a00a44004091140e04400000800c0d502441c8800740580d86040c3e450600140079030304540c080e0842400e24201c641e110306181801106884110001034a850032101c0018407503000c8080b030a225070341d244c403281c03608001502a4a0314a41ca100749440803c01c01d400600d08010072562144904079001050403030381829030400080d10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 537010503 1250 537009253 537009257
    0x5070203012009040f180609150603030813050319050d0b0a030506060910121b060509030715022e050c030702030f0d0e03030f0103050c040b1507031407080c0c01 71
    0x1c01e1202c4400d150b4003034803404001500e00241c1e40b45519941c0c03010f0080e1515042c5504a01b036070000501905800a0400601402078041014094404034044510b1880090001008413010424171142606482034581c081d200712410075480521042c02c80c115500d4030808141c00003080c0c580c041142c0034203184103d045411110491a6840c1c2d00e03100d81c1d00401140c4111400c0000480903400d00031900f006c0c0119038086001d101551604c600c9040180800310b1001c0341c40302c80040d81074428800c4600511018000e00903444c0f8050303003844084108141c0100f0360207443c0c5003d01211101c80d02880d115443c540c1001040c0d117203480342040350000f510720141c41004008114400e40c0000071a0080d150520b07807a591102044448e038010a20b0717403c40300c0180000000d1000b401400600141603d00034000e40e404041d8402c02c20044070041c0285130740240c1480703e004503401000014000c03140c00fa0400c00010020210394a071590310540c000c803441440802c0101d1a40701c2040407056103c028 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 537011753 1250 537010503 537010541
    0x602070515120604090507180f0209030d0c0204020c0118060b0307060801171f0e0705190501200f0a110108131e0b13030806060406050406081b04060507020301 70
    0xe0703a210588034a4010785610040000410401d4480b81d00500e0b1440d0000d00359051181c03262800c200008945807a021513a040c0f4213201007070041c40c400c907801454014010240042c8580055401000307902d07007660b109074203200c45010a0000e0080c0c41c250482c0c607440401000caa07160070030445801d500b40e02c4c02544100420b000498108020302d05440c410f003000e1041101c41c1c024149000c1c140c8400485046641c5650220108660484d801540556007035440f0140c44005002101d0801502c2c2c0c501a055904e00b00a554010121483e0803000c0941e07120001c4940c00c1c0b030502c0d0082d11311000340240c2c042e0005905100c6459929a88041c09103044e442a00300812000400f6019940280004401e0024405090b1000407005442540048125142c0c64034080a00c42141c4060040e070124081c0300c00142c5c245000400c13a41520280c0e210b180c2400d080503070840b02003000405003c007180c40d8031038600c03c6001e00d4000c0c2c0010301a0341eaa035a039484440c03052500b5600d03030403a840000242 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 537013003 1250 537011753 537011779
    0x2130b3f030406080405030c010c0804150504022202160f1202120922061e0b04052808121305061e0c1005150907140a0804080705100606020705 63
    0x40304450843d8034a03c0c2c0070a0325184d50419904501c1071144e61031081d86806500c482c0c064221202c80c1c4607602072440c005200c8001c0c0c40c42020380f00202c500a510400f0300d42070428480d1908044824900c260000508003400c00040c3c81c0401c007051020380d0803202d4002000200004a00040103c0c1100e101030300608800e1604d020040c01041a058400c070b003030401c10302c01c10105400242034011540d1040c40310542c3ca508044403c1000307486150b1000040b03101041e80100b0348215002c843e4064184142c140030081c55400440d101d000e84006c8100800300010018000c0042c1c4900040700240f0139030320303054011074054440b402d0780501d001d03000900c001c80d6404c0b07008000c1034004190000003a9504500f900c80c505000c80380c401e08184038035000c00d00007028440c40f88090116810366141a55440d41d031820b40d0380c000004045100c1e21010042c0c00e400ba445003c600e030300b00c0c3c8550409801c00c291079480d10304040110392614466a5155070420503031740e041042c08014281074070442c9143c15 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 537014253 1250 537013003 537013129
    0x201093206151f0c0803130b161b02030a06050a1104060807091403060f15030a0309050f04140a0f020f0a0e090c0f2d121005011b02130b 60
    0x100c4540170340b1015000c40050701c9000c0b00140d9400c166171181d064400303480c02680104003805031b401d2000001d21044a40c020115500d4510701146400400510540d131955540e01d019100090980840c00e48810520300c038400510f000e4400fa10190b100e2018504d01044d0080000c1016400038818039a41079040d44191000300d41ca0780c014141c3d10580e42c0350fa41d49107002400d00e0840c14865054803c903ca60410b15a0140c1c1c00d406035a011580d101d40c010900040005807084501c182c1348c100e40d088003045030b0242d241e0003043c1790b0078070740c10241c00c10b503240c0c0380d000e01c94211400c10000b00301302042462a41c649500a16400b440d01d540b42414041244184001d900500100b0b541512400c400820701a145500d00c03d00413214040c026901d0b00710304040307400c1c3d2805071162020700443c041c01186540c0591040c80b07466082042c0302568144a07001c010f0507103103010222103016039401c1c0104182d00c0321450600394100d60f010b4021008903a1007281c84446503005060050785a908a07000740079 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 537015503 1250 537014253 537014267
    0x7031506180b040b09090c09180c0105160503040608040618080906090a1a040608071d010e0d140f07080a0b011509080706031a010201093206151f 64
    0xc040701000508500c148001c40c3c01482852140e50b402880d4404022044100081c10029154180c594042d280c584042030000d600040200124982203d000711b80c065105101815000d051055055000441a11014115030143c0c20040001e4500c01c100011701c034580c010b6095240701000d005220010640312004180200c402880c402d00e4001000041c642d51405108040e050721041d044890300111070303064a5500134402c1c4004512082c002070b000501800080c0314908528005101c554034030001120b01d4070f045041a036018000f111590b000ca8dc034020343d10350b2010220010040c14035a10b001600e004401c4d40b16103101c4c0d010760000c10004a070040e0301e40c11500200c0d9000341c15a1505026240c21820742c001c2e923518071a80c4c10001d012a03040e081000c0e60010718a80c480100350310070049090b128001c0c8058040001c880c541030440003421040070789a012290320340d101c00d20386000c05042c203500742c038030a0096084c50444407041c5001c4d04c2002e00552000f0b03807003c0105a4410241100c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 537016753 1250 537015503 537015539
    0x51e060d1506090f020903070501021c05031e040f0302060c09060f0901030209120604030315030b072007060804050d0c1208071403040b04230705190b07030207031506 73
    0x90405521040d64101c0d003500808058043c5540a00500484003501d100940080329014460310501d0300001d199400030a40d04016404401c400700070000484003582c4a51018018010700e054440303420140e01b2150703004034080c620611403d00c0381009410028038000001d4400c2840000802c541c01541e40d5020072201c56007010b00311942c658181000603070080c06404c881641110f014030340a4000304010035141d1243c2d200c0e0b00c007000700b014404e64100600d4110b0000a20b008008000b1401050241d440c6690790000300500d100c0d102c4240c8030442c00c100d410f50081011860140034031003080f0741030206030345003041440c0c840d201b9049a01c071030000c41c0c001d101700c038144035031403001c117000c64414507100c0c40d0464407460195aa0801c1c8ca41074480103000c40c0d00b940c0b0310f103103410751080f850b00c0103866080c40501c6800500320542450100710074680006914200c50961000004075184e424000d000c070b880c001d401070302c00207241d420840e40040000d810400c00c14508481030102500907000b403014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 537018003 1250 537016753 537016763
    0x10080d020a061e09141b010f0806030a23060a02070c06120f02070b0103020306061207090e0c031002030108070603090231090c0801180f1407031401051e060d 69
    0xc025000d180250f280325070340c40800c08240c02e142082c0b00780210741014903d40e4104c501181c1c0c1028044440952500e542180c4500049403803604004007485144200c1d041300c0b00400f59160071450341c1d207500b4031134003406a0b0500c5602000c132110f140201030010507130000c540b0609601c2c1619580e105250310846015041c103202c21b1000c80250b4088a0b403200b92069091041155109001e0400c0060220309200483c0719105c2d413800600103040800301070134100903403002001d40c14102000800034000404480a0038410302300d1001c81c0fa981000700720382028030b074840183c1e82d5050070140d034200b215075000a0103040c18603542c04016101c01e0020501c8018040d4811484002070b65100041100036959000703190800038001c041c4104103c460080b549403034003c01c07090f0010804813002c3e0040701005032650f110b1303019082c041108104201030204104041c2c40702075850740da40d0707201c01d03081d203040c40082c0c5c0d565420440c0315840d80d5002802d04003290f40d540b01ea403034000000742c40146a4000141 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 537019253 1250 537018003 537018011
    0xc090603060f15021203090102070209010605120c0c1203130b090a0503030403080a0603240506012a11090702061017100b0301020c032b0204030816080712020610080d020a06 76
    0x1001340300380700c0311a001c0a2405583c0c2e0702d040800c107890207500400d4003a48182e0925000040a5004408845480403410900c80159464070907410b250381001103080350900031400302c40940f0807080e000b11310030160f59224402c08185030410f126940c1009003840c1030340c2d00c10f2100d0f101240000007900d41c4954186003690250384d6100110340a0051584001c01565254205a40c0084000107402040412207401c016a50702c4000445541140c42c00c400940c5065404a1211084a014102240b13004100200208040d44003044d040300c012500382d00140c21000900c19400c3c40c2002160003001c41546040e0410052000305886541088500c034140b40e03507103448807468500390143c0e030781d850002d0f05898032494800180c00102003c60300f0048142c04242411a1903841c2e44248c0c0c0940e90408207060410020304056000213002c1e18003034415050901480340020751212030000e11251907400360101c0c0c01c221028125140254008450a410900b05043c40340d41c0018854800e541003c0041 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 537020503 1250 537019253 537019289
    0x12210806010503130215040608090607080114040203100509090a050106051504050409031205011d060a0e0606030a020904050a1e05152211070507060203040302030604020f0616060c090603060f 84
    0x507100046c41c0c031500c0c561190100300011a1078010703110030310419012054400907076070f801045072240c50074010003042c0740b06110078000300d00702540656403014100102140389602c0341e0000780a80b004959811041d0301c014000801c104083c015003004210a4452000d40180400d1038003050180e40140b600941d0b64070101c0051500c1907945480c0b41c0d1050004001c556125100280040310400942c1c52030940341003c21814100701049204840c116030702c0280b1a2034034405c0151562015140d2800550207010345101e60703946200740760007258201c1000940e54240214030360440c2d4012240d004040c90311080021300e4003641d054600364a0111405590301000c080d40329241d1203035540e1414200d02d0701010025020741c0c1030007890390902450840312182d96a0700b04030383d40d00c41c074080290181c00c2800803400605204115041440006280b03e003898030350040602c0840003d50291215512510304c103480f150007030314a8000d40f16903c1d05121290606011220f041c20317910038040f4000c1c144010f5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 537021753 1250 537020503 537020509
    0x1009020904091a0601140f1206190b070b060103050420040f1b200d030c03060803120712140c070f050d020f0105010b040e160306122108060105031302 66
    0x1c034403040d500c0300c038500d20303682d42c400e032a003e60f14100d0b052800f08200d01c0c0044404500c032800d0360104c0041e60401ea03c0d02102e400840c048000162401b0742100007200488000d240c40f842d07041c0030300b1640c51500e031100300c0303030070016040d0101408540c1454038101c103120101e8100c18500e00b1031085060f903005143d2044000c5401814a50213540d5410f02d00701c03442c2466002d040c00c1542c0d40c451695060840346402001e1184101700c508600042d50048401c1c01a140c000c1d048171305480281d04000031040e55074055241554401c51540800c242c0350410050541d810003201c0414110fa04410000c580a0030018014040e020f007400b071b05400302280c810f0800c000e540342a4080380d17118080e20500304000328080c1d9500f6105442c041d465003000004507958010100362001c031400c00c5803100310380d226500c0042c5200d070700140f290300b015240c0a000c900c1c3d1415588040e0f001c0e20940710301d180b003862109060b0000128400301c808004c1c004081c4000c0d0380c0d200341540e420040381c09220007100118400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 537023003 1250 537021753 537021761
    0x80618040201121a03010c030509190201020309060d0f0c05040f0b16050d080a0f0c0e09180d0e1201020408071703130b07050f060402011b14030313031101051009020904 74
    0x1c030f042d6410850700340403140810303e4504c2d80640940080c800f240b171244041e001e9403c02c641c242c0c89944011030048001950b040340054603401801642d00d04801000418465403041101451954544840305c0c861150703840741503030041d001d251050a00381460b0100b40c0c0d0714040c2c41b40710b1840001040c14a4509a03814400c880b0507841012214003000c582001b0f440d00208584298140385428032102170b9083c0e5016054400c02a41c2d038030f4102084c1e003000c101416001400c0c0b034502c203001c0300000c2400e0740c040020f80054202621249007001d4804104109010f00d4007080742564010b120420000c800020a00c041c0c59004810703100c11000d848079a407540c091143c03414490700d201d50000440a5000313004025550081d01606e074010074186009617500c1341624001c1c00684000c0070552418425271120042d9032054403090001041103c429103035400546014406007074003204101019000084440c1c90300c0308100a00044c504006c420079507102da07100f10110a500001d0700c00c100d544540c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 537024253 1250 537023003 537023027
    0x80c1305060d05271203090f0703141006030b0c070201050d0f02030103030e090721020409060f0512070e27011e05060f060712020109020312070c06080618040201 71
    0x4150b21103a0400a180180c90155212061000000703403280880244819058060900c1030082c0080b0419056644440e80018000076880c05144e8201c1da0401040c00280000c60081d99281580310010700c0399400d002c000310384c40344001d00d0304808200046860a00c1644680108030642d168000f90005940c6031007195a050390403482d21703600c03928a09030356010f103040c3c0780a50b80740b404181c1208240030350070340242e40e03034804950101101c2814001d212800c0401103152200503060554801e500c2040c5c1d102c940001d4000800c1d0403040c880c5080c03115100002006242c010b24030b0901d855051a407402028002d00480611034640403008540174620032408059600208203605030f00300000c40c40104200703040111070030f00300440c0180ca416002e07100d081d903004003035501e4003802d2343d114003410010b00702c820190354070381c818030001d65014040a0109a03080d08126901c400720701c0d040000c40c410307030054414407000905000c500d403100c08074103001e031500640780303590343d11240010707603545603411 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 537025503 1250 537024253 537024259
    0x61110050606131706060f06070b2208040e070503040b010b0c03040e010b0901180602030a08092803031b0c03031e0f02040830031b0304110916080c1305 67
    0x14074005007001d1004c0c8000c949904000a441741c50b19003138208481304002c4601103910a505000a8000c10a17009030540c124005020844c0c1f649003111180883c4517864505036140b4502080810448549a080b2507104689141841c82e52503d50344907051180c040c020704040010202d99610304010420444020700002c004000c4a9a5160304d0340c1d049070300003201e03680040d8650502142c1a83e40e0312044040d9102c43d000f56013041841141264030300c10081032500c81c0e103d00003944041c801e5007052000300f030385040341d41d14508039641406020340d80c03000ca0184014034442c440c103000c0380d440b20910080e00d0b1b2614010544040c81d5a05900144203401040039013454400c6070101040958010300c00c9031b91210903140b08080c144940d00c03805030790300350f036001410b1900410000088668011540411480c2c500d20394400c08400c6000c0d0f0f6001150b00703c43c06101e141b9a00503920346181441d41c0644004208181c1100b00a001080e4000190003200d40c1140894074940411364800040e0150a0103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 537026753 1250 537025503 537025537
    0xc050c06030f04050c040c0f0c06020706050f01031704031101030507030e070f0810020c0303071b050703030306031a07120203070c170310150212030402011205090a0606061110050606 80
    0x20750400045001e5604030b410740705514460703403103081501948001c1f01854584d8840403211000c180c4486581401c203c40c6582d0801c9030b08005503c51180c0740c0141102c0149221941c150300c1c0c040c03c1303481513080c005070f038807010301c81000000d00d490f01700340540c0d0007883d000c0780726201e66005401a000d05400084103015449010503103450f01800c2c40101c0b07410b8000c44030341c0d1030321003a03010881c42800344141940d001000001c2006020341003050944102c1d403603112032405140c03100c0d400c0c4506c0b070300210000303903ca51301002031220000010740000381080c1961f81c6400c1c1180301601a8420f2480c02005c40e80110000d01128011004080c5007504611692100d0207650041122030744119446052020f45000100d92950541001c0400b003199030003e00c0c1401c1000031403011a000280100d04002d608003006138051268020180a15410030007007694080920b044426200725800940c00c10003038172894602180005080441c500c8498000650780e154a000b140071480f4087d24583e1010007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 537028003 1250 537026753 537026761
    0x2071e0308040209070507020108040b0709030c09061d010602030a0c02120d0c1a280b04020c100e12040e04050705060c0706030b01080103020d060e0c030f030a1b0506070c050c0603 79
    0x7801034070881c4216500c12541c0da50351001d03201402142800390001e042c0c0d00000380042c082c016060f400200505000d940c2c56035940c0d88041c10721041e008554507c1d15500c040008888241030111144240005403186604044009540380154155082049200d200f840c3c1036458111011000c80e1400040d00d005c8140074001a0410002c1d0204840465041300420385c00031111100c2400303120f4410070f0009130b00341810304c00c0140d01010300840c42d180d42d4a4050314175a4507480245260b801c0c840140082c0800490840704680310082000310980041d808001d00000010803601a2410f80340003180d642c03071704c1c14500d240800980059070882400110481c8003c8000303442c82c01c032255a64180000c120107030044401402c280f0000350080c02046203a800a00e250b003141480a80940c12502208400400070b86080c002007004802900300090710109168800d400c11140601003552003002c10860780c6050742c83c01c00509140c10414015664002c20906000c10760114400408494503410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 537029253 1250 537028003 537028007
    0x12020c0c010905030307110907021c090e0906070801150c0f030908160806070c210809010b010309050a06090f080f030f07030c0827010203010f050a0807030b01050402071e03 76
    0x120025031400724918440c00101032074000210b403003072a0721507980000101030a0034030008102c0500500c00354000c540342200008404c03001d2044203000b90351040083c520b080c155500101c006000200e59410441c1005100350700040301c141100d003120704a482811000070103c1d207403034010800811648180600d5000c0c5540104c4040c103403185403017555641e220b60b1520001d4010300d8412424207402c910005003800e03001e514001001c40c054240901018449100061910040071311a40481d2100301480171400091103051090003003030038100020b00b00c070340f1010781d80c000c0b004008001c5600c0d0160101006610300c502e41038644c0c0809a0340d124006e000740500030782c1084402240120003c0e00142d003e0f8428028410900c0e4142c5072807515071038075110030403081c41806540444c200101294100d03280240b00860003002c4070005200c1e482e041c4001c201a21540c1d500141190b03100280500c0030901000d0f044d4111541140c0050351500c0d6403605c0d0300080924844150300c51191710211051503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 537030503 1250 537029253 537029263
    0x10e0303160f1d060c1f05071103040306110c0f0102040e0601140304020904020604050d060e150709150e10030903090506130e1905041212050c120712020c 68
    0x2404214001c031040c01010202c1e0000711658041c40052610108241c004082201000c9240b2024022614051001441c0c40c504071050f00d2503d98401700c0b00c0e403008030f01c0c90780c07081940140340d620300701c04050b001c210a6a901d00443c040130f00700541e910712003040d001c619800c039800e05596005403144a020104900e0003034210384a0201d40c0300d041d80c0091815803040420a0250214007030341c030300f5610749800f8070a0181004000b240c2003141000041455500d18040a000d281310b80e40c0401d10b0041d090859003414031304522010030b059000f080c401503680090075502560521070f03284020039041e40c0221244080d1410071f0b0341102d605d681c0201f655074503405c00c5810900030344602d8940c6c4d5440041c440d20f4450076003904c0000c0c90901041c414103945e0046076404c1080021651010080c114000c2d08884054808131400054000c030030190540043c101480e803403401400308580e00d0f000110080354494601c0c0c2c4c00c1914091000a0907280c02444030449c91900100119102c4000b50401a518 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 537031753 1250 537030503 537030511
    0x60b0316080703151e0e07030b010f03050705091e09010b06030a1b020d02031605071703030403110c0a0e04210305060103060f0302060f030709120c03030e0d0f140f010e0303 76
    0x2802802502041c004818040c0c4025030561003041505c500e100d4003d20000c2440c072000c841e0700c0c05289000000f00b580818614003030046103500021131895464420710b41901540700320b001d003000800b004802c10700070504400c0d482400a0f8483c2503a145d0441c1401040094690340d03205201006000700143d560303204a26107219003030184090f502c0d0410036680d0369029103071440141e008010380c54034154540c151051384ca00c18400c9030b80240e180d440c0d54031100c00802c05003600c1e502c00f00c100014141d005040038143c540400180100c01c6507800031a400a56a00401c1669407201000c20b040010080781190403000c551003a880d03d003442c54006020b001c0507151240040e0410070041517070741925180c40201d90f0300030462498040000d60a603481d40008010a00740051701c04001100520025580b503810700c03494402150740e00b5840c3c058610801c031008240203002644000000079265000c1c05c03655600841003a801e6040781913034628000150780c0001c0c0550801461400200c0000003441c02 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 537033003 1250 537031753 537031763
    0x20f0702010908060405100c12060b070b01052b031403100f0816140a1d06030601060903080a1409030a0f051905070b18040c020c0f03010c0c060b0316080703 69
    0x740903039600e820381d03035070130251005042030b0801c039000400705600d035103d400fa43c04a8104184422a14a403000898640d5031000c0541036000440004003c0c9108080380581f00444100038881426400e0b201d161991804e030326503c0700001d10a0042c0b5020749010303141101e584c025141d80340752a00e55410b00c0d40030307807203414402c1721018000301d049640843c616145c0c0a07440c0ca00e201e0b5502d010401890140c0c0f0b5108507810002c000d5001c58521902031070100c090400301412581030410100385454401c050348070504001c04200c050000500020031102003510350f141004c0c01482030007900c603c510426164035414800c14003c03000b040744da80000c40c444c501400a840d030380750442d803c1c08171a901c0324500400e9504540700600002050b0000381180326100d15140c0c605040c078202240884003c080c02c60701590051401018030b00c1c3c40c142c80405000c0c10b0b0000d06c5031010703030b00001d013a0400401004000301d80390980c0300c025032001c020391401400703840d503240c07401a5181c080b5620341000d0b000a403a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 537034253 1250 537033003 537033017
    0x50a02100227010302030105011d120312041407060c080c010f02040f061103030c030412020705041d010506010306180f110a0e030f010507090b0306031606031b0e0904080306030a06020f070201 84
    0x3043d0b00038400d4078102d075010303100c0ca0790191b03050304010756402024002c140e0115451141d40c261101c00c202411115903411064402810b00303003022344101c0c5001d035008100b68841e00050001946c021340005d00682d018441030384602442060f1409844080c05c0302405c103201080c0010028000580f0344101d8855481d5a280c1c100c1421890b500da101c211201400300000708041800200194070b0900900464410350380155107980005003960800007089102940c82108a10220310a00c100da41002003400c00b0000180ba1421555003490b0f001040504c103a5501880703000c651160b00124003808801441550b00d003801c50025001d1003034003604500038441c0d43c1c000802c2001c140703d00c501034107080c0c84000e50a403802c50148100d500003042c403600750150030150501c1031103848a02c2c02070400e40d1008611a0f070119a02c1c4012045040070703400b0411f04821030042510f5104c402900203070002d1200381c4e260b036503101091a2200c4210300408040c400120681d00d9010700c000f82854502c01d0740c41c20 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 537035503 1250 537034253 537034327
    0x111b0106090e120403110d0605040b0106090617040b0c070f06090b1305070b0a050d0203070f0210091a1b04060302030415110913150803070c080d050406050a021002 72
    0x50fa40300e040d06800000030504000610125402c000b010007400c00080c195100b12040380d99101c02c0d80c0c0e058404413400621fa000601115410840107006400075142c0940a6240d0074101e1401c808050400780c00300980c940800c015403107200460b0040c6420100c00480500d69240400041040e02400d41c0c106124801080703410200c964103645a9810000078075000d82455480700417079010300044018008104800b468419081c00514132404213510b072035507000000d002c0642000342e01c0c1d005420a6280c09401e500240102000b1026042c1e800c903c5891503541030400500c0700c0e0207031010b600c04640403c00013080d65140c0c0045214601c110b42c48003156041c54001c005848401c40e201c00a80c01c00d01c100c2c1c0d4a802d00d03a40040d80b0303621411010664400f03098004031682141c0d000300c0c410390400aa490b080c04900e41e4808000c0c0401801000b0b1603961072001001802203015010800c54002185000c00e80300300b1038800102d0421000315034843c0c0d15070595001901380d0600e0106224000019 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 537036753 1250 537035503 537035531
    0x200f0106120507030809040204050a0308030906090115140a0e0c0a031a0a0303080601030f050108030405090606090f060a090305011d010b1f0c02060409050c120a0c020d03111b010609 80
    0x8007441e60050003803582a003141c2d10504250000034006800560074403002400341e0742c80301040c00460080c0300007952410094091810b14000030401031041e81401120f1070b00405a10b4a202158422011179a600f10440e001902c40100c42d440101d0000c4031106105c001e04040d0b00602e003c0d04261820807001c402004031400000c030380c0b4922940024500b031b08001281c020003501c0d41c0100145000160502c0140c086800c0b00c0c42a04284503941c800b003401d10076802c040100c1c0f60403480840e80c0324205280480010345490020700c000e405002e004c9401503280e0f000d40c2004001d913070f120b0028041c10300610b00030405c1100302e8045c50340070740c28090b220715542000c621000d02c0d4681510648814071115000340c03105901d46100b01e0300b040040000003a040007512506000302e0750800c0a603500d180141c1450000ca80107840c0c851041e107400603c3d4100c40e0005904800200c00307040110b415040300c031280343c05002315030103542010021101c0d028590010341c4040140c0302110300c20841450320f4804 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 537038003 1250 537036753 537036779
    0x204061704020922020307080c040b0a080607030903020f0f1c05120601050a11031324120911040e0c0108011e12060b0a0303050c01110c0a030f200f0106 67
    0x280d0002e8020020850500c01d02480f440b144a001c0c040884c01346503680802e03c0c000301a03202400c4c4c6c0c0c004160107403003841c05008200207140300301c400b41030303050400845c16224000076140c18281503039142c0140030103009000c249891018901903c201d400c261008039150481c007440d00c0a601c44901c031200d081c030f00600030754404148080c40c951890380c0d81e000640303a40c0e2040c0c1c820014419151402c0c0c0c8030040420040c10f403091181c0c2c0300c1907000c1c50205403c882766040803000e41502141c6c50708080c021380c0610207051601c1159404184188241840e1107000c0100ba80c164000c0c0c14000c800c11000000590226880c1081c0e039004a10703030b0b803564246032040c1d680b416010442091030081041c1c211802428000740e024000000e04d0080c500c6c00a0074400c250380c0114045280800c00364900c00007131149000784600040c40b14940400142e489441c1ca9118070010306200c1c82c103d42c520f12920071024417030070b6000c08003155454a200620340f0359503c484800c40300c0a41c2090300c04120782c1031000c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 537039253 1250 537038003 537038011
    0x30e04020304120c080423120f060a24060c031d01020a020d0507090507120b06030f0f130210020c040f06080304031212020d1d010c0509101b0602040617 67
    0x6440b808100c03c43c0b00484064030669801d603043c0341c0601c17003c14180032111505540b0000c101c41108034a4945080c06103454030001c501455420032240f0541203940410880e50129031000006400d01e03001c00d4180810b000074101c50b01c03441250001003001c94002110380010740c0aa1140355107032007024844070303081c1c0300d610000740141c10600c0c071000142410703404000d00c035118000745d07661030742c40750402d0040b117004460030400142c0041818a0b809814442d14911840a03030f078041c0f452424201c0100390320707000b03450100c410140c100040c06100c800700c0380010b103940c01080c00070309507180d40000396595070710f22030288520303d03004600c84015050f2007100c0403200c10501a508003455078440c4920030213460f030000240240700304c030860500c00c00e10060884609100002a0711103605a05114118031224100440d80c50320542c4240a5001000e4841c41841103465406403080c03010200c516001c038008188110740032800e9501003010540190066409581c0c512031343d100e40c250850f4400b40191 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 537040503 1250 537039253 537039263
    0x1c090f09450303110a021c18061d04060b03060a271d0607082e050f010c0209010f05091b09010507140307030207140a0303090e04260304030e04020304 66
    0x1440300961070486800c08203114028240052410b07120040050503900c00790810b001030b0400c40148802d403107007a030400034900f010702d059444200f03580711006000d08540108414482c80da012946120b03400d440e5031480c1000503100340310942e0345841114041c1c01c161202c80c490302c503500022030300140385040c041000b420049a01c210080c07018007c4000c110700890043d00f01146450f11900c020304200d0540030740322580d00c0182d107180c48460b0100c5400302e0b40e02c03840c0e180c2c03180c201303400c109408004003819903200300c0b56000d070421900010707151301c91188002900400e8040001540f003200e20b10100484606440750251603552004500811850017503c0d03910703540a120031415544120003828081d441b0703444040c3c03010102081c10345107070031200c0300f2030050b48800030074051401e00140325407410701c0607600b034a00207056590240c200005070246410352000d1800040501608048240d41d910780c01095100c444203150700d050055100303c40c10b81c04109114500d050b50306282c402c0741d04c110b03000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 537041753 1250 537040503 537040601
    0x2303010614130515090c0301150507110112022a07060813061a04020415090e0105150d02090a2306090616050f0f0705030705060c1c090f09 61
    0x291030b190002c04014000c0301da2811000c2c04003c03e0303203580c800b69010306c0c0b104000b541c5941c58518142d810405043c0f03094208402404898001f4131014014030702c01400342060b609141507000c401e0024043d0f030500400e0001a1001d4240c50540303240e014000202e500291031903d030311030301d00f07030b4006009580303881c000c04032048801d002c950580c0c0520707400e400656080905040c04030004d004d0307070010340040440c4001c0d210407100c1650000c91030001403400e080c0141c41076240100041c404036816800e280f5518000070f50b2104901c050f812641d190200400c2030b44600e485010f207030440e16500503440c1d290001d101040c021403400f001515103e000040c549460030b106040004011811004200d80342d10031520503541d08031090106981c0401c00300010400c0300e250130300301407500080d0303403020b4050401003000400c0c094000c07030800f518084006400c0040f8440709801c032081c0c20303594000303c02300040140200ea04003c07a0046214011f208000c0c2c1130441c144600f5500c44a04028081e469143d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 537043003 1250 537041753 537041779
    0xd0b0106110c090a02040905130b0c090604030210021507110606060f070b150a05040e030a030b010c08030108010f051501170606131d010e2e2303010614 67
    0x100700d0907030403100007000030b036030000062201155584200342c403030040c140d8005c01c0910400c121031150662201d00700040032512800340d121080c03030450150064201020020744442c1e00c1d22507104482c001c6074060301c0c850213444244002904c508002d4a6115444403000c0404c81c0c152140d0303008079074000703070001400c0c4e80c1d1591420000e850340701c464038860790002407002c0000303c1c0000760510700c200c1304281d5039280980d011003088000c0c80c1e5500310309e00c10b518001c040012200700100744c1e004030302c0a0038001250f48020005071002260321200a0200c0e00000000c101c0316810340007503950700c0e001074060010b070b2a0041c101c50185140e04240340084c00c10340c40309a1011226810782d80014020344681e140194648a40071b420701a82c011039000800706508003084400aa2500d00518074200542003c1c00c4c1040340352001000c0880041c01c28013000a005030241486603200010200708480b07010001c13546a501c00c0030421a9200c0e44603502c1c0c41c0000441814680a4200d09040101402e6500391 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 537044253 1250 537043003 537043007
    0x50c0603070908030d0c02010617030f0309030c071205010b0f0108040303090c0f0b13090b0a09050901060e15010906050c0706031d0d0810051906300b0108060d0b0106 73
    0x14020001c00c42040300c00105400c0034001450151703400c01c0c01040005000d84040e0a455055106840c1411644540d6079030032008004c1c0e5641c0c0301c0444c8002e40e280c035071523461407030b60280800d0740a0794000d290000074070304c013020b00c14264980f1a01c000c0c454102d051042101102c814517407a40414a03010020b400288250700c00701c00c2c00d120340c04420640d91903d03c1400c0c4030310306802040c04108002020000d0032a00071070300c4014130380701c5800e004000b400e40c01b03c0e240318001d200c4c0c0c80341c1580300d00c0460309d001c60030f402060103480702000000769460001c600c50703a48440000050301040b11b20a0201c0d00c180b20b28219584e07081514010141c20b45012011002804003801d040e65503c8030f0100d42015a8040c000510341e404c0955407544d5505005441c808000d0984c0e00251056002c0f482c00c046484030b15180c2002c8890700d00b003040c034100135041a9048400016940100314801c10302d80031248885038400c0d60254020386c0c500c0714035a40d0000307000a41003403080103803007045003c1c01044418 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 537045503 1250 537044253 537044257
    0x3030807050a1e020d390f02060f180102070302150c15011e08010203130303020906070c080303012d03020f01110f060a0c1805040c140705030a020d02030304050c06 72
    0x42441d140c10f00c10f090554021540c00c0c50082402030050b04a480c0c080c481c60703844000da082124808a00b455552850a40058404001c204100420394016484014810640c0e4011001c0e41c01402c15a80d030000000b1420241d03002c2480c11441a0120100f450a944005503540c15258040c00120148411010f45581d80c1c0180c081c0490a114210140064014280c800f500800c040002d4803254640c00b40c240c890f141440c6c004c440181e105104002c072001c1c00c01d008040045d010b04005039a94005170100e00c65200741c140291002c146030a00144160000005604941c0c01e04082e1180ba0f425101c00286140000d00c4900c048031887d0003803000d45801d91140880e03103014102150804c03414103400c0d041c0040a03540407000d4100c0020403c9520650287e14501c0103030349442c2c094840715907880300150702180100c0d40074036038868040346a5070241c40d803502d001003030300d1902e612200f592501550320b03403240170721300d00500035045010300b8140000180c900444d1b111000c0c20351201c0b051309000c5c442d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 537046753 1250 537045503 537045517
    0x6061e0818070f080102090f1c1b12150c0f200a020d030c03020c0a0308030414010f06030501020316090803120a090c122a05040f200409150303080705 66
    0x6005060002030070b0400105008018002113001680340c180c9202001126030745071494900131240d41d403a0702c002000780b94240b0b038010740c040c07914814054101d1030303103080d0501900a40710304407c0075031550070720003880340a00607298001c0042c0092607c1312070464034008010380503400b10300c83c640d40d11408a14844494080c01018046a8a9000c2030300019a0351440000560100f92804159800c1c0365062050f6180400305403001440203145555030401d42c40000c00180c900d480f510b4903803800b010290080d1070780c01c4644170280301b5141c5a06015000394400d90724000709240d91800013004a0282d140b540850b10000003460810304904021340340c00c04000e144007032070707079a03003001c0c60020f83c500c0c650348041c0c960784100800291841c9450221001e032101c140c280c00e03400c050a001207048000d1400f056510075980411044405d462420190440c1c1c840010403002041035404240041d102410441d0141c0605000d10114103070050000d507540c0c000500081d80800c00212405c0c0502d00a20603 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 537048003 1250 537046753 537046801
    0xe0c0f0f0d03110c04050609190b03060106030204060206010f08030403080f070f060603031128080903150f010f03170a18080f15090a0f0f140106061e08 67
    0x100080080014180381206070224049082d190042002603800c0064101040c01030301d04200c2ca0424000107441d00d01c00426946064214140303809034082150071a80d454140581200c1d200d584402e00600a5003080c06004014801e003130001a4444500300040219031202000e50314041c296207910324103a021983d0781314801c00800010b0005502c4200c0070b00268012440000c8107030441c80c0080254000345095989507000019114441e25024a42140c2c1228454080306c1890980780c0342c031040c043c41c10400e50601500d05010086c400c491074580c451104c00c0968071040e038888650001150305800080d284030300c042d0103050340111a00c000d1001c04250300b81004800b040700307074512640304950400b52181e0071130701140720f02540c200012540349200060b0b08dd941d00d0035403000350f56058640c202404008c4110b5000050000f01326000d0030180e0071541c03215031303403551590035406040c2d82d100c0c110001da1078407000c2d9103e001070710b0b00c0604900e10380d6036400c807911a00c021201100c018402100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 537049253 1250 537048003 537048019
    0x19150b0a020f03070305041a0901090e06010905030303190605061e0306060403050d020c130204080606060708220810050f06010e21071a07030504060c050a0b0c0706050a0e0c0f 77
    0xb00302401c00141590b980b0995466a40341d040598410742214040d0050003038070014400087c0b07582e000700e4800140c48140c0f09062040c0d45100040300c0c0885203138405c5405001c00814081c4460041c512400c05a111680900103a41c0d640140441c9200701000800603204003a1605c0048400d000116040140106036904140c4c903034480509088a6001c100056846820041c200d41000d6080340324001040404500b0b2070300e40ed0b074040e00d889000307140d03032310440340080d1302002c22050f0380030343d82c9990515915113900b107000c0c0d00220708100036014900c554461945002c403a021140141c43c442d01c1c41000d4084552500001590140711038045580d00c100d429101010441001240c0c020051f14a0014115103251004e0b1101c1110510340008812404115101c003003600042190110340440c5040042c1c0d840c582480c40c284a2045401890481444140601e05620401030030095000320002c0000e9140d05050000303c0302e202c1c0b140b00b2240c010354541d83c040c0c0340007030049048440182c0301e69 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 537050359 1106 537049253 537049273
    0xc0f1506010f05130b16030e031c03050721021213030f2d090810140c210a02030115031e02030405010f0903020619150b0a02 55
    0x340502c10001034200352051001caa440017040c2d1405090303264206d00c054420030340e05400c4140c00043c688022155185000b1403201c001c0083c001001d040c0d55107184c001c0d00584402440d030310170301540031075145401012211440104070041c00c0143c0d03507003100700088150798001c3c1003102d0340d4001c084540002908004c0c0100f02080b0b500f480b4088040e90307101e035500107103a26001400850425050961140c0107000300d4240c61440e02134410110045021408603012441900040c43c4c40d0008590080f4500d40100000d4400c00d960421180ca9660003a9503800c1c00c0d0707a81d00c8041c0e40017004210000840f2072156040c2d616290500c024400444c0f0802510500b01d4040c9146a0000c080380070800b095000c09046404000103012290550501944881044815003040e10b0103c404080803400d602c14181d10501c0700d265545081c0c2482c032290243d1f000720140b10190f1181d00504 = true := by decide +kernel

theorem cover : BRFrame.Cov 536870503 537050359 := by
  have h0 := BRFrame.cov_init 536870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 536870503 ≤ n) (h2 : n < 537050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
