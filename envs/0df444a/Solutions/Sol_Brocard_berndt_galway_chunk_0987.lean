-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0987
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:40:12.044894+00:00
-- url     : https://prove2.me/submissions/d985fc13-0f7f-482b-89db-bacdfc4d8b76

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 177338129 ≤ n < 177517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 177339379 1250 177338129 177338131
    0x3091608030c15060105030c03040204060513094211040f030201030c020615040f06030602070813060507030c03111006170c06070209040b0c071a19142d 67
    0x30403004640d59094031401e1814400260b9040d8007070090742042000d140d8024044130750012041042d203941e0344e0f80340700142c000d14503500b100b13400a82d003081c011250030803030703022030f04003401203c007030380001e0070064034040e0101d0384031607084104040c2c50913401000002c62548514aa006000301c0e480d01c03569251400e41c5c1055002e0300011200003c10000c0d960507200e01541241750784042d1801e49012000c5601d000008c5003002e020b907550b02000c0803c000c1c158000f10240d0b1303105809650765411800c00c520b0540240804081c410038030800018518003d07c03c450351107138545c85081c4041c2e03490314103842883c102c0c0f10030b0000c0e02030000c013502e5640c40743c8a450040d003030020390001d01d40b80d4000e1071450b000f000111103006680c200186000b680c3c41f001c501c0e40c015440b010340c442a6680c00807e45041c0240c000041081000754208400034141c40c2c50240302d1041c082c0001d4628074140e43c00003d5405481450020f410b17660081a01703041030b80342c20301c40100c0c09013003a02a0301c5410314040300080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 177340629 1250 177339379 177339389
    0x20c0703140703170313080c10060b030a05160e0904061b090e06011d060c070b0301030828050702040c0e12010e010c030c0f03020703090b0c010f0c050307090b030916 73
    0x404024400c04c145240d21034856061820341c0340c11480c03c0100d00324020b507807204c00781004201040d0302040d10010000030000340484001882520f56501c0124401c0d081510081036482c14400001d02042c14042d00e440403221503035411200381d0020040c400340d00380103001900c0c2191036246500e0080c9010750b5003d40c1302255070701c28410a01d861103c8445140c050403e9040050741082d410640c0e042a59440c180c0000711080da55030703041d010204e450b02a05a228080c050008000001407024410141c4040340c03100c0c52170400d0a0404162001a61803054600b0105400340902d00150600b0750000c030442c0144d007014088840c282000680d8041105000051a91a5956a92016420700800c21041401c0c1424440d4440ca400098100c24484003460304050380421031005241c450840c0ca402006065000c1e40c1e10a81e090101d03028054503080e244010b402d061500e003005e48a001203e224218540d9442121420700c000c600b078a07440a4040e0032103100b280700001c410340c3c00e454408018a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 177341879 1250 177340629 177340633
    0xa050d0305190206010803040302120c03010e030705010e0d1209020406051e12060c0307050a030f09080901183b070c0203070602060114010309020627040e071206020c070314 76
    0x1030071a07800c442c16820310030403800464200c0c00041110400000c185c03001d0b00d03412134462903803412800035141307010007040425925608041c0741a460714004401444854002e00080c42070b10708600d0801d41d6503050b41814800965420821100c06056601c8a0401e501c010804200d43d56103500054880000c00c29000c1024081c200d26450f40c5008171441d404003100340060551480c00032500c100d5030000420702030038020f000855442c09440703031340007118030a4100020484180d541c00c00101f42c0e0800780321940803a43c0500030304540c1c8104403d0b10216900c5401051030700c012000b00c9402d40c0780c0802001c000003d4020148241d0079401e8140b44501c100d655001c00354443c6004040c54001507901c9502950000c40060041044d100005001ea400038240800c1d45003861010840da4407400d03580c4581229846541a4030103285210009148030803a402c0c0081440b00c903141d501c894070391080140000481e404000091200e4001d40800c16004064403140c660b01e0b11000924032981c1e413040c1c016 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 177343129 1250 177341879 177341887
    0x903061a130b030d0c1106030414070803070b010819060f020403061103061c0c06080c0c0319030c0f270302190e0a02030906070c080408010612060e030a020307060504020a050d0305 79
    0x40e0400300207841010a41c5c4c6041c0211303c060352521040c4100d0003d4107800f8141c0000010700b40034100c0608842c4a500300c04480340b803640c0e2500c1a407030760040002180d8540140000045003440000d000945202c02c03c02045a4511542c41000400700d0030041c0312020f409000005c04901544140c0c4e1000e00b9500d14256280b61140c00c01c0790740030400f03100324610044540c0c2c41c404506229821400d5480c9401c1242003611400c24042045c00782800c49482840001250124402801c0c0400f141070903648081c0000003100c00161003070905007a0460015090ba000124041c1030310055031a134a00c88414031000584940210300450488568682c540c00302030b01c100b200c1c8000d1580a82e01c000d0780c1c0811401c50815800103600c070f00025164034100004c0d01220b00c00d01101c0006ca070001d0000c20020040180d071201d0b00841034003200b60070340c1e11614065032900040c1000c0101d40c4e40c1c2e04160701551406005a4940b0000d02002e4801d0782c02110006000c5400c0c0c03150120010030600948030b00e511 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 177344379 1250 177343129 177343151
    0xa2405040e0106060c0602030613231b071b0f081b0f0a05061c1a12010606090b0307020f030720030c0a060e0301090f080306030d0305070903061a13 65
    0x50703510030703280d00c055603241500800441d54085650030b02c0a9000c800943d41e500c900340000d80c9800f21000a070052031801c0c1043e030f502400c60b20b40140302075003904180e400f41e442200002040b1040d081c50002200d0410001000809807480340e8051054000300b0110301e600e410240c0c03952055500042c886901081c0c400c09480c42010016107401d030308448803400c8101e5040030170080589449010f00485001c0303600b50b48901c0303403500b5840c110f40510f07041120258250300a80e650b404c40680b24010b10340050100203e610601689040d1001500e40d81e035003d16040c00c0381c02a600082a0350f04500030700ca030758902e000051004242940c001d411880442000b003011401090740c0c0110144281c1c002030152032a0307200d40303034a1400c60f4a00d00781684c80301200302c0424050300d50910000c203c40e504019140070001040080d60152500b03604940183c60440c806404480d8280d9140d00402ea00740380810008840ea0420040c241c40c0951440c0c41d0725010001c602c0b50064141141143c0d91141c00303500c1c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 177345629 1250 177344379 177344381
    0x40303110313060c02060909090d030c0309020f1c08041d06181b07150e0f030c0a17210a0c05040501170a0b030a050307030f080402180a240504 63
    0x10100c5a805185440c900d0b680002482032107210700300c02c0c803c40200000075507440301c00307640b610180602140300c1c0d0303c1c00c040d18039181c0c0c5044c00690046840c1000c4515218030034426002d480d42d02030207100784022004100010300b604001645006070844040c2400100c2c180d01410041c42501801c50b500340362440c000f40400c900518081c051090181d46200d016440c3c0c10ba01d03000420741d1500f4104008640460685100d884c101414024078900035a410821030b604c0281000d440348160b40c0003a42c1940440d0312031040050480c4e007940400c8141d800b2a10541204c0c9502c1e611030002e038506902c100340c0c400031074014483c41001c10440c0080100110490041c0c04219101d8a4400e01d45070500740060f18810300d4491071002c1264003c001a25a10341d544003a645400040840300c4003011498074950740d502003181140003501c80900c8033000c50090620074019039005094003d45035807030990034ac0144001340501109511401601c2046001c41305034145c24000d01030300d4035941d080c8001d100c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 177346879 1250 177345629 177345647
    0xe010224011703071217010b12040b190903090812070f0b060f04090b04030807030510120f050109050313091a1009051906170c0a0c06020904020d021c05012402070308030903040303 79
    0x8d8142004224000762401043c45080e40150701060002482d11781c004500802000c0c0240030411030300e40b0402405041d000b200000032511040304807403590015004401c158000d40c20f00504417000e1303c5940700050792030f121165024102400170080724a6030030011741030312114a0250380d00c0112038180310a2503484031a00d6840241e40c2000d00c0300b418590a01c90012020b4403998075503051802075101040f81c000c0102d458150000001e02c07501219040c8507449900520114092aa40c104006a43c45041c0074000c0341c0c0b4403079616045050251028030030303410f040c0902e020411626400103e015641c00d01c241c42d03c2c40c00600011521403c2800141c5408001022008082503250070009001c08410444854100701d03c0d0400c405d080d94031b040c0000e0b000f0b1001d00c59105001180d0000d851000d80d02501e903100080003901c02152030840098203c500a02611390024100b02150740410540d410352140c00002c2c0c4103d4420030b03540e40700e55602c0d4105440c60b8040e600005000c200381076202c8005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 177348129 1250 177346879 177346889
    0x12020409020c0105062b020105070203010c0302090a09061a0d09020d03020607020f01091707020d1203092315150603010803181c24020a0e01022401170307121701 71
    0x200c1600d0162181100803006d0f1181e0b044803168100c10b40d1001c591280b007e4820280d4040e009206800b40b40e000640690010b01b44680503c1e1061000280e41506014080c03c8441e40380c2c4c4805ca442c038070803280342168040790000c0d1070b07991108103040060702c912003d010981e000c1c1d0b010b46024204078000034102914511081c1c0a68101018900450340707035541401e21800f005602e550300d281074404205000d180311000350481540e0010600300c51341580003071101c03d12894800041c061200d81c0300ca4070400340d20030300103941c0c8030310307052401014403001d0250410580610068002c002900003201e40e4801d8005e10042c1d01b02180e466a901400700d0144d80c0c00078100e411450f0081e800585000082e03403080050051444509a940d6072080d015024090510040701907696520540c1c010780360555421600c2c0c014442c01e4001d184084d10000c000d02405560415507002d07034641900e00825914001710514280002c1000c1c82c001003141600407007580064440004207041c1c1d44507402000c0c5c0503880 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 177349379 1250 177348129 177348139
    0x5010902011b0213020901020f06070c03090f08060609060a0909050307020a0e0405060a1107060c0f0908210f0c03070c080f1b01080703060509100e060d08120712020409020c010506 79
    0x300b41c0040c0c0e200d0620700f00d40c084281c4016116140600101c1c42c000300303200c4526640c001c0340c0c20b1010307656010030711703480e428025103400807510760741d4010900c00d460b18400c0003003640008001c02d0061400701e0b0b04a420240c000d214181241d1036094801c00c41d070450f40c048801c7d9100061840c1141015039106004150384800c003116032030561151500d0b02001080c050200d59603041c101c03158060700c4242d40703130302350821402c00041e210389002400b003e5100c000c04010801c003102c000740030030000800900000c0c00301e602809800070000742050702c1c0c121259400e11070005000c2c8000041c803c02c050300b030705130140000071003162070420b0f45400c29103610038144071500074503000a450214403003492a2141d00b07107001003ca544000c4100d000303041e9a00100d90082d650030078804209208400d50041c2c82041000c0b07004c41d1a40c1d41001403a02640500404d00001484212080900c40010783d40c040d80764184000c0043e14040c2c0e50302203a100f074001e0010194049482d228600091040319072118043d50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 177350629 1250 177349379 177349427
    0xf0909030206010b0319020d0501210201020d0e13150512010507020303130203010f060b030915040c0e040c0905042303071703070905330a0503150103020c0a0501090201 74
    0xe000351200302c1400b03800c11000001010071583e140403181c1303d1142004540440d02e43c010301c6084c0e400b4000a00c01e104003d00034082d8119450078020208401da0341c16001003805402c8901c0603146185601c1400d80d11072504e0794800303042d00340c0c0c8c0500a892030861407114070080c10b050400480700c2e500350f40204c5a030324080c204001e01d900003080342c2d04000c2184034030042111342d2000a0140c19100070781c60301e0605003200014018120380247d0b000300c921000351078070210207503840c00c5104030841e0064006500c41e18100034034000c2ca102c0d9608076005150205425840e80c0640c2d060762030542c1c040b43d1440c407a1100300d0040c0a01038040c007094014601440c94035503030385c580440c211f0704802003030706c1c1045c0080031075990382c040e0200c1001403202034051018026041c0081c441340d841c2f020151309034240c4030303000d0003820714420885800101030b407a1541152078000c207698003100100b00050503da801c124507070114108125029943e88144000b04180d117640c4001810b000c4d011441c89100119a4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 177351879 1250 177350629 177350633
    0x6030c06080403022505060c0c0909190b0c071208040b010b1227011d01061a070f1109090d0e04020301081002070510020403150c0c020108011412010e070f0909 70
    0x1043c107442105c1103180c5c916071110240310030b0f80e0102d06940400c0d032080000640c8198580e010501039141941200c5d052416641c081d0341644070075090b8880040b400c0784449410002e03070300748511504407810090316820b0058540d1000c5c042e0381c0c3c00c0314030004540179800f04000c004e00c030000e180c003510701e04c1046403c09500402c0d1081034500a040e940728107a41000c40036901010441661b4400c001d14000d10803407450400384101c440c07403040202555400d102012600c0038074620b110090010301b801035490200c150b16100e8124020520464054018030145403c640c0c0e900e01150041c40d03202c5c0542515415144050905800710350f02900840c010700c0100881d21000c00c03035480e42c030102c2c0809a80e8590502e0170a0404507207104428140b84007107404000d000015849800c035011204041020550114064404400e59500240003e1207400180081c8494211851501f0000b6011804110803481c1c41425190041e440c0d806507070042d0800c00100e404000f160000300751080b01004003081603 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 177353129 1250 177351879 177351883
    0x60709050d02130e0106180e0f0a20060f030f09070303020303130c0b0d0c18030b010302040b0301020c061f060806031507090f061d010315030209060d0501020d06030c0608040302 78
    0x144030040d210740c1d41506203251007811504000150440c6a00030440c15403140d40c0d05c0c0300381c2511501f090106140484915940c840019000003a00d10200140031001181d81c0700a40441000b062921030382081c108440c0c0340d22600003030540901c01c107a80c907890f881d01003900c1401e40b400904404056012510400210b9000702c100d0307801120000c80c83c0705880300c07424945101c0010398444e110310361000505040c56086a07026070120003a03641d6654548494030305030080341009000181040440200400061606034048202004060009030a01c4208410b040c02d1040455440c843c030481c2000012500c030b66503010902034140c0c0c4c2405003c030709028011990707030000300d500420480030355004a20b0301070165404c4802080031001011079940c8032600140300d00d40c07019203d0990040840800310542c0240140c1e564075440b0300180d251b82d40b9540810602c01c001500064101c803442901034003150007800101180c804000003c2541440c44c80c1c180b0314000141d0000741001840300a0000107640 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 177354379 1250 177353129 177353149
    0x50702012a060c05040e0c070c15091202130203041103240c0d0902090a020a180605070b04060b18040b070e0105040e0601121e0b03070b09090c0f03100806070905 71
    0x1041c00064007940b000000e4a851056810a41229031142c01f08a2440c888100502e55540b0820718025516034a0a0200002607000103603808120001d0041c40320060401489410301d0004240c4004040c149000314100d9100352010b07105119020034541e540d080402030080100085094403240003180d040360300b080c04015000b00c50364000007070060031190309600b006030340c40e40040522405042442e410f40c020f5211040c0b10f000300e0810b4a0b01030303000c800c1c070802004660181c2c9a0514001050303031810b000800040c0202c0d41c090707645107195841d0b00d880d02c00703100360110f1128610290810f070400d40c12000c001805e00c0b04000c0f2186880d46140d901009940444410003a02c80c090748608005944043e001288400c00d07900d05254020b030740560201c2d0300b44c0341e01c020700204403120418040c99182d031300e41d0241c030064000400020380e0b24100254265405002c66022034107180b0b48242c40a855401903c015883d208401380c14030041100780011034204001d4208003030084e2801000c5554009 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 177355629 1250 177354379 177354383
    0x3070c03021b01020a03030f060f060c050115060905090414010516020106050f0a050907020a0b0403091409010e0c0a05070614011815030602030c0c010603140d0504030c0b091f050702012a 82
    0xe108c25142844020642140c400390403056002521076403180e900800d160380c10700d010359042d800c0401c0040e01d401c8414404045c0c45169030f6940030b882c201000d03c0080725000e002140d405030f08400d8a00b01800a1190f140980101d8000926520720003500038250340706500400d2281c0007000703842032130f5610150751104460701500d1500c00ca503200102641061201c5c0e4024041203075040802c400c05900c8420101603605080d415021080c082042c403c0c268001d00406d0051104e1001107244144a40042d050b9448a4504035140c402035a03541d109807100c05a4031148a05040c0040c45404003074801c98840e0383c4280802c1107200c40d241900b014004282c0701c0a04140d03400000f180720305111108482c41d03c00180001d1000c9907403403a01105006032004003901c02d01541c142410440c1c8104115011260442c4014100794107103c810410b5034800d20407254406007105603d9042410a0004142100b003510398075240d01050002501a15080781800741034042203c43c989070085407400107914039 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 177356879 1250 177355629 177355631
    0x6061103190215010e01150309030f030e0c13050103140316030c0f0b0f16020c031c170903031605190e061605012405011d03030f03070c03021b01020a0303 68
    0x80d8032504168200082c400c000703c0e00c45020750000c1034104216900504803403050240c0402040c0d240c10403803c4800e800d43c000d002070041e0300c100b48003034803c2d003000d840c0744020710642e84449010f00c00a503d41040212280300d050f141c0f8010000c1c00321550b200750b00d81d200f00c0b014519040412000c8030310021164001020b00500c0c0c0f65000c1400400b45c06503001c41e0780a98030140d181003407109451a00c104680c1c1401005044600d185010720200b181d84004402500a00d082100c09000d01c407a8000d80e0034000400044130209032440d0b210f07411850082408802855590810707413001000e1320b00751000402031250030404a000703805002d101d801c01240034940b054180700314000040d0244620703182048411507100ca40d50500006500003a0f11044042410b00704810a40101900d803085206690108441001c041101c00100141100c0540c0040c1904e207004880c1828000e540c1090b50400c00051040f2206410190100005501d003110306445400e030014010000350b9400e0351501c001c0400d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 177358129 1250 177356879 177356917
    0x90a03050c031308010f050603122a0d0906080106080103030801090f0608030d06050405060a0302031513051506121b06090a09020a0302091306060903020607021f0e0406061103 77
    0x7204081c400c2c0e44504925402d201c40b45503032680c1282c0640003032034010b001d02d03140a0105585d4039001074081c10f08440511100e052105005200e0030b4285004c149d425060714038000c0c02210f02c2c01313001082c920111510b40141d03840c1490340c01081120160002001e221401d4018804250026050343c1160307101000132800c641c500980002400e42c0d0751000c0b1a074813000caaa0754601600360444000d6940c00e4408010f596500f00400401c032225201c081d405400c03181c1550400c04c406043d0581c000c2c807103036a0701007030855661280c2c0362201e001203411a2094075070a00c1807500d45640000c148184800c02411814400401c2c1008603000054030381c81800700003030303a10164982ca05000e004100c1d8031011500c800e24020042c2c042d501180303c540c800c801e50f6800c0d0100400e00d205810a43d407542d55003503401e038259824000c0f2540602e100b43c1e4002d4a00400d9201c1400b071689800c0701041644d5140321038607981c401c4c84180c600d44d4204c0303000c0c405840440c00b0b410350000140c9143c8200d400c0320001d2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 177359379 1250 177358129 177358147
    0x210603060c0d091a09011a0f040506032a100c0c09051b03040b0708070f170403140a090501080a0603021507140706090602120c03031308130303030e15090a0305 70
    0xf45040a8001c100b03601c0b10704000802c2480c0ca80141c4a003103400002c2c00403094400300d54021099843c0d600b40d001520302e552094a0405a004680c00b90014040321003601c0c5010007000c8800802600c145644000c150144841c00c01003101d8103020450304001e45481080d03038030b8820395400b5024400c4490703507910000da540718800803401c02481c43d0b6003105a42c3d081c107090035001081e08030340600125000101040d81c45d80f15200201c2c042c0815a00e0903003100c405681401c0742d40700980141c00b00803d0b00700c3c4600303800f110802048583c1c00d94450903045407a0a002502512004203007442191419608001586415000716216807071002d003e642ca0f4140c0c80c00b210504050031100c000d91181c00004669980c01c0b13000311301134406036000c4402803201c0c0e83e1440b0f410300c0b9120150060781c0091000c14443c1c80354800041d0f10501c00c2c0700c151b082081c4110288000c9404c4d034001d40009888450503024043c0500905130304040545e0f0240d042e00e00a038040342c3e5101d00348402010042e002401e2a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 177360629 1250 177359379 177359381
    0x60609140f250905030d1e030c050708040e06040b1f08040510090c0e0603210903011b021e06040f0212100510080d020c100e03070509010902210603060c0d 68
    0x1080090ba45900c010b411241c81c020702401c103c4c040c090081c40780302d0b20810b016000f1400000001892901c1d42c41c45910134400720050085c001c03903072051080a000400000d41d01e01d02a10240107030031004d42d224a4440100300a0310355040c1c10301d000d0352861280b0440d401d401c0b41203006038451070030314100303544a42c50014500020b00205940e074502e00750690301041800032a040840d44003031030022040c3c403110109600d601600f07040310885a007065210f00c0d615105005807581460040c00010340b0b801c401d0410840349401c02d040350060f0402c04040c114000740d01400003580c0c030304000a0860386015a10491040841030000c0e108083d800c000c109091410091a41c40594890007032045007005401401c84590900480210703000d84107034074584510004501004d407000401740351921001d05810303522040b8000c0081c0d01406100030126180c0c82d000270f100d0003440d02001c01641c0390a6440b46103070500c03081d2440035a2490700814081c407650300151044c1c11450b4a14503950320380c01240000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 177361879 1250 177360629 177360661
    0x3180b0d0f05071103040506091c0c03050f0606090103060b030c1306090606020307110105220e1e150f010201110c0a020a0b07080715021c0b041a01020312040627060609140f 76
    0x4015040c54ae0b00d88810071181c11841401c0320700c14000c840d0482030354961203071100d9081b24504d030090411310040001c40d806030009409000c024007a20290044503000c50f81c41095203202c00c0010341c4850040100c1184c0d442144014001840a107041101da50f61715500c070f03480041058100000860f640403615655000d10980100c03081418101c075503104000d40300c802081300c11901840358844000300401513020410300c24140ca40c03901c0e40400b40d942c1080b50594046268504540da43d0700345140100366103006011340070001c0700803c0c0588143c4100004188250030050481205106940005403480c0540303060540c0103000751180032001403640e00038015030603810800d0520840c01c40c410302250740040715409058409000071341c1c00001003010821600c03e00350044e40108410780c80d000c081c500701a001440b03070310046000264014844201e40240518105c4804c0050140c41000464411080100240001880403098a584211809400621011101d20500009008503020b96546 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 177363129 1250 177361879 177361909
    0x1403120306040612050a0b0705190809010e0a0b090d020a081c0207060609020d0509010506030d080408090d0317070f080106110a060204060509030714060703180b0d0f0507110304050609 81
    0x401d0810401d420301d07946d950308040301035568074010008100f800c7e02c22800c44810b00b00c4003000c003620340d038115411110440001e002843e555a203d41202002c0c006100d100b0981b03001e0746076010320342042c4002500703040000303188400b0b6500c409000800901d00000707468061103a00307070366a12683c502c1050b101a1240e1007000780901d00d0702c4804228200581e02038a107603950040100039580d11040810300302e40060341c520340c2c541c0c082440300120a12400c41150b0080c402e0640d1814072401d240810300040c400030084011543c03030b40c414503076080714550b031691104041ca046044000c1c0644007a01800060140c0c10402120f802d051200d0581040b0040c94940d01801c215603d954031003004115402250a580c40307030081d6100000e04014103070201102c0103000f00028548283c0303513420b440050320710000c0c006200c040d8100080c0c040c030700c1016094080f140d0754045041065070904e501118001012901400720452140d54469000825a0103803503098404c10b80c0ca001000000d03280b00100846 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 177364379 1250 177363129 177363149
    0x4030e04020a17090109150906090209070206041203050106170403020102070507081b010201360c08010f0c030905070510050c060c0a0e090408070215040306020a09060914031203060406 81
    0x4005110765101c2c065000c2207003030034100b8146071105011217003a680380c08005081c07562075910030509404154011410144103c038000307001c0c400d07640400c00e408011660311f00540c011070100800d2200d00021840003000c0f51608000075070500802a101c00303080b4440c0c561040c071550010b001c050003503049804550300102110402c81e501c140c0b480d92900017400c14203c9101e44480d50400d9401400f0740070300041c0601e04040c650a010300764001e08840203002480b15409036a00c0000b1460090040028050160000ca0300060440b401c1e415a1110607071031041510300580d45002c203101213440403e44104075510421a01c03010b030122214090358010034002d0040105004150070610f006090009440c0c8a0507402c0c0701c1c3c0410071221920448000e0042c400402c01c1c48010325090858544004200b03400700d052a46a03101d0340300300d81000c405080070840a81c0c0500090380c120304000c0c02001910113240040307507103002194840e4150624003440031004008649260303900e411070005007600b44c01d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 177365629 1250 177364379 177364387
    0x1303030b0414062713050a020d111c11150d11070c090b0102070326030718090c021b031510031208011a0c1f0b03010e06060a0e04030e0402 61
    0x610700c1c6000034242d882920416200c200c115a9114644c01d0310310b00005241203010642d0b034030329041031201a2010032a070074062096101c0042e40d8510114440b18010321b868001400d007881485984040c2d11440c082c41e08040034070000050100706004641801a1a0090b00d2211207a903c5154019803600700b80702414105104540c0020001402c145401141e400c25003c0c0d40d0200d002c03c5518610803140140c000040038800300f0f200240c0304054814103d0040d81c10710407840c000c02140c1098074a2000a0426000607061410f800742039805001e03024010081d58490403001f03980c0340881c0c1d812041e02030307071140384040e2035600b404a105080c11038130341740d002441d101018002100940c04101c0c1c0d507207440c400e145c00075032003107070400d0607540211800400740c418241100403c0e0420346801041c3e00c50b11502008010390b011002c51075503418034011038080c41c040105030030750301c2d0750801c0704055000d04100100c07540c07050309100032582001100c14141d166810111002c030300d8501c00300d420500001e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 177366879 1250 177365629 177365651
    0x9040b040f05070f030f020405030a1211070b0408160807090f060f1403100902030304090905190804060e03030306060d021c0516030b01080f010308090f041a0301060f0b031303030b04 80
    0x20702403e2004c034065908024042e91001c0281c104d000b680a5580c25910506890002400d080801c0c0442c00c0303241004140c6d805c215210300c1c50090160410042c041010508000c80b000410003680e900081034280c40c106410420026074482d4070b40f181040341130701c40d001007903482d8007a441038001d002911421101140c03a50240c088441104202500a204031900640d07600c82c1031140194140e40100618a00f5141c0240c8102400540006440d07d000341201e1055080140e0503442100c0e100311807040d15203103001409001f140340400442c4c001e400030070030085181c3c0d52004440498a500c0401078581004000803286d0b00e503a044800390381403a0505001000c0650948543c600220703a9051200600400c011900940300380c848441070030b425001803000800400103049412006000c1d60350402003a00010259100361045400c1d00441c03110f200c800b41800c3c0a808083c2400b4166040f00d04d150020845041c480203000044a28001007620304141c8a03420011100c0700060042c81501c03149 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 177368129 1250 177366879 177366887
    0x103020706050a05100e040b04020d03090815040203060a020405010507080a030209180a0f0204030201020d0305040302240103050c0105040305030f36100305332710030809040b040f0507 81
    0x542d418040c5201c045d00000e02c840115220510441d0700258119860301c440d0309002c5010340c0ca41c0d00700e0502c1100113000c01e802c0310400c00755003903000c00d091103403003402c0500515081841c0941282c1c7c0c0c0c1c80c0104414051a6081001c030350039994001c041c01e90790787c403e102c02c80080c02524489a800700c0d011081c92200f00c281c141c05409015490010010358408114010881c4610b1200901507044401d8071115540a9440580e20500900544030700041218403c00c802c506000f6001c01c1e521214014818000c0401c01d184032410203085c05850142552542540d0b40200d80b051141030030b000500046c150540001085071100e50240516090b41d070040341c1c00c00302080b00c41540103001c000f100068240c440c3c040c450184485403440f40a120441d0240ca040038540000749a0803800c410190090380c4401040c0c1013040d03000e4404c2d0002c2c010a04045204140c00f80c03010707085650b10f00003800800d281008403004088122070000d940d42c008000716010f0103c004802e10540c0c68603040194031030b08 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 177369379 1250 177368129 177368131
    0xc0f2102010614010c080d0f180c051002030f030408091903030305240f0d080a030b100507230109150608071208030a110c030a09030b0a05040b060105090103020706050a05 75
    0x5950001c1c030a09032504070a03101c0e07160b10280c0c140084c0c640117481c004580448000c08406a404c6804904400107010318410744ea080c1c0c00100800d0f41e0202c1c41001d000c00300041a0103004d0407039020100d5200b03103000039624043c1031404c1d140c41c1c00000201c0c082010321021503000b0781700981049070b982030078080703880710b40d20034030041c1c02282c01c282c001021f030604486c800304540158201d080751000340d9014049118a0358921540000100c0010300110f01098080c050440740c5a8011071011220014004c20300030512124041c002c00b442114002130f081541c00a54102080500f1603180040d00b19901624070b000b0060311a48100320814081e900d2600540c0a0f43c500c002200d110301e6844a85c1c0d032410b00b140d107024000c03040c00d201040141106820251450503121405828800c0d40d082690071070380310001300c0d40071030400300007041080300102e48141e20040e0f54800f008a86000c0c0c4841c440720400800043c104100081c24400170b0b0700a030305482005030000020496403902c4803042e401098 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 177370629 1250 177369379 177369443
    0x3091c060e10110c071401020f01150815010b0f030727081605011d010e120a0201030b09040302031e130f0509090a0210080604180609060b030c100c0f 66
    0xb00300364942603c035000a04981841c405440145101407605c0710703040409843c4501d0a0460090908400c0b07002001d0003440c1c00003000b201c040d100680787c007860750b1814610141014401c88100b00401c000d074116410742c0d4001c0780c40034210781d603541d07054001c1300c2e002101a40d00c44800a445a10414030f00707845000005c0d00c044908458406003d2038240302070117154860301c0e00140c88019048110200d000e42452503460605000a05861f0b1400180e00700b4940300000400398001d4031040c09540e0f06020761051074072709442d8100a8100b9071002505c134400c4600001641300c0d0580c0e0010080769003030440b03664101c2e0040140d555a01c6014210841c0300700d100c3c00388951000740110380040e1001c980701501580c01002080a4003c242003a01c0204008040310b5000ba501c400e15808400b0b154189070302d042c41f903440042c0c5000d051900208884155132524000d60008050001a4841555000c4404c00320b05002400b148030b45415807101c0300c2c1240c01460440200400d0206050800360345074104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 177371879 1250 177370629 177370631
    0x51c091103060f060f22060611010f140115020c03060a0e01110a1e030b060d090201180503030904020c0a050102160c061e05030c12040b150d0503091c060e10 69
    0x2843c0d0186201d056442075400c0c561005407150000e542e840d00c0d0382400b841c8804d00511a540c0b9143c03020300401c0301c01517031159010980712144600c0c00d01003032041d1705601244100c00c01030030400600e100c108a10502400131a10a4001f401e40c800d0b00030800f407142900006d0491b08580741200380e400207403c90b840601810360801030b5150100d000c00d82952102c48642ea10b070390005100590781d491600c07100800c1818540e80380c040c48042c1d183c140042904200142000c40d4011309032000401c603030411074900c15204003800060001d0764003c812a901e92208481c00368039200040c40403410110351080081c0250704c0010402d0001d00c0c01003403200c0e030f1409200040b01455032a0801c0e1109403070006800544c0c08542e200d8542c942c018400745401002620f1410300b40109c010004060b140e0a440513a610f410300030412502d50303504045600001b03010303070782c5a981c0c803810342c1d80c03650b603010701e2906600c0f5032144441003120780202084110880d80000c01800061a40413500c1d40310b442000c03040c5059 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 177373129 1250 177371879 177371881
    0x207061e0e040609061409060904030e0d0503040807031502090a0311010e12010605010f0f0207030204090c050907110c040902060304080d11030f01140406080a03210f02031e04080a051c09110306 85
    0x1038174080d0492403062300040c00070308841d41c6558080b6201a40e0074602d90348001201c655002050b0200080d0000d41160705c018454a403d60405034035443c501444031103402c1c010803a4207a25240d40c0c4049042700e601c6032903144188541360041c0d50b040340c0a42c1d0aa0854035244402903100b40540019040351002c1e2a100303550303901524102c840040c8244184e000d80d006070790030001814151712552480f4000ca481070f20b001d484100061171010183c0c0c0e48000100d1540d0203035883d07441840b0122018608803000c0210f100c50341c1c081030490200602c080c20030039011a031054981c6064000e0500302e809015999070780d14081d4500e030311082d0b081c00707026031010301641032800c1c604151217030406030740d48d580c01404484c065603000c03103844480341c03070003808407080b0324a2044c00c0d4007034064110350003622903015840b8607010b582141c40c02e044100b600226100c03042400301260880f01100c5140842c0d180c03080d80c07a2841500c03401c0d0711042e02d640d80d40c59403070807110800b032001e40d00040c1c1c0201c804400766446 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 177374379 1250 177373129 177373169
    0x100e0c0d0c15080105010503010b070510020d02070605090316150e12070302070504020304020612060409020301021815030c03010e100b0301090903031b02030f070203010e0a0b160207061e0e04060906 87
    0x443d0402d014030f82c00300b401040140440c1964901609a17a0701c01c00031240c0c2c20741d40d0345070700090341c02c084071054080740c0104c1c440341003200b24052180d0203807603000110b08107942240c80b21504440030741c002e400003080e1943d20040c0c1800e500090000122401118814100020b1586141c1e0001f1015030040c019002c000c00c66107046d0003101e0240d0f400408040c24284010151400700c50050000f81d4003d5851800c440161801c2c0054001809101c8990244d9041d0000340302c4407403d9560301d5004d02c4410410440044840d0068030705562400c1909166540c03240145920007915400805001001000000303030702e841d9400440401c0d100b907506000018040d4170818900c0b80d28080880175030400e1240030f24140311a0090002c03c6c0c001000806d180810002d91424042c00107800c0d142260820304003d503004d110b034003456440105200908070135182250051000601c080c00006600135030f9403500640348074840341998008014420080e007666425284024060303486210b40310681078980005d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 177375629 1250 177374379 177374387
    0x250b070b0f18030927040b01080706080402030d0305070504080a0516090b030a0206090a0504020319050708090c060d0905010c0c060609060b030606160c0b0901080105090108100e0c0d0c15 82
    0xe00d100b1884010f609141440013000451644000c40c82c10300781c0e13540310100907449184030a42c00795018007500d8816504180055051809540014040c0031014060200584001a05041900711481c0001c1d40d88c0700c0380b10807203440c8503a9200340482d11581c40000240440854100141880b581c102203280e603071141d1480a42c0e2031500ca042d41500440e8156025050040041181140050030011001c0e00c0da000502240c000383c3d100d41c1c0340c3d03848650a5120fa001c5110740d81d0132a000c0e05203040c40340f900300d00c216616403c400f2628011840030a100144180c40e40011301540d81c041c000707101313035009140001e003c0040350b2000c1c0c5080d41401000940e90140340300d40420780b910441c106203580c1c0c0345024030403030347e20072041500544107117600c0c00c0100e098000081c0103030502c449003664401402000500344801a04407920405803c001000b054000050724a13140c9a0401d010611040c01a8124100985034902d01c1c0c1112490b10710000f00042041d4010564809984040c081071442c40111 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 177376879 1250 177375629 177375661
    0x608060a06211508030d0c0504051c0f021e090a02040b0a050c0c03151005030712110f0a08102405061303080403030503011403010b0102250b070b0f 65
    0x140811050116540d1449408209180c880104071022459034188a80d502d008000e44c0e0040f100350304046400c200080b4a40a603004440760343c500b6504040c02c0030300045010b1003114550b0300949103c90000200100000d2800010750020300070b243e05840b5030003408091020003000b07403194090f44001500c2e4902c42c4240e4040c1c48440d1880c0d4284500c118081d076440d404001c000c82c01c0e200f8150340c3d20240e581044803113000408500f450080d41040f0200f1160b45205811488c4a50000345060140300840b00c0d0520203143c02c8459880020301c44004200006142722109404c041e03105000b0620503070000e10388440b0100c0c0001045003a140031400f10308003640340c0c0b00c1c280a54688008200c07034070303011000c3c0030707841c148041c044050366a07691021490703401a40200d0115402100400030014040074520b81000d06500a0080b00b000c800001d44804404031502000341001103110f8102140d04192400340100014080c0d4a10321414051403c0604841541450816000241a40e1070b20f141003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 177378129 1250 177376879 177376889
    0x3060518010e0a030e010e120106030c060807050a0c080d02070b0c03091605090115021014010f14090601080c040f03080705010c14120703110706060806090a030507080f0903030706060608060a 84
    0x1000303003440345d50011126000144060784c1c0c01071004d44a40c1040c5028800d50740158403641e01d0321442c070307d40b05018181c19402840c41080c40014068082001d8101918425040d8002c00d6141d0b6500903026400003070292680c06440b103200f44041080300805d00d00158001e68000c0212503513256981e0f04243c2c0e00f100760098941103081d502c0108003506140f115000480b00500540e4103207596240a80129010309040c2240d5145c002c0040241700962080074000c0d02d00c58920918056250011514051000d001c4604001d04d1750001480310b10340700e06407809000104100c0084035a80e003000f12191b0494441aa0345501e40791911010902172404201c0b202d081c00006410200c900d1481c1e986084c0050100e410316032240d14440c502c00cbd10b18001e12030f052003a0700006156007050f02083ca407800080c01040e8503880480890f010035080b4041c0c5103407036440000c06036141c004081100480c080c0848040d014400850540100001ca4001c1c005841d90b590345d0684903600c0d5420080080303a24404c1c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 177379379 1250 177378129 177378137
    0x210f060305070f0f1502031c2a02031c0e0f0102070209010e04020a090902010504090c080a05010806060a03110f1005030f0901050415051f0b0c010b090106200703060518010e0a03 78
    0x70401c643d2140101d9161000340b17900641e810410b41201d440b80c0e0619003001d42451341c1e640c0c0d8a501070450340e11500a10142c0100811112603191500a50340f840f841e99484103603901108540406c10b00c58000c0800203204a040e541d82ca403103a41d06602030741251401b20b00c074000c0b550000c00c0203203c07100e880d88241c1d001041642d2031890f00301000c0040c0301c01c440c180e0401c0402c00c4007242c2c0c140d0500440f00110b020341d0358034040b86030402c050803c41c1c206800000e01c6d500b00b2418009aa542e104010094941182030f01d12241b16007070006000481c43c0e00b220ba0444c004010400300c00e900800070310f02c0f0342540d0245050580c0c03401c81c05801c81d50308503402004070703800055041c00c1c019140d01480c1d10000210440303115480005011076030304002c0d4001aa90440016480740b5800d00380950042c000054400c1403070343d410704074043c1054021000d602c100140c14a030619656108010303a03801590400000c00041c10f041e510400c5000d08115425800e60914600c064403882c0062041100c40e09603407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 177380629 1250 177379379 177379409
    0x703021903110d0804200a060e03072d12030f0503191a030c03010504080f0a0216060203041406071104360201020c01050a0f210f060305070f 62
    0x180103003106082035042000c0b4000b9a070861008001c0c204500c00ba42d12851494501303854460282c8407001d05180199002030b01d085490380350742000006607045401c2211100743d400c000b00385043c1250740100005100d050311001880404071103990440c81456060448584550202d0303000d1142c0200200010014000000e55071301c910007442d00068100e01520400c41900802c40503108aa85507542d0003801c0380240303031146003c00a500e000c8005a00034803082ca010744440045000360302944540d0703540000d107000f140e4421700c40c40c451a28001190300c1c2c41920b03a04002c2d501c2c1c210380560410420b1640c0c000f44540380c000165501954460300141214400c5010700c8082e0541801c1e54a400c142c810302a030070740080c0300310a960390480d200c04c0501d460050000a150518005074941400307000c000c1c1070041540308075406500c02860400461044c0034880394118800d29a040c80b206901c1c01d0390900403a0f0071a082038003180e0261045885840e10fa24151840d51500c0c4180465941510 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 177381879 1250 177380629 177380653
    0x20f1c03050705070203031317120304080d0e0601030c06030c0302091f0207050307060c051018030305041e080c0601080c0f0f030102040302040e070609061412060f060a2003070302 79
    0x50040359000b69240b4040342010040e0b40802d2950b005011015110383e410340c02441001251b82001e15500303000b0000345149441801000128400540041c0010000041d4036140e4482ca421050b0064032810441d00c803503959051500c410768540c012000001c0c1403000b06c40100744207009448824100400da056031800940501c004000310710b19600c00d40c080e80000203081e40d41402407800408440c0c8420414000c9450309070700307200051818942d040e00e09160b4a02510303a00c107400341b281c0d9041c100042d0640711420000050380301c202c121558882d4030103661082107103240190200111500480d0083c0e41c841d010b00380c5501e11107035040c0d084403072079400c580a403800c401d0a245900002e0001441d01d2f032260081000d490002c02134103050b900010302040312507072002c940402410140b405916003a042e8a0242c141c0c41009203a400350400d80d0081003140d55603e4640c3c0b14440003d0443e5a201d00754940030300550035030192500b03544d03800b04100300684408422280c0c03042c1d0607800340c80d040d038401c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 177383129 1250 177381879 177381881
    0x806060310150c0c0506070c05060d060b04120218060108190b04060f0e13020a0e060f180105010f02060402090403390c090b030606060d11030a0c020f1c03 68
    0x14078005605600301c5002940c0080740c0000031000b2000c0e80c0324550282642001c6000115541c890b40c002c80d02000070b600815501000401034400c11a065540c80000c0840d00300500006d80140c1545040001d000032214200503512120b03500c06c4d20b868080c0c150111945030303425421915103000c40c4041c80020356035140d20740daa0b0308101080000169150b401404039003201c08a40200c090220420400d1100340c10040c0040c1d0712007103481c0c00105003c0e690f4040740500d5480c3c86103801130111903001c0b03040e95035901900d8500391005040039030485901242072161000078410203020503041c10388421b07218804030b81c0d94070403a00504080042d484940d411119447c80c82c04180356140384004208241c000754500620441440102c0da240074010f007441c0300ca0034502d91101c4501c80c0307400400c0105403400304400e50700c01d801b2581903456120510700301e0094903200c22451034080001080042c56800ca40c0a8103a41c69281d007140e1070700440b0031440c1e0303450100b0810300410710100303141d590704c031886 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 177384379 1250 177383129 177383131
    0x190b0c01020c1e0114091b040f0c0306031704060e191a0315012d022e05090a03120b01120912020d0207060c0204050c0408070303021c0f08060603 64
    0x18100005142c078400c0390100d03003040c00b240685080907207542100d8442410034018507418034000b41c8005050308248042c1603036201d800150a40700c61040300c9000d01542c46600c000d80c100301d403103c00d016504c1203120003030040220340002c90b5003902e1142c0c03e10b0f4900d0854144c2d800d031101c90716885000f5082d1020003040ea458142840c824860800010440e0f0031a207040c88000409100380686a081440b20540781040300c14000741088074050195003000e0081d12100c00c161100101106100d002010032407c10038500748442e5143c2804400e5040102e4861110881d15003c800410840c1c481041058407040070300005000134181c0c3d601c01b140b850750b41d0300080664005060217010722900a203460191040e8010a0302c01921202d020300540780c0500c040d000d540006c0c40a08841030900da00500011281e400c041e0185941e40006050010780c0800c50f4003504001088400566480c640255a498022400700d00c00e0604140442c405018a040c2400514941c4400b0303041e0f0b844c03609000303207504 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 177385629 1250 177384379 177384397
    0x50f09040609050102071b120c05010c0606230103061415030c1611090f0103081804150f030c09020403020a050904060b09100f0803071208180303010906060905190b 72
    0x140c0c50b40c4510000c0c0c824402030041a01c503100c4004403240801c503400d10425203500c514460620340d158540003586d807c038120207548003406c02c0c100910040c204017004100711381090003070308000c000c8403485400000040c400c5000c01d980500200c1c0e2507400c001071f141d941102d80340c0c009003160300e0f10610303540701c001031540311000800382da040100241c0440001030341c2c01019079001b5803030070342042d5504000c02c0039540700031102850754043d45036545900c40c0c2d1040c002843c50151505251414564a6400207951714809031700c0741030466140c032009040e010061000301d0b04d90503800000540003010380207650071642c00501d404030b030500d070030f0900c009024002c1044070401d40e9012101299590054050300030380d035452010300b5246c1800a008024245a00501c01e1a030051041c44001061103c2580400e5190b2928a01c1601c1d06100c204444d0480700141280f40008000400c900c05030b42d02c854112030442e074944450f10fa03242c0038000045155891f0700c5101d5801d0a080c0041c20040b801030040f54 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 177386879 1250 177385629 177385631
    0x13050a0b010b0409050601020312150307033f0c110112051312030908071202120301080609010501050406083c0f010509030a0f0807090f06030504020a0f050f090406 72
    0x242695100124150240c00030615403401180034850b0702024401d5560000080c0000c51501d01000a01400706000400f441040d01884030b114540e0f0f01e00380302074030085600c4080856940320945220b1841003190040c00240310424174100890720b01d4001200007441e15403140d00704102d081d01c980341c3d10000011440d060007d01440c401114103144203941c4620080c1c0c0c03208505008520b007080780341c40e04290820401d824203403000081481a070440f444503074854000074a204072140c05a00701a031551040b40444008000052105004107196104105c5030002b00035607a00e03074080004072680c5004070116035000c4803c80d10661640350012401d482811403044082d07840c1d09000296140b40f03d24030710f0b43c1e0020180c003900c46009000b402d401c449207402450400c6c00c00000101445121a0b20808000800c000f140c284c0c2e00035590f0314041d010301030080a1840c3c807402c015000c1c180540301280910007600c0d0015014204c48244010398900412640d42749500c0d504020140340050300030790b062 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 177388129 1250 177386879 177386893
    0xa110d0912022d0c0a060201090302060105040507051c0902030a03080f0105150403060218130b01030b0915010c210f020c12070b090102030c01060306050718060504170c030d0908010606171305 84
    0x65514845000014441b80d40041100c0c616458001d0525506900550081e400d0100b801080c54009068034081003400002c808843c00c8480d02e800902000113001e50540285240718080c507520089a03849104800c89551250341d841c5c0030b00850445034003e26003849000e01041c00045c1c7c45400420401d020140307004003491503280003480c0d0340841d0402d01d00c100e80c0c40c4148900d5503098000d508850104071801201e501d056030569540c24044448503040100d001e000c1420040c00758400e4201c02540c40c90000c4c403c8031881c001c0c100c095100c00640140c40394241e052503624125004903d8920683d0103002c01900e0308172018200d8110b40b2074541580018000f4100012003449440001c0d4012100800c1030708040c40b010741000c0d40e4134582060702c000a1803c1c811113811404130b500700c03241185104104503d0410b141e081103004800300e0b82c140641032080c120950700ca00d441080e542c0d007100030000b40e60342d62030a49a8007031b411140da15000240b000a108890741c8002c9202c00c0d40900290b03820 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 177389379 1250 177388129 177388153
    0xe030c0a081b030304030c0308030613090c14040506033f090f010914010818030c0607120b1c03030e070909030f0306030b0604050a110d0912022d 64
    0x1125229030480081ca6000d00020304140c035000401d0246044194041c610b080e040d0313103503076840c8905400007800c01040000402c51079182d0400c02c4004c801c420004002200007854500700e0100701784615001204003461481d5031f46010300c95a40a0030009000b02045095440804a06c0100c5141c0c0112100c0040d81811207110f00f91804000b0318051400301d9881c2000343c20424401c5031440600c2c10071030b020000b072002e000300748001100040c09082400440c1c0c1c40034a4000000c4403450040e246000101d5480d4180f040000d0f910301400842d10f440504002d4140c0303500c01c64454142007640030408111800d452150880380410260280c40e000c185074520b00c0d219460240c403a031003811429650100c10b800e140c1d00051180d0500040e14090142078610b840b00d0301400c1c400703080c042c1310b01da603034000c600440800e9004140307449c21382ca03846840d0010108244024180f000054550384050440c49081a00c007040b812640e642100307522003001d811a450010020410080d02030b103210310682070403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 177390629 1250 177389379 177389389
    0x33010909110717041e0906060903030906050310090c0c030e06030c070609110a081506060a050406111507030207020901080c03120a0509090103080403060c030e060610030f060b0306120c030309010e030c 88
    0x50200c0c220f41707003c0e851074602d80500302d5081e0b50000f0100142210f082c400698006032039411215a49030440c1c03079407111110700c004ea00c1c60364019000c180c17070986c0120300960040405500782d802070301c0300e0850b10180300c14491383e4441150707218038a0750104030303240020341e072944080d103070328064043c2e5802080b144010581d0724940760416201d41e0310002110007811b540411150784058165103207414040c158401030500c0c0030780d01600c801d0088440080d18811010421400d0301c0020090480075404c20b200301500940c00800164040c0840b003002060000c0005000d54155038054010a00d00340c5a8006018640000100c0000c00c1401c01031503c1e03954420402030f0286005e490941c0c0d42d1491440d00600b1200300203440014907080c14441100700e44040340071135000b002540c1844d510800350004500610302c104070b140c0003078580b54010550920ba440903501c1010103840c80e069040c0310107841035032007680c0800d60380d0507407080000001e59445184e180011340406411103409243c04c10000e1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 177391879 1250 177390629 177390659
    0x11d1207031a060901120f170903060414160b030703020304020d0b0907060e010c03020c09061201180201090509100b090a080a05011b11060402093301090911071704 72
    0x421000010184503e62030f003400000d0040c80e050064202411190b603c20040b002c80da40d000d8000c200c410304041e00411080200ca02c0c028005058605500c3d05107400c00404901800e1041c81d031091205034109211100c06c0c040c2034401c031041d8542103956200045000e980018002c83c4c0146021040e48000381c070841086000e031710030074090310000d230900030300800c00201144100c4c10414000d0005010903000304620081c07030350540340904a1390b0b60401180f80300243c039105500c95860000d40c0351100c1c440e40c101c0302d4400d200340c0e1480031031550791003005490101510386400c10200341c28104081d0a98400401c04041c003d490203003134907078443d9180d0401c5e00c1c0040688540c0d44442034244400380131074904011032420b0400141d40842c0b091025038800005000a002d02c001501042e01d1510500c401420071611b403881c22204d86031003410806c07040080c001203000c00d00060b00407902007002e0041d1200c2c2000e0b450301070b0400050340c5442402c1d454090603914005000c010101c2d010306a58044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 177393129 1250 177391879 177391913
    0x306050106080a050606072a0303110705010207030503030a05040318030f031701060e040f090b0412121118010311042c0f0402010507050c06130311011d120703 70
    0x40a62401c0303000342c100e010041c02c0f046150b02e00810400d2543d5504150b42605410012400d0b4500d000c88a00524286404061a00301907010380001007503401120359a8060700d08040d0342400b503480005a07036841003404000d28503001440081c86400d041c0d0300540d8000c0c040d10f000d910581c1821180455403604d5001507510100c194120703402d0541160003181a4011008041d40d81e600d002070040000e0b12060a05104507120440e10014010070f4100c42d0783c0641190001540d42858603005030f90001c13407d8080c1c0800c0d0030342451081c030b8480e4072601d240c1040402c24980383c42c0070b024441c01402c41c2190300300e06169a072000710b4201184080604081c01070707040b40c0318000381c100c0145021714003510030a0240e050520304201030602405480b42c1c2055080c00d04584444a610300303603042411058941d5080080481c0e40d0040482e41003051085130b0080d444211828120030044074100710070760000c132102421102e440898103000718000306030540c03c0c0540300002d450742d83d1802c40d0b5240c0c0301030b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 177394379 1250 177393129 177393131
    0x206040609170715030213050a06170f010303020c060a021c050405040b04020306030d1b08070b10090b010c0201050a020709060b04050102070524071103010f050405010b06070b010905060102070f0306 87
    0x184101a82c080640804041e800010010285041c850640c4000e08080705410503801040505110b14a0455403000d880020030403072910341c4462006142210600700011807a010f01c02003106062a0580030f41600d0301940500709805501c1c06111580c0e1103000c00404500c00d9504030300700c4c41520b0709980160800707503469036640c41c6004c081105946015454a100d40c0c070420500c0100d03580021140a555502e08108400c4640440d40d0ad05402c0100809440e007000010031400b0440b808441e0343c402c1e07403000c0c8dc074450661603000314422038891241613404515241c0d81c04001d507003d2800307070a02c00740500c1164440c030f4031080072500307440301a072107a07403017080c0400c00344003540e0184600e20149c0405d9030341482600c034005141c421405100b011b0712403080009074000074000000ca003000e6000014000703000503080404040000c00080364240c40a51a00c0340e1000e41d03141030000c5403403541e003007940802d8a908000000c0001c1c480034020505601c110040000e24200c0c0c40b0848000f5070140308 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 177395629 1250 177394379 177394397
    0x21e120415060b04050d080c03030406141b0a0815030a0c08010f1e18080304031706060c0a06021605060c18030106050105040909021908010204090612050706140702060406 75
    0x5800c001c81810310740d0800e1000e0601500b807250101c803100399812908200d914516001c52410700c0c002603c201c0703e082405002c00800c10091141e19040011a910040070400c0e13607554071141e401140d00c1446188400001c10400000301512035400240c001d0940b214019180f201c5000091420b410200212202140c0040c108401728003071041258220768181c040c480d020340d0b4a0042c40702050099084001641c0300c40304015006072122a44080380e100102995908250502402441e52001050441d05030100012014203080b810345031b11301450b100410a111803a65500042d410001a0418404000c15124080f0f2410010580682c0e089254241c3c4c904044510f003400640d02c00140d40284c1c10200200500d0741d00004503412106262070000f0214160701c0051000c05d103400704d0700a1000746081c081400e00040d40103004031440740d04100034450340c8007100110b4600140000d03280d03401540040000902070040d000003604001c0d81306280c08140d500182d035030340113900044000cd80101c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 177396879 1250 177395629 177395633
    0x110307020714090f010e0a0e010c030b280501120e030f07030f0207050303030c0a0e1e010207060201061409100e09060a0612170a02010f020c010b1c050a06021e1204 72
    0xb084a260760109541d50380c03052a00c0020300ca03400c0018442d44a290301d0f03100004008201c2c2e80e11104400a56400902000f10002401000340030b1082003030b8402c24075548810840e03c172705190100d07015171b145038100030b2900d0000152658aa01490310811070b45660300400c0205051000f403000e8103a40211540303e41b813a080c0103100303400e103406003815548200802c1c0302a69000060300c0d03002680d41074003a03543d44a40011280207c0d444402d607000b4070000e20b5944442c00444000039514420f81c2203c018558841c012403da1340c1070320071b80305400704009407120103090501c01950b10800c60074118500940d10f00f101c07143c01c1030468445a00350420814084004064001c55000741041e040d03141c0409020f480e81d200100301c84a006080c500d001400006660007908410354444220303c086444007001c480b01c0e400b030316020140b184035071104811031814051600f68600ea4540040c002c1081080030f0366140f000b5031042c841202d041d0a16140040c01a8008009003550380000d428219607092038 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 177398129 1250 177396879 177396899
    0x1020703080c030106020a0818040c080124050304020d0201050403020307060c050d0c0302030d0c200a151e0b060d0f0e0f010b0609150d0e0601080706020a080301060507061103070207 80
    0xb6240301c0200e1410401013104641c00a00c1c04003d039003000c01c49036115401d41074201941281c0b0319080c1c0085c140001d001a50341c121080034102d45d429051003401441d9140968001d2a01000c01c9000c41c0003072003c00c016041010307082d0812407041c1031061a0903204c3d00000c3c0703070000a900038030005403005011420402c080c08000c1051006081c15101c203030090b50082d44900822040a48032590b800d06001c0307242c86011190700c3c1da150702000040c107000445426440d0840010280d4110f18080e2405c80c031210070348074200319514008150b40c8180841c1d10f480c2c2c094170301548a00d40c005800e01103082142c1c0320b0711500345581b25400340001d21a40982c1c1c050300303095580149007402d0345054003050300e07503c8100c215811094112504114260000c10b00c140c14000c0ea48040d0450340341c00416030080100089281c1a240b0080072a420595207020480c0c2c0c0d000c0705040102101c0d800d000412075103010f48058034083d44544800324200310300350407041c1940c004075001801a4042c080800a04040c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 177399379 1250 177398129 177398131
    0x1008060312040e040c0503060c0d200d0e160509070f020f100f140103021c02030703080c07030b0f0613050601020c0d0506060109060302120105010c03050f031302100305070215090304080109050102070308 89
    0x400d6020344a640380c0309e00752170720a028a10105e2425611090314964031440544400d10400f10030b6920703502d400c151b4500c6001455107060300b00342071007510840040e280220b543d400480d0310042c40e504030b076a01c0c52000c89664440300328000540c4280c442511001c0014008181c11902421300050030074103500da4070050758014508101261103400051025031610b030040d0481d0640003c1070000f0740aa032010a00e058801c0e4000f0b04010400718280d95607060101d806802c89000340715102c982d80343c0580b0203101c0402501c1942d8070860700c040c488035548080d0080e950049050041e5000895282c01064800124800459881e04107008009040da04001c0d41e901070000d501d421030070486030840854580b10103000d018107005c004840501010b11901c1103403442d041e030250142d12307170a003140341c44854059614124420440840b9907080d043c4248103082c82444240e006243c10555150900b44942c0040c014143d180420000407038020070174080d00303040e1486000016a0f48019080003006000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 177400629 1250 177399379 177399389
    0x305070b011e05010f050909040b040605060901080c0108040f150c0f0c03170622020909061c121101022704060f0603050c04120f020306070e1008060312040e040c 71
    0xb052406181c200c0348100004103a0b8001e003400005131185030000d4490740034a00549901031240e400300002c0194003060b09004900c80d100522464440e0300c204440e05c1001d0050f042a0ba2060032860820b603c54140c054200f405160717403401c00035494850b02c41481e000e04c00380709410717280d001780301407580e005640f024181e419141c40c4000c420959001000c0b400c2d6000d070a003402030310740c0105a0a943e80100ba6805181d41480d0300ba0800f8208442e01c041c1d00040a01882641c40d000003030202c3c00e054000c401221130750108086c7c0a032250f07480490300d05481c0c3d440020407110718926039a00b00240f0042480c46c0783c8100000880c0c01f00b1020190140c1d1501c2d126006078144007041150702036203078030030301036845608021a56070389001400c001401540d10160140c072000d5420418092905454520300d4000c0d003d4942030760341d0002c240ca0f4080e46a036402e403c880d2014400308164030801c41190030000c0141560f40a01d08202410220380081d000608130007800070a010070042c50404101c0104 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 177401879 1250 177400629 177400649
    0xd120908010b0105120a020909090a0506010b090d0605070201091e02030c0f010906051605070b0304060507090b18030f060a0c022401051302070209040818060906091507050a0305070b01 81
    0x141c80d02c0000c1c01e600030300c06a206112001da0110702102c1140d0184d1360301d00005840b00d1107e00c0c0c030081840d80c500c2c0c03040055480e03000390f0001040b10722140040b1441040c029103c001c812803d03075070314002080e00618600865582d40800b02c0000d5800c07441c202050b10a030401c21034916580105803c10340d818807818401e10915103a00200d0360440740c07000840f4241c0c200070792124035081d00c1d00c40340c03a80c0000c02840c2e4002e0000c041004058400518091801120204241d0351005406d644803455070141d404520000d100c49140e000704060500001640641030303403c040d042d8a5006d103407402c01e0310020070b503e40703e5960102e00390f13041080c140340d0058050b10311000d02107800700c1c2101038818010203000d4001e8401111541885070100c3d04490b5001d00a00d0b418503040c00c0402003074101d0038044022108035030380154149403c80c1510180304005001b2441c2c6000704081186000d815000392002e604180841d2001c6241842206019802902c40550b0350010b0300d448007030355105800018586c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 177403129 1250 177401879 177401891
    0x513170a0c0320031b0d14060406050a050105061614070e0c0d0c020d0516110d05070f0f180903030b0a0603090302010f05070f081015090302130209030a0f110d12090801 74
    0x21006805242c00c1700c00d01615040c11010090505c0c000140c002450700d1810b100d00c8090000300142d03580400e2056083d880b040095907256010444a48210400c003080c00254100080106250041d15040c80035004100c0d150349980714003000f440728040750501441c1c2400300b984039000e1000c0c0035500b12540b40d0710240c203114030001c03005030880c0108504940407501445101d0100f0007508001c8480020040c2913903040a003a01d0400e43c1c0c1d44690154450100615100040380100c0480010a868000d030254180050340086200104102c40c0b0607400c01d41c07216480c40040c0c03103818100c0058001507801080301c1d4910709000c1d00352910811182038251808041040e01548500a102c00703401c00d1605000b56200e01091694540c541d801240e40c0e51100c0742d184401540007036200b411a48240e4a0b60748217040401200300324000d01010507016041200c084c0e001540700c980c001c0441e8450780000403104600030102d0303140d4281c0c90049440300320036102400e42941000003c0c0092407000000d0000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 177404379 1250 177403129 177403153
    0x1150302090c090a090e0604260708030907030602040303020f01061e12020d080a03061a03010b09060c010908270d0c1401032004150513170a0c032003 66
    0x14428002c02514266401181601c1240d441d01695002400104024440c0d80203c04940792038032016101100c85884808100c0c280406c50440c5071904040c0d950110b08140b130070744036000b032980001d00e403214600840c3c40c08000940385101400180d1f019900070200310794841141421a10260007191401026000100004040445000035107003883c001e007c410389184040f0b8203269040000404908020514001e90756042d0700600844007a01c404102000001d000002e2500c0300380691241c000d020020505c641c00c0880007400166095400021100300d42d880740343c8035030051415281248504410400185ca9820980e00c1c11141143c91005055050780e0319001104544200306081907041c40001c43c1d40e00039401200c4000d41c500b02003c410703440800c1058140d00c14003505c1480e00c0d00f41080d4000c2880784080c1c2d400401304211500002d41011500f80d80952084150302541c8981c0a5050010300070f9600e4000541c492443c103190011000248074080c10940c0d01940682d00c0a012601 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 177405629 1250 177404379 177404389
    0x608010902090d0210050d111c1104050f0a0e0702010c0e1e0405070e060c0102040e0f0103030c030c060e0f070302011e1d061216031b020d1d1003020c01150302 70
    0x283d00c40c1d0440c0c02c01030441d00c04005072003074014400300121151808071a181c0d4031412400030300c03501d80386581005070340410240324022564a1102d410741143d082c0024001801c00f8640e64002e00402444080300c580e841d40c80f0070303030741c04202d99100060f5158501411280d8020150000c0d00d1001c840c0750f00c00b0042c01042ca00060017120545105580362070204024600a185500035104041c00c0f03240c0e02e452140034140030b54824401c001c9040c04910008400c9000b40b861913040c0c90389a50b5205170080c49803400c4413a404107010031749140795500301c00c0d0f40300070f402c0040030043e02d0981c0260041928600016042011019103407a89a54040c82c0d41c007042d920006458840c4181840301ca0b500307030424003044850240c0300b02c56030480060800e025404180025071048168a60380a010102c1030b1885182d013002c6d0794a0300000742c1e100d800f1a01c82c1501a104401030701c0011582c02c194270616038002000e6a2045c0703015400b10364001034407100043d007030099283c806c07000414005000e00e140e002c61 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 177406879 1250 177405629 177405649
    0x303031a01170c0c0304030506060a270b271801020406090b0d0204081f060504020f1602010c201201140105010c0303020408010507030f1a0312090a03050f07060801090209 75
    0x42e07511844000182da1251050984003c0522002140c0d181d07a201c0c40c0590341e070281039402911a840700da20016074280030303400c0319600340d0743c1500c640c61403503019100b80060461201c1081e4880301450180c40f2102d9003940da00ea070a000046120003e05080c01031060000d8140e0b404581c07a40104020720071035420010b02803c8804c0121055034170369034480220028096900040c90fa03008442060200ba6003d041582c44034802d01c4c01040407030364030300401c8201e1140008650034031506000e00601c58018030304151007140103050400749206203503920403000c003011080314a4604405e50010381810214485158276003804003c000c002c003d456144c03500c0d80140b02d06410005400c1440c0c08040c841e805030f030b0007400d00030020f000030300346140e024015102c04600c142c5168a407140202c480050100c50845140f40900078160313008445001120b20b80c40030415a8100c41a110000f0005004214010340304207079501400c00d440c109280103000301e006902c143c1005006200b8002180d482400c40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 177408129 1250 177406879 177406907
    0x42103170c031b04031401060501140c0d050a03020c07030803091905120306030a06060f05040f0209130209030c0a0306240b0306130e030313110105040f0b0a0c1203060303031a01 78
    0x484005426450304003020311440d00011b002c0300001c0c0d0b0480c41c00c20150071101c1a50f00980380c010320300204031a202d259001d00b0a030030095134044041c1044440c010304c01401142d055160240c03038403000844081c40c12500b50300c1200d00c0c4000004110a14205210a21928040000e500007901490300e5041d80d40e11590401c80c102c8038008003203a11a40e04101040102e903000405100d0255500311043c3e4148803445058060341c104078003501028140c1c800c4801030303000146607000344103400100c84001e41001c21060b405101d1031010500c1c0d55102e8190800a51051070086100306042640c003044540c240b000000381291400103000ca00d06d920180da41c421001c0d10601440744810305954007a101c0703500e006a5900002003401849026108a05101401401c160103a12003075001100c0f00e21862140d616040402881405100802002051003281921313200004030026107582c1000c102551403900840d030340d400b0030000c168050280f0214020003802a00744a00b4100002e425030a081102d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 177409379 1250 177408129 177408151
    0x30717070b0d090b04060b100302030f19020c1203150a0602070e041e05100606050406020d0e0f03010c230708030a09050f0706021510030c06050f042103170c03 70
    0x2c0d030148000c10341c000c003549074004d00c07200071904040c10580c004200d1707085110300070312401b1004125540a0f000300d070700440c0c0c0c52807403901d1940ca070181c458096551201c84100c041d001c20118408410420600e102d0303c40002d9410b580e400e000702d020004601e1000c440d40201c81e412003c0025680100b250412144100c2c00910156070394a45025418070703107001c0d01e0b05606641c0c0e015060150015907000d81010070b5070200500d94450000741c0c1d03d40280d2144000590007200042c1c3d507180b0449000c0440030b005014603040c903007600002429a4a400c04c8100080e61000c00030340b581c501c3d241c001e030300b00712504807031403600285450300d803168070004001c2c1c4001c84d215a42002046810061015024412001c2d030341c0007900d610000307485a50b020950f43d980e805e1180420b4a200041d0013000440744e110140a810383e00c2d00c10f081e0303455000301154505082051000181580c1c0c10582c03039443c00341b00640354200c00824500544590f05114101c80007000510030010240c454074100d03a0041a0210 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 177410629 1250 177409379 177409387
    0x415110f031614031803010f090506071101020f28080402030303040609022d040605031b0d080c0d090f060503040b040b0612010e0a061404080409050c0d1802030717070b 74
    0x4140c3c01e5141c0ca600050103d1100045c1c150707907800d84180c0310280307030011030003031020008800404083d14560b44001d0615080200482c1026005021a2000842c89400541003040b09002c1c00304540013100b1516182529980203119070803032240d40703800d280140c2026665400c0607004240d4a010040005141660302c40c045015555404054a0800440c00c0022001c04020405424510180c001c0500036414140d02099070310b03001c40c000300041c0c100300c2605e036901544402c00c801c0644071b02050b511750b101081001d060b10414000c0582c20702c42520703441303100307403074540c0343c2d140102958801010090140280310001d081e620b1219003040e080420650701e03403146000100c408a40d42c0e8a50f84961800d80c1c140f29507c0041100300695020b00d0080044002d000322500c1c410008550017013020108000911034001340380e0016401c000081101401e01d030258002c01d0031504e03130107100102c1006040c0190b0842c42c00f00f01c0e509c05004542049248903400042995072016507019810030114089 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 177411879 1250 177410629 177410633
    0xa021f080c070c0e04200a03030c0209100302180f0c0405010203070201030c120f14010501080c0703080703060e04061b051c051302190e010603020702010509010e01020f030415110f0316 81
    0x48440003d0254a51021440c5c20700b0314003040c80c43c0d2a0342c0800c00c4242c0c680c240030300e980b17410303102001200d415403501c50840d03140d682000307042000148008882c942d005d6000c00541c807040d50300052401056000034481c2003500001600d51001481c1c50054039041106100599020040d54142c40d428207012840203011003003544c5020f0004d90a42c8400d14010940d000140150040301e075071607081d404c00b1043e9032a1401110706420841d40612a5901080150002407080c90100c0c1d01c0201c1d4580003032115107403588081906400c0c0c80a844203078444051001005c00105031580c0f08800d418510702e000003803181003462103030100031410101da49030001550a1038402104078866401441c00300f0210700080c0300b0582c40c4540c000c22a2a810490000c14076a00900c212404190140c607100d00b000c0d40380c401110f060108512090440c05502c0708880210f40c100040e00140c148401b9400220b00c0d21000103081c9801a25142440e600801d119002c0745c20110840e21842030707103100d0560a210758 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 177413129 1250 177411879 177411893
    0xf0603061302121216110303040b0403030c0c03021f0201050603010504030f110f030a09030c06020c0105091512040c170c1f110304080303010504050f061f120e0a021f080c07 76
    0x11060f004030000c00604d0b807019001000e041c0407400c0c406c585410180c1016070038555280240c0c000d5030240e140801090011034001c0500c00300c1144950f00d926550740c5c503540403640000503000300d094061900c41100080036028090194005002c0d0020022481c0c1074500034500d40000b0312080502104848140c1400da052106031100c00f008000c895903142300d4074000701810390921040e070700a01984808a040340c80031a01001100c0305035502801d00100300b00308003181854a48410110400300104c200e0041c0c0100c0c043d200d140502109071b0f41d44d01d0400c07000e0b00e0030400702901d042038001031000c04040d6240304055000c410f41c50305c1c1030300d446107205007078034a03040003004114284004a00000c00c0e4a0000003036040e200103035020700c440e494100300a0794070354003590700540c0320460070186000c603034505015204109252900701c1103d110030000e842154002210000141c1201c140207041d8101181c2028007961010100210b03180d51007030052034044094464041c1d054002185010700202d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 177414379 1250 177413129 177413143
    0x90b07050d1503080a02160b0d2d2426011515030606142212060501240c060c021f020309070929040e01140f060306130212 54
    0xa400c00b446a4103403282080d6502d500700e156a8401403280c51448429400048940707411500100e815a0801c401000c5106c007520040c000101e8040c1d800082c0c2981d0000c410381c040303a1440c901400160440c044590f402c028008180a400c2c1c03903202c2e10304004251981041c002883c0343c020f442c0004410401e5060f000d841c0300c2d8a45111000300c0d030404070340303800d43d01091038100030603450420000c0c0e5035182c00e685180b1340f0354000b200c0c14000c4c424000003c000b48240d03403035032804c1c40b880740c1e1103600e0b11603101c188004442c0607682541d441006101c40c10142a082c0c1c850110096012132003540400010700c01010124010006030701e0744d62849440b4001c0001400900c3c0c42d540306003070401e1460010f0004d403c01c403596009031150650000380c2581c0c0b4490f000341e41c018200c1d914425414001c0c18090b540ca2881d1154125941e0700142c0c2c0075250038421050413070004490300200342402d0380c072800002000f810040c42a0040401c0c0041c5005c0b030038100007800c0d41a18401210030400e95800d0402c08 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 177415629 1250 177414379 177414401
    0x60906030910020712120c080f18010e010f0510210c0504020a0c03031505010203030a1e020703030209030601091512051005090c2107090b060c030d050a050a090b07050d 74
    0xc004100358040101700d02402c1140c040315540c2500c00705e00051000c040c3ca1148800c900490300001c04107400740d00452402e0340c042c10205130515804620501d582c2140c4d600482c0c03071900d940d0788118101a60f814080c80f600b0804140d00e0103e514100003281d003287c4012903c54440c0003540348403008001000210b8801400020421034480c920b050300a0f060180418040700003034540ba503010800e0002c220050252903042c0d0085045a4524081c00000d20300320a084100c036102c540454101c4d5100d00040100a111b56000f5841e110541e040c540307041c00603041300d5030940c14050601c402080020940c0100d8640b42e450540a1501d070405505162480700a40d10b21b034200810403c80e094006131003107984005a80c5440c42e0031250102d24030034150100300c0002d40c0c11a5604100c074a0f4079802c1b0785400d81008140902d01400c4140e1249180c2c806502d918020751075204011020070680300300c3c0c0d84041241e0b02800034540d03658a00316490f100070603074402d01001007107907001c1c801c141c0d2018020346 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 177416879 1250 177415629 177415631
    0x31201060e0a0915090e0114070e1504031a07110a0813051806032a0d0c0e0a140106141611060409051501090320030307080307111b060906030910 64
    0x54560036140458205134060140f40d207050050600b07405c6c03014452280c0c0c00010b40440c641e2501c80200444540b081e013182144e11060304c640a04103000841e0051005620a0040303044800005444840c480ca0090001d024031248805080c1421000710300c588500e540498480c1e590031030280c2c0c062051403240c2055400c2010503007010303800d40c05c17922518019403088003103640c81c042d46400c0c041d408a504440301c20394411848114018140480030f20241c5100d41140072040d03032500c1d0180e4107500100c0708800000e07110341c00d000700404105c0a09016180c0d40ca8030f0589840702d0a80810b1512400c51988a0340c50390260302000d006185101e0009043d000b020079542c1c41c1d540405402810083c0c895113400181030a9084d0991301422128048076400207c40940721314051a000740001084441501404100007540020361010029071251101d502c0e6100c01180500a00b45003800c2020040c0c0b80d00c840c41741c1c003490fa40d195015110420300071a00c10760b0b0303980c1e005d50590511070240482078583d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 177418129 1250 177416879 177416891
    0x90b1f150e0102060c0301060c140c0402030705130b0a0804080901030609060b040303030f05012702090303270103060305061303020c03060c071401020901080601110a140d11031201060e0a09 83
    0xd903900241000429800740d08031140e03500d80803d414410b201c02e01c1048013044851503183c001800d01d000504551056500340e40604104002040903039008844120003d2000518205a0703030508003000c0160a0072140141450780110001e0f2607048054400380040d0004141420b082c0e110760010000750604c02c000b8000e5a54484254601d6080b03030104401090803c00040c484800e10320407681203860310003e14100d001c014000c43c000c2811440340c65400c5808101c0518240c4041000708100031044c1868543c08147c0c4a12508000c0c01d109864101410440c1c208045100013441d00e80110300c0e030301e440300310900500e402d9250a6010180c0b42d058000d1908010300ccd462118090132407280034081d040302044240b4105402c0f4030031070500038049a201c83c00b03da8154800e044031103e132454281100c566112503103400492503204484120340da0300c00c07410500e0075940201c0c26806d66079540011410f041c1751265000040f60140590800c0102c104082d48095036920640001800080c00800c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 177419379 1250 177418129 177418169
    0x1204032003012409060803030c090105070f0804080304060e010219060506010e030111180a0e0c03040c030b040c0611010b010e0f1f0f021506031504150c050c0709090b1f 74
    0xd0406a4813401c86010300d80309001820240c040b048070302c2188060000c40c500101c190054840f5003012209039140c10504505600050701380d001000a89803080003507807280c0c92300800910001032920002c1c1190044100c2c030001c01d20000846c0000da40c48400030885640e2080100c3e4a502c0c901001c07540f5608180b0301c00f1164201c0002441c0c190114601e4030340e00002c140034082034110610804018900c068006403542140201440d0000c1c440c5d91204181c5950780c13541c2c3c071070000a8405980034030b0a10401c11000303810a4250424a503214004e120440c0c0038070010307100720340c038540b1940a649412250b0b42e60744d81d850341400f000c40c5034090300205200c1c400340c001c007036041740d285c208054455a0030404207070388960041c500c6454002e0083c10072035241424101041e4018100f1508080b02c000c8204c0300c901240501100c54660707980f015112640040707078a26200030b90744030500c42440d040c3d10307074040703031000040c91341c03140c0380404910084039206504401c0c00c61940c0f040850500390041444 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 177420629 1250 177419379 177419441
    0x402040f020c010c03140c090102060723070803090c010306050a06030908090402040f060905220c020c09010909020a05040c0e0108090c0907051209010606020d030c0e030d080405120403200301 84
    0x10f06e00351401d12940303581d902e400341c0750302d0351090391420741c00350740040e0000b50441d12030003411a0380308100e10b0303151107140d41c40c444a860703401c0120300b2650340e4004001c12448170406c00040311401024030741030142030302e4000414503980181c002c1004040e122000f8405201000e0304a882c0600c0251046503a03560320b5400360300c81040d901130000003810f0300c580007030649401111051b00320036020020701c00c0c2030f5842100b40105400302d118015805103480303144c2140e0310400312500800d0f400d85c01042c9130b449071040102e24001030308034600c55441e103651b46c4c401543c03011b11202007104c00e003401071050f15441446403815811001e40d542c004440410800b00c16070040181c010400182002c0031079880d10f6060078260f42a5002d03180041c1d11001c03c0165062280d001400c1405184c1410394055190304007103410001055080340100d07150900340001c100041180c0312814a1400085082c103007181c0c0d82440c4130b840c05450842100c07840800040540c1d080d8068a840783d1030b966015804086031000700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 177421879 1250 177420629 177420641
    0x30605060c061b03060102070504090219180f0905061f030501050411040b0301021e030a092a0b041805100806041103060105010903020d020603150d050c0f01030209090402040f020c010c03 82
    0x3d200403480702e1514041c2c1c088400341c9004000c160054901030f030409052200604040c84141e0f8000341c0011008484500d502c0154090406003280c400a0100c06254400b038075111400c5141d035903c0c10500304081180860760036002402130400000d840c1480002c110450100c0d0409441d6510780b409010400000d0100034010310710a1708c1c2032002c500031804140c200d01580c0d40440310b0b12aa04811040b060a8000555001070700d02c800140d0103c154030340c45e60400e02d800c0c09903a13041900c004503c03c800c031074000000501300c19107113601c3d00b030400540c000b0b1039611108400d609078598001c29409a102c02174036000c3c002c0b06044920f20b180500301111080f501d00041030203805880700200c0c15512507001201640d4000d0302164140c10280e0a003d126071004040001c400c4d69900126880d42c4c42841d103d0030507009400400ca0b0600041c100322800b0750811616040c0351040114602c00d8844440440c0d000b80c040740c0002d5002000c4040f200a84100501c41d24154a410701d000041d0350194010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 177423129 1250 177421879 177421891
    0xd0204080c06122701021201031506150c0c1a090a0b03270f0d02030307030c1707031515091e121e05030a052104080d0903030605060c06 60
    0x50740380700e4201007448401d200f030000420344000800c00254142900e9015035048405030801e2440d89009040b8081c00ca81201110410b9011200c00410038050032021708030134100120b6040140c285400511050382d07260027680e40c00c1c000680f01810a01503400820700050258407400100303040528418000c640c00581840d00c1025650004601024881c041c0c03882040849000c6801d42081501403d100180409402c6c0611800961031510030b41441403140084c11034009584901f400d50740601038460040c076080801c4036201c0320307200e9039071803a2400b41c01c03040074240050312032810000600c0045041c2c00c203480c01d004284441003451b6001c60b000d8201c42071000c412403010400100c490072140d26104008000315043c00590103e1581c1220001400d12404c0880f0700c2699075030b5640c115000320038098040342d0702060b6844561074000d409a41071404801c80012490b10f99105101806920101600c155072107140804141c001e42c44a03002e040020a015155050900c0e2140e80e90011104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 177424379 1250 177423129 177423133
    0x140718050d0b0f1503341706070f0206040f02060d050702031e030f0705092407140f070303080907050a080c010f08040305030c030a111b06011707030b090f030d020408 73
    0x143d10106503500a04e03001801409001c81c03901c40000d8028082d2140c1c00da03610100180c210000c26400098800c00410203280d0141d142c0040084e0300d828444028248814001d155102e075012070b07400708217a640b05901040480d2030725058004101180134070650000c2680c988001d0152141e0000050080182d44c600e00719098600419a86014042968401804e501800101d01500e005030003815218101421940c0301c1d804849010f0003043c0c03030300000004600001202030501148184254210700300500522000300041c80080d42c6a103544030180c100518803020440c511001d001070b5004040080c6164a5643c48203402902c801407480c0850105442d020410b01690103004500d00c142d4143d05c42508640d2684000780f01a440100148020303544d90708003060101c8031902070000300d2941e122003503d02e0314a007601c0745440300c180c1101d0a28800180400e0007000d00141d001d0031760b584035441c07200c9901c400c1880ea180a10308103904e40d90b0300000c60542440f800681c0600101c84900c01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 177425629 1250 177424379 177424381
    0x50901060c150c02030f1c06050414060103050406020c0703110325060e040b090414100e0307080702210a0c0f050609040504050a0b01081e01140718050d0b0f 69
    0x181070720441050403000380072006030700c8803001c0740845070300200000489005880c80d140308404828925800f02d40d20b21016907030903600c0c1180303000600c103180242c181560104022aa4661104204540204924100f40d03d4500140c02c1012079010f1760492921003080381c05060302c0340380c0a00401824010315000e44540c50200d0000030032008071006080307800b001d0180c020300b001d0044550030b00d860440e03034206460310880301003500ca8074940f40c4141c0c0035480b48011108070a15850410744e900340f038950401d0502062401e04080841101c03046130b0312149155441c4030300e1001c950641b1034003a51040390004000c40000c401400306520f500c692050300358035005600c51b240c0c19100d02c03d501800350000d5041c004151541010351000d500280a541103820310341c40c40d98ae404071104260041c1c186908691b02a500160030501111400d4040e50000c2c800c080424040200d039030f4004016408002c0c0a00d00d8030900c0d800d010340071000c2d000244c200c0d84c1407005800c2c49408031030107680300741e2507194000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 177426879 1250 177425629 177425639
    0xa080105070f1b0c1e08030412050f0d0813051e010b09010806010e0402100e040624020a1707020d0b0f04020108090307020109090f06120f1115040501081905070801050901 75
    0x1030f41004003d9000c04101001d03424861951407407a01503440400c10100c4913404142c01d2010006017008100201440d0f0a401440c0342403030418038044141c400e940c0c011140b11208982000e41594860424000d641c034026050808602c0c0c0655510000d180d030190b0301d01e002c161003064000002c0711805554140b140c0e6aa0441d69a440c40309115605043d203a04020070700602c0c3c4960b188450000c0d601e00b007181d000c5064002803c40d800e07641300303403401c40001910b60b0504054509440304000c01e03001800381a14192600350902c01c0140c14078070140703000281e100071550340110210039103402100d415030502e07100c0103c200d0030030301380c070160b001c180ca203400520341c032400000301d0f000107030306035a60301e1405c2c0b8052031a006042c0361404a2103a646840b0086035040e180142040c6c214000c0a07990406030107420450341c00c41d0703901d514074020700c9000c2d0281e42d01d0b81c1c1d1408032400c855080c80e21030003d80e030315640442d101c80108152407526050000340500c00c0c0d44640b03a181a039508440b0710025036a11 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 177428129 1250 177426879 177426917
    0xc07030b0906070e01030504020103060e10050a06090605030615070c0f1e030809010e1c030306031104050105150d0b04020309160b0901171b07051609110f07020a080105070f 76
    0x40b144a0700103540b1035401c4c00154480d03041990010301c18100071a2140c0c03500be41d25044c480171070328180007079a000c1e400c101354940401d0f0b8a0080200d4249840c4103810010000c0c15807100030903903070003006607050488568240100f1980015000700781c417520542c461141260f202030383c0c42203242c1d50445806000580031544040811258010100e030324081d240700041d90380e180b80c07000003640410b0560f2034401e100c2c110f0b01c0441c0303098072a90300040d5580c01c42c9025000c000c0c205c500140a94500801800035032621520140c02e00504d041068894284110000140101c161526000b60010050100141c0000b40c4440d181004d880503410442d2900c2c010001c1e0701075603010303500003241074014020802d0140c100c0c90300401042c00d009005515481410541d502c85003049580c2e40c0180d03a031030054825200b84002401100f5414041d015a40c01000072a010b45103800030380c2d0700005070307034011036595041d44002800005c009012601d0b01c0800a07141c060302445220204000f00c5140f42003103c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 177429379 1250 177428129 177428131
    0x5071b0803030a0c0201060b030109180507090c08011401140d0e030d020405130b01052703010905030c120f040e0a0b0406080619020903030f031308040801052707090e03040b0c07030b0906 82
    0x4230200603811603207444c141002500e80c200d14101c84c0340b000800400030410070302034070000d00102c44010691812464008002c100144e0000f00c088405e1583c000e8142c3e40007200c0950886a0000e507500c0d516042c03840001040c4d00ca98074010b51000041070b41882146802a200b212001c59007c05501840101c410a84040030a0f040c005401008051500c1d10a034240c041c40000c007507109002d00c5400c0d000310b8216403100c003040c0c403290300105404232203030800c108002400c1c0c1e49144450500041d40751b825194080c60061509605559000400c1c1e80c03000e52203402d04110040050101a41e103d25407500c0d584103036240070000000020012480032030b40222418640098015417412420a01d490000d80025080c15899030040b2141c9010546080183c0080e02001d4000140340c2071102c0d901c544800510368943e80041141019622041d010540c0011104032000c0442d0500003080f0a50a520940d00240564a0301007078401c496403001074110181c901c2a2403981042c1c41d000340241e0b0b1000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 177430629 1250 177429379 177429389
    0xb06120604030e091e0c0d0608030f0c12070f02060703030e0a0303090308060a050d06020a180b0406120506011b03020f0703050105090705040213061803060507030203160509030d05071b0803030a0c020106 89
    0x103117a40816800c0c06248000c010318100c20100044041d10386440e182540d0080c031074902c45001c0450480c0c3c081e1814441000700c00d02d643c035802d18000307840d607c0ca50710300e034050b001074031680c0040713005010b06010b0b07000340c1e80f4440700000b0b0711f02008051402500a1080c280240d0000703074194001281c50230000301110a45400400804400c80da03a601c42010b540001949010042e0100118284807079440181e00604000700840780c555060aa005000d0380120400c50f00d41404c203014803403103980060385034100302074400300d2202d0b00c0c0f043d0800b6864403c680700400100c5c414040000103110041d1300042c01030070542c00f960403075503440003040305074000d0300e1066074580c00c9202c04210850003046c42002e03051070040024180c2e9600e803503540480d11f085a130803002c2600001000003142c05040d42d005452024200310381001c210b175000c69582e20400450350140a4001600010300504805904150149060710358209480740c125038dc0304e0700207682c145840d50800c40c0880d000d50060180105a603 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 177431879 1250 177430629 177430681
    0x10e010c020c190b030c0408121614070315091704081218040609020a0f0801080d0c030c0501050a0603020112050f070c06470901030b06120604030e09 66
    0x28040d008005003490503070071060004144840011320300f0181005544150302283c295901c80b4644401103092911414802680c3d0750204484030140480d012142c42c1160000044d14805100702c2105281034441c0c3c00c0940314540610745080c03100c400e60401c1a80c903100b8021020301451f0500255a180a6801548525002843d240391044211005405a4665081c000107407951a10100f41180c41541100740074a0f000503503007958907004075007500902900e1409440c25807400301091344503422006e00c5c5003000110040303001494829004507584079008030007088107042800e00480200400d2008a0100d851003455050f92030280c410b01e803040180d2404c82204d542e50800c00c690303040c2d080000b210010350356002ca02c05540b100f443c2c601010740c0c6440c4000500b1600141c0c0d48100f0022030000c1481e40415662545903d8030004c0c6030440e030b4804074004d240c5c0c82d176400181004403868a0259244500c000f004281580400c0c05d4601c3c1310181d80e0480107842e5003588405502c18240c40c44014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 177433129 1250 177431879 177431893
    0x206010e040204090f0b0406051b090a05010305100e01091406090906060f06120901050f010b04031a07091a030f0f150d03021218030712030c1106090a06050705010e010c02 75
    0x2d8105500249038240c03040d0701d404e1841d0281d80c0e404101000035542600c1e41a503a000300000c880740c068482c01c03440c40c92066203007006401c400043d0074102c02d00445e0f041584510208002601001031100503081c80d03603440040c1e40c1c503030394540c00400c401e60703007050301140040c040307880c504085460390702403151040a044107640e20f6090000b004002081150014802c2210154803110311103254041d0007003c002240d1401c06c0d0340c20820380e200c1a044050740445c2008208006480101c00480e1941700840e40c2c11940e4078000c0c140c42c1c428007940044075410207440b50b41140b004901c02144144c46015005000751100000c50305400d5040f82c0344a403144031007071803508620b041c0f132009030010702c2407040700c0c0845907400d1605400c1d001011203030700207415490744c1140d5107814010803018084551804681c4c030919100281714102c1c8181c003800e082c0481e01c0d02a400c3e2510f104442c2406406004440d10643c0e0f1040100943e1110a094615510702a801c407506203060155071000c410690040010b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 177434379 1250 177433129 177433133
    0xe04050114090c0310120f06061a12060d080f0a0215040c03020d060e01360314070813030308042108060f010c1b0806010b1312030509040504150c0206010e04 69
    0x450f901c050820011a0f0b04800d0001d000745200800c86d102d10303c14034040300d00348810b2611409035080c81d04000a8500322181c1c0400211500701034559416440e60303020690381b80d01012514042c58640b0140800c1d20014038030400252600c000e280300c0d0a294200d64802c05070141c40c0344407030802c1e0340c01043c07120381d200d04101628ac0442860f10407030107507000040c05c030b11629620b03007100c0b2149481924550504c1c2401c00c2c0a01c80300c034080e0a0310580d12004014080341d80c000380f02076150041541180c0010403c681404400c00903901c5d001c0c0100c2401c04655260b013401341103a803049404548646500700000709086419801c040300603003944503035001d902c58000b041808125602a1410002e100440d94007040c2e107080301e0444034500c074032030300e070181d0503c408941000c005030821151000200301c021158258066020300701d0701140c0e0300c2800c030059440c0844040c42004d0450f135101d03040c40c0900050008440c104112500180c9040000c1c106129040e40c42e0702c0c09201d040c04142e50b01d000100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 177435629 1250 177434379 177434401
    0x303091202191101030b09010305010e0c0f030601090e120a051201060c030816030b0d080307110303071e110d021609060609090b03120714100e0616030f020a0e0405011409 75
    0x103c0d80014100401d03809420b01c0031490f101402d07441a5216911070100f1351561200340078002e0450701c141d0310007c402c1a200301080e590801842141d5038160341e51070a10700300406201d043c0c40c120901c001c07140c0c1e4840c2e0210003083c940100c0021221084000000a07480c1c0c000d4011030040c581c55201d42d041a52030f094050300070f1050000b0740c01130540390b6074a0036141d6100c90021412a1241c5107040d102c3c100740400401c140d440d40c0bc1180c0c1540200142f210007504928019401506503422202d03002c00c0031780495003d04403809000d03440c0f18404900040035004a4000e00280060f0f070710320342c682d40d04e85090054030306c00d01c5030201148000300d092001007841d400c0b9080241d406021207140ca06402d801140961100340260741c89007600100340c40b1014140084900074245003800c0c0f0100c50988112615240e02a08800380440200b02c99400c01d4026000b00501ca40948802c644a61000c5405400c4c5026041032a10031440c110000c980300045400c0c00e00103220142c240071143e03a070140410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 177436879 1250 177435629 177435653
    0x3020a1407080106030302011a040506090a050901021204231204090e19050318030c0a05010302070f0c0b040302130c050f0d02070b0c04090f14061905030604030309120219 75
    0x469014030740022540810034041d00000f10312903030002806480e69100701b4115440c80209501c1542804240141079441482e101d0700102080d0000465031181d071111802031141880c0d8440046001042005220340c080e605443c6244003911840070035140040903480b4403180b0051907142c0c0080c8428003c0154503400b908a12844904445e00304d03840c042d0a500c80f02c00c1c004215a250b0000645d41d441e00c4d03004031680409001900100928000720b130004240d51014040c1c1d80c105540803540d4018403801c499000c083c140c0207841060400d0319a5044100e0360721901040c2e000f82d400a00b42c03100d4004910030320485c0600c40c3e0b180b9061176400c00c401c0005500200c116071181d6000d1040c0304c08610a2858a4001c07409a05419a503600c0c20340342d4400d032152019555481440c048400b006802e22400d42940070600700c844a42e1180800d28000e9001d01c29040280c0500ca54410881010780543c4422031250003070413590515a81550b04a94411075910800040404094a5000541024600f0f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 177438129 1250 177436879 177436913
    0x103140a0e0c0909030a18050102060a090305120a06080f1501050d03090b03070504260c190803070609021f020705010f030f05040f0308060a1a0304050703150207031b03020a 76
    0x51268404410000b811540f8103070b0341c14105400000b00714645542041038019490040c0c0c100001c20b6150000203521104020301c1c220340c0a4503141e01c0302c20548201c0450ba155000f0380302d1415981490700501d8000c0280e8022000f41d4030a854a42e1b401410001e005203e4410004829400d42e003088140490441f14400c110305000b0b0340c00c3c01090600000000c2c51180368150741c2da81e11640b4001c08407114000f95020940c95014500940d9446a00441c0710400040191503100c0c0d0941008030814000e0410303482840c0d14000440c281041041c0750308440c071a00d001329454884a002401c1408174190064404009a44410420003031035000d210030b000c1c0102c49080014040002c00000d0050329001c440841f960340b1079014034410140c003c4544c68001106541400d03205080142c4e0b4503007024802c0903110300910110015040100c01c00081000d1030313021100c1020b1070300020150b4040d40041da03085000c10f043c40032501d40d10101c000c0c0d0030000358269008002d1342140d9103074403404001051038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 177439379 1250 177438129 177438133
    0x3020d0f060e03030a050717040803150f1003020306040b09011818020d030c03120b0f060f1e04090b0411030a0207050f0708030a030e0d020c090a02071505060f0103140a0e 75
    0x18010b9001007030000e940309048442c004030f403030701d40490020540d1107104180c0070f102c400c3c2018000450390b8242034039440242418036000c00c008400004a00d9841c02c25250b90280180c9150b29006505401450003940c00b80c0d02400081c0411040080303502e82405041c9540c85401c103850b480e05103e81144a21098000c5c1c0c1d038600c1c00c03554010900d00c003050b00302500440c2034041442c1c10507521100c510318a80107010100300c4846010001264404010344240c030520000c90310200101c010740484e0f42035071002c642c04a00d82c00360100b00034a504248038403000c20b441c007502042c03503040c54003a02602034407844226183d81e5400744200c1c0203402000c01603072035102c0e04400903004a4108006c41c0500000c2008540341d40010300001d040d204100440070190700107600314266203800080c04442c08000310344040c5e446e034504480900034090103030041d1411045d060201d0100b14070742d2086000e007100f580c1405900e503401d001541990061700b0060b0b503610055000030341485031075110f903104140d0002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 177440629 1250 177439379 177439391
    0x60b0a0c0f0f030302030619030b0601050a090e07030e0d020a08090d0503070b01060e03070909021503280c110a17090409060906052e0303081003063303020d0f06 71
    0x21198500c140030b03101180030a03800400e01ca03491825041507085032141540c240422805c40d42d03098580f090241c2054103015003c02c1110300c0500403541c05001c4c0c0380003004400c0710310340424020041c20390001d51071243c0c02402c000071161840401c0c813a0f00f10b07402c003030010326004c114070500c084e50000311803d80d01404203101041c0002d000241d460b0003458250b4600c0d0341c00000700c0400d800d10b034603a4042c4030301602e4845000016140c4180040341d81101076441130f100c0d5201c10414901c45072006880441e00b13003400200c40c001000b9407060704240709a90b02d8500034503246200b140c2d80e003990032025144054165113608080b40326402880d0840020b00702103588202c0d541d070002600c1c0510740071180e40e500c078000c000000c02c858103c60305507544510031518082d202140f401d8209a075000c050204403059000403009410550308000559001d541001907030203503804c1d50004040c0c0c44042000480104000107040403c1d007228083d00c3d0000c00240201c422a40e81c03800c040740410040700e40584030702d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 177441879 1250 177440629 177440633
    0x310050f010509031b0913110d14240a020301050d0f050f03040306091e20012102030f09160605090a0902040806090c010f080403230d021804060b0a0c0f 67
    0x100c09104501d1750100c030400100b0692080000c0050006c00d1103258140c2174120303e020505195200310640302c01e40780c40d05102d0307044c10800b8110b10001c603c02440c0c4166140d007140c081c1a401440c84da00141c40021005031034035290401070784820b10404d5444007a02600402042010440f0322016104208030390001c8441c3c0300781800c680160313001f0b442550f501c121210600841c40003801040b03520400480904400380c2e19981c0070001c03404540b007016981a440009070f401a0031841d50035891708080c94041440d601d079400a588126040c200078165040403951f00b000004001641c1c0424030325444400e82008d800705e50310380150b01c2460740001d041c080041ca101c654401000a07020b4503014098503c1c0581d0603d20f4000507602d41e13410800780481c80c9070701a1380040f816800651624141c0c4070054100400d904880d00d4801e401010003000420000b00a01c2d03a00805c8902418859004455610b60800c02117524070310034041c4003e410401c03003100038424080c614580344506200c4081054613 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 177443129 1250 177441879 177441883
    0x1021e010b041d032502220c03061a070819090302030d08040b06060d0b04110307090602060103150b030304080a0c1802070203070b160501180c0b0310050f01050903 72
    0x111a0184565500e8a16580d0342c14280201d01450700021802030715146500b41144d40d078820305400d0040f207050194011034006a01140204a03038004241c00d0402a00c8803c0450b480545088a80c001f803070f00e111440924040e0156401300d88074441a0b01e82012003603068941940400003c0b00c016204100d22414141c07252540041544640d079515a15800d41c41070500c1d000d03020b540b00b028000d141d810000095800700901d90302080c142c0e202c58851341565011405811300314903541c1d00c21300f060a01041d0090510142d8400c1d0b8640d5181c032515596a041643c40d0b031002e00004c2c00d801490a08803c0349074194209802180340135044030304c0d1aa0310350150b400c0c019240c1040b07607052944c010800690b4003503600d400040705d115500318504000d43d40000e5444100b41704002900b8400324079a250320f415150280c3d02c403034100000f4001c01942416038400e0451201044800d800c601c040424512201d00c10b9030b2058001c5034101846904000c10040c40444c0c009000d4104181001104002d44007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 177444379 1250 177443129 177443173
    0x1110f12030c120f1803040e040303020d1e050402040b0a0b03063d02010f020301081b03030418020405040507050a090e102c060130110c030706050f0112020603060102 73
    0x4514890480d0800841030041708290040c07094441d0310a10003407110280d15030707a558006a241c200165a007a8019200d8083d0401420681031480c03900d050048104082e0021031140344215002c00c401c0802c101000a0380496004068040c0b41c117000240a030304100c8816102d510103d4140f4000c0401800301036003080304940004071544100c1c1c4280c0c110364090140c0002444480e078203504541c1406112036980d88501c4170507410000c0d485407820070f03480c00e00854001e00704102142000c5400341c2d0084010394001d103d568081c1c3c2c50400003400740f620503001d0741c2c0c46880d01c0c0d480c10381c82c42c500032404041900207000c8820134420702100195651f2240d0f40d0207419518645110701094080c1b507205c0c1d192000500307103814004035007036001c0310a20052001c1247d41c1c04412900224845c00c00b010014a0381c500400490078001410198281c80000500209807081b1014003403a600c1d151805203980b400e100d251114001d011511005181c4000516031100d010710480324800d000440590801003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 177445629 1250 177444379 177444391
    0x605040c17010e010e070309060608030c0106061101020702060405090c0d0c0f110c130c180f03050706030207120c060b040501031101020705010201020319051806040303060501110f12030c12 83
    0x15085101c0980004128400d4010003012680d07904541c07410440403150240141010201551682c2080820840c0e5010030054100d010449495030380d00c01d417890007468113000b1100851070a58049015200c14022034200b1a4090000b0b410700340381030240140d00b400601910300f004402d0040d0740d00240c1c2c83c402c0389110302d095501c0c0c0809944074500078020600008545046802c039440804823525031034600c50664500c1600043c1c1d0300310070b10f001c680d182c030484c0b0001d1207500c0041e40060405036050109080c0c0e8000e4054411041d5075000944c01c074461801d005051141984164a01502403d40624614099080440c101c0032240c0007608450090304102c80d0652405240d8203c0d5904104842c0030b001d0a000861a45c184040a00d0307011041d09040e000c01c1d41c2710400140d00024100d645260340b801e00c4101d9003181030519015010300030f40c3c01101c0c0000c3c040114502d40c9000000c2410802d003018014105110420014280070341c0000d00c0d00094000404c918000001c421150078401d407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 177446879 1250 177445629 177445637
    0x5061605100f050106050c06070e011106010e0109050108030301031a060a0306022706131203050405060d0f0b0a0302060d2a0c110a0e13050114010905040c170a060f0605040c 76
    0x45a0580b0380c00303c41c01a0404820400c081c00311042c000000220150420703102d04010012800800040700e00c0c810a02c1c044203240182c1d40001008001c581400c0e040c0c600420062200380c1c2c8500c101c907500d000134030000d8001100b19140070540a034011049802a8016101c07009468484d11038405070b03840103081d20704d2442c015540903103803003043c4036019050f642103584502d421024a0ba400c25848940644405840c1e41401c0000301409101140c000305000361245840300d41c0c05110500030a081d042484045042c5047c05642e0716006c00e4000580750300a06250503c1c12500105008014a031103a0003010515001182d9192800140820030f016607600c5000200a51802c0c1c00440c2184021030301070701c061030080c0444900c5a640755440980300485408144440c18924003500035440b40345110001240003243c1e42020386c1000d841140158404e590b215a615003201604984800007407442c1c0105042c41c00056464105118600c0450404682d10341c0710f0380040c0031652840c0448000c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 177448129 1250 177446879 177446891
    0x4290c0a0318050d02060d0b0d0b01030308090604030f0f0905130209210c011b021f1e05160501020424090f0b0904020901020f0a05030309070f0f0506160510 69
    0x3680c044820042c1d0b180114800460034a0000415200003050400a00c246808201c0b69103110310355019a220100040041d50b09034468200031842070f90a0206400090100000503122007001840b00e014950584e6100300440c040d840031951602021207080070050300d840d001503241c0d62404038045502c1103903001030b615080344081121440c00081c40034543c813140b10703003410214030114441100c8602820308190340e00481c01651040e2050420080d4030010b60200c81c40407801440d076030004040e4544a50103010320070708480301228000b0280e440043d000708118003465449110060485204500240c20300b500d44040f00070803400c01c1003221114820387c400340b5440b64846105002031040d9007030700802d181010400f880500c12491424000c640014611025900c01c03c8203042c000261030a8038050200d42c80c000b034a039401915280784510a1480206000070081503905c01c8980b045150107441e4038041c18001c49030000d41200160001c8144072202041042c00401a011242c040c00148 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 177449379 1250 177448129 177448133
    0x1020109020d0516050f15070807240501080606100311040e0f06011803150915020c0f0c04180f030302070507090510060503040b0414030f0406050c10090804290c0a 72
    0x2041340780b6440310388940ba10079245103554403508842d03c1c80740002c601040d950252400d1045185c852084010070081040b0b410110800180601c850703a500e83d08428486a42d840d41403950340c0740c00751101c03a0310980051882c10303211300992001c1d070540a60a00e50b400e240e910140518200811506d05d07070000c0c000300420809603031064000420401d070703008a81e001401d60f01c407840c2019001d200200d8541d510021202030000051440c45000c90a043c00d40d83d0340c041502083c0c640d02c0d080341c007981c64465000c41d03420b10716142c0603100d0000c48690040d50310803100c3d2102c10144440348403d9003410b03420000d03100803400c1840070a000d4041c0302c0c00414036061030a034030006081c1d1742e032000080040c28810b2100048039100c9050304941c01000890707074a00c0302503556045200d11021204001c9001500041198101025102c05103540042e03801c0440c9410750301c8281c80403140c00a0400324200414032080e080f260a52140300d405142d00560b244606c2205134195000300b030a042207500118030501 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 177450629 1250 177449379 177449413
    0x912050618070317130504090302030c0d03230414031908070906090605091203031303030501141c03170709032105030601200a141b060d02070201020109020d05 70
    0x6801c40c0c07410000d105142ca075461360140d080052421100b05100024150511842c03040024040c1c64010010421003810341b80180d620f07885505c040b28140102e5110404041c06845a15400c43c60360320100381e50400309014410031344001b0021101100250011340101d081003025002c0010500d044040300709a90714040c00300c20000b03160b0720070482545014019244d2003c00c2c0d10844015040c65a29008201d0004000e4504500f20350002c0c880403007001952044051100a00c03406900c0411060340c031505030b01e44100119a90ba80c00801101440c0c0006050305602c4401c58001d1821070f149482900454810b442c0c2900d0080008580c1c00c5c040c030501040600c9562000c10440d085401030024200203441d03400f0003014241808a8000649000e1411100300140510900162402107046180807440e10800350f52039201403146241c4448420030400207408080e8000b0103817030030500881c203148065807003c00100c0c115500d51b405c94005890754916a03070205c0c411001342c8034680440a41703030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 177451879 1250 177450629 177450661
    0x80d0e100501121424061c0615120c060503130606060e01030f0203160e030a081606140106050301030b041a090c030c100504050d230a030815061909120506 68
    0x10144c1c0d042604081400ca801100300281e0414104040c0000ea98150001e40c050402e500803c0e0301150106c111420800d46521110714007240d05041014640c03500d0010301c82c0100250b0040071401905018444680078001840c0c0c002003c4e0003054850849035154026207503c0da0105020900c1e40110151355a094042c0e090001504c10b0110b041d03161035901102c2101c101c82c5a80c0600080c41074507440341c0c03801e100d00d0346e4150700924041d80e11461300c240c1c902d50b0f03188440240c9003d031405c6103c0c40c880c80e0000c24281228039070307a0f55608603400c58031003000c07000d009802151184001a4030131420301c60510028800c1c80f07514040c00030600300c0f209044c202a808021540b048070320602c10072880e038000e8155401d540080d0b03119a13644030640341010504140b00114403100c109414400e07000c405c0059031074a01d074469036540c2c1c9507072503542000780003074189103001d80d1201c02484940a40b50107201c00d1102020a8075044140d41d83d03d0b64898a081c0e41880f00341e8154000030100042468050020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 177453129 1250 177451879 177451913
    0x9320a0605010509061e0d020c0601031a09030f13050a0b1305030d09030b0c0d0e070f0f0f0302040f0605060d0213080319110a0507240c080d0e10050112 67
    0x10500d0311100c40001041c2d8403c0e80e034100140001d0b803a6a01d6102c06140c140c0301c00c0c1318119808c540d01c411080c4c41ca60303200401d210860340c40004041b07401c2c08a400c2ca91490007004110011810030481c10001c803000d40101da331a02050b01d07200b8000982d0b6a4035441040102040b608641d9215442c0e01b0340c0303c40080a4101ca8000c1d4015040c0e0b03885070b5070003801c12080f240c03c10045800c1e0703240d60308451420300c02c403001c42c004682000800f640140001c10460200c0e14004100815150b0301ca0040780000c9542c031400150942140d401c201500741900144a0500c00540014a80b9214000109290030101c81e8010043d03010541c00601c080d00e229180140420700011418800080d05c4c807260b800c20f64042c182081410342442e40f41c10006c00005243e60340c860213640a003a100c0d00d20021034104424901e158184105511032101e0088541071400f40c0c000016501c0c0050051240c1c000c0d000810001200e03100d10107004d045000c2c02d110346c2d8080d0041500401c045009401d000841000034581 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 177454379 1250 177453129 177453137
    0x51920120c06091906170a050f0103030f050d060f05030c04020c03030402060f0d020705010c030c03181221020909010e07080a051503010203040f021009060203030109320a060501 78
    0x8518018000524070840302400c6a6040d0b4039105032010503a03403020510b94450400c0c8401010400d690070440c0712803403016541294100355100740c90341d019220140d0340c11002c019000d0060021900c550390165900c08107041507454007400c482c4080443d689640b0001680c0302c1e800041c819440c040c07190034480c1304111025418544144d400e291240700c05800240b0031500000c01c20081c1004009843d454910b9600841d141e44203424945d003c3c04190100303100003440c0a4811031000d019208210514001c82c54110446e80280d96001c03044140301011000d0014400621680d1421039665001100690f80c0260b15101007600388028040181c00242240383e2820400c10003961103100c16074450046000400c030b50302d84403180c1610070320012006415500000400090114290000940314400d60f00e0a810000421088074040018014a03005030010801001990016040071035a10000c07042a6002d40700042800c5001c81c10304498901524000e080001c000098403444005020a081c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 177455629 1250 177454379 177454399
    0x80c04020711040b0a030506010e060415030f030305071806050706060602031e1804022d0f0901030e07050d03020f010606081012051005090a11030a020306010e04051920 74
    0x520048502d400c0080b050140340c1d9425038010a6a0300c40c8201c0c01190054203461142d41c4458a18800d010101c0d01c440c0918246402c078101c5240c10300c0340368100c9401071540007020400341d404501400026200b10100000d034101c8d40500c1a400440c5001018540c0b81e040d42c8080f0307031410f801551015402903040d034000f405500d2030083c03124600741d10010b100342d040d07a46210081218400c0c0245001c000e4000e40302180b40c0f1410051076080c18426216445a00c2a000c0103240e9aa1203104900041907002c0c0e0501c0f240c00154042c0d0442c81800c2c1620341a215a03640714408501c104200c0303407050b401030f40060784e60764a10304281708402c0070b0715280c903004085180000c40991058003038401c0074070000c094815a400d005051001001d030f400c0b1844d0900c43c0d03043c502003080d9140806841a24900f20451540c00117280016194161a0b4040e002d4041603117021500020054010001c2c0e806000310402030035064018101c1c0404248110050b6804403043e4486000c220f00c10901e00d401503008007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 177456879 1250 177455629 177455633
    0x80f1e03041113020c07060f0e0901060f140702041103060118080c0105071a07050a120501140d2604170a020d080903030f040306090210080f04032a0309080c040207 72
    0x2480e060b844410603036a4414000544031000e00034402d201302e150150041c520b0104140364811050407040006a680c19484044081004010002803048002248408100740481400744602a4043e480d582c400380c140f0b10f00c0e4020806550045000c080481d03000010402c066800c00c1c2c1d50f10070300303080010754202c43e0305107031800d81d4400e0744281d00c40c14400085a228200302c1c02c180c007010444c1400c0054140c40c1045c3e040544550007004071200403e10b01c14081004c002c0714441c840c101c81101c0800c04400c0f85440a114000f000800d0903102c110303024240300b041140d9240303100c1a048039501c1c19580c80d442c0180c0312024150402c1d010905030800c1906202503654200c2c950002500290b4241d0358880c01c40000307295100e9201103001000010070000b041c4a220b42c4050503203802940d000d0080483c0140450f02041d04848444401501760040b07404603101b00c00000090000064101c86080c0d513684540345c00d01141002c5001420184c1c09000b0460b0603c0300b90644003041d6425820400303da = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 177458129 1250 177456879 177456893
    0xf180803040b04080702100e010221031609080304030f02090a182003070b041a04050a1502010b090a0203060310020f0a0e030a0b090607020705010507020108011809080f1e0304 77
    0x54405450104080049024440744c4401c0318440b9500900100d0705101440003e080703203208400840c09409100440c10030030a0f0403220309036800344c0201c82da1440c1d40c4d48a81c0d0200790a886600002c0014055000c1220380d0104020030241d80249040d0710803545a1040003221000205411507241c10850705070b00e14140701341000c0e4181d0b4007004040c0655075041005101d030f06c071144520703850301c03600c1000901c03408100c004100340d510b4040c6107800c05540d40c2c01c0020342e00c21440750311f810200e4003404008920b44c0c5614120f140d40184008582c1481820003d01052019181404c0056000041c00b03020310381000310848003c98443d0075401c2010705800c0000902441c840101801605ca00aa0456509000b420381c410f60140000d0b04504020241965620048600c0d4025200d0300300081020360240b4262503a03198140c1d6000001da080c404002c2c0c3c0c1401003031344844c6e9035817502120800170396060701501c0c040c4e655045030b5031070384190520000d1400c413680d9425404041041804046508 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 177459379 1250 177458129 177458131
    0x5031027112505010b0306011509120b0705070305040f090617011e09060b13020c1204050901030314130e060a090501030b0406020307140c0c2701090c021f0f180803 72
    0x410005840b4402420558058101400740c1540f50181c10000304d0a915021191103c40c6900d84c0e0300034800b07840c1c105a02509035405000b4021030310b141c0c0081d11551294008107070703061103131410a052a0395625004000880c4c1d070015240280c46d00c80c00d0203a40060000381c05045903010080c04003101420b0082c1d1304000202c0c0341d5a200c1d4542c10600244140303604620380305103000d4446401106407408201c0250007480c0f1003545030107280002504038994400b61021303510300804908981e4a959020340d0010300c44016025104010b01c4072001da1045804510014268640d080f2454501307a010001000d030507804c80a03156250100500104128601e041d0380698000801079494440000c01c0c0c6002c4850142c020600100040303c2c00c40320004103072940c0202c015581030701540d1005800c41190000080880c501c80b52900c0104507541003034020841d4000f0b1401034031407405043d4650f1018009211044080d00d84800c420150011544956541c2424481c46980d0360302960b84c442c882c07480 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 177460629 1250 177459379 177459427
    0xf02010510090b0612040803100605030106050a050304140303040b01090b060c0a11010e06040b0d05061e04090c0504020a02010203010e07180e10120302010504020306070806100503102711 82
    0x29446002d0070f034a468003000c540070503040700c480c100103181c42e2034280ca090f03104442d10000c1410302003000401a0041059a050743d4070303034444504140e00c43e801201d0a400082c0195081c160f030701c289500888003840118000da0040014003074660400c1c030b0490a850103900f20f14000d6004003c5009642404240d00462580c00b009a0740c00110f0507004840000348589890743c0558005400a0880340d440c0c010304600d60300500500c003590754003007046015910510220b644030080140d00c0110f140c0b44d44169030091044400e00002916075010030220781004c074a000c0540c0d0b000005002d602c5801100d02e038010390526180300070303009108050a1090b040c0c4688017500c05100d0218290286808881c4082c2009001100c5402c0e800d0800030302030b020035070b130503402800f6032004156003600c1600d039140714440250a0600009800c401141c444c0d000421903041214051004220200c1100025002c02e00c261107001131b07864000301c00e0f030442e041002c0014880d0420003050202d10b6416410050061b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 177461879 1250 177460629 177460631
    0x2070e0106050d1112070f12200304060f0509010204030c12032106210b15031f0f0507020c10030204060e0904110306010e1008030c1b0a1211010f0201051009 69
    0x8840d00d114807140703000300d4041a01161140080007269688003800c10400381d619a112641c009924600e801200d0382541407202d03008003142c40100d40340309d2500641d0042c5c0310f481c2c00a20200454009400c8400c00e9440c2403059400040800030b00401105a002a207a40031a0020740200750741c01509440044918408507000314240a010741c4c0d4591140c401486111810f000c010005110b0041010000c8012140c0800b4038011130b440101d01c1c40300020500d0058002d044070b0001d201c081c1c1455004200b60198a903d81102d40d400c01c0840c010280501b040b40c000742540b02d880000c0207a0000b001003860101481484108040f50340562180840c1409980145d4203071110b042c402660484281c610740c0503c1030b07100000e6507203403036a801c0e8480c070380c180c6141004545507501d907a2213100e040b403c40181c3e0b00003c0700d85541140c4684540300828000d0080071003d03950004121181c174030020654145c62140c1510440b541c000c00c40c01907405061008200600d4041900380c4410464042d2184031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 177463129 1250 177461879 177461891
    0x9070f08060402011107030b07030c09060e0d03110a02060c01060e011d01030219080a140c010507020112020d0b0a0303020606030d0509010f08040203030c1b031b0603010b03060604170d02070e0106050d 88
    0x40c18090043c48047c7d5086070403400c4c1c618010f034000d4054505001c192002410640d00050110b100340c1d03115a04510042545e40c81422549080301d4030a01c1103200f0311540200c03110500140c2e0f0b024010041c4064007000807469030718002046c0c007030394016030020000c3c0c0711441e00121941040100c49054070340c1191f060060001ca01c0d144103011649820443c4070f8410350b03d648051113003101407007a00946810845d03006114110044a041c02280d000902080740064940310060217034000d040e050794100700025484200d4000203032507c5480e40190056080710041c40101e04040c44041002165418094544400400001c0905480c5000c49040000403c0814115681802100d41c1c000d0f228084a042042c00e00c609a1303101c28403240e06210307118048510406203a44520450000c0006009904603843c050003c000366100801035030748074008000200c0c10000748501c0000c2501c502004160b81003e54034003901d0f0003220b420615120041000420149520004070795620109200c0400c134 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 177464379 1250 177463129 177463157
    0x8030901110a170907050303070605060f0a060c110409080904021e0a020717010606022d03181309020a0b0c07050913050d03050f2701050f09070f0806040201 69
    0x42140050855080000198907900242c2c480d0344149050101000f055071611079407400c6980b00981d100381909500240641004150b03240d008903440b6030b0190844040e05100c900045140826400c01c03400b164400305090188401052413081c1030030281e6003040808100d4841c800e05000700c4102d40d03c83c41c0c0009210407000301c00301101148140c81c0240980315000084040d490b24414082ca413000600110305542d90707441406070a04503451b03078010b4882003440b02111903100144c640f644500546480740c0c04454141000100011032a1036a0b4200c1358081c841000703828103040a001c00344606005442003d80d030b420726104225106071030860b5840e580c24400c14200300f403940c841d592100d1008204424003400e0115494003d10540a44800680d000c00603801c940c0c06603100c0400151000003e24420359003903d50404103070003e01e076450746680b12030181c00d4850458400446402c12020712044900410070b100103084240c40d654655405c20064030360300c01004102030304024a603170f17590403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 177465629 1250 177464379 177464381
    0x40b0d1d010219020303040b0109110c120307260c0306130f0509062a09010c150c020c03070501050d090c050603071d09010308031306020d0213090c020a0f08030901 72
    0x100800d00c5189408400c0a0500035040941c01c0c80312204010308042c44107201000712172140d68000c2c510080c917401c01004c04014912180600140c000c1005185020b070780c1008980d00203082080318503924589610300400c501e1440c0c800c0038101c0c107001080302e0700a5a40d65610303400140500c081c2e840307a40f000000307001c1e100b00400700b0b202070345031022003075580180fa0005071142107c14120350b02901d464801c0b0020070102c1040e00141d1260b045001008038000f8000c0c90201c80515041c041c0700c10341e803650350340144c22081403a4190740d00d299101c0c00d00d40521103103601d89403c030080d00c0841d18042c0040c04901c1494130031002c103560b070a01a03080003444504c00c070103480003414061b01da00d00b01001074031001032190051928000404503817032603d440300116050b43c0c2d10841d0b140c1907840b03541d002c0c0f017140040d000880301e5507000d2000109110325031001d40129000701d42000c0103145070130034000440b1840f044920864000081400104da02a03180b502100d0b485a600c0380e5941c4c0b41c0c06458 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 177466879 1250 177465629 177465641
    0x102032209150801060e060d0803070201110a0e01020c040510120203010e0a050d09051e01050c01060509071206141c03020c0306191a09190b0307030c08060f0408040b0d 74
    0x1c40032500c2c190340c200310401c04814200580e02510000c104c201d0302c408038220482c40403210030740e120303152580b17000005102030051500b019403400003240c1c1003070031b046580c441c0d0403824001d40014515030b200c00300345d81d0401c000c00750800240d5041100741440c04c3c4070340c010f400500031346440352030301d403041c0003151001d61004820b0210300003580c01a00c4540b418a0b01e4000500b00200050040303000801c851030070680801c0c000703074105110210302144100549a40d0090221498203540c4e810b00000e681d103845040e18842c9400350f0b2201c0a03030a22038121001c40e10142c10502259224400c1009141c42d140307103021001d580c140c03901d440c40c082032808920389081d0f2400e0a8040c000c280502454145480d82d03070300d04032841c0303400303020803403460309042c001040b0711072015401890b41b03002c20031010303221044056900b00807101140200c1c0020100f4074115081c5c1c8101c8138090080310070045000f081c817031603800284001d4200102d0400380ca400059002e80d00850800110008a40078400d4240c2d00103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 177468129 1250 177466879 177466889
    0x909050a080d020a200a2a080609100204030f0f02060409020d021b0f0d0809120301080606010e030609030904051008100c030b030705011d03030c120307021b01020322 73
    0x642c1e500d420202800c0c000e500840f206201048441c5404881c014944405031440f85080c00282040c1c03c250300d4007000d40070349003100992800440182800804c0b001e84403070190401d03000511940c05c040030f0f103601d05000001c40081c646c0c814441440041c3c25969040c3c80550000a0a0b14490311800010341c81e00c00ca0303101d45101d42c40010491411074007a0040c0c000741c01c07015884407200d040c0c01021900e404456000544540210076444103241c0902c160035086040c40e400c5801ca640c1d44900d5140c2030341f080c1c0001e5607a90240d001c000317042d030f0300141d02641d459041d00640b1103410308401003996405030001441c07149450b140081c030b80381780011026004020901c00c48071454444190103004006000341c3c500002e00700400c02c0701c40c0c2000906001240c0c41079444645903820f0348000302114504250040d8903000c10880060780d5042086818201410300d03000554a05005201910740313607094240c2d00f1241c0d0f1140c0c0948140e030700072060319500303640d003c2e403209020072454004503241c107203404ca = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 177469379 1250 177468129 177468143
    0xf06030539190f05010909090b070807050d0609020909090102070f140c0406030f02010f02010b06070609020406030c032a03020906010807110d0c03090503120a260406050a0c030908040909050a 84
    0x40040c100c5481c10602013111420b0700c925000d15254007166054803905540070300103040050110381418461400254054450b1800600300407070000c1e9401034600300d034004401c9035004103120b4014600302c0c00c059008084d14008620300031955039011840e904d1901c0c00f070800c0340040c0101c0308440b414400140f03864801002041000e4036458444500c0302842c01c04c0c0e001070714480310410810300500c00c00e5083c003001030055090201d955580c8000c1c1c00d202038107d8006841d448000001020ba0015102841c03150380340420074803140e400748208021080e407000c83c43c2e02010b41040135842d00440036030007507000e10701410180d8036050183c400700030114101106100e03c80366501da050384040400b050600c40d41e5000c00817552402010364460500f142d5100100c003c00064803001d00420380002102002c0c1d460582605030700e00c41160070b050440341a22900d441d1400c0001d07079840b23441410300c800400d040030490460a500c5100480c02140500c6a1880d5a00c080106010f810000c0320b02c82903105031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 177470629 1250 177469379 177469429
    0x18070506070c08120c060a270807140d0f020319030504110d030e01020f010b0603130c15120501120c03141f0b0102060c0705210d0f06030539 62
    0x11152409030b0080403020749031b0203400041080740b1898020800c00704080d200d500403900c070200d00f4505407080c60000719a40b07042040713850006401c042500c00317500800c00103020b0081c1003841c094144102d0310b83d14070841d0000c11010010341120400320760242c9103490f00007074941e100d14000f116407940385a1240c1c40b0010300c040c01c0c2015489541038514400a074281c902c0280c000c8101800d986000e1004c9910a000740300141c07052031113028170040070380503136034042807503558a0300e4184403901c002d035090000c2c0c1038003400000e04401e07008103030062219500030401880b007600c81c0724000703501d800020004032401c1100c1d9174000c0200504562010598020030710110848442d01c0205107400001d80580034240009000a886d007080d92941500000605001d04441d400c212000041094580721042d082c84a4050040390b44254242c26240e00c000140b09030031800d0007031501c1403a00460890244c0341d10a220b8920512000d0103000000304a240c070320340c0c10107000821441e06540881d5400912178 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 177471879 1250 177470629 177470653
    0x9030c1e0f060f150607020607060504111504050603040602120114040c091511120417060f040b130219060f0e1009060302070606120c090b01020c0603070818060a020d0518070506070c08 81
    0x40c1c2f050380241d214907420342c2c0800220341404620030f02c0d5800450310010510040103e03051240c0150781c4680f081100501e0155040d50a184800003a0803520301c041d1030200d6614103080c40d105151600c02503081106940d4548075071218044ea01c1ca00040401c4402042c004680c40100481031040c00e0640503580c44507182c01200c2c912014080d100d640e039100c1c10b000310f48104481d411840c06590451000c22036030707490102509035643c0c0403108036000450081a44150748140b001400640125941d071210400b844400030314000004001c184500e031000d00300f00e1082d81104682003150174500b000758844c4540c0c00c100000740388540c09a107051840f200814200001f1441c2002035806072001008040d8410340120303a2107000a00f0150041801c201040c0400d0007181d0f142c1d0303c589031800ca0021125000c10f501c0c1488010f4030b44103443d03500425401d41d013074401e010341503010440c10110611031f03078454541c540d10010761154600885000a0440038003c82d03a500f180139000000840e00a56051 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 177473129 1250 177471879 177471881
    0x3050a06030c151814031207030827010c03050702060907061b05010e190302070605030c040e0603100e01020a0f0e1003200a0903021017070809030c1e0f060f15060702060706 76
    0x7680046c0300f4001c08005440300d1085409841c0101d406903203911242c1d46840c02c0441901d04c036440204031240300300c01d02d40003800900414002030380076500410241083d9801900d00500076044c00c109030070904050108940c007900120404d440070009800c1e44185040260052aa0301c0905000b0301a400c2c60750301d88ca008400502900c6e20980c01c980307125542d20700c121807501082d1041d03402101d040208002071003030511b00c5904502d00a00b030307a0780c00b51a100b0b81001c946443d001e800990350042800d08040340c11446441d0100300717504203182e5020034180010751250600d641d10f028103a465000c44064489200d00090304ac0810013202d81c0c903600d9150141250080344402c0788603603070b03000d034084c000d034071a184003203001000151030140341e03c83d11002d403102e160090030b0710054401030044545010b000c02c0300901070504500114201c1007442040b40c10081f4250000e21180d01c00414018298a410609a44400140c4a1800c0c0040e00800228280f0400c0f00c013a51180002c80d00c00180300741 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 177474379 1250 177473129 177473159
    0x4050301090b010e090304120210030204090c080f01050102010606020a14120d0603110d0809040f0b0d0c0302040c02160e0c0f03190e010b010905040f06050306010b070303050a06030c1518 82
    0xb04c48940c01059445000340d980e17911a90040000e213603643c06104c0018107000d800210401e0190502508254035011042c0807100e0302d004000010f032200b400d10140d5048141800c1c00b4000a200a1041500300000a03681e41809400145030780e4500c42c141451100921192901d10040303c0210342d41d284200d40e203400f81019004c1540d8030034070009046002d140c01c4444616a5510803106424420f1a0040100030240d5110074405180c450610710202e45d52516001d41980c442c8414041c81400c50051004031041181048150361119041d1510042d510340c198080b03c0c0389441c19007099444a41001140c0a02e02101424840c0401400700d03c1d80c028101c0404607140c000200003203200c2119680c03c0e1102c3d2100745001c03458940052007542401d030840c1c0d044400b0b820010903490307518404245001e0302640000c61040c004912a401c041d8580101398001e8841c0c40c080c0078260640c0c580c84d0f8001c0492041c102464040c00d0391054103409081851010f1602c1d03038144480d2035442d8842c1072007401c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 177475629 1250 177474379 177474389
    0x1804090b2401180302010807091701061d010605040b07030302040909080c010c17010b0d0e0a051f02040e010e1503010c0e15070503042d0303020a02090c160b070504050301090b01 78
    0x14200207280c815403041142026105542c8042d2810625640040d2041c1078003400c440200241904082110811b00d0001050f0385192800003c405250100c00c284001a4209050002e81d80c01c00402055510600303403819190340d164107980d07401a51605800030b01c40e55001407115030400e1680014000d20710098440c514003000288a400c90842e000c41c0c1c00d0079a10006052401507a005210b14601c08000c0c0c8040520300d0400200f408480802528040b01e985040340c4580c0808507038036079489160000014621040b2066041905103000708032581c805000f80803040c1c584000040d00d04c0244a042446d1041c042d008000350044200300404c0380300243c1c1c5e070314012400c6801000c5070340d0381c90044031510340d007010180d42414101a101082c0c06640c3c0d420450300d0001004040040f9010701107080114401e40041860207000c0c030522002d80001003c5880c034440a101d6440308003108a4442c1040380d0000c0d007880165a200b40035151030255410480d015032038450301d5000c022103c1c54041c1694 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 177476879 1250 177475629 177475681
    0x2040e0108010203040302100e01060b0d0219050c1c030b09090a0201030501080c091b091503060301150b0a0c0206040810060504050a0b0d080c03040b03090c1201111804090b 76
    0x203030700c0e070500a00343e2205560060059010201648254025a210502c8030381d0400c000700b0140d030b039661081c43c41d0708140c1b00803000b2a070000e91080e010040000d8480720040c9070400ca130500301140b42407078880f42865514330034880722085c004440d500c0399106c21040100286602150b04003c1c0b4820ba50780c481950490106e0701c0c000011079a80c00000d90004048130081c03585141e030b40c0f40f40d8860742a40400072082e0180c10280000740070390341c0d074a46019090460345859a241d1404404040c01d4075240513410364861711452050080e1481d220803a44188034504020300c2150a900c0401d00030305c150b9110301d00030700a04c01440345031812900000c0485904803006c4c0040e803201d1644204450507802c03280da0041c0800f40d00780000d081c04000e030003840d00c0e4100352030610343c0e100c08828103507100315500c4c1c2468022180d0f2507598600651143c1a130030f01c240007001705030b01c50144802141700d9201418105420002c0c020b00990319038100c0783c070183d0b0048492440382000503902c01168208110080d9003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 177478129 1250 177476879 177476881
    0xc0d05070327080702280e070906031a040e0a030207140d030807170708190905060a0209280609090209010906110a0c031101030e1507140d09030302040e 67
    0x165110380200904000e12041c120b0310780080000114004114400441c0d262205000080269030307980c1284414031810b0503050000f0042c0c1c01055404030083e00880b40040e51582800100c03648262090152040c1d418002000d4002d0001c16002400b2140d1199025007032540d41c0000480203d2003070484c80c802c0c0c0031911005d440e045d105498030f1001851541151402c02c081e400300b8480c02d0000c2d0041c1c010b081ca2092000040d00310415000c0440d4490041755804040c030420240113440003480b0150b012040003110340c5591a1600c1e00409044031000c15000300e45c2890702da40e8080c01002402c4186d400b0110300084500ca101e00844038801c030008030b00c40e070b203000414180705d00803100039000594072342c4403142c140142500d415031004a00003c5210751143c03a000251203c840c20040e5000311824803865480034001400c0e261304c00c155040c540c01c6807046018840c540e4005a820609078180030b21100203100400509000308440480c4843c140300c001c6090507099802407060302c8034100c440c207103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 177479379 1250 177478129 177478141
    0x1501080106090c0507080a08060105071b03030f021507030b01050405041d0c060c060a020a09080a0c050316030b2706070c0303140408090f1201020d0209030c011e03020a03060b030c0d05 81
    0x500e01130800c011b015103608200c4001d1441c803038040c10b0740c40710050400904280458680d03e405807000240c042071450300007018000c1c550007241810900c2541d10041c05882c1e80c909000c507200a014201d40c0500d606c4850103100342e030089043e540580400341c02000b1030001c4400c00584403d035040700040b90701519044001c28180501103404211074ac000070300711504e850100300002c0d84012100005c1000110000c1110344084c061504000c1c0030384a480b04003400c00003014180507003803402c10183c07401031104000040c4950121070303001031145828100994200f8a02000c1888002040d11500440080200141d00000700c0100540259000c110340c1040403c07454072207100340e601401007070080c40a5152480e110105681d0000040c14026001030395070126426a0005c4004c2d10005401140d83c8009040821030301110b1113091800c1802001041c110344003207620711210381e08041e00001c0480c800d60007504210300803c2e10742c0000c1c0d500d1519004e0000d194000c0c2c565801c0c1c041c00c020124417 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 177480629 1250 177479379 177479387
    0x30b040c0509030d1d1003050403081503070308032707031407180902030a0803010906060e0405010308090112060f030f02010f02070b030606090a05090403030504120203030411010305091501080106090c 88
    0x4024054000c0200514610043e201302c81c1c0200c005043d00005001a80310f5190b205c1e60451b421034545000c00c6034142485d02911190004111002e08459440400015071700021140112600001d20035070f0f039150b9032211088c01c4030305043d42070740300300b4040340701c0c0c0080c000078012040720300419405514a540ea0602c41c2c44000340c1c070903d0b480c40856880c40200844907800560f000b0301c01411101070411560382e400154200b60302417030401c0e0761030000b00704180c1c0005101034002d82c110b034100295810350340c2c2c60006001c1c8824050411400c406980c0414006600800181244220340c0c00403030354078640b007a0795003c1d0b580c0803400070308040d440d0840315000150f6441a6600381c21214210342d42c42091080703039000042d00f90fa012004147c00503680d11031981c1d0718000e07030090390041200d00d46420f04149441b82e071a00182194020401c110104951030b040a540b000d092a0106e00c2d6102c6d4a80d0760301e80281e000103403000e01500c0000041e4030704158012012540c40c41014006146984415a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 177481879 1250 177480629 177480637
    0x809150a021011120f01080c0103020c0312070c06050424020c0628050a0f0e0f07061d120c010201241703040f060201020a08010f270e030a030b040c05 66
    0x10160b44041d10044400c02ca90300000704401c0707040c07006818034030740250825500e401602e109030611070201c018810b01d40700740b00040c4000740a003030940c900010480007942d07921400340b03601d100d0809000400d81161150001c41641a0450024005824142071000c000c826041d40d41c11880e0410030a11070612141c0256000c0d182203101070801944d52009031070480b00032900102c07000d0701400700541c05001038407582d07004400c4940b0001c2c0010030400700d0300441c3c035840c6500b805a40100160a00c002000402d101518624641b28a641700309480341c030701045942480550040a2410740425580001182c41c0c0e01d520903402440624104010310b0203000305050b001100b04060001808800b4007048810f5191380f070107048a01c1c0943d5221001070301c0c005a0407440c0140d4000400032003150740007403030b1805003000d140b07100056450000e1032403080143c01403040c140780307003085890590815a0b01028040c0501415070f0350703134400403500500400e050100107100b240303004c0515100c40d104000307031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 177483129 1250 177481879 177481897
    0x206070810211e032304080714011202120f010504050c07020402030903070c0602031905090d020d020406180b0306010e01120b041103070303030c021507090b07020f0607080915 77
    0x805428048000404450b40303403203002d0394243d1003514881606a800700d544100203001c0c0e500e0092038400c4601561904484005400b041d078814401480302200c0402c506003200d01c401c004020084082005854035810890301c0c0c02c0c00e40c40420001000c07285070620901c02c02240c2c402071881c0ea01d80f010081210790035200044800424811180181455401103030084081c5d07040320b09001c09699450100c1080d5000f11b40141c201089000c000c003d4254802d04169660418030b00389603402007c1135055000c0745000c0e100e0200034100d90290f440c0c95222102600300301c413200491b454000034480190003aa402d69000e4460303400001091881c1e41800c2d4160f030489510881000600d4070343e1aa0204040c0044c0c984c107203d0070103203c1d1941c08204410040d0f200741c03000320302c90700c6212010b03040c204101c00620200fa1054208900158001210030a0f540c045841c0e0f40c49407501c1c0007080c22411403400d0140c0080300060300105024001c2d02600788003204840c2030400f0074000da40c0801d0f40c0520407207 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 177484379 1250 177483129 177483149
    0x50424050f160503030103030e090a09020321070b0f070207050a030213090510020c0c1807020a1211011a040b031609050a0f09061b020d090902180a060206070810 71
    0x145030800c0d50610014207000c46940b02210941056032036040c11540203038412004280d18400308801410030400c40d607842200c1c41c1080247c5006600402c3e01c4410012450240703818507001d248020640800341c030302664105080701070624144002080362a01510406d001d481014000520343c5058201c000540e54007500c000485610000000013410100c1c0e02142c4030f002e803590400c00340030755102900141c0f034442c0c002d1000e083d0900c01e103c407c610300307030b030344a4511844020064455000140000c40591103050311350803048883c1c00700c901c404201f00d4140e03554201408461031035002c52050780d98900440c3c040203890001e60400d6036429603e20760074a4042910010018016198051a405030716503401041c03540809148a007103a8180300c0480e0710680e80c8426100302d25140103280181c107000c3c0000d00380340940090150a11103503110301c2407402d400007072030032002d0100d0320300c982c0009001e4160880b01d6283d10700a03403144000c51f0350b140007822010000720240c000d030759003001710790741c02034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 177485629 1250 177484379 177484387
    0x506120a03121d0d02010204061209021f020c030a0b06030d0e03060a02130302090a0504061a0d0204020d060b0c0a150204060f030911150a02010f0e1c0e0d0305042405 73
    0x194500500f0108400c440480350001200e210a6000c0c0310301001c040f0030345d00040c4d80c0c5003824005000c0b42400c0c02000c0e600b5107021750300c40041e1186801c0341d0794110001300c01c0c594100c2c2030300d0032490445070460301b83d0180100800c52007000f154500392809148200c081d43c9070000c4440086507035000460f190703945079010341e02054445116600a010145c054840402e0030b42d229004205071840544940306001d641d00d08020030300429200e448081e42103280038121031440100001c41820014502901c56540000c0b0214003484c075900803030051a00c848181d8907182034140c01c9071944005107081d44d241c00c240f05c0a02215050303100700c40a0701e400383c564240342e03d1584e80407001440c0882045691400c9210022003540d5039140f851440030329000040e5940d9060071000b800c0d100c41301c4801560754100078001c804181c01080d16080d10105c1c51202e105120b4081086400b880d005003031541190039a640c50090580c070500078803d03140098403c0c3c078143c0d107070035600c08000d20454260b000280c3c144 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 177486879 1250 177485629 177485657
    0x170c030d0e0118080111090f090402060406050c070f0605120709060504030b0c0c070f05030706030b130b03120a0302092806050306010c060e01060f0f03051209010318060506120a03 79
    0x24240791401c0700050480d01d0165150844c003030071100b0600c50701242c5031010400c1031a40c50710040e0707020324000a4030030341c200e810180d01213807450181d40200b009206006c10028861181001303480002c00b030009503003841590755000501140c0c05451400c10492440d000a0041802503003d0000c41e032190341d03410301e030a245444002d03a9450182c42c08168000401c2012100c20080080c0d101522042c403e4140003032801c0304142c9060550742c04242414181180c902e102c1e42d941141e00b445404078100401c0d590036080000c2e050107101c1c0c42041d882d07400410444071711a407580c06000448000d803480e48802d07022405581c00090b600440452600c903d000c10300c04188120003441d00414181007a5610030800c0da10541a664840180c91941c2c0d541c560400601c0442d0404e2002814a60250003015045444043c0c0b280c80d0086540e16091000540841a0744241e10008440d016006030600310219850302001030081074840511403624035846400031070020580c0907020b070b416200c000e0000c09130 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 177488129 1250 177486879 177486887
    0x30103080a080403090302041d0d02010b03060a09030c02060d0603021c0f1202010b0303040e150604050a031209090e0105040b0708060d1707020a330c111306170c030d0e01 75
    0xc104800b0004c1701300d00040117031918003c4612400c40c05040f40300250b035240c505441c0001c00c10100c000c40e07050401c510341580380401c1184e045214100003080c1040d131800e09a13101000424002e4101c88009510341ca00102540060141d80c82120b2070b441034207961803148800a80b130741d00500141904601c0078000f94950102a9062031980008142101c891001900b150042d50042c49480c001904003c0f1304014465210281007007161000c1c180750030900866440c4149010041c0480c0101000f0404580a0043c4d10020309029030b09015400e241660107004e0a0203031402c41e5190003081c00701d68014054143c0340d00c56900900100da000c8429100d41003071414a669030103180703004006010241c0c0b1520003134009006136242d440c00340450b582c420550040b2002d501e894500480c2e1003801e4156004441030040c0d6040440724680020207400600304070100d80009000601d000c10000d1415281c01204450240010a0381d032058403c1c010707d911000300c408a68000b903011400a0015801 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 177489379 1250 177488129 177488131
    0x140607050c0901090209030717030f07150914010b090c190e04020309060601020d0f1202180a09060f05010c080a0c05030705010e070312050a020d030c03021210031403030103080a08 79
    0x4100726800d114900340850844442a0003513400560000740f00d001904040001c400101128000f060456401c4010740c1e40305c3c0201031200c204a44001410403d021030188440c02d40f14480c0800c00c40e40c011440e100c03400004030340c2010550350818111003240d181440c0c00c1ca21684507061005e1808801a0080e0040001d00c07a8110500c009500e400d01680c0321840507601c2421300f0001000c441c2000c3c00003a140c030040150390f20400c0740403840c4001081c0e100518401101c1c1d2403001507111550a0741c00c0300c0358440300c03442c1e58110181c140c000075042195002241103842000856685544a038011207644503030310700150020300204035000081d0b200c2e4030000b1610740510140c03414080507640d2203094801c0020200704550044d80107006001c00000c0d060403242e0181041850041a100013a485084ea9a9000103050b03840c0c0c01c2001c040e00940490700e58140082420301d50303140011010380150300350f0000b60356481070b140349034400c1080041281c1c1a0b0b60040340e414100031109104a407602c130 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 177490629 1250 177489379 177489383
    0x7081f05060904290307080f15040c1203120c030b0d020d08040b030a090201020705100807030c021213210308040609030e04020c0a0210030c1b02060f22080304140607 73
    0x1d40c402142c010300502c05007500c2095004c84003110710407401c03030415140c0080c540184900ba0810004407200d0000060340003000d6003004100c1085a0700c60030410360084007944440746c0b201076040d11a017096400f00d1840c0c1c007030326196001c0044201d0340034118215084119517a4001c1c02d010303900000b501d0220f91995000c0e100c4e20341c1c5841c5c04c0d2181e03130651681d082940d40784001901d48840c0d03021981c044c00940701030441a908803400c0404914010200e03040a0404400e0550b2010450700c0b036403003401a0380040d40e07140c00403a5140c40383c43d202e400030001440303005440341142c919056081e5415800755850f54040e50b5030409901d96403034080003002c25450407800d000c0f6290381030145032500c0c009000344075000307006441480028014400d00c0030409429004161130b000148800542112084d401311118810741c0344820468400314189204071580402104808600301c260104178101451981481d003c502c040d05a840c113103140d0300d016600540740007100a900d8035a403030a1000107001c4c00c80c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 177491879 1250 177490629 177490631
    0x7030c0606051005040303030b180105190e09070305060105030705011707030605100e030105060916030b04090503030a1b0c0510020705190b060a0f12030c0510110307081f05060904 79
    0x140d41d4100180d1804141d150703e00c0800c101140810a040e098803031041250002e9800f14008070744815907098168050117003500c108a445160000321200072000340284c20003260411060600640d010b07a529828070081710b0740d100e10000480c8500300400e5039030485106031a01d04c6500304402e2009104800140780c2020036940d2000051682c0d6501069003042c0040e4807210400d80d1900e0a040c2915801406280203603440d0040c005131010601c09480b05070f02500d0b00081810254001402810344000081c140744004814000305180b1980400c0c4461821100361442c500324502c1a540e070f01c00032002410540198402c40da407110035030001c03c64a40305a003511880b5130304d00080c0c400c0180044094030040a07180030000380341000d00b0000041c1501c071145044113032500c400c6204030010030344001d041040c041050000c11404014120342d091001c10300380f0072640c003107000d941d45da0801c840040c0099950780c040348180003410010105d0042a00485040d02d040506210060703101c46844c50b085 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 177493129 1250 177491879 177491891
    0x503011d06061c21080106031a1002010914031201151b0c08160f0501170105042309030a030b01051632010b0f0102011b110a08030108010207060c1407030c06 69
    0x1d0203140040150030f1424012502c03d80c07a07032130003492843c1c140c006e02c06041c90303c0c000c11220840040948408542260b039000c4840c0e140c80100d014080c10300c8001e000580c54007101c64404000300c013910507403040d00c007118034683c4c0e00d110380c5003071214003401d920108548061040e0104950005080781713901400e0580d040c40d549200891900c050001c80c01c0c24000c42c00c1091100302000c60300640142070910b0402c1516885040803950044180b007021300c542d03612000e91500c0c072650340017214189400403645586180034000507403250700000c02100040d181490104941d07004100740d6980e21a4009c40d0072811740940e0f194026429a8402244034000500a07000b201c603203213514811a144140002c1401c42c00c200c10701a6200c2c1d103078411415641400700f90f00217207480b8924294840c04a150198010b100740c55100d050600c0c104003d010300e1400000440c02d1030301500204505031003007004000400781746c0021503902d40300c0610380340111405c102401c0400e208000d0003883c0303070046000040c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 177494379 1250 177493129 177493133
    0x703140a260f0a020309011103030115050306030c060a0f0305010b070c03030e010e030d020703020102150405120d02040f0608070e0f0603010b0a090e090c03480301060306060503011d06061c 83
    0x5800c00c2c400f074401039100040401855912180066044448000440c1154108ac1e5501900300209155100f08000400082c0d02c82e40c040000e0b400520028104030703565054040010040303034100c40d80e40042410074000044260200b0101d0b280c042d0000c800b40d0400d03046a07400c5030100403591a0703c0c108603803240d1004040da414420440854925001007001c1860b42c030019090815982e001003034007420700e041001003200403032600c60a501010f0881c1e030350390b01d1650550081c040d540140070b0071111900c0c040b0b0441e401c011800d000311110b8580b000c05202002c00c205000168080303064000800740010011800d0305005402508058109030710700d036885680041440004481d40f83d860703801707103e03c444913080500946200401d0a03440104046032003440075280c50401145030544a1121034202903044101040e41c000d080003002440400c2e1340342800390252203940111031181d468405807000a82c186442903c20300040d8000d0300040c0d490604200000c07c103181d884541c3c40e00040b40c180 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 177495629 1250 177494379 177494407
    0x12270902041503150302010e1215010501080603030c0a030509010c0501050415050708130b061f09080705040b0102060406020d11030403110d03090f0b040318080703140a26 75
    0x101601900800689561510b20b500320b005201c266524145454600381d0310a0298600700401030380e4080c205495a6111400444d03804420b5030b1649506000391154220070f9510180c101e41210f1090341e6182d0f15031582000c050b100c0c410601f10010662001c3c0c9a580003030b000781c01400c040001414480712041c3c02c1d46996081d51003ca0301200c281520705131301c2d03003500800d12030b698100740280f80840c2685441048100c10001131903000c0c3c040000040000d070240e071114100e01d1030311181d000094400c01581c0004e441404a0f015246440c040d000011a640c1468070a001c9502e505a0040c0b0480e15a42c40c1c400003940049004808607488010b40604600b800d001180181e10a645480d0f01082c04001a804c103000e808810742058100000c10300404e0302250340ba442c25410020075500b07500d03185416a004805000b1840d845660f5003000541d82070041202c40482c0d004988600d049900300b81c100362500c2d0003103401040f0300c007180c5104030a85020306600303080c00740c40c851182c0b8003000c4060440c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 177496879 1250 177495629 177495707
    0x10e010c0315061403071b02060403060c02060f0c09120a0b01031a0a02070b0f070314090f1b0a1206090b0c0c010e0d050a05090f190f08030712 63
    0x80100c1e8440c15400750744428800c0c90b4000340f401346001c0181c003840d006034403c20b01c806022242004500398400080d00001c0c00c840800b00c0e40100340c6e80d9169a00d2500c40301500e055440c49015001d44000a42ca200034950740522402c01c203510107103080510b90400840a0cc1d041d41c109482c41404d40140000781480100c90285000381d038000d240d031070042c0d02450305020050500c41e0043c0148510400640c81914464000d5070081c2902e9843c0e40b400300440c014a540e41c0354a050054190900c420420042410740789800940709a8500d0b0341c4c06c10a030650320030b4910a487d0081c03c1007504100c0851500720100010348038030404282900a51541c031000c00f000d45012030600d00001314032142e101c3c01d10a100941080602070f14041100000141c0b181c0180c40d080b400b84180010311300c0c416070368800c84807500c0e40002c141d41c891881807020080c0d0078810703000704161020021000b01d014140003080e01e2007540c1c05404042041c1801a049416050700510b043c0c1c002010b06150892a407200048 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 177498129 1250 177496879 177496901
    0x1b030e0301050a240503060114010e0307140f031b0f0a08070603020a1b03090b03130f08070605090a08030a09082b15180203060102150708060a0e0c0a0809010e01 71
    0x4210018222000e20a004c2c001c01610a1410307101030400842d240400c10305c0c112101d4004554000c00c0800c01620344041c2600034540c107008840c0003040c480c08401010300c2c40e0405071064802d640382c0c941490340d5031245d5698048441c0420b01e80410034904024544940d100181803800e40b40e555506c0e040c54400d95030055404a0b401248070b0310600d038080c00c05c121140f021551f00ca41800740e505c014041101602519980100c00400560034010072220003800c2c6600004c4404840424208404940c00040048454504100c041044000006401d075051508480d10b689144c42d485114402400440304c1114043d4050005104d010305005021a041c0d50480000007091111b00112003210b01100a04440c0042c0d00030038050301e00b40d61412103604910420050303881e15801c00507490320710803141c0012004400800c01c02d174942d1000c402e60213040181c44011034261641c8500304404001c070b88030106154244a45d02c0c0c0345201300c01c042d4201d00301070000204c1c1d1801c0c240035803c7d1040c060300c0b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 177499379 1250 177498129 177498131
    0x120c0c0a031110080c0a030f0204151812020a09090302011b050a0201060803040b0706090203070e0c0c0c15120402011419020c030309030a02090c0d090b07030b030d1b030e0301050a 79
    0xd400050a140081544105580ca0204c2e22442c1521428600340100000001055961424102840a15811580540810175a500003240495001000c1d003912405c014000c6200100000d10900c0b0907482c0c842656000300702c981c85900703004102c401030100303220035421503407a01c2c04903600326031085480000c40f005544050f0b40d8912510080d0950300994030040040c0e08c10030081001c510000c00380d401e02e41c1d1008004c02c104015000203171902c40c0300d8000c501c88481060600551164180c002e041c40210103081e600420a00d000300300c9900c10800c800a041c070700401080031280220b01d0019807103072050402c60312014100b21000c0407074210400e5030002043d144100e4030500e404008501284208a0045107050391250100e5101c10302248028040c0700244041400032a4520980304520030205080201000b2403c0030391018406540c1c2c540801e1a000844465040104e9540c0a140b00e54030f80f0300491007102c0500401004002090303040001545443c401540c00f0f001b414022101140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 177500629 1250 177499379 177499403
    0x81906150809070302010e0f04090503031018050c07060e012003100e160804052b0905030a020d081602220b180106050315040924090203120c0c0a03 65
    0x800640012405040803a8a0744002004c100517a809152591400d0b000d45851500041101c00710b00548600303400181a0300010040080071030481404108644582071090140c001404840003124410346011503002410804038001c10110f4108a441c10150000026050201d00080040403408082a40790b0500003050000e00741010081001030401e152440f02141440549010f030419404d60080070701110ba00001c4c1840418089142014803050301801c0322016801043c2c02000c1896a10022030046100485e290030006209a0f100fa40685010185040e81c0c542e103030560006a080d050f4842c504008000503110295003e900e884102c4550401110404407102601d0011440303501504088554281c100c2b450580141120300b50f08040360b490300d90600d01c0580d49e04107015a50400c0c217141444c0f040200c41880030703185081c3c0b101e0200d048060b001050068510742c20020354160b0100840c0c08480c0b02c46002000404508401c0700d00d003020703d030045041c1c80c420341d00560348050201 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 177501879 1250 177500629 177500669
    0x20907170f07050c01091112030f040306090206130605090a063b030304030803041e020105030a0c090b0408100e010606171306051602010b0108040b04030e210309010e040c0c03081906 80
    0x40c3c0c0c01c0c0411541d03000274609101c1010340701c01c00c90080788409400c1a446216803000c0d0b484602c200c402d41010070792100314035a11142c2c040c2c140d5000000480c0600751428002803400c2c402c1c0061100362a40d541b09000e2003c260010000d40210759190301c1d240703101a208100d141c0d504100800095100e12440354491810f802c0c01e0aa81c0c0740b00c46411880104210500b0060b81c0c000116031788200d02c001300069014280e40e04590b0041a60403e001d01c4c03030005804292142c00140c0882003d444641c18010640c0e0781824500340d518900c501c0c1301280d80c001182c9100491421202d030b002c0d02240c05520500b9040d00c82e001510b8040e0b501c1c3c060720300081d0396111026820b0080c0c4131700701c0c1d082c2083c0800341003517502e114683c4001000a020080d00003401441a80c9190201030a04404001909032082d420201522035100c1710030240403c000700300703600aa090500403000300031034030b8948030120607540d201550320320740040581801040c44040d0740501d04c5544550000340c03803c0384085100e00b040e6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 177503129 1250 177501879 177501889
    0x14070207030c0f080606090a060308120411011805010302210a020705060c282705030d0206090a060b061b01021306170a02090d0519020907170f07050c010911 69
    0x90703080180543c4400d501031045400c0015455041001a02c1d01005523449400c080004c02c09600010410301c2c0018844003120780e940780e0702d8041c03802010324081062080005680804101140740c40d25480008100107030741c0030b0350107408100c2d170340f91801110303500d04103201d054244200d030000180c80e800305003201031000c104803865004682c00301041c54100c1101600c1e00080c84e50010a2708220500308103425140b0507410380c0031048580c601d6041c8019404001070b1340b0318481c01050300034403c030644c10b610203200050281c01100c00001624410b8465100d4401a183e103101d0709030400c5041225200303010200b9020442c1031540000181c41d0303200041d800001c5044c941c0000200030700003810406400c80c9940031303504082c4a03840181d41c0c020003408100d03d4590002c1c060154080c408142625060304214428400d03c212000c2e45555200102900c0c03004e11000c0b202240360880300003640c0300c40a00070071901b2010500b000c40c00d01030065812401e48015031401c0360405201c844803801c038205 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 177504379 1250 177503129 177503153
    0xc120f0403300c0908030a030b030f01060e19091208100504050105010e0103090213090b010801050106020111031501140301031407090c02030711060405040507020607020d0201050f010b0a031407020703 88
    0x907204024030308142d22032038a2080101d0844002030340355a4043c46050501a410100c02021803070143c0ea07d50541c60005002481e08000c854080d0103803c2d4104d1000d24184642c1065981114444030a0340351802d51081c0347c15081d40300f12506a45001c0040404e144064102c2241610750364041c0c1850491001098000560300c054003170342c04c10005105507a027003000400c0a40d828a80051105051b000113009840b0600e8422099494080d41c40306114844032594160365600009002d240d0b600c00c0c04170f0032100d00a40442c08141d040c00072402080c1d5a1502d00d0040301d0526100421a0020481c00c8403a0b100b81d20448241080d0b8800c2d0002c0041400504000c20000d1020021003016801c0603480c0e01c04c0d00001064800400040309840d0b0b41d0005072006000d001d0410805480c01d060041d40c0c9800954068025102e11105c005031280705000e0b4a00c2050342c1303421201140d2a0118422054114403c804203064030f80d00e4050070742040040e154454a015801044000c2c50f41c2040106645 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 177505629 1250 177504379 177504407
    0x405120d020f06162303010b09120d050702090406020909130b060a03030f0e01020a0f030206100929030309100305011703030f1b041707030605180a03080c120f0403 72
    0x1030400c02c00403500480210701301d102d590070084443d02000c52400010fa00c8065a40303d03001011001003422401540a06603400382602c080da5030b80032200501343d40305c81ca403c2c20b00c0040d50411101d0014203003200766a4119103d24805401d0148070700c00a1400401118948030141c0b41c0151141440841e5074090303005a02540c0e030001032070075901c000348510000107042c000d1021800349140141d20803c4105041c40d08980c113210070410a02d4029250300082d2a220800c0840c0c2c107001c501c80070907108030303085150342d20b07a141585095901c80c034020802000c1540d80c5400140210b85054507101100c1030160390307640d00000c2a6060041c0c80001c0d8040c0b101d2040c240d4410300c10050082001c4950700c0d00300c06541401404007114061a040c0351265420a801849801c000c5981c44800043e01c0b07400d807485076609002d1661200c00203602c130f0580c060310521039888064803801181c0200c52507038220400c1c0400c24903101880112080281c0c01f0754072100342d44a058100310a150340110408542e039 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 177506879 1250 177505629 177505633
    0x1050a15090c0e091503060c04091104060e090c070605130b0c09060412080912010e0105060105120a050a0204090c0801140301020403020a211401090203010f0b0a14060405120d020f 79
    0x1a05404000f40804180700d1200d0140d10100041440d03038490000030403955030000c080b5680c41c505000301400390307042449090062070034048100084200c4a0548040e078401d60b41d005120001d03501004039a0030041c0045081701e01c104658404581304c0e01400d881f80d103001034a261980840c0ca00303041818030041040d202d6000034003001c0181c2c4d55190454086900e4441c0c001c1c2015907a08020156114002e0304a52050380125802c5405c00306411400109540100030011640c1d60304c01501c00b071041c5c0c0600d0a4550388140010181c080302e40c41305030070070030601c801030900352500e001d441254489109038000c281e000d8010082040314006510352030609800035410545582d021925003602c9020300788504140580000c1f0340323014030310740a1405ea00242424584c03030303142e52140d0007000d40100990195092105450200820703004200ea02a405408080803a20b00300d504400040030074441a80721400300320008240c0c0c2d841d030110060122170009007004210141000c0d02d0158000c0304070841d0307 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 177508129 1250 177506879 177506891
    0x12070f240b121207080325020d020601080a0f0311100f02041806030b04020603070309020d110f09010b04050111030d14011d010b0405060d0b03070b1308030310052101050a1509 77
    0x1480f10006480001d42d101c212180c59417070743d4841d140c851905440140d807c00c8200181204a0340c0015181801e0074950282e4a003a600c558100361500c400c0c0001074424491170090038002445072680c190102940d40c29549000c102c18103210079585141e042d0b950640d0045800d100b1525102a0a01140118a070811401e45155146034104400800107031090302c0200000d100140139401040d4110f90081804029801ca480d0032446010858240e50081103841c5161030a8182015080e05a070b154000882c00e0510706401160310030130180042080e0702042c0450700c0640d04d00e025017004428070204034000d03981031410a41c2d41c1200802840e041c0c041100041120010880403907003940c00980d0069501d15900b00004090300000030419058414040000340908004010300006c030485d80740d02c01c0307859545090640e02d00041c1d8108083d0058600e040289140100e614124426166440c000543e20310142a003161030464185c414640c542541a80c000030f10941c813009804020410854 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 177509379 1250 177508129 177508153
    0x602030408070905040c030c080706080114090604180204051602250e0604020405060a08040318031a130813050a050603071d0609041113050312070f240b12 68
    0x41da41891041c1e0300f186581d180031a0a21506500e440050340c2c001b81c50444441d65402c4c0e5994800c401d01c5000300060131903001241c450444030320009504801088040c058461108001c020211810048147c036055455400140c07214026503120f800c10007850081c06885080180c00c000034034894681106046022503c4c4412011580d0305640369003400701c04554581c000320f0028421508055405480403c23035010869001c84a28800c6109030780c1d025040ba01e55508080100e02800000d02c000c10344500a03803151004040c90f030b480081c40c1c025011800365600c900701e484d400030b610409400842030050005040c503843c020020001558041c4c41c602d0304040040c042d42c003081005000800c414030001550365103006070f5581da10300500400022780c0b0400e0000f070660021025588011011070006040d2030b010a0030303450803071814080e515000c06643c800c01002156081256044555a02c05025402e454203e101c0d608031040f002500345917800810003482c240c000b14414951040c0385442e6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 177510629 1250 177509379 177509383
    0x21030702100513080f030a0b0406050a0b1c02040608150a1d070309051009060e0105011203110f01060b03040b1803041202030304081501030b0c0c0316030309020a0801150602030408 79
    0x6420707610300000003401e803200407040035800b440e14400340c60030b503000c40e000388060741d094025801404494000c200803880a000d00041d20042d02c1801d1b0301001800c070402400411000520a40b1000c07500c1030308000c4406014012a08a40c200b14001900c2e00c040140c550014544444860307802c6551200044c5000b148101c006451003c0079450070041c808950a280241c11000b51180d1050030385d070000c002144107000800074128192501418004003003e240317030601c2010305941c10440e0062000f02c03140c4050f0794101d141001228540714400540d064102d0a114403005000000010340c0e4034101030030450300d09207010b0b065180d0340c0c80e10903841c001c0d8000002240e08840400b00814401d228500009042d40620343c0045401c1c018410342600c4050170001c03850503244110080c100030f459130802c00c0740358014800011056441000340c0d54010070302c0c2c00c5489109219103804500022941c0c007054407404968040d00c1a80e440e41070303d1040c80010aa1003014003420302c020b41c1001c2c42c16010715 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 177511879 1250 177510629 177510643
    0xf020a08072a030809040b1e0904150c030501030b0a022b06080304260f070603051003021804060501061d04151a0a02011109010e0910090e21030702 65
    0x5104150031010b01814144414106a4400c1d00301508400d03036660307040085443d80944442e034070680c685010320700c207890010020841440d031210042e140002d00d4040c010602000341080da4410078100070002d224155000d0200c050899a8011500b945140f90410400101610001180f40148500a0701070301c03140900b04449084e03807120200071041c82c01c00c4000c20540e00300142c240070000b00807505e40120400b10311208284440248000310310b0408684030715500c806441240c1169508018cc248260099604559902c59120791180d90354006100604200e0502e10004072000811062156501c038803170040c080c41c1000d00c0c1c501a5944952114400742851520590365030380ea03103031401c0c0d44402c004040c10700002e0424080ea82c40301e054800d6004044050011340c00c0580c0c4070160560b000c1900c070700d01c01c10b0f16440c6420041d0f00400c114507800400c46110003c0380800010560054020307402c0740c00380c3e4030140148101242e446d0044a0101410b03a148070420018010050750004410f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 177513129 1250 177511879 177511883
    0x702153601030b060d0905010902090c19080601200d0e030607050904020f04030209040311070f050105040323010218040e0a050a0b0a0e030d0c030e0a0c05010518040e010c0f020a0807 80
    0xf43c101c007910b00140081c0103030030700c01040078640141801001415400305600301c2c0202c440f881035a0703a012804003184612030740220b0005100070031811050180c004550401e00c141031444152080c01d044a5006070032100c007107010707805201c403410400c0d0000f4000340d100c1c1069000d030000d40b50841c00600640301d4040c03018062903000819543c80c0250406640145174010140384050505050003402c428400c0381c101d80c1802502000141c501034403a085044070010b0312103604141c80d64541803181701d290b010400398200641c6100c0c2460100784002c1c2000000f440e14120500d0140050000b100c552030a25070701c0c3c0e40582049000b040f000108255400d50000022460703039108407000c0c002c0c101681e500325461001041d911341c1580a40c11500710f13020541c6d03080206042c4680308541d2707540c3ca808060701c00c00d60b180701440103521a00c010803902402c8031072280022009404142111543d410307480c01a555901e0450b5a160307c040c110a0242d220b100070028401c00b911074004e984204500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 177514379 1250 177513129 177513131
    0x20108010b07020103230906070503040209012c01061e02011112040f05010e0d08090105161d1201060608010b0708190905040507080f22060c05070215360103 69
    0x45000c682c440c6d08212859140c4110310606403030300319400041150300756580c005a00582001500c1c1c01d20820603a03204680003041074849910306202c00b4842c1e00d4034044815070740d0864005984018804074054001c002643d1003c942c1069040341440416030b1802140c21039041a001300e4103030a100b41900c00031509900d88810701d40700c2c0d1500011101840c0c0000740705500f0805001150100825141d0015800ea00c62948030350340d9803034242c02c07907404071a2030030b0741c48140103170050040c890f061001d51406000101c02e100304c2144d001929071074260350100d05607034441c001400f00c19030041d0f04500420003404c0c224103081441d50307815454041d43d900c407180203e551344130045007445840484001c20026000b000b01d41815076004000420403242c4d1a1051040404141c0000707070b80d180840c0103400329218841202c1c50b507840d10090704005102e43d080000170722240000da40e804503804030860020f4510341e075462a40315007071900d0340e91041d044000c400c4072003640c0c0306134290103d803031003440c003403078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 177515629 1250 177514379 177514387
    0xf0c08030723010b1302180405190b030705211c0f0309060204030803040b0f0c040515090301060f0f0609060f0c06020307090308031302030705120a020108040f0605101e03020108010b 80
    0xa03243c0c0180100a0215440300e04c0da030814404002650003014841000c021202d10b4501c00c2c01408203451055491201100c480400607102c0051a403021010b004000c4c01e403240141d03031b000010a130200880d20480141313a400f131903102099040084207900b0306807003040e0761080042080030300354907a0039610109140d1601c40384e1041040907070482d0040d5511405150712801c190070b0031a0f484000310f0360417820080401c04500b1aa480314241c50403208010700e01c88a8030f60034000c0d8a83e0341c1044000c80c4c2c066486000c042002840303215140041e00204800c3c2007440d141000081070b40c12a58485c006002403604400307001603004101080043d005000542e0325100e04070100c88010942d8070141000070048144030101040b40040c0858a0084084032200c3e5100d504103e034252400140028550028141d1070044d4040c51075640d009014481100000c5019100d401c150341c02264202c041014016041c401c040c540b10540351300410f101e11171051b541c210fa001030700c1d0345c0040c041da040b00c2401003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 177516879 1250 177515629 177515693
    0x23010302090c0705060a0912020705090117011d010b01120b033c16050f0603220506040b01030b0c070c0e06040609020409140112050c0402090d02040203040f0c080307 73
    0xb9088662583e030101c01c9884914001c01000010f104406040b2980d894413044000700520018040054460007000d61720075918014101080c1e08407905078a0055407144c440e121032450b21015240703400718040012a00b01003010006040040d4408503030741043c9080c150903481e071000200300c403130301985081804a2103404903c000c041c0d40c030360610b804030466441c0c4601071241c2c085030701150f460780d524404641507294000c0101d02e5104040c00d540154091001a0030042c041403c4640040f5144040c115006030340c031174034140202201c081e103105108500400811450180340c40e0b02920b0048101e050a1144d90b800c42c0c1010701b44121000303103000f003010441c00d0743c596001d50010314402a0440d0f0311581c0700700398005400c003000c0304050340d035010000142008500781d10161096222003d4016000c1c3d07101080004d4101c16122a0000320340030b80840161502c0c8010350060703000c1c2401640c20021480c00b440d607041950046c803442c1d08140110000503220442e41340508030440615009007100b2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 177517985 1106 177516879 177516901
    0x602010204050d08090f090a0b18010308030402131b0c050c090c04090903050d02030c0702030f0d1d030a08130911040e010b0901090503060a0f2301030209 68
    0x42801074000a0340303070f0000c15080400401c000c4000003940042491808101c0c0d54100041d40c800410700f081c60082b00d0b800c080c0101d0400e0303460a41c115070300d240e00303804084e000074065680c5110b408104141508141003001c04021642c0c0814800f41c0000d2030464991810b8695000b01000c211032401d00c101c0700c41c4907403441d07032000c3d103440d14160190f0002d0007480c4d005d03801c029091141c0c0401c9001d600056004040303500c501521036215004141c00d001090040302400c7d88041d02c2d40f15030301d81011880b804029445404041c40b420440424180070320f481c0010101100060241c00090010000308166485003034208140d01252880600d80d100b20300594078403e610800410010b154640105030808041c9010300e1300d541c1e103c011902d404402d0354880360700d64881000305060701551080500850600321408406440c812422800c1d413418000030b800380b610700300010080610 = true := by decide +kernel

theorem cover : BRFrame.Cov 177338129 177517985 := by
  have h0 := BRFrame.cov_init 177338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 177338129 ≤ n) (h2 : n < 177517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
