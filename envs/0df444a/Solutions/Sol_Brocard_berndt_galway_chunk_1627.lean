-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1627
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:56:18.829783+00:00
-- url     : https://prove2.me/submissions/74b288fa-bdf4-486d-ad43-b96328060a24

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 292446043 ≤ n < 292625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 292447293 1250 292446043 292446059
    0xe07261f06080411120c122401150806010212031003060204090c0e040e0307020402070c050907050d060614030a090609140a06060e010501170c040503100204060e040506030616110601 80
    0x1030903182540c42d11031303104c0f41803010710b00700700c04a00c2c1107590f2000d00100d81c0401d00b0002440c983d84043d0b02280202c181c1c3c0141c0095241015410b04841100762030f1075410050710310003215200c190f2009206003001484031700d82e00003a90140880040d85400d54903540e0110301c020001c01644014952400440c01013013148807030700002c4001d0555500d0800b0021028200b100340c0d40c1440040c0450b400821041d005810690000c04c042d40c002d0682c180410303941c40108a880c2c2c3c040315107500080000c00d0281d0108018040c80008090500d031105406440d100c01c40b60600c009400b08990a82c0c035140c100030004036411608200d904056486440700f16040708136254001070a00702c4109191000c0483c0d00e400e005201c074145c40060b034500e10b134003050405120717180c1c038043d00b0400160418000050641d804011507911003804810250b00d46190000241c090710b555461103101ea400d11081041d5a00c00241d42a400f503401460301c681c0010000c0192040c2619140c1d04e40da42c000d810000c0343c454 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 292448543 1250 292447293 292447307
    0x405120f03070609110d02100e1804030225050901060f180308090f030111030601030b0a0e1303120e10020306060904020403080912031602010f1214010e07261f06 71
    0x4d8050710002c1c0d0305040130b108005110754440740c000d601c4070400700040c00c2d04d8820b00c0d20800d482c40143c00401a00030036000390900030812a02100140d00c8a1002041c1502c0c10201020104141c0814420b032410034002030300c10401405440100503051441c00302c5203104441c140c1070b00c0c0c071004011000a1716410306046a92101c0c0445000e0a035480e010300c128101480380c000100c20420003c2c0c01e6403514401103014040305120a5800424080041109800910014022644220350003801881c0f49000b401035100c150715208042d01c4c05100c4c1e00307480004207600c004c81c01010001a0303a41d46a900041a500079030980039009403003c0303000f00410400780b00a0082481c100c0c0c1d44204441c00b620f00c41d94034840c681480c01078040342c940010040d4000c0d10000c0f4400030300d092500801108014510480321a10240341c5010a9000100445d0004116541d0410420301d081100412110031300000440f0203206655060001d41c0014020300314500d003104020401d5851100c00e50351600020907032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 292449793 1250 292448543 292448561
    0x120c0c09020d0c090b0703050403080c01020910020a051513060519090f050f0303010f030605041a04050d1805030318040b100f0212120103060b0d02031015080d050405120f030706 78
    0x31500781c3c0d80200b45c45111200b03070781c1c409505030f0307aa91a1a0855480c83c4103a00503544584256409201c6509550380305e1211001040041c2e0042c009074006080c0146041c03858200c2c0760b0540010b01c10710840c41e50b01581f00344126049000402c194441b03041008800d10090007164000c0d2504194100304055201208038441c0928106c40c9a8600310203255120301c000e20418a0b452703034918003000007034071070340100354864010f40400c04c0c51440012042c0120008075400c0702d40d038000346110705801d50007003d030700c2004284940b01650b141c20040800d0303a078840c0141e0f86040103544a40f8008030741e038541003500d503808080c106002c20300040d00301400e401034502210015015500151800c01e800d00c1c280c41000e40040728145d0302da480c40c1c0f0307003030700404140003c150010884601c00001d600c4c10494000210f41101d40011482c0a8002420908099401c00e1000307402072150362410650020a03902542c02c110703514a14200d50084441c41e01001184003031645c040441c40106201075503000304a1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 292451043 1250 292449793 292449797
    0xf01050108241312050c070902030108010c08010e0604090203011808190f0e010f0c2004110309031210030c090c03110901170a0207020901170d020307120c0c09020d0c 73
    0x24600b40031030000340d00c0b080f20120b10b83d0301181003000101c0c01e4042c90300e4001e00c03942809841c10107021281424aa040d420450721180c000004100400c801d1040381108403084c81c00d9140c95062130080300c0302c0c450140405120320303101c40c000c50030365800b9400100242c80c2801004001d165a03d40300840380c00020020b5050a001048007440328011010494602034580e1030000030608003006450381d0956511250811001510800014001c0140110000b024441d03205801511000b0081503c0242c1d5400f0500c444c140f0604c207501e0400411b48000c0f501000030040c0c1590b0f00560343d8152811948050000b81c002c41d40010310381e420758840424050599010701c241601506030f114140b0890b14202d0014a4008410030003031b018240460b007004683c5009880d020554000400f204402e0300041000025000b11003a034000070410303656030f01c3d0940040c0d0705003613032034803603007441026501e010040c0704101041d9070412407155400406465000f404540381c0c40765681d6000207100305441000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 292452293 1250 292451043 292451083
    0x90f0308011211101106070c0b0c040e01090b030a0b150f0d02090a05090102091215010e010b04171f0b030d08010b0a0315030803010e040303110f1207020f01050108 72
    0x5082d1465116026016030880d085032110807100d401d000c0c2c0850300440004c20490306140005440001388039031402032405584040e000a1181800e6000d0b145c040c042182c1110200403c2161021030800b243c1160f05880002a4510135540868101554000000d102010000801507502040d01310102c1121003914822070061131602130115107030700100043e50250b86e26001442410513070300b099074450728040002d402c01c0c910002051004203107109100320f035001003c0c0c040704013094040803801819880c803006099413411440392410b100e00c5c0101c5091406861394003046d502c040107404202019580c0407001e6030b4000e2803001c0102040a40544a40940c10903d1490b80c450f040c01c5050750aa205820714000380003a0075402400d071601c2c03000c00d0404c0007000101040030600910b000f800e141071140f1170f624040c500181198050001c2ca802c02e5400d009070b482c1c0d50030302003d480801d021180540b04c07a4031100400d070f15152030007114442c0366007010000f00b20202c0105032071240b5a20000c56031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 292453543 1250 292452293 292452299
    0x4020a1e02010506060d0504030c0c0801020a03140601090b070602040518010e16091205150f0f011d01090908130605090111070e15210a0c24120e01090f030801 70
    0x7403c2e1101600c606a21400501c4840030020b466070150360400c0c404d090480d0b6110840c0e84040030504075900812007070f580854620f006582501421540b1503107903400e503d00b8608400080c01018080c0541c6140f09004101c1c20100440d550407640030f080018441c1daa0039262004200c4004800d00a03500d1a8003240041742540d00800061003078250103440f13040341da13404c0001c4074400c40d11084d401d6a191107102d00c42c02010084180301406480010ba01c6035580c0b0300902c0703408a00c103043c0d014840198080b02d85032400214084102d040d07814441d004200042c050812072618060042c5001214035010fa00084641d08103004042c110401e032209481d8140d200302c11902c440d01c43c810081c003a503c0000141d0703003042070801c3c03140e00b54005220208805a21140c12400c0c01d05a43c9d10445070b1140c0c20410501a81080131401800e2700d00b409107d0f001c40e60170308909840b40e8940d8000340a5201901c909044403500403602061005008100140060030a0000c07051008802d40210340030300e0000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 292454793 1250 292453543 292453547
    0x4050f06090112021e07110117161407240606030b0604031e0f03030c12091110020c060a030203060a140105070b070e0d032001020c07050402071104020a1e 68
    0x29504164050f141c0c12000100102440080d60018081c8502d4540e08034458501c04005030240140f1030040e0f122450490200001400030f42000144a14011907032007000340000c0c0010701c0c804048076500c2d21490001d0b444003000101e0142a900601c01e0314100140c101c5000c9400550000e50310b00141442515660142030303080f506001c8405030002410801030000c203503048041807043c0d0740d50203440106141520b4a07011404c0ca4070046001941f5048001c1c41d240c0c1c0640701182850029004100302c51681d56040e80301800200400c2c000c0000a400f861024024000000d28040c09090b15a5429100c50000d00a500441750f081c8190b5038824042a2002c05488610803404180c56407480c01d602500c1d100b19403100203040004015900c2968541c80d01c441154032191131180e120b1026103000e40c07030351043e00400400c481c28503a01c180502954140c002401004451040d500140e80d1205410b10b48048007400380b40c640c000c0c0c000900d115040358000c080039070320103151500003400520b092007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 292456043 1250 292454793 292454797
    0x82106090907060503040503040b040b030415053c0106050408160608063102120f160509010c06020406090812070506010e0c091305090c1c0602031905040804050f06 72
    0x4690582c07001c030051003014040d02c001c43d00715000e00e044038282580c1d501c0340ca2555100390880c170768100000c41400100807915400c1e50010403909404d0000d071904120320305803110240004000b2603858550a41c0103e250701c8201d6100c0b130010102d40e039668440700b002d0f00c558003c0c4142c0985126004000b5620542943c07903c055880c0c59461f00e050781c441e101003140c4803d20443c0840382c00c46145003148002ca0003606081c600424020150b1074a05246145200347e50051844108150201c108000030203030743c081c0d1070280694180980c8403503d03a40104c540800405000702580d20000b800301d1200d070007501e080c04035003100303003100e482009078882d90345030340140840244030750300c100014001460b41c01d02140e84560a40502410112030f040010038014850a00e0f07500156680148200c2090a0208044004041e16548d040480d00104a03a0751a02c020300505500d0780440440d10ba0308400c5907018010440c40c0e070a02141c101406c0144844d4014800c007441200800c8100d5214140741e02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 292457293 1250 292456043 292456051
    0x70c170d0504061b0801030209070f05040f0e04021309021f0c020909011d030f0406030b04020d0507030c0e0a05030a1401200405090a050c0306040f0b0303040f0f06090b070602070c0308210609 84
    0x100100c55211004180d0b50070941115080500400b440040ec044200d8070b485c0e0010408041d402c0b006081500500400c1b000d10300050301d03c0e5090810900250300e910454620301403000c8100b8541540c5880125031101c11440b000750721000f00d10038020511015007000c0e00002c1d98034408043c240803070515550740e10603010340c0311a220040c0002c010442c0603501489051801510152174226189403400481710202c1e81203003c25611290003079134641c09260b01c0c1d5030070401e031440c00d4107900384000a5503d0120500040c51180741040d0b9555042082d00100060311980c08072000060385400b600d01c81da0041e01529000d009103400140c00c819050084078003918510a41ea441e41e164003081c003001e48040b00c5ea8000040d00c1c0c001000003501d007000140010000c05c8034501070903083c019815880c89290748002e040004400040c031040011104880034554020001a0f0743c01c010310380f2908481080d40007501c3c44201103803510b200c42c100038002186200e0341001042c0d0b0340d201c2d0300b003003101c0744260303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 292458543 1250 292457293 292457299
    0x301150c120c1a0c0a080105010f020c060d020c0106030507060806030607080402010c05070b1803071208042304050a0c030e0a050303180c06030114030f0105070c170d0504061b08010302 81
    0xd861049501581e41e254002d4014025201c001c414410041400c0d40c042d1008040100000340203c040703903200d058140500f50910b0b20340c0905403a040001e40d51801100034620031007001a400100380c1d11581140d00c203ca21038028808031b6524282980c031101d062082d400070642d000006245850301040c4e8903c2000c05440314001d544403500115180d8500302c02c111010311512030f001c03132007600200c00340215032054121f00f100e10424109050030400c2c07541c1311032145020600203000148650040e5416140c0b038101101505e04005120031a4621003440a80c110340741c1814800785240e9900440810303c3d5a0302e0620410300e02d03044981c0d45110052010f0420740042c000b2505100e4078078904005000e0601c100d0301003030800c07030014280798400ea10000b021030070080b9825890600740100d1003480c8442e8004c01040c0f0380110702078034880003030f08000c00461f4544041c0118806034000e40301880b1484400700010701e02440c100008000d54000101d140c00403000405600b03100d0392159041e690b0203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 292459793 1250 292458543 292458563
    0x240513050c280e0301050408040e0907030609080706060e101404060f0f0e090d0f0309080d05180106081216050c12010207060609111209100e030301150c 67
    0x10509480144009011040a400304200c2c10800b00440311198000542d80741c940600c1200407070020b00281d070000358450080c0d0605007000080b50124099800303c0d41c068030300b0310301030761034061040c01e00415400042c00685400344502c02e0003001e1000d8500c0c1c9125500400c412500c0b1111001945011505104c2050383c0f0720040c001c82d0901c0c00181448a0068004039440740c0f15034000c0154442d50b0001c0c09014076520382000031280c50f010058104812030701070500d281030b07814002e184400c1162a10103058480543c0e204101c0850221388104100400420031420044d055548102c80074911102030340c200203001c59251800b2a0003001d45038050805840c2030201c10420440507840d602c190340b01c0c01101140b00381e9845407074104520b054460b00040e42c8801c2445d2000844040d504240786091510211800d0205d00d6011036002540341c5014000c02c2d510900c0c9a494100c3c903001680c000c0d0300348203c8650040d03001000c0c605032400130580840c424052101100c152a005101500c5a018 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 292461043 1250 292459793 292459819
    0xb0903090405060429040209131e090201140f07060c0f0e03010b0d02122b0f09030c12060b040c05070b060f0d0210030b030604030807020d02070b04180209132405 71
    0x102c00286080c0d117002034000340c2806070000015141c40310301c00b81c4518580e10f50981c407410a482d00f040400c80b411021003004580050b8000030b0001d80c0102e075551890340c0005a0718a811540c5040c1d8021070340c0b000042c0102422004c0080025030141c040030081085d98110740203515041c0944100d190000d41b03550700b0f8940d41c1e02003102e03002e1284899946400b80e26103208860b44c0f0800100490031400306039601819045000030040603507411a5030400915103024400203665440703d01c11030f00d0070300c400c00e510317455810034900404e19a4401c40d403081c07800c0d464420558000300a0041c0744d00031800c2c0030306540e40505103c41040c6c2007803081d50008110030a00010726110b0462680c01205160000b0281c2000d00841e180c8801030354203801140081040180300b5604100761000b2090354805015000d00c0d110080c45940140d000e04403903400307850101291646558180c41a00d80014905480424686581c2006007441d85001402000d003d291041c04801c100580e8110780c0b014201030480d42c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 292462293 1250 292461043 292461101
    0x110f030d0209060d060e0615121b0d0507110d0201060506040306110f04030309050901051008060f0111150a0b010c050709020306011704060605040509011512030c0b09030904050604 79
    0x111264603258002c00c10722003210750340380621480c4050b001d1980306e810340f42130100401c482c0031004043c075690024100001021451f0180011760482d4018154191a1440d1000721f0010b015081003a01c4292070b2100300041e80f40d0103032101000d419100d0a5500642c008c400c2242a81c0e1180142a040002040200001013042c0d10000741c800c41c840c516401c00c180c2d0f200c9030805911a82c03040d000511121018000c510349040c1e0a401401c088607000342401e40c1c0b40019045150041c01a03100311100031114240340d010b201086076002401c415281058252a003111030040103454540a113846c00003c0c22195004900441c00700d81c00400808409142045440180d07000508150400c01c0064242e4405255411014003e80c8900004070781d190418040c0412608018107554650f270600f040045406880307400b10080e1145114400c06914550405441c00e00030302000801080049003001040ea8011000d41101c4004540522068944004010948489010507103214541d0300032400500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 292463543 1250 292462293 292462297
    0x603040206040f081c0504060c030e04020f07140f06060a0306020705012a0f080105011709070e07020d0f0203042304110d061a040b0f03090f011506110f030d02 70
    0x600c0280310615194488502c5002d010440e8080718541d03102a41e10b002e141c0c5040704030f0404101c0351a105040c249000302c010a0946900d2010f000d20060141c00b408545440e01120070056078900b69a61f1400d0f05e240404c0345000034511040c00340a1031004011284010507024081d4100500c80c810171811515050025800344800325010b6688807100e1580d040501030401c44185a40926004d0708a20710000d0026801880b07103000b00070400006000b10b27a080f040f501440c2d1900c0ca00b2034100e40e99080020f103005440e401518100011000b004540b590000340c658040b980755950f04c0507009070342c03c241d9690062f8000c2c0b650008000341d201d15070404969821080410003840840c00000d204000e420390360080101c59440b40e1600070910000071000d2000c8800448d000e1700c03510b02880c10040c400c040c0a03100c0c1568140c0b000001082c0d0324075041080340315480304980200031034081ea004250601200d07110715404078600c10701c115081d040100300f6810340c04000024500e02120310403100025 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 292464793 1250 292463543 292463551
    0x10b03090f06010b07020310051b160203060423010c02101a0a18060b07050d0302070305040f0b1903090221100e060a0e0a150507090504090c03110402070b060603 71
    0x141c070841c040312441c4141040990b000b0000700d20455500e800c2c2e80141800d124030010031415050910090046088040d420200c1000061500e2b81c3c450710914212034a5500041c0701961510410082c88280842a52550b0104101d0301c800c02c0013040803c807036030030b84510540704400343c3c00c001111903011040340c00c007c03003e400404900f54006180f1000425015040e04030140c03c140306541c094441c0039501c15007002e808503054507400c080041c6d58240e510010401800101900030400604250094040d200500140212002217036128080d1200320780004100c83c0031072031b860580000250191260903100ea4016028042402000c401d6405001c451030040b181403080e010381c83c0020529105c0c550540281030090203507030038540300242c10746042c101e06036016000005d900d0f00184007107030402911180100041050340e11141d081c1c58100071544025001814040b2aa003000040d00c0f040080e2441a0000b00b0301d003030f0320740a000482c09240341c010140c1100300041a1079283c000051684 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 292466043 1250 292464793 292464811
    0x1030908040503031207020601050102160308071e110f060703081b0d0c030204090501060f0207030b06060f0c01090201171504090206070609050f0c042307031416080c070803010b03 79
    0x501582c45002c00e1859114030b60309910340c08144107020200394184012801048248028044a04100c184400c0d1440d1444020105c41c80010b1103020486e800040f150702030710013003034180c1c10ec4103410609008402c1c0c070440c0c0c1c49150048106901854400c0039241e034030b601591041c100340d40c3c0c00444410902c480c2c501c10006074007130105d442c50800c41c0c0500928401140e8000d6200d51600303500304143c850681100f400c0c8550503082c10502e40d400514035003102d401120b100480c1d110f440102e1114483c040d4241004d110003c0c81c41501d40054000002543c401c0c0d88400988881060b980d4100b802681d2142c00b594548880700010702e0107402036a1007500041195180c448180e030345504544403800211107a400c9502e56124040060050f0b402d03881e07041d90140314401c5000079010780000200c1d80340d011001c036400070403a060b02c030742e02150f040f10240300b1900c483e04100c0356103801d40c89021658800200c40c80b00155140d40104140ea0949a001003901c2c190790074a00311105d0f0b0b8000904000c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 292467293 1250 292466043 292466047
    0x1050c131502100f06080f010506030a02100e06131706190c211506080915090c210706050c030909041407030b070f0c0b010308031b040b090a0807031101030908 70
    0x1c1c112828454280311040781e100002d42c1741e1500340c01c1c0382402c00d031407401c0e801c0340d24120805c02e040d1004038034440815412038520780d80420041091790542e4404582580080b000310f002c1034541850752900043d99030a201d01110b140c1c0c0c1082d410b03607a804c11104a140034a9a4101d1700711041c0c0c68118822211007414404950f1200b81c3c02c2c2c20890220b5a061841551070700342050a03a41c07a142d9070f01c050402c034500980c0d20724190705815500c0c00c2c02104035034840401000141c0f42c04d014814082c6010303005189180e104c20601001c2c200e200307204e0481066000f5848000780c010b002c0c02c00c42d1425880c100c0030b03504011010007040201500140b0540f0040d21054103004400c10500080001d184100c9603001ca03401e00702e02c010b18000500314508144035490102c06d021904880c03920b41140d80c4a801283e49075101e078a423074900542c607125006280400700d0041000c101c001e014107040300c41a604100100e40d02c03c44190b40702040c0c4005401c4585101d00100554429006020918040c0341024 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 292468543 1250 292467293 292467313
    0x309011103041511040308070b280f050702030a3c0f0207090203010509061012061205210f07020f09010b070b0912250611040801050c131502 62
    0x446981c41210200d032440c0800300c2c4521883c1e410b1041d04580080d81c85140d06103030841c2e0b1806803e101d201c00190a40f0305040c000303006041040307009040c03110003003d07280d0050313034008141c006010002941c41c0c01c50b0501002130399492001059403286078103540c0300010503100354146440c0012500f1015042c0000c2140c410003100210b4407400c01081c20703035442d811010750840c000c1c1230400e641c00602d041070041004020700c3e030703403403000c030740c002d041160843d1301584104419130700c101527040060f0950b40ac00c100007890442c0500f12500880c01801990301c090103404004001040b680456202c0d103809004004000398504040d00d0074030f202529a080304140d010004003154400d1344980d11004002646008200140d00c401e5002103a010041104601c00a0411801d00445401101104150744061451000110500041a0800010080c0702e107404444240c60f4001c0c001c441c0b0940c00c04010800c2622008100c9420b1a490070b9411740a500b0480b800c6910304929080b00c085102e9040d003c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 292469793 1250 292468543 292468571
    0xa020904050d08010b030103020d03120f1107050c18012c0c040611010c0806010c022d1c020109060f030f0e010e15150405040206070611031e041205030901 68
    0x2030096005900034a000001280c0c0200494016002003110034020b0004000584440d10491485a410b0074145074141e199804a0010405124a0001d440c284002c0705c002880490081116038000d800781c400040e01c81041c445034031404d00284a5940132507004001d403118450b21140308200d0803903089040c0c204911800040e9101f03941e40800030400103020800590441403003000b10304981d000b40b00c584d2465001810340c403001005141801a408800c130300315074418042504d005044a5a040d403401c0301c068540a2919040b111400707500145542002c82c90400c0350180c549905a4a00401c01d00b403000480d040b11000840c40c00741a01c9681071060f20f0003074002c0340140b403011400003441100c080103180c5480c102c00e908a250f0000003007842074514042040c007034100e209aa0205d9a500c0d18804141c45108213007000d0085440d01603100b0380d1a0500d8003e40c0102e401440301400c00314a8443c0340440e50381510018242c401e00d440b409142c0d40103a024640c0881082d0000424010041003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 292471043 1250 292469793 292469809
    0x10e01150c12021b0d0507180e1608010b121b15070f0b01050105130b160f030c0209060f0d020d02061e030604110a0c0609061803051e0901021e0a02 65
    0x1da0015811850b8940c00310020700d00104121034088641002a1800303444030f646589190042010868540d0303091023000340960400c15008280e40c08039407010780301082c40d00017550b880c0240c0b00d40c0d50900740c4041d058507041d0880c1444840b60300140003011690301000001644410045810241c01c205244201b200c1101500c0e1040c0034040c048405101850404003e80c1c0581002e410320005001c0282e010340f01741d0008096441042e50142d5031030701500415a83d040001e0000c0006078040569000c1551103086900c0152081e06c410000c0c2d1118004c00c54214880140c490f0440851151240540342240d095841c10307001810891402d0144c50800041ca2024125a404290700205021030f50506200c1c4040c010a0204070900b042c0c10440700510230403c00c2c802500d034540758030184003403140580c002c00c40b18040c0e040103107940b8034614019100350819442c0054a581c150f8100071b414000d4001c4964016050340580500340d00406120700400b1140d00300300203446010103e00c016229200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 292472293 1250 292471043 292471073
    0x7020312070c2004051f0915080a14072112090e0703020913050919170409050a0e06010f170a05060f040b160203070b090102090d11040c0206010e01150c 67
    0xf44034440600003080c401681c20203072102c4c100d241000c15902010042101c5042980e500309030205807a4001c0700000c17200e80543d0400d00c624001e102e1620200401902d5600c112009441030f40c800c0d5980c0c400c0c0c800310f035100d0501009170b00351034155880003c0ca402580c41c84404282071280310386443e0340400c007072000c0c00c45107840426030010304204d59107405c40080560a0b0203050070301440c40d03c0400251501d0031004413002039011b0840302e500308900307017640350101c03c40041490744850792075400c81c0141070140c0c0e0f190308582c0740144902021001286690503030304400c001d01441c914200401000c00154a0140c0706401540c01d000005581404424040d81c0032034101886030070b0034100008030360000381002c03504400078400b118400d40c0100681d0201900324401032140c0d580c001e01c1c140a40709540d00990300607500b1100208004c1c9000e040000d00d9000d940c01c2007540355044e03041e0303501e442c280104041c10113220010000b20500304228141082c642c035200742090050394411020f044043c1c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 292473543 1250 292472293 292472333
    0x1b0601230103020d15050301140907090203040201110d0207050a080307031d0301091b050f12060109020a05040801140403030c021902130b06030a02090f060921070f0305150601030507020312070c 85
    0x305e000c114034a824010081010800b116001d41410090101c1c2c0d070b5022248101c000d09030300480042e007035a020341003032000303049941c0a6036090003460400075101c41d0f55001d910312a00040001140e01322001047d9028990716440c5e030441c00340389a0002d10034103000030b4001d52640d00c4e00c681a0000d80c422007003444031040180e040c16401c1c2440c0c2004407503506070030224003d501c1149403c4d11000f00060080c11030320804c000507510f1031400c6086a03944540d0700103030310035800c009640c84180c524074032440c42103000c5d0b13404200c0900b9034042240c41c2e40c07810031390754400c030180d032544005403400c1d8481d100315000ca10400100c000108000c21000c0c0c004648000c2e101ea40070410201c1070134188100106040304940d0a442c1002c01c42c00544c00c40164030780d4402012234803681e184011000c020003006802811010290582d907032030301568844842440030000d00c115408983c065000340102c601816113a000b035402c04c4134071002c00480d4800101800c08018041d0104004103110800240e00610300d6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 292474793 1250 292473543 292473581
    0x809030d0e1f020415020d05071e171905160b0a02040801240801021c09020409060e160e0907060c110d0609051504150b130507051b0601230103020d 65
    0x1184510011300781c43c5c82d1410664001e4410070700b070158040d0440d8a140c0d07010f4002c005038000c400d258503040210050042a421061011101510f03606000d09680b00c03007810240300e1000401d800303c6482c0680e5000310b090300151101c40c00024a04286994040540340b40141056910b0348a07501b546c080407031514010218822a80084c0c0e41800f00c1c9000c1d10814000358a40360013014103a511403040c9140200e0075564800b032408640c2d40740c201b2024035420607000d10036071983d2140e1588401d0f100ba03c02d19030b04400000094a800641e0b041c5200340003100240c41440d10b0140d0a40d947d2409400803110b03010640140396207a9659055442114018840054101c2c2540b03441031130300c45101000800400280c08000018007003134181500c40c010340b01c1c080b07201982ea42c085042410b1020b02e44d104a8203040c100100182c0c0003018103071801100d01d000380500d4030340c0e250640b0343d4001e00811050400d03c5162004200742e21600e0f00c3e1403a410300d40107207400c40034070445040b10711784014007510b4082 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 292476043 1250 292474793 292474799
    0x626121201030b091605121e06100905010806070e0105070605070e0a06110727090f0c0608042015030906090d0e060405090903040f080a0302010c0809030d0e1f0204 72
    0x24202007544001164000c1c1166880d05203c1101c0010b2403050307910940b410b20106941c01f40601c920124551103801d8410150840071070540c9450b011240003a18401e40c10780000d1221403402a90304a802c1b940180001d07407a262812038440190f241003c0c14824104142000910b4910400d8884c109960312110005075000400c894a0101d91002e01000050040e400e005440451158100d50501403011400c0c1e0024814507681c1a613aa80c0c0702080d4030704128201030001c110b2028601a101300204c1c038038503032507072001d5580c84000d5402502c441481120003542c42e80a15240707108a200074880c8011010300c0c0e1a00d00d081e80226804030791900884103100c00d112040042c1d840c05982d90078200302d4010030001098840c01244a5244554800e2004c0740300f442040c42102d0203030200e045110051901e849000d03590b4001031108030b005620749505480b099105d00042ca000e020070001852600c0c5106550001a19a203100281d450160009544650103c11001d65508840c41809a100d5117 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 292477293 1250 292476043 292476053
    0x503061006081006020d12110c010510050621270a03110106051005071511070507080a0f020609030f010f09030e060c0a0311010908040f05090604062612120103 70
    0x1d0054245100110b076580f00344141c03500400c01180e00d6507189044540450003a100c0c1d00a01000b001c45d98400d0740005913007840c4030044d080284568000d0f018244d1041d070391814002d0314418a100068a4803828000f424003001407000c2c1600140c05900144039141e00c8906000f54403582540007400d035114500c010200b540220840c02d09465910081002d9031070900820050034004080e4800c214001401a04010f4100d0481400f46a00c4c40100201040b1001d9400a9032040030181c44500c02d440000900e017800050159000c0d50044051a20072242e5080c840e0603041801c4155140c016401e008001d42002d12945594043c0c41001103000045070602a1003d4400002d0500400081000c00489903001491901e6181e243c0751807510324070a20f81c8a401440310300c600070f11010001070f001400c00328244001068036002c8420804503140d801c2000304444080c07042800100c1c281010f40d203240d8140c10680c1d003ca21041c00d0b514401c00361a0000150381c0168101074486500f00010300a002d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 292478543 1250 292477293 292477307
    0x310060c0c090212340e06040801180201090b040b0405060c0109060c080109060b0403020306040b0601020f1005041a2e031506090608031303060b0109120b060405090d050d0b01090503061006 83
    0x440c8513100d00700c00b50920001744d041a64004407800a02150840d5003c03161200c80443c0c0041c004c101c0208102000c645940c9104016800103900144c00d500001c1005400f41c81180c045601c0210310918151400b028881d043d00640b407507004d1380d581c408401d00814058000c00c11080d24036034800710b1315810b107030301c0e001100c00a41061501010901c024001601c00080c03582c1c000b60414070002181d07884500403032800d03007144900886c5020320070303e16429070700316001342f40a2841440c00194195021028003250f00c1c1c2105d01c00400b00349400c441511002001714800f02c0641c2145090b41ea907200e1b11396550512415010050b4943d6a550030030004040740f1a620250040001a501c2c103000d0442e000c006000030f000c06440c0317070f50f40d01c200e0070b0300ea0149a801e002010a4201c60221041c90b041030f224076a81215500d004e1403d0800007405400d011882d280890b045031281d600305038886808600070710550000c1414003c0c0c00c84089a5507604004051081c000200512400707424900010808 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 292479793 1250 292478543 292478581
    0x200c220528060602030319110c0a021c030203070b07110d020304080c06030c04140604030f060507140915030a06240314040c050f0409081803070b0310060c0c090212 72
    0x151910600380300c075076400300451f90045104401032404d00203500c0c00100903d608803008a0306c00c80000e8400d4218804110040a580205d80070064a01c0c090164421001307507070700c0100180c1081100c0000500803080c0b071600a091460801c160441000b00289020780f103540307810140e440450108140e010401591107180030644603e030450506c45034060b481c0c015405035800c8941041c100a07070701d45448041e0fa000b540c01258412616405052071402814142c2d9521300061001c031058034410102822a04c01c040040c180b1b1110f4a4070900480140c2c04c0078042c01c02c059245c86001541c0d81030f0990283d10058a40c0003e00070400316070006c0c0440e80d2030241440344125103410400800c125910400c1115802d840000d094002d0300000b07801002e407040700a0030141c011070711098011302d407203000794100c074180c00301d406030303500d95154003d18042250f140500d00504801407101034402d8070512000c611031a104044552201180740580e080007000e000429030650401ca21001c41e44c11160384 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 292481043 1250 292479793 292479871
    0x240906090b0102062205101a0409080d0f0612030f0816091424041a0310030221100c03060506120601050a0c020d06090201200c2205 58
    0x442020740001c1c0d10303200000e00700e031034071918002107212414070b8182951820b540841031316040144101110300070002451b0000380d4944542d11031686003070500c10300f20601e40210b51a402c200d00c115810000d8a2181c0e68001c44603158040000c004040c0315501c1d200a10a0712003405030042d6280c01000488000d141420000c000c42c090080980c03c44806405c1d292084a10098000404049005512040c05003240742132281e000483c100c5600014005482c0e04418802041820000b145501e01003504c00382c081d40d40c04881000141703083d00a40c40503c141c0d0f6200ba542e01000780f8907070309100c84082c500f001c064480b0342609440c2c1d4140308500140200702c580d2424100b445100c1d140016005005074107120740040d8081d4038070701505400c40c22540c02483c4c0d00e440c0d11280750100280c02c375001c6c12404610340e141078194016860b0b45501100c88044010041e002c03040003040b03107128540902c090502d4680304401c070704051a02540b841500c24114440d6404170b031004d1380c03202e001350a1420030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 292482293 1250 292481043 292481051
    0x308090414071e0302040b0a0906020601060201021812071a0d06170d030b0325030c050a08031c0209040e0105090606010815010c02060904230f100905090124090609 72
    0x100c0e140c2000a4080320300c0022800d03500043c1d0003000764020300c5203402000d0030000c08a58015226400705058098405a03801d9031844c2c1d82e40c00040e420303030047c900e426494038a03d000f82101c50500703108020b641001001214107080c0d80303541203136106c00b12090000d900c0900041c07140741480c960281000900000410a16124410740c0c40e13074440d2990b0380550304054460329203c2c1150350400c401e0714140c0681e40c0501c14510003603546030300c0c010644000c81e0f0141c41a0390028103403400441c91422503000c10041c40c90081002c038000240c003002c80541c15000d40c280b01c10680741e21a44a40d003050701004000040781c1c20918419850980020545410018007108001c0c40f510071051881d041c90b400c2c2003180481100c0d100281c05805690f078401e130800e14101c0d01488402c0c400070260301e43c1c52007120340d10b05522040180904050b0403680000960740901041050446680c0202e502c800b03550000543c10320015078450f0000c80302680c801039684a1042440072008034803d5400410050178104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 292483543 1250 292482293 292482301
    0x160c090b0901030314093007080d09150504030b040f1a071211040b0c07230a060507020f030607020d02010e010506100507020a0b0d050709060806032509060308090414 73
    0x4084080c807080001903004003241400c815100e03102103802811401f40107109071358085e041118407500001e185151841415000104030201141c54013190703000d981d450720b20504104101c0014030060070614100202004000b012a51120006c0d01441c400d0726124203e0f051401c11403850548440e403408481040c20621682640007001418844000e9001080c504084096880180a035500c0150303919000601080f223047c2c080780400a03500148542a8106581c40c90186502000d0100f82e41000b900c003400e1000c2401000508002840101a04406104440440e04048081d648540582d0003800c1c01900a40c080c0610451400b0340c0f4020002c0780740000c001200210102110f50521600040380c00a54031208000000341200008081d0340341d421642c1800100421101078000451a14010480074441c0d06040d0040d04010020701d140c22001c0d01000044045080f200e010110500d030000e078440150207548001e6001c0c0807416200d0002009110076a06070380302c0c0744400000e4400300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 292484793 1250 292483543 292483547
    0x20312070201141b07020603100f1e03060203130807030309061d0307060b010323060a170616110d05030604061a180607140a02010306060f02030a0507020303160c090b09010303 77
    0x302c0e13400400b40c2e102e000b81070200c1034000c2e81c5116034200a50480400403c0000b13800c005181602100c003004074010020760388442916032126010030402040c241d80d4030800104115030061900444c6c4480c200150000303555039155540d1002030110042903d0318920300c00c0c455984034188520196210030040c2d4009404c01e5034503032081100050032030740c0d5800342c10490b07403107940200c000401a8401c0a007070201a441c10486010880706903205010800e8082204604110340c41d0040c138242c0020022500c50482400035103040803d180108a00003114801849003001043ca00700c1494132500e41d00c0c20a40184415646243c21582e0b100600750040e06116100a040f5118010f105501c01013022803040050160301c54100c1c09428902c0442609203003076404160583c04c54400d881c10005650b4410056a1104a110030309c0c01580040c040c180c4020b000c2d000a213080ba20045c162890200207901d02041240070100a81c0c3c04805010305108e41c0f540c0e803041c0002c1407022a00045150324583e00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 292486043 1250 292484793 292484831
    0x10606020c0402070c0515030114040903050a08070e030102030c09090105030d08070c0602040906030605010501030b040e070519081615080907060e0301021204060b03070512060c1c050403020312070201 88
    0x141c280119030000c1c120081c8440d600910016010080008519540075942060107400070f01802911030514841c1c569245000e100307409a8035415121241404540034040d500324400030000380900800300103810442e40c00f031009511840c2030240461716005000d003407010703014050304264020342c8400c01d035040064200000d6035000103980740554004640b4681312029010356404628654180b400c04000c10160f50041c5058a00a03682000f000c0c190104100544180305082051600550030501c154101004407000f60000129054821943c40c07082e9440c0c0f0f500400c2000c551140a2800d0007804851310701540c8880903464940c5040c10903800007901c920380342c442c1409011000d05c000c0d040751070a4056400d42100c00708110084c0c03070242003034000b4103054415680f203801024400324813031521245000c11180d01500600c4596281003007021182e01898201e4034000d0800c2041c03403c5a901d0148278401d5100b03a000c0c43d29106078041c0f078000110040d0204081d039040504180c92600f80c084 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 292487293 1250 292486043 292486063
    0xc110a061d07060f0f03090b010911070218090705060f09010807120507020d0e0a08070b03090c030a24020a0e1011150f1302060f030603011d010c080901060602 70
    0x30000507a03690300018109144807110760380305070303001c1d00d200040c845400021400d0212510745420b8040c002e41c2100300e00b10368000c0c01c0144090780070f40041c00490311a03800780090040b00903495141c0009500004c6401c9007a003844021001c58030100510300c2c6003802100c0040c50300f03603202c1c0d04018607198201d001d80200300d0541d04110b100000100182d10a50001030b0014403081c0401c590701f000d41c0300940310784800c0c1c002c002082800300c0310f0010381880c00f2032408440c1c0c1c40f00503014003814070740f0700d10003940098203608141c030070201504150303501841740d4030682c0c3c851005010400328070104001c4d41c1c036078806c10a100070f1052100c01c240642000c0c068408980489900ca582c1c20480002c2e0740c80081c591180d480c91282c02c01c54042c0c1c0505000080c000d2608080295580c0e42760303444004140c424800c000c2d007000c0148142c0c440c1000301d101a40e0402001400852500c3d0350344d01c0e115290020b09100b170303520380d100c00701710f01c00c940c2010300142c003e514580240081030030329101954a40001c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 292488543 1250 292487293 292487303
    0x3040b0a0e030405040c050a090f080a2003070e0a05060f0a05060c0f0d1808030306030d0507080405060f1206030a11010c03270602121602090a0f09080309010c110a 72
    0xa88100050725092040310058a4020400c01052403840c400400f9504049000030200342842d2000c036190303090b0501c80b0f00b01e4440304001d10a0702c416694891210801880e0a42c0071800042c0200c60340c4d40510404000d441010a188150301e00480e0090640300064540b41c010b06202c945004c894440d9500103054840913140e041d616140c044200b860808814001c00040c028002d121039080c0d800511920b010041041d02d250440d04d445800d522484241c60303065140d4007a00800c1032641c011006044c0c518001c03c640c0d41450341e1800461a2035200000300f99529000281074400c600c903013020b09400003c00e50042c40001c145560b014000c00c1c01c108114148121318803540101841820010340d403140700703442288003911103050310211101c40d02070740c40940900d40c100443c600c500802e483c1030307401007111100b0300305440d000e000040c01c0281421307018548410300a500d8001a00803400601d200380c0326140c0c1d074500700039018210b4805050390020448108036000000000160b61003100e03404c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 292489793 1250 292488543 292488551
    0x130506031c1101060306051906081c091502060a060801050f0a050a091b0302180702030313020d0803100e13030e040c0c0203070803030412140703030902060f0d09020f010503040b0a 79
    0x55000d594201c031090000b405507080c0036000c41003080d0354101034050805d00850110b0507a0101d250000c0d0b0710f05004100041e40804082c0345000071740030b0901021605810030400b2107807500680d46101c00000c0165015030f01c800b013030122003801c41c03245000070800c250007088182400107000545640c050400c10305642c84a01140d0000b00c694008910658011017849190304500c105110001c040c0c4001d81c031508c0303029150448e8046c460b40d420710a94003036028519641d66180d403180390000c0548181d030010140c01c031071800284140021350042c000c54141e8803485140c40c2142c0200c3c60018180404910041181c0c40080c2d045440c040e41080300b03c6003c10054607400081702c8040c612480a50f1500c00c1d030b9000103007110302000960007240684001e600007240103405860140141000144003c03080210358080303031007030348180300300b620040c501450107840003007a40164000c03060030040c80750b076200e0100840c17500b1340b4014213441e000e0030301c0c41c1035282c01c0e12010307294000108658400b03030322 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 292491043 1250 292489793 292489843
    0x6061204021306050a032307030b070f121109040b010504050d02010e1c031107050d0308010504020c0f0304061d190e070203040302061b0d0c4d13050603 67
    0x2d40c110601a003006440034901590f00c0c24110040d41d10040c3c4c41312401140c0c160800401d0f80802c45c10181c0350003000c0489903407510700007125a00004c1010001b08250004c00d030302602100e01604d1055050103040748e440300d26100c2040210340c2c0c0502c501d4148a02004100025201c00500140d529024207106540000d010007040c01d0800507030340707400b180c0760342c2c22140e0415403c40f0350884604885000c55214544480512403540d01060014000c01e02a0004001c2c6140680007007010716507045c160340300711101030112403658105170441804504110f0a480c440148200ca1881c03408046400c0c08a2501501c5400a80c8405000b1804a40860f500103080346008004540c0295400b402d00c6540d2111504d1262500555006c9071107503000d2499003548203841341d000e04815a401c0b2046d9000350381455200c039461961546000280f41221a201c2c10304007100d010072500b0001050040c1c903000e0002c0c1000b0004402c0c0070100119440d0000f800a01e840000e040301680103045616445500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 292492293 1250 292491043 292491079
    0x603010903080a0902010c0602030a0c080c0304020f301e03040b1e040e0a05010e060d02090a0b0307030c150206090a03051603120203090f07080c03101a1011060606120402 75
    0xc0e6854088c090354000070902c030711040a5400181e980c1143c3d82e80109a40740c5181044ca40e201c1551b000c1c4d4001103105c0c42c40824a018126039403034000d1031a2000e082402a03c56840b00307583c400024070903030007105d0740c0300341c107410109400780b0403225502070343c0b9207030030f01d0105021401039001100c5000140488020440c05030300403100640079644843d09680781c9411010050300302406000c860007280e8000c00d8060510382e04281c3da0b540c0c020203d41444c0d540851a02c000c20074031043d42d92601c03803554000042844a41c0c018003400c0b0240c001c80c0d410a805030040d2510300090081d48556000100010202e0ba0020135201d03402c1c0d2000e8000410217560030211030311041001d40d42000c0f0320000c180700c6010000150300c200488100140c901260792110107648500d0b8048040382c040e008525030078034290303ca6120301d8010f06e4440900e00607400100c0410720038281c0e480030401185501c0300d407812001c000c1245a500c1001102c00a140c080c420407503110441c80508001d00a03946001c0c1c1081350a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 292493543 1250 292492293 292492307
    0x1006121101110709050105011704020d03120f0e2802130c050418020702040609150909050106080a0506100503060432010e0120030405030922060f0303080603010903080a090201 77
    0xb5030401160b11150712100c18130004c003030a10134980807500002c5014030400a201030300d4441c94004107200c030103420343d0b28149d4040050907040100d00c1d95803810780d150000c0038884c07640507851041c02040350300b14010a10461104070012107510085c2000035a005a80741041d042042000403804500c584507040141c580f0f001c0d40d080322a960a0305000e61518603480d42c09801d01e54003c5805000c4d03955108103060803503203840090042c0c500300000601c6504103541021003c01c1c0b194000103501da94585405091059101d02210607401a0040c050501e180d01c0c0048003402007200074110714141540d40c40010301c4c540381480410019400050b905042d640600d055030143c801c000d102034807094030501d000380105600010044070340d451390041e052100003601d00c110b92000040d4a4240c840c0d0810210304001012011040340c17000081d810020715001e028020203021a5515140707045280c060b000c105d0051000e030090b031400712020040307940458915046400b46500166170b910b5400100c07410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 292494793 1250 292493543 292493567
    0xa030617061305010e0a032601050a060f0c0f0804051503070c0b1f0602031e0f18130608071503090327090603140d02070608150f0409030c02031006121101 68
    0x150055284040038107401580780300701805d802d002c0c0c8500c0148c0031075007442c24a0a009040d00b14213544001c1c0300080c02828403040b5400181001c2070000199601c20420300b10a9500b1101000081420410b90504040f041760f0005642240d80c218540754400070300d0499080d0002e4030401800300810100d43c032120074400600e0500101c80c1a00d0748910010b5525801510150030031614004960f400c18003108c143e500c04010204103038a4440d0950459410b0700ba5083d0455011020640980c01010240304080c01000710602500b5044d1802c5290a0f552002c01c0509061600b41115100040d900001000301110070820300074910f0314280c11002e164440344c11019a5502c0c040c07021051044444100540c5060b02c01111810051254100d807182c00b00e00c103002c0411880c1001c01c3c04003c412040546221700940040504c000b0207000a003a51900c507007e0340800c0b940d403080000d60909210b002c0c1031410317422040c001185003440f8540c0986e0a0003001d01821092400300303103140e10402e801011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 292496043 1250 292494793 292494821
    0xf0c0303070201050411010201140f070e030610090b0409080702040f06050d061508070b030c220e0a060b0c07170c042a03110a0e040b04050702030a03061706130501 72
    0x120725110102900900c8207070707401e0744c0790480c20120740c2c21903205004e00000c01007002998010b03500c1d0000821400300300981440c041c083c04140c00102610200100c6104285442030301412034505030203501200c5c1031303400060155040511503004100c1c1001191007042d4181c0340014940b000b80742d02c400030000b80c1c104507031146c15070351076106101e041e4000540840341070300e030b600d603290740c1c0c00d00d10356108041d114400c0c00c2c0000b4030018002c501180c0242038402010220010084501d0300303054210703901608aa18140c00e010b0a000f004000380c401c2802a0168007005854002003840e00c1d607950b1050b100b50101c3d40d044000702c00340030006000280b103464019005004102028140001503403180c20010f00b007a4123030305400d881511030f0203100850324003450924603100501000b01c920700710103040c032a005a03d070307040051030303403214881c651040003154080c6864428030300c0001c090381c0881d842a165070003c02050004858003103003841e04025003c12581c5400070a01c0c00700c0c0035000508040b14 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 292497293 1250 292496043 292496047
    0x350c09070f1206141302031501080901090f0605190b0a053109030212093f0d0f05130902031b0a020a03110105091506010c1b0302040b011b080f0c03 65
    0x3e10480501c0348500c16580c01c444500110070845c003c202280000c940c403200003180e030032526000754051040c103500501140300100c2c84600d1074890100e140001c10003114616614000c000d62600c40c00388a040012446a09100300d82c00d5174001283d07148107008481c451849112600800004c1e00400c1210307400354045065071803100300d624801040c140a003540135000325405a8110b100c0c4038200d85541788010180d48400b52812051a0020140342a498800107a205803140030410458051462405c00f00104087c0d0b800d03020081140072251403c0b014494107000c03040750707212030a602030203840e00d19034010f85a82d20315028440ad1034058a180401001c0024000c001e03a070702044d0000d1250003500c51100d05e04607804094200c07442110201440d0f0405038510a0504844103615004241490302e0000ba0506450301030030384001100004e100002502d08004604250085280c02042401c000c10400841004071015074840c0c200144040400210610450344410036190080000c00440b9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 292498543 1250 292497293 292497299
    0x2010f050907030606051009090c110f07090e0706090b030919050c030c011b020d11030106140306060301050708070309020616082a0307060b040204350c09070f1206 72
    0x540b281842d000035104a428484040340a0800490b040902240369030341d0f0441906d4801500c00406a1760070700030030401c1501000c92601c50412840340c1c042014070152049520700020001240c04201d10004a500b21030810440c0c683c01403002021030724800f40c1c4d650359654172408a82000c1e810282503807000c00282114050007000503900704400d030b0580c219028104840c0041d10800d0f5082403140c06001800a40c3c030050901c044408480d903c0380d00c1980103024101c2c006800d544041d0016180e0700f070001a0303048140707420080903400c00d1054008114900749528010080b0500401500600d9113400c03103c0c1c11511244111a082200c801106c42c48220f80e00d010b0881d680080c403010301200140a400b4440e40700340d8400700f1200d04910045141c0b05407652500068000c410b8102c0e40140c0c24080040c0e00b980d00039092004018290816954142c2c0710200d0366088450ba036618019070001c100041c15454020200b5040112802d1800c0000b0040030100c42c58590740071010f0846060100c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 292499793 1250 292498543 292498561
    0x30b0d020603100e010501030603080a110c0405090a0303061a041512020d0605040e070807060e1c03021f0209030a03050313140d020c0303070503040303030203060a0b0403240510030303050702010f05 87
    0xc0d000f0b41360b08425049040c0d90b510011415291036000241c01e4400030440c0102d054001c0902100d08800d95040d0307215a9100c2e0005000c44004542192a41d00720303986070420564180325410140c440d00c00a0155501d80c800d60000501850044802d131aa44007005040b1901941c26410060200c17030381550744400c0c1040d2540034004500c9800e000b9410725281c140c1107100030072010142c03072a00c0000c00c0590324140c0115030402e034501c043c41d0402c0c0f2480810040c003070f40ca04410000e03070080c0c00909507000742000805001000ea03807014151031040c40b85524030750300800d10520160301450b0040c0c40e40c85090580e90701100c0403100404110a03880f030454182c0c408601050500341c00e400303a4944950220901d074480c0b048070001880340d0001c100034000a4040e902440c0c112501038010303007a9a446018200f02c5601c160403d940c2200e86a18100009468001140c1c4070103140f5003e0085080402027900c1d1000070b40002400d05480f44006101e0134401d6101c3c00c1c000f04010410b00040c01e0900074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 292501043 1250 292499793 292499821
    0x61c05030a09080a150f0204080a06090203060f040b040602180405040b01210c05061605120d050604090f06110c01150312050f1c1104030305090301050108190201030b0d020603 77
    0x5000301082104000080c3c15101050251051790402c29141c8841e540380700d01001002e42652090481d542803002043d400410040e6603000d91042500050120003401054074054008141da40e020400008000c0090070b03c0c5e108036081644000056112003508038510201840000002c0e081450035041006014100c41d03441d040310224503003001e4040103214940841501044058003d1441c184100841c2c2000d80061456842800040344010300a0f0b07101800c00007020081c100c000c401045440302254240715a07a0010710031a420844001c0e07030f43e504000400b40040240c0450307038880406419001c00d4089800b952000c000800c0343c80c01500c1808114200d60200b910030159211030064964081d500f141c2800ea12404624100380d140c0240485849212000c1d041450b19803079108946d00d20030300a000910300c00e403283e03a110003101c0306150840310140c1c040b022a074845408140c0720000050b210107180e4081c41c000c141402040041109a4211038000390088000410030206d1003c40d11 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 292502293 1250 292501043 292501057
    0x40e0c160b151504030b19090804080c03030a0f081b0d02120603030901090b130b130914010b0301050103020f19021c0f02030a030f1b051306090b12061c0503 69
    0x19810442466181400000f00740c480c81d0381141e1030b003000144049400f0950351a8018074079080c0110040d01c541015007600d00702d01089400d28400708013401503a20a015400c5044015801141400210140244848054000c5c0414400d5860200d00d04000495101681c0104000c01c03030359840d602d0681c0802548405221102c2c403004001061ba5482c001c0304554500030140c2d9014042424a00101d6550740000c01601c441040b01d08000341914407400604851241400d200146524040e03040064800c0701044c1c541041d038400050100d41c1949058a0554900f845e005841d444485108242485407040c0b8442400c0c0810a00c04a9540090103241c401c02c40105145180c20784901a0780c8117456041b03c00140c0c106005800c1c0061013580034204006c1c1e400300c08100e440d40002c00628030304014440300c0c001500002c8940312415403050040043c80e46140c181d450902d8084100303454000c1a08503150b014002022808a42d158030080d45250300c1801c00740c0a0705c80b18540b0f0750f501e030311201d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 292503543 1250 292502293 292502311
    0x20a05160818090c1905271002010504050717010914061803030c09010c080403020d050610170c0418150e0c04020a120c09080a05070e1605040e0c160b 66
    0x35a03002c0503081c550546070080300000140ca00b00302030501c0482d00e8042210410040003002c0c8034050a00c00e0384c0703e503c11006c0c50034288490340f142420910122005003030104081da8101010301000880025100d0100c8a0a0000d0040104080c401c180988a1408007814040e04c0c1608101200f80107d059801035020044214129400c801c5450702d90001300e4038101c2400080c414481194061101494054852420b4620f019140e41c0055404050038405444d940d110004102c1c800c0080c3c44590081c3c03a00d210418880e011030250180d980c03084660160049880d1450007020200380c1c000000455400070f6141e200140b40c2c03c208004160440d00c1c01d13482d115815024140342410b1084900082c850341c2c8800462200030000341c0501400c41c1403200b0040c1580d40024401001d00943c0340300c600c680050000b070707450050509003440c03002c0e0021312004803131203642040c2c2e900f20741210211000340503004a55035510341015058050070481061519620000c1020020302000c4588180c5040f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 292504793 1250 292503543 292503577
    0xc0105010f0f0b030c0f0a020102030603060a0b0d030e041d0f01150303050307110c0306070513080105010f060c06110301030614130b0c0d02041502030c071a030a020a051608 76
    0x90481c034411070154070030711815801c011818400c1c0980e800046600a01c0043e6642c50407165005040f030780d900c0f5606400050b540402808940e01e07003400610781004a0300b000344a49880d6400241a013450290024188642d040013102c0b03a40300c0c2e800c04002440d9504042100c2e19114903802d45954003801c0415440d4a800c00042c24114409040700c00c0d039030159030b80303415a6114103061f81c411209006c181c409110305061480140e8040112601c1085580d4400c0d464001840d44010291001d130002111030b4140700042c4071021020400000310380d514600041e9008036070900301c1c010b00c04041c4080803903c0000c0007100340020350300082c1c22040d0107103c850b1140c2d00c47c00c40c04402c05032080300611003890000031804240050029040440c1007007c01850103a4a641d803003042440d040302c0d480560404140c0480002041c0320703200040c0310070003071038000742c0785418a11406d01c0001c020400c031540c04503a101241d0b10400550300d442c0c07521900303c0a8070026042180b6540c01c020f030304080705154 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 292506043 1250 292504793 292504799
    0x709080607080f0604020702090703060611190605190510052e140d09060b03010b0303030c0f07210216061404150e0901090e011125020a120501020c010501 68
    0x20006196104800c60307600d4034659218100100f0740944044c0100d0381c0142c0030f01c02e09015a81c0c10085900490301610009400351030b0041c040d2140c2082c110007681500011030340c9026075101c8408058050b03011400146a65410b43e10701e9044c9400342c40d04000c28a4030040203501c0c40341b2260751055503422624075282c0d50790b820258854583c13480740420140c0310100d040c01654040d02d001040d81300402103160800060003c0002202c2a01c1002d545080e00c81114094030304083c4240c43e02c10106070003661540c5001442e6400e544500b0290007070114000403040c0c28010a1080c82c8460b0720382c00e03a00e286003000d4800c001c2d5174110036894400b024055140004d2200d001e040c0c54100180002c0d03001c0d05003482e25489088150b00e018106d8180300c2110115841581c03611100382c0a0092a8400501d0210803610f883c2107a441b00c8080d280700346d040200948003482ca22103081c00d00c001112000d00c6d48030381d01c0481e0710305039070ba4402c2582c805c0c403076207160030014190040d1100000c40c1c1c008001c103a903 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 292507293 1250 292506043 292506059
    0x2040e0a0623240c01020a120b040209030604031101061a0d0608071401140c030417070b0f0d0b0d06180b0f130b090a081615110319091a0709 62
    0x402c80100c1035000c2690030312103041400601041521106030300100d41803094044216080e80d0110140e400050360000a440c00340d0600c0c42159043e0354151403c40c05c2c001124007103a5150406480a030034002e01d80006541c00100f50000006004004100d881010241c10070342c529401903210f2900c82c60411a0100344003d00140e007804541d82c20076024041f04030300d0010344515404000c9001c0044042049550421080000388000e08540303010b203100c0707202c80c451142001070b01d800800d90410101f00d843d41d19410380c0152644503802510004208122100007900141c0c07000005240c14180490240e189500050300506c10b8024001c1c7e080d695a505c40300c50302c0550495608400352a0019160081003001e200541d2000b10141155840c420303540340c00c1240c1d0084200440c1c2e080c141d070340f408104102c10004021600c10100309000710100a903040b691800001c1c04588002d100180f4903412410030b4000c0141d403a041750500e00703c031310715030418a4807030800c44100c0040781c400c110000da285 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 292508543 1250 292507293 292507349
    0x5091309080a030207020f0a12020307060e011d04091b0f09063b04060f0b01051317010b060c03030901062c0402010e060c060601030606030204030302070b090402040e0a06 75
    0x1540078031078900c2d149051506038025041500180d80050f552081e41c0c88607141e406400d00584400b4185024080252040625000a40c0c00910410418082e03030b82c0b11345d0304058440b22071540303a6200c2d60980450400328000f400010f2002d040107441e4480c0002c00c1d40384905010503078107246031244015454400500c1500c91a108071060550203802c0040d22421480b40c801444001480034000517001c0b1202d045241000d8a080e28965030782c07a07080318040c4503442403102000b07080c03d11604015000300000d00f00ca0844c419049404911094201225030a44c402d40110b5002414191200503880d15590f4942007120761040c0e80d840c0800101c0c5024550103090f00700e103044641c03581061034000c0e090444041c00351040b0b051161010460a81d90380d220003405440c00d200300180070600d020400103042e81d070160b1208041c54810801800403a6002c200329007a615010f004d10380d109480d0b03002c2402441107078440b2020704103e03418421880b00c030703030407450450342d550403200c00f15442100d619050b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 292509793 1250 292508543 292508561
    0x3070b0c0304150f060f0b120c0304080702120607091202100c08040b0d09020a050102121e040504140403090b0c0a08030c160b04060f020f0a030e0c1e19030c21020d03050913 76
    0xc00d40c8c44000405403003900c0015988544a0341586082010b198046811850109103205260308071a0400200c03962000c0d810004103074000200710710000a40200e4504454a0100d504005d61002c001051100c1c040844000342001c1c8092690b031242c41c8003000003082d42c40f400b01e00c1507801c020002529840024510280381241e4101860f0202001c48001010000035510402480a00000800c0e5545200c4c14200b41d0101c500c0d0030940c6000d00c0c004120b09000d030030120f02041c0034040600200c8000070120941580185020740d40d032100c1004401a00070003200b030000444040c80c0c8010402c4910680340214030440b4144065450007680800380d000b0244501b89c180c40c1840186910303031003a0007641c9656401c0c01910300302c880c81030200d40c110325900c184910f224200e50000b0b803c1d00384030030106024460700600514940c10369854401da48070b070303120384018144441108100464030751603220100c0d41c01450000001601c0c600640a5004030700f019201c0c10204400004080b021b004003411 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 292511043 1250 292509793 292509817
    0x108150102060c07030c0503070f05010b0102060103050606060a0e030f03130602210703030f0533060304020d03050c061e06060a020709050c07150209030f03070b0c0304150f060f0b 79
    0x60750703032070400c120320702e8100440a404000c09951b0302d80209006000405041c1e0043c81004444240d0b418450309454060047c1c90455000300010800b0510104140307030001c0c012100c2c0c0303907505544001102c1c00400407007126814000d40c0482c01c0c0040d0f0001c020602e494038100040710082d0750300f00590700c90f00011410812031880c14014030190240000820095200b0300f0002824005c01c1d01e1135003241e500b11050114031501003200320924221141401801007008500342008035a80040340b80c1e400080c20090040011403414410980140250380303490b500702045a01c130b4942603800c0c5220600300205841084031400101ea51402c00c20101c86071b0481640040050031300c4c1a002c0d80003131000030514412138005201c030000140003504020a040d1581c000940c1360b1130f5020426041c448400e40c0c41503c4c1e84100440d4000520b0201510380c8404180d150944130b80c0c1ba4103040f070100b120741e80d6005000d89400038440001200c0d80c801000e4406020769a451961149440c3c80148600e1986c40c00c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 292512293 1250 292511043 292511053
    0x305070c03120518060403020703151806051b070c030b070c081804020d06090e06010e01080a0807050309040603050109110603100e040f020d240501050a1e150c020108150102 76
    0x30109501e0b40200d0b80041a0300c049407038007802644c02609025003030b10304400507003001c80104103200800148400140d80b03131108020a2000c00c0400740103044604c0f00030201619a00002c2d40344642c840140100b21118544075590100d03840c2885c0960f10034042200d406501c44045541c991040d2111a4000d038080b4103146003c082c66030400032014100324181c0d005408100c05948100303e4007500c001401415400f203000e80c0300354501810881d050300700f10340b4540000010083d100e0300041d07982415030840b41940d520009410030030308501c2181c0c01c840d0843d041c035000008000c0c056120a102a002d0070b0180001200041044950300c0161884050b00340304500510060750301002640c1c1281c450f060300c00000c070065010600300703035180400761000f4014003642011040320600301c90100002c0c80e0200150b606080024071081c0319401100020000340c0046943d46100c000124090000580c1c96400d034154910300074104180c00c0b400702d0003c1c05240214204900c0e02c560421480c4050700901 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 292513543 1250 292512293 292512317
    0x71a1b07050904030c0c0f0f03051b01090e151f02152e030b1816030203100218031506010e06120105060a0c080c01020406090b03060d02062b020a0305070c03 69
    0x2a0f448500d02000c6d65007142d41a000a0094a000030398802010450f10803001c0a00c3c43c20018103042d5260401480c0d0030000d15660f40607070340401c0c1e110a42c1c07114003482d1071684801003006401d693300c010f2a5046034011008003801c8a16031622002c01c2195401c555824111141645100d031058070030403550703204004400702c814a200000c14498a82c86151280b8540c3d03138075070a1261200b91140c04070a100140e28a800200070b020030781d10142c0304c500300100a4510f9010907642e6403248140002c040d408210010400081c07501001075400007000ca48020202c117031242c400d44425a20b590225422560032480f50a0000c20380300d00e01c00c2136414100a0b0719103401e1284070b500440c8040c042150014000300040d4000700945908090704000584490030008041d148401a81144589010a06c20031095540d1030f80c1501705558113540d6103445d030203c1126035444107ca0350209405583c0e100000d01c0c000415800b8040000b0141d03010b000c5a00c0b50720043d104c0030b00708000074002030f0100d5030360 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 292514793 1250 292513543 292513547
    0x60b0a0804111302120702161a18130b130e150406140103030c02030c09010b030613020c01060b0d15030201090b0c0c0a0b1b0607050d090203071a1b0705090403 70
    0xa01d000c0c02003c0d02e98000380048580800c1240e00058000c48803045100c2441701c25941001010b40c40c003510305086041c28209110207402c1624562040300844001680741a100f0b001c141080e4000c00c0501881e90742c101d00000034000d0100319800c01d0180704c2c0350075a400d2211190080c200d04819000240400400040060480c400010803c0d00c0c81c40d15000c140d45d6103078071980c9541c000c50003070703841841c625880c1c410181030002031942070384034100e0200140503407984503040781c0d04913600b01d60107002c0c981c10014443c00b0340244004a27029520705403000420320b01c0301d4002d0a014280e81c8040101c80009800b0303503680005400f01900080d41c1c021300340041c81540e0000c00100130840d00715000503100000241140c401508114556000811000c0c4807955082c1454941c408a2000e080c180c6410500100a40600501502801c5e2201c1400042d510305008070030103445200580400002c200e050008aa0f03c540581c00080004000b10311940c20080303a99002c9d50f100401c2092261600c0d142 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 292516043 1250 292514793 292514813
    0xc05040306110405150a0206091c0c02030715021b031207240207060f0f0c0e0f01090f090203010f27111b1b0409020904060507021519060b0a0804 64
    0x640c02c2c004100108450760340040d61248494558080d641c0c51a41240080c180031010f003e5802d1944141c00e140f41380c0d0300d0b0029031003182120340b40644d100402030002a2a201007a0b00c4055900b00140c120b0700366560204500240c0840180801d0551105100f4582d84038a0460500303c201d106115000015145980307440b05a0700003900107545c000720b00b50f84c1089a110000813141c0750380d44c200511841d41c1601542002d09030b0320380704201c2c1c46421b01d00500008407001d0050300c076582703c0442c134266a0151820b4809481405008400241c41d0600c060080d4000c3c0643c204058181d50009100054280d10094100c2c0805400c1c40288082d001100a03244000d24042c1c111001d1020ac8100798000704421650603c0d00000c0101001030250382c1006002d681d20b060207141848030b10740140c3c440050454029502030340005096440c650f00302e09085c61a8620004246401c061018201d0240a48800c00d05403400401480b90b44440403401d0740f103442103100c00b040309200028041415400c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 292517293 1250 292516043 292516061
    0xc02030c190b0a0c0c080c0a06060e0f190905010614030c030f030d051003021201050f010504090317060607120c03090b0406121a0a0b07050f06070c060c030b150a11010c05040306 78
    0x4004141c1012036486001b01d4010304904c507180d505c000300302402d100c200c1c002c001c01081100c1c041119420400c03068042c45d18010a0070081601c41807414441f00b1042e40940040c50304200200403403501c40c00d00103401d0040c213091512912460391541c03081d190100c0e900c41501400380046160880e20212100a03100040c89a05494000040080940c480d20301804452064800008072031602c89480c82c1c17007140680055000d580741c1050390000a4000308641050b0004844840c095500c2d0800640d443c070901034000d04490f506203080c41d801d81c0010480c072580703102c0e07142c0710300c1d040d111030801c007850003184501800078004d1352602c49880d0342d0764400e2265150014100e410100600d010881207461035004406a060000b4924144603080c4120030054048001a01c2e180c280207800501d00f138500a40903012a0340c40d0940303400140648e00008483c903001e08080350003d551307030001040703400180705000410389203422015a40c40c10701c1130740f45c10010740d116a81005c0c03d6486100c01044464 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 292518543 1250 292517293 292517297
    0x6140709091e0e01020d1d0a0308040f121d0301020901170403030e030c1e061b0c010b0d080d1416050c0c0619260a0c0e040c02030c190b0a0c 62
    0x1a141c040510b0442c0507006110f19001c0000d41d44000c035003103102c225011024000c52000c15201c1003032000300007183c132a402c0c0e074052038010119282c0e428405044500c49200904425002a0340e1036200e03000700113420001c07036138504d405202d4022410706080c0e100f0b2519550001c0c0c034038031000d0512013840d804035070001d01034600003407008200c104080c915400151941056804000070041c50a03044400f624030160700005802d05e4108001003070421403c0c1008010303620300208900701c0d200d202354050080d04038001d080181c0c2071014180000c250740300304400400302d802c0131642c0c00f00f26a01d4a445014440c418000003440000d40406c5946801005840210703000f60300034071842e17640d441d001c0d0210310150344c91407444035900480034180306180d03030604d0700d07800814084400d81030041d40182d41c081003446020806565045d000c0704d41c000b010210940c0305241ca5034071213045a000001e082220008000c40d00d21030140040080b00d18002c50006150480c4900003500000032a0031003003d0b0300681c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 292519793 1250 292518543 292518581
    0x2190305061b0705070806011e0308031315020708030a06080d0905121504081b0d0c080d020415081b090d110111030f070b060901050102030a0e01090b12040614070909 73
    0x5a07071352400c05415600a0a15910480045c403040c00304d0348101280d48804d0480500080c5143c2d6441e01a000040400c3e5921074810340040500c0b4841e40e80d8a12010003600440d0399461505e0819141c1e0070960304220500c0c909074000c60b8880340010b60540004070340d210380303140515210400c050746010349840311143c0030700340d800d6202c03180c0c0042450045202d0b070070705038559a600c8208105030098010254055202c84c4101a906030000080320a054000b1145980c50702d00b5002c1d4400b902c2258420b80c44281710b03068201046910940c441e0042d0120003400c0c46416200000f000305005050002e58080c4d07060ba824400210ba9560404444006040050200684046880c21504010025510300c1c00c001491820040600800c0e503000100721055007142d41002d000079942d000c0c0420020900041016a01c101d84c000e4060701300903c0003821580c1c0d503c1c1d4500c20481810303000d0f2000c594171b03410709640b14000c40001d00203502c5020240d55051f6924540003801c40900140066180f2280c46 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 292521043 1250 292519793 292519807
    0x1a07031b06020c030c1c03140f130b0708070306050603150105070218070c03080702010507120203040c080d09080c040b0f0907030b030a080315090402060f0c030408100902190305061b 80
    0x41130000e440c840030548003400c031125140110860140d80c0c0d01070303602014070340f400b01c0d92040b180454050300840c81d4074140300030340d5400b540020031601c0c0d134402500810f8402c0800012036802120103101e80e046548c113100c410358950500106000607640c40c8000380d20341480d145030754401c0c3d01814680e40010b2450250324450f04008520440650300d80000804403003c6006142d0417a0940da0015003610003080f0524003100c0043c83c0b0440c1e0540d02603090740010204050041441d0303600003512103901611100b456000d400f03400c000d854484c0c0c08042c029003143d0021840c09104610031444090407489e04ea0300540c080201218005080e041419031340e10b00302140341c40030014503030502c0c400d01006950f42040b84908884041e001091442942c61404000040c0c88400540d01c1025289203400d8481c003108a40c203041d800b03203030061000c40c440c603843c600704020143c000d5284e0b2030003030311034240804103100350807c02200c40c08007420030f5102d040801c4d4105a00c00c0003200c0b0252901c50a410400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 292522293 1250 292521043 292521067
    0x1a0d0203070c1704051503070e0301060806310f1e08091804050a080a0c15150e0c04050607150515010305060d0b04060c11060f011a07031b0602 63
    0x429500c00300010b0310045004108500c0c00341e8400703010700c038102d00ca09051502c0000b580a4020703002c650b030f40a40200c04951400c2c000c10444c01c001c84020f00a12805403900380f0301d90f80b8941100c62904e200301101c00b060031241c112600c10700340781c07120030344030a5800c160300d550301c070070221400032103507816042d036a0441400101c40c00304a2601c10426680d032441c8030010800d40030404541d144000c0ea4120a200000d08009040300c031a84c1c2c0004526210744481e2801d880040c0b0101002d407500304050f801f90030310b180359400752000e00035854804250070740b60800c12001c004100ca800c9200e00c0700300810310141c40c00d100500341462043e903001041c03803501c2a206007990b2055400008031030041d00926000c0d038040c064107602a005071154141410f00d921a12000c40010380050081c0c1d030361b0042007202d0307849510450000d1800b2800c40c0e41038103100c041c0700003245013440b41c25043c030300403040402c01d02c0d100300c00c403100c1a40640e549410348440c4401008d881c86144c44c1105c07000c1d400c000c170400c904 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 292523543 1250 292522293 292522297
    0x12070201051c0e070605120411030f0111090a080706120e0313080f010c050a121505030d02060405060c0301050604270e0a0203010f1107080a0c050a0f03020d080c041a0d02 75
    0xc8000c9004038082c075071003034058500040d641217103050090900a8543d04440040e885034483d8006642511078101c40f000309090075000d07842d10100d03509001c2c83c2c00031040303046d0040910320020fa5007070260350740c2d5150484c0c65209178052000000c82c103110031034002c00c0d20341000708407080260640b40b82c030104124010a100c060b5010007103e40160340700304080c0d8428800c0000395031481c02c046260a094440041217500700c41807072032034560703501428074804040001c400058800079046076205920210003079925a4121800c0342d403489004005040924910300790703030494030040d001c1c2c1d04083c20007000d02c80c11603520100150540d4215101c40c0310901c0c9024030301c07080d120400903194020140c01814291410344080803d0b690a002c040c010310b0700000100c407070241e040801c03a80c5811040c2c104940b81121180003909900c5807860f04010711058620501406120381c00715018590039078030544901e10100c49400c7e4444051000300010006142540075964074140034514154400801c2000c07a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 292524793 1250 292523543 292523587
    0xa06051818070e0a050703050f010b0d060e130b01090204060206060d1a04030f0f030e0c0405041509050d26010e0c0412050601050a060c080427020a03140a0b031207020105 75
    0x288000209104041c4d00ca40308454014a40e40b505005a25004101100104c1c041c420200700303140000d40750305046000d51010303010f021090380000c0203080441051101300210f00d0b040c0c59808920000003200d64881c0b0843c0c0131a20281c028040e1a40d5080400882e04446102030703a0a1401c0031720741d40544c1c041014284594800d2f25494095072016034001c0210544d0b00500e001d0600e845582881c40c0300004031a4951102120080703403e503900d1812500084820105002480c01e0a140c03004001000ca9001840b61703041d81c0d191505142c0c80700c0c0202000c840040781d21a5080e180052101480120341c0c0382c0d105001c1500e462901c0e0f9991411820b40b1358009040d1819002540140898680403034607800400040c40c20204600701520b0300055841030b4480c1001182d111080d408801483c04102000d820001c0b02c215202e20801c1800f50142c0310411040c489880384000152001e1454415198040c0707003c1c0050034400a502041c1007664002d5000360706022017400301103d2000e08960710070342 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 292526043 1250 292524793 292524809
    0x2220c110705040c0207030609050c192102180c040510030203011a09031e07090c030504020f060c030702060904140403020703030f051903051306150501080a0605181807 74
    0x6161203084880341040016003010748118100b90365000915400207664050740e130030540000f40a0203e1a0a0385007034000d261541d004480c90a492071108800c1c03445104407856080180b5000c0c0d40800d04c500b1a5841e804000e41c02441d400828411342140e00866601030445490f2618140e05c407000100744125142d203583c00a600000144a450f4984240d48044d24480c02818100507000c4002912100098a48407078041615003050143c181040044020081450104807000074004003d002e01002c440c203038001c2001c50342001e900c0c01c0200441e074161210744007460038114190f00700242030780140d0445520948840d203580c1b0490840419500440c400d070000c040a0b8a189400307403c0c2060baa03000401e010013030220303000d11041094580c104d00c0700341c6000501395a5581d44440c01e21019880500310900d040030445111181440480c1559401d80715070300e080e900d80d580300090320700c5400b50540109070980344160710100320140710b400c0240100d1000b0078100d80341c0030030f160541561105013 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 292527293 1250 292526043 292526057
    0x10b0c1f0b190302030a02060a090b12040311280305091c0c1a0301090b1f0f02160b2208120403060b01051204080d0204170601060201110c070302220c 66
    0x101c0361400c0301c82011100340b001c8807501ca4503d1500000c0e1154043c1c04080d01504d40010614000b80c410306106003d810484d0303a06444490046c45401c10080407503048002c1083d0303072041001120001b42201451003465115140a845031040b403005a003446012414401e007800494001d83d02c441c015031092200a0700c1d0460680d0310b0a01603000343d180d03841405421201c0c01c0e030b01e0041e8000000c4a0540b01800c2010520200d50710208469607034a0021003520003100680000d2954004030000c801c1e0503681c00c49071002da8601c2c022030104524441c0d585900c80c2000020403401614640540c052451840038410640d100880c1e8240f4802c0d51039680d4540c40000d00b40104442841804000d100c00e00e04141005100d4607003040800d0b0140c009081e00601003030720b400a00c0140c0488010f00101218504554040d0095542d246403e00490000d942045218040440c00600b561410000c00d401840d482e8515000e04c05608080c400407200070040244064003116503008030307840300c12a81e6450f0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 292528543 1250 292527293 292527311
    0x50d0f0b06060a0c020d0c080604110103150501081803090a06090e0a0506031e0c03030a09081e0d05070302012909060307050102031209071e0306060b12010b0c1f 71
    0x481024001d0010344521030920280c030142d588035542290603a8151035000b01d58803103041c203024042299000f19894070030302040104102a409010403111001c0e00c043c000304d00c04e251400000e40e550b0203241c0c000307182d05000420f1560000c1c4240b500014140949182c0b8060202203210700c80701e40c0042c0080f0311807000401400b1100b440302548050a080200007034105840000d4992110b9003800c0c001983c0b542d450f1103000014440854a1403004084980d10b1401d204003600301d00b11840341e070700713035002d041e05c41d020050000200c00d03218218900604524034042e001640c15810a6000323908542d41c41d91405030700346c03d060301480c2c1907880301c500010810401c4100190703510002c208500079000300c0c2e02081a80d0b000415644560211810b00500740d42d401d0b480d910b0000d89034090b40616184d80205117515924100b82c00a49015030824400340303441c2c9242015034801c0e0702030a040c00004000401203408030001070103010714054141e80c501416001c00804c10391300140d0205049a480c0c0d118 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 292529793 1250 292528543 292528553
    0x50604060f0e0f0106090302010c12021006080109030e030d0e010c111503150f06041206090203030f040815130308041b090b03070504091e0f050a03211a060f04050d0f 73
    0x20b600503c0341e1b10303100c1e440341d0071940002c0c0a4424101d009018072030942016244c180203002c002d151090a2030100001c40d52603003114040c0850282c15004942c02d40c3d00d451403410701084000c072107a0a82c65020000082e400112941c44034034105440c80084651031000c50341e120a00102490380e590038441d140c1c10284e2018100e0f80190b1501c0f0311911080d18003100300e1300c581041c2c2d002c40b1080c00203001c0c5c148003414444040c02103580f00a515000000d0040511440c140c00381080e98101c00c2101c1c1029044400b5030300c8460240d42c03402125511800d1031000902c240f41140e40284120038045416000420b14811103001c0c3c1c021030000380c0c41d030642100b07030b060030024034008140c00c98084c04a0740068869100541521207500d502c5001200b000003800344040c0d02c0c1c091b070796210302240e10901141c100103202d803e440c46502c1c512280c0320000c03006802035000703541c6545100b00c1d02a141c40904030400c4241c1c4d00205c0441481c040c1070000107401d036903e9401950441c012011032080c64443d20b80 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 292531043 1250 292529793 292529821
    0x2712070b0103210c080a020307020307030606060206010501050c070e070e19050114041805040201030b06030a0b040f05010303080604050405010e011805060901050f04110a051e090903090f04050604060f0e 89
    0x30f03415803020301030480740300c50344208521007507a04240095658044804100e0440c8107503000a9054841e81070300104201556000000b2a4440d03820f0390190390303d85004442d1841900000c45290740001e41c00e00100d00300e0f00c80795821250500300300b22440c070010301190a09840c1c40c08240c6c0801c2c0c0103000c120958100050118048422624500e0607081041d014030300c8600602020446680c0c1000604590003988040217003d401442d840c0c4901c1d022001801070110403560340e0017030b400c1200c4141c2c600501e0082505907a85601e4000242d40c078003081c131008000080045d510b944d02c5030103050840c2c900703200d280307400c984202050704403152900300305181c4403004d001f10f41c09a1414040018000c0a0b180035a08290302090504d0304c0320080c070000f0300000b03080d08210780c030440b0b101c1c40c0443c0b01a070081d96450501d003511410b2141c0d840d001805d4490181e080b9040e0031546007250b2000e545030036440540e011000420006200d500c41085900500d465002200440202c2c81402002c20b00080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 292532293 1250 292531043 292531073
    0x1912060e0c01201203040510060602010b0f04020a0e1306050108090312010303120e03040e04060b09010602031c0204030f29130212150a02212712070b0103 68
    0x81a1941c03003900024400940380c0651030681815114407001003c050114a02d02881d5080d11078980c203080c24850303142c8881400c0c000340c2c90b10f090703c0054454018016886080c000a10000c0920030781000e0101a610509408081041180001d11a0f5655a001840d00017004100055140c01c1030009004040060912a443d900a0240480c00b0300319000060540c0e90601d0842180c400e50410740016141080d40c1045502000c5004290a2503440c402c42c03080340180c02c203012001200051000101080c0030b1840160001c1220031048220300318444c100034214030b030040c60159039072185000b4100400c0300b102c491310603242c1800240c02c40c82a071404205980422600d50407c034000e403034504000c54000303024010414501d50114018031407840c0341703001c404a030341c0c02c0e20301203007102c00961008520f080d1850a04c130586556082e1410814843c1b4a500b00000030b540780200e40711200848020b40f140c2521600b1000750901d600b8002a10000d0b2051810445550440ca407280050b00b0b454 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 292533543 1250 292532293 292532321
    0x120501030503031810023f06040b190e2505030a0c050c011503020306011a0d09023d05030f060f011115160801060504030809191206 58
    0x100180089800842280c0d004000300e048400103011041006041021140c04031071250f202003540e08841441c0004c12000601441c4540c03074102d15000c000c103280554068006445030b5210028030700d420141e105004440c00201080d244050401c0c0b101d08124940c0c11605001500e5818410a40082000b500c0303e084a81c060010880c054140182140401000c2032006521103e10909042c0107108458422040b14003d100315500c43c0521500c180d0548000c034043d100b81d500000d45418007006d45e0510600c0c4000541c540031410341c61401914a011040c1d80c0000380410541e00c10064840e500964a0000343c640005050a060780340d240e07405401c0a000c1c010304104124031003030603400d81e90780a00b0440e40100241a20401221012075495036954180b050001c8164861400360006208464400503240420414202158401404c0c4075280200f20180024400260714201601c102c400c0070b458298500c1b5200914140d01c1c0d416480090700214000c0c0c2d03c1c0c180b05290140300c084440074 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 292534793 1250 292533543 292533551
    0xb0a050306040803150901060c02120102031b09040e03190e040908070f060e032109072402031603091701201c021306090e0403090303050306010c0c0b090112 69
    0x540800d07200d0340010402044540000f0015106107001e00c42500d61030f40c045d041d81030968481c100038140c005280300c107921a00b294010605400d2050084900c034a0302c0d1a5451f612428000e000210b0790003401e40341e039100c2c0e00c41d4001c502841e010000b610250340010203c82c0c00c24032400b0050000c254512600340541d0402000201150b10710303040340c1115902c100c4001d00c1001c58104000206640703c4a84c50f9400f0003c1c0e160100882000c10307407220031048004a940e6110608920341d9010184900d03041074000202015080905103c4643c451a850050300e2611040715400700c20403041c12421004188000014090f0500300c200354841c0c845000c1c0200700251820150340c0101c046d401102508220004207044807080d0070030710180202c1300c0081076480340825802e010271302c1500c0c0a00e00c00550000c000064980f00c80d06818081d5406072140c3c030026056403130850703aa0f8030061040703050192481141303001a07004085a4010180964503581ba11036120004141d0308910019140321418 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 292536043 1250 292534793 292534799
    0x30906100e1b07060b03070b030106030e0303060a0b0a050c0706090e0a05070c1419110f0109030b06130b031504050c04090305220b03091b04180308040302030c0703050708010b0a 78
    0x108103050824060140546490f0841c0d482c1490141055418894050060100005a003408800658180c440c151010701424100c0305000e0b82e203000c120b4016900c20070140081181020b034500400000d405860642c2c80c02c03074140f944505c1c080d5141d001c0c00004155840421403040410a642c0d0060840441400329081089000303110040410340900700420904082c0b100b00007c00041d10b19049003981c0d102010340c582803d081c0c125520401a005050084029401750b105a07401e60a4075400781c40700b001500c3e07150038025956116004c4d41c1002e82e0b112683d12096034100300054002d401e13021321101a19091901c0c50405d0341000500f13010364200750303124001035000b0040d20581d1841103007611000d1040e00741d0041c0240503a000003000c520020520215110120710f515440700c5030890702100e040340c80280000c841524800c00d10108140754082d00180c420101c0e1500140240f04981c1040b5200b0142414000320354401c84045d80303c01d1080100b10300a000700036482100700d0f003251500e45 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 292537293 1250 292536043 292536061
    0xb15040203071e090f06050c16050306070c08040b0304080310080c010f03020d0f05011d011211060309100f0e120f030103170d0c0908060a060b19020111030906100e 72
    0x1240c490005107010501a1100d800f80c0b080071440003c168010004241a5680c480a01298031102d504505801002c8101a109242c502004100c3ea4041d0041c5083d40c1e078035504560b04004000100c2c0c00400c1040005000c003951b1000c0c5000c1c500928074940c2e28204040c620280c10030036400000c4035002400102d14503038004080e04004112030401690318490119558001e1042d84840031601d860407001080528403401d45a100c0d106001c0701c8801c0d66220b000c080810600800d0040c0324981030307035110401c0e0810102071a000400e09040325445180e2041100c241d030441c1840500007a550349004507204410403440004a90b80440b07686060b50200047d80b01b4401408042c1440d04801a61110040380a0803680f5402248104100306842800c00a261008030720907560395108103804039911012901c00c1400b00d40080d250180b5040d480c140e00c0c0102078245000030259580c400d80d03100b0700c0036544021441250b40c80048d000340e16003115900c1c40b20100d9004080e184007040c0070401c030b0f41 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 292538543 1250 292537293 292537307
    0x1e100c030f0f20090d020d11090a020906070f020d12080603010c08150d1707080d05060402130302091b180306160f0305180f0601140d020d020f01090f030b1504020307 73
    0x601d000d4003850343d074000e50005c1100381e100359100171341010040e0050414080c041c91a2954080c04548005058584030180b80a030b02640e203a40e41d202c4020040c0200007512040402c00044c4081e00d460503903104d42c3c40b00103808a8445400c0301080d006c400b0002640790a00c01e52121451605100001e0f08100308014035100c8000022030042e22810154418028440292032a85150b0300070ce41d03440036a4541028075401c240090200c035030030100820650725080c003c1da902d00703648103d110000d918540070000c0003100074111048811069640790358880b040c01c0200182e0002c070100b00d501241e0390061500e0018014070072079071891240710b2031102591186800f90709501d103140220741500c610782003910f640310f0846490407030700c00e0165a20a003800400c005040351031041c80000d203502d054043c0030007018100030081d40b10301e8039004040140b5102c0c4d41980c00c00c0040c03401c0c40e10715441d481c03014084802904240d0712224140e081007040c61b0f41d1021614059030070345040d07007075003090038016000d5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 292539793 1250 292538543 292538591
    0xf0f02120c070203010623010318020d0b25030617070f180b06030f041b08151909051f090c0b09030c040501090e06090303091e100c030f0f 61
    0x400380002e078190a5680035000768003d0800002401642c265006c040ca944040d0140450701090500c10440c00300c1030380880060010f90041d2446c1103800007641c9200b280e450041c1040080d14400905440c05829142186400c2c0070617100040c0d013070308041035400040310141203c80b55a0045506202c011002810402207031104010029042101c05480e4083c003041d81d2081d402c01c2d404030800c0010240d00b0100ca0150b4007801011048444103a403224042c1c490340240c01e81e583c0003450403100d00c06140301e2158845030320b0124880c00d0207403450280070ba4a014205490561110707489450968131285031025a4042c100100100c4019680700f0400d000280b0812029100206505440e0b450512101c0c03404240103004011380c1d03858044800080c81e0851014085203c0c0c0c1002401c005000003c1f42e000e400d020004241e58006502e00b90700c08501140b0f049060301408401c25585000c40c020320b5503a1201e900c000ca010040c210209081391050206800c031142000b495100c44103403901e06c7c0b209 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 292541043 1250 292539793 292539811
    0x30b1908033c0d11210a0c0206180708060f04030f0f0e010e13090c0602120f0706050c120a06060e010315150e0607050703120f0806090a06180f0f0212 66
    0x448950000301801040e0380144c45a100000040155010075000c41c00c40e610703401044020300a441c1c3d60810b00880e6000c20708280503a0108001c00c540c00c03c60b45c0c0480c042d2443c0d400302c4d100d0b944c68041c84c90420f641510b0090004003094203000806401882401c4400c40764a0031924403409182e00034608513150115605211400000c0d2150351070b4890340d0248051000030905c4404e03814030344082805101d119010040c0a52904420542200400c0756035070312694280f10f04042c05a2034031001000050020304407420100402603100c0d000748441480740004010000d00140340000c080c0c40d52852820b0b050405181c0110079640b880409110000c0e114903101c900f0801c2c4200000b6114102400e1000350321040118160041000c0010b0860035203205c1d041c04003159004210039248484e003200c1ca02c4c082910b9000140d05400c2810f42a9401030100a000c1201580c0d050008448013181d0034105d10240c0740c040091203038040e8003070104101e08810382145421f0300406181d0143c01c024040e404 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 292542293 1250 292541043 292541047
    0xd030804060f020408011e0e070b07020f011b050d17090d0f03061d09070605030603060f0717070305070e1f05091503100f0503150601030b1908033c 65
    0xb0b5000c5140d4161409024200d0081140003001102c03034102c130740301e8120071120310304115110340c6c44070b0042150421145140505420034100d9401c11801400f40707580c140c100600210203030300c0d4041c041c0b5591400790146000d040031030b10301c4800900340071201c0502c07144010410f0078013201d244005140c211034a1030380f405000c03403142840d0071400b80c10107030702c48200c000d820100043c40b200e10089440c028403241c03089403203941d40c030707002580d0b140000c0380c00c603605800502c0041c00c0307504144c403078507480700300b503e820b03d1044c50320f42030f182d00f6242c141c5070307030002a50768810810324940140c03400d540e045c0102d404460112100c8880a0803070701a95606081100218a0343c1c5180c680d0681421018007104203d9100c2c6460810490300000c28407803124062034020340055207090100f846103075030f446051107454564030031005401074100011044e810a0b0030440341003d0f040b000d0000d09c040c100500143d039481c01a0100207203140d00c3c0c55004110035400c2d94910001004034121074803440d0440f0b004c80e0b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 292543543 1250 292542293 292542311
    0x304110103060f080102040e0109090c0e04030c0c120b1b2b050106080702190302070603110c0703030801090b0102071419090e16080609060a0e0106051201090c050d03080406 76
    0x203015012950100c90b04000030103000c04d035400c0640152007610706038450441c06a90350400c40341030352041100a0507900d40c20000b0310541e01d000e040b15900900074145014881c0490b5602d00d070740f1003540c0c000d245491003050000200024210702c10b4100d4407100c5000980c41c96000081000e1083d045080f4200c0b062000040303402030081070074a400e090410f800c000541c4e40300006081500b049842400500580302e095580007090f654403250180c2680c001c0610f2401e0890075401410541e084050340c030018866521228030130003a0f2009144a41e480079a213502d05800142503443c1f011901c1c0c19500f02e1402030040c0c4003020008100c0740403c80f42d589004d1074010030039101e030902e6049180d0f2541410304140300c0e1000020411403110351544c564405950740d6410036203800065030321241e590010404600e490380700390000d00100b0606000092020b99420002c1c0700c1110030032060070207035100c140000a005500c4803190040c00e059540d210310f600250f80007001c034280140300400c99940c0340320031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 292544793 1250 292543543 292543547
    0x902090117040f0605010b03070503040b0606071b21050a020d11090103060e0c0909100e03160506180106050604030303180c030b040c06021c0e04020d021201030c05010c0803041101 79
    0x304080c1d641e10740004846003000d041c01c0031900d02c10442a40d041c1d007044000a021012242103038401d4a0a41c5d6050940d1a5a038030001080b60181220764000402e2103039001062515056220261080b191740007001d03e0254a008040c005000e000c242011669146010034000b0071110002c6504550b007148600940ca018a0100304146520f038000000a0012003000419400907403942410401c07900a03460300800c000c0008411580e0800741d030040700190012240c240c029840340600c00302980c1c1031030b039403a42d0500c2540c48590141d410358400402e215400c9400034840342c0c170a04c101e00900c9050304180c00710f0064071461000404255840d0f010b6114441003080c01c00003641d0144040b1000740e604d080c480c0100d503080e81c0c1990070041c5043d00084c200d000081d104110303920301c22a1000140c0001e01030360b4803640c42c80c1603a00540c082242c003201c2c0107244001c002c52803d04803207400f50350443c20035443d0505913801aa0500140894110105060506407035206c1d0f401240312010110740001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 292546043 1250 292544793 292544807
    0xd020310021b010b0319030f0e060f0406031a030d200703080702040e01050105100c051f090c06030908030411060d050117010e0109020a0302090405071a09101809020901 74
    0x10948006101149020010b402504022004041d140080c0308046007042010f0b11130303800061a41e910320810204600180c0070306c1c80100c0e03070f00c500e0510070b144450b000085404d070340c00086100c860b000001010b01c030568041c401e00c140d03842c508114448407044440840d544580032000c040910494080e04d84d038201100f160030310040082c4050300c05003652880c28149039000703484104c3c816810300c108110b510030140b05141c101c1d4801025003255519501040e44d0981070680280c525005026982c1101c0b10030360300304d0250b55002480051241240c0c14081c030000504d8010004041c106070124001c9140306066035005604600e088101c0d010602c00600c2d240318100c905103099060500000e89014082c12516115040900170b1040888201c41e8508072141540020762084101d2018005400c1c9514000d42c068420f000302c03112251920744c00701c0540c0d8502c101d094403500028001500d401e14811204013900c0e42c0c204146104054001001e280c41d1030f0044880807540401e400950340e1142e04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 292547293 1250 292546043 292546063
    0x210501020a020a02090a0e070314030c010527031e0310210605010f0e0112020609030613031709031c0b10090801140702121608121e070203090d0203 65
    0x402199075802a00000e919066020700a91140710841c002402e00300c00750140e000c0744104c40c0080c10708d850540d0307216111404c09030310440f8107100c02c2c00003103c01c3ca82489803600800200101032417600415660524170104200126002d4005016042540044c00702c81d01044c1d2401105903100c0c1d03100c540c2c611402c0c1503a132052002404121145800300004040800358901074902030065a80381c5510310a4407001e40b150200e032058800042110314050115403d10300e10042c0034502d802d00110004c0d16124007502c003107891032442941071041640000349503046514540000940e40762072450681c880c081c581600203429100124445100e81c0d5a00c000d00141000307051128a0340c8030f140081050f183c2c2c0c02000c11a40c600200f8098180102002920906a0780d004140e210307000c0c001016107802417420341c001542200180c000048082c009000701d042d840046200c4c5140c0f020681450766152101502105c0700c4206200b1103c0c2c0c0481100c01d11389041e10104a901e02d14800b09151041240d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 292548543 1250 292547293 292547303
    0x402030403030203090f1b0918010207290708060d170c010f0f02040e0402060c0a0519020103050a0e030a030e16080d1e08160c0f080306030f060903030121 68
    0x41000304054041d070103503000c0e2650004540225000c9050303550756440c01c811495089480090314449450141406030703120445919120148145150740d41c2aa04204070440701d1011142c10640b1f041401d010a01303185022214260b5642801c40b0050510740002e46200d02406d502542c01e41030098500200d80c0070441c00d4042a5200715603180180285683c1586607041400d050110032180d0050091358155030030792511240c546c40d50360800245174441c04130f8031418010510581c0100c0e070144114425a1104004c181000d42c0e02d00c00181140d030020000d44480d8078020f041c60240c2000810b50300c914086040005440740e0000146241040d600061f005411400d400400e0a00c00483c0d072446031501510740505490f510400000c0c0000d20146000c0041c070900002100406140340010480756507040800002400c0d4440751203110314102c00b51030368100007060005030f080c208040007525031258040d0445d411b00200544c0c40340b2040c41921084011100501112000020381000340d603072207 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 292549793 1250 292548543 292548547
    0x1107020307240206040503030a0213030b0106051b060403020d0f0201180804080607140906090d0203060403030e0709061208130b030117011a011707030f1e0b030c0d060507020c0402 79
    0x802c06803090401c411400d403000403902c03903072010540c00002e04c0380c056944000a07509542e1200d0700c07880203400051051a81c0c0b24403901c00400320f0b40203404503001e000e0030707600d150f9228102010394020900341c11440580364414420403011990100303645946802e1890180080442c400c0124003414403c40c0c8984100350005150040014031002003040340c00c03540c1a507074a07a80d045415181e524140100c0c5800c82002c04c42000e942c64070304010000d02c00014503011041c43e5980210386000740c212000c0700429030f1101c15545c0d03900d040010b03400902c007503641400301d1414000c80c1c81401d1100d207030080c201c0310003292081d2188040d054040c0a07010441049483e1342e9900b9458040c9602c0c49140355241d464a0b8903170074142c4104d000d81088600686540181104a111104c24410020000410941e8480200680b490030707009651248440d043c0310b0444690741a21041180e0b0070401c0b50388254004280740145840da00040162103070070110005050b545c000741a41000c2440a00c00e41c0a440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 292551043 1250 292549793 292549799
    0x16020906121603020f040e06011404060b0a180e0c040515040902070b1603050121050f0f0f1b09010506070305040e04150b0d170d0b0409050c1903151107020307 70
    0x2c1a511441124005c6401c00d4840c03d0090a000840d10082c008002e103800c00707001402107008041483c1e1012030050720005403190f54141200640c1c01c03409241c13000030310b01883c0d444541da8419062001e0440d10040e0328050030042012041403045106845c09403210b10004160303c4544010b46005104ca0307081955544043d260000080c5000c0320200000f088002c80c041c40c141c40b9104840c142d5500004420400b0301034480c09144503800a006c03030b03d070f11402880e082d031030342d0500c420002c1410346001000707242107040d01c8604120b24500c001104043e0b14058018566031554880d044070000d5407119600c4080b810f0440300742c89035800c00401d40c25140c05200030004240400c00303045d800558104042d00d45001002020500b0b400080c0611f22022032000b849c5a070344008006001c20a0000101e0500f8000490151074820405071420b801402d0a04280c5c14604000001e950055a02e403200f9801c6603151105007003041e400070180f5a6070820303010815040000c403241c0580003412100312907a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 292552293 1250 292551043 292551073
    0x928060b0306070c0c09180201030b0301020c07181119140f03040305070b0a0b09370c080f010305100c0903020409060504030f030903020c091e0906010e06061602090612 74
    0x24504c01116242000100000c2c400840c0c80340428684900300820303150b464980046025021071a40d9603810f550070011124210b00421594008009400156010701d9810304258211a0b10701281c102100d01044119401810403010302e5644e1514100416202c0103034881c2c3c015805280364981d80858000148810f054020014001c010702c105e4000816944056002c005d03180d00915540d080340c11034002c9071040d4100b1003000350f40d81070888000754806001881c83c2c10418884003000410f40d4500082d00d1499210341c206500c040092003070310039540345070b80d030640d908400076500d401d11b0741d10010b480c08a072040e4031840007107400420501184030030707082c0040140030a075070440200307615015000c0c4c424081d019100d102501034000c0c0070300501c003405205150900502031040100903140d03984100d2961030300c01d40604403501c000d0100307605106507078040c4400500301c0c0d8031810081c007042c022030f04070300407040d9120390680b01c003038030b580307034240481d40c0c20000186200703207402034254400c0420 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 292553543 1250 292552293 292552307
    0x6070c020301060f0e06130e12030f01091404081813020c010501080601050a05120106030501090c0e07050702060a0f030902040c02030901032007080304081207030e060928060b030607 80
    0xe000310000c12000f82c3d56a2030880300c645611450403084030030790010310189050160443c044004a00124070340c208495260f00744005040c9c0395010311404814404400c6d450a5000c1c050714000c82c0c1001a294404000b281e0034200410040c03400b1000501c40c18407018452074060040340117030229003441c0420858001941040c3c556070031545c0380c02c00000321400c0000b01c203812200050102640ca17030420301804244115148030802e40d64030b030340300000021400d00c918078010307000715800218241041000a146000a800c920030010305000c0f000160340d4203405c0307600084685c01d040842c091249015405441100c2020350311a00c0c07d0926400690040003c0440001c00d9030208007402c411082c003070340381410417101010a01c0c24494070001940d030000858116024900d107904110f003c1510200c6418102c841100098444002c0b444040b020004140c1210400e000f0b041c6545481c420028800e541000c440203001c4180004018000380e5800b05041c5a030103009e898503441c00301800343c03000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 292554793 1250 292553543 292553567
    0x5120f130605030106030c0f0e01110f060f241c0224040f09020309030a030c1209080912060f0f18030409020c0601060507150c030b19060e03030406140304050304080607 74
    0x800c0c102424110022310584503103c2002d416100d01403c4250f00d40110392070903c0040c3c151007803150351000175007480c00700724481c8102d50605425040c3d14108410040302080c7c0c800c0320304149140f0110b19911f5480152881c40702d900c00018441c03000a500001300d01c605c15401c0c001001710b2014a821601008100a0050722102000805200c1d40d44400008900c01251210f40c0303500103100a04000d48641c001c00321102017031504040120312009044100c1d510350004070b409000c00030f1390030240c1c24041014256114000d0145c41c41d40746c980803040302070200408040512200794006030198014503646242c00502100b100d44036a21340310302000940c443e50501505100e14800001c4080c4114100c03100305038003100d6803070400c0ba0141035030042c106505450f001c1c1078031019916110340394030203100400700c150b031412b410040ca424000707002924400c1106000c2e8008000921850350400c0c540c0384410500c1042a17603c0da0749003401819170250780c110559070302a2000744151590f00007182442 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 292556043 1250 292554793 292554797
    0x122202100305041415160203090a120506010531110a05120f0601200a061b03060506210405010b04090302070f09060f0501050313060507210905120f130605030106 71
    0x4d1341201342c1c941650344d42c050a014040900c41400610006500c2c2441ca440107464011241060002d40010360a4061a00300700d800d069245449814031204000e5540181400e0b500d0103140720954107400003003c4c03545c242d00071070083c0036012460805c43d40c3c4030110b20f8420800c1b85858225a00c401006503000c0400303403206689640116454852040d91a401500161030f80314800508140030041072002d00b5038004140903805c81c0c400030503068005c0361440d030b00003a581d40040391140005011103400c1d13003159010300d10500c00301501c900c3d503003820f00d401d400c210b0391140c07260b40754a802405820aa801c11f50003904100b034160406800041c20010390b02181001150640c40e03403c0e44041325040d11a0081da10701d903c2c0d00f00300c40c0d4081c2008507001203c8850041e402c0c400354440000341c1c0d000f600d05500207403003400c4245084500380503500240e404070000303110455460302c0b82903407944400500504140c00040c40700045424504440030f44800040300c2041581d00c810181064109129041c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 292557293 1250 292556043 292556063
    0x150e2206051002060609040f0c17010507030605031002131707050a06030209010e300f1002090d06050601110d0306030b0a0e071e08030c0313080312220210030504 71
    0xc0d582c9000c82003900c1031142a07005280c0c079a995800c10488800150080d1000b060740c5030840301103545031030400083d2a4010588266442180803075003142e1000300340c10b08161078004c041c0119680459500d8021495000150f00c0781105501451000d94035803056000e4034040002c4e00444401190303900845004440031030700d89948a405034141e01c0b4410341c00f40090f00400d2400300c0c034602071494689112101c02020841c2e240c010000703070460014555a203240d0b0100c0d8030f640320070004016030320018203401c0c010744c03c0c004e24002140c246111510300400240c1c580b800034103241d115054048003c1c103048100d44801a01c0c20f40034000346420b020680e170043c0404c0c0010000d0b003160150340d903902c2281c0300910080f85004440d900c1c0340c1a118040021010710440058400d1003040034041c0f1944020186507218035403205500c0c650859441020300d50002d1080c40701c500c90751100194001035400300e01d8584178000c49050440c0035107001c02036000c2c428060345030001e90316601c201e10032442000d07098 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 292558543 1250 292557293 292557299
    0x100e010b0117070e040f0902061b0c06070b0a050604110a080402030601230d0303150329010e010603020d020f0d0b011701050604120c030215030406150b04150e2206 72
    0x42e44440c2c04543e1400402d03040341c800c6459041651000280c3d240c11280000d689101c0d600080407607100d98944542d66086040f02224078005011102c6c180314125039640c903015290b43d03902c0103410b0080c10781a425950b4400909107480c2e640001400c0c18450361103981d560084c103006005040240c4059000c2c0c4149400410004e103e41840b00e4402c46038041d1007035020410080103031040c4112011001c141c0c4581c1070100d190b910840b100050351056068112103180101051041140310183c6248407046a00420500258102ca141550400d141c00f40e070f10114404035101074400c40b50307840041200002c940304421a00d920504206609980380910030f00024941200c1e083d0a000382c80d800b040410042001c1d4105403042064140300e080c1c030440d519643d400213615070b0200c0e03c0102100500100b00b004001c0d0a00c50725528161801c0c5902255081c1400d49180d80a00d008800d82c0006c4036501205160091016000500d4000e0102050300c61800c3c0b008a1070880e11980c582003030400c5c5000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 292559793 1250 292558543 292558577
    0x103051c0503011a0a0201060b03011706090105070507021c0b01060504090b030f12070314040f08060903070f020907110f010f0b0603160315091b09051002070611100e010b01 76
    0x483c1200c4440901403104404d180910101c1c0c4d015440b20410340d0343e207280009030504a075018500038680307280051440801c1402290070010010507618050345000704015560b5003080542d0707006a01610450f000c0c00b000000d1000b640e40045c000340c07241c0c0c04100005060b0ba0f115000340300b694481d03403040c028540c2d52414103507184403e002c0c241c0c00ba0404c0304030f0b4403c0514940502030050192404040d800170607a000091039100e90050245854040d1080c8003800c0100701c1550014440d00088d494018903840b40f00104146410003880b900c08580424081c912504403c42035074400f4040d40c61440000403a00c0c02400201070b071640283c2001605140e03480e0030b0003074070f10031078080c8211101c4001810b0200c00400c2da2489117070000c20345010103e00c9160512454002c3d401071070514000b80e550030f034060060480d55000c036200340c51410340708848545c045211400c85849003007500e8803010141681d42001f410549071242180390100d60340342d84c4015042140d000f6400e0b00e415001c41203074101 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 292561043 1250 292559793 292559797
    0xa0b06150a0212030703061701022d040509040807140f0606011403161112120c0403030516060e0f070e07020d020723130f14130201081005090103051c05 67
    0x15900580c001d03d288000070701e18580250b600450500e000180c05444000110895061544445041c1c0d8046207000e0801100c555000e03001c180540d181003842d03039100145916101d98055940160850800700e0100100700c4c007940c8072640d22500c404488052403c00c0750761100e041c020b1003801e100e04400b1525035402603141181c1101d805c0c41171442d42e80c41640c40000b915414142c0010400003030706801d089602406140f40e8200d44980301980c86000f13466500794a80003815001081c0030401081000942210840742c01c0400902a00a40045400d06000406095a0320501d5004103c00401060008182e0401340c400e014000704d040d488044d812030750340340b40000031000b50340035413030500800400e4201c45105c4101d24020004600085011031501d224112502e03a0454aa0b488083c0022a50140070010922451410020b191034080301210200048019041c050f126011942d03960440850700d014000c054894507103540d4a18120b6918a960400180c8112401e14030b00501846841 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 292562293 1250 292561043 292561057
    0x2030a0501050105180d1b0b0a0807030605010905090a060b0a090503010e03070201020d3204030210020c011b170c0a0507090c0f030c0e0a03030504150311031f03050a0b0615 76
    0x400740303104581c0a0501c4001841200240c807c03952082011b0341d02e104603941030740036107000d2050741c0d151321074102d001e040464090002001d06080c100301740000c3c0d07030000d501d40450b042211182039035154006500000c0410b90084444428006041e81441d42c00c12104d4045039010f4000b001040380590416869000b58600280140c0055002403000d52283c030316600b1001d030fa41e0381c40760b0507800e400507245080c0c0380c50000400341201040420a52800b01c10003d02c0340c015002500441c03e504000a100e26281c02d603000d4640c0d801d01c7d522080c41000f828040b50f1503100c0780010703034403098918000e5641c4c0c510030044825104058012401401034000e119104034591944031861441080503006410310101010130031950305080c0c4000d41d10030341c1081c0294060f450701d560380e500f410200c03100720070180e45417014141410100e115200284040300d51246024111240307000d10940030200e04c1caa280e00160151181445102c12300c04156a030b02c0c0035900071958400b580709680d58068560059007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 292563543 1250 292562293 292562317
    0x1b0d0e010b13180b092b0905040c02210403051015080a0c0311060705060f0906070504050a050d0c0f0b0c0d0903020f01032403080331060c020c0d0602030a0501050105 73
    0x101000090013902926400c24002805d860b010203a0055000008002048a503410303400080e02411150304400154040c010540301881020f00182000c2e50b203088a503141030601c0544540041220b501c142030714059580f0009135500d01880384014000740010030020303200c0d8903082c90005031400001401c107a44651181c84020300e06c3c61600d4a94948180180c20741d000b2408200c0540010301c1409800d05c91469003079208843e007084448146001c1c401080401880400c0205003c01e80e52030343c401c81220340c2105c0f001d4900340c0c140380c1600c0f40703142c55100403100590345001007044107051010b0030364004008210340081c40400801c80d80d210b0107100c01f07034004c994640d03c8440765202e500041010001c0303003007508896100c2140c40d1405805c5d5801548e0612007c411b0000b102e200640880d000c40b80c2c902c81420850203d1481e02d000340700b4810060050340d0710100580064000d202c0d549411034003c10030265140c031814010041e5004035601601186411b0000c202580208245c07001c429002c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 292564793 1250 292563543 292563581
    0x922050c0909011b0503250f02060f060d1e14030301061814010305040f0804080a02040605030105041e061503060207030305070c080d020705070506030702010629031b0d0e010b13 78
    0x402005e865552000c0c2c901098424281d9100303004c0140c2501d4001c48070416070300c03411411a455130090404502400454884a10002740012a036941141e40301407a00600403410740d032000c22842242c01444030009040c4c0030501d84035081c40f4408800303107040315200c0d201c0c951458020440c0300c502c4100c90103264800d0b0741081110743c0b00d5110307900aa40c003511510a902c0c040304035032030309071042d0050340c04a18190720a400350300450505008400c020308094000f072180c0c0c18070b42e84820310010340124080827424503441e00710501c912504000c0103a07038250f11245400b0f41302e05000e40654060642900800d0030300d03021440071132158805591441d04030720340074105607005031000080d41c4070300c0c0c0a640501c694000801c0550f2804011406107501d6000003810b02d2901e03c41c48030032032810f0078040302111000d4a5a40c0020301d03008032680710041c503142642905440003803991902501c0f01a00c84980b50580e074031410030055211020341d500448502d04440140026503040c4d84181104076004068 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 292566043 1250 292564793 292564841
    0x903020916210e12041d10090209010c0b070801030623041e17030a05090d080a02091516050705030a03090509040606030b090123060d020922050c090901 67
    0x851826207601c8a140b110101e00041c020701e400b45000e4544510569907100000c04021042c000c00800c0540041e0114926803440c200e002610741421911910040680016181005a1059150b1218150300156514182c00c10b09001451910240800c540315854040f600c94034410b442e401c8220044071035200111a0340d0b5590b20300c400c080701005c4102031450441100000380702103140b29186c1c144407100585030701d0321070006419502c002d407004015030000c003144e000b80741d0f0191085921407209c2e2405079441010001007040c01c18500713054401040c0100d400d6128000d21301b003600c0100d00031003c592184c0d4541d010191144100d00009001c030740000c80070405414490046507001d4040c00c0700281460b525159880660340480e07420300c4595442d484058112420f80f060f40008200d404d41001394038004011520011020030040d11030805a400180b089405144000000c05240300c00f2100f201103140c07d541e6844000480f0348038115034130001c2c030444414820b1440090b4420402c45044d00c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 292567293 1250 292566043 292566077
    0xb09040b070e130c1d0a0b1206030a0804060f0305071b0f0804050913030f050f0d020309010b0619031b200f0a1202010c09030c06110f0703030903020916 67
    0x140c01400c50340c000c812044070083c41c041a2141000600d520345503416480c96085400c3c003243c921070f00c0d040c442d500045c000d10004009000741c0e03001401d11380003201c090312000000707860701c90380c03960040c5000c0c1c0000d0007003281588014031110724641030300c0510103502c41d0042034500c4088855032150110403d0318075404541c540d410381d00b2440c001c0300b10704c0c40c141d00c0d14049400ca2808880040280503422511401c05070711201c006548407951811604209107010400d0b45845000c415184050b0040042400f404003035014800007507004201c00d40d1003060152031604604102c40e11030110307140003405c040100c004160444d403401740d581c881c0c0c18ac0398038000d040112030310a40105a148100000e0f12140c0804100c5111a10f0291026214026005400a00795001042c800b4200b060301001000003d12101a42003a15400e0824040342031360424254039003064024990600d03c21250004103054021400906607030094404041c155203c240745182c41000c08003007000a00490300b45201d0328 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 292568543 1250 292567293 292567307
    0xf10050d021209060601090f0608010b09120a030e030d09030812180a0303060311030a02010f32090a0506070f02010c150e150114030604060f020403120c060b09040b07 73
    0x50603000c0142005040030b008a402c2c40c0072a02035016500044c01d020301c41d030300244880020001180c94601c05030610348002c2130389406100300c1e0044030020500e6102070359540243c00d1210211070480302c2038001401c00a0004c41140600d90003401a101c1e03c840c600c1c0f041c3c05031000d0341d4002894500e40520490180200c80004007a800180301c0c0d00d10842c4180d60a01c180d15002c0d00907600400c60310f045080c106802040c554145200f80d00042c0c2e4500181d07001100711140344090b0070601414414070306074082140c0300342220510459600c00809d070390290303003025002e040d4003a1411084261500240a81c61041420103032510b0405565603005612034491500c1280c824103504c0781034242541c80005070340610b890020190014541d00c14a00c1d003503582d050040c144642d94244112008000c80d480340750152020f00020b454420106d050100c3d03804490056a0003039841d0500b881342d62004100407682d040c11145c190070b14400048074603090f84030078011908841c0c00d41d415101c0076000d81d209 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 292569793 1250 292568543 292568557
    0xb0402030f0307030e041a1f11070602010204080111030106121a0414040308070206060a09151e030c0b12010b09040906051302010e040c0e090a0f0504030507060b0f1005 74
    0x3610950480c001c00314014405024098803944a502e020030552007084161020603014450a204900c0080c03515a41c0d10003d4084000010504d03a44032070016003266041e150080c00c580d41c0c0f28022002850765030560050041790008002005070b940e50452007034080c0300a2081c0030004405908050010700d00c0d80c4511990003004c002d945010940d01d000c1400d50322049407002880c08503c040000b4941c000c508581c0c0310340c003440500440c2c68210002110000ba0b40510102036a07207241c190900c1d55110f0000e03015219404d15000950900348410005103280c0c0811601d10b40d150600054940e50380d41611141040c2c000f6620540e03090a1010700c650304444038446e841501d500540010030f000744070f81c03406140129144520000799000143c2a03d41c040740b41f42c021071400c3e1180d035500c1d80c80300c0010700c1e40e0411184441b640e1100040180503160000180b9855803a2070248070806812400510480c2d00c91740c811f010b1200c54008100b09034004050440d0040c01101040a105110ba40142a0303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 292571043 1250 292569793 292569799
    0x5150d150207060f0501140a05032508100c0f0c021f020118080903010c0e0306010311010c05030316260609131707060506030a1a04031e03050105010e01020a020d0b0402 74
    0x74000140c031140f0a0f24070340760404011382d5503500140b10076681e03161880c8400e2025034643c1d503054a0000800d513140548191280120707040b980d41400d40201800610043c600c8001b105e20f0740d1410180f0070010319019600e00c000c142c40500e8410301902540c404107240790020882543d0b5407903800c2e516450042c84450b081103559442c45004500c1c44e4013548000b150048400320340b6100580c0a050031141040903403010f0150b04441e03c210b969001071020305480d882000c00001100d084016118501946802442400b002c0104004a40494407c202c48840d070768603d42c0c85600941c1e601a0b44003a20b0810b0414400349000a5850900e55103a41c1c00c102d00142d402c15060143e110980845e45081c4c160a00c003000003540d10500209004086d00300e0b2003180603020300d55850344e50341d040c10840c610840b9465030603000a010b160107080d84505107c503080416405441c0c113180100104424026140402e0003049103038065440042c680400a501509880b01d00b5002d48030b0240d00b90300100201c3e4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 292572293 1250 292571043 292571047
    0x170a0b04110607030201090209060415050d030c080a0e0a120206070b10050a0305030d06050402030f010e04030e040e0f070906151b080703090342060509011805150d1502 74
    0x507254403440c008207030060107a800000c80030301ca0710401410380c0740074100c24440c0d0700340350344400c0052007110300208441086440c041020303a01e01c1c0c10340c0d0203400710002401c801804651803101c507400c51100b10612000b15210719402d40c075160705204100d92020702a4001c5018806000025000d0000070b8014040d805441011596880001d410720030980017110b40c1e03040410f0364118070501d4010000074090844040d411171801c5030307418020000c14400c140d084480100032500f894040c01c111444590701500500c4201d90301c1200740da903419441c9496503184240140010300300c01a1042900b912803030740c0c03544100080080c0c00c8660380d40c6a040e02000003e01016440040c22050051400c01c5c46a160341d0207103880d40c02c10104c1000c060304220f2a00e100c440307020500400503496600c014504800c2407003614407040c4101c004142981000f41c116404000110b00500e039a43c88280c24105d03000240459600c40c16032012480103030040c2c41d004a03000001030002011001d07030035402031040034014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 292573543 1250 292572293 292572323
    0xd210e070b0d0c0207050604050f062b02030103020f0405040b2a19080903070b040b1305060f220c0509040516090c1103090120030c01061509170a0b04 66
    0x70605038040400c2c54410355907031800c00003454040c03201d240101800c6500030700340b901d003001060728030010310380c084e12409002a0030309402c80440007400261102ca18449e0b034204c4500c2070780000394402e01040c0d20954490402044910f058081c0710b1003141d0101c0300c0d503507070303200c0403a2210000600b18280e09000440d00c1480f003130b44520009803505480d0b0f104501c042000c1040d024100b00c0300601200d80700d4104005030030100e0100011940c03c26440f4021070020745d1410300d010f03180160401d00400c0c40c01000c0038090b00b981c007103010364003404c60920b00b40701c01090a01da880e100c4401a00003000d451550900300602c0c42c2800c2c04130b07405070040703056680041408400c216840a41d03004a0003107540c0c0d0f00444016940801d50006000b09480114648031500d07001920180400404074071048410b0307440c0d102540c083c0241c0e605805260000e10680e42c5a1008042e00f0501924000000e0702c0c00c1c0c40040c6420f802c1c1604610f840b500c9003e010b0760801a101e00340a160300a0058820b010000c4800d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 292574793 1250 292573543 292573559
    0x10306080102030a020403110a0f03030e06040305030c1c11070302040e0123012610150f030c030b06101e0c0c060f031d0c04020702030127050d210e07 66
    0x844c4101c2000c81d0050340d55083d454411660280225458040c0c03c02003c14401508002c4410003a80d406040c0312130182030510010b85240f1a80c0c10003440340c0070200345000041e10004d05420b48004122801e40c50714503900c41150214440d41c0c042c6583d5101c07803c10070150400381e008007404044600003107031810340700b00605242e440c1c04403808649244c3c8401044542c03170f10f0381c4d420400b006400c49105030305640381210340e0b19103104e8403d403890365071500500c64040d08442458001d0040b4140c0d031001d25603c0c202980c0030010380c842a5400c4640000181c114500044001e295012588898091070b0310400146100c0c0421140202484000040d940c041540306102c000100110ba41d880d01d2640384240c01019658a241c803032050300303502001c0b91030003000441d070140c8041e029200140c9599842c00000c0c0504900840e564006201d1100922101c0b4845130200d410f0b030081307084966000903680304844484c444545c1118045001c400c0e004502c04940050190032a842c04807107203123840f0307403c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 292576043 1250 292574793 292574797
    0x90a02071a0f01050108160f112505060f0a080a0f1a011e020d180905151c110d06020c0d050d0e060105030d050c030c010507020c0f2706010306080102 66
    0x220500390007071001c21109035440c24595001d041c003031038403421600340300c80d03021f2540c203181e54088140842c2d1410050f0f801d00c103540c00ea0080c0382010403200c410150045140b192500380054034266442c0c100302117118207040c42110030449011815a2400c40d094a0450f516000504141c0f1100e403209680c070340d9000d80e8001c209420882d48003804081c42400d001521030f01d2511420b03000d84400d07800c6509125008180b6603034600d41410300c0b4041c514a0030940c44141055006049024584004d015002c80406001c0d4004002501c07404900c18001501058043d00742c60000d04940c0030703009054107810a084100100e510486000d4248800144503d08080b030051160001a10100302c0500203502d50280e40000d1040038003401c000d5045c10b011035201d0f610302c0c250000340318000510180c0310000300200ea085c0c1a115000300054240510000c1d241d400051000d0300ca03205842550350700d45400c8001603c0c03141da103c4044205c1c410703400c29204182c4001c140c90305140d1384040000f1400800c0c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 292577293 1250 292576043 292576073
    0x2030d03022215081311010806060c07152601060e010c05061f0b0a0503060607030912080702030706080c0313020105160c03050d0c24060b0c0f060a020f0405090a0207 73
    0xb403042d81c50f07048401c002c0942c4e0000300030307025004840f070341071000c140c2503a012a461242031070100c126581d0310000c18002c0c0b1030080000e40d18401c20b0f400094004000300c2180e100d4007281c0c2d41119903e5206004015000c031455650900c086101c010014140910301c04540f221040c1880c103244026034648504042040752203241c1c2c019000000c2c0100c00505e81d4101c05070034070074407040c10003082000c01412400001c0c40b031802203400181400a00d401229544000c19501140080b1003e081c1780c602c5030790304403101c128007034400c00c074005c1000b41c002c41c10702d4421000100400d0031555107101200c2c2001540b8810383c1440070402107480c4041c0c0301c10004111b140203210b01903a1500d146001e0b032500088010741410070180ca0300e460001041035900480100c03490001c075100d843d00c2e42c0360000408a40c0d10050341f070b10000030110f5041001042d01a0142c0001e802d8640d41c0d0341c0c55404901f80d100f6800c070520381e000100018030243c17403d03e0303c00b6000040d8520060400c1480d5544048a0004403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 292578543 1250 292577293 292577309
    0x301090e070b0f0d11040b09012307050a0b060901050915040f0c0f0207150504030221010f1a0a140120030307030914120403120203090d060b0103060e0402030d030222 73
    0x2803640310004d0640103c0007419010090546040c3c0f600080d50b006001d135900c842d0400010341b6111460300e51140350602e5002c0c1c114006991004a480d24503512900b902046a890f090340001440c1441e0840c0c01d18101c40c0060806022607175040030031108000c41100f40c0b503001d80d451000032078101c1035201b803414030b44003501c5a20284002c100302910301816a40700c544a1003030303914400c1240307500030103072400c076a41034076102d0080c070180d814442100c1e6400000c6483d5807900805003a0f14825030052011070f0402c92840b07600044180a11007518058000c2c2c0c07046c8200b01c1080c40d06544100c4400311070040320440309082181c8000c40d98110b03030050755010002a101e407011810b00201140c010b51041e4a0f400401c5140241160900700d0301442c4000b9048105980c201079000f4000d00490b411264002e2160400740300501c0e00740b00038000f1a00d0a40043c2c0b41c05d4001c2400f220240340346000e41c0e0020014043c1c0c420284040700658070101d00e1610b99500c45080000700002c4001c2000070385411 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 292579793 1250 292578543 292578547
    0x213021c27121211040509061201020c010203040b0a0507080606030903070209090601090501150e0f0a0905042103020703020309090601020f07030501090308150105070f031404030f17070302030301090e070b0f 91
    0x25a402006243ca08242080c1d880c909002e5100181800084904590302031f209907400e952820002181505e0070b600030002c13540001000c06010320194000c5101e18412080304d0300c151548041e45003110340c01c940000125403640041a980d14140016691007003001044038075041096000c42c424800c2a191040d05500c05001403008420600519002d40048501c0045000450900514568180d12260f015901e04080c9c48202d80741c0c80c3c641000380008200030722082c24140b40a0902c440442415038a4a00e200e000981c050711034000c80340866050340c011414980980c0030040290400351096041d4854641c1207000100d09001100095015200020b03420809040c05020307014018004c203544100056a1156a030300315090300c08450701302101e440d0840c040e01c0e00780c41003003120003040103404001c00d001081110062078000498410342001e60340b00000e803080007242c0035106c00100943c0081c80180300c481c00b560b003d4040e03070710410111480380c0d68a140300041c9a1222541a04603540 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 292581043 1250 292579793 292579823
    0xa0b07030c121b030507020103021e091002010b060d02030a0b0901080d081006091811040b0a110109021c051002070c0501080601020d02070924090204030213021c27 72
    0x5642d090215400a04050b40030314503940000044038100c540090a000e00446c103042075920a5042c0c0d203210101e481c2d07440e4103d035155031000c60750b08070b965081d1003510300b0b007070486210788107000e141c844070400f034221400c0a00c2c0d41820000303500002c0c000078829075a03c003101403030760301c0f40e401600a00c0e40c507000e0160000c0c0c13410000c14205008040c040d1203c1007100420015038810084000c0750800000280701c12024030840c1e01400340302c84101d072881c0c808500031803807600101c010600c48015490300c1d0160465040f55178240e49008001075400b4100c01c110148000d2102900029107109109844407011800302d2079003260400103080d294080c00403c01d01c02542c11840c01c0c1e4000310240010003120421600c02545c4100500440248a0312054038000c42d00035401c500c0340c85101081000206612290084029041071000341e22500f1844540c0c0c050380581d100300c40c900000060ba48440151904000c005450b090024400719038444030390200c440c510207203c001c0351f0301c550030603014007071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 292582293 1250 292581043 292581053
    0x304140d021302220803031b0d05010321020f0c041e06030b0f010501031a0402180303040e0a0510030c0603150e13050f03090d0f020a0803030907050907050f180a0b07030c 75
    0x350413101c12280c07802044007071125042c00016a0ba01421460001003004030f60504004680150307500c1100b042d041000100c00c000400ba00a901d0b00c0140c00c0c0d0000350200759208a0b540c0d20030500c0084540c21204c400d420f2818203412003202c1c01c03003208040342c540324100c210100311980b592081c1c80b00510541404a0302d8840801c4074014942442c06100c00d45544440a20401c000c0490714821680051100d410044495840d4162600101902d8031666074130038a100324a401c81c0c1c102c12003850710000034442c3c0c8140144501340c1c0d03085840004690f08055054000b0450010410032604c40264006482080d8090319881035041480d0014246403030f1030032a103014040980900c003904144190031803601d4450240e01495003104c80051070440301c0c0007240c0c1881d581d40000c034007400004200038040c040003e0040890784162000b080e960340d80101100c2c2d602a450314102c80d5102001030b0440750381c0222015086000c01071800c501d0300c1da034020540c0e0710351100c10210085951070b642001804 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 292583543 1250 292582293 292582327
    0x605030c09010e07030509010f090303020c0d1403011a0d0e0c031605180c040506270a0e0103080c011d0708070b07020f120f01050109091407080304140d021302 70
    0x3800640301c804a650401803a01040d070402400102090b594500181d00c03d402500700031040c3e240207604100402050400401951001e018600b00e445141c10400c549403081601d070300c1010480302d105056034202981000f0389003010042282d040f40030700001910440a220b034602030b8000c031005141c011240c10506050440f5010b803c5415805900104000e4032440c1208070300700030300000d808a07aa1011124003650280d40c00c0190480e9012448641001c00122480b2504a90420300d40b40200e29400700265101c032401140083c0d00da00c0010000148494090591a1504c50000ca40d00c03501e5600386ca0702d100c4940c2071183d541c1c00054108030303800302409072030f0241c509121035914201894010403100044070b40d8039805400001031041c19400244400d45a801c502d000034001561759a171801c01616040d00140c0300c15103240e0b0036100b1000c0000302c0104940c1d548015506181c5011607269aa6601001d85600403001c150f0020050b5904a0355041034284000010384955400d624401d4803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 292584793 1250 292583543 292583563
    0xf0302040e010b030712031e0806090f0c0706090311100c1206050a140a0b18090c03101a0c06041b050a0b040b07030903140c10230307110f01060503 65
    0x69143c401084860b071004204c60f825200040300360501c170149841c00300c0b241004020030300760a0f0100030695440590010840d4080c2d030003141c00c40c44e1911068100981d5a02c15520201c0d00c14040080c00d0029030a90441c0301d9480c002d00b00144024045072849003008180c42e011460f442d40ca1038240b50356074019600080e880c09104007000702c1824030011503a548a14000d842160020021144696030340c0722880c4003030403034101c0c030a886540d058016015000707441070780f6200380b00700400204031a014100b83c901c0b90010112a0315041d01c1d0042c49c070360104815190003240c680400c04600c0d00c0d4400c001050055118652298801c5186085001c40500c65003100f4460342c1e007180208050340340030003941c0c180d500415680365600305d5403400b920b01c00c100303500042c0058208541b01200000c0410f14000000c420307180c42d8041c2e0400070048401d5401a4094400080c400e00c0c00e041803d54100510307442071060501003402a002c007406403500000400074070050391680313028421404d05124038064 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 292586043 1250 292584793 292584821
    0x203070602011503200d1104060504090b0f0c0c011404050c030a02090a0507050d060b0a080c0306031023090a030908010908030a051b03091501080a08032e0f030204 72
    0xca062005071284503ca20000e030500344036410740c81803280401111461024028807494400209240034485604038000d0325201740e00d08507001809041074060100f942d80d20045d00e14980d078480d200401e00c900090442d100a400a0043e209200780c2480342c0a40c0c0c40030718454855520303052074181d292600034040355000390060780c451801a25403240c41500000d004c000401c1c15642d440003150180036604c0a0280581400b0000440541586c0202500004c80e61038403016602c1d801000e0031071000383c0d8035031307055400000c14484001e404c0c1e0001500c00186503c15225a408071070b8407018001c01c1e2000e040c160441c814001c10503400c110604010201e0b00028005044580c40380b5405000091024407017a4840c00003c50811090030038400b07566404a8880d183d04010508503940c2601036400102d04460600105040300001000d0443d0750744000290715542c1c411020442d0500291290b0394481030010400c041006100b010101134940311200a81d8103145004110540f401244401701c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 292587293 1250 292586043 292586051
    0x1b060c060b040c0c080c1507030501140307081002250c0509130812071701090501060e01140d02070f050604151a15090d080c0706021c1d120307050a020307060201 71
    0x280342c64024400d030302c044e80c1088640e07403900c2d4071241d05810000c0305001ca41c0340404800c10054075a0b00750344064141c426040101207428880030030300d5520806405400c3d5140c0c4410640c40e0205100d800510f17450440090003200301c404250040b8502814810449070700141d144144503038203041d40840c1e4000381c0c6145010b02403001361503107607491040e02c80307407015142880d000a816038001e0300103100000e40720401120303540c0c4da40c041100401c003e0140300700081d00c481c0200559031207494002002d408003030810f450b00407a1803c0d50003d51228008a85043d40409000c01154040c84620311541c01078403400361140c00b1040c1c1c54110344070301d0036089012030a0701300f4003116110320400d01c980304c0e50344005650724241080041c00c80b54589800500030040011014048080071410030112840c1c0e4088031070b01481685521070303070204130003900005603032206518034038200348069142e2400081c00722200e080011511904591020340c0c02c0e5016400210000c085041c02c01242e002002c05100800c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 292588543 1250 292587293 292587311
    0xf0207030f0b0705090d03090302031b030726032206141209121611030703051011040b181206060d03080606091008010306060f0506161b060c060b04 65
    0x40e0710010004002e0803001540000030310300740c041c2c01164040711008051780843e0886240c0184410f078240022802805002e50780754a0300601c2d1095900070710010701421809051007180c85000c10b804241a064004071044002100c3d028402401444041c15603406130292030309002c507090500754040800c002c121600e1301510150042565011400e4204032015502e6403281a4541000c400325060040c00028000301c444d01000c0a03c044c0764468820b01316109040420180c54203080e110140250f000b07415a40040b0070207074003c21211600b000d000c2d0034030303407a21203506150304203c3c4c803801c50a2811a030890300c0d00d010501004103030340381d40040146140c40f10100c2c8201c00e0900c001010b200d000c001041d003030381c0c03420140c800030600a0300c0036403c203100d208020030380d031401e11007038651501d0080c0206a000e8084420700030303070303401802003403401e00b001c0082001008454015141480d0803000b104080b6419044500184015607401c20340301c1071400c2c1441100d581c0a0032521540c03a102100c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 292589793 1250 292588543 292588553
    0x11060a0206090708030a0c1401090803011e080d02060f040f0f0303050105030c0a080d050706020903010203040503030f0c0c1507180b13080303040506060607080705030d0203071d091602010e0105160f020703 90
    0x8100540c0e0312840701808d600c04201c0842c05860002002041648084000b090980d208054404a50000145190020b5849400301d45620014161030010303001070000036412134115010030342041c401c07030107101d4100c41c80d00c54406010303804c602200000d8580c001003041e1700e0204030841c1242000c81d19203800c0703440d140190b607a6862107201e81c801e0041c080f90740c07000d00a16034180d40103d50058000c2d5901c3ca403e1618913161b900032038035100100506030100e40110946816100c03858100303001080307460154017900c140b090001b4944402c20501812400d28140a00a160001c021103101507442e0040500b546103400038a8200b054241e1082c0300700004a4400a0501e4001d801a1001544c8000078204050f9030701c640c0e50080c0c001d200008200a0b103800650045210320556690603122510480b02d24400c4102140361503441040c1c5400300f8101c4200119969400110f4000040c0c440e4251044c13900391002150403009500c005100310351403035084542103500c00250b1020b024a81d0860b84c1d4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 292591043 1250 292589793 292589807
    0xe0615070b0417210a0e1c0f0c0f0305031530030a080c0f04030c06020313050402090306061002010615020a0c0e09030307050c01061d2703120411060a0206090708030a 73
    0x4040002d440f00c002003980d900d010391000c0081450342c410390324140c40640c0c04a441050b50044c20000560200071002ea00f827064071850710040e40413201c245032030b0030754504643c650400b8003400440d050810305000a5520081c100070008418070701340b40c8007015000710309112660b4102c010a90b170410040035402503809131000c2d80c0410216140b40d1078141e40c0c800c007a458092500001c02d11244020049500c90f000006880410484401d88124a841e04140b1050b4080d10802c0c541550040c800701d5035625102d1020058000079200001d00c00da40caa40010060010310914400350300021180ca007401906d1980c28080c0500c40b04242c424108804160781d0b9120003010103042100c0404c040101810a4000c0da00600303103481700d0755904442d520702c16a04103080d0390321110b60b09540c40c1480d1540c20300d00d0300220b0750b1842001c0d50603c0205104586031980003003003191042d407001c56840c0140c0c0c401002d4051211660b005241519180102c24a414007982182d100e9510912a0754610307607101a03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 292592293 1250 292591043 292591087
    0x60303070f11030307240603020f0f01170c040315020309061902041d15030c090a020c03041802090a090902030c060706020d0c0e031204030b010e0615070b0417 70
    0x100c203001076040a25009040b41e2a80350f05000001e0a182401a0741d0254180310617280034151140700903503043d1040798024480250810140e82500c6600e15000c2203402d0026418106031000c00c8116215400817001160903041c02c18001c01d0034000d000b80f4042504c0381c816240d40451840c20114011966080d005110900190301e07500802250a080d405130740050003e507a060300117030b202d12400c1c0c00d1100300321540f035550701c6e04281c0080607180000340c40c0c0c0c0110002e010407105884085800001e948542c0c14154544400c00000402e041074a840078080c4c1190100140c0300c110060401001c00015400801d40a0a1400d01c2d000750354046052401400100c0d4010703941c1d80d541c034100f0064094207503281181890a05801600380c0c00803c41d4808240807800e440c1d91802400c0c2010385030140d0300020305503145102c014426003441407074058009000030a4464030001d03aa05022080d441800201c80c031003218018031040280c400d411074080301304950803500b005025440b520f4041d44040e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 292593543 1250 292592293 292592303
    0x3230c03030c030c0c01020406081816051014040b210702100b0406170d09090606050d0903140f0909070903020102060718050a0b031501020a0c06030b0a0e01120b0f06030307 76
    0x708480e005004c08469400e01a40b00039500e41d65240b01c040e200340300032a0400d00c5600040c4200c0240c84010440b0320300c15608000c080c40301800c1c041484045c038070324060700040c04020302d01e1841010000d40500010840860f0f520b43d00c02a600c201c40343d861407030300003198156590041c00a1190045031115602c10003000002d0841c8440f030002d00901034583c0600c103002e8030481c040400120208040074004c0c1076480394400e8603505c16010045074103620440c00064424410700103e5031054200203415400f034542203485e00f15552000002d03a00581e400980300c2030010b98040c050400514159128066082ca5550302e4699000030751580e000600305010002440c0c096044003a5098022001d80300c082c003020b88154803030381c1a140350b41c000d540c0d9480749031850389072044641c40062140d07091035110b10210405498580242e02070301d29280c015610000c048004640c1c00d550155071402444914507d940d040b0442c20714441e4000302410012640c0000c07810440d0a07180002101c818030b03400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 292594793 1250 292593543 292593547
    0x20010b190612052205060403080f0106210906020c030304060b01031e0e10050c090f04060b3013031b020906060c0703200a0608060904140f0a03230c03030c 68
    0x36207903104e041d050000701c0748890600c00042e4000d100300040c0c8207128074882e07151070405855040421840440920038078001501c03541120343c18900040404210f4100d125000c00c0d855040c1e5104d00c180c5c1c00101d00200d150707001208000a200443c000c050340084282020000c40742100050fa8103059400d00e020715850700c55003540e4504ea0204104282c24440c26000c2005081c00307400c568550384521049441000c100c40702607003a107803900c142c2d02221242e05540d0300d0100460010300c02d01000603d00d08140742442d420160140042c0040c511171060072070f414030729807190f24001d041020550a16500403c0342c4203400c005803038520304d05401c07410464000c1c1e141c1491404c0180741c0301e82500002d002c402c4a4815103054002c80030000c0000c0c2c3d04540b041c801035200d4004a4051500300c1d00a5441035590021901240c05003103116000c0583d0400d60790041400c03a801458140506821000240403808a074000c061900500c03844915418041c0e03d014400700c0d0f080d50b80e00010300240d01c82000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 292596043 1250 292594793 292594801
    0x30c040510020c150a090503070f0923040521090306040215040f090603210f031a1216050d0c1703070b15040614130b0120010b19061205 60
    0x8003c80d2102d000014011402825080d038000000c1c0c10011013440841c041c4000894a0f10b03000c42e120041d01c80049050102902e0310581d0030280c0f1181d400f5880303440044e0410400c0000e4000e040348900d008800501c25900300007000d034400e40310044100306024050000c1d00380d07640c020074a140c000d030f011039220004c1c081440203100d40b0310596004142c40409640c0000310380040f03403c11030440340914613034030041c011542d80c0c2c41071103004003442d03001890308000103040c140079510004130303004000600181201900040342240c030100e64a541d080e031042190401d00c11a003100c51001d070a05850b0302482c58401d80c0d80c906444401d000b10400d03200e1001040151100810555002541160f420b103043e0804000340c80300b2400083c0a1402941031030000306041451282c00b007618000034103040090002c0282da44000d008503001e16040204000744140070b103041000200d00c0310b216100015142d070701102040068415800140340007252284100000c0d030f08078400f002e890b21b540340082040e42e9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 292597293 1250 292596043 292596047
    0xa020f102f01020c0703020a06030903080a0f02120f060405070f0203040605030a18120212040e0a05070e130e01180b18010e01060e24030c01110f0a0515010b030c040510 74
    0x54a071a500c0700c562001c65602050000010780b04100c07802500c003c107001b504c85004030b050f211080c2c0c0142c00309407128045103402c18540c2c040218200103850041c284402e505503c0383c144000c0c0c80010640d2900c4040c08071b18036003032040c6500303c801b5081158084a80e0301340179440b400342d407007240c040c01008800283d0080d0340e6004420380c4503030b020501c2130b140070710319011045040d0402e03600e0040c03194034041ca40011544040b41e003581d1020548500540d500d6079075031301500c4010071100400c480011422040e444551100d19981c0d200788010130942501d0f05111f0840c0c1c4901c12118070007900c1c08000340803a501c103141d0f6400403a4105641610710700030324118058481070f81c24190a41c0b03007080c0092600300306001e803401421001d40103a16080c0009600d030f1406101e282d400c5d403581181080c290158041c0e810b1009440403503080d552902c42c000125410041000703070944407a0014003c6505c0e1403103004d0076a024101c00c0c0c40b401e06604001d0309031103050107180181805941c04649100c8454 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 292598543 1250 292597293 292597367
    0xc0f0402130303050c1c02120a020a061e0b0a1a070f0f0c1d1506030723120c16021507021003060609050406031a06060c0703050a020f10 60
    0x66a101c990001441d6240380041541d8011001410309000d20814680700782c21040c442113500800d80e006181403880112400340c1580328008841c15403150a12000028602c3d004414a036442142d6074841c00020039070180a1f110b2540401e84036000a010902002c000c0c80c0d01000180d48003003131251264030614040711402c5015a014ac11046a01c005004000b55001c0d944140d030201100726954031039410403415100030513201e08005e4410001030348918117120303003e90790001585c40c00940200745480d066806403440350b800748021745d001440c100b401d56441010758000c0c0038414610f280802c200481c3c0724607200c900c0024840e0300750383e1202a25202003015039584507002401d21260030008240030780204075901c228004202103040c00903051800d4802d000c00c40303400241c5540e40c944a0701282004410041151750b12140901c034841702d29604208500245200c1d400415810006004100780000c5e00459544a0346510040642030b941c0705550b05942d10804410100c8001002040354000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 292599793 1250 292598543 292598557
    0x1e01051b0c0901090219030504080313170a0207030501060509010b0d0b0109171e06011508060a09090c1e0b0409021602031603031b120c06020904020d02070605060f030c0f0402 77
    0xa620b5600110380940c1c0e0b94005d14580003801c01d03c65407481032076000ea0030307200d08881c040c000d503c2c180000307948000180ba00c002040d110b00901240c1604110384180c054004e400c0c070400591118400303004000091041c070000c2c0c1002c580290842d890710b80d46180c1381c818401420314982e218030381501d1a90181403284d01901e00103041104508151900903615803d001081800e68841d4220961840010540d02d050340ca0540400300c82d20340030b443c145d41c1c0c03400c06040ca6070840420040040c15060324855094401c1c4140082c156540c078000e0900c954100080701c905681c1407120781080504a0001100c045444994000da2140030b0080402d000c50f800060194160003104040704402e00d81c1c3c4402003c2e00d00c0303626440781d104048110307201d070301024080040903c91154600341c01c02d07004007600780a861160b0805407502a0200c045030070b80c0c008000b400d901d031350081050401c10202e802030690140007507a20f017042c0300107240001d543e81321148015008480c0d074503405070b0b1510342d50110f4601c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 292601043 1250 292599793 292599799
    0xb090103080d090b070e1003060303020d0e01020f0316050615100e0d0606080f0d030b0a03030809120406020c1e1302030612010203130501110406020c150c0105090c1e01051b0c 77
    0x84e51400b460302a04480e810500588200d1000e5269400035000344201001d8a400d6801000181c5c2d00c0d400589000502c4401c3c5415407103600b6a8001e00c203400c00041484903003080c03000340741c000c251400c50318220000c1c2011500c0a0641003031001c82e10b8075030030351a6901203841c0640b1107652440128001c4658110060001424142c007c511203e000a218a82141100442e0b22020302c0580072000c4035100c040d40c541c0711403000410004288512130940c1c12101c420f096945607078203a00294469070150b80140b000d0781000102190300d1615061012000d4a16002e801d5035685807400181c1c01c9441d11620785078140d000c00418200d1310764982e200c2c84003032800002c650b40d0810700407a00e1040d0500008441c50342c00c150354010307001003000584080303851a400424a900304002000711200200e0440b10585100707000c0f01140e24000d018103801180c0003c0503241003034401d001c1c0034080141d481380d42c0000c1c9985c010710f1743d140d074084202e43c6941030414444035102071100300d1034104041c002103c0d038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 292602293 1250 292601043 292601063
    0x50a0f05100f1a09040f110a0206060103140603100507050d0c090e13020a03060209010c2306060111030a030b0a031407060e030109020a0303030b03161d09010b090103080d09 76
    0x388500c40704940c0002e0303071403a441d2860501e64079910b5450740b001040309685540c0e4148490900781c20640c200701c501802543c40800c0c0c140c03071124920320603000340e032801006a22200c144000b41d60140309502c2403020981d000c0060307103401400310ba43c070501c040c01071103415a1840082c001500c14016600510001070091103510135411008200e96258000d0310300d4038a030708000c50b10924401c05030210180d405050948114690780f00d520080d0010140b241c1817042480090b03002030070845d02c0001036104144c0515140740c4400805250520050105040c0b110041401e00c0c0403000000fa9800c858003840c0c0820355102a40100e602101d1f00d070f2008103504a44d46107072040030804280e01042d980c441e5030304091041c801081600341c500481c4080d4101008200a2000ca8425040b0300b83c4e8200c041e0441380141501c8000c41000328a640c40381111400c664956007803a026007000c070303802409610003030040440b914005003030b00c10706102c01084100b000407281e40d047c1c030640041600e5600f001c0c041c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 292603543 1250 292602293 292602301
    0x3030603050601060507140c010f0c0501020f04030b010e0912090d080d11120901020a0c060c110f06011a04030507170a05030c012309070303030203090a0507170f0d08040204050a0f05 80
    0x5e441e58015031811030302d41469141102c121900060908501181695070000b484500c40080c1d98a04c40c1c404252440d540070802d04000c0340c48040100000d601c60004800b856142003100d06203031101800c03240d242c0d08411000d802d1a0010700941316104021a50028201c01a20f081c601034411064840e00290902e4941180000450050191405001c0032503203260f80d1031143c02d00700e11071070004001252a034a42e81c400300340313158080700040c0300900b001900301081e0700700310789000c24509440c010760b070010005125540030011200840380c10030b00881c0c20301307046945954644160380030301110742a48100360b2800d040c04005555001e81c020050301c5e070321241080160b003e40074440d8003503050000702071800c120140b1080c045100b0140c40c000350560038195070f800c42c00381d4405065070020340324115421f00411350501080c0c00801103002c44209a4000c0000c507810448994687d0b91190061540f141c40f250304420180e91213607044a00040395514a2002001014541035246106242c50100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 292604793 1250 292603543 292603547
    0x9120708010605010f050307030f06080a0b15040b0a1206110304050601030b0123130e2e05010602031b10061e0b030105060708130302180a0c02070b0f03040303060305060106 76
    0x205980d8500020301825440d07000558000310684660000980200006060248654030680001c0c207407070001300340e042d50b900b22645069500c40080d5041401c000c24000111041040501004015a028800c04000200041d4a24002e00c03643d11884081503500d42080f0f410790059070780401e40c101442d26403c15007401d9503101424001120380c1d0348a03c0011840c50809101658010390f000c2076440c410070900c040c459005110030031045215180c41102c1c100c40024000700d02d40d60a40303c0ca840300d517010281c03000a5441e2412000d40c0c020724000c01804401c1d4088225030240107401c9051203030307203020491185003514410a800d03c1a03e4004040345200c13140d03800c20910700c100c0c899550102e07103400c0030140314442031007000c4e4030007800c01030303500000d040304064905080d6401c50088441e9503900401d424407091604070f035400c0b81000c2001000c02d89031245011b10030144c03009065050031300041070110b1144c07039100224002d010001038100f42c82030f04000051070740f19003034403100c0d6980c00d80 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 292606043 1250 292604793 292604803
    0xe04090f0f030207060302030f0a0b0d061a090a06030c030f0309080a0803010501180e012c09010c02160b0703052d0901020106050301150306091a1005090c0a0903080c030912 76
    0x8800601036001300103020b92090095902824228050030315a841d0540d181c00103250350f05100703030002c103504403000110b10302c0d04c5a0400c1c0ea00b01c542da00c0d000c000040400c40311407801404041c1d0700c3c2c6094820310200d001c0300086429291b1000d006804d500301820165400d60742e59028503000d01c0384800c500b041004000145048541c280c80c1e061801e08000b82d20070320842140980b903403100400004000c00380e520311042a040710480b5000803115890009104c084004035540c0302c03036079111040c82d8003003641040014034038226003040e02c4a00d42044100341c401d10a1400c051f04124005ca6022416180031080808031545403203910b604010103601205103800c450700c0b583c0503510302680051203003818010100800f000040c2e1240d624110360b80d000c020010b400090703a400810f40c00e80f01c100c60030721221900412100345000304031450a020803885000081060181240c1405a09010758008a50b5400e8aa0040381a521108401541807440c01100d03140c5610102d25582c0000207500825 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 292607293 1250 292606043 292606073
    0x30619290d0908090a091b050318160503070806010614030606040b03340c15020421050601061b030c060b30070506120601090323160f060e04090f 64
    0xd104030101d680b41c0c450030032500840307480687c0004074280c1001884c841d400442e40000d00b0810340c0e034040d4011403582c1ca42602428440201500010180060303d010402d4000a068840050046604165005000a80703412034440345070000310105038640e48443c11789018001c0c414240c0d8482c81c01c440d0755030040400240f00c0808810000d40d404500d000c402801000000c2d9884060a11525507900001420340d0a070b42006598284030102d0203d00c403004079a40443c0d10800d00a00011f9418411b08141060b8421000d0109441c03021541c0c615aa02c142d5507560581084901c1c80214100f01c0042c1c800c070501160700912031012220a045420f860100c84c40030491440760300301e450680107590304054007880303138028024041c0d10503100c251403881d139000c601072510103403441c0c0d42d0340e40e00610600e4101c004619208500310b000c08a80803c501960910001d0240039014a0640959410100e078040c00c0d08200214010400720740796904241005070b070001a45000c40c445040c910000c1c00204 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 292608543 1250 292607293 292607299
    0x41e170105060f01050906040b031506070302030705100207231002030a06031a04020d300c120e090112080c060702010b030d0810050d020103090203060705030619290d090809 76
    0x743c450465100314140c2d19a0038010b0205031502c1c0c1490001a02600002c2c54042c101040c0481c078003082e1214400b402c01588650001d42d222105440c10a040403205100741c40c12074814070200c0c0101d07502100070540d081d04c0c620706241418011050b14100000359942c1c1d05098000001d0001c00700c01039110a048034010420021044115600382510743c0098502a41c04600700e00c405000c50856400345c071040c1d01c2076003a840c0e01141d030b80c060481103820051b4503002c140072030840400e01541008243c44506140341002d88150450001950310006000e460700c00203182c8250030070000780100b101e0800c070701d48040741c102c1c2ca0003003c02801b80c8448051180603000e280d0b00d48103054010701b541801000c1c0c40359081c010601b4413007800306544404130244d04040d06c0d440d001000d61424485a03005544583c0c0d40c580d030345440b500340415480344541a81080110050400022015580d211007040340041c0c51403850044269508413802180c20761007819280ca040ca4080140301d030001d040310801a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 292609793 1250 292608543 292608559
    0xd021306091401210209031f050711010b010207030605060d0b0103080405031c1e17040b01030203010c020f0c091b030a020703031419090203160f0302130908041e17010506 75
    0xb00c004640030760b07034101c5003090b4440b0301c811141e02489075009052921000f5088628070104040d100c4c000e940c5000c10043c8059030342041c481845d510250100f001081e502c000d00140c00c004d030000b9603541d010700c0b019103800c0c0c0d90000b003010340c2d581038072611003650060105080e80d41c40342000401680644140340c0300348150108800c01202c0c20f0360a8080303a0554071044a513003000b02009203605041409030080110f409951180e1b42c14810700c960103180128034541042d810342c8141400c65282c1007106007507610403041040c00403800107001081802c25a0340703254944608041914148012004224850011040044811455001e042c0f014026039003031040854111900d04081d009441410041003145024041d100c110340140107801d1024045a00401c024a8103000700007180d0000211038400321400c000f50f142503150b205c41d900781e0b92010024241c581c0d03911a080d01ca41e21856240c0c910903080446113042244448005101c2a04103040110710080441d0083c1000c980c094824070ba0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 292611043 1250 292609793 292609829
    0xe011e02010506040c0908070b280e0310051005130905060106021c0f050937060e04020901080402130e01150e100b03181c230c120d02130609 62
    0x1c500e070414200c84940b80a04259410801c070140076600c21942e4030b03001182500c5000c00642b4400c0d40051142455031007007811918242010b080041e100c8940130700600308400e0081031560211060115a021603040890705c41e00940e00d40585681c0c00c000c1d00c40d00030000006029a00802e0381445e0101c84000c41040041500f415112000306284220004005003c000a01d041c40c4e000c07043c8005c0032031585483c51000c03141070080180c00c102d902c1007010310820204403041e0801c2c8a0301c80d41c00d040b00c041d81440b0a4100081030454000c00c040d00c100e0283c0b11021001c80c407603000c040e01c841000c0080c803c07074400498146602c050751285c4412100c1d91000101c44842c4030034138009813a020000f0a2a5454005040d4010006030f0061040c80c0100c091901c500b0007001a20640030020b034071140700090010745203140003224131406070003100e02008070703d44080c0701003100c3d162481c1c5258a103403107010a0a03810001d0003004076a58a0700342d07445002c1405600071000b1401c03140225419614045 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 292612293 1250 292611043 292611047
    0xa02090c190806060903060c0a021005010e2d100302090109090b0c030a060b0706140601020f0307082a1b01320f0403030e030715020c010e011e02010506040c 69
    0x401c0d40206250111801c40c01c0028600c80c148031030f04100020060382c21301300c4840c00030b4200f10041e500003100301000240c4a42c59a0107021030203014244100c1007140390302d4064141c0c2c03060f500510a010398050b0f86134801d045400b900c0b80c40d84100002070b080c04a494900e180c0301150340305001c140d00c00c0801d2000041e03018250f0244681c401e80c0305c403803075005803036a0bd2a6811508050302004020b0f032104004912500540050f00c5414020000860010b2021445080c000c10241445046401400341481d1250000086801c0f00f640000207a90356290700780700742d54030007182c07001e41301440b0400c1458048582c00900c8860b5540181040f202100e4a80010740e045961645482c44030180c941c4404000810b00300700d51004000100fa10f071070829040005502684160411008502c0b0100c03020503c0c10704020030005404180c0e940b8860320307564030001e5582c09904684030b0402100c000c428441d40d1080b248142040300384240a544105480c0c1c0c040d001c1d00707003150400d01a514100425020714 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 292613543 1250 292612293 292612297
    0x50c0d0206120405070b3105090c0a0912110111010b0a030b0c250302070b0a0c12020709060f03110d0b0106050a02010b090106081509010303080106030b210a02090c 72
    0x1a038000d000d546040e0805a10400c10980144142c070300340281000040d008001400600f5100302104010100110103241007615501200c0300d00410b51008809200607180c0210441d006454075030b09541304c0081010845010600b030b000310906140019004041201b88407002c00e0700130090300c603086a00c000b070001900b240c904402e9a9844403407800704201080c3c40740d0801d0f0300a210f101d0098600411a4200390b15640d00c0a440c44100c0004a001400d0640c1070103500701514020101f03615003d0f80020041c010a40c2a00190001c2c0c0d80b1452801d070203000f000340200825030410103000451743c802003402a01020300c42502c03408400e400340401c80c40e0250001c564036034480200101a401c1c503400f154541c1104c4114010356584440c1d41d02c0135038510308928000c0900745d4483d45240f9000400d5860b08104649450050008400500000c1d420252080c19505c044c44c0c001418018100082d041886058940c208503204030102d0503800c2002c90a901118001e40c1c02c1c914030b072120f2000c50424 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 292614793 1250 292613543 292613569
    0xb0a030c0608150901150c020603040305070c0b07051f0e060a1b0201051b03070212160606050405041505060117010b040e0105060c030409020901032406030c02010606080112080705060f0103050c 85
    0x2044c41400140180308071181c0040e02d018261500000b1a00e850307011911a60095400f907011410110b243c0c01044400b854650140c50b4685d00079081059075039445a5071081400c101ca59a08416003089550719160300200400c80310324100c50701c07030520426901c000e02403800703000c0d039454100041400d040c0c01401014040c060720403240302c1300303e402200710469400207092442180101c2c0c508030001d041207070250412020005240040542c0c80c500721040b43c02c40c0e84a903003d1410a020000428050714401031280940203000c50a0f6841000480c0c001004280411078502d20200104503460143c1c0500b084d10f00a01c031004241e43c071601004582c0c01101c04100c120313801040144084120350700540b084030300604000c0f40300f0765031808221500c503000c0c40d1b04040881c541410050640d05000e42111604940002c104040c103161000780720010500500d0010140001c905081042544c1200d002c250000203584940c01d01c503501c0f1614100a100030fa4a92082042600c2a442c011502c40c42c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 292616043 1250 292614793 292614799
    0x18022a010e012a02010b0a09020a120504030c020d032309040b03060105061c020712030218040614120a140a0b16050313020102071a130b07020102070501050c010b0a030c060815 77
    0x1058081420a00036075400c1c3d41d80e41c1c1155207690740c40c01e80741c5442d0100c0003d00f4000070056152280350000a011000504001c0b86035030509041c48003207604007450302c0c24540c042d1104101c1d0003042c2001d0301d8464407071400d4400347c500350303035040d902c0c80020020340703030001007150140001c3c030b130200405a4541082c00307504d61001c02000002c4c000c01c07502c2e160343d845100145d000350800c00c481d20b45070049000010360801280c0c0000e4088040d02d41107400039a414001c41f81088000d040c10b80488121202c00d03c1d80c1c4c01a201108901400001080a40c611a9000300424100120104440d44543c5a404101c0396600c45201240095111401c0e0092a8200360744030f60540e0344038100300094810341c50069066005098000c40c914003620006550b040301d18046c40c3d51344e004204250103004156110078034405043c4100c0c230041c4c0c0d0210703008044400910303003c0e80f101001c100546c01000c001c201913a010b0500b003270010800a40b0f161000031203c1c50349809040395502c20f91030850f0038640c44107541c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 292617293 1250 292616043 292616081
    0x121503110d03030e0a0f060509010926090901030602120a050f0a0b01271a1305060f0c0601090f0507050a0f1107091d0c060403050718022a010e01 64
    0x900c0c2448840751032024040c0c0b802181640b030400c0f2250030000c143c10180d8a00b00903084490a118142c003c00d0f422980040080040410a03103ca2645110788500e071248903a00300d0a4003d00c20400d0705607081040014900060303965a464904001c2d40528002420b841c849000202c003091184100c0348142210112640d90340d0703611221034000c1031420010b5040c0210410b5840e809000c4242d0722000611409006441500304038409551440c082044d80844908228070302da24850514a2000ca80301614916220100c0043c13030b0b4100d000d01680c0000c1c501c01c0f400002210100c50f0481c00307101e03400c0e11007040b1a841c0d2070000c8440388590f0824401091580c05214907052064049952031030310002a91111a158121075080c0e92401032208501d441c048102c901500e0207014120500c00b04451103031900b483c5a80b0700d62282100d104031031090011200c08411051250121601c13021040e142683e00301d051030b0000e024201c00003516420b50300e0409081003210b014800d1801c0241c04042c1d505d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 292618543 1250 292617293 292617323
    0x301060c0b060d0f060c032403110109180906060e090c221a0a0503062205100606080a0506040501081504080d051009110a050f09120d121503 62
    0x24518007409000e481d00100a445010013052681c072810200c50301c9083c021034200c00020009095a0004020303801000c08280b4039440002842c0703102d81281e40c041e4044c0d04101402d80140d400c00000da0102c2c0180552010f04c0003058400d602120403248180410061b0588684c1c4403101c0050403119030300c10780d001c44092072803482c18564a0040300300c56070000350003016203000001643c130251019079020740d03092058880d0b40b9118034280d02410064004090510340307400001924914401506610198004030074280b15046c001040f0071150508280310b100c0d41d88070020040034003250081001480c0802041d0640703400d0050300c0c125040940180400c0281c12495030400902602c120b60700e140800051001c0303140303070040b0381c442c400e0f4903080d43d9054a0b00701d100058400d214030243c010321040002000e002c0c2c0010a83d281443c19001c65902d0708100c00109101c0d00300803450b84401d114242c1c0401d81c07290f12091106c04a104080c003400150501001521100c100780802002d134000c0f03000702 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 292619793 1250 292618543 292618553
    0xa08130806190906240302030c040212071b02041a120a0305090402090d0b070906112103090114010e0613020705070302061309020a030504031b0b06060a121805010b060301060c 77
    0x44080c441c099000000c110203088103400e200b031403038030f1006a04900e00f40c080047d440d05008140c06641c2c2510b00307500d0800d5030490301050820041c526014483e00e1401980c469006119048000381d0180003004506030800e4030242c400042590284113505515201c1000c400100d00d00c401d00c0c0c1d15445042c208180b0b001084043e401c00d0220030340085d02d440d800390101d1001c00c1c685025652986540780081d0519034001c05001c0703100c41d000c06aa008201c480c83e00302000d400c0801854011040079240e4544100080c0545103060300c0409101003040003113031030640c440e44940120030031a00544000c1d0303000503130010380c0281000074019400842c020405820200001c0c900000441c0e0000c5c80580c0313480a0008030b8002904000000b0b5980c001c1100309074200135011f102841107101103013655569542c1951111000f040e250103001d000c00d4902040303015103c0e40f00e08460b04403081c44a041d640f01216116000c40c10306460f198246860003125003403c00880341030719903994558240c1c003966100c0e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 292621043 1250 292619793 292619801
    0x6070c140402130e070801120c03020405060d050616110a05030d090f050f0c0406050418060c05090307080f06070e090c2101030602070506101203031a030a0813080619 73
    0xc0150070680812181c000907100ca0000009089522010ba1490400c400e0080240c174050300400d12418a508200d40410068031010701102d604a0f008102c1d56074040128100c9090100018a24400d0006110b41c60071442c0d984210041d0315940c080800c0403007805103a032920f800308080d059810800c526110400d281d0807940c1032a020300c2003076400310141c0c1e1b1450b107482d0a280c01f400b025045502c1000702032825009000c002d020440303040c0202c0f40138540030b892103034102000414490b03440701841590b43c0100241c503020540102a00c0c10030755a182c10301c0e204c206640c032060a80c082d21002920940c0240ca00d0000407901502040040c0e0303a054000355240c3c0300322951440004403103000e10386d55003d070030220b01031351080c0300140e03c90009152081c80e00c04040d00101d42d08840b000103000c01e81c00c121034070a8440e010318000c1070b501c0a15100280444807c3d03560383c2c0501805400c03030107101c038000c000c14607044103110307002c00d043c0d40b00304c003035110700c1c1c15152034140c040c000080143e01c04082e00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 292622293 1250 292621043 292621079
    0x3051e0703060506010315080f0d140412320d0c0c0504020307090e0108030a0206100e0f04030201091203020a020d020f060a09020604091103040c0f05011b0305090301051017030403021c05031c05011406070c 90
    0x1070420400d2076480030341242600f080c6104050ed0503441c0c2c040601c01e00070300a03005400e41c10708210b0011642640e40007035540482c082d10380950350200018074034902c110740c0340c1e00500340120f20440c40e50711444602e449900028054000d4496180030403262044200a4411650141d28541c51502c8014040d582044068015021036403160401310225485065104140c20152001603907280c0000c000303410540400280c8065401140561901d4640485c10b654402050719000403191081d100080c07103070103644c0118280918101240301404242002980030324042e00b014005260740300100d9104070354900400340005c0c0101440385181502d5052101c109101e07050050406244401190071120111081000500000400c03c0704003018500d51251440b201c01a43c1381909607001304103403c1183d4a00c0e00d00e0180a5000001c5c490140140c0c4e140a540000840c0a801503c00c081e028080a01500c1c81504e25610080800c1c5000012510ba456102c04020649440c00105c40700303400d41c1e10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 292623543 1250 292622293 292622303
    0xf050403020a0b1e04140109051008190908030a0903081b040506030a180b1f140609012109020f010e370303080103051e0703060506010315080f0d140412 67
    0xc1e10031103131090312020300060614000b05106031110070000401d002050380c403031806810075a01c0e0100850307101030203a50046089a0602e107061038000c0e150010100080050300311003000c801e214080d66141c000d000000e000b5620300300d550700c40811030001000142100075050f5001c103c2001a42010000396030300040070500040c211710300203003100a000301614203d40d030710400d804000b43d24180c80545448000022984401f803410816104a2101202000c62003050045a040746036031082512035850b02c5184000480f00b9034130318044000d4100060200d10800001004000e01c1d445000310450b1064018407120180698101c0352114040c0000d00c00440b4040764002501703612001880d000540c841d540d101401c1d03155080550400540b804410080c030b40040c00b00000303001c00604d0505507a00598005440c0d00c0fa0401030700100314004101c1074a1070b008400051100780130031000c01c040d140c101544c0e109000c022007110211074892124001860601050001c600100c1c540c01201e442a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 292624793 1250 292623543 292623577
    0x2f100905032a1c02010f0216172b0905010f0e010c02030a06051303080a0506030d26010b0403020f15044b06020d0903030807020109170306010f050403020a0b 69
    0x29030701080f80030b00c1c0e0b0100c080310504081100421540d0011511244188a20240540030b00700155840b5285592240d58001c200b0140c00e84c003d00c0d41401141c80c40d003000100d841d00615a50b000c4a140510b10103030074081940c0090000d03040d402140c100504802650344c40010080080054415524000d4141e805104110315100000c0e4035100e042d01032100c4c40d40c9210080d8080c90700400d0b0100080c003c6800d60708102c14040b0580380007649144105040c03e00c1704c11100c16100c12002c03d4031705211140c0c07803580c081c00012401c10400013002524002c0e9850f81d9800564410f01c01100401003100202110400c0200081048407005600352100c003110066071114403804104040d00e810281d0307240703401901c40ca075030518036003110100510583c0060200c10200300c03405400250244130190034000031400182c0003d1003948101d45060b80b222201c0d4803c2500340c50710101c0d81040f03820030b0100300828081540d190054056504881e4001c080014560a1410321740c0560040010052580f0030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 292625899 1106 292624793 292624873
    0x1806080601030803040f0c0b04050a0902031003030509010e190e130f0320030703020f0c2409010302040b04030501050405070608150d2f10090503 64
    0x3c404065126074950400084401440304020001410030380081841040c20015005489060740c2e80c2084c203880ba0303a0300c0200e01c0262001d040e85031403400c0c00c02c00a8460340c010840e444041c0340031040040e002010450080c10040b89102450001c207003400300740d1142301c2c203540c441403d040e00c07800c4560703d44a1504045241c18042d00304030200b203c8011751810316421150002d50b440840e076840b0110f0400039118108060714140b03501501450740c0c010300e04a0070540c0200c20b81c0c0205c909919000340e0083d401e5000c50301c024141358090100040c0c0680c0007000c2c0c0019030060002040b1843d20f840c00c5400e0900a03000681402002000d01c100007a10145054240c4010341e141740c4d22070090b00f0302824410360711444410a070070800c4c2d0518982114500102d034000140c0302031404500140080e5a201028056070340c043d8052500b078958500c0101c0d400303c941902500344811000 = true := by decide +kernel

theorem cover : BRFrame.Cov 292446043 292625899 := by
  have h0 := BRFrame.cov_init 292446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 292446043 ≤ n) (h2 : n < 292625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
