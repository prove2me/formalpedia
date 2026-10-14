-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1327
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:23:42.615162+00:00
-- url     : https://prove2.me/submissions/d4bc7ad6-5933-4fc5-93ee-ea04cbeabc30

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 238489208 ≤ n < 238669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 238490458 1250 238489208 238489211
    0xf09030e01180b040e040203031605160b030702210f0d02030a060b030c040e060a03140c1302030c041a0706020a080415052502070302030d02070e01050307150807090f0b030103110103 80
    0x3d1041d50180000d44040e100c0c18500c4c200191240d0000910358000e0a40c903210301100c01c000e20b000c1003004a02a02400030510b69102d00d9170b03d9480f0b032800750200b1203a40c401a40031002d4030081c0802d60403145520410410103901c0d005894110150030344c4406a2010659000002c1c05040442841088010142e01030303d14118180601101980d12541c031411054903246030104038103603203941c4000300543e40134102149180400b01126101c0d14a145c90074410880746a600c01e00a070a8003c4074861952100b12602d050f08024559901c1032182c1c81e469403c030400d2101e0b03c00100300f48010003400b40307035803111205071030b280c23400d15400322000798505015401d05090080040365006501c0350300900e0a1a5902241400c004918203181d517480079500d0300c5550001221944c0100d4410f0590b021a8002140c503a200e500b8560388030a64400c04c0d020211980c00c0c06e031814854910540c000516240c000d41503036039084030706407420070b5400880764140000700400030040c0c810f41c05010b514003804c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 238491708 1250 238490458 238490507
    0x60d06060e04090203073b070f0e01021e0307120c020a080114040b130c06120608120a0503040c0e070302090f0d1115210115091a0d0f09030e01 63
    0x443d440c0e14862168900622800725032900441d4589407d40d010604109100000c0c20900b0079400c0b1040103540072808625568840c450b900d00c10300010110181c181c004201c08501000311003444101003c20300ea80d800b0900c85a00091a4815407005640d80c0c7d03030320107030314814600400036440300036030205440b80c3c542085991820f0b0004d88466109030480c0c0c0c002c000b90b81e4601e04189008141d44020040108801d01040312a080110091070034105141017285944401049560740c10748030b1150004401409200c1c2c080b8468801194020300c02c41d102c0c401140e4031300680d01806401d0340e208001c69004103a200c0d480c200125076018544c011201442c00303003501d0300e401e403825140d01c02c0d0382d0048441c400c0c60398545150341c00315920000300010078202e034066a400b110307003207100303000e9810590108a1100b0f5404c0c411200402950b0b00346c0e20880800e9401c400200c0b9980c451905201d50320b803100442a0000014480d04442c2c038044d8035a20103002280b030005106604140310408201c01510 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 238492958 1250 238491708 238491713
    0xc1605070e250c06180609060b1e04020f070209010b0d050c181327110a0503100f090c1d0603071d090712051c05030c0703081302060d06060e0409 64
    0x50308540c0100a0342041c01c43c8100c03508004000e0504e0030f0320508500721304407a0394104006a84070050050041800b0400001700b80200301c0250792a849018200b5807030001c0e95000d180a0340144000c0003201d20340740c5000105e07030108400d41e1090340080c02030708000c200488240d10500920707901c811078621661420395810070020410380e07001c0889024814210803203401c1640d69204a003210030f5082c8607400c4284800204c4075903600c0e0603046401604450030841c1e40d04210103600c0680c1c3c40200a460030b40705040c0400c0081c543e02225070219a10f9000600104010700c041d500035000145000310b000c51103250340c04200038090030341030007580304040c1000114191070401102d203c1c070308070742d9400d5280e0482c01840c0c9075458115145080c811644201005000130381141046915004a841540b5914040e81c503408100c6510740b54900070851140024824030029a0243ca420000b460000050300441e015030040c111234864550348202c244400c80d0401c0300160074041c2150240040003071035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 238494208 1250 238492958 238493011
    0x403030f050d06031e0507080601060807050d110304080705011b081602030d02040b090a120b01051002010f0f05060307082b1b0b01050f0108040b0106080c1605070e 72
    0x1248503801c00c10042031200c0c160000da00100025a040f000041414034088508980c0d00382c8030004441d10701c0741d1040000c2568021403860b0407240b46444501c41603581003419511548941c076000c81140c2e60303403040c00880844401641c00f45004001d0240c5445141c60917600711850141d88615600e05040c2e01e2030b8055010303d84913807200b0360510043d005070224600703030700d54059a910140020300105012619074144005807150712001c84a10f150a50303218002c40c0610707680320010301004080d0700180281d0828031000b250b084017620000440030031f00b426407412949211408480a80c0720024003c813441c0030003518000d001c0550150901852003600b40040303c0078200d40b1000d0040c03514100c40300c0750081c07281c581d07451391082c02520008510f00d40403020210074015030b486441d100d00d603425035510555003103200c0e075030111151015900b003200940e1901e8004100e4006030004005420b100d07160341c402c007034900c3d01c00c600925646040100f040100c0b20b00501a20f450139203000d00f01d0510450 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 238495458 1250 238494208 238494227
    0x1141c03110c0306040b1b0c07121515030b010f0501120504050a0c03080706110a0527060d090b09031603031a0d03080a05180a030302030a0603140706020d05040303 72
    0x1410100380c9480400c0c001c0e401c00c030160422aa25000314000c000170301c420b518016200f1442e64082d0300b107502410f500500380d80254015141590b1103250103000c0c0b020300303040101c0c20301d00545941340c902c407840103a001a0380644140c286560400401041001100c41c11035000d46002464100b501e8202000248a203d500040d40030680c3c5510108086c80003e110b0101d00d06c2e0800c002a05103610307801c000c0c42d030341d0044170121000c618007842108034840080a8481d103126030790702d20b45498010140181101541c20b9100220003030050100301c9070303503548020810f05200040208492001c0d0404030041c0b4401040f02c5101d400400c0400c0989810241d01003089900d4100040d06011341034a02e40e801c1e4000d00026046111040c825080c582c11564484c424000003c051040c1c2d55400303540422101d06180c141f0003a4840c45040380000d000381c029640c010020080020340c2c940c0c1e516620b07c1c86102c0c03050f44581e60810714050201a038140489400080c40d4103205140514541d8002d04070001c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 238496708 1250 238495458 238495463
    0x9030a030906060306020a180812030f10090501150306050d0803010b07050c13020c0c030705062b0903030501082509020708070b180d02060108030d0b030a0c090501141c 74
    0x26560300c44070400c032441d40a603018541141c1c0454480b046a08058603a40d610795040d800b4034130208001400c2d060010f5602103a030b50b0030700203e0458403007040441076103601420000561000c81c0012031050040e2103040d008004070420412850102c800240450320143c0003e07005455006600000c13526103812281100c00090700c0517a030381002d080090425521100311503100321b008403d2108031459401800c59031400805940314800c02604041e503407001c9100e0703a038004070305001e00e1010b024140b00188140c034861400c8040c0c4425010040c0842e01c1c1c180003280484c0da10401400380d040100408088400101482d96901c03491001a148642ea948100d502050f000180b07101084501800da80c0181d900003e00486400e00680c907805521700d60391a680f480c41540081d031100344c4005031290407122120042c40c50051204000c801403c030b110b4241e82c2504c01d200749040011205000301006001c01c1c00e0000d41541450f04a0100c20b80520b689407007441e130a10401d05c1c00e00760034407000e840c07035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 238497958 1250 238496708 238496711
    0xe030903030a0e0a03120815120604031b171305030d0c06050703020f07050f120a08010512070509071e11030a08040c120311010510080a0f1a16020d020609030a03 71
    0x503540701c0001c000d04c40581000788011240d480041d201b40d040b24445e0701403d07410f00d0143c000c034110000d1010100c10b0200d615000e41c4044085004640a0556804100070003044182c04064603280d816641030801d1284110b0300001954103664900002100e0150400714041c0401400c1071000130250700d142c41c4050605541e80300890200d41c0281c1c1183c05035800c0f000c0f51b9403200c086040080e150140303080d0810f203e0003405100a26000e140c8122220392200d41c80e02860703642044288002d6040c5100310351854450142e0100b00359642c074441e03512070041c0b66112003400d0541c1c0b81c4402118052031403c02404064590b20350b070040c022090f14240d04251501b0840307540e640c1041e4040307242c80c0e40014030702071004800c2e1092540c40b20242c0f00d0805400000e000340d88500a807a07500700418410402560081070301c000000d015000b804002c81c0c050342003030051222201250180741c0c0300f40d03170002c2d01e41040c089644805070113110310b01c020591740c00035000c4c2e40790003003219480b44520401d0600f0107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 238499208 1250 238497958 238497977
    0x31b120706020d06051f0f020d12020d060306050f0a0c020a1709130f15120c151202040e07021903050d0b040905010c0203040e09160303081305010504150e030903030a 73
    0xa0343d55500010050400901c109110081d01d0b0f8401c540700030712103107040050210007103550441d0001903203000c0c0078001e6542143c4c24802400c0702d80203410040d1000c4106440e50000008030b112030007868020180190840711500f40500181e040383c0341c21030424203641011403e00040f0300e06490303500c0310580c0704141c0c965a804d9500040d000202e45240710381418940303555800b0401291b401865104031a003110501316484009204c100703401e03080010a40400c1c40c0d030900011201560018600005040116030071340015261410381e08160018101103403070b401000b001da68100501005c0c034013148a005100e503d01d4034014464480c0c0c2500e44c05241e102c0c443d4070410740361544107510440c1c004000f006101d40c031100094032a0f005204803d2002c16190120700410800f149480d080302c1c0c04145002b8151456606541c4510000d0403401845000046000400e00a0041c684141e10411041240e20300342d03d410012034843d090104080e6006009007a50743d18000103c800c251240d061541c245e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 238500458 1250 238499208 238499227
    0x140702010c0f060606140705030406030e0a0b09060703110909071b0b010803090a0501020304080703020d02040b27071d090406091a01050a0e04081b011d031b12070602 73
    0x44440103000240141d180140c980c0a104440c0e2044c0d0a07034030f0a039140386c0046070b06211812a8014071201400c240c000b0401002058042c0c0d10003d03c1c5e040e42c03415659208a55110f52100c50340c200c41400da10b411140c200621243e040c81003809a4044100c42414909010041500e0200041c030300410b000b4203040e507a0100082480d00b2407050740c000740c01103082da1a40130154813a00300140b00d501510601c040850f040d1300102c192000d0318103000003000fa00385180c08200d0a101d40040903608a969541300c601e042d11103030b501c480307100641d000401120007046408a00d410000306140c080083c007032400d102108492040c548100003c85031443c072030300d8505040b0000c00000c9002407901d000403c500013010340b9481c136036040341c10071101003407081c0c8e840c074950f03d101e81c007114020a050410031401e00c003241c0c0964592090780d101000000c0c040b0143d0b1508005003e404820500e503031022400c2c030440725000d025020420f0804024010038002101c0d9481e10f4021034000529803500410413022 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 238501708 1250 238500458 238500467
    0x60a0e0f0102031b032101030515100302060706020a1206140105091c0b0906160917100f09020a051503040807060212010e0604050f060108070f0309060c17010e040314070201 76
    0x4050352400180c01413400740c8078507a580e0300590b640130400c206003800c020444e14003400c89040704d4000000e8103049588540b64201e03a20000d2031001c0c0314812510120250702e648014040d0f95201d07100043c1c1d1861a8040641410101814130311124141202400f0000a40649045611003070034003507103d0f4540720008030070b601104080000c000c01422041d05000790050101d01507145e14040e0390303103925001c1c00f00c01c806200e0051000480c0d000303503080206122402e031040b00d0410366001c0c0c0d0160300030080c00c1820b480701082c0c80c2e16a1a205c000e0b850641c50700501003402072000f141c1c40040124178101280f102c2c00010001f8241e140042002c3d4103202c244d03011114a00b100d0014011035684070602815101000da03240f0703000b185844001011403501c01901405114141c6801542d960f40d881d0454101212400c0b440805482e0b11a1400003030f880c3c0038440c1040c1d116295a4611f14113000c40c0e22000c00c0c164400002000018244408260040b80014444011606a82d900c2440e0f000688 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 238502958 1250 238501708 238501717
    0x200d020409020313170a05180316061107081b040b010909021303030e0102060702120a02030c1203070f0203030f0604050402041805010c020120090d11030a060204050906060a0e0f010203 81
    0x20781a000100300116009030019060400e0710810b000201001c020744900c1c06801220700341c02c0883c0c0208070a01030401545075086850310000c0481e0340584598000c802006004d91041e0b02042d80c16101b120010782c03d00c20540a000c45000514900460300f040500e0003586100c102c6c081c0340e846d40c510f4941e902c200652070190040310b1040d9910340741010228207101c42031000b82e000521800d010181588081100380c01002c2c1c940c0246605801c0707080c1e5904a601c80f07031344034042d848104201c0343d8181091050f8003569001600c2d070750700e9281c4018068008042001c1c1d800c215001041000388100701c0300c0e11f081c0c1180007036030000f895030f076184042801082e83d0070710062540c42e44d00d103020821405400c407024203c040e500911900319400c00d07510030349442c000b45220540302406840a80e013000303c840c0c0e0545024001c003681500d080004242488100c071001c0d91b0560700000c00303100718100805c001e41c100034140d81d0940f9049604500034403090784182030740d2040046d07810202d101c0c0e10070015103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 238504208 1250 238502958 238502969
    0x120313080609153c09070b070f1101030f0c090302030c03030705031b010b0a26060c0a0804020d0614160207180e0c100908060108010204030812070c0b0f09060a200d0204 74
    0x5403840135440e101c065810011181541c0511860002246040450707041c1e5082d968040d401e104003080b241e9403000305511107400c1e1410581d0300d240c0d10b480c2d1041402101604c4440780c680d18900c50460061604100808415a019a10421541c40054400012941e00b0380390075521181d041d0401602d98050805c4401d00d5a10400030703000450b04507c0b002d00c0e03000102304030710802007501009403595161041160803e20140007805040d00f024040c42d5016409840241500d01c5100709a9440c0c04076041e902d8544000c481d20410010030005100c41e4081c0d00d05140024803a01c2d2030b1180d0340c0d85050901e404802d90686896500281c990100078100303e10700020181e003640c40b0b91440003022507081d84598001c46c1715100c00018050418401c0b1802d80341c014103c40c5c680f00381003902c45041200505100c00b0049401801404940401c0d19903000d040200046c11103814643c0140746481e40c0070b02400f4100345841100c03204019020050550005107401c0291240240c0038440001d000c0c59004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 238505458 1250 238504208 238504291
    0x105010e101a0405060a050306120a03120b010e030109030816020303040b0103140a060c030509011505030c040e160603051009050f240301060f0305120406080606030612031308060915 80
    0x1088043c0e0300080a10300c24840ac0c0c95606241c42201c20203035403012a034a01034085a07407907414102d140e0468016401407041814010095540540440d084910461003580007607100014002c0d4940d16140100c48502248011401c500b0942c442c1c0300d40b00705c10320009006021000102c00105010310042c010203412030010271450203010400340c00f1349030885116071103520700408508410886202c440c03d46402400624100c800e207800d001c0140540302d00290b0510445d552020a60110004d1401400350382d41c01060714100707001c819000c01c000b034011607002c506003020000c161100007400d0f50300c062118114000c4111401c0a140402e21912030760383c06501304500424140980441c007012288030700c00b11914603946500240840c011030240c54006841d0314003288080ca881c80107180c2140c0e009000e0b0603090314175107006146a0080c1c0015401025841082100c441c0030300000da4054010806000c1a42d0790140198005800600d00b83c001d4a01d2015802041140d0150740d1103095600007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 238506708 1250 238505458 238505467
    0xd080a090b040b040506060604080c060a090b03040c03060f020406080f15121614010f11120304061d0712030815060307050c1b102313080105010e101a040506 69
    0x207204041c072030104e4050782c580c40b40710045030007400c2160480b0200c0c0d24441c0901040103038401001190b03445000004100511901d010070100490360055000d14800d10440610a1862805400f0356038018030415200d0b00c180420400d10707401002c103a500c04002d214480c0356540d800c00040c159606c1d94141504035540d0140b03940004000240c810f02d094501031040c003550b5503440c0352216101c030035940d50700054441180c218500d02401241c0500c072104410355115440840520525410031101070307420740e4599400c500310b501e48030480d00c00c5042c0074018007410760901d49220f0300b1004040b001810412120001900000340c0c0070500840035005204594a040181e001461070304011814540340c06103407484900c514400ca0b00044101000e80202e24040e064002603c41ea00038040d408035030060b20035981c0ca40c40d4880300820801a8182840e1403090418681e03d085810581000340070718110018030a0030305135407108a088440c4094110f41d980c0140741c07003d00c81d014a6020b1038102c440450f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 238507958 1250 238506708 238506713
    0x12060402030718060f1e0e010c0510110711010207061b02120f0c01110a12050304061503050d031104030803060904080f030c070605090a020121110d020a080105120d080a090b04 77
    0x40c1704005004051741d4446011200e8a030590107400038940c9540440c00d402104000e41d40a81c00c000d00c000d0040341070740e584c1d03101d200043c81070303070600905140903640c00a40c090070002d503142e00d2402c15200f8401040c06c1410450301410910307280c6800719010980d9044c1c02d045694401c1e0b1b5100c0b201001c8252a07040302100880c5a0359a6460107050104610100504403030a0021b81d02c10f00a4204943d900d12a540100994055001800030b544c45904e5001031403051b19402d4400c002188203200070818250300400c000c2c00c4030310b0340304030300380c01501040204003069001d4166030704010300301c0c1c10b462681c0765451b20200d140324041c4400301d54103020042140418816010b04107140c0283c00a014541c0c1d0307024035603211610790000a002ca55000c0340c15090003d452000ca18081d07800d00c0c005040145c5010030702690f005403a042d25000d40015115000c035070700520140c010f00d030580d03034202c0304880103884a8403810b840c160541000701c0c11000502d20501d0360440c2c4800b6400c0000303220113042030f0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 238509208 1250 238507958 238507967
    0xd050c030d060f06090b030417070c090c090806010f060210020a0e030d0503060f1203030a1a061b010c030c0906050306030307060603110f1005040e2d1006051206040203071806 77
    0xf07103e010b000c101070394000070f42414a06c0c102c92142d43c0c06129850400e0000c003400101ea00541c4094800c00300700140401c54489034402c150074a8626118481900d1170000d0300c62030050141c02400c0300c89642c460810203c0d4000801005650366194056154011081c0c100e5400c0d1405586580c11321504410340b00060300032000350300852040d56108111140d110601ca03a0032491004004642d2080002410355016035008020704540001c90349074007403407a0001900c580100341901c030801c2c202c1c1d007040101c50f000d1150141501203070a06001c04d8551032b0016142801c00d10810707040c40000000540d044d50700b40b0490f68840e9129608000003a12401c0c450844811403160a009440303200e040d07281c0703150420303500c0c922400b03560b40c46141c54181703070341203030003800c098190103110000000742084580c5004404110a015030036840c050720f00b01c50783e0110b030350300350b4000400d01c54108581c001c203400416025034041c0043d82e000d60b680d10381c82401c40302c82280761a01541c001003c00042810341d0301 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 238510458 1250 238509208 238509239
    0x1c1b05030c0112020f2a0615010305090a060c05120603150402011808011503020f03060c04151e26090307060c0519050c15010503100902030f03040905010f08030304050d050c030d06 79
    0x61b88081c1041001030201a95500103a0366048040007001080742c0e82d61094001c0c6030310000640c162000c1d480315640e000300b90b402c00903890010039004207214095103c0301e9421580400704900501c480407214100365010f41c4041d001034100b060820314800c6440302104038a004200c074034020010300783e01d042c80728034020b81030000324403902c040d00c01500036180c005142401a00b0010700b2510341440c16500c044464401146842800701001c2908201050840001c40d28502629444108000d031411008044400b20307150184511140a00c01084800005e5960941d031220000441c1d4221034015540b41c00b0350700115150fa1240b1071828078580d4810b0141612000610481d0041c401c10619034501c0074007409820b80540c400a0b40700c51000c0542c004400890010b010f54000212000c0c0c024215402a000145119107802c010811801e1100c04840104440b1010b9411810155078458903201458003410801101050f000c5240c00d00740116404c1c4021003c023084029075880810810160 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 238511708 1250 238510458 238510507
    0x240f130e091c08190b040e01060b041509060203030402090403090b0715060603020705100f140a020304032d11071211030105060a1a03151c1b05030c0112020f 69
    0x3082c00303600340600031040140070f809001c580700c02490340c500ca180c0041c030b81d41000c1c030fa006858441070407007503138203120b0703940907290741c1c0400c0d030344c40b401c0200540c0d00c0350039010f0322400c1008001007006280d6002c02900d80056040350322080791380326410304407404512604043c0c054100012000c1c02c00081448501d0b0301007011409100055540300258200d000b8035401601c035400c14100d20b10030481c140d0007424844a00381000851010320207001c54001c008881190071180c1c00030511051581010304104502c010744884408036044030f01560080303000200050074052924910f2820000c240400c0e07014240c2c00e01d640c00c5a04960500342800720201203114001e521b00740120311141003200100d000d5440ca80c01c0c050042000700150011584001c040c04181c8090405000070350391b852010104090b034000b0b04a409540c50f003480c94080315444508595421034680811943d240401c103903039074490908042c0c0001c0f00c5c5006440c0648035000c0e185103042c00c0042e800b95907a01c1c1c0b090b0840c9405 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 238512958 1250 238511708 238511743
    0x3050a1419020604021f0207030303270318050d0c0e04020a0b0c03120f0112030f020f010f1410050312091804050f07060c080405040b04020c0a0b0105240f130e09 71
    0x1e1b02c070710a0840080d10342c807524006030018101480401c1c0aa0000c01d2401c00c81618200314404914880c903840d10000340440000c0c14a042c20061002d804111758041e100c12541c002480c1c100307076120441782c03031203101d1070602c60320100008040d9581c1881c184010103444254a03551002d0f40c0b070b0107480e80e01212300a8901c0d44408081031800103900c005506803040c0304c0601d400b0448a8600343c1d03541000075810300031482030b60590180301400b0300500324a01003030100451032011011035040c000d0002068501c104020302410003543d07600017522446c40c9045490581e0324640c0401050510084410b0340c00d0394a020350030311082010024130120310480300c009844186441f24006c4600003020300003c0d010320802d20003803189283c0355000a012000040c401454003c141800c1401d19012003800d86c0c200180400402032418080240c02d0b4600c071000005c2680401900e0343c8c501401007000016000ca40422450815192460940040c00076250400441d161002419a99507400340002e40d1a8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 238514208 1250 238512958 238512979
    0xa06060203030f060120070602010203180d020a031209060219030501050108042a08161802040b0d0b0409080d20090906090405032106030106050d03050a141902060402 73
    0x1403021090340d00800d07503484034074182c0e11000011a5500c5000700c1000745120305803d40100c0840c10000c0600400040e0005601c2c1e2400c54070100041000e15051002c130341007402000003040d404074120303038110740c103050030082d24604481480040c03400181c0180007500c002180b000e150b12400d00380d07c807621700766014801c9a80314401100c071048251401007100401c400c03081c044515a82c00f03082c0c0010451415244507a980c0d0415203450865074079030320401084003044c0050800302125441400485c030055290a1038400d0081c030a00c0703120084802c561f501c482c031201e00c1d55a80c005411640e0401c402c0d64641904181074070061149401c94404070354087d241100007040d2000380c801e09a0024000419540c60009000c400c0c14002c00c221023030300007041401c03110081603d0188c400703000c1e16110708842ca41740e0141400c65009401c040d00c1072810300700345000681d004044554000c0949490b0009540340f100c02c5049004888002d4404081c200319a04055400101c003845580200c481c1c0210 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 238515458 1250 238514208 238514219
    0x160c0e0106020703030503010e090a0f0f020a0605030112150204090606050c010f050f0c0a030b0a060309020a09020708031b0706060b1c1a10020a0614071d0306180a06050f0a06 77
    0x80d0300f0710b40700060204d403090004004c0f404002d00030950000c85541511a2949070350344041040c041d150701250a03034417808002080d8141661b20303030050015410000d01d1541090304c5100c0010700d10800030000800d0400d1b130240d0540b150146c2c1c00a0402c20018828140c66680c0a4065040721090442540c40c11100e0180359629001d818060300154440c030344c880d00d401484400310b9100841d14000d02d130321044241e0903a200c5000703890003801e2544e4001423000d01e51041103002440da0788110302050040c094000424010021241c01c000b9000c0c50409050440d10148668001c07000050000c0c3d1410000141c0031040380c1c01032440080c014040e02100c4c10980d00c04080380c0701c0d04040c01482c00c02800f1a12241040702605802801600403515048150754402c0140c5d02040c1a6800c0c503505003060200107608503401070407040310741c0c001544002c00c24000c2036842000030528080d14050f040d05a810305400e100b1510032981202061002d4944840300d01c0d11500b0a99100d48500e1820b20300261 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 238516708 1250 238515458 238515463
    0x6030c021b0604051003020915042309010501030c0219110f100e060307051b0a0218070f0e0a080105091f0902010206130501020f0304060902010f0915030c05160c0e010602 75
    0x30030400200b0803410241000188042c005c01e030703044c1c50309041c0d0811065010765100454245065016140c980c0c1c1c3d5800d003d429002c210307100c50040d00130501c0c1034803d142a6203c0e02e107503054840070710780080d1170744c090f00080385000a000048a804d0420100da102442191034070b01620071402e0703d91015214244040c0806910110384000000f01d048148511601d0b00c003000715044004c5141c400e09101d207540891070620183c1e2104551a400752000e103003113003003501d0000601c5000d110100058075100d08081c1c807650a06010b0410003402a080b51081c0e070b1190320310405441c90750f008101d549404501141e40303843d5a024a8043e030707a03624001c460080b26001e04001a54181e02501440c2c0314070054011840b590001101e0554003801460b1000c441d610255109601500c4d0201d2480340a0002414144500900e5401c12010135018012043c48040c21000782d1040e14001504d0b00c80c00c3c0040762a8003400300741203404a00584401d00340696000044280c80b03e44500e40b5040c0d0740d0b8034043e40d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 238517958 1250 238516708 238516753
    0x901060506181912060506040638040e01092003010e10081f0504050a022d04151202010e0a1526010b0f0c100603151e020d1506030c02 59
    0xd840c0f10031340b51620002006600000e820100240011503125207400d00c65040413026010b81500c240400e680d8445600380c6003002c0c5021207a1a1030500d810b0808002c8020b0700d2050080f005c0c06500d418007803036080180001080c01c244601406ea440c1e517110440f40100398170030740c0d0401c01c241101c030740403543d110046020715106944210807120345018590300005272100810940c1d0714010620f1a42c09078480c12054110780c1039525100c0c00c040c0c1c0c1e0b03032074074149550b0700095140103c1c42c040f80746502d5105218010140c46107036a0f9018152058030040341d2084024040301d4100001e01c80009210200d0004118103500582b82c0c0342800b00740d00ca43c5180013240042e007071640c6041c1001040368190940c0100903802092403117614144c0354010305440c0c02c0741c103100703405140c2d612101041030010342001500c4080040170113000d80c400d44080d1000840b80d190060350311990002e00d0104810305603003d007182d4007080180300d9641d03642d0880034005140c1d0105d0702d000360041d2440c440c0110781401194 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 238519208 1250 238517958 238517969
    0x4061d03031524090102070f0303120b04150e011a160b0601090305030c070f090c020c1908100c0f1b080d06050d12020106050612010e09010605061819 66
    0x85085039034010441e0301039408404015000300070003400341e100084500d1410080c036200348485503204c0040000919000040c1d000310b2445c1c01d805000d000295206040c07004d005a00703030011032142c1c95a00014010076200028504011001d14006009544143c0d4507040350303100051545104c0026441200764822041003152030350028444100144081c40c0703190300840107140c42441d41c0e40701d80d101c1c0c0c51a484880034014550200f542041003922200c9544003809120b0010b0280e402240c50203903448405504061003404000d0701e03459505c8a0040650003030441a0448035519026190640180010803081000940150203c0c7c132103402004650410498a2542050890300c1d807111101c80e0441c48421141c01c5c0c03a1440003030280e651042941c011802002422019034000304043d0841e440c9502c460b008090078030111800030311540c044c0c1e044440c80c2d107807601c060303803441110345c01000a900f19030b41c0b00202003400e0011040326203012003d0034050b1000d45401c91110441115a50248a030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 238520458 1250 238519208 238519213
    0x10e0703090506180f07030c080d030608030a0c051c050702041b120c05070b070521070c030507020402070c06090311090c160219092304080915090603010e04061d 71
    0x300d01107503040440f40d904d5040741400d4410b8031501c031501c035081c01990703071050310381408812061020860900115012052504041103180d10f4265074544030701030501c9441c1481106860301040c803c3c188448800c14102004443d8444038205002c2d100e500000400c0e03000da450101d4540d02250911a54002c85038551109402421406903640141010b0800c44007000010f000040005906017184c6002e004c40d5100c0680740c0380c1d801240003214a104482c00c0785400b4450030b02800c140c01c42c2540c3c010580628010780d6070012800031a02034070071000b004040141c00319000600744d07442100d40c001e6034840c10b14086d504402c48100000300c6003d4070850a000c100304214040d00d0040945882d64610103008200a00000d44900b03001200c0d6600148145440c1e007180d040c8290b00741c200c00c560400c800c00c00d15030350070191038580d0280250260180202160f400004101d55450146c43c00c10030003d01860b034079a114210003003a02000c0da01110000d060000b41c0110202e550704064030414100c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 238521708 1250 238520458 238520461
    0x90f010b0d110d06022505100c140f040f0b03180105100513090204050f1905010f06082a0d1a0904060f0212040501020a020606060309100515031005010e0703090506 72
    0x8000100324058002c40f420b81d82004590360300422980c2946c26070f00241d83c0d04407a0459414000d0400d01450000c1d0700f064034140150000380d07000b00030324551a40c0010003070746441e407080500c03241e442680c11003441079a800e5000a40c0c0980c1c04000d41c42100171012104290384034543c414280d80c0c0540c0d000c08189098a820320550402c1d246030503101c001e0000100301940e81750040b0b81100c80645801c26500c0d240c0082103480c25000c0e041c030340401030802041060750f03d001c500f1440d03100207015003070030811082c007c07071180402e8107a004071790202e02c84540c000c10a01c0110700c4107688051190300b00c0c2410000700041d0f001d62803010000b150400380000c035103a035865690900030300c448800103852a500f0f2150140c0069400140361049104400060340c54a4100f00685040402000c451041c0e60410030401402e001045140300760a221a010605440d41c6c0300a81403166210185900b600c1079100d9803500c0c031b4403038004134100c0d064800c0d0b00d1a40e03117a050086003907801d01e80014100350311600 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 238522958 1250 238521708 238521743
    0x9010e1e0708070e04061d0109060519170f0618060a0b010c02101e0309020310050603030a180b0c03030f01080721020a09090b070f0201050f0103020d110306090f010b0d 74
    0x206a00c841c00c4c0c001c1000402d03649410541d413441c2e02d06078080008004040060040100911660001d0b0a04440940300b40311010034031040c204c81c034001d241d0a0054540f4248444204118a040c13050340203041d15032a10b4034030324124403061200ca1071880c51041601055001c182c0c0d21849900c0981130350340d500c41404a40031b024620750030b01004c80422001848081807101202c0200f0408200d6a8001c1003c0b0045d004244c070f082e15512941c44280d01e44170500038203542c000204c4060086c1c500300600704103480c3d0100e03a0b124400341d00051064000164011204030040700940c410740c0c0d60940d401850f602c500e1130950b141c04602440c0d896500020071110b00345004803005d0442d0384000c128200098440c0d02c2d4000340c4010360412202d003403a14003840091500164059500b42041c0b000f00103d280c000c0107040e10000c107210181c02200301015800134415005a0881c49c2000502101ea80d4180100340c030baa200c03c90f4103241c06c3c03546080c010000907d018010b0f0b89031960040500f4a4044001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 238524208 1250 238522958 238522967
    0xf0616020409080c0c2709160909050f010b09130609080d02030711060105132019020714180402010201020903010903020d09080c10110a0c0605070b06060c070317070209010e1e070807 80
    0x1c0d20ba213031f081c0700b000c0e094400a44030300c84640203041c0224020496200c5440c0003480e00b03075205070044060341044095080c5840e034601c02907200340b00b0110340e403025000703003800d50041c030a01001601e41100000d00c03400303100203a0000c43c054922555040300450841042e16203414082c01180e50281340f03c1c9024a035450b064001000324100d0503000b1108410110300c2c010140e000c501c04980c120521444641426010300141006012100c000080321403c040084d80d00966400ca02d081016103030045002d40e4401d5041d564025400742c0201301040050030083c1d5100643d076244000208154000300340c14401203a42e29101901a06040b9910000841604c441015031307013281180c4030303100da8100400d89a4040c5e500401d01c98407410340d502004d040a01c440580142040d0103401c00300301d0308440ca00d000400c1c1d01101d030404007440441c0380720180301c2e8807480b50b070101a42c8840560300110391501e040c01800d009080c82440a00034074500706040d03007040700480e24140420b80c110b00044443c0d006 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 238525458 1250 238524208 238524211
    0x2f0303101205120a051308061e0f0105060a03090203010513050d03090b0c16020d080a0909020a0c060906021c06080705030c030601150e10110d02010b0f0616020409080c0c27 76
    0x685c20120308000e00d003400b100c0c10700d038281d1000495503c00300030310a0200742c0b040c0e24003004004001c03440035441d000c40000f02210301803185600400c00010031340250dd1103035200c040020750041c024403090901040e44007030248190004d8982e40102450344501d00c0c080d1082d41d40d2642c2c400c52915541da14044aa00942c1001c405004030000c9200e10400607940c018180c00ca00d03104040c5113071a40d21401000700215a6a0414000f051041007140c3c480c40e04a1754407444c1d19481600419a001c9500d442c102a00440150140d4105250410880c406541d000102a24510400c03100c566503140105681e801e03d40c1001d540503001440180100b0310241e801c905280d5080c01c11400740121103000c82e1101c2051a044030010740b03291000300c0001004d2154503102d5035244001e01a6490582c00104149080a025480350b680051362480510f440f2100540030f9030001c1080005c0c005c0703414100416400085075081500a544002c006031820480c0305a40341039603407118205180c0ca4003060000b110 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 238526708 1250 238525458 238525477
    0xa0f110a06050403110105060108070c0b1b0408010b041b0e060a0207030b07050a0f02120d02090310060605030415110a08061f0e01090906152f030310120512 69
    0x120304984000c00d64901803103004600c280e641d015032801040c5003c0c211640600003c0c10001e1003800c0c8002c4a0740131185051554120703981c2482ea4039842e440900800407403c4000c480d0201203400142d07504198070904849106403000c0c8442080264500c135180c1d03807641850003151b103014a01f902e40c188000034204d00550381c01100e09403512900c6000c4580c20440d60348000400000318902056030140c036415001405000414000c00341804608a42c00b518030911700c1198049190700320750781c0401400c070030132029401c1040380c643c54080080c90b13075000311411344000f451440d00749040340442c490341038988440c2d4003d42c100b4a0400080300c2a034030180074079622000c119425403044030701003030101d440310207034482c04500c501000000d450404031b9804403062a03d00042080340c1c4d4410031800b00003031620300d017411001c050028132800d030401c01080c0e500898503007030f25000d01780800002076000f5600d140803411030ad540c40c00c5840c80d2000c030080c011310f6508200580303a04181250050510240e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 238527958 1250 238526708 238526713
    0x60d020714010f091103010513080c070e100807050105030c041203170f04020a080a1e03020708120a08340e040c20012003040c03080f1309020a0f11 65
    0x703008990a494080d8400c402d86642d443c1c1d03807000c000d500140e820710404142e0081c00145840c088800380c03030000010140248000140c41c11000c0da00f40b1180340500030300e40c003540031410070f80e10308081a0028002d0840a01ca07200c00401c50398050410b50f441070016048152415051116001c0c812000c00f80803030500401c100100e0603010300d41c60340744c4a440c0080d0300920703902e0140100201e218080d440402550801c1c0300207004620040d4841201c482c1c104504e0780d50703a0003403400702e207809119440001e00e4020440c074003524103808401040708100c181c8da140010740f01d8007006105010060901c007d02812400c2d0b40040d18100c40c0b1181614210382045841c4545040c0410150f8584141c0b80b400909001030f030f129031520501541050665220082200040401e100e0000302002c100140c40740402100003800c000c1d5403003140c4007840d48100d4107034960b0945086140703150004a1f0b1803013a082080b80c0400e0024036032090327030844409569508414904100305464107107100341d000e5101d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 238529208 1250 238527958 238527983
    0x1060e0423011e0f0b01090b04140a03050d090305120f0a111006060215011a1608072001080a0c0f050901170f2505032205010c11150105060d0207 64
    0x16003040da0900e01540a034200864030384d0503901000b08071001e01e442c0320b050055592040c005406550151000d41e42c09902055003800d2110000d001c071406075100070003e01c141c1e078041211560100705401101c1c170882c00c40c1c030034a0303000c0342940c101d01940804000c0b0007805c8c401b88030018410422000c140381ca441c1540d0b802c0000000081c21782c0c030550001d0300035034410614030b5101081035224070b00400c0d100c000041d4a180310b0101510600c5800b4001d0440c4040c4808401030040c3d0324101d030b018a5105410350342007482000640da100c6980c120b0700d40850303400c90008074448a0360041311811b20041d554848051007045e02551260005146a030400114689240400040c5611b61b40554403440004550b8031301002c24103c0c10a2000c404a41014075940400505030000180d035000640c840060020748140110011243d08801c0080c01c950708125100c0c180e10b420000b81c00441c0491403c0e181c41242001d072011400d10203102d8241c108008100502c42d401040d03000c0c0c9041c600c0703610511040e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 238530458 1250 238529208 238529231
    0xa140f280906080f010e0a0201080702030421030f021606080c0403020603040503030a060f0608060103050712020304030c0506131109060118140a05011d090402030c0d050c0301060e042301 82
    0x40950030100030641c1e1180309011007075040141c04904c0c02d1000c000d114468403c160603888803100303180241440100c20201d1100381c002d005940141c900003070907480400b05041d00007810144000c0a60118610030000c0c038605101081d80d00140c0c6901c028400e20915200003200c0c035010041801031b004406210100c010b81c1e03a103006500070f5009400071a1241003500400080b0343c5141d20405081050510030841644c0290030345a210401f400c000440e90b4821209441380300300700840d80e002c07074400003c001c00c054016021000680c01001152400d50701c143c01a006a91085400392910032030384c00d841c402d40340c00c0d45416400038040c035003054203007a40c854040184510380c03c540035601149041e0700d207500f4560102c4000388070900c0d05440381c1300451000181c03103080005080c0030b0301c240c0740028255203003000002d04491018000c522058000d0034140d0302c501044070310b0b40c400c0d42000e00c0002c00248060042d07004d15046000d400c6580940794400392600c509200c00c40065480c2c02c491f401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 238531708 1250 238530458 238530529
    0x2010e130b0d06090b130c1502010b060403080d05072f030f1306080903030f010b0d06150504050906040b06191701031515081c02030d06090b0a140f 65
    0x1d420b0b120f140701050388886032800c0e01452100828a0f40003800300d42c8604085204514580c08844010321000418a50000300303d01510740340041d19045200002d00004006119008208020041008004589030380d2803c4803c800050002c500088030316809441362004400c401c11042028030450745040c4100031524110b42220f60f80d1340c16101c0f401802c211003074202d40159800190705c0061440c0d46400c05002c20000410700a90b80310f030f5400700d54040c911000b640610064007042c0100cac81d0a11144c60002c000d64041c0c0a024003400600f00400c58a0425000312030000b48010321070707030602120280255415480b0b20074001040300000404803180540e210040c0618021551125003841005016082c1ca480034403150203c0300d6200d04000015020800b0420071203c03000c086141800600200c1c5540240d140d8054420319110000460b10215840124841c2c002ea41000140f503480540e007040c1c8489114140d08501c500f0000c0104d171078407002c00d011441c0102c101c100c0b031001c50302ca5441c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 238532958 1250 238531708 238531729
    0xf0212070807110a2405160c170102070201020316050f06282319050a020d0c050c06061908010203091011040821040315090b13020112020d140702010207031b02010e130b 74
    0x40311108c661038113021030b9080740d03000c1e62540081c600a40c40d220061740001d6072407080301c1008c07810020140245003004418000c0e41c0141101004403201420800b0002c0400c0c90b0800c140503c140c2d241584041c1c101050207950207082a400c01c003590304151080800d643d45005103a21443c09512180b07950901c070717510400d805440c0b08079005072103000624100048503500b25103031052007018031544411036000100307640d01070b03c2075030400517106030b00c18035420240301a0005880f9500100030803000d42e8000500341074400c01100300b44601803507072040305c0641c4140e009500940e04a4100290791006680c00314502c8191401981c0c901036980d154024405810340b0b45032406500c0c5c030b5100050219400199070000c144000040c4c03400300941c0040d08a420503030090070020b8001c03d02808403220303644102c80715000d01c0310140040c500714000038000c0d80500012004254109241982840c0c01051941710320780c103071075132540340d0b91420400000c4680304880d10715040d200d25608900e03446207031100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 238534208 1250 238532958 238532963
    0x7060204140f0904020f0f0303070318061707260a0b090a0510050906040615080702010c02070e0a15080d090503060f04020d030f0212070807110a240516 67
    0x58840d414895071030200002024418403030800324500c460540d440c0c1e10050f030400d504a441c00200243c10001c01c0c00740c0c80b448180ca50500012500c0d0003407541100d0749008030210742c080b001d0005d80321007059070444c20350700b040d2030f2404010001801d554098044456410554032010f40013020920070821304200c110344803803120341ca442e421091030074030858040c2c0043c0801c03401e000718504014000000d081d58886c0d2485001188080344c0d86882c1d41d400030300030304140c07004070585100400b40a00701100544035040158640072b81c810946101260110550780c80d01944611500c44e1030440340505050101121000c002d0000050040d004110502d0103010740e07150b040b0514a07103420107003480c2008018046070f600c10020400143d640c0b005211982e031781401e00c078031008140d407400c03450104040012141003600080030001d00100c1006840e4840c8200096503205030300b6400d0010082284c03241c00004501541e1910aa80444da0305844088261804c1e0b401c1c00c00103040c0400582c00303081e05 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 238535458 1250 238534208 238534211
    0xa0507140c150a0806030a0203061b040302060d06051302071707020619030606030c03060b1608120403180602010905060f0c090d140c01020303011409060604080105091516021c020a080706 82
    0x403c200d05812a603411341c4041d04a01070310740d0a41c960080794a070180100510b40040ea101010071540c0d408005480140d41c010709030b2515040307064044d800a10032401180c0c418100055450200141070007150025980072070080840d135040040c4000b035400400040764403034414089404a402400d00780300408100e69004030390755190000107012038009440103800c150409070240b10103003103032040710750651094081c50560304c124100081e050264151200d40c0030068414801032503440402907961008403114240c1c656628101a4200c2e895003c0040c090b402540026605404903812250f00c01109400f5a02d4101c072440028004449824212880206149501400d680802082210050a00065165506001350040c640b50b030042c103644201601c2d0000751036500c809003964010840130b0002d00c498200701d8080740c1c48003e004507542e6444280400030b42c610300840c1c40c0350000e01c02ca4024151840042510210320f02110070180290f00c6800e0842d800501c1c444024140c0b140103800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 238536708 1250 238535458 238535467
    0xb030102031003021314060d02060705030304030906081003050c01080415090f051015120312050103112d0409140a03050714010603020f010315050a081b04020a0507140c15 75
    0x10042c0300c4545020380800c032407410010b5400d410061206c030b60003075800c503001c007003854142c800200e0b244203807800104540400b005210405400900017400e03603119445840c0369a032400d142c0c0707400b00090700c405003540c4e00000407007a0325406060705a1300203002d07600d00b180f0141c895600005030ba0b13005030b04440ea070814040403014894140301205400c0c1ca06803084c401100c00003815007542c001c9002d08011000792030014020140922141c2c6401007032100284007a60b96820180c5031503000825140c050141a9107120751035151440c0200c02080812840317000080c00c02c107100c002c0c10821000c48101c214458400e4000344100070803c1c4140c400c0d6102036582107686023900c40800c8030344184409030304000d400d000503610410700010000c03082c40c0c00202e80d801d9440041040d40c040e0702c04c80d000b000f8000c01003100c01d80850746401d44150404000902c554290a00c0300301e20a0740d50300000a10144070b100000b548160580e03003644c000030100c8018862045c001201d0381e80c0341c1122842c2140024 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 238537958 1250 238536708 238536713
    0x9150a020304240e060c0a060507030c120c0f0e06041205030c0d140904091e030504151d040504052113050f090406020901020f030c0a0c050a1203120b030102031003 72
    0xb030700448882c00c07034580042100c03e4500041e04660044400a100d40380100d0b440e4048142002901006900302c1d030180440e003008500a00200398100070000010741c1680b114032000d1a0340a440701c001002c0c0d4442c00954111201190701614142050354045020480042c0004548018211250069001c1d598800c100103444d480c02c00c150034a0401d02c1601c50b54100c01001410654124580c242ca020446843c2c61426807071420203502043d400c641c681142e042072540c880c01a1054400d0380ca107100d1194440c2a082c0c0314171910b03141522001440e07582c190010708040d0405a0414400e0049a03130b882c900e00400383c9100e0342c2c0c403549400610007042d284451006080ea4800400e000e6407030100f1420304030085a550800180040c00042c2c001600c056213034420400c0c9041d0f04000c0050765110303007240e402c6c80d0b1035007201041565440390046020030b981c1340030701120301201e002120f603640c0d0342003a41d802c2d52a503058840190784143d41d0380d42138a25860a00080d441a412203004c2d01c0700a0851 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 238539208 1250 238537958 238537979
    0xf03060803191107080d030207060f0e060103060e011e0b0105040506030403080405070b072001111f05010504060b190309020604090902040e030a09030b1b040b03010f080c130209150a020304 83
    0x214003c510303071041c101000a214085501290440c10313141c0540d40f111a420480701820250745010b81692406445170b805410201c0c034241a288120000c0c801c11848015040c02d8502e07001c0c007001c0041c2c145480c2809120175601c400355140d03040c10000c0c2001e541c0d0380012040e80088400750042205401004104a0180000c00c00b81c020613445c2814426a91240401c0c0000501448480a24503060301c0040e03000b40c002a80014080342181c80300c01204500b465040c08a0500e04402d0742400004202454680945019100858215810700c240804246201c00500d0500c000b45a40c0300c911201588408004202508a440300031814112904c1804201d402c1c11158880702e4009100c0c40690603405010841100e80014a042c002c1d12102402000000241c0380c003c0d24040028000a1503505200514101da10b05c2104030716140c1d403143c0b06601e8044a20303884c2e030b0002178180440780320949540078181084006d030110003078084951000701140c0c00081c078400964804941004281c010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 238540458 1250 238539208 238539227
    0x3040f030507091401060309110603150405060f0f0907031416120501030309050d0501060e07020606030d08010b041a070c080309130e03040501030c0c0c0f030b0f04050d0f0306080319 80
    0x503420801070529a010124440c04c0103009013003c0580702c0d5021418401000c2000b940c07200000c010b03507540d0514085176240c0d4540781491031b0040741060005a07071890404091403070b1030005001c0c0c0c000d011980d001c1005000300203000c44281580caa80c0020013000324290188030311099403406a19000410020700b410440b0208100600e040500520000350b101c98031408803602510f100c00040d95501d0311038003600041c7c100c00030441281d8204482e055000581c180181c500f41c007503403210503100200b03c4526500340100c0302100802c01007000708402d03600c0401e108140041e49542054141d68039584000c1c8198054409a0b2005c2100300300c1e40f27024200c0c882c50000881040203205086801c0a07140e001d02d104a0b41810343e56410620060700580185040c0c3d503220a2560003142c0711884803512110a0006031802c5004400040503083c8041385d29000d01d4108008100a0484210850308620072090940c20580c50700c03400a0100800c01c0500059440c1850100f03540d18502c2000780820320 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 238541708 1250 238540458 238540469
    0x815060a0b090d03030b030f0a1b151704031b030305190603030c06020c1f02040920070605040816030908120a080703150e1501020f030c0d2003040f030507 68
    0x100b2a10701a603031070350440b400300c80d410308021a086031406d001904000c86c0000c02007160051900900820282d5800200480d05004c6403c1405031075028007000c0004d80524003022401209030700e41d42080a0030300d1507100b0b01c285000078968400b0035209030030400b03204048000c41e89840900c0340310b1480c8407156488060369501003000d5031031502c001740400e03e13104020b0403a9500140c04002c0660902156044650200003244191b020842c03150080d4000d1040307a9101d07140c403040c160001c500c1120464100c200c02800760400c00c507030700c510000b880061701c01c1b03c08207810441007810106403052821101c0c001c0e212402800d19020400f420910303800c00440404204000308c21080d50401a13140d04070034546400290342c3c00071031000c01c039141d55800c003019200580c410040202d21070504804140c000381d00b903862084050b003903c1d540b40a8686840400c0d0058400340e6100c6200b04203001c61031284150940b0940e40700341d1424250760154101c0480c0000321030060050001c00c00c4071034000c10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 238542958 1250 238541708 238541729
    0x6021902071505090909010609090515010603050103200f03011508160302014d0c0a0b0306040209010507140f070605030705040605070219060801060306170304060503060a0815060a 79
    0x40204001845407140e090054805e091040c0401c0100e002513020001400503007008210724021801c10b1030740c07031100b05e88800b00e13085220008280305101e802000e0480ba40b2903240c0c01030102041e00341c00154400c7d8821600490440f10104a0303035001d00031043c280280b00f071440e1180c2d080c540c0369070502400c84641050700c0e1000c401040140d82c08410070040010004000b8818103104154a14000c042c084140d400c5044010107007210000c04210200d10b03182d9000c98030060400c0c014007040b400f0710b12964142d02c4e820b00015501c0d00f13140e00105400b040515005107406403a43d83c0602104143e0319103846a8440c610640b15100200b1560010b0185070809600790710380450001e00754804c42c001c960401a01180440464443d40c844144484084070b6154440b43c5405004000e01000d116060000e8100070000034041e01040609243c0b440d00340103546002c0c1840f8040c0e695070310140c8499003105c107408000a4800c1d082c02268258402c042c0c01c0c0601d03003020701c1000003518540e0007400b01c06 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 238544208 1250 238542958 238542989
    0x608010b030c331206030d2102070605010b04050307050607050607031d03030411011b0804120f050a080d0b01050c061b1b0f07170601060804050a0602190207 69
    0x5075000521050890b0003101d088140d10704500a451507029400c00d900c100340340480807103082441403c0a001200c1c07800d00d00b24082c1e0703110350805586111080a19006c00d0000c45040080d40b0785041044000b1180300000d0b260402c0d40d83d074401100d0b001d130710100c4080000b02d0284011310b410f000c0d840c002c0c00100d03100d07803c041d00750712180c0e280e81c03000e050101495a036207082c180105562214a10504014041d40d89034a0f1500700140301f040b6040b0340a00040d00000315004641d003031b98403010100d422802003802c180c1080c025200d00700c14010181d070440f0800600c0b0000031340c02c012807001e440c030031000e8946441039040c034a41598142d0725181d050042c180000b001d0130b0000903240798094462040e94a0105210b00c40641c1d5121720031801660220280680600072000071711428402039080c111000c0d9965502c0c1c01114200011100070039070804c800410030729100740d4030590024081c80940d00305003016034581d405c0b40d00040c84006443c0b18010030030010b5405120881c020008624840c81d00c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 238545458 1250 238544208 238544231
    0xe0a0206030a09020a05040c110c01091203030e0118080d0c050313030f0c020a0f03050c03060f010b0a02010e011a131104090c050403050d0207030210020d020a020f03010209090f0a060801 82
    0x1400300404001010741c0e9070743c9003001e640c1c1e0340d8024030080501420030408540c10050080c0411343c85150f02c28140301317501e9a12615440307440e90004941290008200d5110b03959411005803100188031a10b541d03c8e0018244442c0c820381c0d0307042c403940c420004c1568078440c072405041603d490761740704001e000081c42045030030000c0070415083c16515203815922400b0702582a60040c1800c0e0300650070204107c0045050309644000a05036030144089461030b01c19101015030302c1e0300c2105c0702c5500c0295100100107a80c0d00101420035151035000210721646040e000c2421a1140120004c10034030301d04100d04d0500701400c215065260901d400e0001d0440c0c2d8001c0176444c800c61181d9151250354100101016103d00180c40103503a00005444188110340c2000b5550391580c00103a1060807400c4000e90f805000140b01000c14a1035000b5042000d0103030200300c030010b80024000c0d050b5400f040300d003020b85e44d15600b8910405d42803000b400c05040100110f01101c11039040056282e24041d0103000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 238546708 1250 238545458 238545469
    0x902041b020109260f22030506010f08061e09030c01051501030513021f0504050301050c031501020610180e0613030f030e070e060d020907030e0d0318060c02030c030a0c02040e0a02 79
    0x4013000105c120396074480c01e82d1210960100c0c041c3c0c008002da21811301c00b208121703011444038102d540d444001540d442d211a4529100c480c01d82c0c908a2610360007034101400c2d1039800d541030384070980c2c04c01e681c01c0c800c880b0600790950b001110b0501e030b000903501c01007000703680510910f50000021900c00b400d13641d0702e50110700c0001000183d14070500401024a0405104070100c038080c0c10081d00a22444c1000092004070307800c10f07035900012001d420300ca40959440040d0642c0b0400c0c9042c82d034000c10785002c20410303500050415420040341c441925408a000030006203000e00d05170b0005517841034090070024200b500c69122101018105040f0400c4031000140200a0340c0070075120b54400c1d102c000016a002d0b03000c150003500544600c0400903550f800d50b0101060902000540304802194401101161220480c400000440e03400b01004203003a64450404180c176401205e180565882003249150401e0000400184c02b54400c030f41141010b0280c0390020343d0319001402e4417040c1d58001403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 238547958 1250 238546708 238546717
    0x5070c0b0a0f060506040e01180e030307030b030a060e0f0d08070215091603030507060f0204060801030308041b0b0408070905010e01030f06150b0c0f0f03030a0902041b02010926 78
    0x41c070680300c00c41d207042c2040d02d5011030020400200341e1580d559841c0702d81c01e0080402d2103513100c00c04c2c960300c0c46122945580150200164904069440d56a032400c06900a010841a0315010310441c80f0240000b00c0314403804245035013407001440c020284405141c608449070700900304004141c3c0034450010b0300012045010741520a09080c0c0d42c1c1e50f105c190f40303000d8403001d140d968084252030000516400030018950b19000f400280321103082100080d041c3e1041e84100c03000104120010800b00f44145609a00248107170100024460b55a9914984046681250003c080d0001c0d041202000410a07100140302c0b00d0340c00d0045626118049040d01070511000d0200a495040030f0100000d541c40b0100041513660003601e800e440da10070090030382002c800118184220350f0f02c0c03601c802000480383ca10303040303d41c02145550f945d1034075040540089041260400e888910782c0c00c50b100740700003c03c03000f11545e000040500c2e25090801d41c0b1494555034140900c070240c00050b0140322041141c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 238549208 1250 238547958 238547971
    0xf080105071106012913170309011715030106090c021612080a0908070806070921060b270405150412050a110a1203060b0f0301090c090e0c090405070c0b 67
    0x8400454171644a1082c01c2c81d032800b4801c14120000b4540e4100e286400300c0c1c400c0e07590b11090250061036078030035181d50b403080702c0c4054080341901c032902c42c0b40b4078001d11003640000701c0c2c922001096001d00101e802e45440e42c00c0b000d1031584840d19421020f074104003080b500b03020190200446840c0242c41d96070b65aa00c40090016000060907819890052410000900d25041120082a41d41030200c0d180c2c2402c2c1c0f00701000800810000950030b42c20600a284201c403c80303106008100c1d643c0b51001060b1041d41c8071b40041341c1144118888480c12142480c061400813030501d98600b03480c005003440758203106d20308172040180611000c02c0b1300000c3e03003459102c1c9041c0181e868610034400d403175602c805481503c540c414601e4103020011810108076028803551414000f254885001041c14010f959a51f104003409000400c6543c000307800c4060600303846d082c0440295291804000c000c40200c90031707541144001032010359420a480b800d6031194042c6000b542103510b41e9950140c3c40c0020303042 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 238550458 1250 238549208 238549229
    0x2030d031a0609060c07060305161707110120030103060e071d06040b1f1404062c150408070603090b0402040c111c02060903070512070f020a0f08010507110601 70
    0x1c0d1081d0f222071341115003081d200800c41e0481d55079001d005003c2c0c101150421505542240304040c028081d50401c00e4401048207810004d0303039458400c0b911502d07503198400079592242c501c0c1e40400b00e081a000c040f484140c001990700d60441c00c12109603559140b03507541c198044c1408020a44412a0300e403410358003081c3c0e2080300d4440100203005001c1c4189090381c07200c0c09200035110b10064047e5000c00380d0305511101c1302c180362081024031501491060201280045411100780c0050703445846c0300b002a00381400c00806032201095580c8919031032200440340003e401d2150718400c200c00c034001c00661400380604c0c019987c1d604288030000d0b1000340610749074038498900c1805041100356104081c2c00721011142240c1e000403039030146000f044094020384011541580d80803045942d0130340c1040080c1003034224000004c185600c1090f065a007220ba0800b80e00040e0340b0000b0401c000d00000c00800e12050074010060300715403020307000509121004003440c182c0b04c0003041d8181140d110008 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 238551708 1250 238550458 238550467
    0x3040e0f040809030d12050a09350313140703030207050402030c1606051807080309060307050f130321120e01090b160201050903120c0901110102070302010902030d031a06 75
    0x10444014050845803544c540104901880c54641c03040802050586040c0244034503203500c1c02a00440e01c0c508c40250100e040101030b07a800d44080400c11807118038505d200918007044803a000c455420540d082e282c03c209201600b014000030320700c02048a203078803003c1d040052031f41e035001c0d43e12013075481501d004035008400102180440030550b510f1f07031102e4445107508507044c40d00c54001c01c0b00b2104c40d043d488100301607500f850000070780380381940c50400055180c00070f001c04001103600000d00400c00c100c0100040e41108003100003400780802c082000c1c010311420361400101e84485400c03514900880e2201904195500245c00301d09658070766000a40c0d00000c6a0041c090661003170007401701e90203101400b076468034801000c1e2036684203030b008000549400c500e0640b2440340300400c0600020703901c089280b03045003c0c01490310900504010704109000b480d0306007179800105047d40540d5413a51b542c0e080d0f050034412101f4050b15482e0802c06441c0d0070b00014031500094804502941c800305 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 238552958 1250 238551708 238551713
    0x3081f0603110909070906090b09010903110613122607060903050c0706050408150705071101360b09011b080d0501030b0907120209070e0f040615020f03040e0f04 71
    0x404480e840c81c00600313102070720b25041101610002051090038002040a4400241a200d000a9483d0303248160f4550f01314904d10340342c5650030003c00d4107160f4040410000c0d8840b2511076811000203000d10f03c8010f140c030310f60b41000480d51282c0080380e00d5640240c00300f050740f200d20108880b030059001c6070000e200c00310b60400f200d00b03000300050381500e40720307200010401d83c2d00003000c3c10444154004980c10703080b008005080ca24020b4031000b02081090040c00000381d0050004200c1d44410314001a41c2400710170756408014080d0f810300b90b52500005202008a0b0b02140320002d4070003ea29146040394040000381f41c9500c3c0ea00040c80d4524000c459020084100b081310b2018070503400910165840e070404540d910002c0e20320300d00b14400c45000048654050002c4070007550020904411961660004e4030203880594006500c41c507090a14101640d41f072040e800905a10011003a641d007000901910340441054180f0040e8003c0c4402c011702c440c11103165503c25402e0602000e40c0d2100d2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 238554208 1250 238552958 238552991
    0x408030a06081234020d0609080706020d0f0e070504021c0203040309050307060801260a1403030126100b03070305030c030a0801060302120f0702100f060303081f0603 73
    0x2e8100d01c2d054000d421075494800355010162088010b11900d04040680c00302c0d11240d00070f03803448449400d10a04442e98090310b80602440c9442d0b00134200800d0100072130351400400d50003c80e08680190303010a19101d0303d82d0900c500104403218980030450400e84000d401c1d80e0300740e00c0c0729042c4a81c0d00054800c064040d070000800070140c00d6001507480741010314010f441c0342c3d140d00903d4003900c28443c001072068030501446048030000003d41c901501000f4181aa000000218034514465480840c1c00a021816208101103c1c800a1502c0e541001071144c0c400088000d101400158015a8000c1a070003103a005c1084611480000d08a20484042410081c0d10b07803014045e03006c08a00604407401c01310003448019600d66445c2e40c5c5a0b00c034201601203004040c20040c240c6c1c070f0301e40069480c03020741d040b071074200c201801140d810005a08401b025105545400091b107a02c1347c000b0020180c00c42ca03410340040071600c200008900580040e20380940030310a140400d83c4681000320002d108 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 238555458 1250 238554208 238554221
    0x1b0109060c082212030f140601080f0709060c030504150309050606010302040b0f031003080c010e010f1b0806011803060e0c0108070503070806010905040501060e0901050a0f09050606040807030b16050301030b0408030a 95
    0x2440000e1007d042c000700c6071412004112402804a611000020746103030764007080354400c011984842c0b6006050080890f441451000e04400303107c0c00b0040410004104803071010700091540e008030b803610302494000d0030800c010340304a042c54010300c410b1100291450030342d040130070b446d000c01c1d49960b01d100808020702d1706c41d440a02010b800141d001000c0c0e01c1034124104251012009010700480820031001b1115048815002582400801d19440d8400c100464001c4014504442c0c03200070724030f01290000b002ea1048600355640e4503800080700040c0200ba6110307209080c400c03981e241c03072140545103120050246003005078030800141240e0051204c100504000f500c2042950f840301c50250061074030310226445600b4160000420345041803681055038020813201c01c4c001e01d13108104000c2c00d00038081c903074000300c01d110100d41c4140801680c2e004502a507441038160a01e4040050410300a030b55a02c10048200010320115411000c2c1d1074009600520080e541d994144244000380032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 238556708 1250 238555458 238555481
    0x504020c030309010b0d11010518060a0302040504060816030f0c121518080a030b060903100902090c190503091e010606020705180105061b0109060c08221203 69
    0x40450421030545001000e94032503001040200050400d00c010442c645e112180d00a020b694601c5019a0759442400039100c0204d038041810714500d80c450000741d05070000000300000039404103040110f441c10340542001004854041c02c8455000300d86164000c03842c0c00301600034401503e2041c20040322440c1390f4003d04910200705c004c22030500d84042030010b6000f0318070303606060090741c040d000c4c1900054007401d9401220030349002178031381003074028110300540294080c2c014411904613403400d0240701e04208c4811000a2600e4540c410445400f002504100c480c190910080c1207451403442c482c01c50040714146507441780e031200d15031442c0c4000034104442e51980080110158501500440103603201c03a0203440c50039480b442803040c440312400118000300452001000b4504196004184401c2111309101c2c420020444440c207461810f0008c45440b50707210f64264050758032200054201d80c50034a40b01c8801850b40e4055403000000b08050403040038032000c0696035000c0e900000c070040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 238557958 1250 238556708 238556711
    0x7020f0d0b04150c03020315090702070b0d0905060f01030f0206090409060e060a0c0c05030904051003020303070c06080105010f020a062f0702090a020a020a08070309090f0518030a09050d06060504 86
    0x2d41881c021400d062102c0001c1d0406080006904465000b4001e883c450b0b00d080c541c07440344401c0b070780400c600390901500c13480560050f03240104240c03c45d00020445082030507070200347c0011070719046103010402007850110603821001031000946100e500e004e55038044411075110300001c00010003c0008a0740201a80d00e02044042041d001007102403064011140401110086042c15600c2910124009209070420000b455003460103500c8250401d4441065034891610785c5e0110349994400c0c4401d45606040da9010066964820b448070301520007840c1c041842901c0741006913842600040007064103407103030b845054038000070520102c040611300c00086861414004c5016030f501035603081c0d001e282004c0000b407401c0c1c80e41c000c44681040c81c3c0c0c010903501031b40d0f44596101e0340001038102d00b002810710000031004101c0c0a0145000140310000845050116091184480001d941c03050b5401c28000d0217900d540102100c0c04a40d01034948041840541c0744c001d00604954000c50b6006 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 238559208 1250 238557958 238557961
    0x70207060521090d0e030c06090d05010605121b0d170a0c0606090606021207050304030f0501020f040303033e0d06081603031704020306010302040b06090306071214010b07020f0d0b 79
    0x81d40e00144d920280e4003d43c0b10400c4010744601410344980041c110b050700f004003000f01003680d00701030000a10050090b17000250141e1554000b07400584020020400381d40700d001c941000c92071826512412900444550b0009039496440984112035110415140314001c121002d000d8000c0c44092440da5204902b009840c1d201c1103404000d20090266400520404880c0041080140120307211700703400000440c1000d1540d40c6903160160204411502550280100c221070381d84a0060001346200e5140856180d42642012080e00b45400125031180a107100d12020185001c100d6603c100300f080c00181c1d16013030119014050017a41d4010784a0344100b0b03072144c0a40fa10b01c0031150070790307100b690b41d07a000c100d41072441a4051420384001c0c0d4550032010041006151680c0311407111078010700341d40c0c2011842000281840c034100d90007008101190710250706205544036130313011050394030403404c829410841c103502180a518070090003a840d080640d0b4140d50b0b0814080002903010181511a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 238560458 1250 238559208 238559221
    0x519090f0b161404031509020307180603142409070f09021819060c03030902030a0b01050f06071a10080607030209040c050319050415020409021809070207060521 71
    0x200e1042c01d40120001d2000d425005900c0c82440441d000c40307170003006009020300b618400e41c006248551040780d06109040f00020440b000003020648a4401d070b1300060030502d54141780001070f84100140481c0d4222481d07100c080300508401400b050482c1d0315521441c1d451210315480e20110303420004010078682000039510702250010100707041062270780d4400c0d480e0362052002c0b03198410324801e110b4488480a00c5903d00c2804003440060007480e01054180d0180c001c41e0074040500403c0c3d0310307940007600500035828040c2070b0010809042d5004c0385400101c3d11155400d902800c890b982001703451001c1100c0c8488141142c0240010b0403d84210f41004000600207500880c0f0540c0141e007445860141203010b41c0c1078031301c14000740725598410b50303403a01440c0c01444010411100d13440d000100c80008029031000d000904210b07640144d66070710082c1c0142d0f1003210b280805104050303076403c110380d10358007144400c00c8912034101192546117500203843c5010000c9035906c03100205c5004c02c0314 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 238561708 1250 238560458 238560481
    0xf01080a0903030b0d05280b010b0c03040b1804140c070b06031c11060a0501030b0a0b010c0813061d2110050c04291e0d090b1602010519090f0b 63
    0x503440f000d81c00e01540d01c000005113401e10b243e207c402030a002080e400401007a50200000c00f24807000308282c9203890340f03a0003e10b54507089010891182816050380c0003036801c0510482c0c008000b1400e188a0030720782001c45040901c00c80c100200402034110204200751810030024080241003507080703061401c204401445008040702e800418803c66005c101502c01c2403040d1760603641c1003000c0301c2160799402c000f140a45410400141040940443c2c6004030b0300d0040600081211100009005417034104001c046503030a40007440e080200c55407012856460280740c0c804120f942400701e6a1a4502000c0b41c142014500181062403d220412000e000080024400d8800d2195900c11200400250300d01d001d40c8042d00040003181080b503903100405000c1039203100c03e42c1480d0390b454038040394440f60075540c50020450b8400d50400500c1840100e603a07004001035034500c000c010318900b092034010801a42c4000703210140c0d5844040051107440460207854582103140741350142000d4981d0103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 238562958 1250 238561708 238561723
    0x30403081e040f030521061311070f080409020403030509100c050d1103070c15110609030301030206070c030206120403180b03010905070203130902180f01080a0903030b0d05 76
    0x200000c0000380000d4000d040800c400d85009162201e110381a41c50366140064124001c0d01030381804400e21034a81c03a1500302c801c151100240c0702072034800e42001c80a009044038443c0010a80a0412218040c406450019190359603041500c0762614074890030114501d2280f074100002640c00001c3c044103140c0c010008094104c1e040d00c03e012481d00640f41240c194130540c800401c0303a04404200b20416200340003103c85915240141c80c41e0100316600e40ba6500d04940c4994802e054214030015460740001581190341d04440280010340703010075441d40c0720b04c01400300a10441c07010601c002449940030001000c2c641c054003007655030600403c83c0030b505404680850005000525a010b050f004551000460b4030311000c0300e05507402c1c400b0101c05031070018920000c522003400702d0503001c088040e01e4402405200750040e81c641d0460b200c22003001003014024001d055150700f00350b0130b9038060741c1300b6030011703420800242c10242490b00310068034400380748540c002e0402c815181072050200703c80 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 238564208 1250 238562958 238562963
    0x20d0e180705070c090c08070c02091504020910081501080c190e04050f04020f04061404020d0b0a12060c03060e01120201021203010617011203080f13050304090204060e09060f04020c01061701020304 87
    0x211496079401c0b000722271554915400940080840300401c8601c030282550380a6503070020000b504002c41c60022462020355000d40e82c3c00902c41600b8070490441d102c00480c6411420318014500d031520845843d070512400080501050100540d075507020b11680d800c0000640c020418001c600f403010159041580940c0c003640302d0103905450100c01c2c5854807402c800c84400d4481660203004000800000b5001100345060ac00e4540003555805e50303420007503101a08900300c1d0b40407898900e040000803075803508108001d142c0781801c01d0040e03c0f42ca0301487c0c11520000758085841c0042e100407400c0040b50038501480381c01c04000441d1094000781c4400100700d900b40025070581e43e0b00c0344140740042d40440a03002c24804004140003405002d101d90b880700078001141250340139595010703e96030080c2e100e500d0340755020170b040c441c10b5032042d5a0251080d00711900d2841d4100440018072214604000134800c50b800a074285003113100b90800d000829030881108201c0790f900034a40e01075032044808 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 238565458 1250 238564208 238564217
    0x91808191716021c080c07060b060d0e100501140d0204150902220302060403260301080604031209030207180b06070507050102010e03031506072f01020d0e180705070c090c 75
    0x40c0702e904c0311070b12140200322906035181c0c41c0ea9103421400300f51692148400307a0324035446803100d00c215110280240034190f40160001524860340039030f0f0781011071851034807441314201300c0100402c201441c00100c0203917040b10009a17001c001e1000078014070341c081c24404c0840c0300900000b24807806074041e01c000b01c42602240358505480c02c4119540c00c0c5400300030b6010700305001c280081261040102c8011880c5039207440240c4a07004074101d150026804061a580002e040104050780803001a0ba1510007207418840016542d5000e034984880c0e000b440d074040c0401032099509140da41018118800240441b5034030075103070030003030303110b0945004060256007403c2d04600340c0c3e100041101c1c4180c00c4043e101003c410000300b0000d40d50310008041c1d42454540044c110002264020b0161b24504164000406014080068100b040644040e0184001d00e14050300c1600d8081284618001c618003641855540c2030b001d9410b8051440c2c0031b8915490340c6004207220002c1e40c005400000d80303469 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 238566708 1250 238565458 238565473
    0x1003030908121209190605010306151202150d09230312010605090a0f1e2c06030f060c0703030b061603050306040609051009180819171602 61
    0x141e1542c0c034685400722980c110020400881c3d0648521002030700a00e0705001c0e205220030401c1e8445c888189600c0950709140c1d40c0c00100104902441420a0702250414114050b450100f40c40c001c45444030019005d1103480320b488031840c580b217044450a04002d0820040c6042d0750501402000001113440d10303c180d55030040b42268000016940c001c40402003109040e8245242110a030700300d810070540210107074a0104145400244890140030014110a04241c1c1c00b40784069122180c1d100d007900c0b00746400f1508898280000c1e10030303660f90040c928046a00c2e41000310b850031406000c0d501d058001c80f01401444608078004104050003950140120741d0340a04011962244c0d284510316100980120400240507001956100400600020b103007691500901d05548044895130705950400383c041c002e281c0d040c803e103841007c404591441c101226a5000c4580c031a030140d01108070899044021401c0c8a003e80d4038000810380800901410500310910415409070280400750003010b8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 238567958 1250 238566708 238566719
    0xb0913030806060304021c0501020c1515040b01080105040209060c01180c0e070207060f0e0306091c021207060e1207030306031703130303051305070f030309050904110f0f0910030309 80
    0x2a2802030780c0041042005001f150700302c0440705884101100d540d5000d10620307031400003c1c030581c80d1110588111044d075280c0f00b03910707043e0b190006043e40d100e0b51802500e800182d1307100410b1810b44e5016900181c1c2c030802840000c54074010701d42c40c2d0100d9800c25020341c4442640d5903030000c1031446040c2d24a0110f4981540d110a184d00301c0f50040141e0120ba81040f003940329240a0322030590900303000b560510b8003c0800e00f000d07400c81d280301255000021140702c00350320241141c0740130100e02c0500744c0505010141036140c407428201400c9a07131261032103240c1c124284400b400c2c004010050319030300c4c5001c1c600a8042d180038442075821525061079503902c510302100b143c2c410145642e20704101d09150740d0980003068080d0082141018040e19000081c004100340005010782034090311a551552800518211890700003500031485542800b0025013803605904d4007040442c2c1d598070f80981240071888166040142c13076882421a000d0194402d4003100340015030b0b009540d4540100e4031070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 238569208 1250 238567958 238567969
    0x303070204110d2d020a0c0605070804030207090605031b0f030d12050c04260c1503101509060c020f1806210726070305030c010b0a0308030703020a030b0913030806 72
    0x402140346809801401e050313880c15198020190340096081c91020104151a00c0c401c9813000c0b240640881c5800e000e100600d50100312040c001e285215040c4401414a8082500c4244d00d943d01d5000314030814409400d90ba80050500c1c2c1e045001d401c495105000351801006e03101c2c91209550640d28000104090000034012241520510b4a08003600384807030a290348050f66542c402c0c1058091034074a03031002d555144403903c100036141c2240d40c4901b040b5250000e0600241d00040d0700070145030100d0030751078003e01300130116821070605440c207103083e002040e0240341c2e50140700d91140c00004249a01c400c00300d0303118051001515007001034a09a41030020313200d030165010310b466002c41020848101030300d110002d0709072170a42d07101000518540b01440d00c41c450304200c0d5581c00c017141038494610309103e44ca4107a80111400d00001d461515a6411f52101800e00f00825800190b42d0814074000d4024409212016091586603c1c04416442d0001d0b40a8011030000c2c40701d001144881c54039 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 238570458 1250 238569208 238569251
    0x120804061b090e1005030d1710051810050409140c300a020303030a0501230904150b120610050409120c02010215070815040c090b03060303070204110d 66
    0x494684410490038078038800c801e00c40081c10b080c104140ca0740003003226101441070600004440c0c41d48410040323015190840c17040d00401028030f0f4002614100b1042d134a03180030800284540d04510480c2e207600080503038110303440c0c20560704603003407904e4401009040100480c90b010300e202550882c850035010403c410301c98507852500b18010300d8850b10390703401e000c4220800484c0303007088400101066001c2400c41e042140d07240380c40355071440100503640354201c0100c03110f9064200150054000c034000b0302114406000a043d45a00030000c44c030290450703001d4403aa2000402000b5240244c1150030b0743c03400110b03080e00864030b1100300041e0714280360084111460f07225945e100307001c4000400b00c0d0300415072030090b41140705620030301d0440005506c007140038000996919080e8070b0f1032160024007980007030b0000c0c0214035080d0404186684800a401507a06880c1e0007640c903242d06002901d1402145006075100b0314044403880b600044030300078410303008c0c0f64034140214044081e84007141240f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 238571708 1250 238570458 238570511
    0x9050702060118060801231e13030e120709060503030a02030d24090e010506010804020d030819110c1009020303120a06030803090309120601061d040912080406 70
    0x184010f000800d060210141e01101280000a61542d200c580d1425103103540781d61216940d802d81125140c0c1000310046a01c604070799407122406420040030121001c0061508042c0403001800b2001c0501c10b0003103c0c0303a030f08010100c0000e0442d09944548420081c414180100d190a6000815007000700c113403600c00700550051420070f814540c01c100940380589600090307000b6101d60441c55290260031401a00b5500c10004491030001085401c4450103403141d81407160721002c0200581d92100c02002003a8545421121510744822040c0e0002c204880e001029003040380582d05102030391f000d80402898078003184c888603d4a4080c00c100c90300c006020b50141c10402c10032010b4078850039190b800448032080000c400b5500e4842243c0340d041500d0170007a582000a030200f03149401c55688084410720300c041d01c101d52420b01c01410060414075074030309140450160b5400ca54542c1e01103102c1503003081b0b54482070601624010048070707045030700711600c515001090007145800f9400004400c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 238572958 1250 238571708 238571713
    0x30f0507050a0c231f060b0706200f07022404061404050604060306090f0e1b01051c14100e150d0c0305011a0603040803040222051f09050702 62
    0x840c1500031103035000c80c000e080c2c0f42d02200840d103c0d40300c24410012500c04c4140401740601c1c000342c40c9185514200b2421801c15607041c84014801000d410b0200c03024650711a100040343c0c0011455408401440c0c80384184000011440c5190760306a6401070101c18401c50700030a820305402c420b81e05030b0080303921603500640c0900040c80101d01034680c0d40c426000c208001810b00340c1c0c9000142d0964096000f4500180d25842c040200303943c94004c0f10012400c444045c40020707440c620440e980c0002c000010801d9a1032040c3c4005c60340207000312401020402200c0a920f140040340700040c3c90b003a12070076641d442d507500248415542008540650308400c00b42d80048e00d0b00e03102c0c00c010302540c500b581e520006503400c500000c0e5118000c8030046204e04008650034a440c9511102d00d10f28101c4240562010020040002c0500080341e0380075604903001e101e41a80e8a03a4502406941850040ca0500c0c01090041c24608101c041a85110110310716244070f40384e1a41405541c820396107040907a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 238574208 1250 238572958 238572967
    0x40b0102070b0a050c0a05060709091b0c0201120b190512061909150c0206100b0a020c0d0f0c060801091514090903210907080303130816020a0b0307030f050705 70
    0x80b07106500070564105c1c020201e61900380240c5035242405003e40d00c8101103212204108504a464000c0810504004c031541c07074803c04c3c1d40070240c07040071000402410027200200030703008924607a00008003400060a8210526100c20309200c10321880d005030781c0b0401d11060005d42c00c0d0000603a00384a00003040c0056604c046a1401d00098003080d4000c40e0004c0840f614901d410301d4a22503512282c3c15903000f400e030ba040048410303413488d0f0395800418000c0c03030422030041c3c113903000034900c0c080150903101d12011103014100450b0a400211000701400007040340043c4450380402ca0030305031a20100b0400c050100b00f215080168410321400e5465200354016030464940118126071000c0700340305503031074200b40038003a00c001840c11004200001000c414807920480400c010b5020740308100044d071641c2030002105682c1400250000c0a071000000c41681c103800d10a2a0b810042d030151904000a451301d50b0482c80d0b4100b1610040003d1400721100152455802038038014102c9440303107480c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 238575458 1250 238574208 238574227
    0x50402031e07120903051e0906120a02070507230612040602090d0506091e01050c1903140a02071e030509010c050a0203060f01050a08030415030f0f09030e040b0102070b 74
    0x4041c00144010180401034503962a20642405203a506600c00c2d6140c2d61780e5202503043c0c4144000007002c14081c2e007028040c00b0142d44501e422903440700c850003084a06641d882d140000030b84120040101140190400003418141e0242031010400f1500880b088203030402c814464540140c4003122640b061840200300031801c070b6030040003064006441280050401d88420b8500042540c240d00994401d511000e20100303c030680c40704440d40310000b4049070400c215050f0b610f0180700e8104414030549107410402c140641c0c400704c420481c20444521518100c3c5003d0025084070750140e9020303a42c140c414901103400c0d601d00b00801d42c5512a50304108524004540d18449110100c40a21903523200c4405a50200074180c85000350040d04030f52503041600f40300c1310440580c000d1040f42d01c107000c01d10179511010442d42c0304000901c0c00040c0c03c01f4807501d5030090006095001e040b40d2912206178149030b40329241780340608040c1c0d070500408100c90700481e0344160364480e07417414901c1400000c00d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 238576708 1250 238575458 238575511
    0x1d0108012901050d110301090c050702060409050606070c03110a08010209180a1e050103030f1e050703031d0109051c140c0106050a060e0a092d0e0d0201020904050105040203 76
    0x408490600d011403c01e0000030010701210703030a017035086988034003000400a41e602401180402401c03403030303c40e051000560203e8080c0c049c0340210b50105803984005040344d1103000507100300c1a0802d034074555240c3d407420031016605003c007009014101d4403030003091000050080702d50461016200689154402411000300100505441e030960f8441204e03904654002c0d0801404500b0110001030719459071402070180303c901c1501206004110007002d04a0344a807802c4c54040c2884d0034160364a8000d49030481c02069a0381c082d01d00ca08802c03c0180070311105500088495124108a0f02102602142c02d070b102480404c0000018000605094103008140041c0c01001900380010840b00d440f80c0010300b40c80c2094128200060784c0c100d2021880c680140590000d00040343e0801000305c24030250310354103610307400b440045c4c40030700d03062080a00241d000c042031000c0340301660302071039100704000d010394082602e06218504040010440745007901c00c03a4020f00443d00e0501c88490131030382c540c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 238577958 1250 238576708 238576781
    0x5030d0e01030b03011d0c01090f150c0209090a0308060103020f0a1b050607230a0507060506030705040606020f120301121e05060415051003080d0914071d010801 71
    0x1e0406840358002c20454409001d0055403030560203c5e01080e08424203118980640a841241040007401f000c10112406048480c251079900d608048408541c074019981c07107a04240080d0000000700400070070f00c2011070007800d0305200c2d13030720000117460f1140110140d000d012000b15400307070100400c3d12403900603d4210480421f0203006100034946895485c1859800c076510b8011802202c03108400e800311601044051504e5020203040400450f4014071501442034010142d40ea1940404c030701d0381d0300300709030b600901000744280070440d21444000e4035184840001e0100d40705100c004100c01d90100280d03816100090780d030030150205520340030403005401c2c5565960070703106980e06001c40d80900515104030f0180c80e000176002030540b1044c1c2102c100800c90144a20303402c000b840091000790443e03075800060100856201c4c01c6003014045101c411006c0040c078819840300150a0006081c000500122a40d008204d80e82e0b1714030f00c90a8031080d11b41000740548015226540e03041812056 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 238579208 1250 238577958 238577987
    0x70314060d050715050307140408100504021824040b15070c0306050c09011202180105030910020309280804030303020a050c030c0a2a050f120307141605030d 69
    0x40798030b1136942d020b005508031144280310004100100300b181554200349410f407007003641d000031b526042c0f800407040d031101c00b4004a20741e03190702c950118044d5900d214a030103541d50814140c1040c0c1c10881d09020306107544a02d40640c0740c0c41e06011038000d02d400c0c41100c5640c00c001c0c00b41c1e102221004100b03601544074000c1100d00c92942000403011402070311039144035a40341c882183e5a54008000500f841b002d560003403000d50b004100c9104164004070340c00c0350b51802070070016266103406603598180f05032034424900851001c41001241c00740050500f0086404462401075503103440044032002c8a580805040240204000c00000c1d211390b001741801f488510340141803480035990a41580d21032400d4813882e6004507407580c1400420001c1024000d000b111a901c0e002221000203a964640c0c450b0a1052820b0125041d60341c88664054814051000541e60740755041e18129a943c04d00c0000104a40316041c40803840458900020040d03420007030050014800c100412034600c401100704 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 238580458 1250 238579208 238579213
    0x20d0b060411070303090c090218040903300b030f0d0c0204020910080406060f050a1e0b030103080c0606090606030402120f0d020f12030c1b030f13050405070314060d05 74
    0x2102101c0103040090700f0902d110342e030302280c2c81d0410b0404039804035094116107001c902c1000840044019803005801c074031810340b404201c0303400d41d050554141c200c003502035200043c402a43d03840091228108455100f120000300f0454101c40103040ea0360315101e500300420b62003020b596114500600001a110348014400740c070f170414160108491480103100d11000c40d01190600017003000c0c9000c2c0002030310520b0f020752442c0b403429001170804103942c07254451412040b40565480e06031004088050840110290358a5035240340c954140d40c030034840581c1500891000c245140b402200060003900000c20860854982d0307002c2044010010360560014406c0c84250442c00d1001d010502c442506070300904640081d191056041c4800040048002c800401c100002c2c40c0c0000306a69039010f140e2101c1455400d8484254035501c1206a0800040fa01040c0d230100d01c8182c05025040d071300241c60500081e200d05100368180e8070801c3d844e020318060140040c0c51407c000b4400c9180078041d004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 238581708 1250 238580458 238580471
    0x30a0219080a060b01020c19051c1205070312020306030622150507020705121207031710030201030e0c0a03080a120f020409180c14060c0f06070801050409020d0b0604 73
    0xe030b440c01640384000c58003079899600f0b1070010b68040c450200c2c4004151007046881441c09403058001700c13640981c9204440c3c0c3c0c0c0031301c2144144685c40e99072899004425a4411000ea0030203046d540040008400041803e061446004420f00070f0303a000d00c001070018421038640d42000c0c50043c141e179000d40e90000f04000070313001140c88030080f00002070007510002078500340760800030309025440c4c20940c09074200510741120500002079442000e000164400e46030701030ba107402c44d03419000380d507409448404c000504c058490344850700c00403203100342c03020010b040c2420080f544075003105001d00d5010403800307000c201042e400c00042942e00e0662409100d801a4508503408507142054041a020740c00316080c03002081314461801010800b820701c011641603035840e1038070100e45004105c00700c01450700c510040d4403480d090b6150007444000707a80d048185415083c0d41c1e40c03030031a107030340011303807501c00004560400740b01e005002a0050040f25201103140c40c4d000d891803014105039000b50740c402 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 238582958 1250 238581708 238581719
    0x903030b130518010603030e1002011d0c03100c020a0f030908030a1d04050103022b35041203030509030405041515080c09010c02030f03031f14030a0219 67
    0x2100350201202526000400f418200c1c0c0344090350303a42441e410107130f81c900341045c4007094104002c3c0900701c1080f81d81440c01c450f035040490141200d6060b00500d034010f01070340801c007080840c0800c20481d0a41c01c480685080d1003d840c00d82d21290754500141e04110310031000310307024100b02d6445030700134244000801e58421040d0301c2c69010540000020b076508010780891780c0e00701480400344400b10390904c82941950001284030740100c19080c10340e0341018403401100c1801d40d200d48a950031942c6d8055200c8101d1580d0b526045506112100300c62800e081318551108501b914103682e0390940c0321581d18a1580c050b03000b40009400b0384040d20003804005a169074900404c91080c40c400b00d80b28081d0319109100c844400d000c00d50205001010303041040e202c801d030b410307141000307000d2802d40300303032407260001c01d04080703c29074202590b000000c10020350b049841c4401c07100c0301c10042c040311669590340c45030302c00c40030f040a266415086408541e0152402c0b1484140844030740d0689600300b80d448 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 238584208 1250 238582958 238582969
    0x804140f010e0106080a020604180f14090f0109030f0f020c040501060201020408060c0403020603040b0c0702040906060f0501090308040303030e280c05010309020a09020a0c02030312060312070b0a0903030b 90
    0x10032105080340e4445402c041426001e000e04d030300824840004202001d21540064041d0040707008809008007214004c100381c0d001c0d1b03081b041c0440d28001c8104101e6641c0c0a0360020710200f16401d0b0700758880d802d00c12a11040502c1403005840d0543e90f008491000b50000b118440b450072000002c5100e010760340e20352541d407441800c4c001c2800d07070001a0b881340350030b00b900d06000300100444e41d120028002080541c4500044030741c0158400c21119280d907454030410101e004001010b508107242070102c00404c20103a003c8826128000b5080702e045603244011a0b408410340001060030105100400000e8001d81042e0072052641d003d0f0781081080274911003441030395401c03484084840c2c0210100703104c0b86032840c0016110a180a0001140c56008511034124502c00c664046a00142d00b06856200302d00020b1000ea00a05803680d40d10340303080000e003c11060f51107a100703001d280003003941c0149071300c2100d40f456840f04a160041d0b5504694000400d01000c054080c103803600140403d50303945 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 238585458 1250 238584208 238584223
    0xa0605010e091612020d020112020d0f0515030a110a030f200906061207091805041403030f040303271a09010b01050405130e01060620070501080403080414 68
    0x6003101001c45151040300d840c075242e001044203190100a0806114200140d41c0011205805031400c03000a50a880100c0e40540d4400050b04524030110f01c02101280380e4005200c400c0c2402d00a000c29268070400260808a030842194103a10042c0d810b40040c2403002483ca510b031000304a032000c81d5403600c0d04484c1c0030b9408021140306000c010041002c5100b8845210001025a4501d0107803800c1404905144103071a4400214900100001c028a110740320701c1d00500809260b0301c22141b4100c451b807010703240a60701202d0340c1024205c804100c400000550b489030501030001a640d40343c5460543c003c090f01c1342195480310380c500c0074242841880d49100d85071807082d0328a081d80e11110443d5000b55002a0640340c959050038030740449680d1190a84003540c20803240c1c024081c46420080b401041003103800780c019400d000e00010569007154048a547c070042c038900c00e140ca03900c003426448414500403d800319010402040c007282c41060001d604c00d00c40c0c4081c9000c07949100302d55250040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 238586708 1250 238585458 238585469
    0x130617030d0522020105031506041d0f15100e0d0f0201080708061302160606060302130b070b13050309040509071509180207021507050106030c0b0c060106110a060501 73
    0x19505206074040c880e10b540184142e8000b040300c40c04401e00740c3c54200b102c00c007074100200403000c195803110660b00300c00d400c40c0c0104003e646a039200101c0521544c4000d003000360100c0c100000f044040304141280c80b526020003030300592041c0c2d9040007005041e620800080140302c4040d41000d444421141c0c1c020b07802155608165006440010070f400c030000c000c94204400e09092010f241c03108201001c80f884203220150b1980350b9048030301c0c5803100615014100c241031610010b649500b640c014800301120300c80c40c203903068540794840354900c0713140001041c401c90440041c11520251007003084070f034800c0c0c00352442c015014000405440b0300342c645103496000190104841880c40c0303640034144c0b520b41800300e07403103103000740c01112401c9000c030104629800181074800c6655000d008441040d0802001e500c80e161405c066000380400d000840e00200b510300c01141558008040d180544181c030010500e0b42c0c24040d003203550010b41804280b081c4070f030040c0c038030002e185401420301901 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 238587958 1250 238586708 238586713
    0x162c27010306020702040501080d0c022103030408070b10060905010c0c0519060807030c17220606050108150d030309081611041a18090a0b070503090c03010c0509130617 74
    0x481368010002190b01c1a445042180e10021000c4490790b0001d294400454044416031211541c01408807241c0c0792400c403140d0980000010801004014406014980e010306408001551080e000b4800840c0354090080850840c8004001c01e62050071110100f0b8482c60705111110b507110041800d070b16048025104107401f043d820b010380d540c09451698410460b24090212a19a02d0082d000284101c28980b007014200d00081d01c0350302400102c4000740c600c080c0107000100d41d081810003090907028039800510440c01181080311000405248000c0082c8003841014043e60290024924000d00700c54441c42400524034001c50301d842e4099850090080250840344002048100c607000c032207051105c00b074950441d041d034684070041086590351621000068a803844141d203000714500d8000c0900c555002040140365000b409180150b1f91102180c0010804008050a039525580d804000130070038420083c40e49401c01d4072107800b5994a81c0041c113261222040409030308904821440703039 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 238589208 1250 238587958 238587967
    0x2a081207140c0d030b03060712020c0a120801060806061327020c0a03030b0a030b0115110316050c010809120d060302060c07030c08031218010f05162c2701030602 71
    0x12900740c0a0742d170700140c046001c1d1507940303030036640a401c1d58840c00c410a5032650124484090440070031080341072540085170403400305064100101581000d016a6000928250209442e0300303080044d02d41707031042010101d50041c2000302e010407442c07003840030586003180d1240b0030110b405e03107200804035a00004040c1240d21f0044c00c000d0241c0da08122401e009201d01d01040010800078880241560007000d8070550884001c481141c46811501c00710020340400a901d0380301c0f080740074510482038410750544a440b00901c1c01940c1d501380032125910190000e108071841240c409001340304244400c0000610540c80783c0100b50117802100981c3c601d640f00444c18000d202401405c0401400070304000c52921500e81c401c10f00700300f000707010782e527001e0f80214252841e02020b400004040d2031503441040b40c0c5c98055220300882e0015194840031070740403842d280144c2d07400c04104010304644a00d642500d500d80c42030100e03d034150a030600b04c545420003c1d118007003000000500030360140b02d0260301d4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 238590458 1250 238589208 238589233
    0x121b0c17070806040203032d0313120503130605061809070e0903040303020705010f090503030a02060601030e0304120f06200702010e04020a080612010216032a081207140c 75
    0x40c0000c1d5002150385500c02e83c1004010f80c0d000049983d0f080d18035150030308640d08000103d00d512500a841c5001c403401004101ca40083c3d0065040079030700441d280003080c0394096003500c19110940e002d403030880806501384003141d21500400d800c00b6000d441c5007110641401e0a1411078400d442e68000c0381c000e0003003003015884c03000301e554000d001d213805149428510760380a91303540c1f02840341c0e506004903c0d80170f040a0b030140280100400300581682d6071744a411600945441c01124080c3c0030901c1d098100e0445140001503c054500a005200c0082c0c9607840d4400700303c2200c4d0088034066152420104600f900040e00381015010a072a503407103808520014189002c1141c8041c01580b06200d1510180e42c0912440d4010f001a150b9000ca0003a01e43c0543c0644903040f07814600707420710114003042590252525250755003502c2080708002840441002441c003000c1d02800c10b02c5e0a0040c0041c0c0c0c03118072525904000d1030700b002d02c0144000d584101e829013000040280039000010b01680 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 238591708 1250 238590458 238590463
    0x280e03190506071b1401020d020406030207050727090206130e070813081207020a0813051503040c05091503070b030402040c0e060a0c080d06030b06031009121b0c17 72
    0x8010000b42040080f91030346058000704d031441144081c1c08a84031243c9120403107801c0d8111408000e108800755070391a03c07810080d02950010008682c548a01c03040020745460b003a4410241d403080c9000d204401d20100340300c0c030180c83d0880c426a402001005190302c0000300820950043c081a22008110f10b88120040c0c40301d50000c11071080101c0f040e220070001100c1000301c500c80f88203120020603544421904a1414140000040c42d0541c001882c00c41e141c0019126000c86000f21440d0b8050700342d0b803a0036055404140c400609207010702c041800389207410b02e102540318240500032400c91400200080c607107810351784a0141040c0000c01c3c8402c1d420503014416841600e410507020b0440d4140120385540b00301140042007001c10903880c3d0400c00c00100f100c5030030100201c00d101c483d4680c18008c844083c1540c0d014403a01c42c0c2d207080d1a0b400407a0044405480d000111007008104050098942d040c1100e144e22900301560b20700c0340042c20890307103070300902040310b0741294405003405401d1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 238592958 1250 238591708 238591711
    0x30b040b0a050603060f0903090d0b060f0a120809150a0504031a0403021b04021e0309070614180a12050d030605030f1e07050d050a0b060402280e03190506 68
    0xc0800e4144002c22509072000101d241d04252811b0000d0040d5684c3c0e0040da0560140f404501c0c2e20002c4003240506100c3c64180c410701940003252180021800c100030040c1f11640c0c2e224040750820603c0004003c141c0f48000f50840403406080349140c0a07414060000d15849007a50001183c004101402800442c0c81c104c0c050400601b0789995509254a02075074407500389c0b82c019150454071410410645031601512001c08078954003e01c400064400c100586c0c204490303d08091040c4007000400c54410040350114041c195a5503240180710031040720050080012290400b04074070340011344544580c41c1300d01c0c590040c0c0280001007600399006003520ac0c250b001d030748a54400024070409100102d00003d159180b00c40c4010b008030010140350a22140b40c0c000b50348401400c45a4081c02400320715222081d02c01d80301700401e5074910040000328018500709007242100d2054550040b1341c0b240c01a111510381c2d08201180e07540e88800280381c41c01c82e107081c818101074070703500104000080000d80d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 238594208 1250 238592958 238592971
    0x1e0506070f1e050c13021c05160f080f060409080c061902040513021303060c0f091a07080c011104060c02150405030a0f0309050d200102010b10030c031104030b040b 72
    0x42e01104456200c6540d0b83c0340c81ca48552040e000d50b88001c1e2600c1c217079411178558103400b11402058800c513049110050800701c8400241b00444031a45030a248201e400440390071094032441d0268440e040d20002d42e441c01040f8a40040e0744000d8500070421600161603401030071700082609162204040d140384005e800b907030b1a41030062000b408247c0d54100e003481203040880005869400c100040c240d00e58903544094400340c079044144401c1d03940000c0385100001c107926083e00c495907075407a01445145e00004054440e8042c407c4500049a030002491094003400020910303a01a404840081d40700340e200e07401254440c01d0724000c500301115002c15825051107030034101481d020102e03440f524440c2d03000b400b180c802c000400070107009003500f802501c00945500102d5140d0b20b055940000e411450007501e0f80c0d505000703005903205000307480700e50001134980d10b514070507608160301802c1140d901c1000d05448148064034800c1c00d402500086025220084182c1000d050a620240002d401c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 238595458 1250 238594208 238594253
    0xa0c020c1002100906021603030902190609060f02032802010608070305070b340c080118120504092a17040f1a0906060f03070f1e0506070f 61
    0x50412107401140703a60803c078000c200400c03400309620317002d0000d00c2103104441261580c102944d060551560000800d83d1007600c201d0280c8060300803040e111503040c8105400100e403c1010710101e803190b85410b910300503e004032401d0040c0c20085840308800c01a40c40d190300211340e4100d8900b81c1c24002c210041031944081d010450554580342d0315071002d4021035050050009031040c0103080159805c117400d07002010300d4032010600d008405401c10302c51083d2000ea122000c08100c0c54818441d00004424800c6513225181d91a0347e6419108065800c110a20009000c00503099540c0d010303100d00d10040c0b2281c00d00341c0d160b5100c01d002810b1500724072070420030710144900011540d40c0c8043c2e00700ea082203140000440d00e140050710b44040d058140103c0840909114994100041d054080d10040301c0340820349088505240e5550a24424804102c031054410051001c204000d61050f4034004a090701c10340d102d601159140d406807404a80401b1000c04600034801e14205404180c61074844 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 238596708 1250 238595458 238595479
    0x52104051002070b06060a1404030305030114060a080712150807050405070e01020703060b060f2701020d170402041409030d0b090c0a0f0201090c0906050a090c170405070e0a0c020c 79
    0x183c204110800a0440b40241c6c0000740c60030185005201c03c04a00110140c00c2d036a8540b41d150081c1103410038403804845003a0030702e80300c4d850b20308441a1102030f2100d50ba296a182c2d1128421540c1810921007078040035030741d200d81c240e00c5483c020690701030210b4030014510a85403005010403140c2c02481142000021a4914101c0c1e038040340c01c0040b80d0700710601007010351072400015020302c6170f41240d0481440024410703101014074000c1480c8288910240d940202500c3c0041e40c440701440b40c14000221410501c000e40340703001400c21340090024000081c50b00c03190209140600c004d80301003100d94008610401d01038801c3c003c40c01441c8064420400e0b9091001c0440d0359401880750100500644011440b1068400d6010580194215191001596441c210000244114021940912001100480d04070814001ca0341d21440f203036241200010b0310010a014001d0190007207449014038140080c40e100001d0303450340215808c0c080050b902d8039040000c4e1824002d91f4505004143d83c01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 238597958 1250 238596708 238596713
    0x70b060d050601121a180c0301060602060601120914010209030d0e060a0305071b14071e050f0a120303020405010f0e0a0b180d1a07080c040b0a05210405100207 70
    0xb0207504542e0f004940e45070500042c0b608100b0444100703240489a00310302e0811030110030720344036170b4603801b050030079902c0c0f650049051500360b070500d0082c070001da0b11940104180e5407150020383d040e02c0a80c82c001600c2a42c3d50780e40e20103000204521903240c0e4001c00c007000c20380f406000707900300020b0324188494901502c4000c161107000320460101810f81c2d601c00550518000c1c400d0408511031001740c0d692108951520071581180b00541c2e00145c490028003046104401d441c205c0e94407404100c0701d507854506020400b030320182244168010400000020310000103035261440303140b2a440140e00e45080c140010440c0c00004125004c01c50540340301900d940b2107600f60400d540140b03e4482c0c0d02c0c40400769604c05442d542c000d550300480402025810304c0814030394501c130840d00c080c0480d00c80c6c64800086a640d0750566400d122014100404c11480780356600600c1801c2403400c010342002881c0844058800925a92195071140101080204201846039610341c0c45000011820180f194 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 238599208 1250 238597958 238597963
    0x3080919120c02030d0216061119030c050d09050f04060b0d05061c0803181614040f0203010803130e2e03020604080f0f0d0c0b0723070b060d05 63
    0x40406480300301c01da501d41403854031400400209a8000e001c50382407115090b002556910100c4c1480014900500c0c0865101c0c4100c0300c4641c428040b60042c4001c00e80d0198080c01ca8518801c200c080c0099141003400180e828030001313003800c40b10b84451142034601070038090217001c211081845907250000c24003a4840800960744c404008840000301d6030390b25404940880e0001d9003207403102910580f010100000311005603c19001103001404c005c06ca080c0880d41c2d0300403500345501400340340509004121140f140c0400c10f080c010404680280c40c2c0308a01d0890303000381c204111603000003c141c420f0041d4825040c00402084240926034034000aa05503018001e00389200c10b0400041404e00184008a00201441d002480707265a16a504240380d07130703861040c50000c420b00400300301040440003c0740c1d42c0c4881959031076070149100c080d40c42e030440590062100c018000d101c40d11950190246405102c00c05d030385403071a940d52159017005110340c540205901d02c104101e82e440710001e00d02 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 238600458 1250 238599208 238599253
    0x7110a0209011e08071503060906030b1b0d02041409160806060a030b09090a021e3d08011406040b09150c0d0207050f04021305090603010f050a09030809 67
    0x4020b601104240c00c0f0f20b9107180c182a9904c00030052040840201d07400014241d0b180c81c50b00f254404010050340c48001c2001c0e07441030701c00034120b0502c05e8006030a0184400f403041601e28203004107881c105508602c2412a00030341c00040c20800c01e28034610031410140142c40d0070a000480f042d202c0d0110143c01000d0003001004075010345408901e100c402c034080d07005030404240040040002d445c2081c0290356602c0b880500340d05c1901548013403250160f00c0d8000d074200c42e10180010848900d0241403900c00341000c40c1c4011142c07901e6008650840c502400e240490340955580860303035240609844005075942c00d101d00c104810030041000752068404c4070071200007a0ba01c100300030391a030300c5005a40a0f103205c203081070051210a080d10b5501082c0f45003603807002c96805142203980d02c01e0008a00500c811180c403228109001d1040745030141d03103190704c010014001306c2d01ea4144211142502c000f603900011090300e9168481c101600404071551005201004109400c901410316042055 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 238601708 1250 238600458 238600469
    0x30218011d030109110906060301060807051e0309070602100204081f0618150608220507090c03020c0c060705101113060f17152707050307110a020901 66
    0x502440d0010200029810441c0050080000030701908020800015030040c1a1140703d210b00001d49925000303081c1d0307068401c15501e00841e41d0b41c4038000d4401ea445000d41d550307d09984208800e520a0707540040d0301c111401e02c064201e031880d118000e841d02e5802e54031124801d005010900c48100d0000e13420001e0b048a02d0b150303070a40c258180a80c01800641c001c0081c095980e00030071102e00c030ba5003100605100724905501229522801122050300070b544006049400c81e480801801c41d444ca003420181c003d100340c0e00e0031959030460351300301ca101a5542e40800c0d00441e04004841082c020100203220540302640342c000f80d60360f12511030405e0352464120680e144101c40d0002d0300c007030640d20400300039007651410300e49900b400303450750440d00e401c1400942d943d5402d555000b900d91031b4174001c03c0142d09010290b00107034200503182d1200c054103003d0350191100d2141044134903031624000d01494880316500c0c1400c000003410003050040c078019a0b0b0040c40032000580340c1c203184604459 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 238602958 1250 238601708 238601717
    0x906150503040c09020a09030308070e060d020a020c0616020306090a030903080a03060f0303110613020307150e030303100515120f060103150605180915060306033a03021801 76
    0x42d11850840140c07034140d00700740d182d544046002c011854201c0792010560380241c44d58407542d0307200c0d60219012500d10000b103400c203000b488810350303580054024008180b01030065904900100020840980100c4c245140c08002c4040e200c00b581010b00c0096001001c02020b1b22840130344da180507040d59180d100060000c80c00290101d0980e20981c8240c001c0c003600d900415040b96a4100240780415a12215440b4020080418100385583c2242d8420036405005802118074101c0108800102007003003000b8001d40621688a60b901800198864a1a581c00c00703452030401007400300000320341c0300241c0342500030004080d06000b0358a80f00e0b444009030414403225910600120050020030502c10011805000301140040e0003c000c0d0604040c1e030b100c181c2040c21104100700e441281590411803e1040309410415400c00d103005590044000d0111182072264400c0d4403803d1941d1081c580c005000d020b4440e003681804002603651071a00d140035410041041070800b0840c01d048102810710 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 238604208 1250 238602958 238602961
    0x90608061608040f14030d06060309050c13091a160507080409200307090501120204120602030c13140f010c02010206070f110d02010917070f150902060309160906150503 74
    0x8508940360201d980c00080e54040c40404c1400c02c6e40c176005006007800c110b042140100b0600c0c400c0c455405030640110040c001c1111506c1404031100d015035110000686405903140803802036004090100c201c000c00480b180741000034041c041041c3c801480801c00d041000c20007045403201658141d4100385800903000104203030355081c7e1b0340c0e40303402c0803d00d120200c20040890b8000f8203044c100ca500386c0703900e41005403217100001248194010a40319a01203240c04001c103416501555001150036000c0e450312201a5880c0030300c43c81d030703030001e0312203070f400940315041c0e04020b5031030080300b0380030b003455102e0110740c4e80082e4561100514010400c60803d103680419031060340e541514040010643e0484606500000c1c00317041c00b0001035415030500410014800b988504444a442d000485285034a69940e04c5d8110302e410359100d440415200c46907040940d9640c0011409a03d0440041c00c2074200c00b94207005403212035004000d550310b0560200b1034140d038054568401c4100e4a40103949 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 238605458 1250 238604208 238604213
    0xf09051009020c010603120c050d0809070e0907080a12030b011809020711060a03150506120c030c0c03121503070302090a02070c08010507050c07090b0a05150d09060609060806160804 80
    0x420055001601405507c0a180115500f004107020b030340d80903000303940c0540c2040b4816101514280c62120103940a240c04001d120320710b0440a400c4407852050302c0c201ca079242c06440c83d05586541c16070761740305282d02800c141c603018440c5100c150020700f081d030718940b15581c422030400c03043e100e429110383d00011081c5c104100e0f1140072103548001040c03a500d902c000c0100400074010031180480c040500321011809140c07010984601071411601c0480d107a84176031601c00c080e0400303070086411680500c0b0340700c4201c20510103003c0016400c12100040d207000310380007107102720300d40d5540d000e5002000203102613180d42c50381c076900c402d55400c0940c0d039030b44600e040c008100c480d9102e0070003540303440306201c00b00e980328000301050080d403c119807203036881d0210001144c07001803886d98000705070b850070845402c05071f50b41500360a00b050541d0034102c0400000c3d06880c682c03142140c046658810030f00c1404824456400a08810001000246003050030042ca08040305046818071503018002001c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 238606708 1250 238605458 238605461
    0x60a05011d0c070b0a06080c15160503040e09100b012c06041d06090610080106080604020d020d0504140f0703060509031e070218071e020120040f09051009020c01 71
    0x1a00e03603024010f41a0b0b07251017070f0414014452406440d0880c01129200b1103c0c0c60055540c2d65000b2a030072000e403810f0b40c0400002d22000000108444502040c0700c000f80c0e070303900341058511070a940005400d185607046000001c0b01d04c860b280c0c03418400c08603003807080f200517802c0802c40001240e4100c0c0b02d458203000000c0c2540641d45c04048a00210003000c1080303481d012086020755800c0d21491000e480f82410086e00c1c1003d00151400076400c2c500400c42e591150804036000030015000510b48080440b00f04243d0b80024421000603490f00103000400600c101a1007120b003004010b40410006800d2103501c50032079110140c2002e4852000c00d031005c006208607000c51410507400c4071105071a03450400250007440081c2c0c40356104160b06800e19058442d0b00388505000d6889100c890801665186031044400c810011136517189809440141100303180801803440350913082d09c0f1803030a165140403181e07540001c1795250a08050048a1100021000683d54059070140e100c3d41d60200c2c050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 238607958 1250 238606708 238606717
    0x715051b0f0a0302030d1505060307082508060907050f04052101050106090f050301020909010905040609320c010507150917041502010b03030a0c0f0506070809060a05011d0c 76
    0x500350066403441030400d500040101b013101140481881502c5129001c0f4014092502c00d030354000802700009030041d031055020540c09606141c1c03440c10b184056004040a80348191540c000c1400301046c40890302e0042c600ca503000e1894600340d4500360f02c90303c241031035004900c10b150054402a0894071418404c18604480d482480020007c03982c0d42d6100600e85529880b03880347d044018100441c240c10103000b00d640320701c0d01502c41200ea900c3c0a1414000f000002c10548a40d80e96070546400a00c200008a2451144905181380c91603c00248a070804220356240c00640c0f20140444407660440c4c02d440c1c6c61504050705aa01c481c000c468074000d81100ca100801d580e01d40150304c13000728044800b502c19076214500740140102c0f4120181c1c01c0340c06d0508040e9054ac02881085602c501c1a510209014410410110804c0403a40c0d00c80c078060342510440081070f0820108446144200320443d0f004001001c144000c0d403516180141082c0c8800a00c0c040c00c0405c00081d0240010f6021107 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 238609208 1250 238607958 238607983
    0x51b100939121415010e1006080705030a020d090c05030d02061003080703050c01060e07030b0d02031b0a0506030103211e12110c0106050307150e090709080f01020306030715051b 78
    0x4c902d40200c151503254108000d000d440301550403000891404913a404048050f61007517207949a15844400d410341c1e0703503000101072080c031f16000c01c091b40003c00607009900615106120882d4081d042000701030819850b00601c1003191302810400a03049900c0152508507034000c00360941d1144541030844c0c481c812020003e17919801c01000081021042c010244a042c407981c00700445036445c0c1c00c115050096410107941544007680100310448580310002000c880200219102903466000c01d141c2c0c3c000b64000d07a120441c02680080d40c180e0030111003440401840d2440140d044110b01d0f40c10012040301500800100e0b40c15501540510703404a10348655000510707848155065400e80608414080c2c18006c0c054120001240303e100350881c90f40c1c000a4a8020401e45070300c06024000ca4001d0400003044020200000d1110f024031400055828400015a0300c0c40c0c8042451300e061710301d0740b00842c000004508840003550180c00e4552006400000901840c07500024034540b41521915 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 238610458 1250 238609208 238609213
    0x10e03070e1b0304111e0d050615040204031509020102210c12030105060a1409091015020c06030406020309010605150403030e0f01051b1009391214 65
    0x7080c0940314004051240003400480001120000718082c2c241c04152401441180d40000c1c0d0455031514081070744540780500c5803c0703808005034000034036155408005541d0713504803400b032160b401803081d1070b9009414141d400351310302071450350743d40034480c103411064034035955405800c021688207200d4003051440304a0700014012070b414a040e420741c00075040d1100c0c2d1007332124600482d0300d90b034256412a000240f259080a00900c000d0f1056081b00800311240d0318200301b4200c0513034819520034000c0710041884001c160422035a00701d51404041481c0070b540c0031180404c01541d404080740d0313010b030317102401603101d0701c41c15062400f400c1c076900107962140e01203107200010803180c0c01030001c40703009540700526041c00b14140320101641c02151800100d0810092241080040445100f46c41c00001c0311002081001e4800890764103420032034030501c1043d02e06840084012007000071811150307902071141c0c3c3d086841510040d440c8200e401300d603441b01d07004052112900b550360344515100306 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 238611708 1250 238610458 238610473
    0xb030403050c0607031506050c07030b0109060501170103081c09020405040b0a060509010e01092c03041805061809030702091608010e07052d160204060512030301050f010e03 76
    0x2005010354200500e0002c0911888002070740c0300d0710038003c5090018011120019060070190125225808060b21803094404c40500000103030000c21140d000b0006c4003800580c15040c00c00040691611180c00001e005003600180046000d460454101c402c0241d204449101c00d4582d81015003540b034030195026243c40c7c1003200b0320041806061068220010420026458504100f4100d03000c0c0501c1e4090056240140054501d56100e00f02d4a0f40c80d03c4608611b5500c020180200c1e0380b540303140006030704082420080000c0314400c104400715140001d100e1403410354040b500c041d4510106031b03101c100d8000441c04050050080303469075178004d4102e10141c5014807100b00d0311a9980701c04000034031418000a0241007130001203001d0300199031428601640c0e0020030301e019070500c0d4448410313030440004140714810117000b0a00142c05211103594440b09004200c1180d101e0740c04130303010f00409041200190404002c0340d066440c222008282c1c0c40c12500101c80022580a04c00e406105221 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 238612958 1250 238611708 238611713
    0x1f050106200d18050d030e040e190b06010c0b0c0909010b09090406090c0911070b0c070308040305031005180405061b09120c040501030b010e060301020a1d030a051015230603100b0304 80
    0x903031003004107040c2c40030b012034003038492400d41d1081c0c54000c40180c006c80c1c0d2640c0000030810041641c21033014908003010f1921902c4050000d4003d0b68424402c0d20006103078480350801800301c5006000350200b00b0304248a4001240c003e0f080140014016940e406c4860304000000c01c08101a10000300f00304100340a60380d0703601c550307440a103040c1e95003888200050000076181003100d926640c941d48610342c944981e07805540036007000c4d203074494010003450041070ba622002000494030980d60101e09090070503052143c04c202014020131a05510025080030301e812002c01c444084509407142c401c1401340c4a815414000706a5006038801d05200002042c0326841409034140d6440040e0500700e40c990b10105402c07481400c0c40c000103d4404890030075130389140201c44000700c13005000d681c0312101c40ea5680d0705090f12142444051a0b45169181e5400c1d181105d42010300103030b60041c0d651000b6024106803071805014110302c10607000000510114030510300000070003078104800c1c1c0b00d08103403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 238614208 1250 238612958 238612967
    0xf01020a21030e0c0a0b1c111902060106080117030405040507020120130306020304032003220b040905090712030906030b010c0c05060306031f050106200d18050d03 72
    0x101c2000000e820300220a020000100f90003010160040c0100b08140c54840d80c1d6030740f50071a003081c800c11105281c0c004408001c60080707a061200340ca0215596000ca103a0721034054580300c11807800c65101030010b01009800c40803450540e20182c22180b001e803120179003640f9511440d00090340050030203007403110845d015000348105e099410b5070b01003000e07109905c490403409110745102c1d401c081c0010130804644681d00071034220380280780140c0c123031206039820414904c1c0c2d1100103403e80d000040c0c20200000c0780d20380c00c04403442d940300d12005034a0000540d819004a000c1c00c0d04160781c0f03002046100201304203180c010000181020041c80c6c3e5814080d1581310309216100202c1d080141c03c3c1f15640c402c001c44003079680d01c100c01c0f0614904043c1844001e81006003079a8047c496180c4c5583ca1000004000201040060021a1079070601c02e004010b000240000b41404441c1410039640f100081013101c90076400d49449034100b014030701c82d081c414507554012500701103821081424180c0c00b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 238615458 1250 238614208 238614263
    0xe01030e211306180302040903050c010513060507090b07020621010f080601170d08060a050612040c1403031611060f03090d020f0718020702040501060804060506030712020f01020a 79
    0x1415038003030625079500080e140703540701c1441c070803048130080f0003400140740c65031203440aa4000e00d445402d1030002203516085035000d85039808040f0342d9181c400708020041c01200d43c400308501d0300c546541c0c6030001d9121140628000203219080100c3e50448040c075054402501c0212908841c0e02541d4900d88082998400c0c020701000f8040c62002081000202000e0804591108002c080400c046071080f01d0100000e0045540885520000039036a0b88bc1d501502d070651480340c040d200c0703003410f20342001c200180e94030900f44240e811002080d19900401621030000000420490081031440c200041003c501034142c0e004030045041021800040051480750055804031410342c44600d600341d0b41c42c01c500008042c240d100300c0050000383d10740343c45c000031601390f000c0160a110311640000c090b07030303402d801401c000340900c4100700911030a8040c25400950540c0500403490808204210440f964a8043e01442000319250342070f0344204540d002c020781000503821516000401c17800d9040340c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 238616708 1250 238615458 238615477
    0x207030804062004061d0901150323010308030a0209060a0e01171b0a050c010222120c090b01020a06050435030a09020d0609030302030103140d0e01030e21 68
    0x5040110303d00110000074842001081078001030410340f0b03003881118100e180015502c1422682c00f4100303030310380f12440424040d18800c0039000c60820480c1008003216801003411210781c00d100c0141c4807103150b02d0360140c196034100001c1a5250380d030054917000382c454030715955001f0f1030000d03000400950040c580d000707881090345d031004c0201e480c51a87c410f006064070301e40d00c80a5894017000095010381d0050684100e0740c1015420500c101d1801400c9030022200e005907403245880c0c14045884441102018001040030b051403001e180c0c4401410074550300905807201d90380c0b202d42c02c80380c0c0200280701600d58004401c0c4003a29151800090003109501e00d1002852031406000803403982c07003c0350f40325550140c8680d065a4a440b082c80103041900002da8100418100c0400815030b41d001d403111980c00703030b100036980b540f42d460316800484800c0d500c1c01642d008005103400c200d60210b0022983c0c0d000340307030215620395812116410710030301c000d4a0070b0400085800c035a00000d20f102070b0152070f0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 238617958 1250 238616708 238616711
    0x5030f07110d0512030a0905031207140f18010c060513030806010c030e0d0305040320011209050606040b040e0a150b0301051003080310150e0a0506090604060309080d020703080406 79
    0x7610141841440001040700a00540145200a01140c0d2100155a0040b0300031000318180100e40c03202821540401d110701403103500e40c0c0c10455240d81009a01240c600c401e400306107031041c1c1c81117103415406500254010880450a42d440301da2154070814051a0410800c02c20cd00b4090b94000120024050440108039088000b0319a5806000610405501600c540c01105101c3c005c11150900180d4103d040c00810300c00400801ca03040400d40d10800300401c58081c000900002400b54240840c1d1100b40034105500c0e400040c5012403840e8205006680c04507038002403400080c00b0b0180010078508505c1007005400600036004a4a59500b40340801000044682000d01d82a00d40441e5240ca040700e600f4000c00008041100465200d0b08000103c0700c0941c40300400340030039004040c2e64000407480088440c442c9402000f800051204660a9191020700004a2282d000e580300c1c84090603602c03101d07141030202c0c180072a440b00707076402c80856030f501403854043e0801c101076a06681c0c10703 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 238619208 1250 238617958 238617983
    0x11090a0501140708031b070516052d150c01020405090a050105030316050c06070c0e0901060602070b09010c08030f040c080c01120b0609040e070501032405040e030705030f07 76
    0x254042d0002e0400c40b103402d40c0c1c143c40c0c0415622091040c0c5d001510340e440552100c0420b00000360424040e085842c4110041c2407650b00502141d0303040c080c10f401048c4100f130f0508080a16001604001c500300006450701c44081042c2c20020f10441c540707444403000403100080d060480c07203040d4000c4c030984070110b91328219525054550021100c0034002c540d010751003085002e64840c8580384076031000d40301d2003c542c8003203001c0c008290300e500b101100b16807c4499400c244090655602c07000da100400030001c00c425031400a00a40e6001b0783d200b0403800c200000781c12481030748078011042455800c034501c3d17662400c240501d848124001c690644a114640c000403070700d5200410500d01105050b50750503005080e04540300010a10361405c2907102c042005030110645582c092a00581408006810030078070701400942580c035043d112180d4090022502c2e540010800501c03016250255000107200424003099491171064000203800c910001c16030300c5910748400001c1c5080da210306200b0800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 238620458 1250 238619208 238619219
    0xe060a0f180c0303030203040c03061121040c050108060f19091b09091d100c080c090d0f170c010204081c0503040609020a12051c090503031605030d11090a 68
    0x884450785000300a407503100400c00110340700c0e401950f0464028492100311ba5940e89e50342c0f04555800175401e22014011a6041c080d80420400041078040c100306100c10703182c00c2d40c2d40c0c1c140c0140c601030306041c0101d00c000325000d0740b294022056655805020719283c190344080e40b0002d402980300d042001d40c2400304044880c1c000546268100a482e101e0464050520040340054540d010402800054000500c1f9260000b003200c41410320f00c14100140c2d00c04440b030010881c2000030074052031000c040241e03200c40c0e00c84034030f1510b0341e1340c00076944020a0201c0c580403031100e0440f0b41403088036901160b81e5030120410342c010310403101e40d81c003102c0060212112480b440011b900c070344000720748180b0010b4041485a000b589516200604c01c007815511110988840c0200b08025155644030000682d901000040c52400c0c41c0c2d86402c0840b4050300d040002070b034a11840c000c3c10340d0100440e00c4441000810000e45961180c0345d1818000c0d035001514171441500400c00040c4a1741c02d26000040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 238621708 1250 238620458 238620491
    0x10050a08030a0813170c101802090c0c010501080601061b030905040e07090c0207060306080102070506010510050904090807050105250f18030303060305060f090318040e060a0f 77
    0x1203424040180d402e011200c1c0041d41d488000800349844e10028261900028507040c281c40c0044a8428070b441d15594460b42c45441c18501e00c1507800702d94a0f2a080510708010241e00803070300fa60483e02c2a10707076510b01480c00614000c0c050701142e25030815001013070000c030201e0094140c0e012a502c203422000c650fa40d00d008082000400f0300842d810982c188103a05240e080110007841d0300c81252901a40e420300303101140c042c000e00701e005030403160040c404580d1501846000b81050300081d41000480d440300d54680c03806102d0310340b01e00c3c00c96146210241c051019502c0b040302c000c10420042d08181400725050340301081c00c49507546444c000a0070500b2070701459001d4803440590144002c1c090900b900c84400d80c428660a01050f140c01c1041034450000001c080c40c445c2c4e0700403590601e149440740c81c18001030300da580444041010480712000003c280c1d000e03400c0604d244003808070001e0100300100f12110390340005015800c01c101d401542078009039414031000008000014980d070394882c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 238622958 1250 238621708 238621729
    0x8010204030b0a050f06120c0a090203011502010905030f0a0c06050109050610170c0a03091b0f0b03040510050c040503100c0f11060f0a0605030d1d0d0b060d1e08031005 74
    0x4070000101000c100e042c00d11900d41d82e44103c0e02c104442381000541c00059004101d54040e05100341c000006105802d0040302c2c00c04103c10500003401817004a541d4580c1701e008900c00700b20b0405010491340705442c4074005003004150484e80070495561142c41e0750001d440300300e070086d0080240e0b00b0f03a802c03800c4c0700d2024007124400728040d61845440320301d20001e16034004c220390005c141d203c1d0394101c08100003240004524400521503681980ba240b20014604040d0f4003401c20ba0900b4800c000c041100400c050b07924820fa5080007130580d985030a200307114040c0d42c201c642c251140500b03502c1880001c1d88580c2409040e80c446148191941800b140c0c09002c0b003a0040041d081800800c8080c410041d00c2a000b00d8416400700f4940d45400210f49000c20a04100c070008042d201040480ca5001c001c0080c5001e040c2e0b080941640141c940c0700c005007025140c0c601490302d9181d0308051041c002c80741094001c90815420301440780e418060382c55042642d9030480b00300c0416002603640b038100c0c84003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 238624208 1250 238622958 238622971
    0x50406091a1602221e020a1b1e0b07030e0106050d06020c07090504030203040e07020303070f0c0f0b0106120605090105220e0a210207030c051c020a08010204030b0a05 73
    0x54500702c9020003000052a00840c201d1300310303400e9001038221000707860140c2c4c000c05403200001800f403126030800065001007150340c8440c92041025141e180da1209480640c0d6601c1130300c0c4401e0312850329080b100e001905212032503080004040f6410000c0300c0401c030340502500d40c0d0501c0403010b200300c02400c8905a103d07041d0701c0a08002140c0c0040c10799006844c02031640740503954201e50700e00d0342c0380036902d046900b1030044e000028280812041200da298000b01c40384021804c51600103005000d04078454281c0381440900c841c00401c000c0044080c0b84440d41c004240300031540e4901300641218500200b0081190030441c5c0800e007804c125420904031540203110b28040a00900000c0480065200c0302c140c0c07075150b1a07500e0111000b04850380406114900021480c40c4415618940e410151144800c5402107903040000c150f841f24100301707490040300c000103400c1941c0c0340d2070440102c2081c025000710b0418000104a0010341c0980b0490b030080010741e2045c4d076401c0f900740440703a00703c0c0c1c00c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 238625458 1250 238624208 238624259
    0x402070b072715050d09030801180b0312070501090c0f06020114060f1507081602010305010e0609010902130f08030c0106050a06120902040f09060b040b15031504090f0305040609 78
    0x40112016103d003030742c0c0f18100c82c1882403400d1040e040c4038090311001001940400e0070000100401f250a0046204038144202c0412150a00d0800661141810480ca80c507401012a01e0300901000b035210008181e40b03d0740b4425000d65a81446000080e148100c1d000f55180050300c2804140d00c600051181800500d10140006145d04100021080d02905ea00c4690148901c02c001090031004080c3c280e580030540030500643d10006007640d00581021250100c0101408450349513554101c5c191490141d0241e10f0b80c401e41c0241d410056107034000c0030f015800780e500207090b1002000402d40040d40030000c0c80f090f5101d105005e5402091320030b8030005162811655840300031640310018140c4003c10103e01c41c0401440a0242d400d904415030302c0664400405025182a114030052900250345100c10740d070f501080000b40e170000501100d1f030241c1c580030300d960a64403a880160600e41c04208458002c40a05004016030001d010b0ba4010a1615074081090070011351910103003c002c501 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 238626708 1250 238625458 238625537
    0x80601021f0c020c09090a060b060f0a0e06131d07020c0114160b0403170609010810090f2f2b030c02060c240702060112110402070b07 59
    0xd640c00100402c80d80310085000c1c2c0c50700728200d640c40903001c2c0d028011450051484210724149001260f1040e001c0310710a000c00c000070113404484205070703400345802d030500c27a4021911102103541813180301d05004d01914111004500c9141d8015042c01051281080d4a20350b610701205076540d02c8400da000780030840c0e403046c07090f180300c030000206880c0101d4901e0300c1e11214503940c0c1d40d210000a03201280410901420b00c407450200103071076039020004440c80d01c115494040c6140d2102003e4010395407254072030351840f044c402c1c11b08000d82e02661040d0b042e0800c5d20880040c4003844400303030100102200c031040003c41850002100d00d610a41310030388106c001406050141103010300401101070103c0280407038007503600c840140034542420350250544c0c003407a0400d803c0b801200780e00c1c12600036042d424051603950008015042d0f4018004c03030855100a41801190304a804640541c81400000e50360208424441558021300382911110440394000341581586111b410a5511408d00802c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 238627958 1250 238626708 238626763
    0x14060a0e0612032a0c01020d051606020c030304140d081b0c0c0306042105030c040306090317070f0914011211070f0503040501020601051c02090a0f180308060102 71
    0x16082d40e081c0a880304813440e02c01002015122241a410203010a42201103044031900080c0503403480c0315802d2000d4654400307012030151950003905401c0c50981d04501480040044a504403405809044101e0f51240340c070703182c500c000f01440e000000c228095503807925910350103a100075014035103098040603090300543e100c0425801218200f0900c3c40380300081c80003510103021842c0664005c600340e1380241398451141c00e00c5542118682d0400c01c04104000c02d40c0001d40036281a40e03803082e004140c8400ca403c0454221080d00030707051814280b24140000c081d005000303441c540304180c4440c202e55942c1c00c0e030f200800c0050020b60340441c88448080d0390100495012421801c0c0c1801c0c2036080c00350b15101c03106102c50284045480d540009801d1049680400c012401408211494844507003c1640c03150942080e00d4000d0060304000046100c41855400c1000c10380f140c603408014030504001d06203c0380307800c68019808034484030003103015540302160500900144d50b1400510304c1030345 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 238629208 1250 238627958 238627969
    0xc1e060819061508060406080c150901090810050105030106090c080718150804060510080d05070501020f0f1c0216031d040203010810060b040f03033014060a0e06 71
    0x280114924182d4840000c640c10004180c0010810f060340d803141960b16000040c04110f40b0103070014402c0c6d41c000c1003000a04d41d10314400c6044600c1c3c1460480d2100380010058038020388a4208121a001c1c11102e41c1c1010601e60040307040f10421002400b1460365842030608440c4800ba0500000740518005100d15001700200c000e04c02e401904440c4c850703550174018004000d19001600003c1c1040305010500c51f082c09180c2d0003038112400344501310b02e012562565070420605401c2402008140c0c181030000030740c191901443c4101410b0355584039440100c0d26075101d02e102c850f4012001104c0f00d040b0350301d8401e40d0f40702100c888000c2c40408441d02d00b0b541e881c20641400100c6c4510040a080c0c0303031114009140240784d110018075200c42c2000d400c0b01a900e40b44c216280740c45080c403080080307071940f400384d000b100d406040c584a01c1005403000202c02d140d10880030071094100150713030441c040c9580f1100c0c1e440300f0800700740c0c85a03c030728080002d210010301c01e03240d0502808020a2045c81c09 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 238630458 1250 238629208 238629241
    0x403020f03120408342c0109090203010f050601050d0b04020403060213030b0106020f0303010e06040f0c050415031811013c0f12051f030c1e0608 64
    0x80845641061066001e02c1070342c41a0894505900061034011020440c18101e0b0180c1404001105a5915800c05034980070780520130001c054900c2d008088a814102622001113030340140c1c02c0003a5a1511a250b014103804501240a50300c1c21100c001361186a10039a070081d40143c1d107031032400e0002e205090142c00c0009180c2d83c420380c20040000014906d200514220181400c410385851a40c204103003c41c00507481281950031524090001d624040103c81c15541458250720107a220680864000c3c4150400c44411503c0c04418481480d0090050400c540c82001c103180c45c0201c2c1042141551072140e00082c01c609950b5a003030008155008501e030441c01032510740c4100e011500d009001d440c01c0760034828514a00f000d004440f1600d0141c50b2400c044904104111a24404000f0021407030b1003107a01d8401c1d030316800304900541d40b6502100d0f28501c2414001d28907140d040070b54002c1c0b0326100320108074119104220a091000d129841108c4240c0c0f03403800f45a940c0311180001486c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 238631708 1250 238630458 238630489
    0x4060b010306090f0e070e281d010e16050303070b06040b091905160f14160602030105030601050f030307121808010b092a070f0b090a0c090908040302 66
    0x102d5500200d2484058410b040080150680224801c2c921070f01041c00c140840c0c01045180c05000100710404d860341d0482d00501850403100d40d80c5810f9100700700001d10140b0030080f2200a5010700900c8254150440c400d001019815610440d4030050009032100c0103102e01909608184519404587d498554990064018002045099528000840b10302c0225035100001d00d51000d8030000d08034610900360301140014206101705c901200251040418000740e00030018412880450b40360072406885600504003160101d0040c00c1c80c050004c2e401c00d00403980240720311400021549000500e04c220248064043c42c601181d9446013150f0100d242e00341e100740501d513034121286000c034a0440001781185800040d41010403000c01c0010600940f00f144a2050a05003c405a40703490b446803c103100c04051580e5400c481c0380003042c0044041025060440c00002c200342e80c070000c00d041c58900d01c107286918000b5200c5030f42804131120500054056481400240014105020180300d40074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 238632958 1250 238631708 238631711
    0x100f0e150d080408010e03090901120f06110702030c030a2103060b040605070203010c03360606060903140706020303060d06020c0109060c03110f03060d0c0f1d01080d0804060b0103 79
    0xc040880e480c44440722040352140000201003040c0c000030702c1500c0840c28250080c5142210100020300560018001d00c0304c2510340d01e0481d01040312040d0f00c245200d82c0060107001d00c42641c0c40340000303a00000c1d8180d00a000b04100c0d042c0d14036010440900e12030f8802c281c0d0403c1e901c070348190441d00400e403888005060f680c0b82d0202d450007401028100074401aaa402d980300810b105042c00d41d4643d800752014181490040b14401c00ba0300c03140c809288141250a40c0041944038220785030a40c840003806140c60000c022442c1684451103c06807401140050580e103021420556620b100d48141ea0058105101007141403400b081800303141c500230f82d00507003018182e80340b1038219045900d003101c449507a2032040d080c198250003189541035a50607034a04107a0b501a00440500c002005180f1030844c100885040001d4185030b03030b002e00303c1541ca058206440350110b07114240220b001c51211200c0c1c0c0300010702c00720002220041c01000340e54200d4aa2129500c040203056011b00301070505 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 238634208 1250 238632958 238632991
    0x405010314012d0b01110715030f02092101090822050d05030a0c1a0a0c021b01090302040f1d01020909100302100819020c031804050705030c0c0717010212100f0e 71
    0x3100400c00d0401800408c0b40107840303d441448040c088940182c40004210f00500954140e07645680351641c0707410b400740d049882c458000d80b10714014104114010f06071400802c820700010505500e41c1c030307403250340d0b55020581602d0f0020842a48103100008003164030400c841081c45100f040b240d0300c480d104201c2c01c10302c00302c1107880312416a400c89072207040542e40c2c265030140d16410032001d910700034080c03c2a4104507a00000034041000e0303000190081d502c1c1ea03145280312aa5520000361000078010110814201600b001d01030340c4000c4a90784100c01180225000403a903944135405c0340d500030b01c024a07001485505070b0700c0c41001001103040b1400348079484004a107600082c41c1c8000c0180140da030395508140d0414003c40e1168426018501d8030341046069600542100d030091620064680c0356105600280d1501d45a9042403035900304510b500c2000d41015000b030302c91806061840c000c0c555a059608001d01018812030420036a0580b04014070712040303140d141c000007c1041900203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 238635458 1250 238634208 238634237
    0xc0102040510030c030615020a03080c09030d050a030b010e06040512151825060c06061d15030a050c060702030a0c0f0e07030501061d030102090405010314012d0b01 72
    0x94110308030b0300404203440301200000d40b82d15110b500085d0190400e20400a50360300384c002e540c0c0c550014010184821500402c02842c10a03090fa01c010f6030040c119410070b00070040003406038000408140100303080100ca0402c0d903000f038200b0741c280e1401600083c18949000704220300c64008403600c100074001e0701c0031011010b440c440d41d01d06c0341140c59403056809540400c01c0e03252030641e03542d54640282d100c0314020140014040101100d4592038101c0c9860040c2c00c1240003013080fa4030130f03031510040049049a0424494400d48a0141b02215a00b260031580500d6140e202c1e00600900316045805100700f6881d294001e040024000303411507000c41500c2d80d50704020f04e45604500f1814030310b2007007081200001600954802854917040c0520b52401101030081600c2c4001c401c04241920b40f142d1442d00d0941c180e80c80b140d4000d0080c0140d507580d040518858011030b403014407075401d18281c2034421850000112659141045001c4a040355622000042940c03c541c1410000742c150756929 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 238636708 1250 238635458 238635469
    0x30f08060105070b0a050613090503030103030f090b180a080309090f070c020411070b072c0103020c1615180b0f07020306010303050a030c0305150409060204170a02120c150c01020405 80
    0x105d40c1448200140c0d130309108040200b00042221000c0000c3e08001403100060800300550341180da06040c4030310344c081e6815003607906211030340040c500c42c040404c44542503445280c1100a00006a52184400351200441038507441103c15450304462140045840e00021740a03c07540710103686481d00b00f0790607d500107801d4461000a202001c0404a401c00511410184254100e2407904000c44500d0020903d440d00510b8100340700030780800542008100e074040e0701140e4000365864284c1d1024503120344004a4900c0501039901c43c041d1101440c0f81c280e0064140401c06043ca03000d17400d8051424030320380d48682c0300f610b0704654048184950b41c0140c4040200038040e5101c0c1d1036642e1101c5c111040101102c0b0344281c0041010700313102c10300c000080400e081204401e02540d020031f00704158108140070303115940c0005401c0b403180c100f0060501d00800d40e038007114800c03034810004004100c1450f50700c1d2240c0082a034801d107040300c54145551504024030742070309201c0016007000d41e1a0002803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 238637958 1250 238636708 238636711
    0x10c02011e05090607030903060b0904020307060c08090a0801050712060b0405040203060a1a360d0309080601120204110a0806060c01060308181c11100201200703020d020a030f08060105070b 83
    0x1b00844e600100600400c0304500400900705001e48050150b4640b0350006940e03424a0300c900d000788145815903509104a8030111a039801028264404280c4d03a4141d207802404201d0340341d4000b03000501d113400e00085900680307003101c2922078980e08041c18a13042000a51004e8409580030f81e080c0350024000c1c8000c802c0c2d04d11410085200c50710b41d102940303070389902c420885100e8030754511603885405070341d05803e03d21100c04003030700d5001502c1194036050b15404000d40003d4031501c1385100000302c03a40408640f07400f1038800d0314140103210360f00d40200550702840c044000400da20302e00041450500c80050694040071000100d00e4580d03030f4032041065803100804120700801d6462800701400d2061205000315480010194050616111140344a104040e00341c0304250b00050303104418801d40141110860156140701d03801e01d60030100b44194000746040b4094022680c800040c00c7c004511190707110307095199040420704814080700c0b01180140224184401070000030b020a05802005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 238639208 1250 238637958 238637963
    0x1a090610020f011a1002010603030c0602070f0203150106020d08060f2403070e042d150b0d0905160e010e0a1d010608100209010c110a030210090311010c02011e05090607 74
    0x71040200138009005c1c03803001c41c0011a080d60b040100400001e6485044a011a60000c0006850307020510340f6419000380c0100c06581403103400780031542d500403406028125103058089409041c0041c1064440c90740496800381d0142c40aa0080f000c1d00b00b0a8a202e9401008038503490842000c1000d41303400d400988a0300001915070340e07850200d00b03203485180c6103274240d952603100380007603c0100c441803050581d8003118551502001260039a0882280e405880c18002e5507440d007070000e22030300082c0190401a10b01d441220b04045171010310071990702c107640e5a01242c40c81baa0810038803142c10000540322040141d5104030580ca100404640c1c2d15019100800103d9030502c0d0000d040c1c5004a0b80303890350342c0d5620400c26045c0582e08a1007042b171041d4400c03002c002c15000302c1e0009021504a90000c0d4110203010b0000d04c6895001c0c0c00102074a00c920706003140f403030b00100111080741130b00c0402404600340d24000d4005000d5121240c03d0200c2c58a1701c00c0c80c241000003ca40c50350400b1004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 238640458 1250 238639208 238639241
    0x8090f0126150909060a0b0105090a0905040b181002070c090905060601200309010e180f040b0a051b0304301205040302030f0d060b1603031a090610020f01 68
    0x5020b03070384090040c0d80d0140481110000c8182c200718460035110100601914510b5a039001c0d150003613401002510010b00e4001c05502c000c035541c0300c0740001380c081150215850000c000003c0c124a142c62114290a24018001c4c0303a4100903050b000d00941c45103209580c1e022080c01c0c0003542c80d4080c003c90405610440240c1080d0400c1c0002500f5540d01d200f11480d0078050080800020b100001542d40310842460843c010300c0e0804040b540000da5030350056a2070008008120700c22000240c2c850149102d00008000f964445451108455056a14030000521800e18884241195001e0b5800078043d100803410040401440c80040070700030a5100c0c08407100003001103c9411110303040101628140c248524517103903070003d45038410340d2441d1081890201d603281003900c1c81e0740198090030324005040e035124007200c0d01080049441d84111b0000c5c0c101011042017600400c0d00c002c1284c0040c1440322551105410441584410f4000004600c41e6460b08c03074003034000340180342240d41b0003042c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 238641708 1250 238640458 238640461
    0x30b061602010e040614210f06061801260f0a050c03191502071b030602130605161101170c0a020d0504030b0a02091c12081308090f0126 60
    0x9042800d0343c8540d5441640342c042c00f00040940340c0014014030074100c815141076841034040c00a003034040c0e1454140c07481580d906030900c0c100065420300030001100c107209050700c810f8101c000b01c00b0034028108100c0754a80440c488040401c1481a14941201038802d1a100f408940746800410101514140c1c02403580020b2814144040d903200800c5010720950f02e4095101c2004c44641040c4401c10590b00290764400e000c0350341c2e42c996202201072843c0111540c0d0f403e002019420200440c20010b030b00007000503100307024100700c0d0b01701c4030160703032443c10040c03942c0743c01d05450840103016041c06000190991030002088040e0711520f80c3c18461b9858078801b41c1c0082c078000007d80350b40c051010420042c00031038080b065140c0e0285500c0009a502c00320308000c1400c0c05400c105040048040801e403c08000404031446034100203a510400e04d5a81c103402250444503090000d400b005d800c0145003001c0c1801c0c551100d54000605002c0d03500903110010b1110300e02140c0c40080e4840b4101b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 238642958 1250 238641708 238641713
    0x8030c03041e1d060a0515070b04030c140c01081006021b03010b06040609090f0203040506040b13080703050304051005061302030a111306030c0302120a0902030f031b01110f040b0a030b0616 83
    0x1801902618059510b42132540702a4540f5800348100385019009e800694000380800d44201c19070000303194071100301c100070a01d8155044c0d0f20381400b60041d000c1440200010551503080801d00122949c070b600801c042c1b80000941d04c080e00c003203058960503540b1461000c20301c2c2c4a07003000b00010b1000e03540b44100b2510b803500c81c0e4102c40c1c00401c086820743c01001030001180c000601c49800c02d0300648110401e440f050441d078591081654001c100c2c03807000c5811414103410a000d0340c030441c050000e403241511fa042090040f10f104a48859000c900d05a40e040d0b143c006034082d5602140d4008005500c10600780342d139103150080100040410390300c420074407940da41030081c0c40c21403509040039810040040d028107031104009010f440c143c0da0b5510b8000541d80c04211001d680c003211000d80b9a1503404100d40c2d0180e101307104025080390300301040c407000e99420034100c071002d44040c500300e410542444000316603a8442d4a0981c201615000c85500ca51346800003042c0040c14000000390960051 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 238644208 1250 238642958 238642969
    0x60f19210507080f0a0305030a02040305010f020c0c040e060106120b0d06020910030203010b0706020d022206090b0f2b1a04050106080906220b01091508030c03041e1d06 74
    0x6400c0f40c1c18a0f0400c00c030072040c45030b00081c044041c40d0b0500701543c681d980c42c070280c4002d01030342c0e01c0a4844d60030804e864a03d15115401080400d050304c0c01c0d10301440c0004140070079140721020801d49544034100401c45644503a1080440c1d03001b0716030201d40482c00340e000a003c0503d43ca0281c440e290f00041624851800011001c1014441c4c142541190f1500d03111071490300441d48041d1120b50001200f0203d281c41da4102d602002c0c0b11100c100a03007481e44403280d6001d005000300004a100c01c88007045011400c030039035620500003ca05403401c40204040383c40708502d14000046401801440d516070030040c096010301703050002e000c0d85011031400c200400d5502c11317400b450070b10400720240107184030301050fa10f07030000f1014a00030385102d401c105034041aa03089070162260a1220000c203000079141c00c0140326584c0b40c3c07688080651129005901c91088180710000d46d4030802041041c06501500307001108410b0034910303001c5649a842e0a10710321546c610a01c000b500740c040002a1410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 238645458 1250 238644208 238644223
    0x13150509090d021c2a0614040b0114060f0a1809020a1701030f030309080f0d06030b1b0307110a2102060a0608030412020f030a030203040305010b0603060f192105 71
    0x1004d000c1d403210b049201028000210108502c001c829031114040300c01c444c9101c0e50385100d680a41c041100b03284903140030214100a903000c56410004038000154201c0018010790700345030040280d03140041d9005190341d9a0310000c011024405000c04023000341d00d01d0b41b40300004117942200075030b4459078100700a01ca0510301881914035018880107102140758070582c0d0f00c8642e0b05040005516985040441241c01110b05001c0c0300100001c03816203010440e000356044038807840c19081030743c540c020007290300d4440c81c0c200900404244001a0101d22812900009100303034425210286590385600040c031005c0500c58022035980f41c1c0d210219a03041000310b80c04200010200300c80c60400845d1030b203e11480c80f42e6010b50000c604800150f641d0404219001324000b0103c81414640b860065142c3d00030384010341d5207500c0c2103840601810700c0b0085a01c1204000c02c0000b075031181d2410003100007080d08100c402c03036420b10408102c48007071014000d041011035550f84c0c41140b152403c140303413424 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 238646708 1250 238645458 238645483
    0x20901150e0d030509090717070c060e01050103032c0301020d0506120c01051b030d0f2708040e1806100f0501051c05090a0c03060b04060801050613150509090d02 71
    0x5400d402c1601180d44581651284002161401c4058880c1641150054001e6140040c499a800181301142c0d0304900c80d4030419101c1c400c14824120460320903401c07101c00744030150105250b4404c240c014410a8019140c203503002e04403000402c2c200d40800c4c2241c0042d0f00c0004170720f0761072062150030b02e840d824501c01c5070052070040c07080d4108140020070600603c45400a00203600c059050000c0b010301c143c038071a1040090030004003017501e00000240107103440e1010002055003c002d0070000006110003000e8002c40901c1c0fa1600d00080802c1030300d0300511031a401000b0291000c0540d8040c09864001d0181d42a1703800164101500807986a900340e02541c14400104155120640003444003043c04415100c0001c413543c0d0315010781d00381050004020500da05640e030203c1080441e91021040703041c00c0e1020051551204051400ca51b816a1860b0380034480325968001441e9030307004000c40440540182c1906d60b0b4407400700380c0b007084c00c1d100e200361600304200851f00141d0400c0307008100b06 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 238647958 1250 238646708 238646719
    0x16051b120f0c041512050a030f1409090c07080309010c09050301090f0f0206040312170c070503030a0f0e03040303020c12010203060a18060b0a05030405010606020c2b020901150e 78
    0x203031104059a540c403524149030f4010b03915903e01800101c0d002a115004081d16409000c00610f6490710310f885940310301c0c1c110086204010300c02d0941d440f03003030680101c2a4040c03160340342204100030070003410340003089460041c00070850a40020101c502560049407504004246c124600c803000c1d1202d5082c1d000f040c003030383c500b481e4000030560242c80c6100e059041031500324050118000706040380715a40020341030b0450007140301078490707128186208440444130104d030b80b80c80320366009845106101014200703500078801315408024690001c6184442c0d10000103407001c2000b0307844d00b543c00039881030b000358101e0303540040c0303038202000007002940200c0021840c1d85429800907500500c0350040b140703840c15204c60340302076890a52202029020074240c20351555a50540209143d1080307504a07003039428004002030300b600004804244c808002c082c0d00342d46545a0102c1c2881c071004410740e0500044005174005078036000c1c075280c040c00341150f03140c0d00e141d038221019144101d0060391314041c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 238649208 1250 238647958 238647973
    0x6050c090a0b030903070515090d050a080c1318020a0210061a07140a061a09160f02030f12040b09030702090402060702010302130e18011401050616051b12 68
    0x2a41d424028605942001002540380c0c1c072400e03003107071441c0902c2400a2852140301d09040c0740c040d0010001d031085c0d0040c402c540c215824040222441d01400c829100851040b4003c00c181c200401e0240001010160760105655510800ca0340c0500181c1080d84a80d83c0c00122141c1442d410b1005251407105d9580c103010b003525004c41465511000290111140d4010a140e42046080e44107040481220011146601e54a0400304018610000c0c00003518032170f0003002c50780c0d040803468203100d01c08404030320103021200f03081035540003205605c07441180410000360110081d205d025154100318142e080403180f03803c0c6803501e0100d4001c0c0c1590742550007031000600582d01c0301510f660040d416107030386d07482e40a00d07c0141c01030b0103152420340c000040c0d42400700d40e40b440c089140d0300c100142d80400c0300940780d943e204c5080b915030048240c1d0306100d00d801400a81031640091242d6440e00100c43c9a4010700d071a402d0400062103103110074103032a003e040c032040c90f000c030128504812840203070556 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 238650458 1250 238649208 238649227
    0x702040b0901061d06180d021c060204090c020109050c010f0e09040c0905061804170405120d1b03090302060a020f030a0206040501140903070b360601060806090415022506050c 77
    0x205081014052041c500c20020108545a010540b40d2500301070346274650741490f52410310080e402a00400d9000d52070300d85040300c45881400f85281d01038000016107030a041c00b50044620700e4120041006105115010076441d07100c3d4034019205a000cbe4030401946800d015030401910405410144a4480007241c04000303031220f03d00d2034002e503000081000c1c00740d402d4202085d500596100a51000c00c003e401095150b000c5044c409400040c1d9486c0d80301540340310309084043e00d003030000d000a10a1a030500050600c02c0040401e034030035004403100050440412403031039100d2101000141c10180500003006424002c06848000340342c011036161804030140390343e0707000d05000507100c4401c040100b08802c903140d010700401c0341c01c1c800034130700548000700040a0420110301d000581c803a0800002d5070511502e0198000d440003003000c2c2650712113848941c0282ca07440079039003400303a0070442520039180d032702d00c9600000f000c040210b0782c01c111401d1030002c40354001c04c103000c0e04404200d48a070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 238651708 1250 238650458 238650487
    0x5030106180f0303030b030606090c04030204180206220b040b0322060c09050109050a050901050118050315190501080309100e03060a02120112050c060702040b0901061d06 75
    0x1500e0a41c9000107900503490300c0480780e001c4a5100d545400090a004028580d040d00010710510042d0b0444119850300c03000d2104044088607031015603402030005000500d882d401829015844124645a098254000500c142e229003460396007800c0303400d08804400c100c1002d1034024011804824107140c601580c004061000a085001a82c000344424100c0e550040d6060b441c00d030401c00402590110b1080505409014001e250200c4d000610000d0245040f808800a403800540321001c56440e000055a10071480b0421041a180a0301d01103030382c0d24100149085d4110310070048010b414005444500384034203190060219044c0001441408400401c8460700301c02506c6000341e001c40040c00b21002c51005801e01d03898058030050041140345600138208803907101d4030200050f681e41a6440440760418002481c5400c001044030040c50316034081c0c0b2050740041d0022030384503000c1000400b6030760240c00030004603c0c41c1d807200341c400040101071151030310240c0d1854503200d0b4200075400c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 238652958 1250 238651708 238651711
    0x1b111206100824070c06091101020705120d0509060c060702060a05060f010c0809030111030c07110303070f060207021305090105040302010612110d05030c0304030c031727061608030a0509030a0503 86
    0x1400010320007003201144a0350b21240070540101c000c101c104810700d001366500e88c2c48010b06005200340d610106280ca0a06289030100c50301b07400614900c0000f41058401d50004140d40e980f00000b880303402168681800500c0c490b01080c0c2c081c0046160400101048900c00382c05140101039035070621030166004100c0c081c034103403c941c2058560310003000003030240c14490500940000c000c410f100c01c1030309038005411624810010800c03006004010705540e4003a103d8042c0444803c008082c1c00300b0b50300e600500384980060b0900f50440741803c40b039416600103403022061695907008000c181a4207110f60300207080c2c1503100380c503141e0031500d0740100c041401401c0e82c032505c87c102000e02000000c008540c8001c00300d0041d00e0311195242402110b0021324482502c420440088080c68489504200c03032000304c20000c3c03610b9402c03c3c5030445105005c91000c244c0c2000e01080903230000b1070525049005030b0712400c0825500d1414502d5203054400190101485030b00a10890780b00c0f039001400d81b03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 238654208 1250 238652958 238653013
    0x5010f08182d0d1d1e060a0309020306060402030403170406110703080403031d03270d0b1902030105150d0608030d06090b0405010311011101090c0609060e0f011b1112061008 76
    0x800140e02100d40950510041c551980c054000a1f02081807a00358010f40e600314001c80603104a695507800740030692104540c0100014000e01d4040b4107010007004558102d0301030030002071403254061000c211540189010350109040c0e0701008105949400340c40400e1007070444000d01000e0f040842c568900030324140c1000b0380880d0104544602c00c0e10765103006003200505103c3c0071019418841c003200e200f80d9540071900441030710240300301030760300841341290b03400b170526000103000c040908002c2e0415014583d1081c0c4900d40000d40350001c1010b8401c6010280000440915242840d0100d03a101e015050060b41040700400120b0300316440c0031500c40c42030810740f58008100301041d004180880c0018100d41045401040d403503807120114090b250703291100820311503010204489088042c69090000715074108404285041008680259100c2d000c03000d41c13100403030300140d43c0503000a044845c03640300c1030402040032600502440184140d4020349604807524040003480102a20203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 238655458 1250 238654208 238654219
    0x6080c1504180207020a03030f080a14010e04300315030209040615030803010e070e01031806111c020c0d0f080c160602070303060f05010f08182d0d1d 66
    0x42d0100c641680444080550080130940141d40303e1034081c041c0d02c600130500c00043c44140010750070b82c0003841030340060031355000d04100c81c0c2c0c68082c00e129032080081080f10050800d502c50410a6a04140c0705120002c00030806080729101c40c0080849104074262070800e0803010040003d81c583c0112150011340003500410383c403035070324681010400c103035000504032180000002500b10403980200d0188081c0c0c1d1303614210302244401181903070510b034003200b031003000308240c0da000826a90180342d80e2507450883c10b0500459207048114044021142c0490035000541040c0241d42488903241000503420034000d83e113117554005040c440001c041400b209030005411000528108240d02251390010095588580702d16006024002d18862842c100228130740101c1c140d80513140e8030141503000da4032000560b40d40f9180151490900740c0c10340c498003490b10b50803078a60407042d100c001a085661109c0b54048024003003071402081d803441d80200301e8641d20030911005480d0400d1f00c4560204c64 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 238656708 1250 238655458 238655489
    0x504050610061209030c0b0a0b010306050618100e030a080403020a06020105091209150d2901020d0503150d080309060c04030206090f0a0905090a0302070b070309030b070210050a06080c1504 83
    0x40546003460001b0010380048203c0e0200000e085194000c1c0d641540d00b0b03a8140003459852050218034003a840d070507501e4185a0000b8030b00f07400c001d02c40b0780c3c59681d9842c0c019030598007100400e040684c0302c2070503030b440c0d00c001505000b941450030551004001c1c51000700f1983c60080d5403d0303265404003040c00b010060003d14402141c0e110b01e5881800590b0030b074110303503400000d00420000c0c0f00000444103030030801d00305c040c0406042180941000c40603006007040c5000c1d12800c13200c0350f10080074440950481801d51200e512064003a0001d03c0c81440195620f01f4001c244505d0000000d1048005000c208030900c0140c0340e81042d03803002c0ea803d942542c1d03a51400000200e00040941001c58880e151000b0041d00910001d82c500b0030b03e0203038003514200d90b01d6103c028154816400c01a0201e120140100001a01d48103504c1d407203d41071043d2100b001010701d501e01a40c3c01604c0900d07003e0f444030740a2101074030074032152280c1c1c2421141c031617803a0017000d8100e4075070149205010034802401ca = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 238657958 1250 238656708 238656713
    0xd1a18060603131b06021504051207060e0604050102070309090b03070b0d1e021809010b1603020f0303091c0512150a05030102070b0109050f0f011a0c0d030504050610061209 76
    0x3403404080c80c2e40b141e801d5040c120260391004442c1c41602c05c81c0010b20034101000c0141158841e0180a45d4010700030340f01103080f0b5035240400341c2c022082250f0055441c8184d00301810180644c0e40035034403e4002503518055410010208240d54000d8203401d458500804026a00007404c84100c80b501e0b0306003500c490f88209240018910305220a0320f41c400440350420702e4007260f00802d0040000354007464502102400e00450010074001d48044003020014255402d0040c1804241c3c10f01c43d1040b15080303020400b100742103810540da100140e0384512490340d0288010065103203850b0b07092500f541440c0c6900c0303680210f41d40240c211496254074208605568841d45040005054060004c0d50b4800700c914100452903002d111700381d4a01c1c40c0201181030202c400d0b000900941c0d0300d0b1000d00c00e40c0d00b040201718a00c1c4c440e50300304c91800301c00c00c114605440244200c1c1c00c01390345c1d9100081c403032519092003801c081001707010210710525807900b400000d811011500d400c1c0001a000101d019552 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 238659208 1250 238657958 238657981
    0x120305070501050906010e0901150911070203030a09030b1308030a0507020715020a0b060f2101060f03260f1e1204140705010306050a0603051003080d1a18060603 71
    0x90050542c0d402c1104000040d08001a620304882850b600000340d55502c540c0c250807168814411840c1c010141e90400c002122a00700c146100f04a0041900d403851f142c1c000b92840d8001c500d4400459aa40001c10600c01049100781e400b115844191800414540e28101540700061410794903e6550f80441c2c07429208000e00406403c1c8030006415000a26001955882e47d0b8481143ca406d4201d00281050a0000031002c00301c5007c2c0810741d644090260f4503000e088030b0445c0c881c40e590303507032400230f0840c69181c00c0c0310007540101990120540c21200d400341c1c80e00281a9040c03034020030810080d1426800d0121148400c6a20424005c005186030b0b116040c440c00211104082c001014001032100002d0303440d5001d003084007142c482554620054068803a188120b40c1d101729004810060f45000390030407a1701811481d070207030f03100b903c96541c03840c00c0e00700b00c00d9070f05540d5840d0404003050b00d0760b4002e002150000c49865a20110f21254401d000d1300040c407140c090100072001c501101c984 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 238660458 1250 238659208 238659217
    0x260604031b210203070c090c0203040e0c0d020a03090b07030b060d0b0a0305060406060807170d030507020115090b010e01050304080306040e03190309020f01030c1403060315150127120305 82
    0xb2001500620003000c002950390300100429a608141903034006060880d6208100c035444044e0061411705162501d00913109200400b21544020200803074441460184001d00c01d0921984000503e4601810005500c0600030f054000b49850480d15290301d130f41e030745c00791030000540302e00100d1110140d00100c0e25090403540b0080c003510402d814001004101c0c2c200341d0641c0c0100b0119000b144ea42c80c0500c1200103480410702070b54211a00b01c0c800c1c58481d41029134450000c0c000421480b083c8100d540c00784141d035014048003a691a070040341907900520344e8803007120911b4651300710b00b8240c86511080c840038055030b101d130b641c0d064484142101403040e100031662a420201c481c01e550708024019140f090000c0388184051007614041e58002d00c96404201d070039917180500001c01030b1107405580e00c0034129560500c128000c0d9040e8401c40410a8814588036070050001c0c00b000700003414103a48465244d201031b00504084444555150300e03242200d4070007010b5001199241010f0700c0c0c0780314 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 238661708 1250 238660458 238660493
    0x103080f0909011202040c05160206030a1803020f070902070519030219080903010b180a05071e021b030a0308070305040c0320090a0501050d030503040c0e01260604031b 74
    0x10b4800002000641c8048404116000340d605120640c01c140086500d445071058080464526030841005030404101542d4031161072130001885214407200b9010354541240c00710010703404400b00031401d0b0010b001403801088001425030401d199517440545901c8064a020100380c0740c0d12513003041c980300704001c008041500c22003240d41810340c20105259442007081c14007035070030407110004904142103001400c82410650540540f100b0441f20042c2202030180400c128120210392000550050300d070415001d55002010b040680c21002404000403400952080c0c0100004801007600000b0707841c0d02110310301c1c001440c5d40c0e483c5003000401e1419007000d00000ba11a02c08501c0c0507444110300108501101c00c0e000d150303142c807203a4098076402d00801c1d810411008481c800280a00080d64125104a0100680d140c9503c000305031030100364032590107100001c003000c51030707405e00206c3d81004240300041c08540c07500e41c80103400303044d0301d951000c001480c80fa402c009002c1030313290000105a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 238662958 1250 238661708 238661719
    0x303090c0b1908220204020d1e0f060e0106050f250f0312090c05010e0f031501051201150e090a140d030e010204032a0312050301060f02060f0103080f09 67
    0x141d1500e1a0aa55550440c0c080b0200312428003003405544084070200030519061510300f92000c5036400d100103900300030354400b10152904000910031110040c030403000714440340001142100c54550f18251900e90780205680700c801c0b401400b01c15070203403c403440d101c10302d091182e0710a4a15414180c844400021f80381c0c06000300c034240100080c680c4285002d600036a9642c004c0280356100f04d088400400c3c004011200140d0200045c0d4014909006500001480003220b0801880801e0030403a58070744440344a002240103005501e413003c907112120641300300800c4007820b411400c1480305180d000d0704180c44040c030300045050004000345500c040d40a0401d1040f84c940000741e55480101c0341031600802d0801d602c0e1384070b00c481407090390202d0742c2141d80c0c03822102007244a401c00346112040580558040c3c0000b202003601580d0410440c80d25a03521030340d961500754020820840d5100303810841d007140d401d000b16401c41c680034a0549800c1191150744100810644000340304400315039070040c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 238664208 1250 238662958 238662967
    0x90314040b03100806060f010f0302040b030a0509061b0a0c080d090302060603060105030109080301120f020618030c010302120f090715020703020f18040b0603121804270303090c0b 79
    0x7402140034500881c0d280c08050701c9241c4030324240342c903001c0071980c0640104c03217540c013481298400e00e413100d05012a410b00601c1d01c0c0d02c0703d4900d40c155200f254482e041c00d0b11340060151034141081810360011600401c0c0c8031b41c0441031030161380c51143c26074650400941800740414404004c007112001e03d207840d420001040305181c0651070b61012510759100c0d001b1a000000c880c101801490300c19a480302095103160708101b90780845000040f0b0549000420030090780050f1595401002c803880c1c50340c0712014500d46501014580300380e03488058105030050110081c1c0343d880151a07074000804420b4640e1568441815034030b420b003143d000c030701f00741c1101aa001c07036541c010524009680c003d90f0103d000061800a01040700721304008031400c100075000242c040b80c1d010300025088200141a0380e2184c03000a000340c1c1641081c440c8040c00109516200384610f090701c0b41c403c110841c07940e5195440ba11000c1c03105181c0c1c10b6500602419180c103510b03010007803022550805001801c6a05888 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 238665458 1250 238664208 238664219
    0x403030b0f09070906030e0f0a03020318011b0807170a090f0f0806130311030d02180a08030f18090103030f02100209060f0a17010b031603140a09031404 67
    0x80c00c501502107024066001501849061024041d48200040c0d02c400b051140707000401c400500c4014040b1216006010305101011003e000d40200b86000e5801591201c1c901ca001e81003020044a10905104966089004000000521034607054225440544995643c2010121007080341c0f0300b84070302c3c400003c50032155904030400300195912443c10b0440141c50301502980d03440240103951841d4000c1001510303200e000c2403230103100341c424034054408407521046e06141d50030071004180076940103c1c04140203070000482408281d8102ea180940c6860a0580c80c0c491046c0741408849520000d403d088a0340303488000c4010600103010346000b50303901d080c01804800000361000042c010000c1007808050039000703031064107900034051440c04450b03c80d1603902d944040c01c4d00d824040000450107080e150f03104480d0003414280c0a0594904c5e0146091415100c00349181701814901a00d2010300c207208820b03190b22034a04540026000e0240c181a9210a442c0d600021041800140404c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 238666708 1250 238665458 238665461
    0x9030703080913110a030605010e061207051c06140118031502270414010609060f090305011508250506091206090a03180305100911041503020a0518010e061305040303 73
    0x101d00030381d61b0802c0100c2e140ea0044405580d90103802ea4030110030f00426000540000390150000358504045281169030500000000401d84500001c141c4e03445041110000d200000c44541400740b070302a480d2912684141c0a40040f0301019118450440651102c03424650440743d141051a158030328460401e0031401400c0300a82181d40140d0600040348041008074496505036075407529051201d03070400208890024020030300c2c1e004c0124098000001c1035083c402c0421a003640490f00c120642000040d80c0313802c01d6020410901041c04041031040400021620140c42084500b155190032045c0003665002903010714152900036041030080413100014240c0c07060b4403d4550210100c2840f40303000002c4841e03c0041e205401103c0c80c030404070f1266200c0d02c80a4400c840707006000d04444080f0303003141c02d103c980b0030340d295159005009500d0303c841600000d00c7e044583c0304c06901c2c0c10204031003400d030620821088644030700c00302d0340b15610343d280845840380c190410003007460107080080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 238667958 1250 238666708 238666717
    0x306130c050c0a0c03020301111c020904020d141503060709050f03010f230c0910120603051204260d0f110a03120506030c210109020303030405070303020601060201020903070308091311 81
    0x3841f039031900303a111000c510044143c400124501101c903648614845000c0041c0d400040b4907a40960308221002a90b185485039400401d03510070191690700c0d0082c0110011120105003600c00d6000d4010049002d5004000d02d00380d42040e10200a501500c0c0042070160030136460214078142483d42000c203a021426034a19440a666026141a103a00001280ca841444081500304203a5010016558010655110403401d41800050420b5132610b919040c00d1032280810340c00030000404111403114500e90120809908000760203001500210540c0c0b40c124600220a1000440c0803e406038016000c803507c0c0d02e040c0094400d0529039280c021b1002004030010201c182c9417001249550500007075050600502030981207850100c08010080d20003c43c6030301d4070540d213540d501c00050f1014006540151b03c100010b040f102d040d4075010b070a05038160010011a0302c1404806060394000643c8000c69810085095890803554045a181d02d80c010304e081c00f260400030708070601c000000062 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 238669064 1106 238667958 238667963
    0x308030601120c0f0e040b0306010311030f01020307030207020a09050601020a081b120306030105011502030405011d04020712110309130209180712060b0306130c050c0a0c03 76
    0x2842901c103030f031580500203060081d2810752140c0040351080440781c1181e0034071051a8110100350f6a660520000d802044412a00102c0d074a0608c103014100701ea0b14000e659a2402c83c0016010b903020150803170250b0f201c40740000f002d002607c106802110140e015041d9861182c650410070740042c4211031903910468220031205004000018040020188440d128900141010b0071034030145d00400380412a28548041c096010040b00e00360756090800d064201c01404201400141401410750442d01c0005e2000c103202c007405c0c011104003161f80da0301e4544501ca000c116201d003d1500000d80000d42c18040c0f402d5501d803500a0003044002034681c40b5218052100700b003e5117016074521000c180b4454405050403141e00603c3c02600a8602607480c0d4101070011500e8811a1b40c0c1c1104100d990344c60082d02036118408a6151088a80445100b20320a0400880026061004 = true := by decide +kernel

theorem cover : BRFrame.Cov 238489208 238669064 := by
  have h0 := BRFrame.cov_init 238489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 238489208 ≤ n) (h2 : n < 238669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
