-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0976
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:36:27.5602+00:00
-- url     : https://prove2.me/submissions/513fd76b-bc4d-4907-885e-ee4590833592

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 175359712 ≤ n < 175539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 175360962 1250 175359712 175359757
    0x12070506010f06050306010207061d040213060f08090c0108070504080d03050901061a040b0d0b0d0f15050609040311120d050402040605180106030b03030403060504211103040504020c03 81
    0x40c0641039a400790b089052039620b84000781c40754001295034600585c031280c020701025104aa14084150f9010344061007070254a000074140d81103011280c90700c0540140c20002c59911a1404500001c0e50400c80071604010482544507450800114180301c01c100c04038524603c140210b600a00d0a002a1303065842e0074074000303019042c2900c003a4441c0d82041000715440c1613003076030101c0205010b0701e80c82c5010724204038100d1039000f0405484089039104c00c5500c0d5a2514413015580c1ea104000c088001c240c1803030700300705141c1c3c4100b100c0a150300d89410001303d5112403546036085a05401d100210400c040d00c041e150212001c03220314112804642041e451023203800440c0104d00c01c6400380409900c44061003150074540b0114140800d0700001040064029401840c501c00c002d4103407490309450780c844106543c020f490450f00034580c0032000c06940c0e00700f00c0045800c800c0d480d02a2514220691856981c021802258426540040e00d4561130000700304980001c4803120000101506 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 175362212 1250 175360962 175360973
    0x2070b0a03051014011d0d020630010b0901080405010902040e01200315090406060f03030c03030b0f031b1207080d090f060203030a09030509041409070f0803070f051207 74
    0x420383c0c0100e501120070a010591650019000e51068410f940c1d030402c43d411b610740d00c01c6c3d042c070000425411200b02c051800143e11404010700000301c480e0442d8240060341c0728000c2640c0035100c2c11032032242e092001403000300c00c0b01e03003141c0c103802003441c082c8142d88640c240140184421385000b51311070b1920907201c032007a4040d00f144080c400792004000e02c0040c0841108014032080f29440c401000310140101c01340384c62500c0540140c01410001801901c854401611100300c2d002070380400c00d8801184109540f50051915041054618608218440d408256982100600c511010700350007611030150303c3e00307030030001007003e040c0c01c840210b030b41c80c0003031912280c02916140016014201c04030380c011010340040121001039000354599034801c2c688100a00b07008004030100401007004c030f0601e40c0c40c3d020b00600c000010a628080f801c08a441900c2c00c4040c0c4d04c00b68440d07a841000f007101c0030001c410340d2103054101d58000502000c91034800d0900907900170080446401240c408140030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 175363462 1250 175362212 175362221
    0x3070512180c01020105190e0f0703060f0b030c03061611150601020f0d0806010c060914010e011805060c0702060405030a0b090105060a0510030e0309040c020a06060609032102070b0a03 81
    0x6540c0c002c0d290b152603003000490030780e541110320021841c115151061407884c1d540c00482200d00180c00d03036001045100100e42000d84951054402c182c85080301000015948140d0036481411802490079010b0440400e4030365000521b04800f403101003003401401c6000c3c08940000c580d2560503070b000400014508442c0304819102c05005200d40c80c5c0004c24540b0000303640921044c08d40b01c0341c0841d074074207004480085510f40d00300e852903220303828003001510503062051a0041580041504c484100219084403072000701075020098040310940410800b00f00c0541201d010101155079445030b001003151407040e503100503050702c034540000040c4180d10f40c3c0c19010f81c0820300280500c0d00c40f1070800c501e034010ba0042c2640300c03844a03060382026000303503c8030944c409040d041d0303410881c507000041c0440e4200449030016802241c4420204201441804060030050411000e1941144c95072514820901340c1e2920000340d8000c032810a038000c008480060041c0c1211a079203074000d01c0010040c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 175364712 1250 175363462 175363501
    0x90e060103050d0302030103080708090d060f200415050c0705060316030b040c09270e1f02031015140301030f02030f0d021002070f0807140f0d0e0603070512 69
    0x50040c1c0c0d110f0030590388607001701ca04032a0044074a40c141140c03030325030291550000c8095980209039000313020006006010359501c40c82c03034010006d40901d40180a088090001c0c01040c4141c400f04410300c0700100020b020880b0411a1070015110241840098a4580c040d00140ea0040d004020840e102516100c1844001c0b6207641c140a681c00d01000e11054842031182c0c0c80c0401d0301a0f50900c001c915030494003031800c100c407410800c0000003613040011200d03000580c09464000e80c0e0b11203041481c0070b25500707010192100461551416041c444c0c00388180f4020f141c40802e40710b0032030a15174480d502d02c440e1100888115642c0e560359140c0240e00b241044c01c03c90003800350b60402c1c80c032424003041c0d8004d01d002ea50080c2044004100c0081c0081d844030034121f491840c049020390214060034081c203081d52060010106c00c150395401a803401e00302c243c5c560f030039502011200030425031050210038800c17800d96010b40c41e920b43ca002a680d40c010b003230390007417003900303e82c10030650078000800c41848 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 175365962 1250 175364712 175364723
    0x706020310080d050a020307060c0302070606080309010f0c110108070c12020604110409113001051f03080a12110d090b0c180d0c0503060703021305012f0106090e060103 74
    0x280c200b4003134415002e90350018015070014004200450303084e4210300e05041040c0b0b40180340c48103554800d4115006500031074103691000c40c0080c00d40d42c00030800000300400707013404181090300ea81c440c0191502080d07818104201780c00400c0c2c0507402420000340300c907408044201d424001c0d00c4020340e0340404940640d11624000921505401c0a1181c0170a5540140d24014070008150500c00c4c40d4103440b00da40b0031029076103c1c030310302d11550302c24600c00e440a07840046203504058112020344034007204030b985400c44c0c4070310400016914a0855044080c203003404142142107030804c600401c441c2c0c01d440003087c00001c80820b0f00d105580601203840c03256400400b5510f881c40303040c02d280a90f101c0c412500010480b03407040e070301d0005541d01d041031003408240181354480c008207040407400c0e0b509001194021643ca07204101500e0790001a00c0203182080b103090214481e051a0381c1c000704140c18075804c02e400038203070243c20b4020382d020b095080f41c103225034030203044015075035282440140c80 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 175367212 1250 175365962 175365973
    0x80708010b1c0b060c030d02030114031f05060f0406140405070e0307060e030a0204020f1c0c14030a0603320105100b0f070c0e06090703050402030d0e06070602031008 73
    0x4505036000256a0440182a10b408114850180da00c004100700c2c00150352084050104410100e000c20062000f6072280401580b00d52400104003012012080054440d81028982d0301c60382c0c17146c14506215003201c40e400b29994603881d000c5841c1807030107080c40c0d4001d41407010220300f601c040240100000002e0b1810001a525480200c44203105c458259602d5001a9010000b031441140c400c0b1407900004c0c1503032100812076001504903800b903112003082c01070102d8000c03042800c5211401c000880004144500882c0480060280440345a124024640032012442001d565440003000c0c55110458100e0030410104c6042c0d84152016609038481c5c401408440682040c00f0705400f1b20303003a840500090f400c01c61180180d8004c4080b00c4010303e810f20040021804800011004015400440c105820400c0510000e1b42004000c481898200b6081c00300684001541c054041d81d0f030f00d4034110112000001690501c64034402800d5280003100740443c51107690b1102d03040707605517400c456 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 175368462 1250 175367212 175367219
    0x3060c0a1106010303020c0d05011b090501020d03050903031305010f09080316030e0c1012060609060e180f060604050607110a120c0308090a0503010c030b0306060a0e0a09081908070801 81
    0x42d55001c0c24040180180c100c00c05c43e40302c50800041d2814414415000400e64000c0c40000d0700d5850000714254000647d02d2000300038030b503014406000d100c03502d807400b4802031510881d816501d2001500f8031039403500000c0d49030140b04080d03000e0030094001400511040100b401c2001490f0410351b452410705049085891600d4003c1c4240e004e25590f000140c405a6a40d100b040500c68078840d0b410b0910018424400b5100200c8c032905000e070a00e51901580917043c802c0003000004040790940c016017910798a00b068880d154845503010404905100345540c0394008a81c0a0046034041500200040742c401c041100403a88401c81d8081540c1d0307103010320369070700060150a40d071290141c0603411002051021aa9002c02000c6030100039005042c02e5589002090840c0c100c81d045800084c1d80d000740410b01d01d03060000070f40144013211450505400e2601c00002044e025182c032800641d129603900410000c5410b584000d0a0381d000280100041d41010300186012034014000640410020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 175369712 1250 175368462 175368497
    0xe06040204030c090f09120503090115080307020f1201150e0901090b07080405191a010504020a050405011206050604080f07080321060a27050a110f03070c0203060c0a 73
    0x35400c40ea0000b1240014034602130b5484020001110034a407016124402c1d10042100c0c6401c0003440c05859031801d5a03440d080407034134211035481d030407200d01005540301000660000416079100035011140c1c10aa11004070000d075407001944104038880d401d02c80c0b446501c0c1380d0a030100301182e40640c044030f100c2d070724051303c1800c960302450010b0040300301102181d1041d1085441030381c0070b44a40b00b00c844803040c0100305e070540c5441d00000c81d0480011072240c03100b40300d503000a600411040c0c80560030f1001101c030151045c000c038000c25041001c401d41840c8a000036803c04002050050481983c0715190341b032407034039450004124600b1303100350310340054604030000880d6404200c8814a00c1c08500300501e00300e00000280038541e202c44c1e0100040707441d07405590042814007000c10390090300c02d280d00755031085d20700003000c50f01650b20701800705d40c41000351022540000c0524181c030340d40390358901301078405050b0540c02a405224240402140b000444000c1200010a48503001c08250310b5014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 175370962 1250 175369712 175369717
    0x90f0603160c0602070c030605060111060613020a030f020d060807080a03200f06150103060b040e0a050c0d020d0204030312021c020d090f110a0509090c01140909100e060402 76
    0xa06200724100103201203184100a1004514855076001d417401c609130f1103c00b01c42c0026001030310150394401c05d1151540c2c00c148030f500300c044907001505280c5080e000090701c52600d40040340340c0c00d40006000101c50f00c80d42c0500411403070b4010071500c810780030041320300601c000d00441070302c4d1180700e0000c255000001039402001d9415500c0c4010039215071809207461030210508412403140740c03400300b40d007402030241d0741c458100844d84001c4030112000050654095922804040c08100410f1006141000e68075901c420b1078000440c1c1d50322040c4214a0b03502c150107004640b184085101140720031207070004d00849010390f48603a0480c5a05001c18101e1203941c42d8401c1d2004401d0b614101892180c02030584074000c0c103030010f40c894250711075402da009100c000b15031103040300708075607200d03d0318a40e400090841915007680c5841c04002481c2d84100c20081541408201c1c10100142c0301e12038110b502101001e0031901c49401c2c460540304502c140ea0041490300c0140d0f000060321400d040c800e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 175372212 1250 175370962 175370971
    0x2106090c030f061012030908010f05091218100c0813060906080603150702030d09080d050c0c2503020a061d060c1b0f0603090703150605090403181a090f0603 69
    0x1154803415151001003070305eaa010107070407000c1c0900000002640c0c4006c1c458009880b034403084c08a42403600c1e001d40c906124951511046901e000e1000341c1c400e00203114400c1800f08190b400703648042d10380c3c1f0191000c0305c106600612502001035a258200002c0500d4000c0325400e032181507075551202415110f94104841003509070313110403601c0030005400000590015900c0c0162851729885101000559400c0b03401500c10305000a0b0300c0d285508a489003d0f40310948212550901c0f205251441d15140c0344085158039840c40c80311a105003550300003c2e001141c0c0101500c45441e500c80d406481c010000c042980e1074515103140c040141003a0003100d022104c008090550458286900f4050500305c0c80590b070000c1d0361036502011900c417207000b50b0007500d140000b403000a00d14901458444c41d4442c5200a003070401030104165101c0408054000781e060400c800101c11414a03400c0d922040e40c40b09480b08400560301258191110040c07030041d1060b19940c140361050420311009200948 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 175373462 1250 175372212 175372231
    0x3040c1208071505011a03150307060507051c0503181005040606090b010f05041806031707260703080601020307050703030e0f24030402030708030a170115020703022106090c030f06 79
    0x6441025900341c0c3d00a59214006070002c00c101001c8034080ad1801c031003030f0000008550002200c8003400400c0003130380203e445a060002503c04c510f400104540000303402800d06940c402c014483c0844203011182400246810800052905080c0390010388841e11580c00b01c54075204d5401065403080c40d00358001016a203446142500d01030108801c0d04890f420080040e640303080200c0015009802c540e01400582640f80d2202e01904004c1d070260643c3d07030000c4416020601c1d01e54030024500564650b1134060074404183e64580c00181e08600c2118001480c600942c9408402c054001a012002c00c90583d2110b01d006054000e005803a444482d201d20500141445035544440210085902c5880541503482d840d507610700e41451070304580e1545000c5040c50240710381601030100348030700400801805000100c254800a91141000d01029000705082281c200c140d040380a0491080020710302120020301e8401d00c0350f6141c0d00c10322913a601c2805010680d40441c000017602ca030042d072104 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 175374712 1250 175373462 175373489
    0x21c060806041a1302030307060e010c09081b01050909240d020913020105040f03031106060a210c0b040303030e06070e011b021f0c14011b0503040c120807150501 71
    0x5203c1120030070000c02c485100c0c0d445401d07440041c0c4007400548030079031240301c021900c4800c406846007550b1070b20603802c0c01c00600001c00c01004071700054240e070500c00c00003d62400c20080b0012200c45c4903040000b900490301c00d05001c1d640c2400c11031058095261001138082803070074003c200081c4074038000a540b0401c103c012130340040009400e11030380b6105040452500340da40b45031002040c400d03801980402e00018015130b600b5401d012660b440503040b903414020908110000741610703945150b0019800c0c2d01c0c0000c8003017140040c011030141940c00703007681d151956031400034007400b43d00c007009544d0300401d40800e00e030a000d09484542c800058403161002040107031070015007d407140303040c0d0313000c000310055545584d401d07021810a000d840e59503034803008450502e490040035803198411039078945518030300e40e903200ca0b51000300030b0703081d14041d982d80e00c40e42040c00005520ba0030800690141d0b04622040004980013030a189116050310f400c4000b102000b0000c82e00240b14508040648 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 175375962 1250 175374712 175374743
    0x10504050f0301090b13050d090b040e070c0c080c0307090902090c030a0b210606010f020d0e0310050108010203011a04060c3008010617060a09090305040801021c06080604 75
    0x184000751200107400056000103548030041c00440035900c5482d044c0644140c4014003e06003c1d041d010140d505000d10754a10300150f8a85c40d04c5948102491048108046090700c3c1c42490a0200da07500510301842d9680c0303c0403c15156840c02a00a20900c10800c000900100c6130088807034403500141002030310303a580c9000041c90b0340000c0a10b07040542c0c0d0708401031140d070703158203440581c005100e00c41492014000d90a01e06600500302505011480041185482d070009259a01c2801e0b4a00855043c1090380400e151845080c0d0080d4010705207400410003900550195048900980081202c1500d803406d81c6c400f0312650007076800182940024001007002120f001d40240a41c2c1109806400d17004505104619101002c0001900001c0104201a440340c4d06465400e0500800300325070810500203103c40006108482c5202d80315000302c014107000d10159001042c00038029541d503400c40d0000007900d101c50204c12041813404101007a41400021513070701c1680d1001c2c100521a51 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 175377212 1250 175375962 175375969
    0x8011706010b0901080403050d09050604020a0e0f06120f07140f06160204020913090605010602010c020f070e061206012408060609010c05010b0a061814030307061e0207080a02070e0601050405 84
    0x10416028040d041161076400289d0b842050001401000a0000b0b0304142c1f04001049190b940201417190b403030700c180101d0907100004d85400540c12212100301d8034003114054200070055401010034000c0610014081d070707a510401d40940002c1f10004000e012840c20030186014620052041130480c444034001414070782d0051200840051149507800c0e1142c2c9100c09a035030b030716812079203240c03560300410000303809000307a0301000c8050015100030810460702c15950748052080d0b4002d0104900130a069440700781c94490b17841488802d072030096031285c0300717882c884014110650144170b0b06d6100606040c452014280210001003ca44c40d200940004540d910074040f01550380c2c2d541c50544400540c0e54070078680040030652a418042e55a518448603018103580c000c0c1c07004403901130000602d40e40030049601642d03004c00002140c101000c500c0c9110003032100b140c803201c1d200003a440d0900601c60b0203080320303425075400c6548417074481d450403282c2041580c0c0b16000c40c5080c00305000518 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 175378462 1250 175377212 175377227
    0x7030312050a0b04090302030a0207060e10030b13020417060a151214061f09020a020c010f020c101715130e16030f050d020312040605070c1208011706010b0901 70
    0x8079550080f6016202d4400902201c1c6003c0703040707000d079100060802c0340c00d406000c3c9030300510003404c00310001800074001c0341c0c00480c5880a4001c15558003040304455950380024030082e01069021500c8545035004070000079403102e08042c0500c00e00d4001480c40700d00d030103608180c00361031051782038541c036000441030464148034044900404d403070720901c4440c4081000a128010306402c5441204034610740c207408c4e1250b43c10250559004000c405800c54001424140c0d0312028600300d2030000c3c0700ca03422410b1100102c642a84000c03a030090902e0700d58030040f2042d5050452142900d06d4460244000f10440e010203c0740d0040b038403110b1101d25640c02c6d801501e07000e01c0c0c80169403441040390b8040c1400c1e010350f0005c80d01025847d00b028140801080b5080181200b80011842c01380402e46058902000034002070a40d0748803400603d42501c140c1000c1c41859002c0c003108410010700e20094011170090007018180c5210042c8004000b40014481e4126600f680d032031441c00c0280e800460303400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 175379712 1250 175378462 175378471
    0x92103090907050910030b04110909040201081902030109020a030b0102010207052e020316090b03090c040f020f0304050a050105070c0f06090309050607080702040c0e010522170703060606020703031205 88
    0x3c06020f0180240c69000b40381e105504603540c0010341d04441c1003000110703124150a02c40580b0180001e09054039101c488035045902400c10306c120782d407030684d00000360b45440b1243c02018004000000d00c421150080c2c6410100c91f141486036009840049080380920040038006500c4900928a81c0300d01004ca0280c6045040400111700d0031403002c17906a0340203841560004580701c50b1811081c0d88000c3c03000241201d00000352440c181040030564a00344c180a61744980e0b91014840c403000d810f681113030001140c41050549070710f864207109842d11940b000c192019400d240002e000c1c18418503180d6001c036400501c002c0041031541721140100400542103040c050303044d8010032103a86105c007034004184500302c5196240840c0c41440103842d1025424024040c40b01d4410b680d5a80040a503220307505111701c0c06000d0180034900b50301000c61a8800b1115000341c5940315a0300e04041008004e482c05070105003c0c49076038a6080b65600b005120240000705900c90940024009030030540e0407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 175380962 1250 175379712 175379717
    0xd0c060b04060e011a0307050406050901091508152b0f060510061106010b042102101101060b040815090f030f040608070903120302130b030c092103090907 68
    0xc41240012804850341500030442003a0300c0401046410300c6109100c1c8400c94140360b04d41135003010400034103280102c1c000d44050200101d101305480c2d101c3c442c084018407003402040364019040340c0191042e041501c80d080d00803801d0310742d07072000d052103001091303c0300c0c0d001078008000b0b40580c0c10f4049001c01d071508840f010030942d12400490801d00450340034640220034149058034016010742240c45040384003050360003c0004001c842c070800305030303000c03241060310340d404140f1402002e500005100c4002903000c1d0402884400642d07024a5000d1890110701c001c00001e521880f040909000e07920544d00aa480500e0b000c599071401c10686070800041011684c902c0c034903803159410364200c40603c0c1d28001c0040f9042145560260010384c00204038148072808500710340700c0c2080307007582c1c4e2400414140c0000e22078580110b2505a00300400451640c0d9032241040a400c010640c40551032510442869034210342c00c0803494005c090b900c95140083d49082c8408050028105000740100d0070f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 175382212 1250 175380962 175380971
    0x31503060c02010c020609160e06030109060e070503010f050c032a0f07020f0906150c030f032d0c07120504080607032a050d2a02010f06170d0c06 64
    0x28409000d040c0c4150642e800108152200e03c0e4003e28040380100251800d900c800c41ca410400084503052007a222004c6c1d0a50f100c0c0c1d91030012034050559020300801903032a050000e410401c0c04205802078075401c8009100200612410009071401034540c043c8012040000c04c600707000c102d802c4a10406103080c1c00c0c14030384411005a070b580d04104030113004513000152103000c500d464081040c03c4440ec864907041818004081559021684d280b0b02e9412070006042c54050301c10001e840070701c1040c18425940e440c201d6050005140540784800200d114142e2200614602826041c413404840511601307120503500d403680d081030b80d088030f4414400101301c04515103505121a41c8a0001520040303203140c00110345052401d81d40203e00c1405800044c0d03071443c01e51100c1101c4440600d40b10100d4802684c01c590f60a02228100310140350381100280340c2002d406410000c5807030b40109040090342e41e640f40c890101c8021081c0f104158114181c0c20050a014940c4020310b24011100020b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 175383462 1250 175382212 175382219
    0x30601020111073c201909150608130213060e0f060f011b060b0901030f0507080610120303240f0b0a08130503090a0b0a0e0f0609010315 60
    0x25840301c0410307101c4104070703812100e000e5078280071110152208544c1c9488044107a030044812804c3d00c00050030b020080c80003401d205100404100e54460080400b81c070440032142e503982c02c030104e1180d81507090411402018104032a01f020003211810344600b009941c442c88a5610f000c120001280d100404440504510340f0a2007038202070a1610003901e0903080440c03030300d5003d41c40100350305d101d00c0b50300c2d030700e48600c0c0d07804210b40c1c8914501080c0314103070380c02c03a00d0f009024004082c07099030003030319810000062140340280441414007132030036035940a440d926400d49900b0b045402d01d030342c0e003440e1404000078200b030b1000300c4240d40079160008100070215441d02040c90304900141d10740840c15400c1c0150550701504000030501038840d145481c40c60039004c0e0401100402510749115850074030800d0000a0003202c0d100c1c0e90040c03141c00b500e521007900700b086030000d0b120600040d0031810305210508014017062906e1600401d8281090307281c0004602600c084100c00120240310031000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 175384712 1250 175383462 175383491
    0x2d090e10080c011808061302011818090204110d2301050105030609070509030706020d020c180103020616050d030912050c0a0618140601050114040b04150c0516080d0201060303020c060306010201 85
    0x3c1b07010704044001401f00300f26078000141042c02c4c40f00040c80c0307800141010461081c0d1001360342600e080400010440e041d40c0e000282c0245900c080d107000a50b00018503c41c0e00a03a03620842940030341d00340c0b42124030b80c0d501c00000c01a2090184a0101e0b40c104080f0304030745070a88840354408031518145141403110300100f41000110f50008000d40e110700d144008442d0107001c40440840709a4074a54042e49110100050741c41c1032001a00802d00064003280c0004004000e034081500b01c4112100124030080083c020f0811040c1918150304010a8500c414810301c100c8120010020003807600340420780391301d03000344a9100c0c421100c80c4104925800528800b227180c421640c01d2000d442c5a61401d0005000c08010300300403861040d0411041c440558000c00392001d03034101802e81e042c03000d0060410307100c07400032502c080c0840c400c0f40203c07403110340200c03810400c0d6510320702900c11035200d01a00b81e00ba210b17940030003400b603001809100d0842c1804005140d103c2814030002c207006982103040d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 175385962 1250 175384712 175384723
    0x4170609120706020c1b0a1509210209010609090b040203040b0601110f0a080c07050402030105060706090602041a07020a14180402030705060a20030f04062d090e10080c011808 77
    0x200346c0040c0b10a191585403500484c5000102004074104012a8103c60020002c60060044c00740c014034030f0305042080a06203c44241d6a5805420900700703586560b005000450f03d8480e411f00c40d42412a9000c41e403c080c020380f40101c1e0f010a518019444060041d5050701d800c500d0001113105801c4403800d10001000380c41c042d140540001030f1350b02d242d000300b0f82c01c01c0003036000a4040e5004000412950b1507060448040b660406000038050324075143c014064465648484a00661071034840c1c203180300310b001002400e108071500f414056640c0000c4040006683c0d0b03042e03000348445000140c4815841c078250780107100606480740c1944440004040350002070718080019540124030144061040031080d007840000010360602030040384030780440c8500d000c0c140030419100b0381805109040c54100000101038408120b0900071407000904140003442072800c80000c03000428503500b449d410280689600300e01810110212a005594629a102a4124100c0d6200f000115107109111 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 175387212 1250 175385962 175385983
    0x9090103080930060604180327090209030c04050403080c0d090206030702010501051806090403050d0f0e1f0e15130b0f04030e060310060f0c02041104170609120706020c 74
    0x30000951003c0040c4140f40c80d200801d418040c0d881c0c0180701d07598010012560030b2295040c5003050b48680694200080040c40f1a02a212114038010105007100660094010201d0075000c980c52100d00e14104000d8410580d0083c02145d140c1c00881c40a2501b00c000302400ca43c18880890300c8401c5900ac01c050b64000c455070001030350755a0043c0064500072070700c864429202e5201e88010309110700050b0329182c01030001401d02000041c059030110654210904140c01000e0400200b0030201c42c01e9211940d039200c0042982c1c0b03100c0035203003d211520940744050040d000814590002c40710765000f0307400c003814100462818a00f5000001c0702e104119109450705c48400314141054503002d0141078941201906c0344000740b007048907146440d00f00008840051409070304000d045401902c003c1c2c406000a50094104481c500c903800301c0700002d1084402100201c1190b14088100c9626880203640e0807100e500136024200c1c2c3c4200210280148034024140107140a0302203114038901815801d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 175388462 1250 175387212 175387279
    0xa18050a06060f050d0902040605030303040606090b03070f0302041a09040c030c0e0708130305210612030708030c0306131b0807030203130213020d0c0507051002090901030809 77
    0x60800c1000d11090007032000030203480c20201c03044003c01da4094a50b003d1891520310035a42c0e00c0002082d540c80d6000140140710103000d50303640b030500c0c0c103014010b400701d4059000643d0500030b24141030f060000f845c0046907048045080601d045508000c00782860460000c00312180d1140d4a04960b24800c2041c0201c3c459101c0d19400c500e9840c00b042c140c1c2a0b03511036009540c1c0082000045504030008581c0820101119603000d100c078070b816a450f000b8800c00014428043d80546802e00038a00d490f40204d400310f070b240d985071407066400750342e85c03184200080445406001290312010203001031038105900508106204c3c40a46242048a18000b452030907800d0f50f44610b0042d42e0416901c64120f142c4e49800c3d0301d103280c8241c1340314981c8520345000307000300240b5140000e110503030740c183c1d0f10300c1d060140c043c00050b81916008001c0d0300000c6096415028000010b40900d40e00d20807207204010107402020141c0c610b450720149a00084004c40c5c120303101c902142014013882040401519004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 175389712 1250 175388462 175388471
    0xb030303241c23030c0109060608211605030f0d0b010306030b060d061107030c050610030c050105030a0213090f110c0307060c020319020c09071d0f0a18 67
    0x205030208003018940da406018003280d40c80303489001214005000c2c2a50010711148042d101c07082200040c80722942c60ba501400041080701c8041e006421020301240200760030300060303484048064840742c91a0080398112a0440054200030f01031001d03000b003402480c6070350801d4800740c694a040d035000400c03410141200152001d9514454460010b9204c030a01e4104440c0303056541d9895200d81c0588201e01c10000d21000c4410000b403500000030044145680c55161681d900e0041d1400c0e55006007202c1c24003500d00050254042a0941030440380c0044c8501401d524040066425a202510140804d80c00308200c600382c0f02e0703021020009103044c80780050441010804401140c1130580c40c00d604080030400c0c43c0340c421001041c0d43c070f40768000d100000d039007046540a92452041a0035100c01c0b4034003c440200c12078021582e082c40c1402510700c41c001c1c0d611038404540c0501c1c0715100018841c0d6003501500c450400b00704d99044544003900c4407807480e450749421011010078202650784a43c40c5e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 175390962 1250 175389712 175389751
    0x4240807030606080a1a06150c33040308040f140708011503080409020a0c0b0103030f0f03020306210f120702031b0a1406040f081c091503050a0b030303 67
    0x328800c1200811104005d0304c00484a07648004e5004290b00c29074002e01d0349600030501e143e48075075440c0200d0450101050f42d0741008001680ca502c282265030820105920141c030227500c0169850052004041c0090156a541d56051b11410009030083d281c01000f0b002850000c3c0285907205008504d85000b071200c28a8000d60500b501e06891240d00480704843d000c0001849000a60b402c0e28903501c40982c482c042880125105245040003402d6040c00800001c02d06800003030641480e0b08541c2d801c880c0d044c901100350305a202c25552160012030078a0307c0c074135040c43c0041400c0b2424001c070039a00100f042c1020a03181a13100c008014400310009008011403034200680600c912010900c02e120b220350200040c0070315441d100e00c95104214903543c15050b0340c0c0c8001c4030041d02541c04d1b600d00721516030250b40da5615489000d230a07042009103d0220080c051501c1c5030440d120b400c07881d82c180e03981b00b07001c60181902410300040f80e034458100d401c41e6617080c400340d031040400300c0d01082d61600303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 175392212 1250 175390962 175390973
    0x212060402120d0203040b0c0a080a1d0402091c150204231017090a1a07030b0406030c090e03190509031002030f04061d0706050405040f05090307020424080703 70
    0x52585804015030000d05090440f41e0040181c81c2207840704030200d900c0305031040c01c00d420b004203998010400840020074683c40b5030482c240800c1c40c2c000440b036607000340000091000324800c0143c44c0760312003e544600c0451100c61156244050b21910b46410460740ca0002601a600280c124104c030002c2003200d0207034204041c50041899000301e94040c0007001c1389a025240c0840c1c2060800380600c0000040c0c15a1410490f1a0100c1d91040102907001d0404e040c0343c0003850107440c0140028100007a800888c46c2c1401000e058030707082000d40d14001d280c20010801000e448034000c103280030034030580b14007005900e201d1102c06507646605a4542000042500b0411240645910b1920500900891450300341042c0c0d88a50b1041000a0181070400b0519244c022030002a8061240440114155034030030054022503009580c20701180320109084015290100c81c0005546e2081c040d071809403400da041898072070900d68189103912065042c024032800c058001151503400301c40100f08002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 175393462 1250 175392212 175392229
    0x1504030e1201020d0b0405060625050d0203121e0705030703180b0f0702071203140d0203090708010f060605070213090f03030e060609010302030c01080907050a06021b012a0606030212060402 83
    0x91049600708100c0c5803100000300940641c0312b100f81c954905a0628152281035840142170980180071100702e04004c00b0300a640e9404401f881904000c900c0200ea4207814040d90903403d0802501c21014540d00c0c1007088501c0e030001041e0200b09900e411a03011401a0242c0340c038000d601a000005031860a04d00001d01794001424036400c5500c40002040402517811b400c10302180d040ca080840896641501e0606020b890380300c0d001d56200009008140c5800105c0504580380c190081c401090085810402c85806101e0034000c540104000380041c0340141c003e142c0c5005400b40000d00c49000d80740da500e0980a4881100880d958500c00b030342c07403103080107415070002e402c0303404600960642c0c4c0866120410b00e2911030501034404045000c841d0103114840c050031002e0300088019503141c8000b035881c820b444002c24002d02e030004004595104100341190450046210700d140c000c0c50786c0f0810710084640040c2d88141c0c0d035074408401030f42d81c014060880d40c8040001c142d54107082c010018003c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 175394712 1250 175393462 175393481
    0xc03020405090705071e0503070804080d2c040509010f050f07090e1303050306010e030f03120a0e0601060c0c0e1801050a0c0f0c050a08070501090c171504030e1201020d 74
    0x80014011503001480c65106d0060700c10b0b80d80c041192074810b41c50700d00c0c554054414003d002101c04a0081078030000020fa0a0306080c8c41e03a580d20703072101a26801c0c0d201e2100b452443d0b1110010007131001060501d50042504614080000140d5180c0b400f082c6049400c1585d0404200004205008001d50b00c119020040c007500c0744800c0300380c18100c17000c41011001100c014140311000c030000d11a81c1c014a401124038101070280d403101c1c00f041c015583c4070341c08041108203200f540b401140c0c4d4400d051051b90001c03817100c3c0081c08281d080c03840503a604079000780d0440360380100480108030051242146801041c0030034480420741501d4400e1380c2910720003000f00452500d07000e0b032200740f20b038019100c0d92143c91034244481d000105007003060404c0e1a406000d0a04800050420704100056000059040c041e00c042c0025a80300c40c1288200d9107044100c003010340c040c9c0100c0217164291412a5001f82c0300e41840c034640001680402c482c00200f01d09102a0303540804c2110740c1d43c52a000b1580305 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 175395962 1250 175394712 175394717
    0xc1306080303070305060117040506012303071707030c0b0918061509040605030106030f020301062c181e0c04140a0906061a09010906050a0c0308190c030204050907 72
    0x9091103032659482c04000c00380700c2015110b0010038a107034003411200c44081c0f041c0718002d0152926007440f903aa0f910a100b01003003039801201d1101c811444000309000c07202d000f005460100e1405813425010345152041002d103019032040000040c050003400c5000b04200c280d0f080e107508040d010007004001d14014003c000c003a8004001184e50360b0043d41929645c0742072040e8480d40b40c2404500240200d42059030151b1a000c400720038400e40c0020400d000f40300310028002103441d016003003451007650401c1c140203c922054400c078104507212003548000000c52050180402102c050f280c03141c0044c510540e040780c68a85500280203008001c5441d0080e1010710042041010098880380020130107100e40703036221940c10801440b60840d000503c141c1d07820004c0310404489201c010b600c045c0c00703103000c61081700001070a5801402039841c6500580c50300001c0607c680c50a4400c910010f03c2888082c01d01100c1402070742c002c1c4291064441c0c5a0341c016210350802051010b8600d01400701c005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 175397212 1250 175395962 175395971
    0x306061203090d06020d0608061f080304060c061811040525030e0102070506040b191a0d0201230a02070b0304050a031b0209191a091311040e0c13 64
    0x40011001003280e45502c02a203c509502029090a800a000d1882951001418501c002420317a0707000410601030b0300880241c80c1000b8410780c90f40140c41d40e84c881c40901d604280010031010b405845c0f0b40d1107490141101280a12101038004038201207810204d5110300300c0da00340744060400c0e108080d440040d01000d8440309147c02903050300c802d00c0c0c0300c80c1000c0540300d0b032440c100014290142c3d10310507031003411603009007070138580058030900488102400c903540c00a40c02080704140111103200482c81e0030024840d041200b409045008104280d0502001002d800703c409120b803558905210307003402854032440301341c00090400015038440385c4805814414000405d10115002407450307070500f49640c88880448034410098204240694040003820404c01c0317103444c82c5040d01c00e2400b420010452a00c2d44a051001c1140741c1c130b0031941000040c4005040300c2c4003004803080d203901a0b01440380749500301001400303030341d8030303510f00e80c03c9812048208942c1d0604054244401c1c9180c0c90521 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 175398462 1250 175397212 175397239
    0x5010e090a171605010c021f02090f01030e0c0a0311010905010207080729040602010c08090613112b0c0f03051002160503070c0e070905060414120601060806030606 72
    0x2420b01500b0301208101540009880114101c2c860300d540a10b0307407080c02444586e01704803003c0e4607114259105801c000803524003110750f03006442220140d08004080c8000c0000b2180114020012441d01d4031451003400c5901403d6034502c2c0e5008000d512992102441122540c00188100c600740c0c0300b0743c1590b012a00a0002e002d02241d0841502c1c00e240591081c1650013110450612403000d5200c85c0c0300300050045003466040d0071102c080a01d07512040c8680d00c5804100d5030702e44081b80c0d6a08001c40342450000050090b942e8007488140c0204404d0b4440c0c19412000403c0b071180c80c00c6c5a090031b00f805000104010740c540d1000400448400f4041146141c6030152103d12a44003140c4047c1c0c00506202000e58800598215540180869484948910f00b40300fa2003460f0107a0f0881c06070003000145403030701c504c15010a44201030240c03400c180c600840e40c858200c0d00a03a0a90042c03640c100641070000800c0718a000f0301041d5610703031081c1408010b042c201140507191900070742d00d602050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 175399712 1250 175398462 175398473
    0x906270201111f0b0402041703190813030e120304060e04060e0601020604110d0b0106050d06090608030702010c0606120c06031407080403080601120f06050307120c03020105071b0905010e090a 84
    0x140710450f200308003c10b41c0b070354401c00580244150340010915a40a50032100380010000213402c40c4d8807542084414409040300c15541000d048642480810079404e0050000f8480d5006683c4410003404003464084d40356400360454109400c20000600310040e419031500d040d0203440020301e481c042003084c504140000035114840140040c042003580340e42211141c43d0f40c6031f1401d01c181c0020341c0075400e50311050000c0a87d0301101ca014000c81c140300011070014894070458048450250085103000515030065031405007043c0c05841c02d50340da0000240581d003004c000e41d03249109401801130039051180140844040400c1c0306108000f00d420800c0e550f0300500203640142c2c041c01c01c022181d40f02001220b0501404424a903101e062a4000640e802d0079003103641658011401d460784039488512071030090700c8080c00a08070342540c0030b0420265000c3c0c4010450603005010303005000340480d2501c181050f5a611940056030703920b00400035120140405600030542030090440d2200d284c481 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 175400962 1250 175399712 175399753
    0xc020c01081503030a031b030506030319210b10020303071b150c0807020c0303090306070315030602040803090a051906030b03100e01231603090627020111 68
    0x50621400364082003042c41d40b40380c105056140201100d540c0c009122005010b0001d5440744007801c0c03058010051414024040c0f41c0c40382c0c070040c004600b02500c021106544e50a200e42490901c54003040c0454401c1c00b210f04002500304411000c0f44801143c01404500290b149461045400234000e1280c595440014071904507844c1500e800c1c09000342c2448040d0381240f210112855180c00c82c2941401e030030a000300d02c540741e1a000d07203180381010001d140e00d91140d03142c001d5064210358001100a03001c0e5020016450a40b810341c505a5180d40d5010120391203a0000a0b40e6400072800b01da0703d180038131660000c1c01080c1da600c01c014a0740e400065031321074140104030900d0344a80384107010361800c0000c480030680000e000e0004401c6010302038000c0090011310402c7c0050306902c0010301018540341c0303008070703580b40b4601000c4880d114224010032414900700c4000d07848104a5103680f00e5911808498114076118480070180e80c40050444109012000303107603000240c1010249244586 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 175402212 1250 175400962 175400983
    0x30f0b09070f12020105090301090b010e010f08031b07050a090f050c0702010e010809010b0607150509010c02030703141c0e06062b06090506010602150f0112030c0f060f0b0a090c02 79
    0x1c030006445900c4c030058a26024417101c1541541c0b90031070700024468142c030654100c4064034003405047e600c1c1c0c01650f800019501032440564800c01403c86c4032800720002d0701c0380c41c11010070b17503620940381d0002403002003040e4800c3d0500d40d2980c003200c03103010301e510640740c2200c2c0c00d00141c2d1400d00d181d400607042c1001c0c0b5001074140442e0303200240440c5000c0d040808503800050500d6502c030b0080c900220000f00145405030964901030000b83e15000500c10403402d00c1d403e400071030410959a40888000540340e00001e414034041c17004580000c04901c2000341002c5147d030100f500c4081c100311b1440c142c1c00500c0140715100341d0654254403400100050310350711501c181290b255000d818008040c04001000504070b00ca0301c00000b0780c807a408a81c1c044c60001d85042e5805980f0f40c0544440805400e005100000c0840104000041d00410020401034880c003021315082c0c059031592001c6900034500c1d02241d50701c0b42c9226500b45402d00d40350000d071291860030022044d17100d42c000d5981d00201d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 175403462 1250 175402212 175402229
    0x9070305090c03010f020a030b03070308120c04050904151406060316050c0a0b0f0703090b010605090d020d0605010602070f0f0b09030f0a11010908031903020a11010501030f0b09070f 80
    0x310381180c106120340c0301c2c003040140c02803010102401090000303600250341000003030320b400146116813a02164400c2203d03003040003c2c0c1410160200c002000e80041c02d01c2039411410000001e0a032074558069202d580a0154660380071340303e0141c101518185604c0243d4030fa103100410186680d4082926000701c4c0f003201d00d0030082d10002054a1510421200c020b0f14846c2c24000000c100d41007045c2c502c1550003410b240c07142e0311822030a40c2504c1d0450402403810042400500100e4403410140494540040c080120500d00c2d802003903440e10a820103440c0c594580005111507901001102d004045040c1301c0b5080514010140300540e68600030020f4240c4000703074030881540c0400103881d0040411040d00c40ea01c1d81d038540921308950002c52940400e005610018284002000b5141415000d210a40c201c402c9100101c0081d409102c051003072000c0c085580011380c0b000d00c1943d010311f03c104490f98114015090817544420b004009078143c1e4400d09042c000b2403901603034001102e0101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 175404712 1250 175403462 175403471
    0x2150603070b030f0106110a050304030f060f05041208010b12040b1e0906070917060f0709081203040b0a0902010c110a0902160c0b040506070807080714030a0e03010b090703 76
    0x10000781421080d0b844003051074008014000d5110704403240c14121519512440898081d41848a0712640c82c0003002d0000e4000b44400c0020400c0200304180b06403041100190844046081c541114400e0b202601c490190000d59000c03607800403406805803010b0010282440194031420502e80d000810050001640b50003003191202d010040d401d501c42d102c01d81000070b16100400070340c0d400e02102c0d00000690780d0070380007411042c0e0b000002c44401058018241503070300c805c00b5240450b4080d210000700810610005820942401a01604005041815030342c0c2000c3c2003a40081780040c00c4c1c4001d8034603140c1e500380144e8000700e9401c11036a015207660200e00000c40007940034010303075000d40c5803a40000381d882d031082980c065901c00305200304040c1c80b132543c50f000c5440b441e01880c0600c0350006010401400414590005091020300c5000380070701d400507640d900c481c80110701c00c0440891b480401d0a401158001c1d110740c080400c190020004c2085e03102c000307000e90001030503800c02d1643d41d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 175405962 1250 175404712 175404721
    0x60f090506180f0f120a031d0916020f0706020102120105060c1c1e09260706031808130e16050f030a0207060c08061908061609090903090905160215 65
    0xe104c018102c03003030300419041054410304e08550b00c40000c410200e00052008c2203031483d1200e2244028494140503105107499900c00300844283c1104002090039889803100a4050544c01c11541000c0c20b410740c005a242c3c4c11000c04200d4001040e04140d11031441409882c112805c0003034a0780602c0c03002141403d407442400c03410ba40f2500c803442c12040707c280e00c01700c3e0000144c000070b0071011103504080682c0f1000514a594140c0340c8099041c94650300403072000c0213458802c0d0041900c40e0129405200050141ea40d485280c0c0d0248411020810b4585010801421090080b9501440c0002d002e40d2010b02a0030040c00f5110f03920304012a00000710100d14a05078a90550b0100341e071100040000800e0408007070420383d0300700d4141c2c0c03080034651040300044488810620031903201000400890321220651200058084038a030204566803d0009022080b07000e9030404a001e615075251940c2030011200035070f00700808407482c00c100c4d817164154440e40001c071445039907428940d84005444 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 175407212 1250 175405962 175405969
    0x801060510180e2706070c02120c040207110102070b120406050c07080a020c0907020706140a0c150605010f05091309080412030806040e0105040f030c05120301060f090506180f 77
    0x400390041d1000205050400000954401c4850f15114440b0340d540c4e000c904501d02c155441d8011500b000000d07200700420b00042c00c20140020603928010159000c000b400808502241c200c00802c1d200c21413200403110fa1540c040c0104000382801c0c5645503e030504030358044250368406803008040030760f21300025403900c100d0f400744d505280d2300480d85591141300200007075543d02c090304068480c181c500c0c080b82e0030600000e100003c43d9069181c204105400c440c0c0d000a1703030010740300c4c801032026048a10380000c9411b0034029503000900d400056090505000400d591070200d9070b1414064200502c19040d500e80740c24090303007040702d880410760900516007140140039582c8640d100e0186140310a08054104d0501c0b48a40c00c2981c04020b29002c0d401010300b81c03802641e015045805199040c0003081c40b41c000b17900110b005904036501c6200d0080c003d2080c1d40300768000c0d03000641071400d25440d2580000720500400084445605004850181104c0d184481c2041803242103a000e41807650345 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 175408462 1250 175407212 175407257
    0x207030321060303020a0501051f06120f06080d0909060b120603010b0301050c0d0f0203010b120a06031208040203010e06060f04090309030804030c180501080a03030b01020c031002130801060510 85
    0x4100c0798041c8900c076503d240c00b0f959a080b5080c100e50b01c0d42050005070140f5400e6080c2072030000305150b44a03441d4a0940b00382d8103091501c81c0000b00c2c580302d070b0000d0740d12802e030300a04d402400004018107400c2180c10b402080b8415542007800e006040400c100100403940c01540c14070303051480700a28a8a40c0700001b40100003280c80550154204401c1200d0a418a0058442881c0d00103050007541c01d110341c95030491009000381c803000d170414048800d1040c0030591b15980420800d50002d20981c9a0700c0d460314082e5405640340011341c01208110842c00d0a010b107020902c2280020b1010342408800288100d100300c031414050380e9039500200505204100a00080d6000740b0f101d82e41d0fa8603070518142c10300c2e043c0103140001e481840d005000c1c140c64031405040b107840901404612000d03070780c100e02410710481075504603c80c01103e5100d1b5981031000c03404440a0240060741c8034000c5944c0b00d141613150340400c074564035162013001b071610b506806040381440e52030702c28842d8511902e11290711 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 175409712 1250 175408462 175408517
    0x91609110d150614031e1f0308030703060b0412030c080c060a1d0102090a051005071502040f05100203030c0f0702090a141308040b070c0b041e1220030f15060906030d02070303 77
    0x1f422004c000107012844004500075101542c09201c001d40b10602060b892280e80306800b80c150102c040c01780460b00c15210004024170410b5043d142c441d8044002e85000b106990707424100b035454251340c012010a94041d0084011f40000354185480781000501845d03262050900132805042d05a58540c030800443d000741d0b40c40100a8046141854408000e403c14000c0d84201201240081014545040f9084070461143d005602d507640352a80842c054100da4120b0318014400e008040059669003451845040381c841c00065015280700018013500014005010a1000e9a541c02c0402d0303100007202e0030307141c2c0310100c0c5503640030310f1a080003d90038551010781200d9001c80c0c00b083c5866079403819003003514281c034258021038840d620b00c800c4241d101d034000c004540034194207141500c0400c00a62884008043d2113090303000c2805142048501c0340955902c1c252142003148034548590040d412000c10740041c10b071360b0020f18001c0e686040c503000240a020000415107811110300080718400c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 175410962 1250 175409712 175409761
    0x9010e01122d0e1b0105040302100203070c09020301050f040504150e060403230313060603021c0606150804081303020d0b0906091609110d150614031e 66
    0x18566903603500641e550400304001000240d8608240c039590140100c07907181140f48040c1044c003030960407900e0400c2001118030706000c0240800409a0390b00788a80025890a4001d15074480203442c1c03411040203e5089071f00c04c10302c1400140410381b20000004400b040540e4005a181c48900b0301c10079000c8452215850141008049070b452440424103034080e51007a154280f11070b003101684026014440002d102c001020710014410464015100040500036803001440584a401040b60b00441001c4080c0c1e150002c0800403c0000c0c900c01d1800401c00303404a004d4299201c41c0040c40b0a6001d40702520091010074101214038000d24950006c41d8020309400d0001c0d0306160030303111020f0455043c00345000301d42c00541942d10220f22100700180350002801440e09000c64040100702600100080040c18040681410014801c80034a540003600d440e400d1480c04500030101c2c00c0746424641003200600a00911000785c214484145520071034200c684d41e0740311040680310034805504041c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 175412212 1250 175410962 175410971
    0x20d141308011d07050306070e01031409072102030d03021c061d0106080402010c08031803040311090c1201030b060f040212090f030a090e07140a09210809010e0112 72
    0x4080310154003550001061100f02040c15501c5085591165454824550150400000601940d20a00c0c1e020110b4005040c000348200c40d51610100401e8100c07107c241d907903c14041403020911002c456a041d00b90b030110b00031004860b50200751113504894904040c1a00400d00c10461541141100d00700b14841d5000c0090b290b88030b075002d0f00b64011980c9050034810303020001c20036500c1032281c03900c0389406840d101d00b01450b9680c1c00541e5400240016241c607412031107441d40d4a03051005200940c095001c800e802c0c0040400c01013800406065a201c1c060204031603000c00440118040c1140d40124803000e040c1d4400c004211807021544440303030300c144001103401036402c0c2c0050131400347d0005c600b100c01c203829500c151643d9201d0a100540403648000c0e04102541c4548901907114181d440c050840d41d0600319041025040707014a50f000c900c007843d0511485051400041030810407655403007140f845a29a24180d00c01d000c04241007000030b03100340059074011810840c502011083c100b0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 175413462 1250 175412212 175412219
    0x62e0e030303040c031a01140f01031d06060a06080106022a0604030b040c0503071a09040603050a030503150103110a0522090902030105180601270606030e0105100303020d1413 77
    0xb00e84d4885804116404e0350a6000d03001e0407400072070200d040e5503000d140d076445009060b0030048034480b2801001d04060b1a000300c2c00003a009409500102d00440b0010a40d40c1844001c012a0903080e4200e48208044280100151a80001c4520440c02051000c03103101d00202204a15440961035280e00501c0000d40003040120740303c4030910840c05007600c00d14551f21401010b80702e04080c0700d08107500024440032040c0070740810051414070750051000900030b42c0c0e641c0361418282181001c0e00440c00c04404c10100b6101c8004040303014500746020048070955010402050040c540e0032401c0160200e81c005501942001e1031000784ca003140c200604035520300e110009800308c41c100b05d009500b410007086400d04517804803034212001070701815443c4e09200e1a035080038502c210f510040021142003060010251141001a0085d682c0110b4192200c241140c25940042c190403280c86000c0c3c0b041010950220303441c1e0b0565014504000c18201d00d04076550140a15020100702182840002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 175414712 1250 175413462 175413473
    0x501060519080c0306040e101b09080a030807030c02010e01060b1e030f0402040504080f0703052502101d04020c01022d070605040201030908120f062e0e03030304 71
    0x3414007945044010089210401048820a0055075400b01d0f0890500116003141740580000010307084200456041881c40c40e0640b0994604820000610104140720709a080c0d001c1264070207420900c001740288905a6002001400001c110004040d5605150182c0710310070b4214801c6419414024001251034071002030003540140c4c805642880701c940352110200518054a1003900034401900d80d50b580d0b50240009000b005108070b820346410000c05060109c824050a2403a005c0e5030b40f0b45d01c50012281c0c0c24000d02102c511107000000800ca5480140e690380c48240c08140c0e40e192100a2185181c40000094a000715165000f070001c51040c0c0200c80c154003030044049501c0f00500c03181d203141500d403020340c0c41010003550100308005c150013013485038120769000303031041c500010011190f031103441161708081101000d040070302c0240040c014500d1000e6400c0b0350203c072840300380d9280c24908400030300c1400c10710b010b0000c2080004800c40c09041400c00040010302501d541b8a03007807400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 175415962 1250 175414712 175414717
    0x3021008060102010f0b0306010b0a0306081515040608031603021204060201050f0c0309070911040504020f0c06010e0603030403030e0d0b0106051201120305030424060b0403111206060d03030e0105010605 89
    0x10703030041d072070526899002942d07401001414403024001d01456401d000721041c060b4001880c00007856140d410014084c0d000b000045d0030b030345980506101c0340c10002c90200e919507111403014403903410050f05105001c80401254040b044801d1b80e52841603440c602a400c081100044c0c07080c400b0b01050002d40b8907019080140f00c4c803880140d01031607582e048a2400c06000555541140b5030010000f8020800298041a0001d0826a817641007907502d500180684c0d20100011034402e5020500d0140404200722017030141c024501d00088500d0540e0120f60380307000701c0c4400380410242c840c0c00710039034039400b610351681600061202101d613100c89011f00036500c1444c6115595210720000501441e1040b092400c3c950315549031480d640304c58681c245001d100c0a01c4411040314034012461410740341c495000104a0f03038071481c0e01c0b0b928500f03083e4504030480403007074050f00364945100c014801c0880e0080d800301044420507032280c001d0408400034000c00441c1070441d86020000304260360010003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 175417212 1250 175415962 175415971
    0x70302130e07020c03010f18081c0911040e06012d0b070605310b0a0f06030605060f0a030803041e080a200d08070503090a0209040b15152203021008 65
    0x207022103960801d801c4100c85800c0380008c030408800e80103800003943c46005018000d00e4845281480504002c910704450340f00100311040406215510194141402a81211740a400183c0881d62400141c40d03d0404851400c0405102e44103510103034041104541024003275041005468150a10b4401d0042c10162924480d50b000e8000240400000e44075449141681e240000025101a500c060540c00d010701807a40c00c5448200da000c24815070b11075174005501988002c00d542c01d01c0c0d4184281c000c158070145018403440c070000d1000c44c0309001140d8003d60f0211504444102e02042e086d43e40c071208200400805000946109295001904d030b0983d500c5504c000300050402a6100d544040c000d0b581c0022921360000903181d02d0060001c0d55002e030071030080d981c0305502c60b8000303a01000101c40c22296403e8440900000d0140301c08168005002592142e20500f40c00a4000e403a0162001e0080c000b407031281c2551a01d01006006001194090411001d5494104001d01000c00c21103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 175418462 1250 175417212 175417219
    0x801020d020706180510150302090717061c0b090312010801060e130308151f02031b0705010c06050c0904020d020a0305060a12031b051f0b0a0e070302130e07020c 71
    0x10b00801e010010206100740c90341c0100141310146e282a0140003401c0c08840107109804e603440b002001d0781b00c0f01e1025110b080503a58800304c0b014040d03083c85c010080038101d903004291403504000f010034204104101650080c440c440d05a4420405034658803c036601c154803000030303000004200074150414825100000c006580541e5502e00341c03003071400e0704500680003650410201e00794004c1442607001030100130b0074500d840360030204402c405506d10304e03d000041e80000b800740103d034a0260580801ca02d8040600301c1e070303480e000009007002e2075030101a00c4142d640d00461803900d1002c04841c0c42030f0025000303644400c070540e000c0009401003580000030a040a001070301d0b40c605180b200c81a07982110301008008540d80781140c0182d0410f03c50514000b950799480c0206104100904517600c0c05500c65071100d0020740a00103803032003c100140102d50820003442500b2810521030307404016482c0050715011181c01c2c8411511044c3e1107244c514501001340404181d0106890300501c5007036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 175419712 1250 175418462 175418471
    0xc1603020703110105090a0302040b03070b1b0733030603060f0b100908120c030c06040b011a1c0e1618140906010e040f170d0501060f0c080904060801020d020706 71
    0x40740151755500c140c610107607001c0100e490600061600740d0000340e42010140449001076150603484c0340c035034401c40480c9500b04400315015080340041004601400313840d0761103940c072985200f50111081540c01171051100c030546c00c402d0303668400d500080003160045810b0107540c0d0702e038200c82c00400380d191540c0c1c054001081d5800000303003e286200c0c1140d050f140146001d103170030324240310b0940007510a403456010030400b110a8460800815000d0790042120000c503500d040c85c03007454121241008080341c4010f21000044211040c035002c0c814600150116504e2800c20280b820170701d02002e4003420703840c240004102e0300c0a40701c07031240c030f130122500400030001d40d0902c0c14403140c02121507045581c840d10050000440d14460303190410300c5046010304441c01c90b601c42d0b0088400034038141c2c82c0b4070003068514084107030340206401013149051545410000340d00081940103101009030800c0000541c03180207448a0340541c00400030382008544441901c2c0b095030195010060544559050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 175420962 1250 175419712 175419743
    0x1a070306060306082407030207020d140607020a030e010e0607060207060c02010509010b150d020405090f04060c05041d0c22030507050312030403110109021302210112030302030c1603020703 83
    0x160003003d0800ca03440b05024030341206581e045a01740103002004164080c4003010040c1c44a8049036030507403007140000001402c0f08515490408018401d408651090030780c100171070f0300894030000303e15007840c204011841c100e002c10311070f116214009058030303c0000c1603814070149a00105e01c5120b10390003401641c51302d2010b182038a80e1402c106a22129a040c10484070f103456004000c0c1600035a03000d03041507615800201c8004086900081c00120303101000b080014900c10074003a25010704060b07080c18208070425605807804203c0440715450b420206a01840354402d940054003407070364115040d00d1820780e116500c0200c0c801156548a000d0010400b49800b0071f240b9203ea1492403a030341036680d9510101c3d200208030700d512095560794050080580ca42c01090078904000600240c0ea68140741d1f0580805d008140c4400d1144458100510180f07401e0083e07045555094a800b40e160345a100003240c16108003090041d2036040158032004041e00031403c403080304d0145850030780142e803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 175422212 1250 175420962 175420979
    0x23060102010605011412150406030c0f05010314060603090f0f0a0c0803190f0c06020d0218030d02070612020909070207031208010b0318010b10030f0f11030604091a070306060306 78
    0x61750220381c50303c1101840002c01030600300e01c400340e001ca0440318442c0d0400951011034210b86103074009490501d8031050a1099106060f0498002c2000f0303c3c040041c00448511991809005044c207403050200002141c1c07402d8080008070b034410f40d000f0a40316002c541400846d958000200d040b100e07103c80c2d175400a1945400720503152011845114407092800780c45044840d45411340410301403000c0311210002161403880a03107100e00f584080141c1d50210300c82501c0441802e00440c5120354411100c68880e00d0340840c84100302e0b00981403200000c41400d0281b4060b0040e481d0444d00000070008105a07142c3c0024280201c074040d6660900c942c012600c1284c4200c001d015011010348100007090040030750207103949902c1d00c10800000d544e0301140000303070100c0d0a4290301c00001e4984501513982c0c019445101015124800100842d14070301c0c500b50110300005040b203100d01d0380c07040c110040c09468500203000014090f12a81c00c0d20384000b01074000e0447d400340307900092030064082442c10703 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 175423462 1250 175422212 175422227
    0x2130b09010e0303120105010c05030c0607031e0c02070b0315040e07060e120a1205041508010510021506190e04050f0d0c0f1401060f09021207090e0117012306010201060501 76
    0x503601741504082e800d10005480c40340106504803810700c410040940c0c01e42e07085c480d540c000c451654020824080c3e114004402c00440702a20042e03074541401386810030380001d086000c880c00b80300000c0c0c0740d0380c0340b449859103034205004a07508a0300708040142e000030085001e9068a13810340303c034400d07da10310041c0003040c004400c400240b0f41c4081007160100d050b18050440c0000c0174030f400780c60561100c980810b00b1075002d14440100303150b48018091850011100c4844a60702d1000f0000c807518400d000d03e0308c00c0003400c0e440c0070310f540780214002c05007d114030b4400f03015416803844460615181003a6565581c0041e540a03000340c0102c0c004051045003a000f0080e006180003c2e60000d0303850b20407801291041d100e40c290b590744000100441ca90142c5001090341410068948815510a16059100404500400080d20300c2030110400d1103201505585880a07081c412215409481d801400030425500803003c003d2040010b58201c2c0121034422038082c1e009000343c40d80e850040d1800e4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 175424712 1250 175423462 175423477
    0x4031205030412052b0b09070807090e040f050706020607140306010905040b01030f05010f030201020f01050606070f032a02040b0d150b041b0206071704080d090602130b09010e0303 79
    0x30300303500305901d42d40c490006005e04180b03400360010310399940510680405079062003a0080c6803510020300052030080c90056100e009828030503814940180010540040d1703004000b41342c40d0b5540030600340103031342e10401d6200d98898120340b60345032115806951540100e400c01d0009144080110700804035205407030150106845058000b802d010800015100004500d030426903217502d040b1040e415070042500030306199004a490f07a003103000083c14841407002c0310b01c0d00d81c10a0184605a00d4000172110090b802050824880b01e403880c0482d00c1301c16001007031000b40c109051561072207481c0352050344044c0c4211000c100007001081030010700c403c03150000c0c03c41c00da03440307900115041c05d82211024410040002503070003000c00d40000344041c1c1112440060f44500300b00800381e90010800006071281c44030b5141640703003559441d502403152030241d4510b5900c45c0a4503040000079015510a00c20b01d0b0040c0400c2d41e11500645802d4222404983c0081c88007481003030030341000f00464114 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 175425962 1250 175424712 175424723
    0x3021516020d0516020301110c0f0304031121060a06050a0e150103020c0313030f1e052a060309150a0b01050f07050a120302040609170d110709090503040312050304 72
    0x140902e50180e40580051040c0b001e00c50b6800a0003005030707001e214401e02e800048003100d403103401d2540003900e0000718802c6415198010041032010401200c22150005022070b69080d091800442c064145002034030710320480d100d0038080c0284e280080d00134078183c031025514420080d6890301c00040d003030750940d00c81e51490008450000e070365110740c00070202c2e4011981181e242100b0444003100801c40c661098841c5013185c9000d000304240030900e600310104008914583c80344540380d06481c0c1001044800034410383c0e10503510031002050356405146d40060425880e8903203404010785031103a02c0c84040345000d1040000c0c0405000e84190100410182d42d41403d0001d190070503e44ca62011909561510880510b44000b0713603202c0740003200400503900540c0b140d2900c80c0203460186c2ca9040311100d42205a420484d044001641407840b440602e05101200044405070303090945035002140e5481c2400c4411050000000081c0200d91003040c420a0100d90034804031000d000a650080c030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 175427212 1250 175425962 175425973
    0x11406030c03070e03030f040305010b040b0a0f060c02130c051b1207030302090604090606090e01060e0906060306011404080a0b010f06090e070509090112120e01050a0f020703050304030302151602 86
    0xd403440340a04c20400302e4040c003100d240c44002542c0c400150010350040f211070b9154400140242000c0c0078401c003c0c002518118221340c10700d01d000d80490450f00418041041c400c20900035503885031100e02c80305049010412110914000003001c3e51702000201c200380d40307801c00310b4020040c00140320041d4140b5900003070820103141d8044010303600280845510220500002c80ca001e003034070a03a4014005601c1d5581400e24005443c558104160b0012051094080800c40c4980b030b0780d2589988103034100e034403a40c2d1b96907010050390548016806c082c80140045400f04042c0400a18400350b24081c1c00941580d80e030b80c85140c8002002c3d40103280c000740f90382c0002c1022070100e0000c241c04c68200d08050741040e01407004600311001c02d03030150722450409100351061007031a1503000720400140c5003603200101c082c1c2c0068000c0c81007031098010464000da00d4050b42e07109105980c00341d944079060342e54541d81ca00b402580c8119900070040324004050101e440550540556141c01100d41c02030013 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 175428462 1250 175427212 175427221
    0xc15020610081f06080303090303041e1e020d05010603060b0a1e0b03040c150f030506090f18101407030b0d0510020315030d0201140114091303020102120f011406030c03 74
    0x2030f0045100100c2108192540408a41060240b01651080f00340200030b64880c981424010311625030100c0302001001c0b4845420b003c40c002d030122003000c02a41c400c14142c0300391440030039038000b11242d000d4440c0d4030b00760f0080308201003a0428044020122007001007581c841900030320406603c4985545100d41003c100f0040c0701101c00341d60300c00d020f20204409a40e40301c03449110190640c405800003400309100b00f4040340c1502c512908041d041c2c0d1500c0c454501192040c2055001500300d6421400d40c1c54000100c45040050720700ea0720315290203104245128060010043c0305503800800710381004c208454a0a01e84100590f40350068010050301d03c09180a20080d40041e29111002440860052036610108616041a03249a00000c1c4880055041c00511003041e0840c540a03c101c11402e40543d8955031000d4025000159040e05d0380d099103020381c028400c8071941c03424601d0203410001c00c002c200389450304840b80e0901c00f44202100004002170f5100403903101302c104c282400030a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 175429712 1250 175428462 175428493
    0x305030a0e0f040c020601090c05130e011517060d0618060b03011116080a031103090d0909050702030a0809010b0a03050703030f02341a04090e010c0c021003090c1502061008 76
    0x9810008030ae040043ca003642d0300510140114681e040000400c0043d4010040240130072001c40b54a00f00749000c03001c480724541560b000e4040500306a11601240701d4260500c05680d0000545030340e506e000c1d2220341c92603d4503502801d801000548a54600300d9031400c03c405c46400c490300030640102003005220b003656442181e4106d40780c0c5008256031940d01042c80d542c0c0d00002c6001d030521900030040090001002428034400e03030020200c0509000600c5850b0b5000016a0461415403d0812555032280303040341c01014010002c075880407840b640001404004111130041e28001d94626084007038441c01a81d442400151048009a42081c4000030411130001c0c03641c05d4240b43d224180d420768403840051000300000e8042d0160034001340070800030340e1601c203e03089170304804000d000c243c0b09801c010b02120425070380680110f000c0f1021800c4ea074400d9001543c004e40c01900c1c40c00c80380d25003030081480d0b010008060098450303c00491006c14507403c40301c04a4010030000c2c2510710602d40007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 175430962 1250 175429712 175429721
    0x70507060b040203010608180c091603020c03040603140702010204030809100e041b0216030c14061b010212010902070b0612150f0403180605041e0305030a0e0f040c02060109 76
    0x16154195500c04070200c581e6580002c2d4002c14407507a800400e4140319103a055090310310404084294000c2201344800e80703030703c01200d43c05910ba155803998107c0814042c0e0103442419089121070000050100f01c160701644100c058094100310324600d6a10508268203e1181b03010240822100f0300c203030119850302c19074864001d480d6103081005d0400e014046800d0b80c19214009001d48500303500444480c0d4100f10b80c1801242e04a1002083d62864407030010b0307510140940c01042e103041c070030040107071a102c0c00ca801041c0c403020113401c1e140700c400e0454001c1d001803000160341d06400d0300002c1c0c41c44090003500d201540243c41c039803e40e100c1a0401c0031440f4030843c18800d41c05408042c403680005240c0e000d01c51b51200c0c86c956801e150520300240441100981885d107019045400c0c0000390340403064405035520784c0e0030144070205900040480020740e40c4001e110f27101c0041c0344011a94041c0440c0700b2007605454941514a00d0350820090741d006600480041c0e001c4c1c40100500c0465420 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 175432212 1250 175430962 175430977
    0x301061202180613080d05040b07060b030f0d02030a0806010302090f01080702070b0c07080d030212041e240f020c0a08090a0518041a010302010f050a140a20070e0705 73
    0x84007410b0030342c800042229034000f02c0b03c26800c2038074002e003000310740000d11000300182d0841c50110310b8603003030000b1a180790113500c07030140215581c0c0303a1607240c0e40c50402c00703029810700910840e0000a50050029541e9126980c0580040c4a079000705540d54000d009888401c98010b040086043d180001110540c0f4020403080031441440c0380010207621210087c03102c19090300c09881040c3c14030341940d1824805514041c00c1510410548100000728006a50060790180e190907681c9048070310800442e002130000340c00c02c20090440080300d592083d04241d0010000c0d424402c034946040d40c90201d000301400b50b02540c00c24440d05001810460040c0135001004004251443e100c4004c515818003404928a40c1014103083c4014044200d84c0e00d604040240c01910456041d640002e01424841712a902031003004100740f01c0050190385e0300400d80e0848103985856101600c13009003000d440d2080c030308588010000800e044140030803c41c0075a4840700b018200d60700c074001d08588580c005071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 175433462 1250 175432212 175432237
    0x2040e070b0a050403111804080f0d020f03060102010507020601081b03070b0708090a0e04050307021314070306141f18080106030c090b040903020604080c01020c1615050301061202 79
    0xc501188008000010342140d41071542c640e500c1d641907250004407080300030545880341c1c3c00320480260400b030000701c07503038041e034003d518a441d14585101ca2455000c3c010b0081905030001c6004640d8020040207584951400d0b8000d04c190341303954509076100c40087c003034800710b0740200700500b1210a05040c2c105802034081c0c100c0760300541d02c40240500f80c1110b00f0488140d54001200c0c002c501d01180d541014040c40004e01c1410b0406a41e1245e0f0782c861018000d0145020426010410303e15a0008042150102c4207402c2e03031803c0d0400034000c0040d805070540c1810490080485414445440199a401044d180c50302d24070250050710700702c0e80030038031a031001c0a180f40400c80060a002d0308000714400d006980a25041c1000c2c2401c3d25006500300e40964076040913640071a90000e01c09030800c1e00b00b1550765540007804901400780c411200c001405100c0d500030714241e28101121642110503c0c0d24140f06950388000c01c0b2070900c400c0c402e00001030b0505c40070303038180c1c1403030740c0142440318442 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 175434712 1250 175433462 175433473
    0xb0904150203180a0807060510060c021512150102070909030914030321070206071b1b150503090c0f0d03050c0a120203070311010b060703080c07050114100603060f0302040e 76
    0x4650324030b0000c84c02e10440e02d8800c00b01c0d184040080704d00419400c61040703100f400e1040d003080e40040c0600310315103000e031103000c1d01d5420025410089040f910240300ca000907000c9890440400d904e03406042003070500620030309200060399041031180c100000d5256540e00700b142c0c0352261540c10164240c418030b40c54003003085006030490315100090b4a00d000107241d0981450002000380c20410014003031000d0115035211548115030100e0310700300090303100d880400c00202802420b12101d4440d00642200303054143c004200e65000b502540c4a0a01003045030901000700042c040184108580035802044030040f01c80024064005040c904001c0300c1201c040c2c07800c0e902c82e50b6007200840244400361300b00080e008203241c0d0055080c0840d0031020020f11000d030300d42003c80c2103407081801c050104400070011803a0b25100c1da00b240d200580000c024400040410b8001d4001d103c19980b01840e05d51010303000075618041e01846c01201c1c12800c80c0350f596880d43c0c00b400b015180340482d01c902401b51 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 175435962 1250 175434712 175434751
    0x4050609062505060109050f01060c06020c100e0f1b0a0e04030509031b1206010f06110a0203070915080d0801030803040302250f09050c030105060a0516150b0904150203 74
    0x410030b042d260300d405200100490752501501204075400078000c00200100341006002080c3c10213960601264054001a81d406005c040365040000070825946000d083c4184c11780035032030008120740311100352401d071140d0b01c280400903080f0318074000e07009402c90165001000312928024001c1d9005020f4100103240007010f00009041400303c06d603500006d03158003070148a505000d0004120420003c00a0803c1e5060103121080007100e44500e5080129203843d68007154814051403c2c0c1c5c550240071100c400f5182c02403000030b070000e010310b000380400203100010300d864001b070800313940e460be40c0b07030a20300b0b03400c6880340c0c12150300c020429000e40c8521462480464201d43c1d980d184800d200d140c4c00340e864104640300c505103000d0f0303001d0303083e25051200340510105184202c13411a502240e00325541d000034082900d15004244000c11454031710088401800b42d4041d00ca04590074108040101107554020043e9000041d02e002d40b05025090b0704520700140c81e801140c00101c00c0000039008280d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 175437212 1250 175435962 175436017
    0x23060d06090501030b0609070c060c170c040e06010f0f0e0f0306090c040e0a03020c0f0103110406020604020103110304050604170d0207030c1a010b030c0307051303050a020310020405060906 83
    0x3941c4514482591a001003041c095088420307071b00442c0071102d40e01182018a40104034626109002c0c1c86c032940c1c0c0f81c070003010034002e5090f001c003074200249100380751402c0340c1e00900b00d400c91722510b89401c400b000054003540c85401460707406c01c07090b00d13200d5000c1c075514400c031350182da0b03440c80b5500141259902c0a80b0b0b641044194411040700c0010000d160b0918103102c2616101410101940e120fa0003d8001a8001c2001c5c0c0590400b50748a07000108031500490240800c2c001030003036003100146c0481c0e10b95000c1003c5101d14000e8905001d840f24505141761984822240605140c020340041303800201c130303201d110416814610000d410054000000c1080340d01002049000c0703a0801c0801007002142d0040d9a4110a07005418541e503241072590542480001c1c26950250b80000c00100880e009000360742d038008464843d01003154681c0750490f61900c0a00060b44a032041403090f181408440c0201d4042d00c0002d04410308195204061242c1e9400c59071003014010b0040d40040341c080b1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 175438462 1250 175437212 175437221
    0x2030c040f0e150402091e040216051e150a0207020f12031b010212010612060801060b0405092818060f02091201020702010e0105031e0f0901110423060d 67
    0x105145000d01107040091103038065507094407009005a0060222082c940d40b0408241c03064a442030441f00d59081c41000203000b80304007401441d45045404195040c01000142045100c03160050340801b01c441c1c940c0103540c2c01d074403000c135046030000000040411400d9005406190700c0a030100c081404040c0018201211030a1202890f40c404219000280c1140c00400bd039440400000c610340b0860800551000f4014007409080c8011060307031a12030321441e448880100902002004040e480b180194180da0052056600c1030101001140020107140130010620011104107200c0003807680094026003104101c403d03001024605c100085621400f512000f107140710401a55411401c1c1040144241015a0940c0360f2044c0201c0c2e0060360004c0c0c1d0012421400d00709a030310f03591403080c5c9003031204041044006400c400d105210384c10b1483c502c002d0080e01d50100130b000c00e5110000744145401540328200603088128254000c44da00118040402480600401c0c03400c0848002c6c002501c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 175439712 1250 175438462 175438469
    0x1914010507050901091406030c030606040f0806180313060e030a0614100b0a09060818030703030b01030b031209120f0a0c03020906040b090a05060126040c060f02070902030c040f 78
    0x10310010702c01e6240d44c0d000801710080e001e62412a10780b240c054000c00c00c40c0c04001c15000d0000400008224595141415100241317594004200081d48138110309464850079992440050311a4015043d05000441a117910b4100a400314040c146806001c4802d01404013138aa094043e80341c010020400a0007104600701102d2400d041c079017409090340382c0401c00e43c0d00c0203007004810f100c448032035913100d402001210120b20789101d1544501d00320798440301d459441e0b0051840700064450030150036800200d0b40d81001d8800b00039030740c3c090040c1a151640003034030f0b41921f10108500c8000e07143c80c85500c540c214440301195100c4000c85410780c03504401040555841020040070000c514205900e0740c1d1000c0152000d10248151700007007201c1000240c842c030040c9460301c00060031644101e840100c00d40c2a201c0900980c03a010700c05084860080c1d805a404104000011a0150140d01c09020781c080990040201360715040d201d100a402c042c00da61040b5408210020b1076641c03040240c5c001c0d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 175440962 1250 175439712 175439717
    0x906020d3002190c1101090602031b011401140a081f1d010c02071e05091302031f150f05011e140307051803070b040504091707060b01201914010507 65
    0x313075800b5003821003000480003460740c104695950117021036075010040c0e854803540310b06043c4406226402d22405416070103400241d02540394000101c00a60881e100244602661140100c98031a04a10789590040c0b2a617108010800440700b402d80d071b540e020b5030050009403203400c07036014440d0083e4252030400c03c5c103200583c89400240102889408111140b07540180201e03c018980400b142007c03030000c01412601c10035007040d00540d1024021510b000304100c40782c0d4448419100070500902102440d070303056805010012401d80600749600b0103844050f1250381d50040101403452410400011500800c40e0451007560b02d000700d0406140600c5c89600d6154071000c0800603500412907140620b4425844500200040c1c07008001303ea0170768500b41d13400304080d001400d01c0c4410241480e1540403a250004445007070003840c2d07210070f0224809030385855841c800100421400e540900c0e520310260400c825215130300d850300f105845114070070b10350f41184001c8101800d003103e10880d2018013 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 175442212 1250 175440962 175440977
    0x1110050603061e010e0601031b08180109020312030c0d020c030a0e0f010f08070203160507050a1211040f0e0312070201150b0f0306030a120906020d300219 68
    0x81030700c0d091100c1d5a201e11284000b0314118140700c080500c0b0705041c4508010080b020001c03d100d40d10a0300000e10300301000300ca9101e01c2d11410001091400700311a1030001017407420b4440c01c182c2c0c0602507111700c240c0040080100900d0188c241b0301c5c2d42d00241c4003042c134000c10080c2000000e10fa0002d80314610810014641721018440f0180c240c8104030f41c22842420860422411a80c000508010b100054070b01803c0907903840e41d044c0c1c5544101069181203020541f440701c100640000d01c2015103c003620320682d903542d15007500c546440f458100034200c001101e1518818201584a011351800111000c04c0442ca107003407090560f4010340039401544240303001c01c40f4042d024021921168030303104503e01001d207442030552140c06200c2d5580403401d40080810308540d410450f0800060300a01d82044071b414000000e0100041d80c0304240150044001d4006486d00078000c8004050000070004011803424484c0c1c0c1d2401c44144012800c594280592894400340718404810006580c50304038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 175443462 1250 175442212 175442221
    0x1107082b12050a0204120b04050111041208220b03180606010f030e0c1c060b01030c0509010c0201031d010c030e0105060d021203090d080a0305060f0604060f111005 72
    0x4000e0309030581040c142264003650400301076110040e06080000440002800d07120100010f02038400ca071300043d64500416041c2c0705004948803454015407040d0001c0001418240002040c3d000f02e00c10548191401400f5a01003101c0e4002000320342030030540304203240210140848000000d4204003445040032082040700e06c1c0031003041c400b21401070010305035441c10200080281c07820607100c1d000c068851512003d28842081070743d018800c010942d42e0b20b17a00320031000c00d04e02c51403801030340c2c0241011903100141d4081c0c4100300c031417003c503a0744a182c040b49070015200014944000ca04140e5294000c4030201030b041502d2184d00c5408001045680c0111001416035110a084103400e91400050000c04e9070b503400c3d0601400c0d416900c0e06002a0346109041c10760042d4004160011500c1040c0310400c0054402004a0718884d1401c110b9a111101440640300b0313060021034202404001c1400286d0083c40d001640303411130300d45510711640140c2c5041c00c00c00d050721000e0101385c5503011300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 175444712 1250 175443462 175443493
    0x806070918060b0a030209060d09060e21121f0b1b060606070609020d0f080712080702070306150503330c030f0a09051b030609030a090504020901110708 67
    0x60860710300350424008107060104040786841040d0f514018190b0000303115030030b13464400c01e5590b482440001006503042c2030500c9c02c060007229800301c0003402250410a10850768120010503041060501410580302c450b1070300c2d9610b005490010000300103450505100000750303c1002400f07050b0310882e1134151403081c10040500d00900d4000e81c0c0c0000b8100165912000c066589440e004030300401c1c0c0c10802e00129600c0011030402809c948103240f034a5050050340c00c0200880c500c101f055203040c52142d00704840703261051b64500700580040c00d081000c28259005002141d1504400740d41444d91400007a02c3c0034a5008508201d4440d074095071503241c0b07a04585a182c002c407140c20740b0030381f601c0e40b54400d41c4d10000b80103131603102d80c08001c01d03509550303580002d100643c0142102d070382c8840940c40219042d00032161a10138407a100009200401c0841518130840c040e8881031109814030b02000080e4100c94091810044a000910404c25041150074010440c140240c620380050f050700 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 175445962 1250 175444712 175444739
    0x2030a03020a03120e03071b0506041d070f02030a0309060e03070b0a0507080603031b1504060212093906210a09030804110409060e030405040f0c0c03140408060709 72
    0x80c8804da600c0c113034540040500110468100543c01005012208103d425030b40d2004006c1d00540c0d00701c41e01103004226042101d1803128042c28440604040f90b44490080b55840e05085c01c01e00160002d00c10351201b68025041500928810354000c0b03440c50718204d0700c6185130000300003580c10890100605c21009403030701ca400d4110a4a03d80b220785443d00b140403990740d100350540c0d9024010507042051070040c091000c0c10202c2d07001c1ca43c660302c90525080c01d030007940144640c8541b518152000c20001880002e101c01c0750a0040c0003004590801401d810404800c0c4040d41445400115080c0840e43d8000003030100002d8030f4104040d104040c000000e0000c00148445c0084c1d1514140b003010a03008540b850380680d202450000d50140e000103e00908440c50f0001d0000742001190500050080054820754005827010454070458540701025030b01640014400f043c8100f51010200b48100c841c02c0c6200406c0c0421031415640c0c030040752902d0002c595903400506108424090082c40c90704 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 175447212 1250 175445962 175445987
    0xa0b130b0a0e060c1308120702030f07051f0908060903070c0b09011d1c0b07030c090b040302010e010c0b241806040c020709050a050601080c030c03040201030506010c02030a03020a03 80
    0x5081125840210300e45645080c0645090b100368004038243c003442070075081141c05400090107075681f01d106d22185601d2a0840e45049110340200c4000c0400c0c0b100005142c070031100b00a0401040060410318105210100000e0f4000c20440ca500462621010820b840c00742a80c98029590340d401c908249807501038541080301c02100070400e03411b242c0e90020460603605408020609156588000507001c512140040712802c00c2c1503080209010068800910078041c07500d0178441c408070300000b19000b04139070045039009a030500c02400503511510911044004c181404180c090b000d807583c801d142c40454180300000420700f0941c03607900f400d43c1c100d000610255589028040003c921216040000b80359134000c0b6501c80390740c0b408901c2040204c2c010b00306480100501d0a001040e1400781c81701312100c0d8085078903034001c01c5101040c041100e00c84d40180c14054190380304e540c0110040d00c0701130003080c10401843d00300805039909118100c04140329400404d0f80d84202e03c1c02500180e030644 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 175448462 1250 175447212 175447231
    0xa1e06050c07050d0503101706041202030405010909020708040b0408010501030c0504020a0807031509090c0f120b010909060f020f09040b060310030f020409060608061e01050a0303050c0a0b130b 85
    0x41840005140004c00f40140201401d02070344a9403181690485140580e020360240b00c4107000c0c00d441e814004c03034954042c0f030103070502108081480c00c085e607580c4550312540c1e00042d440340d41080142051b0380540402d900c19841c0740d18003542d9414086142d0003503040125965540d000401c00c1064411185e4014407081e00e003075080c402040d4010f04038010041010f001d15440d00c4150204110800618001e00300c070386020043ca0540c0d0074241034180407401290101c05c450040865403a0316100da18070071903400714103e0510381c2000c01c0d4002501c0c0d8084101c1d60b142e19106c0c00d20401d415800a81180019110b00e0b50700e0300343d0301d42000181c50b4986000d500884080003403085940c01301d4020f4050b03e4000051011034070306480880d006018144014100074a014404078074040042500c81c006c0d9490100c0d6040c0301142160300c9027441d03003886625841308610b00c04100007801140607001711400e00d81a152003055640b0b6883c1905000c80b040c0f02841200d004540800099100a46d0491741e5607 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 175449712 1250 175448462 175448467
    0x120207120206030112020103110c0102040504110301080a150908040608070f0c0b0105010509030f01060e04030f1d131d0105060a0803041401051c0e15010e1504020c0a1e06050c 77
    0x780c0102c0e10030300c0180580d80b50030054211000c19a402500014400000b003014142c1e01c4500d1512203000b504180a8644200e0401c543c6507030446900303060768180d5400c0d1000e4140049641e03151504070070f4041c80120210740310055a404504a40d0280005000035100c034801403030611030091503c006451440240000b610744030000c100d1414525064410a08241e681c2c3ca2800000030725100a03d0b00348402e030340c02c0400125002040074074060055109489401c202c18085a040c1ca100c499107120741600d1518507144281d500c1d0446440b030340120310030000074400510070004102c1904a1039001200c1e9112010700600b400c110441600a060b45d83c003079800c0c44d05080b5880c8405140660482c1046070119a00ea1100381c0349011101c032660507a0f00f002500072400010f900e07149a2145000180368800001400c5801900464030604c0f001300c1e20301c4680121030403c802500b045441360f510344280c40036080025503101d40b50382c84028003080c0c81e0f008007441c03030a5001d491000740524013a241c01e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 175450962 1250 175449712 175449749
    0xb07020d0909090c05100210020c0d02150408031501050436090503040b030a02090306090703050c12060609090102040f091b03092303070204050f1503010c050406080a0605030109120207 81
    0x205101e901740c0700c0031900d48540c01c0302e01c801246010108814610020701c0018500380180000030241e20b0042140c090b1004c410184a0075104210202c4001d05901e0003080050030403d21182200300d200014102142000c1d1540c0d1170f000d1842c980542e103000003040100381b985a60301c47e41e5100e001010000140003a04450345d030b04e516800b0f54403650640a801002240c00e008494055443d83c10000d81264050b15040d21420b0361012184802c2d100390058400301c610b20b05080198020034bc4801004100548034407092104505000300940000d541c203010103d030b17000030650240300800b4000f0021860405044091201ca068035001c0014180740298102c00103400307110544010711000c54a1248680b4440e11904511451000a41c003134a0201040038544d809a0700501036001c15542049190404040c5030803610081000004204103020412246115180065000486035000f02e90940e40c0c40c0440e0a54101803000c0724541701400b40202e1156040200c44003c00c2c00501142071200c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 175452212 1250 175450962 175450973
    0x203150906011218050d02072907142503030818070b0f040e01271e1116030503061003050115120212040c0f0501030207051c020a0b07020d090909 64
    0x83c80a0074403098862819558a8940d0078500705201e42080a48080c050071040c000c0d1240d005001b488041c64000400711050050b0b0309501740d865000303003915498080f1b00e441740080c6113403050390002c85100305140381503201d4290459115418800706040c8400f801c516000c0e05a0a000f88541c45c644e12401b4046a06000001c5020403141403140166990f4521145c0401911864124240ca030003020000103818003070340b0888180344892040362142e0341c115214601075402448603030150210710205415118900c2c2e0203403180020b0701407002e181c4840c5031024011079645d01c80540c0401c50200400c025814040d5000b0218070161034100455810107501c4040464030b12024801c100701c0c1558081850060b0341107802c08506040c0e0320aa92031300e40703001c198008070741c050f40c2e4604440e100e0001b002c3d400780c0291075125a20002811504491000801d00340b102424180c045104012442d00482c02901006010300c81c030340e01401000c043e00d54050520f20081c0e0090800b94075126a901c08500d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 175453462 1250 175452212 175452227
    0x2010b09180a2a2102040507050705060901090b0702060f04080f041d0402040c050708031815130b060108091e0309130902030c0a180203130b0703020315090601 70
    0x4800310034205481d48040e40d10340318080000030f001c4200340300381e40100c0f1480e450b00060421260050a4156100c042d084504041c021041143c041c40a02580c0103107020f8016552025540c40d00a0030001181c90700c62a01200762074008280e50741d00c101005001a038074000b503100d40d40d40001c0c000d6040810110f140c0c43c07801040030746005804948540025500002c50300281452125280000306060f100b0304140c2042d5000c9100f14900103031904030300e0149060f81e040b40d07007101400c0c1c03d40d5101c5200080030444004031313003440e00440b010b10b03c1081140740024002c4146200c4081121003916201500d207030040d040358107024041041180301600006d9481d5400c40d013417504d50324018040340c92403840c0210880c1c154440b204282e540103004455009426242c0201c088030445007404042c4811034505000d00d8050b98080c403170b41c414a8030650015a005158940c0e44203400220b901c4880081d0021342d403120009400200b8011400041303503400340303810012103c0610608002c0300280148 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 175454712 1250 175453462 175453471
    0x608060a18080d0209060a0f0801320a03141005010812030a0207060f06140a1d0c16020409081215061605010605060f1c1e0b030307060608060106030c02010b09 70
    0x1402c0094000084105501038900d5410007610550b150011908007900b100341c1c0c000b1480004008170000211200803000d001c00000f001d5680124546a090445109100e240041d0b40c0001700e81b0790000024206001e4244ed28920b41c016049001203e5486000d652040c2e000c84050ba003c613003c83c10800740c0d0000ca0b600200040740040c0d940c1c0742850800e020f040d401c1c0f00007840038900907000a40c8008007907038025940d030031901e2514040e151030308a14903000b07440c541d0b102e000350000003610034160640140352049511054542a6074550b0015042d1110241c045846903400714048000c40c80d0548a15003140c0c0e014002c407080c0c003090b07011820a000e820031546000030003081c0c8409115007984440040c1c04054400369840007410042241ca50004004141c100101c40c070601c40c21503948a0300d040408810740c4032801c2d807900512900a406a8101d103640b60004010480000d400d0f481650001c1c00d5803805007000e5890301c40043c04848200b0047c009590500100000e199100c0420f00c2c0d10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 175455962 1250 175454712 175454723
    0x3090109060509120a06050105011b0c0e0403120606120b01030c0c0b060a0306060902030f090f0c0108040606051c03091a040902030702120703050405031606020a140f100608060a18 79
    0x951500f2030004401002c512a5a0050300628401205001268100358181c94080c0c81b11825603407414804000300440348800750000e81c1c411001d0240c2501103010301d030054000d24200e908542410a0b250450704144d001c4400701c0d14200c4520100c500340c0c010f50034410741c242801c06c007008410b003025000c0120450014200740201c2c0025001d070740d90b5815100695040707007040000d00c1d26030348010001c1d0310655180360101c10800002e10340c00b6000410410809a0001500348021602c0c01596601300c00340003200d000d92140c00200b0320382c0710100340c0343c149214841d0580e400100c1d03042c06006842e1a4105425010b500000007140c1e51280d8120b40450340f40d8000165641d541301e604a040145025400d00a0800040d5a9007403580c01005082900d00403002c1d07824041c10080c0020100420b8400d80d0056001155240040b6545601d44182000280309546030040130030300103030500041c410404c46813a5100800d008105080011940c4020203040811010604041070003488e0038250000b4070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 175457212 1250 175455962 175455967
    0xc0d03020f010e070306321009091b0e0c0405010c0503040506040b0c0d020303071709010e06070f0305060904050a120509060d060314120412051e010c11030901090605 73
    0x2014400c0201a840d800c108000300403510048900c1a22a461440183c03130140c101880c079408800141440b070007044104020100c08084001d101000c4a4000c00d442550f0100800004005510b4000c401c40d02d07100b5070f03840190401c580740d00c240140340384c0c0000110b01d43d06400c100c079020340d0382d08681c00d80e90f003420102c0c03106145141c014503521403038100701d8000c1c00c042400a0901c3d0000301418203c211002a24500b00b00110200ea0b40d0008942e00f800290220241e022000c2c4425141c6412120b80000466a00100e41045180c180103640b48000034000c03800805003590306108864000c00c1c00c80e21092030707007071517103810b030740c540a07000080c005040c030100903588030380150300f02c40c0c0d010350161149403036540d8255000000c3c0214030050741c00d0200c0400d8542480c1d40403910104011400c0d5016007441d05144840d035013641c42c0b04c0110303203c0c03083d01d5284084407203a0b05a1856150100d0000c1002100a80010402080b032075510485a0086c0146004c0340c0c0c0048013071040c0d074400d260094 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 175458462 1250 175457212 175457239
    0x30905010216051509060c15190e03030112060e060c090102010e0a12110f0105010605070b01150c080d09140c010908030a05370e04051b03062701120b0601030207050c 73
    0x70f2013482100047c0d107291045035002c04005002d10515440381d43d0101031a52035100c01d0740060156500300001e12400c1e0020070040c01151800c024080c0c409001b0240001c0340c00c20b02181c1458228183e40046102c000450303c2d542e603603424010075400280250190642900310390714221482d075100d00c4101401001d210552190604200311208070154000034080395035615009012584030401c01d85005412130004507038149810000800b8508a0381d80d0527011585450782001600f10b10201d403802d90b02c442c20000410380f5441840c2403003000c0c034003400070004e40a00152520000d44d010308015041032080e5000103402c5415102c504081c2c002c04140880e00c40a5a040c0d03a10801d2f6035082c80c15251245022942d003ca000124404255804c00ca1503c40751000c1c00007914040340c040d0100d82c00c00000d101c1e820400d850764041c1c0403403210550300044010190002c4030b826040a02126607a120601c18005203a03c1560070200a0a0441c509240c580b110ba49951290042034081c114080007071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 175459712 1250 175458462 175458469
    0x4110a18020309280303053313140a23040303090512040315060506030112060209060706090503030a0f090807020d0203070504050c0909060402091f0c080403030905010216051509 78
    0x1413185108803400355400e208405803001e500c1c41d010806400182c94003001410210344c0c940c840c240c0c0344010002c40b40148003d910050b00f00146611103800c20420102c04130640c440e40a20b4481110101500c141842e0442c5240b003103a150f2941004002c0d0000912515801142c0b903641c0c01580519010075580c840341001c03454218030710f0031040083c9001038008240103a0510f84240c1d80a4208140640f41c0e0720f00c20420540000e00481408140881c07006000640701d07401409018405085541010165102e1500f00c45000740143c0d2030340c00000801c1460030007403042522440c055401040000c00584420a0314015800028010085c019000081d5941008250010b00000703000740801d2401d0380c40e0301856041929458044c06d00c41c004200340f40f920340243c448501c0e0141000740940030010840280000c02800b08092201c00d086c2d900105040d4801040a1806500d40007206450440028503041d01c0101400e1020036050702400165502e040054003000c000248644500c00d02002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 175460962 1250 175459712 175459723
    0x30d08180c0612040b0609040506070f14030a0204150f05090f0d0b090c03120412060203130602070305070308010519030605060312031f0806070207090903090b030f04110a18020309 79
    0x1580e110310085654101019030f1110507209521511651541c0e403500307020301030605420f480080c0950450320003d03103658407520400130303030340400d00e042d01944a0780e8806003090740c400d0750f60355811170b000074080c010f540540b602c1800b141c4442c902490403013201c54005040d40503288407284a07111621201102d0394403081f0200d1180d4000f6066001800c2c80110740d652618440b01881c06801204c42901c8041202411755040343c441c007000100203140f80d5190402580024120401c51150145840c080790203407000e0440c1c070b8880c0c0ca8155580203142000f0b4074903031050b8441881010b0960f08bc251070b4480d00c600b84101c0364040030205054071703280006030a0443c40103c9504103240030017044501001c110042c2042e41d81c01510442068480c0010b9440e203401300d036200c025030300c1700c1d1040106900c2940318030f0180703019140034074000b42c440208000301da02c207070350040c40c0e107910341d06000500088820300d42540382c045030613040c000e10700b40c0b0012064410300000c0040a40c0807002400c4110705015 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 175462212 1250 175460962 175460983
    0x91507060f09020f01030c0e0409030201090b042402030105030a1709220f1107030c02030a020a06020d0e010207081f0902060a0203030702010c0e18040606090204060914030d0818 78
    0x703114400c0c4070a0090000c000806042e845440b020030815141e5000c0d100307455100089a076440309041500c0c1c01e11000c1c1c1715850040702190f5031403900b80301241c9640c104038000c1c5d2007040205143c460060042d10b400c0042c001d00405244100010081d41e030f17000641401c1c0641c000c680001030100079410641038003c1703100030751b000311503400a445400250749405488030f44100080081801c584c2108040b00d00b81d8503603600081c400c01027140401e01607002900d4840c402001c0300c0c5282203607030104070351403025800440547e10029040680035041160700f0f2030750038284011721a5501e450240e542c2c0d014250407801c5880b45204a80c83d40704440e411100c641600070300f02d156101c184000003036407a44203c40b804019440c1c0100c03252801c0c131a100c0e800100c0c1000b826101c0580007404c2840001401510440300d056440000003800c5641d070000d072000b05025250a101c4502e0405c1da94101025808440e00c2074000255a488050300144820740200030b00c80003010900d040d400b00c0745000100d40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 175463462 1250 175462212 175462223
    0x15050307060f021002031003021210020703080601080610090b160c0e0405060a050103080306010e0f0d0606081005040803010b031003061401061103030f0c03060406050a0807030309060f05091507 85
    0x40828502c2d08926105240c100c02e0382210940e01d41110740b40f04a010940302481044000700b010409031a0841c0c18800030140b041c1941d5105070305901e20b40403684000000c40c042805e2200f040f0079076030030a1110364041c00603108500203410b07840e0020020101800b40c4075502001140e2005403900198141c200b140d0300240905809031651510b4900c2d0004640c00c9541d0700c25903001800c40d00c0c60b40141030489902010132415500c03110015292103594a1981d90820015880c400455888040c074580380341c021040012218104440315090100d5120180c80160400007070000013080c040448c2c0c1100c454000154581d2a00000550040d6013907002500032420a03540b107100942408810f4100c4100e92910905044888615512800220b55005402c00080300240070075072408021b55008034000e200080490f21203000450102807a08010141e078800402441016002a20310000d4106820009090007100c1e01c020034034802e5000c494080c4a10a050700341c24800107080c0d5075403943c0305 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 175464712 1250 175463462 175463473
    0x63c0a020c06031e010b0304060506010507030c06020f071e2307031b0512010204140f0102100b040605060c072c220b0a020910050a0f2a14071d0a150503 67
    0x3150b000c1c071b6503042a101540d0301481c01c0040794943d0300070f03000c46107004d505840304811020307a41c82c2c0b00001c0d0404a0051200d210030442c1c4000a4000010b000c07401841c05c40d008190078003810146801d100c0c0c6910444200400081308660034400608401266405610000b00c10300d082d200014449080e440140c04c210410079076900b51106402810548100090944554202d94100500d42280c480700706d007d604040c0060314074031501e4111289070172020b040400c1c0c2d540c0d01c00c0030071403640c0034005c80c0031250081c03e020f002d800562201d0142a0504004043c0b441000607415068000b000d4059002640f0848111280c10710480402c070029401c00e580c010f083c41c0846a20020f54007600c00700b80309105010307e80c081d01d0b0041d0141c1c2d07400f03200c6541b0070721960040c010949426644401d41c0c445010703403e044822000480400b0442c0314030901203900120007a600d540e03e06075158010002038250915421440070409103407a5100c00c0078031002c01c808250010348120740c4200d030410358150054 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 175465962 1250 175464712 175464719
    0x203041a07020304080c010c0f031101111306090509010b030f090c0d11180f07030e070f0305070501080108010504050a030f17182a040b063c0a020c06031e01 69
    0x203c0a40100c401c1d4200352410050081c0045035010b0700f001000700101300951aa0010038401c40044051031142030000940819504441032070f50010400c9161000c03502e201401015403020002000b0041662451700c0d55041007200009404000d1880310a0224400020403041c4200f212a101c0c1c3c1c00500b5801039580e990409140a07496140c107207004606068482880100d404103040c4a964510b11500c83c1e525075042c1200505000c400c09000781c07040240200d402c0c01d810351414011845900204404d81c54000017614a80741641701c80d483d640f6140410001c40e00104081c040d503541403400315030441c0311013015601c6079014a102100b24000c202000708031440c0d242e014823010306c001c00301c81c0c03402c414088400003091029a0350f841c1c0d070041c1c0c0b0300c03018500b410307080810f1500d001480142000c90865640c000c02a5000c03d80c0e040d4100d5006100100481e41070040d103080100300b0503407500c1160807000e5a525020040c5900a0800100203008801588420311550b050000c045555594 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 175467212 1250 175465962 175465967
    0x1f090b030a051506031314070e190e0708120715020c150603190803130b070305040201090b0406082a07050a0c05030703031403040305040504050a020d050601031e0203041a07 76
    0x101200e10a100100412003d5060b00d811001d891040c404210aa40b096029a4440d03018916032206058a8410540d01146165025180605c9034002c03003544000b03c2804081c0c28260f940c0da250300400d80c0c01030315040c40002c10200d03a00d010420005126580c0b2056803422460200321404074082c418400304207807411702c00c040351141e0319100710589001e03241c842d20101a21080794200844031401d80054545c00502c0003006540d0220050300800d200000b00e8407038281e20030048035850006540c5d00c0c02c00045617004983c001c0a80604001c0e1410182041000792400001410307084206110860142201c0003a81740c10705c64a40c25400c540e0dd6102c141b0b0810395451288204454890200501103414100040e14100300d0760176565581151485c4c440c45801940042e10075800c0040801c0301044648940c00b415014031460000107940349022400360040303460142400d4100f505281d640c0c410044c050010070b102c0c55060304e0040e600d0710344e0314040000810390010070764140e034a14200a40d294 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 175468462 1250 175467212 175467221
    0x15030206042301210f1103130b011a120a0b12030a1e14070312050c07030f140a030b12011103010503060901050105030312040501090203070807150503061f090b030a 72
    0x115848901464040e50030041da24210600859808550003400a51306000305070400c0481c004a9540050b415481800040c926842295a15180c1000e89000400c00010052003030042140740218902e111815218014500c00c41401d81803240250010a0a546445c1d0059409042c010724000c2407082400009441e80c10110340d4002040c00c07a281d40400200c885510b010484072940d0340c02143c00ca205062a01e82c00c00d0206030200441e045a00c01c44035480c1c40760300e01401c400c3c00c03a02d0b154441854024402d9050740003138800c106241c002c0d2414600320300207031002460340f4103001ca502e40112010a0120403103008600c92036007007420b030386101109600218181c6006400351440b59441170922400e0390310a210702da4050f8410407005000510310100240c00c2403161001140d5000950002403500d140341e001204035410401c001c100034043e014903400340c140941441030039881d0000025450000124501181038a030140701001e0038807990054018000242c42c441d100d0908610440081 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 175469712 1250 175468462 175468499
    0x2010f0b03070f12150501060503040b060105070b0624030c0301031b080a20060a021c0306120602030a060e0a0e060a050f041103100f0207020328061503020604 70
    0x21890038000c04210700700441c070300042d2580c10000d80c404030314107100f24200402102c415036890141c06414076181e580c44c003c4500800417075594a8582c00d180c1030019003024040c0ca420b050100030003008000503000d02600c2c3c0c1c03010040f07880c0b0454207150710910039190b56403500d96115190010400407515140300203107041e24000c90380b016803215015624401c409990141e40391641c07009a078070001408290b40340c1a0303c0250401212014128004a1402c3d00100b00b98409a0065641511620291204c002c1c2011441c50140815880d00d00000b120207410f0318045d001a800000007503900213141c01030802000341c00c4010a051a007070302c20000500d851121801103008240c0840d41440f410b010344d9001c0c03800c0003040d06241d1210750340d02d044000b400030402c3d0517008e00c50ba4402007440e0b5115009407981c01e0240541c2d80e11292040500304251401d9085040003141c80701c0a90184150002901540c0240d0000343c0c04c131010b01c030040d07000c16a8030083d40301000090106502c000c4404c15450b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 175470962 1250 175469712 175469741
    0x1b07140c09100b090f06030103120e0316050d0c030b0414010e03090f060a0e060d0f05090d0f0c14120d0b040603120c08160c0315021602040b060d0501060201 69
    0x46004404200540380e007a515546030aa0b40c240511409500707000601d0100c000620b4812a24013036408a2920740003603000380c80b0401005000c400300c940110b12145104c400320090700702c1840b401c1000f08081064007034036000b94094042041041402513417000590f0708016401480d14017890110301b03003d20300301b2025980d400c0000607164100f00005888600800519500e82418600e0a1020307980007200f80074204200361802c541ca0b502ca40004001d140303558540403c070515520b04420650b0806406180190f001103080d44515074008518000340801303141400c040789580c14040300040030850070103898001c440401000c010304100030440715942c2d141c140a002e403000c01b000b00721209440b01a10f00c4800e0211341501501c244e01ca002881c2c81642e000e414080c1c504103101c0c80302c811040845011850b103506206000e401c841100240c01405015440c0058003454105002c0340b03208000c0c01780d6240c0b42c1981103541d0f5002910740d2204540e00800296075280402806040c3c110b40400c83d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 175472212 1250 175470962 175470973
    0x6030a022106010903151b09080c0604050609040203040507031208060f100804021002070b0f070c0803041208070602040305010e06220b1602190f0507050402040e0f1b0714 75
    0x902490007034a24410301c0140c4420443c240b864482c07081c20f0008801040b0515a50759528002c40b840d046043c260585d10368561082c1414164024502000141c81601c18142444100400d980720003c40342404016140542ca03501c0b54903010f441d00c0000d40000b03000700b205004107419540d0041c502441035800321a110300e140a01402d2203944556144904001101c040000700503040c5190b100460914520454408540c0c580302000c2c00d41120144540219000071a00280045135640d4000307014100007540c5801c2c9840303c4c8138034402080a00809812000c1409414450180c4c16079000f10b030402e0091245250301040036803034803000c803026112340852281850001458200c20400140d01c02c54042868541d03845100b009820b08000b14218410508581040701000c8080c01c0c09501c00c8051007000f028038600300d800c00da490780003103019910501007004680d00ca4610103030072524040445031941c440042c80324109241c88051032101c00000344c030908006203010b0440754901804d05407203 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 175473462 1250 175472212 175472257
    0x510060e010303020309090405071a0903010f020f0a0c1704090e06100602030703050306150c0f0705010c0309050607020109090e0c0906040905031e040306050f0117120a0f09030206030a02 82
    0x1180100c0038040500164004d10070a80c00d03060800c99036802078011021030700b480340e40d98000128040700b28150502c2c1400800e003014a42400d000b1080942c040c09001c0d800d000c42c1012240031401540f2100c010440075034a00700601007501030b550503551545206541c0c450712107823210098240c2001854030f070301c6104009084141c0c0c008600003981c000d40c4c080d6207405a15101100c40e60405044158040880040105408012401046003a0841c0c0140010060b080f0340c29040002c00c6d403046041c00100386020307000960000c1d08006541c01258403546075001c2c2e000494002903d078100c160b465203001303049800482c00140d0711691070000c9812500075a1090280020784030344500040c03d55005100500c4a00d4a0352585c0c1000d2442c098200e040c41c0e60b0f80c541c081078a0040d10078880c032440c820b00500c000c2c1e001c0014500c86401c442c0003411115030342c00342c2c0b501078030920903541c0030420341c0c1c030784903840d24403407812400210340061129031281480d203c110f0084d40305580081140c0708204446 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 175474712 1250 175473462 175473479
    0xa151113031101020a08030705090a0e07170907060f0f0302370203090a090c020a0f0f020a081609020d0204050d211107090902120102210c040e270703051006 69
    0x645d5940d80b0107005800e40d12a01402d90b400c2d04510003003548607a41a4010400ba80b0445040744201c64582d41e0214100d06000390115154000d4410390080e00039070f034240440d540041504000030300c83c2c0380080010603610401c41c024002d1000c025150701642040c2044800c04004524502c0c01d517001c1041041013040c41aa41e81c8501010280c00c285203600c01c1041d1400ca6000040f008032500550300c2c0c2c85032580e5080080014405c0c1140e5414120700c01d4010350070000340803400b45c0501002440022021418900e03c07c01034810342ca40c1075000101c860805c40c054068600810f8058070300c14009045103000b801003c814404000c4040d20450740070000c512803d0340c00c0000300000c011b00441420030b0900d2016114808050ba00592405807038040b5110902c003d216244400c10000c0d064440c2d845c9000785c6072400342c80d0703008004003440280314511850400e81d4001e403030b4000150207140d00f20071465050303025240030401d9002e1688000240000803803005446006100c00300006921004c16 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 175475962 1250 175474712 175474723
    0x4020423010609350106030209040303051906030206030f0601030e0706021c0c031b0c03140f0c1210090c33030903050a030c230a03050903030403020a15111303110102 73
    0x14803c66410040c84d10318101c0c15a1281c20070040d4403000451403640300d80203e1901101903808500182e45d840400842e114800181c0d803403a8102c260601401740b4540000383d40340005040041c00c4080703400840d040383c0c0280e0000c46400144826220385c1c43d6519006500d61400c5c0c4c0249104114504940b045e40340308411801005078151524485101c0f1442030203460720111504031240f420440e0040013080400340404600307250b10004004d4507408500d02c5040a42450b01c0501402c100d1340a0204983c0205511407912124900000c60958904001d10b850b030096001c1c0b4404094a511001030300074941600718800d107449201c4080d40280702c0110300b01d640c6d401014001039000e03c800d00c0740c2403180e0000c24100c0300b40e1500c80c121503211818004006546800d44003e40d10000704c0400b20360f0140070701c0e07600000da10061821450030b900c01a44440c12010020000101f018840c2145982036211084004447d408a600c0d1707001d420003085a05481c0c08283c175250002c07090100c0300c0d880001c1c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 175477212 1250 175475962 175475999
    0x10801080705061603020f160501021515060a0c02090403091511030f03190c090503160f0311010c0c03030e1807020c01030b01050f0304050a0b24010804020423010609 73
    0x2040f4a0f01040355813a078044441800114114090000e03206200e079010401450340030169154140c2c1c01d0b141800180c03504440d14007410b40c1c44a05010054841c118a0901100c014190785c1155251480c00e000c48080070038130b0f0000d41c400f02d120184024035900030100c105543c100c0c000302510a40a08003520840d42c2440d52a40b941d0080120008d8040050003940e00328103118005001c020212082a007550130044032080010348a00081015140400c4204031031b113541450190714071300f4041c54088241a9000c0904421350018035409240d100e11044181650048140c01c1401c0c3c83c0c0c900140441b03d00240f0782c0c41038050700c1e175482c045941003000c64050000c0d900240074911101e80154090040b01d5001c0381841400c0c003804104e41e044030b004520580c4140050101c2c41c400b4941102c03008401740103400c6243c08001c0c0d51001c402c103001264003044003400c180180359502d100003406000c4915007011080112011030001010448449059881d10340b14036102c0ca0f200d00404c1d0400c00340c02ea = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 175478462 1250 175477212 175477219
    0x60c120c0c030a0e0d2112020c031213140d090911030403031104080a0302060108071502060c07020402090d0303140601050c0a0201140c030f070c060503010608040308130b07020a02010801080705 85
    0x40c07120064081c07544c101110030080d00000c40c030003050701d92100a00880c0c611005400c0c00e0030500c0300e8141d1125945480c50440c5000b1814007401c50540c503940c0c0101c070905a100d9025401090010035103100d94054150310400c01c803212960100402d49031003803c0f02400c0401d000400c0030445044030302660358202c148100b5207086903a1030302c0403030103041050b00724440c284d010000814009814428044400d001c4d400a08255141140d40c41c50540b00780e103c4030442c3c80d41104d018a20354003044958221402800c110303160840341c0006402442121095944050b11351209030406415401107814005201030601d1150388810041d01c40d8840c0720181c3c800380e00218902001503002c3c0340045000721102e12a1410001e07800d144500d540e009040d92480c0d1000811303410104a1400860005400e0516100d0309651506001030705929018200078140705801d40011031450203e403100e40103d401c10140c2c00c0324240030700040e494400004040e0b000071140000407a00c01c4001072650221907014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 175479712 1250 175478462 175478467
    0xc0b040b030a020a090b0c0c0a0b0403170c0c03100509060f0411040c0c020918190302100c020a0507031118010302060a030e100615031a010c02150c060c120c0c03 71
    0x442d085000b0f61001188806121022038046802d0741030380701501450300f500c0010280d007034002c410040015a44d40c000300491004001c14400950741c1511849400f80b840c0c40c041e11000c440200b6814040507a000f950548103140c8203e141100541050f07001d40f032081c2c280d03242611090400010326034101c802500001c01c0c862240844c1c103181d4086a001150351410340240c4100d90700044050501760752443c40c1040600c60140a44400e0081c1084031480e24000d0b2410303c01c5aa02a440707503000741003050316542e00c614010000c0d00070300c05400303021f600800352126542c89242c94010400865800e07400790511050b422052034040c01c1050503030740c0040c6940c1c10010000230031009000301d9002d0003198001c04070800d011000900440703028103800030304052480301500740107045a03080000c002c1c110308041042d8440da6000170380210f11640503501012244081c0741107244500c1043d40a0300313188070b440b04110040c01400054280c0e09624a030800c0152603100381c900c45c0703000d00410544581c004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 175480962 1250 175479712 175479721
    0xc0e090411090a14090c0f030a0b060108100302030a0605010f05010302040315110702030d02070311041406191a0409061a0f1c0f0b1002061003020613170a0c0b040b03 73
    0x50302e81d040c0d001c90103000210305401161540e20038200281c1c0c401c941039020780b0b90414140f81030b814040780280c0c00d80082c214600e464585001c2d000707025200c0750501c5003079004541c074555082e294101844d0090101d501c1290320b454440000d04003481883e20139002280b022032258860300031a01201d8116016516022101b16800300404044a006000c1f1004111540058606101c49041010150082e0090505d1810b1072030388d2201200c03125100340e00e480c88207500360030f40746040350f00722800340c982c156804242440d05001d0407250f000758003107800120a21b00c852116400405c03d07595403400910495958006010381e01c011a014002c00c3e0000344071510141013250094924101940401c0c10840d1000b600041100d0f00103d400682035150048001c26091807007101c00121030520003070150b0f180202000019014030b0100030302c1400c00113000b42d110100380200c0e401a00c10000303c502ca07503120a0040f0385d2541a1b01003100d00c82403c080c005082d41007a0141c0341240c00c2c0140e0646555038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 175482212 1250 175480962 175480969
    0x1091403030c07060216060309021008090a02060d0902030f03030103170d02090a030c031103150a1a091e010b030910020708070b0103140709230612060a0c0e090411 72
    0x4180250340610040c0008004000104281401060300d6006010203c0a101c54040c64950b41d40208090501307040c0c0c440b00588a072070310800000c195241880c125219280070a0600e00100b00c081e40c012004a070641e05001258800c0c00400e1085044940c0c4000d0745e192103899000034400070341462030a611030700100000f00300408000400500040c40c0002410018a410005805c00e441211030501c0600c204500f0700e05000000c0c00440040c026403034003281c40100b070361000b840f141c0a00c1d115080c1440000385500400150400104000507910f4109a00a000511040e220003150b103018000220b1080160480340692404d07400703080301ca000303411640003a60103490102c40c1c0420400c5010041130540140501a51107103421045084815082c01e207841c01c40e40024080c00d1401e540510084617014a0704091b101506074a00c590350751400003184501503000022040c000c130000c0040c1220103501072609141962070781002d4508000500c40c81d10003c0b00c0040003c1c07070b141c200d07a28515 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 175483462 1250 175482212 175482239
    0x21501090c09090f0f0c0e030c040c0c050303010902300103120c1e11060c070302190e040302060601020706030e19110a030507091802011e020102040e040f12020c0109 73
    0x10340500b00500c031240e6810350042169200268002c000755a01c1c036000264150f402455051102464510314500400300005c6d1202071848030907104e544d40c0c6003083c500b540550010885150030000356a1a5039481410360080d500c0761809c0801c104410000c101805210014500710162448000f461a820340c0e4950012455a1100505015000084400244400050200e10548004503443d0110607141c240385030b50104010310f1181a06024618100c1000600c00044a230101c4084046080b4443d40b451110b03015040b80d807009050a04020500d81c0001d036490003031000b070342140d60700c039981c620480440c2c48072000c0d25001d804c500c00d00d1814034000204c40100a0090b02c102c000d0a12150001d2800c03555540100d9a80c0c106442c2040850040e200711a031110300f414031504104500d42c0005c2c80b440d648001101c0e026100a810700449100354140e40150006082242d590f0426050403010908050703012200d1134403d01c952400148081181008000c1c11b03110115401c2c01c1c0740c008070090 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 175484712 1250 175483462 175483481
    0x1120b0411040c020f07151409130c02300d05060a170a0302160b1b0f070603050402030d0f1b02040b0607060e07060e030705040f090605090304051002150109 69
    0x852a04908181d0302c80c41440000c80d2550001c03c0c0c0b103e00d40781c0450034920a5030202a80ca16000246101207400035504030101541c00d900b140e6034100e900010340da00d0300c180300d406189813418518101c150b40010b00215001700148584110039103194000b41c04507001c40320100c6242c002d118020200f01550809a0070150003061824400d407034101c0f264500c107030140003d8056002c480c00c0828160103100720181c0040d011030001d6054140b0b000c1c00d40a220381a07510f50341c40801503608028520a010103000c0004c2030003650b818a40e100001400707803105035000ea11034061055018006c50040b4100c1d004038069440e5003100350581032034601000f00020703050340c225440c0d01e00101960745080091062601c151400940c10001c074400d5485c110707141d04408244084e41c22100c105d81d40000340001101c0b02100d01254410f1102c41c3d0f0406040c5450000b4a014206000e1200088d408030161066039004c0d1040c2a04618026040f07984100c00915041e03611440d81c014040e50402341c00c040a02c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 175485962 1250 175484712 175484723
    0x20d080a0c140106051c110607050a060f062c01050108060409050f06100512120304060615030b010201050a02040e010e040203120d060302041407080a0b031c0e0f0901120b04 76
    0x181c2005894000c89001481403010b650f0355202010300070303460112401200000d04002ca1080a229592825400e0221506a9200c0c803808199881000345c1004040907980d4004410300001c10780040c500040c2c1410301800710b0322000503000b0003800c90916100f000c4001c010500b00c4003a441d0500644509101074102130300705407695015004039000f04100d000d1389284030014042d07031411500103a00564250001d602c00e00c5001d81c68207400c08002241e801202c040900396640b600c4900d041002014030354070480d400c2c5103006000a58940540c80780c000c050003a002403107580d403411a007404900c2070303014a140d608030f03500045c405065185e0905600a00c080e048618103418625100c00729007000112a0741c55460302410f00440c01c01c0c1c00b515041002c1d0061184c05404c0600c409010b03000c0092455113038994511141425950411104038002850140c030841c0724035074500100340d0800c1d0030b8114020810f02c450f0781d00d5070400380d141e40e040702c1407001c511400300e025540340c1120103c0a0004d842 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 175487212 1250 175485962 175485977
    0x8150604120803010e01080111041505160f061d1f020409020f1908070c0210090e07020120030105181b0301091b0309030207121505090303090f030403020d080a 70
    0x15881034007030010881500a400305500c0c0e6240c01c1107a000e880c4160072140d480e034109641c9580c1a9000c07410f803015035510000c1e5160b480c02c00801180c560140400c40260340d191480200c080c00311114110b01001c0c00ba40043c841900504025020854800c030100b00590280e00c003100300c9082e50b5a0842d04502417800945003076641d101c20001da80000140401d01e4000040d800f64031300000c0000c480c00da58608284259150a840c0a040f883c40c0c0500a40115400307101c1c484114445c00e0b0000c003174a85240340c0050b030304004070000c3c024410b1044640700c0d0480c0c4400001d4413051201600d048a00051103040721011150340c400c003072000600141d402c6105030040c810465000f2018501804803124002211a031403111a2541c07a10036003002d0506251410f0380001c00c1d0b0200704402a03800c0d40c1210880007040d4176009094010101f03114203414a05418025100d078003100441c000c210803402c0703c6002e8400448644c5034450f500c0000c0d070060400074084000303030981010740000d180c90304048070b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 175488462 1250 175487212 175487219
    0xc05130e060106081f0f05120f0f010203220c09021b070810060510140307141204020907051201152703020301050c071115090607030f02060601050a08150604 69
    0x285021000e802c1480407980b490100701c1417801c8401030910b12500c500308169003d01e07104161569401d10b01401d0301584507514a5406900c0401ca0500f1702c1107d4030443c1c0c5040000c5030118002e400c2900d010040c00401c90300010603140e000342040da1980c200441c1c1e41d11a280040f02d1000390701c4011090741408421504901450003401214001d20208002d0490100313591880c0040f200c46800252040c0c030040d107060b603101d5001c0e6207645e1064850b0171542c1d0720f403618501034071000c1d102d1102d003e1010001600000700d01c010300c501c41c0602e100303079078010240e100d1190589280c041c0450100e04594040010090000080c5179400c00000310b0910000c018545003031130b032000348091500042040b16000801c2103050034840e05510a6040d84e4250409196035100f43c0d03900441003055103d445002d0484040e98641000c6a0090000800803a501c0320649406869400180c42040c050301829000410650080701140d11441c0f040d510054a90764150b1801062000303a004036820407401d00000c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 175489712 1250 175488462 175488491
    0x904051501060504050301051b1e0c011a09010b121f030b010b0a02060903090609010c2a170114040b09070e0108030d110c1c05090307030b0f0604090c0513 68
    0x41c00b81001e9911195611700f008103050a562001d85030a0441110085154040581800341c80c21410080a04100b08802c0f8040c80150300400503400c50b41d500c1c05045000e00210003003040030b607000c00d454400e030980c0d95400c0544180261041801400e020400148802405c209280d000904030210103544035200e440f903000505098200b800000750015408898680410800b40d0062424004501d40481500860001c0c007850541c28144040f4040c050100114540130740c1c40020460071400310912100c881401c4250329200d044c29110840380c0c407040808040c055400381081814544100782c1312a503030b41e00300d104020031100642c0502a03010a101c000002800d00900d1040c00031506c1d550130350008021a81d1a10020080c80c1007041071207041040811444184c0f0740c0258242c0d4840030018064139544281d8440350740c10b004203c80403040007100d506242c0103c04003000c643e2a41e8844041c0803c4410514024202803482503080155180ca01410f110131a82c000010603101141c0860 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 175490962 1250 175489712 175489753
    0x5030325150504020906040c02070911040b0310030c0806040c0b0d020c060405010b030d0903021e0102190c0f1706190e190506090604030e0d020609090702010b0109050307050609090405 81
    0x215407294580c420300041d403402c2411250070440450b0104080600c0d544040d5072040fa601c2200b5205440f003044c41204c400100507030740103029200c0e18a030b0324070703101c943c04102c0043c0b400212030002e0b40800114205c080090100c1c070a0340d0180000e5041814500015015044291440346882e000c100e288602c3c2c505010307140c0514480c1002240d0a40301904043c14071003081c801004104080001704050381e204420f004e01800c2080325100d03205000c0d00100d00708140c108603100408288a2545c0170450f1601011007141c0c3d11542d01c4000c6500c5024529103886103001c4c010007a40f0110101d99100c01c54440700400011403400042c0c55859840c8090401103030702c543e2071000c54001203407800c2c04004d0000d42d52140071f0001409841c6803d6030003810410341c030807004c1c2c0155800d81e010021511114101c403074110004214102c241b80650b002400782488043c45800076580c1500004d03107081c0082d800c1d00f030b154000c1580d42000d09038410320448160003001034a01d44205440c40c400e40401d41d56 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 175492212 1250 175490962 175490993
    0xa1a0303070b0108191a070c0203030f03040302010f0605010c020f0f040905030706050c0a09060c02060d02030405030c010b031906020d1104060519050a1d03100510090e030405030325 80
    0x28100100c3d850121001d08000304d81404504040e1200032820000e541c840c0081c01031100c401c07a102490306c615108460002ea0351100940500c0b0000d030328150714024501451140741710f580248100700201c89400142e4900e4803403030740070400700110300b001894a801151140d040240030409245070000000b02601e043e080140c40c5a00b0004270300051102d17134014107610001081e402ca1506a071070000400c1d91f51135220300410806014000011540c03041c0440b2442c90105800f5526404c06003440c5889502080241003d50700e44041401e95007804035074480422441c0f5088901d40c100d58550401a42c44003801c03141550703640003082c01c00e018503006403015080b5035845945400241c044006521031208106042c00010301000c101c0980c07040c0314540d00310701c0c0d550062025a144011030710f04194200416030b003900305020001c1611140004204842c10620140700450031410b019440340704900569405420030041c03c0310441c210315000200726080c802040d16020151500c0b0b82d0383d101c03084c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 175493462 1250 175492212 175492223
    0x3050a062301150314161803020612040f21030b0307150f0507150506091005090a0b01020a02040501150e090103082203050d0801031406060d170403020306010f03050d050a080a1a030307 81
    0x1500c1b0550306c0d807000800101855108001c02158203580001e01c1a0042c0c001e842600f041c000e00290410900300c07040e50485038050800510b02e42d9030541c1d0001600c50313036070790300029141c103c444d40c0034a000207000003100d1021840d5650b07005280021200c4400004540b004e100b000c0004000249a80d2001e10004940407000240c0741407960030040c4210000c1c0500c02c030301c0c104500c148111faa40322a019001100d0100004012070f59074010707410207040480195010b45008000105001c4000400380020760030740d150303a10380c407030102009003080082c000a4403003501405100c2c40a010507200c810220140705101300166a80d966070b5250a03d040314810005000c81c00410070000d220118a0281e21540e018000c50314100e0003044111082880262038660146000e08006002004545c091a0060140d0b0810340c0c684e405203800341c021b071000319400d2080070500e40f0344500c2841952021200350390f841c80d250321a145102c028140704481e0784210b404140392410385075401c0004010061041c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 175494712 1250 175493462 175493491
    0x708070302131d090c0306071205190f050108010f0e0a1e0803010f21020603070309020613080a0203240c070501020415020607111207150605030703050a062301150314 73
    0x4c0c4046400d2a28401e91a4081e50121083c44012a0042121048000c2440c0c0000745560350088100302084401c404880c1985001440368802a0540200c2d040e650000004e020034100b103540203007103a0440522070741682180c051180000c202d980f000604d1903d595051800c64060b450707103501030b8000e0f0f01c00100031562001c20007812000c0810103008040c112050207001e880c0781c010132080c6c40002d2080b010559035880d41811591110103440e00f030071107003098004442e203800c400b5a6580100b00140d102c1e12811075a019a240308000040325940300103144065510b54056099481e0040364040792036540a22000ca07010b0944071500780b0840640e0b00800d500d0502443c0501403c0382e001602e80700703800c0500c00659a80410080b02c0c201e9074800391004041040030251001007945400c8a940b40c080e00c440041071203000030f9024400c0c1d0042104100607510700044c0002005503040142d218880000100200104151000002e0a00b03050220311020708001710103424204540ca5594420b44 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 175495962 1250 175494712 175494721
    0x80307020d0e19060813051902010306170304050d0303180f1101030608070b0d060503030403060b0a0803090f21060f0a14100b070f0807060917030708070302131d 71
    0x80080d00395000d82c00c0e40e46216460400403200e441c10424014030080c0400140410348035a8084a440b03485034000c030654130a0500d40c600301900c0a4101d501340d000a00304140404d10440000100414040100003180b505103002d05020181100800507410302d40c0c2c46201d142015042120309410302e02c50440d01480c0c0780207113840300062128a4906041529000381400354810001c1e0f09400c5c3c40310301c0915629600f03c1032280004d000760f03410594050001050010800201c5e8112030340303a0701c2c201c0d0200d100684a901c0a55203009051046038048588591486941028025445007030b0b40360400d25114018203500d1031501c04c4c29519000448019403c1000310582c0740702e4108900150040d0544d50b0810f8000301100076030328060040341d624001000c2e01042448003100301140c1d0b00c280403503256400c7c1d00703049000780260001510110400da0003800d007211840c00710b0340b1456064468015603110b40e00124025001494450030001820001040c5416011003100c024481020300351042d261 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 175497212 1250 175495962 175495967
    0x60209040c03090f0209150415090c11031207050405041e0f0207051b0402071407090b01030507021e01020c030d050a0c02010e0d0c1502032a030c1602060403080307020d 74
    0x40c01d49030303101090715208061000400601001104a4040701e01c0c00460700c0e011480140e000301040407691003446c110709105c0c4809200902812920242c004100e0307403800005c1525200c0400a5046040c1c1040100c0c1c00710081019400d50041041e10308a030505072660089001c5490b00611466190f080c054821741c07511042c00794038882c6043d60400c1d405c000d0a56681551400d1000c01c04c0c26400c0500180340d90343c0c941e541034450003500540761004201c9851005a02c0c0c501c2030060a61840c1001c06509041d4001c0c01900c1c01598a40d00405502e00340c0e20207a00950801e10941c0142c0d5020080c07420702c000b0030006800c843e03107070310130004071400d2126001048800f0000d0304015a41030400046803800c012540041880c001d08120051086a103011a12011520341070000603101000b0b0001c000e9000d2040505540c40603090141c200041c4172807151400308481161826a0801803100d119003c95a210341c3c0c284007400c0e190a05849070b9499000da01b0071100d0400591128810105d82035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 175498462 1250 175497212 175497221
    0xc081f0f0f020c0a05072309150301090b04030f05040e01060503100f0902180411040302090a090606170d020c0a05120c0a06053004030e010215090607030c05090a03141906020904 78
    0x181d055441401102c0c0c6030700e07c2180e03984041c0440d100302c50000010308015070604010106002c002d00804c401101440e0209021505031001e400080c008407c0e100001e0180c03048500740c8090845042e0795a20b4400200c41f40d030700050641d01108190710000170035411105116018005407080561540356001101c4038094045d002d8034031803424074420707400c0741d0004000c45040da5019207000c2c5140c2d8654441034060300f4080b0000304800e15200300001c1e6410001c0600002e003072040d00360b8950780782d082e41c1240c0d54500403004541c81225032104000c907207003000041080d00486010b03100f000c00b190340000d03c10002640480003080340002e61070400c00901d9201d03803a602140000183e0b281402950b2041070b02c0081c0014148000036500003883c0c0c2c001c01080300000589001010140b5000b4801e54070f46006440140100e800d000f1150251401881955031180c0f025054905491460f02e84401ca0b8a030300039001c00303074040d00382148251180c0300d98210490340500384c05070f61400084103000889 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 175499712 1250 175498462 175498469
    0x170a0b01031112060607021c0302100c08100b0306370e0405070303030f0e01051303020d02071a181302180a180e100c0306030c081f0f0f020c0a0507 65
    0x100030441060048a45200315420990030381c5c20315103980e95480810b1103504c80e1802540d0000103044c0840816034001181841c0590144003400343d0180d000301500c1c8103000359807110041c0c10b644c03424082e00b800807020b036600c40801005480742800754a801501e1a140b0304008100b0300e401c0a12444003181d4981030f100501c040e02c1d183c8094a81501c8068440d041808001c00700364880c80904114907040d0441118907284000130007880c20101c3c0c415282d0044094100c0260045901481445001040c100c04445680d950a140401800c8482040e5400078000040d80703828140f1900c1c5640b030f035039114868180d4007800140c0c0d070ba00c51810344e40c0542c4205145403003100202e00a1044821158105c42c20b00344a61001c9034500650b00014208514a081c03006414944404880701641c950840d0040b070b030160205ca00380c107803200c2030705848003010048081682c840c035000f40125036455114a089a0700020001818420940040c0907603101c01610745d0564415102403083c84010b00494008 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 175500962 1250 175499712 175499741
    0x4090501080d1e0804030c0215030708060a0807050607080c07180e010c200106030b070903020f040b090408030a06180c1704030f0507030302040f0f0f1a0301090b01170a0b0103 77
    0x3a100340003d035550090781841d01082100c1c1c18046001c060281d02c41000346d0b03500814945d144491001800a2174000700d550000048064000c1241410322070b194500760380f07402c40a400350714100b0081c000b445c1c0c45244100c4030b07410200b007200b09540044c41200c014100084107071103540303214007040c429504840361400d00760f45010003c0c501c01e60020800c0c1002c0c10320b02d418200c88514108002d00401e2168005401a130f0500200400715a10130583e6003038a10865200d040080381e98207000880c0d08a882881d04003824001103808100c80e01c000e03650040b4884004200a07446060003080c1c2407600d462401a10380302d504021f84503800080b82c5514107090390503c0f10b6494551001170400b40d92004203001d00c007000545809044c480d404075005003500b89000741c40a0340e01c980004100001d407190000c581d0f1640d2001c17456040c444c0d040400c45008071107150071030f400e00301e00f100200a5041c4460500194401c40524181c0e112400380c4034034035052000801d941d992001400303488402080448 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 175502212 1250 175500962 175500977
    0x6140a0204050f010c150c020c010210110a08090304030507030803190b0310020f0d060b07032604021c0f06060f050d02060f030c0c030d0e120301030203060f1b04090501080d 76
    0x5141c50f030303203031681c0944403d1800103441c02c0c0a0800c41c02c114070401c40010002d01f4181e40d80e5142381c0000b580c03003003400203908491082040c50b00354802c5a03448140d03810290010030202088603c2040c00301e07008415601901e1500d0f40c0c0303940321803800070141c8c000c03902204080108102c040180c1c21211900107800c1c0280180c084410010f91a0740b14581c5c2c000e20140d01080142080c0002015207040710303124402080300d00d0302c40c003240846401c060402c03400104250300c5032000c00c5440780003c1108034030101c00301140d100c5500304144440c00441c21201000092101004120209100142e0740d000f01d000281980c10000e1900d0070b000309401044c0a400b00400305401a1240780469032289922841e181c2c40c0d444102c1249181d100344a4642442c3c840401c03000d441c411941c0c402e01d42881d4050031a03c602c441141d030b054036030109100181d40b603001000014000e1100464841c0c0c00315958980034101e800b59000210607030402d41080411036138a40040c024504108030307000254160f8103007441c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 175503462 1250 175502212 175502219
    0x60a0609060b1215030109050f060a020412030c08161a0109020901050a0e0a050604151d060409090302100f0e06060603061c110301023f0106031802040906140a0204 72
    0x1a49100741c0c54201511000800003444004c50808044000c400c002c0090143c501d203400c2460351907803041400103c0d800f407000441c0d040c040d80c0c8201d4040300c14110980b103600500e520180d80d10400301805503105503003040602003642c0100d0f080c1880c1d901c03c08107a8141c490700d40b10900604416040051070724070412070403490380e800c5801d9420381101c80c901041e404d03046c2008550310300e8880d40299080b41380490042002d40141414500c400030642e1000a41c00e90550303982001c1c8042c011850704440c0401043c420300d189504420b807180e000f401100e8807200d5070501d405c02c0302c0c07080110000070380e5074040f4003500c880d040c44034030341122007203490070b040d82004400520301c1c0304200452040f100d06003500504110004015102001008000b10f450314403503240b003d10840c1c189003860390082480000359604265140c0c0440c01d100c00c580e2600f4507800c0c040190010881d10003070b0300c011501720943c0c100580c2c1e01d005999442d4460a008564548160590800198044c00c9901482d00600052 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 175504712 1250 175503462 175503479
    0x5040329060d08070f0501141302062709092103240d05010e0115060203031b0d060801090c03020109060503090d030203042d0b01060f09090e150108060a060906 70
    0x860300120115201000c96185152110f403521401000a0034a96082c40d00d4082c0f01c4190b10020481c0b113401c01c9008190b680200390400800c00c002e00960002042c0810a07104110300f020340740d90b0004001c6003810603160f10000e81040000c5a001d086c03640310b80064070f410240c031201060710b200d5440c1200c1c110300303104502d211803070b8200c0071981c10200180c0c0b0382d4400707945400b02c02e055603800c44003c01100c0719410440c0d01812030100386002002c41d518001401c2403000040b24420700700d00000c00d034502c00016a5000035071050680655042d280d54020a0044003071280402980c46880d00c91002403844c8009424025154402018001d0510822422110200b03040350801e42500c0d0069590781c42d480d02c4240c5e8461460b640300180e01c003031415041111615840e201050040540340d2081c0c0e070380c010403624001d0321030f42c0b00c2c002200b1040c10400101e054001c41080c904000503225098113080801725801003d071710040c0d03164041c200f0f001792105544110300140c910700c1c000740541402c2c29000d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 175505962 1250 175504712 175504793
    0x50106080c1509061201030803060a140108042604060203070c1e0e1314010c0e19030204113105031911010306080d110f060402010f0f0c080a050403 65
    0x10410b10490000b802280c659412084403020240444040c0f029610b80c2001381094204440040c01603048a0300071a01e840140030310004808140d40c6c046140e992541ca07e0018140381505c120003400e00b5024522411400002e0009040c0c00c1c0d0007035403240b4150401e4100044154421305032004002c29266412140460000c00e9655189000083e5201c00c4100310b010801c0300b8010700100364400022145c0c51064021003050b504969541d0300481007402000f91109141041d200d61900b00031080005051640221000c2c0f802025a00e0504e0200000c3c1c1005c2d0351200422100302c00c100d00c044d030440750a400040c002e080141c000b01b2a004c3d0304451700c13801c2c41d042003014080041d404142d1003141c0c0b00e500483c0c040d1541da030580754406d280b140c0180c8031041a0302e070300c00c0b50301413640310182d12140000c48a1040350142d50300014950030300f0058030221010554002007100421070107010030300c080000e240303610f40c03507880964031440d608141040210000f24007094800000c0b0104090f22080070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 175507212 1250 175505962 175505989
    0x61503180b040828030615030506211e01020403020915030a080f16050c0f01030b0a090b060f03130b0a05100501030203130b040818030d0203120606040819050106080c 73
    0x40c0d1070b6513200e600c407850030128941e4a10084c01d422000100c18142d4150081c2080f01c04c010074400415858681c1541074507800c6425540007000001c40c482021003c9045200e46c0c20924165119401003580c0110010890904c520b02030390002030400440c20b141a45d6644440040102030a40b6440380010351a000c640e4405001c1c08800f260105003a14583d04403070340c034401207006000b13640c2039151440d1901e405d610314a04c1030748055851a990350182c000c0c3e130511180144199415801c00140c0300003000414500e582080040c00004000802c400040d4000c00c0b04204070100200146824210706200404403529542480c06118481b401070305040c05981007402c001d0307107a076980210160007002480b005455044280705100038484004000d1800d01d2941d42443d50b04a044001e02d60303602d00c110400c500580c003c00c0300c0c0d81101c001010351608805d0050000740351603991280b0305e26002881209400d0404000c000b030080103402d200d80001001282c0103010111902c4000a912200700c0c2c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 175508462 1250 175507212 175507223
    0xa0516110309060922060315020906070b13080c0115060c0b13050f070303030506120d0503150d021503070f0f020706050c030c070b04060215010e0a0e0c04061503180b04 74
    0x5080701c4150f0f900818400d01004521401d268000038401c2d01e4043d045070701c01500d9001d1024641c088d030281c14021075070204c2c0058020b514008442e81c5000302080000c189400d04040704500703000142300310300180040c103845d0001260981c01c0b00d01550502c0f5465016005002441090794005138200920a0f4400d440780042c07900403100381403950800b54954480b08044c01618408400c2540592146029205c10740344840b5031107102480329030341c0b43c0b0b650182000c18024030008420701c541c0e4000c000c00450107402d072540e450702c0340e002c00c003c1010140203440c400004810070100f0382c2d200c010200101c0c0146030100030301c03100f403001a403a00a41e001e01c8041040c00103d007241e54004104440e04a4180f100321140b080c3e8440c92891150414042c1e40d005005440340c0c003512000703e000c614140e512607081c4a071143c5807008075000500d901c480806c0c550144210118056840b880741100608c031080403119162070700c4500030700b1695030b8141041840705841d400000b055642d03000c0c1e0360041c0d104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 175509712 1250 175508462 175508467
    0x30c0605040c0b0310030c0803070c1a070204020406030903030b090402090106030c0201020c0f0c0a0f0806010b0306010c0501052d01080d26040c0905010b1e1c02030a051611030906 79
    0x1420207800c42442c0c1c1e00b00b44401480001446481d8150110002c00c490082c21142820f54441c11516180e01ca9240007500840024009202c076400102100c150086042013140ca4042e80d036003c1401d91b0443d5102401107030b40c604e000410f040e0180622440104110340c5103055181990005145c0901030042d281059980c0d101c01c100c5030f00035811a040641080111000108100740c1c0b507070344e95428815180204030343e400c0000d034503032031408910940b503614014115503800c04e8500c40030b40d04020100d50411401c1c44480f000300f402840348600510111203818204020301d40c094000c00a490001c04030b0a0b0305c0c03001000303132100c041440c020200552900040c030300b0507400d41910485181800300c80c01c1c041c1070107000410881d0083c2800322911078005204030303030f62604544154000c111b0190b0f8410240c1108145103800d5600030404034801c0304001500d2089000040d00706e07007086a102c440180e0364400d110700410207000d100c003100300c43c2c60604090100da0140c0c50b00c03400f42d4950f031400751001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 175510962 1250 175509712 175509721
    0x506040c170907051509012c0d23010c26060d030e09090c090a0b0f13020f0c100e03042706031515060806060714070801090804080609030403030c0605 66
    0x42c400d843c0200300080030340703083d0b980155095003558004610103011441c40300da1040112044031b82001030101801070201d030910203005200d66203d54100488070303c8a100c240d4450128010f520a12001300d00000083c2408009005440c540c02400b49401181d02441102d00d40700d00144102d0b0300c09000c0d10690b98078800391800f50342c01d030410221940c0c484454030421000090000307650703000c045d003203030b604015494400e001400c540e4030200040d08588020000240b90038a03000c00001c8410048005107495019a40c480c0e030380d0001c418490150f004007840010bc0d11041c0200b40b49183c090000d1440c0ca4940140243c102054a200b802e10201c0c0789001d481c800707060ba11400080d900400590f5460340304030341c1e610042c0942c0307200f1055408507560108400d481241c109108680240c002481c0524685030020b038461a4041d00b0628441d035040400d04007002c0c080c0f8004548519141512503003004207580c10203800800900f516401804100042540512000728480d00316000280c0b0703448 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 175512212 1250 175510962 175510981
    0x9060a1103040801020c340b1b0607210515090403021c080a1401030b060d02040f060803032706060402160210050921150907030c0605040303030506040c17 68
    0x969018504a501c0814a20301c1c4d21800f1842d01b4800e040e50f0ba00c0800040310380d8079903030301c211500c805e0681207a20f030741e0500c01400042c0082c89d0540c0215060800b060b02140d0803458400301701e50400020b084c06a0040443c60301d0541d810280c0740e40c000912031440c081c1d42c0c02814542050703150f440740562001107410f160090101e82c001400c028200a200d0319a08805802c0300e0050311006d10316890807c8240c4400d17942003500d41030340c0e440514030103240c46400401000c2ca144800680c0d010342c1d1511482a508928801d00e4010b08180001d9900c0e40307032a20764100d58004603640c00e030900c2c05401c080c505105000c206154422000c440068640214003042d03180f201400e00001c1d0041c0303060b120362000c2600000a001071250481d140440f01e2408100200d404041d442140600d5003c0032040f800394201250781d99014440c081224900c507541c0c2c44014824496a0103000071803400503040c018140d2502465900080640342031104244005000b01152120060158241040c0e00810080c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 175513462 1250 175512212 175512217
    0x6110d060303050306010f030207030909052205060718082d0d02071e050607020f0d080403060b010801060f020a12021608010204140108130602031902160b07020309060a1103 76
    0x128400080000d25101e00c1c002c0c045074010399025000c00c02d0484d03071407586c52182c02180c0c4801e50607940c030b01c0341600d46420180609005801030a1150544d01507208014060f026110098081c50081841b400c00c100050040464040040c0310061040c106000560000813000303082d1070000c248a446040c001c00aa1190300c1c00240ca400d6801004032001c00b6a40c0044e0b2101582c1802c6442c0e508080541c4d240c10011006204094108005000400140c42d00c1120a0b00303000019105000e048000c2d940e050313442d0710039001120000c0d52105604141d5a00003840781c098500c500344506002041d207000b0f569105512002004d001c28200c4180001e0320034000f0344000c00e01e140110b540700e034a81036000d010390094015011159010b803028509588101081c5019101c1a07940d000400710548407000030b580000c0c010355040f00680000d0b40c2608061004101d5540483c1c1008c5545c201494000f02101c409081d100855106106042e0140c0d5904212054910766007400c2c203031120303100100c6041d030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 175514712 1250 175513462 175513477
    0x1090f05010308041208160b060a08010507022107020d1505090c011d0d0204060b0c121312030207081f0c03061406070609020604030609030207060f020a080702191404180f0611 77
    0x4282c1c10590b410400c01c8d040031402180103c4291220a0300d9020f001d00301d52044440000517400254490b030f80d2008041d0f404106600f0800007403070300c2440d8001c2a040c03824210201e481203011200d480d0003a50a00c507103a00001040c0207080b03d2501e03000000c0c04180540d0055004c000c803001c007401c1903602d0400301840303994080d00900c001940c503202d600c229001411000c08038002d24030030391100e4000008680e40c00ea00003c10844040c10210032080d0409100c40c11000d5104010700422101810002c480603a050070041150001440c2d8629003901c156024200515040100034440800031542d0690a40303000c0e03800c0360303c503003050800368003a2941c140e010750050310006012082c810903410a41010b4000e0f02242c0f012561190129030f261800841000140c02c0007000c500000c58002c000c00d0000e0005101c0b0130100040325050403581c5140c0c1c06080c2c040b407808508211400e00c1e01802ca01e403188015880142d512a840b03d0444070844030f802800c0c0c682d1040d00c1b07001305031464140e4102 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 175515962 1250 175514712 175514737
    0x290f0d0513020910090c020708060c090a090e012304030c08030a02070b010b0903010c0c08120c0405120f0106080d0e060714030708090a120f0605070e0301020a0801090f05010308041208 81
    0x41c1042c8600c0913200c0c2d0103001c0d421a4a0628240380c1c819400065002c046409005c010308080c0c0e9004204040c640149400700d900c1103400700000390000d240d0041d45500118240005501038821044110161805414410a00301c000030000480d400500d00c0c00100c1c1c0100c4081e961f680c0b40c2c80c40304000e120302c0380000d002c00e4260b000807030040b020002402030711400703900030050544d46480c141e84d10150580002c24000f42001440c0b03407851000c5c060b50300306a03101c0c0c4240c00d103a1a1000a412056003c03031949190748003500c1d00c070019009000c1c2c0d000814400c006011110b62418000780303082034495910f030240c0c00005807542008951070500305082c01c24415030381c42e800949401041035004040c20341c4180010300000c0303420400d1044c0007080c59071000e0040c04e060b0700c0d07a452001600c0020010303414000712512030b4090b40c07428001021701034616a121161503052031011003c5426400400c14506d00c0c0c42e0060002950440454041d69074404502c2008103180ca001c00c100d100361100a070301d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 175517212 1250 175515962 175515979
    0xf030605060a030b0906030a05060735060306010f180e0312040b010e01060203031e0417040602010e01060e0c0703050d090c0306090b0703110a110f07290f0d051302 72
    0x1c519070f040e07120307142c20310084601030180d498030401c050340c078490b030b4201404039000f02d0f002c0b408560003800340105030b549501101854015245203100441101c00e0020002030b071810810480749820b1002c0c0c0d001d040c20091a002c81030400305000e410080d80c1c41c0b80b440d102d90312181349584850400c1500c255601807041340b5014a4507140c07503a0001c0080c45903e0543c900a000415501d0011090300e2084031140404503402c40307801e0603940c0d9001c0144c000d45402c0c1031503542038402044000240017904c0740345c0012070900210030001d42140e200340d02c00ca0741c4508581c240065000c0380c2040701d0840341c040c502039440f109801c0c40040100502c40b0010600e5101c10f0b40042085441d4000d19000d034000c0c1c42002d520350740c0034010740c262480c2d0f02140b924a04100200e010f0f0741c1c0144c00352081c030f040903000c684140c40982c0e546c525100c46608002100725036501855610942c40c000030b984001d122084904140100220f00f22074012414114103440d2204001444501d035903140c2c2d610250000d10161 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 175518462 1250 175517212 175517227
    0x211201060e01140304020f0418170306012319110106080c0a0608040f080a03020c0f070e060109180f0b03030703030f0501050a0305070509060312130608010f0608070f03060506 77
    0x148101c0342015401d01141c0086081802114180c0c141d81c441d540142079001c02d60301c80b104000082c04944100034100240364061000f1a0110307044118040564003803031350b0390401308000f52402d503845a8640c0341412000226118103603050a1b1910000c1207503042e015080d82e808241c4840f05030f84440d0401d036181140c00141ca210009100324150020340e01c0045207600d8100850340d05500721405050b181d00070401200040d10342009041210481ca0018140780500005908052071a40c071071480e607008038003c5c80407003080541e054101c1403d0901c40060340c07401c0020b52004e8151400c2d9111203944040792500c0d0040c07600300f5010303884010180c03641d0700d0440c68040c00601444019600940c45d020020407941005510301055a82240007032180d58036090402962000003056141c050040640c54044c0e0901000075042c110342c254802c20350380b4140341b002824400b0591140c4d645c1c40c00c0c8101048025080115250006241d1411042d103000c40c1000350301500341544901e8101c600001c803c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 175519712 1250 175518462 175518467
    0x9030b040309090539250c0504020412110307180e0d0e030c040e0c04060b03010e07030c05180f0303190908070509070c0311030d050a050f070221120106 67
    0x450a9444060f000c101580342d00301c8a80ca02d00602448024a20b041c1113091090240504214810400c001d83e440ca07081040c010b08840948081c40c80641004000460301084a205a03a030007500040da4210708091400c85a124002c412180103080e0a8525a40d40c07116102172001744058024640b8400048090300c040d0001004502c9040301c850003440220200f10344a4051812500d00090091074484d0910b02088000e141c2e28001445620031115401c00ca80c680340141340040004144560b1290315103246420b800000800c41000c15140c024845485074001041c0c51042c2c06812040440700c0c9103c020a0000342d80d2814190306110101d004c02c00380d213141b00c858091310000d036942c000d65659110416601c0c2c046000c2c10b0351007482000054000c91090b4901036100d400303460080f0214802c90440c6d42541d0025480c0441c60392030f882000750980c50740c0503480d04403014a09c1d120282c40c200000949850495013844130315254a4004410410b103d000e43e0301e01d92503c03c14501c1e40d60340c0c0c24007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 175520962 1250 175519712 175519727
    0xb0310260f010501060807030c020102091f0f050a1704050a02030a0b15060309070e091221060d020d030f02150906070207050315010504050a060909050a03030e010c02120304020109030b0403 83
    0x1484954420320150700719040301801150b04849264940e03d85503160113405a0141944c400ea40003103641c01e0164020769a50074543d40c075071150340d114100b8072060b0040d000b401d803a00c650700082031100400513a2b9030154004032400104243c0f45881e003443d240e038541107081c41d40301007001c0e525100d0500c600c41400200c0b000d0318001c2c4c003801150301e50580940d06004050000b15202e41e17050300100410000011466800381e88664900c051303d60441c0290a410f0f095040104081d664001c004d03580c00c2d03243d00303ca881641245080381c1e44031181d9066030000365005228200142044a95803100e01031500030425206610700b01032044203186001601ca07590b03a0030807182c11006124101001840e0b0601058484912401901c4101981c1c00d200611010303002c064a00b8226598880c000a030b4950345108280b4a18400c401805258005090007016248032901c000f9140c0d240c02000e5030895000107100004040b0010040c0c1c503643e65000580700e488090b80060100c0c03500c401000100f540c030240 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 175522212 1250 175520962 175521029
    0x306030f060e06090703080316090305070b070c05040203160c03050f0f0304050d050a0f0305060609090a020a0306062c180c030109150f0509040f050f030d060e04020306010b0310 78
    0x440300d0f19556040041e07591343d803501c0041c1140b4010070101c1c03001d0080100c41c80240300e040c18030070600c0b075403640ca8174604030040d880034441c41e0700401c0d030100b00000003540c1401070400721025811350610800d0ba0104628003003000007840842c80611007014040d01c141e030542100218115100d1220700b05d0701d441a802110110b509009902103150f81d6800303181910504001a0b640011715602100d040d00140000340140350700007400e0040c50391540d00d050a403442485101e001580700e13440ca04002c2e05940d840e0300301c2402d2201e4100c0ce6111143c8501071402401040c141403083c1500420124904060040010304100b8529080080054002c4021030482e0440c000c2008482840314642005030302900500414600d4408100141d01d4044061604070b07004811202c2181696034505181101603945035860350000700f0107074500049482641c00030071421000e80340ca894140c2c00282c5610050050340f269032004800f061045400e10540c1c0040d00380289800344540b000c10003640840003054 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 175523462 1250 175522212 175522241
    0x2190201060807030b0402090c04050409030e01020105181f0204030c060c1e120e0102150103050c03070801060308030c0c1002040902041a180402031306150801060e09030a050a0306030f06 82
    0x1800098078150020701d040480b50046200917a0342c03110307400c100f0070000c00741481c0c2e06550180f10100d110354880c41041d0340c00307200b500c400700d88000120001e402d44400070022a00b00c41c01c90241039110b4400306200e00703100400307060070384103800034184034009002c3d40c1c10103030080c030303440b6004110036401882d0460500e02802294070090307040052180310b404002c100500500400020340d2201d1300035035000900100500584018032402c00b04030741901c0c800d80c130544136648001e6009180303040038040d0f907000e89446c200a002c3c00d81962940381007444050030020b80c00380b00040c0b01e03092240c10b2000390380000421005541d182d5a0b030b50f80e03501940040c000e400c410306640400e010b0001c4114100c03200001c9412800d400e944bd002e08003c0203400007400b40407501e83c2020a040082c40510451103090821054440c1e524145840320b42100d0090f004050401c403007030b0030b01840d92000801c0e41d00b00d0300c06240c9130351384524120307040b0b0150405520052017015000c070504100b103c1074008500228011 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 175524712 1250 175523462 175523471
    0x5010501061710030305160803150406060f17180f01060e06220b01051e071b0f0b0d0f0203070c120e010c060203090f0d020307051903080a020a030e0102190201 70
    0xc0d80c0d44080e0310035a0354510b91001802c0400000340660090414100c203000386180c03c0c1f00644035032601e03500441d844038081840940d040040c2c9041d01c81c06000d4001440c004203812040403000e80000d201200401c01351a05200051118110307114042022918606036035200e00c40ea9035490203000716000b00700310414110000340282c101512122005c03000c0c0c503440780c900c003000c044580c02040484007890410200b0050b00d0250382c56440440b009120082100d59104540e00303100c1040750000d00001940084a5000c1041800c0e00c03044605a50240c031260f6940e4444400c1c501c000c0c0810901880000d001000300524182c1151544158502440c141c810400c20b045080ba1a1a60020701501155260201c1000716000394083d580c030100c403100710380d485180801d82a140c19194132410006034400500d5008110090007107590741c0d003c026840c8440c941a0350090000400186989843c82d40490601c19035842508226054103000e00210340c0c540f107800001c045412003c0081e405036081 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 175525962 1250 175524712 175524737
    0x20409090318120803011e090204121a0405070b03190c0e030d11060a0f090f0506100e0f0604020a05130e061005030105030d0302070201121811040c080402010f1b0501050106 76
    0x3c626500000300e60141d54145507a007840000300ca41541040b0b0701c01c10907a81d010114101e4290320041015002545c00881c050aa41c0340401e00c00f046030f40c0000426020b9010710000600010b2000162140501099180e555090501c100c0c03004845400c0c403000d003809444545545c1040c9400c68503030056050369081e0f04800b00c165410010040150400d5200e480000c00c0c030780c04bd074440f96042078011804200100e0a8032480b804006140b07060320540c10080030300c80c0d40c1c1c0b420140310f00200700c01e8003400034074034010b0146200440c00030112070280b030b0005150a102440ba00844a4091200c06101915500d8409c03206040d1022152140102548009240200d0080c0d05590407650001c00600c6410b100b00002c602a40024030202d06003d100060078450300c90300d0042c0b0002c002020350702c1000769a1030602c1c0b40343c0e6491288690007186031802c55201c040c2e2091007954055028204170002e50346815042382c5410030041402c49402084008104010041d088913040340c0303c55413940300039a01f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 175527212 1250 175525962 175525979
    0x1c06060e010e060f0d0308100906030809120a0c260604141e0c0d170408010906060501030b0d0201082701020306090a0e070e0c040f0801090203011a180901020409090318 74
    0x844d25070141e00503049102d2100107032140038555880f103000c1380000c59150380c81c0f130580300303558107034004a6640d0300c04030314038141c1c0c2444100803103074142200061151701c0840d290315200328140c0c050030565950322440071b04006500c61003d443c1200d0002283d400340b815082040050000c0d095007805405140c15000c1074402c00b04030341c1044020403003e400b900400a00300f00d443d0494502c04c8076104501180d603440e11030b218024200034a00c1d01d00100e4080070500d0050300301d9001c0d1300b160b8141868944902d1032502c41040c8400b1565080c2000d0210741c507041080544200d0844a400013101d003050410100b0701c3c1034018501a050540c1c904803d0b407034044603401035451031100d038151a880080d08020440807a000290030069800100b45840d840c1c41c4003107100c005c030303401c800410b0713458010b00811400d013445010322018001d928a90000080303c0082c09910340945802803248100c004a50601820b40c1198020090480304100b41016864040c01c00c0040c4c050b1540700d241080d90001340c0c00c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 175528462 1250 175527212 175527229
    0x2d050a050612060f0414040b0705130501050a03090c08210313150603050d0c050d210f0e060703060e0a0603030210022101030c08070b090307051c06060e010e06 70
    0x324010803081c10300400b00c4820600c41030007055603074000c09104031305511341c0300d41c400d443c0440ca080c41880154603040c100220070310070103044541004000c003d68091081c24040c007100741c0394246041c0350f5400714690704502602003144d01800109081e0f500046104002131440030b02c80381e00c0074101160080e2818030301c1070300003282d404040403284d440082c00145110b54614910700c802070005000703030312a200c882c94038606118041c0810080903040342030110030080d00308651800d19202c0703900069502c850380700c0001c408080f13030140d4a8007540c03990040e040d0031038850040c2d040304490f003d00d0040c2004000c9c024510503543d4409421002c03440d80010f900a00c026260950000c24a01c80800885002544804c08030241d2070011440320f5500318008074064002d41c0158011070f6214109002c40e070903c0200d40c00346800f16010001c0a019444c00700c0c692044410460f110030300000081c0b20000648c121850050800780780c100045202d1665010b03140c1070b60b050700c42054031551200140201315 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 175529712 1250 175528462 175528469
    0x1903020c160311060310080706091a0901020d120e010e010506041d0303010e0c040503030a020c0307050f0f090403140c030a020d080705030a0903091205100b01020712110a2d050a 78
    0xc0f0400c40310540a401c0001c003d6802c80100325181c01c0c0180e40f50303d1203041640a4000000182122008124079915500d810b000c96240140303d0745007a11000020b0358494210004070240071820b00d6182410801d40e0104880c42d189000900c045511100d17520f0080c130044507841e102e03c0c074028035607802d209450305480180307034400700075403459080c48040a452000200001c200c51000c01010a607510103102914140c001600101040f1852108050038803041d5007015010720f9500c810441c080c3e80e03020801543c2c510039520070000d174079142411255211252070106862000150411140b0000002001c40c403801c0da0079110220354055080355a1803090b102d50380011000c0c804120910541d500c0f0f6041c03075200e41812080942e842c0100c445000150f4003d90b10b0f0b8006c60400d1201e10514000d145a40900b4806807c0e25410305100c01d80692002001410912149280003266250042080040c000050100e0030164640da84282e00041c00c80c0c0803a41c1e07443c13450380040e01d42450070a44059 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 175530962 1250 175529712 175529723
    0x91e0c2115020903210703090803030601050901030e2503051c1e0c02130b09090d210b0d080403030e0102071a09010504031e030815010804060507051903020c1603 71
    0xc50440390890019402022600b5898002c41a44140041210320441405110003210584a034254140502300701459448040650010004c03c00140c0e886803c07504001c42c2401c0020300103c80d141c103d03284c0280d101c1482c407034211048071250031501e920b6001c01128031030821520801c0c541c10840602d9101540b00c0c034080b07180021841030349100303210045800ca54502c0e000303171002d001d0b40000d00500d00800758038070300301e548003074034802800c04101a50303220120030000d001d00c40380c1d01d40082006000a824550305222900315044501c0580c00070207844800421700002400d1500741819a5400f034071046002c100c0b2001d0310000d9500200320340003112a07262022818101038140005aa4041240d850405c01f040001200041140482e520f05a0795140c0160002c4501d00d405850200083c00c01010040d50700c004204503139105580b035500680c030650114043c2c5522400340d4190244000e5844c450504669043d4440c1d03055010380b214080c80d1045840c490f10031800d0302442c545502002c1d19 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 175532212 1250 175530962 175530983
    0x5010f230a060f02030c011b02070501110604061104031515080c09010504150b030a060e0f0f04060f110a0f02010605101e051c020406080a0e10091e0c21 67
    0x2c0e1a025031504103c21500c0e0050b00e01e48901c3d00c100340c0c00c544000d1065041b4030000d410280900364100404009000d003800c2c1021444d000408850340c803100104000c04d030540302c1072004114209007080d64021607010078401640c15001c0c10381c1c000350504c42c01d011008401d403000020000700c0064482c0440a0241041802d64207190501c40034152020610800c0340c40244002070000003640118030403001002e00003042410000440b458a101070243c0d60541c014005005131000c0d030034000c42d08164400c0d0000742d0f0079107040004004c0d010284040c24030707100106103410150b40200d41c0210896460f80200022621502044904102c08184800059005d2114044a500d000c0d01d40d12840d2a401d110342007034600341c907015070f002d10009c60b4030419402040c200581074120104030b80102c2c0120b000c1c400d8001c0c0e01c009654032100601d508c0c2440703441359039240074002c90a88500b8080040c00d0004800300440c140158074500c1d1380b0607010301d280c810081c0a414442000141c2d18190720051290 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 175533462 1250 175532212 175532219
    0x2706030708042307050a0f06020303010b28030203060a0b03011208090d0203032b06050f0904020409020a080c01110303040b071d04021c0b03011a01030c0309050105010f230a 76
    0x48829500910441d2620904002c440c00d40c10f0700c0305685002e00c0c40c40c0090103054205024021507440d00e42c02200c201d41070f0345081c00020307004019a81503e440300d02407901e5025110780080000c0150700e0a9640d0a0126003099240e42d05070000d621030503081e10f4a2900e02c0d91042404114402440b030342c9150320520002c0c10015950758002e04060400400f401c00740c920507000613040d40d0140c40a0151202502e02040304010080e0f0411151011203004101a07468640070a00640d40090701c60b100d04c0368500001c04660b01c9601c0f489005030090030415001d506c4980981d90b0303806142e88240441c44d9900b4400e1490380000440307100311340c812800c405503154072109550b0b48005075803032111940b56260709126600c41d40b01801d604c400301550700d0342c44442884002e0803940c40441c12806a4102a001c518046240e580a840d0940031b00e03000407840c00f00d803c01c8005000300300004080e9402c0200010784d00d41d8034141c40d001e440021140c65580d60f44081c040e440d44110160803504452000c1040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 175534712 1250 175533462 175533467
    0xf090f0d14070203010f020c0309010f080403080f25020102040603060f1a0715150f0803070c061103070c0905040314070b0601080a020f070c0810021305060d090f0827060307 76
    0x40a000d840900085600301c0d02c005000d060b48c100307a0f6581c40c41c3d0700200c0c07044071395a480403000040d65864105010941403e880007010244020610303074a845180000c15039104040c001d4541d40f406a25202e4004100120028042e6006100e01c3c8002400c0c01004500011116aa03204030b43c54601d01035080501202c114482e60401c038801c0c1e4080e158a00280010302882c050310364003031442e0550000c8036040100206003034149801140309a0300c1440700c50000703980243c49405550040c00d2401d0381c400c1d10044207296104600b002481905401d01c006580882504068081c5100740ca412005040340d0358015901d0140d5100071b0511081500483c0d640c0d400707055905d0b0011b024120141c6811503242404419a112403402c48165014103803c110680d0203005017a040b0003042425498954100220301d0729620300d010721840743c880020710070352259a940c441403a8980c840c03811403500215041c50301b13240e000303035904010f000c50314034a1080110401605c540d200f40000c140b00e0030750310385034000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 175535962 1250 175534712 175534717
    0x140406110a1b0204110328020405031b03070b0c0a060501060804120c0602041d070e060903151f0b04080724080a24030303360302030d050f090f0d14 65
    0x59800a5845c1c00d0381c0300044150005601ca401c806481480341c095680c01540d10509614501c0003180c03051002303200035a40031490020081040c80310304889224500000c0c2400010351283d01d01180000304000c0310780340880c00c100100e010764000c00c00c40e84d80d1030302036a6880d170840f8000c00303580d102440d45680b81c1c0225245958107010b034200509058507211030300c4d0405d40f1140d05071a00e50090007000f00745a071203481d4030710100b0b007503440a080c990305101203a0384040450030803402440134800228400d070b405581d27603401190130b0780380002107640e0044400c0550140c09050140e0150042c00f1600000d1041c0c0c000c02c0c0812600101c108402208084a8551004e0700010449480d001d003005441c4e098040e4000103a07602200c12a8603141d450302804603042d0050542200b803441c040403202c020444400e038103041e60140e80c090040c559140c00c9081d4480c500b4402c2610b407900c42400805a802070070036114410940445840c1c080580360b095a40c81d80c42103680028070041c6812080c082d28801 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 175537212 1250 175535962 175536017
    0x807030e03070f020906240c030f030a2a211803030f150f051c06090302150a0e1011090607050d180f050114070501140406110a 56
    0x1400a44540e508122074115801410180c03250b9141d11882d600394078103584015001041103890003c0201e403050460f02d4913502c158010303440040865a940c42c8502482140c80040000d07100681d01e00e0140d410700c006100020032521040709800345009035400c8881e500c50405c5298555a692503c0c000d56001d06c2c01c0703688421501c5985880800d2005041802c0c078141c0103100c1c1c0c901183c20400721403d14100c0320041c582d1503500c199034000b0484070841e80100d50035241e0944100d2807606400010405028641c1d0005040c03d20b045088424180e01080000d8010b6515010601ca500c3e101c840d201550301029601c21107810500890308141c0f400d42c010100c601100d0b054a04001060000402542280005690a8000c100c0c002100d607400701880c0b921400b00c901c25044981000751191081840d802240d06000441d2041441c2c440350700280c40c40c0650080091128410a100c0055506010f840440740d10b0308100d40c0d1003491680b48107481c07110000d0303a50400108044440381c80e140d411040c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 175538462 1250 175537212 175537217
    0x91d0615101403040b0718060905040903140301080a1101050a021515030106090b0a0f06080406020a0c080d0b010206070815190e0115020c030304060c03030b0f120a2003030a0807 78
    0x200c0082181000030061481030b40035124002072031410500c007520006042001c2c7d160101021000d021480d008050201951015500058200c9862409030790751407404071403040d050720200000030383c1c1c000003418401240c0305540d6000105075003001540e00d80180710808001d81c001d41c040c0d00c01203040c180401e51006444c09084088050301c0086402c5455079049125116141d030111039041c14824458070080142280281d5002d01d017520080418101402c018001c0e138001034082501486501420911908400880c0e40c0d040010a0007004044411210b40940121400680c410b409a13020510409211200001e500d10302c00401c8441116070802d440f40141d0500042101040850311502138910b89080400a000c0c4c090080c3c900240d0090442c425441040140049503110301101c425961504000c140001e012001505454001c030606401250100780e05044010008071310960500a11500808150b2449005454850b5068580c0c160b40100040075001c0d124a403031691119162 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 175539568 1106 175538462 175538477
    0x7021807020607120905150a0f090206160303020c0102040602160902040f052b060f1103010b070b040503040f0f0906081501170c0901091d061510 64
    0x700402c040100e11940c100c0c0301d0403a034002c1c10300b032071b44681038821640e10540e0846500800700c07021064241400d1035020851010310070303001104d0b0050095440c0100c01483c1407181c040d880d030100c2c2015402c05c468800c440003840a84007034004c90340a4862018140c8014280441c283c212a5260f481003004010001d8450040821601e0a036440113055041e40c84890500c024014000d5030328000c06e012b0000c000440c0c0c0b2152000300045401c00c10320035521155900c5000900994402090810083c004145030500b4154840c0c802c408507454161241420104203000380e01c80c0d0210582d13440c0500840706076004030000b40810310000c026a460128048580d404103101c2c000c460782c4880703c1085000002d100c0c01003859030240000c20036580d12004400100500241e00030304460081240c0d0004001203001c6004400078141e108a12045408110210004002009c24004ca0 = true := by decide +kernel

theorem cover : BRFrame.Cov 175359712 175539568 := by
  have h0 := BRFrame.cov_init 175359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 175359712 ≤ n) (h2 : n < 175539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
