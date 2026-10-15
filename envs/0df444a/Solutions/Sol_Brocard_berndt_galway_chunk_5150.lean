-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5150
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:54:51.426279+00:00
-- url     : https://prove2.me/submissions/95549333-bd7e-44f1-8a91-f7ab2a097662

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 926079136 ≤ n < 926258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 926080386 1250 926079136 926079139
    0x10609060b1602151603030506060a020c0d14100f0c0201050f040803040501020706020c030c010f2d0f06171510030b1b030c040504050c0901051b1213092405 69
    0x60201203003d54840c440400141c100080c68155500001c41c2c0c2c00342c4001d0720b100e00794006440c100000301c44d410800300f180c0c2c1c000003a070014a46001540c0c100f003980704080304212000c41e00304420200c425030810442c0d80340d20403101c0100f81000d13681c94410845059403420001c580c1003000784900040c0b60f541d1980c1080c1c2211034540c0d0b9540d14282240684245030f40144506d01c001074401e03060102002510000c1d00c2c0e00020702c480c81d010880002a075081e0440080700304800150f0028242d515400c210166006070030204100030340707880d11f00c12103202c0d074801e10000112404401d00e02000340f01c20307107803d086814481620b083c82c102e201e01003906404018120400240031400038003600b00450b00c46c010325281103a491801101000c04c54115126141c01181004c01080300604000140e800c28141030751040c0c10704642441c000c010703180e5803464607128064600c00d284001883c50007083c03101080641c9079a20b41c50005840100d0b545103010106944408200b80ca41d0000b560005049900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 926081636 1250 926080386 926080417
    0xa18050613031412070f09050312070227012d081c2c040e070f090c0e060d0207020a0305060f0f060f0a03060c03060513150501051c180f050f010609060b 67
    0x131030701c00613907407d001500150340c140b2941d00b0031030041180c0c400401e00d0030320a443c600c000c0c1a80030400000c00034000c2c503a8003441b01c1c500c014068403200240803580f03000e5098030442a60a00105000b070301619030001c000d1030700460403409200d440c0d142c0181c0005c500d880e200b4031550520034142240200f4640c80c1069400d00f0301910180e130341c1e58200068a182d541d0036a07043d070741e403000841e0402c0c0e6644654171142d03007405940d511142c01070b00c000141c1c80340035048a1409000c020040000d500850040307038840340c4400f0100200c0d50800486208880c005a054058240341f07809000c081c2008021900c5080c1103a200d0b002601c542c4c0340d4004032580700c00081181d4030f120310180c003e0105500220b412000c0c0380301038044e0600d00d0f00714075a0100c00e01c0d081c01f8410745074001192a4402ca503200c2d43d0080d21035056070b200032803a6000502c0c50746c000021080384a955641d0b502c183d085c40005890302e6024440059600e8000e104202c000d00102c2c03401c2110519201322007109010700d03041d01854a5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 926082886 1250 926081636 926081657
    0x1014010309050303161202090904140109080a020c13090519060f11040302120115120305041a090901060207080d030b0f0a030b041b0e0a1805061303141207 68
    0x34025007140e564a640300e8103503a2645400000700d46031444114130040014900d10707110388008500d201b250011a80074041000c21340d21503c0d06155030b012070003044581c0d0344e01c2c034039031010980c148041d020961940c0c1c003400c03500116108001000001d03034030300030000340b600e980c190014000180d5002004244003980c403114140e424030701c00400d00d050050070b099061120500b91a0790500040059920032500824005e0000d0b440600b2100c14480104401156410610a003240c00c5003030320300c0610a00d00980340c941c41e4140359443c091494145134400c1c4001c500e414907858064825400b42c0314078401030868030f15101c0410380c0d82c80703074800b90010b00d95240d8143c440350710340ea001c1c00500100038020103180d56483ca08101c8071b10b401c40b000c3d105d0050394446982400c06520400b4101c1c0d804803141152922203005400c0141540b070750003004410f030018244001381b01030149a00c02c802c015079280c0c0c600000d040160007400420906c0408060400c0701813107690101d2580d030340100c4146040c00086 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 926084136 1250 926082886 926082889
    0x112a2a1008010626070908070b120103030c060204090c09170a050309010f1812120906090e0c0702040f1a030111070303050709030b3c010b130509040b01090b091014 72
    0x54958144c035416020400c01c005105420400507001c0385d01c2902129240d9039144410316080c050045c0180102ca9039400401c040307031041044600c4c072401010300524165488110808075010520b03028082200070804100140b0740b03c41d02d00005e0000d1014100d101c1c1190b8810352a4800c04103d00d042c05441d046100b031f807a2099548102e04039070b4107920f441440d220f074a21005a8240380d42100c0541c5000001448144a40941000c80313005403610010603041c03e02c10182c160000306428440c0a05119040c0542c0e1a0702031801c0900791080001400410907010603201c8560301c0d41a4040e0303051142007600d40d0440000c50b032596415213800129034840a50031900b01a00b42c0c4094029076100c000e01420a2984140c03850300a007222550b060f440d005130804804488003210081580300f80c100400108040c80004c01e2455015401d01d1300c1a40c840c00024460b000a940948241400381d0041c040316216129a0041c00803c940004071890000c002c0801c191081c007a03c64050058000c900c1e15 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 926085386 1250 926084136 926084177
    0x12d03020d0b210129040507050d050a141509010b030c040e04050d180e150f0d030207180203090613051207120801050103112a2a10080106 61
    0x2442c2c0010602c040500c03040c20030500f200d40181a900c11940782c10713190f8a8090a200789044540311002031080c00c12a00310070000181801401c140621004200030301031103c4038400d82d40b090b007604000051042c407180480c203420000402c40c00240360200b8008215990f55240c850440d14151001c83c0ea070765850b0001101401550300c1200030000c80c00c00c0c00b0401c000031070340480d2a0166541c50352044c190b640041d070701082900c01e424029010801043c034110103000d0205140a010340f904801000c0d81e00403813907801c1450401c0d40185c01483c800d22071440c03024907103188042c0b001c60950460130700c0c1c00102d40f40c050180c45080380414900380e007020000140020441c02d40485819030b1203003807500b0034051313a05620091b00c0015540b0000422158040c0c13042000012483c1c0c015800c05200703d04540c50007a4044010401d40000e80d0b145580001c1081020030041e46240010581d00d440520b0200013031a04800328801c04400d85021041540108000d045940c0d40c1f03012500c4c10509008100b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 926086636 1250 926085386 926085401
    0xd1805130b12010c110c010c0b07030207031403070906081f12030309060617010b030d1d060f0a0f0909141605070c0803180a050f150c060108010b012d03020d 69
    0x1d03542410000004c2d56040100859404040c8043c0d844608280004580144a0750002003281407044d01240015102e40d000d03000884c032030b0500340c4c0180b00040c20080190000c8401800103006448184200d075800b008660304607100c80c09510305c034030184828031142041c50003a6104640d60501c01c40c241486074118600d0141c20a50421200d030f15118045200700080b28295210742c02c050008410341030000b010490b0000c2580e843d13644854403001d040140308105909540260144240c5e440e104005000708940340050704e401025456143c8081c1085210360b0003410f101d8a000d04503141955038503043e9a001d0501680030603c05111441540c0c01c0c010828050210395040c08081064400000101a20800105484d0300e03c8410707020804140c4031400307119000510032040d6a04d504020308000410064615454100810100502e2800c5030981c8a0103007a9111210b21803207582103201043c5925802146403446074401e0180542d8050400800c001c00d031f800100c012105003240d0001c0c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 926087886 1250 926086636 926086669
    0x7020907120501060e09010e06090624160b130b15130c0e03010510082a09090c150309031206041506030207060b0d02180901140403020d1805130b 64
    0x1100f543c440000600140418001a00501c640c2c000801c099400b4560244540e900a100304c800742e44e06810f00c081c90a032480403000780010030342d00c11044000c8001803c0d00d18400c4403943c502407601c0c00c2c048035840e0080c01031010550300a0190000c686000d40c1c4550041f05940d0800b51001c2000209214171159a2440601490507280d1322410342d2180b030412144200300c000b800141c44d445466007900740280b1070710032554801c048081024406034000d80c0080002040c0081181990703020802c11102143d01130210782280d184040c072442c040d202d070442d00a44e44150750442c40e0411045540b4840c131076141030012110f20002d640e9030b460fa00039246000740da80c01180099541c0d08007401940101c40201c40981c1070212a001e0b5003003040444030030640041c072108480d440d0742c091110b01500981490b460f55214850350b041c0003c8074502c2c9005511a900801c0004242000104030090341b104901004040701800c100a54907015803003011101c403000000c041c421000044e030303803221003203406 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 926089136 1250 926087886 926087891
    0x80406051512030a09170304090f0212091606080705031f150215090a020d020d1a10090f0509340f030201120510030b0c07020d060509100605060702090712 68
    0x10001039001c03000d05402c1000b501c4031003175903482c0c042161440240158008040e03005100401400c0095007001c6000450741000514142d45414003d4903840115040041544003010b00e0503002091400c61001740341528080c44981000c0034020302500c0090444161400b41d41c00345c0b0210210741d104880201a5200035050314038441c14042d440d0300d1156442c8040c10b5052001980548001c01c2c0c05000070381c0107111211641c1e1940c00c11a0300e40c0c1c3d02c9800c3e581195150041a5401001c210040c00740f844501150440d525041c0031b03a06a031180744249540d142000107005082c1030001d070000d00306094070301d101d0500c89034208504200c0e0702092411480d1a0781c410004000c1c1d0010346200c2503034002e07607032061a15568115102550025614041008640842000481c0d0300c1d0071130070f03000018000320307515080841c0c000882c01c050401c010380340389544000b48084150100320f03098455600c03140c24401c040c41c24000804901134900c0103800360900f000004e40113031007400089030a03070035041c08 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 926090386 1250 926089136 926089159
    0x207080d2d0c023c011e08070914060d0513050d08010515070b061203070206040e0106080c130e060d0b04030e010306050f0303030604022101080a15050603060a1a060a08040c0e04030804060515 84
    0x10320250703040da02341002c11001040401c0303448100f0044051007001411440c90305081701d1007200200b6009081ca0311500c400411075001510078000012a10103075595480c165042c10300b08114841004444034404000b0003a010004102c066842d0f40500308440400850303200c045224194410b1a60081d400314002074003081d001c580780301081c103843c8680d4902c0540e5894054401c4039114200340c40c0034180701c094082012408820a00390b2042010380010380b0300c101a580c0300c0c54210b05031000c5002c2014000500595681407194030010319080704d61a00f07240a48012984a1001611550203250001142900c00140c40305100a920040d056a1386542c0c1d50300c00ba580300d1003070103c222800310f8240407660425405015050103880300801920303564540124070030040818240201100c80081c03c02940350359000b0150441d070200c0e44405185160510307041d03800100b40d0b002038041000700c4092202181c0c0c01f5040c0e9a205034416800507054580c848204025500309403004d6014912902 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 926091636 1250 926090386 926090447
    0x6040b070b0702240411060309060f070219110d02060c0d11030702010806060703030f0615020f070f05010815130f0c0207080d2d0c023c01 61
    0x80900a0280540650988888030b08070380310341c404400c041c00b810320b074404d1003484104208070f60340061180c022016841203440100e802a0421502c40320550086006c10820082d1080c1890f8001420b101a108a04002d0403956407007290a00c003422001d090141c40d41d240d119441d0b5003010580040015440341c00009a039603a440d1201c00c0440080c0540c0c1480303214800000a58607003a9050711030401c566600c0052080c660005032066042503120b110210302d4540034410100508113002102c1320340319030320401a1510300c800c40003072003a0f03001c100100a0b0845e0404881c054170401d05c4c1034800c585400c01220b80400303004076000e41c0001c4402c00c4840542156201403000141d00c9000e200c0034008407000c0c0d0300d480d141c0c03150a80c2ca0f0882c11801c5082ca20640c2c80d4601489508040c4548002d9950045c0c940407100303421901056044011074150300d020140115880c0000080d01510120700d50140b403950100c0b62411517107000014003800f560701525041041e29000074102a90f80700440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 926092886 1250 926091636 926091659
    0x1f020f0408070e1006170703020309190c0f0b2502152101050402030402010e0f2b0c0b030114060f07050a0f02150c0604080901020715020d0305131a070e0604 69
    0x201d122042c03000124000501728012960544100306200d284d580c0b0b991400320a401946c4018024805030291010301c20a41000302d2118030345a001703000d1401003074105801c172a0a5085c54100c45640d0009005c80d16609008203000c1030806840814034181041c1407002c143c40c80c0b110f5032134490048000c13071109803140c50154440035400e07004010000d181d81c1d03201030100303c0c0310584010740055900d000c00070340c5042060400000c03407805420b880b002c0e09060280e615120780700e0320b65080e031462a10700b00c041c00a02c0f00d03a00080c10f0f41e102c880789554503060804209200440600b4018100481c2d012450700d5030074140d422040d0000199a21140d0910344990fa02d40c159000700c1c49808225a0600750701003540940c3c2e0045c4c4c0c14001002c044c0c40e0f507110815960400d40c2d040b811482030601c04200809900142c0c03841c82242d40040c51140e03081c0308050140c0700e0042c18440c100d0740303084e182404100d803c0b074450f90039108000c81c0c1c00581c0f00e414080348d24003c0741c2d4027160452000100040d800c0e1100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 926094136 1250 926092886 926092891
    0xc03080415080c04060e1504080d080103141c080402030709060905040501060e101202210d03051f0605031803041401020f0105071e11010510171f020f0408070e 70
    0x40e510740e0300c15034a904504055020754024200010540214000a420162030000741001c80001c0789023801d81d5100d0540c41d10040310540400039039a07000410401444070440308035656000c000d000300c000c42c01e80201c404118401031208125400e408102951024003c000203000900387c01e10400d5100c141c80c1018100c1580c00f1202c5600c0d051001442d096102c44041c06007696003500040c480c80d0416001642c0c01d90b4002b66070001d10120b8000c00070f0140700300c00e0391520340c2c08040d0103101c50000b000b07011030300c00808c0701c1c00c0202c0f45608240d640d1001007400c0c00340e03030150800c180c880d111012041c05e05850003404c00344601c0f0001e00414606000d12802e9101c02d001d900310780ca00360b203031b14000e42a21030544542000c51090b6526030990210858101500e4881d46004120306003a1080e090035600141c03407039003140003840d1041c004d00000200600c4049444002401e01c5902905114442c1070300d0b50130b0b4240c2790b90104006803624501c81c210f40090001b0001c6461068503180b840f80703c070360b05 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 926095386 1250 926094136 926094179
    0x13506010e0f09160b0c100911120d091a090405180d020c090402040e1015090f18020f04110c010c0e0a0f030201031e050906090c0105070b130c030804 66
    0x144000a40107280005091440400c2c0c4242a58413034500002c400c1a038000c4402d800850260040b0040100f5807441201074150081522820101c0f040c0305102c0544813480d0700d80c001d90001c07600001c256800100750801c4941d50112017482200104240d40e4a004091310550b005007410140300c018000380da41800701d14055030aa42e01c581c480001070b40c0e14010041000d4001404000040c09464540c0c400720b2060303000400d6446803c030b031800c11400c4031007200d422081d105803000203000340d150512410001c010300c103500304481d030801c1142c007510146c244c000900c240704603a0b90b840c0503183ea40000c41e808100891041d1191004100c05000e000510104000545d081805e83d100f403500c48505012180c41104d04850341e42950011006041102d000c40b00c40c0030840c0306068106064881d082c454094a401b8102030305040c002142490048140e03241005010b100400105120800c0c1c0c0380c21942025000700b03802c4a03031904181c911415070000c0e1000b4000f1400007900790780c042c0d022078034000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 926096636 1250 926095386 926095411
    0xb0a0206150402041d27030a14070f2310050a050708160c05070e09030a090801051504050406112808130605060a030c0b1809013506010e 60
    0x20740c1030900c8100e001e640b00d880000c100c2c8a10781c2d0b03111500d450501790010100d00b0110703500d50146400700c80d100340c03c0c141003001c1e60001400110041d8031210700402d2210072088245000081d031168920300d041c0d04005021000e0607007107407620514070382602c5002c61541060303c14240c402d01d004801014126040c0000504000004060fa8460001d842c81145450424030f200d98030050101e554603814070088501c1d00c5144804110b050041017030501c5107441074000c5139900c10640000b4000300f003a03070024100368189001c0c000740e0706090400e01e42122055500180c5562142041009441031800743c078400c01c2c0001c0e40c8008600014800c80c8a15251940c5001e1401100d0045502180848d6100300c20a010306041e000214640c0005404ca10b000f0321084801d038607a05d81f010903600c03c0e40010b0420342c0009000200009000011140394401c642c490035a6150204031501d04146424108071015403040c0505000d41f22108101080358940498425686503511144400d000f920030784030420 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 926097886 1250 926096636 926096671
    0x709030231090201020a1e0c0312260604020a1e03050609011a0706050a1e0510060801121119080106061b0221100e1005071d0f0a0b0a0206 61
    0x18075030040140d8294103a00900040d0f0380f0b80c071030b60075118801c461050340d05075507211100031071040021030001d1400303101320055242504e00084c2110705d04405d89907140586c510f4004401032841a05640701e20140c41c00340e03489001e04000c9a0b20090564502c0d4081d45d80654642140c0e0704d54040742c458030b010344100c00c0d5640c1303070000ca03003414003496003682c1120410020030000691903040950017441143d408108000781d924200e810302c8031081c0b844e0b4134590f42d00c00c000e03c645a14208000510309802e184c0070303650402c00c1144107142d48880140207501e0100c0c1240507904d459803400184000000098509500c138507940d40600702038895103000808085d00c80f0480440004c001e075030590700408c5450000d400113507058203214241c07807580035030081074101c0d00b246249004007440140d0307240c0a0503400032040042400c5500140201c3c003002482e6040345103034242d416031307c0c030354041c00c4512442d13080d19440002c2d00380e042d135041000c0d0a072001c0781000c41c00f0f1b000100280214443c500120060703 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 926099136 1250 926097886 926097979
    0xc0a060c0810060507111206071e02060619050a0306060812210402150c010608060708070906030b0301020714030901090915032307080d0e0618040507090302 69
    0x201c0e01035070701c40d680080440040000c140901d0090000c3e5100740d02010012000e07900003a01d0b400c15034504007064000408102c1c1c0103900c44031200200c406200c1e000f4210104402c0250b0b0361300d00409490240c902c60008205810a07501c1100082c0070080950380030a0f22482c0c044003400d0380d849442034510800c240d80014107460800ea0740d02035160606100c158082a44900450002400581c1c0204085502c0514211000014590300e03c0c1c07800003141080c40c0400652400c44002c0c042c50070040050180300040d680904480c0481e506407401065207030540e40002d009101e10342c401028060140900c50002d10080080c000d1820709032200078242d0b80d203182c2030040e00e514113036074a10002c041c0d0090002880403009494080850b82d1606c04566460140528158007600400903980c4802c80071a410b603440100c4002c50305099030f5050912808a10740386100c46c098515920903611074001400051003081c88200075900144419504040b00d86041000c07481c01261014115001d000d56252 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 926100386 1250 926099136 926099147
    0x1703070b0c0901052703010c0e0f060c03030c0c0114040c060206100b190509130605090a09080304110d060c18061701050904020d05010207051509191104060b0c0a060c 73
    0x200d011384030686845131800100003010500080304078200101c81e40401c16441c01d21a0301288402a01c9000081c01444100200510f50584285c459082000748460410001c410303250400f88030401c003611183c403003841c503003d851180101190314032010100b07c00d01101654000845047c0d4082e03070f06c0d548651605c14842000fa005402403e142007010540840c0180d1000c0c1c1804181c4ca0300324140380d0f801d4005001c140798031000320011903e50074144a0791810f00500354110240e1081080019215540c0c0c1000303000003032000e891042030360403215068584c40d1807445a01c0c2e01a104204400b010000544909000ca684200008104101007085405180c1400780044079884580c0f5985c6400208110000d00400032608902c87e501802c2c0007507403d001901c00148154040c22009105901d0b085000500030203140c00356000900001b030303004120b9a9984480c5e040960407281f508042e02180141a50703074800f074601c0d1000591200c02c18004074491801e148079482c20310800314110001c0311b4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 926101636 1250 926100386 926100397
    0x625060e030706060e040c0317040503070906080c06030f0f0a110703020609120c0a060f090807050a020f04110306010309031803030206150603010608011404110315150f040b070c1703070b0c 83
    0x381047c070301040c004511003c84001c0e1218000400500d003039212030219083c24440d5201048050703c40740280140c3c10203100c122030446003a030325030341107240c0588003820700d0b0f50240050404a00000c0030a00e01042900a50038242824400699032101c44c0380c02942e0b45002c844407c442d000d401040814417040c1c20441cac907010300c0d0038001c001d458041c1d00c81d4001007640400c40c1e64616500d005d02800181c15a0190000d203020700050031002070180184104140150680741c811858800040340d480c403d5019079400c10004c0c0380008103903c0502d0b05552020036400f85520704c200c1008004105503000840d148101d42113400020342da0307413000600505010a010b2100810600340041c841088403e0040d0307941c3c80c0040c0086880f404150201000da403081d1403000e00c1ca0410523030300c061070401d058030210200820001700c4c03a10b189982ea80c3c019003ea401150b900034000076800003884852141000503020001c04101801c0a02040665079408044103c071043d074a400010341a0180e201941e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 926102886 1250 926101636 926101643
    0x30b010e09132d1506120312060506280c02091918050304150203070803150405060a0f2d0815090a021f02010f050c0c120301050625060e030706060e04 66
    0x7401c034103265850040b054840c0d600e524025549180026140100c200f600f4030a0f8081d0302d0f28841c80207000c00071000d80c0c44070340ac00382c0282400c01111100d0b0011107410001e2010581c1740e08142d41c0e91401c00c840340030a030b00001e0360106100c81804440d503240e0f078419004840c0e040782002900b040402000341c504203403002070519003050000300259200c0c240201806c910510541e0316280560340c81d40ca61742c01c00d540610720000c10401f180e82908240c815035800a10461b02c2070b12a51403d50218844200780c01543c2c0740416064484031002d1411a050031142c42d01d80709580380c2a103400f85a0b5035601100c013009200100380700860308040d4003150440c0c031580c004c0c0060b2404220b0b000150b18002e81d00c0c43d90b81c215940c0ba103c00c0303648500c40c032460307005290254115540c0c240758903031503282080140c8240d00740030080004100f00d50b620412030f607248582813000c80600343d0780c000e03240d600c0c04080009044207050901d010080c2401100904000c1d03c942801c1014a84824141080c00f1742250001c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 926104136 1250 926102886 926102963
    0x140c07020d0507080619050603032b091a040203070e0c12130b0727060e100509031603021f0e2119051e0607030b010e0913 54
    0x10000340c1051051a20958019000c40f110180e481450328540303c81120f17440d40e40c00c8400c9007007075a4031b401d00409800c481d0440040d42441200f00c5c1005c450b0bd415440100e00142d00c040c2d00782d611181e0f401c66070120740c10089658420000c1c001010590030101c804038828003490310045424042c0680540c080d045101c941d505000f031a1004448044000c1c0c410040075640040610000e00400c0c0101d01c41c1d41c4641d1003005116000c014078a203041c252201240c003481c004402c1c00000e40c81100a20303910f4007140c021083e490b590703006490b03c1c400c034080ca9405000d40b11084c0720b00409403a130075080341d1007550480c400801c1d41a40300b40040c6c0000c03a44000800260a141e000e2500403103146d0b051502070b5401d00d0703403000c00c4222850034035584400e250300d03c8402822004e008090202400c0814902d11901d031003240e01c4220340e02c0da10001c213864181595a503144006911504001081030350107070842140d400e081d4800c0074020389a902c100c4944c403008044a01880c8410070b8800b40c00700004a4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 926105386 1250 926104136 926104147
    0x230714120706050718030f05011b020a2a24020d080a0b0f1003091b0e0c03070c0501050703060312030c0203160501110301031103103803010c020709140c 67
    0x3100b014101c0a80a01e007000408500380502071034040302400118801c00300700402c101d052601500f036031143c1d901fa20141c01c074540ca056115030042a8004403030760280740003c21415a09019400480c0345004d0100c05e146120041102c56411910052080342031102031100d0345410b40482e6500010015040010034110200320103541c1d82c0c0200c2c802c07103030007401d90880780481000303d000d090107198007000017500d030101c45040c04081d42d00c00d19859441c44203c0c60305401c001c0151504d1501400c500c2c0035032400800100054481c0340700c070702d145a00c0300090019060034040240034003502d02050398100d21452401d072034103010344213a8001c010300d6000743d410451309616a51610101ca44c080e6169500c4082500b100c1c40700f80c00860103148a00001c50580400c001071500d080600550406131524240aaa0416088124140381036101d802e24031100d141310420705240c0364290525030b8040d824400d01d02e100c42d40104541d015110740000c208450301341d03044020b54404c170076103101d000354004021 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 926106636 1250 926105386 926105393
    0x21207090e1e18011b0f0c0209010b070f05030412031e021b040207080c011401172104030f0317092a010203040e040804030219061b02012307141207 65
    0x294030f0b41c80000003500c0302e14201603840c0c5600751198120700102a0740c60303206800c2401d42003140d0243c04541c42c41d108030180615130201d500c1101c103000b104010000462040b040080400d007076039079554400c2c1600d8481c0d58540280d40c1072504514200c0219a40030608288858580d0b0b05ca5249804c81d4018914401103000e458441c5008000c50f40c1c00540801106011a503000010207100f43e031440002a00590026002000c0b07106070031003100050f00e400f41e079890103000a218101c80c030b5400c43e85e0035203441618000c1c4043c803803640000c205102c040681401c1c10340103001c0d4985114001410b0520344d4506542c903880d2203242e01342e05615000300a0013281101030a003807001060b810b0040342e203050b48401810913012411a011114603038009001d000718100138041d003009118011103000350508120000d0005c000300c0791b440c0c400c43c406d00000c1040d68400e202e100207013408401171003020082d4403001d1076194400581512103901541d01140725000000750400c40440c5005241d061170150740c2e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 926107886 1250 926106636 926106691
    0x510050306090a1509150806090c150a0e0a06020a060e030406091206060b0408070f0503032a0715020a140d0503040f030504180c0f0212040512030d021207090e 70
    0x40012a804130482002c0b910702014850029180801c003103900c021480d04021a00e0a0070040030318100d50000084034106442e240ca03422140031022810b5600c40c045924203c0340c001c0f580f50000d620424140c0000b80701500492103403800d41c001c404c1880a08400342803680d6a11851189000140c820303541085007540400c61204500c2c40342c03001161890b51020104001e400a800402141d000800e0402103500001780c110003d12041e0080e6080c80301d480121417020b42f048000205030841e0345004989283c06104040c0038140c08001c402140220300c60003035403526000411500c064800580820b02080001c0d4000c00c280c41d96251844c564032079031020500440c0f45411400d0110074840402c1c040c5442311401241050300500103200c0e84038403c014507041c00c0c5100c240c2075402915003104009000000c50702074403c1036480003030311030b000380e5414030307501c02d06c4004181107200dc141984003610501081707010700050341e103900c0c00f29240d81c08078150076001d60300d9407241c4031030355039103049185a00b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 926109136 1250 926107886 926107901
    0x1409120702030102090a0801061806030804050103050406020d09080901030f0203041e154203060e03090a030f061b050307030518062511191106070c0510050306090a 72
    0x20340050b0803e00200302003501b240c01a0486e00c05079442c1c4c501400950f04285070f08840030800d180900c210307407070b5889401a07840f0b1400760a04064035603000a00340f08180c1c0444001c440008400c00299400d42400d01c0140c10448400d800281044441d24500810740283c900981d008030108250700f810800e416200010240c1c00c41c0c03041912801104d90b14001d120ba6141c01c0020307842c80070301c0340c0090749006000e201c021000d01d210040809a071208446016500152036004200081010790417503154034500599031441d6010400410120800c00c001c4140c04185101c0c40050040007070f074000080c044815a80c502001650610000e507410f486600003540041103006030000b8401e40361107960400504035121041018074400c010410340341424810040ea08500c0c014a0b03103484030040603210300d814160f02580645007031080051101e132030121910880028241075481000745080030300c3d405c0300d219440c4240409664041500e00903012280b08900041803485240d4131180201e004000300c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 926110386 1250 926109136 926109139
    0x5010e121903170f010905060402031311060c030c03041d16050d0219031e0c05073f020708060411040c090513091709060a051e0f0d1409120702 63
    0x524120740d0b03e9021001c41c07280103211150700500658181600d14054400c040d0442e4051841081008402e1130006580510345510019015042d1203480004015000f0410016650b002c006020469072034008010401c9030395006d44090003480b440400d550b00700b000ca0f0004410780301441c61342c0740b4a00c20700040808541d032940050421041810300240c00d1a03a50984000c00d07943d03a030007041085040c240340d0020258070018820406544001081406021401800d2900e44035100c80c100020b00c0900c040f0503440006800710424444100ca18403084500c108054003607000d01245024010403003034419a005490b00507407120a0060100170020541d04504003d004000070a6607900c10b50030301c002c25019040420491a0f50610015800c0d80e6105142c501d42c1c05c103c804500c1d146c150545800c40020700700b580d21240245400b03141100750400c0000c02c13603800210425000d400d2400b42c101c0b05143c40b030810401002400c2883d070320105664442e4658444103406440003484001002c40510 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 926111636 1250 926110386 926110397
    0x20a0201020c031b10050d0218041808040b091206040b1e01050607080d0b030a0b1801060e040803040c030b0a2307140c0106090e1c050a0f0c021c06050105010e121903 73
    0xa0040001249c02943c00460666071204410441d440d180c040c0804a41241541c2d4851070f080c1e40c2e0720ba40d2480b4074801c488020a010504903a142e8030308900380c01084403801a00c107949080c1c50441801042181c0d850303110360f0070800440200084506442c180c81c0c014060b21316180305d5844020641e0072081e2882d038010748032480010301d51014440310483c01c1c41106c42860908125030204000c035941c156507541d503890700c00f00b009180c4038a07000e2500640c0142d840d594075212810f050f404640903403c09803080610b501440b03408809a8484d0000345003940d100c940702810340d2540803002400351480c20014100b01d0303826011110741402032150440400001511301d0382c0d0003040307080d04c00403000812150051580c2c2102d260709092825807070f0040b4a0070314a841a075400180c1185c1901c540d403000c125000444c901152114040d15001c0d030640203624522007090f00c0d00d00c1c0581801d0249900107540294001200d040c01610580c5910001000d8229800c007440324500f03451403050705608010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 926112886 1250 926111636 926111647
    0x61a031c271d040314070c0306020f0c06040503120114090a1d010903020c030d050a050d0b0d0605040605162102181906030b011d0f03010905030406020a0201020c031b1005 75
    0x81c42850a00c00c0110720b000500b150b85400d05010b00207060900144004070401c000e00b600241d502c900d04002d40358050300043e224600c20006002600844c038805040b0b128002c1884140080040600005091070030340c0e41540e0b8036840800f01c3c003246e50081940190400c0c0110304511000d41001c00200d41d203911241aa0041304100c5094449003c42500903801140201d01c10741824001c100d15080d841c1003141c07074251322900050151141c2517481e8500c56a4400542d02076590081050209030001014030450034a070600c80c005020503140080c046071040160081e10b405010312460303420700500c0780342c8440c051900394806540f1003107410644003c0384c8a2001140d84d515540c090898004600d00c030010304100014003220b850415443c103000c240c64000c0c00c50b4080300070001000100b52100d00050044002103805000030038001412400081008141c6580c001400c2040c02d00076421640b4210482301030580b01c03020214600e42d01d82000420b1895402d20044000182440c4d18183d032412 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 926114136 1250 926112886 926112899
    0x91a060f0d151409010801020306091602030405040507030e1605011b1e050105100b0910050901050d0f0b0109050f3003030a0507030c0f0801060318061a031c27 70
    0xb085190071042000780ba070440c200d4141000320240c0d000d070001800031072850a15030001080010010600c940100b07288180e51110742c820b1041e0360041070054004d11441c06c00402c041c014020b140c28000481c454008001006c0221818900440703070181c40e030031040b030701c0601030711159210b0903400d40d10694109000049100308421070941103024600000f41810511405002909c155118aa5401c41030000007150303600c0010a001a4030b0605020b0358030040340b001a107890003500e40312810ba5290071b450b0702012003a5007000c0e200d41c0090303a48145070342e26202000142d41d07205111980111800131603038041111002d10343c00c143d070205410b00c910b00c0742d419003501c0d692085601200e041e8450040c040215010300883c4454206401c1444003040b004100815034481480380c48101500c0b40d42400e078580c00700500111494221005000030951416007680c2c20f02d0502d21103000b403040c41e18009125460003003822802c0c060b5039940440040b00216000503440b0842d26841d545840310b0000703101c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 926115386 1250 926114136 926114171
    0x210a020f070605060a0608010305121b0303070e040b0105040608010e0709050607031115040f0b0601090b040b210c030c03070e0409060e07091e0f02040905010f091a060f0d 75
    0xe502ca00703004030b8145001018481001c016520401c180180f09005100144010038160110340c00c80210700c2c1c59808080f10f40c00529070048141d000d40c00b000044c0101160710081d070740f5214100f036a00b446440b9841c0c00450f6144124440c50f0b001030310b00c10040c0704404d03100400c00d400000340d06d0880090b94031400010302561052030b00b1004900400c155081c038a00a0001007082082070310ba155091815444200030b9180c14480240070081800018100303030700804180000c0c1206412640d219604c0b03d1500b00540c1c41201c0101d042c4440b1200c484850300c03022120740c404c2620707142a40c255201c02d80d00c0d42c04e54001034600000d20046454200c86070316240f20b04912680541e0011400d40601861541004083d4000500396810051203548035149480d16003030101400700c00284018a500c01e40b0024010b580080002a0501c800015400007e115080544414000412a1004c81c901f8003850741c50240100350410b501344108001c240e00c140160054003100100880c5102c8080008040b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 926116636 1250 926115386 926115397
    0x22d010b0303120f010e0114040207061d07081c0c030c062a120b210304050a0306021207020712062a05030a0b010206091b06120f041502210a020f 64
    0x40544481000003400740221310305e00404055090724804e504001c0070551800e070001e00c45c0d0189400103102010080c90781e100c4010410085024110000a14580c036210600b500c10170240307110340c171400080000d42219074403034111141c540b41e100351115601907070200708101058401a0361200d4202070b03a07620748405184101c01d50a440d03803c842030500901501100c94205004030300e461003000302c3e625062512048074079000801e220064022080300e1031480307141c0000b03801044800300001048900d4025109001070302100002d9640c0f41c3c1c4049a81d102c46100e000c6030404101d000101180c25030b4080140c0032034a410300503000c00c40729200d030407140c80346c20f1260005e8000010003e04142900c01c0402d5000248003911040c107008064603078440c1240d1100840c07128110040c00241d88140c05c07500f01a01c455500c040ba0315102d40c21607040b0200301e90945014580902550030b03d15503100301c0300b4041d01180a0031a840c030800101c503120713200030043d48200340e08022100520131504050074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 926117886 1250 926116636 926116657
    0xc091e1306050705030f0a020c071215141b0a121803020c042d0209031605090c0c0303191d01020405041d0709020c0a30022d010b0303 59
    0x10008007841c15000b1110700400d4a01004028014000d68030100680c140d0481d21071440036032100e9819881030704000c01a4400000c2030f4890700184200300344540500e40d041050300e4100a001144a01d01c007010104640400750313150f4030fa41c600761180000700602181d95861403c4501c25140821850880704840441100e01c11003400e00000c05504004c8030400d210252001e20902030754540303548444400b4260010303105182c2c1801002402a0b50544550f00d4008085070350380c24159000700c3c2e111100780200e901a1035114005168001040b0855981ca000e2100642c51550f0384010040001000c05e42100311680f601c004c0a0114000b500d00e0404082038000140c0d160701d06000c200403540d08484400381c003407910342800f1142c0c9010419104444161201680d03d0382280c01e51800d0a21141c401031014030089645101c2c5418080c01582c02c6030340c0103c11004100026081e81d40b41580b003071103052a004400742e44801c2e0076003070321020078248420000c101d140110300040d045820514200307 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 926119136 1250 926117886 926117911
    0x10c0b0a06050d03020f0d020318060309211809040c03020d0f0605010b3f0403090509072a0507060c17040e0402100e010c0b0606070c0b03150405090c091e 68
    0x1602c00e00ca050047e1080f030a400d000035850544100c0b000c600a00400c03000d10711441000c00003d1740a9414040c50056080d4070b00d0301000b15a0034060802c4a8120040001507090200800b0a89040091040340550341140703a684040d0328581c00c002c1d0581c5214812140d80081e91441301c006503082c060381d0701908102d05155203c40c3c2c3d00e20701c0c82500040c0c01300901d04030071412a0007006100444000411810303840245855603a50030151000051540415002503104042040341035000e8041d42004004000e050302e85541c1c440041000a035154025100303030841c2e4001c01149010b901000ca810348035100d00803030031250014141441e0055800401c00c1001c071000c010452901f02412522000e040c01c06003c62407898000a00e0a00c4946005004201c203e010510a580b00d4041c0e07085035500100a40f0441c0e11054085260b0700162403810454550700f4035103066103094042c02d44201410740040c006c00b541c00d0100595804040e00301c046501501d410b000000040c141c0340ca100c0e401d2000c2c87c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 926120386 1250 926119136 926119153
    0x3030f070c0e07050403060203331c0f060b1207120204060905090706050c010e0f070503060705190f170907050108220b040c1505120f070509010e01050c1524010c0b0a06050d0302 78
    0x148040c4c24412401c10704003c40c10714515000800c0d8200cc0b1a02c0d582100340014400913030030110b41d2800e8240c2101c1c0480c41030541c0040c0074020000e42a1080c0d01c262010f1150982d9406040d09440701036526280ca50404642407040511840c045c0ca86030544d880003240085000c2c40d1281000d00c170321102c0107541c203c4002401036003410046a03410003120702d485840d00d40c40703264001046544400900400c0903030103c1c844000c1c41180c0c03030f11200e2201154045039013042d40d1810b90b120414403607280441c525900040d20030b4103a008030412010314020381d240e58a4140d80e0395192450060045644201c1c090011548410301c0307840e28401a484e45a003550307011000310703a51400c5c8006213240e400074440020040c0c002d6004041d034200ba102820004850404400161228007482401c06050311a10582503410401d8004080c05051820508800302d4201491209094040a501c602242000b1064800240c0042286500828848002865644a2001a110b611803000c00c0d401603000141 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 926121636 1250 926120386 926120389
    0x70b04170c03090f0f060a0f09050909030a031b0c0219080f0607270b0a021e0d140c0607080a092102010e0c150d0b03030f070c0e0705040306020333 65
    0xc91302d030000003120028010404800080d040f4814292681c0404c03a51505029400380200b6800000c0d0000521490007403400220142c0d481d00080700c0c00303001900349001c0d040c01d8040506920000c030b0031903a40c0210740c070158091012400040b071041070200c0d012040050410414030035100303901c0d10a03001c0c0605042907480100103083c1400d826000062500c00041441000c0d00d0030000c503003218050503100e405110302130f418a0b60800e00c3e000504004061502c80d800089021589d40320300780c4944200420348488210240914503180c44d059000c2c1001c5204076000d40002948070405242c0840c20f45030598603400110703070b0f1400194031031000b030f055000701c250280100e15482404c1001001040c2086c000654003e2030035111090003103000910400d89129030b005811029405011203940b07002280e543c446641c00510309451344c0962803404164035900182c0030b8010030f80d90f6155401d00381580c54440007540054030814814a4400c94035407444100050940c0b40895440c0c0c44030000307070140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 926122886 1250 926121636 926121649
    0x109080406022104090b0301090230010204080706080615070506040b06120a03201203270303011e0306090c0f06050a0c08090a08030d0f060509010605070b04170c0309 73
    0x803c903507103d40c20041c3c0580081c40c0c0740584040307031850100030400c404000003082c01403045101c082e402c2400320100f800c10000803806120305040d07d6540c80b00d210902241d03035080303011700c1c0203181090300f0005080050a103d80c40c0d02d50020b90040a80c48501503248494400d07920002d0200c8040e00440100010b01111032a01c0c4e900c4071059070a2188101104281c039180c0080d00001000c0c820782d41e04848180c1c0d1fa00c684841016084801c0700c944c0412285c03406081e400071901d0380e0281000f11a40fa221124040c0b0b01400c1c3d2030a40c005500356400c01016100e04c15a41d000d900d046441c0302c00c00030100b2014018030030214010500c0d60720041c2000700244904620b40c000806208041008500306540081c000f00c6c05904854483c2c2c440c000c40340081e900d4031542c1d0110600744000700d012030140503d42d00c20b034142203551101300001e607955001d000400800344241404100c0902410002c101c0d12803d07198013038401e00801a01103c4800e0062107070b04100391641065002240c00895420544c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 926124136 1250 926122886 926122903
    0x130603050604140f0408040f0e010e071701150203070c0e07030e190f020a05040c0216050a0f05101808010204090b090103020a1a071509110d0c09020a020f010908040602 74
    0x2a41c0074041100700f0304a8a0f1040c90280030b8000902c5660001740071310044c41c0640e00a41f6240040b05041c603544d884d84004003c080c0205241a82e800340410360043c0111409100c04100802c84403561f80f03007524a0b91541c00480704003040d03000811843d4001000c10002a010b401900c402490908000034001c08841c11102d040f07003503a000031042c000c5150042d039800001940045c1c900780e80300e12480490340c2d01240b584031682140c1400c409080d05034011406d00a1602074179140c4070740c00c0d81d030401c0040401d40c40c401e02c180070b000030138244003e0a1030301010700011340505000082042c2c01c00d040140001c603a111070810b075030218060084844074020110b00000840703200c0840e50641d00020088c03555445120112010701c2803001203810034000380c50f0440c2d00004980c1d000c8403501d40104c090444908c08550701c584c81e07010a862031038000f211031239640d04024002260703814402c0c1320000b54400352882c010340c80b40d242c0c81089220709015003415184540d0907540c840340b074202c01a01e850364a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 926125386 1250 926124136 926124139
    0x4061a01030504151104080307111e06161b030c08010c02030405063c071e1110020a080f1803120711040f09050f1e06060909121306030506 61
    0x301000d203c0410000001d12105219020000030040e035942c40400c0381c0d204030780c800c000c0750101199580521004000340c401d5128151610307480c114408100c2c20303891041846084d4041e60a00010842c84210031944030086d00c1100d000d690303402800305444140c1d050307603c111140302030b40006101c5010300f80540304900b4600d000842c10303d4106800110300c0c0c000c8031680250380e5182102059099038285020288a10050391002c81c5030008043c2c0096900c040ba06403014808049181d201035400c010055010b0341221921095000c03000411442e03a003001c03085011882200c04402c01b0880c8a4002c21011003540c1e94550340e624000048002c030007120110b00c1c030035007008082c0c140b100c408a048a0005030301c0043c005501030341c080010300405038040003181c05841c0c01c03280e4041140008000080321514006c49090004040215004040100884007150030040100300942800259590803046031801e507102c07000040f004c8032564104612002101648080400245406100341a0032020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 926126636 1250 926125386 926125391
    0x9020f01032a020a0b0702100b010c0206070b190c1e0201110409050c0d0606021506091e04170f0d1112072102041509140f010f03110304061a0103 64
    0xa14450100020b194624030b905518004044000602c20f000c50440c0030b0f0700c618205a03070305102100035540c90b11a50340e00003951418901084640c050405041095030052049290101d07076510180520000b606030041c0c0e2014800c03851030031103103005141c1018402e07038840e203042e0143d80c206440f074901a03c50a055925000c60b210051840a0450701512000d0401140701d032500c1c003140c15140b00d49502d2011070740c42c01401083c8903902040c1c44c000d00c115008410640c2d2034940400c0b5403040c09603800700342d00080c0e2010b21140c00d000d60b082caa010340668050100003025809154003648550a10800b02c00b000406260845041c4110707140080c4650354030b03003000d100c440328120115000c1c1014081c41540390458031410078600e0044900d04410300c4c25034503140d40b545c070b0801c0b2440318000c40003c035030603a5020507110080e8400d03179078100e002010000a440c81400645020712456644002c064403281100035a5070350000a6000e980b03d6000000d881a2051101d080d40e00c00c00305a604050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 926127886 1250 926126636 926126651
    0x5060d020a06140c010c09031406190b03010b060301300b18010b0a06110d020c0307091104090e0705120c010903030341010b19030209040b1309020f0103 67
    0x86402003041c080e600c040c2880450000e40c036110400500034940c846800c1c0d82048001c82a1540c082c03c1c080c1100c0c81000d0085081c159000425201c2c24101e60f1080f581c080b01c1c41c100906050b980040c00c2d001400b4000050344514640407500544c000d8210703014848983c07403a0b81040c01900c0700311100e40201510b00881c00c01341d50340e141e000c00700a4102650100b139450340300160b200a60180c01c00c00801000040015a5900302402059140380140c00c5030241e183e003880036074000308024802c000028041c224850a1034072040040c0100002880c03010300a110204010100e0721030785101c03d0386030b0010501030b0300d072004220103070038504e008050582042285032160f176003003504607040d01d6141c00c010416070018041407000c60340c0b0f4403441e40711801c081c0c0c0072090f06081550000904d2050241240c407a070b01e405000d660b512586c0404080400f44802e82d4005511aa0160004640040011404850b01c00010f8883d4081c05401e0003983d5554114104520746071b40804030300842800c0900000c1d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 926129136 1250 926127886 926127889
    0x1090b1504031707020f060d05040510200d06050d0609020406121109070e10050304020316032a03080d2306030a060e0a0210170906040b07030e01090b160305060d02 72
    0x300700d00f40001100e02c070108842003190395081106041c080054246502c680f00c0002c100003400c0240c034281c480c0e000342201c807508100c040c06011182400c0913202c0108038049c55004950b035010300c0d48000016500c0303e001c1071a80e5103007488196540140008220b20380540100022101a64001a0340401e0745502e00c1c00281c00380200e48040c001201e012465540310a41650080b010650341c50b4860000e00f88054900e41200146014500075421140887c04505134403001ca00076020203071060200783c402420500c019503448904441500620b1401a41d0b50303150b104941044004c0900140c440040404c120075000720110290040413245643c3e0070503c002c07944170061404050140c1d0344880000f1a2690100402030800d0f5024049142090f24820000e12212280e0b40489016030b0302c1c00840c10150000404500482c1c1008813130480703884610041c0c000b0142002020110f548414900020425404045218a150103001912100d4421000301240c0000b8030080c4580701815110016 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 926130386 1250 926129136 926129153
    0x70e060d0305070c03060c120f020414060703180f08300d11040b0703120209180711060906070e1806040903090f120213090f020f060c0601090b150403 66
    0x5641d05030908030341e507001909080c140280c02c4d070030240c03031941003840b19110950f11010300350030480c1c0e04c1c400f0002d22440380300e03c009034410f5100f100b5001c662002e000141e031070120b0041507150710034201144c40322505030300318030280d00542c0083e0000ba000c20081202c050140821030001c640740c0110f10010076a0310308001144543d003018041404040307040c02d03003d0110717840f80e0140b2103040302d491b0b283d65690f01c110710190b12042d81140020b0f003181254150310241d0081e01c00c4414002c0180840780c915001208541c0802000c410401c070000703d80300c2d00300030141705250003844c1c00000740c60300345440d40019202c8440c0d210158007408130480c4140c41100703030b510029006207086401107601d5449050840710803c00b07400480c1d071001e66000000d8103102100700c64034007d1094900042107564640e00c54101c0c1d0410002a10940c000c42c04480180340154210198200040a5038103100900c0c819a1401800340c205000a03550b40e03680c0041d0303103052910b800300050b130401818686410360765070008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 926131636 1250 926130386 926130409
    0x2010b0d0308150603130606050a0e01031502070f030210060602030903030417030f04080109060b150909090102130608010f0f03031205040203150408030a1109010c030c02030f06040c0305070e06 85
    0x3044031002c0070400118003c103d140301c0200050082d030303c2e0304101901003000c19040004030340051070324000085a041c88034221048030504040755070503a1031501d032013200b160120100784c1e02a40c20010000020020b003600d030400d0340282d0040003010180d1400ca8129081a00320702c0640d401441000791a503000001c40701500d100200190504514040142c507501030358010040308400442c000c1015501541321a0645020741e40030300c0402c60000c01d101e5012840c00b84450003000070006030a4a041031101d064120b944900014581410f005498492060075000300e0001800200104000c1541c01500c90290114240104040f80b460b503001d810714004083c0300d0b061035185c0d40001c040d0b50301030182c5610303d030003440040c025260600e0704001755403048444a10341071410060460305003801056945146045e1140103401000d9102940c039400300d000708030f134144074034050340100d19424042140680c0c4119544800c40e402c40ca003a60900c0340981004110102d840b081003c5279880301c07040304 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 926132886 1250 926131636 926131643
    0x4061d150105091e0301140103080c01050c0a0c0f0f02151206100207030f082b202502030106031212020307020c01121409030a140408121b070801021902010b0d 70
    0xc41201c0c1c004d0101e4054016100c5c00400402004000800e10403404006c180c49800c00f002000351355180018050107018071420b65000440c01000200064049298984c07454010b000c6648080c40b03550005010440b00390000c4120900450038140c0d0006c0e101c4405d40100c811a0b4a500b400407402c0001e640c0d200da4803015040020065442d0f05104243c4120b607030707508192008000382e00303c01c916250040d40180d103c0c1421494003581d8841a11040d151b241c0036109246400c1c98002006a80c081054048405030781c1d1004040d039080069400b40304020096120301c0c007081e62600c4919014105a0281c00c5c416296401001000b0025034045000c5113800024288022030f1500000d00400420000c03007682005815103040c09100b0800001808100c1c082d0394850407003048000401d1600d014900c2100c03402d500545608101001c0500034000b100c05041411010100081101340b070000345501428181c1d40c009203802e003008894400c0104514030340001d00002100b0804200480307441c58025 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 926134136 1250 926132886 926132929
    0x30605030a11220908040501090b071208071b0b0603061e010e130516030b09012903010b060a0c0b010b12063003040807080c06160204061d15010509 65
    0x3040410f0b10405a8220a81010b40400070780742c103403a1152455206001710340c0800d9518100040a203003d0088802060b0b03c0003000c6000b8520b5041a03401c0d07000540148180100a030305c5000c1c0b44180d104940d4040d014107519529400d02c0c400341800d00ca8080c100c01004803110550000e43c0d40309221480c119089903120070515034448290b240e40400d0064000c02500419180b1525414030a907017130f041c2e81c012881d038034003515019101822201c48000f032601462280d440d0034010208010f00d90b21100c80900045070800c10b00c400902d05520860703140c40403400c10500c4409000080500034003500440f4a4685800c4400b0541c0032004001001184602e1103d2000b0250003190b0140780785860503038a1868119001c04503040e1039800c0f500504151340704003a80000e464500245910083c2c0c0c0c0508020b15204100f00300782d4000c18419005e90304103403100340c0051a0240c6480c1400d54a016000320296400d00180d88803440b640c046007141004414001000301e0340d125a60203e841c003203040e10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 926135386 1250 926134136 926134159
    0xe0a1206141b0a30020c01050609090c04111b070e0601031512060603020405010b0a0201050603071d0c2a010b01030e07290a0302070507060804030c080a020f0d0f030605030a11 77
    0x80100440c8455244038003078821404c80c0042091640280404820300c1d03000740314a0740e0307540500600201c00c40c3c0a0b40d49510620007000d00b400c10390310803443d034081c001300103182003411b401e4016040003411002c04543e0003100300300034805031004c0c0e054000c0c41c2442c050201a43d518580f0079403240b240200e1840e03500c13040d254000c0145a5000c1e000450b13000e801400756613501c0d8920850381c0c00c0003490901550902000605a02d404034070038060300da00146900189103000358440c0507410091810000c44010007801c0f10b0884203124980744000c03865509140031145051060964a041c44490706041c100500b0456044d00850040255109650403148001a0840c00400e401280c3ca00704524900041d24250740365142d0001c00c2002e0081c801ca8803040d0352400102c07036410341120081c001420240040b40051040c0c0000e000c0c400d803602c11200b600300701c08142e50401e40b4840902d80821f000702e56a001d6181c16001304001000114050524540c0030745669032002c3d240120144245a403400b03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 926136636 1250 926135386 926135417
    0x81f030f0b0a1503050c0a06030b060412170304120f02010903390f030305010b0c0709020f210619270e150118110a0e0a1206141b0a 58
    0x41490540c14140c0e008411513580e007030143d00d40603000c00460280e1032448010030048d009000b12542043c0282c4407910340303490145502d00300d182c9040125540b031908041c20300000600703405140164050110b511201d000a0b4003e000e0b074006031565019641050b90800109070030646108250070644084c001520a50404c1800c541e1000940440c03502c10a00d44018003800e4204d0004041c0300752400c000c01e90321110414154081c80d90b02d0110703a4401d0400b48000050350f000b625200352000c460354103004011180600c80001d96000e410602058400c0055901d0072862481c08101c100c101011464141442a0300403c0d500045034803242c01c401800d080c607080b41c2d03c15540740380c80e0415281140c901c15003007010365a080c855120039491a20075011152840d100716100380100e440c01900d850100901a280b10301070607602c582c840110308001501010070f50400c1450740c070850000800e401301c4000d003c64044003900c0d09000301114410440c00c100c0110490703602c8620303820502101780c40d141c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 926137886 1250 926136636 926136641
    0x1e150903090d080d1503050d0e01140309030a0212162406060c050106061d0d0f0b070c2907180f03060b0f0d260d0903081f030f0b0a 58
    0x540741c02000b1100000c1c1807007a141d02610505030342400900180800ca8009051003515000180c000d8010365031400605001d84521031105030107040c842d5002400c0095840039400c211079810141d0030005240c0c003c03541c10302c900c142510303240400303a003058400d01d544449141c4540b80100b000c000703200c40342003041d81450301c64070030034207110288a120744951004040c8401c0341e5044509600f0950040380260040c0203c0150b881c04000510401c43e1100c10003102036102c90050741d5041c00c0e4140540804c03600c06c1010700c106e1054071120004081450302c0c444030300204030003040301e5440d8482e8140c0581140e020030380280891034803d100c0382c91040303550101304840d4803c1407031010000000003003100a40002208002c200e0b8001c505015100601a80c2d42055034020070b0303012100c0700f002003c8024154400415141140702e030518030382032828400c40c2c5541206a0108072060200104410b2012485402e80b40507040d4220041c0303180e44440c01105551b6000704040282e00c0000d100d00b480d80d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 926139136 1250 926137886 926137897
    0xb2d03010b03010e0d1e05031306020904050a0203010f08031c0e070e09070f0b09030709020c010e030d02092b0609140a0311070602012007030302090604030b091e150903 74
    0x1402081000502c80009a68000c611940350105480c410300e4511003048000940f50010303a030307c03564035540e109040720348401440f08085420720b6091044c0101c1d61500d02c030b00ca01c601445840140c1d41e50402c030154200751016404160154010007100d00b400e800b01200c0500030803100d00225000129035042810403185810100206050504000498000241710002c90310602415180c0c6501c40e0500150f512480c810300b50142d01c2540304101c5020030368014080b6a5000c0000904c070500d0020044c00c55201485217403805402040b8030610b480c2007020000e41c1d5814194010720310040714003a01c1c1e007030499000500743c1039403980450280031959856800d150024000e4503020140c80c60050111080228541c010303114800300880c08600510944501e90702407480c0f20303c04a90b110124520750301141044007003580a21141070140c07101700c0034202642c40f690000103140b0706588032628154902081c103284240110001740c4183c0042444c1000c1100d03000480312558503900d45d5480c52051 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 926140386 1250 926139136 926139139
    0x201b0604060b1806010e0904051c020a11060412030c080712050c060f27010e011803170f060f0103060e0703020a0201060b0708040e1b0f0d0b2d03010b 66
    0x100810001003120651003180c92610403079054495009455001e4a5042c08560040c007188412020b403c0c14900200c0142e03200b8440d0b01100c2a404208180701c40811000380c2100140c1d0102c2ca01c0010010b0b080360035103609009541160a06161002a00f0300d580420000f07400e000b26810b00000380241d45044039000c98201e1401070204020490003071896020484a0f54a40500e070040703a411441d01c0f000d07501480f2012444c1920004d0104001000c003901c52071072003550360361001461101c00070301441a600070500c040382c460a8040c1800781c01c1c0c40c4070300c2070070404051403401c20821b141d043d10442c0c0c00450594580d480e0000202c01030b401080180c100f0b9540004940400140b541d0540040400291560007070001d00c0eaa2100ca442a0040400080c00e0342028440dd1001407901619258480815601c118030040c5400c0841200d51040030810000c04000031104001041c500941e401c034101518400490000c0c00742ca5207142111500c0c00c10302401101c4080e04980e82500319410340c240 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 926141636 1250 926140386 926140393
    0x50705030a080405010318021e04060e0f0405060705030907061b0b0c04080111070f11150c030a090b130e070e150705060718062303040c0f09201b 64
    0x190760030003002d1604240b2855000034201360418a0f12070341e01c0c00d000c5038158003404040718028400c1007241d160b04031404190700242d440d000018020b007401d0041c1c2c051440c20520000c507042c9820306900701800203004c0d03414000104180301c180240000c400c0100c4001d03180142c2001d0048656000c1c10442e00005016000640b040c068600d1090300144105c420360b800030000030040b4200032440d4011514042c00c2031000340303502408902079080826804a004068941011010b240c0c0c0e0403d410444424201e47e1001c10400720294210b00d641020301254036405007031004110360b1044c480c002e40140c910404082000c104541d000300d810a4420310002c00042000f46a04400606a001a80152042c1c400c403004141910301803160710070f10000819858406500b020710075a582c1e029000300800305480c00c00c11210100105000e0f40c003561060703400c0d403c3c2620f480e07509130003034000d03030403515929241040c205008104c8189407a807074a0001c041984a140d02d000311200d080b10f01c60100c54501 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 926142886 1250 926141636 926141653
    0x6060305011d0d0f020307081305032a0405090c0d03090503010c230a0c1712132604170109171e160308090f0d0309140607140705070503 60
    0x1889000502940501ea0489004401e0701c1c1d800c07140304c052010f0910140e00100300080104038010f00400c509282007803510180c1e0781d10b102003880e0030032040540c020a07421402c0342e0705100950701050209041140c3c107000398204005046d864042075007655118082c0203c0b010301b0503020751581c030001c00c0010003c002e140e51003100a4054202c1c203182c680000ca4142070070b55101981c0050381c003061003a41c0c64144260507544c9030020f8107981d151050000d8400d0100d84031440074184554458940c1d107281800300e400d589080c402c041da00d00219004108480d45010390124000240d4003103621842c00180e0103541000d10b075004041c00040900700c20b8842b52000702440c8181c00801c03034030703043c50f83e07a4403902d2046407015114018000c1c000c105c00702c00049400441e1084520700d40000d1003000b03442c50341001d60729080c5400c524540410110307031913600c0070040c0030780340e641420703088600b01c05000d481c68a12801070a450020034018219000803d0490611408000d0315014101c05811a00c120 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 926144136 1250 926142886 926142911
    0x5011d1e07020a0201200a120504030c0303050c061008060c0a0c020907020a1a01060e120c12010e07060201090c06111212060405130c0315140103060b0f090103050c0d0606030501 78
    0x419544038164081031b2110306009621554854001c100c1c080540a4140d5500c1640d40110b820701c540c0c078001c20030100b84800300c0417580003681c1d80000d41c42601c403942d80e030506090442c1030010041c0840d480d0071400034100201c81000c0341685e40101806d08442d1b84903030302c80040d10008080e11003e500451050100701030907800003103d03500540551900d5200050809000608130002d014120010f0f030503100100c3c09090001c6c80c2c02905810005451035160b254020551100e8800b20414640e13454045040d0081d1080c400ba40290a0724070003800840010f440302e80c2440c0041c4210b40070003480c154007119001091000808c200410901c641d03443c00c1c10783c0301003c221010f66850303104601d01004640d103042c000d0181c6400f00e1f407018070300303c5d00e030310b140c8032141c40c00070002c500c06069481e4039140710300c2280701825502840c0700300d8001400500e4030080c003501076409090a8002c04080c0300503c0865400590720007041f804843c1c1401c86a41450100080c0142c0d03030000b4a25800c2c1040c10098 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 926145386 1250 926144136 926144143
    0xc060c090423040c050d08090103092103090b01140a0506090a05120303160908060a0b1908150a050402090f0c071e0213060b04120f0506010f1805011d1e0702 69
    0x107a13024402d0070404130b81300e0040080814a03944001c100354020003140b40d0b01d5019030803d408260007100701811140c6a015161501040140c0c100c0000340c0d62110700301000541e01400303000d000c0072240415203e038001c0110703504171454020180700d940d0214810b030f01603803250500c002800000e02110f41020000c101140d030380d0401d03a02d9130346e505000000401301e11b1050303608204903420341008040341d440398a4100028100d0320406c541004136072980f0748044200300b04000c01004080011b180e110104261014040d0f009000c400c10b03070b824442800096a9010b1b5016001508026a01740f26100c1004861240c0314104004040c9143c0308144403c10b6024010410904d00a83e41074901d48021400001100d1250040801202c42807100f4031042c5054038100c0322940c4140d00c880ca03401010340f42c10b07103040001d0703000280415400c4800e211407110250305013590150000280540e504000214500c0a03020052030f16800504001810315524013591010341c0406e20200c5506041c40c00c0d00035203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 926146636 1250 926145386 926145391
    0x204050a030b04051b0627060a1d0402030103050c13090b010b0901030e1518100f1b09030209011802120f010504180c1a0f0406050405010e060c060c090423 68
    0xc4c1401411003001c045910315a00c50605030004210b0b92803d442c54080904c3c4584240b194441c11001015140b11a19403030010180071041c0c1d00c0b800407610a081d16154820089510940620b0040c0010400034200048540004404a540391811060b10300a440181a120000f500b4251a140000360018011000700020402a60280f1040e5180c1c901180c0c0da1111020201414660100140c680140f0b032042401e40602c5100751926000e0011103182070b83d001c1c224503542d040da40c481c1c1020719544042e04000094403800d245d0040f900ced64000800307005c0c1c1482088050a42c1d884042120032140c0e04507203c84c00c400030284d58a04204103000301000090003000d00070b03842c006044503081c01e106202c501803544028071102c1c0505050441b449444443c1038945401024001d100b101e480c0c1d240a840500210303610240c07183d18000c00144030b0186a1941c078080e8204201400b0b41c0b80001c6003250341b04c10b20042d05650361200c2404200100368205a01a158101114403181000340c004002d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 926147886 1250 926146636 926146643
    0x90f09051f090c0e0316090213031401140601020f28080a0801081614060c030909070323091c050408150604140106081f03060c05030915010f0b07060204050a030b04 72
    0x5000040f00a1558520509100c0c1c031b1280d10200b000c0141d450039070020003c5030f00880c1c8580f005c5541c0d0fa6010300d83e600314071840324940d4407054050a60030000d801142d00c000e0920042c2410720310724500c251601d82046094050244000c4d800510058100740c034046543d100c02240c0d0740e075050300d40040c001482030003150068028142d9906100c041d030f200315002e40e0000b0b0000ca21120ba180b003046200d80c401c8d108040c084c00140409846503403000159031082105407008103501d02000010140401840742d0800548406c20601503881030020300001c1010040c0b0300d184010313030b14400c252541e00481d4001f802038850300341048001104100e84038010303281902c06100309100010020a682800d000f242d0003e0b900d4400140795a040c40e1085040304204a21071842549903115103066031440c910050101c1c200106001c3d01d480b080000d48aa540c94480100c0e945d410f00b04da0000100ea54070600500c014041200310a000407039040380c0042c1401040b4039a000e9880c6411001d01c1802ca4050303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 926149136 1250 926147886 926147897
    0x80d2708070b07030507140c0c0901030f030305130c050f01020f1f05060445062304021c02040e03033c06150705070e16090f09051f090c 60
    0x1602d058000d000380c6010741029144d003401f00e4120100c521440d00140102c2409108804100500ba11811542030103540034205507024950141009402d030744003e071100001c00c42c0300480c200032078100c4862200740c442c110b440b0100c192001004078642908500180200e000d184200da40c00f031000040707080c146406d08018007140d641c4004004c01c40300e46844900c07461000440b1075110840c40c0c600000031620b4003280c144030180400212000b6620400200c52040d0f94501140320502c500804c01c04a41c500039200c00b0910b040ea020601c00c0111802c202a002c1040306508210355a9410841c500c00c403800486c1e4803071034020900100307098809111400398482c7c940c000310300158000800590101418084042e8903020300703200c2c0e0004043d00c0b15602c508203001240c0012000e11043d03004000300b1000600e10f0811488122900384150103000038402812002c201100c126040c03078044807551207002a85540d07114520080042404400004042914020802420366800100541c519560f0ba = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 926150386 1250 926149136 926149141
    0x3063007120804030b060a03050d020a1509022b08180f120c060307030f14270a060c0207240207090507020a12021002070b22080d2708070b 61
    0x35a441903041c0070240891004000520200300c5403003030160860400342c00d0314403c903a251030752410007d071030b0052030050300040d12036030a0103070038246407600c0c1c2d100c04020840c00100d540010603050007003d200f080b900f10b1604071001c1c0804513030504040340d04003031402d5880c8514080325040110314032100b44a42c001c540c208102c1d00340a114000c2c60211003008040610140c410031002c3c1e00018003902c1015203440380749a42074000d02030849403026490404d07065092000ca81c030382e6042c070003001004040c0345040100d02014001100c800e2203800003c00206800d103541b04030f042610075006090425801d0841c14039420100d102c201107100140d00751911103840d40c0140003a15000e0341d0910043c2d011b82c8060300420106401d6040d4141c241c01200d80b6403020b03400c0c0109a801a18058030352459880070410303400610b4400f40c3c890684000c4200ca10304007030750362032010b004110101c000c0543d1084141100c03040400076a002d490b80b648802d09144030fa1810702d101c1e50111004031000d03030b1920007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 926151636 1250 926150386 926150399
    0xf0403020a090504201909020309121306050313060606080f100f15090f06090821070311030f040b030a140403230906041401090605040f030803063007 66
    0x64034000c45c2d0100005120824101911020200313100b001030344824450410002503108a200400400020401503240e190017400d482c148000c200000e100d200307003004104010740001a134102500c440b814100d850b40c0710300d4241d407920340d00d845004003000c0c54110b01080340c1d90000b00c82841511100c070013040f07581ea00c2580543d09045031058101500403c0d40500c410992030100300c2c514581443d02c502c01c25910303d10400c4005043d40004049810a00c080c800c0c41c1c41403100940704404802c0788017620b090b020b22582c942c89040030103410000d917070503d03c40000c02401102c3e5034036882440141c4403601c0d0b240d2040f0315801a203080c2d0f4a189810059203005445103440d41c42560580c84a05141900901d0120006004001c00810310000c09c2954119030722031025101030301c80860060030801018001600b40d00c0a030300020b0134010700344001c00000701004c0100040d2a400007000c1d485e502e540020413102071004600d502030720440b0101c0c490b00b0746104031030221405903004840e0f03050394800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 926152886 1250 926151636 926151641
    0x12040203060a0e060a02030a0b0901030320120d020a020a0f05070e28020c010608070f090c020303010807030204091104020d05100b040303080609040f0c030b0103034e020f0403020a09 80
    0x400390b400d181c00c403e0028055104c17560103194031500c0c51f00301050b15082c40001682c0c00000340c02c120045105070721104e0090155811001c01e031400d0320014000c4080348140a007844c050705500551403600002c0e02252503100303115040d00c0302d03406116895038800c1d9103020780c0c580302d45010340100800d120000443d4070104500022070540641c11402c5040444034000000c1d510030041c1d222990749606001603401c3e000c00c41e11005150b413068588107181804403c40540b82c2d41014003003150300900044c0070140740807540d901140e40c12030300090002c03a0f40c0b40034000c40b08120061030380070b407012a400302030300003d420092062245c0607103402d03e15120007104405c1d0055000c094006030454ac0010468103003121829001400f8480401203541d0560b11a1919071131a081100c00a4120004008042d00300040342c49924011104100d03003815000c981184820240c3d101c014440700c100d1030f22004401303400f4120320381c506240c19903a50b4481c000c4d40300c0a81c070510049014042c00c020001c0d04900701d2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 926154136 1250 926152886 926152901
    0xf0a020105160512060a120b09011b1b0201091d180106080d03051021060f0506061614030c0c090a0b06040b0d020c15090f0d120c0306030812040203060a 67
    0x549901e410400c440004c5585020000c080a4000c0340c03000010815040720100302d086d1601c10700f5802020b00d8444441825030311004139150351080464600c0c0b40705a008500d8212151030042d901d00c160001d400126045440c9500400d24845107018011041d00402c0002d4452207411b10303600341d40c141c5004500d088134003601c6080d0803a0448010002220305c01e420240e08001b1044190a505807180d2254016a004a01c05036041080145003010000e150060310541d82460350108010316089020a00303a20030b802001d0710020041c0f510104000100701018808844101101e0302d40c0c1580400c0383e03441120340a8a4810294031000400380092405071055801e4081c2400c0d003800d1030401d864075a41c0011800510307103038081c040d41003980d40c10420000e628900d048072521a00b07151054a082503d220b5551a01e500403c1143d9945078016a0100d04c0b03201e808000a490490584118000c00150304002c220480005100440410b5484d41902450084041d140261182000c50041780d040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 926155386 1250 926154136 926154181
    0xc0d061d0603070b030106050d0603020315011a0a020c0405091c020609010f150605070c0b0d0906051e150a1206050103050f0708070302300f010605010f08040b0403090b0f0a020105 79
    0x2080180b047e41c1c4104042c000d2080c011a0101b8619200d90010b410b01c0c3c44403030041062034503c40108500d101c15042001c8c222201c01946160040001d002500d074000e5101c203074003a5440e240802ca001e8000c02501030074400034030080c0340351051080e0003910307000107450641e03a641c21300e200c140281c4400d10400024005401c1c0b400c030140c1c50013900780c0315500030303080c00d8504d007500180c0010141d00b1180108107080c0100000210400c8074500b0104442c0090001075482484650b99201110400c04603900300503602d01b00c118030781740000040c14110b11504070304c0840c1c41640201d0b041000c03c2d048030303068038400c106035100c5400c0125540d55902480c41004910b5000e1503040025080030119040c20001e490603042220000640400c4000c5000320704280c6507122003400c064503d0280b1404000d04400d10300082c0121000000404003407019101400f427401e42000705041501502032a001004081c10306500d034482000c00d9120340e0131400c1c0701001340d400c04000400c49807000e100801d0300d401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 926156636 1250 926155386 926155409
    0x30f0a1401060e13030302120a0603170301082a062106040b01050a030c02031201140909120f13050d120e19061d03100614180606030c0d061d060307 65
    0x83c1e41c8118446013110800545c1450340c20810000882c00c5060301c5c0d8401d042c140c4c6e02103003542c03a42c42c100c0f254000c24142c2d1247c07400280018010410701190180404015100c08d016a40c00802171140c1c1c0b01480d040d10398040c2002409c0c0f8081e4502818203402c072181c3c0c000c0010503070745074010f0000340c410030a282800500308128000c01e00b401303588140c1441d40d10303104032410034110b003007240740070000ae070405401c036260300c40304248030b15156210942c401144000742c9140c042c981001481401044020100f4110100d0fa508071108070510030001040003c0031141e196484d410b1030050510081190030004a407212031041500702601d074144250607101c1042009881e04000322000154109500c441280b10911070f05035075400c01030078a101c000c0c4080003401510b80300350860304c444140c0080303010741410510300da2400d111060712940281d041d01c0040c0d0303a545070204c6c41098441c40c00c0398240b440c5000400f04e10501403a0700b1000101c14980010034a840d079004141d900d6145110b450486a03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 926157886 1250 926156636 926156641
    0x604200a0842070c050f01050103210f08070516050a110306010e01050f1003140103030306090b12070605070f1b030b07020f060a0b0105040504060b030a110f031311030f0a1401060e 79
    0x900c44e4031071440d064007690660311305045000f4403d007580c500b0b034801e0b034120503001e074041412541c0203005040003210f0300388440c04a83c3d0490107080c1d844000c05400c20300102041140d00081c10f100c4411a16510000303451443c01c091030200030081018180d9800382c0715800010030800401400107061f1480140340d2800689030b401080450340310321240701c04254986030109060030701040340700c1c041d5110f80c40100743c05003050805403ca49604003414807401c1c07813a8556212000125a40080d44c219140060f03a400c10341c100210482d80010300240090a9a003003c00d54540c00c0f0401d40980344207103003c10300307520f9010b0100d0b0368944016881407103400c0000411890303100d81d4005400100c040c10140c0c04c20307640d600090101c81143e40104a03c141c0041000415070042c8104440c9034000882d550610800c0c0c0302c400064000204280100140842c0000500c44022480511102d005040f1500182e40781c0007140c0782e6254490496004601120f41640e202042c05400240c1d03440607610b10700356 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 926159136 1250 926157886 926157901
    0xc0f06090a1407031502090d0b040b04020913170a0e030f010c080c04030305031f080d270e18101802010905011103070b0a0e010c0f0f020604200a0842 66
    0xf5071001c2a0188e0095400da481e0001a0400464500c100c5c040c0c2c03640c10032441d05005102c41880c0080010721080360362203a030000030b8811080d0710002c400950308152180000d800036608408c840890300d0303241c0b103103151800e10100150031000703101c1c400e582d43c03200301d46480704084c0740390250b404010040f960500000d1809444403001402491f03100b0803550325079030758054181c100113000b0408800a106010010f4040301c0b080040c1c49a11007004c1e2a0301031528018400740c1c0c0e00c90281c00b212090003074484541d01c0d407004100c002c032900c1000b103041040d0110000c58080d40c1c440e494040b40070801e00b100020740f83d070240300b000c0c907003205c5403029524200f902d55443e50440d000506d00f01d01306583e03000c00f0790308900034401e4200d0301500d0b07144e030072064646000140280c030721008403270115402042080000340c800301d298020780031202104110084080700080e10b07070086401c036501c1d41c405d628195070003010442c824000540352144045625001030102d0303412030807003a17003445e2702407909e800b040c1b65 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 926160386 1250 926159136 926159141
    0x9050112030e0310060f290909042607060b0405090c190e04050102070c090e0d030e0a15060612110909060d060504030801031104020a020c01050c0f06090a14070315 72
    0x400000900360340c1c01d0070a0140103022251707541c00220800150329014000c0c0510100011811980e03000d10306d080c600c41511524a51003440360301401140200d002c1001c00401c642841640310140070119690700c1044400c611030340003060151401800d0000d0864181030501ca02c0c2e024440040281014616080900800342910000710308111a0044000343c00850b11070042e0184c0e03c034400160783d031105810084d454641d83e801103840c2e68074110005e03480241c001517001c080c0c00d00d42000301c1e400e00d120541a0a280d50010007600340d80580010060200e07240e8007400c1030f2031141c0c903000140368000b001201261512171b040e000103203041104001c9403400404c0702ea4401c40080070342c007d2480c1c44c0c1e00c50050b03c406603012800705d00d0580051040010f194509941000c0c02c1d00e0450800b4110070f0000d60360b80103d44814144640055080c01100080c03003103c601c0c803681811100705d801c200341410350314203200006581c0111100018200a840801c000d0200c075000380f0304902140105000100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 926161636 1250 926160386 926160407
    0xe0915090316200a120609030e130e01050c0702220e100b0102010f020c0a0b06060d0e0c10020304081e07090501120b0a0204120b06120105010806100905011203 70
    0x80c40c441400700c4050aa00b00c01216a0548a624100300702544118221078035061407030400d00c107086151080c04501200340f60f0b00c0c50a5005600410000030604094580c414100202a0080c0c842403000f0314000d03d0b07801005006c1403010003000300d56166074520000303000c3c03003000940c424070b0240341b504203600340f020240f8902920303100054042d40d1410000d10340041100500b45442e1a1b48080c9501d68081c81015020f4124140031762a001e45040819200c8040701002090314400d20302003807050301c44000b45c911380c41c0009001c06c1a0051f400030782e5a034142d041e958502c204070068448091f644003005960417075021100800c1050703d001171241002426000c0e10095120710100040c0e002c901c0c1c041c0d14000d0241d001c1e10340660440781414664400020b120600c02c600400040000701200c00d944184036030450311407203454441000055012152403071040c415824040085520f0320041103182c000c48004003400300c1c042d074404072042558003d110701a0002801003c0c2e0300172034025000c900 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 926162886 1250 926161636 926161651
    0x601020d081506070f1406060d0246150503130f0501021902011b0203041a04080f0c01023007081e03010504060b0c1002090a030b0a050601090e0915 65
    0x400c5866030b000070031426000000284c0c0c04406001080c0144070131060459103146020001c1d21061601d00d002c5490369140c0080240100e80c0741800c9540d4292035040c140142d20a0303082c00c083d00a0800c5400c0304144a070801510038007a0360000076640740000901c2c84840014ac8030310341503950702e0220000030b400c0c0e240240c4000b1024603100700010000c3c401084540ca0140f0380420444242d100203086500c0001e4005015a203041103022a58002040d60f0132600d5107200c601030024140c00f0365410f0300590f0300c202d18074454441c4031030f01a000800e400d203800b04c013a0300300c07204c5000d041c00c903290840011681300f00d92540105030002c07100d54031005221650041c24414504030b00c3da05116041920f2410507004500c7c088014003841c40c1600545000303015071a14a030500300b000b405151a6010454841d00c01540000d08013000e4880c5141440103580001c10310010786003224020003d44000c030390340c0e40081c480c4000412191960341030f6900a103105001442800e00854144059040103455134 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 926164136 1250 926162886 926162911
    0xc070617220602030f1e04020a150201020c03040e01030605071803030806011e09030227161e090e2217130f0e010b0f0a03020a03020d020d0902030f060601020d08 71
    0x7004507800b4002940a81c064500380000c0707190100c45400ba0008640300014240d1031a0140720159a0301c041c40d405554444810b00d02114003200107a009205035141e100380f5000100380001e1b090040428541200c1c01850288116900c00c5070840d5080340f80340c51407240c0801d1520034030201c0e101e03c40080d03104d041070524a601c500c145803a00208403c02c0f941e0f1000403007a04083c030446c02e11041c06020000045034115410807003411401100200600d4039008526411901c211a80b01daa105440d40184240c0c1806040b0350001c0101400344030b004802c079007400c1c2404643c00490a0705c03c200d4208030b4111660782d00b60742da40c07010722960080c1001e20310303000301f0f00251243c580751200d558018040000f681041e540b901c031a03020030220507406814074000602001210f4603852003180e0382c48500b4600103a85500c081c80c00d800a010f0001c559036020300c0031030100340191081d844003999078001c5040342d4210120f0b2001d40c3d5030318400c450160050b08a5143c020724140a03800b02d540202565506 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 926165386 1250 926164136 926164201
    0x9041401080a1202060907030f0206040504061e0f0b090609010e03030c0d0201181101050307030e06070509011d0f0418050a29160c080d0c02030c070617 67
    0x84012140003a042404140c01c808401000c1202c03545036030388000402e0001d80307051314003030405a0316100039120141aa0789007500010443d603d4004075006000020030401281d80c030b07074500c0b401183c840001000c030294580d40105480f41004a444111070b228007081c1e282c101e4503010f01980350405901e003414804a112101c485603014006040e00d03d104130000c1a4050007000002e095aa010035682101100b046462006c50b60010303031109920820300b440c03a41d0741c603071180840c02841800d56141c805d0050390706000b40320f9400401003c00c0d100c01d0380c1d84450f00f10100c11070301b0b600002d481d42c603901c40c0701a4944103031820f264000b41082009800b00103034007445070f1203031800c004d903003181207440810700c0d43d80000b03171001000031400281c03258484c40309500c0c087d0400940d07000603043d40010f101010030f2540c1040048411100010740c101c0c400c6c8000c500c106800795485d00b11440d0842e250085d03240101381144203003100c0310104280964a1000d13290304060301c01804426021017000c0140404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 926166636 1250 926165386 926165411
    0x9060112050a06020c1c030c031d0312041401090303050403141801030509010f05010e0f100e010311060403020d050715050a080406182f0111061f051002060a0506190b0904 75
    0x10051b101003100e80300410005504070004080b50700c2204400200c10002d4a02c1e070681c000082030750450204075480011540b12401e00005210040803140c14647c00c058440d000c06070305401440c0a0b0784240c0780c0000b108450804803400d40180c280071000c500b4826084800d96229030040382c0c03c01c86642c00000e4440b56124510140d030403d802c0455148400d206009010701100040b9501900d51402c62900605245241ca0800300620000d41000c2d00885080c901e81e40f41c000b1200115401080c000000da003510f8502e8486441e03120b150b08044c2c50398507480d143c0d40550200c540e25a26030703440001c1c9581e030790f8450313005211003121050181052401e4400003a09069840c440d01580c3c2e0b200d801c5c4031025068550241d5004074403604214130385001c1c05c0c1c1000300040740b541220b40032031142c44000101c03094298045440d4000c81e803020f50642e170f407200381d0340110703205000380b49012060040d59203900c18801c42c80b903080303618000b034804044200810150980174002d0310304c1c01000469511034100303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 926167886 1250 926166636 926166673
    0x90b030309010f14070b0115090e04110103060509010e0f072f070f061119030807081b0d0b09010503071d100b0304060f0e010605060d020a05091809060112050a06020c 73
    0x181708a50f820b4040d0018091075952800043c3c4100e0075191400d0741034103180601e00d9051000d080100413001004540c415680650058005020041c240c65000d680d00e49008256007010b84a881c40c05e602040401e0307415205084800035524800c080304c80c038001c034582c40d00060380180d010720045d0062100124245140842882c001c0c15159200110050080446414a10414510540710004d801004d000a402a41c01503011881742400c502c59607a00401150903100228980c42051000031030115a954641c8100c0905105480d00326550b0b80303420034941d4504443c05241910541030007000d40c4492410011039000d0084250b45403403541c1d5402082440e0000d5038101d035100d441d01081d0b12607841611462105000341d10003404290300e4100400d07010301c101c4003507030542500000c103c0602e9004030105e42040101521102080840800d62040746405880207540e9004410000400c0840841d0725060b1642203400f40c0b0250903203980d100000c1d803100441c2e141d10700585a08080204201 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 926169136 1250 926167886 926167897
    0x3050f3408090d0903030e0603092b0909060f050603060d0b15040f020306010905010e041e0b24030c0706111c050105010903150504060212040516090b030309010f14 72
    0x5403128600d07402d080101904102c1400e81030420011415010404a9405905668101005e4030840d035207485404608e07040c06c41540c114156800d26400d0781c0c0002c1c0c0b003194200c0300d40060340d40d8211b00b141c030342142209581c0948110b034040481c80c2c0c2d081c040c0d403800c90b000f1504030324010800078070380101d95540d01001c041150384060203280c40214007054142402040946000d914003140f451a1400003e0700084c00e501600e41003040781101c2001035102e030390000c42e01d6440320860850780000307216a00c011b0303c3c800691030b02400d440091a48000506841c0c52f0502e0004140203003580e8400740c40102503001080c00741c07001d40c0c1301c650105288504c00d00900e03203071340d80d04400d940c02458001c4c02e9060350010391020341001607410040003c100c001764440c0c0408841100440e5075111410004041e016550881441c0740440050004210b00010854070542403c80e00d001e1440d40c8618160445100074101d64064004101c216019071081c0201c4070030780d00c41e0070001c8100340d101542d0790094000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 926170386 1250 926169136 926169241
    0x50109180e061311040506010f0c0303020c0102180a080607021b041d0303060901080c0319050f010c0f0e040504020604140325090e061b180d111003050f 67
    0x300446a018032800400c090540c3c4005e8500b40854204080000c001c6130b0300000080400c8003042100c810513109030102c5522401030002035488510400c51a0881c0343c0f5030f18024420100c80900280d0500040f82c640d00c65450354000e00344140d01508640707220a0281c0031250302c03540da41402e140081142c481d200c101c0c100d090085171603103400018001c11440607040700145030310264a041155078001041003402c640905070320001d202c0c030324040d4039205028100200e41d508200700d440442d640310322005407056280d038544a1944070740f814003048541c160390180d003141040100303116030081c507002c50741e0785140602100ea0040c5008245540c54100b0083e5102d102000013041000da6140d005170407803600d10310050005400c0c1001890705401f02c00c00e0320b01c81c150000c5028007024007039024040c0280e07405031914101ca2614a00b900401c0003c1c00c5c05e51103051300700f07502c0500d181310388950b510a44424500c200c1a4448001800001d1941450007408204030310800c45890070f10580b00150070b50 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 926171636 1250 926170386 926170411
    0x110f06010e010b16120f0e0906100f12060602033004030e03150c0405040c14090f2701030308090109051509010204123e041d1f0b0604050109180e06 65
    0x5100384014007440c0301c0b20700b1f24401e4100c03009000c01661060a407986400341410004803046400c241502c5500b24400d409052078074045001400b281c001c0000e00c0680b0340f039041010803039914844418000b24103071501d1098009c3d000000d0009014000b000c0d6031034002412034240041c1c0840d1001009812180081e100c58040b504110703500b000c0c002d203441c134925818480000c0210010b455000d00501003c01d114005458813210b1986820301010f002002c445403c0218891590801e012001e0070b02c4224000340840c00011101d1806104008082da0b020f806404054041900c0c00c17008400a80302c900310355420031001406840525102e10058803039800d9005030100c5845038103044600000014191a08048032022005420906205c0c42c5084800182000032401114811010604803030000d1003007040d081c0c010440302c0b45102c00303028076072002c1c030080000c0c60602100340528442c240c0400c661020900c03104420007400c4114407080000050700303030b000121042c500141901c01c42d29000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 926172886 1250 926171636 926171657
    0x10507210f1409040b04021b01020901230913060b07030905130504080f071a0903070c170d030b0f100801060311040308090607140706110f06010e010b1612 68
    0x150031449149220009003803140c1030b00c00b0200c0003140e078071680358058452030340d90080d00201d42c0c5650582d01369140e40700e1038484015200d1040d60007507010f00020340c080b61010020307060401050248225101c030001200c6d0030b00500209226089a0881002e21003644440000c941c001c180c8018040003400b13035990b01c03c40c91504040c01684001007507520092410a4101f1020415040480c4d46003080042c01c0f9645940a0404086107201191355040340103000003031102d0325900002410009005405000e0324590f1404001404601540301041a030046004810307194080d50024940c00005408065101040000603011000c111803413000320b105040103011080d4140320398540f8440b034002d4503181074115101d1049500130562002e20400b0009808420442082c0041c03284481600403034200036240e44000d01002e02d1f20018490328482c1c6084110002e1001603164101d450790040800140d00780001c00e401a4003011115001d2400d40607030800140d1400c0c80d0b011072644c142d45009144 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 926174136 1250 926172886 926172953
    0x304050a09020c0304232707020609190609080f0a09090207020a0b0711041a1e0f28030605180d0906051b0106090506011106040302060f0402010507 65
    0x5080340c201c1500e851042c0311480d1024400000c54098403407810501c200c001000c00c00140c44010f1181c8190060010901c03c01d1403010181c600c09640303070058204440390b0b01d558040741e407503404440080c1700d60701c9072864210500100b201070b00706502030180401ea0f07015985508869a1005484070400780c00015042d10350355100508001800418a003541f800d51140c001402884d001d005c6c9080ac0e901c009000410007021031a107a000c980013400500a0440f00710030012003100c1100964000c844e054140f0000003158410b24110340750040a44200c3d840f0354040c4844a04202900518461a0381b0700b01c00c00d54220000500444c42072901150b645042218000e5800701c2c8840c1711400d50281100d411510b8100c06204280c40e41440e03c40c0e02c2e0f400b00c114400090780c8006410b1002c1d480c108000c030b141d05007a08030324410007080c6c0301c2550a030b0302c103001d540da5038200f11005001600a0400301c1c503c1d00c034040940382c0050052400508003085500c0724884800418841c00c8594810312661140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 926175386 1250 926174136 926174149
    0x61b0209100b22060f020601050603070905210c010c0c15050c0a050c03160302030d030b060d18061104033801080a050f06090d120f090c1e0f0b030612010509030405 72
    0x50005172404041154800740d01941c2e600301070107407a200c0d240101c0056445c0303100b00306580007813034001d005108800d00700e0309255540c981001c41e500203014404010304a540a50700203501c150348010094102460100d10702004090540c6181c100401081642400803041007103801c0140941e01411911304201c04041c079040303c0e40007600b0002c0c80a42c04002582c4d0200718248844018200414a01550350001d01ca6109410411403d20300e00030000d000b2036040000040070f1072251404000b00c0d4003002c000c03036040c042c42c840107241c1d065942d0740e0004d0400040e00c2400700000c2043d010100d000010030402070304801d8005182f00e5100d00548014440c01308010f0780d291a805014001908040405680362215906aa402c2c05403564440121182c41e502c08544080c065000b0404280320f441c0150340c12207188100c94450f225040007040340d01001c6402c104170313051000b00b480c5087c60800082c055400c02484660f11a03140d1034440d14010303083c06518410381d02034028564480c00c200401a5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 926176636 1250 926175386 926175389
    0x180516140f0f280e07270302122401050607081c020304150c030b062a0f010c1d01020d27030302061f05030c120f010606030f06061b0209100b22 63
    0x1000701601c0b01740300f9031540000306e0710302c18003041d40100455000e840708803c0f81102ca610003508509485203114402c1804150848a0341c00181d056090f090680400e000c103960032b000b1352b40d02213002c016040000f840b50b00242080603034491903c040c1c12000b11004100d1b002101c01f07540100c09040300d20b1000c1d20b24410000039500c0d40c101000300051610214040f800b50702601c6141409083e20340d0419901c1c0205841000489401c565a80c059481c81e1406030001d0101000410581c8210350903240040c180050b8245041e4002c1900e00141e0508503607203d20b21017100f1501c80e101c031600101c04004110320010358002d40041456082c1044410540400098a4442d61945a2081c0039560700886c0c408180042110140d4030b0043c1580c0349800d100011078000c074250710f01700002603041d0705900300d00c400e00c403191010081166211019145241212421304000c40081094001803400100e190b812850102111038890380320017031032015900004000e906200c050002c004480380140c2c5c08030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 926177886 1250 926176636 926176649
    0x3040911030f01090c02030d020304141c050706021e0d09031d09010302043201240203090405041103120301031709012c04180516140f0f28 61
    0x80c5145002d141d0404804010301502c011585c68010781c2c03450510030021303209041c0035504115668101860410304550003904254854001c1030304007014283c40548000d14020325440e003a15250040d581c100095000c4140380c08006032690881c150389410101810240c200000c001a144d8094103028101800400080820242c0000c411003251250300807541165816038001c1a5004038610440140703c0c0125052030107042c0c19000210060442c8a80e4101c400340842451980c0f180300e48049140800000d05015a000708248005400c147d0b00c107507401030203962480c0a841110b0006400d1100001200151a502000500500c850200c99804258003000342a01d01111080041c04440d0b00030a400b210b03401200b8409400d00c2490040c2180540c01401000000e40d040400c826944007248151490b02c2502c01142900010225900503200c0003c9072000091162007004007140c012140107030003403010b0540002c281c8444201042c08a1305401340c4402503501008101c901110340d0029 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 926179136 1250 926177886 926177921
    0x706150e0c0708090312070f1101020102090604031118070207090605030304060816140f19082412061302010f080c070201030e0115060f120501083705030409 69
    0x4900070035450100c0c1c02440d80003000f99160a1400002400d040c4242500d603280340d000100041040505500b04880904c1864020851082c1c10300480c01c0780100403c09070040c800300414404180c0301d181e035040c50000205421140594502e500046450690f1810050382c4278000900201c915801000003030081603004500b81032500c2402401c0000103040c01c0803030481e034841220010320441a10540c21110040300c1d50b43d10f0b40d4003003484c0c04d5100306140c070070030401d44801110f47c0c0c3c416004d103409448022340c40d001e6083c80304004003101c94003a18590780155a240300300764080003409a603116203800d81038500d00d0a06800050444100b14140f1001c000807401004000c030b800307900765007030340e502131900013080030400c0009801003600c4840da06005814030000100d85900030070070300d02e0740a02e548084805041c0c1d480340094070801e004111b015041008819070102c4041d9001d00d0055640450644203171220546500401c8001e1040d07900303400008007403001c118980145a41c1c1d00f4880c007035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 926180386 1250 926179136 926179141
    0x152a030c100e0f060f07081801110703090b13150e030613032304120f151505040b060304150219080402010f09050f0103150b040e1f0602030703050307090b0706150e 72
    0xb058905c0c0d138010480000d004050003c640a100300c1c40180040e040390780002c00041d04451a11260f0750070807101100080d081039070101e800d100b420141c0c0c92000203442141852401c00702910034110080c00c0ba1020842485484401580c040241c1401b0b42030010a959205100303007001400c200610302d01d0b03070241d9414802c004420042030111800c0320b40d5148601642d1005e49045024407401e01005028441c004035405c080d40c10705c0d40a404020841d01e944055240d88205002c140c1e05c940c2c2e0a20f03407101c0d0900020780899440c0c440280d400f001400014174007103500b080c1c529900c4044025600003007811042004558000c043c401c1c0448150601900d410318010002e0780d8010b05c41e00f030904154070307400d0078110784600c19440809403140d039221a840303039154042905680c030211040811007441500f00c1e90140c514510100c261210b99026602e80243d9803010340752540040c248808214a911000a29488100c003034001584142000300704000400e0341e1401c02912500001280950f00f0207 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 926181636 1250 926180386 926180401
    0xf03050f0303060922020409151d03041a0d021903141006050a03092406090203040b040b04050f011103070305060a0b040531020702152a030c100e0f06 66
    0x4403a80503a545c003100c22450004c800441c000806403d009420078200020f2000b0051010fa030091101c1030203004015030140d090015207030441c0742c03021901c00c1d00200001d11602c12001e142c654030762481d00c1c5003440c0800130503103041268000c0807800c1540c00080c01c0820300c56414001c2c001c400c0381d54240f00799a03060401031005d518146100d1281444000074100b000d0358000d420040219402500d113803401d000a040e02e110364a000346400d48440e00c3c0c8200411166128401d40340a203400c0070360441c05982d50b654019403000040e10548651040030070600c4104402d0042c0d224031440c0081c4292281030010001d400e80700040c0c540b500c00c0b03208200030700921901c4003d035401c850003110a40c10505502502c50701c0e00913032143c050600c4040c0c1d41c00051810300c0740c0041900c03500c2900c5813811003140c4505140c160080001d071681c01140015a01290781e2031500c07009800388054103980c03418280d13601e40c6140c403441d9038600b50740036181c292111403014180400c207100c0030b100015140718604081c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 926182886 1250 926181636 926181649
    0x60f01060f30060e181b0102150901051e0108060f0709030503030703090c0b0a080c0d0e0111041a0a02030406030c09091505030d0e0108040b131a0a110703120c030b0a0f03050f030306 80
    0x41803000030406030745550306c160384204803041700403102100354910343c24610200e07806003c041b15011030050440c44d126015085003016141240c255a001c0c02107a118514544600540a4684030400507100000300c04500148021030140000d500c0c006501d82d00e500d081c40c3d0000c0160b00c002da0ba4601481400346880d041084160b000000064203039403500003104102c001c050f8042c0d180b0b020340ca003c06180d804069903004200f5201d41441d01c2132441016991448148100b04e4044016007007840100406406074101c120015803030f041001145803100d032907404940c0030320008902c01c42030420811460500b031007174042c15141450810100c0794040d002900030030010340018203990340034001920041c2e00d200c4170b4218a44c00500000520420780b00003840b40740649050100c0c9151082440145406400301e41e411359064075117042c1d0040641c084002000c4444010003450749811443c40700d03aa035502c070013004c0e15108182c02761007800d40c10320b5480e04c00d00380e074040307400d43c0f0410a211441e9502c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 926184136 1250 926182886 926182903
    0x9051305100506061c05010e0609100e0c040b0d15051507020609060405040c0507060f1406010336030e10092105060705040305060f01060f30060e18 65
    0x20280070400d03032500340115402c1d10440d0540d0b040c005c1c4039200000e00c5801604818103c40c13030010005990748481c410041250810f0701c20001905103080100324180010300d086a210f500d8848003070805a44020300c9919a003c200882d1074181d43c0c07540304800d400c081c04840042c0409840d5001240c20b41c4003406a03e104e40c0c80d010748204000b0a00340010340c2e03000304440c00340c10007030010301083e43c0752400580180c11850044036014148403441c44070040c980301e0845084403400116070180c840c03e0042d402410804009030b0b10020b03203401540749003030103090711555100c03014014480696605000702840d07008070707156209048442d03c81404a9001010b0004e40d20000306d070b0820110450101c080744400c90500600f117005200400149942100291080301d0145d800d407002c50380d8060988001072404d000c2c500100344100000d40603244a40d441c0340301c0c4500c0080c0a0180604c0001d5001c003813007290342401200d512362009000c5420350401a50300442d040d200000c40c00c000310380054998402 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 926185386 1250 926184136 926184163
    0x1611130c020705130b040e01050403080a09080403020d02010e0904030e0103111c0b01172403031911070e1602150c0a0e0402070f060507020c120304120212030a030609051305 76
    0x201e44e0100c0c1c4070320341035028209404000b442000071411a84609003c0e24080360b0641c08a0400400a240c84002e070060301c40340382d40035110038a8a41950701f001005401e101e03080c0c2c100102a003012016884051800e4043c6000b61240003c8004600004043d2200540b1103c0c0c011018400c2c42c00e04104049a814106c1142d040031810301002c8004035007108820b603040300684410024491003e100343c8402c04500c1c00414410844202c2d8414156244122081c4400c8441c041c000702d02d9445c070130b40810422103141d8080c0d982003951402d900b030f41400c0564000240d40302d02c0c80003910058040080412801c0b0030951031615142c851102c0c0d0070340c0103960062007031201c2c2c8031404c0310799901c5a040b64141544515007a41050103810050700800d0126000e00152252411450140c03501c400c4101c3c00140483c0114a858104014040100340743c0e08201d80140300394a00081000c4180080c02c8203c0302580c000402e60300c0c013180c003400c0d01c10140c01850020b02040703014020481c0401e07001d0320103c9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 926186636 1250 926185386 926185399
    0x50306150402120a0b040c08071709100c0519080103050715021e0d03150b090d110d05030310050613090510091b020c060c0d11031611130c020705 64
    0x16403001c24080c0c0f00b043d03041d42c00302c03100c1c3c000c11003a44015880032140c0c400a94080010700b001520964840c90290b440001044000700c0f48840207076038001d51688868000c081d5080750000550304015510440c0c40c0c034010810220303045c503c16030312040c16074421503945810320580d455034507195100d58141c0203501a00b41d1115104196500030007a500e026407502e4010164520509101620313450007480080000b41070007000e20b0040e00c0c1c0c0000400741c404013940140b400c000001003041c0000740c400301710b41e80d400411003260103956a88070310942e14021805150f603450003006c0002280d041c0c3c1c0200d8400c030400d01020501d070804201c001c0c244c2e04d1103103000036213440b054084240742c040d41d88001c0c801800c0669003103c1503002040716056a22035003c0b1600080c0700070801000f400751900785c0c483d55001c0c08925004521500850540500100641e07241401250841c581010214800d5501000c1d031500310044ac104800d00c4083c011103100c08104031002180003d480d504203101c5c01e4868103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 926187886 1250 926186636 926186671
    0x15072003160302010f0e0f060a020c04060f170109080d0b0f0a06050a02120403050d0e060717040e060d0201020a0212030d0501090f05060a03080904020a122310050306 73
    0x90102010428500808503444410328402941c03200c5501d0100701d0001e000b0310081e84001d07029482510100790014860020b1109034402d000e415003104840800714401c0715007400680e280c610950000d0420140d9501c074580c14010b80b80113041c410180955607a241c22041c0011540701800d40e606040c14590100341d82c800d410005a9900740d041a040c0d02c0051440001402500f060050032507007441d8080c0c800610220318600300d140603078440a481500000f07960304e400c0388116148542280003d100904086064079142e66041b0b5821111003440b00019052000105210095600035012554031000d00300c1640002d40741d040006000340140101c0d41c103140c498a040c400d5490902c4c445d0020403c0e03694a540c050003410800b17000e041b5840c034050101d038003400c00e1540d00381aa50004c480c185404601c00070b1100039444101403100308100903540165a44503030141811040380f0b50683c61600342c9080c074070030204401900c00a4070302d907080302c00c00a50300c01169140d40810f2203284643c540 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 926189136 1250 926187886 926187923
    0x20f0310060f052b0b090f040209100e040609051e01020403050c1e19170105180c090f0a0207021509280b1b06010f0f0506070c1401140a03020901030b1507 68
    0x10100c17806003a901c104600b0070000c1c8180b0304d51001b485075008498013001903c80b2020506080c000e40034500080c00503100040200d02c1e240c000410b69031140b0700b1284201000204c00054080801d2210450794002604100380403080007070322805c4600711350100c1b54400d20205e000d0900160b4486034001c501c0340f2500076002851030081e81c010241c8820043e071151042c00018020310040384c094101422400d030700351140c140040d91500c1150003500c41c40e081e80703a103000c010458a0040c605c01d50700da002c220b66001611a42465003100700e00745080ba031190301027402c0007251090303076400c1890b4040710704030109600364043c0c440d0100d600d0740160342d503240134035114030003070950922617118284140380c000151041070050800031219025010411181c9039020084184150903000c1c261032030f40f503414400002c142681034031b4039905042110b03200520f080c8108258004d00b40c400d021950100f0340d4a850758150103440c45030a4100d0780004060076440c42c00d0258007070003401400003402182035003031342d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 926190386 1250 926189136 926189141
    0x6050f0418080d091e020f011b050313081005061c03020703060911090106030c09270507111204080a2402030f071706090c0d020f0310060f052b 63
    0x8060700941030540c1d4502003901c841c083c04180c0c2c01103c6a5900a45c120720100e03039140c0391003202c1d9004100d8113558044400442c1d81503031070301400702441c0da100c80000008030100020000c058031000c0c409201803400e040103003440007501404451070304110821001d0b6444001820001d03c0307803000b0a4000c505400e00724608201c91b00010245442c0a6100d0188050000c6803034400383c007102d21180b280e8a03a001101075134a10400324010034101301080c001440c407404181d81500900000500c210142e51160080c1c400542d42c1d24041941e8400c16022500144040a845000b9850b024603181c81c0c444440d40c1c41c0340403400633103225406441880c0c4205d010f01c0b001c04042001c0c80954890600140e6210101d000340c5180002c2009900903003c080940851548101c01c0102010001c2c0c1d00c00e0002c20042e409101c0d020702403036081106900c0804130b140918080c148094821158606011020345000c00342c00003481030010910140d034818102d80761042e001550404035011440f00ca20101c8003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 926191636 1250 926190386 926190431
    0x6040c0909050a02090901050a0b0f031b070609060513030c0b220804080c090c070212120408010605281a1b010207060515010504030204150302041103160306050f04 72
    0x9080e040005002107800030380c011700302030351048030513183e0740e641c3d030081060118061241c010088402c0c003551580340f071450040e40d4001c14032504580f41d41645001c0e00c03101e030b0144c10115071940c3d491030f94000b4441c503440344941c0704010030344900c2240002e0b10007a004290404009091104c08000180f51b41c80c03001c004642c0075804450300d51050420302d0503800380e400c580186a49442050320043c180d1801c80c00b114080d8442c6540c10340b9200240c1c09110001110f804000c2051144100195408400100400c000e00307500000044c9a400c040070080e090701d1107000464405118072103a0020302d54994504e08540f400805c9015403103402490303d00034003e0b40155462404c2500030f0907800001900108040740c49054100516528048411001c00c11224034500013102440240014107090b03124142c580c960021005050b6a80c9d030002e01900e003000b4206142200220610001c00e4120200300b040c1700481c1010b2000030705000108240c01c0e4201c079882e110b25200c220440304250341c1011040d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 926192886 1250 926191636 926191649
    0x131511092103040314010509010915020307020a170a110111160c0302040c030606020f1204050f15340209280501060e010f020105010f0905040c080304090b010306091406040c09 77
    0x39102c2c1e940303082140c0381001005c000c603065406c000001d42010390611915607038030307801204100142d1038400364000a40005240300150301c2591880000f090403821103151562021301e03132a0f51603000400040c00e440410070051190380c10441144540c04071a019220b20b60043e00c02d68110752814144016250010b6201940040c42d203500f544005606d80c0014041d14096021911007030461208107655115030400611042000e2000344120700c0d00b50380d90780c04a60003c08103c2c0003030602c1d401452551028416040303800c2d001c0004000c01003d1346194481114a000c02000c1e00c010b9004181d40c420001c19490100c042030451032824200000c00d50224042034030100007540e1145002350903a50640e604130702081207907064074086881402090b0617102081090010185017002200107458054411604100740003c04036080c80104083e1008181d02480420104101400981150419081468140d00b000074008207000707aa181942c2241e4117540c0081c050a1740ca104031130030030781508080e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 926194136 1250 926192886 926192893
    0x4150b0906190c0605070e0915040f0f0e06100e0a05071b1103060c0a090909050c1f0810050f010c0203100617010c020c09190f051315110921 62
    0x90604030b50044180c3c41c8540f02d05000c024648505c203003030b1100020780c180320303074402d5810780000e4000d14096441c25220101410129101d018501c01000741c888229464a80c666111700b82e168030f5004100160b00081e1080c80006041d080c020071082c8a20003c1210038040c2c1c89001241089219508502c080300e10200c426401c4075942c030382080c19501c003e1445100307200300008612121b00341400c45540080b0380d1903d801c082d00e8004c060015214081042c4d07860300071001550400c2c0c0740e007101a0360915081003a4000d4120221b8060300f40600542428003001407800305001076252108103000d004000d0030500101d01161000034a0042404042015582400070005100055008038111091550000d2182520716203040703030b46041c02040316500c25440001316105c2d4000020501b0915503204010505000d001039903010340c0c3d4140d4019111003c41c07a00b81003400142c405185000c0030344072003489000211004041c0b640150301a81d44140300d04048108600c203540c185190940391242035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 926195386 1250 926194136 926194177
    0x180c0405061612021204060e0a050402030f0a06090207110919020c0a0302190b160201091a04051615050c1f0506030d02010c090e15150d0b04150b0906 66
    0x51000035030380d002c044402402044506400e00c2c0085030f00f1a50740c8200118a0519145c01803c440c0d800b801c90350b654010b40941c10205040d15140011807040b40700d00c8441c101c6082a001c00c9045549561040306100e10602035000000c1c0034804003401c4038070803948041d007a00c5540c0c3c0c034501c07120604486100f4030b01c001004a0040c0700455280106802a001c1c0d0340d10800100300e01102c00000d4000510148046002035855520100454450700c580d100000b00c0744102c0d50340c0b0346c100d032818100d0a16409a101000f04228040041c40d40b90010141070140c241d00d8085440103050f0807040303910074402c0118050b090a034041001514038820000501c131040030810f10240107210942c0c40c64028000c940b5800c1c0c1441c01402040402129551222902443c014820104c1e04000d002403030001d03d0204480d58541d1043d0b1501c01d9030513483c50665480c190203041d5001c491100e40868001c40c1400001c0440045400c5034404841c09229003c0e5903400c1e1200207a01071040f001083c4222048864 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 926196636 1250 926195386 926195407
    0x40902031510180f0e0112140a050618010905100b03010b0d121b03020706120e0f10050114060306150705061005130b1003090302014106180c040506 65
    0x3643d05400400c03200750420719490700000c1007400194090701045680e09001041400907885c224210217003d980c003504402c2c451058a41003065181042d0360030b0340305100b8061013039510b1421890200e0068020800341da181d940349601e910004080c441000c2e5240c1c00070000361029080503c0304c8400500d0000b0390311141c6080d0b50301c101c480e1050300c002440d854140d1124800300745144501a0180c00801501d071030218111080c0b2461054501050388440c1c030301c1c01003501040000a0000d0b08000741c00703008080083e880488505038008941c0707a10a03450f1610940b91001200c0e0009801d0742c1076901d1480800c40b07202d4600c2088030082c02445401c1c1001f0f642094000d8007810790b01e0480390b40b1400410b401004040d2403040a429a03c1002540c0c0411028000e521442c42c548c824000800d100b00354903400581d01c000000b291680214511618a0b071070420034410608640204500c10b090030000d01207840e50212844400c443c03c00030340880c01e4807201d442510000c1c44010701c42c603a01c141100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 926197886 1250 926196636 926196647
    0x4231f020c0d180b090a0509040305070203010b1c080f04030c0602060114150a110f0102030106050d050105120c13180c060f020601050915040e030c0a1214040902031510 74
    0xc410350814001c0004424070148284101800003030f002103034250b4942848490700c0541d11080c0360326405a010714000629484407014588202c0c02520b556072681b2442c0141070965074801a81440b560700920b6030a05520509015108070350050140c40c0c0782d1038903a4070760020b449150005010441282000918103600240780ca0682d00340c12038030980340c0001014412601700310a0412042c02048c420200510f220750b18040c0d0840300d0310101c4a00184041040d4222b80c001c0c0c1050001039800200015803450f00d01034140102001e841c1d04501010380101030b52106c0300c5846070391261000d0204083d100890340c1120105490a900c02d00500101e0714244610b00c0c3c3c248030fa20042103110300f13490f43c400d002064582c12140060215003559807124003001003c0d05500382258840d82d0761000c80201582040609151400d044c0145226005414018110340c80d01681004101c4110024540f11014505480441c6c44954000d038884d15804103400c0c000320864802c81c1c10119021b044035036241d200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 926199136 1250 926197886 926197897
    0x1e050d140c2d01051b0f0912060106030b12030d0e0a05010606090f080f07030809061c0501030203161a03220f03080109151a0f071a0a020304231f02 65
    0xe0078121a8190000585070907101304458a10154804803c0c15103189025001400306489801d032044c81c0200800005105c41b1110359141090351100006100b21034043c40f441c200c0c0c0c00d046614500001410904541c1c0b880b801109400c4962a492450450300d4104403401100758004001c2c05221307150900207004c0b94082c46420a0a454448001407a8002003140029008400043e02c801401c3da00c0c2d000700c941c4421502604110100010b44c900740d030850019400880c0d551000c54107502d540101440c0c581d924440416400a85404011030244003452444803007007414520340b01d40d5030080c01640c1545182e0181151004a0b0314107003003012a142c0d0b000100d00c251144c65490f6221807050088803444c0854035031160340c100c4188600d40003070842d85ca0782e103412101e452410b08c1020390711a454003d80e82c00c541002c0146407120829000b16040c2d580b002c0300711411402d41c68143c80b95041c910081c0d500c00302080e02585004400c0c0f0042c054540505d841540c040799001c18500788000940c080c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 926200386 1250 926199136 926199193
    0x90b1519030818010e0915060417031b0f15040501090f03020c01030615270519090e01020319020703090306020319050f16080c09040c0302071e050d140c 67
    0x180410340030b190f000f03a00e031a40780b0101a10381d0301e540d0342e11041401d03035035100e0009039448023050000081200c1640d40b400012802e4101a649071040a410381000102241c3c41e40803d400c0303640f00007080c1e100001c6640c246030702003880d002151203508015004154441c4003078000740e0a043d038001416000030303d00d00c0b010000c0e070342000280e68500800a03e10f0703040e000e182c0050590b4610001205086500e96035200132011400030036176032200040e070160745800414050180700d00e02040045903511951880401c400029440d614022030001c107000c65152103404d0a80c1e01084401c00d0502c908034807400303954454400c5580b410b103034a202080e03a20240ca5001814102070006011307607100d001d0305004040c04802542c81c02c4a90006880c041002403820f0040706d018004244583d40303900038010303a002c0036140147d9804840c01c094449155034100140d008030542d03620000210300103101c1282010700d190481d5011410b0780c18011a104a5110301d9081c85020070200000c0291541c10004500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 926201636 1250 926200386 926200417
    0x11011b080a0507090b07030e0a08240601021002250303052202030a03030b121504140f0a030f05040509090f061e0a0b0a030f2301090b15190308 63
    0xc030341e11114251281116104002401540b00f040041208030141400034800e040008440c00c0303d038081241c89806a000400780e40c4601030700c02100b000286040c80e1b0701703800ca401c40c01502d81480041e60b11500803604030001a4009041030b000707141e526200032426204180d0115240315400c0c0140940020b907141d100e441c82900652100740707d090700700c10003280d002e4041c00c4400d9180c0c405800030074481c0307600c0707401840035400a10341810611081e8800d4041850100700c43c1000c4c01c00e02101098000c15131000c1d0721907603001d0740702c0e20001201007006526240064026108402c22502401298020b03034101c50030000b84001820013082000d80800a131007211400d0743d4034004409008a01c05d1601e005005203c04039070224080d4104854091001e400308c030b1500da899a0b414890380c1c0c10388080e1400c55641480c201ca0600341c5c09040440f525080003803000040b01d490340c441c811000b402a00c2400003051070356020391036403240100d1003c10744c2041d0840540d20304080032964000e00c1c01060900 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 926202886 1250 926201636 926201641
    0x10b010507110904020402091c050115050102060f09010e03070c18050c0f0c01230406110f180a1509080606011809091b090b030c0603042111011b08 65
    0x521820541e038085822a030360030a44210a828099403841c060800da81168007003007000081d481d902d03d200403034465603005412400d0281401801c5a1441c419040300046514040120303a90003e6000d0b088004101d400580b41c45a0038000d00400a0808516031400301061000620848103075035400c6510841c00103100c17251521071003040b141c003101c2c0031040074010b01c0b010b1500d401c99400b9040417003280d400021000d4040d03101c40003509001c185c1680251800c400c1000700726160042e110070382c0d041e00f0305a040c48000c40ca01203043c014443c006940c811290199841c0341d9400319084014682a442041c0c0c50f003500f1001024542d850040f0a4240f00f00c81c00f0560170b5114911803a10308582a19001c44c072070070304171044080c1c181d4134020380c1e106a90000f206605a01c08041900a02002600207140503000050605120103464007506c03825050041001142404a41400b4100411801141202030000c251104000d8040b594159031031708014180e500650000000510001d4551801c0c95 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 926204136 1250 926202886 926202889
    0x12009010210050c030403120902030106030818010f02031c090c09020723120a0c02041505010908120a030c0216030c180227010311130e0708071e0c0501020c0d02010b 73
    0x461044c1c400399510f0703804000040102e44140303034001d0303640c80a420114650906800103800d60314240c10903190034100041080001c0001042d0752810300080c200665001d100c1d410194a03401200c24246890090366004154100c8650007a0446030f4011064107680d0f4850054000075000719100319140ca41021000740d4a0299821060000603810010011003584100b03c2d1003a030045e400c00014004000ca4000059503613025401c00100344601a0840f28039101c0010803401540e40108080e030031905e110581c84040800319030b151800e07030502152540754940c007245414403112000365a9000b01c00d0100400484120300011a00703030740b0755007180c0d00e08848840201e00c544240140005e9900414200700b1142c40c40f40020074605060010760301002e240741203607651141c44002c3c050300903c4400d01009000c0c0c0ca120b500804280fa2031030440c601010080d1060320003c001140e2401602c568048140c8179064001d116688200295201c4800764550f030740c3c91000c1d4000c00003550030f1022010b0035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 926205386 1250 926204136 926204141
    0x80f06060913060c2c03010b041a04111209010209091005031b281802090306190f09060902030705150a12021201030308040b0c0a0509060c012009010210 67
    0x144a40d000101c070381c00c00320394494000f401d07198600c0c8280442001040021300f028030355800a01c3c842081700080c00700240415003141c40d000c43c0140b1543c03502c01c402d8403074181032112285403175094400017480c00d288091446c1c03e003d1b41d010a00c9406081d8200039405c0c0c0b042d009800000001c1d21081415100c210111160b031110340078460b0582c5c0301c0b080307100202c00c0c0c10801621074907010b4106005442080c2c82c1e040e44203120302c40e0210410a00004124110380841e22155100007014118106001d550010343c0303400c0040c00e480c0783c40041c202100150a0031b40d00449803104400d90810000c043c0d49031403405400e407504c01383d210780580000002c203400d010320b42c2031580000508003032410050300790030b036000d005440d51682019801c1c0204070702c04094031354180c042c500030f8840107420304e4249480c2c000100010001c00310004180032620a1031381000a403000b61070111003460312440d4419260340100a18018014661400f0009680ba080010010060f050082e82612910308128110704103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 926206636 1250 926205386 926205391
    0x10f09060b03150409061409010e07090e0309090a2c1011040918050307030e030714090402040504030e03011e0c032901170a020a090608070c06200301080f060609 71
    0x3c0d52050b4808040b80781c15032040341094403030100000c103200300e0401103019240446117046280c0d52a0440c00b0103002c104401c0005100c2c8020502c01142d4080310340381c0300e024002c02c16000c1c00000f404107004103c039400c407015036802464820b806c0900d094800c0300e080c40707600141b0f41c0c07806842000001e02a8a014804002c0d54041145141ca0300d0209942c000740351482950160840b03000e007010000d5001c0c80145800b070700990b10219031005840c10103017041e000394800030002ea54580c2c13503070164440602003035001c0e030102c8002641d596141401d44080c07405199443d8103501c2c0100c02c2003d41d0703c04540d0700041d22130640802000044250a034200d400003099118407500c0180504c110343c08c1c1182100b0703402018500322600203000709941d48640819103080600a80114510301ca1940c044034040081905103404000307801d01202c05021400300b940701178005910f0700d0a01283e00186610740101d5401255403e030f50b9a5240a9580c5948280c6050b10046c02018089552450690031207030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 926207886 1250 926206636 926206651
    0x12090114070e0a0b161a0901051f03030e0a05060c0d09050f03030706020904021207020619020a08072307031706090603100507090e15150a0e0d020301090b010f09060b03 74
    0x20645400c0c06002e074003a070040401080705e11100105100017803548040b1040080011207800a035040130080682521070041ca043e000141070015440305207103c1408004494150a041c00700c0c440e0f42002c903490480c81d400c0250005000541049168000524840d003940300d5a60b0030260b549031001c0102c800d031030701203582e8540d10511a12010a11540c000e01e00484001d10061414501c4a8450f0725408110b80d268056009441040300e0310804024403070748a842c42c40c04600e04445100007420b00704010340402e080000050080c84460612082e28090950b600c038101c2e11820b5502c1c000f000c081c401c050340381d510341ca501b000c50a54100600603a0041800a024081d01c0c11104428401044002c0140d820407600c0000012041d80e0745034018001c0e581c031440300c4860011802030010000b9456000b2400034410040c194115602801014544034111080702c21b0010740d0001a0140926500c054603514049c3c0001850404956215046415900303081c40519519040300c00c1c14041140c012 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 926209136 1250 926207886 926207899
    0x30607021203060f12060703050c03040804092d02040f05030f1c0516031e080103020906010c0c09020a03020301050112060e060f030f0109050102090a090b031e0312090114070e 77
    0x3102076111030001d140e00400103042c03816102d01e01d0000030800c445050850300d16030404410f20040e1a45030246035440071189011914505203070361042d2040c440c610a032070341c4c6959102005a0401c20020082d03613240001013001c12241d001070914020344c442d100343c2d04038036403180d0001428100800c0851042c01d0032009811920303103601401c03041d8050b04a41c441003103400c00682100201c842d20328240c0d540665224880014404040c032204881466074509004000004000580d01c0c40d610b12380c045000e01e400c008030001440e000c046442150891404035002089070040c0f564190301860403540241d84440007600c00342c00b41000c650982c0140c4002552210000341f0900300003090b07031024003020341110103540d8410b252a08496020404a03a20703500043c03844c2080c0380080b0954050030f8202010000d030544240026510031540340449603a1a1000803c031981c0c40500954081c550760101c020aa0301e00310719051f00902542c5003940b0503ca40d64040b0b01200d11552052030340e031001400c038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 926210386 1250 926209136 926209153
    0xb030c03060121060f02040f091a010f11031204120507110616060207031d0307080703060510031a0406050c0901020d0c11060403060b033d1d0a060b03060702 69
    0x30803c65142d05101400e81011403540c3c800640c0621500060f40e16010340142c44030f05003d8020300340318465020201050030048043d030181c0080d0301c2c25201039800d0030b16600c508688102a2144e80000240f07210600004c0740c0c05800c1c10840304540c0c403541c803a0000c458020aa030030151864007400318060000e24112402c12102d09041000346000b103070040c00b040760310009682d403201b030f6880010200c1c00200d8000684821006503281c0c4104000100c014000050074524820366401c103a200103424940c0301c001181184070340318240d4002d150070000007030006400d5a85d0450200c0306039400c464913450031b00000c0021030400103a032202007050340608183c402c0c600080306c07001544081501e1080e491091184c5039555180200001d5106041c007080c45451001050708000c10302010300500702c0c00011500b038540400d0460554600207941d00140c0daa00381c07101e03000400b40c00703246030b0840d4843c1011500c1000d0010b03402c00124840d032400d01c0781410b4031081c1030710342ea8103491020259015050307 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 926211636 1250 926210386 926210399
    0xb01060305090c060f1315020d03020304021c030809060c1201030201051309020d290d2628020703080412060b0306250903080f0304020d02030109150b030c030601 71
    0xc61034000310607a040340e2100010720006941a8000c5c601c4681d60700340082e09a4038000c241c050100101588000e203018580e105902a440d181004a00e50415900000040855940f041042076030701c901c49228500014a2030080e213180c5003980c400360b45105000c0003c5045010340115050075190040c1025107918590054400d900010410500380d0744c0c0c1e001c081598440c52014110f010045000824098480c0360a0018500c40740403040507851403903081100b42c2c0301d11444182159200414035039040e031240c240d01c40342d04081c021003500140040c3c03c40c440300450702894141c50300301c0604158544040c0007aa41c0e4030321880010004d403020311080101980741c00354a83c0d6a17010b00c0c004141c0e96a0200000d003009012511410301d91004074200710303000018800c4000075100f50400420640c1551101103040c041c42510f0038011200000050454a400b4200707a035656014000380724082042c03800c0150241001e00d803107040c030315100c41e0422501d0700003100150084040e02905c49a401c298 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 926212886 1250 926211636 926211641
    0x11202120309031507091d070807020f0712020f1c03030c05070203011407081e0402041a0d0c0519030f02040917040602030310050103060803093007080c030a0b010603 73
    0x1806480c80c0000e01c481c0030140c400b0b014a800001a00205001510f80340382d01401c0310145d40c02645a0640d00300786102c41e0300f00c802c0000d40100b09820300000a41d15210100d02c1c2071a0710700064082d000342da000161140318180d0346c0e0341c490704c01c4a4801f445020380040c04010a840780c070b0403c2c1d00c800c100c0710301c0c0402e0096010010b2040c1c0362070260326000d0b0315000710342569582d00103440705094a0f410018880d501c9240c031a04180d5580298025418415610341e041c8070162000c0c0c41603607940c0340010f0940070082011406072000e066101c0c04201c030b080c44501004e244c41143e0084c00c01d1800405082604401541900c3c2d00c020424081c000d15000e00c8020001200d007103c00304412075810600c0511400507000400c2541d00556070ba07c1c201c1c400d0b81000009070b10950500d41401001c4c0820f14000c4103490512005881c08000c0da054120110894a2811900d071500003000c0e100308262017022582d04155130004007180c50b03940c00782d02419a41e078003894014007400c1da418010301c80da034409e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 926214136 1250 926212886 926212909
    0x703020303250e0d0602130305070e07020a0201020601151e1d0609011b050c0612040c05190b0c0c0402130501080c030c0708070602281e2715030c021005011202 70
    0x4007401403e004140810060584223500145c803140d00c00b000401203060b2808003560700c800c9900c080c1880c139040c0e80c0042d6440006000d40c084408125401408141c800c4e4000c12141c1d00200c4c82c2c07240b00070102d20141c0304804102040f8050668110101d10302d090160851740c0e0349406a54100001c0e0a0503c0d1000b180c107106000c0b5000d0080804101490f91220050320035000903000306545810140303403010380c02e01c05034440c500a49241d440202601e00300241541240c20311545155104c40400c3e4190404038610340150f405840491070008c0c801c0c0d80748051058032002e0b00c0c0c19110f621407220741d1209000071103000e01141c0003000783c00d00280d52840a807005921030380c3e000d4103110b0707041080f0032886041961703409400c91800854000c81c0d4813142d805100a4491502e14541050640040084501c000c80144107144030440c0d95070b603484080136030f00520542c0940358182c0b4031482c1c0107024140c0b21b0590030044c46140000d103003c094500c40c0034100c1e0100014521410013035401e005494100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 926215386 1250 926214136 926214143
    0x17120306040f0906110a08100b03040f11100801090f060f060f050408070617160806060306030f071e0506030106050702131103040c08070801020c070905040c0b0703020303250e0d 78
    0x482c0d00b8440060114092210b031700c000e0000e4251100d815200040c0000b000404464400030031031810441ea10b80c001c11203030041c0e0001d00e41c1d4415942801c280d40441c41040100340c001c04510f41d00c08080e40c1c000c81c03c0d41642c00c0340c2814000610310640d4201512800d004080064050342410440d850040442909142d03181c1402c23402c1c50703555805181824000d51040d40070501ca004c926282241a103031035640300c214030807a00d40c0c0f0a0700c00da0007402000004d01d124000c484c0000810f481da9010030000f2141c41c12201107689540d203418a004500c49003c8120b4079030304502d20b0100d110328004041c0c0e81030721040e0f03503214145036554082140e507044400700e016209a483c030140501d12440ca0046105030f00840400203028901035001e41341a4460748074005592043c407050b0311811010903000d0468442c001c001c185e648031814122204403c90348020720f007400c0050000101600440030b1440752510403942160440500c88060040203002200c100040210700002407034a8a0007040318090301 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 926216636 1250 926215386 926215391
    0x90106090b0d0b130204230411041b0c051002040801141503150a110f13050301060506070f060e0d0804030e031204060807230c011a030c15070210030617120306040f 72
    0x142070310490821664152587c4503644200300b0070060207516807000305120815102000080b0326407007072407e01d24405003400d082102d113600c40401d0000c2041064207442c1c103c0b40441d0703110b6a50707803128000d26490782c4051400c8081400606003040541c40a60707640c0008d0061311804501114a1201200c01041c281080c0d50781c0c9800183c0a140c030002e000240d8444044c0c569519400030000b10034041d03540414880c0c1e041810901c0385461b5102900c820640c800d02c40751160003d40b600c40050100d401e141d40e02445550601c140865220100c80e006034025110140104001018103071035004201e405980c4e28001c000030042c26109500095000080d40780c0029251303000003e0008280306014041c140c039602240c0301c0100340c401c0c803900c41801002480c2d000c04561840110f6100c0c1c01d0940014070407000d04501454103110f5000703c1c0c58490303000300803c1c181414094050020020303400f8440c14480005a1614209400180101c001c001c0017185070039070355880200300107000012000902141c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 926217886 1250 926216636 926216651
    0x80c060c01200a1d030c060705010b13090b07090303050712170907080709051303030b1c080a120902091605040e0a0b091b190e09090106090b0d0b130204 67
    0x1d120385a000b03103080900b6241e50b5500d0b041680100079040d1311814018078295030305075500a9600117400c00b5640d034151502600d038512403d201e40101070701c9180c0c94004050303145001d207655141d440709690903c14584100306e40c41d0200121607500440c08002d002c99410845078001c1071103842003416005840c40c1100748010b14105944140b44250340403002e950007070005010501c02401500e02909019000308214a00004603c81241724400017406165560048800d55110040700180c8500200c12800e0130321610301d455009980b001601c100020b094901ca03074002030b4680075004c00030350000c050900c240c44010799080fa80d804402c0c1101800300404c0700062090203800d007503104004101c03001039480b43c890b0a014242d4001081d607040d04000e036854100915240b816501c270303032051110541c0c24541001d000d903960240c00501c030764064400700800c41044015002401941c9849106000c180c07142c0301400b4071865840030007003c40c11180e0014003203600c541e0f45211080e00007000455580c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 926219136 1250 926217886 926217911
    0xb07080a020f0a081614041505040807080a030206070333050409080d0c080c03040b070201090602040b09130203090d0c170a020a03080f1014180c180a080c060c01 71
    0x142d000443c03010100343c0c00301c00c00070350b1844040401005036150034a01d540c8150409268280d11503805801c60580300e8504410703501d803084094030040c1c40710703030111418180c0701d0030415550424040110010b110300d40000d11258420b00440440c4e20320440c0090b030011490100d200d80d40383e41c1e41b204500074034200000401c3d9445000c1c94207103a000e410403036910400300d0020010380b0000c0500e40b0030b101c151070510040e01c15420840b580142c000d104002503803a1120102e02400a1f400040e20040c00818003180d10520403004252550007103442e00c01001040003648141e020403202e2901c65085a0740e50580c1e64011603803081ca440c814034850381c03e100d40004c8501240c11011428005170700c50500300c3c04040d08080070f5034002c00901000d030f41e80d280c0100150b4542c2004c1c0104034881481c190549026120580358148400c005211050799241ca000d4020441d0081403c20741008000c1c10300c030841d41072071341c02807095440100141000c4486101405540d80c4803283c4865559601d2420b100c05 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 926220386 1250 926219136 926219167
    0x2090103110313020307080309030d0c140706030e060a050103050d120b1504031a0f130807351303080a09150807030c020d0e01270e0105030f0303040b07080a02 70
    0x2e010000c074041a43e2035034018185040142d40180007550300c01c001a490503540040c0070f2008807400d00e4030302840e80340c174580710f41017980038580069217100e50180800c03a26015004200e509941a085401c01d40d65814a1426140c0a10000d000c60300010700c04402144036610500c080c2e4031038140450700700803200100b10055031181000140302e0010805100304980b00b031805601110104606419007400c0201401070040507244040352208808103008001c14102a5040be94000994600032102100341641010800c01179640507148515074041d5104880113542010440203000001181165507100c2d09a00191101d010301c08041000030b40b49110034005141c1c0800c590342c00039641818200036064514030000c038800d64004411900640f0382c4940d8400901300d00f440e200c2c3c44854110a0a0140c1d06144143e0551008020700481c03088490112203040307400590880f451501852070298503400145d030018035200c1c400c00410380396071140104580103100f80c2001031a081c1996916800d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 926221636 1250 926220386 926220391
    0x100302041104080a060912020d080a0203040c08011404060b22020901030b120c010806010e0d262a01060b0a080601020c090f0f10180504060902031e0106090606080703020901031103 79
    0x40c3c51b0703280c500080402456040800c2c2d40e05290001b041c11140210f03014100d282d00904074011264040005402d214540910900409034132008001002940c900038030b41d103208440a0b00c6650400251455504040011908030b020749109a8070441e1000124030181d0b012141c1c1c0d9040540703514104216558000300403d2201b0f003c4000e00181030320000150a41c840100b0b100e0500640c2c4080c1011601d40100d0331540d01c0d4800311503100e9407041481900e00c414030725203250100ba000f0585656007001c01084003190070040e03218561100f48a10445d00344c2c0c000d800790101000003403110207415805016120f400c510140151a240c14640001c00ca07102c108448070f2030300620b20710034080c2c8101d0084d1242d0700020800760aa03c0075080504403100046078141c400c641c15580d000240510015500124800703070b000f41518000e082412a0f0500308811402d850300c41d501e020400500344c68903208100403220f66481c1c50109076581d20041c0c00940080ca01141419201e031219900a0303ea80300441c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 926222886 1250 926221636 926221643
    0x40605180328050c0603060f01050d060b03132607241a120106050f0607170d0902030d03020c06040b0603013b0c030304270609050a05090105100302041104080a 70
    0x20195811814104d1a00c00c000400754042d41d000c0043c00141d03112901c1e424816102030800d00d0b940c210708420311004100c06d45c003c5e08a244007005001c0c002088600c184e000c14058070040e00721030014003c100d40c682a0011f040b944440c01c01004000940a000c00b06004100c00c1da00b0704007803058440c2c04240c9812280b440c10100d13480941c26481e181144a0703005451100c0002c000e61410140407540300440424840c0c442d1307102052000030048a0081c0c0c0c4100c450090310691a0340740410500050600e003a4124031034010409048000751080c0700340e03036040c03680800500c1641c5503904d0f640050300001d400c0c0360b01552a084039131107181c070b1684100710b00700791610007980380300910f01e605490300322200c203444d030079000308410f13061030307600081910282c2da1014624044455001000725442c0c3e003070b440451b807050a020002600e030016a2000b80b00708030501e014041607644081407800c8803422075005510341c400c400140054180740e032010320741c3c801d200c1089140c242ca89080c2c9140c05080501103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 926224136 1250 926222886 926222953
    0xf16051e1207181d0f150603161e0e04111c020910080c01090b0f0f1b07140a03150c0e15090423041410020409050f09030406051803 58
    0x12084c021100c244801c00f240030b901400d050344030700f24182d8590102070080e44001c0c41c19804643c01e40c5d42841510500008903640400c1380e03503207003c007000c20030742d08103106804100f1600014030011030010f4903100369801030001e030080c4c0341d5608218050b41c000a1101285180c10900c0740142c98200c0c105009814101200030074a103040c10241c81c250070b04c06000e0421050410030421001d0309000e03903c1d10100480307210740750000d80700c07848014003e1010484074160340104004840c4408200308041d2440700e08604030310f40c10700007130081c04502840018101107400018100e118559403000910301c851785405040c44020400007030303203060440c16030311003640006000c001c00d00d081d104003690031802e4010131b6504c52100070104010400180007408005001812000c085014000c48031450780405c0c046465580f40c2a00c0310044c401152800b641070341240c081801c0c0d00d000010780d412680503549581c6001e03e0704003805580b0b000a200340b03415110f00c12526610001c070030421401c60703000d01e804 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 926225386 1250 926224136 926224151
    0x6060203160825065c0304080421020906091005031b03011b020a02100302040b0d02040302270105120c120607090f0302060406031d0f16051e120718 65
    0x200c00c55805041c4c20030b41505641c4d440d0280c2d400c1d110903140b58001400d0b178107040c00b4416842001102c0e550729a422407505001081008108000c0c0c081c00541d5550385525102c01140030310030605000c038000107540f080540e4000355591400c0090250700040d2116071844580d030b076a001c24600003410018418000b15900204e8103800e092043d4003404c80914950141300c03007900000394454103610f101a0080c83c05a0b0034440c035500030380480e4000d082c0d91700740e1079035004080c4c841c600941013030001724401c524440d00b10230703283e81c410300515480094050081a5074079103810440c103107090b00300b002141c1c043d10301405c00f10381e1340c101201001c081c1c41002d011146010200101010303aa600160390140c03c0b00001e20258503041c040d00c044d10700a0400181032800c007400b41155002246170321001d8450304003460000040070841842c8040d0190380100c407103403141c0411101c0e00c8429040c008145400d040210a40360800e1f4040820140206071140c050322894021061503204031403400ba140c0b0703000e4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 926226636 1250 926225386 926225411
    0x20a02010c05040b0a03020304020d0b01060804170309100209031e030304170c0c060d0f0e1501140303091c051608060105010305040308071107081501090606020316082506 75
    0x41c6062841040c80c000d40f4060070806504a40e001d0b580c4200c01309903022002508640300c104041d400540c01c81000b010941e52450f008000200403241180d0034020f039075105140414160a8a004085500c01f030a80c4051241c41d01009422140c0030f507a0510640e52201c0d0704491421001c040d0000e06806545c5d00e140c2030030107075040184541008442c000400ca1950340c05e5000c201c0305090f0400711800c6a50b000401c841c02c020304040494110103a25202c46025400700000d44519201240900c02e41c2c030b60f07a90382503c1e60100141c66a540c05400400c4210124940f0f9526074281d80a0024200e18002594442d117240003085d03d02403156403c1008203015400c0c0070082640107020920b024000707842c01d41d5009100725400740c110340900c00e40e044150380ba11001c0c02904c2c05403106604841c1c64240481c4031600408003031080400003460070b007000c01d2480c8044225004c0d41c20030140c004920b400e0f0740e18581c1d242d00440e030030640c2d8013051548a003505001002c9183d01c900a80001c680c3c03e03403190 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 926227886 1250 926226636 926226641
    0x60d05060f0f0d060c0e0a140909010b03071206110408100b0306060d0803040c0312030b01171003080a050c0a0c0503061303140f0903100606170c0f09030f07030501020a0201 76
    0x211054461031400c0b182e16416510f640d00c41038450341c05200814162000705064a04940e640449940942014000b00300407940c80205106200c04075400ea045807030b95141c142c22281003068280c0c00d50460300003404000d90f0301c012601c085219610016980d03103840e88525032a0415040b50841d41c011141d10088901c450158003070605040700900428180040040d90780c9000d820000c050742e0b000301c001400d1250500b02c0100a5402c0380c0181c0004251440084c0200404500341d0702152090742141c0c80e513000711505901c00d0304004100c0f1030b9103040d0380741c403403040c2c020031f92a0082207002c01c260b0340c680106004d284241440344804031741045c1460105810210700600040401702c0402c9040d0209a2200440048a400d2041c00b44e603110080100e12a601c6211480d0782c05101e43c1c00492030070078560707108000b112000d1f42c0d40c4060314028072404443c1142900c2e000404031040c0882c84003116410f0003071036580390040c102c45003c180c90340c410f801c0c107001c0d9100f1340d2540d41c0403c980c0100c0c1c2d02030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 926229136 1250 926227886 926227909
    0xc1106010e010501020d021501061d030a060b1201050405030702040207141501090c02030c0d050f070606031a070212030f281b05042d03140f070b0a1209020f060d0506 73
    0x3400501038031481c2c4040201c82341c90500c1610100b00301500e281400c3d00c1014000e40030321801806980e0500018144040505205088640100900e804654003500d040c8121401540e0201c0914648203450f002c00001c0d42082000741c40c074100b1000141c5101c0010401800c0c080d0005c4070026140d0316001500c01102e2036070035080150b420030040c00e0301d0001c010030384c8901070210742000c23601d5460000d0107059a002c1c010b0014041407a0890220502c1044103000d80000c422030146407030ba90341d00100301c1e00ea070f15541304070740001400c0c03000c103a5488036851090b1b4400b02100e9400c07100086c040404005500d041c44000066598842c01000b462450011142482c51360030901d140a00c0c000200104001542c6440000c400449160b000c00381019001c10003076820180d0512512000e00d041a19414180c2c40e1400e188101039001442001c0c800c15184480e80c1d5407920300f52840880c030f403080600304221049030312504109280740a552810040c06084502040000755480e14005100d01e80060 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 926230386 1250 926229136 926229163
    0x1050405011401060c0312060801020a0302030103060b010306060c1e17030411030706140309011503050f2422170c070e010e010b1b0a11090a090b01090c1106010e01050102 75
    0x5800144000c5410841c2a68050b070700d440c0c48404010b401120b81d0051423580c00605065000282c01480b20394190080c0d4181da0003000f04003c405001801941160302501c42e01c000f0940005085010500c3c0030740744500040103000c0142c0d0034510766034000440181900003090600302100f4402440341d41e0b88400348044040e00200003140c100040036160071410020031035001d2000000032043e100039082880e851484c0a0601d00b030315102e1828030b40390b880c203030030310ba1040c410070312458150b0041c40d2038051800d202c20005400c07a144c0803041001c2200c8250252405030801d2103160000362292811a980f02c0001c3e50661207180e1143c0f0326040c03010540c4035122859042c030060103503029040700c1e5411a040c1002c290b0b81d500040007038014006410994100718003a0700144410b00ca02288501007030a070485000503c2d5890300b11600072100c0030b00700507090200440052000c40d256500001050400b4101144018060a11940360140903001011190203c2c40100400d50f01009001b900424 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 926231636 1250 926230386 926230421
    0xf06061605061603150810090822050102060a18410c090f0c0c1e1e160510090504020409060806070206191116051b01090602120919080105040501 64
    0x34103046d6035503950071840349000300d580d0340400381d042025800407640010b150302a58080300c1914201c045042541d489410301501a440c000313401802c081c4102c0c0c20098094003541c034400c002d41c0790110a580d035081a02003151240b4404215108075896607820320180c204070000100c5071030402170601c5a41036079507000d0b84440b001d00071441144001198810700d002003507900ca042d1109100d1034200c0080c1074030110000048000d128900200384052090002d8881c400402100307008640e0341c00d121544018400c0e460390080c00607241c400411030b4000c2403880d007916800c1e21800081d040307130700c40e902001c01181d9840041103c0441400840d034001000d0028041c2d0f441c14407044c4242069056035800e5070359917130005c56125104901a17a6402d400252500450181841d001e5529044051800d41c505410402d13604a903102e00314000603113000f030340540001c41030180344022a4204510a81e40801480079003103e114001c49a0001407041e44004034030f90a050404608541d100308040020b81e1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 926232886 1250 926231636 926231639
    0xd050601180e43050609180115030c0906080f092a0906100914040f0c08060307050a05010906050d090602071506090209100c1406090717060f0606160506160315 70
    0x1001043c0e1901100d40a40f1450b58988803c00012500c00750750034280c8000701d10f0030000c64042d41c58070954282c2c80054408102d010b0907181c0998038200d0501c2440b00286800001422079005003e0054003c0b59444c00c0313400d480313803003661b1038401c00c00d0001501040020300441e403030a29011810540002c4140c510509845401c44014209141400b170b100000440404600494035941c5c840380b807000c0c401604101c800c0140c00000c0c03c18106035a018440c0c45404008102e42c502003608500300c0c0c805031a05848035191040c2650950030598660600594400301000810b10a00040c002240325080c9611543d00b0100e081084448540200c0d403418814001d02081d6212050080300c1c0070303803506204008002501d08070a86180362400c210341c5024200512204600024480c7c042e00e0840748052a401210740c0c40e1075075100b0803a019074207150000d001c0f8075541803c01c01800d84440ba904a90b462110544805241c407109031600c411411202080b0030182e40d0600c9110003e01d164121490b095 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 926234136 1250 926232886 926233003
    0xc0c160f050d1a01030b0103060f11091009120605010e09010e12070f0c09020d0b0609030a03030504081e03252f0a060603110d050601180e 61
    0x88054081c1a000ea5003032800002032045100c0700d10ba09450880d110322183d0303164542908441400e1104071900c40c200102c803400d18442d4080c004102494204071800c0012a00400860900541e5014144038070400d010400001103005000150b0240c000412227500d012070410456400030b01c00c91703280c1d1500b0301601134240d0100b40c003182901940b000a0315509a070400810112502100904249645000181e0540d441c0c003e040c140100312020085902c80c64103020075803003404407a9500d83c01500d005e0300000d00036806580c0107401180c5050614030401207058040b20700f5010034841341b2000c0304110a0300702568820790450305520218580301c07200326014000075009401c01a1402002209000401d0801030501c14460040e04907a00e0405504055000345554042a0b500e6401c11103804450704100840c0021a82c1c01001007001303a290600051610f100040400c0c0800c7c3c5611400400300710412030043c24207898001203d14814400f80b500380c083d40b00c0310b50440018403000607080d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 926235386 1250 926234136 926234159
    0x30f010f030f0f080d05091c2f0309030a05030705160302130c1202072f03030304030f0201020f21071103040b030405030d0c050406030b0301150b18090c0c16 69
    0x800341e0105644202c1d0302d5a14002c082401109807007000285050300300495088009407802c480811300faa0809001c1162000f00d851600490481121102d8912703e12030315182807060842c0c003075415041c2d80c01d0240000c0000d0038250000c4081e1020351012030450284502403007103078004602d20a005961915581c0410000c1c4060000404040d035250603610381203003e20002e80f06105100b000f159203090914004410201100d08880a11300c0b200094a5010806021000035140107004500b075035203a075004c03600b244001d034400d01195001d0010910450121024110400b1600000d40d4000f0a00100110b5601c0041541c42009403441010255240c080221400e45800c0080341d50380b5651420b000746988200d01c80d0b044401d103010480c170200d680c4600074206441f5103a80602c01c0c50018000c05090b200400442103508030309901c108419080c0f48010b04800440f03a0b214440703039010100007200c5000c200e07001658810009a003102d4030b41d0900c0034010040048411208c03842c1040d442c00715 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 926236636 1250 926235386 926235413
    0x305072c090703051009170906120408070c090b03101401060c02030a050f03090a06021b0922030203090f0402070506061c0c0605270f010e13060b030f010f03 69
    0xd10605400204a451800380545409143c100e001c03929280c0c1803890210003400c50340801e0700c20482c05c507080c000b0080365008035051428002d10a40c145920003050034405000648121411002040b00f030340002c2e5960000e500401c10300710f0014440105100385401c0002a240e46000c9514041e85204040300e00310342ca5064612601e44405040c0b0070b4804a85001071404014009102d00001014950b000100400c1c10980c243c0300c00441d150713101020b82e03888100780316408411611442c0051281082c001941d4012800c41c4020308442d070711404092104c0d00184280c0040c2c000041d54601411b01804000e601582520110b1504003661101616040c01505140c811a02c07009854011004e0303038058031185401410f4003100e03030303620a00070709154003240782080859106581100d0f1140f2401c00e14043c1000a0100c1020340d00c000c00454071981c6160304640d100d00004c0f1540c10640b0240300701805441d07000c0b44035a0fa800c10120307050206105a1001c40d049a80460a000040b4a600240e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 926237886 1250 926236636 926236709
    0x1204060305281104181a1804110622030b0c0708041202190f0305070905040b06010e03190f061407020d0c0206040e0f060a06050412031b08040b04030507 67
    0x100b50400001c483c0c0300d840b0381e600913425648580700e01c882004803503000c000507000c07031203031611103511040034450002044004140308264807000540800c8842c601108850b1008040c1c51074192003941e10300c9003410040f201d06541c0c0714510140100402c00341e00c1c40d000011400d241c4d0401182d6030b0f5010b45407207107004030400d007a0300d02d00e100f04548429943d0704001001080c41c00c074184d01c51904204c00f02141c4020f440360300c02c6440000e03640580d84101c6000c0c541000c0021055550300006499164a80c10425014031074491042030700940e00c0168080a4401c56101003c641d480c280082036407030300e481080008040c117062001807500050002c0202c1e850b07007040c88c0fa41c0c500c3e000240341030003160b001d818200180c00400100c00308030610103104020885054203841d49415040350a030103180215808150306400440210f8055540341d14070b07007480341c014112400195649507413500641c0c45140c2e0544046000e00c20410203200c964040d040101107900b441c020341c001450040c5c102440305 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 926239136 1250 926237886 926237891
    0x9031c200705030702060c030d0b09060604091508010618051602030a14221d1005060f07060c03060512010b010903031214040b0702010f0b060304170c120406030528 72
    0x10740c2008814800e4403a82d9400510035625200c02c1c0c14029101c1d030082c2c81c0154442d1910101807410300e080ba800c14000e90003d89460f04040c00c0000c00001094603503241c030a1000380840000750764009004140160002d15100b0300741c4107004c010401641d4002d000c1e004800703c45100880c080e42c0c0002611a1400e039890a070b107810103000d00d001144e1280903217250740150b140c54008903004403503030440304645455061900d114462000c0791821703881502d0310b0002c0003c0704000c01983c5080300180404c0c20080390741c140707007500030341e18001251444000c0d000401d4a1b5181044240b40c501a02d8040d1203035800203210000004000801c00d000d2804001c0c01c0c80140340c234a10515050340e11805083c2500c49151025040034100588900c20441b8540700540c01c2c0701415030300c0c807881c0c0070344162a1400740000741191903561311540d206c88560380c4070150010612840c5030150042000741c81115804802980c0d587c184040142920342c01401c8401c94040301c10469441e0701c1c641d80c412106401803000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 926240386 1250 926239136 926239147
    0x405090708070507051203060f010e0906040209130f14011203080a09080c01090615082d0f0703030c03020106061106040f03180f080c0a0510050304030c0b09031c20 72
    0x80e1140c1c052001d01500c68403c0030b02d000790746c609550042d80109022901d0a1005824100440e00e4101000580703402c10100c0000c280e0604240d0043c0c40c4042d40101040e0160b80c4144c01d00c000c860700e5a41c4100782d03d440c1c2d0242280650541080b0b4090401c0d208803040d007c0b902e0300c01a1202d0b001070201c1c000d00d070b0345175020428801941d06507406040b6280c001d1040d15903606204e00039000800c00390172001038030040001e4178000010683c4091421444000030703030b04101c10301c080d01424101207544a000f483d820003000c413024485a8055807081d01c2e49031080c0c0650600a0844a490b0170040a00c059503603202080100024842c0d40180d101c580340001001d00d01d0119120116150000901800002c0100e5000040504941501c40c658101d445035000b4408000e000f5200e442200d070884004400800154400c00c01154001e0282c1040320b1021003a03036032000503010803a081080c507000429801c0d40c286c062043c003111509801e105000030707015020b18024054018162128100380040d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 926241636 1250 926240386 926240401
    0x130903081b070c09020a03060b040f120c080303070f030b0627130c0906030f0903082a04060e01031b09150e09010b091504030b01092304080c070b0405090708 69
    0xb201e01060f4007418001c12203540b1040780011b5040340c0040c1020908142c1c02141e180d101d1001c1d54103c0310303218990b000f617034034103282c03021304030700c0d01e00243ca03680101903001c01c1c980d00400046025583c190b44403229110a008001d044520b209031f41c62003a03000b000020841000c8419400301050401c081c450b0110100000480700d20400c8415001c060408441c11102900202028203c89080e2828007d9086401080044034110340e00140410802c1000c51900301e1441c40e801040604e0b0520008402c44120304861507802540c428400a510000301c1c0c0101c1d40d140c081c40e02c41c03c2d200b04440031035000c814009040308a80c0c1c02101030002c000c004145006111790040500e262001c0d154000c0e950316580d00d82103580c001200780d40190030b40c00c1030f14003041c102403c940c100c940000705200f0356400e0003800c03000760905c68180c007162880182003d2290f40030300402070050b0b1040114650380c501411205050080c45e80c4580b83c400000e000400c0a5150040710740c0d801585450b00b24002e41d40e10f0b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 926242886 1250 926241636 926241691
    0x6240309050309090a09060911010e220e073f03020d0f0c06140901060e090303060d020409020301150f05010521090a050303070906030621060902030102160b0613090308 74
    0x3910950422400000340401080c000d03150200030790b41d541d440bd1440e020302110b40e40016607400709105c2c20001c00c20301c14956006620414400d02611a4280e80e1020105018228100018100c110060204011030444142c00e0103d0b40351200103440401501c0107901d600ca940007080038030800e80045071000d0701c6106520000e542c414010001c1c1603d54000550700e401c12250000c89601c0d20360086003090311089180d1180120400a500e540e43c0c0038144080e00d421008126003298882c2002c00040e0340c05c1c01101d0303254000a0740410110b10300111820701070a82d50005060040800002964075840c11014007041103000d03140702291660144c06241c0004090043c1544c0404814011400c2d40b102802040b9040f5030b8040c0300040e251401120030800c0ba044d498400c82c4040e0006000500c5500449000ca000400050900c0b1102c03081c0140b03d00303111412210780d501d01e0100226445c11178680110800910803c2096601a54000d0281e00b40a0003e03060002d4220f9003408044445 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 926244136 1250 926242886 926242901
    0x302031b0f04060906080c0a030507210c060503060a05010e0102031b1507020a061a0a05040f060504020c1e01091106070f02040908070203061812090103020d06240309050309090a 78
    0x50001c0011a035038500340001801c141c099000703d0f000f007121f409518139103c03802109403604000170740480d81c5402c8007441c41c1c00640c4000942c000409503410045805110424010103043c2c881c07075501e280c8a400c10259102c980c202e941032215081d40804d19903400400d880405514243c2145000b1440c0c00300d0345002c0c5052003081c200244801004141e581c0480c080f030865114902c140030f41d440750070520740c1154049080541128002500300480d1500b5005044102c4c260b04002800710340b00d80204003a070340040a21038159001900c1c07070200007143c80c40850b0b084203400c0200050700c85540c1e1b8500384c0008014080c4170b94008074070a0b0600040701264491194010000c001100007890009100d800040c0d05a00c04c1c010800026120281c546c140c1c1448110040a44044850726008180c2600500119410541c3c203004640b4080424840c0b94040d040201600200e10b40e400314990540180c410114200342c104003d05c00050380001c207850100f00103c1c1c800d40b4696421210384018880e8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 926245386 1250 926244136 926244139
    0x2011710090c021c03091e0308040312150f0f091b030b0a0e190c020c0102100c020f070b13151b240903020c04180209040f02030706050a180302031b0f 66
    0x11201280107130390182d000000d0366214407898091515100341d80c2d880380360700c0d8070040d000ca044c6500090019100b8207820380364003949540015507480d000402103905030700c1d41001402c0c2296050512046600681200042c01d0b020414009840c43c001c0343c450143d090440c0700300745519081d10350714560316070442c0b0780a003a12000103416441d1a411016040303507101c8000c8a014608518070f04c41310310202d0084d80d03040f8182c00400041030643c00c4400140b040161140441c0078a40d448440464103100b58002407c0000d030a985850602c000c00c0c45421081d4041001010a0a41001019041070100310111003402000e0009940f6080c002c1c0300c0c034000382801c030301c40000c000c4400800030507500040100d0702a07801c03281c074000c48030140011982b610181c400da0192542200c00186088044031ba0f1042c816200a40c243c00b040e40400d180103801d405c17041c08902c1c0030a2030844190700410b416a82c0120440101940b4035580209454100da9203074554044ca042c03400f018542c0300e0015000381d0500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 926246636 1250 926245386 926245423
    0x1e031305160f050a0b030f1503010c020606041a010f0305070201180510050f15060714030a050315031f0f0e16050f060309190609020409030c02011710090c02 69
    0x49551805803610514000d140c2c0300c0d00e10010104150421030315080c103440d00c40402e0380c5036849101d000312050000030b1401305080b0401d040d40d54141c82c01c2c00360700c101120f290020111428064104016103050841884000301c41c84440c0205a038080c20000d0320b400a4240000e03203440d4241c00702d0140c604d0f1000e82d01d8498265964004210740001e6488158606041c108a1a150706008a00d545403c0e82c83c1407811800b000d0300c0311180340c440002e151243c452001e4148149075a2402d0f415904410030200c0494004804c12840d283c4404016881c2c810490282c4200611174a850305410300e00340c004084a40e486540400358500c2d40d108840c01a00e24086603160304d0b000004c62000210340c0074003801505002c85040d0b1605110f0306581c01140d0b08806450446c10208910009001c0d045050350465103504840000d41c44034030582500c14020340d00c089031512030b070002400c2c00e0301c021000e8012079907600c20841c282d08180359241c1500c001c40c1011840d0610303141704a180c0400c1c00200820480e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 926247886 1250 926246636 926246653
    0x50105040c060f02060603031e21100807030b0f2a2203080a03151205030d060e090c10050d02040f080d02070602030405270720031e031305 61
    0x7000340c102158841e59950803109500ca904030388511094400c650154414440c009900491256007408421000030b064200781c10300c0450507207848108580302501c11040309102040009a100501401602001301105841c47c0d03030350544150000c0020f802c5600a00100e40c0c3e410031203600d5040b440d8408032200c0314800070700322600d06500800c2461104090342c000780300d036080c1d042000710881e0b410051080c00d11710604000c3c1c1c040e043c5500504d81072103140c2c0021a0301d0031032810702c61485020788000e544804030b04003010100c1d4a0354025044e00e5140800f0401f40c4c000009030100650016140d2581202c04000281e480740911380484131510f0011034045410090401c01204958604044901a5120441c1681c44404074041e92005030000c010501040c00c146440054030400016148440125000740c002c2da448142c0e0101c0004240d00c082c60900c01d840c031284010310380c0c42d0014601d40660800307202d0030003800340c104050030400030000515020905950002d09a0080180d40d03c26 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 926249136 1250 926247886 926247893
    0x3032a050d080105010f050706050a0204080f0f01050a0b0904110406090908030610050a0915121a04050c0412020d051c0f1202120a020921011e020c19030c05010504 72
    0x11085641c01c40001021007000040c0c56104024403003044903d45c4070303a45000d0342500d542000d4440200399051aa8081000060022003001403140300388502d40502101e000c14504c160a41e200540100c0105040c072010b03903e266206ca21b20340d000390344012140c07a40e176032905c049005004564084414035180120300c009000e0064011449110101c0d100c0d4040c0710900000c3e5400d0150100503c00201c1d943c0c1d0a00a007005504602180c1401e81062107061040040307580945440c245850001d505d102c3d6038002030b0515010340743e003184941c0c0d010b07800c01d420b00001551601d518080607108042e80d4080009100301880b00883d040c8500e40521004280000050486411803d20b0303030004a000c201c110f1300512900c01d5500461840e103c0c4990354441c803900f4070180d0450010182c2c01b00e04401175402d60b0062048000b854418440003141555241c034101a001d005003040c4d901d40c03401005603c0740040040703008c0404036041c10314807660b4007140c2012142c1c0062403000030410741c81d210510050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 926250386 1250 926249136 926249143
    0xf06010e01120c1a0702031203010605030402240313051902060904021309110c070603051909081c0c0f03020c0a02190f060306030b0601030b31110d060b0c0703032a05 73
    0x500307009a04823843e00380b1007101080d09100174800c0e800000c4050000ca40140360000d281c2250740c00b2041c03010941405100140b041d81c1c001d484506085407029902c070b040000600079982170005542001c804140181c003c11840d00c00c11151510495000600c0f0300a0924200b503000034002c260410002450409280c8040d5804030071541c407184140000054900d200c0e0080c40c1c842c4c0c00b8092252064a540c55203a00a00940c01d002ca030644d00c00d01c15507029100c0071540e400e6100703003010046601085450044c100c2000190f001d402c05004001c400f101d0480081d41403182c503415910b04084e4000d502c05254840450303044420040640500052441c3d8160002070070342e03000f04c0114485440b420015801c99513402c0506800202d0303000b04400900d010300c0407024116694204201d641034200c40c071300460300b41210101c00084040b0380744148640c0c6128280103403900880c20361900c0c0308404081d079904c0444c40b00404001400c21007426003503503480c140140c5100c032040502000040d1030182e48 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 926251636 1250 926250386 926250397
    0x1060603140c0403021e100807081b07080306060403021002010209100309110f040f181208012412050a140c090a0512011d0d020f06010e01120c1a 64
    0x68100028400c01c0140c1e0015607004180b8201160310301071641d400e210602c80d9100985c441022540213040c220741b00c01c1528170070340380155600811b51401d0000508146805402c55405061055080e602410b81404413807109412150385500e03507649100084152103560002034000c45000940404290150003401720110119026066540e214000700d04503188584007420740d286600e801e080c682441d007400101c50030040c1c0041031460524400006680c2c5049003801d1160b0b03245a42010300c100580110750401c09481e0a126551502070b4080c44040b620102140320107144201d8100d4500803e203000d058910582c05110b14949504c0140042002850207000d400a1000080d07034811014210741036840003c0400d80d14500784001d11040c90303c490311011082d940d44943d0002e2a006c440700e080a102c0307003c02800000f80f030300c10007401c054540100d0001c0780d0042005000c0440444041819101c128102c0c4800c003445080c4416000003551180c8a08925440d803034000d10402da00915 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 926252886 1250 926251636 926251649
    0xa0315080f0c2b03051c051611210c010b04110a110f0601090e011b050d0908070b04060e0d090503120309100c030e241b0714150619060f030e0f0106 65
    0x6490207146c0f0381c024150f40084444d140e07418103000442c40058082c4501071801d0142104503071703a0545450025084400041000c0b90b8808042070008100c8024000c407a03908606990034041414900c4140d54940190f00c003480c14081800303000e8559041c01c00101d40a580708004464680d60b44030148070050404071016086942003504074100413120015002c5480c3c3c10703595840c0f0306018401488010300301340c0022984042d0030050800420301c03d140b07550050b40190400200b81d0070680d00c403840c04c03c0c034a04403818400d403030034108000d41e008900c400107054400841c90307403507035100c01c080e0414007050080c000c19840c010215038451742c1a0311400d440002e107000c1354501d0f8944240302110f4034072189541403944001c000110221640b01e200b601071182d0106041c00d060311907451a40c81c41c4a01051a007941c841054940d42c0004e41080c0342d00034401760341d40620b2440d001d81110984c400b60007064180a0381e004014140e511030fa00840c50010042c00340c58003456491079940c0603207190b100c1c04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 926254136 1250 926252886 926252917
    0x5040c0f12030915031d060601021510090c050d090302160b07150c02031314090604050408030a0e0705150912060106020a17040504020a0315080f0c2b0305 68
    0x1052402030810340500d415003649030b0382d0405291134194202c03950280340796003c0684800070b002580036800002c0f501c856100000d400c0340c2c54010002803620080c55182402c48410030140444581100c0c00b081c1680c3c15440c0c04a0881c0d120300007030300c1701d1113a136007083c15561910b150b64090590105000c9403600e00c0c1d07c3c544680998640c24404603010300880a0030b1039510001820000d0284e502c082d60040b400d00580e0704100e9032049500014000b68002c0104081004501002c0c0c5040c072000c5034020000c0300d0411060500303850b030f1110340c08020110301d0a80c0e83c44e40345051841d8200240402000010031850740003e207410300414980107284982d010707580020306107140400108141e030580e44940e004010804254440c10154110006658080302c3c00f00004035203526180003c0c100c541d055100400c06827000ea544652000c51944920040e40250212400300d1102042d205000f442c02c90389051502003a0b42ca01740446005840b005030300c0b8005200404050300400500854000e2a07100c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 926255386 1250 926254136 926254139
    0x110f120a0f0c0f1d041e0c020316020d14010f0b1e030c012105010e010302030c0f01022e05010303030e0f0a03090909060f150f1d0114030f0105040c0f 66
    0x1c04040e03440c001d0900010030700b01c1d11400c83c8a4400e1180d0403000301d00080d8035440301100e00201e400c0320000c080140c241c0b00c20608070509100e440c0280e1f052800b09200451610780ca003200130808001401d0000d1241800066001c144402100c200c035601007100020813426443d010705100422100e4121402803200d0300c501c2e0502d40700b14092000ba1480640540b0269030010b004540140c1a60101511492040003080c00d0030200d01c01e0034003034080f110314000194190300415240401c99541c40e0300c07a4503034a13140740c9544d81c0030880c014044540801407115200300b103c82d4202074095001c40401914050001041c0b59154015800380031100c025140c103001c2803007620f600c03450b80e07050280104441030b00801540e1001e90201c40d0300303030080c0d9001507a440d00101c06003d43d44806a0140d641348401e80901800300f02580e0380008205000030b031940714407030007001e0500d201c051140501466904034041c0e0592000c0c86119468030b90390303008100e21326007031074159070502c500e000303c20000d18200070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 926256636 1250 926255386 926255411
    0x203100902091305061c0f0c0504022706090405041209050a0e0f180609070305100c021b0622030b07030b031c2703050c091009110f120a 60
    0x8840d000c1d2409020900f0f015568581e0348003909000e0059a0494120041581c0b203041c1107a0046055100703c9180c48880050b06008200e10070350f40140d84100d204104141c8003958200c203c03105240048000340c0404000b41c0001c5040c0200c40b0300b00e4200342840200420800011401e0402546a40f40c100c800c5444100307018450115000d204c1c02200030401142901040d001c80c0765001c031100032103003040708600803042d0a0183c262104441940425024410010140540300c00701c071b40c01c0c0e010062204090310003907071040001c1009460f00c10104076480d5070303110340301140c82a085070142400b00d10254a441e4640300c0442c40300740e03042842000401e02d80d510a004018071814000c004288400d8450302400c1074558100d00b5409000c1d000d1211010340b06c15100705806080100352407051545182089801c10803c8074219102d1440f05081201c2d54000a14030030075125030500008020306054142403007445a1907100da010080840c012900c4500d02c2c0103544602c40345441440407081459 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 926257886 1250 926256636 926256641
    0x60605030f16020a110d080d2009030d0c0501060e0f1911070602091801060c060b120712080f03180f0a08033606040c060f05040303050c0f0f0102031009 67
    0x5142e0b030050304086013110100342c07141c19900ca50000105141001d203610303540d403140c0313500c000b6a60441d0747c0c0702c400d0328104a03200216201001d042400c01c0d403030704480300006500c0f164808013441c24041140040030501000b5400800a0b000c128100c02043c01d00307043c010303100c1c0ea0848252480080c41c04c407801001c2524010a00b00040c04580755042c044151b486d00065001401c0a82d040740c0760240443c0d48550b1040018028030090312a00b51913155810701200b540c14030030003d402001035024224410f04001482c0e4121080d45800c0301c16010301e0b04d13298000e441383c0c42c00d082c0d00c45004420f00200907000b190800c52041a20f044034900d032000c20780c540c3c07034094183c0058110b900a00c00203080340b0200c005071004190b202c00c400518025404444410445040c210703440c0da000908100410032481038043c09014117040103034000003080f81c020001e100d5404000c0c1004808580504051010051030b02898480010fa030440c034400300300503000b07400840340d451a88200d6403001410032003e1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 926258992 1106 926257886 926257921
    0x120209041a0a0e0624070c030302060109050a1521052d030f0307030b0409150c02160f140a1a04050108240d03050d060605030f 56
    0x642440b0221420740c02c0a034a010b22841440666a981e030103440401ca95400744402e0001c2d160300c1d5444a0240080c0207001500001000c030806402086060681b0001d50003040581d5984643c074050783c0303e031000c1e98503081c0d400400340308030340030040c1000f80d0380f460703820441a6903869510186082242c03826403111501d0320300c0c280b101e14084001090482401c000031420131036000d00d4401304e44406000c402c20b060782c900c0b980d0555100ca40042c441e140e00040c0f0410020006d88455019000320701c2260018040d00c003241982003400c1d10b1800c1a01c0118420416542c1002810b10040800032501c540c0000e06d140001303070716234070452204e0740705007038102c802c1d1142d01d070000141801b0800b81c20b40c07100a40c09460b4040003640b60889103101c50007240e4004c04411503040965082c07049100c14a030b0b0508100300440c0d0160450001c5020780740a904242d0030703a49076504a0b0242481 = true := by decide +kernel

theorem cover : BRFrame.Cov 926079136 926258992 := by
  have h0 := BRFrame.cov_init 926079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 926079136 ≤ n) (h2 : n < 926258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
