-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4173
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:46:59.354476+00:00
-- url     : https://prove2.me/submissions/48901199-91de-4713-95ce-6317a99c6401

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 750359712 ≤ n < 750539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 750360962 1250 750359712 750359749
    0xe03010c0c0201020622020f150a02010c18030b0604110f18180c030a050c040e0a091203060f0b031503030a0228020105120a0902040f0b03160e2202090a05060f09010b09 74
    0x2703580c01401240305070f41c400000c16000d41e54031070b1602a41034008071104071501c6401b00300c007a0940f864850500300c0344000c1c001446580d4400409480501800a41e001c900c48054020385841600d410104042e0b64618003a00c2401011202480c60391141510751040ca1004407050864507480c41c1e08014210241c81071000030740502c40480c10398848044148685854100410141070034145224400080524102054141501401501d51103420001202c800d00241c1d0750305c4c1d650354900c43c0071041107104168140030016058010640c00910442100601c00c038540c102c1c408100d004031815012400240428002d2106846080c15060001d0340b11078101d901084d010400c0e8002400c403403d22480700c40c01691504140d20705e060400a200c3d0070f50745000700200c0c00c0e00b0720010008038200148a094501600041e8403006400301c1049120b407580036140b18810f0a090001a010340000c0321018007074491840c000c100ca141c03c04803a0704a40400c0e11442ca000f07100d000b401064081c0b601c44004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 750362212 1250 750360962 750360979
    0xe040501051804420b090c090f0411070c06080411060322230303010f0e0c0d0e070306050c07111005130314010501050102070f06030c0e03010c0c0201020622020f 71
    0x200c1804030410299503840300ca129032400202e1451166000d00941e01611010b2810491803025203840098540103001f60160607101c01102000412441107400141e41045c00c0c481f12890060460026080241c1700304403006241346c0301c10045075080002c0710094a0302602a015401c60b00744040255005803071008400e801d80c0ea03010444030050603119003211503218502c50181100f11108012001980703035400307149194903100e0007070f070030010600985407410003a0001c038501c00042c100300d88290303080a07024412129240c0005072141060301c800d82d00070b420000020001365000003100c540541c80b40900e03106055841c144001d0700c12010014082c070204212504104030300855840c01544580880c0c1103962030080e90900755001a4810350640d40040d00c107101c290242c52486040d2421071500090b0a20781d00e0781114162141d2502ea5095480c0c006d250b481180d11081803d5a5030003a02254895121030800203070a4048070054003405128000c4035005140414400400c2a0018180740 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 750363462 1250 750362212 750362243
    0x41b030602030702060702070f0f18180c050f0411180a0503150114060405060f220b1809010819140f1605011e18030c09060302010e040501051804 64
    0xc0780c2c819542e6030050ba00180400013802e40c10010040071f410000c1c2c00f042d03610f00d880241000400745000e220000c5207925a0b0591390081c0c0d92101c0040148031260b4400300c50300d4101201c2201680c0142409041030040040103814035004410382c10359025090751421070f0401d880300d81c0303c80440e1115803090340c140d00000c40b542c00b00b103189043c030b1f0310200c2001d065160010102d100165000035a024040510041190341d80c2d200603161001c08220202c1da80e01c1d00b0307100301d13010540401c2000e588044140d1002c15003600130005130261034018100040314940e0722007000700c0c0c03050034850b1243d0f41c0d028030000c1039080e0691400000e0300e0310440070040c050304607129542c18641b41001c0d10b0400e903c004940f00310300003110ad6100083c038007824003c5031819115007242c10300b03181c50081000e01154903800c1c1c0ba07500089100130011500308404d000709648400061001c0e003e14801a0b00040c0c030328011051a141611030541250310042c58010b600000300001c0d08140b07002402903550801110b2000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 750364712 1250 750363462 750363473
    0x30c0c0c0f0509090a020612040f0c060f080a0b0a05040b01050f0d021c09020603242206210b1906060816020102031003151e1d15041b03 60
    0x1100980703840c02039000c050b41044103210b48008010035103103c81c3c0c0641d516101686843d41212600b00c844245911282d68509104600c00d00110740244201b0820354001521030340038000500802450390b98800799102c2d40d41e010141c0e026410060350140c1048001c201d240340c80d0340031280c4040107040c09820514000c0c22011184c10000c69074100781c1c1c0003e2031080301004602001a03002c40c0c01d4042007040ca164020401600008044410008000f400382451400700b0074081c00406004000200c0b240080c500c440f900782840c0c41c1c1c01d0405042c64004204c41c1409015070402407601e80072908144400c3d11060303131802d40078000820000d03002c58881d0070031110740035003005031205443d4a103a90800d4400405104510a0190116441032043c0800300070550704a404580c1c10004803034201008046202c003c000402c0c1d104124280808004040403043d000341100316a40a8801143e003603042a2a40342c100c00e825085c0000c0c002c2c030020300041e1089101c400344030700184124030803940782d5642 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 750365962 1250 750364712 750364733
    0x303040f03030608160b0d0204030f03020106051002030f0f250602030f240f03012909060303030403080a0c0c0c0806150a06170a090c1502010f11030403030c0c 70
    0x15141500c5015000c814160107008200051000400929000c0ea00b100d00260006171801104c6600100080c0d142000c82e241d01664051a00540000d022094030701c1d01a0003007035a0301c2034900403015220b410404c18004030648010b0110051000c0c03802410b85212003c0364445030103001944040901034130011040c0d0841503c10f403040c500107990342010003034600e58510003002c9180c4000705a5000306582c84591281c0e51100b015100b10304031110510000e80503051040d4a03204003200c0740c400d60744032658482013400c07110054030049019112a014952030b84011500074000c00c40c85408141d51240703503804090a10214508800c800d6021760310704804218551101c26650710520600041e03001d13090044184200c21200441c08616042d4080d00d0456040705942214194400007a1700c040c56420501c012948400071780100c0d5290744084640502c3c1712400c00040d0f03e040f01d048101142c500c1a900c58402d03105d4014215a510369084018003020071880081280c0b040c2424001100c0035074 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 750367212 1250 750365962 750365971
    0x913090f03200313090b1305090106031505390708090102010c03060513021b12120a060f1a1e0a0f020606130e0a05060403030203040b01050d12030c0306080303 70
    0x16082c8070b4211034074180340310441c0c072990808160000c010700e13031301a4900b848660455003868030205e0400d40b40000250071003080000d0074003407414107081210031601940088252441104140d42005044a20208990303040760549901c0320b03070107a10740346000b95010b199080070310003030350303404103100103182d140036401c03051045441c004003241200c441e60702030056010300c100e50720702040058640400901c2d0701040380c01580d14164001000f40c0c42c14034540c689100c000645046030305010620081491b0340d803100842d04200740300c074004907002200c280284801c4416000e036420401341094121036075010242c40d05850750340d0810880305403070039480d040958801c112001507114001c0c0032010f0000b40020350f07910210b401c290308005160f55502d09019500c0c0c6c082100140b0084810700f0146800c900b0400527085119003800c101c201641074004500c0303603104559012484e60781e0303010b10800800c0042c1c014140320080f1080c09038184a540002c1c0b868a17941780124919130b466105508550007030301c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 750368462 1250 750367212 750367217
    0x40e0c04120b060f060309070608090a060614031509060403030b0402120907031202030a05181504030507050f1512070521011d0906011703040e01090516140913090f03 73
    0x40070444580b401c00c40d81300c0003050554501e0300d140b0b414031800f502c9203014000c0d001440700280108080388001c0012400d282d80c030071010842c554a9030f4517111050b40c100d6800c0c0c0705c0e100b06000d1418a40460048034000e40ba01c0700101b08a454590741075018102542607180c105500384120942180c03070940741406914000c020302001411030a1180251900410b24415980104400c2c0d882640c003500b101c03011000d0700d45507905078000030700162024200071400c03c0c0720b140114001c41400004604001144e900b00c03018405032482d88280038610b880c040380000c02c0101440840301111028034003550040c410b1510610700303103e5040d04242c03182052640800581c42400501850890b1007980f944a11003050301c003030354500424600d64841e0705001d0651402c402c1504500d04507410402c1d82c0252803140035440e400e41e190b500350030041204482400c40a1645c0307403003c0320280030710103a11880d00f40d0070205180100c40c0041c000120440048000e61954410b10b420101d00d4105802d9149407099 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 750369712 1250 750368462 750368483
    0x20d030b130216140105090a021c0203030304080a0806030c090f07030b130f180c030212010603050d0e01120b0321190f0f020c0a050111031c0b0a0b030c040e0c0412 72
    0x40c14504070f5400c2c4c80c0da2000755a0314260502010319000911091096130490300da5509418110200c0d000703a9905000039054400842032104101480d00036120b000c8440c2d58080c000d030f80b284101a51180700c0d51001e60460400790100310240c098000c0070b40c0c0103103d4100800c41021000c04640d80020760805038008650322000d642200c8041d01400c1800581000c4200c0516400d40707584c2441d458500c00244554031102059540b18001c5d0044801550000b00360742c080c0142c844090156044407110500240445400384110300c0700f0310840d00042c1f0003a0040216170640303559002c0d41036080e0300280040750244488011908880d03000c40354102035640d0701c102000b410201810107030700100d01005541014080e150580c58281e83e48080358030900e007800743c50002a24041c103502c0741250606907140050360300e031141c68154102040018090f0351071042c09944075255441404247d804900841b802c000802c0002c0741c80d41201e030403a9501c1c1c56186010350360801000d141204100440754039070704 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 750370962 1250 750369712 750369757
    0xb0d05120a0f08161110180b070c030806220e01020409142802040312270605030a0b03030f03011d0a06030302030a031505130504050c04090201020d030b1302 69
    0x80070002d15180c980c1000764642c203224a4244c00701250a01c540104842e10783c0c5407080003010040c1c00c460203503511040240400d100c1180f0404603510320706030345224401e00841d01d0603100f001e40401c403036059070f1142c01d561105020007500d0320751001d4821440340a200c49054210711480340401c2c0d0382e040c40c001030b03440740b80c03010580a4400400c3d0140c1000406030810104a15100031070b90440041000c03641460b20181d0414001e008640025200c628440340d000c401c1d40d08000580d140000200e4030401e0108100c0b0503a500c142c0c540103480024406002061030000550041c0040b038074010103403420040100c90f140300d00d420982c0422a400c0301080d035603a20300010929641c200f05a80010302000e419130320040d60341d20412074140105503848020b00800440145084050000102040c2d02d03900c1502d5418083c11082c0c0d010382d000c3c002c00005501c03901d000d2140b2180da0b40d060300603003c0e01a0041c0c0c150700401b050440c503600100c003c044403201d1082807000b00340d8030042602c40c0e80080c0c507 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 750372212 1250 750370962 750370967
    0x330010503010b060a1202190f030b030102180d02120105250206160509030115321f1b03051b1f0207020103060305010c0c02030d090b0301090b0d05120a 67
    0x101a4065402a490000e074105141c035000100c4008144504004414400003041031000344684000306074005940080c0034078250307001d51103201c0400300d940c061001b8002c000c2054201e100d8142c041c094817403007800010482c10f08a25181460f80000c051010401c0020a0395081d40c1044131030141c070008120381030b481404080d1071045008074510062105107050061700f00b001c221084064180140801c4603007285c0e42c250403061055540035448000e1781d82e0380d8210083c610141d6102c07240d10220700c041201c9004240e10409a016000388000c4a0415180740d11a40c02d040340060010130400ca9140c2000304401c035030001815101c2d43e1800d5807211090503100052115500b004065004590301d188603881c0c506a610f90315030032110060f5200c500340f006078002c10440d0b20017801c0b9400c2c14680c18515412010094a4600940075190302800105084404800728011030810b64800e10040c070003c1660b5101403400c0b000a0000c403010b1003551a940d00d0300c40842c000101d942e030009141d0b01000d9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 750373462 1250 750372212 750372307
    0x120303150e10060c031704060912021f0b060301030b07050d050702030901080109020a08010614040e0406061403030f0d09032a0318050d08070309050607060e01050c191103 75
    0x4103440e12034448031366507400502e41038000c002c2049841249003c541440540d0b403000c80300a6000c0078940f88110003040c0a91a80910f42d11050b00c0c4048080700700c3c18103072600a441d100e8034010642441d42c3c2c290b642e28008454003410200400809003c45c1308014414421a80540b503150019926012030381700040541ca416045001c056005100c0441030540104840381524403a0034060304110303038150700494a0081d544002c0d140d03000c07142404103200803540310a00741c81c0b554039001c01d492003590034503590b8841c618101e0501c050401611020f41e400e6445615460b10902d000a440f5087d9250105400c5c800e011424070340c07006c007260100b0103410154010b5040d0b28030341d150415900d080001411051000d001400085001070369408041c80303078824101900c0010801d82d01d803111030906000911140d80041403641c0f80c0000329510b01407880589548805402000c44454003400e01120400c0c1d0190402d000391006111440b0044103a0201c205003000007030300d0a00b004007802c02c0c1144074 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 750374712 1250 750373462 750373469
    0x6130f0b104a06090a0f11090316050901120507150302090102070f0602030d1d0f0d1103040b190e0301020c0c210622080f040302090a06050a120303150e10 68
    0x10b00903184038000d0014070b24481a0b00c8201122950003907a1100c6400014007401c0e080d42c04000d02e8001d0211541641c01c0207011070400c25411200280c48450900003a2007040c01120f50080c440e40040211950407111315003810320800a585001c0d039941003120071852684ca4040201e60089a40350065030f0410140b03009189440c030820701e180c680800a0348a02c80c400c1c121800d591141034060100d8000301c03040480c030421101b00c0d2000355001c43c0c60b58650306500d076030000141a03903010342140100007041c2c40070b99106900744c3d89840f6103003106250500445000f1400d0110000a1640c103503000e1024041c1d460401029200c51010394080010840d041c4074180d40800030700c0000154107000085495101d8009448000940030030034800c1680d501c0210010089640061602c910007040000b620480c0e10a035440c00082e00c1c2d07200742d14160750140c09465004602108100440d00c444002260128081e0800060342d0402c0100e400318014203401007041e80047d101800940c0c0d45103042e80008 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 750375962 1250 750374712 750374819
    0x24060a0219060621120c0201031506080f0f070f1d0d15180822030b0106030603060e0f0c15040e0108010615050f0403020108071704031106130f0b10 65
    0x881c581c5558801c112500c135285c0e2010040340c20460400c40e402039011840300c01d251700c0d00441650361080018482901182c0d0f02d0762444104022603002110007249a00580140e120040c43e1300040302d04031121202d040c04842c1c038942144840002d40c6841284034044d5002d100004650b0803442d13141d0081d60400401c900b500031034051150080b0340c110068645894010520210314081c02c806285010b40701c0d00050030760b0b04e200c400000d00c01d40550010088900c100420b10803c0700d0b01c0340340340d1254101030f8002c400350000950f1a04600c0c1181e0350b9504100821602400e060b100c031000201400260400141a0342d903202c18440200b1070103100310071071103d1071303d0741c6840424580b46500d805a480002c0c180001c00d070118600300d000715504003000104c910207084500d003d050082051901c220650810702a041c017080d49101e41d4002d202040d6000400b4481e078201550382c3c540d02d64402090201c1201d1042d00108540c0046081e6004030406001c1e0307900403401040d1080a03030608a62400346 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 750377212 1250 750375962 750376019
    0x15021b01050f250c05010e0109180b03030d0203041101090302090612010e0102070602070203010e06130b060f0d1101091a0403140c2706010c0f060902030a0c150824060a02190606 78
    0x416a8002511750a139201172b9003081541c00424180c6000d480c0c102c034040d03410300022891071201240346d0b01a601c1240a032808104804038800190f880c1700460001079004002c1d2000501d0a08000410b42c050842c030741e00000f00b181110310a40d0891b0881401100d1030342d00011102d06514090103072056055401014018a0038070403290855450b0b5400010800502c96002540550b900c2c801070700940400382c4880c000b00303100e00e01007030442c000100882c0810584800491090440c502410541004412b140d1510342161101041c0010020a004451084d010480380740d441d02e400b8100c0d03940c10150200800d260a02034502d10040c001d000c036040007141500c60740410b8003421030341c192603000000000c10a003180046824007079000e2016144c02c140040020341d40300b0341201e60044850030fa54a0805807281c501c150011800c0c0c01c2c5010070326080c01c04040c0c1e0303490000020301d1088aa4011510000c001040040310144d00d12000e582040e03841d20104401001c0300b4518803007002c4502c5a80 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 750378462 1250 750377212 750377237
    0x706021612020d170a09090c080702030a0302090d050a0308180d090b18040603080903100e031e13060302040603061508010b0a030b03060903030115021b01050f250c0501 74
    0x1001c8031071210080d105401e81c0080800740701d00000301c00d90710b0803040c216130341d034040022015000c0c04851140c0d40342e5070f00d045155070026200b21617035402180360354003071860200c0151007280a500505d20056010b10200d6031a00000c00800030985914421340b6200360902c1c0c020a10b6040d080c8100c5510f02581083d9048030600d0780c4420100103a441a070000b585660ad0800b00e450012070700c0303030240e0b001f5182010200a0103200c0010745040d1104404441200440552210075189114040000d81e030090146074000048030745800e101d05c0c81d5128240c1080950103c03413010b4503050b40044046680050184201641805804082c050030907000380004069507000704801014418034444142c0890b0603540203200360407580c40c00704010111034043c1407224095450b90310070b105040e0034145500d560b02800e800850329808120449081e00b40c0304111000542c0e15034043c120324103030009c08209900e800400c0100e022000c83c000216040e1030b445038900341e411114035401445c1880f2100e940d41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 750379712 1250 750378462 750378479
    0x708090d03020a03020405030d020705100f0c020603090109051002180a0e0f090102090303040303020102220e0a0c170f040b1b09130609091b1e0b0901020a05010e07060216 75
    0x318103488203480d005a548802c0d503c01c500074050380d0031107540350190080c100c0000c1c0d800101e240c1620000ca80d411219403d64000b45c031f5001d900c03819100416001814038016140080185510480c03d83c008903c12045548180c1081d80020081e01229800706d110b4600944600720803030705c8401a6600e6402d68104000050421402850f4039160141d05000464840702034056824240c400384c00c41e5146c685903c0e01034080e42000c800042c191240c4807116550010100025040b260304401103c0c042d210340040e41c018000040b9144140b025280d4400d1040d03000a06192181e45c501c3d2003101c060a1030300d8003200d11180600508000c5a0000c4004e038410750703500844044920440300454004103040809014240a41c407041c2100d10744020102400070f000300d8480c0041580c0c52910000d0344401141c81980703501e411164800f02018001e0042804d000001c20b94080140100c1301c105950766a0302c0d09581880148000070b4119500801c503498040110442c0c0c01241d01440d401c181c10031915 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 750380962 1250 750379712 750379723
    0x305030f060a031502210606092403270d0207230d030503010f080102130504020f0915090f0301050112081e0307030c0e040507090b0c070b16050105070809 68
    0x811040c00c03044080780030340c0c1da07591044008682c400d0030074141c0200d408591001750800c030700d14000c0362404410b40703001210700c0c041729100f26802003c582c01d00001c1e905000c1e5044208800702500c0b14200000295202007802942c8178602240712003001c0000382007108010a82d188480e0b016a210348074036005a50003040c124243c50f012881c210303042d04000191074403c03003002406600001052642ca051603032040003181a18003910402845643e2607031814200d204d03100300721005829061062005180c0fa40042001c2d82c154142581021075107400120301010010114a110600190000d0341c2d0810008000c1c0000e0224001c0100703601d800e0410a5041d03c01c2c02c02440c40d82c000811014994802106448a00d402200c40780c40b4580130b03002800030a60300300e6502c0851401121381400346894000c4074800c51469440341d41052614001443c1500841040340040c095030b01c000c9144000407003e0020110300d926440309110090500e0750031a840a00b810302045402c008000f441c2900151 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 750382212 1250 750380962 750380971
    0xc030c08180709090f0507050a080703081b030a030603060f0b0604030b0402150d061a0703020d0c0c1d19090302150a060306050106020309030106081b1309020303031e090109030503 79
    0xc00c4400100d0041114200304283d0012880d080c580500c0f038051201c078205050300030f4414021030700f4254881d0100901141e89109425082e44621414400640b1040240c14407490124641c40c0900c500ca18880c11504000e01076030000742c1d02d64003007041c0710040c011113020003802c0030100540b00100c03010880502c101d0001070401c10034500410119103a680c0445800c40341c40501c0b0ba154080b813070040002d8031040c41444440d0751040c8825540c103d002d070846401640c5a0000d1410303521503e000c1d6025402c1900984a40c003c1c5407000600c8162012080490303441042e180007079161014044001200601c44400c5092820441c240040e8001400759045180c8410a094035a00c0300c0402d000f07490103400040000c0d040c00000680660000040c04000b881100240009611100240d950f2291840101c2c9a1100d10f40b04040c9070030003030b80d0002e10901c11a030110755000350390046499540300740c45004000c60410481c0c4190800d001000e07811540710b80082c0000401924024000c0c00040c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 750383462 1250 750382212 750382231
    0xf140304021503011203092312070b0a030c0914010206220f0309180516050c010e070b0417010e0604110609030a1113050f0103170d020706060302040c030c08 69
    0x408641555110100b000d00b01040c101a1580c075a161104282441c400c000f00b180490007918010482c090220601c83e0605840c40344d18003690b50040400402d40304038a0b8180060095a00203e14a000c0740024001408944c07400b040a001b888001000b55425030311400381c080d030443c4024902da81c0814015080a4080c3e104000c103000c81c00c5100307140601c4600207102c0d8070805025401c0603005603503001103540207400d1020352405200187c0640c1d104541f01180d001c0c280c03001021150003040070740750103480500002201000d45244920740035840c0c20108a5210110701000808010304131607034002e8108000340608904450030581c0c56001620092118540300300f05c200c41d45420003551803036040181240c0c1d43c0e101e11704080c204c9000401e6042e00031803403601c071b101851009020f054081e0030000380400441e807070b45e03c030424000700c2c908600d440c245040011600e090258000351401a0103514000394840c030310710400c811520071040e0a002d042c10072600004294104000302e82c41039111 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 750384712 1250 750383462 750383467
    0xf0d2405030601081e24060103050f090a0602030702030c0f060f0603071404020f2b0608120d15030b040b0f011a1e1e0705060702010e0a030e0406050a15020d0f14 71
    0xc05e981d9007042c540460401c001404488125180e2040300301c0140204001c1c2c80c1000b00d80c1b14039108800c0d55402302d491004c0d03940404403510005840b07a00031a032141c0a481030ba4148408084010b06204a0f415010500d6000030705021288a901c03241c00d0708070b00210014004c01d49000e20409520303410640d060302c61a17002c60100c0c0c000c1c1c0f0f490211810b0002512800b0f6200451078103011600c4c6035500c9858880d032411030082040d8100040c90784072580340d0090281401400030f00000038040341e10000c0c103052401d00300000001c0c01c401e24a4000c6100c0d4400200d1858a00c1c403940400f001613110b55231a541554040f00c00b00d02c00412508003500700c51b07004994403c00030044640c2d10036001c18900304103c4a55051544d142c0d1009082c110303104030280e403a0789e182d449d000c03800e880c14106102c00c960800c1d910000000e02500f0014500c480240000c10219074520004405802941c400341001601c502c2c045a8140e040c0701c009100d00c01800c040d001d94400c42d03c001c01030052000c0291303826000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 750385962 1250 750384712 750384763
    0x11030402032a06030f0702070b0f040306050a1d07030b0f04120e01180810110a02060106180302041b02012405210105010303030c1101050411060f0d240503060108 71
    0x212102c48107640d001030042641c80c00c00700207069071240d04880c0c540043c0601d4001140c010300d80011140c5c850308042e1100e0030036040d500c40000401024001560305c5964580d40714024503550142e801d40310801d0044c00b109403460400561040c0018801e441d110030034400c010015000140c1100700744664981005504640300c0180c070000d01054401d0500480d217900064410350009003e040e108030704000b030281413503185040b50740b4012005a400503070010b00040c02036030300c03401240c0915862010320980382c658940201c3c0840d81110052a0f42c0b0302c2070031580294540900440180e24a040c0410900241c40c4440204240140c0511031061901c1440100d511a14140c80b9580c1c648490081185580d2840c018004110416143c004590100058000102c045c86801c1c85540c101588801180c140c0f000c0181580c081020a4a00003013400310b10309120483c03160400c5005004800400c0c2854450582003001081d4001c038840d60080c0300502c4032020100d43d110301c0381301c0300912280d005e05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 750387212 1250 750385962 750386023
    0x3130f020105090d060606020f03120606032d010e0c03060a1401090e0916080d08010b0a050c10050907080a02010e0618031618110a0e0120010605041103040203 70
    0x2a800f00703194031488001203942030050780e0b8000411a06d0f15021905a004840181c81d141e00500c0314804880ca1508006001410281c00641e48807680d03680b501400856401110f0340c0d50152003c5001902071070340180100c0f07590030021a0861500c0600e40d0441c9030240003c0d00c4a8180d005420030325264034641031481c2d014822580c06080707031020203000c0e450a80c00841e561046000c05400550303002500040000c004150f000c4003901903034442c20f044e800d0212504071940300c000010304000c010821050a003605220b40e10308828030010204007418100b51091070003a1701e80040039940c010400c0400180c0c0c004490005013407040c3c50315138444144d065100444046a190581c00d80104140a42d51540850300c080c1550844180e03040c1403410400080115810087c269009120400002c80003038026058080514014500300c82002c2c0000c0175220070074400400702089a4480c80140206c0c5041d02400b082c1050000c009829494640c00181d41c5102c000f148000441c500c2907007482c0c0d4031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 750388462 1250 750387212 750387217
    0xc0f090522110c0f1005160513090e0309010e12030d15050d08070b0f011a0d060801020c0a0b090d1e0504090207030c0209090a080a0e0109090c02160b03130f020105 72
    0x30020b4082e80d4482004000554481c90340514010b524000c4107400324101480340300e01401000c8220000b071400e14184400e0307400c1e80c40706414189074010440e0002e17016040d4090801d4084a1502a680316103400002610004001d29403a1040303507000301c1158032120000039540c1c0b528006c07801251001c401e03204000040350340c0c3c2160340c1002c11b07041c3d40401d1040c28401014600d1044000c00322a036910035078a07800e00c00c2801012071003644034122000940041c0003408103600400c0000802e0740e0345800c00b508992000c0503504a54028202040c10702480c051ba19a01025580c050103c5030b054038001842e400304000c40c56100b150304660603c04a2081040e1405840141021035881c02c1c0390070058610442140124401c84900c1c0005c0c51003080402c092150552010300c0c41d061000c401c42c240d2700b100d01c81d0307036a41c1005802d040011312440103014001c801e05140c0c024002d00d110590300709100398059082401402340400c18480103003e0806d0174682c0b01d1701700c4200c0c4002095480125000e1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 750389712 1250 750388462 750388481
    0x5041703040303080a0b0a030b060f0405161d21072c06030d0818010e0a060203040c0b18040f060e310305070f050a05060a0c0f090522 59
    0x11240000a0a250400030040081c1c0307001c0d486410f40f076030314442410b0a48100e03c1c07000d50064512582000052103074403440b80c0101c07004011260420400e004502240d01c00c44002040e000610036010b00309820880b090f2050660020105c03000445001151079515518007200c004420381602001c02c6506000940280401a0b8990050700707500c4202c80c1d0f1405064402d060f00c40c01e010109010b860001040724400d50907403590382d0103503295240b07003035031080c130140001c00c031b540300d00b0300458446042c00514030300ca104010041c0c4074207042c03d080014103e2500280e41540c407c00c012240c6c41d001c40c1d40310440590450700803034080b0070030b002c80700600000e80c03007440ca4407540c03001c0c0010f0503440346000c00e54507943c2e101c0c14004000a085030700070b41d0b803a00010700411010840315005c41c8048141034001800b8a041711100c41e000d6442528114007140d015200319626041141c510340e10105d070640689851a041b90010705040c0060081000b003000344c0b4a03140c030115114208202a0056042e1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 750390962 1250 750389712 750389729
    0x51806040e03031302010f050909191104170616090b030c1e0c010522080f04050913060e0a0b01060818010c030b0315041110111b01020c030d08060607030504 69
    0x40b801d003034007a0190013069000403404201040c80101590b8800c0058804c900d50080c5200361a8650307251054546002e000180100e50f142c80028000651010080c801056503484040e440354001290381d08001c4084e00c20241d00b2040e0103190380c4540c1c090594001d8400112815980703403904204e11035103218180c0c0171f101e008890f0401c06040a030440207081203d1441c0000d01056039043d82d80744e400e2598000980404d040440da01c40070404000141061300d2070591000e140984030340004607604800c0799010342d0030b2129091081004050300810345000381001c010003600c4826542e003008100705014082c10440300340001001c2d4903e280183e03100d10310b0000200401492038500030701404040303d016000744a81e4540e0307120035211550a52085401c00494200300d40c4e130408000110b071006c0003c0d02080003071004c100c07400030248010310039184d442c141c0141c4a400d40b0700282c180310890347c40a100e030700a0b065801c0096000795901d58401402c070b990f69a5105589000d03526401160000c003070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 750392212 1250 750390962 750390967
    0x90e0102030c1c150e090f06071e030b040906020433050a1b0c0906050d051005071709010c0f020102090a0603110f030f1f060903020405060a030516140a051806040e03 73
    0xc0745c8030902046401025070700252410708126480866460905907202000221880880c201458500a950104003202e00e00454032200e00000030702591248030741510810b500180420060316242c0360518901c07502c0030fa9036006210080c1d41d0f880c00780d02c8076126003407000006000000c1e034800e01080001c40100009010f12402500300110264908c0c01449515440c02c000407955107404000c10103000e42c400003d000751191007213050040d1202802e0308082c03100b03240c0742c030000640c40704800c0d102e4004100001001d4642840042c0003110000c814015640f0411050b0900d466811120041d80d01d9070a010a02e030031100055500c6205280740d5415508001c410b2100c942c194201550242c0880303940e40992000c240040030070102c103846a000494140703441040142419044241d01c818024480d2611642e01d446290a00c2c0d000c000d100701880520780e0510030207020905d5140e2014060307818176001c0742451b0101e6000c03002215002c904c52894000921f0079900c0d40c00c101d0b050600301e0140c3c1d8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 750393462 1250 750392212 750392219
    0x60f1d0c0d022b060e0a0903021e0c040c030212040b0c090d1103060105010e031f021306020c031b03030a0309020303071208100603090c0905040f0503030907090e0102030c1c15 77
    0x2d492580c1c442c03107940b0b68030001c2503440400044d00a50003994202d6202011030b444003001d1030028060440120154050030b221034043e50803e000040000b6081806440312900100400080342c80c650030810a2505c1881024246160391403056440b80e40004410900c2d1140d034402c0324507024100140d50301c10f59030700c83c1008001d142003a140b08804154211011643c0703c0c001580d510303d84200b05d40d01548990804442016503404009424954100c010701e0200d41203040d001e00040d90704a003000d43c0c400c480c2c007501c6c0d0404010052480301c82c41200213902c010800007a481c2e21519005404140d11100d111040d5601030003111016a80462680d4494102d25805050b400c1b085a030100d00c11002c03c000101e4900a0241340365566020107a9004e5a0030100d4880c0181000b400c1950004203200c14900041c100300020342c0a0540030700148585e030b2400c500b540550751101044c0200d80d00600600440c800315034151891001d600e038038000d021803a010781e01c0041c202a60200540c80319100c002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 750394712 1250 750393462 750393487
    0x313020a0e10051309020f060a1404030c0608090d0f11160e0402150c030307031e06061d0f0d02040c12090803071709070e0601110619060f1d0c0d02 65
    0x480c0c5043c1c4003032103c0058138864408548070340300040c0d0424000da41407807040c6040d82c0102940c4005091002c05130440d540f001d5016001344d04125450300300300500b806040c0c1c01920b45580320700070500409400441c800000c2440320141202d0b41030001a6011003101e03007052107134030341c00e081906008a51a1780c80301d510403a00000d940c281e014000f414800c0e062400c0945c2120041081035005510310b0701c0d5800b00714001d242c000c0c5046002560012404c507400c400d4001d550061400750780b290b0320f2003c25103800052448035038582c2e1144102c00d0b03190085840d040900c980ca280c0482d400241140c4642041e640441000702e540300141c5020960000c004200c070286005810a07a240155000c601000d068148000e941d03803422980001c50070070a1a58070718a003030f80140c061405140741e20325008000d1501100b030740c00d0b405003001440c050780c1c119144e2040c01d0061030758071014840d00d03107030a2880194044102c840d502284030200025030481c500011078000b01c0c5030304802c6540f540d00c80d0303c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 750395962 1250 750394712 750394741
    0xf07050c0a081605060a0903080a17090718020a030b030a050601080c0103140a3b060601050a050f090303070f050a110405070203160c15051306140313020a0e 69
    0x4500c252000d000100d0000c00c0012a105200e02c1007074102802c134101010880c168000c1841e500c2000b440440210000b00b41c0300140080044a8440540010344e41c3c2185107200310080690b81264040002045071030301e009508440360142000c0180d5620349a40100c010b4282c03101903540622a0828110412a0001d0150b048944039000c0d80c451180400045081e64507240c4000c4034080c084000c0f418802282d03000400b000d0302c47c3c200204503581e0810014801040d080f101c0300300c0a160400d0300010406000f042d511402c240380451400d182c2140103040d070b00a4580c0b11003a1403001c01c7e4541b0301e445c20001c442c101f5402c0042c903a41001d00e0f140543c0d03901d81c0d41d88221064000740400d501c41d800c2c1401414081c07030701500038606040d000c100b590380b07a0b03659240903a0f0744a103080c00054130650369816410350542e195115561020601d0380d008101d011a4454000c001240103010b0480c0001402e680e0010040c28041020b0350311400050318000300d84e009540040c14441c184505480b40090 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 750397212 1250 750395962 750395983
    0xf0c0603091c0f180b07080a09090f0911060f12130506190c09140f0d02040c030204060f020a050a020603071106150f010305010b0d05040203120c150f070e01050d020f0705 75
    0x180c88820713056480300c0105490355440342e0b140400060000301e0008000d94042d107001845403911042c115520441c95050303507181901d80140503580e0f0604024810f845001080710b0b041038400c1840c040c0000403640041c0b042140180025002601003404c0c8649a85040c000039044400c403103150401804654584190428449000e4941641e80d002a8000c1e81c44000b00c9940b60030325044400a102800079201899000302d070321008810044005a850748259035907030f005e5036801a01c840c00c080001c0e0a45002c404840d0035135102400440c0080c00c0000c14030020355065a105803a0f4030f405000b581e15501d40f91900226010344002c20510102a000d0090101e000722404000c110402d40150221402802503495015007080842c1642c075803600320641151028040b921690105201e200e01500604546121074000d000700380d10040d00c0902a80d0421100030305400c4a08103150040d20f60a4003031002414480003042d422220140d0b0f5050b01e0060103601c011503030321191480d105446580c0b164 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 750398462 1250 750397212 750397217
    0x307050115060332070201020903010f050411060f0a23030703090b010b0f03011e0f090507030605060a0c061a0a030f0c0618090b03011e02070b06030f0c0603091c0f 72
    0x31825040303a070318607100d20141d41810342e0000c9003c0c0c6080760204c040b0020022000e640d0204031401c41764409200e0131442041a02c000100c5080c03e26103411500507080c0030501c0f404042c88040059030000d02201d0032044681001954100c0e25170202c15050b100c0d600718001c007400031041040e01c540607003041d161140f10304502030050b81c8880390000f460040841c00004140700380014400307103120105081c105017140402c4c40c035203aa2002e24820303260164014079529502d41c3c050111154140c0512170141100703d07011400c0c03004030355008003040f04006000c1c041e55154603a0004240c036100096078104009450110402d0320381c2801c0f100c0060207042140e5100c074201d00050311070711907001e114104100010107000186130210ba44040d194076200c1507419507940e8000740030b0110070703250794404805444001d030b254011814050700c41ca40092a1a00070381089240071031000c0c010071301c5110384400306e40c060f481c0c2c0c0368000b8080c505112400000001c2100305061200560000c2090030b8034007556 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 750399712 1250 750398462 750398471
    0xd150f141504110706020a0f02060c0f030408030a15120b060621191b020f060108030921060c25051e191110020615060c03070501150603 60
    0x400a00400c400448040500084246080c4090725040d00b0081d02d4410514030f0f82d04001c825203d000c101d9001101080104000c405042d0115406201180c3e01050018182e0300300410841d82c03074500d1000070030080140600200084032030b0304503804043e462620f00740e000b00c03080d190740104840c101858010348890443d2400180680b4240c812140c21200c800c2c0b960562507101d02c3d800c040081d01824010007240c40b181031040020071031080100401c000100c2510311000b0503c040c1c2400001c4011640075004040103104003100002103030121202501c03500c04590300c600c1803101880d19003030f5480203030103501c0c00e1001141c3c410000d00a5442460740d80b40380f484021540460700e50280d00024010340000c50701496400030542c0c0301d4801c580d9041582c841c01414111514009150314044a003a40b408501c044c407400d040300d528001c020140001c0805d030500c00f9030309002e01040d10079a80b0072600040e8440c0000014016281d006038004000d0150075500b141c10540d039030060042c5400039152 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 750400962 1250 750399712 750399731
    0xc1214010f05060403020d0b0402030307050307110a080a031d0402070602070b07090e01080a0b041a2712040330050405031c1e1b03080405060f0417090d150f 69
    0x3c0f00480341180d50040510301c035280203540713042940e00000c0050b40e25002c180070007008100300744002e020301c51042840715a81d03089081001801c580d180c01084240d4058030345140000c0c0c0040011020983c510709800e03082d507601d40081c1c00b0348201c5e10010403060010400030100302c1d1041241d40640e0050720303010450340d101e40e1440380c80c007000d104c4c47d0405d038802e02d0000c2c00b043e020794502c0c5e00320303000c0d4007109082c1285140c01e0f100c103103054420b00240b4111402c403403030450012a448040d283c1200240c1402d10000c00306540c0c50180b40400b4044080981c050072031903d502c0020317501d449420000b14946085148040c2035a0028895203000c1c3c00360301c01a1140804080940103011010384800301e20290100c103036000002d032606194180084801000c0b41d040f080440041024425540d50f5501d00d40741c50181d04200020700040002c11100d401d120000340140904074450100d841865200d003210320001b840882d03203900c0580040355840881c940854580c01c41c3d03202400c428800c0c03040540 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 750402212 1250 750400962 750400969
    0x60f061c05090c03060a1a09190f0e0a0318080105070206010305070e040b01060318080c10150f03080d02040e31020108160203040806160809060402060d0c1214010f05 73
    0x6220800c42d81c580c00400c001804001b07250b1001c08000c07454036074085007645003c04200294401d40d60982d4411780050070040c0d00b50140a40d9409088052040c00000245020540d03590a540c100805000b5059002c102540c2c01040400003040454002c1c8540c1c00c1001e00691544800e0105490310b00070124086002411041c1c268001c552020940c00580e04c2e01c1300440080c41c070826600c0d801d030340e02d800c20804204108060b108031440c6402a084086c403094040b0100e481034942c075020000e01c09020403540e850040c0b40c000300da40043d0080d5580940b100c1c0c0100910444d0011041d8030403001c10301000303c0b88141021103083d44407942022280803010090300c1c00480e0080240064001000581c100c4469070343d0701441c090034011281819120740440f03080604c100c507007a117000c071000d950b41d034456840801907070400844c00c080c1c601420309030081107207441001641c00c1c5035038480c40103130220391103075601106d80b503540b03101049201e042d54030764916582c1c00c1c481d00400544031b0502107046e00c3c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 750403462 1250 750402212 750402223
    0x15020703110d0228092003010e10030c060509120309090c0d0603020301091a10060203070605040c03050d020d031a010909050403020c120c1e01080f060f061c0509 71
    0x81e00807515001820a5008014450494107001c98104001000d1504640407041102c191954607010660b082030a180c6914200c0e0403007a1410b010000031440150729603070050480e41543c1800b0b604070312581c3c80e40702c0e02e420260940e1008164000c050350002c2c000e9403280250410b020202e43e800180250001116900d000300401140d2058400e0040b50f210183c91008080b0240614008100540e4907000030f0b0840702002d1040c0c0301480a11088180c6541d10050a9401840504c0040e152401c005000356a1701601e64010489030b585d1000c01e0a014501c20060005c6510000b00da01c1480c1d0350070000e407621001c0c5804008030b030078001b880a10100ba000504010030040e59006140d500d0514004041d1002505c250254013801012800a440301d4185003a00c500103001000780414840900c82405000c0314030041042c640c6004842986c2c2c0155001d030440d40e100c00702060b5032a940300280c100d900798149268031541c00256044401e00e20b942e203c0388990700c510200710030f0361800c40341c0d901c1c0e1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 750404712 1250 750403462 750403469
    0x4050414150d1518060c0813030c060b060a030e1b0d0201120f060b0703090e0408071202101811090108030307050c0c040f0e010f0605130b04090b010f150207 69
    0x441d0340036201c40d600e04010410246807400703040a00440381d82c1e90030803002c40700c500800380903035240071aa0b0340502030700e4028001c090311246803903181494007100c40354070400119401800c03c826569810300f0305c00e498100d4003021000a00d02680c0b060b00580190080c000b4800340413081c0190590600956076144400104107000b6000c2032440c2514ac0c011500799a4148455018513a14440c107a0801090b01c00e0340c0181280f91a240d43c1c8109a00300a031440301503910040f081580340b0704220010380d000041d90049035102010101c400560320041e404d00340041c00e0b9038a4646400d401041c800200641d54503954080c45808149828090034059413480901861041313510410100e4012803207400201302c014000c0090302c542c0c1070340741c0c00a0140d0f003d04501c4c60510391544014201c07540c0a100f1440480300b0214208441482e02001c5441509545c2e400c19405a441f008140d586d00c3d680c0104e0901940990103015030741e1160300781660b100040c000c00503007400000207440468000104403054 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 750405962 1250 750404712 750404731
    0xa020316051918020f0c01090803040b09061603020901030207020411031b07051507170405100e010b10030513021c0b0702160911040e100e060607031b020a120804050414 74
    0x800c0090395040060f6203e07000c1c04c110340008001b0400b1016003031052400c020b00c0385542d039030390742414281030143c0d4001400802c00c9402200a00c140c8484012101007111168180981c550008000503402070040000181d0401e090414100545240000951283d080c042c03a191445040e141c070b0000d18061190014650ba10a03150b20200d1090b2001c566800721440c60201c3d99a000031010808002040e181141c40b68080f4071000c01e0721000303020f0108589180c000810017000680006103580a110002109055640b070124494015041203480450380240481819445507072107040f22a5090900342d0f90305544d0404100030520228185104084190810702c508d41049401f9008000e1500c510041c0401084001003110b68205882c2c0b080c541e446c0d0000c4450f1400d0010000d40030010800c0303118000800c43ca4000a07002010340b042c950895207038101c00609403010a41c07030245070304100e8824070440800b8040000e407a0040081d254117640c103000c1d507030342440302124401046d20700c01c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 750407212 1250 750405962 750405989
    0x1c0c02031602090606040b0408030703020d1707030509011116170301032004092a0b041d06040f240e0f010e040318150912080a050c0a0203160519 64
    0x140c60098080d03600300780020017951403c2d03a02c20105c100703903016a100505e00c0e080480d0550505805200d0a01070540500b080d202e1401440150001134800400003c01e02d5540c00c04102e0b0007000f58004c00c0114009a0782c0e0396034040c9090000c2c8403811550701283c0114510b10700f029641d265205a034100c95020500c0d0030b0121145480c0b09040801080c1260015034900721b202c0441c0c500540284102181d01040405c50030540d40b808000009030805040b610080008110b01898105204856a1480a00941d984803440010081c144d00e1040c95080d5040c0b0b8a1501e0001c4590301c44a584818103034103600b2035070346d20009003042c00100c81c0444c00e00c400303070010070145078082281944070b0301c00d1510320b0120381040000c440321051034021031080c6514a611104440d0007a00003c094a0a5a000040c0400c946d44081e080d1042100040030803d002c030300300c140c003002041441c10050303009060303035008050741d8942d004001302d92040728490900606035102800403c2c480f4000d40340c6a03924002e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 750408462 1250 750407212 750407257
    0x209030607120209150702040c030603110607060e060a050108060f1308072906010e030114012d08150619090c09030b0a0603050c0a060e01231c0c0203 66
    0x1940342d18031911403280240c00b081003500d5035541d11500b2542c1e007110045240c652001d40180004c452484006009040c82c04109002040d0800900c030440c0400301c6000340e8440f62440c11001514150203240704610400c000d200007050660482d6050303030300c09411107003240d0300c0e4481d00000c0482924800e40c080020a864000b00c1e405c01e000b40306090082c1c0f100403080c007425a058258200350350481048072100301c103200503907034044801d2445503c100c00034440c013030011180c42c00c401018807035001030042d48440c00d220a510798030b16103c60801c0c010410340703080c0d0b282441601c4a1008080300a00c941a000240c400d240c82410044103a9900b84a03540c402d082501a90041c5078055014040c0300300b9003c004000f07070552943d00d101c0c440001012450301d02d0b40c0b0300303980344c012880d02c0d2074130400d8186818803001d5404000360306011000d107000b00d0100e06010781a081144011a040750440b00081c65071207041d8a0413140c5003840404e042000405070742c0808980340c2c001e007600494030304d0b2400a400c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 750409712 1250 750408462 750408467
    0x30d0c0c110621040302100c020a03050f03060f190302090c0a02032a0d0c1118370c08060301110405090907080304080d0e0a0510031820130209030607 66
    0x90080128400403815450030328243c035203190b081142e085005038001180c034042070a00e401110404607090004100303050032a54040d155014004038060781400100000301d443d5241c580000b0141005071884160f9102e0b80384c40e080350740e180c0c08142d002e01e0714007000c541403002c2c980403118240274070341c0990f007400d8000c0501c1c80a10341c48003100419904507800d90070f00784010321a02c5945081c5071601190041d403032401888c480b0005100901c00c42d00c0318811000343c030300305500d140d000c02c0c50341c040240e00505460441142c0451101100d51002c50403101703010364123990008451f649207845541c0f4590b203202c10103083c0e412003400c801c030440051008005e41e041c030100b0150000342941c203507a440c40e10f80308103a140d600241c0c8a1041c0da449140c946502c1900070024100f42c0d4400d854588105082a01023854503a0044100080556440351054050304000e0307050342c0785922483e61629a4803401402c00d0101d07400e0034607031040115029040743c40d001c900c2151424800031b000b1f0442551408810f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 750410962 1250 750409712 750409717
    0x7060906050f070b1036050a1b0f0801050a0303020a0201050a021005240f0f0f0114070521070203060609070c0204050106030c0f05041a0c0f0d0f1106040b15120f030d0c0c1106 77
    0xc1c40c4125481c1c0c08141c84140139521450f2400c00714ad50340c943c500380070000051a020044e40864000d1102c1c1c582800465400308000801540a0806581d108020001240303020b00c2e1b07803a881061850701c0240140307110000128007101c000315504494100c4080d003000340702c0007040852a84240403851640f59410000104042d0001c141400440841514079000441d400700d1003c03642c40d0481b07001d04506130940e1826181590340303c606c030f9040115543c080f0383e0b5810042c203650702c16400340b40055074041c072480c03500700d0480d4044c20030701c0a541d4400d00174001c0c1c092104608003041d81450490700d401c2c4141c05541c100c5500c001e034072490b01c1500813004c2c0789071b0280d241411710380510001501c095108011354000050241e42d121589100601c000b401d288101c4040110398101809020118104a150741d411000044151307103071b440c64800054405680c01c6072105540a0310350b030105a2200070015200070000c44c1030a0140c1e2014200407150855a800003d080340c81e507911050b070341e042c0310f4007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 750412212 1250 750410962 750410971
    0x6030e031620060c06061008070c03031a0d06060806010611070e0403200a12051903050712060906050f030c060406030f02040f08030703030e07060906050f070b103605 73
    0x200310001c011a14040f400341e43c403180c58529164083c4041c0901070a044d801040c40740c0007807910007001d00702050000c01c0c2000c000030140425442d41c40107a807904a00401101c604401844c3c0e854140061801c40c2c00303002d00d445440314a0060700000220700d4010481d0440141119024028490401c0302c596a00034000c0d0098040110f06a0160014003240c02c000c210b0707048680c01001420951300e490a56000d61900c0310040040030b00403495500900030072107514100b241004982a59100001c58480e00300c00703c0005014188400010407104503400101030311419180034040644142c28117a0b1901d49146042d00407004001c200300c8103220342c2c0311420030011100094906541c86148240000302c607004240182c00020f140302c100350305403040c03039100c0c011b880203020f10030b103840f0004c3d2400c0c0b800e101c7d003c00e010b40051076803c41c102140899141d581d00038200084c6080c90074000280603d00e008550f241962100d0740401800035044110716503129850b818048036030010500042d010141 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 750413462 1250 750412212 750412253
    0x20601080a1e020418050d0e0f01030c1206060f02060c0f0702090a02040f030b06010f08040314070c09050a02131e120203011404150c090b0901050721030606030e0316 73
    0x181102c0059603540514280300c0001d485202400c000f0b400c1140c20b01c4005490348042c8041d04526240d00e4894942c0182e05482c00d080008261612400944402c0d0400c03601140f094a001f0300803a800e50000b03a1a44800c131070740c0c211002940c40c8460568144142c13280314a01170414001000145003c0c007110341c0c84041084d016040698031024800c15140d40d0f081101c900045400304140d55a1000841e0580c0c620341c07810360700328201500c02404101d502901761080110004400f4188107440b51303401c00030004004100014a0500c802400a403c507204030303004214075220000301164040c041e152290710351142c0403026850840358411244041c902203805548503080000c00a036a20f96403417099020341500200d000e0300c04102021074454219803400d0124681301070250090a1083d44c003411400e0a041c1d81e9000386080410402a1003079400c3c07001440024404500d980c142c005008448080d1070500c8001128140c5a0b1130b40111034421215000c2149440c0104210402d2081c0402818 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 750414712 1250 750413462 750413513
    0x7060b0303130f030605070512040b270d0801050d150203070306030503070c030b090d021b0a1e031a090a0201030b01110a0804051003090308072601060c0b0106020601080a 75
    0x400210b1028540307600400082d24280d508005000c0320f4062030768062001d2504515101c4810f0700010302050107030001e0b020003c040002003007448400750f0000307041018080781803103800c1e261940c1e0342c0e62050502480003601171000002c241c00c0c015a00105075600c0900c44d0500f15100302202d00a42009100604054444e01e001010610510041603064090078104440900b03605145810507030103004c840d407660160115041c0a940403070000c51400f00f201c1d01c1401001500c002941111980d045a482e42040041c45800143c1d4070840e00b08070f920030710042030001c125120386030a28a00302d03820701080d00060002c2c00150300c80d0740030f02c0030388805046c0301094000c2d04100600e0500050030403500620001400e101d289000d03d0161150b000c54642031000e801c160350004d245413400351040e0184109807500101201c7d90980c3c103035240d40d0389500c208080d80c1d2864018040821600c00740c408100c0000040344440c0302181483c162040d00d4003e0807180480d0745c88040742c001c008116415076041 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 750415962 1250 750414712 750414727
    0xb0403030b010903240516020703080306060403050610170307020120070906090c02120403020303040b0c011107150506030c010212070303020c0a1118130f02010e040f020d0c1407060b0303 82
    0x17288000c182849865801d040d8184036406070508594000e000d2000e8000400d07100b004182c0c0c0050540240ea07401800c8a850f80c441d000488c95601079030300000e1143c002e44080013541a2094003103001c032004444e0401591013011078841d200e04c1400c0019000980e0100b120340c170302207101a04c45654685c2403c1703407290303643e840491040f03560319001082d80c0c1d511059000d22903076042003c0380c905034101c1c070220f03d814a542e0000c1c0e0b40e88181d20440c12601d1022410300940380c0c0c0ae42c050900d4029110340745d903592403a0f103407071543c802441404030303001072070000030a1043c10001034441c4150010f030024020506400c80211107038200c0718040b02015020009800309633400d000c0500b110348918055611130300c2040c1003000c0e503050140c162511414450030401000415240301120719007100e12660b00010600048407004694041c280d0482c2c1090200915000c10b0b40c000d211454188608202034484403404a803007141400303c4207080036082c005013010036859400040400e400030112844c2845 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 750417212 1250 750415962 750415973
    0xe03010903030b12060c0d05040c031203020a14030702150907080111040303020706080c07060903030b030114040213090201080c0a20060406050106030b06070f0606090f020315010c0b0403030b010903 87
    0xc44000480c00a40c031804542c0807030030f094150390782001424010704950b2900140b41411802031010b4015050741718008201030040b20030b4104040e40e00100c102580d00030000002d0045d500ca084043e0000f008809d04481c852202c0e02603034020b229a5000e070035038541c3e038540002000c4019040400c1801000710019240400740310752808a40103d07506516a0314508002e0300b0110940d200d41c05006007442000202c0765040201e44446030f00820000e00300300ca40c00d0440080a800784189d80640c0f803c420540300c0000800c4052082d03100301e400c46024a01c90b0217641c145c0d08940c030000d02080c1c0342d40c041a0044030342070240510702ca103854000e90b819400c80342000000351840b4000410f0b00840180070500c243c600902c0d01600060405005445940d404910a4440c5a030080e010b40c030030590b11000c000960f000540184991710050000e4011855280020340c002c0c0c84510a0514850541ca1594020082c0f0101c840e000f4404c40120354454900350003500d82d1041480c10400150344c040700152 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 750418462 1250 750417212 750417221
    0x271b070f02131e051905160807020a170702040c050c0a0b19051807080d09031209080105070201020a080603060636072a08180613140102060c0403110603070e0301 71
    0x703000c94000724250a04080351094001c2d1701c651110020304140c02c002d002c1e0411240000b0507072280c80d03e4070166071282d80803401d29074080381c014003056540e181c03000641010406403036858000c540801c079000c900d0005484a1141420811440c3c0000700800c005c503c0140f0180d510810b454014501c2c1304000705900704a07903080315802e000d100c0008042409003801c02040c8054050200102502c0c01c0300440a0283c181c140f00061004800f241081c00403031007101040002c181c000000e0040d030800800281c042c0d0401660300000400b0880010954070f00040c40d540a0900600030101c081c6001526613404140d000313800d20b00c2e9144100e42e610181300018090301c5140c10b65540101d849101c04801014188084605c8003a9038201c00e00c804580900221128615140200f80c0001d01030301c08506a40035240184c00d02280784000040c0700800110b004041041c2607007600c05982d101c8900640e40d010300e001c054845064143c840c881c50800d440103613005115414103019502d000c10009082d103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 750419712 1250 750418462 750418511
    0xc1e060c010203040c0e0114040f1404030e03010c02150a0e07030c090f0b120616021204150e061e070c051e27040b06271b070f0213 58
    0x20782d0b0010403c002d0024518002d005014009031045103940342120b000c1d80c024241075070910450351000c02c04074141d00f030307401100b4161342d101c0002802e01e0a401c000e003080ba194946d19000303500f0204004600c0f0310125000c030010110314084080790b22094100e00007020317207130064400c5104400300403011805c0b03440d455006020450011920040365105001600c01c0c046000f402180c00d600c0c1011025400305005502c50840c1c0308070364a070030307110030f08074603204c03840b52441c000103000a000b00d050401032400252220300c64841c50142c4d180201880410302c1a540d030b1083c84003140001d0b4030b80216141c000d240d2075018600710240e440d1640c000801c0001c0408007034403030004000415500341080d21074044030264000c428081004228404074464100078001131105c400a00002c0d180d03a44c1089c1a0088400c20301c3d880300400c129400381d00c0d01c0000395400d034540b003410211014245c0d110701c2112002c0d07a002400f0700d406440e0740e0920241c0056020140c840e251950001640c1c01911807070080031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 750420962 1250 750419712 750419737
    0x206160905011e0315081c030c020c010c21030906050714030a0515151c0c09050d06020c030c030408010614060d1505040219030b0a0e19140f01260c1e06 67
    0x344045070200c01380325107d24001b40e09042c1408065060079030003180303032580b1582c2804c6c240203c101d9403914103402c0a0302c030743c21190415428241c1c07003042d81c150300c600041803241c60200705d83e4840c1039094603401c64032011b607030301d9850070400515201c1d100d4001c80d800182e00e402c48010103299100190804105d00d0220803856000f0401c641090203004c4020050320750500d04000c1006840c100601360707032060203050b0181c01804041c804000305030b41240d01c0803101c10300341c0e0348440c42409c6c00b54495001c4d2203940d003258244200403411504128481c0301140004000074035100841d074002c4040e260440c41c1d81e00444442c000041c0f1a20f89000800c4010b154031400e000b00000508058101d904244c4420b00030305a100e02032010a00c6411015001f04a0382c0001540300d07004040c07079000c1e087e81440903040440c42c90a220040c80070307404140c1a20001d000c0da41020080301c1c0d007103003080882d02a0740201e84c010a00c0f13229604001c04003040f84005030030f08549a20304400880d405601945020341e2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 750422212 1250 750420962 750420973
    0x290c0313120302061006080106050901020c04020f0309120406083c01091404080f070206070f06020301030606060c05060f09030d020403050601050916020c04020d1b0206160905011e031508 82
    0x10964144411070f0300481d01605c00386004c3c01e1071001004480d05000d4403050200008000610b40e000b001102e14601c0c00030020343d40d608000d9021032061b0010740b400c515900c910408a0158201c03842a40c0542d0350340c0e44c1d004201c0d0754940042111400c809982c000c00d1403440703034000c052000f2032141c150f284141caa41c188654900f0000c1802c489100160802801203402031000207200e0504540b81001c00080c45503d6444600010745940318602c001890000041c14000802ca03103500614122401428208220f40e80ca020684a4010511006000b5040740740003416003d030481d82c070754011a501084034203001c8030030b048030200d0b48035030030903a080c1c0e0203070b40100814070f4040301582d404541c070441c0c240100c504a1f4080e50301d840b030840c21882a500450b240703007100d001c3e61141d99003051514028599013501c00001c2e4071200180d80c4001c10b40da10715500030034180a5200041292010394849011010343d1004119403052002c2d26030405407121500080340303180c0c070315201c06000e0b040d000c0c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 750423462 1250 750422212 750422249
    0x10504050c011805090c041e061404030b1b09060d02090316060903260711130e0d1b0c0303183302070504060b0a09290c0313 55
    0x280341150300030072035040010a03c00d082c43d0118442c2900c0485034161420801600e507108010f031180526000b05040c00c101c0a0240d45650b0305d190300c04210b0b0101d4452060145e481c4081d11011322480c0006402d4911010201c0c00008944600d0405840e1035074146042010304400aa41c90340641646800c80b50045894055440d0510203804800041a50000030a00c0d0500107048400c0330311000e8032003440025910090071040301e8002402080ca20125511006450607a03407240f0340c600070900aa0100081e03445601e0103200f50745090356448000e010a03500e0020440d101c0d4039009030608040044900381c0d000a20002c2e01001441c86a111440036a0200c0304102c280328103540070f00070b003074213000c034418074020780850345020001f2860151040000e800b0007030f071401e00726512003a0800c1c0f4061000a0b03c42045000d4101102c06a54480300250755098400100010031380440c1010000001d5020404401c0000e0142465070f10949041c0040c83c1070303010104c1071031350000c1c01c400c48444000303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 750424712 1250 750423462 750423473
    0x140d05040509100518090f0307060203180c01051b0a02060f0a080c090a09090812100f06090e07030221010e061002060f07110327210a0201030f0f0509010504 69
    0x2e03584140400e40740c034001c40c500000140100c14402c01107034403d08000210b100001c080c482c1c00503d0002c2c604403941e8607424a4014000c1d401180c00074040110003d03824041c2c0d43c0880c0003000e421050f92003a00f090799a03a01c005071070f0089a0000000e101303464504006885810151804001036800380d51a44282c0f131003c5e00d00f44c0d0003030050000d04000c1000f0102030356881c004a0a03a01d85200c00074000c09545040b400c00c1c0718014050810803210801c011520244050240030381c0e102c001440341407a59500e060b103001c0518001e142500303d0003c0090205846603000d808889c050090880c0b5000141030110012602a0040082c070356140302080440e08041c104020396141c1c40c401400c0d103241040d800c0080040180c024010070040c1d451030288104100f0507154020203aa02020142c040346060301e207884920024580580f6500904840c250380c0010f40020058504010b011143c80c0c6a00460040c80100c480e81d42d104e43e1015000c50180080c0300f003a11170111030000090074207007420305 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 750425962 1250 750424712 750424729
    0x3040812030106211e05010609080c0108010306052206060303021524060c0708061914070c1a04030f0801080304050f150c0f0a0b09010b0109030f140d050405 69
    0x21000c016804000400c90075600011501c04800c1d000588203030402c010301d180c4003400d1060848440c840d1004009042c0074582d61141c2c0c105c51041c0c854200d82e6a5420220b030b00c402c581c00405000c02d000c00f00400200b100d903044294040c070300a5900c1c482c003140c103000c150201040c080035070750155074243c07d00c10141c04000011603441030503040c0600d4034218109414504038405d50103004c5110300d940c042240c0f604029116501c00c423900341c8180b1601c1e00c60451b03030f681d41150003450b0a400c6244a48007207800e881070f03050080c03000d8001441035440712015540c44250b280102c540d090000c54210f180e14020140340d000790f100340d0740c8021004000000410343da0041c0c2040d005074000300007c105c560b44800444010000c10703078081c400c07050308269400080c001c400c0c218800303005540c120403100c0c1c40428610310b43c070303c100c280e0f451a84900440340e00300c0748404101d41c00309040000030700116001c0520100100c1c480d40c9980301a0a41644003818811ba000c40c170f40110301d001c2014002403418160 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 750427212 1250 750425962 750425983
    0x112d132403120507020a030f03121113050f030606100908030d020414011103030105010c0c08060106020a050d090e010e060409140607030c180b300604060501020604030c06021812030408 81
    0x9181342000b5a0380c001800a1096100041c60003201c807044004041c0180030800e100c0300d46500c20059002c035032145a010740d200d0000400d640c0e1000802050351301e0403c004001c0800090000d0034107545003824000910810180c45007482500003000561107000c2000341260005900c0150300c442c6400c0c107141c1c4da8965000302505001107000c070040a01800010381e0b045880c24030b000c0c0028045410300c03014110494200042d00d019071000031444940004009204505c190302b2100d580c168400119088041c50190040c215205401003114813a480001604054000c10000d0001141da03079203408410300c0ea4101c00c1a030400030070048810340510490380034030118100040903c0708820141c500d062240034814648401042e28012072041c4070101e9000d4031004085c000e1100c8101d4103070710200d001c980d01d62046046c95408030301342d4800b02d4030074040ca92580740d50f1044581962414003a400500423102c000380e43d41d000c0d00d440d80d2041e4144100b8070b280c0026641d154104041035061080007003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 750428462 1250 750427212 750427217
    0x4060c0807020c100302030a09020d06150e010e0a0f020c1b01110a050303060904031827090816020f040c08100e0c0417010f020403112d13240312 64
    0x1148099161a13031200c80901c44041e107001030340c0b5586e034802d250040010000194002c680d0204850800025520000d034180124074004101a502c9001c20b241c01070034040e0b507030245503680c0841d19010345074002e000c0d80110000c002d4108800102604d160400084490006040c018205441c42d60005030450035482da0b44050b20700100182c032059a00d100c0600040d02401403c0c0016007854420510304428199544d1100f041c141e680c00e200726410001e1052000b8082d40300200040010310340710b9108120b43c4408158141000101c81c0710682c40106810303a081300f442007030040c056860f40b041442c18041c9480d8003409040c0301c05088140702c481d0300440c81400507001070142c104180c905440c08c8440d48000d410201a002461901400300d0710381a1400c40d00100300030003000303030f03003000188042010b9624540320380202c0b04031420322840001c07803100e140200500002d5410281c580764580300b1110300c0801c07000c1c2650380807203080c2c2c0c103c420b0800e94805c6010a0003000003041541381551000d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 750429712 1250 750428462 750428473
    0x71502160c06031512081306020607030c170a1a0310240515070819031d071406070203070302030609010507022505060c0c0901060e0f0a0e0411061204060c080702 71
    0x22101c213028600341c040c59001c1d600305901c060070040d0344400c90380780f143c2014100c04c40ca03640d03902c0655103002c161024000300c0d050682d1010004e2089040040d00c4001e850603028640b00c40034080010103404000562110715502d060805450400a5559000240c0070004005841c48603002d11402c108044178804010150104416075640c50380b039080b0082d9a0000795144aa45020901c80c07095142d480d0071420300c526140c103e66010360202c01c1d440110300c481c2c1d19810344c1540090f00d0b92900c3c001c1070a2102c070b20700c2c500e1050030b01c480a840014406000c0384c103c992a83c00103840c000e4125440d10850391520104002903030f0602640191071b13108000011680740310502a40011064051240120000700d50b0212901c820000400e15101c060b08150155840d0030000305070041d492502c80c050320703042c048903945041c04214141110000c41d022a2140c0380d507035503080803409980c83e65038049004e220189000390381403c060b0103140700e0301d00003407889160003029101d000005e24042c199040b4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 750430962 1250 750429712 750429731
    0x70501090b120703020318100b1f0917070f350a020f0d020d1101030e0721020103091704030516230307081905060901090512071502160c0603 62
    0x110800079400004600f40540ca1341d0340c80b4144640005120b101041e50310031408088c011006d6a8050694010705450403d48021b08402540c0c0d501c05030b00101000824400c020040c031909131350a4103c0e5170f0140d02f96981d07141d95482414017a4071b00e03045032a00d0038041c3c4119264441c0844000c24040001101c1085201c800050540b81d05085001901844501103003080036921040008a85035001f09460090001403e0a450020701011414017003072420380320b007000a44c00240c16007158a078010500800d910302c884402904001300c000c0f41816210020b120010b1101403100702c0d444803910300c803600d862943c2082440c10701486801101c070b0b4180b41c8284030600c41da44054001c0300d1001500c1d0218070400713011074580340081d0b000d21114041d40c8980b855a4803204151b000241c0a0800c45021b500c50700032490803504810401040c0b5071102281407610b80b10a00646801405120700c0a82000c44030b25000030383c0d104481c40480100604802c100300142c1d52042d1018080901d001c000c080709 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 750432212 1250 750430962 750430987
    0x30506040c020109050a0b100906080d0f0305090c010507080f1c110403030e091005040c021510151116030f060f050601050405040f1b03201207200f070501090b 70
    0x61101c6c0038082074049400502002e8081100314000c0035040e9007007045a0ba00d81155445800c00024000000d128408660b4594441d004290081c0100e001419540304242c006580b0350f44200340c221400f48040c00b4005541c0756010180401c201080b8221a44149144010044403816440c0a0a24100b80014004242e20501c2e184007044c0940d503444164a900300320b101d0003010b581c081c903405802d1008074038045d680802c07864030884107e040c2c4000c0b42c03181c0c218440d00120038010120200384500c2c619013090b00c0b581d003010000707400c8415100120a0029040b17402c3d1031580064454041d40300d1440204031b0340e8826402103140010341008070b4105a00001d0880c4518804d041c4205d4a483c4a0844416241d2000504020b2105000b03440b0340030600c041e000d0440250070b4001c0f0202c44003050700350b002e003400b21401200481000002c1d07036140c3d0b02c140d5100c0000e00d40440c400840d01800c0c0f41c6803404005031b00d44258900020b1181d64a00000104006405d07080002c050310180040a039040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 750433462 1250 750432212 750432223
    0x91a09010c080f07020705010323270c060906030601050409230916030212150406150e0c0a230d06090b03030a05180d0b010f09110306010507171306030506040c02010905 74
    0x4209107404100380702c2001b0f0341032b4500003a901e560003c0c0c540c0700c180008803489034643d0040303110230104594018500d83d412516664100003035500050304120b02d402500c2d000c0019a402070341414042c0c1015202d00344441128441901c15200c15680841c0310307002803012030500c0e40400729100514411002009240380035016210080c05503802c2281c4141420f0180310384040b61003c1c0030445d9941c074050900d580689840d030351001c00b03098504004582c4042c0d00000510034070440803414581990700ca012107070440c5501c48403036400980c81003009907035031300e10040180040000e00802e075941010441c0b402c40740640c50f40d40c030a600810001810f150880c044ea10b240103444051030311490a840130420000094030000d000d000a80e0000c101d14400d14054419140720003001c214222458034080c90f944001c0d44c200d03000c10424040c01c0b0008803d41000c900030600011610b00300919071002c211840125040140407a0312072040200608180c41500c0b01e092007031000b030142c11140e469058480b0f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 750434712 1250 750433462 750433469
    0x20123090c0d03030f02121506030408070f0c050d0b07030b031b15040506040b0d0606090b04030b06010210051618050607080a1107180c08060a09091a09010c080f070207 74
    0x2c80d0b140304080b05040c0a5403020300c03182c1100c0d5096541d444600d0a40c5c50921040b103500c50b04908031140c12800781001015244140d50044001e0321b400c4503515140e142c000000d2049030902850400030030780d42c03604964401100d1058140e08054100060701405581d015205280039034058500c10940c4404c0b10010549090300352188200120211800002c80c030441d0880c9801c20000100040c401410b54001c10382e07003154150402585840d02411541070b8068880d032400e001c8203010030320210b0101080c103904410140101d039107240e016081c0c0b500755901100e200322860104890006855048a00254801d10410304009124240740006845002d50b0102070020720f00450124800b5025007000d50111a104085410882e035849e616242c0040c2c000d84201e02500b4034080b04080781c008c4020380e001d00700041400744000d0406854000401140000303958190760609404a501300304008540901d04c0b0b40b00118511494060141c400c03c0090001e84010f6148410401916800b180722000d9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 750435962 1250 750434712 750434719
    0x10e031f09050a020901030503041502010c0504051003180821091005060d0c031514070f0e03010902090f011a0f04060f0c02100e01120605030a020d14030a020123090c 73
    0x1141240c0c01c180d483c200402c60000d401055240010041c8400003015004450054203040711542c6040c004a00340d8460500702400704d8414001032010f85032144204200314580e140000725800001c0070b0780c1010851250548511600060303107240108407509128014154080490560405090407541c41201900c2c20305041e0340d03000418102e60f43e10300174019141c0c10861918003a83c0300c2c100064402c1805800b2281f4504e06402c00402c3c500c6d43c0340c1da601c528800c1d101c4404640c10320f20141c4203e521035480a626550302c0e0790301001640c0d1200424061300090642494a42c1499600c5070f10802d20501c1d1650030702c0070301c1202051640324007150b05880c0140b40140d201c0208010903a00110b141d14001e5110703018881d11121b2652008030130800c1c9a00f40d039050f4407055007914030411124540a580e4040c0c01041c50780000d41444100010403510400000081850816959041d50040c0011a0042c0d444107015950040c001d1002104038898407a000014103200e50301039640e43c802d4607103e00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 750437212 1250 750435962 750435971
    0x60213060210020a210b220f1109040e0f070b1209031e18040e100c050307120519181a10030f0f23070e010e0c0c100c0c02010e031f 58
    0x1109421500f0900000d8400350030711240c43c1e20004002c604141da04521f41d00382c0d180002224004c00f441c0901e0240d5098941454680070a81040c0300240541486c40b80540c81004a501001c102c20495170005007003111860b900c0d10740520050b403441318090000340300340e8000c0c4007008540e45c86449030b480800031840c10554601d101803024050694407103003198800c0c600350513003580140202d10043c5409180e00100005e41c1010340a03a054003003980c040380040c50141c505524607140340e000300e401040300d01d48442008210016030040d188101808202000f240040c00708000002c52200c5100780c000e03c0044161a0020088414400074800901442d05c01407844051082a25044010f20341001400040d04203804110b00c90011841510701c8a108406002504003c180103d40c16030b21205a0080706031521810a034954005120b01d0660740202c0030001c8580754a03100c0c51182c0c41c0644c5400c0c8100e1b580e4000545a202d4226015009401041002070010307180381141d00c0c4c1c089459070019 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 750438462 1250 750437212 750437267
    0x81b061803010603140118170c07050d120912051002030c07020a09020a14030402030304170f03030109050a0501060c020907031824052508070c060213060210020a 71
    0x40310000301020098242d480c156000c01840304100200704181403003c000d001400c40200180004c001c400000362040d00e00310030400c424511b0f41e00130200d80ca150003c444486071501c0004d02085040c0340200c803404005e10340d8490309a0001d254100030081e0304180140c1c40c0c2a61a11520ba960700c3c60703944c1800358000002401c3d18078141c01e840141d40c010380901c2b0000c1d11625400d000b580714039404000b05219054000300207804800f00ca105d40e41c0500503600b498a00903003541d4940c6000610b503c140111880c0111102007000038500030282050045801c0c100316050004035001038010030708120b0400c2280015031141d00c211a0850014540050780c1d8021080902941d554258000c2001d06403c10201401c801c50278000080384491008109980300da075140030204084810018201014005131026070f400340d602503603c4034090410f261265403590340c200499019210101c180c1001e401b0a12072113a04106d41c051003407101204500e8141d9801004c1c2201e070b010100303100d0000d80d076520360 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 750439712 1250 750438462 750438487
    0x2409020903150403081609090515040b040c0512060a0b18090c07050d08060301020c0d17010e06100302030606190816031109090402120607021f02040b040e0402030114011707081b06 79
    0x7c100811114108008a04004112030010340d05452001d21650800c8212203152070181309010203000c042c0c80700d43c5403130b00244101c0400100182240c0d8040f098090001e1003401440c001d00402d181c02c10910103070b072440e0b410460702250262407804907038820f014000000381c00041c5140380d011541003040895880c0f40010303001e40f00d08440c0990710700551451654154218001401c01d200c0310090351101e82c0c0782e80016a14101c00c0300d05952004000516100c101d009600964000c0d102401e440c1c54410641c0f049080326800c10804000902c80c8000c02c600039201305401c8101d2030305842c0034003903040f1014070030b0824010340309428880c03c40c11010800315a203a0720380c4102010205d080e1011458143c0300a52503144015035031084910140354851242068404c48054803c0c0c21492814103040515443c10040d0042040341c142d9a43c58400141503d003001090080c4075001c4180314002541402c1d9080098070b6205905541c80603400c0008201d58988141c80c2d07090545066440f084000c600b07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 750440962 1250 750439712 750439727
    0x1e0c0a1d030f070602073c0e012304090206043b07080711030d02030703020c060a1b050705070308030712020c01020301140d031224090209031504030816 67
    0xc1c0d15100b202124050301a01140c82c408407004d0340c00351480d4513502c1c030703c00031041c01c201e40a580000070f9400107003a0f4018041c80c1482c5804803514112255160750300d602d260703402a0051030584403080329480040352941614100c000d41502c051084c0c0b00654082810b90007203010300140c882203995030240300c42100d80302019505a156081c134418142c0880e54900c40f10a0b01d1050000381d408002900043c060000d400740810f403000118508098000c4c0c590003900058249410903800b0171040140000801c09a4050700d0352400004980d0541508a100c800101c024041417007800c4c40b41e40041080841e10b2003c8903000700c43e0715982d581d90300f4100c2e0620f04030400354415510105201d15100015809103040c0c5000c0301e002240801d052040105044010000500181035004c42c2c09411780390303030890034181d201654200105100142d4401e1000c0b82d41e002640450ba002c00c804007a032408200f001500c101e01074003c404c40c20640c40041c4011402009500d20140d0000702d0040700e4444c405 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 750442212 1250 750440962 750441017
    0x316021903030b130c090308034302300c1605040f060803030c1b06010303230708032406071b0b03070203030103061a042a02030910030f090215031e0c0a 67
    0xcac0c0581100e0301086501840c1415180d020390940002d04c0b000d820700001c0c0f10407000c0800e40465407051900fa82c092104402da8060200e8210f05002c030f102c0100c82000b821000c0c00f40541c038109468140410b00084a0307a98071540c0c40581440703c00c000340c600120489400481c1c41044555a0900040028806002c1c605140b241e10405000209040c1e00030840001c901068010940380c2060b8042e074402802100c030050000030040020900340c1c0500c01e003010021288050802e2446042d800041c22070b00b2591040d50854190f030b00c4071450048480d203d030080c00c1482252401d40c04c1000009607a03010501004103c40d07034800b480091540c01c0100e440c90018002d1051119410f0317901c0e4200048180140c6001185a078000d08c58410b00100585a403a0741c003805029200c0c03a0340d01c00f10094070703041c0703800401280e4951050001d0380f6003503080b07000c5a11880e10b0641c6c9003000104600780c40201d0b04686c04560303004090003120901101103d820300a01d00d0001c18002c580c04032600c0c20154401c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 750443462 1250 750442212 750442261
    0x1b01051302191e03110d0c090b240a1e0c03050328020a0e040e2e1b1d01050a0327051605150316021903030b130c09030803 54
    0x60780001c0c03140e444543d0a5034803d280c00c22038150100140706c0c1c03032149904010024900240240484170781540b210801c4c001c014035460032101c0c06c01012241315020014103152080004210b40c4d5617820184070624004200c50740c05c54484040d5005202d400c6001d40101080310002c080368413810890000b181a005007070303204061403100b5030603900070341c0400515000300d920424a4035051130280301d070030030902d41c2d1130103428a01145105220043c03100d1070f000c03a40200b0002c85000c2e01c9198031600602124145c9074100913401c0d02000303082d074182290000105d0210418250407039a0000036103031352401500300841c600056070004501c4001900e0300c43d034040b000c542c4030300c2401400603000450008000300d480e0402c3c2c13a8414011460680e410440ca40d02c41040462461550340c84191440342091050703c405003a00840c007028450104010f400283d2281d0400d191407030b061142d2205103111120802a40c1e020072000b0b1b0081c1d141c0d20016003049004800905008440e21410903080c0c00c03503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 750444712 1250 750443462 750443489
    0x1207140d1208271c03090b0402040e01090816030e1f03020d02090316031e1a0601020a0203061303020d091511030f070602070b010807081b15030901021b0105130219 72
    0x4510075a56004d031804010f8504a000951000090186c800c0350a2541c226100344410f0386c42d40c0901c80030b40300380c0383c840d5029940d80d4040720101f800f80b0040c1201030398002c103034003c0300410300b8001c09194500070002d10078102007024035140820315042d00c603a02000e04002d0384508025610200034025a03140d503400d4003030040c00074403803402040c00c241a80d22034112205410348454004003041003003030004003043c5400c00d00c00111030b5040703032650f03000b9030510469507200d2440c2c0c04242081c2050f100c540d40d120702204003004043d01480b40e8001c580480c0b0b810348080746441c101e00e00c400359080d1000c003031105110004070151007e0040700e4020690910256072003c05103001e2009501815040c0c0c1c0031903489001242404020802e042203410000040247d40755102003540134000d4600c90b1036000c1c5500b01e100740242403c1001d0340c800d08100d000161500c210040d40c000004e003107a41d50703040340d02d018200b140c1600580001604960142e410107480158034481005510342a00700480318440c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 750445962 1250 750444712 750444781
    0x4030b070e0111030f16021c0503030f070503061e18011403100506012a020405010b0901110f030a051b07090c1403040804050d060b1207140d1208 64
    0xa1040700c56180a83e124200c1c440d610030025101c3c000d0710042400e0031010060b02c0240c00d04603101252407800200301514090410b03402d5190342c0070780b01c4115202c0d000801000340e81d54800e00764661008060401c2807940c64580b00040c294000d8144842d1841c191a0000030152546035803040c0140c0c08804448085d6154190040b90740004042c0a10900c01c030302d2200383c5412a40a054001d04041c1c40c4c0302c203202e40c00b5032204140100c0d00b44180c0704485001032140035a40301c1c0106402000d00c19105913030780707181d08001404250680180c00060344207680301002d03000b0000449a0007003091506036250030341c408460168644000d0403114512500d500841d0300b14813588a61681f842c9074491010084600120039154001218003411103c1d0900c4100800d00740601610001071080000056006202001401d4184011004140780c4d0001c44207100c270390280068080c1e01002102c1a070301508031681c4047d1b203020507035408810443c00340701140702c256040030a1440720309240060105074030b2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 750447212 1250 750445962 750445967
    0x7080a090204050a1a060f0313031b060b1206070212094e0604300c0507050406080606060c01090c0602010e19020d03180b13030c05062d04030b07 64
    0x10f003030607110f1943c059505aa5003511b008012502c0c1642446031ba00d00f5591190014100844c00031070a50902421815881d420a140140c4a00f51403140d41d0004404068009020540c2c45410709148203500000500510a03000a550000c14080310340066444440a012490007219200552680f0b00c2420f00d07201c11007040508403840c002040c0d0b8000d9400c0506896080c0d0030081640c682003900081c0115001c658081e568203044000da001c3c0071465140d00703807080c0407021a000b41c600003c0c00e1141c0c1604004040c80040300400d022034003807000c1401d0807612511100c000d8240c40c41260300144010041c50213410608d0b100b0b8004c550107030169135a1001a0107042c4c2000030540320b00445000903141c06046400000300c1e5000383c155942a0801d40e030680c0c00110b9115104101440703000c0000b450800c81008040e01d81508076150482403540c0b0f84600b107111590030081c40750005100c9030510580c01440f030201041c5110b15040c180785071281c0e00303205220300e80001d0100500f940400000d645c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 750448462 1250 750447212 750447221
    0x60f0f040311030d0816030207150507030605150a0305060f1f020601080105010e07030e0c0907110c030d0804120302070203060708010e090a0302030d0b0a1707060216030b07080a090204050a 83
    0xd0103105012100102d92040507215140d040003000070070010004641c0c2c0f910a200848114105030a0061800201d529032240322030100e00300102c1e02d40c035481001403899242c01884010041030b40c410301c0d41c1080c3e444224450040d44a040304059171400001d10380c0e03507517075806600c4042c0980035402c610a41000e24400d031106101c200d01520403030000041c041d070f05105c1c6078126022400d85240c84d440e607010890203048202c07080040c9100d0003012000316a01d4602c040e008a001d84c80d051215420035180c2d40c10681030b0720809100b5082b074030070303008400e42218106500c682c1c4a40034400038490348d80113400034003c2c03090183d098031500041080301c5422000c850305a4100080d0182c03540d0302c1140e559912064408010010380040c042e140f4411280d810034441c19170020408014243c849000140414405034103410580c80030008110240e0144a00c0884007146600f4601c1c40703042d6100d000c1090800303002041041040000101072000c41c1d44241c0c210340d4000d00a0100d418a00c2041c000341 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 750449712 1250 750448462 750448469
    0x32309060913092909060105010e010507060507210b0616032a0c0b072024190c03091208280f030903320310060f0e0d020f060f0f04 58
    0x264440f1000010b98a000105d100e00300900003451640c0c20706004603686e4056680144c10f03c031060014000183d414007500d4070400490b03903012070506030b03060304800d0f00d2459103070342590624107820030300152a40000c0312519102c840082c00040c417a46001c440c50030700c030b800303c6145002084100b08411601d060a04c4400d029440200d51701c1e4550407024081e1290b041c0043c41040303010051104c10080643c2542245002460702045040f00300c0c000501c00040480c81411b1580002c041908031801c4000f09880c14007841e140640c8a4030780d0707010b4032010440c05080030800003034501e1820070480604680c80a408a00c41042c103140105c090f0911040d000080800315008002c0000d181d0301c07070b22907500c006816603624460200c89210944007410420f03007803082d58505030880c0e0490f11100000307600a20800400c045d4091401400a28a581000a4604001d9080c211282d20381d15051410001a0125002080e01c401400080c0c1d25200b001112100c1100100e2680050701d071a00151040b03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 750450962 1250 750449712 750449753
    0x2a090a05010815040f180506060319020a090f020d021603020606100e04090c030609030908062d060a030c0b0705011107170307050c0102030a060303230906091309 71
    0x100c0e110801034542d088201c91410716803001010884162500d600000301c0d2000071403001900d00418600c2014407106014161707190ba0141d01440403904040007038100c024440c1c0c25601e80c055031a8005214040b2034458040e9141e1604a100f0003d205503045404200103004215a204440c104158000d112014142e01501030400000c14505140f42541c960242e01d0f81c0e054042c2c195030b030402004183c600b40035500c5a440b20b0f0003000054082c45a51045030194030340b07020701c5103000384803031400c50300900400d040c4002d07601d00d0070400b0000504900c0010007980c02502540c9020101d0b000d441244c1c0090000c01c40040001038096134070b001000001c0c0a04000d10100b0310050002e03805100e44000202425001882071009040c240007554000c4503a141c95403030a4507070186242640c1094840c0380d100c0da0795250800400d50460201c10b03104114500c2443ca029012540118034026a0031450003074400107004000c9075517181d0500c051946c0300390104801501410720004e00e801c07030701c4090075 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 750452212 1250 750450962 750450979
    0x22115190e090115091a060a03090506010909030c02101b0303051005010206011d0603100504060614091014190e060907020a0507060c14100507030513020d0b2a09 71
    0x3603160040c018503071801401402000c841d0b00d85911500102148118040706c0301510745800c0c0c0c2641c55400920303404010b5500880c200006048c96411700c00182d001001440c503080322040000c0d01300c503104000c6901211403141d00c0b0305000c0b003030701c4011070407034844142241d2501c01e408240d00365100d02d02581c10002c8031580142c50b0b0340166550b00c820b00a00001d05e041c5c400c045101d1654800d159031110b005003d075401c01d40241e14860a90700152811109591074039400d100e1410301408900420404403990800d50414008490020307066000e00300312819419280306864032000100b1640e100d124031410841355485039220b940138000d58001e442180c0c1c007000306a91074400100e83c01d1103500300c809043c1007842c0c040d00342e0307840504080c1110015004800c02814a134240700304450036454030404a5586007001c0020100c540c0200403005d82c10b4494422009a19042c1c2c0003402300d80c0c0b02007489429190001c01c1d9003500c261000080c3d41101c402c0d44515083d100c2c2c0042c00d00c528050319101c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 750453462 1250 750452212 750452221
    0x415020607081b09100509030a112d0405060a080a0b100602070609061b120c0b010515040306050411040507091707030b06130e03030c090f0301022115190e 68
    0x15a550300d000d11201020240045505490f2242c5c02d45c05070300c11400c000c1e18002808000c2802c21460340c1e000e80e038403101c1074065a0503041c0300c0f180f60152010740e4964100740500c0b60342030090000041000380516a54400034505840d02d0082e2000b405074042282c0c0108058a40700100c80030071650701d0b62010030301100103000e5000040c0d283c20f81c3c2d41611900e219505001c4200c1c1c0c1441b21f05081c080b2071840d03008510224416003040e62041d00207945144240e11030342400f414121069000c0b601915800982981584848042d50140c070340c44040070550342c40360704007100440000382c0d4495001c1e1804040c00890354100302010b0861301110b0b9603508041d04041469115a12444050166221000002d26500e49000800c0031800c3c0b607500081c241807020707051455900121080c060300308002907448028a000c01803103500f51001c42c020b6180060050306504111008050a02e9911003480840d030100c0301071720f00c1108580050608490408203407800086084907200781d03013000c81000c0108 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 750454712 1250 750453462 750453481
    0x27060b06070314030405120a0c120c0309050f03011508150f06010c020409080712030b0a1a12060a080d0905010e1e010e060f040803131d011a041502060708 68
    0x85081079055200c2c1202c80c6049210f03040c003a480100b0032111401502c415160300d104243c06040c80c0d0f0032660318441c03a00d05511348a02842c0301035503414240b0003003c100d2030000b40d01042a1040d100c040d2201c0502d01740800101e4050011b52008070052b411108011986202c000768a0401c0400c800c050b52864440303007480300c0781d804d00b0341e0f0690024038051341c000d000d410f041d0804112103119203401e80ca003035656103d04406e64896040d01c0c0c0002c0d01c5191041151a00403650005440d400a95440034817401c581590301c2d00c58100d01e1442100c0d200b000605954a00f05001c00802d920342c20742d4400000740c40c00900d226518060603002c241d0115514100703081c031080c0302012040750a400b41c5420b03913010040d0742e007640c403d201e65440302c810840424014503400190005020810044d41c440302080c81c441103698558206100c401070260b0a079006074405000b480c11245c5841c0001c1c22841d080c6c104007403070702c00c0d030704442e400b039003d0340e501125641c0c0096041d01c146c0140c1d40e02c44a030b80380c45005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 750455962 1250 750454712 750454717
    0x201080f04110d02210c0405013302120c071a03162f0c09071106010603020304020310020c030d110a050f030c0712020a0c06020303060a09020c0127060b06 68
    0x1a06000d040d0001403200e040031080364101a00003411103c0060030903542e140350f81e41000415690340c00401c41c090300c2d4201806180c0c0500040318032122b03c0724102c021102c00ca500ba140b45020b141041c841101c0403402400204021084104940e56407070303500008603030710205403240754059070fa0b2448116414400e0001d4034010b44c815403d070300301030621034401c4500101503550188403000391129110b051001200c000b004c0801c00c4050705c1070f03440c00d030208200904010f0000e030034030502d0700407419210340206042d41510841d003801a101c1d2114008030b4079084150502c03110fa40d100103040c0e00f091600101038000614003180c14400ea0241d0000441c51740111048240030078024803c2e01d040002c060301a540c004c408102c51410010591524040905148200409600005012401c0c40400e40501010780070a000851031802c000c03000c140c004140c0c2c400c2054003540410491080c5000b9003080001100700d01d044100804100450160a12061401c840903403521301543c00e070381025020b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 750457212 1250 750455962 750455971
    0x14030a0908030711010503190501150e041109090c04030506010603020301051c0b0c090d120504170604050d080910060e07030b15040308070f050d080412170109021b0601120201080f 79
    0xc4d150759a1104001511150009444900303080052007103403001d0100e43c81018001d040440703101c6040500400c0c05032000c0b10044450b8000c508014003501007180200480f110400e0a4030200d40550303c50840080c0d9015640009006000d000e00010701c9a07450b0f00914188c0b034003204c0032203c0816a103518900090806001018200400005800d03070f08924090101504040c10400d4441c00c1c6540e56182c026102d4410404188081420b05c07101f9840040c44a010400d00f004180d2401c0c00d0300c6076543c1d403030020582000c1200050004a0541c014071554502d0480d149050040c031740c0f42d4000e5000c12408603824800289003500f160740038a0511500951802c14001e21482d00e030560701c034203030103601240c400d441c01c0020302c4840001078010085c466404101380e071203024a081528100c4800500c840c0b00c0d00400450845c1a8400b100801c0403c0c110340344000300580c0d0f500c403030b064040d0100740e51006020700d01540d0f0001130324620002d0600c011502c00d90301d5442540d20109421104101640d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 750458462 1250 750457212 750457223
    0xb0c060a05130c0e0a0c05130e04031407030e09130b0c09190602011e1103160e180105090708070f2712150b060f130314030a09080307 59
    0x32a5204031164042500502d480061038000450b40e260308025144552110302d42028110410411000724841c0c043e4201c684d140540c5040592800320300b050365103020300b00c003403414031020070201801406019881c1400f149800d403150498100902031095070030519014540c40400a00314040300c092140310ba503807101c002d00c8144c0326100e0032072903500b015100c00e402100143d00301c04221240541fa030000d156a50010502c501c1e100e003c3d40320034440c180c4042030300341094a00d510310342004060300d5110f004403030030b841e15040103d801c0301c0c00441040302581001e0340403542810842d521082a0603500199010041d40d07c5980d011181d4050032504000011030031603801040c1d910408202c1e0101841404020341032480c4515103d0040c1650b2290001410700e84400e4108000081c46000810401c075080100b160300c0008100c0900c1800c480c3c00d01c0f42c80001d150481d554012403d44051170b08900300d0b0043c200007190030f550781da00c070025580c0866040f010008050303000200b203410715503000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 750459712 1250 750458462 750458473
    0xa0e10050426161502010207170a122c060402090712090c0e01081b01051b010612060504050f0106050a030210030f0e1c050405060304140f060403020d090b0c 69
    0x5411420801c128a10701000c40045164161025400f00303c00c0c1c0c0d4600c0340407100c01d080d900c2c000081000c81102c40d0f8110070743e4014000a0045803010b495050140c5e43c990180ea80c0d0150384000312641160a80780150b01031400c10058441a222608000c0961384a103d402030750f09105902655544200e1300254480c1a81b400608090300c1000951000c008448000c240310b03866603241031100c8403503080034503c2c0c070703500e001040750784030030800c011824401c0d40030100040c0e40305000a145114000d000e60040c0051080151494800d511590081c4000861403101103994a0080e01410302950b060320030f4411900d00904003001849403608480000b418031244918650078002c1382541e8102801c107160b982e004002b11b044840c02445540b00c03941d8050070701070034504e0001c8021200d2004100030003d0a1000384099101e4404498103c0d800c050f216a8565014030080d1a0502c000e4514545005450610040580018102d00e90116540301ca0380100d44030031081816004040519413540d105 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 750460962 1250 750459712 750459719
    0xc1814040b0d0c03050a0c0510080c0c1002030901061d07020601060c1103011401050a0b04080a1707020604031103100e0604200307080a0b06010c0f06020901090e010801020a0e100504 80
    0x6944054400038001d0848a6448419107503140c40343c15079881510a41c0054048a003000002c001c00d601030001103440425005001c1c0000301030303800c018050f800000c00080d64100310300301005401101502420199901d143c43c2038035034041c2186104480b214080c06c0c580044081c403089419205050390340c01009039a180c56801c5a05000000040e600c2107006180300c641d944087c001c0110b400c2020008801e2541b6200501440c141c55a010180c1c40c402400188076043c00440c031100b007150800d0301c1c03103904a034800544a041c821064001d60086001400204100f440d1100c16014403044095555181d03003d0104010b50300342010190458101e80000b40009000380441c4103051083d110307440b0003c51650101c2c2c6000241d4003d05d016902c5810030764100041c1d0035469074400001e20340100c01551750390300c0115950941d00010701c0a6008600c03e03211343d101e801034038002c1c4122107410460796582d002640c000d610040010740080c40b840101d4030705040c60000c4420400107581d900745002e00e03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 750462212 1250 750460962 750460969
    0x1c05040b0c0318014b0f0206060405070c1103070807120303060806070903020d060605044812140a0906050901140c0901020106050301020c03040e01080a0803150f040c030c1814 77
    0x40c45100122005001103c0054018181d10814145450702c414414000d0b421000e0322301200182070750300c034609000402c04040c1e44848000c0b202ca910000010125546900007824019241c218010031b1150030000510081040180d0400300e002e518200f0995884039542510b440003150840003017041c0840030401170038041810003196025680004001e92954001010389900c005030b12143c05540c01d0701f442c500f1141d8503007900c0520803003559240444010040c01d005501190a0051100c0702c1d4101c400c01e0005c2d005040002c80c0c07840b03901742071f1420710300300401041d00c51015580e480c9401d0000f09022014800d100d2028001178240c00140c0e56004010f4172a482006514115500d84400013640e84090015003075220f95817000c0c40d1500e06040c4040007a0780140e1103030a007680319160203c007203825902100d4000c01204003020b8647c152502107941a512000003940003407400f405151980d50542c030103400c00300d480c1c0c0e404181410110104e00201c640d0b0040c0c60940890034001c100625 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 750463462 1250 750462212 750462287
    0x106020f150a180b01050f0301020301030c170f01051017031c0b04090501181110080621060a0c03110403020a140a0b0c030705010606050304051c05040b0c031801 71
    0x10780040f5075803900c51030046121034121012201c01d188072005200030310b0300b4413210480040640085046601d1358450446652041c422048500000080d00c0c1c880d41003442030300c5800750f060000313000d2410b02c0342c0b0701054540319103d246240b07440a008200c030b0300350100440d400001c071071860700b074400751039001d102c01003950350348440d8803d60b28850200007400a0140d04021242900f121441d45224101110400b03401c1c00d25602c070b5480101c0b8000c00039049014103800440c01d54056034207001960186d00b2000f051441d6000d140700308030811400310142d400c403541d81c0b0842d5405004022644074000604d000e1400001c2d8404001c510a00c02c01845a41d809040c4000405030088199038086c04141d56101c9a86078446810000707001060190900401005014a141c83c901c2c61404d030304d4941e1078007841c5d01c040c51010a0721740d21100c05072140007640c01801402c04803941e102900c0300015034961002e0071a04806901041c078417401d60046400700103803071741c651601500c000851405003c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 750464712 1250 750463462 750463471
    0x3071505151207150e03160302011b06111c0b03010c051b1207080a020f150f091018060b0f0d140a15020a0201050a0e0d0f03180501140106020f15 64
    0x784203c0d02e0000320440e44012120540030b01c1c1c3c803841c004404480a05041c008007048414042240e1002000183d074002c0305062038a041100e500c080300d801e850060007400c3e13880f2003103041c198041500030130388001d0710840c0e40007500010200041d001e05000d047c2071b9408141524046081409100400140703007810074600d07189003040d9040082c08050031200794004020079505a440030801c54483c9404001c9074464003008801044a49082d903540c90039030500a0030f5040400407076002c210b0741c0004122004105241040900c80c104051081401e4401501c81c00e84002d41881e6044495040c030010f0450409800f0705a06400c1c10b150300c0341c007920001b0b1a0a0303105032007080e5010340415008803040c1030042c3c0402000d130381c0d0004641e000342925009000510524030302108441c82940c00680b03103044c80d60340d0409501800245501798002c2040c0c440d050081e014880d1000204031701036008002168404411170384590300d5902c200e0323070782d45444800c805941c841025054a070b01040c4115601 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 750465962 1250 750464712 750464749
    0x5190c08191403090d030309060227030d08060f10260709080c010c110112020301030f02010306060513051c200a09020918100302060c0307150515 64
    0x1992051181d181601c40d0014000800c088000641000300000b030412841c0000b0004600b070018410018400100c810030040c00d050b59103000004205140d0140c81c16034502e04411005900c07425000c0c3c041e03409d00410b9921902032002d01400c4540a1291140070700d4001d402070f1240030801050152610794103c0080070f02c5083c8035880b81803208100317070902000c850b14203090306082030740001e08a0001038004941503001030b4a1415180d0703105003480000c98003d840c5140b0f21000c4001610405002c20302000c0c0316000000110600490105080c60b0502c00c0c1c1c0c00700a00c0340d440341c04465600501200200c42e440c1c1c807104102d5440c00c039071a46c1510101e11070309442b9502e41d41c0c1e20b20410011280a150004e281e42845c0800d2401e042c40740020300c0107220962400062100240b600040c10a00065401c58840850b01c2006a120031030302a550240416a94030300c0540c1881d42c98100c0b038422100c8026040075103200c2007040c040e00d400380c840c40480d04c0000001c2e10802c100100f501808010b03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 750467212 1250 750465962 750465983
    0x30c120f0203100e1501140d1e0c0f0e0106052b0207031101050c0301060f0809100e030d0f090b0103021c0602040f0807051206061509040f050f06030a0519 68
    0x241c1da06210000449a00782000901a032200075000e05012815405c80b003000a008010041444150045000124111580030003102035180c000040c030010402e0141074001d03c41c090041082180001d01583d054112102c1250390359464600003aa0902542c00003c0c0203001d00100c404500c004194000c542d8a045c2691010303440d080380c200c1e0088001030340000c2d1704c80d80f00040c1003001e125944d04600c44500c45482c56040401c082d00c5100c10000f034030304010b204400600801c03814011540780b050144802d00c2200924081c5581d680c214000c0806120700c0c00035610500c4003540b0451491940c40766800ca081c2c1c2c03035034081081c41815011410300d40700c40c0455070030020349584000c3c00500060f45041083e5801c04017601e242038030540115025000301d15095214140001c0c40310340c0400c013100c0b06c001c09211020001214000c2c0440641c00508100d26540b140006400207841440030b47c0e10039645903074030b07010907548805942001c1c1842d00b00214940701c4041101100b000d85001341100c04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 750468462 1250 750467212 750467243
    0x30121051903051c06030503030c0c0a0506040303020301083003150936060615040308030106020102030f0604090c0e1f091b051810031d010e0115030c12 67
    0x20300405404800b00c001490014900301c0c0c19442d064030a25029484d0703020085d0380c0c11903540a9407880040c05080f0000e00104031311190750320802c201c50000e03a0000035140b1508142c907015019420a011343e0003031380900a006030010241c1c0403048560750103480400081c641d0550311042c0303980054215445500c41c4001c1e070209484e118000c0f4001c0c101c2003a28910142c0c1c041c4e03d03c0c000c071080c0c400e0302d010b0304c3d225180005450002581941100007100d030185845405062886c4c984119400100107590200000424580640c090741c8101e0410b04103d080344d0790301040008440e40c890b07008201d900c10070ba050004505101405e5441004048109000340d00c0101d01304600c038136940814201c80e19680301d007906c1501c41e6455810020389042c12030414800d54460b651080910010500486028034a502040d2283d0441d02c0700449a504100c4540036156509000e00f5100b41014420740c240480c102c140454124100e0860f5000070181c401942020141d4400c180300302c809030303562448120b007007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 750469712 1250 750468462 750468493
    0x61d0f06092e02160605150f040203061206070e012307031404120f0521040b030406090c09051e070f140c030a02030304030e0a050108360c01120203012105 68
    0x104151000c80313401042d03081d010720f001e505446c40140b107183c01d08014111600c1948814605003040c05c0d0407640541c9950301d03c00404c00500c2110700140b1715204620620402c40d81001c000c1c50b294000f07030394002c200000c50100c1e2425000e8a074046208920410446020911600841588000c00181c140c90710760f0380d440d280d0b40424428025510a00348401c02420008100a511183c0c1300c281c1a4075446050b01c2c081824902642c8a0300b641040000000b900704a002d41c8440c1445610072142c00300c0076103400188006040889503a824250498074a80c0308540d202510f0744200c030103035100c1d0500d1080a00032104180c1041c459010b01a00f4400340344040d4080c0064910300400e90300135610391070071382002801140348981c624000c40c1d0010b000c0c03210347d130b100c011103520041c00014800c0000c800c402c1c035260b803640c8030880c00003c00300e0f0380c00c1e001c100400304a041420784c09a80b51650380d0b9400905070128402840351125644d4540314452a900e42200d5500c2c4070350280b01a1800d0740d030401c889 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 750470962 1250 750469712 750469717
    0x2090708250323091216061406010f1727070308091009060909270804150905030613020d08030c030711030c0d03020c0703061d0f06092e02 61
    0x481e444540d0007001107051032020039402c41d014980c85440c1080401c81743c0b01c07045600e050ba2807080004085540300765800071044400e80c040303000c114541105c0706191086100341d030035a00042261068161130345c81000250354801e142c14040d08991218551414501c44c0a040980700301a03000084803504814400300008600800003565101034040c10010341030303101c210350020b00904100c10301a06a000c013458041d130b4002d182c00140c04802240d115004c1d0140d2003001180440a841c1904020840740074004492405580719105030310203505441700301c1c603405480e4240d0712000014001404000740d10060701d0020303286a0328803029032141051540200c0e14072100c1d0b8000824040c0d810790106400310900071040166081941c07003004580c80d151184914020550041146403405074140706401c011070f0711070342c00c0040a14011040b1a28a00c1c040120400c0c000e01d580901209000300c0c030140f1605a81c4050301d001c045408071060640b62090382c10302c4208102103083c0b42d07142103100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 750472212 1250 750470962 750471031
    0x130506040804060306120c1401050c030a030b010e15070b0402180a0b1008010608340e0a0803040b0f0c031b0a1401150b0c0c06030103031107050a0302090708 69
    0x10010340c0c40f424207001809a03859036020450383c01e8103401c802c001c05d0800182000740c42c265410600342000c6039004031414020046540e0a070301002034401c4480b034060f8840c4140400030b80741c85074840d0340c0804208032030549140084134040100314200025a01d40f85003039000d880203000400001c8040c441002c001c1c0304940800d105907544454040a150a0181040c85041807502c1d160540c1004401003110304054000091160000f4174009401511401804102c0c0d20190b2091441040c0781e00829880343c0e80041c50084c0440000443c1c110800300c205c8042d54042c2001c0351070006c042698407043d50010528400c680014484a14403c0b01010441c00e1a07081170000c10200100b030070081101040014034045a0389000c00641310140b61181c03000403201c0c900d242985541c0c0903224a801c0a1b250106154401800000401016000350001c1c41c050040000ca80800c0e031240d041c0800b8416900000e94803502f0000004ea61501c103c1c4150750001114800d0b400844401c100700c0305007818440e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 750473462 1250 750472212 750472223
    0x2070b3702011103160318060e0106050108180c06031503061306141b1612020115090c0206150d300201090213091b081e15060913050604 60
    0x1403524a459090080f009920207a010391441d40c1000d60440b0918501111164289a2510105002d001040084140c03183e001407050088641a42d0024003c22013401818042120782002c40e200c1c50154060702f1a040c118002401301340c000b8401c20903290001805003c0300c81c80711a14580c2c589040c4100350144691000d06010b1100030b1509009545103115000c092000031001c0013a18102c1e0321140010003504c1c0012070740da008544d00e4984000a6110290004074000a00111194150b21100c11207010900d00a040e036116524407058a4010f00c4800c01a4040004a40c617115040070020f540c1c5401000d412548920340d84540743c03261351806020014081d9800031042410003850b01c4072805040c0b000f0800c8004a40c00984c030040035441022885079118421001c10000120140100c5620400318140c9a1341d40441a501c04820111031101042036076000c014141c00650240703e09404040c110300303540e8143c18030014200051001070000900b21501b40824000d1081500844c00390 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 750474712 1250 750473462 750473557
    0x20120301031101050306100f0c06060e07260f0a0b030109030e04050112020d0623040c030203070b0c060a2a09031b050913032105070801140102070b 65
    0x500b0045240030b01ea0560b14140131040040014603514414000701c07200c52410041e000904044c804c41c0e41d0500810014410780c90860046004901072822621500181c2d40d4441c02040705490001c0b14580c0c0300c11f00d000780d081407000c5404240032580195000040b0400088d41c036280c000080d0a50382c10000c140d0116030b02c030340c03c90a9412b0078040c1c2409003510081d6400031a10350350103c1d41940000401070f02c9160b40394254840840c900c401036441c501d40340f554407410300700b500780359850055034482203209104030000047c2d40c905003025250880051000b420a039030f10009480302420240840740c6120488034400c501c0c0480c14045840708000c0341d52141782c1c050440c500b45041500d00b004248465421240030410b81e130701d10b0100c1d90300c07000300348041100d070701a8176040d5a201c10400422107003c801c611101d07090091684220b2155040c3c1d0749481481c0d80e54081c100042140c810240d0050300202414446d80b0144001418403544003002a0004000c4000a107d080610003a021441c07000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 750475962 1250 750474712 750474719
    0x70e150307110d0c080d1503030206011818020105030901110a0302090f04020c0703081305130c26070521010609150219062706020a0216080d20120301 66
    0x9200031180b641030004142c003095044010f455484050710041100000003806042102c403500001ea1358004207000c0c100071505d92401039250a024000c0c9d00c11440800c440c0d4161101d0350180c50038075543c52080c181c2145407a0011078255200610b40b00c011742d2500808000140100c0042003400e05540d0014cc44641d214104040c0030311041c40580715034018048c0c0307109a07501013424000c83e903000346038070f0380c451221010301c110001e9644603503408281000c0720b410441d056000030300000c940d45e603042c84003848060020070000f07940740066480440070002600c0140140e0040000b040c0440590060084016105c0c5903550b09030031110014204900800800e034003c900c0d80d0300701d09180080c0055036420380b403004004d241300360302805060302c03031005000702240401030744107004146151616140f02401c2003406584040d08036401840703515184100903512251000a451406015203507030f40d0040c9003102c0c1505124680514200040c2c1005240135080140d00070302200043ea1517100d626 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 750477212 1250 750475962 750475967
    0x3071d0910170307110103151703071505130201080a061a0705070807120f02060909042102030c06130201210603030305070c020619022d0601171005070e150307 70
    0x2c81d102c901e03403060080c000000c016a06503078000c2d42c00e01c0c00003103100e000c101d4407045608030b50280c1e40e40005552481c140711000700042c118540104004041000d41080351411100704944c92074480c801c00b14100b00645c13040005540010034020040b506d180c03520f0103400340078115410500c00c0c42c00010710004104042c05200020201980500941480c00401c200c0380c842c1c210000b040e40c40d04907505811540c91000381c581d003c1002c0c10031030107464a4a41800030603c0e80c15100191600c010b00401e10910000c00c44400322072801c042c0019444100f2400340452030010200d041c410003d5050141e620030859240403070400c200041151480e5060280c02c4440c090401c00821820504035000760710307581c040350207000301007101440700380c04820103c0c2032240200c210315800d0010058606071418844c5800e00c80401c0c0c0042d9403550f45c0e1414218a600510507041880d9005101d40c140491002d61019034803e0803130a14445007000c81c40081e0103445c0404624a0011011041c04241135 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 750478462 1250 750477212 750477239
    0xe0c030c0301060503070b03070c060f0f0b0406060c1502040302221401051507050709050c18030c01210605030a0b0a1a03071505090604030f03080c0f03071d0910 71
    0x100c0940c02004400d00340b1012903204c0101c0c1c01036a043c1d240010201d841c407032180d02d1100d48150000000c20001541114800c06868124000200306040a0303214401d490a8800c5201711000354492342c20004c140d42d04c000c440e0402c071090a030820b41c01e010000c0581c6580301540700001c0084501007440580078010000c950b100000e480500650400510464907540f20b40c903520740142401c65203811036441e140d0301d000c046400580b071503801c003010311210504540c040e100c1805803555886007076021a061603656204800f4260008040813071402040c0000800302e54501840c4101027812030f21000802d24000014a0840315000e80c1000c112a490142c440d04480b19240d44000800c95006070010b80d50341c409002e441201d038242650307900924010000c4501d00c281c09800341c1c4d00c5540d2400c045021000d0800305801045002c00044d6050403420304407520b07840039507101c0741140c0354075104440340310403000520700c9905112405c0c14103a490110542c031402900e407162801d40c0c1030590b0015803c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 750479712 1250 750478462 750478483
    0xb04060306090c031e030e060304050c030706080a0621030e030a05070f03021305042a080f010207050609070807091814100c05120103061a09090303070315360e0c03 72
    0x2a00e45c0650000a9019004070040002100c42c40d0700e03600c440c02c10504040f070b0083c0031645440784650000b10280c11501c002c0c0308184610382000004c0d900c40003569481c0d91268160074401c41520a100000d01400141e03040e00405411141c0c00c03601d0b0350700e1510b8a0803603080780d400d1600304102002140b03000c540501b01031190010030701c4142019a105102d40d0b05e6141420303c8040c0710074080040c101c4503000312006061042c06c80304460b89581400b8001d41c80240107032124043e440000d01c481c01d0004030790040300e42c64002000e51a180a21501c000c0c1103008500024002c03145544010401903551f80000c0240f14002e8883e000340b13000f40c0b90456110a4004042c090103000c0041c1a203078185640341140e40000c0045035514054001001014500c11169803161100060204c4040c00002962189005803802c1140305801e0b00e2400101403544100380244510a44440107840400301c80c80c0d0390304003001c200191034049407082003036135844801c00c0e010754410400000c891030100280b41d0031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 750480962 1250 750479712 750479753
    0xc2215060e10031a0d050c0d081201090506060d0e12040603240b0d0f0f0507050417030304020904060c0320090324040b1506030703061706190b04060306090c03 70
    0x5802100c42000304c00500d01d030ba00e600c80c04a060140342880303401d200302c06031860010030124844aa030b02d02096039402001c0003910f001c0c0c9030000401e20450500c81c07030303001c0c04009000070b041c4100d252001002c1e00f10300107840924016508019001031060340540094003c07610007091104510b40c07000d040c205140340c10011303840902020000000c01500301c94510243c40c20100741030f220341011001a001c224104c40b400c1e4a007600308100e150f8014050000d5483c60940c2c03c00c18901c082c02c050342c1c1c0c0001d46010358032090400c08a40090000d07800041c90012604010840d030740c0b80d03035000b2440d440e4140072038020840080d000e1840d02e8244a800f411305140220f0541d2600118002001c0321070041c8010018000314000c5070a981c0c0c4050301381c1c0906002001155681303419070000f409070a0a105014005007841c81460400b20b003c205180b04040200001c035800c002602808040c1090901150300550b032001d01002041c01c134050004824081c44030042c0162451038038400070b40005440414 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 750482212 1250 750480962 750480971
    0xe060301051f05040b0102070b070b061305040314070f050d0206270a1101170108030406030c08150f0f1203030906100e0615390c2215060e1003 63
    0x8800110b0b25120003522000d490000700036803480010f03803074903030281c0220100300408100d6000b000480b0540605c80c9005039802e1214440980e01c80d41a04c41c00e483c000d0106d400304032140c2420300c10078003508102e0300400c14040c2c500026101c2c1d5080c40035444c101401038214904000c000744411100c10200866103001040c03074041814810744070788201d50001c1c1005044460012580e1180080b038403400c031101030003d02943d60b0800c40e03942e43e00500ca50b0000c20304086191240724042d0300c400d031140103c0d00320b490040d000d1008004480c02c00004403940044031010302a4a07481c1c40a481c0d501645180007903959040c841640740c0b1b030110047c0316010300c0c10300540600c6000e00740900175410010a8556508030040042c070481c541c0505145820344c9002140054054510062543c2c40ea102244a0310030080b0b44446151721040c0d200c0100760400700080c2819900d0502485800c446941c440001450040c41654030009642070b9000c18000346000c2c84241140c500314981e426821001d040412 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 750483462 1250 750482212 750482251
    0x1020a080417011514010f0801180507140d150803090114090d020d03030b011d18060f0d1b0509100b220f1e0e010302061c060e06030105 60
    0x40040c410740c09100c0e02c05401424040c8950400d410010321207240031108019603440300410000e02003d11082c1e0300084204004030640f07800b40001c68165000991640c0382c13502c110b14010082c042c0a80b09030104218400644484610f41003d0f140f00402c44d0000320310086900390244642c42e06412035440ca8104224001040c3c1e0010a40c2c40c1040d0603050702c40c0c86450b94000110300c020400002307501712179002c02c44020150301da03000390480e04d07090f00d5221035811a44941102050102119900700d00c0c562030311a100621690034680c8040028210400e00c0c40c460041100c1c0a0310740d50448452a048000500c4c0207061510304008e42401d427501e03500f52a10400403d072500c5140300b00c24140c2c6002036604240c50403001180400c803e05845490000c0d60f80e428840020f400d44102c103103240e00c4c400001c01e040301c882000c100316091020b1415269085d9001c0144a900a014030980ba04002072000e00d000b8107405030343c0081c0f04103011014140390a00500d1700b5203400401f802800382840e400030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 750484712 1250 750483462 750483473
    0xd09110402040e0f1506070305070308150102031b010b0406080303041202010b030d2616031802030304031707050f010b1c0b041b0915090605060a09030807080f03040506040c0501020a 80
    0x81d0300010b08040004c882e240c0035004010203141681c900d8008500150190600da0000020322515109660b6820540d03035401d04917040f45084c0f5100d50058008102541d100682c00351502101e1401c04000143c040700d01c0001011a8595440001a6040441044144000016040078850b9940000d010201510300066141d48003241c01c0028030008091071410803070401c8010040060f500030160086c10031404800d000010407841400080c180355420080c0740e0000b02403600141d016008500707240c11651031115001691120200d00300052107100c0204104006541c50312100400000c0d441c00c01c041407040261681207115003151000d01e90500040c400a2000d5116400861010f40f24880001c07906800240b0384c0440c3c5140e00703100c3c070805602001300d0464105e407040a800c206196803030062104078001d01c14480042a16a0010008141d034500200411441990424907000315050b850368940c00036a0b00b138845600050401042003251507e5002030002400200003101c11a07444 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 750485962 1250 750484712 750484739
    0x5241503040605040f0f0606030b09030c070b0c12070309050915030c0103090212160e01120827040905060601080903191116060c05070603020a0c020f0d0204020d0911040204 76
    0x601090751207000800384840c140b008440e40c0e40c81b00081004400a00b003410180440e4041510010400c0020441c4020004125000540303180d000e440c00c03514000b40e000450300070381c4407004203002d40c0708014032083c0e485009103450352103034079000c034140e003442d0500075a068000d001d450300c6884600300f040c00c0d0342c000a418000c1c0900346400b040c008a00e1001c41c1482028840f80c1c5920700c581045110962695000b503c184c40072106505035586c0c2c3c030b12514101c140c10400203016100200030446002420781259140b050840070981d40d128102004601111071a10090f01c1c960800c8043c0f003899a4040003090f00203041a004600b00034125001090f418106005082404a07808260302c1a010a0200e40c0b506c0d08400072120204e81e8403240502211070759801102d19004544001c5042c6003c1c4c42600d111207150350318801071074102d50a1100d0b05071101c41d00381d030119001400c580140d030307036000401071800100c0380400d0040a91034034012110800c5000d5204500601042c000e1007100c084 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 750487212 1250 750485962 750485971
    0xf04150302060a1d300a0206130305060c03040309030b040f020d030e03010b0f031c14070c0321080601080711010e03044e060c170703091101080c09030105241503 71
    0xd0640d6501c5c3d440d0305003464042864802508131307030082462080e80614100c164100c0303000382c003a0745541d40c1d0400b030101544001c580c0200450381040d000d02c0410460750109074001d114249406000070981c001660018030b500040b00059880395900c642c5041c203000da03200c000360079150740c4407840124000980740c00140c00e80414115001c016001028411503114080003202c502843c1c0e5480c1a003402d038080404c6010589980d00c0b041a10341082021311184948404540e0b145540d40e02c4120044503d802d002d85140304104801f824003046a90a20403c104400701d680115607907480c140c8501079420520821440c0c460400c803e203a107a04e50701740300e60907985540c40c8420050440400003d69041d10007809000249820316070500310b40c115592104465541c41d90f4016a55030078001c0342900c1d81600004c1400c281d03483c11040b55401505150380201b80544414109503c50002c02c1c01c54004881803a04031180601c04200b41d0340042854100c0042500c460140c2c40801c3c4a409145c40080c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 750488462 1250 750487212 750487279
    0x30f180f130507260103032003030a05130503120411030109080f0304020a0e010b03011e0308071205041502031308010e1f06180e010b01020102090f04150302060a1d 72
    0x30000340118880d401e06009080e0048507100b84030130125040c0030646003400202c011038180420803a03000380b450314054011031000300941ca551f4400b81400040d00c0003038542c2d0086481c50100500103001072000d0612005003070302003c058a0903040c840301d89018480c00303901a0b45040040004581c01800f2201c81c0e80d0015645940c81d2035520104100880a0b40950000705100001083c250000c500030b504075403d150703c000d01820000191000d00b040d0380320007002c2140810007a0f00045610070b42038036240507801c021342800c0d56507081030001c1420300c02c7c417001600009104030814101c0751100c80034105000082064600640400e641e0700b4000791182d0f1440224604a08809116003100e000350030045440d020651003621a10050700c04004850035079400e0140084e120351051003a1100c000d0014842c80410b192041400010000f40d01e50201914203020044096100c1c0030052004032030716543c4162550340c040c0349680740940503007098030a1040c0d42084044000900c040d0802a0f01300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 750489712 1250 750488462 750488471
    0x12032f0c040c120b130606081618051309080c0106030201080a0b030c090a0e070e0405190209070e060702040c0530180c09100810020906071112030f180f13 68
    0x132000404091180d00600700c5107050003070104c0c15552055406020302c0f2030f1414031585180d46103059907004298640c820030495008020071040c6000d44100559840f60f8000041100c1d071921210301a6100d9000b01c48036030f440b80000c20840d644044aa584007201000c2080034237035580000c1c3c2c807525140c1c2e200e88a103581d9408903129451951000d141000e031301d011202200d80c0c41072100d040c0f11007103400f503c0c00c6c0140d0100c44500d40c0201180803440d64000d0817600d06640311807094951305403044d5201c0e041001408000c0050301e5501c180141c0e040d0fa178031003544500314008080d14825403041d003144501c415615146000a4204030745030807510240c015501c0f0b02e00054014602020003102607801101c1000380b050603034002001e0000e172480318054030742c45d01c280441002079220744100ca5800c141c00300070000c080f400c0b10001010b80c1070001c01c1c1900d40035010908500c0d41c0c001c1d01c0c9446c0c4103180014000301044880d559064080c3d0140c92003220841c2040c00194022210b240340d05426444 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 750490962 1250 750489712 750489731
    0x50c0c09090f01020a0c0c050123031308072d080306040f0207050d0807030e0304080c04020901110718050f040b0f0406181b08070f12032f0c040c12 65
    0x502803280c0404042d0002c5440780c2208170f00918184001509550400b040100460607503c01c011540d05003845d0403242075101d0141d200351603583e000804000100381e4008141e0700180c0c110000344580d44c001d044500c0b640c80c000c00c2c45426001c90480003009070054900d41800034410000362a030050003117034000703800c211404801003c2c0c40750b01070090043c003a0302c4030300100c40c0d0804601e9004501a41e030811550346540d856594901c03c501500380c5503400040e401d0080d240c180c0081c0110441850981d6401044c00c91803031902d13750ba001104844030b80902005a01203e200345540710a50198161080c106911980c010000140114903141c0300700d4005028000d032904401c100b10401a0407620120721420002c900149500c59104241010800017480030400103086081d2a031480c820907402c0e2510500101800305802c0403010b101e03144610210b0b490212140c85144105030b0305241d15034003541c401a09002206941c24859460b0042461181c0c1c0d1142004c01420300708440060078011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 750492212 1250 750490962 750490981
    0x50a030f0e06030405011a01020303061c0c1d041a060127050901060f080f090d0c1127100b09130902030d1707050c0303070806011e050415050c0c09 65
    0xc100700c8250400800003c2c4010400b055001100d0740d15003a0541611220240049869204c2a04d003d64840c81c140d03000e408041540b035403403008510520001003115501d0142c540360540d03a807070b400c0c0388240c51400c00050068900261400c90803d20754120107203030000c0060049022002c558101c1c07412104682c5c506c5000c4d4541d000500001050300f80d440d03070350784401081055100114000150100c01040000300c60180d400e02400030180036058010700d06000302c0748403a010800f071340c15280304400c901d456201c50000384410042603071540d1311b0a107094501055145c014020700b144440030070301000101d1341e060a807482c5107404c561407040f0034803ea040a02400705200065072501441c8241402d4035040507622a5103000c0d5a043c1c40c55a803084402e072450701804580e0082138100f040010300302c0d8400c07440c0c140c0c4140141001110b51032000b1051b00c0040324464002d000c50b1000405100d09210035420800c3d9038143e140051804e1148c031411503e50161152a81c0a000981c0104040a1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 750493462 1250 750492212 750492227
    0x182009010c2414161404030609050604021215072105010e040c05011b03030b0a1518050f0a030215040302092404020721020c0607060225050a030f 64
    0xb50080c4100c2d511640240b00481c031800c54280d0401254600824582c90042c0d40018a1098003003e034400c0320000303110820307104500003034084007032003908201c00710000b902403048102090082d801003103607240600c14403021446203030f8040020342c004a445000703107810b444a958005c90b549805113440c0d107042e408000c41d6a00381c2d0a800c45504180c004123001460f151090310841c090030108400a98610040d51032183c600e500315001c18080c6d5180d00443c7c000d410181e275482300503000a580741d030b59014054100307041481440024010402419243c40c04a401101500c012a40131003800ca02d0000200d039400f09110017400360641003486080c00c880305003600c0003141c0252082c0700c14603002003410311400c24801e0007145109041c0740314240707040610a44081a60241d02c14075814100d1110003240510264043d04600ca4160b065a00d92a200d001c1d0608621890000d03840d100800c20340003810190045080780100c1014400020660010b0b20f0107049415052032084910501ea003240d800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 750494712 1250 750493462 750493487
    0x4062103120c110c06070c09050c0d020403050d030b010201050c12090304080313090c05071a0402030106051504060305060306060a1a1312020414010f05060d020d050a0618200901 78
    0x61820b0707250030001d6004415000b601000364140c8200382c03e901c0070000300d4010500c2c050000f42001c2000d0000307001c56030040e82c1000114420f9130420104914010507079005400803522500000d160040b5182c00d800740d1007070322209000900480c030302941811402d00071101441070070018000810314a540910031540505101c1d801e036503403002c0c1c8041c3d001e030040d0705105980681d0b1030314810450380c502c00c2d0300b41e403207255000c4000e2401d40c400341540007d000700503005036415507890345c0c0021a035035010091071140c50151a8651200d18004000c2d007202c01c000c10b0640203800c01c0c800c00c00c00d0b564881e1403801ba0703001500e18880804120303660705004c0c0122a6107054080840d940840c41000d010800448188200c50910010034201c54860891000380300b80e032060020400e09102d245070480103800c0760320f000000103092040710040c00098a1054858600c850b40d94402404440c600744928201034294a03018040c0c3c081ca03411031204444602104004c400000c40c100d0386070b038402c14108028 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 750495962 1250 750494712 750494747
    0x906010309081b031b010608060c0913140901060605070f08071a07181403150703090c0e010515030403020a02040b0a0306050a05071107050d02040c031e0608010b04062103 75
    0x4003000141644e50340e0344241d00109050050b00031000c9154014015142681c100300d000e01510348400841107415080015031990003142c090321040501d040303203d14800080204010882400c11144090071039500c0c0e041130301040000c0140c4070200b012210f01d1280316601c4000c40d6a941c0d114102600c84041454128000c1ca0b0300c0d40a11000507888040c04407014400c403000541650b0b18070301e252166280000305030701a0801c0103640f4100400c3e4418a42c0901141800b040400c150354600084102c0342e08220f0420640c0740c010321036420a100c50180e0001c0100625245007060346020b0b56402075904024451621b071128030003039031582c00c00c40f4000c40d40080d091001d03090003074041e005820100c803404002881c010046112607800500c1030201d8001801003001e44603d602030201500346c181c468024180c6910403100650420152104441756014002038180e00300302c0f0b41401e55070111102c5105a00b0b001e8140f05105c052900a83d03488ec019858030b070210850302c0d080d0340141407403202c221b4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 750497212 1250 750495962 750495997
    0x219050c090a050609060409030806150d0c02012313060b03030d0e010c0806060f0d050901181a010b0f0307032406030b010e030610060c030e03060a06090b0d02090601030908 76
    0x19141e00315000180684c60490f00b604036175440109000071a034130614041e0018000c00c0100d2158100740603c040c580c0d041c203944524151402c40d5210543e40c3d688005401070f99039850820384220821920a920b40c500950110301c2c0c20401c9401c1600c1101100c050015950b0b001e003000c1541d001c0084590501000c6014071101a0002d600d074020032844810201086803940064054504541128806000104401d0400d09500e210400a000c0200f0240c040e6680384a55498601100c05c1c4000151044000030003030800c0e00c0202c10b071610180c0c8120f42c4504140001c03044815a801661707401b4100b03103000a1481d41204031201c265407401c000005031030300b210000c03800690603048010046001c2e00c4c0c00c00b00f0081002455900c0c001202c48801c1d00d178038080d0600905120301d8507900100c0c040c0c82c02040c00d00f50000001d040840c25030f1110304881e640e08003003092965601610300300c0030045408042d045c0407a004940c00140042000b410140d464104400308006001a80d105014015a80c0c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 750498462 1250 750497212 750497221
    0xe0f0f06130204271805190f080f030108101802010311090a15020706050903030d1d07090f11130506090112020d0b280e10180507090807060219050c09 66
    0x10074041d07141c42501103007459070700c1340045e012400c005856580180145854560000510b080c40030031442121181180300c02c100100c1d861b500500003203c1c180ca1a140e507949400070303c40c03400388000b0384160003d090105802e400c42032018200451a020300700460108400c0d14222020b200f01441e8540c0300c0b0000b01e01007a0240c80710f00462a51007a40c0880f080551aa48240c1d40c81c0280c000107a81640100108210711f02240c001c0d2444040d04000103034204036040007942800c86640003101da66681d0701403400d1503034140c001c2c04c4202c4c002100907842c10302031000580e40b1484501615009240009a4644d075074407a020040001601d11421521502d0381600c06014001c07400c100c900c00c0c8004020f0b034884405015007008074040782d03a04c0040b09464a008090070310f400901c2103014882900000a007201d200402600c0c4441c2460000344e9454158405080150290050b80c02c55006207003d01c9150707000a0107400c2044500344a9001b0384480c5005464201e00c481c590390002584000d00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 750499712 1250 750498462 750498509
    0x20a03020d211802090c12130c080d0203090306071103071112030406110c0604081f180f030f110c0d0c120f0c0506031b030901061703040e0f0f06130204 67
    0x65082c1d071003110480c00320340706d442ca00010350207040091041014000c020501201d07201910061591060781c1c09840540c1d200501810003044284040146e0800a0a840180380911070168000c1d400d0038001d404254100c00c881d0340340102040144040580039103613015030f48244400d00e80948460440395125100c4030020107500000b1031005040c032501d110030744145800c206403801d6455040c02801160741d503100c514145100303081c09a02c02c544d1008002c042c00c0b040d190800500740540c02035124aa4903240c004c0008903240301020401140081112224501150b0f152400300101e03000c10041c6040d0600c6a0800400d0f03001c0046044205d48010400030340c0070203c400640960b0110102a503180c0a000740da100c01c4a602004152580c0480c240c4d00d100c0025580054456000007412500c44a0003602e82e41d41d95107a15950b03001090410a000440f620b85030f1000c842d034109075140c200941402d414400c084d010303074444d03000c00a140d0b650f80780710f6064500405000d1003480e02c018508081c03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 750500962 1250 750499712 750499751
    0x80402030c130e370f0c0b04050f150d2409060602060108030a052517040911130b030408130b130909051018050709020a0e01020a03020d21 61
    0x4140c1c060082c0d2504c40940681802011542c00c0d004003600322046428442541c4241030400031071305900a0200a408505201d02d00006050809201e40d516810041048450000c801070310340b0441e01140c25000060346001a81d40c0c55107a01002718207400394980030503150506075504a0561038601001600e800b031604490f00711440d03502039500c10790300d80721300c81d80301d22a80b005140071501c1001641d9011123004030f00f601000c0c410014080040e90740c5d5a40c0c412050800c620b8034030710300204042c03102c0e102510076107402c2000030780c1036440c0071562401500029640e11404862010110018040c06081c4d400c43c2c07032680c544084402000d446480148260700420459040003000600120321804c540c401e0b0064070360400014403540181d2a5013001074000160f00140c2ca10300c0c1103400000402c208a14000f80007079400158031000b450703a00902d05c60401401e581198440b02da03d20200c0c2d00854401f003203c0d135924116007400d241d0321202c18990388010340d9901c194501800c54400c05c404400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 750502212 1250 750500962 750500981
    0x3020903011e0b03161e0504020a03150b0913090305070210090305190b340201020d1410060c06091a06031005190209040f051810020415080402030c13 66
    0xa04001c82d00e00e1006140e1713103a0003c00c2441c20718150302414001c80340c404a502c501d411980741c0c010803654a510100e8285e0704010345a03c042602c80c6180c81d680c88550000c40042c01c00e08d4491804e0080080c0001c10011203100c00c201d01c181e4915041062510403001ca600345500a0622002d4405800009010305038901c000c3c2d50740d0160b1208000e401100c0b04413185969007010f10382c003982d240d8a4455030092b61041014a000c1c4080945540c81040d612125500d080c0e19000161510b80c0d0062803000c1e03c00146940003a0f11442d41000742054204180009541442c580068a08003e00d498001484050f0020302600084404045480c0c1c0b6809000e120320405e50070b139811b007030408007001d064600c02e50b0030380740d5840c1d1103170303055038418580c0d02a00d01c6100051001c6403000740c00025400f01c0b08281c0d203808088011251307001510000b00141d0402001408046140602c1d140c100c1a10300d144e141e86404001303121000c06c00355a000c0141c1540103800422a8505051004400c03004111118 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 750503462 1250 750502212 750502271
    0xb0d06032915010c02011b06060f0801050a090302120a031103010b0a0f09060206070f022b110c09010302042d020306010e120709110f0307020a0b010e04210302090301 73
    0x50110072a14106502c02406845220740e03900c940e401510032550401070b0003145140007a0301c0000c1810b40c05420002c0c40745d20744044070317581029000383c01d403040149424401410702c43d2280c0003a40c0010015140b03e01400c9003a203442c0340d01800c9001e03245c0600e074241944004070021400c00e0400d0000e1090f6000e90702c030b2000c800c01e0481c00380c5d480c1c0070310b22407640560060800205402e00610220f100c00740c503441030741e001c0e402a0308134a25142c42c10000c40302a0181c40c150720031881e0410041d070340d00d201a40c02026280d034002c000903040c20050000902580c4c1b03418400d010807006201407a0307504640d000310b601540e0300c029a0380003500220785035030016580151011081c24185c40c140b1501c440c1d07602526241e401c0502c51000381135036508a0140303400c200b044410710581c42020b140940304950203007580c1c00490409108403401038009051029108090100041c0318010100a01100c0240e10054442064054000f8002e81188a4055080140041d08920700651445003000d160 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 750504712 1250 750503462 750503543
    0x12090501120902030a060e0f060405010e060c04230103090209040b070801090b011e020c030a0506010305070905010e0615040510120e0a020105180418030f110111040b0d0603 76
    0x268004400d403400540b0180d0150020b0381c1810120300e05130045096130041c0411170788210604d2048525102c0d0844040d650742c0d5441d1741c40000980d00b8404150848046200581403500b020503800f6018403440840e4400d114410340c412942c1d000703410007074500350010080c0403246020b040c426100e410444404000034600703800442c0c144801e12411184c0f01041c0d5648038103940c0020540000c1016441110a42c4104542d401659904001074580148200050301e019451854000c0c6000600d0f000f506405040400510129400e242002d900c003800321031404407044088816115442960009a04030000c403020040301764021141000c8a26200410006401020300340c1e91280c00300c50740240060030401a0180c036244508420010301c60040001800d103c48001090f070540c2d4130801100402c1c40e200068442e560803e003640c160b055203400034040104643e00c010101c2c071560140d40306922010660081c0b40805900c4813010f1940b05207000b000244070703010341e62506d4074800740c8400080320 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 750505962 1250 750504712 750504737
    0x904050601020304080d182c0a0203040b1303032406110309010207272307030b030705040c050c01050c0c0d031401090b0103021204150e0316061812090501 68
    0x300c50444180b1800341a41c00c1400c10101c50f41030780790b1f6010171440503d50000c5984c1203402000c44a1080345429101e004080c01451520490300034102c6804230710600c1004040394a505290350b1100e41005c07002901c011900c2c00707600404120741020207480300802000e541c04000743c2d44405542c03c80e11020030040140c0d151680d030b40300d2040360900582184000b040043d8a0007124040060035407582c072104581100050102c0e10000781c07820002c0100da000003c11040c0300320b150b8020103285000c0c0408260600072070750311011486128000c5d0740d0b40446000c9a84644c060354403066143c0020700c850706200040d500c540e00034455152160184103001c800035402442107454241c95202100f15603840d02c000da50040641010203418582c0070801c4000300303580001c0c940e1142d8890b500c03242c8403205903900c803002ca80022100c035240b0f0303008200b24100316424807140c007080d0340d0114000c182d030030301e52141850f040d09113800104015403180400790300580044441060398400ea0b81c80240881d03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 750507212 1250 750505962 750505967
    0x1003110f0306031e06193b030d0606110c09070e0a032004060b0a02060402040c03180308010806100e0606130e090303070806040203060616030509060705060603010c020109052515050904050601 84
    0x180c00d48030500e903101c021182d403080c101c4285004407002c1c00761050380d40c502003070047c03e046a020000303040c205691000280b0000350020510503000007014001c101c10300c3c240d40401c4d0254000303001042800803d80050030f036951510482e1014503131004a01e171214141440c1c10102c5424220502e10603424681d0100d68428034800340c643c1041e0981c024807090b1901e8081c48010849803611508040d01e070384443c1c40c03418006202a95982c443c0c1c0d47d00410303602d001c00c642e040003400340000c0c0c66408568000c205004030b05524a81101048403015541e48080ca08403400c0012a404420303584c1c24501040089800400510b102d0506600e92404c656030b40b0701004100c3c44115500d590104092195440920704207841c001d01d80c1c82070078070a01c1c01002c00300043c1c05812580040b40c0e158010400c200709424280154140d1007500e00007402041441d5680644502c00c1640441081d640e92488400d0600401d00700d600501d55001c94030b04500c0100c00040c16035001d6400a8051400c00012405c01e52 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 750508462 1250 750507212 750507221
    0x190302120d080412020102070b01061d01110307060e0106051c060b0307030b0a020a02012706060e012115110703020c010c080f16140601051003110f0306031e0619 71
    0x2036240d0360001107689030354400e04611301203408a0115075090150000140c90806060f0180c40780b52540d10b642c0901d44003007907050360307802041410010f540b007181c40900310000c1a41d00581e4001004665420140d80e094014503031940310075448104d20b07500703242036207601c4040c094542c000e100a1244000103800d05581d0202403100034010041000040c8603207650703a0141c5150343d010310000c1410a01c130521100c0d118080003600803228503c14124003040554402c95004160008400e4200e45c500342c6c00d944248150680c00007100f00c1044400108075a90541c58060074186004002d202d10382165861180c101200440c00f500c10580e06030060341c090f43c450344410740c0c4442e4103450a1100458004103410000e00728131807541c60480d0000081e034016407812401c007041e005104d25072400003000030020001313106505241c54007519a107502c48074011198040c0800780080d50700e03141e0001203031401040410183c3c00395100c3c0c43c13000c50700384d0200754180500f0314041c0c6041241807401c0c00e2011103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 750509712 1250 750508462 750508483
    0x7090c14092101200406020d140733020909010b03040b0604152d0b2503051b01090506010501140301050f120f010e1209030607031a19030212 62
    0x40048044051100000e0308141034003030400c000828130182410380d800700022507040da4070001c540410107101c01d95042102024044441c40c00d0b0b1081d01c40000c0740d40080c0320702d90000e8124502c0846208003110f14440c4510045110303941141c040507114080002500040c00b128400d846104c0000b45c00c00805050300d015039040600035000d42c440404020040148804c000c005200782d0743c00003101e1062211a044200106104000c015210980d00540f00715a411000d1007840606c0614070084604203005100d00340300015041003040350030169554001c0750005010704040c0f07074040c1c03581c4074107410000e40a0b01ca0b0003112400d980310703030054441c507480e8a034a492581044c40100441d15004126590700080a41882c83d0040c030642090308100c3c0d086c00610340b0b80e44501c80c03c0c00d1100100451180010620708a9080205001c0040c2d11010040c080d18100f60700c0789501c40101021424102c400c0300300800148028803546a064107041107840141d10644031500030b1160580d0200d049200e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 750510962 1250 750509712 750509719
    0x10b09010501170a1e02030a060510020a06051b03090f07140d1511070c0311010504030c09020a030b040e28020a060f031e05090d09030506220507090c1409 68
    0x107104440f224a0128801040d0344291515030501012031032200071500700740e100003500965030707140c0074217a5400d541065101170700422049038000080c640c0460b0104901c1d500400101e840d03140c0030216151140c40c0d4204202d015000028440c0c000030000d05800550017000c145d884040d0f0b0345603c400e00c444014256038000b4141d00c07a140010780e4609481e00c001001040000d4500c422140c0004103820190044071031044c3e030300e8140280700001002c4c40898400f40380c010301e403070b055554a1240ca4014800c90038440e030042444074805019070004000300300040c01c00c100c0440350907052a6a40001c0d5811060200f40c1050b05d0300c0e0b2940745000451203500a4610300000b0311307000701182e0b07400440c00c2c0501051307560701c1c0206503103400a0340502c142144407400304040c205802424100712091082c5000e00156400420015001081155000b00c040820030b111549811a240454200c400c0003086801200c5001c1074000d0310381e00031040c00d0701c6580c540c102102c52144903d414030946414a50 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 750512212 1250 750510962 750510977
    0x30501060503070f170406050609090f0a0201110a02090a0c030608010515060715050907030c080d08040201140705010501030503030a0e030a0c0816060903080402012606120312010608010305010b09010501 89
    0x41340100401400c400300c41c640019081c03c1c1e0b9141030603050054904480d21a118000e00c055842c003104a41d4102d145003001e844841070703041c44182c0e03d05040c90001e040c0078034082c00c4029108140b11555013640c0241807a901441c2000385040141041180300d0040b0f841d00760080344010703051080301d1240c141581e0006800d00054100030b03403504140d004030f03070b00d0f421204038400342d0950b40540c83c0240450401006000d066141060902400c0d8100c414158010012202030701c3d40556040d03002602822310b40b01c08024041c10b19914030410101810f251700b001e00000030403034000011803007918220007c00c912600c0c0035085070ad82c450100d4880c005405580c8000200d02a10000c0c0800c0311711030b44980b6082032503650042500c0c2c082c482940840d070000c0401c001d41d40c01071645260f00821045814040d01c04a084490601c000381045024044544451022940400803642c8211100803030700f81c50740c0c0d108801003030b582c001d001c11507480d420070107040420704100c4c6903141030f114140c4034002c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 750513462 1250 750512212 750512221
    0x31906091401050613050604060203090406140f0d0303060914150102071a03100f032f0a1a071b080c04020f0414031c020106031a090c0904210c030f030501060503 71
    0x40c25400400d45141003c176610b00c00a45991020f000344000d140a40156071200e02c01003c101c203e4641d5400054022040c81c02030103285d44110314404941d400311038110303143c07120342002c400408080d000610303021b28140d01e40030080e80f4005047c2c800c41543c1800000b10404800484e180c241c24030450b404c40000d41c80f8042000caa50700a541e11580c2c50301e03844065541e82c2000c0740c0040341c9510680d000c0c1c0390224510802d0300c0e080032000e505803e440b065a5203910305e43c041000030702e4900c5441103400c40c000c2032140411052088803002a044504004400384160084190141e2807140324a9032290310005c0c0307058200760003964801d1407640002030030b06103032854094100c0030351050390741e141c0180800170311520080c810080702000c01e03600001e4464114a0901c0341d051034000c01c0514090217070100041c503580060f1656002c001510109410f84903450600380d101c003084110450304000207280c034212540640c5c80000c8a00035656604100200941601161400c4c002c7c440001c00400005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 750514712 1250 750513462 750513469
    0xb0414100f081305060a05190608120f0d02130e07020c0307151b06020c0708071401050702120307031e0e01020d08100b0c0105010f0b0f1c1103190609140105 69
    0x580d4000da00c00d8030020300d80080c0c0c4c2c2c2d02d81881812209840402d40d41c400380808021134000113003414408402c20413045080590310350740c2d01c600d1840880740703101c00030340b000c84409100143d40501000c00c2040d51102c4150a0f80a1314107898020500c24070320007000200c502d4800200c01c1c24041016000d402818204050400c0340101c1e020746500380400000d00301c240000310ba650261b0705010703100c0140ca500c02e105e20788d41071590a42c0112456885010107200c1c0c05000c1400c250700b002d0034285180c2e5a245803001c28503140c400005400103000200c0c1a505040e0040c4c20052540c0e03c0403407042c10891442c03001c0c2c0d484450181d159005a100c40b91649406001d01d2a680e04001d4a01d118400c466955030b02c94815840800151101e0751144010068540b4113086240a08a40c0b40300d04c1c14403c1403000059580201103c00103c242c2d03031b04155038400703000c0d80b100e030b1840c211010aa0784c9142203d10401030340007030702c0040403036031410b40001941d0209108900300350010780481122a440c01041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 750515962 1250 750514712 750514727
    0x20105071427030d02010903020106080c031216020a080105040308010b0f0304030e040f020403030c050706020f3d0c08090610030b0402120703032601050a1214070b0414100f 76
    0x42c01d01002c442201528655030402039142c00030a15400440c41c2d980b2454000d095030804d9002002d25400f640e00c03000c041e0380206680c01d081700c000c0d031582c5c2c4403810b2400310703c0f40b10034140c0080e42040030b041000c01e1003007040d0031051140b07000e80c43d80910360342ea0b5a8009002c1c4504080405901c20501c0481d00191003500607030309580b0010404110b0f1506030181c0c5040ba8000d62088002c070300400c01c1c0d002000000e000d0302e0010101800030741141c80341e468440713481e004c0200c01d15901029190311030140484c0f0f106880c2d01e50044001c400364030801180100003c104c01a008030100318250000768803810001400c620541006104031425072030342c0d8400c03410200c01740080b070b4060004014001002d004000d8000194000c0c0d5a5404c4000f00c00342c0013842005040d488100b0074541c0c0014041615891201c2d4111403519999021011380c03810f004003280c0a00d0f91580e400d0054603070004544004001400549800c211402c071042c40c1c04003040b010b0003c005498021030003a0402004541c020351b00b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 750517212 1250 750515962 750516007
    0xf0b0403030c0b0601090302040609020a020f0c0303090922150f110906070c0806130213022502030a140705010e01020312010512120309010203071d03060130080a0201050714 76
    0x40c004071b09501e0758000b500f039443c81e030003050b2030340da022481490541e81004401607036043c5038003801c046112000825124800c104c0124040c0440b00d0101e03601c9100080c030300441074118103205d0038804052900e10354400c0804050052103050107440030b0b01c1c0c42c05100743c8072120501400185004000401d00c59503412100003500da0200c0c40f0700c0040c2201007407103510f00c1001500c074400c152103124070400c1800485080404600c520510a0110303020000b107026100b0701100741d103104020303800d10019107000100940101004118100b4124498002884c03605803442600d803e86101a500012070303480c045c80c000c80311036015442c0100f00b2414408086d02c0c1c4006c409041e50441042c00044211591050b507052502d41e40c000108a586988102c2c1d40712000c20141e100300c405000500080d41c0d80341e042c01000899201c1c4410001d086816601842009405584124184065040115190300305404180c05542003100003100c0c10711585015003100c0d054403116042c42c009040e580e1841d000c01c007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 750518462 1250 750517212 750517217
    0x705031b03070f180f12030f0c0c0509060f130b010f020d02100f02040308131e0302060a0e1201060605090a090b010c0609020301110313050106050402090117041b0f0f0b0403030c0b0601 81
    0x4008240e01c003030200a200600a80101106c121601d46001010305c070080254000700940342c015500012111072a60040361421904100162180000601d010200508295008568585078400780081d07401c800c150201c240c0324542060760040080c0c0e1a1401c054038540180c000340103410349441154000410700004020050419440e651440b800380c2c014008043d2521305a14108011401184440704282c003105034800c90a00d1540420891302400d0118000d010350680a040c1e41c0e1030303001d0042001c0c1801c1009110a654031540540641d01110a6901402c1e110750301090304100b500400c03000c01810f9480546042840d00e86030700130709241c0f0703003260f05549a0b008c0441c040f0100d4003460048841541c3c040420b0300c2482d00c00c0c03c41313509900441c060b0b80140840d40c5941e0704590b919160200040540b4501d546502d851007030b40d000c0190300d07207640b8070580004c02e80c90090003051094031020020340baa0180c45880f07074180341c004d5210003070001b0341814a520014800e4028260001c1060 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 750519712 1250 750518462 750518507
    0x50a0509060f060f01081509041a060402040e040b060111190209060301020429040e0709080c0405090309040e0321040b180709020f12040312060f0e0105060c0a0b0705031b03070f 78
    0xf40c1c0054980c230800c0d1429203401e4001106d1101000c50810000d41000b000c036801c42ca0186421884074400780300410140081000b2800100242d0184664854100e9a041942c0700440c6d041c1090080018801040c0e020b95000000510141014800c990a542680e00e2042c8580340b05500a50602c00c1907440d229856000d00c00002d200301c40d520b00c20300505180e1200c0d20b46c64107001102d458480c0740d501c1d440c807460520f0180f244c11f21021044034102c000549000c03400d603c14030300c035600d944184402d40c43c480a0031480003000039400c428407400b881c400e4880d0030594032200f50443e01a440d030307a001c100c03076000388404101259180d40180402d518020105041c4403444241404152007100d040c5d001c500204401c010340c220303500c01c601c007030004414010803039420240949649401401654043c0c0e5000625110041d010009070300002d90089811380c4510300a1030042c9241c00c00e0380e82a084020504490035008200c000352032103a48140d0b2412007180c460b2804803054450300f505a1406500c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 750520962 1250 750519712 750519751
    0x1020f0607210c0f05090411030a02030f060607081204021f111c02100f1b18140102060f101707030c080712080904060504050a0509060f060f0108 64
    0x144012445501c040d11460150803100d454400d1000301401218140d51400585507095500a82c036203010410314a04992a40e850034045002488410030300c0345490804410030201882a4000354480d14600200c1d642c103449403402e05c81c035030081901c02043c0c0b101c14001481003040200202d0360250004050213040540d0054580e001d0804002c0b800000d1100c424071100070100b048054417510340500503201100d4040d0000b9251385a5100b00301c800c1d5110202058100540c0e0410040194001c030610060411903030060040d8140040d801c46100303840c02c4c00200c0c54090a4500700503c0184c001e851286d44440c50720110050080c001c81d8400c5100c4030108609140400404800d442100141071481c01d40c00e11102d6203466030b01032140c40c1d03c8510184103150030100300316482036120001540322041c0f03600181c083c000c3e640000303401614203802c02c10809041c2d00030601030b00400064549a80300e851004c6070000301101d9040d001030b074000c2e80c020954403440115a01c0003a40400b009040103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 750522212 1250 750520962 750520993
    0x305090402040305010e010b100c0b04080c070605031509041e0c0312050703081b04060c0614040807060c17010b0a03060e0c040807080a0510020a0509030109051c0309020303030c090102 81
    0x4690004c0d11130369505d030002d08141d2004d01ca0311031104404c0f0780800382000d03032290042c500d0705c2100004000440040214003004a00e0301680c001444000130346806079101e00000302079800494180342040010802120342e03082c0400b83c54002c54100300b00c2c000401c500b02c0d03000d00740545100c0071211441c40241c000046040d030401e03120b00f08243e40d11569194220f08000f0884840038018034090b10b6401e5607902c600001c0740c01c076411240b050400d80342c013264908120004010450707003c1d054600440c200410000040002d10b50241b14020400c800040103408540511046240700140c3c0002c20060100b04211000307171480b40e180749004200540c0742d500c01004040d040c0c803100c02000340401c041c00035000c107202000181070780400802d41d604680e180d03a9074491201c0c0380140c000c0d07400200d00c807032180700300c3c100c2c1c1c0f2a44001e4000e000c001280c0c9481607030742080054100d502807640304085606403080c054a0708127030300280210300b540c07500a000b01e0745911584038035055210b546200c080c0c40710f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 750523462 1250 750522212 750522217
    0x7260702090106050d0b0603011217040e04150c0806091b071509050d0503070215061f020f0111090303040e130f0c15050702060d05090f07030b090118050a08070305090402 75
    0x410f950782c0342e407110303400300f00c17842030310500ca200300d1140c1c0702071005201c4108a0a410b0580c40d4100002072161031a4403040c02c01481581c009026801c1508200f01c14030040b443c1c100d501c0000014108468001c0d52402c40d085c041c2074135820783c000140000710703c0382c45a05246148202010041c680342001541d200078510440c03030802200e4684403102141442414850b1926034401428500e203180f4003100c0c029102c800c00841e803a500200500802e200b0340f40c4140341100e8500138170200410b218600c034065078511241014034140c0d0300f820300803015202880107035010502d0281c000e5040a01f00000001c05400041004201c900400c00c00800b01c4c1c4030700034454405001c1c00d00c80b202c0034103100f030b140c0d4050f207136a1694042c03140c00c00c07855005031200c03000c035181c001c12070100041980380c0003845414542c1da54120606481800303c04014014941000d42c068441d0000070400705194440e40c101966090402420580024081c040486c010790001c0c007190340b00346012860500504001002c0341c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 750524712 1250 750523462 750523469
    0x2a10110f06090d050a0f0315090501061806030e074505060105030c040302300d1805060f03090f1207051504021e0102030904090f0314072607020901 65
    0x103030300c40300034042c01d01001c0c4440c1d007906189203820340c038202082001503c240c02690060007016514030720a1000c1115404034006001a800103100550703543c0c00c000c01c0944c002070410312004141794000b40580c028482ca000056a00000d007012300d203884080030254425100c0c1406503042000e004403084980305c0701003031300498081440074801840000c0c9003101d6004110905010041050211421210042d281125811189001c0c0c544211511040940c8140d00c7e032003148101d150310107070300315010030740980c2a078003680d6081200c010324100e10074a64007481069000141041080d80550312400110b80c03141c012411601402034040760715180240070044842d400c02d011480300204441884141149041d403442e00c038841c10181c00260b101201002c12200580c820007203071850782d000740144c40076000b001b44208010051414203081040900b001180001c0b03d61240d015124903505c15150701903004a000c2c06000750755203005080103c040c22848145c1c0d818444500183d64804802d4040c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 750525962 1250 750524712 750524743
    0x62319060504080706092907050105180c0405010b030a1d030c100507020313060315030b18151e130813050907020d080f060402040f08030c2a1011 64
    0x8071460400c41130f003012010340110040000510781000503010605019a4041034401801d1803040a0360480c080c82c4100c40005040d942007004108a2118009250202c044145c0990302c4000070340041004aa07004d01070340c04118400c0c00410545103140d484030440044031400c50b1552500c4001c41840d54100075a502c07090380c010004034008002c40d0042503003000003400103508240456401e01d6564065000d408201681e035650300e2131750401050800001c40c1c0010380c03041c590030b142207502207065084504500c40c1c0b0a03070490310015101803205a1141081c8411419190300c00244e5104400015061905002200d290f02020640400081c0300026000c0c440408240c80d1500348070391030f40001c3c12003040d500614402c014698000c00440e0b071011600b54003020564580002500900858002060341a803040020480c080000020098608140221048103059481c080650580c49850340b01e0385903403020b0040c860811000301e007401002c034105100241c06106445180003800c15a01c4603 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 750527212 1250 750525962 750525967
    0x3150a03060b1c03051603020705190305070608071b0312020f03102114070306230a05010b0a11280c0902030f0c0c0705040626010623190605 62
    0x401e483c02e0039801e840c882031030414a031268101e8070041d0050103802d00c8100c00340c016190301010580300740030758005040003d000e01d50140782c1c40d01890780980d0500084856204150003c50018000e03080c039132149449540b0310070000d00044003842c03c000307072a00840612590980380854405a030024210031800480c58a8072032410707003e14503841100358011010410a10060b072561086018514a1203030000e103080301c104070601f2810328088282d80042c1c04c0304e1038058500020358512103d155200303070a04221103540c84000c0e05004540d000c0c82414015541044000340450040500302000501c2c3d8080c1c0d4942855124942800704040c0d034414680343d000c00c070074030800c0811049100600040e100c02c5055103054028005110000307000d4065203400071940071154842044100302510000c0c0062040658400d101c95142010348000f6515460380000f0504103101480f50604039848401a50f1900318009000000804076a20f080d421405000c074440c2d500031803c0300c00d40100082d0340d9155 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 750528462 1250 750527212 750527231
    0x40306020c061b0306010c0524040b0f011214030918090f0f060f10150509041b080c0d06030c03110f01020d090e180d09140f011403150a0306 62
    0x141000c000504820700c5881c40403c65501802c52800e90368000003c0c02c1100340d0390350742d0030510b1030403401c500300c025030030414840e95040c050844101c5008a119880540035070700d514000e92032101090245104200000442c078011661080f04062a440d03418240c92501c3c1010f00403450518014041d14400342c1010244980f17503c00300043c111042801d00075002da003074081030054031041d0103040c007200040701e1001f00b601c4038100194030004040c04140340d070580b50242e40280450704083c1d0524807540c9001805000c50021034010659015560340e0f10010343d440c4e41c0c08681c5a084510085803071079491802100140401030701001460180061640320101001000700202c0f000403c00e045400441c9030082880d0061402019a454601c2544a1f03666240409e030441d04500114000c500c10603580804054100131003605132405510a510200e40038001d02844281034003003140003651170101903400c49154000346800c41c94522003101e6147c241b10004100540750780003070342d0840d070350301e0001c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 750529712 1250 750528462 750528487
    0x3090303090f03020a05040209040204051905031902180703020d0c03022203150e3903030c120c0a3306050d020103050603070f0803090a080c0f12100204030602 70
    0xb404240c00070b90b0141d0465000c94004607042c454907020b5a0046501100d03a513854043c2c402510000e480004c4403a00380b40200c1d004256442014020301600003c40010080c1080c3c007880580c0140020010002c21461040c961200a0801e0105079003071100b492036091030f00428800e0502980c000d80c4440c1c0c61400040c1550140340b110454022006040000400d031519800381303c800d944002807032105514216081071031031801c0c0080c440301d01c010601c5007044024007034408030b02302c00d8440011800a09142c0c1d00e03c59816602c48652100c603020306000c078910300130460450f0710b0054610542e040da07203d0440364074892895501d04400d12035800001041000d00000c0d8034400414807104d490315010407100ea80d1791f0300c0a030415856000188040d1000c10100b03004008290788201215641c5101940729001001c607030703205820395080054400b00005884544da000184800f80852917071007004420b42c00d280e20541c10303004451191203005228809000110300032400580e0b144002c0c18003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 750530962 1250 750529712 750529727
    0xc06060506091005030c210a0b01020c1c05151015030c0507020d14060f0a0e030711280807050a1d15030109021e0418031e050d050403090303 62
    0xc0c0194814030481d855070342d610070f0440c0105014104550b5a071100d003070780b40700c5100c0c0f40901c0e00f0401640c0002004072105000680c4110000041001a0f440c88030049885a10343c3c0380c500c1d400454114814610580250300588680c420021a10715401084010740d01c1c06040f50220302075403544004114400351100c0c149007a40c454039040120030007800000e4610b014052029024800113000d110411241c1482d24605d05414011903400d850118441f080756041125049030075420f2800c0c0e00c0b083c000c00410380740c210398042c02c1e2044003070b5800e0511000c40c15403001400c1440b5040e841d00104400b91881201810a080142029a040c582403041404031503120350000c428054038080c40840c1c0d44a20b42e007011060070040f000200c0c820001e07004d4800d843c03010394084095101c14040c10050100840310301d00a840501041c0ca0b00901b20b90315031040c0b2030103400300b00d0003101203090002c1c031842c0400d51400da061480c2043d0905140000b2188111000c0380410b0824506000341500180b0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 750532212 1250 750530962 750530969
    0x21010f0b0d03050304080d020444030306040e0a0206040609080625080a020d0606031e0905120901170103050c15031504200a081b03010501050f0304060603120c0606 72
    0x90790800186265001051440002d001a2200401040a200c5035401c0e8044034003c4c9440f41c3c0d014980510040240b00a01341000c008042e80741e81c2d000e0340d04046a4007200300003104040059401d66581200303000c068420410700c2e104a004441043c00140d541e00043d0020b0f215a540302d882040c14180c44600c1d04401500c2d100c10095059031000e01c1c0c0c1c02180500c41c400200340381c40a00c41e120000d809020303010303040e00c43c0d101c0703803d04c100428041d6040e0300440090744409000200101c00d40404801c50780c0300440501640c00c100c080400665000b0001c000700001854881c85503c02c1403909580c0c0c01e020380040714180c1210034a44c04034074150070203000048180f0545d51450820403181402c024400c14080d005035165451152540b610306440c26003540c990b8001c41e0b46861050004201500c00c4922802c0d122511542c0d089412420082d170b816108182c4681d41340202006850140750401002100d609440b028080f0004800048004042441f904d44910300d5540f4600101038482581 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 750533462 1250 750532212 750532219
    0x1902060114090a0b0f031b15090d031d031b090601111902040e0111030405190206120a150e060a091a01052a031c050411040b21010f0b 59
    0x280758007000d548a800c07058025191071030014400000c070001c0750021101000c410b525000d030900b410704010340c0b0344521300100da088070713441d00e102c0d030040c20a05039000380c0282d1038000c0c0c908444000024007a4240ca495820003401000010118200181c5003001d00b891509004086a0f0466420705001c040300c1c1c5c103c5000d007460221040410790b01552601001c900c2d41c00011030036604415912030303901014007015404000c0c49009420084207a06a0080c1c8084a15100d0b40000040107003003c4000c0c050560300904003032604490b814007400d40030700070381311411142d9503d00000858186020bc1c000a052524540c1c415207484401c02641c003603164440305d1400c0c00c100104601e0301c1410038090300a01d00742003003130b103510548420622128020b01001402010f103007030384d941024000007421000000340c444691002020351300b2820396a00f40ca0040218007075011182c4180b600303400410f40600050b10503030060408118010002d110300c60b8543c5a41d44d151201d52030306041d80a041e00001341035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 750534712 1250 750533462 750533489
    0x150a02010c140918070c021809120415030b1c050a2102070312050c0d050c0709060e04060b03100c09090b01020613111801030302030c1005160c021519020601 69
    0x90f03020840c0c22005901102e64000040c0000e142076024545c190705541d0043d000c04092002c00499401040d4190b848404501c212140c01c5101c1c25040200d805441e8a1400015409007490003035018140404a0b070b07503c02903003040c005202c0401001454034901074070041c07120302e00c142041400b036800c0c8001300791a003500120f8480c0d0340c5d0700010f0304d904990744808580030300d03115004129428010780e0307000059400f4907014816860340c00006401c4004070442a41d480503a01d968031421140c3c6072249403511507400700000c020074040d90210300864070180036101c818a60400c80710484900e4122940480c10100081c002c030704141c414000800c0d002e00080c042420051441e00340d03461803c600402e4496000d10b04002c1e40c4520b90008104001c007603d0582650712480d019480e50010313400c120080c07103464002d021921060296a00440c0344100c803003102d000e50f800841e9402e960101c142c0e0040035520b00c4406812090004224058424034181c40d03010034050f00070706015040e806040e004a00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 750535962 1250 750534712 750534727
    0x90108150f0607060b041d0c0a15120f0e0d021009030203030c07060e07121a0712021b03031501110a030503061309060e061b070b15150a02010c14 64
    0x46019405481d001198201c0d150001490518094004604020342007803c04e0701e031070104030b4600188446c4102100903210000a8007090042185c078920901c1d250901b4004400c2c00303907005044403134103e8000e00001c2081c000c0c07192500b00b691009883c4400340d900401d801c41c50b265052080188010700c5100c1407201608545009680e40030181006284100c005008400c1200941c04040880d10344402d071103241d95500765204001c010144280e401000a14a060841482c0d0701014031520807a180c000451006040d400e00035001b0f0303100b965288407446d2100264010410103036200703003c0c0352569504001d26200060040818072000b003600c1d4407000a440000740c00c00192903001c40180d400d202a83c10300c10101001d040c2d00000036086c240750151006004030089003c62060101402d5506040502d8409030014450507201034001219103011406c29402d012404140040062038101100c0405804084d00d50220b0100c40240c0c1d0f50301c81c0c3e0114189c020308d030400c039801241c1c00c4034100100f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 750537212 1250 750535962 750535969
    0x60603182d06010b120705070f0b0a05150a06050f090a0b0a110d0c0201180e07031d07080a080c0c030708100f0506010f03050603010f09051509030c0316050705100509010815 76
    0x501600017080081074400941d003903128138203855465400440e480210030080c2480070040350150703402d0003510304240c009a11650005582d1030317190b20203081144114a8a041113801c0d4200940d18003154078200b12600e41071f55000c201c50090562846c05964a0405203005050b9444440011b00c60b1341142406119041c0c1080e1841141a028207016a4100404407090f010008580010039448a440300340300c102541940314101d098442c003e4901001c4a48162a03030701c900d1031040c40daa9031310040c0000b00003a25407004c3c203c055103003000c5821600e1060300180c14000d1070f4004000d550f108020b400412200340c00343c4da4150011b40d00800c01341c1000c0c00000c0000100001c0c0d03a06041d152404107440d601d095001900348064140100480380c10b5103041c81c0c0700d40941000c1c010b1071540d440440d0340c01380d0100c00ca504c0809200c00540c60f00303510266042800750105001d41c1c0e81c0c020243d00080c191580d5030a0b11002407140d039405c0d9203c1e040030014150003405404c0030003e04440240a541e40c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 750538462 1250 750537212 750537217
    0xc040c0f020a0807150501060f0e0415120f1718011b0305030907230a15050717040503030a0503040b09070620010e030703080105030706050f03060603182d06010b 71
    0x180c0010003d50f440c8280e04144080348640d00640840514040000034195480201041c500707006584600c495040c1400b0402500c560014903002d20116080401c1855601c480400919203c0e102c2d0381c11152041e01c5801121310051601c0c0c0078810009401800d240b16254041c0c0169000d080074030b4000542e140d071500c40342c04980001e0a00000002045d44c1620410005001f020308105500317141c0d40001c0e003d107043c0075103030078680104241040841c1fa40c240813032000c64082960b072094241945502c07030420700c26000c2420804404108004500d644050004250000c42c5032105540c81c185460040800c1030f00a02d507030a9030304541418090941d21a0014805000c51502103582e000005c60041c014442c80b1000320851000160740020103820400c1d46040b03590880070785e400b82d581c2d10019141c0d44648411040101c8003000040c901d454030700040e40e000351000c02a14200c5107410000e52a00700c0240c20f50904030205003034009440b85680380740036003110141c042d104951410b00c2250160 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 750539568 1106 750538462 750538483
    0x5120c040614030c0f07080f03010603140c1801122403120903050a0201030c0c060905010f060b09030304120201020309090f0603010609060b0901080403090801020a020c040c0f02 78
    0x321441000d0303d00c0741c41346001c0c0603c0e25a00c2c9081c540d090740000d40490741c0301c200380003681291031541c0c043d60180607552000a0311440da403000001c0c41c407000b071425580440402c545403403032015100d0403810301f4080c2040100650f444e07084d01c0107400500c0041c051032401011156500d82a8410320013101d0140b20380b03140351240a44d0440302c0007081c0c0009012607101550340e20040d44203500084802000b403410320b141150507521001510002c2c582520503039110440f40e2210340c118440d04005000700710240d4602040711004c240c803801903118071952518107100300419640203108560403e00010700200d20b0746071200400880300001c2e03d519000351301c4c24001150740541071040c0360940b4071141180341040d044400440d402d510041080b402c12005403400100d90b00709001501902840360080c3c5075801d4164188001c50b0042001e800400c000d51034034078245500401c400e03007003 = true := by decide +kernel

theorem cover : BRFrame.Cov 750359712 750539568 := by
  have h0 := BRFrame.cov_init 750359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 750359712 ≤ n) (h2 : n < 750539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
