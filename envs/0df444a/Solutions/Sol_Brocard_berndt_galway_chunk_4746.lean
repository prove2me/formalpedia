-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4746
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:36:02.155865+00:00
-- url     : https://prove2.me/submissions/bdaf183a-9bdd-4972-be10-23ce8e0ca16e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 853417266 ≤ n < 853597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 853418516 1250 853417266 853417273
    0x4020f16141c08070c120e1212030601050706110301030b0412020105100512010609050106091509050105030a0f0212070e0103061a070b06060d060f0e18150601050c03031311060705 79
    0xd042c008440c40e500080411060201c0c00384800d01282000103a20f06283c800d0f1116030200e08424204a82c44a14149108103a44440e0390740c52142645010b0701e400c6842824107e0310307038495241a030084c2012504411820030080000000d01403000b0300103009900441c09401c6052011104a0a0780c908441010165482c44010440750074200c03004143d80d00303020000900b0a0311058202e090b80c070207901c00c40c009000004140680e010340305040d01442c0381e90425103812807401c0c5c0081c007140002001d040029070b54400d0108040440d80441d0a280040c8140c0791061915103400ba200b4941814140d00184c40e04402180300b040340a4440210b4403e20381c502d041ca4080c0e5030300c0a000301c0050045030440400c1c0b05800146681e030042e44050100840c0c04503400d41407160b00b00c4000001029481d05503200480c5901c03c000c00316082c1c50031031011403201084d59500b8010399042c800c000310811717a40300000804c403450400711a03d85a00b4840c4144883c4800711000304005c0d40960100a0082e81 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 853419766 1250 853418516 853418563
    0x90e0309150c15040b0612150c0d020412060e0d091202100201090503030108150a0614090405010b130e060a110301060806010e0a030b1009060803040504090204020f1614 74
    0x580101520030034444004443c040d004007440c80494010903107044815086060901c506490076182016491038480c008069603406000540c035900030142041c104c448000443c0c84483c406070301210040e2032088034101c14400e0519200b0010006104c2020030342c0207400c0c413010494403a0740da410458042d40020300314103059400300900b0440200c1c2c12025990b031001c46800181c02400614004c0c0750f40d00252207099206030001d030020000405044030a803070300d00144081503031100380101c002c00c2511600b40307595541c03416500504113402c06c4d82c2c1c0300b8007c0615055158190300129214229481929045c1e200c44142d18162010300300f525281842c140018000d440c0700f004c115074424814588045107001c1c1002056078801580c20030b4912a600000304210240d40350461001042a032408012041c0f5151041d40c89004502419102d17940ba0b281060a6544540507142c16a00041d44d20340e88a02e0001c500c0e0355882d11100032145d5800c50300c0b085180000100c0e40b4202c04000f6041d400054 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 853421016 1250 853419766 853419799
    0x201150803041703130e070e0f01081f0503010f06030302070f060917010f050c0403110d05060a0b0d080406080702120301031a0402062205030c0a0308040b09030a05060a06090e0309 79
    0x4042d0001c22144520007400b0402e91500c1c0c004201c00101220700c448085400c02600041048c110003020720300681000034a20f4540c0d03400300070b496006007055013100f4034021186007000300e04481d500c13442d45982400505036564106602100031a48a5003c1300d01d00341e6900301d00e551544007889200040b45280a0811940c0302c009100614500b01c0000040c1c51803040c270007403003110300588160104a4000c903080c005c0000001c00008044401c6a90784c44604081c1d8840d0f07500c3c480144600f01c02074417550445280c0c0c0765096801c0d64140d01000c001d440c0c9031a0880200a0b0404551580c014840c044d00620b610801c842228141c03a0010b10402c218462070507610400d0f04003420490308804100404245003040e0303001c10121108403890104c080c6e1500d0201403600c050005240d200b5065072604000003600e140480d400c90310801c03c2aa202e094520000b410562070762005086809400d0402402100580c04007055a003540810406400000002c0e0364034010a010113801098141428001c07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 853422266 1250 853421016 853421039
    0x30203090a0f0f031e0f060203060f061912060b2118030a140405060d0c0e04110712170c03160e18220b040203010506040e1e0a0b07050a020115080304 66
    0x1ca0322091170340c4504a202d1b98428140103a240025505680e021080c4000c03442c10111038400d01d01c044a00c18104000c500d5a403000c00180006c400c00e1103001456035800c0855a000300c401001c403e518292510016801d0407407500aa00119400390020303400030340425038084140880d00c0300c0c04002c5040410011054803041050300d9840f05500303003030100045551301e030707402004211000c0d40003154640b65004003808242596000b10f224030309107048c126201e0f64200958546da0340041e00440302c3d480301d0105640d41003641011501013080c4004220408171948010341c000d6032043d0110740907800000c0c1c11203032202154425544048850b00345042c044140c00c4041d00300305581200400701000840300d608500300c0c00400c4414403030403001c01c019807800788038040d40100e05540500950080030b5159866248240f4219528400074020b02c1240700100f19808649501014010507410030950140964100c0b00103c40150300707202500400e111070a5141c01102c41c1b110065003040e080c81400306d01c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 853423516 1250 853422266 853422293
    0x9050709090903091a070209090303011a09130908040e130305040e07031e0b0a0f12020d050a1a0115030905070501050c120d021b0601320d030203090a0f0f03 69
    0x402c003121307501040d421840416183c40c2c0342600ca02c0c0b59100203600c103200c21074800800d000d841d9041407004008000350341c0402c00c10308200480080d90382d0b01d0703140007800d0b01c040407844404113468400c11004020621000700280d5881500c0380c2c2d190f58400c1d1034407900340b050a000a0000c5c506001c2084003088044000350007800504010410940c2c26250003840006c080400391a40d45400f42c8840d0790802c5410500585440c502510241d0b0030700c1c0c0d0710010040c2c41100280100660f02c401c509000003072240352150f0781d10010030920320b40202032042c8061428042c03400c0d01514066000c07203c1d40288500b542159014004d00b46d2907140c50015030f25a04006010001c600416404c2141c02d1880c0c0d000b0036141c00802001a11556140b1125811440c1110b03c815541d1100300140f020b50040b010780c66007640312280c24200c00c0c451841d0307002d20303218021a450708295505240c004140d004805400c03000e009468140909554416205151980f403040e0545101d0080e42030010580c0f891340b648 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 853424766 1250 853423516 853423523
    0x2010e0103090f151a031507021e060f0108030304050715090b0403140f0a0f0b061f080105010806010c1a04020303190504030510090201200c0d03020a0606090507090909 74
    0x603400e4141e180c581030000c400030111810300d1800c0c007a0040e00500d05c1742e00b4160026400d03009100c060a004030f40d4070035002d020000c07000034940005101c98420464810784440b0760004425601c60328280343e999040590b00043d41c81c19040011a450100205603803050750400000d29410b0319080c2c01c40c0c200f403044001c038010040324500225034100c402005000440c072407081c015820361034511507810124a105441c01542250b103101d00403680d01000804103507003100e0301d006280c0340c1b0317400180341d07046480b1008400c81d85ca80300000200c3e003102c0d0007812603900b80c941c4906a039851f00116000c01000d071006041c03000d54420500000c80023079019a2141c40602100d26003e140f070310714003004403040941c100240e07000906004000003800b035010041c41442e014002c82e2541d9001821900a2290300c0903800300309611140c41c07040070000c1c1445204081d161001340246030078005d4032a4810441540c10701c0c18400c0009201e09248650341c8204103035030302e00c0b945d6828422000081d250a440a0303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 853426016 1250 853424766 853424771
    0x80304320f0d0201022415010e01080406020306010302040306060810060626040f0203190c0504050114090a0b0402160b0603150c0d06211202070503031606020d090f0c0b1602010e0103 80
    0x31a8580f5484246d003c0515101418940303d10385042c0c0c1d081100010100e860410100055001143e6003011000d90859031050b4007685907641c02c40100e000b4050781e8005454681000c40c005080000400d2405003010122000d1140325164502580c0031103081d9081300c2d032108000c0711b40e10440700c1c081d5a540c00500c50902c0e134100c0c10030380d0006498903e4886030844286824810a810401c4080690000304025103003480550724007241e0309015600c201030a0b0040010310001a11440140e02141404000410454854464848550204141d060304941c600701d14000f00305249000549007042020b2820004a140d0f01ca030200700b807a4110000e1140016210080855011030400140c2d0100050003812860100541899003215455140610a5402c6007000f8019a1804800c4914440c8480c40d84402011700d07107420302c000d1042c43e044045aa240c01d400504101804a00c001118021400e201c5129203824466180b8800d15103c42c0740c1a000c041142e00550160030b00701c00c60b01050600 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 853427266 1250 853426016 853426033
    0x906010b0f0f1b0309012003030109050c0c0f1f09020d02010302130b0c0c011b022107030602040902070317090c150714060f071110020c07080304320f0d020102 70
    0x3d400380040745181c1c4640000c6107031103240d60b205000c11038010520a04003a601c107003002c01e80c0c0f81d10060180d0005a6151380c00114113440070703000c40e60703140030302ca00326a281d0440c0c80446407181e484100284000d064841c04041226240c018541d840c0e4005086021a4120740c0c010340003980841042070000e40c8410001403001a8040a4941c020500c4050a0306442141c0010f04504600e095400d5842d03811880002580f50fa0042580c000c8103526540d00034500240c03802d2804110360310007008240002000700717818016401800d08a0311030744032100d03801003028050b46062070450740141645e005c410704c1d00c124605031030415011489004003030315040b141d03112001c24811601842219611034414004210710042533030354001c0140c680038200c2c212441c8850746400e8480a02c41c626500030400c00e40c000000d1202d04010220b4034101c0f07a0741d0b96140c80c1801001c9188503070118042e0b58800c82d1210f100800c0d50300444100080c80b10204000207010480c21902a0205074110300c03500c1903 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 853428516 1250 853427266 853427287
    0x150c020106080d0908121c0b221401170d14040e0106030b130203070f0309140703150609020301050607020d1406070306091b0212160203060f0a050906010b0f0f 70
    0x4420041c400c240c0d203800c600c034146281c0d60300e050b48003455440700b1340c0c0c07c111882215102417003d403442c140d0007070049602d18941d00040c1008a450145404010070010b8201d00d00300710b45c0c055107904880b560391410980e070355400718a1021515041d1400c40d0402d8a1720b121607485580c8100350801751102d541d04242e144c0100c200001c0098000e4404240d8950788040b2a11340440418141a19504151701c0c519100d00000c00d9819002550028151210582002c0105440d40888040e29440445100780e590341410300370840420b2112044d1468601c1c08501001a802124166a40a410710340350100b26424840102403688040d11300c4001640b40c0c41c8040001c3c810f41c1c0c0240d4050b0740208050707062410301c00c12240d175111910064101c0ea180b100d02c0302e03000320b015000780d4602c0704207540341d1512030222000c43d00b001c44000c3d810301070102004014021680310600851407040704008039602c1000d11540c401c0c00303005c0c40708109000e0091280da20000d100030300c01c0c6486c0c094400d080024101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 853429766 1250 853428516 853428523
    0x1110a120504080f0d0203040b0706090f060915090c0b0f0c01050a23010f0b071505041b060807120f0f06082401060e060904060e070807020c0a03150c02010608 70
    0x1185800200002000c00c44028208040180c1c4042c2d2000307020f9035401d1140195a80c0f0239032040038040c8402248800074803000c1e50000002035044031020004071180d280000042144c45411a42e0102006015901009170300c94903e4043d80010301d1a8154100150031240781c000085a40400c6d60030000035034805028015030380103803000003001c141c56040814139002000401e11000c40340307007510010454854901d500328103c3c1c01c442040d41d507603101c500740805401e140150041c0d6980c28442807004100b9580d800603072440903032031008170b0940c8a6100311041c910580c4c9807030014040700008260001c5940c40001411400140003856961400c40c000a0300c0459211110642110710310314641c010722042c1351019901040c1c00c4c1e55940c180748000c1d02c0300c0c6881192600a03040815100a152215404031000d4800d12008942c00c0c03038034080040250100321030032130042c05001040046030401400440542e03600408021560711158a0400148441400346045640b070300000921208c050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 853431016 1250 853429766 853429793
    0x2150c15270a03110d090e0a060305030703050711040c05090415080a03050702030d09150c020409060f02071103071203110a1406070e03190201030504030e0a080703020a05120c01110a 80
    0x500203000060b00c1c505024056880310a26500c85400140c20701c1c03081940b01c503c803000e41303800e040341c40904d03120501c0c450003e20858000410502c0000f0b01c0100740358101000e81443c80c4078814034001c0104100a02003030b0f0303800616000200ba0103010030304040c90706800030101e80c4e0320400c078103240d955034003a0070307240c45980358007500420710004480303042d41820b000940c0094014281421900e19002e03403090b40e29000d0035130348101301c6040b405004542ea5074002c2640750b50001e400b481030000c2c05031920003e40c4a130500300c0390080d1999411900b8200490341804035611590744500210081d10151180941142600303090300030750004200244420084100c11000304008001c603103410701020303005412258406110364041240004804024032903503030703066070a00c1c0105107030300d03031740b90a039031107502911540d5001711034000c0460303000c1e00002d030b450407640212180c454030359868043c083d050300d00103560a01c90b0058480c20240e1350003804200c446403000d030f04450110507039803284a80000d06 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 853432266 1250 853431016 853431091
    0x90b040603150216061509180309050d030507080a050a020d0306260c0301060b0a0210410411030c0105030c1608041a0a090608060a230a08010902150c15 67
    0x100c0405201c008030500c110f200e0b508508c064101c03541c1050314003418103202485481e1040040c142c8082c100351150302035414030365121400581302c61000790098081d8001c49940070061249030901020345110340180b10886942100a2030402441901910b01c90040b0a41c021141324503031741d14074143c40901c610002019021003858031495000c40080c10155142400180c26040400700c120000c103001580d0120710251040e0304c2001c5008101307d13040c00d00310701c803c4c0300c0312081d00801081c440d08410000703d501003101500c0003078400200540b02e40c001681d841ca03003680d0511460030401d4852a43c498981c1c010040c1e642090b03604c0350251100320401032420b50601300810244200c41d0400310103c003608640c10030a00c54640000412041c0910b446803640e0f042d40110b1071600803e80090b800a4103d014191102843e2500ea12a0280006581c00c0740184c0b0b0b0511184018440030040c0c3d00380c01003000182485003401541a902e4801c0940168000c2e041c3c001505030000501201c080030702e0382c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 853433516 1250 853432266 853432301
    0x140405011a060a021f230117010c020303061c0215070b181015080f010608160b160314070f02091501020a06110408070f090b04060315021606 62
    0x2010455000c010000c29841c0e02414040c044211216008101246444130206101c1c03005010500c034400a04007020880054544c40102403107080ca01d103452505940107025040d01c0e480410901c3c508031081c0b045204c0040c1c01c1800411018504a0702d201d15101446c992010042d90302e80024514191440d10b4500a1b0301c001042c1c4100901d54068650001c4501403801c1c110550344c18064503041100c241155440d41d660109103038540c0e42c1224800b0b031240f00121411001c5c3d8150082c000c100c40e000d080010b200303801c00140c1881d41601100280c41d2941d568a082142c036820320100c1d221038031021003e00c034441300c0c8030b501e0302142c4025224090181201a070010098014400491009070070130400c03016030940813080740d03000500c1901a5910040004600fa040729841c0d68174083c5800044850095007030006004110440c0b41c4142c0d003059600b002641d80300b804200840302c07544801042c40a141c0c00341b00031040c0c10b5000e0032131040c03c19802c0b6000d81c0980d598204840302d0181042d00d060 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 853434766 1250 853433516 853433531
    0x1a13020f09060123401206050a09060204091a040908191101020a170709290417060f0c031006032d020a26041115040e0412030c08060907020114040501 66
    0x40d032100e9005102d66824511182c200684002000c94806c00641903a0715003000c103201e41065400070101d0781d08910115201c42d2100d44000141980c400d06221003040114030b0040c920f0140305001c9004c0c0d0002d00240f505c009451051491607088072884180300d458030b515080c0e51828002020071100503079600003040810310340f282003000d007e001c00c0100310401000f4801c041a0402c241e034519680d0307100da0440c040c0c00c0844e000910942d040240c0c2d880b00c0d0101701c01c000c540098014081c40c01d4500c080540d5481103583d0351300d804200ca01c000d2140b42030a08011070b60003a032000041896402b44200f034a040304000d01e035060300ca000400d8150764005141025181d0042044811010105003080c601944c4004c0b4489000c000d80050700160200e2160422950741c0101030001c03c40500c07040391941e0f580c00004a200f20222400d46a07020004200780282d40319108000104296445803c195241c1405102c004000205158155941c07102a102c107502c40408480c46280b10307600202d00d01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 853436016 1250 853434766 853434847
    0x100609090c090b09030f1509060115080a1a1801030303180510050c070c0906080607030e06070c032714011403131a13020f09060123 58
    0x11554090041540340c0100e111145074000401e600f211100500640ca031900580002d04121007885904807030b00c5510101c19041d01d81001052040c0b803001c00340da803243e07680c146400c07076281d04c2407004000604c190002001980305612180d10301005d102200c81c6562010003042551802c42c41e042800c045000041040542c1030103000c800404000411801d20301c00c1e507030b059a0740d0007050035a0103035885400050380c0a1410042e00c4240f600107030040d48107a81d4111070401000e417070250b4100c1d800f4010000300f415009002e40c40801a40400a02903580e890000312814911310004401700030100c1820000700410030300071180c2001d0000f200035824604900f210f81d03e02c43e141c102e070620a041d2065591403100c803040d640c0c400b4440607400110001403070040c1404600300380040c0448182c000380944821040c001541240c82034403014840c072442800c201104104461060000c0c1c491200480d0284032860082c003884203403025a418038980200d95919410b1001d04020134208004078a03101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 853437266 1250 853436016 853436027
    0x30c240204091b1b0828110601060c02060403060903140c01020c071703030c0307030e0a080a02060f0c0906220311130207110d0312290429181006 64
    0x801c5034608011300b80344d0b2404200351030b000f4505000340c840480440c8900880b00384601c070720524044202002e1300880c001348090200c0d0808a0b100c402407092000104805004100c1c502e000c84d0000d088a042a1561fa512800f514200f10101d0412050030b215040044581003d04041103101d000940c881d00501450b9140c02015400580d64a960350401c00100701c0c003004403a0445070a07081d00b96280d980c101e0540181216440401d000d105240c000c0081c4404007002e00700100241c1e0941e001900c0b01c40391034544a40545400d40c2a000400c056030007440c04100900400007000c0340c4a8a00301001d4517440d07556400d9100381d505503048a0007800c64a004100c5010080406404604213803080e2500542c494141500502450a6030070000c02e16014941c030300340c290745896003800a4455040103038035403c0e0820440510044071800c0b19031900d800e002d8401e901c15602042c1c000b180800042445141c0f044039000d0700448880c0081c40d03158480c06500d4480c12981d540700f4215480c0500c000e00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 853438516 1250 853437266 853437311
    0x1203020c010e1c03050403020f0d12060e0402030c090a1e0501030b090a080306091003050f011a040c051e091002010c14031501080910020d0b0307060309030c24020409 73
    0xc2e94100c03e81103501c01d20412442c9a1601c03451a0001c0c3c81c0d5980d1905038603240444030300c042c5600c5107054070060580d002400c843c880740760010030320000341e4500d042d8070b215000740c50003075064004011500082c1031030554641d2041c80300130003040d80b08240140485155880c204030000c6512500103109002c40701100d2500000c5490003051a05000d46509c0d0090002400e2180310b100780c2c0f00403030400681c40217074001440c0c01000392503500b81a0503030503000346903623075a2859030419035a40640624140c402e030200b1540c1c90f100c0510f0030b440000f05031940c0c00d60044505086c20b05101102840c3c41d82d0480b0000900d1580000400010607140685241024040c1e64545a001c0040041c5041d064483c1034041e0002c0c20905000d4865402d0603040c160032844c1c1c60845031010902641d0100b203500700b880c000005800382c841300b5464100440540d085106d0207030100e4120340c00800080c001102151034041c200030300044070001424108180d0b40261b1011460f00c0c0c41d80110040400c152030a441c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 853439766 1250 853438516 853438541
    0x30f0507080706120c02011112060411030705180d080a02070612050402060703081e28090b061309021f11060118020901050c06010303020d1101110301211203020c01 72
    0x601c940c50800002c021080c1201000500303a05c8a00b0042218000d40080d0f0025100c45040380c0c845080c084113800d4070104a814500c1542041708000b40e1040041c01c41e409000c00c0c1c0d5615181560400400030703c090944140c130f80200d601c0748800e0110380154040c0000703108690140103110328000005141c54010002094000d14000c180b10040e0b45031402c844415a0501340440d80c0c1e40c40c84000010f4800503040321041d50740540401080d0a11802104482c0c0c2c1d00c0e400030500314010f11050002c5608a5800812001c1b0300c50200d000303807802440b8210031004c261004a24441194081a00b43c54900d1040042601d1481814005600800d000851050103001480300f0b40c5400800c0030807690350040708a00603800145038080740d11074012190742400b01000c075407080d690b03898000c0d0359003020441403000941580e00010140410300950b0100e5a080c400d8a0850b4200b11181450709031030102c80c2c0407000080c1300d01c4000b0302084c008865402e8561001030f29514800e06075801c0d0307030f204010740 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 853441016 1250 853439766 853439773
    0x406060e1b04030b0601030f110426030307110f010905010b0f0f0d111c12020105100f05060306041b020c010906020c01080a050c0708220e3d030f050708 67
    0x2203041d070210034242d40c100c81e00300854045548542c1c2c0140c0003041c0716010040b0242c1400d00c85072102c0b421400801c100c0341800303912080d59641d040c0c00750b003501c0150aa90101d030010808582c0041c030420070451042140d9058454101460030528219082d0800480e5141d4407481405441e01d042e285059a80006031130a903688030b02c20f800591121582e071001085c2c81c41061001003076032290048005401c4903403c0440070760340d0604040185000c04001d0000541c00c02c00050480b0107101301a80c00c40e141d17900c03035071889414402000411340000305409c0c3c00039600d28101c17410484e0f00804100c18005c07900034003811031802d0300045c200701c4150171400c10b40d8003510b0704100c6660f00000040d0300582c5180005010b40360813000c0c84c12031041100182c490a40440e083c1640c0c60b4240d00c000745011050070086103139981d00e01c21252540e0864014408090a501c0d142c000c0c940c0000b0b50100380c8801590b02c50500500030400c0c41180c680d001540c1500c0c090316a1020418104201b402500411008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 853442266 1250 853441016 853441051
    0x200a031b08130b0702011b0302090f01260a1509050601080f0106020d050d0f0c0206180723010309050111040e0901022809031a0a0b010e010e0609180406060e 69
    0x1081540c03000164000c0ca4034100f4000a640c96100b0350240303a82c0c01d1440c0f09460540c0300c00400074041d4112500e1355110340b44001310392075a980110500b0b1840100c100c4040c45078064030402c0240c0d40c1004004254042c2c40c2c414900f07141d0070640b10349001d030003000ca000402d401c0000005050b8040140800c1e0460300c01d00050144940000301e0f421581232500d04140da0b0112441104081c06035940101006030600c14400c0c80c0940101c2c0c10341c070ad0715540300b003603510007135502e4600d50740c000350f00c00c0d14444108240d4400c3d140e6032043e01951421018100401c5507010340d5589821660350707240f180c8900d1404102400000e001c0c801060308610740000960420030300c000303800400158070782190175000b82e00c2c03101c0c4c62081c050f4680200840e0030104204001d042070024028151044801d042d11a01e464003108003523004844c0459403642c181e50701240b500411051200c40da022145240d800b10400c1c2030785800d0b0350001e444030f10403403241c9404039040d03213015000703641e012000d0001c040e5410b01541 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 853443516 1250 853442266 853442281
    0xd080307021b010e0d0312050c03010812040e040f0303020c060c040510020c0a0b0705100c0302030a06050303031501110111160317010b090103092a05030705031906200a031b08 77
    0x1d10101a040c22100301782203850314a810340b80038a00a400c0801d080c14001008507559114000d07504942d820400d0350000240030050304e040e07105030f000b01901100e0003808a004580c000030340c00d04d0544242001450414080c0e1480e11f4540111480804030350f0019081c0a181002d01020a42e0b01c100c3c001031001e0f078040070014191003801c3c0540090014003007841d20920204002d4030200390758001d001c10444034481d100030080d52044496070a800d060030000159030400108482c42455010000700201d08074000454000410b1040b18105649982c844482241500001c0c4414014901888044202c615002c0c040a14100c3c85000700c502040040000140340e034210f8203d00b0003440c1c00074100c2c0b440e103018195051013849001c91240700702610100b0346c0000c0854000d9410880899103210341d55420580d0b50258500300d45c900c803940c0c400c800700191107034229540c00c0451071444901d103604107881c90341680000d0743e1000041e442e864070507280300d0100182e0361025114503004180345080302 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 853444766 1250 853443516 853443527
    0x322060f0e2509021e0a0e031c021e010e01060f14040e190503040f03080310090b01020a0305090a0914010f06020304211403210906250e0d080307021b01 67
    0x2c0f0314140160000348900c41c2800700d0b11a1a00800034044007501e8450410300103107520740d0300701400e01900c109146044441840c0f0314126020100d0760041c0303e480c0c6195201501c0500f4103074220003a649801400c0d00c500c8007070040001400c501c2118500341c600e4080320b50030b031150106006004600c0d010b801c016983c0042942004159030a4840041c2e07003003440c1c090f107035218682c0000f1601c840504040304001c00c01000794010048181001c0400d51200d0321401101d00321842c03107015078080404203000031700075000f41200e2400103042c1044d40781ea6449060688004480200d142050003005000c108061100500507118a1004504081c02d1242e4049600c2104461014014000349070030300300150b080704581c69100f11004e40b500c0782440c0120865100c5980040c08a615403200040d5a44400007403903481601074000e20800b080140281c5041221605240380400054007900e82d03480d110303103080201c250b02c211144ca960f4030704003030000c1c1000311214105040400201020416a9020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 853446016 1250 853444766 853444769
    0xa23120a12050c0601091a0301050f1b04091505240412020609130f29060a1b1a0a090b04060f0f1104060e030703080322060f0e25 57
    0x1d80026400c00c6140040c0d0742c03030068501035501845280004555041d8a8104190301c81e890051200c542d030b07001c010503007601c80498680c0c40140940f000240030301140b00e10324130100000b6000c40e190640314000c9400fa54056245000c0401481d50b0030403060828041e04030074040c0e00f4241d843c1e1104511800d08051045200d43c03002003c640e1000740075540c610040390003c140041803000d512518010050203081515020310809103030560465882c408010101088000ba800e600000d01d004002c1000d2904400000401c00ca65100c1e0260101c14000c01d80c950f0318010710310202c007040c42c502c403c000c41d20020980400541000b05e03400c001100c040110340c0083d03000501050024090307255800508240c645c2d41681c03420040c1c0c0d20115003401c0000e00a69400d5510041900070020034141d030384d00d603071200900c9080c0c20000a40724038002000b510310841c904440c1c01c80c03500c4035200e0134256908000e40b2907981d65241c0410200c0d0208000700c80480c0400ac5401019144030f1102c40740b45c1c81a07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 853447266 1250 853446016 853446023
    0xb04020321041203051b100b240f070f080702040f0209061b121602180106080a0b18070f110d0c11061b060403090506030c07061a0a23120a 61
    0x20442c0f15003c0500400c1500c60b9001006803901c000c0c400c2c0700607959100541044101260f2410040041505000481c0002c41581c3c1200b0a4240c4458030f1a4000342d01c940522080c060701840840c0000345250083c8150b02e006d44011030302c54806004100465000b20391404441e441007155484903141e1500b5110000b503080740344586c220041d4081414511403030006011924001041100111490355044150b80282c030707c010340485100c080e8007001020302629010504c244001000000e03540c111443d545806081200414042070007240c0e948000c1e101c0c000030807560b031300c6a00e6060b401500c26210404090052111000480001c0c2031100403410250085545030400482512450112143c2001c0c503d103400507200090645502c480054408400003100c540000459280880540c3d0088841d4000c5900d0f2602503503030500107007803e5896107524180c90302585090380d24026204020f00c0d05000c0080c00500d00c4061410284180010512071540982e80f0700310b61000003002802c6550 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 853448516 1250 853447266 853447289
    0x18030f1c082e030b010b0a120b0306010b070501090206070305190306030b01062a12021c0504091a090901050a180510020c030408010f15061706010806010e0d0b0402032104 75
    0x7085074100070400095040909074004d03000001580c52248002030012400d0303592800f050030a0540c9410546801c0a0346550641c8183d0060081d02c0014004001140c0301e000001440107840c2e02140e19500000c80c29004200d011500c4c0c2c04c0c4038201f2440c1a0340c0c06640c601084110300319902c1207140309041c0911010082c8032104800d1400d00710514964070881c000284020074100d151a14458100c41240030050086030440c01c1c0c41552710300640c0100b0301545410f41004e00f8011031000600b480f0368500005c040c484e800100c591140c000440c001e9008400101e400d10301a490f62080c3c40c0007a04c00c200078080080b100d0040b45010801c03e1030004501d40c056070302c090a81c12540f41d409070750400038055283c8000140c1c8100d1507401404a076003180c0c034030150349546060686581880450040001d1903020010300d842d80b051445c00c3d8491070504103031000c250824040780030810344040c00c03074500082c01c040c0070035440e0802584090f29840b0359581c0030f11041c25021403450041c0c1c03040c02805070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 853449766 1250 853448516 853448581
    0xb0f04090b0a050c07020913030f08010e04031805130605031218040b01020106151d06030601050702040509120c060406060b0310090c020c1002010c090f051518030f1c08 74
    0x40781d080c225800b56030003c001d42c07da42007820081801980103c03048001c54005250040800d025018142c129404040c0c0a202695030f5203080d944070044034812940c40507205004030707942ea580b18050200d1044180005647da0810040c50306d4104555017900312180c0601084452005201070515240c8040d03401081e006050030050340500600d0304918200d40d2000340d10f031260ba0340500f000034082280302c11032202a9641703040c0f20282c40242c40c00380c000b0b03204100c2ca4000d8100350300003980101002d802c4404070803030b13034049a0300768002410b8440d05400c2242488207001450085402600602c10002c5c036600389404491036400f0315100d5a40c100b51609143c0e030540b23000340141040709070041e000d02c0c0c1c1c0e80080c58000303009254000c2c003880820615100464503d031129880b50540d100030700300140c2c842801c00000c503181c100004948084184e4001d140040d00d00b804082000c04003400200800c0070001c0c03418440712009180402005950410000c103640807640da07041c142c0c402c1090b01d0505 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 853451016 1250 853449766 853449781
    0x70204090f03021005130309032004021909091a0d050c060310082e200408010501030b1b040303110c0a0816230f01050c0609010b0f04090b0a05 63
    0x400003004040d0031044140d0444003410740100d854080e0740d6040b242048a69a0b10b258401346901503030000c0c0c000f951000c400d0000420021001c00c0d01114a0410000c98074172070001001e0740c0c00048030680c400345007102449866000040b0f000641040002405401c15000b121140d181c10700120300c0c4100d064a20020a0040c02d0260b02c24010000e02110707a80d161060b541d8008000070711032000144111150790314002500318a400a440c2d80091070024020800c403588080c1030000c01680315044081e4846081440c0a0018030060940f000040707a20740c5113003003038284130750010002900d03100505405400e0400101c21102036940c142007019448a0000780185800e81d4820807a4019914000200302071200007000c2c04c100e80750301c651008075602e074601521800521900c54020400100700b40e02d60703182c02c0c0000543d0100603d0b215041c102a405020324184080c1c032103c14603513455480b6921418202e2503e0300c07400003910706100b51015992802d0b8803a000402070030360305a0f68408217050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 853452266 1250 853451016 853451021
    0x12060b0d110c010f0203010e13031d03160e0103031e0c06020f1c0f050a090503040521030d0e1905031c021306091e1a1c02030c03061221070204 63
    0x40b030a942008100c1d212004001000075403081c002c1c480c0e6216a080000c15401030741400c1c000b841d0b495030355540380364006600441300c0c11105c440240d0502401e1030944200d20120700440c000c00c00c5645c002d00e107514505000d008401490b110500400365118050703801d54004075080140d56000c0340040e5030703004a44031050700b030003240350341041d6211887c2c003004158000d0700500b16000d000e0408000c10344501480b24100c0307410620040054000384020001c620300b09020503c80c1c404410950050f450001c0c8250543d1b03c1045c11302010f907920b03001c2100070b5108103c001801884607124211030081a03d4090762406134072f04804003422180842803030080c498055400c00111a010445c505480d4680900004000c5c0640543c0d13208445006080c1030040c2080c0040700c2504e00f09840590034012030340003903440400034011000080d800a16500d00038401107205200e10501c9a0b01c1c1d003042c2040014a011004031240140d001003019401940203000d001d4011000c103025554601b81d61012401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 853453516 1250 853452266 853452277
    0x60103032c101d0f0d08030606040905040c060f090620071e030b0c0910111c0c050d021c0c031b080a0810060212030403020102130f0612060b0d11 64
    0xc101000d41c0c01c4882464002000800b038291899800e000f81c070400b41070103c4041641c222071351044d07402c07141402044070500250b40264014003107d2030075447e60746060a481055404503511786c0014410003655070f010904444945851405083ca00d1500c50020701c194070307500500d0038000131404000c5d4800800c02010b00101400503940c43d14400000d820a00301d4400d01c8291094070002c0005011a000a02241d808140052241c401c403812020700319500358800303c000c4114071a100c03a03490140b44100ba28010440295150225200a803500604006001100106641c007040340d110603824085442c5905003450b1605010340d5400b400c044400e0381813100f103502c3e001442e10007502808001c00050401e10496120319040c0d841e800e020001c042f025200e15801a0030034018006604100740c000c43d04940a4400035060400a10302098041c402e90311000c103600c81440104581608412140e52503c950b0300704015192400307544411920a124000b41c2c000c0d602e07a1016010303c80c50b0283d46 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 853454766 1250 853453516 853453519
    0x50306040e0708010e1009050d1b0b010803070606050d0201020a26040b0d0c0215010603090c150c02120102090d15060b161a010303021f060b0a170108060103032c 71
    0x3040300c0d58600c4441c0c02000300513800105d90143c000d007020525030350701844c40d1075a44400107044034010220100d9440d0180c41c541c2c10b24009044055001c1039551203624040d2119102039651a410b901d0501d08aa000d80c0c0920301549003540e212001d40c0c1c0120341e42d1140380c1c0140100d0780d48000c410228280307402c00b030068100c3c80000b04001c104580d00342c020713151032030284204107c24540708034181c0e61120624075182a042d403400050100340d00c80d03085035000c1c500c50283c9491030b40e150420440014810344104c00054554083d000a5250416100082d40600002145040e01c0d070404030300c00780001000a0400c852a90404500c00016071044d0300402c4502c0285441d0f50040d0000d00302004421810b0300c6900c44104400790b8a05a01c4a42d0304880d8550002e051301482a024101101c185540c0615800c0d5111400201115180e0040c40880a25605e00b42d403441e080741400e0540c081070f00a08251f600050051000070f801403918204604010400380c011340d0280344120001d42c0b60200203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 853456016 1250 853454766 853454773
    0x40b04061b080a11040b0301060e06040b070302060411190302010e030c09040c080d02060f2404020d0b0103060b04120305030c0c0a12020f0f0d0e040f050c0322030f050306040e 77
    0x7200d24550000d0000d019401d034100a01c042c021107402c420740da008600503145562000c100400c041401110220358a510103040a400c0070b6507641c1c07517403498101e01d1003540960800810841046420141089041d404981004403800085c2560000703501074000281402080d13405e80f6410b03a000c00ca507407451140140244120b260a160002004006114116132449902d1400e040756001141903841408601d95098081c2da400714050b00c08408451000706280c4035200600080e140d03400200b45002c1e00540106900b03401c500010100c0710175500121400d03405200502c54a400f140701d110074250145041da0303ea40b6009030f125030702e200b54210100540304011001003004520044200290095001c2e0307843c02201c41d405548a04d040000c0075210381140404d1910343d0b015070784036400c00030003400000700d2804501c080b4049980940e0940ca20947c04010044000300c200e0207181c5091489180c2500c0c1349195070050040400c043c500c2007413280101c00141d07251241d61100d9811158081103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 853457266 1250 853456016 853456061
    0xd0605130e0f01050402060a0813150515190b07080d0608011a030d08010e090f0f0604050d180e04020402122503061202041508031827040b0406 63
    0x48009240054a1107414003811020128481042c41154030440e005481c0c2407800c000c1c0103007100c11100080c800d90341c0c00480740349100130580840480940c24921400059681010f0a000c07410207018030f43c4a01c6039072024200100000c1900f608411500f40d0244a52525607500e403400c841d008002e0b0031103d0390f00d86a400509984150052100d010364040c1084140350440e0a040d00ca030500007a04000c1140309004022044540e007421398000061425280d0f2440c20480346809c010f0003900244140e0301c040c051105002c07081c450705482c80c0e41414074940b0b0300030304500d8110f42c1d4818071070b241c82c41c2d00040000d0305545a60b01140c0300010381d074081c41194a4100d60b500009844010804403d01280065501c00c60280c811391069589034440002940c1c0c041d42080007420550b8104042071001440000e401101003018004400680f20036180910b0b6001c14050300b4444402c201c1100c200c41c003c00b440020004080941081d01300441409a40d01c6041c80070140c16102d21448141c00c45014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 853458516 1250 853457266 853457299
    0x3130206070312050a02040e042004090c213f0c1109100e040c0302042a08150d060b100521011512060e01030602040306050a0e120d0605 60
    0x1402c00403541d590300c01c2007282c94000c4505d0480c041d90144881c14070030303800400e001c0b807243c9400c0000391010305d0380c618854907a500400d0a03245d810700202e500000d0400c05203c488034000e13194554041c030541b03001d500003164481c0d07224241c2110014550103600b8016200404444200401e140e44820b04003400e002041300061003110181c2c020f0b0380c007c584400c801014580503e106020f5030340c0507013114070f0504001c2141d85001010344112074010510a00000607211401846445001e0360282880c0c0080c51a0a4450880b00210f14082200c2d260400c45001410307001c14540140c15140307800c081c0311500e03140d8000d040350101d242c0c0c0200015050100241d00c00001c10240e03000801e4204424002e50000000000a01404c007020512100d04106148580c0700c121126080310b9001c14429a66071210000543c2a042583c200380c000800740148420b41c02015008100000e04101c00080110344644940c02d030b0100348004000000c0880840300260454409000e005001c8540c80e002e0301c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 853459766 1250 853458516 853458527
    0x405010608010816141302091806120a021008040221160602010603081e1605010b0f0f03060105040f140915130c030602030a0608030d09050c030c15031302060703 71
    0x490b1000ca13229880280c2c110701480301a2000b2181e5003400d2019107481441000881d001210f10751110315401e1020140a40e11664070205600c1900c03254001402d028040c4040385a030414141d40325030001a02c0c80040e00e590102c10541691454a910a502c562000031300342c400386154040514196192020f14031070105030030182510800c0f10346d803030b02d43c2c421041e030995510344005802030724140705207441110340042030910481407a084500e85821211a086441c414000942c0d4980d5542c03440e084900744090301c2c000300b4000700d40400c8109090000a941ea21050068070301868407003a8001140c0801d41101404501c80c600200a0345454410140d50759100f904007002e41e400480071849030310610403480c1300c5582200321403a065085444217000307540080c00d040002c5903200400104090140083c00e4100554407000ca01d0b0941820310130301d0041c2c03c440c0d0510a0700802c45680c820768030310038184030461340045044c1d202d40e24000080c1029104080207500024009021020140c1c001c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 853461016 1250 853459766 853459769
    0x10e0408031909301d060906030703060306060b0c0c0d0c15020c15040e04030516060207140606040507020307061d15010608090606150715020f09040515010c1709040501060801 77
    0x42c4c2082c140080505040308000b00c01ca5101e00030402c3c01c0c24440c50b108a801c0f20602906019160350315050012004c14500d0b88100d80343e000290b55108188108041e60040800411003080c440d401d00d0003d600203900ca003c1210250b1040743c800c1103160800c03031144407440040903660990f91018001d858046c0d00c0d0051399050601c90f61010104a0901000900b520240c404c0100718144a5030b66540540d0264402840800d81510b154140c80000745070b40001d202c1184141d0010980c000c00070a000d103002d00241400f4803c505050420090700c0d4000140e0f0b8170660440b2021811128151082c2d1188210b00c0030184507014249401c149035441c0c1c0403880c121651581d4200e00c942e1283d8016894403010f90b405503015003c0241010300e00502c001505400740950000001e2415003c0244d08076030040040d68094280030511940c3c40c035041c840e040c0d0151501c0e40300504504500002000344144510080c0340d1401401390315114000f0006480c030480018000704180c1d43c41c1c00300600740c40d009 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 853462266 1250 853461016 853461053
    0xb0411040f0302013203070c1707050c121f02070b0702010c120b0d0206030403021515121b270703020720180c130f030201020114010e0408031909 64
    0x1003095108240180e0358810b504085c200200000118a24080c50941e400502200100140c441e0000d02141c00008444e68001400603600d40d04d0802d441c0c41410300384070440081c41000c4e9102c4401c24a40c4c045008a1240100c420720106004000b00c0c1100034012288080e241d000d00c407017044810341d01540700c048141a1919070a0700c07912803100315001d07203441204190b04103038024401c800500b015400b954105100340180c4600f550310207200c0c44120000c446030303850005802c030600c0380750600c030070000d002c00360300000741c00700c85445264030011340340041d01301d401000701c00c0702d582d25005141035043c858042e0764001116400c0411009000e500981e100f030301e4491140d020214031000789034144090040c00741c50f588600400900e61840300030001c102a1001030300300080100014070050b0707d0080d008020032514494190300009086a18940600034010080001409505103102c0c10b2980107510000c0d1554994540d0404110542c0000845140c68201004042000501c01e074001c540c180 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 853463516 1250 853462266 853462277
    0xf05010e0d05150a0227150a090b0717040e01050901141c1b030803040c050102061308070c090e0604201008101a0c1002040b0d0b0411040f030201 64
    0x10042295081070a48010200c0e4441d80c0c01d070704482c00941c102548840008801030404020307131110a80c17240c40c500ca4403400c0c82042c6804080380350400c214031403128003190090424044180c0502002d0f064040d446144402007250740801a0012180085085d03a40b501c0c0c1e11181c0c0c03082c2124140c00e0a0103041d201d0300c0900000311b0750581d5500510714401005003e5900903002d58a11070388800c4201040d10305000007600562030700e2108904400071440b451425075030740f4240c1002544103101d60001c60440d000318044c4010480b04825404c0314503001070140d50780f50b01e28980b500940d0b015500c548400f9060603494a070740f50380410707400c0c81a401424110300300058007207400600f4020440140d8882ca09961082c6814450130829070b0240782c41c280091010b882d01a6212110300c04400e14490050000d01142c9601050080100c00340c204402942414142840b26042c0e0007030b0114500542d0350b590301d003c15030740c654100ea40c068140c41c3c0d84560f2643c9542c60000f031600e1381e0009901154 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 853464766 1250 853463516 853463537
    0x210e100608010c050f1b010203090c040f0605010207050111030c010c050d0f050105060d090c09090b06100206010513020a050904060b2706040b070f0506010602160e040b011406040e010f0501 83
    0x40060240c4043c240107566418a099946004d400c4503803c040361000341d0005a010154440d0b4091006501480311704006041c0000d82d542000281c07442001c18164a03800c0c01020000759800050200035035500342402e8000d50540850a031543c0101c003d207c0c219820200840c88031504080240042008000e060003010311030483e100070b41300c0a1080c2c0390410000c122034414030310154401c491680c4107600003052281e0303d84801054500071030080d03a042d240c400a020580c0307802c0e0b004081c3ca40039400501400d62400300041c040200e44004212041d4000410200030383c4200c088490070f0030001c0080090640710314a481482c3c0269420051403c82c0180217030340c2924a000b0f035064441d000f0b002d540340030b090a0b03884c44a500080011078881295050500000f207051218601034a42c5500901d0088402d000d03003114030180b035002d4551000008180400700355800941c605482c1d941490180071203664010641307a1150791f02c1b46542c1c254510000c50640b5140000c40d04482099a9044005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 853466016 1250 853464766 853464779
    0x6091a010e01030b15131806150f080f03090409170c072904050d1b090509100203041208090709060e2703041e1205060714130501210e1006 61
    0x140d411440341ca91064844080003a0818943c019400e00c03451f41e85c1e0b0010f0b04200365035801c1a42c42e00710000300710584201c0107104c0b040440c0410001005400010000d0321045400c45807a407048808050103544c98078840000c1c4541c0f41c0a40c03805003228080315668100c45000c00d178071820301d40210094010448000e803080c03401203054028a294890050345000d01d040108000140e0303212040751520080d81403a20384132403840300c0d007000306110b240100d00c03813428030278290a180565258101485c17042c0140000f0588034840901144c20034107000000307407601c00700f00b454812a98003d42115041800209200802c400c1c5140109206191200880c8103500020b0041394140c031008250f40c400c9c4005c100d00c80984070600d02c1c030307192040001026911350403c10035502c075551047e03d00c0d60100741807001580e030018556071840e4820004030304200701e4013100c1452101c54400c20341000710b017102034031034426840101004c00000c220f0812203102c4408200d9126022002121002450b00c40c00140c0c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 853467266 1250 853466016 853466041
    0xb01092705100b1605060c04141e030d050c01060b120415020c03040603020a08060904020609010c0503090613030b01120b0127330305030706091a010e01030b 69
    0x144145003420441010002803900052400038009040001c42e0300e000142c80016000402c07000c100515003502c0701100b41051440c100b0094400f03c4540c504100c200f140c6507101c01c3c241c00c045070854105141010300c100c0500c030841c0954080d0740c10f0103030f4500660303c0c0d074000004015040b0060002d110542c0d075181c0140c01c900508400703003010054900050005881d140e103240714044101c1006041419076103e0328a10707080380c2c0100c6c01003940020035003450340d04600641c0c1d0000003251200d00c02e14090b4082403c1c0e00402e500c0380d040c4120b44042408010040c01a50511311016000343d807a441d8806a440000203144400da1b60114110004200c0e2500c4925246820303400c103095400c00d91070040603500740302c0030008a150804e210103101c841241c0742d000d0074074a00810130175031110207140b0b010304810342c1d03590180c0388180d5240c3c0810000540b01106a900040c0c10107800a5225540d04001c41c06405e40c05030341d05481005000450f16044824007241a28007400c2c10602c10307528201902c60 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 853468516 1250 853467266 853467299
    0x503012606160903080a02212106030c04020d0f06080a0f380718061d0d0807060903140c0c0d0507090213051305060105030708100510030b0109 63
    0x3281e003121000031007000c092000010034540e203260910300e007680d070707110303284a60030003040307840140c00420340914070304900070400c2a0064240441c03440c00011801c10075219a060040400b080310350780c00504182c4c0d0910844902c0783c0c02410555075954034900803401000070f42060100640f4210700818050f0001a071503014992041001c0e03461021901d5003a4020310203c240b02c9e800c5203075685010305a2100c40c035038030048008007428046060980b800351841d86890a582000302e2414000c1007480d510a00107a01e40d80e502c08035903082410b90780401c103040c92814000e068018001020420480c03954007516110303000e0303650a10780b000c0d00f81c495100c2d032003894018034295025103009121031414150300c00341a40320b08129105503980c1c07540b640030303608443d0b031009407000001801c01c95030078881031111004000c01c401300001e1810600191040c003002e8040801c1291076000201c0034040c01d52038030084c0c00024451000801c4000c0001e01810204e542180040d0180000207024914030301d8004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 853469766 1250 853468516 853468589
    0x9170309090901090f0b1510080a06050118032a0b04030c0509010302060f0c0f061513110313030905030109151401060206150112091412030c04030f030c060c050301 72
    0xe0308017915101c0400c800780180c0300d080a52444608511141c1c3c441d0100c0b0525089601c072800c9078540070103d4021911546d1090f81401680011081ca0380040300f06401a66840080740c40ca464840c0455004110365541030000301000207002f140e10002d800162040700d2140030301111140d214814015030304002c1c80000d4008030b0501c40031a040c00e4500241012031001d03030480d0b00030b0422182051800074151500503404007038401158103814945200a42c4029104007488403071107a102a806612000b451410301240036240c0c3ca04261095103040c00130040100203101007101401d005d0a54600c079010002000e1a243c2010854010300300c010307040718250b4004d801039503a0040702c81e90004a0b4104281001038164180300c100c2c2c030500c15044460301582895070100507812032103182103600880c0c8007a8400a108115022a4280171101a40c5d80320b00c0c00c00900045180c141c07020349510000811050a0000e5900c503268040003440c101e0b04402d455a9030811081e100c286c19805508908 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 853471016 1250 853469766 853469783
    0x50a08010e0d14162405070e0d0803010501080403140307080601080601020c0a033f08180a1e150915061404051f09050603011416030c0917030909090109 67
    0x1e2075034050507044c4150440c0904c0d000601c5e40342c800c050706030b44034442e0344c940c92540d07542d01404550750348116a51407207139003a6460440400306840703004c40b41c0014401da80c100696000050201403081c152841c450800064440d22420705030400b60244d842101c0942c005841c3c00c001548561000078559401d0401400800c1c245c1c0c02c5440d40100010708114808451056240d002c40190189880f258403100c4102c180000e001070302c0c0e009010410280104080303850807614a14007060101d0406582036000a241c4807903001031001820760b40403024090807140403034076060300603202e17500304c03080c020311a8214910852880040b0b008031482d0740948050700c80180b0000300c0074105a84015084018032059044031a1160803c1d0142c030f482e0b4000d01011510740081c08400d080c01d010b004c052440d4407526414904c1c0c03681558610044100c03c5104058a40d03412a1b2564040c1544e0000351070b1040c00716a40d10302401501f41d5990000b02003a00404844000990402042c4118490700d58002e099 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 853472266 1250 853471016 853471027
    0x60319030c0303140712110c0a03091d1017010902040c1d120d050c03070b040f03140f07060207020109150906090902030609041b0b0a03060503010e010b100f09050a08010e0d14 77
    0x2840300074500441f4255100703000b000f00481a85080140f107200500c81d9951221840c20260345c100c140d0f850711182d500e440300c3d003820300481822081807841503509813401c1841c6c03201c08460023805014034480180d000b5290240d11b900391540304001070059450b450b2400c40e543c10704070070f0140c49108410020116045444450304052080009100c641c441c002140d050180b5078990312128075003640e048907089000e400ba1010140c00000c400c00d03401c0f40007000b604044007d40510100d07c6102130083c000755001818604680c01101f18202400700740c061a01d00490001d009042c0007100e000e940003154610344000f581c0c01403802181d07c107041c003418011094440f643e03246141500c6010103291815444000b1400c060900d014003440c04490743c0100e500b40c40d2405260850311012060b15480e4100315100001c0d0715400341425441d01c80385010803090b090724804803040d250603000f0b160f100940100000e214501500000103018403142520180a00c00005440d03440b60705000201c514401c0c842c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 853473516 1250 853472266 853472297
    0x20f070804170d0921060c051c0209060909060d0b090607020c0f1806011e0537120b040e0a0203011d070306020a110a030909050c040b0909060319030c03031407 70
    0x60305c0380f40d8801800b4241c0d0103aa03440c030076180c840c03410400040000c0b440080903000d001448a500c0c0842d1411880c051402012503854803410b80010b005032100000f10703246440308032140307440c01e4010060003490b0400305134440e03c0e400f00381d52fa0001442030f42c0294407207107400c402030380700200010600025400c500520b4a0800c00c0100090705000c40f0181401c910f0714145810408410165100c0742d4a0500030211030300c00b5016803e40c92000440c00808689580c18014584000201c1c1094014048144c580c0c401038101070142ca41c11504140c0c0408000d6000942d070b06203941b00700c000f44007220702103040c0b07580c24482c0381d41da031a5a030040c18204082040d5a0090500440b28904010307440d0502080307919004c540401100043c034452002c0015100790701c94503400c1018840c0252820b882c0c00700d162090300684031b03694460b407146c8021403082c2e0390410280309022107000f6401f85060300c9090141804401b0502600440c2c14140c110000c881c244410360b1054619495000c0380d00031021 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 853474766 1250 853473516 853473539
    0x6090301143705040206160c0e0c04180f180302010b0a0e06011d0102160e0601080108070510031505030d0c12020604021309140303090d030e01050c09090901020f070804170d09 77
    0xb48240d0700804104035032100207c1a41e0300120f514011000c0014007403901d554031001c9000201100c0316808203010074001d2000c071040d00b42d400d0703492a201041038880c4c03001e07130401001c0300f4210321134448154400904064041d08000e078030031401c0f580600f010b603865140701007494080310f50900048100580780344008019218101136070040c41110110404c00220400d28007864020760741d08010a410000c40f5030740109070502628150307014048003403400700480c0103041c09200c0c99003031648a0078507d50080d07191034450b00070500202100c0e41c00020840180c82016441010b0b03804003548100018882e000042c5180110b40c09007600b60405c204c3c45d0303040002d0140b03400447e06a02e28403800401e805081018600416409028007140c016003030018080f212000e903e606943d05103020040d0100d00201600c3c000842560541525070720180f255009100b5004244001c11001c03a0803c280aa0080035109440030300300780c40301d400c16500b12990b41d07518281c0323114009100110288041d84010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 853476016 1250 853474766 853474771
    0x706050a03060839091b0715020301030c0b091c0809030109030509011d10180b070501021c02070b0115120e01090519120e06090301143705 61
    0x1840c0004045441c3c039109810028480b5160380200321240d40309008040300c85010f48810400b000c15004484000c2c0880c1030360344000c04d1860400000781d060000400500304903110503a0014480c0440001c100c92140207400a0006a8035042e01e20408070f10300101c4070469030100b800404942c036041c10030684200040c030000707084602034001d1044000340d890074015100f003c7d02c06c1e02c52544425071035000400190014a00f040c0c070a02d210741c0c138000c41d103507a031002288035660f14000c440c0001d07840e580e07200d07650160300c401d0351070074009100c006200701940a009c1c204042c0d10340f1130200002a440354103034080c80304081d1600268900400c0084041c45042e00124044c3c14a1842800a0203000041701e00750350cd41801a5100d441c03a4041050501a2119000030b42e28501080006030304c0e00d40509114400790b00500251050300c0605a80301402c0c0cbd4403202d0028024042c5007292000410b819000b511461041c00c9000c2c032056511021019542d1040b880d14285055a00007940c5000580341c007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 853477266 1250 853476016 853476037
    0x31005130905011806050907030812130c0e071404050f19090f050402040b0a06080c031e0c0a0207150203070f1506030f0c06050a0e0d05070b04060f0206100503070605 73
    0x9444410300002c1c428082c00d00760ba084000744031004951400c0c03210660302c2c0106004240d400c100014000181d41200b6100004100c1000801c0b9030382d900b00d60258040d503600060200404040009506060600b81601c61200c664600b000e01144017181c206074000c40c01900c1d80104801341c5201d481c1031900740c0b4a411203050042c0c2401640c0c4002c8041101c841d02c510821031901c580810096040c03074012100c1c041001c2e00d100c4400ca2529000800220b0094010000c455000000c41d95190251032110280202603107550f4160401c01c1d404180b139444080190054095050001280004080002c5050040d50055440c0410136501c0d44178426001c0821a2400483d1480c1450028148104000303148074150b10303443c103012030034540240075030b60b8414800c0010030000d110010741d119403031982d201801d075103400c6403d03600c3c85c01034104109900a2002c0c2d0768041070001d240c580c040d0318401604907076000d482c419180d0f0900c405108000d4080d80c1c2d003590002da410400948644000c2181c00741 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 853478516 1250 853477266 853477271
    0x603030905012f030a0207050a0b0403020d0f0206030a0212100602030d0f02130801150803032208120f070e010c051b0a0909030c060606050304171c0212041703100513 73
    0x6540c4200b0358040e005641d000c3c0992001c9888103001d03804003c100301401d011036409040c140340070250300c0302d0311450000901441490021804004c03030385404107072540e40244220746030315080c0f140000030341046803500c11211941012a8003248104400c2050361500e9002e14a811402030025000d018011400312440d0350070000b20050f184c01a00c1c0d14080c201c1d28002003070403215041402039890440d00425000d40041003031007048401c20900a0314035103103020028a070501405c0c074401c10700a0140c0d07480c0100d403c1081050078030302e19510f81c1c8540c1c034036107a0000e07100c1c0c021300444150b0310721003009242d1b520401d007900d8189000100031180000c020041500355844e41031300025150380101c1100422085a000e0702005a2805144080c01186c980303c0d00b5450a0740302e0145400001d080715100c81c0300090006507101894036071400b00c4d0a5100b041d540d480844011f06070060003140c00740e0700c0307240801d60320418a004070222030040902d021076800309d45c10142000512420355010540b04c65 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 853479766 1250 853478516 853478567
    0x6030c03070311010809060705090f1203160c080102070b0402060d0e030a180e09150403200601050a052706030a02090a050a0e070f031e050f1f060303090501 69
    0x1039007040410040c5110308508841d182002d0005406840050f10a1440f80c001604220103a070b404402d645d1a0b1604446200024090350003048520055601c404654007000500904e10700100e030084100b94802d0949403465950341006508070b00030000010415189030001c01c0c05441d0600180c402840540b0b40080d64a0b04403203000d207194007002861020606202064800d511240c4200008000c4030040800030728013240030380d0f10740104541c052103030b10b42c00c40030a00f03044c0f28510944084141480103001580c15943c40d0360345943c2407050350f1007071209400100b11810800d001c20144082900007504d1f46c02e219483c4410202c00400b9280c0501c540081200541d42c0d01c03460354010201c2e00000119420260f001005580d40603c2140c030315802600100b02c1d0300715000417036003141e800c240c40e09002026045050107050080e90013074054819507100c8408540045900300d007803078468141e5000402c151800c0e0040c0c230407511018010404843c01040b0550045980010000902d4660401007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 853481016 1250 853479766 853479769
    0x1219050711100f17040b0624040f08121201230409030e0306060907141c15060810081c05070516050307080105011802070c0b03010b030f130c030b06030c 67
    0x40712102ca08400007003004515444054000c070541c80c451049480d800c01914040e2520242c0c0b180241c1aa4059100c0208179000c4044030b0b0400d640340c64130a901c0c642d07100c2c1d03504038058400880707000d80b6070a406903005080d4810310140407a50051411840221a030b840c1c54200e240ca0a21039040000c08003040d103212266a865125484059129480d82103100f5880414035180250003000c16014500d01028014502d40001404842c0c590308000c071303503070342c03280380880342d03010042d650030420050a1036040440808860907403020380d805a9103040e130590b00e000a600c0a514903102e2b02c03c0710b0700300402030f44c5025030011601e80e07507241c1c1e03040c550b1506600d9900c1c14584181284030014890329502d09211610382407162000908ea0900240000c1d41807415620a50b565080e40401850380000d03100104401e06408000030001c1c0302c400e40d00c0e0341e503070080540c0c1d960003241d4810070714059a0000c1c050320500203540c240a500311100c041100d003140d56822419001030007255043c450070301c01001c02e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 853482266 1250 853481016 853481029
    0x6211406101503020901171003020904050f010b09040809090703020702060d0b1e031b0f0d0b0907051509190504020703050c06090303040f08220e091219050711 70
    0x40e800040615507001c1c40d0011140c2c40d50220b107000b01c02c0500400c86082980c0c3d010700745450541941d403500600d61500507a16622842c07950000313400c282442c0c200401c0c050f001ca0b906402404c0c480003482119079444c200100741e04102c400a20350f260034032001d107450a08041681d4040c400c0c1c10018078003d0241c00080349500301400000d121502e521a04071941400464118101008401a5080e005110019856024401d18040140410304032814140c0e85d100412141040c00b4012080480b04d0b810034801220046880302030301c3c407400c10009507a042030b00e150b04289900c1c4a900d410b1240d100104408070355884038000042c005608041821f988900c024144248691511603a44110014440c108030700244454401d8005008110124602080a078802076001400a036110312003c606941111911500340580010311008509c00c00e0241b24140103001c44001c5030303d41019940300c1d488500c202d001c40c1c038102c00d88400c440035403401480a0060184240d4001c92040e0300d501c0410708 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 853483516 1250 853482266 853482271
    0xc04060308090f01050f040e0a061a030a0c080606030412020703050f01020a1b0b0126011a0325050402070f0602220e0c0318030d050408040f0906211406 67
    0x10394190000d10b9039058030305200000d0700c10340f080c2041030038502d41d401c1006090203035105c0c45496a44840001d849084d895200700003a10104c040c01c55444c43e000b840301c65a07042121150011440d01014510f01809100c04c0c2c0d2240300700404141c5035940d9581d03050b04541c0f165592805500c911500880052130a0000500d4440712100041c0c440744026001800385081e660320180c0c280001900740f0129030b4242c05c50b03054801000d085c0c45099484803014817807001100d00032289518000d10407003194000c5520000c003510890031110002c0042103035615070301b0300300071403100f041d86140100203906054000c1c0c80c0075401501103503e420004e07100c107010f0381c2c070062001300840138400c2e0842d081e075840412000540360880580e40c141c03610510a1140c4e1002910a8450f09030101d0081c0525030308008545d588003415102f03001c0f03800e0038541217940340c02500540b0149074590320003184120f41c0e0706c03c0f0011200340035081c2003003003515404441d0249129405407034183d9046401c0782c282c0020000c960 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 853484766 1250 853483516 853483523
    0x7080c0f0a061a0a0f0306090201021e010f0b09160f09120503030609090a03021504020d0f0c050111031201140a1e0f0b091809033112080415020c040603 67
    0x886105060303005540f101801860351042001c110306008560004030a90300741c0703074400000100c2c0340940c00140d103016030040585501c07030f10680804c0540b51064006c3c200d0440751010074030000300c4500401c045043c0450f04c42904000241c551642c0b84c1c0b08000415280c000341c205080c03a00c5d00c8404c1c420720a000000e0039121a4030000038002c1500303001c02c400e54801188000303803401000b20b82e8029200c1e4a040080d8140c0c4006030081410755850030902d2217a02d42c003114008420604e0307e000c3e80e5811140c414240800c0000074071480001d40881125440419990360b84d0113a802c1164600e1000403110400fa003008050790041084445408920b00c140100d0840410552418250002c612004d800500c010401030180942070340b5002c8007801c3c50190b4620f14201a904c03c1965482d501036045100111050750100040c00d01115015280321143d51846e00c2e6105d407103040d18000d45010b084000c0441c40100010425400e041075a8140d03035000e803044c0c50500303002c80000740641e000d907082035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 853486016 1250 853484766 853484771
    0x507200105040b010b0f0f0c0c1002060420030a060f021b070e010b041a070201030b0910051e010906050a090503150a0c02011e09080405040f060f14030307080c0f0a06 73
    0x40144043c8519050041c104400000c1c6000d40c1c031b42100b03d0380c0c003858014541124010440c9848080d00340002c030000c0001814034007403d800c00500030350b50b6401f0355080d40c070000d05c042c40c6011981003c141500f0004041c00400741c0321000d03680c000081221141003e000ca50a00c101c07030300c216903c1e041d411841161030041c2502c5040450704040e4400c180d10070440d1100400c010840c8680c1d00c190116005a903500d1b86444032020700050707000d08210019194040302c0751007000000c1515040403c15203000b52918685540e0038944180071000f44400a808240500d40030031826100e507006008241e10b03454003100441e994000f0038039080d1848035014194040c0c6080182c0c07550944070b0122402e8003440284130902d030440003810603810302869901c51684564000082c81000d00c1110020000a030040000000c5070050800414960160306060048000000380b03501030b4084240218a004000e1880c02c0125994101280e00c0641404100d0192000300c200c0c10700140b040c8003056026107000f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 853487266 1250 853486016 853486021
    0x1020a110a02010206060405130605040503040f06030207020603060609190306020d0507020c0d03080a11030f090f120d0b13020313020301150303080f04050f0a0c0e0709060509040507200105 83
    0x140000e0395400340d0304010340c82240ca40d40540e030300050071504480d0541d00012261280c2440d0702a58900b0200a0240b46c103050500040000010040c42120104003a0804590f19140110b0503407080d041c01030340c004001d002046840c030b0400c0c0203000503035009001c510031528910401120000740c0d80705544082d40498600692042c0c0c3c06a150302c45003d00c060400010034000003091501ca090001e0201300001000a51440903035002c205001c1d00340240e15140c2c5014040200751680440744242180500c07400b10221903400a05040001c0014030322174200000805e049008049403600303154801c0d44150304920a20b00c0b4401140101c4072891068002c0100d40141425104850010000c00002407010000319520080c219000703076880444d2001600c131400d0071460184450b454244030f0158021600400c00c44800030000c603000350203408003641d200041590000c16502c10000410020004060180780984c0181d60005841c1030411401c40150b042c08200c5030b0a03401c05041d0381d525020b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 853488516 1250 853487266 853487287
    0x31a040506150d030c06020d020c060105030f07030309090b03013b0d1215150c061b080a1d06010b0405030111030403020d2a061a040b060a051e04080102 67
    0x10306070701498807414505030461440100f405040c0410010f000c0044884001003001241e804851440541e12410754846c020030103882e46811003031140c039119100d00011100b0829001c6075000440307030583c0310980c00e01e00d0000241d000d000240c4c1429855542d44011000d1070761458164172107900704074013480404942101544d40008a512101c05960202108a44140d4424100001800c81d5440410300d558026150503000c1e445070404102100c103c03405151082e132203500500114041d036814004c8000700c540359280c0315012484000010113880001d00b01b5040e9410101303c8400c0b41c4111815020640e0a2904180b001c2c1c110400c0b0304800901004207140c2409180e404001c240341c00c2d440e60800d603401942d60621000ba0906110f004403200386014000e0f1000d54030552001800c1c11240300340d28110000340103509051030040b2142000c400582064032800603103180242c412032400e83e11030b0064540b90412281e1a40c0c8003201440301a4100d07081010b032004140f0700001580300d20801c203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 853489766 1250 853488516 853488523
    0x130e070221091c02060f120a0216080714070e0a2901030e100203130605090f2a0a09020c0c0319081e160c05031614010306031a0405 58
    0x1426100c054404800388250104048915a10088503c0d00980c40c2c001000390101480810196101c2408184c0c801003031413010090101c00300c0000f10030301070341d19090300d041240101d0303a0fa0700048080b41c07400400120444018400540203025901142c17460804083c1750028075000074141c400008103014483e03003180a00110389d004040c403000d00c02ca0740b85c8400201201b0f0b204060401d030f01c4001210f100c000070310440500c001c98000039596890418107203009114510000c4034071616241c0080c812040c00b00390001841041d10142c0351181c4156154199074401003403030b04504500001c141c3c010350350620320100034168000c0258440c0c014100150404c40b44002250181d0407605000707112841842900340c0c55a808040749845a00f944524030421481c20078510201c400000e440c250414220480410303a84642ca419040a84903070130706882c2c40d20700c0c21808140c2c0800c0070a02012a80385901c011009041c175001071040ea0b0fa848001e00002600810745003008403e09102c140481030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 853491016 1250 853489766 853489783
    0x5030904050a29090108070303080f180d02010903080a0903081f12050c030706092d0f03031133040614070807030b010801050a0510032903100908031b130e0702 70
    0x20087c0080e240b654402401d42c14000b0500c10100b4680c50004403294120480328041c0c03003040c1c003160188110810080d000381000c14066011400100c00030788a049a8041e900c1d61550550310848151034040650300c2d20740110402d03201203046008082800207010404a2280307004000500800c03001009150410910340c0015040000034001030089110704603c80c00340c2120382c100d60031400c0c0c11071291a1020520b4000e0b1002c14040840003050540c41f092241004017072000380c4045941c2c1c0240c3c4114408004503c6008260300d4013031500e481d00c00c400720350340107000d605c2c041500d004080003900c41c0c40e0111b880c080840c91450074025280d9062040c0c001c03841c82070901c10002c0d41010005103545807140700361482110a82500221548690801c4001d1a9052600c54044410800800f009204028591702a10450400315400ad1060060150994110710750f24a1074640c10840d0444000741c51160814000401415440704e2107480c11900510300c40340e00d080c640c01c1070070000b030810300d00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 853492266 1250 853491016 853491029
    0x90a02130506010905090403050408010615030c0908100b0411120405060702060702060a020c030d1a0414040b150111030708030a050105030303100b0307113705030904050a290901 78
    0x20705081109990300000301e0800c1e940201c1d18142541d9451404503660710071908140810b500f000000600120809440380c4086850349052020b110341840494240102d40308007000c42e4495a20024103100c5903200701c969507009800420f5250300450722103407503800303c14902192451a4204018807109010990f000691032000d01418186240003c0d070320344000d440c8041c62135000038020010309003002114100c0e4013100717007400070303178146406000859148038030305020340d0501d04000b054800f03815100703110325808038400e82e187d00c420102907002c1c0c8400390b442c0c0c14040f0140c3d861002190810140c00c5861042100c140c1d2032514481e50701c29680c06a002c40d00a50081c802d010780401810906030541b04859a000d0f181d9440e0101107820b8005281050120300515800011410034511442c00c07000303106200c0c5290040424507a00da11209080280c520b030820f02c2440464076180d0446030304801c0c96a008210700603801d80400304851103441840c0401d51240398408241007162032035004010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 853493516 1250 853492266 853492271
    0x204060b03070905101e080f01090204051e011b150b060903060406090303151716061d030a140a0c060302192105040c0906320117090a0213 61
    0x20300d600041e0500c0528042c00b803188005a02e03224400f4884ca982072070f20001e0010003182600c184501807c2d031344094402580e10b07000c2c900041440b0085000701d500f150f6003d002c1e40c481d04140001310102004040e01c0e18104031030428044503503203c03121002c12450040030100924a0b40c190068126504040d169001d00c01c04c1c400303108070741d80105000398007503048000400e25074040c1ca001c80c01019001540c21031741c3c079118000708801c03110724401941188074008503100a482c0c40c03180c1400394084c3c0700300c0c1d000450821f544141d20740030890038502d11002800721b803042d410554401340700461010804046070700040c40e0303a0030b1009030003200000704582d007403c41ca008481c100e6402c0c69103007540007004ac0300780b8180701c5103c082d510508a404601c3c003c0d040101c8d00741850000031094803407085261031410510041100312814610004055001050021582c2d45c0f20414031048500d0a00310305114903a6803501c2c2000c0304004007407040c0e40780710182a0300e000c207104010042002240c174101980c0f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 853494766 1250 853493516 853493521
    0x230402180c031f140904051c030c0806030f0a080d32061917030d050c0304020a1d0103031202091f0306060c0c050f030f010c020606120a03080c0d0b0405040f0204060b03 74
    0x4103614024039400001703071100302d103598403400d1403450b0501045000000c000b00c0401941401d034581e0104443c1041c4c1c0c0d40b0113010761a02410103070f40d03003900c108151042d0415440140007540400041c4052a0012030103e4240010300d07508003004038484510300b112141d01b095080d103041d0b500d40c140d0310240c1150400c00c5e124043c0354015660400303004038600558131040422401c0350400c281c40740f8101080e0148194906070480d0707130355600144c0c0c040b4011203483c007000c24201072560030a44803141e0f2400819803a07107940c4085980d250202c603030101150f400c2007041520703201d810041003101c2d0b9503a480075074000700541c001e003100c0312640014100b16080304000000f410b446041011214110341900002ca26800040c4c104241c142704040c0542c82c16114615030350b00070610781c0c442e01e4211100c80001c080c10b00f020b501c42e01500310040004080d200080c103840c00e20406000d070020110743c005510340d8000041421114160f4041c0d42e0710407021000d800314075107802150090000d048400d400d50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 853496016 1250 853494766 853494779
    0x11040504271533060503070c0308040c03081308061b09040906020f030a0c020c0f0d030305041103010606051b1c0807050f0d020a02010f230402180c031f 67
    0x8a641401010a80c040524252140e003d412032444a00c03d44184010403079038a901000340a00b00c2e14410700e070042c0b440000340040c010303400c0d2071281040d41c0345d15006403602c0d40c0481e801c40004000700c031080d032991b0011010802d40e0001d080100d02031071803c801582489605440c0c41402481c1c01e009200030681200c0c919014000d5a44c821029034001c2001100c40c42c1c0100a070080c0940c4070441d0340040104000031000750030428030300ca030940a8039800902c020510124a520702c0c0c000b60009810f14040c00040e100f5800250702c1801000030249070f25215000034251238160703209400140003c0307025405000d80202c80350351200018010b000a03201c158511541901a07110740c0280229080016916401038044425202c1c080881e40c0d0f403240041c0303251001350480980038006610780b0070188a00c401034800c0e003441000b0740d040150454034080c1c030704040b4a00140200d070064000307503d8071507003800920058011518410b03500d4903443c15680400c2903041d84816141001070702682084903 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 853497266 1250 853496016 853496081
    0x4020307090e250803161502091815092a0702030a03050a2106150e0a05040b0d021c030810060906260f18071d180111040504 55
    0x4042c610580300f09288940a405003c011030344501e150b400002071150040301c0181d5140705061099584001c00324841c40140c1c00c03030168101329a04440c24020f1810382d41005484980c0c84205010040485087c0c0004504c40350025150481400d40000f07031a00d00c003440c1e41c035046041c2c2d4500005405d25846400103903541c0c808010240074083c0004504034602c0c0309881030000d1908001c22914540514000f0100800c070318400c0e800280b500001e0b01c0070551242c030b07414502480050000c6442da04050410009007170384024075500c0081403403d40e0050711000c2010504864a11006210214a003006405840000c044854540c044c40040c400710790006069800d40d6450300d05041d81001b01018618801b0191140c0141c0380e10340340800124200f403540551144650f2413001000d01a0501255920a02c50041c1e072040c800c480c0d2108880304d10024980d9206083c42c84040c10a010400340c80c0c2107810071002c10495007000641401982820300801b20301e580001100184c652654200c101d5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 853498516 1250 853497266 853497283
    0x150314040b04050f07030c14041a0f0f1801240206011a0f0309070609050406030c030209100f0e09190201020a0f02041b0905041116030e04060b0f0304020307090e 71
    0x503001160703020909001081000c3d40c401009001100c03070385a00d81c280ba00ba10b84c2c1d10712030103000f0380742c0b00507404031814580520b0841c500c045100c1d9030301e100c82e281080f61081491783c402c1d42048440c1c0241d08140e440e80f4080c01844800c0208030000d505003124805001500e0b034818030000d4075504034058660340020704504540408940c01030420b002c603140c1240384604001d40400142c003000f4854a10b44c0030a00d60200e070283e0700e4814900d959035003400145e900750b00c405080f44003500b00800150512864070383d40003041c010311b156640c0c1c4560708888800ba003a00184100d803807610402c03822034020071800743c0701e8002040a04030b05905a00007590380c8101c3e0001032010040c040320388115101c0c0c5c6c208100100801c1900c510384080c00200501410380e0b44140c2e8412400e002140d40b03001d00381c2085982c030a10074800c0d00012081c80c0c0313040c0c0714820104502074019580d400001554180d04000d44810111101440d5403800c0500400d8030748603d03134000b0725049181030840301194070001a13104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 853499766 1250 853498516 853498523
    0x12191a0f0f01120c09050a02090306090c01020703031808030703020f01110316031a040203011e0902040b0a0c0302030f04030f03030e0708070510030b040606020a030212040b0f0c01020c07060915031404 88
    0x1151414501001402c01070b07401485e90500388014032101141580207828094800c2c0c084a4550381d4030120142d0301d140b44c80000d405600008403d1002c40c1c421484007100841e180d44495010b981e03280040d1450740460320a40058002054a0340205001e0041e8412024010781507400c1d4108185180c000004054046003031503554132a20030154140c170b84a0310345100c020021034480d81d440c012580204101c903030445c00121212004191240e1b98400c0d103050700d0301120038505098050900703442d40411043c0550640c8400e205000ca00840381000f00051841070244001c44035042c03078090180d03910ba980403200c1d600804024858600300180c0501150401c880002e0164595201540103101030007a55800c2170030700c080400c08540003c4e14000542c07184e822507402000103000003035140280c0c06000c2c0f04140800c0a04010800c0001414a040b0408001840c2c5081340070420b1a0220550059002c50b6440c042040001c8020600c4442c800042c20140403104a100c54505150070081000303 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 853501016 1250 853499766 853499789
    0x20d09060f0516060504140f030c060610090e070e010f020f06071d210606011d09040201051215042421051014070c0b0612191a0f0f01 59
    0x80c042c00c503800c0c05843d1180c109400300000d082c94108003040d0305103400215802c1c031a8000c0640c44038000004ca50003071407120050f020030703201d0008100103400c0c80c11868040243d8460003048500c129900540600440d07110036400303030303054400585840c510000250564122455080010001246056015034689000484001d83c544c0c60040101020219030700020b00000c0c003a0a81851030900481c08404001c4848945d0303401c004640092082024040c1c0140c82c00502d05c150800200681e08144141080d508001d241d0400348581c4004455100c20a07881c0b117418402070a0911410008940005203009504845059111085480c0c41064012181c48190107015000355815220296000c0180d81d803a502c0f030304c1c0a2015100015072100380c070012030003150209000d443c440c800f05510808103245a5185000c0120000440310343c1c0100d400380c00d05c00314440130158540d84000c0e2145103c00310803070700030b202d144500c10002c1003600001c003003005001500c04400c100d03504503409683c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 853502266 1250 853501016 853501027
    0x6030a0b030f011509060e0903040603180b0405010c0e0402040b120405010b090106022527140c0714070e040f050102120112050615061b070305100c020d09060f05 71
    0x219141600390404002c01e9407801545003034021000c1540001c440c000071041c0411510f42c0415440b0107400c0e039410045510030082044003034041d400c58542c4003145441c40f0f1204100740c5825511420840c1e0071034190350364a0091541d640c00c40d41401350444142d170f04506140c1000e00f0808544105503500f03407003500040c002820884e094120300742c0034901404101c069655070001955680d100f0302e6112002d4500c602c0c040701e0705288449502203d468400c8040c0026030300c0200303c006800582641e501c41c1d160b80001442821241030f00740164020030910340d03101a10305002002000c1c012500c246900300600801180030b480304d070140c000303803c500c00802000c0c513450002e0082c41a0108116072030b82d05400010080d110151922400d4000d030141c80050359001500e9625040481e03515911040134094800404144030307032070030800a00c1d01200c030300d503889885161a003444103900991035500c07540345180230340c0c0c1405211000c200a0400484181c20800044c0c4084a0080300b8070030090003164 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 853503516 1250 853502266 853502269
    0xf170301170c0a2610051602010216020103020304030c02090c0c16050d120c0c09091203020702030d03020d0603230c010206010b0403080703090b0a36090209040b121b0a0506030a0b 79
    0x442c0003031a8213801221038000720340c0907000140408840c40d001314000666114005401802107a2040840300701001e0503545030360054009400141060b02040310105c291001038540d0195180940b0b981e541d40f58132060900c4c2454a002c40418407a00c082080b980300700b0240e1a401000055907902044c41650508061022680d80c51416000350003004030210006440d00150701119146000d24880258800c1c108410340a81c414950025019803045004001552095025102000384008042400e940d61346071a1103602c0076041c82d0031100c1007041d9100100c0020031071070250440c20b00181440350724050404c00d041c02030f484058504040080c49030100f501c1138000101070300390070100e0707602e804402400074055220220119058004840000c10b0300030092000350181c2c80f50300f04811164101044000030f900090700c6130381c000c1c1e180c0c0243c03004c82d502c0416420301903424400401042c4c52180810100030820f0307001c02c2c090f10802c4800e0055840c0c036403c0b82d6210215a07404607440c00301c0300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 853504766 1250 853503516 853503569
    0xb04050307050a0b190c050a08040201120c08060a05090601050d05040303090b040f2a17070515120a0504110906030c1903141204120f170301170c0a 65
    0x203000418901480b00c1450130800310740c290f40d0044c0c2580c401d5540c1c1040e000394810444109070f0500c40400c20511548950911500c2c01c198032920601d40b03135002e0008c2c0c8000d03800b40c891a003c0180818145001c100007800c0030010700380180000c40d1640528184040040d100e44a00d882415842c5d840c0d40021f4141402a042100b18030f9100c80629214074160501e043d894100000858a241000355546544290708110500d8482030004101c20b5914000c00c0e04080e482e440e8030810b0b02d0040c540001450350b5580ca100d4242d42d256103141d507443c8000310300e264902c0b0f00100b441107000c1c075060601011a091654021180009079800300090b20303000700080c58003021b6042e86510a454451019248941000c004c084038401c81c822205441c1400c03080d030311824070114004001ca0244406c20000d51104852424280138070003255201000b07480d01f403003001058900c0707001500d000004100d0b10350801400110030140c5c1d40074200820900b000030f000b01d0303024070070105018510340b8074044080300c0d039 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 853506016 1250 853504766 853504777
    0xa02010f23012c100e090a0b07230c0313080118030c020613170f071d1b030103030c0b070318020f04020408010f05160c05060a020d0b271b070b040503 66
    0x2242030f41d494081014080807450340a90708107a201c3d04085051030100050f030381c4800350b20072130400f074036501e0040403100c0b111900000700c800e4031311034440044050940002c00c94928004003640e42c0e050f03424000380b44080c041c1e10406c0f982e8500058010000200b003041d408071075040c548520620020b0000542600440d521021030b00307494040050318060b8002e4802c42e03040401c0c00e56282c505419002901e6800b58803602c0344150364100600030b42021425120782c0300000c500c461420705044030b00401c25400980080300841d0000765039405008000000583c09101480c09100f01c401040700c001c014038035103100074042c80071600662125690b540654018080c1c41c40200501e0503075482501c0070f03040035220410600d001c00501c4e180980308106150009411100a100c562076200c4640005e500146803d48016a5040c4869903540c030703044242c4100c462049102611800a015401c0746000a0b0852142c22070481c2c1000100503818182e480c025000003005103036503103038200242584140e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 853507266 1250 853506016 853506089
    0x21e0d120917210d15030b0117031204020a2c0130051011130f0614070303060302100c1203200306030307060207120914010909051b0a02010f2301 64
    0x2411568140d40d42c00007081006c0328080e001e0718240c0d03648c4a05060100941d20b0030302c0e076581c01c10449000170a8525000540080c80a05880d10350fa9540c101d101d1626200002c0c0d42c2840b40742001c1a2181c058103144c0c0d07025010385111800a8a4903919100d04095a890355581619003606080300b0300c0028064940320b01c40c1707240180724030901001c0004550b4070045080c0314844102030081000390600d00058143d4030940c0f00c606598051020404640d00069000c4003090340300c060200050329070181b69542140c803521802e1421016207400d444090184640701d0806241c650355885501d00c51150094814584400fa913a0f502ca0381c01203410351142000103001d46000083c448108080306501144007030040e55055502134980408440c0081d66407003040c0000e03421002400924140c5e88800d80118015489100c0102e4011000d4101e801c03420b030b8180580d66500d01c5001424a038001c81000c1c04075042e80c00c408662002c10744400c55018000c02700c3c269030b60b50440c0381c10042c040503011008038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 853508516 1250 853507266 853507271
    0x2318030c01020d060b0307050702010809100908091311030c0c0f0a1202070e010e1b1204080903070b041d09070b160614060904021e0d120917210d 64
    0x380c08100a0203544500c8528105500d0100001500d40300070081d28041d48103a07483c10b24148440c3c0045075803031805042a8075a020f5501d004600c0f44c000e1065040641c400d40320f440d04c3d0b8000008200d1508152408140c1403410810a407040300c6081e0100da6010a81200b40da40722010440b40078680350420000e1000c0d445078581c41c0d018841e00e46001500c1c005907500310348503603450349841070400300f0038410710408c511a240820002144210134482d090281244d070380c140140c8030104012036030290f0b02030710003640006801080341010701008000d03010741c000740c0386860314065507000900c001100032906580c108010403480542400300900078161007a0711601c6000810044a0904402c803007110000e107403008103007007500c900790b14520031032009000c11400d5890b5001e2040d415441281c029107603024524050480d034403143c9905c0c8890064042182c040c12408014010200c01d4200162103001d1806030300c1f241c280014002c40e40c107010001c460741003c001c04400b43c24020b40011402850 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 853509766 1250 853508516 853508527
    0x5180411091f0f03020a0314040609020909030f1c0b030706020f070509070210110d18050f010e030301060c05030d0509010507020105010b130905190507020703030e04231803 76
    0x3804007400024104503200301c1502241c0c1e84101d08012080d1808002c80c56100c2a070a40324041d6010701010103407400c000c00e20301e10810320045100700486089a8180c2d0f83d032045819411b081344240e0388640d814004603d03228400000304030300d00a00075030380504541c032013000d80502100d40002510003400303802c50306050b03120301c000f940350440c030703100c0480f40d1145003400211860020042d41c02044c07560040d060000111882a02804500307413481203440c2e041020000d0071681e4410040040c440c400a100342d4a85460070500f44a03400a4450310b903030401005038003120004c000c50381141d41d54203280c0c80d100b03400e1401c51b05502840c82c05244d40762420081105500c0190070851069005078003c02c0305a03240e6101c07210502491110360b0040e4280201440340c0509a400250090000c051241c4a49003021900c0242d800072500900143c0210307100b0000c144e04500b85840b00d5408440c00d010f085205024107035550541c48240c0f03504c90401001c10f003051000036440502042410583e036444 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 853511016 1250 853509766 853509791
    0x3030403150b010906050d0905010b1f0e03030f0909040c0302060d0e160e0c0c01090c150207060e1e0f030601090b0f09041a10120b010e01081c051804 66
    0x40c0d086944000d01c10b003410310100b455840307841c8101c261002c68035202d00b089400c9000d0380c0200003002d02252150740c0c840001c40c803503071414094081069684114016201a2140101003008800d0414080d40c418071240b10003084542c10360394160015070700c606c540d503240d06040c614440781d0f0780080d400c0800081c1589605015820024426035008210740300580c10061030846000e41e03101d035141c2c00403a040454040702202d00102a20840000041207029817920350100e98055540050f00491019405258158040c8000710051902c0e080c848000c0c00311074042051910303a4812010107001d01c5d400c5102030341d40c1e0810500360140103000c40b0099030716800b0713910041210301e0030036101d8904003081035128a0401d04c0f03984207540c03280030185d03c0c0303200040058002c070003c2c14a0034510034034000444c044c3d00c19445140b0700c1d40506601010b03540b50020800180006030407500040d0000c0c82180801007600303d0041104245140603951070f00304034400c1070b8481c220013685a105043c81c0c42031010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 853512266 1250 853511016 853511033
    0x1812021221072f0f0f010e12131e0306050412021b010c0f0c051003020d05011508061e04020c0625021c09031a090d14070206030c0903030403 62
    0x890048500300e2500b900d44070000d07244072202c012594242140b000300001500c800c0c1030780d8600c3c1c0d0560340445406490f04881c49090410a1100ea50203a41d20b0505069114040011500c0c1403c00c06440b40390031281000f81440300264001c410000071014a903102c0364003900702900c0219041442000942424500740c0000c0700704041c03074001807151240c0f007a40c0010b50080c200015005840d0190004415500c904415542d00b50655018480e264006220b40f0343c1080c8805450300b03a500140d4500306085090220759068105801041c65101440042c1d60000b0301244c0282c01110613070100300000b55142030110010600035001800410070002700b1000040440c0159100f810076101c600600d03c5007440c03040d1103030007140168400a081c0d00451110425086451098501280303501d4494030b5110104c0c0c03103c1c001107a208144010010b00351800d0040000040c0e1925188110340c400b000451402c0c0245007002c1d11074078001000c43d4180245004603080c40b08007038103681d01c469503420719918 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 853513516 1250 853512266 853512307
    0x3120225140601051903110f030607020a0605010e060109060522090c1b02060304020d0807051c0f08010b0f0a020a061802120708070b16020904050606031018120212 72
    0x20684180c02c00825246401039281e00c16036060ba08005000386551187d4040c1400300050540000b408a9245220380f004d1002d984a60515002407120200501e4102c0442d0380580c0003c5002099038140a0141e9000c100c4500711400340ca007194849482c05403101c0c03a14400602581d01e400a40b000184102c4907400c00988069191100340004080801140301d014504200a40c0801c3c1040024014903005004a81d42c03402040d4440c148544c03950356514190106414510f21201022958400c0c0d40c130020b184900041031402ca40c00d0351404941a000c0d00810410070100314010590200c6a4800c02100050742e030014424003403104180001d40320360f4400f803001da00036952844003c81c036990018041040310b850741e00900c0d4082c50714441d285540c20202d02250714203014021036016170385002e48180954000c1028005504107a41014601044000c00081c201d04040100b11514004082404c80395008401c1c1050380203102c078102e0404011000c1701e450104003007607184014242004580 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 853514766 1250 853513516 853513553
    0x14070e07111903030917040803040e0901020903070501031a04111b0a0b0613090503120106030c1d060703030207080a05071b21080405060a0804120c03120225 69
    0x10078410011107140d21205208060070700510942c0106000a00c2603118020755805010b9442002114100d401000c0d84240c0c010f0159030f1001c80d043c04402e54608807980c100c1c0c0c02e00001c5140c8107203503000c00e445152901c1b079241419580c0c00c440020b940c80c1da0054407483c0c0300174400c0018138008000303108181c20607241c60842c40c511403280700d4107800010320032450540103d40303078081c1c2e5600020048030000417404100c03802d40f1980208002030040005d4008000c03404040c5d0041c1d814203c2c010304a4807405120000c001c485007a2418415140d4100007034201c0607940190394842c00c5c10240d0181c854070400820406000440315042c0d0750050182000030300c90040c00f841034400700c1030305c4c207080001d00804140c05a41c132043c40c1c41c007075450722030400a03115000e0b06062a1761100010100e41068072640301081110040000b0030130406038071036807400c41b828500210b1081d91001002004c41c200c0e15004181c0c00140410411071440c64820380b03d82040452440400038076201e5141c0c9012480340 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 853516016 1250 853514766 853514777
    0x509010501050f01140307140a03050402010206151e2b0b10030803071d030d0302130812030c160209011202040c170a020708040e0c070c0b040312030914070e07 70
    0xb20340c0f0b1400398440d40c0c00c2081613581d00f0b4034118110040c01298000741000050080380b050044445883c0401381004128a86000a0380d26090001a0509600500a03c035600e8030004081c4144d9078132002d80c015a101d0900c0c100c04084510124101d807003040d0014454004041d50310104101a04c1108450381c85207101e004162500c0f078512169180501000b80540818000216403074425000008100100703001e16104440e40300200b42000f00042c5808000307500020511408121070704a03800030700480c0d000b07207202038800081c1401400b003c1e000009080380003a10381c568803021a51005400e40041c114003607541d4814501c0c0c90038841c1d85049010300d09008400700c00f58062a9400503010b07070003c20783c24682d140c42c0d5036002580403003801c56004c80c00740400300303585209118071449a4072485441d0b90f26a6070382803144400c0000da20221410034108400c0c000902001264580c00a2504000c40c841c025440c24880300c3e000107040d40600d101e07000002401a0751808018010038090303c44 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 853517266 1250 853516016 853516019
    0x15030b1b0901020d030c020a0f0c08120c1b0612010608010e1609060e12070906030212061b1303240f06030c0e072c100504270204090f0509010501 64
    0x208602805005001030140e00a0510130034014003075040141403030103502c15108804016500c0d01e0001ca607102c02600c26007541982404220010050305a2410b411250a418203035404c09a556400c25103001c0c21000c020382d0407041d1039480e444161150115500d681d6000b541e1958402000c6c61403d01c548002c00b1806004102c0400154202d10800f0440750340d016823071814034400307561951400705015003042d408004441d491300188444001ba240c2113102141c01072960041062140c03001c0742d002a1034003e5020f0042c60010407640c000001c503040d002031b0f154100781459030800319540d8809020180324602040024511035442052510300c032108211540803580c0e000d0071a034050100801010002e0014001110860040c40d0300c0302c602c2c900201c3c680706070322824000d000903010a1583d40c5007040300c0c500c035180c540c921044a011520f05242001d203001090501143c82036442d4921040e500414966402c0d550102d8020701072041d000c0c4a00511049071100816084079030310055441d0400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 853518516 1250 853517266 853517311
    0x3020102090f04050610200304030f15050f240402070f0b0a0b0604180e0f060403021515040c111608010509010e120313120504060806010f050a1215030b 67
    0x10b007809101c0c050101b450a04040b032007518000100d2001749561035580c4440c2c020148200014000f4600c0b510300c0b042c004103103207043c21a0229920411001074284001c000304500320060340c95010681d0725082000c0560301005e4440c40459400180c2c0080c00000d04906200c200060707003109500c98015448a0341d5841407100494230444007440e4444d03000c00041042c1807030010f22260000d40c04000140455030207462901c0d10490040782081c0740c010004000600d501800030342e01d0000030683c114007030b140aa80740303114044140d101500c95540c030182070046c0b51081c4030700049600c800007101d034510149442c5a5501070075200321056036081400044130000180100506411310390010640c8003000e50041c801604010041d01d160680804500049007650300d20b08a04d0510f070700c41d40d41e101d0900c20010140c040040086050040100940321030903409801c941e0707216064a4021603007144410820b0242c1411000156610004032000c001d100240c5000781c0280c0c4803030403215043e4421034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 853519766 1250 853518516 853518521
    0x41e0b06190303080a1e0207031110020c0c010f0315090b0f04140f0c070501020706021c050405120d020c1b03250e0402010c050a050109030807020c0d062703020102090f04 75
    0x100010b500c4000300b0340d006059007052010703009140300c20306c404917000714030300407600b08460540001705a00e1402c20700c41001d00c14802da01c0c6e5503400031b40c50005d10112050740c034a03103040300c241080b4546802c80f074418460340c81002040390345549900702d6640c0d40000b0029000040e200c9101c0d040e5101152001e240074802d1501400310070404010aa403407401d028206000280340c40ca200b4001c00000000903000c0c4020f0000d180301e2000141c513039407060140410f0300c1540202c09645850042404049100001e996685c0486034400580d12620442c0440190242c00c0040f00c29100b400c802401d64030107080da42c81c50490943c102c0c1c8030303030482040c840f14802008010201c6018459002c0c402407150150042d841801070420700910001c0e9982c0e00d242542c00e480c10f5a02d81d5449030500205036200758101c0d040b2000f44002d01d80145800d002400c0b801001000070409079440200190000100642c100520f84010561440440c0384c18064040d45c003004a5903c1588484000315040c030741031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 853521016 1250 853519766 853519769
    0x3072c030c031f0f0b0a06091a07030507060c030b041104080d051c090c1206050603010606231b0a03020609060c04060504050d020406320d0515041e0b0619 68
    0x600103210450321222510f0001c00300301000c0701c071998907042292820346480403007100030b0009503210041c9514091200715150800c01007110807100412281001c25800b07019110040d40100c000101c40c46407400980003481001d000b40c0c1c00c2420013010843d02c0040c8005003081350340c050240e400e00301c804002102c043c4100e04007036440c551407940d0900341e071489901600701184a50320213000e4030780310664035502c13990f207031412102a2344440c20000181006c0c002d0000034a094248504040c9003d2541444046400d1070843c00c100f0120700c00c83c1426030320040541c40030150007695044603407030030021b48401084a160095109640102d0b64030ba807050200c0d01100c0240c0d0720399081c24240001c004502ca0304038400d83c0e0207600c8110205502c4c2e0307140c003440595030502d642d0b40c40c1e50704010035410a05803110081445001a403849034049040441d04c0342c100d9a42d0600d00c0e14030703540ea1502110846018513000121543c48084030700b0422407001c0d803800f8400494002e809041200111500070011b03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 853522266 1250 853521016 853521043
    0x507120f06242d1701030c18060302090c071a010509060111030903060c0414030a083f071b050a0b060105090d06021210080a030503072c030c03 63
    0x5420611109141480e41c4007900c0b801c610b88000d5005403102044400015030440080b5000044412030100780c211600980042c9004078080066141d51111030324000c02d0300c134010034140e000a0680202d02c0c1544003d001d16802401c002d20b0342004020031599400c5402d003141d0840381d003040c443d019140c50144d40e048500003020b0602950f00c40b401144e0f0142600300580c0d441c401440045803e1303a0901170703103218080e041200c580741d519128151841e00c2010b01080d0086d01b100c0404000305608034121640f2005a1032124004038020000c54210f500c2c100d0f02801c1c5110300060740c880203a94018090040059603224020700d071a0585481c03020071040d000030080e900010200000401e40d040003070b8803c005040440c281840503000c1403030b1550003d811039074198000351009098040e54606500688480d0360341d000c244c04c013654166561a030701070260034030402000081e500d52240b2641c0041c1d00c000b905048407404003041d2424a040b001c0716141c0719016040d203400c401e040001e494082e8490 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 853523516 1250 853522266 853522289
    0x3070b0c0a022e0c30031b05030402190e010308090306010b0405090f1f030609051908120a02073e060702090903120c0417030412150f0507120f06 64
    0x81da14056404000c03d0b0b01c01c60300342450f4168074070b51020708401d6801c80340150345c2d40c5817240c400c004003c044034029889106000d514042031034940b64000180d0758400c3d41aa058020805140000d03114010107a1084c54002d40301d10011042010400103020101c0c8281d085488590322805043e01a0140780146904090350100080101500c444126007041e10a0560710b418080e4001c0440710081580003030360b80d40d48440d036100810000b0003102418265890f56249070302240d540d81645440340428001c0124600c00c0850713003d84da1a0b0403603800700e901c0a0a031011fa51031150a1000350800350802d0b1807a440f50081c2e02050664420112202400410651400215608004001602805550b03480c0700501900c9071002030210070f180114600007105803680d14107070351401024114210404a600140070800c9620b040810341e1401c0307a070015040614010340d8201c82c0051600c1000760002504200c02c0c00720050b00b000580c11180c101c1c050510201c20072030109816512588285442d944 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 853524766 1250 853523516 853523599
    0x61508011832030a0f0e03070e01120c08030d0f0507030b0a260a0b011509050112050c0c07090e01060506090a030f03050c060103240c09060e03070b0c0a02 68
    0x444107141501d00710b890b2020200024070b1800400c1c55504034140003c04245000c000e4590540c0000c4000e0160308228000c00300c6604280143c20980c00c10b10502c001c7c821445030b400c0401c480e9820040180040d00112074071802034010744405030000d001d030400c10034034100103d00000d1203401411900100a807440d49224680040138035240018544400324a00404c0503410412042c000507a0b501c1c000e100c1d1007025410106508450305460403a5414040c0c0340c0c10410480e6000305148010000220002aa95491541400080c803400928200c035018449000c82c5c00503140d4003028040007075100030000c1d640c030351b024024248240ca803c95440844583c0400c0007480303907039100904a2103490002e04116900380842d01d45442a0001c4602e07458040803038100c0384548100703c1038001c016000340107240300308501400a044a00a020410000c0400c400041c1c501f00070783c400401d03600703025555031000c0700011a111841058200d10901c255108002c44101220f03002c7d107031a122280781980c48 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 853526016 1250 853524766 853524803
    0x6120c0a090902092112040b07020405010803041a0723010f06060f051c02070f050604050c0108220206040506070602041809170a0c06050708070305060102030a0f080604090615080118 80
    0x185c0004603801c2910418200031900c1111101402c01014000c2c1051f88402c440d204101c1600c005070441107940e4400d1000300080d14088805030010034030310301240d54820ba0b9042000c44402e0740503107092510340100201d4006030381507010f1035000b001040b04000003900c5540454000301c0340c900c00400114144034a9554a604610180c520307048010010700e040160b54039081d0415040c80f00b9101d54000004010601c0811301c07105040500900e071410052030701140c10070100540109040f139294520100008544480007103c3c0a028004e00d4a1345404403490008040c0d4010701580005001064038200f070002140101c11a243d44004010a030404c030080420b040d80001c3c42c2c0700e08000b012041d00002c52003610441c0c1c0207080e666980e00d00f40c607021b0405030584001400071411513100700084440c0940c49074980840440d640380c01009919458009030207000b0102e400780615161101c003040b40d9141400740c00c2202c055400911000050102d82c03030800c103014201620264400d0b00e03105030b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 853527266 1250 853526016 853526059
    0x90615060d0e010e030c01060e0708011e0905100611150118020d090b390c0307060e0c0a0905010608010605030402040f050703060f090605030c0f06120c0a09090209 72
    0xd00c1c6200c0d03400aa400342c8041e0b90b50a4525401d02e00782c442e00b0018206110100c00c2c09018041c01c1d40a42c510303241c0c04c2c080c02c002d043c40414803580399076101e10006140c2040e0040320100080003204018000360403c61b580c00811003082c0320700e90114030741003145128204040f8810b14071070301114115009070300e0600c50340624413194400202d01a820070540c0703450905881800c04160082811004514018280b00ca0f05481c0c02d81d000c6060b1a07010079003805501d8034139080900f0710b0344c44100d515889401440d510714020a035000706400c0c01c008841c2d201503000034000444183c1103601c084021313500c02c1201f0403030f0300038003400d00050550300050108a004400030f40d0080c0c40a000040c0d8180c5000c0c80d101120340c1552a840060f0300c85030200401c0261814580c05001d011108016442c079044c000ba64904003c55070a0058154020280307032030b5a4030041d10b141800c3e1449260051030511202841d550141c105280030130f41810002c01e402e4418070070380d08039210140c03180003000e41c805102d025 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 853528516 1250 853527266 853527277
    0x2220f1a0a030c020718052413110f0711010f080712050411031501090c05120f0403090e181507020a0b19020a0801050f030d0906210905030a0809061506 67
    0x81d8805c5610000303240503011542051041c1c008000141820200804500c20052580000d101d10320700d0580d103055600d642e948103801c0c00711a40001e02600e01303000c5294a00903c0b041c41c800500102c0d1750340500c1030007440301502e110240d841c6440718101c510700350780710030040c2d03110f10018202024a080041950f8005c40e08180211100103850301c404001a03d00b10713200b80f44048484044004000346010ba0103040394201240c1032144c2407040511002074185002001492901a0240464241400340c0a1240076180780e013050801880d2005503044244040340c50b40415101e02030121041154039940903003e88010341c060806983c02d034a4005200202070102c140e042c680b12460040c2251074801001c9021803502c41005940c5810200400340780c2c00d0640da4041d40241e042664019400700286c000c0da5030320f042c900b141041c110b10000b0902c1400111000c103600d040311581c14031038000041c0c40c01030780a64078450b1643c1c91880c029100d00041d2004d28030388044810810f411700d441c001504 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 853529766 1250 853528516 853528541
    0x527010605040e15040f05071e0f050a230408030711042003180706030603110603010605220f0f031e030210090501020903250b0a1d010302220f1a0a03 66
    0x3d60308544001300c50481300242c5441c40440d000c03000101817510003140017039000c1c09d181000001101d940724054174901c28044d0090800c14541119202c003243c80201c10030150025034210388a80d01c40345061340da5400300100341c440d80d8030380d400051646040c0c0502c580c248000105420886000c00e6100102e80020b8085100040e405910b00020b030b10400a8000400c02540c021441500d103003011004030605d1143c99000342803c10060101e00e40240485014021494010400d10551720320103800741d025410802140c80d0682d00000c42904083c850f40a40303000381411050510072031400b64064a220000802680003004070550059207a8003000704540070340000b601e4510744c14002810100d03101d64031110902104102d50022041540f900302a26150200b680342c140c3c0742c0d401401004003000e0204e076140300902c2d14991648650142c80c0007035035210500f20506011000f07008000628001c1104207400da500000f690041040b203403c8a480d808041850710202ca03604602810b5000c1225 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 853531016 1250 853529766 853529771
    0xc130603090f021f1124090304092a0c0f02060a090302090405070e060a080a0206030c2a010b0121050a02070c03050c130516180527010605040e1504 65
    0xd03015032200039102426858401d40e00b0710410200034094680a45e102d01050143e0104a03011100e80f880d0b401101c180740114480d10030b0b5031394480362514601c0f80e50080c52083e41030000c80d5503204c01030700410b080c10300308800800c4940048130301100d01125092015015010030060034003d402c0160041c404601780b0320f07290707544d01e031281c020480d0303c01c055804a44a502540003080390481d9600301a070000012140c2050882c80c0911141d80c811842c240031744101d41c000040b0301384601c00d404481500c6492150140040010100044e8450401c95596429400c1800e94040740d0711442105000c07266500340c015168441c019804003d1600174000b1541c90380c02c022201c0030645980c0844001c0d44544005c00b205c0322034805000000102c4214814100d080c034007440350380301134940c1e10070210040e490485140c0b9060340d500e0200842075480903401103503181d2200c0552884822160a50100400450690b40d03501400c03650340c401d03442a000000e803000c01050044c60400344011582d44010400b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 853532266 1250 853531016 853531043
    0x5060313170d02040e0411010306030b0a050a090609140708070f1a0408030412030e030102040b0f03040317010f170c030d051b0d0309051005090c062208030301030b0c13060309 77
    0x142c201d03400340e005006145060800c004c10030008441c110103d01d028a0240070440c6956100b0070781000143c00b20105680f10070006007901329070341c0003918860700004103101c003c0035410104564410f07000c0306112401a0f803804545240000341810490700da001641760754905d01020740d2030b20741c0c0b001290450f00384c0401c00010031900410103440500201032880088107560b1801511002e810008a03019034010b0208204160710700c0241d80ca111510824903a403640e562404940d01c40003c0c441040b445604000820501e840c00080f109880e0070f20340400c0e4401608040c29512a0207062040c3c0c107501c0b80b0301e294080d6214101902244002c1c0025024542c004498603003414600e240d2100001e94602032142400010001c0c8101d10400030700422042c20106c070b900b600d82c0340112040380103e40005080c0750101650011505541180e144502456215036826440c6d9001f888152505900440451140e4011404444074404406c031128182440c004042e8042c05e1001419640240310029 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 853533516 1250 853532266 853532287
    0x6060d09021302130503100e06060f01030e010e0303010510020102031b09151206011209030828020d05090d020609030a140405030a050d030608010b09152704030305010506031317 78
    0xa020b400f005041d51402c2d0030f0500040c1487c00c1c81141008503050304040f12003403d99004103c541d085203003030340c620000900d10310041e0003802c0e00e0f0110400c59868003c0d4502c2803000800514107803030044420b20140303554400220700341c1c04160740c04540c8460b12070001400080b074500428042902a14a00d6000e070307800382180d0b5907004a0b4081e100404444100b00c00b5680c009000384142810017003c1000c81c032070b03850040180344020000501120448050010703060f2000004001d0b2618040665075585511122400740c0029101202c485c07050a07841c8500c0c50000c1034080c0321300550070080d1b08090300c500044400001c1840048940c410810010440d03440a0005200050140b0003d02c4050103211000b004c54005a0001c00c8692402c20544000d41c0c864000c5074010301d612800d8001e124000340000c04c94460700143d030b003030505000c0c0340b0300c0305000d242c500b14495030103900d0802450703a0300c00c117001251104803007001c0800d0840da520000100103441d8410b56a14407070440d0b081140104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 853534766 1250 853533516 853533521
    0x30c05060a112b0c110907020f0d030b121c0315050a03050c030f0f1b0f27090604020607030813020a08030705070906030f020913060203010b090909010506060d090213 73
    0x4103807015500300c4440b9200b4641280241c126180305480c00740341d4413807151580c041c2d180c4016445441202d9800c08a00035a101700140242480c56000362091030207840405401030901c81021409003561078042d494003080464450030b142e006034840c003480140590214000c0c440c5903040316034003038100c03008903003500d03001c017010051440f900062a00f95910010035250403d1012403529a0340520400340c1080c0c4041887d00746400401e403800300c81050b91000407030103c080700c000c0d40c004039884000c408a6150a010f284510a901003105c150703125070020f00d4903600110740103904a0010844203001a20030694a5031100071400304010000041d400104281c2d4290711030700882e031000c075001c0141f10702404050000c201a00742006000e14561b200c004400c3c044001911035140e4074005158480840004040264024400c540d29a1210f0640010340c00818185008038499000107110070014480c150003000003c0181d42040e401c6001e8402400c03d00f0012038003c2010911320403066240d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 853536016 1250 853534766 853534783
    0x20a140d09080423030f1207030302041e06090605030c0a1d090403210510091e0c0f0e01030b090c090a0324050f10090b061c090201090906030c05060a11 67
    0x10842a013240d40c1d0280c100d8400c54030030103500e2094206545180300f1400c00202d0f111014180500c0355210f08190500383c0c024041d46c2d01091800038440543d8586020507452003040e60700d80c3c0c075001000743d00c40e00e0460b01c5000440e03ca00900e2000c0100c0115103010b6502000042681c1d0078103821444c00c04c008c144440402e507404c501044510001c009484c2c00c41c20341540140304c8000801080c54000000d42e09004540704441d100c07540d03103540c11400d1743c08681140c1c006030030501c00d02c1082c002440040040f8454084640011600701d141d041640c8a03004a500f250402002400c891316408811a0258404c1c2400c030f6002d084014000000b620504100000901c8215102110114420b0010aa8500520018408000500708a45084051003100076600c29100010788003c130040866203502c61035401890342d00400580c04001c02c1a40c0020b11400d200303a81e07500c041c96498044900341c420601004000404d41134062005042180140080c83c10303502e808003070b51400c0031409040075241d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 853537266 1250 853536016 853536029
    0x807050a23070f0b0f150604090f02300708090d0f030e01060e09010c020c010c0803060f060c0120040810180228060c02060a08191a040b04020a140d090804 68
    0x280342009203448104c00780660044040c0f1404100c46c000b000000c10900c01c900541803038590310285102c0100c0540d041e92000107030310b00c170401c540c881c000300e4207404c12100ca04030b08690501d4001814492044410034010107200d00140100c1c00511070942d000101c0c02075a0341050764840b60091000d10900418009000100a142207070034a1a512030035141917801d14819980800b10b80451a40d12540b40024160070a101540380e4649400180d51104100c0f49254400404544e00030b0b01201940101008540d03038050020ba4490030030820b24a000c3c83c400c2c011607402003410318119000e280c210401c0342c9540c0417100d82ea100e955001407292031030b080c5e580a95085150300c640f0400340041519000d01514103156900001550010b9582d100300d0300c0c038508100080010545c1810090307400c044150b115842401201d010850201300b07060000d0100e031041f401c03d1014041d60900e8400c40300d011000741d440c88040d0070306602550b80c943c0410b000d80060755903107030b0f650017194146000e4805002c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 853538516 1250 853537266 853537283
    0x307030e2a0303070c330e09070e030c01031d01020a02070303090f0f05060d02160501020d0606091d070504031205070201030507080f0402011b0c12030807050a23070f 73
    0x5408880c041c0072080114107900a9004208040101d64012140004c5604504408220044842826400b0112444602592500c800d074942d203207600021480000e201c103840003002075849480480313100849170b18198040e005405c5c0e01c1620752090300000c00721a5800000c000740d124400010703089900052021006801c0080d0a00402da4801e00c544024603003002c0c5003442d02c1c2424030411000b0302c80d00ca60340c862031001400b1a6101840d80660300d4100c141d000040741c0050300c0c28000d020703500c6115a40c0d00c2618040b404038500703016003078480548001800071041900c80c5640c1d2084041c02400c00d0060140078840080015000c1007444000b40c40396603181c0e1101020b00c009025150094403c0301401202000c06c00c3e20b901800a065000750241b806001d910644203402114850041d0094108220000c000c508000391502c01c40c4018403d42c0c81418544d2480c20440b5280200008070300020a46074020003004c0d5502d0300d00401c0340c2a107440c0c41c9000c0340c40c1c0c2d80510300c100701e00c0129602076 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 853539766 1250 853538516 853538563
    0x3091a0903150f0f0c0f090f0409061410140d031106071206090209030a0b0403031d030705070b1c0b0a0e0103060f050106050f2a060f04141c050307030e 67
    0xc02d0525144c100d1030014410340603040c1038010f08194050003960030204100420142c0d01c2c2c1d5180c1541c100b10b0007000d0070030020313107a0509102c400340440d00700392200a125030011a0b41c1c40d04800303030501100d600065208004c08240d08200042c040340c48183e042140010308407030303c207009001301c40c0181c0003070319903014402940c0800310075036403503a00c4030a02910521688245850110365030190603403014903d91560b0715407400b41d00400c8590a0f2000d164011100b4842425000004101160060049405203603031445009a01d110756001c040e01440215541f20819003250840b50399000000e020804017501c5c0d00e0790342c018180985c001d85150781c8525800c03a440c0014413545015107440e10b0802c3c946681c11078a00201e02c104c091101440c403580030000240140d46180c41756116051082e6012802e20003154198a98140d40640d074842003540e0802d11030700300241001e0100c0c11004d0509030840011029141d0b0f0f00001c000000f4151203601c65120329509118409003010f001d40c82c4100300c07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 853541016 1250 853539766 853539781
    0x307061d040606022a090f0916080f1606090b070302010221011d010609140310020c01060e0106050c0a0f051005070f0f0503010305190807080f2503091a090315 70
    0x2036a8540d607124805041d031701c1c480410703100d001210354464002c01895000344c41d0805070310326040340306501503081111140d0119001c080440c4401a000f9042d0403601070920800078202000741d20720940c004210030100c10004042c00d90058107945000340001810000c0100ea00c00d03014070582c4101c00790f008401c0044c040c22040c400682800c14824144640300d42c104040a8107144080c010310201c00c011764420110b5983c20881072042e001242000c0d5103603d401140c1e0390183c00075009540718044220000b1441c6071048040d644030300005402005c2088907525510440c0312001006d459900500b6150406030740f65000d40c034015035095680c0200342804035802003030700007100305500420a0403c010004500c00150300f1441e020002c000032059400d0f4900301981c0e100340e00c80102041004503464084d032403100c1c054200000d1440801e03200840c00d45011284503004d05c40240400c1e014103042c032a003a00c0e220080c0c540e50088c0741842c6804130704030010346490411820159008021000c2001c00d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 853542266 1250 853541016 853541053
    0x7170f1c0e060f03041109071d0127030f031704031e140304050c04050c0c06042a080708071202011719060306020702150301030b180a170c1b0307061d04060602 70
    0x48505464155406511410b030703c078100d49c401460b6410441c00402d402e440c00149510007606440225620504540d40d1420403068803002d0030545c042108402c09002084441030741c03a2107658580d480340780e4807020341134580c0c000b028440c0403800c0040c03011200c0304100380c0310001c5000d1401071009102c046e4281c1c04100540310028903048054a0511410000d2040003a295802550004100f02084009c0307506165041c00e082c0e0700b03c100b410740000050034038800300343c2c42c003550700035020b0b10112a01ea081c5542da140c140480203000540d030103115503070b840f100c04007142c01c503040c60000c079401720110032610103658041d041500c00d1303580050813008500e4640f081202e100d032900d42031401c44d851900ca43e85401e400404102d116018180b001040c1c0d4410b210421155034071816030000c441072000181e50300e4120030750140440c8103524450040000c868250889540020002c02d501e17810030204840840407200001001c3e004040450780035500d41c0684005416254001d2620a49114400c100e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 853543516 1250 853542266 853542271
    0x305090a05040606120e0f011e0c02120d0203180330061f030b1903030219080d090804150c02090a091e080c07170f1c0e060f03041109 59
    0x300c2d910b0300600700070380f98001158003000484424002040480000c2c02800d00c0d00700c001c040d50319442c2c00201c0c040152200c030300088281c80d04204100310502e03200103a03075900c0603501c41c1011032800d00c8421200d80740c540007143d100c152040d050141a2194070301900d150082c00004000c9000c292141c24011403140b041103054101c4842c2c128141403401c003003000d0b0310540c521051400b001001d2400a54000d070801d0500c4080a012a4481031b01c000000007603844c01e000c1113005001c1c3d411200850340d10804460708003a0000c41140c42c00b0081c804180080100010071100035200784030000d4001c100700c00340801d52440340c8550030a07248900c10003550340c6008140701d107007500d01a4818040750342c604100842003248071081f94a103034607003040c0c281400751070b800713a506c1e2092040101c1c1c1100034407007600c00080c604040350000d0f206034142035200d1410301d90604480c40108180d004a5208285201038110080d0683c0d281c41e504d0403030892254011101950071086d04c0d403103420305041a400a0781d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 853544766 1250 853543516 853543519
    0x201060812030c091c08030f0402010306090c020d0f120f0b0901061103030406270f0b060a0303080c030402010309120e0a09060303080402010e040b181608010305100c140301030305090a05 82
    0x14554584a80110b441d40074040a40d40100072203100321411448140b0143c10464101c203c41d47c40e844c0161000e188030400300c0381280045c0c180140003400014901907450645425009030203a203070128022140b010030030650800304280f400079628400d265118420402e60060070106080c40d00c00d0a0000754501a40b15001308000e94550000c4540c1c0071041d250842d07400100030980c0d0b0501c0e12140c1c16071318081c10740c41c400b4140071001d00421004070641425548140e140e070701c00d55952001c2080d2004a8880680440c40c51400501011140f900039540300380305060000703144203071741c40d4044040058079070000070500a08110000345403a0785002c004100000307052103018110740d801002000080d000a040c0601020b001e0590b54464000c5966031102070a21014a0031000560609507000e8640d12413035883c590890300141c0c07041c01c0450580780c0040041c90148030b114540c0000305aa0703c4408204a20300690043c0140074800840c021400399440c41e407101c0241c0200040c41090f98000d0703 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 853546016 1250 853544766 853544803
    0x40b06040b0712020a330b0303041809050102210609070509010e210d1106040507030209070c0611070615050a140105040510111e100e0c090702010608 66
    0x20403800400c00219038003242c0c4030185091000003031106030b140c0b030095400105914840242c500c440d0b140b2819001540b1b04050055074076000214512046401d00b0940c0c98040e001007005001039440310440382080d0300c440c0d80c0003484105540311903003260400d250041d00140d0b6000302c0003048140d850042d41000d4211030740045820844000390a40c843c8007680e5060107209911040e055403203400170f80e004c501e00e01d0300e07050b1442d109215548641440d0104008100309000501c0c003c040002d4103445180c2c402c00034040b450540d000c1000f005d10042c4a80c0420607046091800214240550194001881a603617104c03803030781c549801036984103c9150340c0340c902031004000a1340e5030300243c000c6590000254a03107034a180e0040b03869100315004907421151400c14081580e6200c0e00c00d07049540c000c000c0d1846110703030b80ca152140310940c641104903540013101d071030010319855000c1704c00f11300310310200c0720300f811042c4c0420ba400c1012507049016075500e490400400c8020f11040350107201d5840301 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 853547266 1250 853546016 853546019
    0x19120314121527011802130911070f0507030311010209030d0f03060905010e0709061826010e01090b070905061606060b070602041a1c0504080d0f0b040b0604 69
    0x3588510030008150002401c80e4248007407103038070740d01564060b4a14915481e901e886600081d5100c0007003c2c07050300e00c0ca14000c4c001c0030a0204500c02d80c0d130318080d2141d604247c3d9107403807898005080c4211503041816000c02c207110015101001203910b0522560242c120a8a90308002c1c1c03900c80d152840c980e142c0d00421846400b56400b245950030b01c170141c2400240000d04603421030090620350021120a460440040741007200740c9401c0f8807c15059840c503900740e80301c000889003001102c0310000706035500c0380240080440003981282820700e80380c038001c803120344c001ea260035100c0702c03045003407242d66840c525021700c0745070202d5960000d074a0070b0025000d451320011900c41d20a803400807400d081c1415581e002c0010541200004103016034105440e4000d608100000b54060b10402c000d0078507115107545e000b0085400d490311001184680c3d10361201c81ca0300d82c4060140100100d80c921400c0090150100f8507106d9074685a805d10030007d40e810b8004140003c40d02d42d40201442004180070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 853548516 1250 853547266 853547287
    0x1c08090c0603150904031b05150c0a020d0c06090803070e011206060c080306030328020601142805090109020d0b0d020607030f020a0506070807021605030d050919120314 74
    0x2e12900310f1816a11289aa0743d00d040449240920b0551044c110800b008640103100000038031141691241101c6401078a0b104800c14003449276162810140e00411f1205d402c1078051718080c16128011503000c00d07402e002b0394502089a000b02d440d803002c180205191159968800c243d1004500380240420520b81004070140040603013600090102c18000001407080d1014070a41c0c1d0b001c0e195981c04580b400f1481401c0640d214a0440040144150000011030020002c58118103420207488040384042007541b90f500d8100c4a80d030480e10080b109800206625150320482c0280500900181c13554545042070054031a40c05403540711346e01001c0719a0150b07541c1c030200c0704055810308154041b4030038100107906000ea04500900b040c003603070003040b41e688c0e0480d80f06841144a5400d81d804039450040e2042c101c08903018507034059101403a200c4280340260b0040040c00c000601c02410740b10110903d0340040c60b690400c5544200034032200e41015005001c80a1108503040300d54140034500d40e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 853549766 1250 853548516 853548541
    0xb01020a0c0b090a03050d031410050913210e03070518010b0702180406020322030e01050d06080102030109060914190203060105070206030412140906030c0306031c08090c0603 77
    0x1c20160302c10014980740c035a030301c4480d4000159409400e41d0120694954007a00501c0080302409101c4800320004090303407600c860340360030307954001e00c0d00c00140c4543c0e1040f0405c000d0b04c0012070354a600540100076089a01b0658043d444461351501826000d070824542014041c1d03219901890503c403043c031442d01c400406a056690501396a0345411650000604c50382401e400c1e000301910540910092003e0341e0001c610440060600c600103210400313044100c80e044940180000e0049088a100d9611034001046083d10813031f0b010a4898840741660b08a9100b0b81c032040040b6603400080000c002c03079020304840c845554108900070b207441d03028005500201900610361030360000c000f8081d03a000d541922242c40c2c014044a480317207481d2401d201c0450280481d4004a1105020310b51702c410340d102120b00080780605990300b903845111084281e0b03000a02003d81c140a95003d51031407120f164645000209aa581c81d01c0c1130070840b05481c20300794200462402424200100301142c002407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 853551016 1250 853549766 853549769
    0x8180307060207081f0605150a1b030e0d020406090c1e030212130813030f0209010806011202130e0a0c030605090c060403021e041b080105100c020d14150a0b01020a0c 73
    0x400d96030445402d94205e4000401c40b98218990103480c02d00040b0403603c214000e4082d150a5031100920340c41ca003001040702c0021004003d0018402010300c207020700340103400e82c002c0c520144c008604c507030302c0d01d4204055036400b50360203000805401103e8144424141d080e0320541c0c190804500e000800c605002901100400c1e07240031104000041d4108414281247c90343c0c207012484201c0151289002e0a2000c440c000507840b4140340000440c050394040f41890407502d0301040c1d512030080660a20035403516421019000683ea42c005000700c94007800b6640c01284164072500500b42186058021544040c002ccd02180d80480c912407015262141140c0c16a6012500034034145144200d850080209611283e0001d0038100082641242000c2e4041207448a441e140300076078030f49090103202e4079160041000241021512800f5080519800c2035450007152a1400e4414130882d8901d0030980707968a0200750050420413400803201d00c241d41446000344064920340c00035844415151109 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 853552266 1250 853551016 853551043
    0x11b030b10140c030f0f0d0b121e030c0d020102030f0703090515090129040f11030c0a0903051203010303110a0b07031d0709051e091005070c0818030706020708 70
    0x2603c80d407888070401c00e0310800521941c119a0302d410f864020000e5401c1000020119403c003101d4010b00d1826054900e510180740d002000d000c400080820391000260540802c00e002c00c0080c2c6240200030f200b40b20010006800251750780c10903140c445070340100100300004140c6070002240004001099140845082c1342400c1130396107030061450300400c040100314030000f80450018024a1801c04a910a601e04440810020a001c03964400392500e01180a2002078200001400c0032442c00140c48407440c1031a18000c07040e126902c03140391a00400c0b20450213030010004004041c1e106a04210b01071100000d401c614025030f41d242e02200c03016012000f41600d680e940030b45240b424290810403040e100c11640fa5590752080c50707004040a8800d104603035001071520308490590308219016400b40801400001d2240141c0b800a010240030305040010090021001c111000060822601d03000f20b1709084001e900e04151402c11103520038425500510804c200d07001e80403403120303a078800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 853553516 1250 853552266 853552307
    0x1080d020a0f0309050d05161703091309080a090807150f0e03190f0b131703061909020d0516020a0303090215281701060e010e03011b030b10 62
    0x220b10f0700303660440c0a9080950419a107240031002e000740020b2108160104d5110000486d0715003403545501100c0c08a410a150b000b0841c510150030450340c02c0a41e5035034003500085440f00c558a81e00c944d480510708000048401100f4802d080042c00700d01c00905920444080041425901504a0340303400c0044043c8080141c003011a6142030240141811742d9001c1900c1a070294607042400c480001003d644405550001803081c00702038020000550b0070071f610781c00300180c0d40344034100c0754001807070b80c2d401c4141045c0d4070290000154400000d04008180982c03540607813210302c8200c40000702080d0000f607481c50b00c5444e29802140b081c1e11141c25160125860440b40045030440c1003a03890751184800000d03c3e003030311b800c1c01c0c0d083c4040d8850780c048090101c010280115602c058070900354102039821801002131900600400304000c4c4181071440b45442d400d000207084400006c200c03200510440c4062114580c54810340c07005ca03100312615801040c803d0002004111500c012210494 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 853554766 1250 853553516 853553543
    0x1206180b0703151512051003021c0c150f0f030504020901090b0a120c170a02030d1d040908030712020304050a06091a0109061d090d05090112050a060e01080d020a 71
    0x6031042d05100a400c070300d004040c51540541d401000421040c8261080d0b1b40f82c40041903d54801c50361020840e40c00400150b5003c010f008006c0040b80c5107803084401c0f030076200340000c1c07003201c8401701070f0f9098181d1190b4030071984054002e0030903038803041d00b681014a080304100040e40d80107080c0b41503400258001400c40d02030000f080c000a4130703800009001050140c0e00e030400401d004072505a0388070005803031803004407090301580c07070b40101c100a626802c07141020389041d2190102106031501c0d4140c25100c0d42e42d0b240410125510084191400c2c40c000041218103500105841c0c04803090350000c52440c50291105038a0f207a0a0400030040c1e0b8640c46000180200e0007505422030091107800c01305565030b00d500c0002000380344581489100402040ba510300c0c0503110083c03285070301d0310241540c00a1058100d42981c40044880c0c144814410605500b024911815118a10500b00041c0d9a0305007071644a25031302c140c1c03008541e9400070204003003043c0d000ca81d2480740c50380030707803072000b4071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 853556016 1250 853554766 853554791
    0xe011e02010905010911030705031f02090d020d060e0601174306080604050609060f03071d011703130603020d1e1b09050102070e0c070c1206180b0703 66
    0x10910b01e440548550708040001043c02058141900315440440444500c5a036820a0584a441c41d00c140344145451020344099107185030020081000010001300745095079074001082c510101c10300f81ca00c5941c908a044040008100860141400200e175400324901c1c2818036680c0e41c6c3c1d0381a00d250800c48200f16101003900b158041308014038070b4418110401c0780703007142201d0101d02e104940000d080280440d0300c0d42070074811503000361406000b0080b260f139003100707119070f16082030f01c81605031048182c00103c2260042c02c032100fa1000814079041545031210a922900d0002e04010281d00100300040704400d185180e0302c101c40c501c1c107015844511125200c0000d04044010b0303001240d00403c1c140e05200558000341011031543c2c1c803980003907980c40c0f044034106e01c14003e060244e4030a14081c0100e107100c1e110345da445042c0304200d03813500c0b245031380e0302814004560100700b00721601022101009842e000b40c5590514148100003102015110748281600c0a001c210038143c3d14103111360f04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 853557266 1250 853556016 853556021
    0x3070606090608031c060905011e0b0a05040312120c0906180b03070f0203040819050105071814190305060702100e190f050a0803060103060b0313060b310501060e011e0201 75
    0x6121040c030410103527035a4075201d001044081d002c12b045030018034000c00c0c0c421484c0c05070380448009560b05c504242c215605c1e201e41e490304520300c0042c00641050204050314600800c01801403a6459076500d600c0d01c40090318500012240701180c3d0000b840c18007200c0362010580e5800039483c07400c40c0e0962024107045e030440c070664028400c01d001d5600c1c85d62559290025001900d88280001c22055661102c102d44400d41c001d480700501c000c1810030000309141000c11182c4510062110141c00200c0c0b0079140100d00c15802214142c10013000c04c0341054045c8501072a08214510611240012115040d151502100e000220400d2000c018091003406011019070716404012100020082c0c00c24075402d4004481316130009091000c0411203540c15000c5c0c9010342000c68000000c040241c0d9000d0261a2080c4169000f110a0800040e22104c1c440c141c1c401a5030203108050141401420f901a620160801003d004070448804520b0364407000946440d5104a00445c0002d00000100e02 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 853558516 1250 853557266 853557269
    0x1030207020d0c08030712230306040609150e010b0c07062006070215010504020405010918110310061d030d0f200c0a06030501050d1e06020c03070606090608031c06 72
    0x1424026000400c842030000014030f001406600380c1d0700c04400482d0200d0380e40541c084081d008c03440318000002c2035038564016540203600103001207040d40c1c44d5039071182100d0805030102e07508540d17498104503140d416918140509043e440d024508004c141c0301039543c41071071280c0c0d8100000700c09a2407140700f448400d085640e4000302550348038140f500000b0768400d83c145428140e20705501c000181c91038a8801c60b0200e0300103845601c0030502d490462140320a008a034030241035103800031242c440c8200d4000318450000c0d0945220550b09020300101400700c50815103032186a8050006899903000665416000c01d500e0405d19520900300110383c2000401ca8402d40051000103002c58084081044814007109460156a195552340c00300e0a81d03a081c8101034200121721551004602c8083c03070b407c052480d6410140031001682e50b48422a885103184e203240343c20100340c200070880c040c0140310080004031000d00046013084107150322849940076003500c44c0141840e103100e5403140d401c03050 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 853559766 1250 853558516 853558523
    0x1060b0a0302120603010b18100b0a0c021806030d0509060c150f0a050103020a03020d1401020d0e0606040507080609150a03060c120c0203220504050405060105121f111e09120a0206070201030207020d 87
    0x72f84503204004040c18600004004030b11030700391015095400007541c02c140d441076400900400558400d1001600c0680c030422085070000e00402c000340b89004100b04071341c0c40b00c45540240c0e41c0c500d0a00f40602e40f00c28040c2c103605c810740c02c04d80104090b0b07a032241c541c0c1c292074040b00d20344030142d540d14001c02c8176002c104601e4001d50020550b2034802c00e0681c015810b206000040c2c498959a600c200302c101c41d0200c400c0800f01c0ca103907001c01d955040014003140c0c0001c00850540029425000080c20850141d0040321030a440750f28035aa00c650001072400c03241ca0302c8009110b042e401d06006034490084205088242c210661044d102e09000c4800303c0050201134400c20060416060985c0c548109015160007030344180300c141c41d0840c0000d00d0002c200d443c0c0795003860703000e110341e1554060680120702d030441c903805100344681024840c080022816651240daa03484910340d00303003d0307203201d822854a09034100c040f404d000b40c0c45060881d000039509190042e52550240300090b000361400a02a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 853561016 1250 853559766 853559789
    0x510030b190311040e1501060c0c030b0a02190e0f040c0e0d080901390c0b030a090303061d0f04080408150f061c0f0501060b0a0302120603010b1810 65
    0x43c080e00004040165030150f40c02e00002c040584401d40d45e448200da11032030b41d040d04004000e00e5201c0c0c1340045e0781c6445110b20102c850f41c2c80d1109032542400342d954944403980020200d640317803103602c0803007060419428420120f000c140006020300040d0681103000b20303202d45c08440070a10800131342c80a103c1c01003455900d04c03540e05100c01c003a0840500203012810034542d040c1034645c0701224408860300351075809407892045046d0b44019409000807075070700d09404008100c1c00221006544112280d0400064055003420002d00f0307505540c1c046601401e281010f000c2e80e0750f10083c2e40b03501802030900f60800c0d48440c47d2070310301c901ca56407180009004104441840007940701c00f9600036401d00310859400e440f100d0810007514200e011031108032491000d0400092940c00307001180c03074010000050350958605801d451a0b002d10309042c00654009408100c42e0380f000c010300c0d0045401e038000c100800302c2d140841d00c03801207804180b8404205d6400140a082c9054860025011040c8c0341e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 853562266 1250 853561016 853561019
    0xf1203140d0603110910080303180a0c0e0f06060c07050405040c120b010f21020d020301271406151903150219141b01060305060709030b100510030b19 66
    0xc0c600d101381142c0e050707124005c0c900124494020a40c910b0082d68803d4001d11328549442d09481942c410740ca4002d240c90146d0503400000c91481c4681c40300614120130f021035a858400c00c3c416861100070f0001c6c0c4a00000e00c411948041d000641200713440c400c1c0c0380010aa00c5a00340265582d0155128940d24005460a1002c01c0100e44507141280d01e18090b60400d039440d00c4a54044035102c0780403031410b004c142c01030405803a152010404030b500140000808028000d000c1c40032582d01120180c18000c1c4040510402c000154280c0c41e0000d00005020319003044418540c400503030240b074611501d0421610340300c072801110f209000319444003030100171062484040000e50088240c1c1240c1049500c0d611107080d0140c1011544c410034500c0d15441c00440d011a008460030700f004100c4290b680e10404800118100110b6002e52840e0b1102c1d4800c61030351800e4440c50b00f0080094900c2c0500020401440d1580c0311f046401400ba07082c007081221001e0007040d41d84840c0c03a040171240852860 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 853563516 1250 853562266 853562273
    0x15051903060521030a12020d15080d020a020906010c1502120601090b03040b040201030f0b0a0801050402030c010f02060615090d03030b030f16090207050312041a010f1203140d0603 79
    0x4104101c0b941541c04182d40c0c40308030342c0b00c0c182c0d011032004440d00b60410800990a203100d20141c100c06140f140307005041c5030320940c0d0301c421620352003604105280440020311040e41e080044064050070b0f0302c02404494032603400310364010320162100781403200c4810700400300400c9100e0030142940e1120115107450180c0d0450361401020b44160b0301040180c1004101132002400701c82c8202e402c81c3d14855a912141d0044004040e003c0c2580b112569512868210743d0300d04155000404141c00045082d081900425040000d118000d506000100311001c810507004920345a00c4801224036001e0b0f0403201403111a14031440c0c24084e4802c0c000450b0008060b019030011412400a41c22907800100e203148580d519111000034030405a030b1400100700c00d0356a0b40050031003a10580031b1324204601c141c0030124008013a01d0417503c02c2c17000c1c038130301c40548507a001035401001e01000405919107010340300e101d60300300454054100300c10031904044480440e41200c19014909204004242e960306 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 853564766 1250 853563516 853563521
    0x5030c04021e12100609080c0f0103060f0b0306040e0706020a03110106030b07050319050907120203120325080c0304060b030c0303040b131509170a020a0315050a0504030915051903 79
    0x4860304135082e0495004110700d4401c0701c0785410744022000400e00c49950f60200700072000c00e00301e03040c1016218000820782c20700c070721040d00050209e0308480f520380c203040007040243d6000741d092480d40da2221104000165000031030034003d5401d800c003d48005020800381c1e003d01041e80001d00400d04080130f00041e6a40600114414000403c04c0e03035072214040030b001e06880b400d071941d5410390701000040c4602d00d9060384600b0a988024101c0c0c000301090f4001c4003054004a0745072411106140e407001c2075100c0c0c0c11044c3c2d44003609150012061810203018000740c0000b410150209075108000c0d034080d20f0411070000070710002000c594a5a07540c0c1e999240da54013801c008600b002d00f04000150024000c40c580082510381c0e10380e80807160070885131410b030741440c610ba0003042c03144114400141c2c45040c1054042c40c010320302e142080026034402c00c2070b2180503188804603407800c410040400c0d4070034025010b6031340444481c1380c5186407210032602800f03046031940d40100a07086249049400d503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 853566016 1250 853564766 853564771
    0x807080a11070510050a021c020106031e1a0a020903011a040b1c02191a04050a061803020613030203010e10051602150c0d09030e01030f0605030c04021e12 68
    0x256540d0480755030030001d03540c0b601001d100351600b16500000f1500d03180d00030005440c00300d00c10310440b101c5500d10350314050303840000c1407801d0150350345e00400d02c24420042480d54012043d103040b86040f070000d07564904548031103110300c1100e00c40d50001c2074100303260b601107426840340240244140004c100351403000341030b1562203038400c40ca051044001403d02d5031510034800080c01c540c141c5410142c0a0040c025455008540c1100c071240010840003041c1c0c01c80e200e50b41642c0b80c580c0c1c5035418841886803a900a400020621003400410340340c090580380644c050341da05032061074482c0808203511002c0310603900000d5055080c04482c10b10312500258640744090402d0090200da02c0303011204110546191400300141c001026415080301c2003803126800c01082200240307000d0640c035a43d8210b030550170086001854039040c041441d0b9260003210981c0108001c100281448e02e4006a5200440b548142c0110740118215011007544130134120002c1e00580001d5a5000f4124080c0c481c0c4000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 853567266 1250 853566016 853566037
    0x6072c03100510090903050708070c0e2503050105060a030e071a0c010b0105040806154005190e0a0c0b03010602060106050a1d0a0321030f0b030703031209080708 71
    0x21500000384c420454021071402d60780545030113240c814a9144d1500543c480d02e400c0d83d90020390039002030104140304406200c3d014010b2030891004600b174003c00560300c402e041104050a0034014880c9944540807500d80c8540707801c0000d84000c404450b41d04100322980080d0003102032407010300b2420260001409068148002004000700721401036401d8080e50064400560000000a98141c20030346d444a102d02c0081081103101c05c01d01048400007400e07540c800300552031074100619103000c00826840c1c22410306c4240000e103000c00300081d0b42c2000c420b40307060690322550303030411041c014402d4440b025041000c40003020344a0b1490049a4030070b00c64000144a000000500648210700703480249c40c0c2e55540700c41d41c020001340c0c0c1e1200c4941500031948141170348000000581c0740c400940551a0380398075007890060070080601140c45c42c040b0800322900b450440c480947d0085a20740030340350315003800080c1030000e80c0201c0080151200090a4a40004400d414400b030704015254020f070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 853568516 1250 853567266 853567291
    0xf1008100f0f02030c0f1602030d0f081008060c0d020d05012907080301051e030114070e0109080a061508030a03021306030e06040308070e03060412020c0306072c031005 74
    0x102e42050703812031004440500710b5550a1000c0c121440c0c03c10010000d1040081304240c248079581c0000742841148071a00c13000c08c0e1080351661a240c1c001000c1684035070b610fa03410314907610f80070307105440302c030020070a0034070000008d0b0b1300c4100b25103a41940c2080d8140d1008218643e1614060f00070030b41d084180400307608949000c0c0241c00442800c4421003030b4080307001130941c1d20340810312000100c0c501429901e0b940324804600c1c5030301d0900c54000d908401c600c2c11034503801c0c0008003030b00081504201e18100b050f240c0080c40354007400903c404000d9805400000c000c07100c062075018628032508034030542c1c0000141c02c109150b168019001c40c1d400d400745203612035555941601200c10500d10100a5001400040d011074000e81d200340d400150342c1020000b2407800d0000905000c411141101d0303507114814240001a8100300c01d0108020a60043c4018181b420700601841105105280c082c41c0e000c00c3c441c59140002d1300b005007000040c00f03c5200c45100301c003d0b03000c6c00e8120349064aa55 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 853569766 1250 853568516 853568531
    0x9090e150c2802060903030c0a4a030d140c15100608060405010311090709120b0901060902030603070330030c270b0d06050604061d0303120f1008100f 66
    0xaa006c01100c0c010072900300d01d03901e8064031001c01d4131607645101c1d58440d204200c642d40a034a10b456070700c98901603000c20308280c94140c0c001103c440311304c1040b041c078002d50010141c1000680c01c803092a19541105089546460003d04003900d040c802e402004030080004062100e04580c0058171801e076080354465030000d544410034401210030034030002c0c250408206010741c203810400710643c1c001810307140846403d500c441e01c0c104080b01d20740080307448038a2401044407075202031003650b015144a12065285091000000c1d58415080c0006070040290f1203c2c00e4102180480542d441d1880d10062716030260040d03c09002440804004070110706a510802c0201c80c1c840490618108a00b980410340350402c8820440da030040050200f8090362030b40b0200b842c1c0c2e0340c1009400281101d5841528020300100703030302c20088d54030383d80c28082c0d4000d0100c4a00c64100010031540010003500c401ca943c1d0324421030102160103580030b16528042e4803030294114409822200000782c600a00b1b003c1c20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 853571016 1250 853569766 853569781
    0x40602040515130e0f040b180f0d020c030109022b0b130201032d0209060c010212011a0309100b03032205010e03030f0405010305130606060207050109090e150c280206 73
    0x240c11600e40911005c604005800a030506000d5500000109040300f010044284d42914007228590340c110158048500002480e070f042008003070716182a0000e1024404a60116402040580f41c5c0c80170b403180000b1140704101c00141400c00d80d504a110b899942c28150280b8419419800040e40085e0400240c2c2d009081120f001c4070006084c0100f4001030102d002c003d00c000d4100302c030765540c0b06900b084500300d00c400034005054400400d0083c40303095490102340d404900c028880700400e60100340100142d604021964041d41200c0c040045088a40e000005e4114030a90003603c616034940703208410113901e07000c0c0240550380203032221559046103100301640c03400b841c24801e9103968100401d21044d4801c1d00302079004070010100300700d0031440e542c1d40310640d078054004c0030043c0d0001808000700d41e0301c03410107002005014401c1011091706034071140c039080380781880d0213900c0425000c140b8070b0740c24a04035480d840d41041460360505007101c10020791807500702802d00605c10400801c400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 853572266 1250 853571016 853571039
    0xa110a1110080f04060f150b040602070501110309060307200d0305010918020f0d020a1401080105010309031b081909080c060307080103030c291803090a060804060204051513 76
    0x1c1d51443c80c1c1d0351400e03529507540f031001c1d2100307107004419180c545908800303892807012100c1c094401c1c2400d058450f0300300034000b0710340032065211504102940d05083d100c4a8080110361380464141c03034259a0395603025094032000f06a040000e890303109100240407140c8003113005003620b42203590901099034ac80e9003040943d6091007455940d00d01c800411001844d0103060405039010140020b100041c2e590001042c0107080d5024508002001c1440740403507a100108501400c02424100401c0c91141c40c01017841303903c1e410514034011200000414400307803206594013400c0c80780031800c40441404004180764190b2180002030322a40019001a20704401174920481c180d0f500c41e102686541c40c111004800000181e808170034014040520040d0201c007c81445a80d0422140764102540503502c0700e88a095441000d800900ca81c2025668040300e0700102e80041c60194402c1c1c40d00d051440c020b21882d4042c6a011180d414060001071540b800790400c94480308503040210344d41c0060070340 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 853573516 1250 853572266 853572271
    0x824010b09121009201807050904060f09090c05150f0d02130e0402090f0c0d0e010b0a030506010f0e070203071202010b030f100c0e0a03080a110a111008 67
    0x11503000510403010386041c40e120401441042c00119a00e40c0c20300c410311002c0340c051900c1070b01c1c103500075920b5001d80c40000d04062540941913410310911680c840c150080528050b003140f0401c00001002010b079074840c0c1040c00a485542c0044800940e1240c01000524025004a60417003030300000180d0f91a10b42c8500824101c0d001101d071a08010f0710f0440d0f9154400303407602c24001d6003803120410007081c1d07078940000780407441c190a0391820103004020740e2500040418905084480c10030624090400950750800d00003480840e0011b1034a40701d5014007800004103400c075070305500001c1031180004031507040300c55035146102c007a81c64031110300d0a00c40440c0c0607000750744200a1200041d480e403c2c09800c00e903080c030000030444919000241000000641c00d0100d034407228010045200501c0748680301040c41c14007001101051010a042d01c880e0f00c00a001008017040c0c0000076402001039036401c00f82e10045e6550b030105480c0c044110b210401100d40a242c0510440807100c1c040d1721042e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 853574766 1250 853573516 853573529
    0x307050310020a020a0b0a0b0103060e060a14031e0c0f01110604021306091503030f020d021c05190906181809050313060e030606041e02070501060f082401 68
    0xc0044042042006503000d0f40f00c0340b04511a4841c0407000c10320701c2e4101d500880f5074103404180310909000041c192512504448482c001032001e10410341e65006010003110000400da04031007000000017400c20600d130010062564200001c107906020100d40c0900d40b040072142c500281d5591001120681c40305440451071354009408540035241144400000703001c6c2c06008103642d41c669580c003080d01d08407000c0d10703150a202a814010950401841051403011744000d0455070a207101c02550b803050324001c407041d003e069200e5100c0307500c41d004580c180d4450440658209400c948001c1003040d0500c5081c002440100c240b00f40380320b4842126088605900044144400039500d94004200184c0200e50300c0c4010481e40c000d00d0f542840c08001440d041d11100101a241d030141400c0240040c94144114600781010300c02019008007aa01019198001600c80c2c807246022401440039801c0403600c01c08052000420000004a03411041e4580c00d03103142603000040c41000074603081c02201c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 853576016 1250 853574766 853574773
    0x2104080c12090909072d030611120106031a0d1a010609080c0307180e0c121005150619111b040c030506010f0507030903080a0c05061e16020109021f0e03070503 70
    0xd01060018812190f1106daa1408191015600d584040c00c031103116103a103001e240d000c158100041c8202a0f250700400a90409100c4074152244145030000c0c59594281302e820f10458039418058010010600340c00ca050400d6050f50b110580508000b084c7d00c283d12452040c142d40720014100491403000b126400216241003118181c401400b604c90f09800080701e01c00c200c0e00141c5a61042038a41d0403210341d03800b030500d500c0a94407070000c3e154001c0c003000c24079901041c210000e4440d0401c0300d1250704407000d01248001d80e0f142c1103035482011401e05050707204130f03011642120349c090b44009501c0700484003006003071840d0406400b500d80446889000c1208821650300d60390080740104507040c8280740c0b00c024140c903540c0c0c4d80d519401600b5000d00040380401c805c000c1040400103141c0100303580c5c0401201c0807100b0f1900803a244020702c00c0c90022040f242c0c03000c1181c006d40001d600c841c1c0c014000c1d40d107000c90302c00c1c14030300142c008840c00004412380000075450901003006000d031640903000d03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 853577266 1250 853576016 853576049
    0x60a090c090e0603030c120903010c110c010e0d0f051513020f1201230411030a0b15130507110d09060801030f140d050414062104080c1209090907 64
    0x80b1582d8040041030640c16000070080c805040800744101580355555214442d02e4400c00b400345421603007480210030030b114925103600b000c29030001e00c0da215008246041031080700c0e103101203181400d40703490003054980c000c10803604008012030348000d0088100d00d0701c070040d036a000164800070041e03007000e500002c0e0524550000c4c240900c202d4407e420b40390012a02000c2c48950310613689070611000e04030301c9120180020061500411b4010207021002019086425100d662103410080c004034201170402001c04445c0d00c401c41d81d282103000c1102c00300250320b045680601129118050000305020388801445601c0c0241c0304101030780c084c1c0d40c0c1c02a540c0c1c2117a456a020100803082954105a820042210308908001d10784000105503034491310385140550034078882000c0c80c281d500c03451080c00402640341401c2a402c1d11315503003101c100d07950b4030749003001c14543c0b141401c04070309400351502c107800c000540c4c0005c10100700b05444c1035203940e407191000c0d900c6028a02420342140d42202c0c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 853578516 1250 853577266 853577279
    0xc030612030806060c0d0c051603051509120a05070b01080d05040303110f060103030f080c0f030c07030306230a0806090307021009050306131202071811071505060a090c09 75
    0x8065000e00c0c050310451425517030402c058134040700e922110000904c080e60000401c0b0040c003000420b07884002c21201c481e41180e030741c40c0d102c040a06440309981074420001e000340200700721041500740d0450b0361541d00ca61707017140140241d000305000e460354038050340006440400000c40502c0024076580f41804c1c5811690110349240f00600800345a200384030b101410142e060000c24002c0d44240c0f00c1036103801c0800c0016040080050a0705214101803040c049031200340e4040b0380e0301c21a152650ba550700302605d0260b00810321600850309903804c0c0f500c007210080034154403405118040f1051200c00355125070082d91110120751007412a0000d200c02c40041c10710106000504515040022031607840740c000c80d140c40001c8686484440344043c051081c0a00201c007201046036520181c00c816080c00c3e000042d540e051604e10f4492a07464070840700d0485000d00b918981e50388591016800541016003001030041950513a11450400e8030000d0b07201d0161140240c0700e105615070b250352500d810b4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 853579766 1250 853578516 853578527
    0xf1b02060c1b010203270d090b03130606150909090240050604060603050907061409061303030323060904020604080105190b0d2d021c060c03061203 65
    0x1000850560824010301d1000d0b00a0000c0d500c2a140b401c0e0003460b600b2140c0941d0802d02c18089840071310f03040b10581641d181e41c405c4a800c20358007880940d91762a00c07090201c100444d01d101c0701400301c0d450508085100b1001c0074800300d500140b59600a112600d07401c840040350000707400290720904c200c0d8030f10400b0031160a05000c0d0081814480d80500640c0d030084220000c880030049210740c3d401c1008075918152148a024000302c0c40c04100f02e28005c0c1701d00c0c1d41c071825801028180007501501115180e900c000701d411091001d04916201d0482e50084080e420260100706c0210341002400c030300401a450941441c0c0548656140c3d036501c4581c28400d440d1000b034070585c2c105100b000042050034003405428003070f402e06d0083d001000220020720048620702402c0c00e1184249000c07440220b28105245854051000e445041d0240390b40315120b142180750354001c1d00007481d507180139405c446100ea01c4010070b0240b001417002d0140c6120071801c4840a0080c40d440840d40c1610f00f01086c41407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 853581016 1250 853579766 853579777
    0xe070f0e1513090b1c0803060d060213080703292d0c091320160209040311010c0903020114090d0615030201021507052d0d0f1b02060c 59
    0x440d0002e01e07020406000b015968255000102c2c0d860b1629260720040c20305801103e800494001e1810b0499625070b01c1e489503104c050004e80c4105540e0300f601051203041d80c120b4850010f80110070441795910b81403103850300c05900c003e4a4400c055014411403032040c9611904000001301d071030030341d503586000c8a811180d20008200710b26294036540b040881d9100c0d030300b60003a03241103070050312004884100a203ca0411041a00050070101090342c10b414400c14101414207661090303032948080c0b0b4119416840b50035010f98001081801d1006064101e41d280340c507401202d00134082d0400481c011313034079442d5a20000b400900c086105072500e40c03a03030010b0030200400901820380d070f00e41d0751200000d032520300e0351703516006204080400856804000c98801d1100b0210308407140c1c5081c0401402d10f000b103019101c02c100b030503145805541c41d00d0280d01422205c1c0400305403208c41809505008003180b5901400c11840d00404044620b1b407181c40310301c409207070350040c58243e0751044072032000c0c0c10a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 853582266 1250 853581016 853581049
    0x803040303051b191b020a06050c0a0b18100b0a060e060c060c030f012102151b030901180b0d050702030c0d0f0306050919020d09021e040b0603091b0111010c090e070f0e 74
    0xb495160bc00148040c4041030154120700703040d005407c3c0340341900703050140c100c0d00d1505003403030070000f1005078581240e1107084a005090011329502c0c043c020034214840d00410036958000c0108200150302d54501071402640703041008005a030700d80c0c0869040d1100b501c0351a03080c1d80205507500051420144030207089043e00100f908145e1480b032100401d9925a039903241d10303040410301d080203503404440c1c414100b05c100c1b1110012817400000000c4e070b12403100300c04921500d503800245824000c0089805442c10720341100c50760344000d9002840d01c10098480400070b41880341c00905850310301d9a19000308242900c190000c419805090000d51007145083e0040c0c1c0c9400003000513071341e00355248407401c000403202000280e00300d0070403044840d03030080d6230300c40c000c18401e02103d00d8000850118aa0025042540010710100141d40c503882c0381900145035820416000c1486074894440001c0f80c04440b415001d58807030f10029582e1054920a2030000388000111401902c3c1404141550400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 853583516 1250 853582266 853582273
    0x1a1806040504051003021516080a140304060f050a020705030a0c02010915021c140414040617010b010e030c012c151b0a0803040303051b191b020a06050c 67
    0x180d070310116041c0c1d8400c980e0345098402a103010015814541410001082001404ea1824428818405c16000480f40203070120b94080365800e00e860080c0800051049001c26480d1130f031403e460f00c4030107481c072401104041410310000c104095014000d4680959000015500341603003544100c2e24030180740010303410040ca1f40d0001802200c00f445030381512060341d000d0100c01c0e200155401c0c04000010501e801c0081c4100c41c812041d155000b80c1e010b80e01c01c50020100d0130b100c20300103005803029400030302030000c49690000f880c1405500081600d4800e032240c8007841e109030304040c1c40e00d11042c0d907140440c07240101d803401c80d41825203543c18074003481c0b2244a0080c500300407481c00c840740c003054a5100000143d40350111200003040600f40744050050001e410320743d5803009940005000181490b07222400b28401051a8901c07050b006070f1845120b49580c540b400160320700606603283340c00b0404188041418080e014406410160058540014a40f800e00100c909602070408172a8602 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 853584766 1250 853583516 853583519
    0x6090c0906060201020a020606030f06010e2a0405010e0a0f0b090a18060305071e0b03061309030206011e033906081512150a020c03160b011a180604 65
    0x2018030503900600b00a500041e154008008060302d440380150065110b5070110f855074204a48c0014203e0540d0403400a42e8890b0f140c80310303a062004400407200012400701d000400149400700003038811503400340c0e6691760400a0400b0700140c42440d009000c601038280314180940f230131000083c14000c034042c01010b54150380740d1032503403020302c107102c400709041c1c8130744040050213800c000d00b20144c122820301340b44559081c50224411040c5201c1c0e0300d6005c40200016804c3d83c0d450003591a800c0400c80d0134003c45a0502c0e00a481d01800d006a90410300345181a1a0480f03240d08030006490303016051140440201c1140c40c4101d180c000c10081c1d404079040003c45040c101c80b24100100102d0b200c00986e4100340500d07202c3d40c4d1001c00040d0094901014118640200282c1c0c0c2403e0031410410441e95165095480064441c8003c0341c60a0300c030006507c26440005c5901d03d0b8040d000340040f03581c90362201160020020602c403282074142c800d10660038035412901160000d500d00411051030203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 853586016 1250 853584766 853584779
    0x130b0c03151c0602040b18030f030702210d020105011a0c0703112202040302041d03090d020a050d0309050a050a0f03110402130608060405060906011d03101b020c0609060706090c 78
    0x1c5c2c0c000e8000410020010491182d0035941962014645030b088020f0400c505210100d01c1d0f40340560b2602a10910305503d58004002001000340c1c0100e0054080c0c85903403d803400040c0c040c09081c0320712000101c003000e410351002c14500641d18034103c00c402400084c0d1568850200c607064090400340d00a42100c1d501d29507140381c021581e030704082980c000d0780304e51460041000316580481e07280103450004050b800c0a45c0b021003118201e0408841d2070f104011035002041c0d4029483d040241c021810b24512024541c024210f003044540469105191607158001d02ca2041c0302071041c2452200b40306400c0c0b00043c07480748001d220b2032010f000142415000344049820002603441300c1c0108565006000c440c1c00c160044070f40c44603050b100c80d4240e0610a000900640800000095100c5071280e1880305036414085000c2500c0550014800048200000d0305200764040511016204040858a65051503010f8410b0450028020b42c2031282c42d44a400103420781311000c61b00c8207480400403810307 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 853587266 1250 853586016 853586021
    0xc0a1427010f0311040504081603090e07121a06030c030712060e0a0c09030c05010f020a0204050106030507090909081e0c07033f031d06130b0c03151c06 67
    0x2c1c004401410031451940c1002c142c002c911101d103d00032401c00c801c01c8080344054085802001e072100881c01c140d85d4604081b0b548052503006400c40100540c140070519074007449042000c1100030b401c00000520b040001e03c401c030309a0201e5000a42800000c00c1008400c000e10342c04140c9081408003900180702c1312048544c00d03008101300300548405d03c141c0041c14030490075a60194188840c02c5411610f5100a100842c41000c0c1005200e10310b00c41128400c2c071406203403a60261081c81103584440c0043c000d010b048443e0000030304100781c0069106041d01901c20380c1f40c0c000c0d005c1481d000243c0156180c00005c090380c0c2e90100d100f0400c48411a504100700c40c02140200f400111541040e804400ca050103002c456454201e41c91030b0700d4200715901d114030348095450500103051b0780400110501c04181c204200a039028100810503c0c1800004c290b5184c0d214a9800503103a468400041e054001603d5181c80d2002c501c244c4622418100081d04400c810b40c0f03c0036001e1119992403205 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 853588516 1250 853587266 853587269
    0x21130e0c0406030608010209130507020c12070812120a0902010c0515012d0e0709030203030d02030601031d1b0a0f0b04090b0105070302030a030b0a0e040b04050c0a142701 75
    0x60020000074204680d03980740c46040040c1010030001d5140892090002e6401410400d82002c09a035540200d90345138020400640d000da4003410b544020500c00024039104c01480c881c03483c1d6805008162059648200200c4030112403220024015031507514030b25000340010754040741803041221180c00450b104000d504040c1c08914402401e070340c144441d814074014200040c028a0310f134500076400320f01081420340c1c02d84900d41c403101660b9440b41003c03140003206034006500741c0400a100042449079800661052501703890038400e4142000022410161500702079506404c180250300d807046001e00d01800e8a0f1006010040c00e540ba8044030003030800303540c8403d10003400058100844c0f021401040c0a100003401c1c0300f400c2071042d4070041d46034070581412908041c0d85220344c43c055a106482e22005d440400017035907452030301d80b40070303552003501745e40907105c1e84508031060f04c0c1c03898200f14100c10b44040344003400e0b0500300341c0d080c041d094a04505c54000e5010040340f00104000e07244400c2d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 853589766 1250 853588516 853588531
    0x7050403140c0a05010219140304050406080a1b0308030412020c190e09060c03070c0c12060f05090106081c0243060203030705091c1b050321130e 64
    0x402c00d903460301008011400d41c0c1c004c5065400882d9a90400400c145803848a59000131030079520940d00e0030303140c1c29403090390000c5500900d094004940300d103001840e5140c0a110700182022083d111607071000c82c130407510005202c68801c00c00240002d03590b500715056004d0030700441302084414400130f0041c507400004501446003408007009400210003440717400807000800351010b0f0600380162912480000c058a003444500012001088000e010440051052042c2a4050031709458402c0c054954075550079191750078040843c08801041c03040204461440004004c20b000003000c84011048400461082d030242d01403030383c006e903a00d200504200703211511031141480035651254035081c2c030400301403440d0b51510003840b400c1d07000000c80e07800c003115092083c0c8075480034002440080750901030030b02c402009240c070003c005103d02003101c1d040c040d09100c0180f9445809041c0d40c0ca0448400423282c1d1401c80d000038050000c5001404103282c000c4c001200d003a16804100b0100754141e6400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 853591016 1250 853589766 853589773
    0x100c06020d0f02191d100c0804030812180c01080a0204050d0b042108041b17280507030803130804230907022d1605040e240705040314 59
    0x810169149854080d910005420018042803017118441c40e84501d0a0040f8010b112064241090501403449000e0060b070141007187d640d42c5924114800340c0001c105180c1c0510840702192030300990a8091061403034170f44c02440d1908800004581007140a0a03100d4895400c1201144545030501144280b5019400e14a524101449d205403000486030090404010808504ca6072716030041c800c42e00907422003040700300090100b212802c018903992000142101c20803c9002c10540444c1c00c1100e4407c06c844003001c0c403218407005d01c23440160f8400030072642010805200103003d04015642021002000c513540c00c9807075a81c90310992060f001100f02c201101c8030070001d4049441001c812003419119014142018040a5518075600501e04006a4100c600d107078070504a82c02c80301c0000b01442100c0c40320400c4c902c10341c0c49400d03500070113020310b06084240e080144001108000100d40c2c043d5805420852910b801600130301805c4502000410400000800c00e8648000d0000c048803018 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 853592266 1250 853591016 853591027
    0x30305100603050405030d0209130c0f020c010201111c020903010603030203180a150e0f0a0b04050a090b06041a04030f1104050f09060a02090f030a030c030f020a02100c06020d0f02 79
    0x1031190085507500c20002c250401041200240020060380c0c84035044880140c1c9805050300040c1c070240c20040001310407403605031a00031319903210880362140b580b19000e95440d10000001203083e1000b5001e1035441600070000798203070000300380a0180a0111130350042c24810320b400028251240c941c42070740181c1c40480c0014450820301413405566a0844542080c14030300941018442640031441d0f003031004c2c121915259896590085d81604801080707416855214400046250014000d80340038031400c01c800710b041c0225100700c0740e4525000300064100b81c586044c0542101c1184048514408240070000003c1d00700c1c41941c004612070600c1c2c03008100780750280811510001c0a03e40d44d1150701080c84075266001c640b550308100f0314040560b644410102207603103400300d031540e65054410440d14500f80350b030003035884c2403180c0f02c1c1d5100440454090b02c1243e03036400000000e54020b61025100e100a4004d0300c0a0920740c0c42040b026060140701541d01e012074102c05000b180b5250001071303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 853593516 1250 853592266 853592281
    0xc030a1206050f01050a05070f21090305060c031e090105060f0d021003240905040b160e0904060609050703150f030809040b010903171801091518080a030305 69
    0x900390008a06508218aa01d0200014100030140c00a541400030019840810501c1541102c004c103401017080da070070301840e02d080c2061050790005031395005003c0c04040050b920800e2140102da402c00001c0040391982c400d0803402e0b9001800c0c0448491420303c01d5006103445c1b07601548a091000000a00340c5002814080684082c07507085100d96a14058240140d80700c0c00c283c00c0f800300d24600001c1d0403400ba18000001101e084101d0b09055151800064880140d0450391140384107034070309603a5446052440d1500c00d405000c401c0401e05403041560941460900d89a00034014400403401c9070391941c40c08100ca0054528138006512072002010f0441c1c50110f280051032500800700085282d9110081540a58a0154800c588034544450356a00c584420300c0a96008200c117580b00b10800071001d000e5200d043c3d00620001248030740f02030b56004071600700c11680801440d52030100405411690035404880384040071070382400114080d4010065030400360320a884c000766901f488036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 853594766 1250 853593516 853593527
    0x40b0912240a0c020607111006080a06110909070318060606050a020d110c15090901062a080306040b22150803030c0f130e0a020909060405040803011512020c030a 71
    0x2064409100d041400b00600f5542c0081d069a10407501e2800700040000800f42c5800c2c01500b84003501c205040c500b0102e001000820703c501c180c3d106000c10401103015420b2202503005191304a41d111000c4000903003024025004031480050703400142c80314000380d650b400103c03400c80e001107000940200382201e6158040206035980e450b142007140f4202c203c482c4d07560365600740c3c9001070302480d9036880904024582400355148401c004003003c0303042d078642c44000c0c444e91008240820306406511005ca05180c0c0344640e480031500502658070755605c800502c00640304090a1941100450503008036010340a460100f00c00b407003500100d94045078110011404943e0741104035107030010401d2040c42c000c47c004840027001000344890f00d03402c9810007211f036000c0f19448800c1041108041240700001d07a80103001c1038a0440d040500c0d5200d160512045503804c403401000d00f42d01700014040c0d1256130280c2207086101b40b1f00f510200307500710025801d13600010395030105540041003141b00301c0c0d0003a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 853596016 1250 853594766 853594771
    0x80c010f110d0905040c0e0915031e010b030d030b090601050c190b0a0e0c0607141e0a062f0c1e0102030109050610080708060103090f0c030c0614040b091224 69
    0x7c0c0b80c85655690880e00103402c039400900403031400b43d002109491552414401c45608080610791041f03c841c42c0340c011400b03840032014244c8640550142d0b60100342c001e10440c07208202c05840c1000580c1c0703040054610b80d000c201c010429100b03080000d0302d408d49403140c07400220710504d460003180c240200e1741c0f07050b40c1161940d00d58a4200900094268032034406441a1541081d400041c06400661007820500100e1000b60107001d601c500c1440d006001a514a03201d1107681d040102542099500502d0191610b1114000400d8980c624071a600c40d4040d141142141e001c0d2510052101110700314901481c0c4203003003903500400100600c0e0981c0c03280541c0010144e40003204410301100052080900400f00005c0c03282c59000704007e41d11a40c0200a400ea10840041425207a4100341003801c00c42e100c1242c52040c04030001c00c2c4948a5804250346d00741c04040b8904284c1400e84032404d0703030801300f03860b42c0010316150a407402807420800c010046640810340383e9444500420b101113007600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 853597122 1106 853596016 853596041
    0x6050a081f0209100f0302090301090b010305011401080a0305070f1a0f10060c060e03090402040b0403150203100302270c09011206080c010f110d090504 67
    0x191440012140300d000300340140c48010780005070710607a82e43c41d8104001e03130740724403c05000302c1c551200502d480c1005030a0014000101c0c3c2100e0010742e0a807581241c2c58010814040203214400740c1001c4480c03411003541c10640083c0d920070011000904111000842d4028888102c02c40a00341e03501c44130843c051005400d42000e03208041d01c040000950b00c070089100070300714042c84c1c012650641c60b80e1003c1c02894480300000d10078803d60900d0b50000b0040e100c0c444d0750328402400688508207602c1d8943d4198200390451141c985a0101d141c0c1c410010300a101c0d07200c110031401c80b54100ca01c450034039100d600c02c2c4602180040319001d0340c45650203003c01c194000014100881c800e1b80d505052004400c07001040e075401e8803420290b5000702e1a4024154404c441c0801625444e0401407010300a00c2d880c58038044c16100b802c0d0010700e04030030a0046140600030781c18420030 = true := by decide +kernel

theorem cover : BRFrame.Cov 853417266 853597122 := by
  have h0 := BRFrame.cov_init 853417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 853417266 ≤ n) (h2 : n < 853597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
