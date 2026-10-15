-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5067
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:38:13.111665+00:00
-- url     : https://prove2.me/submissions/bf7d595c-2ac7-4ae2-ba84-c9dfc98ee9d6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 911151079 ≤ n < 911330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 911152329 1250 911151079 911151089
    0x10302091f0806010b07141203010308072a030510150920160314070807081b122a06070305060d05030a08010f0602160b031008030d05040c0e10 63
    0x18440c0001d884070500c404880c25400718045000314000042d5441c90b00c0090601580039043c110035820090000944403840034215403203040c014401400443e1444000d80f0242c0d11410303d41c0c06043e00b00070b1040141030300041800103025207480510400c0741c240101018800c24440610445603000044540801e842c0a115202030342e41001000305107112071902d102c1040e07001101c0d5903040c0c802070b07032042c91443e41096011030183d04072051488428021030700225004850030341801d42d1a034410000354802042c909030f4600400c4100b064a50034030101b07940c0441003c0c500c0d996401c41c141046042d400ca035000005103860040c428100d1404507000c0d520501528001a0f00e5a504000070005400d040b4003806902c0003050300c40286801000c100d061f2001806504052980d0b55030403030350b80c010a1614815080503240400c121a03052000d9500102e06070604280c46440703100081c55900180c07a070301d0301c1c141c9a80600c01070000e21640301028000705400c144107840c084000e44603112683c894 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 911153579 1250 911152329 911152351
    0x90608030a0c02040c05041806080d0207080c0628080f010614090f030a0f1a0a1a010e1309030518030c2206050603010303021b01020303060120120a020303010f06020601030209 77
    0xc05d02d0f031317922130022a4080d095040003206401c140821900040c50b09003e48081e0741b05200002c0000b900000310602120500c0c002803200c0311040301408180d40106e1010040c00c011090201c0f001404901c0c881400c60895403800c616184c0b500400040c440103074801ca0034402d00c9201c2440b01c1c01c4100840302e44c0c200580e481c03003810003014003083c03410050100140ca135068041003c410000034402c00c401c40446805402982e07118a800340007207c0300011034801e4003070314103544105540a5007485080c03503c000c103000340f0956004542c000380e411021048002440000d081240e480d40601c40007220801540100314401c490804a01120100504010307c6c140d40e01c04c80c40321040c1900290040d103006002c3c1078480d40e4a20700650740390203444a03a040581100b1544080e94800019244210303016500c41d0718520001503005010b180341f8401009d1801002164418110b210005101c41d0744951700841c0d40c1e61503ca41c41c0a080c103150440c2d811500040010009a40d4040c011500210700c090 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 911154829 1250 911153579 911153591
    0x70e0f011202070c08030301030c0905010801050105181b0c0307020114070210110102070c0e240603070e01050f0a08180601080303150d060f1a060306090f0613060b04090608030a0c0204 81
    0x140311134150010790015195100000011080040b100e210404503101c2e05801d000d503980312444c05080c0c0b0700034081c00350091030b0400254480d400a801c069001407410102065803440d00d407109041d94054159001c6552000886000310350340324840d0515502c034400040d0810030f013540041c803c03101607216a82000590f20031010302071000e504880e1565403140148dd4010307690000882ca03e00126a0310420101c403068100880b51004819503000400030308c1503181d540c40c55002c2d501c6c3d003191001c05040003002e004281480880c18014429003032240c440d860149885090151006424228110b007600407000401040c4000000d503600186440f6225111440b51008609001590000500740b030703041070a0801c0c09040c5a00c60405065112a8401c18481070302c148125440300341c074400c1d00454203070b000400c0c008620030324581051004003041801d14011a400080c0c900c9904025941c400c0000e0070485d410442c4182c200918001c0090360400c4c581140c0a0101c040b2140e019005640300d81e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 911156079 1250 911154829 911154833
    0x3161a0c07120b100b071101350103020a12080d0c11010f05070305070f170402010504050603040b06040b04091e02010216060908010605060906181f08070e0f01120207 73
    0x4407241001e4005040c0920b815165420f014a1200c000d60300054840c030141d50101c2c1c04030100b401c1b04c10b03580e0031a48140b24526080c004541180714a00d0f0565032610640258501198441d4481a8441040140601c135415401086045000e69008824240300d2014202c0011300040a4413444007010200044030410780006848420100516040d1075107003840c3e1a50510300d6601481c0905000d95003004682c0d00c414041d41c00c098502d040f2808202401d4210f00c1544400144540c81841807525505050359900480c9045d04203032030440d20920b42000700400d07403c05110f04e403600310f01118140f054101503118511398240717050464080c0c0c00000501130569000b080340d0321803580308032401d1807955950b02c4000e00d054454002c40ca01542043e200081916015007520640342004120320300d41200c01c0d181c0203a21090082c400d410900741841d51054081c1c0150044a044460b2100d0f2140d2a00f1035009002d45000300c80345209030f0015041403541e1b640411304880100960741c3c0182d8401d0a4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 911157329 1250 911156079 911156083
    0x1241a0702040b1201141005010c0618060905150a060b090108041a15090f01060906051303020603040c17071a0a41090108130303091b0503161a0c 64
    0x80c43c0f8660480c0340034004100340c22055100880c3c00380b00c540f0203c465140c02114a00c0c00d5000d01c42c0c20b00145440744841c0220305c450740041640c4d051719130030944d54240740d501c52040d95007040090701d030394009142e0400c1110440702d4490b8025809241000000d060490151b0305026085410b070404c01e15400140c10000100e00540c40e9401845500d1013600e00840c0780b0750346240c00b404041c050310980b008142401c0b103450740c40c0e043e03603e2500c6070f2a0312070500c0c1c0112903540241da032445a400701ba1400002580310100214003c80c002c8a031401801c0c1007100540040c41c2010090381141e0084500f0010520501400d086413962001455581e04a00d0f90458003a64103640d031084d0112030320751103462403030b08154910408224070081821303840310b0804c6106038018420410301003460440020100040307100a01c402034801e080c0003030001e046459001d00429460318109581622800c14489890f081001ca1490b0840d00e1620040b1410305c60030b218056280e140b41068040c02143e9132a2910003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 911158579 1250 911157329 911157341
    0x801121514040c150309020901090b0604090603120906050a0c0201141e120c070f110d0501020d1d03160204050414100506090f1611031b01241a070204 66
    0x4207410008007814542440c20001d240c500c50003400070111050140300500034001d2200c09900200710120b2a0f182c880301da405051034044256210201300b00108140c075040c0b246a02541c065043d0b8a66070422030b0b009015804c1d15003062051090510061070b40c150f11007500c2d0f594503820700c1c180e0170a100603903804035a03000c0c502c000141740000e9a42c5610101080c0302400d001c1c54041d1442d4000d4565035a1030b540e501c1002805410b541401d9006000f10b180b400c1c03201003a801c00341034407001040a07140c840c2243c2002010b800000d8403507000d443c01030840c0e040300e0410529170000c3c610b84116064844084401c08200a0081d86c888000a091107001288560001a000107680708984000039140c01400100c42c4144a0740d541e034042903026080e519175504c280401d2200c2c8400345000c00068611a4400402c2652403008019406801042e40705590344000c0450001c00c54181d9986594500c003000b40740001d210350200c0e4104064282c0c1c0348000201180381703500715074808542c008240a404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 911159829 1250 911158579 911158601
    0x81206330d1103040203010b011107210606080c1f020d0c1407184505010c0203070b010b090306070f090504090b0a0f090b270d0302041508011215 64
    0x214041c040b600541800000310b00c0741e4402c030000c100f80301202c00155100301481218440a51100500313100540640000c643e101c10190b4400081c200c060f038525040c0e03000e50f000382485400245600610b0b080c40b95111400406075030000325009001c0100954504611fa011401c0015800950741400b6009400d41d080c0440d0310b0030785030308079143c5222181c444400d103001d030501e51401c2130024485140a0480b03202c0d5810020b0002440b401060309054030581081c1d5400b050150a00b00002850074401c80035400015005591100b8241c00c0503013003850705a100f0f04459000308106945694040340607907100505023081c2855208881c01150582e5a941240c1e403c245011040c2c2e05200704141d14501c6410114014850034101144080584008a00080480c00d11402007540100c44503950008000344648120342001c4070720300746250004420520300480c1d4006001e1000901e000d800c104081102e0404c50125450005a160320b02e002c1c0b40040c02d81d07201d40e01c411924909035000460150 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 911161079 1250 911159829 911159831
    0x103110706060609060f0c03050702220c1112090f270907033e0d0206040b03100e0408040905072706030e0d08061c020607081206330d 59
    0xd0b4032588003400d86004ca014200206003140301a05103140314004001d529603143d560103040400307503401c1c400d00303602c040c0210040480c2c416500000c0b80c52440b41001501481d90381021548801a0340d504000620b08600c0f070b00141048102c81ca5201d14540307031807640064401072540d07204c11050b80d500019400f844604103020ac400c0c411a0b0600090100503203000307840c1c10b00d151007414961000e0041413210500ba8088440c2d0305030309021441400c034100b410140c56071004000c10b500146003035000760040c2d54103020200501c0a101c4101107620302800d540113400b0b07030504054448039000d00603403142d80030564075580090b20552040d05180d0126a100310707519a103100c4c1240c0c18203908040c0c004e00c00000d02c0e00c290070001c090002880700110446880d84007554030f8400c24441000c5010a4098142461441c0d04005803182c07801400c50310b010382a03107078440d510a40d4850f404100908140d201c0d0f851102045d540c41c0e18000c0007040c119452903000c03007401c41003038900001d01403042c244a280d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 911162329 1250 911161079 911161091
    0x109090b160c02090a230115030e010b0d051f0507050708031005040501064d0c061c0501050d031403040f080a03090c1a12041b0b0d0507030507020c0103110706 70
    0x203660481840000706c1d81c0385503120b24000000038641c480c02d01c140800300285050030350519000380d200d0856940c000002080e0101c0c00c801248107910802c0301141c041e4000400c0c21a801202c014400602810203c140018100002d0080082c082d03600050300a00303001010a5a0b802001091401040301410904c0302c0e60303458201038061260b03102003484009540b03a098224401e030800e004100c1481c2c015110240444204100d000ca241c928507007450310440358038049a0b0740d00409010020305110304641c4e200b40070391088050303401c181d0103d40240c40e801220800603400402d0303c0075100c5151600c6031660398504203240741c00110714020b03040e200002101c0f0101581900700320741107801045111400c6c0c0d5151304150300350035940702c40c0200020510100c88054109080e045d003041c010000c000000c3c4252002090a03070095102e0b07200880f000a244401c80001e00416502c103200e81001c00c00d0b0328040801075103c2c0d003034081090405650741000c040410001040c0c0c1c1009400c40402c00074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 911163579 1250 911162329 911162341
    0x827010c0809190b1b0408030d06030c0b031905220809030c0f09070c080d05091e010c0905041d060901020a090e01061d0d050f150109090b160c0209 65
    0x1009000b0b0b10340d01c0b5280140c10000d01c1140000d00382008503a0700002e0b03008141d480310b83c0b620300b03804500b50646810381c0400002854440410103005503440c220b000088451452a00c01040d4800d076006c040701d040300303104001a0f511824554004a550740201042580c1c4143e0300e03141d10300c42906906c1607000d0a00411042c80851300c0540403103041030b011240c000156000700310fa40e000701c0e4400ca500030103d50025103540d20030005c46d03c0c16403054001c075042c0201e50005800f070b00c1040710f02c424240c1c084448410040c441043ca2110340b088017000f000b4645071810000c003142413900906000c2e80e200d403414070742202896086400042e10f401500c3c018148440301c54080d501401a0600080c1208400325061105100580c101c17603e54813840c0c2c2c040320300f15a42c0901c50517800c00daa03100004c1c80410012540a000100070750100c80007070300041003828052002c4041c107800c060720301c518141c9181e0010b43c0c8200c290341c010107c1c85040b1400c2d402e4403c115150142410000d41203060007061080e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 911164829 1250 911163579 911163587
    0x71409041a04050a0204180c051306020a050d0305190b0303040b040b040314070b120901180302010510060801150c060b040e060103050d03050609220501020a0906110c010827010c 78
    0x229010444041c402526508404805e90141d4042d01085450001c1c82880b00180b41d0b00090351400d4a0800a09101d504410200304500c0c680c052000345c1c004010b05410400140074201d4284414101002907042014082400b00104031190264a40d1160391703071a240d0301002660b004081c0503010135611501c07020750300c1d4980c005e88401c554840c0440c0210740c4421000c1109820740383c00461403030420050080081550b580904926015580d03004100d1005020588c40750800e03000350004109400e0140d0302d841b044030b0300e62000d020021280014003ea9621004c40801d400c21842c207900302004505140000f4004010850b034041c0c41c0141180c4100d00229009040364041c00543e01001740100b016030030740d4002c0340c0e60f80c0d000b8201d40000d071068148038401003104c3c80300d400c0116840303c50760300c16003268403822200303000c600205d40400807194031a1401d0410718414002c1c0c4890003204d80003030000800038000301c017280e09a2032620b481c02c610141c1c01c011700d64120001d100181d00801c1c042c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 911166079 1250 911164829 911164871
    0xf0e0c0f0402040b0f0304110402070807150c0912061e1b0f090308030403020a0515010f140307150210140a05180d08270f06060306070807140904 64
    0x5000c0c0181000404280c5094030a940031202420f07101440d01d915842d043d0019031000b0000c45680320184104002c40e100d510103015250b110340c000903a035090320704041d10400a214820003440303082c881250500fa900201c0708003101d40f03100c01d010790100076180103000361980b40d81e00b2035000040c0703564602c01142d5403c000711a09400c42d10b4050340404220449191014405000c00304007a80004c1000540c0400290350150091060f1064a11545c0d141400c084580070385071000001c500040c000d601000d0040300040070024082030b018160381e0b000c0b9486100620070080c3d1300b03003403c100c403482c280288240ea2651005032820490006907034510010000150b4200000501d860000b50103580103264401c0386e0054030f002015441108041160038020051034546003a21b8143d89550510882c0781206089100a018080c511054070a10340350100080c0010302c00d40c003400038400392030b401440702e0313030003190342d1500e22440d40e50946209618410a00003d070004d14000b201c0e594620710314161 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 911167329 1250 911166079 911166103
    0x706090804050909070e0103030c0c030204050f0402040b120c0607240510060e010e0907030f0614090a02030402010507060905070b0c10050105030d050d0b040e060c0a0f02061311040f0e 81
    0x543c0e45440e90095907503222500d00424a0f50643d007001440803034051003004240c248903420000c8202d4036075000c601512400d5582840c860420028001145018010140c10703400540c1e0140c40b500c8010005941d80c80561500e5000d4840000c1c504144a5880314110084011141510351544160340c4540105421110701c501c0300070340707000811201d1083c52128114581655810000f1005030208626044050542c10915a41d52511421a41180034410050481104503101d1000c04002c0c4030005c84020030084e4420b2042041000507030b003007001d44611640002c2c000030003100500c0c000740b400003c2e802000d441da00c0800c1a4124003000920f43e50600d4003441d00740801d036a030300d0a1540d540c40d01032001c80821814881c19014140035404001d018500a101192200383c40131030350b09002050b40c0c501d50071440005e40090050700004200c852001c0d920040403603242c8601941d002c0d039480b0750000c08041142d4945071880e900e50300070388009180c03010b003081a03840c4c2080c00f540d500b00b00381103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 911168579 1250 911167329 911167339
    0x3070e070e0906100f020705040e0a110904080304172a010c0f0906110c061b07121112030d14060f1203090d0c0b0409020d2f030903070609080405 64
    0x10000c12410b01c5901c0034001c03c000341c02e94503040b003822015111042440150380031032080c9100001e165545018084090780d40401910741c040c07490511041c0300d018030302c0090141c2e03c443c003400001440d01c401c817507219800c0034217901610102e40f0044854842e604440c3d40e46480590035080c0001c0660400f050803054800802c0100184801a03503030001c0710340d540003c41d1004d9401c001c203500074080300302c0c00c400f20740c143d0b40c0c43d890420000c5e84540040f40e10816000c14412060405081001680040c1c0540701e600302c0203038226038448854050070700302c040c0242e210680c04070701c0d4501002a60980f031003100003400071101070310030915420400c03035403c2c1c4900103466800b8000d003042c00404001c242e901c0c01942ca00300088003406010280040d0840300030101610001b0b0030a008405440600782299015a03904c81c1d14913079a06540000b1480a1011801c04180702c815030070030300c0380f6000008510700e2900d0350303a120703841c0d401d60168142c098200c504008072a0304001d14000104117444c2e00b114 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 911169829 1250 911168579 911168597
    0x2202041d06030d08150409080d0906051f0302011b080c01141803031501021507030b090a0b011d4006150c0213060b0918061806060903070e07 62
    0x8043c1e842c3d82c0340f01c0c14400b1411804c0030810030001d00c09001c801d520040c00104540b26140c1c0c1c1d172035140c2d11508a19902554518500c01004030038080c0c540c102181ca0140c8a460b08220f9010109148610009041c0010380514100000b039281c810349030580c21005603034070303046c0410403107010703013042c80c088400e00204c400010340540070000c95801240c10680107600b5075940d0b41480d840d0701016a90306055109480359507099005c8107041c40d2180c00d4950740450203035400d0090161040f0040c25a501e086d00340070a0b000350b03990180c2d103540d0240c4150f5102182c10840300110302c840d0904900d54420040d14104c0244905c4019200f20b02094605c00040390740c0c40c002c0003001240e0301c60141001504009069482d400d00c1094000080c0307000801000c06aa445400343e81203403100d52100c255000e0215260406180c01c42184a04008048040e07001e03181423800914101170b8504901440d20140010070400c0d150179095070710159010301181c21b95515941145081001281c00000042c0420 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 911171079 1250 911169829 911169841
    0x1603030509132f12040812090a0803040b061f020c0a140d0f030e18160c0305041724180c061e071703060a0b16022202041d 54
    0xc4181900d43d20f0308181541140003020811038816110907020440c01401e004d5118891081400b81c3d004500c283d010940d00e040946060065503002015519643c006019040204050104403580316030700c01c0c03c040c0c0c40e80d00c0c07a0000e610180d82c4008825008503030f80c000d40c1c109030001111a0f50950442c0c1210b005a6250091450a000150a40c2e0014282c1c4808400500607850f200ca03268864282031100c140c3c03003404034030b0020703101c41c0c102404082c41c028041c60320340c00e0305100703240c564031b01e000e001e261016100a0410701c11840340052001d11031103c50324019050040a007079003100e50040d0040c418200d003000086505030790b80600340403c550000407004000850480500f0701030b007014100641010208501400c400d17280d400d00030100070078800a0403201c00003d04901c8900d40c1500c0c0c0c18040f092250074030302c940001020348010494410390a0124403800140307603049851820000d078074100090803d60111038130028500103d00803410440e04001e07403032004451015500d00727682c0c407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 911172329 1250 911171079 911171081
    0xe0d022107061d0f0609032b030b1e0f01020708030d0506011b171c09050a05100c0206010e060a0312121a010804230d0302030f0a09051e160303050913 66
    0x38952030b800048804e110441e03045c0385e400f5028948000b000e88000d10080a440318040a00c211305644081030090301000954140c410490b01840555100e440541040b01245542c90345900e4144035a242c5a09d00c3c44503032080000d00040d04085040c0d98485503807400c818040c00c0140d50072404030700c0840300d0200c0032081c140c841484035000b00c03d804452500384094501d5602400c00114070000003a003201245255008a00740320744910003c1c01c2d002c01e9402c00c9420000a1108210002e0510b51004017490b80001c1207030564540100c1c01000e601c501001580c07402c81a0700041250071030880b8419503640091010090064500050007160380900485248101c9000c02e01e01244490003c103000c00c1d058003c100c108449003070500300c040401c2c601c03145041b085512000000e500042004140182c010103541c0081604809002000c01541c402e0b03210801100060b0b0000030400823403204100400540400b2190342211882690704ca007001800741c0e00150085c3d002e000311031030100d824006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 911173579 1250 911172329 911172377
    0x33071e030206010612061d071206080307020108090c1c0506010e010b16020310050c091807020a2a0608090f06070f110a0812010e0a0603030e0d02210706 67
    0x416809800180e081c13550a842004084034010390041d6a240081600a010322006c40f03c18050701e80c1c2a081d1030504030007043d004050511038003c50a00074104030b2000004142d0b4030942c0d090810014940c0c030105054a0440d0403443c15901510109030a1007003c400301d0304420041c020810f440482ea22107580c900180c2080c415801d144104001640442040d2108500c40f50702c010240c0f201c503031013980c2950a0715029100d000c45a040080c11041ca40b8080c00081500d04480c00041000d240200010b900e8000e401d2000c7c1400c0403851080c00034940380f00302000c0c804849190b0740c62a580320b040040c1030340e004440b291201e2003400b86c0b100744900300259541c4200c405a6814040d228080c03400c4a124490040031505172146a841800060b1060054104030714003001070141c0f98580598001c007004040d10b0a15154070b80201480400d41c848100300d0303482c0040d118003a0000c11031020444000d04804103414218104007881c9180314013141c11001c41d0710381e0751144880110320900d0741603564 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 911174829 1250 911173579 911173583
    0x1416020609060705180d0c090b030115150f050d0e0331051c0c140f100801050603100b16032c0d0602040e040c0302010201050109060501080633071e 65
    0x10051140b200f1103a14601d011000420292006e00b0050352580c812080c1201381c0c002d0990f05445078a001101c0c10240b00e85460500c1c220850464185410459070340e100400d441e01040010b12150a120320380140200d840042980c8010041140010030140d1a5001480041940c40c40361080480401680c419000340c4103240340c0e18040c10307142c03004000c1040c011401e00008202c100001c030020a000c0b145400061025280c0381c0415842c800030440c0000c1004501c07407180b0703080e048907041940d01102c0c480c1594001c0d106296a6160590342a80b060340b01d9024401e41000040c140165244400b00c202c9242d10a4503100000e0744010782d01c000004011184030709007500ca200070b102d58504050000860380c000d89006203882d442d408a5661440111010303103180380104020811540e0903c0f8480c0108580c4404008c040d040c400002d12142016020700c2c0b10ba4040da080481e0326011580644050f41d41644000c010000300c01d2400b202d80001b00c081da07407000c03010140c585c2584217a030080c00080d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 911176079 1250 911174829 911174837
    0x50d03060510030b0f040e0601030b07110d0c08070b0114090a020f12100807060206100b13030f03120f0b034305090c04360b0414160206090607 63
    0x1d2201c0b404900801000b03c0b0198080301c001c50f803a10b640c483e032156102e59050710005d40b840b90305504044818a0003c1d1505041080100d0f0b2089200404612900000c40074580003517240da441c10000054025803e01500d205c4280e07000083d0010740001031100c0400646850803241d0b02c6250719422809000781d040e05001d402c00004008044d5412210f40c000300e00340c402000951180b903640e14020307180e000790f40960b0115003406100e100e881c0e105e600800303225200f02c2c0340c03003020f4003d03070481031003440001c0606011600500c101801903414450200f18000f04024900b51510b904002d4911185690300074001ca003c0c0381d0340a4145007940e1000030340301c0041107000040740c3e0b00c10300194558407041c200c6910b20754082419907400f4849401103a0408919446604107841091b01840900181401030350b000d44032401c0e152422003002407107481841c00a0044804000708014003c0c07140b24211040c0d11100300808800e0944802ca501003250b42221502c0c0c0c2ea015100d660343c00181ca00d14081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 911177329 1250 911176079 911176099
    0x30d050a0809010b22150e1e0601021c02150712060e01080c09060a08010c02030304110306150103050711030301090c14030c0d09110d060c020105280e03040b0a0c050d030605 76
    0x280d5028072081c170020420f00800030b0095102c1e0300c0081e400611350000b0106107400701c184005200c03040c0f0704100001e241030404110b030030000d0000c0d40e0307840c146152940130070024020071041f50080c0000001d220004901d12018508800010820440f104011040318508580864005440761116041ea101100244a800300d00000c01c5521000246172580c4040c41c00301c0400c490000b030162203032512158000f1622420b05181c291003c120143e80c250190348903504001c003d01d940085030400c0e081c2800d0008240d12020012142c4c030310001410b269610002000147e04400c41d44025140c0c1a555100a550000e1a0748184c2a100a4402d544c2e002010320204103960207552018205070f109012100081d0110400704507030030109401501d22554a03c1e10264031034081c0200c80c0e01c00384a14502c3c4082d03c00001e0415604440340014400b03603907861104640c0d00b0100115005042000103a684500c5190302c010548012070398219140d000d0710150210060003400b0325001c1d504014010084 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 911178579 1250 911177329 911177359
    0x10911030c09150f12010909050309010e04230405070f181509090317070509030a0f0c0e0c0703110313091806181703041109070509030d050a0809010b 66
    0x290b0002c10002c0c1d4451041c0203041c0c0000858001072a030072004405840d11003002c850302ca40e450005030b0081a6043c01e101511000460220032100c41c40e40c242442c00d00030006001140c020030945042810305009008200d50811180c15400c1c49244a2411180c0140d110f4004a41102d03ca00c904106000d075452501c1c1e0201c55074005030300c11001107807014841560307504d101c0e0960b0314001003a404258a0a81074030000b0820652543c0a106410b0081c40c11884c0ca0110355100400000a4030b01903161f4144010020028800001082e080d12280c111341031000e1a05216440074030202c001c030310254008034525001000342c2e40d103074100d090003000b2130349404c403504042c1281103082204400c200b070654001036414410b80e4034024095590228040c5949041600002c008203100d080d81820705c02c0000007442241004007514064500f00d003542c56649090380c080c0688140c0a40c140100c10b01d583e076080d806409003088040f207903a40c0400c0d48406c0811400c80d84450b00c15600040ba000340307496 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 911179829 1250 911178579 911178601
    0xb0f040c1e030f060b0d0c0e01020c0609130c0e010207080604050703020d030e04050106050904060b0322020a0b070515011509170f010906090203010c0815152a0601091103 75
    0x807010542d08011560580303401c1602d046968641140240c0140400e110707400d1845881100f84848040c14102041035000d00040d5a805c2c002124601c82d410003d00c804140c3c568054038070135014008824880c0310403040e0050803805c007030b105c0c4030300601c1200000038a60303900250040c000c2d030b000b00180510909540a000c00603d04003810382c207200d01943c8500f000d8940f4458240208040c0c1e07070380ca80703c3c56942d0410007030b11100e50200700d11181c140309104804041e40f040740d175058162160316402070114070111b12440c440354440e250741e90307000c1424401d000011500d001c0c0704001010400c1c0710780e290140810705601d01d22000e070008180c03a1f8141310780d080320701d80104140440011169260015143d0f82c1c2074503402d12080f6003070350b11a510300341141001d00510350210030b1400e16141c10314200d444004400c2503d030220303101e048603404075601e040b200c8080341e80342420100300c0501c1140c91030450941d1003088000c44200e105180000503c0b02d458403900100f0034040144610315160001d10302 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 911181079 1250 911179829 911179877
    0x140328060605120d140a050f0a0e060310050f0108090a021002070b0c0109150533120f06010501082211040207051f0209060313060b060d0b0f040c 64
    0xca5003a51140d021400f079482c42890045202d44000400444506850044c240f042070591610b602c40c0901c00070200b20380100c01c1d1020001203406554513440d41203022110304029080c0d550b0008000824465007484180404082d110140e420f01041740c00c80004680c1420b04a407040000c0d0407042c0d1800061500d1045041c4560091040301c0c1840c1c1c484603426010f0b0700c540200621603540c0c4040754100140c0348400d410580c2081810030103031400110380c0443c1810090075131a400c458a070304005001e0807022180b04460007500500301ca401208038aa5501c00e02001000b05204500002882d1340c800e8091030b2151040f4ac0150200800d56034100b0b42500203000102c801c8242501103c2080d255840501a0340740074200500320214001408083c10060240c0d103802c041c0104801000da0b100c0d20304898115070660304c03412400002e8107040b001420b401d0724090703021100103000104044213401018217080103c4003440d058203030004002c21600f400b079219000c54900100c610000056550301 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 911182329 1250 911181079 911181083
    0x108041506080c01020606031c0f02160b0a081b0412020609040504060212130b01060f02031b06220f020904050f0a031706061305091e0f01140328 64
    0x1100140c1102454415540305820684450b40303c6030714405190303810402550060816800781c0325038884010106a00d000c2100d1103021b108134440c00d1924144204240c1d104441e080c0314608013161602c181d901541d0205001d0300c0040c0403040421601c000c8090f801e52030750b0522181c1481d062900340c11141d03159188900f60b0344254207218450440d1610b0042d64402c510410300103035141e0780708100a1800c4070140c03040c00800c0c0701c00d0511000400c01203200741500e110341000b400380c05603000304034914418440030300301001003e00284102d14000441c140205844411118254924651a400b20b6444880038025200ca0101c1c1409070800951054000303000b442518140c4014401d810300c1d040381480c04500003207150b00e0403910180e45c201c140703070041411180746140c240c4038003c4002c520b00f14010944602c180d0380c0401c0c2e40e144010010740c219015800c01c28414949804032003c1c00009125034007a081e1008001615440d0110b0b41800e40300301c2c4070310b0128050792140c1d4564000d02c10001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 911183579 1250 911182329 911182343
    0xb090310111c05250f03050a060302031e06070c08120903091203040f0509090c102006012301091202060715020c0f061611100510060e0a060806010804 66
    0xc0c0e10b0001e245500809000ca07850341c404203143c03d007107920140c2c00907a040e0208810340c0c030200c15002c41d0391040c194050040e0324039001c42d554642c500355200500c0d1a500003941441200000d62031405021002d890200c0c0c0b28040e540d50b90f560400a451602c211702d00203001c0c03042007094a0424030340e00d404540107035080d0308403410450960041988491400e1446409038400b017010040d161049100c000544000e0b1a8030310103085c441700d0680e03a011103800262142120000c841d10b0580300718004000c1008502907060b00c031400c1081951180401e0003440ca141d00c50b07824080181e404240411884001a500c01c04e105142c101071710b00f18000707440c1c101d0f40f01c08208102408298000112011400b8440c0d006a8400c920a216450304034080c0c0303e813400b0b42040301044110014901700581d0309240e400c0039000115055441404c200180a503483c9107840e0105010300001e1400e03405c030a5880300d8640c100c0b0342d4204c40030480c001d4128403450000412100c0000d5403540b051005680180c0f048807 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 911184829 1250 911183579 911183587
    0xb03190f1a0d2102031803160b03070e100c020118080604140120030f072c03030712030507020f0102181e10050d0609021602090414060405070e010b09031011 69
    0x2103e10300b21078000c246005a201144281880d5400780c4d6041d0304220132401030000b4180300c03184180130442c0d4400c4541400c00840000e2803d406042a08a103046c0203058013032030200c600c8003401e5804004400da0000c0da000c0c002c000440c0a2008074415244110020102540c0b10340c0c404944090800d00d2441c030355224032100d80c52400e140d0b8244a03580115000589070b18180184d41510f91000709a0000c0020000c40352020703403151482c21400c00d4501c074654006003000c40100c1d1844c0724030a070041500b4410030311000036640c0365010394010242c43e400e9983e0391054001d10340c00d038058118101181c036500a003105040c640780c054042007141c8039007220b004132007460005a8800c0c1003112207010400004d0507501c0f61529104010103030440c0d4408504166041440c1182c80700c0002c8007d020700f402ca000305061020007034112080805030b07822517036607103002d20340302c0d031103100612980201400e148004161002220706880407000d000c4d00902c001c0004410b854042d0141006024030f00c04200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 911186079 1250 911184829 911184863
    0x30424020703050607020a03120506130b03031201080c10142d030a0501060801050d0314031510090302132f0415031b02010c020d0c020a0b03190f1a0d 66
    0x4c0300c2c40d40300d90303842c1d000362500c0e10250402034011782e11036494599041c60081000740d607941e4140d4610102c001c007203000a80081010100746148130300741300c02140c1981c1000000301500001580150810150b4a0700002000c101c0180c64040109480d09013401003440307042505c1c5040f114281943c2c04400e01203a00344075080c0c54052542c0700792564404103840341c00501409800a07107803030061500340c0d135040314004103032002005e051040c0100940c003078000000c180711402000c2c841c0e0b850034000b02044021950341c00043c140c1241880102e000b40084031305806025240d12450508801410b035842074800d0400e46140075500d0181d02c0102d101061002158011900354117044011860b200050b0483e0f2558110740151900010b00085a050500c100c1107a5800320741d020000c1150705042040b07400603c0010802065500107180107400802001240384142d01c007007011000b01d0f82c0400800318100b0500003591031002090f50b0a5844100320185810205030513910a402440c1d0b0030000da00c030b8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 911187329 1250 911186079 911186083
    0xa0b0412020c040906090330021e0c1609020f0d0903110706090611120a05300a151527120201020609010c0801060f0e0d080c0f03042402070305 63
    0x120301a41c03000d40d1281b1840406412225940c1681110010210751905200100b48c04055005400d2601c076000f00b2988517150f50440c00c40c00042400d0031403900c4618582032695a190403000c1094045241c0b800094a10340720b108503013100000c140400c0c60b02ca030846404020b040741c004110704100568aa0856620341401100041c2c40b144e61501c60305841c02d04004e111b41d480c40a0f0744501d800075035250781249142d00803660910300c6030030006d40341c4840c01910803060074082802402c581c0f44002908202001e00d08061051076480020002c146100048010410b558001e414486011040310180d50340a1030003a0854500d45481c0f200c2c98548441c0e25007651419406191036008150410b404c42d070f0180001944003e040008011079076425200030080d1006104000c1071002d2260000545441400e01000d0084044c1c11031001ca07540c2d280c030b14000e1b4080e110021450181c41518103007820301104450449142c180243d644240310f80091001d400148400010351051000c00030000d070301 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 911188579 1250 911187329 911187341
    0xb091309230615090c0d0603080d2301050103050a060801090809040b10080619271514040f0e0f030309013b030c10060510020a0b0412020c04 62
    0x206461950800716040c004842088034500c801e0469084103003049030300d101d00b01c00c50810b04030803910f8000030340310710322010a184540054041c16501b032182c00310501043c0d90003812031002101c000c020170304e1940c224040c981c0b03110540c646c4210070b41c001084a58401d81020b6000748444a001840640e40c6011a0855918800803540d42c038000c61a03901c1e515162141002c01c42c41614105410350040400420200008182920074880304c0100790100c651851220041c8c1040c40c2c04130761000c902c04004010980f09664801e11a040c14890b07a81f040d071040c1508101c400304031480341c08561540800c005020010819440143d80b90700904501034200301400365440394001559030780c1041c040590a4038001091090803400e5800d0007d81c840105403410018074001d42d001000c201d58201150a510a10844102e280f1400d9440d44d280b100300c2e8414401c03100c0c101c1c2c811a0309000d618050761290605c0c00b02510032000301c00018081003050920701c2d000e42e028415101504001c10001d011205 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 911189829 1250 911188579 911188583
    0x3041223070311010b010503042f0904033209040e010209062b061404150f15090f0501021e0a0c03080306090a091709030c0603010803130608060102070b091309 70
    0x60400d140c43c0c0d09450a2141e000e598134286401c5240d49050384514403655080c401002001490789405200081d00b04022115001300418a456074103060030024152210380c0d4503807181041c41252606c255841070303c00c004400b442c10150707050a4608081100824208031118499502048002c070aa55001c0c020288003840324091068400c002101f16032560708600c6d440c031518508041844000744030b180540c0078503800c64000c941f610204066218507201644591000c007035040002c0b810050380b03212204059001d903036011034645c1e6003142a80c0401d0354401c0d9400360b0020031042c49110f03038600d40c20000304072010481e1b90000140e074510214078140d41c42526010400300134422107142145a00e508000c220350300f44960041d5855400740701c46486425203000c1c0e40080d481045441c00c0c0200c0c200c2803c0180b0003900c0c0e43c0d680004c25141da10514401e0460100c0c1d038008110a405004104e01440741a0f00034040b00d4180f0480010780e81c003840010341d200d21482c101c1c60f0300030000c0c0600d420080c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 911191079 1250 911189829 911189837
    0x3190804090518162102010e0907090503010b190308030c070b0703060321080105010503091204120203010509070311060a03060806150a060219081812160b030412230703 74
    0x19150301c1e4080c10702d000d50000c071000d103541e038100b00485c2c07228900040c603c513550300b07254599904520050f0748107451140c41d50b8000a048080108060f00b01e400c950803684181c00a12640f0106804c0083c01041c80203081c1800c000d07080c083c400718000401035940401540c0c11140340083e65103076842808011900352002a07140c0105008011504140003015904491500792001e02e51601407e146814010241049004000504a1942000745d03050b610020b0303140c80d5485883e0780390355801c4010090168069801c040c00702d8080240001c465007100c0d040010780c4002c6c1015010071000d40d2190703400b2000c25441e580d000c94194424807085000d1400c850401070494100700c2407100b21340d81030740090195084045400d02c0c0c4076402408030000380e84031043c3e540d5607454a0050341c10202454429420803130718811081901000134403100c094000b0b1020900342d83c0d40701c4130658140300803075000700a40801d07180d500e2000d00641103107850288030b0000b00004101004a0f0070950031484c1c0c190001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 911192329 1250 911191079 911191111
    0x40c0e030a48060504030506190f0c0507020a3c051008060a290d09050d12050f04021302070c0302060f180603100302101202030c040305010b040b031908040905 70
    0x500c1c403601c0740500030f0540307003003a9082600c0d684966071102130003090761200c041c10744070685404440f40d102240d82d0102e40c004100c0100b14410007040c0d030300241c200300c1c010300740f140e40440c602071503560380c18842060310200c2c4880d5140560008071900c5903035052441c041c0b05c500c0420b550307403501040c00d4a030200d80d850455511b02802081403404132907029011a6455544404120318040c2544281414402d110390340c521714494000300820810001a000340244450710b90200d5125207101c0407640103001c24811526441d00e01183d11406480095004031503491021407200b03203070080c0100501907403c800c030030f07640c0f5000b05640d513105d07800034060380784009880351800ca240c140c1c4691014040e91268194600740700800020051030001038440c2c120029000c1030580f09180a400350643c070f51042d9108d05100340e824186802c9400700300c440303509204400c265410f052140c0714000400030024401802840060b8245004041e02520a07290030407000c03030421171038002ca50180596010071501 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 911193579 1250 911192329 911192453
    0x70f140427052e030c080307150e0606150c0f03030601120e030a0507080d0603030302090a0602010213150917070302030d0f210e0d0905040c0e030a 65
    0x10090300300312400940c601c0d000038001c10340c0e011100114110155803d600c101070501d2088600c0f900554070040084100ca10f000c1036400f4040f010b403803a68800c21001c41c1e00f0791013139146015101a0584481c00da403014000460914162854646e000440b0204503d040c2a06641034203000800d4216045a0b00c000240320031941c0c006122040c4030503990040103078601c84601d00c0d44030b2041200100400001094030414018450119a64030301140c404201c01c60744e034a17000d00690803842c1150310400c0380c54070000c1c00b54018000c850280404208480c2d2103070500940c1c900701d052a82c0303410300308510408049003915650300d5044074442400001d183c0300d1318520400d440d040c001a42041008030110000400e942c1043c028803040c0107001075800154402200f0344020300c02982281050720404180790f40c150740210400090720000e071414001601c0c10141038818035801020103400d94452007014011410303400410124005040742d020880041d070762400c03440604012120b1420700c0c410700785e000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 911194829 1250 911193579 911193629
    0x60a0507140703051606020c060405060a0f0506060316030b03010612050706090501050307050c0a230705010509011d0f091e092409251e0e070f1404 65
    0x48400180a03035589000c0681c3e0b0f008026004040c0c1c0f1088803003424908074100021901560051000502200d40500d01400d142d5650442552400c0e1600d103032030260742e841542405114403444019240c14616103c0480010b07120030091840310030166120b8604550395428081c0b8001000c1403414070120841504219013006000e900c0070060004441c030800003030340c100b001d899001c000c0781049500ca070a130041c4c0d10f0420800d00380040220103d218481d0000d0420703040e0905101d1040d003201c50040d1600d0056902c0d200ba0700115021500095010601d4980c03a0f4420458071030107001011691036820201c0c4802009a800e07607118024030410300f1001159080140d131001041d4010222441c141c03454021030001280c802a0104185002038412003082001502c10b203004610103140440c400000e01032082c1500031a000c020a90075200b19601d00d4100c1001994142081c40011340c480500c2603c0001d0b10300c0d100d03c144400c0d00500c0c004a1881d20242c402009210383d900e2041b501b4100c030f90 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 911196079 1250 911194829 911194847
    0x1103040b090f0f0d02120a02040212160305060105031812030115120515130b10020d030606020703231006060c021302030f070f020307020a0312112814060a0507 70
    0x98020140e03044060305564800d0561000150107a855090201b04e4a0b0000c5c00c0c0854448040d41060000414802c14002d014880d841039000b8096100300320310000e021030544006503101400280e090022a001d503001b8003036500140340010071540e180a0803c0c90f8401900240d10071111000584c98403842c46030000c043c3c0b425401800400c015a00d04501d03203410a404c440d88440c020282550f0361072034560b840d0f110030030a50000b4402c61400c01580340c02950741c0c42807110140040e08008000841c00e00008004058991050082060001c0586c1155130001d49401d092030300d100704280044c005180344544005000d040d524003000040d14014401807090705007055407020720410400c82000703129899250000b4061400c000894503541d0304900c2c50003081e5010351311100b5044000b00708032140545040c1c9030813603125010504800c1500503102ca5000044850008441c21443c800642c60050b14080b80e1181581a0100910040e0701703140c28411a1310360340840c0c0c1d403020301502c940c000c5200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 911197329 1250 911196079 911196109
    0xa02041e06080c160809010507062c0c0607020603090c0d030314010609080c1905130605090a020f07030e0a090c0206071202041a090a12030503070e030a0b04121103040b09 75
    0x461030880381003001d04000701135a02c003400c0c6400c0800d03600c01d42c1e8030413022074010b0b680104052020700d00c140000c805000c2c1400010b0201305d581140c0c440c1051021401603114207004108504140b5250240542907000605c10b50660184143d00d1102d0307075070420041c0c6460b001c1d540c002400c60109921420008042e080a02440700c610010041d4501c00580c00140500940303652400c10404010003c9415071a00314541c80518030742010350203a000d5000758200d0300308850901554607111030001c100d200c3d600003400a910104031500100e03005030949504040082c0021096035aa107000c0707002c80f58000000c3c801a0443c2c0103200030b0310391000b55594140c030307050021072400d458514254003124141c0380303105c050f4034081803001c1181e44907540e0b24000d008004c0d4403070040e03040b480d0041c050341c0211001008103000c0c0300400f0950400007581024075174407039044030094039a911000a8101601601020840000590310204a091000e40014501500c0482d2105d1144040081a904031381c48 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 911198579 1250 911197329 911197351
    0x806130b1302090118200a020c0a0509060d0c0305101a1917030409091220070b0f1c061401030905071202060c0319080108010c0c06050a02041e0608 65
    0x404000b5941d007503001411100284410410000e8030b0340c2240140c128140184c40390900c0c4225880c4d801c100c04004c00e540a460340c01d450102d9580c0c810085c60070007500640703402060100000d00c007410a1102c10040318041c000041c8541e949a0b140351078080b240c042064413030b45822564401c034110044400c48407030700f140c0121402410740c8000511150500c14200040e05041307420280030020701c00c440c003401002d1024009250282441c40044e84010710880004e038000506000004544c0360000c040b401000c003412080303207401b055a440390880a60024500010028000120304151281c0000f004c145803320f102481e0825110711410980c56260601d414201190002003003c10200c1c00c2d1400380350ac03020310310200c1c00420114082c42c0310000d014400001d60345001c5061100810243c81c0c40e40c1c501d61140c9c1c80d20a03a5098070050810719000c181c0950000e400513119800680c1c0c403220440f801070406680360500b40c040e52020074685050801c10400340700d0107a01c411780a5108802d298 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 911199829 1250 911198579 911198611
    0x207110907080408030612190b0c0a0203070602390f03090a050d0309030203060a0212060d08031302010e030d20160b07050717030a021513020d0c0806130b 68
    0x200203000002c00030002004c0000020000d4465500c191401000305284d004880560300b00480c81280b0030408401600c440c114100011861801c600450f10001200d80c003460038041584d440c40b01039040707491624502c6851a43c6210461104c0e0580012028207800e8100360300c2e81528a40d06191044502e44804d030401c000c00300341e0f6103600c21640c0880780152034240c20b1542c2400c0841d01c15120b80c0000b58940126014440c100c80e030754025010300d05008009480f962100000c0050b0340303810344001450000c040c000038614044c2207a4120140c0d00606218103008001d070001380c00c101000d40144081100b1182282c0380c9181072030b0110420a100d40207082d6035443c4080a504015103200c1c0614100c1e00290503070400009000d000000c00801301d80740f00c5014001020f07901c0380c02a2500d00010f101d4003450801084040c082c0a00038000040d05150042c1d49400b44a80c00220701000d071f602c011000000200c1043c1000407a01c00c031079107a85141030a21a24240c0501d11340a4104900001074003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 911201079 1250 911199829 911199841
    0x40507182111040b06070f03080106090321030e190b0a06051f0e0607060b0306131707020102070e040605011e0e06060706090215090406091b030c021c0302071109 71
    0x8141c40c902241c12030690410610036100007070180c41040449a080100407461b0f10400200e01c0e08000801d1190711118a13036078948508484103091844042c220a0703280350303401c801000a828041e04002103240103e072a0b84054540e41c901018820000b00400803101c500c0705006c5803800c1181c000180300420303c034162a0070000748100000c28108405251905202c404241c06480000c0306000c01808064580c3e0721824104020101640014000e0088100003a08106010704641c41e43d41d1201c90314120f241070b070701d0740202e54101c01d10890540c421748030b001c00e00b03000781c40d089481180305010101d80b13581802e0a00468240f19500c010b2403030303041e0f0700a1000900f04c114103540640300342c03586500d500050400c00301600f61080d01a4100c08027441360319245c0b01403402403948281c169401e1001a943e02014004c90b005001421000d025083c01c00b0200d51207500110700c03080c0b80384102c90b0419034480300005a0f8407205201404250300207400400c100d00112550003910048804000500d083c1c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 911202329 1250 911201079 911201129
    0x172a16061d011103040e01080d03050708101e0306050117071509030314070209040f050105090c0f210d1d010806030d080c040f12020406050922050c04050718 69
    0x707009000e060101c9400d051140100400a640040c8030750b0304d180b0310030b50750780c1040d0741c82d05081a4401c000a040100040d1164003035103919002d24403407101810707494a03103041032003031031900c030020003102203461000400304041d4001c050107091121941200d1500700d05080c0c1c9008542da0095180402050469240a402180395400c890f003600303041d20003001c1040b00c981244504c0c01d00951180d108400c0c0410310500704801404903100b00c00801c60b588846c1d80c004e54420380003908951020a02c0c0c440c8000d400c00320b980d016100088100c000b5141d440030071072814561855035200019004036403580d440040b0359400380c071689080c00e0400403070400c4004a42c503801d1002143c0180010603002c00d68004441c01210001c0c80c8555001c400c10391514403100b00500450740992180e403c105000c00d0915180b080c56025082c83c08409004640040d03054441ca41885403da50600800030f40381100c1d03c0b603004a51140d031266a5140c004d90030302c0d044036428082074101c0200082d1201250b0440300719 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 911203579 1250 911202329 911202377
    0xf06050d05100f240e0f040b0607081204110415060e0a030804090b0406080105090607180812030402040e0c010e041805100b0a060c172a1606 62
    0xd14080420155500c00007001500b40da40e000d801c05482040700050940d0003001105110054001c544003000002503044030300a203d15000d0754801c2e800380c4084144d190a03403220b80c0e40c1b0300142005082a500f07403038502e400d802550070841645200760400c020442881c2e03140c011004201c2c0c0c05c2100e080c400403489070080e45401950188034421170403e00d20359480180400960b4014111170350b99491f5038807030001d4102517505500940c1403241c04a42c1c403506001e01407091a07000c00a11859983c040101d8540600c910a24401d0700c480c0000320b03c492052060070100d0f01000d02050b0399060609c1840212090095524000c0d0000743e0001203581c0d111003281c0a031441202c001c1140440e40400c2c081c030454030000100b40d44120b07005903d41e060f994210162000c13045802410a60b6035501c00e031741c402000034008010100ea940c04c00da0b004d10314409003801010000344084008080e9a003c000c0c5001043d0101c0150b001c1c500e02c062011640740c02c24050310700d614100304070901c140006009024 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 911204829 1250 911203579 911203597
    0xc0e150111030a02030304170723100b030a0b0601090906080d0806010203070f0212010f05101706040305040b0d0605220b1008010e151c02030c09040f02090421080901060f0605 77
    0x1002140c8c54142001d240203440c1110f40111502c4a1a85507006054440e01c88125542c1c840c0181803d0b03040120061258481c4440c005e8081c0440403140d6945021001008280505100c1e80c0240414548a41c0c07040101914051004202450b540c3e82c002e40180c1e401032006045610401c4034100103026614080c400c0356054030300c1d110349008119044d014000240c0391120325482c1c04100507642084c080050112003a040e2400460203550b688181c81c2d030001c44000c1e022820411040009208000040c101c0000c101c400080c1c1d0340e100c10000c1c80000c100240581c184800840640312080c8910510700e10b00c0c0308032400c1075003645921000e0002c0f41c0c140b140b051107108440001d030610030718000005101d9401000000c42c0303110350403140d100e012f18a070140c0c001d104480c2e481d01c05051640a840c029504850109826202c9070300300801d148000f40101ca1400f45810380d0140021424482c032424051611142c1140c50004402400c6851030b43c003580024088803010031050b6001421110604 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 911206079 1250 911204829 911204843
    0x9150626100e0717030307050a0806041e0c08010b04060c020d050c040c0c1208010e0a200307050706050901021207050304141204060e01030501060f0c0c0e150111030a02030304 77
    0x11800c04140c0c28081c82078110407a0a0418642080e00c0c07801080a01c25280c00e607041ca40000c2c1c69080c02640c9000850302400495010040401c2c1280503403000b0740d0000c0000c0011032450452400400800d42d420340000c64140c8441c24150b2143c3c0029a9501502a00b5250303400d203444c241004107020151400039015101001240080c0081407054851560014100340030906200d40e000703060380e00e204c00581e080c030441c100145a4134071480b074003030403161409244001c07a29040070700780040c816041d030004212680c28202c1c152002c00005107100d00c290743c0b1481e07280c0100e030400905a82005001a032641d204200f607855003450780058581052180c07801903181c2c0d40d60b2034a000140303e10301003c0391030300c2200e1081d039103541c0c02e4006005039803095586000311001d66005409564080c010840498803901042c54510321490720400d00030b000320440c000080c3e407040c07401c49040d41616100074003074401c0325122055070002016422040601d00461405c60580d400035103e00001e00018291 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 911207329 1250 911206079 911206139
    0x1d01030f020409020a0504060f0e0a2c0108031c05101202030f0303130204060e060307050103020a12060b0c070b27010903020402030f0a110903030d0b04090c03030201091506 76
    0x30000c41c0c0d058802500d0301110865031070064a80140c03039038102c0e108a00004841c280c0884480e032080300b01c101c01d001e0140942d0861030410200310101080f00304141400c000540c0200041c0d421008214000c024a60145642e04154004074070510010750380250b04900f4802405906900303da206021a002c0441d0102c42555078400030b41040d04903d00805144400301c14417020f080d0300894840064400c40302048110b680f9004040f807140d0407181d0642c140c020500400044d40070760010075149689181c5491115203540c4030302d0840f4166000202488404107001e1100c2c6802c00a0101520b0703030300c100a01304002040c0100c503401e02088105050a41d1410b16140d503405525100d01456000f4003c5d91a80741000d01104040c9044540c0c109560405030000004009030302110805840039014501c0c00b405002c024004d02544a24982c00a0b510065080443c030811500d40242d03100750300116031913109040c10180480880091400580380a41c00c0016218148000340b40c60180e207071142117 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 911208579 1250 911207329 911207351
    0x7090312260601090b0a03050a1b0c030e0111010908130602030405100c150513050c0108060f041a090f01240903031107030c1811070503030f090a05070605030a05071d0103 75
    0x8410b13002c5c1d014800b1000085214429640c0540169200d140d4480040104403100030351200810000550040030402d001401000300b84900e4451a0700c01041c180310003524403076101c817421219501030036640d01e40d01060181c0c140319406040c0e8000e00d40380c401107040a08020016100402c011114000e0150101422040102c0f241d503495403004411410080c0d86403102140313075041000d420844140c0070f20400c014807580910201d50040d0701c05010b01c00c211400c070701800014a445021840643d040c00160f803111ba0381d448125100711110b00ca218442e515050300e1690742c1c0001c1405a10140311800914100b940c44008501200c3e09803901c59030410141c1c4155040014a40002e001d2081c000c60204924203841c00900041c103900030308000c01e440480d048412800782d0384c0000d2690700300300003241e50040921111341c1c10000500640c1e01c0c09019559a17403070030541d0b5008030003003800802000010a40341c400c071a8045158181810f00e00c51548044050380002025141855510804602 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 911209829 1250 911208579 911208587
    0x150309061f03050d03020901120618110d02031e0115050904111c1a0a0b0f090111060a0c031b0f03050726040b0105060408030301030b0612030307090312260601 70
    0x700440e000b800303682c24910b0000000303000c2d502010f409404240d1310680034410029034400c0340121a032000c02101a420354455145c00b800e000c0707a00d146c1204090000d444800c0061006500a1845041281d91240d50030030308820060142c1c03011465001404440581035000303401c640c0300c01360448001402c000d04900c00320036801010b1600c101d1a101600c19180e0386081d510444003d201e0107520000030301e20008001c0d036000d40c4c2c0520045954244000e8050140b148003814020700141801140030f020349110034503100c000c441242c085a15044800b1000d60984a56804580404000c540e0400300c030304040c105040640b040d40800d5580d40000c2ea4041c89020880c3c000c03108142c5492148020389a41000c4540c180d405070307810f070700e140c0c000989450400103c0341103400b07400186065030b20f162201c034511000189810340010511041e50071203001440150700c60346054031085c0c01e0905501708602083d00058480051048004034800310030140c9140ba980041c00503400c0880f55a4030004032 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 911211079 1250 911209829 911209891
    0x313080f070605070f0210060f032d06090b060d050a110a0b0403031e030e0a060504060204050904050a05010f0b0f152a0607441515030906 61
    0x9000503250209110404da4804400e00b076102c8541e007100c072484084e107800411110544142081c000c01a601080081c54982c0c40000d801d002d8003604810104040c1c444041140c04442150031654940720441005880d4140c1c0350041e00c00d43c1c84107081c107800e9a440d42c1e64040b21801608155515420008135a01c1c030303104401400c044a5510780340c83e560301d005003491102c0c8400303030f0002100428249040d4400d106110401e5440401048204807540b02c01c80105405030003a00c4d0b10b9001c02020843d03840302e510450143e841000184070544003401e12500315803082c0403142500342040c000d05220355540c884001101011111450601c5003403041e0480d9114083e108414903d030303240e0804440344c01c0c0540688801c12003003912031a594941c0219111070582d4000c0c200b6480c0c4d040404200394603a060403d1402841100f040001003400b222200030100300d8512540c1c0c2d0f21902c40b4081c1c0c0c1400c4440c0705080281c4640c0074118203001030b0f41e42d1140b00003401802d00b41040200045c208007140401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 911212329 1250 911211079 911211083
    0x405010b03071e0e0f04030507080903160305100b01050d020c2503030f0503010305030406030e030c070f091a091302130c03061703120c0c07050303210c0313080f07 72
    0x1c41100c1e907907501c0c0f80030400c01400b444110710300d6400c00242900704e85420304d11800d01054840071641d116a4141c5075600f20500540e08210203000f4040303d900c041041d15980302c101440440110305d540b51452030086003042944407241081311003155640c001058910360000003001585440c209a0050b1424640300c0b0700c42e505040c94190401c60346403007403603001901d000ea5101d00344620346280584540c40700b840001c01030f51040004105091190380074101441590040c5c9180081079000b2500c0c20700c60740c21400c21107591020030404188240302e090040c20094240a810004120003d194003034024100e124030314031504494110742d68019140d0b4070180341c00081140f03c286100c000c0040c9060300400341403002488841c0702c09440001a42d540305881c2407a01140d0740d0f011544605900000d110300c44c544104440801d40750342c01e102404e028410700000424402d082101c4600c0b0300300c050640440c001e0100180f100c111452040c0180b40390300044001d0743c80d10a4030010585208007000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 911213579 1250 911212329 911212333
    0x40c030c2a0f15232a0d060f0f0302060d020c01020702150306011b0f030c02030c04090b0a0c0512070e010c1e060b0f030c0910030602030f0714070c030303050405010b03 74
    0x440200070350f45180c0004080c1e03100e070411a003c2000b0000746001c405a00401c0b00d4802440040c81400d4034040e5940b07401000e56035400450041d03030401940f03801c2055071a2219803a03c00074803045d840810395030018040301c11080c5005e86075801080d15881004501d2050b41d80020350003020500035011a07000650162031140c00c18400850419140c10503030301c0300d001984441101c114500c25141040489400550b40350003901a55403c0d543d460849400304e800d801041443e100303503500c61081c0d556403030040c0903440080c074240c10341e5801c840318107040c2d90a000c828005002a42046034805070301c801035042100b050203034040103a0311002941c1d4001d000d001811000c9030034800c1d0741c03100602c0d503108080510040c088501042164410203800176003617800844540000e160140d030741500b0a10700c0c03d4491610342c5a071124800d036032088401c0c01c0002c14580500c495181d100d456800e600011800d414280841952890200d04030351001804164950b401f14040c1305003944000465500101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 911214829 1250 911213579 911213603
    0x40b0a1206110c0706090e0c0322060c030e0114040b010b130306090c0302012c101806020c03060f1608070201020c0a0318091b050c031e09040c030c2a 66
    0xa1181d48101c10b0107805c0002e040104001a4601d0580d402801042141d40c91402c582d500b401c011112030701d8030440004180c04031011808900d481c42210004000c541d80416008a2500c02c42c2c03d460011000e400c03003081c01c40420006c14244084241510916001d440c0c1c1d52413240003a072001e52184d00058200c0385005682e40400420f000590b0031240f003a00c0b0740e0f1a010700c4560b10385411851503503008101e80c0c0c211260b40149000041407616100c641050020b9190070600380c0c9104e101600000701581c80310b80614814902046000d40c42900407176060024540741e1110041d1044d10340d1048244001306011604690003901550041c028040488403140914100180201c06c58031041c03048880c10280411982c51034040d0340403111402c00302c0c94008138000c0d8200d0300e90388050000d45081c0424030600c3c003058044584130fa411075141c2021a100c1020303804000031154401d9107007051524143c2104803154102e050300303c00507a52050391502c080c0c040702024010002100083c03040362150 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 911216079 1250 911214829 911214847
    0x32030c120a08120a0c081003120c06020d020702150307170c070b04030810151b0303022205010e06071208040602040f0b0304050106051801090e0c0d050c0f040b0a120611 74
    0x29111601c1813100c090207001842c040441541e8204060322040c1c59001c00c1c210a00101d20300950640034107020345054807030000301c5c0c1c131030800b241c105031640440c0b540c00080200541c82e000d4179000e2b0503a621070f4018a942400751029040780d680d8090b00950400b41c100003054070816000340d5101c19007201c0c0e040400e10f494500107011083c221140314070308131041c1002c51200c54039000c0710444001c03174480c91030160400400c0355542d80107101c101c08041d000c00070550751008066403100c04503004903103180b04a0510b40090300583c603010840e07000f03030014459034001c25032320b140341909c070303800360903c0882520780d81000d901904c55a001400e120301d20f10f44c0010900c0c2e141c1d004611a81c0210001c000707558540c0100304104401d00c010600003801c00d401404810f00030343c0120195000d02c021500310781c3e04500401c50b0032403c60310a0b19140c218400580350340c202000c400104000442d0100b015107111000188900e4a82c0102c00c1c203404180e0b0031702c0030049503074021207075242c10401c40341c0c9542040c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 911217329 1250 911216079 911216107
    0x4180c0903062018040e0c180604060306020c0a060b040b0d060c0e0604170c060703090e0901091b0504390201020c1c23090f010e0a32030c120a08 64
    0x34a07130340d4020751a04c030308012a80c0001c1088100d08000410186020150100380642c00ca070140c40194466514840080010412304c01001032030746460141040b18960704203042140c50302105180220300341054001959100c0848904640e07018600042280c4544021203004036400c03007094110000107004a03d00c0030420303005c0006009038007250280080303241880414000c6a5004001c1040c941081c050008415002540251094000216441c01e612000c0f240e0080d46003101021610450502ca01d00306401120101180d00031103200700036800b41002031036000388181d1031026440c054918005c503c00c0d01120300182860f0115100311404042c481c00d01c13a04088000c0100301a2180309809540d41025a000010075098207800c103181360041c86150103030091190b04221081f09244401c1e52492614000741032080c0c1c2110065504880784c82c801000c42142032146400c2000784c000a650001d0f00c05440074055504020a120701000f0501d4041040d03801090341d200818080b20107118 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 911218579 1250 911217329 911217367
    0x20f0c031218090423031206090415090c15020d120b24030604051f06050f0d0203090a020a090608030d020904060e01060f0f030509030d110c030a0504180c09030620 72
    0x400345680ca0092034496209507a1f100d108034505500702410300007992841c1c107650032039119000300070100e550480261040120783c50704101b1a80d01c03841c0a42400a030406214182e001002800141035000030b1120150400408400e0711103c551078a01111058594140342018080070281658600c203216034440100d410403541c6030301a034075100000d0003a9080712105c5891100b0030302110141800e0000440b08e90384024001280c0010800c6000e000d07403c00c3c401940308616603c0580001c420610400c0302004a039400042c08030308000003881b035450701008988a504810b080140c0d2048018082005400d140c0d000b0001c0d0100c4200024026070080a0312904851980d02c441c076021105074260101e03035069581e030032a0b52082c04020025115680b01200101c111659103003462040e041c00c43c5154000d07180000054030106c0c042003540f90407151706841c2c42c0208828040d00494004c014007915a40c48054103160311b501070010104008000b000c1035004c2c181107180d85510030f9032078440c2411 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 911219829 1250 911218579 911218613
    0xf0d33020c0607030b090a050c070b180c03030c151f03032610030305030612071701060e07020a0f080f04060c020910140409020a050307030c06020f0c0312180904 71
    0x1440b0000f61041e100344154031690314010440c080e591035a040c040004d05d4020708040c0120340810894001c611a80d0f2071034415024450308220b00d031321490b040e5003070868590125010303900c01c3c01001e4601101059006144103413a10038025a61040d442e85070b41c5031114030702c1c00310120004020041c107a210b080b402650415030348a4042e014000324059a050702103c1a903034040c1d81280600000307200700300664005000410001019004190490400026a100b0100c41e03d0484800c1da0100342030041c00700130103110b241c3c40a1440c0c0504c1c0613460b09441600107003080d03900080e01c410000c400d000d698a203003c50340701c41c1d10303941c60b41c0c00501003c01d044020b80c4503504150018520391502d02c0c1e000103807201c403240b009110f00110107003c00f034005040d003243d0002044101180355201040b401000f075000303041090000d883c04401174140010441c03040001d0700301c1c10305810076071000120b0400d42003980d080196100750554660400d00280c2c001594404040c105000600200304081c00c0a20 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 911221079 1250 911219829 911219833
    0x711120c031312080d0506300d080f160908011404060f1a040b04020d020d050618040b01150306081608062a0a020a05100501140f0d33020c 61
    0x1a40b2a0780404443c641d01d42c0080418a04000740154a40250025600701c01c002d055644801c285210129030070052002c510310108104034050203417001080301c0e00c210303d464204021a820008030b030714200000180981d6032a140c450040c130f59144100c0782034009005401c001c200100030036100c81940e000c103907030030340b1046d0074080c00001010161181c1c00102d07480800d4101e0f0381f244803017840094215460b100c0e610036030078402070b074481d2401c1c0000c01c25a202000001000e1078000d00f000b03503032841000040e8880001104020024622191003419160701c01c2c46000e104000e81800c4001d44600c0d00129194000c40c1025044203805160501c03d80d075844080c0d0380075640c0e503900307a14400000c1c2040d203642042049204891004d88008141300c0c4030034410f6074140c1e000f03900c507903184c40c42000610341c034145d490004101d91903001600201d9044c1c210340c1c00034a00810f01c00500003a241030703400342842c1019003411500c0c400301c00600c1c0c0160481548503203001c00b00114030000b9008609001310b18 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 911222329 1250 911221079 911221117
    0x30408010504020906120d08040221100e07030b0103081c1109030601170c190e011d0604021c0b0424140301150e07091d090c01080405060711120c03 65
    0x1c6d1a1561030801d95004000c01401c925a45042c112001d40002e0b0044c0d0b00204010314050315441d90b400c0343cad40340d02c00c034400a02011036a8002c040464000c1c0c0c41c4409140c00200c014000655600900d0b8116904404040d4a502d003020501242c0025070544424041c508510507000340f0b4250b024101e03280301103081c0d8890340e80c1c840e4008600b180f581301012454100c400b40700e44919200748450b040c4144440c030200480e8445180c5522a0001c1c0c0061707510000d00000c0c1260703030b0814001a544064142da0642c1002c4502c1c40c034501d150080312042c00c1054490300c001d07996071503a07403200a511b42c9403035120354070003010001038022a62500030340800707034460f641c001140e00b0b0500030241c910311031000c1520303001c2c50021a44004c51001d8408403c200582900084161185000c00d1440c2d080303080e80d45050806094081c40d010071039642c141402a054204008500041212a4404210b08200120300495048642401c4c20401080200000030505100c880c0000000d0020201410129641 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 911223579 1250 911222329 911222341
    0x150809010510120303020403050d110d030923010e0109120207060206010b0403080a050c0a0c0609091811010509090907050109050102030304150f0608030712090906030819110304080105040209 84
    0x9860040b80d40340d641c210303894402c103d40185186842c407070600a1600500301ba450790b88480c20503d0740a0000001064a105019002014414000c030000d00d41410445000342d81d980740d690300e42c0003060101e080700110b414030001000390069840003a68100802800c4143e28200d4540d000c0c0c5a034100041c410224003085490000504906031260200141c1c00e003455a80c5081054ac02540c1c440104601130008550134007040125159883c800d41d9424080350825a0040051030300364009900a428182030a40144000b1040074015030020342c2892240c94030001603070700c1e00c110507680386c1041c0c100b0200100c68101107454002d40d00260f80e058802c503554401240c0e680000e990203041041031007465610142c3e25800113176021344e0008045025945d9446450642d00107030820788400c261003000416099100d200d900142c50490002c229107170460f111410f240c010800091410482200c418800c1800f50b11000c5c1c03442110011607a61f0741d11246043c0c0a00402c1e41c2c100d0080a840e804a44 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 911224829 1250 911223579 911223581
    0x9031a071b030c14120315030c0a0e01150827030c1b0907030e031206031c021005010b0310050f0d08190e010201050f06010309390b09030a0f06110415080901 69
    0x44485c0c0c06410701c0c21611389805400380c83c0b400c105280d03450300c16001c24064030303200c1c070341d40a00502c406408050590301d00003002c10312505e1202e50340300b003100200400a00142c080b0080d014130800000c1800c4400002420521318031804240e404603216001071140c100c44000210400044c080c0d800c201d40b0b44a030340b020303410382d42982c0341c04d4000e410901900c0c45040fa2980c0b919400305d00207003140c82c130307203815121840c0640c0600c0500c80180c10800041c07200c84e04d07034060240180381074000e240c91840c0c04041c4a0180f03600e4001c00c1e01c039120a00307000800355101d00d20401955005000366a9a601d0310302e40300552114500d05030003164a8000341030b80740d0300601c41c813403050480100006043e598680114000d091100c0c0844080d20900d8918880c203066500f0110110072800200714400d100c03002c10440c0709465404042d800c1800c00103c1d0040d1008140262590340c80082a909100ea0b0324111000e88002e44194840c800d0214000030702800c110034883c1040c4454841c5001a141c0d4081c1034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 911226079 1250 911224829 911224843
    0x190b0405010b1b12030412080907060f141b0a0201170105090412020102192601030f03050a0c15020405040c1d060f0d14040c0609031a071b030c14 64
    0xd541c0d40038045280080f40b82040304016895540666510501c81c6442c00000d401c04e85d4103848070010040c3d170050898100b0405508079042d44021303d03a003854410000e1140e0750550b181c000b00031000c4001128420f002040c0c0390000e0000740841011028084c40d1ba03503030f41800700c00340c0c002040794040034014503c01814a050352000b4003401d05c1d0780c1d1176803907043c0c8a1180c03c11040841d9400c02119032100c2f01003464454080e0985e85800900c0c51021031080b0b6203505036101c66507844048010000122000400d89589500d41055030f203d00070580c05556051a0f000c000c0c2030456032103041c065841c0140d00520513100100d60400c410304880c20100d90312160050310404051900111121034034095014101031051500702625000743d03000000c1c10740c3c419002c00b05111110000388010040300803d1103014104a15090603182e2860f00d6010501c1c6561500111b00301c241404542d09911a000700b542e482a1001c4030040895245001404002400e0090329461100d07820b210380ea6401003680c03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 911227329 1250 911226079 911226089
    0xc040f02090d122a02011409220515011d03070305150714070305160503090402130312030e0d03110403080c0309042d050c071b182a090e190b040501 65
    0x2c44804c2c0c1e4282d00543d000d400324141c1c80b410100c2030001c2d050030703074600a4480e9904c4148426441510b0781d04411019a60043c09144900c961081203070361599120f44e000d00c03903200c0010386418405080001c24244001608050701d02d00800740280c2403500b03600e074200d000d40c601d0760b0707143c404100706840d04c03a160040c410001d001400402c5100540d0141c0c40b42801014064410343e4589603060000030120f80c00f214480d141c01c1c00b1040700b0810300105014003c03030304200d41401c0c01000d071a20100f030348450744240924185540c5608607080785003a081910003542e48482e45a0b5100785000680c0c0c0d8030340029864a01c50b0303042c025001c80c036151079480c4001000c504100c00e4190105c0e600c2d2080640380c000c214091400d17041c88081c0200318662004c0018013083c0020301200c60904002d04000d80c4400c803481c9101d03050640101c81d0300c0c03804001034515a1040b40c410581d0301000c070704848e00b242c40c0d882200c0d6090700302e06110505c1501c464045124071021401c118192641c030911045d40d109101e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 911228579 1250 911227329 911227397
    0x41d0112020a05091806090a03020c0a0308090607050a0206030c030405010b0a0609061d030109080c0d09051e010210050406150f080709050c1e030117010902030c040f02090d12 77
    0x108000b1404d140d6400c1d83c2040c0c52966002c130340e084039160f1a1030058201d0346015654408001501810b8050008000b0384400f500c01803085410760f210400c1c1c512500c0c40c40d501504000400700c0c1481014170110a801c0c1d40102400e80d03034203000070040780075002910240c483c0e52920101144514128004004844031511081c40180ca00304080d00c403030350340a1442d04c4810391012081c4265400307102c0ca103081c51064003083d407aa00d00560391031400700002c0380507052010070380c000d008039a074210102ca140501e5081e40c000d01c0c3d040c00c00403424081d417070032a0051b09050105000421215822030050026009142e45400d5610021040e0f103803190700c40c046054004c90000d224896140d08082e601100c10140d141ca041c100310a02009000031004072607000b2400300050109440c60b10030740c0146101c40300280515101900000e0300c408200310000e12503966149a00301100c15901550881d085c02001c00e00328030124180450456108501030000960751880c0c0030103508003024a141c40121044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 911229829 1250 911228579 911228599
    0x1406190c0215031509060f06070f050c0607050304030b150d0506010509090312061c0b0406021e0415080403120c030902030613031707120f0f0c02011b1d06041d011202 73
    0x2080c00940000034185a8001e0415070f1f5a280503110341008100c440c0c4a1081045486190300b051818488490640f51140b40200003e60124070000292800e40303070000c6101089858210f030b02c80c415822480c2d81508151060760140c248500410454100c070b03400e03106425580d54410070240c9a110b141c03141c12191144902280e05800c121140400850080401e81c10003046601c9159a01c407044600300c9035503400103000c41d42d5043c100d2044000032241e01c08181414142290100c44a074405140d030104048180042c0505100d03001200d043c001d41c92040002400c40d4078000c01038480a0001c0c0d001c5c1c0715440204106c1001e950703c1d40705040d0540e550821102c510f000640c0c0750400900b903081003003601909000350821600c035441c020741d6031003000194107102e0803045003030300da1805005055914211014490301c08075000f012688ac594644502c1507840d0110b400d90244110440c540c20070004100410f44240c1c041031000010b60000c0c2c4030055a0741da1002c601405040c02c3d0094000c13803014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 911231079 1250 911229829 911229871
    0x3060c14042108070f0c2103140d0f2318060754030b01090c05121e090a1203090f020d150e030f03011406190c021503 52
    0x660307400085481840098034091540e21641c0d10700306180010b8443d1b1601c5035040040c441d464600314181c4504005c1300c010031302103440c0034284a014000381070500c0300c009401c9102c550603900228203092450001c102140032420454000c0d03801c001c54025284502c80440c01c0c100c0302c0d0004220480098009107541c0d42c0e0000d0845403005800c18120209404410210341a1200070703d041054898040e0090500c035910541220041c0d0600601d170400b24081092020400c2c1d80e00c44c6043d1242c0003c082207903450b40004a03003501c14000800454258801406101e01d02c4030114020704034542ea4215032500c4102c1c80030340382c525068009110103400401c045642d80290400e00c0b0b00360284484440c24212030300840c1807110005811602016103001c4020780440710301c10894446250401075003051903140454103140b0040c00740781c42c8092003c0031403075560354035412602d08856440345034405501294018241284600c0100e104140b554036542941115000f40e0f07124071383c440c20341d024206901c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 911232329 1250 911231079 911231129
    0x140c090c0d0b0307030c0914060d0203150c04030602040f14010f051603030b03030d27020f190803130810090206031816080609060a0606080f0a020405090103060c1404 73
    0x62290b0641500509200101080c0d041d020100109281240030403031051022495074040380042c00e05100c0d91270400b0110151300c002407807200840c0daa000060040c0c54a9036204c10b680295403005280754000035000c0b50507494107410408581410510032804481040107651880c0c8110381d034070000b5003c0c07140c1c5d40003e5180c501781c44120b01a050001d011182c1c84042390840e40b00f1803070000c24645850101040c102e517648441300c0409482c2c10700b03c1820559000a9030400c7c00444544690f500072070700090f030781070040381c00018100c82040385c3d1f540ca02e0f18440c80c0c9203006403142c800315000711880054001c0260048802c0c0c542e000300301c545560b94840e13030100c403010f0540240390740d03110f80c8020f4080c581e10000c840c0007030149000282010b26100b51042e10f0030b10001c10070b40f0315605051007003180d1900715012a810000c100381e40099596000c400320000e010381da202660103401980000248a2240c0c8214400c0c0220b6865060500880c0c0255406104911a0300420b050f480c60b01c10b50b075000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 911233579 1250 911232329 911232341
    0x50604090212061e060d06020d020c071d07261801020d02070b1e0601080705090901060503091515011101020c0a031e0201050403140a020c0904140c090c0d 68
    0xa000055041541c0c01003090861050041c01c410392101003401802d00000991450460f1116203010441c03626001107402c0485100b0024403054010460900c02c0b031b0107806a07960080101708a90f0301c41d5503622554500e41495020900e08800100407410803841035060700300c250380701080740c000c400801c0b91200c01c20b8001401c104442203103454032064500700303000402c50400d001c00f0140e220855400c10400b2014054a050840d8582c14190303100088046180c0fa400b10342403c1516040d500c0c484162014030540e100207900103440c400114103e81c00002640c001c80600b81221508030f0018500444400240c81e490709101404002007140e622540080020400c02400507080c6074609030442c2c5842c400c00d10450208a45500072524003400382000034801c0500d2000b4001401c1c40d4501038202e100c0d8500348409c40000060003c07989000700a0314228410103483e908480c1b400341014040c400380380f1107500417030246560901803071400c036803010701550f44d151310f03c1d00d0114081e4410000f820 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 911234829 1250 911233579 911233591
    0xb061c0c030f110a09060614091005030c070605010305060f090c01020616030f06090b040b03070308090411040e162c040e0f030d020403020f09010b1209030d1d011109100305 76
    0x54510310103d92a049203003002049004c5002c91030a00b0304102a1610010751240c8411035404c5c020101e10369184482003800000c0342c02e0032580c1e074071605a1590140b003070725005011241402d000100300080041c0851060030800100ca5903600c41084150300e41c0c0844191a0059221a0101d034106401d1421708540030190b08001070040d4900c090306060ba1030a900c0100d81c01d54070841c9505a00f41805010110302044018124460955603903000600400400301d0040c0e5851561004c45054801104e020782603403541030b4141e00c1c04510340b51552080724081000110700c0d03081780d1031407a401c2c07480b0354031110a01d804115100d1300c41c040c400103203006004a1200d01c03550240d8510710000744018100100480c1d80075a403642035005100b20204400b0141e40a100c0d0000100482c401007400d0381d091400030281e1540caa112401c98602e1030040c044104400d51400b400030840d090304021280e1440d10100003408050000c1084402c54001e25001680051403150131101c0d0b1071080e48004ea00c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 911236079 1250 911234829 911234843
    0x40b030309030a060603050d02070b04120609060f050402040605100504170a062301081b060702030c062b050103020d0b07020a1b06180308040b070f06090b061c0c030f 73
    0x22080070000c2d2802015034016154a0780c1c41100b4400c5c0402400040d8802c1e04600003400018580249031400b0b101c0c0c4d100b07a1145100080002041002e9500600c001642041c014007803851200b034a00d00415040e40c08174402c1c1d1501000103800d05000701040c0a0400300c3e101c0f6400c0602d03011010311014409469108240520080d8200245042c03140f00d022814107a03040740204440c05c01d4840d420010307006406990300491100d4100f80350f030300040240140607201c50307072500b07410320100340f902e8503907040e240e4059404181c403500240524514100b1601000890410003100b121450860f04c0a01019400c00020382c1c081020a1100e94600e0b0021058411540081201e8403009040700d000c04448160210002c000c200141d480081e615455049030aa000c1d818030b15502d4600500c664407032000ca40d103011a086042c8074484100c1c1e00380c19002201400043c80c1460210407045c0c007184c22078816900c83d4868841041d0300000790000d00d0f0f1003000b002070981181c41d03010b013a1148050440301c1c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 911237329 1250 911236079 911236087
    0xe15060306010f11030a0309410115060809072405070c0e0103060504060606021c21060b071e0309091a1201090201030b06090d0818030a050304060905010914040b0303 73
    0x1903001c00c010141d140103030b03500040c00310152400040010103030780744101a202224109a1002d62410417400727210500400714401c812000c64280134001000940c041740b9141400002d8003500320b00d210340b26400b0403040c0c41e003054881c00074402c240c1e83d5408581c010051521491940c60080000700786c954042e41030030b1255666a08100d0603448260811901652604140010800c481c0181000f42c0071030b00150110b10703c0c409030318102c00001c0d0700607810440c10304104486401d58042200070001c000c941441801d4444001e9600c3d45d01c0000101e030b00001e03144640000190002d585052260706590720292540340201c054040c260400c0d411010550000c0400d115503100b0104a981503104000880c9442d11400054111600b003401240140030030000f042c85a5115101c0c1d20403658410711441c0c80f10a107064401c0e80244400f202c0e034051203926100014803d00001410482e0001d41e03c14203065100d03801110140380070700c0344c04192070181c1c280303900c03d24003034100454014000d0100d03414 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 911238579 1250 911237329 911237357
    0x10e1306172a2b0209010e04020607060b0a050a0f030c06030209030709020c03040e04210201110706150e0103051b0406060905040b1305101802030408091002100203040b010e15060306010f 82
    0x141041d0594890011072000f091900b1410100c030014010100d9928001d0580703080d402050281c0324030900101a03e54908a0340718582d50b440b1581c025000181c4083c550a40301d20901501840a0109940c041c180c4800040c2103882030003125002d4202502611406203400b5102c8065004440d05041901084c040802c400404820551156000301d6104038003081d80325001d110070f10034035009030031079040c95007641028078500d0450344840c0d80030000140590111f1841409010316400c64013040781c200b0b00010038491700182c440c00070758200c540d079185031060000700300845989200e0400400e030740200030011442e040c3d1041900820103000a00204e01294880c000c5400c11a10564400d503e20400e01060306c1005101b00000340c040030031443c6041c0354607a9615401254940f62090500c011111030a620902040000440c1c000066440741840d2401d0081503009005141c0000d584c840042c1c8039040401103244c100101411444c9103884100046420307801d00b00b000c4050212030668240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 911239829 1250 911238579 911238619
    0xc120e070f05120f1f0f060305250806090d02240406020c031608041701090b0424090804062d08071b0807050111130b09010e1306172a 59
    0x45c2d00c6044c02c1d0b440b0f103904441c030000841e1100c2180300c0801d40340110610001e000020f0700c034401240400e000c0c12514100001010606558001c06070a024031424020400000070b100008200d803034081d00c200181c540c1946602c0e070085804005810245c60105001c62100d50007000d41e003500ea000d9918101d0b00d41c80700d40311021842d20880d19884002000c100340b01d40c5146103002280d00c04000e1040380400c1d1103d0b5240b690103000a4081840944880c08080c00780c03184021200c0c0a00080c092076000342004039498016104010200c1c01c7c4c1c406025801d0020205007050041103815603040c1c500b804400c5600c110002c04500a0108505001101440700318050664174407500e0219038a100e903140650946d080d46400300e0400000744600700001c83c08440b0b24060390149002e190311140004012100c417209101c5207900800d20b2103c1892034200341c0c00c4a01524458250b04100c201c184038196a0b49400801460121090362407100c001d5040102190b0380c400300030b2001d0355101030011000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 911241079 1250 911239829 911239843
    0x150601140d0c0f03150b030402041112040819030501322806050f0f0a020309040203042f0a0e06180c0318032113060c120e070f05120f 59
    0x400f0410741c0c03000007441ca6040c099101400868010030390391620300707003102c0d0b500d000c054030092060b620744807400b4005030008159061641c0ca00b61000103802e281c101029aa070101442d00d184030b400c031589038000781c064041d0f28102d07000810482900410941c02628001450201010511005c01c4110080d0b0302c00c0341803101003403001c00c003000b4400d07001d41622445810786e019405200047c0101a4130508180907525454910f50300c00d0f41d546003001c4107e055100750b00802d80c3c4070384040140000d100090f44455540100030800d002400b00b80341a14048401034050103601245503407041c00710203100c480c0742c2d8005901600e140803600307455000989011046448080504010041002180e4440034100390046503074055440c5c07102281d00040801407680e02d58110f240341134042916520b0400012140603004401004080b19049004124241d44c00c48804201d082540030b2480c07040200d6140201e40c4900c980c011a246400280f00d040301d14400042818010721680410f0035106010707803 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 911242329 1250 911241079 911241101
    0x90b0108010c11070602034305060a0501030b010b090d02030f0307020114040530010905100c2111070602030411010f08040534091a03150601140d 64
    0x4540e900d0001d81c02852543d100303086456540c0007560800c05160080200ca035182c0d03005100202e080a0b03145413400c048031024100c450704401d056801c00e045c0800c01d8143c81c40e0300c10801d40711541c640d124a40305a403405e000143c10401803000400400020000800071f00c0c03800792804100b200303d03800003814144c07141141c04194000250420440d030788494808481c15100c8007407420142043d003c81d40f0354407103a4001d400e00407400c5c1c1d82e25511010a1144d00c030b618150009105032041817070104e0701c0b007100040e290406410401c2441c000c03401800c0c2c66001d501c0f0108500240003403808080044c14000c2c0c030800d1510300400c44480452041d000640c8100e00400010b0700c600184c000042c64520540c00f000200001d090030f00c00010b0000c42d240b43d03116110600301a500d24410609490b10501103525000810503050000309407034150000c2e0029000c0010340a0070310010001e01d51a16007080c03c0c5414008064001030b079075030042001114082036006214101030b48031500340d003242c0c450804 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 911243579 1250 911242329 911242331
    0x10b040801060f06050909060a150215101404090f021c031407050307062004080f0618070902250b0906091c2105010b070c060905091801090b010801 65
    0x91021180034040c00000300b403042903a40d481844c01d0b50043c80750148940042c412140c410100d0600d0380e8203080c22028125071a005441d122a4000c0650754101c025140034109002d8800114000c0182100e0740803140807102020440305800c04000080544160890340d0b200160b4000d00540c0b1554000c0074106240307911182596140d060140c0748903038801d45c039101a0000c1021400050740402a103040707941c0950702146903400094080000f41485015000e007000218000810348400a54100000c0c0c581040d60486d41b50156491942404014415203070350010004010250103940144112000b40580b4801c145400300c4100ac1c1283c0310700c05845074000d90052002151052203a607810a00c1c04005044408240309040e201100368190300c400e0240c40e40c680805504405d1040c5160801c0c11801c200c40e684503207035100c00f030b002102c007651880544280403803403031b000e480b180c015140001c0c5190074640c3d800c84500342140f10b60600443d15507c2d070800c0d60014059001b1107000e4500640 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 911244829 1250 911243579 911243587
    0x70b0307020a0303060e100512010b0402030c132103050a090f03150506091b0d02090a090c0f05031b0c0a060f1a040204151115040804030c1e150c0506010b 68
    0x20f005065410740c0d04503203a4a020941030062958074019000103e40c0c05852681031141205845801040000d1001d03820034000410000540d908100504250b000c2c0892480d82c40c4e16072031210b01e58203285080c0c0c610301540340994404640960040c000440c040d00d00a0010b07501c0300c1d100c2c400c00301c241d8011120385043c2008180054001e014895108000365141c08079031601440441d400c0003210000886507030f00194041e201030454040310400c140c043c01b241d40c1599a0903032000102005000c01002404005010740054403400450b400f907509018044010110340c20001d10341c3d44002c0c0c800e075007441201042800501140510b040904619200180d107843c2098422204030384a240540b01c0c0c0c3c03040006120020703024642d00050403640c540b081d070707201e014040c1500d04a4403400c8804403074613000401082002c00f00040003624801c03011585219910288411100024401c13201c01c007011a07014403100c003403c54018003103604c030315201c20742c51003e4443ca400d207002a0010754203804005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 911246079 1250 911244829 911244833
    0x10207060c1814030309040207080415020d0e0f130903020c0a150203030f0408070203030d0519020a1b08042105150603031608070b1e07020c1011070b0307020a 70
    0x2214041101ca0281450612100308105000802d0128010300701110228504084251420000c1d40d00c0100c0140c42103603192094100008560418802c031121402c4d40c0141602052000c1040c5641074220340342d8026580314417041214504c09a00d000340c110010a0202900e034805006921804d4001c0d005000c0701040786007841000c4a5942002c05034400f0060381c0b0b086668000212030f0b0040b14003040c2c62407504d03580f404006510074080d01075414400899403c20a190940c0524081c1022245010903049100c0401c41030340a096070a03400700d001c104a011448210030300259003144a002070900c0c1a03261100780354040310031012a44250320b5035607902d0811030f0070400703117134000705400309200c4c645041c0f400256684036054030510480c42d03201d085400c011144007681d4440b5031043c0d19911501e0075501040c44801003100c551000c04d22140070544850001c01c0c0306050302c2015110301340b003c0e208002928481c07105103140303005210308000011010840c00256000d813286a000e0b20452105e4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 911247329 1250 911246079 911246081
    0xa2c060d020a0e1305060114191d040c1101050114090703021c061d1e01061805090a0207021e010e0402090a150f02070b090a03020f0d05070b0415030e0613020307080d0201020706 78
    0x2c0c548d0200c0c4883c00c0200c080c4481c1c0b2800703440c000c0c1025140c6650340a540d40070300340840440420043d00107017000740390800e041d000740c8481040781c4010000c016aa0f80c4a180416190b84e5115080d008810800071036070180c8a500200f0314281402c510035081c1c0030f002c8034030341195016413040c4581020b1519000008000c202e9142c0c1240088500100c01d411164410807120418401c05e01070001c0d0340111851258242e9108008003170040c848601032500000c800083e600ad20f608901c1960180c1c200c11640e050406444070106060b0b4500c08907000e0701f000d010081d40000e00165012051348000034803c0001c43d840100711589603100340708000d4500e0080d160414580150324102c006001042c12070700c5640e1064100c1e0780450741d48007602000c0d004540440440d100c09000c0c0e01440d00049048029000180100c6890240102122129000440445113108002c1d0010340091000c681400b400c0201c1340380482c00201610500b03959940c0c403925120690b00010003603500403c8020500880d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 911248579 1250 911247329 911247347
    0xa0807200615030a1518080a030f0e0a2a05090901060e090304120b0a0e010e07031403040b070b040203070b030f060406061b02090405010e01020a2c060d020a0e13050601 74
    0xc150b004100e100304645d9100b0b01030000180750329480b59500c100301010501a41441000c0350000815030b41d030141c0c01c20080c041c021540d0a03900050070034000726241b041c001044c1c030301e0039003020484010313040d5281c01c02c185140e070450707000c440d08040c9000f10300c41d51080f0059008205150001507014078285440361078030001850800660414401004140010040810510b40c0045a0f290715074900d480c03138000740300c00004100e0943c40c003400b6503100040010260306980c003846c00440c43c8010140c403240e880c4141c6c010104400c005100080000d5881c440140e003261009058400c115100e901011007a00b00315a030400304003400c414006141030a00c6840050b01c40e2b49400d4201101c1011044494440305200038020200c034130016051000a502c2080344400e040000e5603034440b006001400445c2c40030030501c8518529070640071030b56600c9000c0d648a68050680e070300740b80c0c841030340500030f40010030088140900a03074011440e680b900707000c480f4203011b0a40000c290a028000406044c9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 911249829 1250 911248579 911248621
    0x25020105041505040b07050f0d06080a1505150d02031509071a13030f0302011b020a03020601080705310612060c020a0b06130908041215020703050a08072006 69
    0x110f04400d20000c0342401c401ca981c84102401c0250f500c007003081c100a01480383c01c00f48001c9610341007012460480220f002d82ca60390207403400100700b00d220100401242c0c000c3d100300075905400d581c0414a408c0c810440c5140740d0000301521858500660f24040010046a800000345c0122000b4009403901e1180c500c0640700c505402e90034402c2180e000d1490b8212804060a40074240551004251013504045101c49900603a90442e480101c00a50b684402d64400c50142c0124000071401980002c1c00c20100d0714020407550b621a40ca00034596405000060000341441800d0b0410200961f4010740c07008141080c0039003485100c80c00e1030801c032041104140e045421040805010424244210b6040902100d02010740c20803030350030a0041610501c002d11030741c070110b00000c071001d165040101d01c50003031140c0c408506003046203208034030800000402140040c44201c83c03052113084112b82c012a1030400c0300c035601c41003202da91410240004000c25074013000c204515980c50720180402c5030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 911251079 1250 911249829 911249831
    0x1e0305040608150312070813080c012a030e1f020a2d080d0b0409060504030201060f08030d02180913020102100207150504052803030507050f12250201050415 69
    0x14200f0400a6240c0900c03000d00c2d11486400300315181444149421a199058401c40340c0e45074641d80d500ca81e0b11445a400d01602140400e001c0321050400302440b1484050542102d200d4610f182c0d6007566080c00c0f40ca0b049411940f85510807481c011640240205c0c4a02900107200202091a0071103001024103032034078520044110b000c54241c00321446020a0b0b1380a4039050711240a0000030004044000d06268080d050030002810320082c0d5020500941c0242e009000385502c559174070010603218855125181c0c000c0180801c01441d560184c4044100030b0807051000040781e000441607441551801d40030003000b00323400d04640e0108001103000426407010360509045445542c50b0f5510000705503070242d1680c0015041140500c20f480c007641c12080841c04518800d08240001e000ca041d00300c01103450240030512036400703001520740d0310080b244100e1516081c55105081c10030060012180100074001c2c7c03c0004c50b030103100e10300b050707669400081d5074030f01410503c4604450a106c2c1480c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 911252329 1250 911251079 911251111
    0x180310090b0604090615091505060405011b030e1206071d0105040303030b0420070605060d0b0604200c030a140301061b1704030c0513050609060d1e0305040608 70
    0x101c1c1d510328158082400c03980091007110b1801c3c4800540015505400c03c101d4100002c0342d40c000950100040c8204081d03030100c003588030720a110030340c4a070740295404210701c00000000f04468100130108180302c0d26150f09101e0140300400c2c0c3c103038086c0d034444040e40c0059081003c1285d01103010000420481d5248000d0019400060031511a0340005410103840348a5000d443c2c82d036810525641c5000c20901c4010602050000190342004400301c61071420007001c902c1d286000440c128100d03800c24042e5040740c6800301003000401d40f00540340d0003016040d05102503c40c0017170141c030040760807402855441c40c09080040c032106200d003035005140000e00061001c1948601c0d40f080c24103000c44603d0010306e00c0e0400d00381c0e04184042e908080d0303030002004010018607441002c11580c080d980c2d288405146102c04003035071011500c05800142d8100040c11501c0c1005400d0550750003080c0603590400c51903001c07814450000810b801140001404000301c6a0000b00241d000c50a4280c005c45 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 911253579 1250 911252329 911252333
    0x9031e03090c060f02010e060a0b0a08070e010627080f100501030507030f050304080f010213140f060d061a0307080711031e0c030a03060f05011d040c0203090618031009 74
    0x342d80c80c5008040070010700c2c3d400641400d0007503104455205138042220b585140103035901c0060141402c0b0940140c0082c0c0700002c0c160000111201512140d0440c44e0580e0708028044407002c41c10305c2c84540000c03207011403100c0c00c00042c0b049005844035802410f1015910310f00e85141110041401c0344051800300100007050021904d0000e4984c4000d6030003143d6500d00308a0b141d8011a002003c45000b01d009041c0724040c154000c1c40801d040103403c070f2501da66045c050168501d050507884d0880d8501c92080c0007460a54020100c8000380400000d2503504c0d00c0d401c4410846c4020207801c5420000140301a40d41c2100c1120307400341d1546411502032043d0300d00a40ca901802040d80105010403240c1940c944a0b80e00703680c020948907080302e0300d5219100004000d00810300c0f95084980c1c00c1003000c0382c694402c01c90011040f0416041e03140440d2140d007800000c1c0350b600402d0013180000e00558203255100d8000b00414180182c148924180d41c004060070f1001841c2040c6c4075510309010300c80 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 911254829 1250 911253579 911253593
    0x10c0f200d050c0d020a15090e01140105070201030903110a1401140108150405010915020a111c0e060d18140a0b01030b1e0c0c190b06150d09031e0309 66
    0xc42e400003135400c1800c40c0c919102040302c00110b90404021440302c801e1100c07080794003058031f100b03d494082d0395104590f650b1010703c09410007110043e002800030880c6030b015500a41106080c1d038460f1401d103803841c50300b1a0460801d54000d500b00c0746103016821307442e000c0b5400d004640c2c802d020303200c031a59254900030100d41d503004074101c4a2003c880b90000a02400800c6d031210003226046074103c800071134401810380096002c880588082515005a48001007000451100118078401c1359001d0000c0904142e076000b8400c80100e901040800c0222a2403941d40218000d503001c890b214000040ea5203880c0f80c1c80c0c401841e0a100315441600c00b100403928001200341107e4102500c000c00b511920800c040741007110819001011805062029a400c0c000040c201d21103120f060b1086102d071a420700003000412500a00606090000f040292401980001407080b4421103240340c004004a69416158424001da012a1340315800400c880c142e55442902c0c42d560f80350402c8040f001d075468071 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 911256079 1250 911254829 911254843
    0xb1314030403030e0f01270807060804051c20010b04020d091203140103060b1206090d0f021218120d05090a06030e0d1211041202031c1d010c0f200d05 66
    0x80d101e501f01d012200c0038000603100388000307000400207550301151110805845500d081d6412101445040f4948124121000d0310001c4c00045985d903020030344002c042022b071180f0002000489540c0e5050411042c0c2daa03100911040070805c102140301442c0c1d00708001081c0d01c00884406040c10102034803c0b5000078012641520b030b211703000050402c01d00000c94100c2c6018165412a4800c01003803100d05038000680280400c00ca42c1d8200800c104c0c62000c0740c071100800300c1d6070002001801101e201c0017207601d5030144500007070320400900c1c1307111542c2854103c1c0b6130414008a540081e400b038075030a00302080340c060300140c203050101c101008000d903942d443c201d01e20b204004503101d0903800ca09180c0c0150910441300101151100d40314207801204808071407089201c1d1149440090620202c08038410010141d5200c1112403028010342c100d2038059208054100042076000c08001103000309607031102c500031003610b040c03050310083d983d207812421040d480c4200c80d00d005020004500041003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 911257329 1250 911256079 911256107
    0xe060918011a0f0915090d0b01080c06070807080c0f061e0a0506030a060504021302041e06171503030f1c06061112090a030506040b0405060604020702010c0b1314030403030e0f01 78
    0x41d4089494454201703403501510010a81c0500f210f14050280580c0c1c48000d41642c2034442074400104140080080502c41c00c400105200f409000907008142c582002e01800a020b10540d040507000b184a2800e044d0304035000c525107100080311018100d616120654454441c8100300114140341e00001d80e1001000002441e140d100e40000341103440740c14440301b807051031713031000e54569460701c680301c207105005060f01c00d151030700e08800a100c0c1d1140c80d000b00c8800a4080312030203510351500c42000485004200c42c1c240c40308004100c00700e0000d000404c2000c2c84808a2891026002030700c1301a038030242d02c42010800b01040000510002081c0c80350172070307000c1d81060b80e12060440840c42018036a88045c009000302010442440346102a50788150710a005442d025a0707594100720490155010217800120050380d201c1c00142c90341c0c401504000e4200f00c00c5014051941c4103200780c1d206c07945000c41d139040440c0400c1050303007103110614031030806c9851949110201c00004d040c45002d04038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 911258579 1250 911257329 911257339
    0xc0621020a09050604141f09050909010216080a0216050a09020d15030605040203060c070f110112090c470418060e0a15060e060918011a0f09 62
    0x2480d6261800b8080c035500808024040c40d0300c0d10395078041d400c0080c0740b21400c10300844200b5140e000c040203240c0301c660072165589800244a08050501007503010092402c00d2542d800c0042e0380c44d80c10488041d60385a482180d0380c50b41c9040c10704000b802c16500300700c06011400104001e1190b6602c0c8000c040036070700100c10050700e0341e0b0b4401c004409000c01008a01d443c00c030300340c030100a205586e002140328034029801c40d2a151614a5014030602c244500541510090f40001340010140700445030038034014980108500720861003402180e212140c01c8400e01070445080103c410102c4041050a03400448141040b01c018000e2038072440c14941c17480381c007590002045280c900b040a541c040c000c40030390220015030018401004083ca401034003240c0c68404001142101c0c907000d100381120718002e019020a141120a49240310394040319a070002060000300c03119168003d0500b1804140300010b140c0c0c1d450640a2001c00c0148420060108020030400350031a0100e81154505142510 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 911259829 1250 911258579 911258587
    0xe1e0601020a06020d14040f0318031208040602040b180a0918110a1a030f15031f0b27150a0e1b03190e280203120301030f0c062102 58
    0x520f840c0201b00940d44c0355003a00e03040302400284800900c440030780503ca5150411402c4e901424603901e0b200c3c0e48002880601440041c0765050320030306030160418480c40003d03080035201c40303038020b4075000180720301207514500395041c3c0e00345446c1c0e0001004042c40303a402c2204000c0c142c480e40c41c944d0a25000f918000032114040a55200d0041c1c4800904240c0b00000e40c04d018160556610350094035450150120b03800070440c2c680d800003040a0728040140204215210054086000715120b13500d0315a01d981c848000400c3e0b190b0031035420700c0909485c14800361820110242c4043c0102030030381c07280901d40006802c0ba44e1120840001699106d0345c4a90349940ea11100400343c3c210190300480605002c41817020b80d00c64034401148007041d1100901100d04050665559800402100540c0030805e81035241c203240c0a84101c1c4440780041c0655459081c80c0003600500c0c0d00a074001c981540e10481c00805000c401d1244002520040c50035210602a00c108946040c1d5000810307111240e00103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 911261079 1250 911259829 911259847
    0x50a23160507031a01030b0f010b0703082503060810060f061101020d02041403101109060d140708011d01031502090d0b010602030c0f07080a0318080303010e1e0601020a0602 76
    0x80c0011903002254000d844c040c00308501e0003000a100481c0c2c0c1040c50710208108800001605050301c0c2e42281c070a0800100b51412102e82a0240c41a24014a4160300c1003441001e03640100d00306c4601e44020403107a141c80240e52074507941410003a10704d45000014880d82e20074051260484500e898941e450750301082c0b4003402840741e80a0041c015100103030021700d98841d1800100340110440c20794055980315045e00341a200d00d400e034691000740070081d00d0400c0c60032001400e0b00b40d038608000600b80f1001d000240010000b5a140404603909400401810782000b100300414944980b95503103070351555884407090b030156005030308506d80100780d031000c54880542ea104850380001c0d00d1039995a40e460042d460b94043e0300f0001450250500040c4464400903941c81124510001441059561b4404aa0308024070414180c003100c244c10000c1c4108041000d180a03081c06000d035000c500f4101100c64020b0300e107201d002a015200400c00c022a030300440d03545109900803a0140c0c0d074084030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 911262329 1250 911261079 911261083
    0x71e0908120702031005061c05010f0606030c17071709060f0106020d1b020411030a0501030215090325080601090b030d0e030604020d020f0d08070b061519091203050a231605 76
    0x15104141103814608c0080244403054110540404e00b55004100c4540c0381c6404a050758070500ca48408a500c02c0d03058a100d80318001180c0d406012494a2150002d841d29140d0910a0654100c50340358002020300103c400644a1b007401003007036000502249580c0d82c4007a0500c030604100d07000015107100c3d41001d40d1500e801015264a041c0c118903501d181c0038088400810080c00145d000b001e5500003141510301d00012073700c0c140002030003041f4829441c040c0701542010094550000300c080400082e00d132204214482c080e02c118040401c0805020301854078050706452948208030b40b1020055094502180c0c0a030015010758040c841410300d4004165100f00341196280c001d002c0a41240c107120b10880030b0129607204d0103440103661103410030480701070317200351003119050410070000039844001e0150201d5840c6a0414495040c0c4e6101b01000611040300c050780800d0001400c1c940103a0300462040b000c030307001b44401401d40d020000214050103001511900c0140318010380d8184882 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 911263579 1250 911262329 911262349
    0x80403080919030804030e060f09091306020a20010c09050402130f061d0907020642090f070207060e0a092406020d02030306010305071e090812070203100506 69
    0x70344000010401070380c60f000708000c108690580000d0120b003007290061070301c0c034111a0404255001d007070400c4020020824007101c0039180a020010340d041e000c001030b0207400034010080c102d4440045094a19041c40c0c200c990101c00010a80d02d08070001c0006600305043d481950401c1d07a00585814030780403000b007580c00c140c2100352030420b04080011707001c0c2d100c2010441d0012500081e030f503145007102448171038107040e01c034207015030815400200203d102104001401100c1540140007a941c04010301069000001880010601c10300300441b80c100105e00a42096400003807010038541070200a449002c140a40c3d0300300074082c80e200880c1d40e13036854207a010f01103c0707800704201000b001c80240c4c805400703040580e040c4444080080d12900124802c00310024036009546180d8030500110700a1000605d8039043c40200420090000841c003c50380039081d1980f039480a035800c00b8405440c0903610044a0140074042101000588001c1100019580001d50101305600e80c0800500078000b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 911264829 1250 911263579 911263603
    0x1707020a030602032706070804020a030c030309030b06030d140c0106030c0e01030210050a051812100e1c05040b0c010b0909010209040f0c0e09041110030b0405160804030809 76
    0x141803000c018005030340d00a500170114442d0300a88004060f0950366000c3c2c0f161149001500640c0000e40604d00602d105a40b10784000c1003001d141d5100c0d56183e1134148141c000303800140b03a07003c003030003004000100b2541000c0c0482c010030268400c898020301c0d80368603502103204c003800416403d1000909401036409542d022003611b2540b510740424545148007403105a00c0307540440c01c00c036030b00342c010021240c0800990755000e2801d144013038030308c00711151038103088d8220f580b800740c2c004001c01c20302c440c41002c0d4100c0e0012034141d40d40303413515203061300141d1915400130b207051000315060780003401c0390b044404201c5200d8458082d1000c960042014204541e0802402d004009800c10194020612407800310f504018101d01245c1120488034040d190b0008242c40385021545807604201155200e4801c541c0781035154400b2010420186074428104007081d2510503507070040c540340c09540e52204006c40400200d082c07804005203400401740010b428850040049806100180441c2c80410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 911266079 1250 911264829 911264839
    0xa030203032703012d02040b0307050306060702130c090503190b0901060e10090509010b010503010302010e0d15140603010902030c09090f06160e010816210e0c0307150c170702 77
    0x10100d105c1040200c042c034581c0c07180d06000300e07068441050062003070302c050b1110304000c03034150354030717072000761840d610140485921250521500005964000901101c0c8481d4030380860410300705400605184255004244240c0140380e0740450000408024a422a0000008951503c441e0542e0340109625007000c1c0c0c7c03101d1000104000351008911402c00c031210040100400e0791603100c2e02d4200c490516100e40014000c2004002640c46100e644000500080540e50400d645655001010480001801801c1d03111148441d0501070314010b05c0d4481c030700360001e0140344c010782d0010740c80f52070410020f44244034183c04280c6418040005030302c59129982201c506040000030703140b01d1110342e000c12000500f4060a014954480c603801e50150700b40c562190500c0c5523004084c1c0310b4a6401c45511000882920075003514085401101120045a030280c21246036a0081c0750800038503030003034002c0703101050320503014a901c661070030402604128612034110b0428025005032050420103075100c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 911267329 1250 911266079 911266091
    0x40509070c031209033e0d090605071a01090506030d140706021309060b1b010b030607051b010213060305010605180904033e0c0310020a0c0c080d020c0a03020303270301 74
    0x6002200c0f00c8059a070032006100c1114207542c00c280c0da641c104108a0f00005188c03010400055005802800d0900e04c9400c00500c850710349400d000c01e60000764400082103840790700348511420b05120152a124851500d4140c035030361440c0280c03035440f907000c00600c0e00340e0004450380c81e4554041d8040c003401c5584011701c280303961101050081e41124580011801080007009c0104105214582e04940d020340a00103070380c0c880e0360507a1a90400003050a02076002480c601d401c220a10041c042d00d0180d0744040e004505000c002030072039505800000500c88100509820f03a101901036095084c030440f841c00e40b940c0e42303207811561f80064a103140b66005d21410590108080403e0203d80c10f200c480754020754804401003140d80710080d109158154114041519104041d0340040046110f1402e01b46d041c0f15565a0b0303040000902d600007129078000d1281c0c58022036041c03120f40260201110021442d90031600006e0b101d100d062041c40d06064040100144000e00e41420224030b00014020888 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 911268579 1250 911267329 911267387
    0xf0f0e0601020102120703020d06210b0a0b10020a140f070909050c040f0914030a0e0f0409020a0b03011806180209151305180403050702190803040308040509070c03120903 75
    0xe908070070704816a4a082600106000da40b90044042a078881d00382d20f50be025440c0c0365200546009441c540c003464030340d211104107132282c03000c101c00e00461785d0003000c00110f503040c500101440054209201d810401c605004040b0009609090314008600000d0203410340c030b091441d1450000e03209810904003000003038442d100c1d90100940c14000c1000c8240c0c0080c4c12001030300c911034400c121021074200420840c2d5803d106080400240002d803001601d000c0f00d40004440a00690041386d60b0180000180095910540c81082001a008080c80803905110641044100d5610b0f0300071169404034001605646005040c440c1d42c01d625202666100d070746004100f041464000c1034020003055941090f50161a6984c0340b007150556206418140603030300f04084a203691450040d04200d210740481c8484042c00100000c500c9070300c005030b40740d24100c1800102ca50080500090194481064010940100c40c60032094007055001494045900d0b007600c44a004c8040407001515480311000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 911269829 1250 911268579 911268581
    0x307060f1103120a022a060109090804051e1e060405092806051810150908030a090306050108060906010e1008070f090b090c0f09060d050a150f0f0e0601020102120703 73
    0x12046d9001c0b1045500c20340c1c005a031129014400007149015408200104121119680500c1c0c1c414412050285001e50710000507205a80d0807011488240c1074042c852040e14007482c0c14400ca8203040840400900c440c80003901c0b50040d442446d01a00d80781d00013400d0003507496000d40b22401004459820402d503105d80c48e000b0a180d010b060701070003c51110050f80382410340c2c0c19200d88080e940c0c01806504200140480450a0000f281405220a001f0503000800d00c003070584180140d81b050300c541d15600b807c0d03003076480c10b90016500c0d820180c1405070020001c100d09040da00c052854118944941d40c82183d01d00c004d62186405025006000c68601c080100c50011500a02000d200c02c00c6050200031746003105803005d00d404101004001d015240d1200070b84011240202783c2401c0c212449400410b0768021148100d54541e40d031350f0012030915414160b40503001100340d06922a080152044607200c00f4083c80c001d07901d40c000000c1e11f41e8801d404071030815003031070170000341800c208202074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 911271079 1250 911269829 911269837
    0x5040e0f06090a0b0d1e021e090109090b070f0e030a06020c010e03270a0b181206100905220b07030f0908160f05060c0a0e0307060f1103120a02 63
    0x1071082042d40c001c140c80001a0280700c41c1038034002c1c040c9802c1441e640e03076690400214445422810702604000016a5641308400c000c288000d000c248600b41840c03c05c94100e20581024a001e0310740860702000c20107410215038040ca007400c000840b10001d54081d969501c03190501945803280083e541d040100c0742c0c029110190072003000b0b1150301c0b0034882079610f03030280c0310f03588201591034011070742e0407000012400c1d44034201420b007400d01c50710380c00c001d00c0c035070702c40c46001004280d00c80e48035000c0e00304240650b41102c4480054050350605940b00720110701c40e4403411010a0f1614041082c0c03115400d4841c03040c81c40300245250340e05040c074081d041100c0c101c0d10240824a0b100a50608030106c2c0141080782c5d44c84440d640c6003540900c41c0009040c01c002d801d4440c0f203c40108240060000c0254600900e110140151030701141c040c0203111100c00042503000b6040801c0400045800c01c04007014400e02c1d091044840140115451540c040e090411040e0001141442400c1016500030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 911272329 1250 911271079 911271091
    0x360106060f18050904030807050c0a080c06092802060c030a020708210a08130f03020105190221090a0803040308040b090f0601090c051330030e0108040305040e0f 71
    0xa003060006281000c030740b410b054440c06401a0039a40010f0009205050143e480703070290030842d081c00c903c40807051801503149000c6401c1440010b000c034596004000555000a07500020280d0342d94007001c40a44038a05084d04980c030311514690710840d80e0782c4040c1c0c1c0b501c848403800c40780c0b00c0e0300c102c900070b41d0b410b424400c00d1003501441c56500d203e040300d417544600945614502c0303031414445d032030200ca00c441c1c018080442c018001b2a00e10010320404a04003c1c0340c02035001140e81e041c48a040d50800c440c00320385d02d0040d40704000604084051422034001c4403403880c1c0c00c0240c2d595402849041014100004102900c00403c00c010103401861440c000c130f01030440c0a009a603480002545e40c0c1e1205140300305580450010803501e205908141000540c031b1500604000001901104401140d00031015074940d2840040c07030014005501c12401c43c5c40f817010820f000c03003030301c0280c5007002003070015040200b20740018040c18042c1017100c0c0200b400c0441d943d0180340c110b02d01d40180d0025994 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 911273579 1250 911272329 911272337
    0x209040e0f0c010c03140d060317130e0406060b0c01020301030b0106171f0503010c2c01080a2a030f0f0c02120702041b11070608360106060f 62
    0x1080080e000014001d000c1c0c51080000340310301c00740000103403001c24164104070100f060001c2c10412680d0b43d140030b400380d4000e042c00824400c0c00c40c913100380861845820030b540c8500034054080d04680444800782240c28041d0702e2516501c0783d013098009001540c01a6013411070005601105c2003055004504030b90280242c02c2b0303540d80311403040340c40ea25000743c0d91a005004401085803400c80b80c0c128130817024102d0441c0c0d010380d0703200040f03400e4440c54020000400d001408840e00d02002c902d058100360000e268180c00c1c4603a19001034945071019001401980e600e2554042c8000704200b07a101029911070b00030204600d501c002005080b1074a0025441800e241444400f1406800b589640444507006030042030100e01c00d440039034101d800166401515040e50100d50b0001e0810342c400105980d880c6001c5e620101e10641c504070080d401807040003100010810300e0700c401e00003002e503085d6501c0c0302c0151084500c211200041c0245c00e0301c0c420f51034030f60006562a00324003031134003d80302a15 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 911274829 1250 911273579 911273591
    0xd0602222c060108010b0a0e120a050118080a120906140105041d07051201110304050c011418100c06050a0518010902130203090319020309010908010c14180310020904 73
    0x9031078024100c06640242c003244e003440040c000000e00e10003415080703a040c603010302d40040f03c40c0065290845a500c06540c0e030059a840342c1800300a00803500354a03007207410400890803e076100c20607840340002c003d0401a07103a1110301d040400ba08182803603500320009100a00d0049402c00c5101401e01c03c4621642c645000d800002240001030000180000c0141908078500014004100709128000301a9542c50881c210514100d401850046010701c0042c44881c0115001502520300c03c018203100c0207080c01640e4450450b4008642d040c041035444148181109030280d0300540440d000600a0303080108016061035507030301c060b10420020311001100c14968406500300c03411600040d4202e07010b0510804a04055001160461940c03011203141400f1040c1804405500603041e10050304001650101903034007680d07400240500308020404481c1941010301204d401e04000d619100000c100890440b1400d1528060745a000d000e0320702d41d041c4d03181018025801003109030700c583d03d008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 911276079 1250 911274829 911274899
    0x10303120e0d090b0903011e0f24050120241f1401050f0406090510050307020a0f03020f100f0c080103020d03080603100207030e0108070e0d060222 65
    0xb402c20000080c0751910701c0410b051500003000ca034030a00d0a182c0643d00d40d2070790003500c481700200c04101d0403c940002140c003000d50444c81a01e40c3d990045500f02465103000007440c064050060440c2c2c0242048411610504130300b42001105030100c1c0d510b4007c1001c4421924107803006031440050884030080140d4030880c2c000404000c20110941e20700000c0c0c824401c082d060f1b0a00341048005040c4a03090a04000034000d141c0c0c4103410440001e002e909082000c0d08080c0e1448030402500d0604070704625004000030b65651000c4800b424482c0c002d00d030b190515000340981041d0a082c070051780c51120300702c1005400788c80036a4590702040e16116007044141c0c410301c80c06043e07950043c4220507100168a00f1101c0e042c02030001585406403c0c4095005c0802e48000c203280b0f4402d4480c101c103c0a440005812004024003100c14408842100c40072aa682c03201c014151360b20400068031015034590040030304d0034814240b02900d045580100d5a61590401106544246070500d46540851 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 911277329 1250 911276079 911276083
    0x1804051207081908161803050a15060b0f090618030715090f06022505061318110915040306181202030406020703080f0c0601061211070503070602031e010303120e 71
    0x200c1c0e41702600802011914802803141141000c4842d07501000f090741900d0b511018100060090700321003d07003800c2c1c895900300d191342c060f000080c0038205c0200d0420201079604611840781d820024480e880c002002140b00d044903c00c1030107200301034125403a0644800d038070000d90310040b5102000c59070f1840c00055051f0000102d0091b550154007600c02d2210340d803031680300455113403168516000010008102c0c3e40b40e200180038001d03125903038400c0d22890b2810302c00c0514441040b1000b15030402c0711590300503001004855840d02c0913102d2104070204050280914060703030704024192401d00d1136201c81064110001c080035400b400350302440142400c01642c3d20b110743d10442d009600301c171004202044411001c1c1c01000081d03090f003882d050300c00042604080c000d0700824080303600b031502810042c08034480d5070708540f10850000e1178403182d51603041d600d002301030008000035000000980c03540d0317280103244400c03c40d4030324081c01c40d610f0b0300d000351140100b4250200340d1803400c40704c0b040c007080c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 911278579 1250 911277329 911277331
    0xb0603010b0402180913050105161b0203070605090105070203010f06051908060609060109080f0609011b09030b0402030a02130903021c3e0115080303061804051207081908 75
    0x350b035450a100010729418040290b130006c0843d904107481c4405940811401c3c0070b024452056140c0600700c10070b009402401c501c0c40c8002071415902c04101c1400140c8002940b03d0075281141007103600c0391a002c004030350a10400c2c000a41550800140c00c850010742d401000c26507070b00700c40440b80f042c44103614410342c0300d25105820080c0d1014001c143c0600740814066003100041c50204502500e5807140c601d01031103244200100e501603810000c08038028841e440da1041c0ca4003454014107095200180403800350f0002810310b0581030040340856030204040a40340d9805000c5d45c039030303892440c0b0304070040031501d0059016000c1e0700080088000074007141d030b00c01c0c801600c8403581003081c248558549020a079100e02d480b60342c4102208001d9420348a450070074034600001c5010700072082002c0301100c072540b00c1c441982c000e00501845036034050850300921a05031142620b603449040041c40d00d0b6401c50415400300307001801505105080004281015046900c0051960704260454103444 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 911279829 1250 911278579 911278597
    0x5040212010608040f0f0b0915010b0a030203250f1403010f0308030910150513060f120309031e0605070c12200601060c1403040609060c080d090b0603010b0402 70
    0x408034014001c5074020710f4441d41160152800b51030f406541e5a6040541940e060700362000c1803528200004948108407515200a6040d441d9a80f545071100b060014010705100d82c0c03d158011000400e0381d00152050311810b1690203040b0010001e210000d0540351241c10050300085404055094ae010441c0442c0d049654920351006854034503160a24907800107842c203001c2e0300598603600c05020250180c03425020b0030070240165107152000700150b14a8030400989420f0510900b0407514a1042c4c600f01100c4082d0265031814100e803400f209c8440e4940c01c001d0640907134649042c080b0704410031421080384547c50801c950b4443c048242ea2804041100610b95110382000188a51199039502c1503583c200304c5200030804000310440c00c04031700340c00120005404110711014410b0380304d0f03800c1c0041c52410240d8a444c1c1000c1c4000c002c08a5802103c040c0100d03203242104206421003181c2116000322000c0080b60f81900e00009200001d5664034400d40c2003052848451400d8400c03541518 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 911281079 1250 911279829 911279857
    0x40b071202040f1a0d0c05250215030603031b010501051008040f15020408010f05041a0c0d0522050106060206100f12030306080a06090b100e2a04120c050402 69
    0x3803914107110710070595a01504148413080c481c0560200050040e810407072503544866445040c0c203002c0d015103030b402402c0c420f244015803240c50090788400118a01080035620750b03503501d80d291030100b40b641c03191540002107035501280d01c0c1a0303207606601c0701d41078038821104400c13525040a001c031544041030f140900020f4485003240c0c0000d0f011400b02440350741494016003050340e119000b5084615900400c0349150b1910704002c1000044d101c442408007100304600581e0600e1540c901d4140208080880c4140d0340b0404203031440b40c202d182c00c0712085076954080101035a460700c5406002c15100760300c0236104080215806440e0303e100007040c3c0c0e0740d11811460203890011000d6060744581002d80070b250365a40e000c1049030041c4035100078240500380104050801e4038080c0d62004008100d0300802d0304022007403080c2085103050f1900032307849001c10421100510780c0d050a0399000905080c43d90fa0018001504290781481501309502510f541040035645500740803d80c8610040c112200c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 911282329 1250 911281079 911281109
    0x206030717090708190503270a0f0f083004120f0c0905061302090d08030f01030b0a0908030f100503070f08100c020a0f1b03060f0506030114131406040b07120204 71
    0xca84803000181c00c2e4100807503011a808e10000c154511401d4000510340404210309000c100f0140c030240d002040f1400042020000ccd80e03213501a04403011103040440f51241c50114000b403004000c0d90083d10030760860754103601c0d442c580000b8200000108403407010f0316030030000e4105042d05c166441801c000e00600003000424203e82d000798031815601c1d5000d14204900d0022070700d444041c1d44039070950a011006541141401691321034000c000031500c40c109400741c40040c1d000c2c0107594006002c2600f0180f5512021050101885540c00494151048200000b26100c00c0c1c0c903680121001c000680360711030141d8071210140d9442c403040340701690103801da540c002203401844805407030290b2100061465040d207001d01c1c0c82800e900a880e450385585d95404800098401c00e5007101d0124002c11042c803001150b03011800700142280e50343d00701c00310101c05001229851200341c4422a0644039149014600500c06244c1a506400041d124841c0701c040c24110b442181c3c1903031814410700b220 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 911283579 1250 911282329 911282347
    0x6050a23010f0b0d140f07021e19060b1f0e0d0f02010f180603230601080a0c0e06030c040905060904031e302004030206030717090708190503 62
    0x20f203a1001d200c225250340d40720f000e00c0300f08a11145060090a40b240e0308144c030706040d41c2c000c0c0707010000c0c1e07030020b107200b40146a004545030000d001d8403440400c0154840b4a2010b04003c8010f00f0345410b200d41100d668009810019409a04404078007800c2c0c44e111001103117002800b65004240000030040d1051a1540016600421058001d40403070301c1c002146100004941200c8400795104402117511500c22b03240f0106158540340c818075184542900c1854244002810904003a054400c140e94600c001c51890b441035492900c11040601507a98a0405819a40c0359034814414a4080e034030b8100840c0f03443c070f0200d88042c09240c142c1d5032041e202004045004410039009404014051748203902c0d1490141da410185990034000c0f00100c4175008400003206175400004000603600010030650254002c00040d0703030541e501036403160388a41d0b890800743c9030b4098065010b292114000200542a1800079820040d504414103403204401072501e0145003a440d0313580100550014450556 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 911284829 1250 911283579 911283599
    0x1409150a0203130f120f0f0203190e180a06080c100305090c0901081005090304050312070203030f0c030414090412030507170a06080f152206050a23010f 67
    0x14000c43c280c282c98020040640d13500d03024510101007100c12504100ba8100038582040e0b501100c0329440c00c009106600b0300720700135103078440d00750300072500f0a81020690382103201d046d001c5d00100c4081c2030310700600c8118501d6610082e04941034004241402c0b00481d0105e000300d50003410304006421754610000c000c40640c080c00c8004c100403d1072181d2030360b01d0000d51303800c102e130b6008050303d0001d0440c103640d034800407054400c02400c400240c1d10400007004152000100d02c078504109407500f9480321841c1c0b001034114869040301401c55a00800e41444801c0084001d0003260300386e210b2031500c40c1480c03051202180003124040e141400c400c00b5009200d000350040c580c401003a1501c04055100a800d900c0c0441050312a90b03140b0703607540c1c403d2121a0080110302d01040007440200300f2400e18114100003608010200c0c1c0e80e18450318100d6920b0841c1044050940340c0c0705206110a180c000007400c004c5c1045d4040510024800c4080f0080030010600365069075034000440d0112070516400c19 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 911286079 1250 911284829 911284831
    0xc0b18062206050d0e0606010f030207060609060b090901090c05030a020c0f0d020c0a050109030c1502100608010f110c0a0611120109140705030c09010e0d151409150a0203 75
    0x80c1d5140c404a801c10300310154154038014160a488071525100034840302801c07940402c01102e180c0d84200107010042e82c1041264400324007074a805650380000303140540162038a58410149141030802c0400e10300e05440103007280301801e407903140050780d0380c102c3d45c0c0a8440690400700480c1040020a14110007600200207241800080b83da24407113280c41c40d80340c170a003e20700c0c3e801a0002e49000700c1c1407030280e48400c000c00b024a00510410708603180c107001241c0740d2207480401c0602d84001641c15000b03215001c0c0c2e0740030003507081090341c1c0e5600d942030181000d8801140e04a10304455056520080c000b03a80509130880004d01d1407046a5440d200104403035044500e040344144100c0051180440742c290180820080109800601c0e0340d4810388944003070710000a1100500c02c02a600d8071440c140c51031280b00b441c0c10460384c0441d42c007180b6140c0c03903540c000c0e00c40c20603c051211400c000d600301802035041503214441e00ea49404055481d0080c20700f0741d17104c000481d4042403010115402075 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 911287329 1250 911286079 911286097
    0x3010303271a07020613080c04270302010b09010e010e01050d3c0c0e0f13060c090510020d020d02030c0c010e0f090106080f0c0a0f0503070315080a0c0b1806 69
    0x901d2a046a44d00000c40c160420010140c2c403c09031a003e0080e0b21061003103070740386081518180041d400704603c04940c400c107091007480e1075106016200926200350841c03441001c000e0309040c0d0a50b180d269010310030409006c2d00007150350f0a8000101414400340b660183c42d0440858124564204440b104c0c1c0c0380c280c01407507655210b01501e046a42c8202c9a44c10005202c3c045001c00c1ca440d00c2c50307031351a0010040c441303050700329040e04002c0610144042904410340c400000500c2039241e03101610842c6540d00942d030016003802022000f03940004000413030204c944c08642440c821300f44106c1c1c1d00d208101c002c44c002d07081800003010300e50083d004142100401010094111810700104031081c01c01d03405400002c8111090181e5032900001103504041214080740c40c04a4404010302510741807070b0074808100000000038000c0c1c0c8030360f00210469000c94070130131807280d9840c0c4c0161303204458401620011001400003903041c0101084520b20708503410002e0070480e01c1410081c0a0300103000c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 911288579 1250 911287329 911287379
    0xd1e05160c08030f070b0a020a0c170c1b190602071a0403080a081e010e04080d0e0a06051008070e01050103200307080f0a05060901092f0301030327 65
    0x2c94501c0e002c0c0007604002e07a1182101e9140d0007a401c2c00e02c800c05000c4c1c404100d1070b00c100041d280c403940c40140e0103011500305444810880c0b100302c3c2010704d4410080401214041c1522885090040300d8030b03604000000c4030880c4044030820f01c1c002041039039108001c05640960000c21040000040e54140741c03400400540c14542e41e6203a45801e070b444450250f000801d04020010248240d2646000c0c0400b10501d80300c0e03d604242680c00c00001c060f102500307a00313012400c9100c0881682040c2c03001c0e0940c0c0140ea42150a41c60b0007802b420013550f2100004c2c0f05200003150040c800a1808201c64104100d1034040e46010700640041c61014801100c030601075800d0044c03001d580c8002c40c0901c926560315003a5181080300120302000107041703100c4150401c0b0500c01a9076919000a0644002c504009a00d14000c000c5248680c50008112040074100500020a0f140040514101c80c081d441e100c2c82500468080c4021034482002e4280e4038200706804d00c0760000441c010310300c8150541c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 911289829 1250 911288579 911288603
    0x60a051c0b0604110c030309072907080d09060c0f020a081b030702123304120504080a113303040807081803010b040b1c06020d0c020d1e0516 62
    0x1140080c103a02498010300c460340001f0a00101d00403c01c1114024155000041081c034141d1200510002c4800702c611804000030a00030213000c910021200c01a0880f8070401c024400c9281ca10090404ca43c0d001d80440c24144042e0790b05130004c40c1d861002a03020110604e0583c0403400003440020300c1c1e040038801d210038010341006850703a51101d251107400500411007640c0c0601c280ca00142440003407500b500009811a03e020080c124154005030711a05c0c80d02a881440c008503400d0059500490030341c8605503040342072010300700088200440a481c4c050b003000b05220180003c0b003448401d0281185599813041d92245c582c000355800a115035440d81c688a41e64548410a40125010814034415604604c1780762900344601c64012a05907424002500020001001c4080d20003845a05599035550b86042010aa0444200e0841454100445c0c032000d2002552a0b110f41303070000200e01e0b08002590b51046540600c3d0003202d41d0381c0c40d030340760034207078070307100b850f104007040210f41680d603c01c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 911291079 1250 911289829 911289851
    0x20412060914031b0601060207150e0d1506031a06030604081e120702060a0507140904060f0e07080f01050f01030e101a0411040e0c07021206010905060a051c0b0604 72
    0x80000c05550b440101100f00401300a1300083c14190180c2c03008040d94003001040000b8030002c0d0400c1d2340300c01d050603c4110608600040b0348111040140100006503590320755a80901e65400305041c0d902407410b039842c00e541c501620026980030356900d540b561000300050f002a454200600d000c98503070b01544e074001c02d0401c01a243d500108a14092507168400b004403003903040054903409180082d0a00c900d09080c070f4094600104441d080d40c5000c00090302d0041511107800120090038200110410382e030ba1800380000c200016100d00001a2504021483c5944002030540c180d43e0000c00300d0000102d0000150014440100940d15602034001d0100280f01d01d03101d03004444011040c041c1c3c15182034410001201c10302c01a454840340180401c3c00440c14400360309a01031030003606241d03174120341c0c00020b1280d100c4413020f00081c81024004a80b41c0074580140d802a0419a82194140e4607072080040e6448020a02c0654034455140480468000c904140d04914003420000b1051071036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 911292329 1250 911291079 911291083
    0x80414060f120c1303060c0f030213061d06030109050907050d05060115030f0e060702010f022505150c040801110a23040807030f020f09010b1b0c040e100b04020412060914 75
    0x1581700b55000f83c1c1c0c9005480c40d107900100380f100c04040c03603c1c045207045c803c40d11030084031aa03802440c0030860144070101c0c10504244442005900c0200580e1326580c0d0b0365001c8000d080104d6005070540618100042d060400321080e0b42090780c42409040541e0809403d002d800444600c024205511442d140c2c403251980c0c402c0004680b44580542401e180c83c410180c00d4440501d00b03208c2443c8104184441d91409a01c8200380304518885801040c403c0c0c1020381c6440481414030030000d84400238084c1200300c400042048034080720084c4001c03009040902c000380102920880419010070301c00c0310340e618440c0125110517000c1051424241c84828103131401c159a0012950800050100c0096207030038080c03001e8a0310110b4040100d98140b00c0801e800703003d4a15030700d00c01c00348210b030402c1d8a1400d01c00c903013580c0400781042004e1010b59008a5985407042c40208416203012480481400d0074000c5409a405290054501d000035a41d00d500520000b44c0968014001d066481c04046d41 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 911293579 1250 911292329 911292367
    0x30604031b0f2604050d06050901020918101509090504030c0c08100e0304051005030c0405100c02040e0d0e060a17040f1407080a120e030a080414060f120c 68
    0x2aa00c50022481459281680c3d4008039002c1543c050240004c100942d00c0311a4614a50b5000b100820036440d26411640a409800c108950095407411800041c400240d0040d11808941100f0070303600b80c1e254606003404403c040c00c0384c0090a08034042c803101d01e044d00119040b9101389468a03002c00f654a4094038240680c202c01e46903040014104540151070166100c11020600a9403825280a00084200e1008010002480f2000c40001c5c03203840400d05840040001400d140c210001c24030008109151a40007240b140703103000003c4800c941c0000703a007482d10031240c94400b01e03001e10200b004003580145c9082000c0001c61280d10a45015000303030180114841c886c0048001c480d0f1910b8070b5a441055800c0110f98011001041760f01c400094058034a034000f10200020340d075122040380c01e20942941c16405100b020701503010840c241004200b180d524050445402d40c801d020012548512040311440800034860150408116070310183c0007000d070300099103090050315010350304500c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 911294829 1250 911293579 911293583
    0x5031306021b041401060e010908010207120813021e0a0b041503200d020711090412081302060409051f090905100204061b03050c030f27030604031b0f 66
    0x1100c030241101c401c2d01d109140c02103000701d5003404003c60103c0340c1c24508605101e00001c011446c000451705074041c1c1c006401404410000750750702c2d1094102102d200d020110106d0010301114002016245c5882e07c03030b1b003107603030051902131940640c00c1038002074481d090300c5c0c0381d101103000000503400311400000c2c0b0003400300401c5120704a000d4103014048400040c1d90500907181c05164040310741c2002c0445030942008400162034140700d0a0188080400340102c5400a00c40c0d41480b0920066081082c4490f030b45580d14201d950b2802603451040005140094210a0621040c41416000d8000b103a001510307004807021201000005d10301952541e020004039907440c1442000d200b4144000c0c0001c0d42e001c101540303414504400208008145400444400410b1420b4000c04d4411340845030401d801c072007140e480b1010300c907044480394041d0207003404502c00b418a2401014851511000b880c030020041d000541d5561801d85100802c548522010b0b10800210800529250b449482c454 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 911296079 1250 911294829 911294833
    0x11d04051c0c17030705040e0c07150b040f0e12031302031c080a0c050403060c11010c200703030e0907090b0f0d050603010506100c021302072d1e0503130602 69
    0x2842d14100700c0350101c0b0040d01480c91074020420004c2c91900042100e04440c2e199503030a00a650780305d0000d009000e60000200003074134242007016540e516820003480014200c80402122948401500403200c584281e80402c0d0002402410b03002c078800040c1d58802c0010900d480300c10082d900003410030850791400f00c0309040300081e40800c0d0303501c442c07100c0d0301c1903000c001000204150000505039004500c4014000d5456282035070b2070300c0c49440380180e10318609000707010204040c074014205100c140e07840700f0581648400381200d050300044c61400c99805440c0c070a44a016042400701e010703801030207042880860307140000c09180810081c040d8496a444940e103038210880a001031310005400540b0980c10301d03060003d41ea4901020441c20821400c10715484403036480414a01c00c21003411107445403001c110301040c0b2440d503582d00c0407148140b00c8081c0748480214803000c604a100c5020b0550003020440c0a02400d6400c030144006000f441224100f00c0140c441c099021000d0300030078016 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 911297329 1250 911296079 911296097
    0x9060c070617070c080c030714031c060302090606070528020109061e1d1e033013090213090c0906051c09050330011d04051c 55
    0x1d64800000500d90280211035140d905040800402c140c002820103003e0180c0001c403a08244401c10440c0c449680c882d500241c0181010b100c903440360060038901900d0000c0000b850122041440743c0c4041d2580241001c0941d152031040c040710b83c101c1c034000c17911032040d024120b222045810703c23800991a4900402d03003d070f0b0544001000c2c0b0010354031000c14480d410542200305008911440124a0fa515014804266074041c516254401c00017058025442c0c0108445403100304214041c2e540c400c0d021903001401400c00d050b00390020100a606000b08207032042c4441303a40b60b000b8240000c000340d05002c0c085d1101041d8040340d20000e088141342c124140e0401200701140502281d01159080c640886458503034003501038401e4280040c0c02c00790350b80102190340560f41c000c100c174941010859031031715808000e2078200c896000b20030103050207462144c0c2c00800020f00c10740c141c03031500c00001c54002d41c1030a0003400c0500940201c1e0340d4080c0072320003880000e555600350b038490848c2d660080340c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 911298579 1250 911297329 911297339
    0x1f110f030a20090607020409020103200301080f0c030607112a04050108011a190f080d1119030c030c02060c0c010e030d05031807030c032001020d0e130209060c07 71
    0x400c100500200c0c1464002c0c0440100c9555040c00d448505e901a07030003185054040c030040300281100c105400d10b040030341c1d6506286050260107981642d40c03010803a00800b0a0081a507a1100c1c01c80e0b2156065001c40c00098515200b1000d00801e040d60030b040350600b40c1c00002c080c106180c41c40e40146188140f15000002d032030b050003628010103034007008102150780c640180140b1101c910269004200d000d00c5d40002c4500c40751581c004214440e030002020b9140c0c000300d911000700780e041100191540580505409000c2a00310187c80c1c0403030500000481c1d40d400b0340305803092000079003e12540d60590030240e15580003d02d10340c5015000b825002110400240508144160b414000d0b40500002c0700c08030b0304001165088010590035001e100d5554840a1621119400082c561400c0040000412070008860996009100102e584450304500126540d04e030002c42d0790002110320b4442c40803814180400c003002580e0b840c000d07240101e01030128144d036001005001e1164005081008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 911299829 1250 911298579 911298611
    0x1241428060e130b011b0507090903050310170a06050702030c0106030302030409150308042114010f0e03070b0c0a090914071b050d031e1b0806031f110f030a 69
    0x70361a00100d600f003001d0080c4a000a11061030a41b2250b080010203c6c0750741444810000a401481c04420500c50000360313180c0240340ea0070540309640104451321002c9488441d00103ca0000b4020700010490400d8940780c030400303040c0281401045d400204040f0040d25000e004400c051400380d001141d54514000c0690102c9542c40004c03031440140300b1003400000c00701d00480f02194500c0400069a807400410001a94248980140107036000440d89038000019001000002c00e042d00c04c0140c4400080490f40b2489461001000a40004005040c43c40e840c00640b030f80d140740785041c034662921400381d44101d450592045c016000c0481c1000301e500c0e071024500001d0046084000c24441c0569500703542e80507111a40c0080c103403900401b0100d0071465901840f001c910705c0080c004e00721640340c1d10341004800280c6c180000d1441d8009007040c1800a012900c1c5100c07000740d0361040c4d651401d410700809010200401c00300c4100000310304803100d1400f5500441541c40000780000c1285c202c50 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 911301079 1250 911299829 911299849
    0x31003020910051003150302040b010212040e0411090609131106040303091403030a0504140d0c1205060601020f0d031a0a0602100b0411030123060c01241428060e 71
    0x30003051b090101e0b02045850302a0380760100c950548020070180000d00040c0d081070a40c0c50381030b107026008640025049080c00c031980c0a14003503030011625a080c88103221940008550341741d08030710b0000114842c0d0100c80c5d80c03003806500502c0c0200d8005060360000d000c55020380d005600160340c020040c04204078151000071160390440040d4604402e101010b07080d4022031203100c400d4000d1103c0e100181c1c4130304c1880c545455024040040d41621803030705484200040300259403601c42c3c030340010311a500010320b01600c0180b030801411500d900e801c080303026000c2c8210414a03104104800311060b1141c10980c1e0280000350090500d8810300f41d400000c503408042210300c03403400e0001b10086e00d5041c0c03044906451000d42450743c4003d902c40480004603800341143e4100c41d0000d050352146006502404242895140c40f00414864000b00900170116000d2112401c45610003009140360a60170704c100c000c014054014108003012140860b00c02d00d030b000303002040090020001903d01304441d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 911302329 1250 911301079 911301109
    0xe0613020114040b0d09061b08130807140624090106121d0303060a0617060f210a02090601020d1205060102030c0708010c0306050603070c030503100302091005 70
    0x1040246006242864008619a806814480303504080c102035071680c2d04640140c00b050080700c1d96080e40a40320801018034003800d55100c0d00d4410010030400044100d8204c1c2107d0360388904558640303000305423189a00c03a10480f171051082006e03c00240303503040320368a0744021902811440c640850b0034422072644001203200d403460300c115213401c7c0d0340750300c1b0301415280e11b844c041c41c090402c55100740007000c100c480b490021100c4413024108050001c021403064406403664081c007566038600b0307907001000010307001000076a440050514100003c100e04030a800400040c1d407442002d0480192008403580c11200e604060300c000d0541c1007442d07910350480820302c001c0c903010410043c020204c1c0c10044188c000030b5110004100540e10800581e0f203001400c10035501d00d01c0c0c0d03580c5224002c05403003041c5d0005c2810500c1c002074514144041e248030b200242c5070500043e02c03d0350f0440c4c143d4401800400e04580e81c0d040800540c5175100c0b001d1113101d00344440c007082030a110403c07169098011030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 911303579 1250 911302329 911302333
    0x13050c041e060807050d09080c0a050d0f140c010207140c04060509090a020d0201020f0d05041e0b0313021c0302031e13180e0609100f0c14130302120c040e 68
    0x8020a5034480050fa03880566454141d0f00e0b090903041020291803440409009101d0200f141c07100110040742c3e60002038810307801c851084450400a0340d0312a2040d45403008146980150308000c0002070040511a42c0d0714001460002c0a070349061070500103100e0003509601c03159090381c060800d40301d0398001e414119085051458107100c920703981e18045078000d004418036100c50b81164020484000ea421010f4180c80348000b0f0080700130311a400c06d02c140000d0001c07910380c00000c1c2420340d4045043d18610100246580e0314101c410b00d800c89031500c12a0048681448906031581307264903446901c1c4613038003540e81c8039915a00b4803e4840126100ea020802c20001a00070a1500707405508491740003200e0340180c0c5a49400e500100642c00f04031249000f0581000102d080200b21071502c564254400c20600c404510000c1c11203807400820804641c0e1040d0040460300744901030484903200280140c4c201c0e8891780030419082c4054200c10f40303503000d580300100c1c81c9068061a10341c110300c980 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 911304829 1250 911303579 911303639
    0x7090501090504020916020a1527030507080a12090f05061f050111030d02030103030206011703031501030e19081b060f0402100c0c080706170601090b0913050c04 71
    0x103083c49002900654002d80401148001d10380280100304040d030300095905278410450483c040030744228070002c0c1e032104003521000c0003101c41c1044500d5aa80659400e400c0c0754480c0e9900c003050340030203130040900032680c003401c00d151858050b50100a20928a40030600c0040c038140745413180103400c400948110038100038604e054241a01d080718800d00c0c1110603c012010744508600c60714007204c0142d40004008820b1540000c1c00b903040b030f21492140c0081c00489501c568484c0810364260a50313602001003046c0d10b41c440e40042a13165451400c0e627095001c00b0014443c0055208000c03075403610082a141c8005d084040f2040e606175082001e01010f1900b220b104100e040000c1c00240300d100d04010402c072840c443c16411900c9030748043e2449001c1c1d00d4800d01540c4842c3c074800c400000c0d0a18040b000303a8100301134801d001d2401a12292845810b102204044e508165015500f200003001c0d0948045410b00883d4000c142c4544840e03515420440c070038217048100107404031030342d400340 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 911306079 1250 911304829 911304833
    0x50303160f0302072607061b08070804030e01030c1205090601150207030b0a0f1b050d0c050403030c020111030c191b260111030c090f01080105060d0f020f0c07090501090504 76
    0x48408a0a2014041e10f403048004c10905c41c0c0f10340102c0740081c007040c0c5404000d044d014411003c00b414804191261350032640d5014089500c12812a03000300041c00001201c001540240c001d800025418203041003903616184405084a80c11a40410346912050040189103a02000142c01c0d118a2014000d094219154861140009060603101e03a94842d1900000040c96000c0028900700e1904521920f00b240b10040440c2c05c0140c0070b0725554a0100c0c7d14201d51301440c01c58084a9054860440710758a9030015900107480c10001d1341a4041040101e07810003062003002e50810208810408070751044c00c11034402c200c0c10b000c50607820300401007400340c0b25503049010800486c8100b646c8404c400c000405003d032550381d80141c00c41001006000c80e14044101512280000344c0300402d0b07508034140111200a001c0c45481d402203401c0221003850714094000c05000c1188840252404c003500c82c40040b19440641107510319004030906110611031030142c24010402d034135060240781855 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 911307329 1250 911306079 911306093
    0x307080c041d0903071b0801050a0b0d0209090f19140d052502030a030306050f04090210030207050102160b07020f0105060307060f0e030607181d04060b0d050303160f030207 76
    0x2c02e140004101050005603400f00100101d554480c4d01540700c041444401d24a81450003146c010b4400315400c0c00c0026904000902c20f400204c0c4006244113441c80342a0240082e61030054414002c500512110744401c02e41003180c8914640d1101c21411101e1990401c0a800450340050b98943e8200364620340640d50302c42c0542d810b6080d4220307002c4c044920958414404041900300a4250055800c204140341e00b5500c500304440c010b0310388040580082c401c01080781d05004000f9400000000985010f901c281d01070001144260001441c1c00010310b0000710b00780c40319804841d04d2412000b00041c40303505101e44003070403007090028019130500400003901c400c0c13140510000c012149215001651041a0940b11141d024050b680103050542009048030000803550700d0344001c947c2c0019002425a4084c0d0240307141040c1001d4503181d9507507540240c02904032140d0305c031412000507000305c0c800f80002c40c000d0307a05d51480c445030711115801901503e000140e400a00d407041c03114101081d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 911308579 1250 911307329 911307359
    0x606021203041721180c15030c0405060412020301150807030f03140307020d0f112a2805091e180a14250b031314030307080c04 56
    0xc07001002c81c5842c2c1c000689511405100714110007103152150000744140890b030424081e400301c1ea0442c825288012441b55203542620480b80c00c00c3e0010000c41e542d805503006990811541c49903c0c0c0f6040d0781e08001034a94000c2d03000300319126601c001803000c600c1d00340710303240010001101c1103a00310b00e0111255101c488501c005001d00c0e80da0070003d010540b06407042c5c8402c0310040740003a101e0500c610001c3d9640c04a500c260041000d030001d14110a000e00102c64045000340000e0040d20026400c4c500604420f05c46c40040c00302407040b40e00c0da0f84e0f9080b6401294451038004141d0a001445c800300104010750000380100303089010300284908900460115011990351802e503070311007020b0700345203c10701c1911000318010107541c00f04200c41c14041709110114002143c1c0d400284030201d42d042c68025182e103459020901c0100302c44142480a16417141045d40071600b07001d1a5150081880304c903680344200ca80000040194903508544030940280011b002c040c180ba0810b0344c3d83e200301c94 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 911309829 1250 911308579 911308583
    0x1906110c010c0c14010323040c05150a0c0602040b03010803071b032310180204050a06050109051003021e120714090d0f1202151302060a0305090a0209040c060201060602120304 77
    0xd8030040225441c0d0194106e1680b41f20750482001284096000c1e40a5400003540e04880d01040c00701e001500d0f14190044002008114607031601c0d040c0c0141c020703542101c502c2011a005034082c0000181d054024020718001c040100140d65a28414504058a026000304c800b02035034003c10103002103001e003c1c420303200703056019690a0035040860038910b400b4140405203010350800140a908a035070038641d01c0351510a0710240402c0e11aa10b04905540c100c1c0140c81c0010000c5000704900d10704450500440f0080d828010f18080e0341864880d5041c0c0000d651030250f5800180c0700404050400c0c450340c1c0103d86241c485c0c0c0e25003800c41d241800e841038a1034244200360009010342400b400140c2890100c1c1e01500f00140c07119100301c042d46600041c0203691422446500041750041c0781c500100c021f580c014071007450a202b40b03500303500902c4040c1c441d09280c4a9071481c1001a00e035441a036020b28021121003207054034003c0000e003901e00d40d070099400c5410400384c06103030302d05860a413500b1913 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 911311079 1250 911309829 911309849
    0x32d040602090f0409060e1501031e081201090227090601050c010e031605060708100303050304060b1c0b0a0c09090f0b060d0506150901020303151906110c010c0c 71
    0x3060b0000019504140c5400581d44075291400d4030040080f070760b005c422040d002006641e4401404401e0706010308091002420100d00e044004503e41141840580c2580c460346005041008407580c803412614260080840d4660010708211100020030706240c0c100007a120460700c104898001c5002154080c0030507052002c04103040d04124003e401003103a80b00d1010850342c071030b18100040070800544c00b038251014040d590204045500c00c03400b161082004d401103000b801d140d594100d4040c1e200400641d50320703950b40c02001440da2450440440a0314010720140068214148440000d0340600840c01c039030310b04505030f5422900880c1d100100d80f070301c040004080040841050191241e1b80e0b40691181d0001190035480c256075000c64040c8400755525003108603140080440d6108a107082405680107000040300807101801c2006d075030601500040a6148005454010103d5500141d0100300e00d40c0a049015604001200644a0074070700b011040d041e17915003111800450066410070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 911312329 1250 911311079 911311087
    0x101503110c010f1a0604150503060a051c03090b03060a0911120408190518040510150f0e0906010c020904060222170c060d0e0a06020d02032d040602 65
    0x258000d403118a10040300038040f4544003c00c21000308210038003160801c2c80311240e480c40341403020036103080d0b07012008507840c1880c140070255282d0300000c04080c0d20a000301008107003912141c600c0700c408070460408001c000582d20b006802004c054100d4040024244100311903540d0b101c0000007244da0755200050f03d0244501d8804c0b81c1d00c29090348902c0a19404240001c00c1140c074028001d481c01c03002c04405a02c03e41100312010b108418902007005249050180f0034541a03201d25006101a034045214640d100c000000c041840c904000100d2440c0c0c00c44214180c004141c0001070300d0032610301340c00340b0b80800064980001c3c0345001e4083e000800005003007140750f81c1100c41007c20060447d03640982080c1707000c800c00c03850041c00c1d1600c00c140c134080520b020001e9403124420006252506200800450900400c143d44d0820b9042c030640b0b03080b1010840c030388014002c0c500c0241d8007581c0e03132425002d00303480014640c1d18200030b0f8440a624440310300c0c900d240c1c6500507500074400340e92 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 911313579 1250 911312329 911312351
    0xc0d0609050d050901020d050405030a29070e0111150f04031b110f0102061e070c0b0a02090108090712081305120609011d07030f031b1a101503 63
    0x20414110300406611569482140c0c0c80e40080240c120003c0c241d080710301000c11101c08441d14011803259a41592001040000044003a0840e1201070001d4040c00e03070240d100e00c4a040c1154041c0c6140e400f00c1c2c0007070305103107455034400d01540c2510301500c001c141420742c02c00c480e80c030900300030014801088107402040415100c0c02d119043c0440d030034030300c50b000c0e41d440c05c00c3c02c85c004c0582c0311a0b01c50b40360490642601e50021070564450103200040d03550300122406601900b800c024080410070180f8074030390000544040081c0e000b103900110060b1201c40b8a80090b1403070001a2000310940e000000c10080c2c0c071250070038100296071000d0f415440310141c21342c400383e002d101d400c0103a01404200004140c040006816885070301442c2c001e002014250300da1100b100d01000540e4140d40000d00c050011500c000c04078541035100e0b01d0100d9506011000280d1a401d0340c40040301da101c2218403459405105949040c2c000700784001040c90645004000d000b100b50b51140390080c140c41303801c9010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 911314829 1250 911313579 911313581
    0x105040e070b0d0513050d0905012a02220f0204080f010e191e03030c02100b1503270601032a0915150e040612030918021c0509100b030c0d06 62
    0x85c0035035201040314111203a9180182007000e040c080c8500040807400b207907001620310f40f81c8400d61702c0f620113a0803214180343c09100e030241c3c20040130550025080d04445070100288103900b00304080c0e000c010380782c60034080300500344004180d2994040c0e060603404800c012004c2602103c44c2001c0c58120f42d2900c10785040001c8000c03a0b4805400400d44c50150300505030980c10810300c0e07440c15402d40c0c034009007114640701200c1490105a800080ba10100c11019a0b14401543c100c02d1740b1018108541c24180c1060110a14000401c41508000010010030101550007045031004048a110702106014000c046c00446e01c6440451512203549110350a454280c120160411a040030700c803060100c0050000107000407010300661400c500024404164220b032010a58155590b000e09454a50964446498500c16824003507081145c82680480017a14110a0943c0000440c240c54245041c0d820041031090054100d400c0c03a1403243c180d0703404104c2d6501404101d91030f049902d0b840c00c281e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 911316079 1250 911314829 911314861
    0x1216090e0a0320190f06050f01080c0d080c01020c3720130506010906180b030603030f071109060d020a0302060a0302160b1f0303120b06120f0105040e070b0d05 70
    0xb0070100750000c807000a002e05d031204407903054050403050000da2101c24480c4401c1409111f01906600308690300c00d90782c80e050f03000a0010780100b0000c0e0501d41031b00c0c021130880c0d02100d10110140d11043d03200c00c40040900d071120101861010100520403800418000060601001000c0e0702c008014210000300c5048203c0d1103000103024910030720050101c080007444292012800f250030014000703511803184800d2000d040c01400d4240d107503031a1034101041d40d000079015661501050000d1504c800c402c1c030251070740d603000b40e4030419a4890002440b5072041c000e4460b82c0035058030814103008d038440d02031000840e80c3c1940c0160f030700e0f401108210002d00070316440c0540c0030100c401450602c440310ba00079000302ca400c21080c44040101004294800c4284401008203c002d52007030300d0002e40b54000015008060b00051500c040c46600e03048445c0d0841707100807040e0605005010f141400d1007442c1d4000a1100142a1581070149038040c500483c05c86284150710341d800039100c0d800d419204 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 911317329 1250 911316079 911316103
    0x503012c04110a0b070305070803090a02030607320702090703021e04051f0f031109041103090706030e0a0b060a120503070b090d090605091216090e0a0320 68
    0x880300c504051408415024140a40b6446499442c9010581041d12001c843c20154551103c0e49814140e650300d03800750700300403c00a003d0150550321000b503103041c0f1071684a54426611050b040c40c1100310704985100c03000c2d101c0e42043d0f02d0301013540d10400c61001c84550680491b402803480c1d40d220000c8010f8131400380400400d03800380381c24910b034100c200040c0082d030348111285101030104014007803081d0b10400d8090005991500c1100d4198003d5000c1c050449175019a0391500010130049410346035600782c0441d0946e80002008201e0b00140540d02c0a8101841c0c1408071522912405642d40f2060790082d081006281c08a2010307940d42c01c004d0001c0c0141e41440c1e0059015060540d186c0d042404160b4503000d421000031600440070422441480c410b8a070b0b0250310303040c19800c980c6500480d00c0f05802c0718985e4030070481180e0070410504450258814202c10500b03240114050300e01d175035164981988000c45540c00241c000c640c40e404140c80b0102d511041d058001024940760f1000ca00c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 911318579 1250 911317329 911317409
    0x151208072402090a050612011215090803010602011416030b0607020a08210c060106050d0b09150a050423190212010509011d0a0e03070203191b06050301 67
    0x1d19001030886801821240d0403c03074488184c15640ca0a10038244144584141e000700d110005004040044100c00300300c5005202e105503203d40100c0c0b07001250712140702a03a4070000403004100f665070900481082c400b80ba41c40407202d0801d226540b10f10b000071742c441d005054403038803020780980702c000c280e8001c1c40d00100f5074400c2d60780c1c034000303580c45220040340111a441d114005401d0841d00da001c44000d500140c004103c5607290440407240e9400c0120244142a2280320042d41a0740300b8045030f000e141100c00c2508079000801c10000030103110b51000d4040c0341446114100c95021403000006010510f0600344c0c50350b60080000f004810002d00401d0039413010606030022000b8119003416187d080d00e00c00003598030783c03403916810420b40d41013502d05030103035000404041c07191704080501403070102203034107040c3c8560000e410494629800d00180c2042c040b88400e10210070310301001000c80000155101e404c2c91030050852005018811b10341d4070400140e0a40000f510005a640c0b60080b6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 911319829 1250 911318579 911318633
    0xc0d12020c130e01110a0228020d15050a09021305040c080714010f050405091f120b0a0c0513120507030c0909020301140c121f080604030315120807 65
    0x441c900041c040d05400f44040e6203400c1d900410140a801183c07014000781d0001c03c50005104542038000ba840b43c102c2c41841843d800280060700d40c025400c0c6000d00c03569020601000f0005a40111000100f010384018144001480980c444242c80424442d008101080c01d55541c10046040c00050348480b48900c0b800e03070002045400881400724810090340c0d454240100480200c406000f40e000c0ca44c1d010032200e020881481d03001401010003550440c400e03040c01c0d924207001650500081c0b080d1380c0c1000800c2001403590441c800d460720003c00c0d08115051469880c82058400035034050103108004045010040c00403c0040c20021a400004044000c0d200c81440018004240c8228000d40c00c0403909001e1140340411248100484010641403620811002c035030710b1000740504044040320b80340b4101040640d502c2c40d014005000080a40707041514000703040302e48068040c41640303011102844850481414841100d4201c005d00d0b8031400d45040c850700440c200f1400c0c3c954044446 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 911321079 1250 911319829 911319859
    0x1060c0f1e0506090115030c060e011808010c091a03190f051512010504081603050708040e01030c0b0306010203040605032e15030e0a020607031b0614090c0d12020c 72
    0x80c010780705040d41402803024060210b06440300e1b0020b40401400400c4400b0140880c07403081c622010914414541b45c03100c11b44052803e0028910f580141d140c6075180c1c522402d0054000034003100404c44803603095541e1181c0341990009000142c050701c082c421009010340d40001c9a04015582c90361070f4020071890400017403586100034483c141342d006141021440009540600c45d0500c510b800184d50381c5841c0720846080c0c0d214151210803018000103000b603d01044100e0081c0000d452424800d00c003950442c03c006842c0003203540181114281001003044e0369901000b0303182107410b00c3c1001c2d5180e449000f061511034440b0846201e04070b00010010366101c4109060f0400c0728009961504c3c80c1d003407240e044040e11103100314481c16034442410b080040c03c010000f801024000d203404107c2c01c1c0c54200702c00032488018426142651100c00d004281991842c4031600100310200400086007144013140860250305406041c001c40040b0314106280244609014040014074035a1a01071034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 911322329 1250 911321079 911321083
    0x1701050f010b030f15120319032004060804030918090b07020a0f11012c030c040902370915090b090f07050d050403200601060c0f1e05 59
    0x31540c808501564800001d0341d00c040c10308480c00707402180d20207001540e8400d00c1d2181c00c10001c045680080d001d00c041c4800f59030903c06401c65542c4181c002500d08070b50440142910307540c40544800030214aa07400032042c40700e080b80c08844032403c0083ea19501c505060318818010f0b40040314403a1180710754204000c0c25803080142d54030885c041c40803925241da040340d80d4454520004d00000001d42d940010542c800325146802c407051400e8500105042a130040341960a05424001c03042182292003d280034043d081c543ea40959003041100309030340000d038462510004071402c00914895500d8070000c0301800b2a48519504007154810382e503840d40d5001014200b21040c0740046180c070201c1c030607140d4012107100e0f031070060000080d030726000c00c80000f104014001c41c045c02000c01c50901d58020703501030148203500980303900c1c6481128502c00c0740124840010030050350032420040c42011307044629440c4d01608007400c00c0ba610342529207030304048098200707085010f401d00310450401c140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 911323579 1250 911322329 911322331
    0x714100219170108120c012a0e060a0816142d030609061e04050c1c14010b0703020309130905071a030a0b041407050c0706080907030b040c170105 64
    0x1c5550b220340141c1c52029400c0d04542c280100000c94002006a103508041d500180920045480c000200745c0c001840c070009440c500c00340380020b0215000c0d11501d198111b030b022006030205071011490315400403c020030b15003000b030034400000d8001032205040c9205140b5000c5000a90842035a5030201802e2114000c0e02440b042814580c55030132a0400034110080c1c1e07010301d0002c1d1280d65243c803100704000f0342c5501078130003d001d00300d0034080d450540d0321406180e024100c01411140d40341444030111400c2c03d4003580c1298030a0501c0320000001015800c85030450b056031200716117611040c030b822401d500c5440d203920b51242883d0070480209441354007495200d849801140c800c550f9411000b5402c051403407001c41403000500006c6c2588580d60011000400c0003000003d030703022600186401200c058030b1450020300b012940d0003d001040040c034010f03104030f040104c901e1805001007035540701c0ea0b000c014680c5801c080400c0400c800641c035507020b05800d0784c0981503038039030000c1103000f080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 911324829 1250 911323579 911323627
    0x10204050310060b0306042d05040209060d0b06010503090a0605010b03100f0807210b0711190b04020d1a04031e08040b1807120f02041103060607141002 67
    0xb0707081202d00314030442c0718883c122412400d0240c01c680d100342c100001803950180f40d2842c6200a00d4054030f14152840c107041d00311040100081398240313030050000b4804001c08150040c0300b22800600840d0003800c42540c8000700f4a07169580b943c605881a0500a80c1c140c01000a42031030004283c141002014511940c2500403220300c155540703201041c0c01d0900d06c110210be40007030700288400340d0f00c5aa2005510680f4000008080301ca603201d032074a000444400c4005151500f500181103401d1004103d610000c02c054070542c3c0e000c2d211340c00b1900010300001d11601400c03031a03104100003007140d108111044c1d00981307204d00e4141809484a826040306507480b00d0b030039000382ca2560003803464501540e0042100c0601c0d950f80e80007007201c000011740b548054030036014000784143c2200d060b007500600c15458001c034000d03913105010036200310869010b003140707080c010845980c030b44005030b448a03600810100641500b0b035441c142000404490500190700005888a86410109620010070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 911326079 1250 911324829 911324833
    0xc190203091815060a0914040b1e011e360e010e1e060f0a031709040b03030f030f3c100510261302100c3f020102040503 53
    0x550f803042040010302c00c0380444c2c2e01080d02403109114011400051030345d400f42c0680f0002d64802d0340f2000400700e0044044201180102c10700c1c00c00603592100e885405004251445c0e0144509210040c1c00740e81c1d44400714511101d000d032401d134494280482040580c9840070761401d0300740c5034a00e02c804810709014020180e80190003203900f07020408040d1403440240703442110301d41c48540400c4024000802001e902440800004c80854188491703000d1007480808215540d2101c50240801c0e07840d00017000c0d105c4e400c00e00c110034513000b40c401126800516080050000d47d106405e907401494016000030004000705640c0310140ba0015511070112110342c5511440d954018964262420302d000e015040240902d000756068041d5a401450100c040540d581c44001d0106c1d5100c207010403200c50150800d40c2c10108258105441843d22211881c60302e5083d13000c07603841e4078642040041070305816242140301000003030855400c94100c07400580000b4001060100024040c3d0402e0064500c24 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 911327329 1250 911326079 911326111
    0xf060f0314060402032d070b0a11030304230307080f0a09140a23191d0f0c13120309030605160804081e070b0906010b030c1902030918 59
    0xc00d00000302144620f50042c010f0401c18401c440c03110844007403007070f0a4186c0507404402c86020f00d062220801038400c44444540311080103100409100441040706035a4104009010200d1955006520348034030342000e075640940e98180c0a40b85102d03505020700411381c041000400c3d25402001042c1c82c03500e6540307008005480c0c40e500000300151030000d951041d20f0880401154070340b921040c103440b002e40c4c0901c60011502000c205000c43c0005072130b2004d48194001e114221000b8140d803030107076014529081038135107900128034408001c1c01c000c60b0b2500c007003402c24400041c55034a102a000031401480391003034915004c0c1c00c075501400b044441604002c0050b810009400e00c40440f091241c2d18a04552a41d0b10f60342c3c0281e106111040311105001800020519030304000d0403558070421032000300c0e18103000392605000041c1c00c4600300910400500c103a090085040d10a440f140c0f0303900c0c000d02481e5003400e901c3c51084109403500021084100e240600d0f04d009000d1103103406001a803a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 911328579 1250 911327329 911327363
    0x1051504020c0307031809110403051c0f12090f0b06031b01020c090406090c061e020d0504060513170d0201060e061c1a0a020a030b310f060f03 63
    0xc0c1d000300c02d59840940e00038031558002c0b034400c840044050381002845012030b030312440440c0c20b860320b44000d5148403000103010070030001c1c01c204c407000344608140c1a4001519541008200350070074246401044000b800345490781100ea404003c80590211101d200e0801915003600051400c0f202d81e4801e000b01c200c24885062040603d01c4255030503405055045510010130841c000b01810607110300d5500c1040c01c000500817106400a82519203500c03400d030b032500030031000140d09441038204540282e13000a19644c1c00906880079106e5906220380c9941c110304049580904551200c0c1e00c0d000c91120b008200c4801195a10b140c2c14168000c3c030030940c41c1c3c00c000d4008407080e9402500000c1d80b41549140c2003d00c801203a04511845d4140010b0016141a00781c034001a240074001c558006241747c460364161003901030301c003410b4170340151b040400d01074002c40d54600d100040800800807840d4402d40010340c08065034002009007089805c0c0c4809200034440b0320380c00100c810300c84c3d0899440b8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 911329829 1250 911328579 911328581
    0xc012a02190c0618050901030308100609030503040308032206151d1501110307050606040506031f1d0708010e07051f051827070906080f06031203070201051504 70
    0x102054000024101440c60410120b507880700c403008071003200b041c0c070030086401e82e43c081b50180214025559116241003101d403a0341c5054a9a10820a00071840d0082000400200940d0112a040903110b40c40c1e40c3c9105400c10030a0510003410001030f00381551604000b503580c440c030a500c100145d400340343c03074542034581101b00213810b40100c99030300c1400040001c019a0502d228022040c50169610150240311501e1600204812034079908080c003008103500b003601c80d1030740c0844102d000b070412210b4002060f5212941014600d440c503182d19205030001400001c05061000c40021076030029600d10040707000b0b0051084802d024000d90400103424a880e51551604008034003408200311512402070781c06a000d1510b4011482010715103548564484140b200790b010b4091001c0d018441d4190349450450000f09101c0a21042d0365040c4030050b489000298081040100031046407039a40000b441d203010451107500001c800803c02245540c10742206020f0303091b61800440d90076111003040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 911330935 1106 911329829 911329873
    0x30b010b0c010b0a230f03030c030d0f020306060a0c05210705010b030f07060804140607020f070605120406180c0909030e10020d050c012a02 62
    0x201c000c0000e0141c801c5102c01181c00484260a1120311594104040c801188016104200130410380320b40b945c5204501d0028116070311005030909923a070b65032240d45010101030508030405190001802900d01820009240e5400c1540890044a01c047c4070703c810b40c5e151040781100c41d040c880301c0c507003080000c1e0348007496a520f81103801d00c0360a44a8072080d481c00ba0703000307581020600c0f1012907110143c414a00e00102c00b501d0f181005080c50800040e003186030300401e01400405500025284c1910810380245d03031810b50f68200598041c02004c05504820551b0b900040001c0c0c01644002282606200800303102283c4d40c0320300a0fa1482600000c0c249a564003518043c0b6400a40240c108a8100c0f40c25043c10340c0000000e440b2500d06111009004004c030b00403484031029000030441c01d000070001e140c07030780910014034401d28110100d00b0150045030b03010002640020410 = true := by decide +kernel

theorem cover : BRFrame.Cov 911151079 911330935 := by
  have h0 := BRFrame.cov_init 911151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 911151079 ≤ n) (h2 : n < 911330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
