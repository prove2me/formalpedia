-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1741
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:30:37.051716+00:00
-- url     : https://prove2.me/submissions/c995308b-a97c-4c70-a428-a61b2e9c4a11

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 312949640 ≤ n < 313129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 312950890 1250 312949640 312949649
    0xd0b010e150604060e0405150f040c1e081602010606021209030a060501060507060f0e1e07050a060f021b01050702012613020a12080403020d030207030204020f1c0608190309 76
    0x2030f42c40303603034401000300b1400702c3c2e44807103018a15000c0828200707500c804540301d484c8800307009052610500c03030600000300b03410004042080140324045081c506141004031850319181d4401000d1f080035110400a08500e40c90301c800d40e85070103010800303107401284190696072499541900d6540c0301d80840c0c203150780040014000e42ca07010003c2100346d04003001e820100d003d0079081148180f007503822404c85105454421160348442c0c807008110964000d0900001907e80668468540c0c401c085400b02d071894000c180418140c0051400f03160f81045002104411a1004210f004507440003038403510424802904024a807418460400600c8403800d82c1503101c0d040129080c074291f0750b609240191400124419120b51400040360425801c000e0011904a018980342c20310796400c00c02000d16030341c400c90940c01440303400400350341c0b41d202030014911130b0801c140d5542c50b511010312510045030300b4600d0603031a107034080c08000c500051070442020b40000b140c00030341e5035040030345a0920b203501c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 312952140 1250 312950890 312950899
    0x51b070c081f0b0102011104210602030403080601230904020706022803060503151f18050403031b120c0908120403030e0904080d0c03290109050d0b010e15 68
    0x80042907400b0400041006002c208010041000808012401d0755144d0b0820001024284020700c1100025155991400381c10781c072082c07124615a8a40e0145c7c2c10803a02603000c01c40c01c108020080d60421840c6d41e80082084c1820459070705120112040d000301c030401402180e003c502d0b2001c1090f640e0464000c2d407001ca440034280d10712401c0504008a8002c0c10b400080d041002c005058140069004100d6060b00402096a5100882103003031024507103250140480300380002680226654001032006070150003c201032a00c0e00300074040d5200d021410f621441900c41d115025907209000e15480316402c03034041001181c1d1034089449030b503180c01c035401c24050315107001121986a8000c0086a00c0713621900001e000307a0301040450407080740d01070065401046503156240056010080724421820300142c12043d4060391900101e100311703506540700b86240c05082c1507801441d41d01c020042215000c00c0c55450f40d48504c01000c06204406e405119800403d0392041c03241d40303542c001c22002c2c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 312953390 1250 312952140 312952153
    0x31701210c03022e111e01020f18150301031e170c0114060103020f07060c14120702010b032805100203070906080106031103150d150906050a051b070c08 67
    0x40c2d485901ca01511000320304842c410b420440a9401780b6103ea5030480c624003e080c9214052505220b0040c031254001d445541c00c00544240c00312000207400c43c0e0480460030141590f4031000c0c400c000c09541510091507030f06100420008029664244c1004400c44000c0c80602052401e1000c0c0324080c0c0386100a0b6002042e0210405d030154403c2c0081c01d60040c00c50215210b06006600b2845000504900c281041007401c011a00300d0304548501e01c41d5250502d01d616018040310aa50018140700307c8240b402070500522540c24003948000e41c108401600300c0039020540010545440e0140c23004441140480000340602402200c5585d00100015540c0c0c0c501039100820824990040700041585d100000c0359140c403901c6000105d880c421348cd0f80c42e546a00e926902c000a015002551120f14101c2c01c40005001009400c00e4002009000c1108c10303541c60504140c1d64000c10740c4207140d140000304007034040e503015801d03510690b07100e8031070b501da400342085c2c040c0300e90a4000281030701c900d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 312954640 1250 312953390 312953419
    0xf0a0b09010216120b040318060c05060906010f090c030b1003060302030f0d0203250210050a0311030c0304020f1503090633060309030c0604060504031701210c0302 72
    0x40460034000d9090381d0b03070810380c0743d218045026140603128068a800ea440000170f10406001a0490302a0403c42c006121030183d16080c1e20721a00680005140034040408102007005004d8000740304802502322036052220303407820100c4511404500b04e407181d1040314854000d5003c0d24202c80050864401c040384e1075409801b40c06903103c00c034064415403035001d0101502081190311302903103501031494072400f411603881c0601c03918a00140d0941c070309041c0005a803008000c4000e40c00303540781c035500c50b00f200e04043d040f10202c101c0c1a003042c500b00200442c252480007241d1340b060b8121440c86151140c00c0c04640301c096407100b8240b20100c0001880325034071000a0852081c03500c442e10030200c400140100e00c1401c05420300b00103246058410004501d4100059640851400116030815500c621042d1038050283d07800d80d03000da030350070a2100f03040d0b102d06030b994804040722a0480075454010340820b0080c0540c038000d0042d030303819988130800008050b00340c000c6400515459588100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 312955890 1250 312954640 312954659
    0xe0a2301030c1b260f0307030b0a05030609010e0105060607020105040e04030201021e0310060e0f0d0215070c08060717010911040f0303021e0d0903080d020d0c050309070806150f0f0a 80
    0x10b03071102c0380c00100e480522000b40c1c080007044a4040c880703040e1146c11074480305001c1d40074149030141a58051104807002c034540e00c04010707141c80703a5681400800c212000381c0c00b00e82192400340070a40103150030020a00940d0b040800c8404980101c800340915035541d0800328020f00071286c4001c0d080b108074800031445883d841c0654081c1c0c070251846440c040e039600c1c4c2925550031260401e0340000403000700a11910b01400710504007400945030030500c040000303030b00c4840d60015008481e4214419401d00401d00300308009640054141003910001880850b01540c0040c1481101210f50303d400560078000f044500f0fa5009008001d50a0011a100c1c900a511802d52a101881a040f1701d80c405800f00000a280e41c903104242c1c68495140e410368031000980c0d401034a86080c01c5400304484064200a0f101da442110026684e9949030301741580c1c07440c1415403030350100c402507010806000402c030a405005108100484800704a192000042686080003056043c4e1001e00d4140c0014900107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 312957140 1250 312955890 312955913
    0xf0e0a050d0e012a060e030d0506060903070e1f0b0a021506150c1e06061008070203030a020901030b0a0e01140607260d09030e0a2301030c1b 62
    0x20400c01e481412104080445031400d0803068640000c0549401841d003032050081e404c01159000b0004040840325220942540c034080a00559075100040440032407400c0e1041c00d0708104102d8401e03280c1007696000903a501018015070700548c400c00f002c501c071502d00740e400b4011009000010040e065940000c43c04c65003000118001601071405a000719180405185115510041014080c01e99202201c0700320380244807a24690310845065241c14111041c03094045411003008040380e2406405004a44003c0703500001403000d000c05000c146038001c030540f03500407142c81d40181c44071010380040b0007812000003034540180c290000458484214400c06040c0c90045001c428a00080024401144281031001d403210003074407003503900c0d6004080c0084c07101005410403802c102404440c8000c80b1403220f0210702240c2104122442400c5c402040300080550038110500c60201a40c0101005c0030240c1450400d540d601c0240309550196000d110040c00c85814916070890510b0104019070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 312958390 1250 312957140 312957143
    0x6050a030501050603060a091109040e0703020f0102030a020a060902151803011b080114040605130b04050c0406021b1f200a080409050606041701020307090501020f070501050d0f0e0a 80
    0x905103070011506040000c100ea004d4a8042d001c160420700d01010000185034091680c030a004040044800d29626405040301000403500501540752461040211000350120114195001481020300351030b004100d01b00103d41182e8007150300881440082d4003005451100034002c44041100c0301840c84003850f0b0760200100391f000300031b83c1d070306204e00321011101010404001150b910040c4164001c42143c080546030140001c5000c5448100107000344420480c0011041d50380c1009100da49050300544c0e4001c101d00c0d003010303d8141002b40c020348900c19401600380c91620a41802d03080e85408103400344511044104440038a91410010985200c2d541002d0480080082c60385e5481c1020540201c1c041c0e0005540c1d03d0b00303140140007006888010300c2c0170b83c4944148400900e4a00a00e005031402521000044e45c901c0c10100c0035000c0a400e801642c1103500c0003c6195105400251030001e9940c2424035640b07914000c0010b20150180301032030360702c89050465a48980000042012041e03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 312959640 1250 312958390 312958397
    0xd0230070906110d110a240b0603010b072303030a090318150c0602070501090f060e071a090609030d090611031207050a1b14070608061e031606050a 65
    0x6a076004200c5000b403da03910005540c2102c91001ca0b014041c18078180741128a1080d00e0503509103807583d601c0740e411080b075085903100e00b8010f860004003a219110b101c1d0f1048420030b0665042c0390980359a409941001008402c19405101c1481440a883c00f0b0b9000540101c83d41c901d401d48064010306450343c0b0440c0800d01c00804544a001c1107405801075802e14841082058440f40b01128064000c041c16242c603503082090201140f801e009400003113001c0d5a000d1180c050910b050360032690400d144650f83e420440040c85820701c12080f5004088010110988541d039801c0050001c0c0700f00c0b824503038144502c0d01c0c584c0c403081d0008426030496000da11903003000c0f12414481a02d9104040e01001e02d03200e44c3d00029801801075010b0f0403040102c0c5400c0903900c0070140e0064041310f008005036081099001c820030088402c10100300501258a084850b5003070420106011240f41d814011030701ca81c4001804180d01d0030440c0c0c43c01d459100c2110403005549210190203035021b030b82c034100003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 312960890 1250 312959640 312959657
    0x11130b040609090e0a060c1b060204140102010b0a090f020405030f0c1f020a0206030a061701050a0e0106060801030803040609020d0303051e06010e090c0d0903020c1e01050d023007 79
    0xb012444c4200c94041381400042d0420741100d0755039400601d101d4151409100320917a203a091018540304828400317103e030030016501d504106000c03c842c06520b031303224110783c1001141700140d280d07040d4400c00c0f6000300c0300c0498040a00341040001e0f000390b0300702642612610702c0c00c2019100000b04103108180035154444444825540040c400900410f50f102591101801200600745480115440080b49800040a546034010006141040d00c0803460b141c0d1520244002c0d03060034451910b036140224003c1000c149000f1010f8001c01c01444081e11100c00071001030140004c5c1e420418585a00030040c9030915503503c4d01030000c0c00141c8004115840c0a04070308511140006890b0056605031100c6a80c4c425490070421a40c80c008c250051005d01844810680e081078042c51060911a0700503048640412062107400c81e8510b00050380840c0801c501c0c0e419903001012034042420301d0f0409a0754005129035600b4000881c65401c00244000501c1c0a080c003400c0700305402540c40303540d01982c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 312962140 1250 312960890 312960899
    0x10b060c07030209130f03050304060b0a12050607030501060909090510050c0421210c0606120204230402060d06030c09020405030d0c0b060d020f0a06110613050a0611130b040609 78
    0x110303c170340c8014003180e131386901c40d000f00b8042e5025540c018425400400c000042030042a00070070160f105540b0751985001d11020014148001d5500000c5480c01700300c550b25145006004144601c1a40300280e80d4034508000d0000034000f28a000360b18900503c418103181c070380301e40d030740d406840b8070f01024855600c650b005c0324240d400c101c0e5003a084014250103800c07800005603000c80f41c0c89072005021070605a140021a140181c0c0024a0101d201d413841500500500064422003900e8402280070b180c819803c070400d003103885411940540d140c5480d11036280f49000104884d030130140c002080d104c2c002902c024070b90000c009a0b00b0030b4040d542d40c0d00081e4015611500b0882c0300424045009000400d02d0500d20b0800c000d5900082101d1007642c2420041201c0003039a8000c04c001405407082c101071840100304441d00032055140560604009071070b4580c45030200c0800030645038640703030525602034080003507448034804084c0ca0417000ba07440b08180d02c0303071313205214503000f1400031280003c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 312963390 1250 312962140 312962161
    0x1502030a0806041e090503040501020114040b130302120c0a0213050702100f09020a090e0c01090602060a0f0605060313030305090a150207022202040306060f06020a060e010b060c07030209 82
    0x11100003107074840707001c19116202080b020f0042441824a0a820826010410355050041ca80c3c3c2d40c0c010009503580c1c1d030030600024299442c0c11200d4000c080401c041c0000142201007140e803140c0654030900c0b1055552904038207106190b85910311444002c01d0f0030411007030108036032220358802c8503c80e4aa1500030009401e07134104688001c0544c110340a10f0043ca40c0307982040301155044c4200003020000341e40094807c8885412484d10507a9a20403000140003c210313520241c07200f400c10b288810316120b0005d507603210040440c8222503d502000d80044400d412240140600401454803850401105d8040064400c8144c0021b030410000c11000200130603101501600144003800740b500ea012020b010754041c5400300d03008141d1402c4081003003d0f1000d005841d01202001580e558591b040c00c000381e0b01c10741c110120a01c041e4500300201900041d0914010398009001f1a5042c001c855003401045e0b2490440d0304100002400381c005040400c1d4502a0f074404ca4500c0465240c900e0b100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 312964640 1250 312963390 312963397
    0x51b030c04060b09150d0f020904050612250e0c03061f05180f0301090b0406050610120b0f03070801060e0901060311130b0a0b0706180302061506040b0307050301150203 74
    0x30030144042003121034a040051030b07044a4104c5c400340e103140a40c0e0303e1b0704500300d80031180c01042048d03020904040c5858640102600712070200c6144d42c865004149150b01d40c00c4041c0c5d072480b441c00c1448070714a0703d9651750204005102c2080c15086a14040740300c800c041e4400c8800900c00c80303900920b1892042d42c04101c50341c1381030903628642001415605102e030b409810704c81c0baa2104485401841c140d500b4011783c40098801d00103440310342030a103031041c295480988107911500e44c08545100096004039002c05000c68841701156203d0444081850701a0650714a034244c0034542c408200c9007030541010b002c854104240f4044c6981d02c1c90300d2401c989040c00020070341840002c01e02070601d07000900801d00341c0151800944000781c4400159000030300e91207011604004208001408801c1c4114444840c100c4840205801c0035074009403103010040c1170900c0355080105c441581e40b10101a0780182c0150168143d0f281404d4030301402ca5002449020400310311161640381d018400b1094 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 312965890 1250 312964640 312964649
    0x3060a02070510150b07140303090705150c0c090c0913020a2304030206030702030c0d020c010e01081506160209040501140108030415030b280e0705040b09040203070c051b030c0406 79
    0x3c007101e4500b86400101e043c6d000482c01d5485a00e00080b1440f01d850a00046014000103030051205529200c140300c0e0200e40e0340c010800d02d4005015604500002040360f04030403008407a040f42e43c1e651070f200c88100340103500100b900311038090751044654045034001c000440140e15020004600d8001500c009000302c0710f00e0041090a100800040c00e2900c05160001b090380180c03404e01140c0c5412a01d4007035030680078070060384984d81c0e0900c41d580103080194140b0007032809941c20718020365219014200b4100c1140940000190361600d21684030700154681c1c0d00600e142c000c0d003403500f810f0340a44030a2418136918071032000001200c031800011242140c95290006038000c41141061380109181903d040e000b46003500e21300c580401e070030f0050000c088862541e0254074204020415138100080008051220030002800005048029076200e030340d0851740540c2c1c903521241c0072a490040800001d00750b1003101d88107008003082a08181011405900f15044030710301000704402e0b030300a48603 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 312967140 1250 312965890 312965921
    0xc120309210e040b0a15020d120b09130302010b06071b06020607020a0308101d040c05040c12110702150409050c0307050304060b031c051803010e0706080403030b03060a02070510 78
    0x50300b00b441e060a80240d03240801c01000940d0240ea00d008011009403403041d6040181c101000100025401098851110802c50010000840d4400204001f0304002d45040e00180d48142c2080c1014400d4201c18041100941074944407581707844e0818510100054082c885204280e01140c160310024a0511800041d40200b51581c41600d081c0c40f4450701038012161a203059001040802d0710082c110313000d109055a419541ca494101401512600e801c11845a400d0182030020190702a205405007403d211001403102c80c0c81c10b840701e0600c10010000d4115015458906c200b101e410040d00884600f0581441151388054072031006200c1190150080350050001c50301280641d4003030000c050004d412181840c0e444d507511000d0105c01419040001c40001d107002204000709140b035200281139000b0b00c00101c40814036900c81c40c030350140c0030420040000040c1414400c1d00041c44000c030180036180e06091548030640654407400302590b2911035441c211a404100d4444c10766554000c26 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 312968390 1250 312967140 312967157
    0x507061b030b0f090903030f15150a080a11030601141b0a051b0109030809010302120f0105270106080601090f1d1503070603050702011104140a0e071e0c12030921 71
    0x11143d403800009041480380d61181c84031460a83c4520b500ac5c0d05d80742e08c0c0380b0441d40391010544010a40f103030003070140f44030038100410004111071140a50f0340240c000d0914403030f1408406103080380360040800c9151511190710042212150203c1d81c565158050310548824101011460380d0800c1d500b6800e078000358104400b08046000e0001600b56034505160262518207800a5207d46440503903090b0320082c0403070010421883e1180d8100a13920101c00e2900303c5035480001e1a1401e14144140c13410702c0406c200103200c6038421690344c0c0140446040380101640c0700c00c510485054001d00d1040e545007140c02040c404000c8040c00149424003c00a080b41810403a00320042c12002c1d0921040d9904ca40501e4502e949040140c00030f0140030b00541203480108041201601c06a1310241206040d002400810341d40001c11610b00c5141040d84080840c051901321403150074064007621003603110b800150210b91580025414900800c184c58503e07803100c0c41d0a04020b980c4002ca400b080101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 312969640 1250 312968390 312968401
    0x503010501081b0d0f060f150812030406020702030a05030c010507020c0904020d03030f0b0d111003050c07060e0c04060b310513090503030c04081513030507061b030b0f09090303 78
    0x80300742241c1c0388078505d00303102ca00d00d5a0320b03001500c2d07a000e488102661034500d0440c0f8440c0c0c010b80c0d000209088070050114460001504a00f440050b201401c0140c000642100313544040221460155108040726501d900f280300c0c1500034441500c8034401401400f010f5046454071000c1036000390703001007104152040998003075005041c02d01a002905072956000000e1380c0c1c0300d02568100074090321540c012210742a04000b104800e036002c500c02d040c80e0005002c541040380742070f201000c2d448070300003075490400c1c160075140ca00c00d07107141c80e4003c1c144030021034507500300409418080040800106c03244070241d8900002009600fa08614100ad03840401c000d290210810900581c0c80d0000108074966496a60441c1e000301d588228a1a00040c10022800c04111600005601c010700210030b081410080c5104145803501904020001c1800c04c00d00030b855200c0101c0480004483c2d01200d03004502034080c0c9601c2c0e0000d8411000c0e10015041e0342081d880c03040c4203d442801a51460740d41 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 312970890 1250 312969640 312969649
    0x405060a020c04061503050f0f010e0a02040e070e03161518080106080607021006031205070227011412060601270807090f0b090609060d1b0503010501081b 68
    0x58640c0320071480740c00d8811180b5222441200041d2845154414800d804448003405540004d0080a0f0000200041141c0114250a41c80c1036804403401402c0541f120011003000e07000e1504a8400d40d0415814010301940003001168140c60607000d41c6c846400309011840c40240a106a15401c02c4886858144520075514030410041c040148852103803580300303860865841d600401740c580c1c0300d082030100d59074042008a00010b081070042c04185d0030f40e030781c05411000c2d0320008802d001020607200f085644d80c024000c09141014001581c00f404009244440502841446003140003e44150708505140340d118800c0c8801138024400e580359036004407012869103145101d1130100759000c65003000c02c013100700005d01c1a20000c094190a04034188210791180c2c04000d1404c1c5402443c01007900c8040d103d0b40e001208590010040d62401c1c04540c5181010344010541e130495410340300303802d500c0d0f5a403105454040c0c00030001a80c9560010380d650080880e000000a810a808184da161 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 312972140 1250 312970890 312970897
    0x109030e060a03180506010305010b0607080703050901050403330c05160c0b0c0102040609050109050907030c1209200324090106030b09030712090f0b07020a030804060809060708010b040506 83
    0x180c0d49000180c130741c0a0360182800582011044855030045401042400303c24012001200c4088a5452400d001c5c3c0e601e980c211f1003401c200505001d004103100302c0c4c41e802082035800071500803403c0c02202120040c0c007448103106aa07200e90046448403401403850240c803424186907141d0b00c2e028a040000d001056002c520300c4c0c4220340003010020045080c94081c03000e0806001c0810015840d00c3c00e107030f005812800e180d0405070401504940800142d0b54110380300b46c00c04a1400d002480d011100b0040b20000c060703400244041e030401c2c10b440100a0410840c0c540c18220450100030800d465042503107400c0030001c1503100a1b01a00094070160200e0406604118420b00000c2c159030b41c0e50342d0170508182202c80a105800c04103001e4141b10140e40144250f02c203914011809600f082c07010000c005007030061001540d008a05081103440e6088103c001d542c01040c155150742c1d4070700004002d0002129054814083c0b040410210750150030041c0c140d940c10840e1038242414013043c003902c1e40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 312973390 1250 312972140 312972157
    0x10c18090b04020c030a0203041508040803040b062b02030105060603090607120b030703030e01081e070f020c0310050105120303090706080c12010b040f0e014b0509090109030e06 78
    0x1070f801c202d00b1030045000c0008020722852600603540b22880e054000080c040020700000500021508000010710317810102c1e9031041c2e100040d0070b195200d440104105407000740e501e036100486442081001c10490400c108014400c600900050b84d80000340155070109884545156001c00041030142c3d020309100340d01c8075100f10000075000003801c0002c0c41c00c1016030013070300402d074614181d801070751380300d801c45600101c0c0b200d51240750180340f10102c060150003020602004030310500841c1a80c42030007510034040c0005e045440401171501c000004020030700c41d20344515640240c0b91610040402500d100c0d0340c1c28000341100a10f403520581d6965402020926503000c01c00254503800c00c818601d0b4080c2c4840c00010352030300e0034254601e524291503003080e0f401c049100300412004d80318107101102c58404c8071b4003a28811242071800700080340309103e52007074803c5c88000480901803c20300000c4400446a6101e0b90b10b841c0c007428200d60301004090001074940c181d4074694100070b8020301594 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 312974640 1250 312973390 312973399
    0x120f1915020c12030f0601030f0902030a110d2f0307030b04110f04051510031505101e0c0501140402010210050c090a030f120905210c0405010602030705010c18090b 72
    0x304078050f01e0f00c0f5540d00c1221a00e13843d4540d03209002941d40d00d88600e1a0100141408004012240d00066580e48a00e40000c1107045115240c16035034440f030711042842a80003241c2d0004c594802c02540014065003607070000c400c4010b801413500d113400180101143d42201d03c03100c00342c980d0f07240e0620100313104904079000080010307c1d42281e21280f081c4c0b88110800100725080f01400410050603441c9408000100360514044c1c40c0c1a0300c841e080c2c4021150122500301d02c0c0140010140d0300500090f2007007142c4c000b103402102d0baa941101c600800c00d80310340000c120100da845045200f0800555000c0e0050f409005400561079280d44200d0300641c1c12461681002c1222001601504240d0400c681040c07800c10b1407010860510b00d060b48000060421086590429000c05d009690040c0c007030340c1003040d4841419645030148003441c0c00350700140c401d000d01e60f111800a9500d078001c44045500d03618290580e411107200d46080a0321800072100028401d10700040b0348003510b80f41c1c0324240d12 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 312975890 1250 312974640 312974653
    0x60f060a030f030536030c06030c0d09060f0c08040302070602030307090504090309080706020d031104271b05030412140306060c030c03220f0506071e02120f1915020c 73
    0x490700000c5d030a00e07401100f140c0040080d0941040c582895140e03080c0301c0c042c0d041842802100405007090310b69901c5c90250004441c0403d00b0300350040c000f00e01141020b589000c2c0c8004003180c2c00701116100e6030107902140e0425940300d00490b0b0704e21003194981d000134000f103824851454940c21601581d4064500700302c0030360b00c610074030342401c1c00c540c40341c4056407015000c41f180ca60140038000020b150b10031034034102440c0001040130034071030018070343c00b140d81c2c901444404c03120341d8401100c1311011080e00c81070104400000d8a182c0c802e0303c064802010f40404050f58a2045861100030003003c41040d0440d201c4c03000340401500490038040b00ea0001b404410b14100040001d401a46180e40c0c0103100c0c00e007450f40024100c540c541040314802d5440c44c0610241c0ca072402160720548d40030f582d142e10b404802c4a4841d5041400c06d0013580071640014040581d50001240f50304020008281e07490440750000e88401410150401091404d14003840d1902c010180c3c040c040c051849000d5821 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 312977140 1250 312975890 312975937
    0x2090114090114030f010501081605030705090103062f07020906030f07030b070201110f1b030309030a05030406060302130b03060624070515040c090f06030320120c060f060a030f0305 80
    0xd58209070840d00c015800600708000e4090401d407030078010442a0037500b5464106008901c170786105000140c440358844442003003132056140308000e5445000b410b00e2000c1842c104031b101907031042d5001e911611254010030554038021501d02840400038004114041c51661780742d5155000070315450965591744c0c03e606d1134860318001000010a4811201e036140a8481c0e01420300940e00040c1c0c1d110740c400d01c10003004900000c21101a401c080c00c003036031039960390700d0810b01a1402c1e8000a4100480400b2180720340582e40008000303180c1181682d050355201428040200d500000740740442400d681519900a102001484640c1c0918213071038580713103c841001040002901c084407100403645d0200000007851007411106a840741d010b01c042850340d10000d1140d0700c00c403843c2c00032070140c8100105040080140580c4480c02e60300d040e85640304160010348440e400c8a50f8202103101c10005030240c0340010294064031740c0921801a48001ca03241155150092103400304000010079540b00c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 312978390 1250 312977140 312977143
    0x6060f0714120406020727020f1e0c0703110f03010c120c0f090b090103060f14040608010603020612090708120705010e0a0305090607020a03170702090114090114030f 73
    0x44240110722100c5040403070039600307103018030700802405207180c103001c00d1010941c08200c0d407044556004003030061040031914030007240a001e40c0c00100a00c0051034440103880e03080034160030741000100d4170390390f1101032035141d062040c2d4180c52420703000508244005143c01c2c48100b103d02c07003d083c0e00c21641e200e4005c03e08403450403c903240482d04e1440810b0f4110858000c25141ea81149440071080c0810200500300c1040c43c05011302d0b14a02103000711a80c0d110b54400320040080d00301c0d486d2040d540d844403c07049030140318414061070034410b01242d619814042c003005c0300ea014009030714001b5801c804c1c00d0020b00280030044a030051120001d01c800b42004450803500c4801091030343e44003030b89401c600312022060495241e070458454000820340003000d8540d072000640e40c01c0d0ba42c0c2c00b28400220820010b0700010031401c96032000d1035145070b0900192810038400d0b5000d82c440c1c4d0300c82c84003118810101c9100e80d0b1000d89200103104040d4421100b542004c4041c007164003400000c00c0c8917 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 312979640 1250 312978390 312978397
    0x60a120f05010e070c02010c0b0a0207050d091d0f06010806030f0d02030a0905090906060105030712050411120304030c14042d0c090509150105040f0b0301050f0a0e0f06060f 76
    0x10060140c94100520011000f10312072038100c3e40741e0800d0344080101ea80040c103c002d090704041d091485040004001d041342d0340441d40700c0740c1e00000b40c03004160b086030040c0070316401c0d002e10940c0820102c4018500290005c0f010701a181514260280b590b0b040c1c01155620401010369402d40603410510041507410804001c0800180c0c0140d515000100301c001c061500c0390b40001e110324010002c0c00010080440c1490b04190203203040b968a40e103122050318004080003402e5600c070b140000300011b111105101d01c0c2800d1046410701c03111003554681503980d014500010304629400e50701040300354507448040c800b0310000b9101280c007080701e00407a6201240d00c1c900503c5100ca01c0ca01c00c18518807031003180c0c2d8a4070941170400c5002d040c10086100d255004045610701022200301c1c027103a80c00b036010755004160412500003142d44541c0102c10341e420a100c2c460041481c51080b10007840c041d100c0300196060007024030340d10754600002508a14014042a4200400f004107804858129008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 312980890 1250 312979640 312979661
    0xf090506010b0702040f0507050d090c080d020f07080111030a0902030a12030b120106120303050406110c100606090b0a0e010e1903140a0809150c010207060f0e07050a05060a12 77
    0x41a00d402c403134010320060300d44000004003401e00c0c3c101080207060308941940c5031480b0803240041d05801629000403040c0d0b26070800d40d441d200309030034460b020354005000305150040b0010789066960341d0390141c0c281d469a189484044106000154803401d10f6407040e02d040740020115024443c150301d40c0b84142d11000a000e000035102c02d0203900d0340c20b1142c40c000c101d00c07540c4001c120789890899100e40b14828804010704242e202c1c000314082c400c031600001640803284035101e0362941a040f100c0d549004c0c4003d2014510304000380050036a010f04141422543c119104070300d4040c110170215600703005502c449040c443c1d06050250302d915035526250403c021851030a01130350450070002c112006082245041d5400540200c0025900758107641b070820050380d071980030000540f050422030141c6a2003419640c03021035a4424407480b6002003d800f50460750400030310f080c90300119251030041c040c1c542c11420082e410442802c03c03400420041d04030b440c000c16548880355410054034042c400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 312982140 1250 312980890 312980909
    0x319050301170604030e04021305040f090210080c030606030a020c070b09011b1e150f050609010b07200a0b040f030c060503100504180b07200a05030306040f09050601 73
    0x18080ca02c031404024030b078452100002d00d040c0c41c0c15980140722034000c09403a40115004100070301a10340c0c0d1007440c1e010306130041080c449440f9804843c030003402441c6081e8815062465141c1c1d440c0d014040580c0204c1c00d802049103966038400c140100e60b48050080c0786400d600b008540d054507824010724020301500316141d503480012400040c0442d00c02c80000030540f11106104000402601c2d030015198440d880500e83d41c2c3e41400c0134200c0a46110031030240700d00f031500700c0c40401503503800315214035411204032405036210201118640940c1800504c80044903600d4000e803c0c01d4080b511450100520f840d04054907006104030980156005c0c4100041300c55040c4104880d000100c0081c0019150481c103500d8881c600805404c51031003400c0c010381e911001d88101d0715040c0081c00c1c04541001d43c010542c10140d20003040302e200110b1003842000f04075880d1027650804501501c40c01d82190042d4110313201d00d4108401070403030158150750903654061420001e101406407500a000d40d69 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 312983390 1250 312982140 312982147
    0x4030c0210020d0203070f020109180e1204050915150f1309050c0f09030313080c0114130311030a0c030c0e070207060906030b0a1707080c0414041202031905 69
    0x414007039034004981040742550020304885008940c0002980c2056030080c039010040900c0d8001a14810242d03040203070361141c0c4200c11744c0c203100c25030041c03203800e881002140c0325181600d845070503034022801050780c0f118601c0d01140e209144c088010801800044c844018007a00980e5003025900111405050b07800c0450740f00b40c0c0c94040b05022004024880007406589400441142c0300c0c81142070480858a0100c1e00074034548040040e03510300c45040854000c02902c1e02c44036030344c60301c080f00403900152641c403004111007144816900d01150210f210300c03d1a0840e600c025201004007005601840750742040c030003141d8a40050b900550040125051090900720784003080e0310020b140c0b60a540c001d0400300207543c0c0c0003000600303e5aa5250000d40100500002410910300e070307012000300f005400c03600b0504003000c9407000031a400042128100c10064003400240e40702204101312900381400024049481251b902014101a1054910f0400030300807444c400818082035000180c03000c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 312984640 1250 312983390 312983393
    0x6030c0b1e03011806120209040b04030e191e05011409130507080702070b030106020303010e0c09130506190302150c1f0902010e120706050c01020c0303040b100b13030201030515040504030c 83
    0x61044e81701518502c0e07038440440c034094000c544e07108400b40c0700409522000000500b45403140e4015484082c005001d02190360340000059400300d414001e07880825504c4109880078030005521108846041e16007d801407070030342d040e0f42550003000f813203034006420f00307031480c0c9640e0745204440c03150340507448800c00d5041110000389000110341042e54011b10800041c81042e8001003500d0440d04e001110303000ea80d803000301a0700c660041060064102030b500c0001100b080d03080d00300d244281000d0b00c41e486030301ca0002604d00f1a1405100194100c601c445060000c540c403040240340a0701e0210803181d104446018241d03800c0e9040503821103075036541e05140c04642c1d00041c3d0b5400e4240840301c0303415510755198016151000c038424070081c80070008506559140070740540c0c6191080c80150b90b101d181c2402e080c1583c00044401d018000301d4a840422040c0502068800d1b11045548a104690442d40194000c00014103200300503203000540f4003d0f0307644c07070044522480c4642d48156a0a519 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 312985890 1250 312984640 312984689
    0xf15031803070809040507030e060f1f05011209050727050105010807050306040c0e0310020319061a09041b0f03050702010b0d1e0c080714030106030c0b1e0301 70
    0x20809040c10310380080003031002054180382a1010040229000200c2e500c961030705a00600220701420350500660f02080010400181d48500c01d0000800000d8100611049600c540c841401901d0114501c1e003448403408580f6803002075514802c00485e000e50303032590f09400c030f2a0320a01041202110340040c1005914642c02528014070003801c0000c1e00d03003440c2c1400b0340309000082005020f1070f0b480c00c070703040c076103105100c1840c0c0b4000140941d8406045400458040d40c011185458021051405035034122080d100c0c0310111000e0100c034000814400c02c070140158090f02070568011b48800301c80650f03100000034140c11404030340711000644c0d9107050103003c0c4c41c0000c18800c1507900d803c646e4003854841c403c5000d5040d50180c1903a01401d0b0944880b84e1203614035a0180420751256000304004000240c4a03041d24002401c03c18200891000c05090751a0742c04001c00300c8580701c9040140340301c8c0c4d402030304101248081f18012410020001a500e810980c0580440040342c0e499651031640c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 312987140 1250 312985890 312985921
    0x60b0d0f050d030504022b06150f14060f0a020120030a05060904050607030c02030c0105040c0609121a070507061a040609020f040519090e07030b0a0c0e06090f1503 72
    0x2000c3c00c0038071003031030035800060103400030b10154905204103816404c050040008008440c543c050404c01c10038010382542900308100e80034074032074292020400300e280da201600c004020b03100100304a1906043d41c00c5400309400034580c0303030103664807031841c0281960962519000301c802c2e205820b0300d034075020030120b007545c1024203250701980d1700200b4400416008154240c3c40340141c140441d00d40c040480407851446a400100c443d0b5203840140420040c0140e40380048618550341d40b4000313074943da26040603c400c000002d02880006a000308503110701851550300c1045814807d04007031590b180d50042c0e6030f807012424135144100848043c0f510b41840380d0710240c4015401142804025005003c207446180160380c400d48150001ea20840d0b81d0528002c003800d104c01d0144240c1060a100d107035120780900049490541c0440015030540042c417420322a8960355407440501c000d02030a10146030b2110018a4118a1000122949441d030f800940e0140ca00300006540c3c0b442c1019187e4074401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 312988390 1250 312987140 312987163
    0x503070f2613150f1413032006030f1f080a050106090f060311040f0204080708240f1503010f0e03070c061b081309110d060e060a0b07060b0d0f05 64
    0x3da100303599a0500c2c3d003c04a0089500c1c04d081151005450b01c0d80700e400ea020720030b5030b245511a00032011040140e0a90f031a04281803c5006040d6580741d5030801540303010440b80b0880958007000000c0c081003082e00038056241000c191a0200c98417281c056040800107101515660b4540c1820030003501c00d80b10b084c901200030342e81002094190380c0c485012b1150500c9040c07095446a0700201e158009604a40c0108400c0d001c5940084ea2040b00355203601c0c5080051004025000c400d1024101d00e000c41841510541c4003105c503681c405921020780d00c4032070a0250075640e100c090071400610b92086402d80743c0400015a00c5034800e1400114190043d0081001c02c041c802d400700012a080d024080000d0348900d206071104400000c181d0444c0c0b560303001d0700c00345040402172202c8402c110010051800b070300740d050003429203884c03008030b00301c0090f21500d40110b400141000a4031100d4007510110f0710940d808200c2600b10400600c0c60441c0240030354100390420085410000100180f800f0071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 312989640 1250 312988390 312988409
    0x220b040807170c0d2606190e1006030204050d03051605060a0b120a170c0a020405240409050601090906090c06050301050907030e06010b07060b36040503070f2613 71
    0x185c4900010a02e548002c11400c07500c110346000319860b40e540029100715002e608800c03000c01030f0740729007003890500d0030303211200c08507800c01011440e10f109008039070039101e010309041c1c02c031000e40e9000c075004d50000b400714420240303202d50b807070000b00c040c028140100312046d40850302c001c1d0300040245d45601c0b011962400e5000144000004000000070b241543d501c81903251548601c0840600f011444800203510034035003010007659403603503072a51400a000c0c1142e8181c00510300c4c1841304035469000050140e5008200400904031030b40c00400f42148074150218250b5803507507036800c0d640c0d8580c126a0100d44080018045030601070720440d0701000d2890107212038a040746078181c50f40818060800c0303001340004d9880500624ad0401d00e103114014001c0c51480803800c0308800c1600407500e04903030307101100e1040c17820381e201e0b49101406190040059850041c2d15964000c41301c0b01403004a4290225410103041366001e08001040f128403c04092f07512441c07204604006080e980011188 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 312990890 1250 312989640 312989657
    0xc030314041101110c0d0b1003050f1b270c16080a0f0507031b0212060a0c020f160b0705120c0c0112110a08070912031106220b040807170c0d 62
    0xe075146c54410030101e4011243c4400e94a1303c61048000c03000d150006800c510913480a40c0190400040012407500d2080040205926200420203089140842a46102c4440a00950105040c0005508141d2400d11503107814449038100b0390b0301606d20b40c240c44601c1e0100c1d50144980e00b0800d89118841c1341e00e002d92810b00b041da4003508400300c0044064000640c40c1c042e6045441c1c146c01e0240c0c0441c0142100d42034074040200d440684890f02030ba4005000c2c03103c82405408002400c5030074048200805502c0504006c4500142e400c00304c0c00755021f2254070550070403500340300024030401d1171644c0030b400480502000076003a2240c20103140092450403400041d010720b11415900c0500b020b10341200c5a840d030803000c84045940e030b0025210009004c990004050b000810b5551030001c1c403050b104a0303500c25000e04202d07c0d51400510028000c00d000b03000258652509562041c4581c1240d801c066080d141c0608040391482c00003080700c0d0001d80b5040041080088602c0c03c2050b10744403c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 312992140 1250 312990890 312990913
    0x10506090c0f0f092808063907151407120504031101111b07080309010f030f1d150601051812031615020903030403030c03031404110111 60
    0x1074400c0b60002122480d000c40c0120301d010071071044607a40d180051511156809a400320a0720942c110b85580110000280000c2c0610001c210f807449440320308241380302c0600000501d0803032030800039400e055002c1d020748050031940340000380c44000e0251400f0541100c2d00c048160403a90f400110081e4090400200f00b2600d030b21040e8204440015000803c4d952681d15080d6915500ccd590422419420314400031603609419000c1c0142d000390b0074680c03034503a01e03080d003071078581115004440598004009080c1c20354040e0411500381e090916000034154028102102101c070360103282802d084036049d003000201402c0090702900a07003070003105e9003420b01d10000b034101d02c25074500c2441d01403081f03124600703075031000e00107c40629040c0c00d8aa540c0e4100700d0445040d20340b0a012502156050010082c0006074426104031141c00380080d4546800d58900b40c40d140324403101242007585441072030040749004803000d801507126a00d0811240003200000d401402030201100303540d40140b000d0031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 312993390 1250 312992140 312992161
    0x70204110309280303090212070806150105070c0611150a290d0b1b0f070c0e010803030a1a060706090b0a140c03090102090315071706180601032c01050609 68
    0x50003184d0500300015a4400d80c0b0108900c0c8000000c0300060f4000c8080c0080c150201103006841400c62051242e400c00d40340d801511180240c0c00c02602c8100140070500003140a45046224140d803d03040320030782e009080401d0503448084944410300b80d02c91648100c0202c1e06140454000c500d010301c107944410040c04140e42002051000c0d080000c0000840d50181244c0c41100c1c0b08440707503034142c2d03444250000d401c0403a03001020444400d07048200000e0080084c4400e5070580c2c80450203589161200f01007600030f09403600280340d5a0310640308214650b07860034001c200c0a0310551010855010701d0500c140480c100030f00030400c03a400d00c51604118403d140515600c200800c00d45500c0c0e4589035000340c024020700130004e401d40300c1d0756a030407640a034030740e0340b544116510380d80c2d00302c2121001c140b05e8503c00142c801b0354000c5100110304c1c10f422031800c55298018010b00d000100c921004100500301941d405d81e101004081200c008403140d001c2c0146030340b0280a81c3c3e506440c1c2400404807 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 312994640 1250 312993390 312993463
    0x91f0e060a2306010302040906030305040f0e0f1b16030c060f050702121c0603030908011b0f390605010803070521070c180f1406010c0503070204110309 67
    0xe441c50b030491400641d41c0da001ba41618007409040c10b04001d11130f1070b841c010b44243d00c00d0191015101c041c40001071f800b01ca80420030300c914008018081c0c5c82c0c66a060741101c3c60400004100300e110140b20704402072402c112009506802580d41c43c041c0f40ca00e0900c40100c0f01443d0800b509181880200203080340c000a41c20207044c7c41d284080d40d0758512420208500c0c200070103804c906824400004141603002803032400b614100c078002c21042130400c0528055103070403450350000c038020600c800445401a0340d894031801040844001440500c84e0391404c071b506c0021120103a194003640e03802881000d00c20795000d405000c0003180341075890303100c095560000e1007540f030f9804040317940641140002000da030803c41d4000c10a14030713640c940c40c0d1001c95001d003064403400d4514041c1c22400505041c01000104014101a0600c03501c1d5000119003918400328141d405100070820500161100d00c200c04090440b09240c5840b070500c0c020850034903000c046500907100d2141d040100480d04c5c1c0020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 312995890 1250 312994640 312994691
    0x1e040c0e101b05150402030f0102030108070302060711040501170c0102070b09040509150108033004061d1204050f090405060c09011101020c0d080a060b070605091f0e060a 75
    0x441e05542c1111510350000034007050042044c090480302062144c00b9003641c0f07001c0d500c01c9081d9205003444030b81d0b4034200d01091090050503401000108054280680203002e40341c05821000c0d8140080c6000c0750036a542079200000c03056035490680009681402802100c80c000d00c09000c04030319004010b0040d000d2020b1007841b0300d5441d40800c125980400c05e00c00b450040440450156a5603030080d602c0b0b8100024914602c22070003100d40c45502e824142c0503000049101403c035a1700c80d0380b40c26006004640c08225040c6101c000c0e07400d1500100011488800500711140c2d42ea0700340020301854500b15103106000389094010700c0002003021480a52080c1e080180170b031607501e0080101d501d140c2c070000c04403036540300040720b40b040f84000c1207079684903826480314002e0340c072341406502c2150342c2442468035100040c40180300240c15a003215410401e24811201088000c1004445c1c00441d4441080f249503103846500c61000c0074400941d00016080b41044003c00000010240b10802400e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 312997140 1250 312995890 312995897
    0xe06091e01090f081308120a02070608071d0f04060902031e040203030304031803020a0602030d05070e13020c030708122d06040506012f120703020d0c0807021e040c0e10 74
    0x1800c0380c0c41d825007003181c8004c11b601c108981803240c2e11807201e0450303484244048010f0045a4010401c0d50242c0781c2c903401500c1950fa441c0c074140f440c096141d108508014000d80c003110030901d00c010b554a5000e03500c050700012400507030b242800143e81c0c4026210345122058074442d50204809a40c012066175841505824601901f40d140d000c0e001e000006074000951114158001140040d030000c05817402c8820420308004c80d49030100b0584007910120440356221084001c983c4079521190003074400e0030100821030741040c2003555000b409420000d0701c0d0b20760541910421042423512100040400c2d01700d08025052444020158034508000b40524011512440415500e921403150001004181c0206425034240d8480880303400d100c0c2080b00301a1301c035010300400c034100030208547c18940d040d002007001c1d4403855410348428003107440580b00010240009409a280c92007040c2ca00594082d880c4102165442004100d801c050185801c21450752078040c0c0070f0300d59856540601c0103d08 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 312998390 1250 312997140 312997147
    0x180c1205060d030809070513050402011709060610030e0a0807120e06030a092f040c0e0901061b0c090501030b07031e0506121b030706050a0f0807030e06091e01090f08 73
    0x20302e040c5805400d031f104e15000100d80e41d01080b001d0040c1e002c10302a604c00d0360340400111604010a110200030744401015402201c041038161610391070010000c0b4044c2804a00e01503101c60031030500c1002c2809aa98050002d10b13a4100040d0300054050354401d418500c0039103880700d0200f60140002868a80002d90310300505052084002480c0000d40e0b0303441030600c0040e41100040c103a03a20b40c10390b582c0118100004e40040c14061503443c0b04941015000030b080381c1c6051030848044640c3c0103255032680b00c500e20301d0007094000c030309040036108035100400d00703502d07605d80344045a0b4018008d60030149402c1380f04d1001c4100c090000840241c0e1000828151a07030070002c0c01240510b20f0407a4980700e1850790307100c1017607002c00f0080703108821016184d03110740d41c6009071040c0c4122200c2c2400100c4848484590a003d01c4803aa040100e5140000d0181e441003101890003d054804011aa0040148169000d08155070218501c0c0010080c45904002d50300c2038800341481c18020002d00010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 312999640 1250 312998390 312998401
    0x250306020a030605040c12050c040806060607060b03070602370605060a05060705010b030705090c0d05040305040902071103060a020f0909060d020d08040e070201090b07050a0207180c1205060d0308 86
    0x1e40141c000b800c0b004000b00079480301143c0203086000c400310041022418600054442e502e0709c415641101c40690242c4016a568030411810f6030107804104d85840c0d40329280f14007034500f045014082c14680c2c0050000c40070310381ca00c128041034032010000305940f811301400f0302d09103050741c8150541e02c8100030840c4e481e62000075a40c1c0100d500071079080030021841c50f0078004150850300065a080c0c0a66540079211000d00c034900008444000b000380c820411806510899444654480c0c040c0c5032003801d2944601103030307050364000344c402d94481a448281e024140340a01c081768022121243c21450012441d1107080c8500600b880c1c0d0384a07808610004080c0d80310f4407109010558000c1525030b0038020791030040342580260242c0ca032041c41c02c60020b240c81c1c3c01413164000711030f00a10908880d595904044800d503104034203600860080401c0042d0401c0034949806410000d071a000c901070b038007020010141d0407518620b5000c28105001e0249944845060710306d4079030186000302c1580d0700c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 313000890 1250 312999640 312999647
    0x10609171e0309040513020109030b040302011107030c0b060a081209060705070f180908090607060f0c0e01111c11071206060f050409021e030a020306090c03250306020a 74
    0xc079500385102898111030280e10040010541103070129002c10030b540724111520100c0c42030310310081c04603241300001c1c404140072000e116886440b070b100100f1400a40360340040507400c00242100455044510b0b041000380c2d114407150310440a40e04040d1141ca42144540d0328240c2942041048400041a150a480b89021181d10035003100454a65540d00c500c00d2030700a0712480b80d03150701039904425504000b218051800d51a40004465050400d440b0030411542d220402c200c5483e540c3c0c0007072100c881c090313001d801c8404802e603c490315620b0b9603c00141c14008401801d00940d00101d441d5800008c1886171a0b032084c0b52451b01020040a90b50001d1404900da00112001c1e000250018100719a0790009416142c151080341c0e4065910070502c030035504004002035000d00624066030703400501c01c000043c1c0b074000801703d4145803420b4001c0f03400c01c0d005565a00240c0c104812018003402e0400228a07048021340c000240100b00c4100f040c03000e8170501000703000e960005100b0000c28032 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 313002140 1250 313000890 313000903
    0x6240815180c07050606030307050a0308102102030105010b070b220206030a1a04020405010206071202090a03050109021c030c030c0f0b0a0c0e0603060a051306080a03020d1701060917 80
    0x15074001200107041a440e460465008000201c60394810040018014180030058400d0141e1100003401c0740300103a039080c0c882020040200c00f503001040c100107400225105a0048407180d00a41411019a80141429031303805070400e940716801000080c00103008110040ea0014504a81d00f072003038449205034408841030f44010350300003404070600c40f001e401c2e0781c0320b29500020a5010300303440105c10709100a80c081d5114003030140c0c00440c00610340e503015010740440c8920154006280082800008254240700c1c0c0095a140c0c1d075034054030302103040c0441d110ba90040504446000f05840d0745d0024110704080d107006040010f420141c4040001840444012903406100d110482c80c12164210003001c600441c140020a054140c5406080c81001c82e40641006440d41c580310b400d0405101072003501000d200b44e843d41d125000a14107409001c59200c840c4243c0c054032003450713047e40044c05604082424400e80c200c1d100100025038101844a0890710101309240300070010340c0c181c50401c031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 313003390 1250 313002140 313002169
    0x210c010209030f10140c0a050307030905010c02160e0103020f01050a110a0b06030633010905030a060209120106140d060e0105040305040f080606090a020c120d06240815 74
    0x1151036200c04803c01d011560b030001444182c030410010a0a03407030811550415140841402000c00003440308a10500085500003964140401d80030745555856085614039500400140c1281060b4a40c1800341070b141e000500890035804d5542d4116000640412480850030b03050080006142042c640913032203202c5024441d20503540b03051400d0900207104482155024468000d20001074442c3c0c0b0007081401710314400c0d62a2003402d080e1801e6880c0030442c0002100d051101158002490360b90800001c40c806100e00070250f2a00f0094050110402c101c003641c140c903904122007806400c00d40c2045196509080b035040c010384010b410040c0041c03032107000e6411503500301020041419040340090003203d50400c8a041c0c020307074130b15040346c840340306494440c2e0201c00b01e008030310031603516000340c500799008805840c0900c400000107151a031104240c000569182c1208010040058403443c03003440c20001d01202c0c8010008000380211070040c0910000500b41c12044090b07152080340703840c4034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 313004640 1250 313003390 313003393
    0x15090302120706060620060a050702150108010b012d120b0d0302061609030c030210111f1d030a300b090601020a03020601380c0f210c01020903 63
    0x190040d0408070003400c0d60340542c1002c5220000b086000c500c04910348211b1541d13580c040d01c180d80f20b941140c0080c9c68050841001c521858000c00d40042115520f540240f07521000064458266030000d0803542c2440002c0607900c180340007a00104288040080510034035250400444580d11519001011503070300c2c1640100c42d01c50f00501709900001c1060142a512203e024500104081101c281070140002424000b00380c078100010b04040100c0c9000d69410b00f40010301d402540b8140d460300420035030440d40205100c0e05811502983d2107070015180200c0d0104144d8100c42810559038414100c14004010700210b1000c0c4243d07140c1c01c0d1001f240840040002076012044509c3c01400314050418807035101176010075065030001400e100c005905030090b040507071a21802d031054841208110120521a05c0680c040d0319481d48405040484c82d003405032a100d00c02e05c0280790107491644104a5807100c60200a000300290301a038040c1c00c02e00e80c4564403027041c240180a0b00441c454150903 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 313005890 1250 313004640 313004647
    0x6090a02090411070501051e010503070909050a05060f0106120c09140109030212010f0b03010506150a231903050106051608070f0f0209070c200321130506071509030212 74
    0x4000c010742007e402030700d0768a900001c204200c16070a07074198080c03040580c142c1c03080c1020060140950018006140150280c0310480400e03114036003000c601301d41e41003000150320010302c506a00718040d03c0400301c241c50100140c02c2407003009816589a4005c06043d6001d403903000d0844d0384200448800784d5800360400d2062840c50000e18080d1801d500c00091071402d02031545c405050501c1124800e507001802110b480c5650044044198040e01c01c00d4200b0031031507403d600d1b070001d0781d040d0003030203210031700c040d075140300c02c0f00000102205554054100f500300b10041202c82e074407105507090031800800c2704c01c0b444034030724205105100d600c40c004c007140c03e469000400d2250410703d00c04400d00a0704c0ca0101c41d51a041c0455003020341c401c00400e41842c0000d500c00a14010400c1e0198082c00340031aa401141401035911601c0442c40003c9000c4001130b40700c0e02400d207410903100600742070354800d007002c89075510b04490442000c59454126035036003071030003032601c20071a504034280c60320700341540c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 313007140 1250 313005890 313005893
    0xf0c010503181e0c03100b0d111309030e0906010309020f09070c051c02010e0706020601180e0318040b0418200603010801021818160207080d0203030109110306090a0209041107 77
    0x44604138122107510034010107515001d05050b41c000c0e07000b81c40f40103000b004018881e6551110144d0880c6055030040003401e001608541c0f14444d500f41d6600a4a40e041844810b0007007125018005045034101414072a01c0001078485219135031221800710f54008443c0d540c110116085400c01d03501800b43d1040d003070740781c0c909801105250b40d00c015a0740207018080c080c0c02a159103494a00c9078000607402840100115114009041c1c0d6113043d420011800d042c08c80444c03440e5400032030f4104076040101c8c1c0c0c8a600782c60300703104000a50388180d4007030010400003054090320080811000d018200d42c806401c090403d14410342d050040014102c40c0c4a58484414034001d4003ca14515880155800c4202162034030a40d0010b0440c41e10b54285507030341e42c0310108030140030752941c840158421060f003c110020180450041038403568000c5d901d9600d000b401274241e0b0f484103d14071200104106100381c03929030740e40d4030741d00140031400036981b500758201150003001e251000351400440440d1140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 313008390 1250 313007140 313007143
    0x103020f0a1128020306010611031b120c0d0e0a120305071b0e010801060806190b0f04020427060303050f0304051501030b01060e0306060109120203070902030112050f0c010503181e 79
    0x5a018000e45c00c488250703032624400d6035441e091031480f181581c8140407400300c160342450f080c400c644030b4a00b56045200300307045400c03040c0c002e0382070300b0296084049842045507114500c0d0b03032018822240c030b40032685409000c100e00380945c8030117810403000152140900540c007141e203c19440c15003440003203c0c0e4441600d990780d0420b018000f0b140d400c140c00091050b00010314a17001c0e410031001c2c411006803001c00c00c030040c4003086c9140d0f04506e104214141d41d40c2d50f84041e000600c07142040c1c1019040c0c4003030301140140c940744100700503441e042003480400e0b0300c101921100c0000b0180c50380d494a49042c0649400c0c00b40e0f40300081000201c00110801031516507203812249c203a1100040300c4078641c1090b03255130086035a02d000070a808400c014407401050211074490028050783e0400d40c44000d240107070780c0241c016408405024603000100102007010704480c8010b14050b2000c0061040001c1040c40090302071454031441044051a201040c04402881c00f4407000400609001076540d6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 313009640 1250 313008390 313008463
    0xa0c08040503060907051302190522090b0a0504090807020d020d15090c081c1818090311060f0415020f030403200f060f0a02041e03020f0103020f0a11 66
    0xb14060003000c80c00703440c0c00c4d0488c001d807512481d204c0c0710704041e0b142c007008c00c0798141c2003114000140c08074070300e118031420608880c4401a0000b4040860344c020b412040c003070052015407045000d1850849640c0c0071034484010313a0a4940d0443c0d50403e41001d0f800001e00c0c6424500018140d000c1e80280028002d0340d5611901c4490b1181c43e07000626980e81039440c1d100c040d03949201144d40244d8000301c850178800e91251000c000c2608240c031510b6111090f000c000d141c4101001052952400c600301403680048103010040241d0000b00414900b84a054200c94030150005012900400141d40349110540542e86030310288001c0c0c984a241c00c0c24010590542d4841603400c903000680382d031450f0311001c00c0c051448802000180b8460311148441914550b000703103655041079082c0808240d101e410000000c0414200348c1e1107080504500410648590a2002030b040c1407042000220070001076055071440192402e0407000318010007011400d00c142c0a10b550310303004a001d18401581c10450302d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 313010890 1250 313009640 313009649
    0xc19050307090f030206090f012624030a08070305040509070509090601080c07080313140d03060906030f08070302070b0d0e01060e040228030602040608011e0303050a0c08040503060907 81
    0x5140c0020783d1200500a045058000607410800422286129040c00c901d1a002c055040c50301012181500f8500c40c0c4112040300078154400c1d000040c800f2421401d901c02000d1140521509078101110300040c3d0303600c4000400415903e80801c042c014580100161402800c001e0183e17203141c50246e02c01001c0d0341c408810144111408030100701154811021148140b01907244145008860b48411142c4c1e003004083c2e04507035000001c0c1000280c0b2000c154581840b804c8020b2644a5044401406494207500720304006440c103582000807902118013282040d42040340740d503451209003800c90820b00c4980042d0601c2500041b41c0386080100d600902002c8050002046900e42f03410310006885003e681c06135110b24020a190707103645010640c0da1075000c19850201c5055075941d20316080ea00145e00050224509000401c10000c130003402c640d01400e40c030400581642155006002ca004810703126041052030380066040262910448010b414018100d13000c3d490100610780c9d554806016 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 313012140 1250 313010890 313010897
    0x1805090d0f050405010e06040914180109050d030f0f05010303020f15010e01030204051314010204030605060d0c03060c0203070f0f0c0506030f0c091f09030203061303020303010e0c19050307 83
    0x4003031804501c103001e00c0740258055601d20b071400c0d203840011910702070003a80c1c40f0340c000f0741000000b0300d0540c18861103030406205aa482d070185010180440a00385840c5840c9e16a41000034039030000d01d000c00d80002d204e40600300021102400d08882004103582040300d1100351814001000741034000540116410918044401c00c840c0c640c0e0b808000b500a110b014440d108100c014001450729403c91507000310214002c0001c00100d494509258484405001e5181d6000a040c8184000c038025264000d00540d10107544030015513540300c00950610000d0461b5070b5806146003c0c610070300480b0002a0084080e940050303085c00c01e00b6100505030800c032049450703070700001198107101d02928822511461a100103503500c82210a10f03920200102d6032040b1010221030440d541e603081d69002e5602a030b9240c110034154410300d131401801070700e0204400b00c420342e05000241c0c0041240e06440740481c142049440d441c44041d85400f600d8400800e00708000c400c1003ca6500c50003070342c4140850f95 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 313013390 1250 313012140 313012153
    0xa0b040606090c0801051507050304030308090c0603061c0c05030f250b0a110a170a0f0305130215070215030708010f0b12040c0b0a05090111010e190507180509 70
    0x200b030842141e0f641c1c0c59210105900307100403c400c0c6800f8080104940d04440e140780b6080c1d8a80d40c0a05541c8150002c8003c10454424071001480401c441140002c080d00c01da4654100800007c0c015840e01500c100022403610001c8104030b48c17944003c00500c406000c66030300d03140e031429039a22140e600c50208039113210302003642c0700401030491103000c42d249011035501e009014035081310705280b0016161514131030400c0c8030700018042145120b044040c000940c1c4c49616407200203014851056170300f410541054240b02e04e51a000c1c6520100c6581110000c1c0401c00d03032403007450300d40200540230b54884650740e00300a100c02154001c6202d800e0303643d10241e090380c0f51071402108103158000c4440041050040444150548040c241c00600800458015540e11150340f030155000300c207038200082010400010384d5821420407000c03d00c2440080c4032001c0e9600e1f01940c1d616a5007003614000c2e401c12070100a102040c00050f0140030140001c04420000f1100500500402d8403584003074403414 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 313014640 1250 313013390 313013399
    0x30c030e01060f030f1b1512110414150d020306180405030415020c030a03050d06090203040b041e0b0a15171b030705040204030609020406120b01050d0c080a0b040606 73
    0x1072107908162078a05014440c1c040c1551100303040b600481400315211b50042c0c82d40610a0340d07201a8400074030703e1740c01d070300b8410322100d1380101011204a101d800103424112400d00310301490084d6000c1c2c5803440340c205401c251450004100d406004d00c40e030180340000404403003446264005500c90386d0300b95059940c881800d5400342800c10200c5018165801c14031090106800d25150a00c000c0e0440c8129026450b44000090070040d1001c0103c1c0880c60000c0d0a20360b040c024003d603030080000707203070860461600d5159145515402400144100700e10008094401d0410034081c09043e0044940c0c80d991500c015010000e055a0304850780f042c0c42902d0004244000c1150030501e8103080015107200340016042d5060900803e600c139505004d0282c0100c3d07207840c1d03440508011070086601048030480c038014001280d5594100700f110b03801003034a040200350303041c003034504440041d103924441300414248031700b50440981010425005000340c2c0001c4c40a544420b43c082c81c025242040040d0340e5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 313015890 1250 313014640 313014643
    0x20a0306142d0a23010312020a0201120902032b020606060a0c140c030a051e0f15070c06020a08060f0402040609030b19060605030106030e0303010b070609020a0312030c030e 76
    0x881048100c0401d00b000881400c4198050050700702c034101c14089280349980c58214054500f4510031580290403e004205000c1000c1c0303408464082c60010b085c03001c0c101d0f00000c2c02d0411241c50040d80c0c0351910744003411500e081108092094443c4400440c8502c3d02010b800d458154013000b5005100e240040782c0c1c07516080085074402e00098444013407500316560380c4440e896000c0728809440c004e40b0030041a50310144984100c1510400182001c1e0075620314410b15a008420101c0d059408243d403101e296800244041d403480c5104c1404019aa400c801100c4540fa41e00000b007400e400800c2ca45c08050704924424000c01082307810030000200d500c1844101d01840c070440d0300180e11000100082405500b6444c0c0250030128407400e90800f030384441f000c1c0d441660002c8005000000100401a4113108072881042c001028503c0e65240c20072083d41c60048200c05030003a5034a000e03800c115501c9080500003941d20003501110500b080b0341c0603005240f400a031030040f038207000c20154a00c0c0d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 313017140 1250 313015890 313015921
    0x4050c12010f050d021306150e030f03040b031801090203070308040e1e0601051809090610080f0d0e030a020a060203180405040f11010215090d09080303150f0d020a030614 75
    0x41c013800c030040e944d083ea020058000083c0c108400079569480340071035076803e841284a01d020190300c403403003080310310070916191003401c140110150b0406c2c00705004e83c050700170860390001d0071155004120360342c0103201c0e8010310441500940c1803081c0f41000040058542c0038004460325001c2a804941d41c4801608002c440c5010070a9072110170f9000803107540c0a04040c18000c40100806800e80600c07501080310004203540011480e400442040f41024504031010041e01004015018441c00c844000e9501c03901a013030b0b0b405010046840f0b00040e01e042104440340c0d0380040002003030581d145406501c1c4d0384000e180480b000c0c0141e83c440200d017014050540659440103a0003086106902c1c0c500800003001c06650441c010140203410030941035120740d0040340c0610103001a8925218043c2c281081c40c1d00545042c0c0050003002408845005410b0200c00240c60140b01700f0414400a904070000c3d100c000c0d8880032012010050080c03603441140d440308144e403600c0d4a511a006284040719 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 313018390 1250 313017140 313017149
    0x60801030b0c0715051504090c090e0a0c1a0d1401090605010201020a020c060306010306080303011508161b020301060b041212050c030f16020409060209011e170405070504050c12010f 80
    0xe003807859034500040e207031722082c0d01580c8410b034000d01016500004090720060b8100f584c0c145881c4400b4400e0b291544100c00607091880000c14200310700f5a245402c4c2c000612a00450360380c0e442e088580366a084040f100c8100d410306e01000481c8100040c1601d004081c010048001c1c0340074404103e41d40140300f1134101d4034070380d001010192800b20410140e548020102c03410152600300c0041e140c8001c1001d5070203844120040840202c08140040550f03000030b21451118201d50000d5021a8002007154401a520300d0781c03410711919800424003501213544818000c000000c0c000504030700b410303904241e40d8070070010081d04141c000411149401007405a403407541040026165002219008089901e4440c41c40780904019800180488407803a4041e0740164001510100740e60307001ca03600b40900d81250f0003000c031542c0c5a10081c2580080b20200e10807000744800302d0300b4041c08106800c01000001c0042c41170780307010f00c80c40f16682c01001e050010101c070714002040040302c000f208030682c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 313019640 1250 313018390 313018403
    0xf01050603031c150503240606280212030a0603050708010e0309060a090b0706051e01030c090c0909091109010609050d1106090d0308060a1202090a051b04060801030b0c07 75
    0xf42c0030300544001c10101c03d01800482c0540b0707001900e610140b0a40c2031100306d1914000d000146401844130b010b400915080c81603408015050a00c24420040c001c040c8000e8400250200c0c4070784180e107402c01c08003a0641c8168044100600c510322508a241502d11490507180000d42d1008014240e852440301d400e840d030820300c403000b0340b81008805010044c040e450480016a580d00d00f0503829803001c0c03000d44034962034004100401028917446100e03100415440f54003036245032142c024000c418002c507800325498441c0040120700ca400140040c0401900400002c07420340b6200400b2a09122018002c15245e4000112580070f54801021100040c09031880f10030140c1d5660a0040203622040d0f00c120140400c1400b6200c040d805502c03076100b0703102c20407181000000c00c6444181584908a500c80015074040141c030740030121034204414031000f1449494002c44030341040150042c1c110000f001040000381c9503405028203048a000c0d1402118984504c41c8030105480380d60800b5044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 313020890 1250 313019640 313019677
    0x3090409080c10050c040e09120a0807030b010e0d02151201090504030e0d050d050a0302040915060e030c180c0f0d0504030912110d0303020c011806060602010605011e050f07050f0105060303 83
    0x30541c2c02c00c050340c8c0721107620107540300740500561013405034211400e000000703840001000001d5130544140c1c6101002402c1c080c81c09641440051006c103a103540090080d445c403001040380c07406c101c0507200003034104d07000b40d400703503031240c011400a0000722000d800081c60502514180c0c2015000c41000c0b58000c0f000c1c00e0000c0c402141983c1903031200c1c20a004040e402c2000003080c01c0e0038441d4210302464403000c85000c03403070300c000101080300328078a103482500300365401030140d80c4040624501c50b260002c1e102469032180f2011030305020f0200110302001e0002942c4072480b03d140e000910030392181e240d040c15941c030392500b01c0d0b00c003001101c000c1215010a05d140424a00121060501c038030034a0090302d4040813040007400e544c421105680085602d0810768104109402200050201840204081c0d498a00002c0030711049080b0f20803204a040f10300c0d840107120f20210364601012400160f0795206924090b80e1340c24510318801115440c1201149540c075000c000c4402404035a03100180 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 313022140 1250 313020890 313020899
    0x11160609030e061204110103110d09020f1203030403111506061602041b1409030309060c192103050c0a0e21010203040b010e010302100e0303090409080c10050c04 71
    0x80290040a40034005030b10b41102d210380e900303402802250305000303c03145141094074090a0014954541074103260504200f6070b90755807002c0a803041c004400801040301d000038004990140b0244481b5074014095200c03000c2c4504002006500491103641d44400300d00400114039140d010031001c004c040b40c05040840d00b64901003000d4408058990048110840e050340010b007195405132070300c90b800e2a120030420703140e90030084030608010403420b01e030301c8c00301c251001a0301c0b4400e1021480c419003012031410070600040000b03400841038a000e40f0807850042c1851401c42c070402070a5034010048034003051060344a800742c1c0d07000d41d1003110001d0620000c442c082d61401404c006464010003c1842502c884081c01000034002800d2400181d0741e0405040c4000d00302c0c0140c0080624000d0800100016219024814041c1c0c24525014143e642980c001034218421401040d9010b13050074000c00c04d004540300241340c03640c0d900048031a907440c0031443d02c0954204131038013402140244810030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 313023390 1250 313022140 313022153
    0xb071709030a0219061d01060501030f050f04140f030a050711010f08010306050606120112120c0302120307110307061d0d141e0a080601020105070c121110061205011116 74
    0x11310080c4102c2d80415150310f080c41c4402e03501080d20000440d070f910b5800c1003241e943c2600c41c0d844c64100e503d006000fa441d00030001080702401420080171109254a0031142030020310842c542c9551200030740b83c0d40e0448420040031604210420350f003008a0159180d00380d8002d08100b007c44060f030703c0c0c000c2c540c0c1c40c0d0b8960400401000b807010b6045130040105000b452401080d00340a4410b491940544148500b840e0202d10311041550050000208202000c00d80024003004c240c0b020402ca10f6490f6100c4004440c0780c001c2038a141d00b6071002140d0f910401c0481d400c0102205020140010005440b505480c1e841e01d0124207800030941850310591611a540010080c42c0350480d260314400d0f4a41c0341d101d1240d481084001c2c0000e001d0001c0c440d482d0f03420b000d0076400401c245040080c031021610b5032500c84081c0140c03841803192642c14080c020708184481945060902c50400c80c0e10343d285041070101e0b030b40082c00c40d465481c0540e0790303030300c0c65001c03054400c0280c0d1501d543d8128202c5641c1c41 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 313024640 1250 313023390 313023433
    0x709050a0b0a17150a030602031806040b15010306050a0b07020102011a0d021903080301061d010215070c1412041d040503090613030c030c060314040213180b071709030a02 75
    0x1c00c65009001c0ca0842c00d841e04017206000f540307e0100140c1c0d9140c04920596108450b00b2414503e8000c0004d0101003017040b490660080e00091203011400e2048005900509042e800390741c114003a0b01c4000344040d0074101408805000380c00030300110500040e102c03100403035107511542c03100301d0b42a114054200b242c4245504406d00e4000410301c0e869464103000754109900690000f0358040740d80d40040c414180101403100280010460038120800400302a480100394201704043e500400d8144441070303041d0418003800c441980c002001e40070600c6026489030045440a00c1200603581080d903102480601c00e6800001440c00e0000020400c04583c1c0032101c904184680d2200120105000d07886040045202d010703028003051034100c025003a0b0b40841d100341100d4068a0800c400360b01c0b0003c2e44810105d60841c0015056800c02c900b400045030704c08041c00500c02601003001803a040741555000520603601c203040c650f50a06059600d1044880000c01a0000d8206814404489500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 313025890 1250 313024640 313024651
    0xa0609050606310e0f0303071701060806091f03080901260c0318190213180b060d08070506010608180318040608010f090b070908060112050a0203060709050a0b0a17 72
    0x200b2007044c07140c045481d26144804c01c02c840d400000c180325156030400c0c2d1400110000a007030114540c50100090180d01004040600404401c80003d49140951108605400b0b0880060403007079200d007401411900000c1115012809401d104840e8490861800c0c9041c51000c00440c0e03d940e07003804e51196900701a000b4a000c0401c079090781c04203841406882d1910f400c0103507004041c0650300410420401c0c8456401c0080e1500c520110303807480410000b081650410041400b40d2600c0c0c2c08143c00102c040806044540003240d010204003001c1507c60407928140d44103802a220584002c0150500c00305d201e0341c80d0300401c8582c464503a007a03074510024000820000d0150b68940301c05087d119240c070038001841d81c9000d03280400c000c2862181e0059000c1c50940412410050700c80e64031300040c01011194040c03042d4400400104000110355541d024041d50880d0500000107000c81c005405480d02c1804d100b100814003000307101c1035500c840c01c04d5554882c0c01c0c004444101000f03038050318 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 313027140 1250 313025890 313025989
    0x2090303070f0201020c180a14060105070f0212010c0c11120a060504110a080d0305010b0a0906110a1a100b0304020d0f0f0206040b0903010b040911011404080a0609050606 75
    0x506142d03543d44950f141d59003050300e0007c5154906003002604032494401040f10b0000094244001640c0c0807080c7c500280d0300141024181455000042e14902e000d460164150b08100100c06125400f026407041c0e10322070b0240c01d409081749400c1203803852a540200e112944140740e5000450345035003045030000d001d51941c8031600507020108030080c203103800030312890340182c03104800325034036100b040d00405140c0c82080c01c0c40c0f21a0720081c0000c455205403010004103600c0021400c1c030900c0036229103588407082d0000c8a01c4608040d003050001c44500e40c03c1c0340c510030b00055040c0003201300c1b440b865008100074400c80160341d408091447e003550503620046001d0322000162214002000a04940e8501c1030720b42c09450109400e603403441440d00e01039414042c03c04009071903440c0322584030f0b409007000850b420320038a08000741d0045902a0301c0602c608102c107008d001650380100d0015010358191600b50340d0302170078002d4000c1c8850856446040d0b800000b89080c400e18500008030701e0015 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 313028390 1250 313027140 313027153
    0xb060307120f060603052203020c01030f020d0204090e060901020406050415120e03090301060b04080714150a091d040c06080a0e01140f06030a050d050d1d0d09050402090303070f020102 81
    0x71403442c01c0395032980040000c02e43e968280f0a00446144112003540e070000c83c0e628544413250b900a4440f94007510440c1030540791000c1400205c04c91f010b45c0d40d1980b40c0182192666600c8482d10050001e030290341d03201380120804543c920310180212800d95100b40c031858505490210100c80c3c4c1c05602c40c52104000c1d0450304401d005005018051701426014011911440d08008050031150140e10010b0556010403042000950100300d00b03040f10780c038114203000c541000000c070344142c0d115881555484030005d801174889030010301020554000480e40040201d21210880d035400341910058429401e20604100d140d10410703560b54011084600840c0b6850b01d11092400e4510359440054180b2089040164141050404640c00070044004200a07401d54a0340c43e11449031100e480f04000000682c0090210550004041400c9d141801071114640a50031501e03542c16030010000101c01907400201c51400d8025200c082c500103001d545810002d5a038a52022003841c03040b8154010310 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 313029640 1250 313028390 313028411
    0x3040621060509191d0622020a080f011407050d151205060603061609120c03020915040c0905030309130f110307030e0a0b04020105130f06090305100b06030712 70
    0x509030b500601c0a490701d540c0303060f130403002d0780140e481500c0c1c407400c4a400e507600801501c0b4000385080c0c2002030200d14502d0500100d20310a50040003240294010301241d000060204c8002448039126808000030001d0790070003904001c07000d009544080004505100000343c2f4401603020701c0c008040540500750f25640c524616180b90403446098459070004000c00200d03041c288a160b0b488404c2d00c0340b21807103155400001c2e08410f0507014441c04440082c00c003008000910201401940e0001e00e41703000ea2524002d179075001e030800d140e50ba014504040c640300040b0301886404042e980003c024605100140090040401065071685195900d903048801c90038500d10481c00694191008181d99142070f00000d0160b070108256a0805d0b489404408045a840310806030099424030b4090368410440c0469441465030ba0403100c0c0310304003001c0010b40103401c0190f250440f132148003a1180120340d800400b044550285c4101e0b001082000014100c0f07203d0203611080e1350b8000d10004010124 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 313030890 1250 313029640 313029649
    0x1812200a0b060603010f12060207060213060e030f1e120703081e04150b01110706200115060c02030304080a0b0f0c0c1005070c06180b09030406210605 66
    0xa0505400503600408000c0003841a030598840d4000403d80c2c6075869549089001c9041c0d20041c4140c000ca1400c56000c00c2c00c02015404440301c40b9081a0150f48503001280d6001640c8014072482000c10b2400c3c08111141c18041482c2c1c0e1a20410000b910103100d0452850614642c00440c0c0c564501581105400c40117002010300340c454001c0d55070340c4c01d0389807900c01401041000ca60202c40445900304100000b240c0d206102210b4504040100b030191031a401610102056000701034035000b8090b003c9070643d8041101240c01001400b900150001c400c03015080b10340522440b00c80782c0d01c800050103582c0c081c0f16104605071014044a14003580d40a01504015441034219440041c0d54180040051081100c58111004103245c034a80681c007000140d81d15140c0400c10f06203616400094000c0f40510090b00c25680c0122050000ca101202600d0300d81000403411038203c883d40e00480c401d10000015135081d18295114070680c4006608a078548000c40011040b555494420201d0680c49 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 313032140 1250 313030890 313030937
    0x501120f14011d1c090b04050f0114070f0b010501030c05071412070c05040c0329040e030c0a050615090c070804031401050717060102280503120703060501031812 71
    0x22a04041c0122640d07800c07105584215020304101040045d040900a000d4200103c504544003203c890071410074000068030a4495140421881400424120240b04407035820301c010383d204544111031a80c880006608507500000c004001400c144416030004064100220840c03030380d40c0c200c52421031040c040e20350940c405441114136101c030310b60070031260800e8040c144403003810303040600c03013406a5090103a0140680324101d09140d0001e0b80341e07046031180d41c402d0382e09a2090701507030781c0c404d0303200380e06507503070581c2102280c0c04d10580000030000210100102d600c81e80003011a4900c0d228240c8a03c2e280d04002800e9520a208120000000e202407001500003460800041031503d0040d4000e0401c02e2400b00303a80c81400c0c0301c810810160390200760a4035101000084035244c0422441d50441003190743c400504a200004810200c0400e04030120b220b000d0039030701070280640301c100440a41700d0b1804121245944e211071040016a524400100790006207403110408602e44826006940d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 313033390 1250 313032140 313032191
    0x2a040b090c0c070503031e03070e270f0919080c0d0905190b040513020c01060e0105090c131a131517100302330d0501120f1401 56
    0x110001d001002c2050502041d4018a811405035061020306004ca0f01c503a00c50700102c03005224000300142131310707020707013503407121187c02410b0800244059580e0784005c0308441c41b181c20041854001602031030074400031910440b900000b030480002ca03040e00c01c07038084200d0403c071a1443d081c08607000700c1108120001296029955200b04140381405100141110440e0341d401c1b2000740c00c0511201500c0e0782190704035107090715901048003100c81d82c04e009029130074802c0d92035404c00900045100c00031303c030f00e816908100c2d2000d400d61a0b05000498603c9403c218852010040c0c0080200310348898040380c050164070541c41c81c005203003040e80728040c0356801014030700140c0310f40c1000243d0321809000c00124554102403140c1841d100c00005122580b2009200d0603c07500e0540e4540703040034580e41b5004045481078030700020841400d0194001069640c80c07586044000551244a80b502d51156500b01c068148107100c40c0d00c45491003d0044402c000c0d42d0f40b64183c0d0640240d000b14a0a40b92 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 313034640 1250 313033390 313033411
    0x10e070308160f0614160c052d070b22060f03020f0418061403030403110f0103021903050a0b150307030506061b0307060c0908030f07030201060e09010c080601022a040b09 75
    0x10311b41401d020380a9050415454108017200c60080006174000a11031025200e0302c4882142c402071501d000307030b00c1a00030b0000a050003880000a03103a501480a090040c0f4281280f2401d4521306640c0100701070302d8410600003d000d42c0c0241d40040c000d600802c0c2d21090318284614294886045900b03400150400c0f07038029031746402c06c2021810880d008400004110085c1d464a0b14645400c1a040c420640d0a03124141d5540400716580c042d504584991440b0500e4444440030348001600400c0d04403112076200e03041c070600c2d003c0c5281c42100d900c407014161907024203546640030210300411000b4800768100ca0300700103861003040d4040003d540035010000030b55a45840707281c81d20686403246070340d10038070943d040c092001e09000700907a038039a04100c0d940c507141d401a040072805040c040d404170400110400c244144168190041c20b03d07201d442d1208006a103038040120f03034a10451540600c580c040340d1b00514650500401e001c04ca210050001c0f85070303040740b4005042d55405031550601d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 313035890 1250 313034640 313034681
    0x8030715021606020f1216080a06061b11120106030c0e01050109030b0901140c0a020f06071e03110d1b030209060d0207031808030c010e070308160f06 66
    0x100000e02051108890080c4415400c1810b580d0056400402e03014004142039008908043c1c100c0c0b0340c9080d201044002006140d0a05014203452600509030300c003100001c8500d00094200045402044111000c964031180200b00b1604144103100424100300c8013031a5503102c40700144d0b80c501c400650004100000102103246280c01c5c201d100d4168446032140400c40b004000e0b603a04191607004980c0c1158540e03165070740b07050740035004200080030788691090610510040d103895070041c10f00103403c2c1e0200d42d0f06000b0410281c0e034820048451100142184401894140311004c495031600d1b00ca04000c10a0b15000d03002c01b085800941c1d80000807070b80d0b80d03110b64000c0c1041c1010040001203040442c0303481c05d81e00214045120300051151903d40005219041611920340c141c034039040100c070524581c1c2c59804143e00ca41c007d100c189160341c20401d0038289000301062042c2201e81c08407500345007003264401c82d200c0b40801102650560240e10f0b1000216025015151850840401040b01d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 313037140 1250 313035890 313035893
    0x3021606050705130f0f0914150d05060408091302072003030f0f180a0e0105011d0d030e030c1c12051e0a0207060c0f0f0510090b0604240b09030705040204080307 71
    0x1811513295000e0340101e82032608e00c420b4284181c07100d030b8010034502d0802e080307228090041000e071600780000800360b1080c642000240a44030000d09001942151100b001c01011082941070f40590300014100590501400885a40a415901940c1d0303014041c0c07414040003280d40c44140d0482d0040ea044500001111181c640f281d11954807007030003c640c0003800070305010078408502c0050140702d05100760004014001c0380d206204003103110000b40110340b407007852302d0001d1420328941007081c06441007022845c12803400c00248007484081840c000b45411141c1c4070401855040e80012003409410880b002410040e00001418500000d1519903284485580203180c41041d52080c03080003904803448001900124049507480c1e040340480420380041c0c00c25505100051148402c02c0345810340007010009200b80e40b178810340084901700170460146145100034000e001d01c1d507140120344202402841e41d0503001d0201801c02a04030340e1030035150400700d422640305400c00b0340306510200f071060 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 313038390 1250 313037140 313037159
    0x53304121103030f030a050c19020c01110705060a0c0c0503012c01020a0f030c09051909050108010606020a2d080c01150819020103152403021606050705130f 69
    0x265600750aa00940c640301d10303031418068500000c0c0141c114152103001103041d038001c64041c1d40c07506a80a600d00170107440240007139650401c000400340030401418201008040c08620001103403000741c03e9903e0034460203400c480c42c003251502100c254040c008003040a0f2400d11070032503c001541c00340d40c080b821888a18079421000c40c5007080a81c010000728240c0eaa000ca20f42a00079428140814030350500c00d0183d640c0c0daa1608016000a07004003103062461201143d04201d450480d801c000b66600e50480900f07a4019000b0300015900c94100040010101071105c0b60400200380740f800848181c0701640d11054181600381c4903108003040070414003000b03215104c1c455000521341004039140007003007a00c0d843d0440d03849140545803564031b410341e4003c1d0010403d4011440c0a12082070302c503036103407000c141c28410320341c160122007124214450003031080310107140000c1c491140d61203c0f50b03211000b0b01401840107003005000e0010800c0c00b107040c4652405002c0e440b0700078034440d04140300407 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 313039640 1250 313038390 313038413
    0x30201082406030a09060c02061005030c1021020414011d0d12020c0909010603050c0a0311060702041b021e0a08071e0f03050309120405330412 63
    0xc20380000500d944240410380180095152000e4071540e0b104c1c1c1d56403035008010580860050485400e0005243c9000d6002c20a00d200d40400e048500070716444100345a0350700030345080c05801c200001480c804060195803002d05001522007100c10b445a0380700c040b000d0b0f0304240c1c0b040254507209c42c2400e02c02c4d07800152071035550110410307040300c2c1c0840c0d800155041d14114000b520305980070058a17034a0b4400d01101c92a114090610001820820800c0380244141d02c0289c2e214062285280c6a0b031030310138103d10443e07801051107540c003403031242007010b181e2104200302d81c8581d0f80c2035101c400000220040c445015903401800b503206096601c0300203007440c017070502030b40d8000d000600300141c42001a41e01c010b40102c010b01d400803600b46501500c0d60400e038007070102c131234405a81040682c807000a520410320781040d6403c840e54611911401d0180380159580181c680c03c01050000c0300b44405040940300d0010400021054100c0035181c1c0c0c8240c0140d4106e94284141700103100b14503811 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 313040890 1250 313039640 313039651
    0x311040e120703050d1a09130201050c0f07030605070e01050301090c090509040b0610051e0309070e01170c0907140703020a080310141009170f070b1b0f120a05070c060903020108 78
    0x280102e421170b1800210344047c001c1c0710b40c240b102552145019a4824020340f0600d82141c0101c0c0c01041106104c0f5a541d100352000312500e03400c0200143d0054442c1e290094245010b07122142940d0a0031040000b50180310003880c00c1148036400069107654102503e40210302440032080f240c02d1801c280072080c4081900401402810032000d09200102c400c607003441441c018240c0e1f03d07078a4502009048c2603466001e50509503d140010810700c1d40c9884001a0f10551012038040c54046d01c14001c0817031040382e8010116100542d01c00030040300000510041b80b00e44161606050555641d0505c3e400c00d0322a03907841e800d040418010203400039401c00360820212040001240640b0008100c0180d42c090310b0001c000800036404010020030030120450306007401e5604054480782c21820310341000031048421541cce20310284080e200407a550802c9103001c00500b036804810f0002c03000c15440607014074100701080000c1d001060f80d00c44004083c01d69030fa00c0c41c2d241c51841c0001071040030b0107400b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 313042140 1250 313040890 313040921
    0x515060112090209010b071712070207150203040b0a12060f0f080109020609040e03070501021801141222170a091a040302010e010e0612040b0109060311040e120703050d 74
    0x40c00005a13480b94492411a01c4612101ea91171482d842c3c40c0501d6441421008071582001c20710307660030000003160a00c134030b80c40d41c210b881c02076481e50090140703001d1420200143c0c004000a00074031401500402e5520a5070070421410015040c0f840200c1d21b03564041c00b050402c03c00207101040d580c1848500911490000340701803085034001074014880c20600c1441699544001d00c021b51051003074a40c0d913034021340215210884240004200c40e5082c5c0e0250009510032a18088040c4201c10390b028843c40013038a022a5840f9442946080000c0754504003c401d0b21080c0d000007060903c10600148580d2101621031990b0a009040f0006980020200011480048507810311460a403011243c091130703e592039001c4003005031588800c2046490300440d0000e0403550100f400307070481c0e0140d841003800c0c4240c0d0b0f84c1d5982031800c5405a00008000e0007030b618403040e03103107030641080c2e0000c0b03168020390341d031440d0506600d0450750096600b00e020a0b00400c03070441c410070313038030a9420035802c000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 313043390 1250 313042140 313042151
    0x10090e18070918150207110111030a03090c15121802060703030b0427020102060106020c2404080106080f0606101e0c24050a0212220515060112 63
    0x12003561552190701601c0661a903c1005038076819520402004082e0444000341e03d60709a11444d40c060740c0482e0b8240c0303421500b00e4555649522802d40d000385200702c000a5400c1c00c01c68a0124041c22001c40c0540306e4110110000c1060320700d8007140c0c9072103a56910396100b40590311141c0300949014448050105250442d140007603240d55049401051381440c00080801c101c800180050100481d20710000d012006a07801d2003e4004078520954000d03004c8a003940c0c0d070341d08100c2c1c0c1d070544000d00c65000a0130004d6420681c10103130b84200f44840380b802260415844148007800c4411a03400480c00e50b2103c800c00c4140c010074012a03811000c1178500c03601da6800c41c5009441c00006035103101407581e0b5284401d500c50f110b41000c480c0326500c00720703600c2e02140150b60f02490b000c08105c141c8c90646040045001100c4510854210840501003c044c9641d41581045a440c102182000a00c00903110710009001132001d111801041120b0030082d08012000501d9520700500022100d8a000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 313044640 1250 313043390 313043431
    0x312040f051e01230907290a03021b011104090f1118240f0309160e060102070b1e0702061c050f060d03090e070c0609050d140a09031209030210090e 65
    0x1050038000e84288a547c41b03811a001d00c000201035942182c40b016030031020418410b80342c0d1507001404401d0103c8180720054210308900d5080740c16584290712845410481001440210f4014400400000d4400034520b24044c20f9040e0a0384841c0010b000d40c4801d48204a0f5032034040070401720055101c0040910081e80c88ca0300402c0d104101842c071008002000150504a00b00b20040d44441d4080008040640d10203580301103543c03e9030103034054050070b100411000b40c04c9081e1a50140340541c03042c841c00207041d4201c41640100750690b040304040000011040b1107580d074105041c000280041e080c501100f040c8869030015284d14814040c55030440b0100380d1286442054810302405215151121030092f1030700f040c1200c0080180d400e210314a41884004154049aa4900d072540140100c043d8a41039042c400c003911400444d88200007400400c03000340f100c1e86040084d05002c940300303490b600041c0490501111880004404117400d020591714405110341000125030000b50703820a1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 313045890 1250 313044640 313044643
    0xc0c0105090a1203080708150307030605040813030c051e13050903191d03010b060a0302030a060e09012004082112190c020312040f051e012309 63
    0x101410904100000c03811056640e20403000c2c80040140f24400300075003c16240c080d0059108031242c50210b81484e0028030950b040c0d544502c20000010060110303e1709694800004240180042d1490034007484110703c6002c41d0501e40c03001d1030003052758100c1c2d01d182004000c01c644140c5811002043c075081900000e44840f1030314040c1801c1114040703020761b90032000382d1660080300f14565940d0761405004501c02e0308400c0a8800c901d8240c8424025035900051601360783c07503d1a00d5400100800c0002001803090b4061500403038012004211079943c0d80d0b109540c01b07816200e100b0242d640d040d10945c2c60040c210328440030700c0340b10182d504281c41d10f40b02a4036a6980034401002c0d2840901401c0151140380c1251290807001c0c509401c1d40c01c0c03401710303440481440111040b503245440c80c0f480d00ca90001050f00c800c822031101070382e1107036a00d03a50200c86070a08202140c1c580310319035800f0b02c5000c6010415803c1c3ca05c800c00000c0e591044418106555012081c0f00fa41c025140c050254140b030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 313047140 1250 313045890 313045903
    0x10c17030c071713050609030c040f140c0a022d0a0b01080d0e2101110d1410030c05040e01090c0303210504080a0318060606081e090601060f030e01020708090909030c 73
    0x412600c031b40e150301032180840d0418a02010b05688030780f501c1d03444e0650039095409044120f149007800f50940d611441c20300510b11540c980e40c009a40842c0c007465020610035280702d0300401ca01c40b5070125104c00601503250044480c2d044920750a81801403210260400250200c0070052401c100e68110710408541d070030710305c01420b6586290041c0c0c00140100f003500101101140100310640c2d031622840403500401c03286454102c1c5085203808075110018a030002020340c1c0d001403079840032924010402005140340d6011910954a42c2c1c40040812441d40e420f00003036000e9211003071038800d500c00c5001c00d1005400406c110920b080140004920110107661000c0322034100018080c29101c071100c241d001d041d8008001909000001c14050352020049004484104844540f4410850460010078044459600986c455001046550710502e59601003034440c3c00c3c00540108910261403e9030b110180070b03250500001b400513982d041803548203900001e00070180d814a403070140c00039219031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 313048390 1250 313047140 313047149
    0x30e0415060f05041707030507050d0b0a1a060703020d02010605010201150b0d061203020c041d25181a062106030c13150e010f05010c17030c071713 65
    0x42003a0000042c0d018508a80252156070440101a4080c049081d61009640411111400754200c00529420542150005241e000901002c590f0f903c610404c0102908480601324230100120211a5140c0c0c00084c140d0a0080e40500a1103c6591000e829204981d2105046a02d014a02030301040e0820400d41960038100182e5581d03840c80500c0c2c0064040c5400c00c005141020b0902c408040d00000c4126920300299001c0c811440c01155062840200451110058001d44e0001d2480300c0041c103030042010412245001c85919000780307001c0001e1414080c1e001c2c036900c0a507101f440c480d404501c118403008480d11841d04c1102980d820b507220500390500c980f8680c4201040756607500b0700c80301d201c00310007405000101700703207100311400b50041003040c10324483e69410100d8100c104403d0707036050391002840050703000d01d4603004541c0d00c2406001521484904880b400c1d00c001c4480040d4050410241810384840742c0d070501480009000301690312045081080303410140700601c1381d40448 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 313049640 1250 313048390 313048397
    0x14010605030c25020301140106031107021804051006080c09060301111903201b0f0309060c070503070b0903060a0c1d01021005010306061401080c07020d0302071e03030e041506 77
    0x41c88085000003c110304010003540342d4200068104400c02d01c0400d28103c40007554140060784590065103424480c004003c2d41003680c000c58188402c103414540c9822911903030413034036650350240303140c01220441c0c0c101040303c1e00590491103a42c9400e501161b0400d4044000304500c154101d4104140d100305007417441d4407408500039503040350003a0321038a00c298a082005155a001c4504d0340c4482d0310400300e6001d0602400044000e103140060303060641d0403401c008600e4011300b1020400c480e0001c52100c1c0b41446820350115003510203021040c01001d00c0b810050302c444c608420142884002000075401c60703c2c00085040c0e0070b902c24a5aa114242560040807021120004030b003001c80000211059a007004000020040c20b81d2000007111038010040304410008001101d07a41c0701075a00b520030000500140c805840c4c5a040c07403030700074800c0c0101d03481d20359103007892000181d030070028013800c0c141440100b051540000401000c0d1000b19410801d04d9540060501c84181900510080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 313050890 1250 313049640 313049677
    0x40e212109030f0406050a080a02120c0d0207050f030a02010e030a08010b03073b010c03120b030712050a0201020106170303072001060906080d03050708010e0403090e090114010605030c 81
    0x81c4010b00032103c1510055001c035540b1615000d01900b0f55000d0a03030080000d28180000d2520909807007030f036404034448070305d04079951100ca402c503004c0e82090000c04600c0c1d0b030820010b00015002c2105c56011200d042c00340d0f03100c1030321744c90282c212452003c0146c0d141d0801c1006280c0280e1011b182410346141d02c0c100c80c1c0725120034008541882c0c403103540c088150802800e035405002503480d00c0e0b001c590321302482050205018011242c07020204002004038424035140f1400c00c1898000000300480502200c802980d200806041c4080005050702e09820581e20314066590a000d404040c00564a40200308484213941556a02c0020030310800c221181d44140100c800c5443d08180800c0168000d10071152a90014030062005218400551154400851940740a801954400d42254a44585503841c00ea002c03040901e005008808000f0050400b03c0c40702c84562000703018044140001481c0842c00c0d002529030901a046481481814401c10000b030585000304c86868482c50300540a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 313052140 1250 313050890 313050901
    0x30603080a1409040612120203040f0e041103151e13020906040e070807170105060a031202031306170702060402030319020c0904210e03100b0f040e2121 67
    0x74020f0040b4154490306244001070755038410b290058105000d1038603400d81c440c5804003640d0301e21403889140d2821600d480704003c02001c07204442d40c024052040448919801c034000303410108000301c1442c0710f8003d40c040c041717142028800180841803a4440e95014206044c030080780f11018000244a40800d90000b08551619002030b2400d070500c104807140c1c6511030b000c0320f40380c249600650f454110142104204100c050044901a280c060b02c0303200c1c0c0900310707200c807501103880400920940c802002400ca0b00211212003034000c00051b81c030076242d9400500c0721081210090440f41c1194409002d000c0965000700448074100c2e01223065281780c400e010070507810202c1500c1d9003903028550f0700400080c0840c010001c0e01d8a468155920401e00c01d4071810795554559040f41030300741d031045844442481081e442244e46400050621a0440f0721000003415510904030000f00f40e000000100391105454600a4010f0500c048940c2048680001110320b2809004191a07141c0b82c03001054 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 313053390 1250 313052140 313052177
    0x61509030c0b0d021b1015050a06080705040b030a05060a06170c1308010603050a020f010f12052e090c050f030f0403050f0310030203061305060f0c040906080c0f01030603080a 77
    0x500085c003040c4c000340148445500140c41e4090080d1460590b410308a03060442400083e0300c6041e1135006200c180c0c80d506280e82295650390050148051110411021842084600143d407140c0e01c0031402080d85d1501d14140507a050b03484d4480000c3c4810106000d01035080c03035544d554420600032131261107803a02d04202025550b103a000071625481c210000c0213000f00450005429030017079030f8884240029000444940d00420001d000240008601d03540c01c010b95004030b0b400001481c1002456481c2c1c141a82d0b0381d100285601c2c100c13868031036003040780078a503001c1d06d000301445050190403d00d00501240343d612000307100c1342401180034000340426020390700b074030b43c8c021400c05000d441e8030b072070040c40c1440891400141d1107841018009220380c40c490765210540c2d9400000b0b40f070366440d40d45c003070034840001130500400d201c803d0102103289913552040c540140384000081180c0b8405d101400750004101484904150401001380042203844040b40c0c0c5004081c038003810b02d55400134a0f01b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 313054640 1250 313053390 313053397
    0xd1d0304030c0f45020a0207090510120305030402010e1e04060e0c07030c020d0f0f05060105040c0509060a020c090a022508071b120f020909010c0816050d020d061509030c0b0d02 78
    0xb54130080c80401d03042e0f402c175030001d01340e015145145000c200a03101c204c40c0500c00601480b5203e0318500e001511070000741b00701c2c003a41c0c0051040c10700100304092040082c44003204c0b11890060101c0a01d160f03070551074140941c80060210500c2d114007814580c0d40b000c218400d411029061000c14540f40c0110b440d00c0c42250021604006101c0160901d86080b54a00e440c8010030750740d901c5204000300c0d036031070b2902c81d400ea81c409544a69141c66151000c1c40380541000e01c1020943c00340201c00806922a40c4d852841070000b0ba42c01642d901c803001c400201c9078802c4d441c401c0f03004902d0710000005005107041720410350f0000f20442e0403100d442030604119669421412401000380300071030801080e0000781e0040d5108890020082c4d03100c0c039041d030803038401203501c00c00a055000414603407500e0710900480c000c5213107000362502d0010500402039034031100e030390450107030346030400c100091240101603041c1e5114035001361071910f1501c0e19a0b0301c1c0380b640a5549480d00000d41e540440c001076044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 313055890 1250 313054640 313054769
    0x521070501141b0310031403091807032a030905071e090c0804020a140402090306040804060306080601061d27071b02060d1d0304030c0f 60
    0x2c1c000402c00014850a030541514040c1c1043c1d082d48600c01c4202646040d288180b0040321224000740c61a00c905844001444405130b090108001341f01c1d80d03444030820a880740f80342c0308a860a90400d103100500300e8030104411004007030507040d4442403104840e030594840e03100d8900451885c409040250519015a100651441d140880c0c1c1d0b101d444004110012034903050410841c03000341e20015541c0c0301046030002d40c401c0e10040e0038840a000352580110b100e001500040c2061540d6011915054042d9011b6400c440042010032003558540500c42c0640480400b8051070b51508501a041201030902e038510029030b44030410950325440341e9407180031107002e5a24404413003031001c000000400d5521030b00007250f240500300301030300481042000d1640500014a011086000400242202c4030513a407521800c00d1500500701c401c001810103503008001c86c101051401121440145d8107a01c286201e1031040031032403aa282c40d02e0380700200c40c112490768030030460a403447d10305005203200 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 313057140 1250 313055890 313055893
    0x60d051e01030507030b180303070c0503040f09020d060b070b07031a09250e0f0603041704080d020105070215060d03230d06091103071d0a06110c010c05210705 70
    0x74800001384000c1140e010340c3c14910030340c54400d040100d140d11444082d90681c41040841c58140c89204100ea115004000f62030809445130b411444101c519480380b05c18a0f00428601d050603641e1203000020648004110b261610580e03900c0100040284101700b8542d8a840402036600302c510500002407005040400324540070980050260b9100c5101003480c6948400220141c0034460340200150018045103801d036215007000b2090307000906c21206010351481e004c0069000c03201a0018000c943c001d04032444040d28000d08403000104903400315440180d0b0340704082403604116070010801c0e507240c50f02d0307032840c01d05864851000c0c030003481c80300c0c2e52102206012003c0020b03100001c146030f01800302c0f990382c0200c2c50582e41c4801c465000c0707842c100041a0464001c2c10210001e020740741c50021034281c120005070343c10b05140d100300c01240c0c45d5048240340394000d00c52141c0350303002420001500c41003038441c0e070303940c8100c61101e40c0120402e80c0d1103ea440480d10a0700c1c2070307031b5100b030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 313058390 1250 313057140 313057201
    0x9090a020a08090d02100e0c03010507030b1c0c05040b0103140709170c060307030b010c0c0306060302041112010e13060e0c010e0d0302060a1a09040605061509060d05 73
    0x100020081d800111450700081450b804500c5510700401c4c8600c0c000c500d40d000345610140301c0c04030002041c3d404010100fa105200840055450a0007241e104441c41c0d18005072400d4500b0502080b5442c400c2d1500d144092080c4040014030320300c81d680d017a21010b41e400102d0450040058004102d807101d0149840112001c200040e6880003111054038540c0c0c03039148012041000d0143d56049002001c4d07482081840000c0b02544a54412000348105145c40b907103213a4151149a54048960000e540c05502c4140620550a043c021020044c070808001480d101101d0301118180106029032442001520042000c90b0340000744029250340140d41082841811103005584212074102980454898480700350a071814281845d2200c0d09074000d400b40d070b910140b4040c014442c1d0b8401ca11a511061604c96558079603807070781841140304080019982c1041d408022269035031050f48840548100007015590b110101a00c0000d04e2070b81c004981921206201050440c410a440b2941480781 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 313059640 1250 313058390 313058401
    0x1c0905030a111912080c01090b0a0c1b02010e04090512040b0309071d01120c03081c050c040b12040c0b0c07140108010f030b060d080a090906050907020a0b04080909 72
    0x4103411026410704460b0281c0038614140070034000f00705032180749413141034440e90001292201e401846520b2100000064080d295551903459107804c0d624250025500c0420301c401ca0b07044942e07040d44402c42c000445441d115540000c0240007800303004c9008648030389202040040401000c0c20312188055900e48494880c28100f240740c10885404e026842101d100044c07040039248403840c0201d45242e40c181076800c10710305038030440c02c052040380c25041d01000007001c80e440ea03018121040c01d000300b01c1a00d104c084802c000340c80c03029000c00201c0c40100805c00421184070f0444401c0e4904009220842c0d986042801c2c10660036404070741c3c11100001c608242044c00b244c84820b41c1c103a101c03108010841d8500440b90b5110901894400300c4550b44280b000c94510316405078400bc0050804080ca03181da40c82210310b810003985900800c1c0c0e000000c1c0080400c50146001821090311000c000d890b080200031f41c0d03410000c001401d0381c00500c000c142440854000c95451010140c0400e40c1400d02 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 313060890 1250 313059640 313059653
    0x606032e060b04061107050d02010801150c060207030915090509190605060c0601180207050c040e0c0315090d02060408030609091603050c09060d11060d020405030f07090c0807021c0905030a 83
    0x46101c2c0e10103801002c6c8081102d01e0419503484059406075900300b417607800c29010041c039140070382d44001800100800c0d000002c4070b0740000c00c511f601c207554060100c0c0c9804800070020a40c079900b441402600c110520040e20b6000f41603500c1031424209041ca02c0b00100c181000b030083d80c10a41e0011400100038403051000106030341200c0b24010315070a9030038400481001c80c01004001402508114107280d080d280540000500803807050076200307450000030000f850051491070b0040ba4030b14110400661071428460315000c10417030300240c519854155241c03919403100620070352141101e0808a40c51404c20802150125060b60066415503101c0c1016651391640102c240d20039040500001e42608088120740740d000d50009c08408840b0300c2108000554018040100e10103500740700026440d501003140c860b8540310540500001420000b0f04000e41d48813481d43d00502150b1802c0c0810941c0c00100b43c20501d03010442d07800040c80c03550f400c0b22a152a50b20890380340c481c011043c003d2016 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 313062140 1250 313060890 313060907
    0x13030203100525020a1209180614040e0327090106020f010c0905100309030e04020d0b0f04060e160504180b100207150c0206070b0112050606032e060b0406 68
    0x809032183d98080a00400100c11030a02200840058000e002000f0002e060f10055004181c41030401ca03a0254854900b060781080201541c1c141940310311301041039241030080150b030004207660900c294691200070590300e1181e0200341c1047c58144040d01c007080e0f0000e84280b204c040040c581c1c146541d44402c02559081c02d03c000c200d05503e0312402c10300040c0250303040800c640c4068078802c81e24045620070b13001008002c50550034401a0004a90f01e0f5880380700614883c00f0300b010000c5c4590601c824450090040c1d016280501c0c500681444101100c00c810b5a000c100340d403a81d80300c4072030010105c60500681c0c0c0200b11802d001104c03010700b0405600b200441c90001c0d0340328071180c5030f20f200882e5541100d21400c403001d03000d810060351880c810310f10844224006800316141618690303403072141280991049280454101c07030202040303030900105030010002c5000782654907070141034900c1d61564103003448010284807021038002c00c40750403d50040184002e9075460300d5580034040c22450 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 313063390 1250 313062140 313062151
    0x90c090d030f090605070b0106080a060f06020706140903030f031518011d160534030908030f0d0903030b03120a030608073006060b1c050609040602130302031005 71
    0x3121030f0b90220304280708805680d1480e401807003c40141e440c2800a40704610050031601105448400202c0c285130000b41c1c51004003120f50081101d1f6142c00002840181c11804021041604100400c00c0355000421b407850701d00c10f005100d80c0c0b40c6411010800c0000b180d5105900444242801176400401e040c00720304a5440007803c0c0c004070447401d01804192001c60f12100406c0074400c1041e005072042000d0030009800703000c80540c02c00114011340c9000d4000850911f0300a403088000201079000780031000901d9950001d506010500142c4000390086d045000c200b11307603c41c60300b018507120f81c00000710340324040c0a03180380b81040022210150300044018000c00e0814000041c0c4a1f000036480d811900705400e012034221100200c1e81110038050801045601504140408610b00307119800003040c2c601003042c2ea880c3c9003034000ca40d46035640c07a071a26941c5042d0410606444880d0031503401340c1e000000680c0e0320140805200a034880b60000b03901031240207403807200c00c85558861030141d0b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 313064640 1250 313063390 313063397
    0x8070203070c120b090f3c0615061801030c0c060e07030b1302030c0f041d03090414010303050a0e060d020a02010e2b12110715050a1109090c090d030f 66
    0x90345c940d10559500c1012000d20f008960000200e12a009900c04481903001c0700d4507542501070708401d2616178030800c4042c400310290405414000181c90002e080281c44000703031150381c00c1016940c40d44202004c1a0290317411f0540fa09804803440380b040003c0c1074031a900101c100050880000d007070390b45404a0208850201e00840450445241d24503482c1141e54010002d00540384031505124100c0315990005800a41b200101001c007112042c4036124400b247c8002c50b241e0b070010f800c00082d00c1c0c2c0340c07100c07800c0c0c94004001840801d50000455117003c2140c00d041401d000c400c00401c04034070a0b842222406440460144e291a506402000812081c041110554801001ca009100780118014007071524900720211840d070040b1560200c0034207501d400645c042d42642c1c01d07041e5074400c010485401240009500c0c622049103d180d801005000701004028040079441d0810700c40c441015116000b40400645000c03020300441d81c400001400000e12584245000b925100251a188020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 313065890 1250 313064640 313064663
    0x30501020d110c1009021804030f090e1510120f02040906140109051005161104051e1302030f070b0421020f040209040b120f07050109030c030308070203070c12 70
    0x7042d802c01581c240841c0306014003003918521442c14000c0c01000b00c120303001000c2038039400d590701c1d004d81550310aa0007a2203800011040403002004e1030035941122241c2c0c500d44050089402001d1800520a8420355480181c404861002e55840112200c0349030b01c24108542000c161926801900c101e482d00361050040d6a00e4148450710740c0ea00700e041c9800509070746010041854201c03c601d4440e03e01d8109070381740441c507100308180c0107150f0030280d5501c00d0704078640409080910880e9800300141415901c20521402c4e1070041d000081e1070348200c4449615844155601400a891801c3d023160848801e01d903101403c01c40c5030010b02c00d0101d001d500c4080c485006829403102a41d603507004255540300c083c00c02c1080300035007180c980e47c4e400c03d079103001c08119601c03404c022070160b481c001c00405080c010945d42d42e15144940d0032150400229900070030002d8030144151090740d40c1401c05c40407030ba842c600d00b28614010008003801201380e505d00042c0006408280782c500500071112003d5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 313067140 1250 313065890 313065911
    0x90501090b090603041a0408040510030b090c0f2809060801120f060b030f0606040f18060e0c03190c06030203060d110604090c02030315090105031e010209040204030501020d 76
    0xd8520062140004000c400c00590b010b9181540c0251342c058032980407240240606031040400c0d04040300c0444003820000340502c0745143c9641c04803e6600c03603240a101d4540d0482c040390300da5101826008404001054500c02602d0710300540312014014141c03883c0041c0303101404100a214031042a01052120790080344092064a48905030340035000c1e0360b400d40c2d12594a500020180040a94085070307107128614255500f40203080d0308a0304c4c3e01c005c0005091203070030481154041c0541c201000d1409400304440501c00c0104c6051076004200051040900a030b004d090100807070407698540070b40342881c2c664608e24684000b64600445900d848262102d1007038080b88008c3d05d001e82e00201d072040f90b90015a548004400b82c2c0b4000d0300d07250409a540c1c840e81c1c1034034488042900980c10110401001446050320013041050459034030f5215450b01010903141c91910703901d115041c11010346502c40f032000750102c80310910003070011903407150f503410003074000d41019194842c80c5091060141 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 313068390 1250 313067140 313067147
    0xb0910020c031b13052e0510080411220203040c090501060504060201060918020f15030703060810050c07080307020106050307060306080c010801080d03020c0a08040b0406080108030f07020f0f150a090501 89
    0x5120306d03400720700765601d45400220320b940e8008015546019000d002d0307010a2a071130702018074200d0750342030b11103001030b0410f0b00e03010b000d00411120550041c9151040c0800c4450090b4400b46041003c20b07005070380c2c1d140c40c180b6038542900c54202d80070183c1007000004407980e110000b00202c4240b64020042d01e901c6a03200001e8403016805611154107500c002e9000d480c1a81040024507070003048400500c800708505810b94108680380e40110307507540340802099a01388a006000104590708011a10303250036400030398082c1d03c20152018030084005487c0900035400039024213801030444200300d41d9888020050100ca0058044074020384068921650140e492141038075800c2c4083c1c8501078180d2400c03002074000720303e41603c81c0325074074410002c01d40072402040904240034840d070b5920300740303003000d0803403881a445040340c0d82c010807040143c88071040660340c001e6412034010203080312610020b140d56100078801580554061000440c82000e20000c010041507078a44000c102d80e564010b5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 313069640 1250 313068390 313068401
    0xc1b1802070f12020a14071701020408030d24090f0e0c090103020618060f0403020102070b0f09090a020d0516030515180919060b0a0f0b0910020c031b13 67
    0x504800b051800740380007404032902d50b016905244100d402c4602c0544450300021140e071040680c982018505003e500749a0490840c601c650b40000e600d40303450241c0e12075491054002e0f80404917a0b42410960f0ba8401250810b482e50711540c0100d505a100c540300340c003c00000102c002c0c3c2900c1c1c1960b00010f0078001c101c94501c840010300c00d41d00c5030320315001d01c500760f800207959544038440c0c0c01008007181d4542c00a0b10940030100c4459484500354400a450200242c10492507004107200c0ea0400446d82812078a902000351000a15600d5542407170001e40030ba0000982214203040801a050340c00c104441641800355030305020075101c1c1c59040c8001c080301c28030f141c0c1000c2a44148132007656003d042c80e400000c043c00f102c0f1038240f01041690b6200300c02008071082c544401041150340741010130b010140c079810030068140b0349040000c0d00144912481c4501605180200801041c0244041180c500005c0c064860040e400d160042440c204503901038801c6180c84c00104082c0800c0c46072 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 313070890 1250 313069640 313069643
    0x20405090f0f04120908070303020a290109090f02040c030f0b0603010501020c0607050a0206030c040801060801020a0f031a19090f0e03072a0902030106031803020601060f0c1b180207 80
    0x2c0c0031512544c460000b510f651042450510003100700008144004001b5100258007130b0f409451944464a8065841d110805200d1070f0360310031030740383c404c0b003160f10840c00e044500810001582e12140d00d00100711100f13034200a0342c098600070b1103403455601a00030101190060300304000381301e00c80081110a010070b020300c50060740004101922030070407000801455000d0011508200000e42c001102c0c0d600446065545840c003280070410b02c5030901648000e0f0142c00c00075401c080003494000c1c84945e08d11840020540c4070f800c14005103001e20480291490090083e2100c00c0000c400d030a950100c1e48030303e0078102d03c0e003c109020928070384034003030398001000007540c40d00d042d5444a20705003103407600c800124034011410100103948041079038014070075003202584030340c9003032005011a0b0450002c0591800a0710079240007035404103205044d1910360501050b0300296140481e0fa041000800419146c540301c04105907080712144801100c5612281c061812000240c0707905034000c6030f20 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 313072140 1250 313070890 313070911
    0x207050c09010e06010507060917190903050d0c14010603030e030c040501030c0302040b221d160e0c0f0c0102040e06150304020907051c05160302120a020c0705090703020405090f 78
    0x480c41c02c5d88120300400403507014100109048040e5103d000f0721046c0710843c421480310010302c03060200c17282c0c800c0c80c211701c20a0502c0d02d14507255458280d120040309290340104104031342040108600314100f02c440542e84030003088056168039014090500018200f8072a00c04e05101204078600b0307004683c141d0340e0000071400d42070f01c2e550a100c050482040c0c441d030310850b9003900440001d4002c59103c01c0458600e80803c44802d081c420310b420005140c0c00003407540002c280390300700780740300d0003e042110a0715002a166940d42d01d01008203008904941ea200d560008003d002d21905402030400d46116101160894460708100002c404c11400264030812081c030002e009841c0403000b0950040203414190319150640304451100c0b174290500071003403603980c018008205649c0c01d441d010300a81d030401311301c7c082043c6203045521100a02c00c0104540005222001c000c051010400902001d007000044d41003e440c06400b030342150044a00403071301040040c103103100101100d40100c90126 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 313073390 1250 313072140 313072169
    0x2b030305011e051201060e0406050402100503271906060f060203030907060c0503040e0a0f0b100e150c0607050d050709050f090a150603061a031e130c090207050c0901 73
    0x82c00c3c010810880d80d500c1e4205d540e51000055201261044103118034810131002034146454810060500c818010074020401c040c01080545401d0007481c0c2c01010368640f41d927010215454042e86032042042c100400d03a141c984031481000442d07000310041d20201011524202e8564404a82c2ca0100311468012a40036800411a450050840300e0030203019105580c0352944030b00d0903d40a030700554411880c682d682407201c004900b14400c2c510340380e2048444800910708960b004048204200b001032040030000e00502540e103410b000c0b541c00074210301c15950245408900030f01a0341104880100c2c541c05c040000b030886206001080a40d48010007070707549041208180a41950010112003406548104c040c2815169018400c000c102542d00894400c0c107056540c4480c190048030a4441c030000c0c405d0190200c40c206041c900b520b0030250b001400d6440701d200141401c02024007504181d40c5540c04170344000d084c1c00422056000d03c04451200391644240040040c0074807a41164000b1030f0b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 313074640 1250 313073390 313073399
    0x209130f08071407030c060f08060a15091503050417090303030c090105310e0c040614280e030604030f030f0b0402040906030b09060919022b030305011e 67
    0x20405800c01e14040d80780c1080c5400000f080c54a0f045041d0000c0d1641700004c0c50405c241d03135004180070800240c1c1e1601d80c6203401e007140030032007880391070160303022000003c1340c2c80b00da540c414080d02004042c92420000c03c440b044002900402c1c0c15502500c19170601503460810303940764030807100d000c44058000c520b107503101060005140c104122560401404003c0e0300b07003081969403195030202c060282d050340d002e4440c6082031500c0140e400f9421002c459001c02c003445502c4002d13201103030224100490007096403a02e4007003610880340c0030b00c034424100d084001007202402e48014030702d0321529204114516001007565a24003100c1c0280062000c030802c13408203100350424414600b9520f00030980340d201000242c241c0e0030071f80040e80455601d1b00c04005000d44003440641014102c00545620304011440310344944d07600b4400c00f89070000c80d5501e011502d0381c621030b0200c61488150081c101180350b1070300300001801c4200b5030000341040000309500c0c8003100f5000c0070800c0d03141681413003840d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 313075890 1250 313074640 313074653
    0x12030a0e06070305090f16090b01030b06120a14090a0219050a03150b0d0b040809190b0c01150f0315090b1609090c0c0b0a060f120209130f 61
    0x2054152415224580300001050400085016480503100030500d86009000306146c200c0c00050340559a000d40c880000304140e60303000d101038a4417a40d020420440500041c1d01808544803296000300000030365005c0c0c00090440315000b4814150184004c0620344d00700c0400b0300064840c40416001002c08500520b413141c03510b4507204404090003001c6964000140054a00ea0300c15560038500401078111100c603840751707404c1c28030300f1189414803402641740c02d401f07118000d000400c05030001801007200e07a68013408004001c0c0f070b44004005c3c3e80e2210f0041c5295008070147c10303c20340c24003103c600e482c2c410024410684001c0010045050300c1e68030395181c104c00015a42d00c0d8550358251400c0410b080f090742911030303a04d1140c030b041205080a801403000e8100d070b100340c40e402e00c0e00c1403082500380d0064245100d103030002015846a110401c0c80c4006058982c01400221503114000814649140e882282c0303d0080b5000d640664034000010010920494000c00c1d0302c540c1c11140d4006107070b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 313077140 1250 313075890 313075897
    0x10b090102121611030303070504030b15040c26090c13090819093501021605010b0a1215020307110607080412030b0f01051c02040902030108070b030103030212 70
    0x20144111000021001000040ca80c46488114110040501030006000d0700c80c0301c4c3c1010120940c002c614514000400030a40d000b1404001c1020215501094a1072a000440c54900b24024010458003101c2d54003d484010300001000080103150003200c0f21134150300055104658010241c0b907564004020400040e410200030414141d86034200e00104852a018002d42400d444503035150100075100540403080b958003001c1c898034440c08241d074540028001c2140c1941c81d418905500e51401e25842c060b0290861107007807240f01403030301c50500605400807100b42c0b80c19035280c5192601c41107440d21a58201e080a80b440030380002c0944c40c001140d0040d030784210180341c0f0501d0310203400c1c00141000b07415110100041c2000d81440b081c040900b0640692403490b0a04111400000012035248411581c805062183c0803400404030401c110440906500c00d400c21591944c81d03c0d140c0c0020341003806a80c40f00d11800f8404950111f14504990503280c043e00209030840f6800c0c0510103950 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 313078390 1250 313077140 313077157
    0xf030a03140f03150f10021b010c020301090b0711010e071203032007020906040218090604110d020d0e01020a08190b0d051506030106060e01080a0b120a060b010314010b 74
    0x203030208002d03a9144100009140114807020503803403080f58030b40c10008503015448506105096658000c6076554000450744d01d0300e0b44400850201d1043d01d80140d506200100c0080d41650034142007804100b1081c410611079105511111040c102e1011124200d41d061000da070100e610081052040b404a10030b07001c1418400d150108000420b86003a25407031100e04a80c142c122004111a0114a4810090790344038500780d40460802c1d00e4902682404000415014069040b1101250722a20b540e0000e668070541181829552151840000000d6000d000400e420300d00e00a180440140180201c2e00402020707503903180c0f9900c0d4900402c5841841003a420031044e503403281c40b50f030b07512030f50b142c42501801b900142000d2482d0503204000c03800c1c0204458466490f02601b070000c1600f040d03a1408403682071801c580d00f990f80020740801070031074002042e405034101440401001c400101c41100b14465042440515070000045d0b0a550b6650300c90303161282003a0041c41903200001c007404292 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 313079640 1250 313078390 313078427
    0x1c051b0c0a0e040b1e010b071a1f0f06210906090303051e09070b0702130e0f1b09010b0d181b05060c0a020910170304140f030a03 57
    0x212600340001c52011650b441880307040701100420083c0460074a0700c59001141030402c3c2d120303e8401c800c619200c00c0c140120003e184c004209401400322842c0242e18501259400044e242002c2d494110b421044010b5242c0e5010024808603400205805001c1110030f20389810010054086590481c40b25481c041103206a03240c00d20350104202e401400d406500036240007a007030800c0c403060808107d0f006458043e2212003014440c5020000035400c0031070314680b902540700d845510005041c0d1b8098400c0480003030401807090015000825000300c2502004119544002500745a207030f1244c10880142e440b816400040108000b008004d20895241443c000341c284c60a800c40c0d01d0f41e00f01000b00341c2c1e030320b04a10300c3c01d80030000c40c07044107016010451301d280c1400803c0150340c6c0d4a0b0301c2450024005e03280741011400e0b0600c91002d290103480700c00300c03840d4003c1039072032510b43ea0342091103004070708007401d00c0303854140c1807503401042617a038080d020740015103031500c05039030600742c010b240d0005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 313080890 1250 313079640 313079653
    0x61103072402040b18030a030e1005070506010e0124020703020d0309180603020a05041103010902070c030b0a090c0f150815130e06060312191707030203091c051b 71
    0x840c000d480200050404201c007542c5036120700390130030501400c0c002014083d1f440f030203403140465042200c114440c00e0032103540303d1080b0050700440b121b000f400740c028801c1c42400008220000410081d0b410388000100d2aa861041c6804440131208400600000360300403040900140c106221100c8032a400b9040c2001e0056903041460340c40720490151040740307941d821040c03007146001c0e644540100002c0b2818881c0c0c80f09410920303640e1006201701c881596000445004112300012284000c540041802000e442c0919556002e0121000d04503000f400c0c4580104198403103c1c6400305581b680842c1015108102205a600e80d8000d0800401860b1840398403d65a40380d100b20940c0040102012840e014154202403500b003018008034402e40100101d103d91050a07420340c4c89080281c2070b200c1c0c0003804a5800e40c5c041132a0180c000003048030f0010402255003540055000715894003c540200122103003680d10300f0740300040c81d400103204120000301c86a5400800d4424080202500c14 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 313082140 1250 313080890 313080953
    0x5070c03121809090516080d03020702030c0d081305090c040b0304150c0e03070806090604080d0f020301090b1201090201140d14090a030f03091e080d1104080706110307 74
    0x42c154103920940c580c640b1044040100030003449850b07000c100f91044280c0c0c260504410903201c0300001502001c0503400715081081d50b13402c010312083e010340980101840562418481c02d0344d444002d024466800311040018241441c04115200d00450500141805c0c2030806004107036101400580d10106405110007581c5403900c0341500400440e242d8032414241901032504008803030303126140300d80204042011a01000c6441d9a00c20742c061840e80c1d4071000e40703120388024130030003201640083c8040b00114558045510245407000c080342d1507120380b00041703405420f9035640b0b40024001562100203440c510990400303410031007541d0101162001544441f85d0318207404441762607aaa01c1a5212024541c000800c05a8500070f1701c0c041c4003a00882e1074030310740e49011000511800d00101002403d1080c5c030010b030740c031410500342c090046014180d400c00b06a0024020003059000711000020070f00c0c041d408100c6281082c034061400d001564483c0e0340c4807000c88070584084040100d40e002c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 313083390 1250 313082140 313082177
    0x5010507060f0c03050711070f0302190b120402040b03030a020703080c0f060901051e040309030308270d140403030c0210020f102003040b28140103060c05070c0312 72
    0x3c100468681d400206031070405c5005024000007804101c071a00200d20034000401e41e0f01000c01601e8040d1842e1901e40040000e5452059440e40b080c0045074004c508090030041403070340c0c02d02860085401380441841c860400d80c50344540c8080c040540d10104007000041c070204081d194030305003201503500000391446501d00380f00d011a0000c0159555400f000300e644003507001c2803101e0784c0d03a841480c40f6240c02e40d005000d1005c10f00000d402e00004000040d90718000303401d11150080710b03403003440701c24200d0005a40e5035040d15500d04085054502000e8200440005a4080703035019a1095100b0301c1c0341e000d000242259450b000d085008004900303940761403c1116200d26207040c1e800040c211841d003124030315216600e02c0680d81450030003d12010410182445403c104043c00031098405d4062070020514004505000e003282482c000000c0d026450030f00c94100c0340a1201440216004981100c01d449040303c0206400c00021090001c620b98101911440c0c40302d0410395461106061940c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 313084640 1250 313083390 313083401
    0x902030c3c040306150b07080c01020714060609010801020315040b0d0506100306060f050d110a1505120609010b0a050706090b0411041b0207090b01051306320405010507060f 76
    0x20301d00780000a020420088280300f040c1c581034030ba0300056459410441450254032402001410241000c10091034640f401c0d41102c80c0240c3c84080100e0a420300210305072565003c0300d040384200250400080c01403418001c40340f240307245029685240c8602020000203102c003400040c3c1011921200c1000a5000c20115003c2c40e00c101c001c520342480c2d4500303682951320582025605c0517038600e04004684803a030742850240c1c1e2100340b06451414030b80c042074103032150340d003c655100c0603040301c0713180a5040002080c0c03000706807460b102c15542e02020701c080a0420301c5900b11450041081d858030341d00c500090507026104100100342c04040c0e03141e1000c80c80c0141c03410380f990118404900010710303142c8075600e0480681c11019028656915000e500c1d0006882064086510781001504036840750302214008090000c6218a160b1a039a00620f4180e80c1149142208c1d1080100c00410340c000d868080d01500324426285040d04100044945400c803000480340c0d1502c0707000880c2c1c0c80901d030050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 313085890 1250 313084640 313084747
    0x3b030f0310031e030804020105030a0207120827030405041d120d050631060302090405160803030c04062f060906060d0f0b130507080c01090902030c 65
    0xc1c807081505506046298001601c200082412000c400d4800a5000007200358040c3c0c0908145032607940d1800c0c050b01034400c0f42001404111009070401050b508003101c24050001c44060700306101580c02c0030110910030003605516640300380800c00640c50590002c1c1c00b058904190521000a03800910346403a0100c1c212011520b170100d5204040d680921400d588600200c80360402102e101100c1e40c08009000200c1c00c5481f1a443c0c0341c480c030360311500720700000e59002d40030750400c3c81d0034285142c4502e00001054070915036454005440e24002098034003c03070f06400400e182070315141040d555565040d44444c14594064500e10b41980d030f4600515001e03544601408040c500350300710500b001070041510303100d8100d0440050100300005034505503c5d0f400380c0310a245440d640410b002e40c6d101108020a188154203001c514650701003103c482ca001e003a214501d00f0381d2074055450a900040f1100d40d0202001d00100680051242c40791054440790820548ca2100910701c071048007600c41d06 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 313087140 1250 313085890 313085911
    0xd020703030f050f070609170d0b0405101d0916080a0c0602030301061b1b031401050109050402093d05030609010615050318010c0e043b030f03 63
    0x404009041c2c00c0b40c15461a1a070501c0c2c82881c001d24841c6160060003882409841795a40d13059900402005076000400071440110041e01c400741810740c0000b61140381401c2c3d000b41e0410000c03c00c410314010541c2d013034400100c0407a903104080c0c0310600d04094002c10700d03070480c030414081c0c041552100c441d0b00080c0040c58042d01c0d0707981680c20080c10300c200b941d01c03020842d402040104641580910070b0044001030074a40c0c0300790365207401c25800201001c001c0f0000c0700c0800d0000401c001c2c604905940d04140d001c024049a1303664000d5104462044501a420920a200141e4540015640e05501d43c1031010094003240300082000e040ca2000c0065001904030a04140164502041000e520410242c0280101810480c0034102540d45244150a00c0004004038403034410240030b0b0300380e01c04101d0003001244460b8a0040c1054030481400d40114600b42050101210005901c006c440480c1501420805440c00d50800c500511750320f91807074001445500e42c486e2001c0c0003140078601c04034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 313088390 1250 313087140 313087153
    0x120c09040b0d05030306060d020904061e0e0c030c0921070f050904080a050a120f0f29010f0509060c070509060102150c070606050607051b0f06030a02070501020405030d02 75
    0x4040c0300884030240d444078807807501c03051050009440002102d500000580700c4c59100c202c25549400a4051078150700c0c0c3c8142000030214400841412031200e80c921442c042c4e0607150740da46114003003030003030700c5000010318100005000d003418500182000c60f000350501e08500008501c3e4285102158000e049070b40010b04c007000320600000440e0090301c1d0440390241203050030b565400c0d4a120b00c1d001003052120115000c2100d17406106003a01c0400c0c425400c0c884208107055030402005030201e0800b0252904410103c03c0c20503807890104d80b01c2d503480d000c00074002c0800540c0e510603810784e02001c0100030840345c0202e40310304011342880d404800080403000c0c105801c1107450000180500e0455001c40c01c1d001da000c04040d15507820051194201d6601c070500d04122000e81b1860b0001908a0000296902000300000320001c042c0b04921410600d80540c1e410040340621002e01564060300034400b240e2000313401e9004042c907521402c0010f141581d01c1010031700701000d218810001d40c200c45d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 313089640 1250 313088390 313088407
    0xc1b150a0510120209100315020715061409060324040b01051008160203040e01030809030606040c020d0810030506010b04080f031303030f02011103010909060e031815120c 75
    0x180591a00800ba00316401c80881c103086040414181108000e8400c2c9010070100300a40b081c00300c40005942c1000e050040281c1c0c1c1000c602c003070341c480142183c41c40e10404c4440ba01090500c24101943c0800342111b00020b020f000b080400880030b0070042d4140070f54182a9001e24081e600550000038a00e0000510f00e000d0900381c0c01c2c031074160300207401780d58002c811140c8242d124814651100004000d500c4003031541d44224514011038001407000c4841600101c04e01c0206000380c07a85010850440d44c032a41d400090000b502d04814a800240c0e01120034081c410b4007509200d517020155040504103581c1c0d94441070300e003080a81c040b00780d221002030144080f51052110080381040ea20081d4944110748508610802841c0f001400b00803040001004032803003900054003841240209035105d5031a1380710071000300354000c011280d091602100034441e00001c17080e100400e1107903999541c0d04940d241880250304a00413521500041001005822481030490b24025449041c1d0141c940304217 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 313090890 1250 313089640 313089661
    0x20310030512040e16050c0303040c21150222030b0f0f06030c0d030e040501090b01090f08061b0c070306020301050f041401050f0406240206070f0203030c1b15 70
    0x3280800c2d0900c2004100a1001044d228411a001116000c4445c074258150710119114012550038500d1808004107000078011400700c110b0980d58043d0f00c0008690304560b07880b03c080203216008040d240b5071020542e01c0340d6940e0181042042880c141c80c442c04164103030703926401e2035400c12903104c140038050143e007243c103004180e448040f052000e403150a1103400640e075068103802d030a00c1509161900d20401d807140c01038107800301e03000d0014011541c48030f8a4102400030a00e000340007c004800c00520044005045401c07030302c0700005001030341c0b107022499004445003102440d280b40100140070140c07004110860041d4000c4000503101e5040208105151410745080740c0700d5400d203504481c6800c907100d081130460b04103d07040340200711140c020038064510340e0f010001400307204080b6000712130003550920608030720341d003503407015620054266015045a140703180181c0c801d01c0091068400c1e02d004100044505482d1035000c409100120b250407420a110b03051800203205100e0802803 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 313092140 1250 313090890 313090903
    0xb180a0c0f020a081c09050c030c041109090403050f04032f0303090415090e070314010c0819060f06110d08070e010e0607050109050a031215060f030e010203100305 72
    0x115292401d074120192200a544506142c40902a043c2c00101c030b104e100c0400040729076050486006000c422850f00301140c8400c0c815076464041c0c090100024510302d050710031840036010710044141031030301d00803c1c032050441c0140210140101007050322008040000940001d42c07082407409820f810400740d01d07a01c2d00c990740003501c120f070304080c2000313843d9404030650346408030503500018500100740d11601c0d5a41d0b250311590702c41e4944a41840d02c8680441d0040580b805040000004a01c86124608a404585031100055072000114034801108441104003400000012501640707585102000710156803209010400001c04a00c0400003408446821030950401d403800f0302c0c14101c054461003400024904200c610381e24401c00e0f5442c00f085d20903858000008002440d85454070950314003041d6001d030b01145403441114100303281405030b032001d83c5841070300e004164a0400195800e41e0040141014152070301100342d10701009201852048514a1401c1c100703030300c0d50800b90305110 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 313093390 1250 313092140 313092161
    0x1303061503080a0302031302040606050a0212040302060a080901090818130606050a05160b07171006050a0e030c040c05042c0c0708040f0308031b0c150601030b180a 72
    0x8084001000461450402e0380c0103c45107040140e920390350007150062045400034025401340c0fa0080106d9226404400b4007000380d0540c00303d44911180c5180031110303010350705c40254001401c00c200c0745c9031840741e0350040d0820840c03000812039010a03a11214503410044011310743c862280c0c4a6a01880e01c2e030004410001c0c420010040c50b4284140140180324030f5801e60b0601c400001c201032090241b00c0420102a00410070126070b0518a4000b000302d000c601c0b8034400781e00b5400204170164400c400e5401103807915100c0c54034000e540071096656250340c211941d0715025019041c0700c503031590f02507241420800da8400395203504100d0210800c2220030301c2c5d00f2007110354810039600e8190390583c0760303001402d0420458445490385410705191040360000c4807083c4407840000204079554014601440e03a107241c2e00d8540110a01d041e0140c011107000c1d104035401541c1000745400007481040c0c0040040c900454442414404075045413815600e40c441d00e0000700812003917698a00c5080c0c0c486c0d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 313094640 1250 313093390 313093421
    0x10306050108090a1106040513060603110c0a030c020f060d050a050c09012a0c0605030105031009081b0f250602061312030209131d03130e130206130306 67
    0x203042c90000155500e036040c41c0100705e40d02c51011115a0b9499a0030b80e4020000244802c421042441d14076011704501d02c81c0b04003003410810415000d03850403068034440b07605100104600102510100c41c140304242c0243c0e08085a82c45103226900d540d0000c005103144524081990b0800c000d0403400c90740700030404640c103402808000000c1ea440800c1100d410b80141c030b24540450030008000300b00b01095030083c06108850b2002500e5a0840c0c05541207132011030540d400c40054075408001c0c0c405081005020070700400040b002451107210101e810340008003204e006528101010703107420703800c02c0f103032100b403124124a1001e800041000c1c0701070141440a800c0780c3c10070854109801640110051156544103004428184a64195031030102d004140c040408a0441e01c08010b118034668100d150040742c05d103980004001084400c2c603a0b015020005641c0340c0000031110030b401030710751003654509044941c05a035440014050740300381c10740c10f034040c01d15501c2e0070004c480310b4000c4072440 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 313095890 1250 313094640 313094657
    0x1605150f0915090c031e0d030207080405040c12020d0f0f02070203030a08090c0306040803090609072102030102040e040c15080c0a0c0204091202030a03060501030207050316151107020103060501 85
    0x1100404180c0e01070074401c00c1115403141e110000454180344000315010b80511852240100c0c6c0465070914084250581c0305641d01c1c6205404210300b03910407143c0c058020f03801040204160304082c2d10001283c00c1501d02190741c91044844134046e03030b11982410f1011a15040e03e06ca0120442c452080c400060910442c0742058540c007113512400358100e100e050204c2140040c000704803d204107801000001e061b64028074080c0303004c0745103801c02c2d01e1410b0140303e98030015074142e00c0024000b0950310040801d4030203010815844101c0217009030200e030555028400090b00031b146148260040348507a802080c8541050301074130300e40d0188030400c401c0020700020322502c1c1140b00c0845244074243d10f8080c15030522800424081c00071340300001c141c00c41009468280a6000c0054000d10b005507505201c015620401103084e4020458040d180707400821840c0d0030901e0a56007100c0c0e05110b03020341100c0880e204021030480b580206100c03a1144000f5040d400c5603414440c000280c002420f280304d6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 313097140 1250 313095890 313095901
    0x105090904080915120606090604030512071203290a03050f0a1a04030806040b040b0d050c1002120d0518030703030605090105090112020909010609240501080f04080f1605150f 77
    0x5d9400c030140a1074051100090200c072251521011280555042003c9a501e0245203140c1c58855000d8081521000b80d107003140f12102d8424015580504e004030401e00da08207400c01c000070317000200f4007213a602500700303140000051800d00c1000303440c0361070401814a0080a08000740c0d00003500010780740070009882000b0009400110703260f006001030300d0004040c02014046001090a503000d1030340079401d004800204100060151078021040d1141040e800790548140d944c0c45022445c01d002450504c2070000081e01c9500196001c00c001e006101c0040d168540d89045a104020a80001e40c44003020300c01c50422810040c014801a541103178250b25002034103254440400e4001e02c46c2d2010000b1505465094101c040a03000b1154104a02100803000e584200c1c41c1c400010703248842100c00203050f40c011858148039551840c565000e640d101e6840c5801580209051201d0910a00080658401d0400c4502425225000603d10515003001c0101400d0000b080118005c500c1020000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 313098390 1250 313097140 313097167
    0x2150d0c110c1017040f06050c0315040605100806130c09090e0d0f050a171003020a0b0c06071b05120318012009010e15030103030801060216050f0105090904080915 72
    0x1413502000d064031100c3c0c5662a240701100f10010020f0911030500b01800100014040250b0058180404000c0c10507507030800d103c00d540141c8941c90f40608889103190b5420b014584803640300368001c0050b90201c6010034640308482101d5000c0000a5030040b081c0040d0351140315134009202080010405000c6441000303080400400c2c00d18100103001c0340d140c41e414041ca0f000113010303080440d481d0303192401e0252968440540c1c40103900c0746400401c0054841d01d42380840d210326980c42d003d410545da43d81c1d010b0f10300802084001d09001d03030382407040780801d4040c0090314040c03011140c5240e032400c2540e50301c03035007080140c9030040c60391410610110481a02411030790a05c00317036005940300c0c0c03482801a14440a81d00c00319800c6001c0403c091450008280110f058912a031a800c4859803584022a51074138038612418a103d07040310144110b152151200210f0441454181d00d065445004580d500000741d504658440c07000c60500c51034641004440024165203100e42c0c1803170011b5140c80c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 313099640 1250 313098390 313098407
    0x30f0a050d0507024c15090507120b030a02010c2301021902060f01150302090406140a061403010b071403070b2203050711010507081903050604061202150d0c110c10 72
    0x1380071740c1390f40400e101e00150540180b46d40000c0c465403081980d940b0541e0708080d000444407140000c0410a89800d0301d40c42c3d1050440f80d80000c0c00070244c0c008682c0c015104458004803e4801c1c58581c0b20b030700d5070a00304041041640f16000b0000d83c48114450000c0a002c000d03104400540d04844100030852400d440540d0455211013210440c1842d000b4064000b07100f0301c0426a00203040440218550102072010890b40380142c4d00c00203501e564070300813900410540903001c404071003040100020b62009019040c15400741510016410350403040a20310f5014180484801c070108007000880381075040e404c0301009803010b24000f2000195001800b501c80c1c07110052030f80281d1050051240d12650039615180c0d404181707990742c0c50f02656429041705800810a00003824600050002d0801e0f014840c100e48844020101c108601e031708001e10401400c1795402c20740c509100802d2b000b6101d000c1e0320071031b101e10744581301c09140800c0e03800e050003413261300503001e0803401840c0c0e00a1540034080 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 313100890 1250 313099640 313099753
    0x114070b040303110d0608030403140102030708150f1309060b040e1203040f0f03050304050111191b0605180c030111070219030f030e03100608030f0a050d050702 71
    0x2444488244590240e0040c2c0d0007030010b0300e06d0004045061400040101306580c0580d00360360000d00240c103054241d1104603425400582000081444100c40441c56000c201c4001c05038030343d0711b803007030041010314000c03841c0c01012545881d410707014030440781715240d04410160b4051144c3c0b4241d202c1c0b1540c400701000558400b150020005080c81407600c1013540c079641c02000b20725080b0890400030f00c41c2d0000d4a0941c0c0e254a461611039610642c07c00700c4494100000f80390a003485d0f04801910f00b800c1da403440b100f50804003800c0d0800504e9601c41d00d4401d01b0303000900504034a640800b1450800310b09420307402a854400384242c03460000e4166081d40e40d0407212803c00d41507101501402981c81c2d400140b41e000c0a007000c900b05500041400140c2d8000c1e0101d0300360040b102542c80a03958144502801504100408254001e1080060400704481d04220303141c912081401c030100c400c00c50b94240140c01841211030103a90500001c3d14076102082d4807034107004400d00029600c01c00b4500c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 313102140 1250 313100890 313100897
    0x3050c0610170d36090509060a0501031101110c10050c0d14031326070b070806010f0509010c05070e01030507170705040938090d050f030901060b0301140114070b0403 73
    0x3040300807500b0495003404411141100390b801c0e541701e640101402c0213a1b590140e40c010003002511110961041074100c07904001a00740100380d110044d0fa82d040c0710700468000740584100d109054a40d1041511728107040d568013a03451007481c0c4060305050031003105404010b01c03110032014200482d010703650000030701d600502c521003041c03900c0d00800b2084641101600d04c0c80841e06c8260b1200d48c060034101d401441d00c41601c2e920306104499401c0100e0f4154081a0720342104543d40f4856000381803015818108250b0004030741c2c880754038100311035100d46c03130342141c3c0d10040c001c0001c00d229040040844040c940358011030ba49400780c0b22506801154011595244030307009000c140141c00906140e02820708a94020540007040680404100380c842242c0100206004100001c2c642d8511034840c0d40741800c1c01c2c0030001e25125540060b246044a41d210b002c04607240d0b01c410000d500a003050891403c040102c81d0002d4105643d007051010f04101c00e1201c880410074080e070b91544242e01d0324 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 313103390 1250 313102140 313102187
    0xb0102100b0406080d080a05060607020315100b2b180803090106090e030d0b01140d051b0c0601080c04060b0d05040c15120e0601061b03050c0610170d 66
    0x90100b0014080ca90012011748510400c4640301904800c145016000c1010b06000d1a44e9450510240d486800c5000b501607220201c0e002a080d1281c0a1913000b841031f00030304907a11f55a0002042c03d800c401140360384c450b10406c1d44400c00c59424030181c940035500800340854400074221000c0d0000000b8090280140000015031200003075100d000500040b400400010306a003a6050362900103d40c1005403034079090b000d0002c0d600409000c00962403c0d540e10780750243c2038000d80082c00c2c000d0075045800039680a030107094400003000e0070640302c14074001c00040d850000460b240c04c0c800040107004506d0800d0911020301910100d0794250000300001c1004e45443c6440000020b655000300c030001e00d134014070f03e0220350104107210100041d1380240a0004c425140319115203080c42601c000c19420340a100500e611030820380010390080c104241440b410381c507041d04004044404000022804106015207a03403881c15400a620204c02082c2c00000440c0181a100c045004060140d4205 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 313104640 1250 313103390 313103411
    0x1020703170c01020a120b030705220216080307172a0c0708010209030106050a080a0204051312030903120905060c0c0a0204020d0b041d030904051009090b190b010210 73
    0x80c00b01e5041c1e00390407000315624018903130300402900200c84c005482e9420008006094038001541c0da0540750000e0042d1800e4101c0705200304d4240c100000d0190386c513000e220300000e1031106000300300c6e201e021760002541c900d005040101000b4600c241c0c0d001c45a0040103202c0a04600842c4480c00060400d0b5880c074010000a050070b1405803001961b41440b03440404602e40c80190041d0985800640003405456154810084000e4a5004620913584810400340240c0317030175003165802101c41d160014120f90940c0780c1840c013900d411480002300e5100d51000082650000c100000108502c6040140484507620300c1e4a484019000c503c6950010615072030842c018003d0002403607004104540d6600ca0854682c060901c1d000341d1032065141140f043d40558504c40030305206402e8070003851810002004002c003c00d006024449291000d0340d0110ba000030b0752164042080c09040a0701d460300e00240c01c01500e005941c0d580003c14105041d03d04240d800081210008006001c0030030f401899 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 313105890 1250 313104640 313104683
    0xc0f0201030e160e06010e030a080703140f071211030304061d03120901050c0403050601060f12090f420908190f03090f0b090c040c0512010e01030201020703 69
    0xc8a1100c41e010b01c1c0c00c4401c08081121000040710303030f140307003640e19961a500196811f0101c00030300c0390140c001c012001d00086440700101741547c400c1c2044c00d41607000c0b5030450040d0304001c0d0100114000043d4641c28000c03000d03000c500070b0090785002e10f40c2c00520789020383c0300e000180004000f2603e40150703440321aa40750004a40c80c02e0142100d8035406c1403140d40c42964020344504409500e40ba01285c8108022000c03101034070741100c01810340d64a0494100c95507000e0162a200308a90b0744c011509850780740c01040030356070088107100034165040c140324a404040140c030740d0700441c50f2051a0a0000d0100b06801402640c2c4400c0d01c2160840c80084040c1000d20b50050040000081000001d010200000c010031000e503100c105039402d007882501282c1c03009401a04d0000001e81d45000104500025a03110398000300380d030340500d001004901540c0e01111000003140c00800c0c00c8002456160001d0f00404c0c528010040380e51450300040c0d1200100e0101a0001249040b1425070707403030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 313107140 1250 313105890 313105901
    0x9031606150308030a0209010e030c0d14120a0e040f05160c020102010207060e0607180605030f0a0b0d12110a0c150c1a01151e2303040b01090b0603070c0f020103 71
    0x3080000182d882c071744600000700a620440400740441d142320100003007410000380804801d0340c064a41c0340d030701c40641c03205100c00d2000c2840384024400c607041100b08005190180000d501c4580314142005202c02c20041941c084021428025140c90b003080840c00701e1502d021544200740c200785010410500041f070181c454882c0103003503907040101c59441e40310001400c1d48548002e83d60410001704040d400c5900c21501e101d4100000d4041c8003103111840e120704800d4002d80290000151a154040803d1b11650900c00c1a10841c540110940000d80c00080040015040a010b806840401ea4482c801a0128024104290b41c04240703009114050386101c440c4039000100c01c02c0d140c1c0c203000c0e0841c030f0f01424080c0c1d44914141a000c0144180964808916101a4800190619440d14084a0300504540c3d4004103c00c0000c001108403410740095014501500d5206165810302d040740702034406000015018110404c20811603560100400e1039140d44201d080d110840c0c503000403009003c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 313108390 1250 313107140 313107143
    0x302090a050907050f1b0606010c120f0e031b0108090d0c290f06030129010c06110c0f010b0102070f14030a0209010e0603010e0f070306050a18050312090316061503 72
    0x1840006d030a03042400103d020000c62071140c04480985d91002d004441a20b0204d800600e40741050b034644004600420901d8000032a6180c0090344000382c500203442c001f8210001500c600c5038132010038055038094100c0e5400b00e0700c04000c0290200b8842c00074428100c0f40b5025002071040e10100030314900319001255180c00406100c0d0707090404445100201405540c0315200b50300e89030940402c00c52400c4403810b140103080031030f413080702240c00642e207401008900300ca016644000c840e840070740450251100c441050020070000107144030450071038440c2200304d41550705c5100c00f0003241c0b44142c042801c0c2c540038199442a4070b02000408d29250b44280025030000501c4004109a0490480d4901c5244d080740244244003018007041c0d126040f00380d510070103801001090010072a2a0010394000152090000e56007000c03402403030b840c901200d011102d542001410202c803170805543c1c2600801008051898412808940e8108440e405c0d4001d081548903860349182c001c1e6515007200a6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 313109640 1250 313108390 313108417
    0x20d09080c0616030b09220b100e0a0e0718060305240f010311100207031707030215060f0f1210021905040b07060b0d050a0b15010302090a05090705 65
    0x40c070344040c0e0582c070380d1401c48060b400e01a540030421880741c07290107441d0111740003611284080c0c40e550082070618000c0000d10b004480d03070a40e104001454942076a10a00035032102d04d1302d184c1400c019600402d80a81030310503d9041c14402d0741100800300340b00080360034010060f1211854492514050181750f4400340c040c1c091102d40d0b000608548000c803100c2c400c809104122917841660203150314800b03020191075428070050700e41c440d00b000403111010314004e004a8820503a6940c41c0c0711011030040b051a0040c40100c1c020041580401c03c4180505000210000900d010804a000103200034882803152411441e80d80d019160480c100200c603100b00103684012103807844c1140a584011440945000b81c2048600301c68841c6003074600356445002d1b00d42c0b80c509a0b0b1500405007107600c0392103a01241840c0080001541044000c03165885070034501a00e14104c02d8580420f65850f040c0c3e07044c1801000564256503507001003c059500c02c0f20b49020907200c0d81000c40d001d00035944002e144 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 313110890 1250 313109640 313109647
    0x9060a1509050c04060f1b02300304080c1017040609080d0b1306030f0b1510080f0703050c121005030a06021c0204030c14042306011106070909020d0908 67
    0x201c80d41100138005ea07800c0307880324000020350740f400700c490b01c041d0a017441c191f070414003d1200524124020104601c04000103411198024840200142c0310b103d5042c110307880041c0421154509011140c0c0b0b50030100c56044000c14455406003001d13650081e10500c0343d89031000202000150341c80780e1500380c1c0140d2001c1e01e42000d5115030008104803212540f1624518a00178945101406000143c0754800418016080159a1000f0a00740500381030310302d10306000642c036151034404412103000119030706e680c0141031180c0104030003000030f000b034010507040c0802c00c480d0183c801d048401e1240c1460500e80d2540d505030006040700002c0d0090b60b4140103203100d5005000d1613801038451751041c581102d410110160a4030128803c9100042c260540d80c0010464101d07403460801160802070400300b0702d0366590101040e18840040f40030202e0f0344a0052240959101e40100d1101b25000000c0459090894010f00000044d200780c900359500014080c450013090341045607465401044280c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 313112140 1250 313110890 313110901
    0x306012c070804050c09090c062104030c0303141e0702010b21250515070b0106030f0b030a0803060409110604030308090f0d0905040b031e030d0c030509060a150905 72
    0x842c801500c0a60f014815982c01c91100d1a000811740d0181d610039005020442140d004e0005941001402c0021890050860201200d103928203c2c031840c800c1d0b0300d80929012610340501240c0650300d0f080e8034106500b04005030f1074181c00290a1402500030f44620300c3e640d003001240034040924840c1d07080710500070f900e000e100c072800c000310075900480c00b91000140082882a242c80703100b00722021000b10550100000d04141c80c50f01c4214207001c0d14103291104985031050b0410083e070014000070394070351524103404603c0c85070307107010b8200301c010b800458001d0b2920714442c000946003a2003140e66044003820404804800788041901800280d2699074909010b45070020484006009004034441d90301174220100304004603048030348941070b41604020521004040360070850b50180304c0c00c103511811000109040c8032401c0c41500656070354003500d4480080d50003006505043c50b0408061040851004c101c1c19440040841d0004d0300f604900d807080c54682e00c40d48641d09491401d0140708 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 313113390 1250 313112140 313112147
    0x31d04020912030d0b0301091101140d05070c06060e130305090613080307210504090221130c051801121109070302030f060604030803040303110f0c0304080c010e0306012c07 76
    0x4280c4c0310007608019101407030007414240c800011000702442000301c1c3c140c80075030040710781c11094003e640101c2d00300030030800b10008a5409555610218007007205441c1002038034000c42003d01155048082542803100304441c100d6107100005080c08000708071512075480f054155000750300b4440c501c44009544100e519125070042c8000e80d48415807441004a4030300c402902840c1c40b1007a40c4040c9450300e801a4440250000701840f0320040c810501d005410b03a5054400f80182c0b840e2440b40fa40d50304030320780464041600d5121b140500d1881070500c2e0113a01c80360190b4119040c6040d1003151000c83e1a05100560099051a520200e414280040705901d980510b00c200f1030740c00801c0d00d41d103030a400c01c00607010b5480000d01007801000020006842034000340304483e07074041d885040c810b03005100d40064002c5040501d035a0f1000ca03007000b035030b8820010010a040e082c03c00740f0080e40c0b40700c0400c1e1101414004c100681d0502c040d00744014401e800304105020303a500c5032280c030b03081050004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 313114640 1250 313113390 313113397
    0xa0309030204050f010302030303190f0603051c0306050d03050c07030602120f010603060b071112030d02070c09151710060311041a0a210501090506090d020703031d0402091203 77
    0x10382c0507078542800039007240000980b541c1030f603400400543c115902d00040c2200d05440c1148203040741d4035441c071442c250314075000354405035201e02c001e807102c0140d4440802200340010400410541000d9040003141c864480001000c2d03014602580c0d1400c0c1c048105241c0070083d0300040913a880022901c000402c820312882c0901d41c00040e030382d0641d80e120401c500307440c40781c042d030f070000e910400c04a800202181d1003034001250107001050031041d8500d50500b5600310300303d4013018a40029804080108a0742c001e0040d12107440c080105c510b04846082c00c804450140d0384001c815075002a408000403c003255000300500310a100300740d00c0740307000c0d14104101d410307041c01542031900291460240c18807981311500040c02c2d011a0514102c083c02030424440402180c100ca0b106c10b003001704c0c10a0017100900d9004d140200107906001c0c0740c4604c1d0507040b248840c01c5421000701800048c1d48084500400d47c0e86110070380c04031202d540081d0081c030131401110b40c000d8002100f91034402e80400034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 313115890 1250 313114640 313114643
    0x6160c090209190e0f1512010e010606031a01051b06010303090501140a0e090703020f03040c0f0f0e0f0a020c0d090911120f1b0c1b06120f0603030c0a030903 69
    0x3074490046114000765600f400d0340600440c1e00d81900004c0e100043c4000d01603841491082c5410001c20301101240581c84100c0300c1c842c040c0d44501049290140034000c50f801010340c3d2404001c4d05c2f401d280035803000b00b07110a45604000b000030b02e0890100700059a1500d0301d009005075409035941303180260000c0301c148070341e5010604809584258603111011780e41c002a00342c944081a464407802c21404880080c155000e02d035090040007401001e0001651190f0b00c550000460304d0304200c00d09100d4051544403416154583d803081c40428440204181c01c074a841550f041c89442e0b0a5040c4040d0145a102864512621100c0052558030a074903200301c0309041070402002a9000003043e040c41a41c882c0c00000c20a0404641c5450407815503d90004c030605072070350450000000752400c2d83c8100c100040f43c0d8410895036585202080f0400b040841c22501c1c1d030321381490302032180d4061134000c0c402c00c5403520340c100040003902d0610445211000031400d803007845205140c080c066403500e000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 313117140 1250 313115890 313115899
    0x1303200c010909051927060e0f010204031502160b070507060e0304080c0d020310050c0409050603160306090507032a050301140609040303091203050103110906090606160c090209 78
    0x80000c842c0001c2c800d060042c2401700b44003111040808202024000d2617140304400e0001c01c00400c003480164540006107840f851001c51410490050340f80381220f04680543d40342d00c100010070000703443d01d0120180c0c082c01540544c960301a40700710059a00e0210707020300085070010070040603580c000001c01c0000e100b0601005010203054166a0740d0185000c3e1050561104104c500303149464080f110340540300408603407640d180a190f10054500a0741c41602840000ca4144010348090007480c0d441031003074000b800580c01102c88017181d102075102c0904a03e581d0010300b024004240301ca403005d56000541114040f190f50352a0300c251185102c0400d2101240c2000704992030103000f10300f0032460302a81241d035504c580040016a00c1c002d001203050640d60341c00c81c0d0014075021041c141c0d40740d99490006140d0701d541000e000d4a48203040322445110600e041103030543d50600c456410034000c0d00c0954a4005640081c0c4296050110240c80c04c4548040003450a006400804215400341c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 313118390 1250 313117140 313117157
    0x605030604051f061110150312030b061b1504030e01020c06121f0906030501050f0105040506030a080f0c0a1b0605030417030c400b031303200c01 64
    0x2654101d00c0842c2e41404003003c2c00804200401c0d4031680780f445001154106540003007100581c52402c903a8020144044403000440400c244885240c040440e00c0c614201840340c58540000903000e0710a816400820210391101001801810404d0012407030351001661158142810060410716060081500600c903442c812401e038101107082d9254640b4540041925840340c0c1c4542c0c0d42e0824120446175000c0c1b621400040c94003803800398600450080000081509200d841020442c505801a82c091403c000c03e000c0340e520005074014405800000d01d0761915035211040007644640620080540700300c500700414464020160540c1c00000d03242c0d03003903170340d606c4006859600085402401000c1d5510842510440b03c8008607840006458000d2074185010b0744402a0a1500040e20180c0080f410045c2400f01701c0e05014103801901d21a209094601000b4000d5440300030840304400c80c0c6804280c080500440070708546035002e61840e00d00800720a079041d50786410300203c900081005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 313119640 1250 313118390 313118401
    0x160801110f1209010e030726250c050a09060e010501020604020306070e032d0c03010b060a0c14010e100c09031106030711070f0801060b0a0c140309040204060503060405 74
    0x1800c5901001c8a00030607400e10032000c101d0350282c40000c040402e907540315a05003007290b40c10f00c010120765204d5101c0000403000c011660108041d5907849806030581004404900c0f00341814059420b25100b80303070249540c0514215020740d6240c0e00c115040280c440c000315803400a07400040a0b901051846203e41e0b90714001240c0c0c414080d58003039010b8100b40301103256a442001d000305a0790f40038080303580400c0c040c0708031a500640103060440d07081c403c89240c1e820105c00e11440d0b4041000b14028015400c01000181d41485401c03401c4050100d150b8120b03040011002000c0307000300c10035001b00326001021171540d0300c9a04211200d07503e039141074451509030307000e298140d0580740c2103009079200d5403081003481426030000c2c21103024441c105119501d1548200000340c05031034070b5607841e4615071812001900b583c00380d81007042c0c40207080c460025025808003100166581114100d60441c003400c0c1ca0600318800c041c0a550040d000040101d802a0030000541c040e09068500b000789a580 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 313120890 1250 313119640 313119671
    0x1302090603130c030209040f03180803182101021c050408030703020a020312091c1d010305040305040b0f0a08060f031f150806070f050f030402010c060608160801 71
    0x105404280e200c1001d00c04945402041d14081c0c0c0742d18031803605200702c1034494000030020982200c0031075211400100050406511203480c2d031060b0054042d040205050040c0191240a0300d010349000c1c41000101074000d50301c800e4840d640c80d0802202003859040c60305110301035030000c1101d0404008800f440004140340d413143c5403142d83c200450030b0550302c5181007240030350320400503103003144818029501000d43e540502409015400000c081e8000c081296504c10011b91084205000d008002036803403044000402410140c24a0001500e5a8038a015615400340c2d41150320013000108030b4045000340a001000f200c55240c032004180c0e6140e00c01c010466144120341c54268010300000c124042007801c0315019102070ba000419200102404000d60f48940e0340640142c0c0d108609103c1c0458111940448184c1603180003841c14010b0803940085200140c802810825034071030050078403d0640c4400041c101c640181c0d00341c5103003480488140441d501401c0500e5180c001e0340c02d640c001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 313122140 1250 313120890 313120897
    0x5090403050a050906042403050105302506020c040c05070201140904020a030516050408070b1c0228030e07090b0a05030a0f050c090106080f1e09010b1302 68
    0x28180e0703589241000e210400c4625800840869401000030300c40415000100c03038015a0a0b941c40c8903160021210b90002800c1d144180c0c00b0602580c0e40c00a0b1183e03400a0b5544280003000c1821100b0059406280d0b0502d0014250807521514040703d50154a111a01c4492800c0b24603c1e402c44400c860031000b048200c0c2d0212000e01c0100303808100c1040194040c04c1c0380c0744261800700e145c7c1c0c00c0050341c10201d42660f00c1071000f180040d6441041001240c8407814603103600c0100d203805410310307090a2082e592114280100018840007140100441c012207264105429148006548407a0041c20004146078000c504000780401c036641c8121141c0b10784505c880599400000b400c10514104a201c0102001e098240d004102040007240c03548041226541480c070070701e80c0c82c240c0649030810904142d01070320700e28400c24007540100710341a80702e41c2442d00000c280d4400c0c8a00c2e1180304002c3e06280b001200c051101c4540800c000c28483c0c10740c444040720f0303c1030350741d030342c6000124102d0000c921 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 313123390 1250 313122140 313122143
    0x30a08070305360a2108010e0c040e04050a060204060c14012c0109080307090315020c030f0a030216150f0522080d0603080d061410030507140d0f0501050904 69
    0x1d40030118030100400104121440e0b280d0b00040d40c000c90b54545030000101c0380b48520301903c0359044801c00061b90b100785118018507064600c00c190b4200340240411a119902c548103502c2654404241445824426941c4c0d465000c201151755607641c0601510880c2c0108050355203007d2500d11200405042c0128829a400450b0038004980070956070b500304c40258541e8280f13503681d0300003100040c0c0200c0040d03001d220b240e100c0c040f035a843c61408204900d55803240605403401445218900311001080d0342c005181441c1c515165a140c0000328001d0041c4600503018401c3c1442610a008400c0c0c080c030b400c203150190502c007000060b027144c0c064807010b80d841c640161030a07021143c1300d2484245400c00a00c40c070382c010719014040200d40700742d40b0035400940e00410b0000d040d507803000061140100400d09003515032076117400c00c40062007120141c0722000615407544001404540300b11520984290181441500c50740386a4041c80201401032440d130b8014034000c004249850034403451445a03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 313124640 1250 313123390 313123441
    0x402010207091808040b13080f0a021e0d120f020c030705060702060c0303070914121515040218030105090f0a140102040f09021c060605040504021b030a08070305 71
    0x54603064481c8010300c100d41c06042c41160b000c030440000b0f01340710f0080c40140100c050194540c0e03101c1e0411601e03012140d1210306079900c02003c1c418408400f15408001765012944900d01076100036050800e002c5081219500041e080b00c404101f00080b03041c2d04542405603540038185001540980c0e41d1441000704940c0356014400805c903c0c54413100402c100f07803029140904018600c000319107540c10075160403010800003201444150703140e180104801e02c0407038680c2903018040414030b458040340c0700d2041a00e0181c0700046c141c400181d501f01a5424040d0045540702c40ca88081905400b140041c14400d5080101180702c10b940090140d100c0c4040304d002d000000c0b0256206c08000c100c0d000941c800355001c1c4000600c0100c44910390000b000e50980c00740c0e64641c801001c03213410641210411001d490301c0420301c00c4030b502105490070307202d041d20010b070340311380810090811100381d13801d40b852403000040e443c0d4030543c04194140070b10540d490a001c680c03a40b03008402c810a2440780c40240 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 313125890 1250 313124640 313124653
    0x1302040602011a1c151d06010e0c07080909070309080c0307020a080d0e061b011407030c03060803031801021608071514060603060d0f1202070501030e0a170409150906090504020102 79
    0x315103140f00f00804034120100006d07003598181c4048048002403200c440654100000400154a40f03421013a881103070b60303140c10300d0030342269a413000038043c4000807401303011507400040c1200c3c06a849411101d80046800d512030340c080d80c4050756a8482e940c01c901544000700001078121000521041c0c5030125250400c58600d800f00303121240e081415003004c80701292440316040e11080c403070070f440129441c6d8403901c1c0740703080c04015041c0e80c11101491300f01490304000b0025100301200b03490b00141c001081c20701e00e203d542d079041e000e8040c88100b101400400f034400020044098018522644998158050780700088044002c44000c210380340000c4004c000003843d0743c94030900131365025000902003d010b50054550324246a0040400c44142680c5500040225010000440100740928080c04bc040c035038013100f41c5420409200618000241b0200011542e40d003040d40d016203440c080820036a01c041d48003a41580c45407040b041110f280000c0891003a07800c0c040d00e40b26503010b03002800c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 313127140 1250 313125890 313125893
    0x203030708130902030a092d0b06120f0a052b2d020a0323040b0705120d0b01031802010c0b150d0f0b1807030605061302040602011a1c 59
    0x1254060052141d0704408031101281807541c5101860140503a800000764540c03ca151804500650404034082407200c0e460000800c401105446042356000080c503026880725800f10b800c3c04130040c3e07880b54900034603202600b42e0100180501a0a01410032284503104113800f009001103443c0da0400400c86503294602d0f224080c0f040d400c24000303007170140811101c0c90038940100304103a03d4480010382146a0a0050503400000f03143d003089444000d5110903900c003030741a610b2280c0c0c4140400002c02096034010f000c01800f0320359018608040b03455441000303802e44801003041584440c0445e28084045001c81c580c010072007502030b410b03159440c8400041d100c11a900c0340c01440c82c2d00071620780d075a0b030050303445c1c940c507907030403980b0440f120b843d10310552a0141c1d0108000380700107018044d0422041d040c800010340082100d0300800000352503200c45001c152504803c1841c0524070b400010001000e0381c0c1588001d49032600c0700c240c005058100c078100080d08070141c40d14181c03819455605030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 313128390 1250 313127140 313127153
    0x19140703020f072a090b030307060b06040302210601080c060a120f0f021b0102070b061306080706110f0c031f020702120a0201020615011d01050702090103151802030307 74
    0x10000102d5401d04184030369a0300d45030034415032442038800307a0780030b203015000903c0c20004026000048050200d1003c206c0400d950b80222032000d85025112940019607881d0081114055134016002e20305141320150200d100300a02004c520f07140c0700b184000904840042081d8114031801001e2501c0c1c202d40c0281220495400c20320348006a56030082150416014420481643c080820250300c40350200120030851008032081902030b40104450700000701d40c3c0d1440750307029808488400c40082174009000013044140c020051502c58500f01058040e003100140e28480d5440c0e048800512148000300c1d1240e1a41600d5500f590266070b400015428403000c0f00000341c0c03645001401c2c1100381d00002c203000703404481506190801206034042d03590500840e0ba21652050703400d4900300c4000d00003060704101100701070405003050803619450313200300d0450b000544c00400b5080d2550312030a00303416010700d0103050061103291100906035100510342c851034254004000d9030418111ba00c0740c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 313129496 1106 313128390 313128397
    0xa17090607030c050913090f0b0108013810020316060903080906010303140a050d0e0c010f0207050109090510031704080105060406033203121914070302 67
    0x80717082e04d41410060401400b45c500040621017410b09020b4004010801010091050000111808150401d101d03103440c2510f80b19500001c02d0207446505040c00c2059150002840300345190b15002d005c8800160182c01580e103042d010702d000c85400d0748508001c842d5295a2642c44080c507500801e115403203552800101020b5043d910042d1840f5244c840d00442030600042c94500e492042c002c1e200342e00783c0800184000540141196100c968030440c190004888a6480d2207a80c030000303d1200b03c8a0685680350520b080084140260100600c031f07071034852080700d00100041c05800c200410050692003103440f24100a15035003520305c00b400c2c0d2485541040070510200311000b4002000032500a0f00c0c000150b500011000e40c02d05084501c80c0e640404a01001c8d020360700340c819403013080b8410081051640c9004098226000040c02c1c00c544400304001402e00d031301a6004 = true := by decide +kernel

theorem cover : BRFrame.Cov 312949640 313129496 := by
  have h0 := BRFrame.cov_init 312949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 312949640 ≤ n) (h2 : n < 313129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
