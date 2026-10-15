-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4104
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:35:25.191296+00:00
-- url     : https://prove2.me/submissions/e8134fbc-9ff2-433c-b5b6-a5702de577b8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 737949640 ≤ n < 738129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 737950890 1250 737949640 737949659
    0x1602090f09061b2215030c1409010503040b180a0f06181e0f14060603070609060804080306032a01030b010305011511030f1909080303070801051e041103090601 70
    0xe46088410515060001d8101c0c400300049140001e500c400c0402c144544440380600c5c0300c40e9090030000402e4039042c0c1956129400103658280c0884601040d05104030900000c005c0d02c4058005044152903002003503807a20003505050030031001604880d41e103040b91501c01e0709032050b81d100b911300c28500301e201000050320784100c1c2c0400ba80300c0c020141d0403602042c2c0c4003009881038801e0300c42ca901d40344660b001030b84680c0500001c4100c0e40c000e10083c9040001c05180c8040c6030451020418010008c00000da0030596180c0c01c41d0b440b15050f41c81c0e03516500440e1030100c0000b224003880b90b65008150a0301c11100c11041e1080c000c2c0d07814803c81a90340010f40c00e403042031055078103003440504024040d42c41400c481d01c400c280541900c0c41d107001c01c2102c115981061224148082c14104020940c07504081700900610340301e00a5821882d0481c4043c04694051007002d0082104148006940b0003191850303920040c010b004002d518014041000640c0040f9126040d40c4298800031030414030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 737952140 1250 737950890 737950921
    0x70c051e0a0b0c0a051e0607050a021903050903100f0b0607080f07300207170d030c021c0c050606030f1b010903121805010519051602090f0906 63
    0x5024a41e14502d8848140942c0c0c0c40701e010000e55000d1140c0c80c000091080c00303904848030126a01000c4140c0e040d440605011002d070100060000801074210b09540201c0e00301c040351090440c0300f170400700509040e81c003817081e80c0c041c6605014010414520b21415400100c42d4600c04100308050090007003404580e01c605a005403441c0424818682d06007088401031804a11a40c5503807441c2800c83c0480c0201242038011140c40c90512015014890741001031000608085e401c2d66a002480b41c3e060341c45006a00000c01010f842d0188818064001c0060400607119410304517080c020484004000801c0c201084845014010200b90b0901d8009880a80042c4040c082c00300c1019481600c05e0982c08881c0007418080603000010220312011417445035400740e40c5031800e41e85610b07150112084000e401840c10b001e8107004124810305201c1c3c00c0c82c0c2d506094100a90742c4c6a500540341205000703c2c00081d8841d080c40100b20039812030741d00d824080c607025000c450b5071303072181601f1041104 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 737953390 1250 737952140 737952199
    0x40617010510180515150403051603021c06142701050c030718030b072a2613090b01110106050112050403030b03060f0601090501020309090426070c05 66
    0x3c0c0303409000b0002c2e0036a4405070b0800e00c0c2c2c60b94195102e011001080151806111401c0300d0700b0003160410a000080c481c49400c1c00c44080c02c0c0e400c10b401e40d070000714085090014a001095000c90702c90401002d58071010404a407103898640d030780f074100d10010107032140d4482d004002e4a000c0e08001285c10500407903004131703881c1a001d81141d54001c8100d80800c299004c41c82030f002c1c42400000807a03501400300e40114000c1e99001c101e03040c1440300f0b00542202c424444862400c0c01c42d440082105001e458899041d1144011060114000b88401c1c900510081d180c1c1c034001240005140041d0354443c07049050280c880c80503020710344400c00d00700c4425100d0b43d80031810184440521420562141303a00034032034180005c0703460740c110103e031070180216503124600321080148031840d0780012003600104000d01c01185080586004198020800780000f0141044110215a01507140c20040c0210030844261501e03820181001c06001040e071041a00074036021b1200441910a0340000300b550 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 737954640 1250 737953390 737953409
    0x1b08040506060405130b160311031311030a0506090a05150c16170d06231f02070e0f040309090204030218070201110708030105130905060123040617010510 68
    0x60742d401c424800a8200106605015003091090000060045126600a4420280c104c48a1000281c0074048030418008411060803e10421500341320786040d49050944c030454201c140060038012900e8a146e460004080b40150401c1011800d400034014000340e0181003226411030a001074045c503048190781902107042c0422826403074589800030000c1b0b441c442e503a0440207181e0350040c810340343c0159001807000d43e150181000440f411303001c1903000b0229854202d03402202e030000205405c01646040540094403540107180310300a01401b07005099885910b035441c6850071000041142c211401c0380440e4440a0209601c01d280c42580d06a9601408035401c001407140031800c60000181107908664880c4203e9030525544c0c000b038080f191241402d107440e0b5040401b00110700c1070340149041d400c0d1814020703074082180001c16904590b01c00d91500c03d51064912650b2560800e80542c507003041c1818000508421225011b80042c00a08000c11442e01c9507064444c0b0b44945208041c1403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 737955890 1250 737954640 737954653
    0xf070f050c0105070302210f03150a0f0506070303050a15080607080a150306020304150c0314091207020d05011407050703020c10021c050c0d09080d0c0f080a211b080405 74
    0x61214090b1f000c8081031066a40c101620700181840e81d51045031017203901c441d094001e0415081001e803003001b4100b4050a1071038541081c1c04115603004286003e07042640b600040740840740c16034028079002c640142034004007910b98120540c0c0e00c2040c1d41b201e0004002d0800120b0b000d150744100a00340c1041611003040c0340c5140c43d6a40030b900b0141003034a40c07403220031480807601030764400d00288005c1a01e003c104444a5000e40d44c107244010074405640c0c200c6903041c02820440001c0300e00a40d41203a80400100b40c0707080480c010300b44800c084c02c01e0141c00341408a516000300103001d20a1003a400c0b40c1610100c8401d1141104d80342d1501d4002d6031111401d003005004910545a40e04482c0c03400300d040c207251659882c6000400701248021a50190052000150501024001c44402c0c02d00c018030b4100c43c1d9130b0b0411002072130401307403100b00b01140421301075100d1092002516043d10901d03849420020b4100c00420400b162104a0404000c500e80418012426030741301d9034018002c2c080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 737957140 1250 737955890 737955913
    0x702190e01061d100807031406030703030c0f050312060a241b150c0e030d0f05370e040b010c1103030910030204051914010309080f070f050c0105070302 67
    0xd82108034521107400b1020002250000d840700c007240c9013000c889503100e040c9810031308000b0f0704136004549048035003401c00c3c0030406a03440008910045903410b140c415004802410308150420401000a055004c00038030102c40c0b80d201da0307805002e513004444005400c0d80d00d944a20702a182200e09180140080c840344c0181402600b11580b2030a005141c05820400c3d41d560000c0321110b00c1100155580c0c0380c80601ea03895000340c0f0030f215514141c00070305225500c00d030042c0c408000780010801b04540080c002070000801c517190112a44580b0441d030307001d0551808800c410000c4654a8001410382014a14030300d0301d40200c4111a40686410b80600219151401d80e100284100c6d50544820040c2e000c6540f11142d80314402c20980da001a140d034240800c11000b0590741f4540301d00e000322804140710f41008201e0602c054042424001410300240c980308000380580094501101c901141007018031020100c0341036824802c0058540c1401c2040054070700340a802006001a44480c00741321 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 737958390 1250 737957140 737957147
    0x124020a03030905280c090c021203041a07020c031203060d140f03071a0c0406050d1a03121806040f06050304080d05070f0f0311160f15020702190e0106 67
    0x3c0650740108140c501c20303880050341081d178820105011400d0009504040b0a0100c10719402e0040c0054010a010244059100a40d40c610b01d40d0b100c030300460000042010000f00e03103000602d9480c3c400f4200154546650041c0d114000e95904c11b0080c000c9038440058680e038101140d11034000207049007650350007078498410b2540b540d00e0500440c816007902e170000001c00c01c043d011561249500c450403034050209400b010304040c10348540c2303c9003480144409034200d426252485052100000c85989101c2c41d203440454a901c181c0c0c0501030740f8643ea00d40b4211000601b4209580c01c1c012450091030341c14014035116a01c980040c81c11001782c2442264850001117400038091055142410181c000440803213a042c0d40318070200700400b44410300305400c10740b04c10b100203260404020300301040701c1d003502c82d118203000d01d4404003401c61558104840c0702d002181c03580d0030a8568032161842c5840034000e40c0848000d074407814039907441025456a0501640031b603604007802034550303480c108054 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 737959640 1250 737958390 737958401
    0xb07110d050f0c0303100f0e13020603070e090906010603060f05130207051e0309010e04051509090307050a05010509250608060a0b0d051f03050c0906120f060124020a0303 75
    0x89004a40c03c00015040100030005580150b4202c01124803007440c0076080c415241803503001c20f0320358603d4403c0105003030101043c03000e8650180c80300c9640745e82d170380811031304540b44038185540701300e0b4a170030300c07004100000e011030588a19880030010a52241311080701200310303201d842da1001816040113000c25403600640b500601c03440c1280d420002d03410141040f20301c00d001c0341440b540040303511b91a540c0d22440d00d1140c588103031420080740c10300d40c0510211000000d1400e000f4100400428482d540c104211403800b038102081e518590007070300c0c0003400f0705029220320500f44190051200521404010824158040d00b04d21140300d16020054808802c0180341340d074032034440740000841c20b0007200203184070081c40360000360030314000c0110401844291042d981c4200098020310005200088003940c0340000c0b00d24007440da9806000441203402418a20301b00d01a241440c924100e001444906850303441030307606000200b00001f4407040c2e000c2c0c0080c07401039020340840e1010900070741c0131 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 737960890 1250 737959640 737959657
    0x1302030c012a0c081009030801060c2a051203040311030d0203120a0609091506141c020415080a11010f080109091b12030905030f06061e0d0c030b07110d05 68
    0x144011181c4e19000642058683d50b68a040369866905090070141d110003030fa405401e032070410b0400d40c03200d40c03101c00402821481911800b45c0d01c4174840550101c0e60714007c0100002420b00b050001d440144c0c5403280c00503c000c039040d126840c4000110b10700400c042c0700a11203a0b00540c105a0b942c69040000362014100240c265a00e45011608440d81c0c0501a41c0c40d005114500a0450128a20040356026444000d0a0800c4100d40f1819500d6081241a200f5a03c0204040403014000100100080503017501041102c03c000200794a0100303040410741e005052242400400000551b00b07507031544120000100303554014454183c51b60f0001e1400c500503507100800d0450041404903107003042d001540d803907146881803c2010707401070080c0040c10041e07014096a4080c084110b60787c00e0050805031107916000040e60001d440c01c4042c0050302e000610710030203018103040081d001c80140c00217503600341660b03000500c0d5a01650102808078000e0000b09007080ca0340314122440d4100085 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 737962140 1250 737960890 737960903
    0xe01021602061b06040311100603021003020a17041a0714040509090c0d0605090709151511030316080a0506010207270e0c03070e0702030307180e1302030c012a 70
    0x458810400003000380d24070a9109459150b484031007c1030041c50400b200c59041006400d2460901c010380380d11400c039205800506001d0786595900c0003d1b00d003801c4207414061000c0b2800c2c1040184100c80d07920481504034112040341c1c50b240c901013100d4010b0180f003224101070003000100400c1c100000c44cd58041c40150684c0d22895a500000e8048008440e040c1c4000c2d03121000d0244c90007003444004010600b210082046410500e048207080e52184200300c0c240b0000d00c0040c513118003488a6904c000302c5501502ea0300d00d0303c1d004443c02c0c0d22074001e1240c0007038088030000d644901580329050007450142c004243d003a14140c1f001c0918080420207483c18509080d211130070310345034020344800601180141030040306c104103152401035503030301014160481030144145a0713008000c50760072044d580b42c641c50104c0c8180130b803510000ea0341d0240709010070003001c224851403140100802d17035200320240c1e103003060071000440720500e0381c6840030721500001c02c11169008990310202780300351041d038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 737963390 1250 737962140 737962177
    0x806240a09050301140402030105070c15050a1112070e06121501050c07090605120102040f140102070510030c110d020d03020c0703020301050115180b0a110a06060b04090e0102160206 80
    0x1000709007501c3c0354050b079603442c95545d01440b045180070b015040e4000810f1070110302c2d000850311614074180e101c20034191801e40e100e000c540307940343c90741013010101c008080403a175940c11181c01c10709109048641c0d0000644c800c200c08058a41a0308507020302030141442901c507280c40505034140780703110f908141400420410405a2441030244400801d148440010400e142a00384004040030403e06403869104000070b00100044450389025603a0181c0040c4c050404a00140e10345502c03500101c0d84071407905a440c1c8419456004040c0740441942e51682480c16070300b8441c1c0c0c9150f80c000101c09608003a1100010600c40d5029000d4006c030901143e034601da480c0c003c60b0841c0c0083e0000201c00c03403104440000390b03412400741650000c2c090440b00c5502d00d04850b0300c4540c00342c6088401004080c1c01ca104600c2000c005203074080e82c10050400851f03694140041c45c40c0e110b03109041e031030340c109000c02054010620030388050342c417032146840c1140d0b5250f003040917a52240314514101e12424 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 737964640 1250 737963390 737963399
    0x7020106050901170c040b1008150a14011d0603150409060e010504140714011b060c050d0e01050411040e030d0c03020a110606030709020d021c0c0806240a09 69
    0x264415008081e4080c0465091030f20800c84ca0400e94065103181c0076a051000c1c6035010b460b03810844650200318a800143e940b90402038105105203443e5455109880400205081e800000202c810440980f030340440d41c032300024001c0d58840b01458084c4d1118050002401d9006003241312040d29000402c00520f122031550f4001c00c0750070312210440d042e9910300c100001c00481004448102030184004c0c8a40382c51320f005c3e01001c1c020702002c581002010000c140540300c0161201403107960003801484140803800c802441c83c0c101c165204669400c19641c14550101880380d903000d160003c40650304044c13950306200103405444000c0c1e0462008019a41c990507252003000140340179541e0141e51041e4822005200241c440d010f000e5079007043e011700210360f41c00034600c01121128140542c4809480174088001d014100622000f0b8152451280095030390b54002c050205243d120099180c0310001800b4203106e42c110b542c0c54040d00040580c0441c800c50000d040401018a8550b0070b840c3c54 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 737965890 1250 737964640 737964649
    0x30509010f0603081905120105040b01030219020610060f090e070504122004060b0d0e190b0a0f020a080411030106050a030605160f1715030313060216060509090702010605 75
    0x71a4030986004c0c00100b00e40020028034103094040103881c0c42c0590500d04818100f00460380184102c07071069641c2d8100e0001640a601070341d0181e850340070a5410039551201c0607495803801c032420480001c2d0b009011641d0345c0140b03101c4100741403503038070b0142e56820000c92161440c1c024020383e00b070100038840003031f4560b03c5004209509200c1e11a06c4403500e1a50030a010261451414601c00d0f414180203120120000e4103840303019441803004640c2c11540d01c40b103401d04003c07010301c0002c48411000e16080c0300410118600541601408000160f45240a007040f8051511800c0015210b0004940800d44030344800301044070040000812070380d14030020300b402c480c40d40102c9586480e0010040e441c2446441c1d43c1e5a04c485080014840484c3c05004240c004041105081c0100c403401060071811880a84885c0340000740469584450351844617592264601c5007000503c5030f001b0b080305c8d42456001140883c1e1407038607002d0411140344200250300800034400003c540d80c0c0e8200081c982d81c1c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 737967140 1250 737965890 737965901
    0x151e0103030906030e0307031b0c030b010902180f030c0909120d1a01020616050d090804060512011e15020f010f0218011b060b13050c030a0c1b03030509010f 69
    0x841d0b1501e242e0603180980c0502035172100c003940301e40c5410901c0102c0119403c0003211450030542c091540ba02030582c03a00043c5070b100e0303810103008000c004001244c9900203900402402d8024205d1a8441c01c001c0200850101515080d540540050307200e4001400c001c0308464004200c030342a9100417022010801d256000641203005070317a114414448501060910001010800e00c040c1c1203a00d17001d00303400e048001d914030000800000003413a80034146660f01c10000c142c0d02c07403c0151342e0760b46c502c0024041d4100326102002a0980000080c41100200300fa125551a0074900e440c19403811100042210b14020400b0940c00f40641d00c02c4ca040007032095840c0094016001a00c80d0302c424840a81d150b120004541404142002d003001520382e14800542c19a204101084040389040841c140e030980d40440c2008034180010b000151100c1009148158070705041084250204403040703480c000078920803010a14020f2690001c244690000e51303002c900c01c0004201c8030400d40145084a0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 737968390 1250 737967140 737967143
    0x220507020604021203031006050307030608010203090307020f031c0c0218040510050c0901020c0d030e0306010603060e240409170a11100b0a0b0a121b080a0509151e0103 74
    0x1c008404000851400901c0040101d03400401541146450b070b00d41a00c684075400b41c0350600a0100000b10351034400e410290143c007501c0000d40d2281045003841765603070072015040713215201e024804801401c000442840600241010314810070050390250351138012030700184c0e00107040303504e201000710442d801e05004074410b83c0141b84003401d10240c1d008a91025000c1d4034403000c200006541c0f0383c0d000540c2100868120f4445840a04a1400351081d1100c92203194141c01800f00001e0b84e950903500c20012540e0584031480150781c0c0d40740380e031a04180000641024001c0c0c030701e84446420240d015403d03852284a0440a40301800075013001c070781101d42000d00144100212340941c0f1828040600850361218051200c401108000341400000e401034246100c0042a0281c0680c841c41c440300042545034000c011101000500000c00588106618086050000803a034851028407415116003118401341c20b035000b6904250100e5400588030b400c058141180e8001d00d5041541c2c0c2a0095 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 737969640 1250 737968390 737968393
    0xf1002030a0e0303131a1e040602100b010504031b0e1807080c0a03030c0302010b040213050f220b011101020f0a0f05030906040308061201140a20040522050702 70
    0x89208000050058041102c124000e40040c48040e40e540401d030380704010384158122924800901e550039440a0084101c00c80000c2d894150710a5100c01150080050b0b5100d64240c880a104500c1c60038195140040b80702d00280d41004100041a001e03041e4505800c146011007010907941c200c000b000b1a070650300c003119498440042c4200035406c02500009102407009000803a0365500090b015954510000d400d114480201001701403007075002d03000403400200119180c1d14110b9104a800707510740585400740d62050782592180c0350401d003400d58aa92002c42030201580b20b18402e01515540c21543d040c1b10805511150214080c00541802452581072607161480fa003001002107034000001c0040c45420001d1003006900440e81603807181c2c1504094549845501c00708641030190103550a20b540b03805204841801c81803145801500d28281c10702c650359416504a03c000c40b1840a0407082c401004100071a00300412072400000c1343c40080c08441c55408180003e82e0740031184080107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 737970890 1250 737969640 737969647
    0x906160c0f0204060b220b071b1203020607201b120a08030a0c080115051e03040308010f0f3014010501090f0203070f03050c19080a05011e03110f100203 67
    0x22013451a03080b030130794038445c6d00c08a007840c605103040e441d42c42019405040d01940c0008074504407150001d200060039180d243c884401c526040094072604141e9110b00000c48240e40b07942200100400c003201d2400c0840501107220800a40404a8070103108007900701721080a11139a103181440140c1d5181d00403410284c0c2d914002a119040300d00004c8040188031440e40180424494484640c002e10b03500d040007a51002d69941107000c044056440382640d040c00801c01042540c8a1020b034101c4851a20000429881d560300b9841606a8007607008022282c0f40303682680312528000060028080c2100501400180c903803a50002c5440494121a9103500041008200c148a80090700e0310103601142503052684005001310b203000c04820030180c5030b002040816070100b048130b8200920a050a2501441540203800c00d0001c5034000151441c0500018444520840204610300141180c902c0c890460303580001404907901c1e0300c0d8100607007020345d0025131512050b03801d0000098000399107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 737972140 1250 737970890 737970907
    0x1081f081015151b060902040903020d030c030e210d02070321020a08060907110f0115080303090d140c1009060b040e031611060712080906160c0f0204060b 68
    0x103482c0322607800084021289098030140300d074015000028890030032490841c0b05014200000501640d140c080d600030f207000c0100e8100368000511100392142c030b032000c1c0613004181038203504650301e038405402503402052891100744403540841041c10100c0704101e007071488600c3c50508980014100b00c01140c1100810318586503004541c940340d640083c0c00350301c1c0080c501c000410074400602114000c0701d2500c04604524002c000341142040700100311012040c910380164007a04001e0342d00c1032800207a2101180b00b075408070449110380f103044001e0114a5000d103048880c1418580f02c42c010307410601608040c0f04081c400f40607020b0703410001251903c0b0030304003002103590381c5498034819443e14040d0011070501205445c2801d214603920004181c4130308107103a120305400c6459601c190000341e01d00801c0741110000380c0c003900a650f140015070320344410542d6428141c8240061346070040c2046c0b031a0703100d18164040380d03218802d280514441680400c041d64070b1500060702c81c00000c00e5150 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 737973390 1250 737972140 737972171
    0x120901020f0f03070609050a05060a021b010603020f010c021c030206010e01060318110402040b0d0504030f0c08041a09060c0c0405061005030a02031f030501140c03040201081f0810 79
    0x1001e060514000d0201d42c01442080d0380d880c8a48200249080d48421110f41808070511032a1182c1e0340000070303100c1518091f09640c00a60110003c0340140d41040c510f200c110505219203400d582c0d0207000030f2410b541c40070040d81d2a021080d0301703e03808000e030440003142404040c001c3e2625803003a001840c1c0d0354106003031007a03407440580001081603c3d00c414482c0030900c5000a0101e030b90412616039107000140c01043c0070744142d821110101100007544000152180c0c802d501ca64000d95842c80c41048a001c211005001a08003410900081c40144056401d0030032403941a14280011442c200000000c10400d03004900109180d800c583c040021508003802090350141e82207030300d00a8014080406003c6000180c00c010300f43d9808400a03a035200c42520300ca103420f150384070310034109a5170318149021b40341d580409100c0210b0000800c12851443c2c081c0c80c0140e42c141c5070f0f000a0707541d4001107001a8400c48103918114084a07000552440501030800010012000820020042040039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 737974640 1250 737973390 737973403
    0x110a020c041d06160e0d0312050106091a0a0509120109020a061b0b0a060b070803040302010c03090f24022113050606060a02160906060e10080c09011112090102 70
    0x501d880c1c00c0a1410b42d030310301c0700400c010b030340011940d070680c00705042400b0455481d49000c2180785c211011946050a05402142039400d1482d200b00910850381c0310f18003120b000a0620441c852036503007080c903480d02c45042d405060a455645015400c00503260b00141c0401c41911b50042c0ca6503444005801b5414803a490b10090015810200c0b00014100c59804644240d040064480c45101e004611440240e401034002807035910039080d1201003c0c101200c0b00d5006450840141d0302c1e000030403c055000780070310341e459a0080d5030a00440e509465240c4030341004021040030402030000e01c16402d2141c4041c0a246140030001c0f10001491724102d0303a07151001c0c00c20345038a00700e07900f0000094000650313164011000d44000742c40d0100d0f0b000070707881d0495080c05a183d0306840400480c06503441e0740080101c4440d55075108110001c1002d114070080c402003074400040c40d160004201c014035000900c5114030600d08105402c1c2d00710380c82d6092904050503804400700c0040d04040755030707040060 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 737975890 1250 737974640 737974661
    0xe03060a0603031d030a050703031713170a180b180102030909132f09012106110d05040c09151202010e0409080c0a050706030b01170604110a020c04 65
    0xc2088074115200a0903a0b10880b014548061890000786040d0701c05020300508258001f040381d042c07603124900030745024052190300005003030120004642103011381d40c00135115000801c4c010802034003001d40100b607010300c3c0d2500078040714103680f14040b036a490040b0010304403450304a0b211160f074005180c20355510300c8181e04542c42071060400e0b50f55a45030703a5801091049070755000310f40e245800440004128582502850303050115440014110682544001f0450f011112a80c8035058079900391a213000c0106850b8a0440c040c00007806a807105050754101006a42042104a85101503540440f030807144689070000c1003100381c00f240103001c403a56132420410242402d04218500048442c031020f410004014401d52089d225580201c50103500103002950303400904817421360b00c04401100319942d02c42d680e0000f4015200c4e02c2682901c4005039682e9800b0103441d8a204140381e00170f00400d62041e0f982c02c20f144104541001400703220056005000c0307180e0300004200840b05140c80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 737977140 1250 737975890 737975911
    0xb06040204050a1205120708040608070c0503030f06010e0a170d0503091f18120e010201020c0304060305061903030f090e13020405070c1209180c050f0705010e0d0e0306 74
    0x512940d941c03a190318003510020484c490342c030101e604020b4540703542c940001d8481c800009500d01403108a90050040c0e892545580c0019103d0b074004442c411400034000d09681c2040c000714204a6070508001d030802014905a401011a80001003059005520418003080310b844a8200f0300d009120245015103d0b040c0a030a40c9040640d540d21058071480c2c801e4200003c08000c030f5146401d80c03010840340802c0c09102d00c600410714040c80c0601c00300d141c24011400122a8245541c81402181c1c890608000a942021320701082500645409885030354070000031080803d044c00d054124000550190b07841c10040d101700f940142c0b49049a810030b0303000c0d00c1c01004100c003550030821045840d941c15100001c080da1981c00441c0e0f152a50040104000c488a101d41c4607154084848019220b1410302640541030f070310b10072000c9440c406100d0000c40c0c01402030070242098940601509170240002041c0b00444c102c0450a00710001108030101e150540001e016007410406154009034214 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 737978390 1250 737977140 737977147
    0x60b0a0903021c0609060b01022e1802190f0f0f060f1106010e16030e0604020906030304080330070c0b090f0a080703020118120804030509030313030b060402 69
    0x80040c610403180c04080d004840c0b103c4011400c0c00700780c83c840343c00794200e103041002880516000015205240039207005210716400301c510f0b00c85d8a03001d030409045240c1d0744996250003000030320140904078105020303400080c0b050030140e280c0700ea50b10142c0103000ca4110740e0600303100c001d40003034071140c01c4191a624019000e04c0350b0703034460034040280c426034202000d076100c2d008400c4405403a40429040305006440000400790402488240a40c10481c1151400203038444218212480d0342c0c20b40c06564405000725000d4149517039034a41298003e010303a4603040c0c64542092641c1c1c466410000d03420640100ca0184090728003900f8200c01c0000700708405820001d02c001c5c092050124013400c50040c0502003446100100103a129142c0d00500b41c45d00c4280c1800c0500598200f1038099001d54200f0308000030250804410b101c1d4964014000300c908001c8507402c5810100041003202440010480012299000c2015100b0302c070f840701c062848079041d403904c0c0d074264001815280c0181d0051 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 737979640 1250 737978390 737978407
    0x90705030c2a030c06060a0b0c0a15090506070206090606040e100b01200a0227010b0c012003061311070809030c060313060b090708060409060e030409090303060b 71
    0x8022a5610080042e1545000d8001d40c5a0380240403581151141848000b41d000c0c40c543d004a4400d118030350407208122440d40d243c05d44034880c800c4000c20b8807140c114801d0100051740c80e0b0030385021070440b404006200140e0b03130b9615140003030681c0e041c0090b900c401c04100c0c1c2018100803142c0c2c04102510148030815402940540c1e44d007111800190041d10341c002141039034480c0b034441c0b121540c1c101c0031100401c1c8000b482e54558442c4802640a1800140e6140454054001c01ca099600303942c40c2c0361040e80b81c0b02c07100103640c011030740018683d521549210f2040d103c080306002404c003208915940d07400c00108103c60810003018040000f41003824001c0707000c404000781d48940307030802d000564403816080007130700b0100b100c1c42103030b486140441413144c10100441402049881000b040001503c00c030104040714500325410f00000f442400040d0342810141c0100500c3ca200b01c10200b200d11061040c41d05582107034200a601070b070b40e01c84000c03d0641c14021000105104010703d450036030756 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 737980890 1250 737979640 737979661
    0xd0b061602010819151a070b06060d0b06040b03070216080d050c0703170304051005040f060902030138010c050a03050f040807030501020a0f08071e02120d090209070503 74
    0x11050280c180b010050004103400c0441201c3e0134102c003403210030803003525501d0300342842803042e00032440600300300c0c6c024146030481364003110005504155918402c2d522401044041e621074440c0c207006540f904c1340c06013541c56400142000d400e91110041d1a4a021031009181541c18012a01c0f80c0c1580e00003007111501c04600400480083d00e00315a072545001c3c1c0d5076141c00301c41d500003070115081492034004125100080c500880c03184040da00a004d014805034146c031000e6070068105448180c075080001c0e00395002d40107640c4042d0020601c030546500d403028a49003128254401c1c8841044244042c09589071a00f403511309003400940c480064803210790350141c800009040c420b0004850b4000c1c0d11041c00e8900910b000c03021926944d072607186c4240030790450b100c031402156600d8074400381640035a826070f20a0485641c0c10444002c60503144080b842414080402c0d402045034510580386100000e1210000440c0003040c3c1f240e85105001030900010080340800506105002003c50b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 737982140 1250 737980890 737980927
    0x608060114240d141014011403361509070e150d02121f060608041104150e0405071202150703090b0403060c020601050a050f011103041a0d0b06 63
    0x108542126110140640010020308011952a6500d01300d8410404c240c1c000c64050010384032104201c4007010701320310042d203002e145030061840480e000d000003034458980c640f038640003401c08078412051504092095400501c1d81e20b88035126040031110000302041c82c0703103254001603e07000500c81c0901e0b10f01c039114513a4019020750142a89112400e0441c1d49150041104540003020080703100e20001049645580c0c1c4c0300c407400002540c0c1d44a091200081c4205012903206403a503851996a0760307944e1804120200b83c1e02e901c50303901c1c482401034007540b107840009482400c070040c00a00707041c20003030b203004041e51000400900c0701c20f2090050f16540b024052001c50304403a1a02c0c0c0c4c102d0314046d14045503607008580500c0f0041000018021103401c6001c5901c640d4007664501d0342c0b81d40a000407403602d4099641c10212041c18118a0752140c0203802c041c5d2022000d92342031075103511711031b8001120381040c2001004041101501c002c00c40c46003601140301210303018604030666050601d0b011 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 737983390 1250 737982140 737982199
    0x1e010b0a0e1f180302210c010e0d02060c070306111c0203070c0206031008060c0706051003082b1d0f01020301061b1509031e17180f010608060114 64
    0x51443e8445865020000c00019650042c1051410517070b2551703d6522440815046855201d00c1c0740104103035005c0c006101003a01d001d021018031080c0b035020300c07140e5407040d030751500c5a102d0440000f000c03030010321900c1204040c1c0765200f40c0c0e41c0c410740703100420031f07000342c0342d4140307592041092240090b004002e40300c02ea98142d070313155180c2d980c000e25103e03484c2060b440050316000d1f407000c0100381c0948600400e01c580c0300300c4041115481d1001500410303442030200034070300c074010400c508401000c80781a45902840b805001d6070000e0040c01300d400d5840c490620100a038080d850100b4501007480400c09400482c0d00860541d071401070010400d60b4000380c10320506400400c02424005141540d00d40801440c10030711084019190042c0760044081c0c0a4511580c0398000310400d510a40b40d807810003242150084168a40c241e50b036188841101c051143c511509502e054509828040c3c10020264800500711a6143c510748081c8041e028035076078442e003515a1030749290401085400c0055 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 737984640 1250 737983390 737983397
    0xf021c0c0602100e0705090c0c0f0601050120100e0a0c03050d02011112060618060a110607090602060a1805070b12070e01021e030f0f030a061205060f1e010b0a0e1f 72
    0x29115079440e0a950700c50b08403551702e036004848072b00c00610b50000d2194102c903400e0b41c40c90000304a100c00b403d84140310920443c1c0941011041040d41c03600741c1c025080a20b00701d030682d0b28080d2541d940216562569000307c5668010801c00c806554080c0704011405901c1141b1514205145d035642d0100500244400d01c106008101ca4404c007600207411502000050041c664403000303200043e2a1084c19842200d09102e4500003c4640e44110844412a11140c00404198490540c500d02800e944451300c44400c1400381000041602080494010300d40380042c2580c400f41c0c1c81c0d98186040e4000d011006002000304410010790340024191400901d4a480b0094500001c6100e400e52054041c50b800140001c10400b506486000080d8001e2500381002c0200a42d03400050544000c072905c09441c5411420014021031000210594840b4980c0c0c0d001a413a0192003141003010002e070486007003044c01050500d442500580e20341510703402141e090000e4803d01d489040c544c1c0500d56039a042 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 737985890 1250 737984640 737984659
    0xa0b0301141e01081e0a0b0f06040b010e030a061d010c0503091006050a05040e0f03180108090c0a0308160807080a1d060d020d0b03030403030201140708130f021c0c0602100e0705 78
    0x44803006d0249680542d032180001415062440000942220a03501580f0551400004030030540c0210f0081c00b0380003010f8044c0c04a52207603100c100080c6440403500716910805000c0c8001c0704020f20904002d0300154403603075241c1c281440a246007942c0085020741d40d07842d050341481540da40c482c1c1481102e1303013190041510608507080340d04140c900c00c2c1030210740c84080349140440c041d0f138910451130503081e13840451590382c0402c01079562090b82c10741c035008107240c00103001041c04000107040741e8180c0c0b400c404820403075a56503011030341701d41c0c82640c165101095044445a0040400100c030700c0c0c0c0a079607941c84004100180e41849040000c80c045540010750a060000c0361b0840340e00d03240000c040c0c3e9103071a80d078100a40a0840700800321646180b900c009003425000d0002c8900901c00030a045c480000c141d80c901440841110083c2c2e0300110f07140d03020f5109a003d09808050920581d0225009481c005020f403030640b44189084105043c0201d003c2c400c2c4c0c00044040c00c480741200c4400d203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 737987140 1250 737985890 737985943
    0x10606050d05130b0403270b090d020a0b0304060603020f09091b0d0f0507090e06040c03030507110904051507020c0d0f080417030c0c01051c050a0b0301141e0108 71
    0x20000c0d4a40c00185241300020401c404d00d5007146c0c03040850050080b092240794164108030b0407185150040d640034150911001b15103040c0700707500b5501c180c8040d00304040c0903140c814019a50704221b404594003915102d09004601b4810b407400b0b2440d4090311280c0c802d09147c058140c5410482d006c0c2e807a980021040c18500e5590f25184019254201d9644000c0c00114200940c98000e41d01800407841c0c14002c0c0f110380320f000014007511880c0c0111312500605d096681c1154903600c40c10055036440d107555010304442c1d8900e1403150189215400905255460501035030345410028264020740d0404140329034903455903500c200c441913021111400120341840d240000307028a81228400314000da10011901000000800714207002108036000d0b03000d0344c2d00454540c400d411281e504150040030640c90b0107019001913400c160f40c00004204280c2c000080707030840d07a000002c040c0d800340c12010f02c00059400802001e54202c41d020b20150b0350b041550031a41c4c0c0c01800004120f01d81043c00008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 737988390 1250 737987140 737987161
    0x50901050a1809060902030a050106091d04060b060d0221070912060f020a0203042405040e061f050702090f010f03020d1109100302010224070c0204021c021209010606050d05 76
    0x30043c08400da01000351648440001c0000e400c2210110030b11450240045856405200301100302c41000880c03101d0450349200091002c100600111911911031210207059556030002c0c2c082d080340d5540058503180d44409515004008103032080d580109502805445540081c40105450780e290800c0110030b040e26200004003c007081c512400707840400d805990b517502000401c211500494000d00030348048944800c4c0c814042c080d030703011a000700000c11281d0714000501d03a1048000300510b42100030503080351601000c07818124000b40000032024110324011802e69007000307000342075540d50341c180311030080048209e000c081d2240300071005c20702c10820300100ccd40355034040103020040a03003407401540800d007816001c22401b5004404084001d1500c0480c490b480e5214900e00c00e405841d01a0265086611420103980081e020020807903003440c400820010401450401a92810402e404821240c000b801c0900640d040c00d00c10041264040d05a030307040045201c1c00940c81e03c410000c0c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 737989640 1250 737988390 737988437
    0x6010311030d08222a0e070f0c0308090f06010902210c0a0e0303040b0d050a05011d07030c02100504080405040501061809020f0403021c0203010509010b0102070b0901171f06050901050a 81
    0x460801101e98040004845e0502d582c170807524074086011a507107580c00140ca0144401080c20b00040302000d514011134440c025450300000e199080c3e42200540000c1d02d81450400d8000028154000640389548020310221607900c11070315603801414184140e21001510176130340d4800410618640c03c481030380d01441101c0003001844000c5503103228403100403000e800c040340d103000e0f924900f400000d80c610b1f00550054190308030200074241c035500c0d034000350300070401440d0102c00c610810798400d010028521503039010b18002d010381c1e52038501d04000c000c1030ba18140c020f0f40410000700248100300440b00a468180c408418000d42c480460045d80a00ea004079400613500118400d0071401d04400c21a030808480d000790000d02c00d03996011209400d0392203001d0309070f0042c0c2c81003c0c20001c841a21001e000640c0051420750903401550145c0d0040c0300c41034a0002081c8032240c418100e0b00140d12291000302260b0078454241aa0b81c00060120302032543c0100a0014101070694010240001d5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 737990890 1250 737989640 737989673
    0x904020f1603021b0102070605030433060812071a07030204150c0203190c140d020a0b0706060605040503070b0306040e060403020d0f1719090b070c0c05060708220806010311030d0822 80
    0x184c44050f00c80c41c54410240c040d900c01c02840f40140342010fd007000e103800031650000d41088a0a0347d58040c81052002840010b04003000c0641c01d00001c5400715107010410701c4580c043d0350341e2130804450b00416040a501100f501105034400601301e0024084241e4201181e040c48a000c00c034505020119480544144000350b109042c0740c0089040350b18500a0071105024030f404011041e203405080d181071056000306c40d4544d0001d402006480c180400030340d40820041c0c404200717100d09114803407030b007041687e08501503005400340409940d8001505030100728280b401c0709114425001c01c0040841c06010702610000550740665217010b00e03001001031541c44800c198040c03414003401070442e51100c00c01c80f0310740048840061149001c000ba1050385410840c11880d10440c1d155924819184000c2c810304452048000211200d042c415a8004c1d4021704a10228400190816040c009202508014021b20b4420f05c8030403e00e001000e1500800c001d00400700c441c0720300b440346614196420 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 737992140 1250 737990890 737990963
    0x1f051e070308160809071e0504020d02191404050907021c271a0304140a060902041118120313080c0111060702030904020f1603021b01020706050304 65
    0xd0120400d6484030145101c0c028449143c101c281d1218030864506005076100c11456000c2281444840b1814070483c0820030a20b00d01407140780d40300085016600b10207810b16070180c0c0172844802c1c07009814901e1001c1641450076019400142c4e01c041424000c5005140c0510400c100048032180200036007841d040381100c11081214056400810241c81c2d51645003900c200041026114640c003030341013083e200c05400040e80e0700c00a481d10103081d00002c1054541581001d1805900c000911010080d14021200842c9150407401480b0a90f04482045106810200700b01d05504c08000c5c1d100b0030629040319100c5200110b9070040c1d18500483c0300440c0c8001e10804006140c403000904408a10340a032201303101009041005038480500b1510600542c1081003088070301e2034a5401002800c0415013018103100000c9081080200221011000b5a0005090700684940441c0001e00d105091000344002e41c10050010300500018000601c0f50001007100e07000740b0b018603c039400c0c0554050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 737993390 1250 737992140 737992147
    0x303090b0a0e0402070c08011d03041514070539040b030f03040e060f061315050708030a0203040b0a052a070501150e010f0b0a0c0311100209030601051f051e 69
    0x101107400306e0891080384210b61a00740746002c0c0c82c0074540940700901d960005142814a000c1c4a045001c026085010812840c1c03000c0c26003420f0000060100c0d41d0065006240c01704080c184800740300020b4441d00c40342c40004a201455001c407004040c1000802d036400700300e50301c01d01d004c2490191140700030320f1a8007001c2400b140c54408000560f1042e203048401c1d0808400321010300403a0b1044103041c1c10f90326581d480501c070100321265481a00c0e8800c1c600f40e0701d4104140c513000d40720f030015035070b0f02e0701180c0010600040c09205032840b9000656040c0030845800d111942141c02c0c00380c41100c0307200300304601c40460042511400d0f82d6030307503800100030b0040d6050415103183e80c00e4140590301c000010f410001c0b402c06100d110100a947c81013402502d40340d010b007402d940d400701e00c0340100c3c100402110781107000d40c014810003c039460100005a11610000c1c00c00d030070301c0016004180184042800f143c1140118a85a1211b21090a1499a40078044802d000c1c00703c40c14411011140d001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 737994640 1250 737993390 737993393
    0x80408060705480c01020c09070801050d0503070821090708060a0f060b03010e06100206010e06010516120e1507080708030606040801060303050901120e0a150e0a150b0a0303090b0a0e040207 83
    0xc2011400130038240e00340d0321141c10701010060240000d4502d6800107450200510141c1000709000305030740c0c000e01c12a03050890564070710900390300402c018800000c12100242a1428200d04250803400c40303009403d0300ca05100206541d0b9200030300c501d40f15900c8081782c83c140031003a8069030180044054442c1c0d00c0da12041030301a00f2400303642c034601498141c42c4001d0114070205000741a80c2440d100d200b215140c0704011101c540041d500801d141c00084003200001d000b2064468805030140c55089045aa5408100e08440c0740d034210700a2000420648001590000464526561140c85140c590310b803000400c0c50703800b803608210055860080301100740741c0c0020282c03020b100241d0b01d0340c02d826600c003070000c00e40d154001402102d0340180c0704000099210540070484240c07420000403801e45000050b4a048010704040d907640a044010512501c56030149110704070040d00d01c03082c02491554014032441661045400401005c540f21000512822026441d540c4c020015922501103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 737995890 1250 737994640 737994643
    0x30a0b0403050d0e010912080f160e12060f18011401090507020c10050909010f21021315031202062401020c0406261c0c0501150308040806070548 64
    0x21300c687c1001301d590080060305016a111216114101c25070004160a4800200355403040700c51442e43e5028440010502c142c0ca401c01040e4800c3c1b510085403030003820b10072b41c21200c0c0002c440c42d050140c3d041400500054003105402c038112003c184000403940d0398030304100d040107400c81c032090b8449a2040c3e50060240d20001800c001c40049910304483d0f60f90f0148030800e0138032803142440340d180451301c012255142ca0b40e244d08440c00074000900e840110410142140e0503c0404490f13030048410510500c5140c982d00c1003480b003540018801420004031803c0308078181400030012100300c03074100c98503901c02d1051044540c4050300501a080e1039841599202180007203820900b49481110309903040005840003030080c0401c01000d9034881e03001c0840d4110f10010703064410359282c005200108a0822410000714003802806450fa4180342c07515080c004003030702000c02c2101c10301c10981c1c0c1400d1040b049580b8043e000c0129a21000303081648100845190054201e059141494140c02350 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 737997140 1250 737995890 737995913
    0x2180c03150402120a0209130608010e0c061e03070909020a0e0102010e0a03081f05030a05030310080705030d030911030616020106060824062503080105030a0b0403050d0e0109 77
    0x841d45001d440449034002030000324040e14507041e010994840100c1e80d49501503004090a101c080c00c0c01d41110481c21400080c0c80980c0c0c401f0000d6907403400d075060480c2c828440038402c0841120f4103880c02051143d848000700d80301d821031b508904000301140006000e50036803001408540c00c103548030311210700081c0c5207030000d4501034055400c200381c03007461030b10200307103a08440d0341502e0b10f00d01c5480340c600380c10003240c00045803c1810f2002001250a640811481001d00e104900542e607906c1e2504d0b00d1280350300c43c2d6000340700f950f220760424402950041102c1e219080c052030009440c030030b035041100681040501c81b13501402480c041c400030148500b0311544281440e0000c0c0500c943c2e030803040300c031800101e03840040c0c40c1000c0c1c80402d10f05010245207803c2d180003824281401c80300424126808a008a805101400505031408058220740d5844c010081240580a524060749500b05407440c010001020031100261090803040720b9845240001c0e80d41000b0440e211251820302c2c0740c501c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 737998390 1250 737997140 737997151
    0x3111603020a0b09030c060f0903070203010501030b0703110406020a1b0e070c0201090f0f09020a27140f0f0d061d0f060604061a0f090d0b24030d080402180c03 70
    0x1803103c4000380400400204aa180c501a10020a800e60300e006841c45000805408092a07010420001d80540e509002e25400317180144050501800d000d603019007111041180100c03080d00a1000300041500410001d050307030b4200014044220601c0442d01940840b504000311104400050210195001400d115214801e032a00c4108a48036010072461070018403c0c40044e0510030824020000e0b15000f500f00c4134040d09041c1d0941400c00a0000380440f840541c001e0b0b152824010000341c0b40d1045481c3c00d80e0300a4501c480b8100b0100c010038528021190317290b005103015144002040074a44c04040b0a281055080c4500f102c40d1408644428801d00d00c00360328030446020640a1074203114000481e05c8a0300d41c0c200c40c86141c1404409500001d0007400001410704c420f139000e03201d9001c400d200c284110b108046d24540b440c1c013542041001802c280e1541110190402e0780d03140001c601d2481121820060b00507030700e9100080071030f018010250440f110726001d2140f0405081c0283d4000e8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 737999640 1250 737998390 737998403
    0xd0f0f050a02070308063307050607120b010504050a090b03070b03091b03010c020606091f0f170d0e0d020402040518041e1a0702030706060e01081014060103111603020a 74
    0x988841b030030484141c1e03d4040e40d042c88034001c02a00c0015103c1c001c40c114001200305c83e00c0c10221140c40d03480c1040c10440d006800300d0b5610092203051842846044020703842400c005080a0810001c18091240ea004000c0301e07507035442034080f540c2d0b81005150018a5080d440c180d03289091f40c20b0301d4031040600301111702c191010f1042c090500d010300542251800ea07034000c00183e559003041240800c0050301c0c60b11201e0f07800820300361001e408151940600001c0481106c85031410f228900c6441c90310746150b1503070700038080d010100380e0300c003107280341c115000c480103850480c2c580001402131146a0100d94401d41d03c01036404022081c20301c85203d64050a21107030301c0700c140764040607814542076000701345040c480d190340c10389280e00d144503800c070b14507204680c10000a90343c1c81d0205c9a0715003009100b05441c07001000810f00400016035400302402082c003416003442e20080001e50b01514840c1450348403a41807115031580010ba9208801000143c10400294100070b9101e0070205c4064a09 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 738000890 1250 737999640 737999657
    0x3020c0103020a1e181202060f030402010c0b040f030915020705040b01050c03180f0307080d0818060f090c012109061103010b07030e0d0308070c050705030f0f0705150d0f0f050a020703 81
    0x81b0b90441802002d6640103041180340000074503401b40150b20080040341807210300c590000c0861045050701d8030813441201c0148075404075090103406841c0541c020308050700d461004800e116404180720080720b2003910302003041c10b810b00040c0d5590040240b03250305071001107145941c0603180c107504544041c00b903070000d006481c01418035403500700078056900d10f54841c400f03000c1d41a01c03a1a1590303200e804603000a541100f030040450a000f000e440170410001c650701803004c074903805d10001140c44402d00344080c03c00d190640169144030812000e4010a60790050602440800d410100c6d041000c880d6a590325038590342152034503000001c05400107040040000c98a00b0006a10810307136030540c688020b29603e440e0700f250340d007410107012299801442d00004080d2420130840c3c600741440406400e1050000c204a46030040503440103224443c00080b100b101085e2804031808240b40d642d0104a21088400810150062900c004150380c549010490718403407650140c0381e80c500c240d96a41c803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 738002140 1250 738000890 738000899
    0xb1e0f120f0601030c1d011e03081c0b010306060f03020c0312010602101b0e131d0c011103070f1704080a0c03020112110a050c0f0a050718050403020c0103020a1e18 72
    0x1007199260f802120203540344001408002e0006581d11064200c1348c07002e8080039180d43c2d81c404250492000303030740c0405142043c8c0031091007034000c1000005080c07030304100d090306e00400280030651030071259050560020720950098010303c04c0310400100281d1000455075605002517881d2803d07800085214980341d20f000c00c12802c1d4150503c0b070150b541d40c807200740041d0b00800010100103040c0c090300590710700d84240081a0b01999000f00003007440601881c0307d0510014143c0d03d003045000144d078004001c41c0000a60416040c4a0503410100780181c3c2410900ea05000b485290040309040c0315105001040000400c44182075034401e0b43c40310100894120b0200036503462120341c0d03110304030a0010400c1c1c80e200d5005040301c0b40c2284112061070030340b01450303400c03e80c24840955142e004602c045c00301307110b070301414074101c0c020f80b504005a1400b038400030f440e0403a00c1911410103400250b4040810320840400c070302045860701035020503001c20b40250451808441c5c0300d0074041e40c8800000d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 738003390 1250 738002140 738002159
    0x50408061e060f060705060c18010e03120c16030818031621150506040e12091905030615100509030c06070305130e04060b1e0f120f0601030c 62
    0x1020200c4404920a640b40d95080192500c1d05010058011000b84138110100d44200710684c0610f0002424a58aa0340b4070000c5d10b44080550407641409007010003c030542e100020003082c03030303110403181030b0710f5007010400c0e241441880b403800c460240c6442404818400e441004110116004c1700880581d22040d050544440306d034040a0610042038108010001e41e2251640384010300c040c228a0030f0106e6500e0360700c1c1d02c800c00c1400d6001c1da5520108100d03810039118944d56050202c0050140e0200121600c1c01c0d880388181c1e440c0a04400224411660b035030404003405043c00800342d40e034a1030290301d0441c5601003070000d43c1c41620440030180d945400780d0200d8807404030241c0603018007800c0380140300300361744440011400c002c4108803c241500c02d980b0990058680950310a00303d0416040c80c2c0292040300003102d10814030306d81c20411820000b95804400c000680300342c40030710000b00004042c06d040310100142c03401002e2803004038a501060b103506a82c85452500c6469848442c0c50 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 738004640 1250 738003390 738003421
    0x20102031603052203090506041d15060301330e090601140d020f0403051203191103060d0f05010615081b0306010815030709050f0906060102070611070509010605040806 74
    0x51003400a0000c0703204403004013065445402424008071903983e6a0104002c0d03406a0f11041c2c130303003c041e00e0210703c2c0b09070b03150900d030483e01c030006130840950074400243c0c50f848184034034044998079041400d0303100303054988884010707904201c2c040c507550541d00c05801d2640e4480264400c110050000d4020b40c000c00c0c541d1200e0700680c0443c0c0c20484485503500095000303080003d502d00c02408000001035041290070042421110000e03224141807100d0506080010300100c002ca0601d040b100a072a17405054036444481100e2041207000c0701d0401004076002c0c00e00141455091000104039880501360700101c03411b455a0365005036445051030010860441c04000c0d1386102080811065171080542035002040c00c08a20030981004000030300d0120a80d012640c03c0d03803200108088814103c90781640044680d010f0501490003e00003515150b660003004140306080c810740c50109002c000e01d2000e450098021440c80d6101c2c200a009034105115400c3c075841810002400001e07600c460 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 738005890 1250 738004640 738004651
    0x50708090610030506270d0203040e0108060c0d0527030310091401051005160b01090b010309020d081c0501030b010911040303020c0628110d021b090a06080601030302010203160305 79
    0x18103107989886155074500d241c0c501300b100034002407030307401200c3c586c0c1030140308608900d0350015030752546040d0800203051016805141e003034100d0307420070200300c604030122a43c05201d0440025140c3d1060445d0752110f403158403051100c040103e040d0b50040c4008000d60040440f0b800d6508410794540501e426921060347d80c81d42c10000c640104030074144051009156551800c1941c1841d50310100751520385e12481c0180d42c0245110010000203a103442a01c00c000da0031301e806d01c190a40d940200303885030b50782d540027015010700085900c44040390b0509602d040003000d0080c407495941c1d044c000c044003000e001da514443d1a00600340f519102480031581140d44c907030003910804041074100103090f041425051802d8030503448812090f0700c190700f03c1c10707019001d031038100381803411040b000c0c1340c1441603a030351040d90f1049d00c1e4158901c4200d426140c9580301101e0382e1805644114560024240541c014a00340c424640040304054040d0050b62068486c0380000d00386200390340007282031310410b0340e4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 738007140 1250 738005890 738005893
    0x9070302130f020f0a080403080c0703050304380402030105070507050d08060409060204030f0521040e060604030c180e1612030201140c04262505040507080906100305 73
    0x107072880942180e400003008403954080050401505100d418000c0e4805454000080e071144104010150410034140d00810a01d0070a07042002c1941d0151a6220140028200701c504107210100f03035507071468900c6501170310404030040454002070b07003c9030402990200d11079400c02d000592500d12a8041d03074005604030006040c00158500c0c00c0e150f1000203400d5580154032070f1003520210305140003e00003980b2a81d2005085019030414504003000c921101d5044040c2502411404115509607400e03140034100c481c6580c0c9441d40000c01520a50f8402030901e4140c000004201032a00c4c0c4030300141003503080c140a2000206081a120000c0d400024401210302c0030501072003e00c1d186140c81c95102c0e0000240c40511801c1c0d05c0d40002080344c400503c4440000c0c207200010509404844910106204030183d050f00c400d10340d110b107459a502d9080181e40c0c035644942504502c070700d0005060140c0104120b0800f164000c20403102269100346502c580e0003c103845047c03844d0b0b2034044942050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 738008390 1250 738007140 738007159
    0x70803180f0f010f0c23060f07050d0e0f0607020606120c030a112d10081302101205090703020f030303160521010815091c080709090509011409070302 66
    0x1030041d1a4034148403004000c120f522440c0c03000044030017030701c6400c0c0c0c0c0003100003035100041b1204e82842e12200070500c03540724900006101d0100d4102080c4d07034407240d034038001151243e5585209890000d00c258440000d100c1c410501c881d480e000304400d0300400003540c840e03469540240840d07644503030407101150181d21001940740400c0012100c60220600101113050f42c20348510060312802d240b46012058520502c42d2000d2490005012102c2d20424101048146441c00d100000481c403150068040c0c940c1000070075105114030307102c1004064000081285040a0010968560072400124000d07075507000600c103589400002d480c42004000c0e88000350f0207101c0002c980c2030f08581540d5001c00786c0382030f820b075030a803010035401c0c0030700305100c002c0c650f1150013414592603003c00f40800d00d064218010b125518490614012000310150600300301d26200c108084486040a9000404803440c10040c80305211041d005112940949114101e40380c07203200701546c076001c0c03500c0025803085008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 738009640 1250 738008390 738008419
    0x100503091b010504050d060501150e09060409020102010b030631120c110a0602010f06050a0e070f05090a0305030c0105090606030c0d08041d0a05070e0d0320070803180f 74
    0x126001e078034012041c5445400d15a990b00070400d1100c1c8107504882c02070310741005000d00550f031306c0d5414102d8000d191004001c41c1d00710200e131010300003800b05401241c651360f080081d64004d4001c42c0300100090111142c0b40341004034070b50842c202680b8240b01e900401c880d00d20b00d040500604038070540001e0951214445030708195008282054101c3e89035400d0610540186d48100e56103006001e90380010508040c40011203088440c2c1d80c11071480b604c07481d00300307001d000003001000f944601c260500040103c6c4a0000744d070741c0d0140201080c1d0048043c5400301c104003021000d4000c01c00c4d0880284410703281e25141503100e040807290160075a004450048070392800c1c8404c0409140641030351032402e6141d80e10700d100d041040b5803038840a0102801c2c032004000500c00e0640c0031405240603a00300d6000c8000540c0c00e0303010700025082001c140d0041007040c036601400114020180202e407451545e440b1096240d03000084802c2c07440c80642c040c0d20850401440e181001c8000414a82046500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 738010890 1250 738009640 738009673
    0x8040e040c0914130c270e030403030507080d020c030a031a0d1e0f1a1e0c070303020c03090904120e03060105031009050f0f070504052805180102130510050309 70
    0x401c04141c600c0ca2400100050f5006522295010129845078000100c10511000c2043d140f072070341f02e0895688100400c00100354404103039240a54820207242e9120b08030303016500640a1281c803c00140000244511110780503844019000700d00014000941c5000041025505903524094688184c0c00310181d107210314031950381d0880703115403895054001c03507890312070f9075030045084458000e404100f848004441118003031104820350140051a00d000400002c40340524400103040c984c01080c440314018050090711601d08001c1c2445082e03152506100a550040202c0c0070080707409201d0800142c02d0200d071441c1a48d1f03000c0e0003081170b41c901c858800024840744800351a1402000d5103106103640601c04020414101c0740100035080c14842000100c1e5006000100b1034030101040722040c164120842400440340c60000582c1d5a426101110a81078a00140001c0d40300080076204d0841021190b001d50750182c541d840610f1900d42c040d181c0c0c1c402524080210360003481c0502c0038200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 738012140 1250 738010890 738010921
    0x255120f060c1106090f19050c2101020703180b072103090506040503210f0613111b01060614030406090201201b01020706200102040308040e040c0914 66
    0x814a00380c1500d4032550320030384c14001c060310185000d4110304070b000c05200d0204021f4080300c0050404588501c901c0d510541c0d030b800c03480b00e00c0d03018410458249400d16007401007401640b0540c0020355444c0d004c1e14000708852a10002e070004d02d8440c0101040390003148081d54815540403050b50182105a50340c0506e07041080034032000c26407500800c60014800b84071050060b0310403c002d507200c2d10f09070031a22400e200c00c50514000f074498820004006154041c084c1c0000c800d03a050070404010549110180c102c0080c0328400c96400101d2401c0c0404035084241600c034001d000b00507407900c8110071220344200110146201c1018004240440d44641c0b00b10003031031050601200c074520b4590f0110703014202410030b00c4550800404100308804020703111010072400d1001c3d140007802c00d040030f000d000400c82811440700d010f03100004c64044c00d41c1182c0c007454000740030a0301c659076000310403100b0320111021600c643d10104009405050380c02020140d60f2a4503212203d40e81c2c40a69206804 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 738013390 1250 738012140 738012161
    0x10b0102071206061a03040b130c1412070b07060b0a030302060106121401060302030a0506150a03021b0a0501020403120206070504030204090224030a15030255120f06 73
    0x380e07210400aa2041e85c1d0020300483e542e1403049603142c0c6020306185004c04030062031090301e032000106010028490029200646010860521a1036515070101e200340d00807481d070010500c0390ba080400c1141024020300b200512606051010103208400d01550306200d20005015a2025006101107030280d480e0b028551390208000401c201701907103c0d0204102a0305c81004268008148214100380740038642e8000710550b02d441c010803041e0511b0440303105621008007010303808030f16031074040400d02107a860310907c28200ca8016405042443c001d500610040ba01104040741c145622070000c54001c3c40744005032109414a460f51302440040d0589040c2260701101ca1015440301c98401041801d14810511440c0e44030728040c3c00c10412203040154100001d00340c00760400c010382c2c0300381d00c01400ca91012054089500c1c1841d445000001c410100c07a0655405110307c40c1743c514030b800c1160108020281264400e80c1c4811281d00c5e0000c41001a00001d0074000c0c40f004100f441c1c20803190384 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 738014640 1250 738013390 738013403
    0xf05090c0c011b1202120403030f09060e060f010e070819090204021614010e1905072103020706030e0d2a08040f0504050f15011b06050612010b01020712 67
    0x81041e030350305400c5034070702840000d10b421105a940401c0398042c01403101c2c0e06000c141145004400300b40d5000301036005200404040d1034048513010120f00341c00c0701cbc0c9116488001803010005085c1d079251607030001c031501403800c82d0000000600a9480240034060029903d910405803581c40100580d03101407007500ba40e190320b4110600042c0c407240300401290740240c01d5040b8030a020b02d4489400041c10030f040405a042a05460b07143c4004501a080742c1c811110f5240503034001d06d001d030b0411119038412685040e1814042c2e04200341c0c1d64020b00350034400d5007501c00903510b508080d02114020a94641c0950119074445140d6005045904074516440e201c2400043c071280041200c0c0d40c0030608841c402004102044503c0490000401501d01141c09000c180341103000e10300c0c0588020044903070440951203008859000321060421503034003500340d00c00f8160500f0001d0151605495841c025405281d02e14030854040c4501d0327035401c10581c060548140380415610000015000a0303500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 738015890 1250 738014640 738014647
    0x30b100b0d020a0e030706020c012f0a0c0608010308030601120b150904051506030c1810030209031e060c0c011d0c09010e04170a0c050703030806030c04060f05090c 72
    0x5108010090644640d02a1002d03a40d680f014600515880d8a400810300960008000f4800707550003192039060003500380f900e03035808916184440c203036002c1107020202504c20103d140701e5107000843c41c02807946c028950302d8100b50b40c60004480c080e50900c006041c030b0609001280182d0710031680c045444800413400f040d480000740008001409049000250b40c0740012090ba0340e040c54003560b070384510b03166400d080740103062011504511000f0b00780b05040200207881d615440d0821031048650300003800203080e0040d5131402170001c3d80041c0441e8403e110700e4034244c0c040c07101d0b6001c441c04158120003516007519501c03040741007504003002c405169500c07011280040c005036280d072508032006000810026044005121440130183c20248075111443c04005c04140e02c44410103401da000300003a276450141c0c480880701c800c2e000a00a015000d803040000030b150340200810b0060314100c042d80c951081e89020481210f202c0d108540a10000340410041440e041c120150311038a441036082c80c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 738017140 1250 738015890 738015899
    0x6091515100e03010f0b0d1205040f0306090b09191101030b120d0908070f030b07140309011d030909010e13051e0d09031509080d060f08061f030b10 65
    0x4480841110741c20000d0039070202008107207024050880c0c0302200060802c00f148005000c110591140344018101d0b000c8000803618581c802d08c101c030014149412481d0070943c69113400c2c4060301c042c0d03d055802c941ca81c4045000b4076400301d4004c00a000c0d0303842413000c404455403841800341c01000000d06156070340049405903280d03400300c0344402c0030603009024140c24108015009541c90340118810394060481404070145400010090725001030090005540b001e1040f0f4006150b00c821340d14101000c0148504880150004c00c003d0036403400300000d1280c5001801d40e0703401030140c000c1c0d124003040e0041002c602800081030f04281c070410104403955041c0c43c0d85280c1464a080c1811240c030100b4081c039807000074001c440d0452100d203050030a2030318640312a00d017036010b501c42400040e51200304908000920f0201c03500344091401c103100d216174480544c8030b01c1450b4800c07a0518001d400004260715200790154110f41c90a000003c0e415085845090360020300502c03088100910381c00105 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 738018390 1250 738017140 738017149
    0x6021506040f0e01020c070e04021324060c05010c1d091e0f0106170730290f180705070f0b0114010206160c020a030804091d06091515 59
    0xb00810200f00140c0da841340800c0d41c03443c0c103969a22615103c1909801d2200507944c400e04044c40040c4500c01140c103540b091035100b6089859012400c5a1440c0302001980c50b401c107840104450081008000c50301e480003041d203884110901c1c8102580c0b44602084007864102d282036000a440452a002101c600c540307554184803e9804802d107011140c010004d0b1a44020b0752000100c0c000590402805e0408000d81004500710784040000020713482c240e030643d0303022440340d0f5514140390103100102c100c0b003915810001c0201d040c170403643c0714103c803031141c00c0003540d00c1a080c2c7c2c050721080342248a4000301c094448050420020844200701c1d40000c5605003400b2000c1600440749203e041d458102d00c5480404c505000d241550001000c200000c1d60f0380581c07454210041c20414101042803001076807200650b000100062008100440d41c840d542d480b004205a20340b4103c00c103142d4840d100c907550402120031001b5a0320400741009482842c428041d000b5805521005554980c000000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 738019640 1250 738018390 738018401
    0x9011b0c050c09041a180c011d0a03150c05130501030e030717090108160c02040e0c0405040b01080706050408070506090109090507081902131401090b1215040606021506040f 76
    0x15113040c1d0325121508100317500c680e501500724441600e418400c2c0740320103200d9240e8001100c80340c14002c0c030442030410303100c03141211501c50b10001d00182480d91240303441d5800b400b038000c80c2001c05107084003080700f9030301480440d02d284200d400300310101840c1500440140059071f46000180c04140709410014800c0403c0c510b42007001c00301980c4496020000403e50240100291080300701180c41d8681180c01000b02030b401130f01a2000300701c40c140b10390004d01d40180500303180e4105150208000a002402c0c0406050703600540664404607030380c901c1107500e80254000e2a141d600314042c100100d2601000a01c0d8034007040c101003000c40c0e0303910240800c44004644940115843d20b00308a03221007400000703030605110101c11820034a0311b050b44a10007003240070340420303501c2041940305107a029082601c0207040550049540c0c00301403020000c0040c082c0c0740f00740c4010044040b0b00003031519018103816076280d0f0b4010103e6100702e4191702c078400307c06050190803654410580d1314a14190052 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 738020890 1250 738019640 738019643
    0xf21030c02010f0203060d060c0e0d05060604050c07150522060905070f080705060315090106021606050301031e11060a0203040e1f050d0c080d09080609011b0c050c0904 74
    0x184040411006801e541d40d640d20f59081c01e2041040000c0d550303c4c101c0320f41a440d0003030360000d0b43c400d800034159003504031481d0469000704201c1c0030b0410464005805803050105035014006501c6140c00c18600707005604000b800300c00c084000008501c8260712242e804581000420300749070720000700d10b4202e200d0303500644840d51118059000d01604000100091241c2c44010419510340380403a030300d4941c980a01842400f0010220301510b01410444070a50b00c002c211b0f8500b56540c0740060f44d180c00c440c806ca030304241c0b450000181d050140303003602e04076500074100e152607030302600318003001c44001007040f0360740c411440040f86a600d5180c0a024585035980081da611410598840056000140110200c4d0701180c0e1400c0c80007040940d00003280c4042c1c4242c19103a69600c0c160034504242e42080c5000d05c00c10f4125a01940c0c032940450844d40c5d1001503501d42e4480551719426588203000d101d0704642400c50100d01b15118060801c80e050088060f40d03032803508680060b8030900e0aa80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 738022140 1250 738020890 738020897
    0x30c0a0306030c0b07050f0c0303090420030a02070228050103050405031b0d1101110706050c040b0c010614030c010804030e0a0308120405071d1f0509090615030a08070f21 75
    0x81400c06c00c42c00b04005d0340d40340d100030300a10118200000007640c922a2000050081d9200d803440642204240416010380010751003140d00da03e0000d00c00002504286020380c4a4201600e04d8801d50b01204840042e03001e10094440405041c040150041d050207001102c00d4030007041510552000425000c03428225070018051102071003000a00c4440c03d01018140d0364900036030000a111140f0440e114290300481c0450640e89080303100311180100d0b80444050310300000d4180c0c65060640c08402a85c0a81c0607001c14600c400d0145030751480140301c5c803070101c0c180101080100e4001c29007030000410003001e29a076540c8030b6031100000d801141011014800c42e8052004010082c0001d00140c11100c503140418055084440250352003c1d118a503810301d1090b90598510000c0e00300005804007030b04600013810403603141542c0b4a8200e881c00c255010303c0d24047c020f440c02149040150b40c0040c0342c0b50034908181c40390019000500070444074510340e40d07802c0800b800c25071030405031185281c0703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 738023390 1250 738022140 738022147
    0x6120103030207050303040b040311031617011401290910110c01050c030a0503070c08031e06030d022e0c1e03060b0d0e07080601090e1603020105030c0a0306030c0b 72
    0x41c029241c00240d40005120340c10521050020b0b4008009403011aa040b800c0c031600e010302c001c0482e00308004140b01c01040d4850b81c03004079100070b100e000906681000c00003001000340c1c2c60a01270400c0b100380a1681441c403140032007c1c64440a00480c3d500c4d80003500c0881c5400c0d02c0000058203508000d1018012906003003a0507c1c1c80710134044450b0b5a803007070800c1c0340b40172102c11045032a4881c10f60311306c050090200100340120320548548034000d6200822076030742c0c20a5092070000d0314100007180108003a0307800007103071802c01251118010786950014070813000c0c112041d22110a061030590080401c80c3e00242d118115405405245941510b800140c4144551060002c5c941002000281818a0010410b100060382120740450401070300050300c00601040504200c0a540078038414801c00c000030420340c186038083c0d406841103008541810b0900a00842d412006100290100304180700250000c1060401010244218a40055405d4070b0b681d80013110926504241000030300403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 738024640 1250 738023390 738023393
    0x209040201122d09020619050906041404150f090902010509030d171608070e012601080f0604050d18080307061406011806030c030e010203150a0b03070e0d0c0506120103 74
    0x10403c40d6400740c80c10f0306002c0a04a034010445071301c5001035042003000d8a4400b48401485007045d00c400c0540141002d548641c0d500d42049a26103442020707105902e030200144140302c604080c4c0017120304903005404542e03e00102800182820081a030502400700403110795a07805002140c10080d0315226004802420000c500600800030f00e461010302607005040d2016400201582d4042140e28001c0a9041440f0041b203540c80c011120f1404050b1a1220340a001d071074081d400d050b5070790442298420744e0150500760740d80034199800b80913a0000c1003606c5a240c40f8000c050030f070001d5001600300e91135842e000913243d1303800b1000654070955106a080700ba4440303a007041383c004200b4030b1310007140d81d014015680c60040900c611000d040d40c0e0303030760395501c140240c11842070302c8407040086449160155105004031040803080d48034100c91400400d82c031b00d4100036640251055079454040154040c20300051861014003507a083e468400005503695404004198821543c1c80010055156 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 738025890 1250 738024640 738024701
    0x90f0a0614010e040b040803040311030304050c0907031a040b011b0b01050411090102150916030f021002060702060705070c1215110901020c040f06080f060907150903020904020112 79
    0x1a0001080002e203d002e000100d8544005150000d03041520785075603480b44d2400b61041d001d064a034414900011080000340040418440000030081d218a0015650914114202c940350750788000c009840041e0b170000313800e1030b0f8010021820103040013410403031124004c9294a5140030103d40c2c8641901c0180101d05107802444030148154111504010707449001035201e102040720180007454031070005106201c00c010035203103020764a1f5205035290b141d0402d0b442003181c800d01a03000d400101241012144002005803040c0750a03030140041d03480c0c40b042144d00342d000100a07103821034482c03400b256a185e6542c2602d17066200e00b4122823640692400003050792109180240c9020040c00f014407a44d8000c5406030440390210341c00070f0941030280c4400d00030502504050280e1142c100400c0701500c0000701c15010350b0900044030102d07942c1e90685030760f42500c42d65250014911030fa040006060500c503003a00300740705041c80420140707480340d0041221000000f42c80a0b015607070040103084130 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 738027140 1250 738025890 738025931
    0x10501170c030c011b0c03320a0c05060309150f2a040b09031507020105240a09020f401a1303050a03030f06140306040b090f0a06 57
    0x1c080d006001c030f005810001a01341c1120007900b13010808a0720710b003020004c60f02026406140e20084614407000c1070b040c0c4101d03510089121210f00c500c0e04c041e0300525000054031270411948000e8401710142801705000b11500b024107800b03840e1207440c840568031400544010710a42021110b160b851506c0c025040000420300c8103403105010410803100d45288032421142a64810140306a4980d40c1102103031814562849454440c011182440001f50381900258000c82c42200c0c03241c0041800280030b941229080d0780c2c0e6910100d0f40401b0081503081e60041c08003044c140c00418200050040100040c40312a41c0c0b40c1d01890f400d030f40c880d00b0a0b5049500e0398222100740c04050416040c040401801862085c2006d621440031070440042d0803c12282c501441e481010740d51100441e2901802408824a840307241c50f0800e200400c429521512010714180010008d020644440c6c9840321142d0000d891006e00c1d018091fa0070502e050200f00351a1b0640c4514000103660f1404c6142003071580 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 738028390 1250 738027140 738027163
    0x50f0f010b0703021b0a0e0903070308060312120a06090513031413120c080a030c0b01050409081204110d150c0503010b0a121d030c072403091401050117 67
    0x1485400c2c0441d90002e0000c150907100c0822002c050090400284a803420340d1119038121364040400112100100c00b610742d4510039141c1d40c8090f20703103008160311303a00c091003e42c08800c03080c03100c403a150300d0700b41140d0741103121500000750035a01c3d4081c07401621800c440d210300c00f165450340b0310101640b0191781010000a0f4040a0524406903041c2584001601c00c91140380781402d00b44c001e00040008540040c94000c0c100e0b514198103107000360104040541c195850030400000049900f010f010320095035500205461a0212000d41c2d586c2140d0060001d0704c01e01186150003510b0f03100c04001c081018007408214004441815080b41a100742d202503404115040c03004000460a2906403815419181058a10144840c440c203008241300401303003150030300c0038030083d2418001200418040159506a4219546030a84c3c10081c1c591440f180605c1050014401b02031032196201c6115180301d030344240500700c2088045402e41d8000e030400102c0280f403ea80484a40040181c1b0b207006 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 738029640 1250 738028390 738028409
    0x90e0f06100509010c02061e1902010609060e04030521180601052b03051201062105010302150703121a0306130314090415090c090e010509060d0f06050f0f01 69
    0x2001c000020302c00304480c0c1c5d000f07026901c042414603040801c5840603007150841c00d00d16441d20f001010b07600c1e583d5014072401026501c0d210010401c44481d005000981d9446100c210860b00c5540d001c550940c0001c81041c003118040d40c070540e036540c0180c402402103080603850103000c03a400248905017003040c1c1c401d034030a5500305400070349240045d415100d01d8070845100c4290300c0b250705003039a051040382c1101440a018900106196801000390360076020b900d400c0c01e004003582007107141159002c2c00042e40c0191600f41d03c098003104900100000b51080ca1b00008080f000b0103150181d030310080441501c070403807595004890a00b00150795001c255918000740c10700f2142c80c06840f9011038400140c0c82a4006044800c5840f02d8001d0201540610300740100d01d641e9480e9203005004103003c0500081e4402000580120380c4d0710028140c400080140381c10717454603005c2101c6940c20b4241101c2c44d200401c006404a0402e2041c1c911400e412070352600c0e02d281149821451b249d0581296494 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 738030890 1250 738029640 738029647
    0x3030411060f0c12030406110a0c110118170d05070f0303020304030c050d02011407090612090c05151305040e030a030c27141005120403090e0f061005 66
    0x10408405468451803000d0320724641d10030040c4810702c03103482002e07078510342403103207011140d104c068810040d40701340c0c01004104100614011803003c18407484482c2000140503c10351000724004088103e01000141000d503030031400d0301c0481d2580e00c40782e4002c50500903000021900c0600034030003081c0b01c507400d1401d5031404005a80701d00c4552100c41000c0c04040d800300018003011f0142a492403000c0c0c06c44200c074000c021a44009018001d401c0c1c0880c011181c08000c10000750240004000380d40860f120346074609000700c1d40740b0042c12000c9054503000c0c0488400141911100410b020704946040240d90343c00241c225078010b01c0c15980030902980ca002403692a00d840427003541e801821500c0c01141d08a109481150341c62911031001c420f410140c41030011003182c00c0300c90801c84505003000241102c0c600c2c00c115140d0745650b41c8502040c010441800c020396181a115809403280c10880511901d80003840c8145100701e650320080f080c02d80902400c0d10f001011141300c240145806840c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 738032140 1250 738030890 738030893
    0x8450d0504140d06060e070f0306060c0209040519210905180618090a0303050610050307080901091506061b0203070510020c03030d0c170c0f0c102c030304 68
    0xa00e11540c401d016640c0c2c0741c0e10b0b0003a055610065800318075600018140140c513250102d081810304162107400116504a070b40344022030107804ae000c101c80860b100e451900c0c03850340a0011703260b00140210740500034170080300c80195034181881c0390103008800a4004000f004032164111100124805c140000301e641080345e55540703540c8105070a40004600035036200c00340403ca219412141351911040200d08000b81c5035400910840d01d140a1340d010f000ca03031901000d03c5400010f2560900c0041c00400c0095038050041003640d0300400b042c070000a02c0380c841c0d11840842203110403000076075034071403904009082d8481c5601d5030b000180c00c49104210740320350001e5070f149601d2103440d000d00d044501000780d060091204c01c051039000b8050326501d4215044140003025900c0d500300200d10a800c043c1446080c07103120038490310020700d117280342001d08120100b0342c2d00005103800441c41074200456600826008000000441c0c0d150352070041405d01070700882c403526651140d0143d20a108000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 738033390 1250 738032140 738032147
    0x30b1e15040b030c03010609050907060516080a0c05120301091b0e100e04090f05010c05070308270f06070306090c0509100302040b0708070302060a06030b0708450d 72
    0x2452500490740010000144000720f4108410078000300ea00d9460010001607001c201c0e000a03105000340c2040e1031030f40c0c6c1c1b202c034140c0d014040c08500c1a40c0d600740040c09000036541d64004d04050300e80d03041a0b81400115074a40c1d01e801c224408022040b4004401007014080714050200c1b4043d101c0044052923108010051210b0705500c0501d1040484181001d0414000c50006800480180003400210481c3c100400020014a0211010f600e000a03081000e0302c100203440c1c0d4994190b4070342c0442c0d00d440d090940c15010412031540344a070880c403411040c3c4000c00041459002490180040e4500801c0150031242c1079402a40c1103030600710607a41d4281d100013202c415900c2114622100503203658120300074000c540051120075400205401440000805045058802e60071034160707a8401c2d90312415034440d4400240001c2d02c58022a01c2d840c081c81e8202e44c42001811a800354440a40310f1100f140c41301c0100e11120160340bd14008001d12180302144000c5845004000b07134100300d20006e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 738034640 1250 738033390 738033421
    0x2a020307060507120207060b1c020901030f150c03141501050a14091519051903051510030608060609070509130204122003010b0a1404060f030b1e 64
    0x1c1485a65400044071180070750000140b9040390031013151521120702e403540c0148001d907022803080040c90b9001d4005102c41c0600b80182c0d40c0a04103c03d583d20395680c0c0042d0090f0301e10121600620f403409495070b080c4038403591000300c0d0680d802090402e4000ca803285140c101501050b82160b444e00c0e5006541d030454100c0f4161500c3d03240084d118100e103c152201070080070304030759016035102090780780c510800c0c0c007400702c1c44c26a41115068201c0740c0c3c402c0e00c540c890042119809a00c1030784400c4000c0c000d03403101d0392007440c1c00e102d10540c600b5100084c102e142c0f0300c6941800700307944804c18000c10108100391648040180c522a0b4036061500000c0c016014038989948640042c040400a030b8206405440081400b101e00c21590700051614804070300c0031543c2540d9800445114102525050152150784e000241c210703000c190a00813454900c1050410113a0000d0312000006401c50452807204001c41c040d000400760781c145080c43c00810348120b803101e05054070703503c240079903200b091008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 738035890 1250 738034640 738034643
    0x923010e1b030109050303270105040203100b06120f0a1406031c02071e17031c020a030902091003110a440604020a090c020c09090a02060d2a020307 65
    0x41c400d034440144002800f52030301c200000c05c103020100c14400e01160710b071241c41c42d44044032100368550044464250880d541124040d502d94800b92540d004080c3c0d6621101c88080068030142c40d20f6000c0e18000041c0c201a580d030b0002c03014a10030803c5202c031138850512044050301c2080101d08000c40000d682e60203404030120514240710748032804c00e000b081a41c00402c074a4045440d194018185004494600e1041414400c2002d010040e900000310859004c0c401d140329030001103404906240007900020000c106159940f2416009030755080030407407280984890224146080d854940d102d4008603401c980561203204d41801026515a400002d240c2d2000c3e85500c8003000e22040c104114103403d120f000700e40c0c50940d102d2a40804204035200754001d945042e00a90348842c1081112100407544006800c2858031450358034203c07001e20307000760a86048440e582615000940d070740d0311807800d00c0480d654524a8101540c907070b0306841c8200e50050b800a030244001d1901a4503031181600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 738037140 1250 738035890 738035923
    0xf0c0503150a0509031b0604051524010e12010218040908040b03070e060a0e1206011a1c11031009060b0405091e010803090102012a120209040923010e 66
    0x100c50901c05c00c1540e803100301640340643c0c0c02c0407121405032500380c156001c3d036080c024843d03050143c4000300d030640e00600032400d20f046030f10b18140c010785c441c0f60810b581030704000b90258600e01c07551302d0160316074a81041400042e03440241c4000121820080300c1303000e00890806024101044182003940d0444032040c4d0920323074036034030480121090b09054020f00e50120003c01c00c1c524071548800c07489062082038517036200c01c10048841d01d80c3e0f84c40900c40c0580da040d00003829400c81c000035014090128400c08410707540c0c8011038035a019a40c14010a03032600c0303c08030400c00071a2450f0f865100600152401f041442d081c00706110301817050780101e43c02255002c01054010613050380800b080c201c0c00c50101c545585450b200303602c0f81d1001800500542c2001092644e5000c142c036001c20382000001c03111403402c000300302030f1035500e03c402d0074001c056401e0000117015211402140229031241000458454a0b42042c810120a050200c0300e140e150601c10004c2100004040c441e0106003075 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 738038390 1250 738037140 738037151
    0x4171c051605011401030b0f06010809211303120f0e011205180610080127030806060c07060c020411120a0e030d06030812071d06071703040f0c0503150a 67
    0x500b940506081c41400300c160b0085800007040c09201d0321124080e0100e5601034105031100c074011a10124195000100f5400c01c18402c2c64291812401903481c03880360700b1050030204038510509260090780d1069408084901e48080088c0c3c1c1310f070038416034440c9800c1401508000e5030000305210190a03081c1484d03036880010038071000c80c481d5400c0100015904035402072424500c4a085023140344181c1440d503080400e503103041495901d00724034205542800d103801d035099403000c40c2d4400000e8013954100030104a00709410406001041c041e010a440783c0341032105a10501003112007120910780348010910a2410f0340c0c503a0780300039820004c0390802143c9008c80351055400d500c5000d100c141b5480c60414004100304140f0040c050f80c0c14041a00300c003070340d150f14081c0d943c0141c98944030000b03030b8039070b40d5800340f0b15000015000c03260048081c4061030600c5040341400d54015035007640d2540885410701c040065851001c03002e000305401411124011805030305907148003070040c00303862351981d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 738039640 1250 738038390 738038393
    0x516150f09270207050c04060f1d0a150e071704051e030c010f060e01090b1810031208090d140403030e0411220e07050f0a1404171c0516 60
    0x2400c112003070724007070b040c115520300035071814a41d100c40d14240c0c81d000e80e081c50400900e0f203542070074000c06c55000380503640700070303100b40c14046440c4001059210610368a01503a810319503001d0703580c0c02030500482d103000c59081c40880545411044031184180500e078004210001d980451001001076000c4038003944802c0444000e8154050300c25040c050b58030f03117200f003510300d40c1c241c01200c1240e01505010141d6600d030801001907500b1001c107180c0029030140680c0000c0d0081290503800b03902541140980364aa0b9140100c802450821030009410402440b00a45043c804101003960758100042440034000505006001c0c500c405001d1000e5844140f81d40d41f11908400c2c007080748407803111396440080580300c12415450a440c0401d085412010540b5415102024010109912600e04015003620a41100d40c0031003400c404004c411030f43c5000640c0500e010300040d21141045100600308501c1d124604055580701412903420b03036401d6908690040111854403242c031b0449480c04a80703 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 738040890 1250 738039640 738039689
    0x7030c020d110402030c090a050d02060712090f0303052206081302010302040801050f0108211204060b040905100f0b0a030b091501150e041a06160516150f09 69
    0x30a100b01d5001030002040280030200f0034002c1446030750444402c0e05064031082070000d100448240250801c40400c11040030456001c0c0c0c24010391f02d246400307100c113030301c401c2e203041c9201456204801182001c1405e682c6000500e00200311442900098a101813070030b400140075903400341c0700b00781601c2c0c003820310000d41e4031a40459002d031040c0002031005041140451020641c03d03c21091207004004014550600c5244c1524081070510845810b00e1042e6180c00c104140142045980f00d940340f100034a55211802062000e9010b00040c054404004d290300040d01c15141030712405a140441d040c0040c1e80d00c4d9001800da079000307490b0103081e90748c20030700e945440c007034040c2510500142400000d807800180403505116100d583d5003a0031100400a00080e21082407041c2103084440d0781034540340c00e103000907228030b0750402d016881084403a01d0700c908004403a05a0741c0720030034042092002d0500b00789942038079111391804000103100c4110027407004816004031884080d2240c078000c1c0c00000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 738042140 1250 738040890 738040913
    0x140909121b061602120f0319060504050703091b030c0e060319050d0201060b09010c020f01051c02120108030301030b04030c21030504050f030408070b2a0a03030f0207030c020d 77
    0x300501114003e080c00340018003d0603480d10000014454504841014210003003a0790880c40000b1a00307003191915a40c101e1142101d05640f02c1b441da0741e203800101c9135079600842d03001b900701e9200054400c00a040290b10015540c14480490320040300810014071044254004c580a40c403044030a61514400a0b04045101000003140e0000c40750607401d000e4089041c03140c45010b5002002a6070340c80701144c0081c0075060040340800c100c0c000382c1000d410025a5252409030501d01180f5008140501079a031304008410f070303500140d020507070001140030909450302400042000b03509562441c0e44003100314800600040400120007100303800c021851081302424205a05150300d000d1a495008004050898003544c0c81d100358031018a040070701000b2501941c800710054900382d401e0100342e420a038807202c04600c11504400e6104022040384020310205070f00d41015180c40041800d00070240c801040c511161031740304000000001381c0180f020030394203034150340408142249041c07000d070303000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 738043390 1250 738042140 738042187
    0x1104050d020409060e1e0c0f090c0304030309050303010b21010e180a17030f16020c060703020c0901080f0d031a130902090a05061e090403180f080714090912 69
    0xc2019040407240ca0900e464020303203480c020440742c2a401c100200008e03040310b80c0030302d0b0308280e44c0c1c2c0103d54042c0380b200046602c54001d0902044158a655840d465a40700b40c0c81030f0260540840c000280309240000e110740b28541b030f00c4100003541000040591302d40d018041254011140701d4401101c1800d05c0fa034800250040100e419101200c1519052a401220305414411a1000144800000701c1160501c5c52065006020310b0518100380485c5520003a029001e62080d0005480c0719642d0f941440c0c043c01462018020800b9800351441c40c280b9401c01c460241400c110301c90544080c010103140c40480110f0341e410000340054013000c01460200c80c041c1d0804506010040d030400769030401030040a040d070b42041d4221000d114070190348058000d955009805102007004603110710340c031480d0752604103d89480c4580e1210441e40400d041da00c040080d07004824104212a42407103a8091500c080d258010b10b841d091000c5038a80c10511071030303e8045400300c0e20340f545c8942071415104c40f0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 738044640 1250 738043390 738043393
    0x405100801050106080609090d0807030b1c0c0f0b0408031903020d0504060905060a060b19020f030301032109050607020909010f020c0709060902270310020415031104050d020409060e 80
    0x25612070300300401c8070305d086540c103002e0264900850b0615400082c3c854440c2c1d0640d0300c40d1030ba500c0f041d400300e0162003080040340c6d0180114030016a0b41c95a5506091858490046e214005160035036140c84c480b456845070038090000d0004003c82403000c002c07584401c48a12800111401070304040e0000c2c001c4807030231046140340400700002c0110307540c4026185c40c064401c4a02640d500a48034003038450500621320404c01c1444807080d08400c0704100c101800c0c1ca4011303034034000c0308000300504e160004d03401916007005074540a00d400030383e41d40007581c8a0300751900d401813034180b03070105200d480b5030350000b405601040005034240c2d030294084100c902c1c01d08030039503503114a825240da442100c0e006110200c0d113000000101c0b00d88030300c2200d050701030401011a181c003000c502c000380c0b013105e442515050301543e000300b4200b800b01e1008202501031009a206d0120110350000e0480d0380030048211080d500700801d001c9a0707214440d404481d41e040f05c0201d0848c1e85031070300101420303000191019a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 738045890 1250 738044640 738044651
    0x41409010b0112181502042c1515030406060801110406021507092709060f0b01080f151516030206150907030b01050c0a05061b070503090405100801 65
    0x4190401180307250240e0b516440105600c03410001c0301c1c0b03207481d081d00b203030444502c1900080202d100411000059480141041d0340c51036468006450080d064990b18624880880969000c80e0b03001d07000021501a41515a450780209621386a080d80300090b500c40480000e0412589401020181c04440b00038400c140b40003a118450346c029002d22030250080c1c442200010041e0980207100d43c81e1070303a4601c880c500d403071051010f0f090361044100980341441d10120541d8014014540ea452150a000410100d00381c03000302110009220641000070301e00501c000da040e0b0b41e900300e4005480c2001c4031640340131500000c11007003c03141180401400807840783d01c98900d800d61111014065003c0d981c29940303440703600ca540b150004074280c2c020a44404210004e20a600c25000c200303040c100305203401d0250395014508400031a0848190780701d0310402c20502940711758034070f02c42036a000c041d08080176030780c401d03813a40600c1c80c03110f00860380c032400520b1041e45c82c2000b9004002c0c10303008000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 738047140 1250 738045890 738045901
    0x11091302090910230f1509010906170c0703090e070c120f020c011803290105220c051204200105090901210803160806061612030b040c03050402030c01022a0414 70
    0x201b42c1c0000c00b2080c04940baa4400045403805140020480c804200703200c10941d98540221a8135003000782d05070104044400f0218040450b0b2101c03038007540040e2103100b65100700b03180c07020b00080817041032010040921610094213070002005409424242058840ba6503004100090034241e80e001509560360100082208400100749900c614500c59000c65039a0b20f40c0305010030007038501e41c40d4804141c4ca6980d082c9004840e405000440000e140c01c3d86072480d02405407091400950742070714845c111103880100400410498804848207003001418000c0711800200b15440520484901048010140072104164545261003d82c01501a9101d08040d010400c1455614024802050041d004101c05140490a4034a400020010328508041c5541d0b0058000c0b41c1151540906807207100c80680781e9110b000f055540212950001160729145c0101460706c1d29000c00541590850580741d880000c20f044007111540080103929070b83d0f248400030074020305000c5002551008000300707111 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 738048390 1250 738047140 738047179
    0x2b15030602072a1208040f06050a0809010b0d140703080a0507031d09010315060b0406020a0b0a0504081b1903080f070810050411091302090910230f 65
    0x4142c03401003100c000d009662640546860101084507a07280c1e0307540c10104600c00c008280041c50764491008541030564544000f1a84000307034109101241010520680c3c860f03000b50f9856010004038020301c00c0c10440700100e07004c0d2070b80b0500074180781502c12600402c408100b014030300075980892555075416220b40020405e400c4000d003200025014050b884013550508110300b2441001004a90a41d1940d13881240f42ea00220301400b14644030320b800036050080300d000e0402050076030040c1100010520f00401e52000c01064001d8040c5840c040c40003003502c4500761148400d102c0d0044010448042050327180814000844034444504460b55041543c020080c03402125201301102d801d807200b800075250006c00f160030011402503001c04114900d895046544003543c00c02505141c403107581c0102d524030200041c1c2c807446580000344140c00742405000150b00c03c44000314008294204101e50440083da42d1854082010086141440ba43c0d40203000e94841c600408141d1050940302d00751 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 738049640 1250 738048390 738048397
    0xe0f06190e030d09030b0f0403030b030f1e060129070f0c05090f04030c1101050405030319090503120403030c03030b03010c0207030506150102070b1b060c0d112b15030602 75
    0xc070700a0040d040643c440600407400142960752029440034165500320704a940160001d0090301019215070320307150b564409000701031803d003420000d4988403180c025140a142014004e0f5600340e0310034401086180c122000580c21031100c400c01341c066038400c442454841c000c1c00710203003504502c0390403035041003034407111326044075403d940004c1d980d07541c0d00032086019400c59010f40407840140d81040000c28491341090803070170504015040c1a00e03a000f0034a5500065100540f44908405036003500760031061035001404110020812907d0301c0500001a01032407000806000311303002d802c420540a500403510300380e030180007000780c081500b100030760b26616440155003a0080e00c0108000342e1803c80c070240500700603001400340f81d00e0981031242c9507114118894544d030007000c01e1400d040c400d0201074041c085510318075854070500c2c00a442110401800c0c1e03020b0340700400c01d102c0304030090701e00c445000c1450b804034294118451204405044c4184c014403000c4030034000442044140e6015 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 738050890 1250 738049640 738049667
    0x60d082206120c050702090a0e03180306010e010305030d18150b01140301300c060903140d080a150302030f010f060801020a020606210d090305060a0c0e0f0619 70
    0xb41c0c520884205810720032210900d00035000030780c042003044054244101d045801145000e40000e8840d61514610b0854002244400da40302036601c03100150f1508111850240c1754458400809514580e2038640d01c0c45008007070944981c0701c5e26140403400b1603554407401e403600040280110600304c43d40341d00600c10103460502280554041e000503188240aa905840e40c010203c001c8082481130f080f9030309440c2c8010602084449078010006019440240041820740c80740300301e0074214684440c0000c203200b1b11017000c0d80304000001860390b2110485404c0741c4130903400a04071074080800301c80041d25820194051040d09500d00043d0700550000c070701024040f00401c08183c541c8800c500707070300c03d4494060060f4841c2000c1105481c2ca10708034540b15540c4542c1000307082c1e5442c101030402c10300030310180120700341500400900c0418001280d2181011078200407002407c0c00c0a003102e410b02299a009401e000c64504403500d5507400c0320144c09106100c2081050b03c0300c0020320a160600c117 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 738052140 1250 738050890 738050897
    0xb0c0703081302060414030313030b061018050405090f0106060e1518011b060501060306180212070f022103100501020f101e050f0f10050108060d082206 67
    0x42d41d0b84503908034480c00c01c1d801041c05281c10315041049101a5030f840060f94140810011000b02200603001400103500c601d59504c52803505504001510074584143e800748180600c02ca211504000c03100015610105d400140c07075250000380c54a8407241e15a441100c1d86002c0b0045690351b00290800d024103c100d5480c040d0b50761046d590b403114014400308013400c10118185510541c0100a21140c1003610021140f2004403070b1140700540780281c0c8403c010980d2041c041c00856441001d00007201b421140075440e00000d200c0702c40400b1001000c40d002c02c80368040b003220a2384280b0468484000f040014088807000c80311030551644255881101c188090000081d25400818080c001d62901c20207403843d0601d010025020305010030003c0311080304807100390b010500520078031303003d04c05500d4036041034a00543e00c201b500b0b001500e1032171000071158080100d80c2c5d005140980c4242c090350343c01001078484c64032200c079001c0e0744c1101c4180c003070b81c0812075520403140c00d1138811140c1654 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 738053390 1250 738052140 738052157
    0x20a030912090f150923150901021b0904030c0201050d15180509072c04061a04020906041206060801181203051303050703211d0f280b0c0703 62
    0x103018090000407080300c6002c105842410000c1e000030380c41b003411503070b8034a403200605064880007440b9070741002442e803408400420300f200309503810030100d043c00115010440f0056660000165041c0004000408006044045004591042c2c0a852030f15a2003001030203829402244000450007600501c01c032044045554641d41541d806514060079054016002c4141480d088844240b60305203400704000454142013821229804a14422405a94001401c0c3c00c1c031041011144c210020480c0300301e0040c07084001e5a0307141000c603011106440403464241006180c0700014040c82d40c8814800d501e85030707403403010b6242c0c18400e4081900c500c40f1400ca00c140c096042d011110143c3e816030070700219000e00d1002030300070707001000018082d050145a41d00c001e040900259540f581c080022601e8100d801d0300c12117405803186403004e000d40070381440e64034000110741d030741a28a940001e4003c1031034000b40c42001c1e5402d40080b5500079060100c20f14010107015000c0e88a50740440010700d00d01d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 738054640 1250 738053390 738053399
    0x1603140f2b02150a022706071209050603072a02060a0c11120607020609060f040f02180a0f060824100803070b0f07030e06070f0201020d05040f030e090408030406020a030912090f 78
    0x842c3c0e8001e054078010607e604001464480389069a001100441030024080703010409a170b8070741c061445102281c2e640465820390070b0b40b20b20840d40c1050991091660010088010b03500ca201359032403900e070352504e119405024203084840742d4410400c19000f00300d4202e80581000c3c04584030b88203801c2c83c0c0840c1c4541d2200c50750036030303076003021a100d0108250300300120340002c60802c0700303911480c00140300080c010644079180501d2001541c840d840345659407074510b10580d07140607500091203c04064410403003010f901c5844611740030240702041030031000140d02c002c00b0450820103042c40d20b045170f807296124034103071410000a456091101300c1241c00a52014400c1c0100003101042001410440e164a80d0540358116102c5680742555000d00042c100e00d8901e200e607902c510b0107411070b040050f185081c05042e5805001c00b00e40a5031500c3d0420002c680380c0740483e1b070400d502400059a076503400034200c0c01812103d6000b80b82d90700819594002e0380d031044188090b58100401c8030b111680c6c8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 738055890 1250 738054640 738054697
    0x20709091109010e150d02040209130c0e180f06010309140c01090f0b120405030c0a2603100605090f040f0207060507031a0f031603140f2b02150a02 65
    0x7100d0b1a03420303902110941c0b156040c0b0721b03480c8000c2032010308052b051800e2940010544124403210300d0310710355944440700c0190380c07050886001413400c1d2022802d028081c0500d02048400601420701c288007000800d1031a44240d0145851f00e4000360007482c511145000c00703407034a600300c04040c0040d01250000c128940081040340803500d1882d015840c011085200e107400000007082076404e8001804041d0224100340000c540740352149464003610041840609081c40c0e1600c0e00c250120014010400c10700701c03000b18401520f0306d44c108642c8881050000925045845400d540c20a0902440036030310038880e0054416140700f080103108581d00c0d01c0007101200e0850424a04060401c91400d0b050f040041d0000c00c00e80000c2c0c1a25001c211145007078803600b04560084400101502058031281401d00c00351040c01c4200c0d0140821605c1d0080000410030503607204509100c0070840511814000c001819031b940700b07101d80c010355107003038541d01c0c000b0f41003201c003aa010f40e2030291420800301c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 738057140 1250 738055890 738055919
    0x10906050a0f09180c1205010e01060521010f021912050910090206040f06020c011101050105060d0c0e0a032004020702090a2f091008060a030b0702070909110901 71
    0x1508000d00080a2404a8240181c01c24040c050b413804110944038011480c1150307044090b10800305100d28040d01460110f0031500d010248a0705645841401d1000d90341310300c8038022034140140c01d001d124403001e10185c01000001c1c00120003610015100b06c54030100e03004c40d00d4440c0d854131401d280004074020402514411980703010a50420b16000140ca815584480a410300182841742007584600c080314088000b40c0050001d83d0010580c04055a445060400c034503855170000e00007940740c040410410f004840d0700071040d07520b689515805c1352045480300c2400070010301e05210315a503800c0c055081c101140761030031101600d207180304042c00c0c04d008540c0010740c0600080d040d035951504100050a42e601c907080c00745808407c100c1c036808040010032626031004411591a40d080b404c022560800d9040f0006200054003080046e9a460b0310300300459400c10140c0ba030617654440b0427800c1c05807540004c00348a20b0416000b061280e1196a1031801900f0f507010301140c0d80f0b50003202c50b000c9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 738058390 1250 738057140 738057149
    0x31103061009020d0905060916050d0302031c02370e03060c070c0305030f0c060106080c03060d0318061e0c0203190804230108070509030a020d17070b010906050a 71
    0x74030a0030100416102a401020a82015080015074420759034580d400d0420556000346540e229214040010411194200044c64100c6550290100664002e9101e004504450031b8800c13060701640d00b4240c140d01142c4105025010780c24400444400c00038029581d16803400280a85d820121560780c0180c5a681913520018000c0c203003a69a000c4039081c2d83c0c8032210072100f04141c501c00100186040014100d039080c208402911003000212462520700140e01410400a850080c4000031201e00c040f280c20140c01c2d9003d4615001508041c1c80da0030301c2c615010b030702050f8104005031036540207000203240b082152407692105e80401040f1413072602a080131303505811030b21001e07604c0c1040f0907001500c14030443d5800d003450340e1824000104100e440b0014002600f001ca070300c10f21740c2d102c5601680016142440c5041150700760200b555040130b031170000d00880400308501c0504c107540d40c20080b101811320807203540b005c0c2480d04c4d00c021802031040f940300030b0824401041380d00c4c0c801406419038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 738059640 1250 738058390 738058411
    0x11100213050d1a0108031801020a12030906091e11030a080901050a270303020c0102072301050904090609020913030507080306061b0102031006090503032a100603110306 74
    0x2810701c1c04100031050350440441e040040c2c81030ba074240d1200040814000c2a8a80c0910f440b00401e040031010358505146160454104060344000603090345100c080290725840d001460051600e840c500809602c000907000814a0707009642c0d03420351b041c104d03940c240f0610f02108103421050a060351541100401003441e0b1050000c5001035208201411445281d89480d0320f40a28440c960104100e030442a15440c180c4000240141501000b0200f5420002c0c40104942c62070020301003000031501c444440c28100b0070b40b001007542c1c451070580d0207858008000300701182c20781c51720b0001010075001c100e003d402d8000000341014031101406200e01c0d00b585682d0b241c003103603039205060780d800107041e160f00400921610b908904448910a40719285200042c0c0d242032120801035a411035600c503108010b4030740e1043c8043d880100c20f840d2000803200241412851b0705007100d80822040300c25007182e200e51525020010b4254025030100c03801003211402c1c1862110605856020482d0000c510 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 738060890 1250 738059640 738059677
    0x20f0a05030a171311013005070509011d0f061c15180b01110a230f031204081c0c0e040b01080f040201140d0b1002010c140f0405040c111002 62
    0x10a85c4004810340c070303030414500003008040314140b1543c00100350000001d070410782030100001c0400f074400c058001240d03041c420709017a814400204610460302498130858400b002c0707100d071501e801800c81e03032405004080f0340c5c48003003400c080308001c4103248a61074070504002c000b80507000d5008034441929280000320304a20003030340301400a4642000001e041007244002c50001590511801040501c030b1419280c2d0395030640f24081002d01e1400c1c0c05091a040301002442c5d05100103304e401a03c0c881140100c550750310b060070b0000740500c1d8040c204590038ac18103c40601c00303581c0066026102901c4100303020f03204405002c12640304cac5680d10301291010f80844c000c4121115102c0d070140c0705140c0110707a0702008200003515001081c89034082c039164102c0324020314203403075420481031051000700b001040c03040b4000c1135140002000442d41a000030204050b20342d01d401c070f45c041c00001d40144102c1d00f03113480041404580a500c0000381c000c101d20b01403082505d008075020314107890894080c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 738062140 1250 738060890 738060893
    0x406060f0305210d09111f020312040c12080d05010e1b070204060312170903120408130b0a120b18010504020d0b030105131401090b0115020f0a05030a1713 68
    0x44000704070010b488500c000713005805402200e07000e80c1404901c111403070300421118406103c001501c4206a1800c6601940e82c00c01c1c041d40042034444144412409a04580741ea003018101130b043d9030801c19440303100d0381c0e850041c01014802002c211005820811043e0380e122003a003161041030301e0312140a082d08031310041d0701030300300080e1910300c4c001000055420740d02d65840d00c100610441d43c0002c5101e58020320843c4501050f02c2da0302810ba000a50700d041d02000e1045904070000300003c00c040d00128030802000c144204007009422468141e66860309541c40203800c1c9544150382100c07050070306682c1c0c2c419041038441c8201010082c40c000c00613034207060400010350492661241c40c9561100048010741c0c003401002d006115000781012200f10034203007205c0e0a0000210520750780c1c1000303401c1000600704146581101c6441c44003034039441c440c036022030a00700008405c81261040030641428010040002e0000e003419803030344416240146240c01a01c48121400c0b126041d81000040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 738063390 1250 738062140 738062173
    0x516060e0d14010b0901231e0111150108060a06230906010e0402040306020306031908090f01050705101401171011070506042d02100c0602041701050406060f0305 71
    0x84400442d00012899402c3c9101003030101e40c00f40d100313451610f10341c01c0031001d0100c800c4441401100c162000840b400700d00702c1429100c5900b03403106040280342e094040341c180050004003018a5a5514010203581da5403101d43e83c0e800c1900c0307001c1414a080c600140c49503925201c0007070300648081c103201c46070ba210100911500020503139414402c01c50b0b0702a03160358481c4020400381d80f191030300607180e00705007040c1441e104400120300088001003407410082000d05003960f110349000c440c1c482c0094010303001210b8500401600420314411618113800d501c19a4000030780305681006003003aa80e0342e076050384582040e101c42006054001640031022004c1d0303508013100c0d4100c42e441640c80c1103c90703076034540b8ac28400c8400392140900b0a0402c1d0400c50b80c0c2c4100c41c0d0101e08110507001030b220640026101c506800800000e104c0c0e030200142c04c206494040d00c0040c00842200301c20038000815943c00780400b15002c0301c03402c3c601800400c02a05096240055907000340040503a000000c40d5036 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 738064640 1250 738063390 738063413
    0xd0c0203100b28050a03030c120503010b1b01020403061a0933041b080726060904051c021e0304080304120f050106090903121407030f180516060e0d 65
    0x66080c050000c03c041115260140200000c5210703540e0070343c80c90341505041441c6038200e003140040140402c01000400d040b5401c2e00c42007068540021220070800340400d009102d140e2000f400c05091285e4520400c8180f2405142d0f25030940342040e143c0e81e50a09001e44448840e400c8420001d0705140415030115040311070011100078100203000644042644410314800581e900040c510404002e825684898060241580300c420b540d1035080c0420940840400107019600076042c0c2070001d03040c0403041040320341403030500c50543e042c0039090100940740d03015030121000c00b00184400305801900041210304403880d02c4d026506280c00c15044a4038013030511802c0c1c5500085c801d400011030001e1140a00a00000000140b11400c0b0300c0c01400710a0100d9801c40303458600880011254102d0015540c0580c9a2600003a8a0178891124005000342600f134419407140700049020000c1c0082c10500000d020001c0480c000e82d541001c640807000e05644503000603104480c1c0000584890b41c8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 738065890 1250 738064640 738064699
    0x80f2d01090b0c03041502090a170a14030406021e060f040510060b030f0c0c06010614070c03080a0219030f0f0903060f0504021203040311060f0c0d0c0203100b 70
    0x309680c5200d407101d41d110b090036102040d07541c0c000810322080182e011289030304110a2902941086500000070f14600744901c50713170740f580ca90002010100c41007801146c1540d50300807200c5001d4610140c101d42d0325005406560090700c03a07640004c01c020076603080010421411001049035550302400700c0c1101c00068400c4890707220302d01209001300500e003d0302c0d024200c0303200c00c0d42e26858941580399008601401c010480d55081049540000c0c02043e8075065a04600f0070200e424100c000c4128184100035018140441140001c42006411001400c82c6010355007100d5070205100a0a02c4417030403442d0080105000f4071440322603038003400189910340c00c0c3d8140340d0480b5540f902c600701a01d10480001d4503090395070041000718500321904108000a03c0700441c1860304603039500040b25856121580700d96000700307103041c2218204c0120b5a06050b0f40c01560b92003400e040002e0248400010124464019081022150344462090284049009054002c114842441e510400e0b180515 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 738067140 1250 738065890 738065893
    0x160b01060e06031302030127050d1b0b0c090a0609050301060e0112030e0103110703180f15030506060c160e090d050906031003021f180b040b0c031c06080f2d 69
    0x548c1c030710a0000341e1910321b181e0321086c1000164441c0b850101c2c1000c442458001c24481014045510b0007041c2001c000c1041d486590745c00262204070300b40d101c501600321441e9115441e0a008100190b0003100b03482180c0040e03000348001502ca0018514008003405040c00004100320650003080c440c3c0700204007140c040c1000102c410300d442d10b00b0229440400c0030744c041f036420120a0041c0303540c14980c2d0001d100000c1661102818002c000c0c2c00b020710020a00105034941020914a80d516011224102140400c0b510740c61003c0311415101c1c108c922410b1082c0601500003103007048003003444061030f00250390700ca241510000030019203800c054150580316841c0100400182c55480d99448940f008840444104441410045c124698607010081d44102c00c01d04100a0041c5070548064401c5080615214000e0307024691071070044180c40079600403580703017000d0381011030350211098410f6202a10300701c0b0290098a555400e441941d0b070102141c0040c4400e08104060711411854074000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 738068390 1250 738067140 738067151
    0x706060302060403060605120a0503030106030e030d0504050f0706050403020f04090602130b1b0f06010b1b010f0c0e190e0a0f05091015180203040c0b160b01060e060313020301 77
    0x4010895a4103c0d8104031822543e4150a101600c4c0010602080c41c01400c01085200c2d00c9694242e120300044c8107a0041c90740310b801300c0c00c0e000c40c01d2098410841d980c3c4020800c038035203400c215a540104018207503580c003410802213000e510410451341585d8015207138024240f21401444001c00c01c01c481901c060b0b5003844910446902a001040200040003003907446001c0b14070078550f40c01c22015828001c0d07103c600b4522240c42c010500e14110b0b032307818943c152a920b040c4089000000c040000603195460120104102d0101e0740c070032101c4000c4d03a903580d80e1071540c0d141408420b4500842900b00c20342d0103c020418040401c1800d81c3c03060b829400803541c0401c41000794151101611115469007041440c141c0c2d440052141c004030450340381c10342d90007926041e90700e540104000c2c0f901a185400100007014402074801d040c008080343c103c500c0da61108244428098150f40108075552071034003000040c7c0900c00d0018000c00c903002084140746458296005800402581d4101c4c0c143d5287c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 738069640 1250 738068390 738068393
    0x30e0913120507050d0c0b130b01030204051f060809240a0b0a08070603050124050712180b071719032403080c07080d0c030f090e010b1312021507060603 67
    0x24405c10400700f10b15261200b0070026494090724140c0e0080584001c80c2d40c01c0b138201c0100d0700d0750001d54110781c1c0548002410b5142c44040c2c1c420a50b82016482000049200014034a41d02206d0248504a81026591880c02200d00079406850f22141c10300501c02d07130404a281c44240c1e030302500c40c10500620a8038030030358807141e05080c0301003544101c01190383c400c0100070740b00b11104014407084900e04004026108000040c0043c0115400980302030094008400c00724040c20054000d02009000c0d0031103955100008040c41d40407500855220381c0301c07200ca0f1002c007600c000303076881c04090310040c1601d0725080c1000c07001092500c411444000000c4000b1a003a165184034401450007411003640d650729145d8000d1908109602c0074817542d212240a01c0c00550200c68100c0e04c42e498070704010140540b000498042051390410002d50300c181d400007482000c90360052012035145181000341030341c0e03800d8a29422703ca109010b504000d00e104a80c03c54160b11000f400882d200c0c4100090300c030b03180d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 738070890 1250 738069640 738069643
    0x6080105062817030c0601051f05070609201f020714010210020d06081c0207090e010e060106180815040b34090b090f040209010c02030a080403030e091312050705 71
    0x80f000c54a280d400021354902545003e200d0a405000d0079241400b00d00700000d20050101130440c20182009000704010003000a190004244035821005240341d18840502200c0c0320b01086980703a00c9010b0384070040100c0110711100060760655500980700852030407410180050f5041c035590f04501969030540900103079171029250b904417800c000a2824103000809281010351072131949030304c2140c103980680c0c507070015140c029540c14450106103000410b40c05805003007600c506072158001c40c80003065480d4400c0340010b4204030b50500903e4070390b40f00420740e12100702d503001c4040c2010f64030016010403071070402e49030005804101e08800c1c07600c21440c2300c114101d810001140300c0a04044141c140c1e400b468460241491340c03880f52814010000246079107180c542a01d0181d500414855030980c0104202002c9035000f8042c1c503c0510280b070041c0751540503001c220085840100100210b040c00d00e1420300c1046502c21410904900b0386034500701030814501c020401c58200501c0001500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 738072140 1250 738070890 738070919
    0x40e060411030c0306040c1422050712020c06130c03050d0203040501090609080c0d020102031e190509060a110a02060c010c030e161403151306060801050628 69
    0x1450810762180720003801c140c10082c036410ba4a1007030b84010140300104003098090700032035081041040203000b644000c034441800e407418040c0c4401c01617203061420540c640209215900703545d1032281086d200790a640c124000d480d020100c3c1c1d1f2081c40012400180100d8104d01d0f54003c00314101030a41d640d5916203007401e0380d80014016040454200804e580000c003c030081c00386820280041402d100c205580d99210710031b4103206841e8600b0080030759009008540c3c92070109002640003c0b220488104a03600c1001c0d4840e80ca041100340d11400c40c414004e0b1400c01c0b00c010b00c0e09103824034103c4110ba442a5049034850700f0302078500c0b024016a40c060040106114880020404103180c00014003100c3c0080105101c0350890314104c0f0500251011680079903010324011034010624a01080c5040144503140846d42920824080c5120b0100e03550b03c0181c0c03082d0824016a51281245800d0f00d07015901160010441c0c500400080300f1410704007030110b000d03100300c440150340341600b500c2103c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 738073390 1250 738072140 738072143
    0x50d0c0f0611010f09031e1205100335130504060e272e11300c1c050a02130b070803010e07111005060a06030b100509040e0604 56
    0x18601a40600340c0c510038040c403040110692405c01603e00030361000b0b08807407625604903100c0b501c0e0304c0d004080103000d0010b2091b00a1500020009807605480707481c803481c1c49000c181d545107103030007181d000a5028408580d202506a104143c10212144d10780c07000d400a000c1002440b050003000b2442e91a541f05001c01040690a0f007009400d1229030b900b81c07501c07450924861440c10f10704400403110001080b4560101d0500001c80d1244d10312030f208e207070500c080d507016600d60901540c5042050a41e002d0300f0070058240c0c0701424210360140300c05141d00001115134100b0501e8000a07040c40985014080c000307a4800c06a81a01200c0c48500444800311008a24070350302060b61000c0da1101d80c8550007034240244401d01c0e1a01c42d44072244280014402c6410312002d07480007136078440c4186c480001e03180400d01244e100c49507840082e805031400f110254000c1009080000326644a80550380b401c0708040c0030605c1d101c00501044a00360702c104481e80e00280c0b40c0368100141041000054401c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 738074640 1250 738073390 738073397
    0x28080f120105040510060e0103181a0705121f1d10050d173403020c0109050607150605280b0304021003180602030f0f1f050d0c0f06 58
    0xc440440c4890903400060300618010b52403e020002c49514240c0020b058944504010351100745081c0101e003e071140050503a2001c110403016030410203040c03084a5030440015085405680c0c00344202c1c2c6900804002c0348001e030043c00800c82a038aa42d040303d000036031170680c41e003259858100e425600440381e4944009950071100300180c960401a540018150849043e0600341040e129601403046100074030300d0307402d0002088503200000401d0306030890030003903000140d801410403120030a40320780700580143c0280c00c01c5401640c404c170311000c15544002d10f003900f0701f00180c440420728084405410001540c2d4080400c059940704c807100b21131000700020801c4801c0ca03906010010307006510484402c0005c1c010301006035110405a911002289000106041c1803010804000076400014150910000505c03058508141c0c00900c22883e541e82104141c0742e000381120b030004600c2100c0070001a8200a0090b403601e803203118601c500038003088008a0f2240d040d940c12101c194802c0010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 738075890 1250 738074640 738074647
    0x7031104080d17060d03052206110d020d090e070e061c0b09011a0a020705090f09060708061f14040b04030c060306030510090f1218050303040828080f 66
    0x8450744400000030f98496242c60622906000001ca218a42840d40040c140200070446d10010030340140e080c0c81c070230000d642c1701280607075401000d1b0100c802184454000c0c0a850700354401d01c2d000140c03461400c0e0141da00c050005e8038280100da11a18040c19110801c203e1000070313001c0c0c0e0385000182000040043e002c1e12001054001c481c02c0303a10301080a0302407410340c001042482a2020904150b40d5041002a40c41e0700e00e080481c2850525080141e000030740c03100780074603510711401c502c1c4a075000e40101c03441c40d22144821307154604101d41c7c440d4440500d020368410040a03441650391265513061028000a080342031046580043d000740207070f410302007410014021034a210354000c0c0341d242010445a8110340300d081e1201001d0b480e005000340c44580000400c01d140701d482a005402072245060184480700081030200c500c843e0601020f004207000c2820b2030048226130403165442c0003003199401420302c110300f90558000d803254290005842c0300c04a00b041c00209080c4115200c41a035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 738077140 1250 738075890 738075913
    0xe04062301180e190f020303040f06090e0919110117010306020309010b061c0209062101050301061d1f08060406050601091508070c0602090409030c05010506010c1a0703110408 77
    0xc5800300c0000c40182d034000c2503a6203440d0900c1119204150b040a0341005d1301d0000c0c000310740355101d0755101e0f9006004206001807c554003e40e4101682c00c0c07006044015203038603808039074580410040c9401c1801407405400050440c1082005180707060400b00f0700c040403101401042c210903442501d169400004014291000303109200110804403101c6040040c030444c031840b00c0107140400384801e5800190000d103582c8002c10ba800103c02c130741190030044c0050020560340c580a03c41c0d1400780d820482c001c0307013015174103068107510103c82100e043c5c2ca07641c4094941c03c0b00c20710004140f412107881c0300400c401c4014002244102c0c0541c2000c038035400c101c8001890358580b03501c01d04514604c0b641d1151041c0d800b05866401c00502e03e0555100901400c0ca58020f103e01c500b000d5003c0d2400d10001c0815400c03240e132240a600980003000fa5986500043d1502d18055400800c615030248440b0b8000c0640d00610b5003142c00b6103800100804a030f40ca0b05204e074002c0d0030214107a80008803d80d0f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 738078390 1250 738077140 738077189
    0x1b010f020d2c0304060c05010f0903271d0c0405060f18010215010303110708030a1206170c010f03020d050420010c080405042414090c040e04062301 65
    0x701c808840c2050401211042c0c60540c0307034001e0740110010410000c16000500c442500059031a44120004000c2502c141c503010b0b0100b00c007043d030740c8c90401c0c6501c01c008880250340568821030703a688000d54003d103c000054007551030020022510f850040c440400d99807600405000e00c80303030302d09041365510b20003c0c014901300e001b0000c46046502204501110716100008181100c1e0316050420b100082629500e00b0000c081c3c20a02080c840840c080044d01e40c4012a41c40304071f0140c034100308058a80701c1c2d45c503842400b40285035607070380640c01070010b55109103034144643c84146401814152010716601c1514070945058400c801d288007143c51401030740e0358109410409080019200c4215542c0700c03014011403094034030460343c83d18410501d00143d450404072000308825503280c10345600354040a0f00c0b0300603481d030140142000040301c004007003003210281c5800d003030005641da5460740c1d25030141042c82c2c02d03103000c1d012059061b0310004000e000c00c0c0c080c1c058000174132079140d180c21001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 738079640 1250 738078390 738078431
    0x403090302130504050318030a050d0306060f0813020d051609270f1209030b0a0509163204020a02060105011206030f170c030c030301051302030103081b010f020d 71
    0x150300a43c580004d0200154000080780c28901d1008800980843c4007c0000d04008407000c0c05001c0b8017400c0340102c0c8007607140d07000005450300707925004e000405140048031500d80444054004540014014015241071340c1c100c4405846082100d07001130000e41d09002180140d840401c07015140d140c81d0f0380c0d003200c008105400d48904a040702220885481d201c80482d411800607004c2081c4044840000d03206031440c002035500248014018103000348031000030042199903244a01036a5901042e50403203a10520855040309030880700c071101d18450503142d241007000340d9a0310305080c50500131034030f4030b001924414042e0f0b00030384017942c5080c001505512400c002114114501075043c40024086460b2102d0940c201c007003205242c1c81900c140034076200f82c4244080c0c0d840003281580b601840040154140c8909450303c0104044500148040e40020300000b401903000b4000d900c030040030503003c00394a2080e4000407610a40100504040b83c0c80050134030981625038000c001240d0303e28103e0f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 738080890 1250 738079640 738079669
    0x9020a050d020d020d03020c0d0f02090f07090e06040603060f0e1203010b0d020f0d052701090b010e10090e0d081605030c030709030b0c19020c090c0c0102070602030403090302 77
    0x4904012030780c0d80020004001e01c90001c0c4a102c02c1a6000245803003042150141072005d040b540c080071031070410200b419003c14040303128220a00005180b800300c07982d15805582541c4821421905105039916894401403001d41c00039500c81002011940e00c1c000c0c050302c1c050f10500000c0041c0402c200909040c0b10384910301c0810320070401003010b42205401c4031052404a1001a02c410041d0030249851046a20036070040d4200801d000000b07600100d5806441d0034820682610040324050501707880781003401a00c001c80c1400100044079a800150768032a41e40c070070702c644854032400c10340c00b2102c1055102400f80c0c005a100201e840d00041c03529003010000e812000a4130507000018030741d1000420703030724075184040081140e99002d40380308030180d030b030105900c2c0342440c01e01d1580c005504007d51400c0341071038010303603500c0541c00030601303804612028001065560710b54014100c158407800d40b20541d91741c200b00e1000441c2ea20320145028034405d641c1c2030700c02842c500400541c400981c60 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 738082140 1250 738080890 738080899
    0x6060e21100203240a0501050d0b12030415030b03030703030b030a12020c0f0a0e130804241e02070b0c0a0804090c030c050a0e0405060d0204020a11011505030316080405031009020a05 80
    0x140d228031307617510509002111001d1038044d40c0d5421000c81e010160881704403154012401c1001601d400e80d010002d8003e5503100322035041d580c80b0140b002c0741070760b0301d440721550183c0081107c14046071087d0000038040d04c015007102c118904075a643c1c440d1200036007614005030060a00c4081520308800c1c1d12603148030803034400d40340724107116801401800c0504400300003888500981e08020b09001510010030307005030a04811245030100d00e442610b60105140001c181000b1507045a4441c00b0b000c264412540c014091039007414205140f580c8503e19120a0303110340a181c0002070030603402800545986000804d02c002c2020015041c0c43c9100212004c0c07141c24001c0d508100d51201041500c07240403240480c5c6511903101080000040c050003940282c00003c607903000c07c0e000394035854040010002002020641c4106001100c0c66000f040d034180c10410910001e9102044c8001606006220540c94250b4440002e8500310f245101003601c1615034020001b549809494400244030555 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 738083390 1250 738082140 738082201
    0x10807020c060d1d030f031501030203090303040b090f0106143a0c030204020a210c020703170d05040c03260a1b02031906050a06060e21100203 63
    0x20700050150148603d0803110b90307034070030315035480c9888412420303402c0c40003400340c1c0e41c1c80c400758540300c07400c2d40704030b48009034400115112600c551080c800c5a124545403806541140c949a8400407140000f034450380c528031071030340342d0042c004081c819400180030410b10401c40101403400c0c03003002c010310214002c003a1060100c1d04490100c01005248040c100000085413000c0e80c170301001d80c0341c2d0703940002e504a840410701413981908805156201c11001091154124200300000b040c3d40c0d6040c1030304010b03041100d00300700013140030b0240c954000d01407442e907047c48186902c0e0000c640c0122420707140103407480000c106100c0c840900c0d600203001c00b07502c00d203007050700e05100550340b00388000101000700e01c00b01c000071940c0489091a4656005099400703060b6040701c40606c0303403007620f41624140c1c5804c0201d5002c60003071007806e00b01c90b8103850b0700282070001d03030400c2400040840600c81035a10b0700e600c4003080340c1c24840310410350003084d00182c50381000a2188941c880d4401c40780507110840 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 738084640 1250 738083390 738083413
    0xc0c060c090f0904240b01031503030f03020a051c0b0913021f020307060c030e010e031903020c1603081b01090c05040510051519020a03050d1d0a0506040201080702 72
    0x4103400140c42209543d8000c468445103891904000f10441c9068014010300742950007400315007060703200c90800d81c3c0a00461078641d040103980011888001d0100710811410708101d8001e4000d4449003c0b282403850418007003042502c40384064841d90101183e0300c003140c12651800320221500001000803d100c0102c480d40072540420300300900e0080c00c59118000c4c2c00d074030320810494640d540d01200c207001c10000100060068403603400c0d00c100d40d50801c860b004550000000352500d803128444180d6200e4500c804c240e000f98080d1106c1900d40c0900460b000c19048d8540c9507000641c410300b5425540c40e14581c01c02e1640c480c984036050b40e641030402d07001c0840e6100b0402da00b550f400301c800203065240d4440010050761141c1c8040c0d0000f0084410a07070b600034010180c03c209440110704600c22030128400c0b0703100e01035010004c5c04108107000e4a0002a51580403076252145207e401c540b440040004514040b600c1e04110b841da44844104011942d1082010350060864001028403280c031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 738085890 1250 738084640 738084649
    0x60b071211120702220501030c05150d0c1e170a0603050654010608120a120914070609080a0f021801031a0108191104060e0c0c060c09 59
    0x340d241e4104464004030340c12040d940ca050b079100d054041c3d0a50500071604c400041805006c00f40b1013a0341d16400994005413a0030404030740c110501002889500c1c001c0c00300d004400030301c2103100c50030400141401340c4074468444000d0000481c1d1903100d90407088800c940611361800f0092040c0706003410408100005540012116003040e1000d000c0c10307010a4410b080d80c0b01d07c000054501415588160791802070480304000e5080142c0e80d4207035004500d5103003015084e1040c070302c140c1c00598028203190151011175406803d08160304d14003001c0c1361019022420965203038110568480a40f140980140081008010020401da080c540b00c0c0c0b518018450740c5841403294081c1a1012002c5c07030740115641c0c40100340e009101c0d07480b030044c10b586a052009040e400d402080081560715000810180300000b200c030890121684400886e01140e88c034645c2e0300b01501000b5802648450004c1500310401c901d0364412110700c810341e501c1d07004d2800141d00c0c008024100e150b18120070410b06045c2d031503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 738087140 1250 738085890 738085903
    0x3011701060e22060204060c0201080f13020904030212270103060303050f1b10021209011802060c100c02010e150c040306110706090c031202060601020d03050901060504060b071211 79
    0x100d50404a00c9020746001d80d004860ba003e00104030b2880004c0c086106030300b0410400ca0345000303a858004960340c41401c12000c40f802e1320189103005d00407030b840d1f0041c5005030000342d10502c213105a41200041c0044260b06800800031444040c2e03400e03140301c080c00c3c994a1119008942481c05110003451903d014080d8800c414688108090005490010311100010355002004820842c0c00110780059101e000b50031010f04d4901880842000c91103408050050310b03000007440280c19900d944035400c0081d070f0782c0a00d0b0b420072280100808416900d14600c601d202d90071650300045400e65174a10858200101c0b02d520440091814003445001d481c40700955082e030360310800003d0401080646007049001e1160010106c6062002201c10409211840c3e000c591003500f0303200c2000707540613050340c9070380c0100c1c0c250f40180d10244071035050300d01c6034122540040f244000018950340345c002150569031190010b141e09031000510b0802c0041e1812408d80c005581d290002d02000ac11000a0b240c42 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 738088390 1250 738087140 738087151
    0x140a0909110c070e06041107050c060a120e060708160e041a0d29061008180307050708060105060c0d080702150a0f05061e040509031204050303011701060e 68
    0x41d61407121191026000782150060111035080329070b42c0390313034a02010310003104880c05070190341045440503000183d01c040c2c50780268458098021a4807d03c2488440e4120040d40c004016041401800780070171481824002103030800030b003425240045001c0c100c048003405c18035907a4032185446502d10390101c1111920102114042030f4030900c0c5100e030881c0350382505550b500c6111100364500700100c01182003290540c007c540c0030005529a840154500c04855458001d5001c081d590505442070151541c4010001107070300c85404203052061860704140811030b1107500c641400c1c0440c8804100c01c50061504032002441c1840e1601001d49600009000a0900c0f42041c086004103009001d1104034248400945503245040031006026107658100d0100162501c0c5c00f140060070310701e041c038882d020702ca006550101203080030301c402070100500c548034034001403004500c4440711386a1680140c1c014401507444e54141900303601c0c8200c260780002c0c941c4c0c1c074042080150044000c40c15070b000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 738089640 1250 738088390 738088409
    0x9050102120c03040312020a0302160501080c07021302210108010603050a080f0f0d0603030305060306010b0313021201091101080906060a03110103020d06090c020c040506150a0c0803010801090201140a09 89
    0x7400e500c2c1929203140190b8000810102001c0c0d06000d18690001d054003601340a9401c0701c03003480007048040340040e000d0243c1400103503141c00040641e0801300043c510b1a102901d40091025064030f000c0480e0042c581000071071100100710007400c910444018058814080200403051850791384a50301d00d04110010b14400011885a000700b241c5c50070350300040001c1842070f0f62070902c51800001041c0c0d03400200c0c0480d1506002c40d805003000245981a614078080d820302d15140d02d8001600004400000c982c0306c1141122418005828020103003170314426114982c4030300c641000500941d40040440025911000810001d50b68002188049a0300045011030a1a0b0031004034068440d0341d245407050380c00c003000014088802c0d4042030040300c0715030940310309228032800c0001341c400642d18181c0c080c4840100f4584c210880d00108070460301e03420018102e4035241d4403c02c403600260300c5140c15035524146942956005200e50341200d04d0701440515200100308040d00f2003e00c0d0203104800d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 738090890 1250 738089640 738089647
    0x200a11031501080c01080109020a090302121207080702120a050d0e041410081204060c0b07030b0d0503030a0501141c0311031b011d03070b1e0403020105090d0905010212 74
    0x15524140100425188004103512041da1590300c640d903144044e04070340740050f040c18000210f50b170710b0340700303440c00d1200c0359517034052080c5550208500403500070301101681c002c418824400c40680c1000b000030912600c041c0c0c2d00ca001d140100f00c4500b0207121010b9241e00141c04a8000600201c4c5d004445185802d280e10850048030100d00108a0080305d20700101c412424400b20141c82842c0c0c400b02c610704070480d50f0341020000202c46900942c4980800300310380801d5400020300303540ca59a80305090f85400a5030054880c00955005824103003514590000400e1021025050052502400c00d0000d40842c0c0310b81d0101003110014680170701d1040e2485110b00c00100361007180300310220601c110803680c4841c1c4062844102c2010241c28a64540c178104c08038044690000c2e1303188000b920a0007071401d2000c151503900107044000c01e2003d140c50302d103184000c00390b040d41a15020b14084c0c2c0c00010140351600a540c5412240311102c028800060070400082ea4001150b0f00c208a42d6035000740c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 738092140 1250 738090890 738090923
    0x306080606011101150807260d032d09020f1504030b150604060c1101020d0e04090c0504020c07051801080601170c0406121a10180b1305070f14030601051b060106080601200a 76
    0x201e001510320303003040c0c0c01c01032f800d03a04080c9116000400201d008490f182061400b400821109440d00c81c00b030f00000314103002c1000420030100d60240d11456401411100014510000c1c000b42d0085d00103901042400c0c65200c10302c81c4000b24210300001c00e0004154007a00210f01505070304041202901c61307501c40c058402002420701c024001020b011b8010354551004500e00703920384945024560051104040c1002088140300d00c4504070cc6000010305416400d080400d0000e40d9071000042c0701d4821026010029202c44c4201d200510040f03085c0ca0340c28180b0f2130300003800200029118140c5415a00340626040268031050071a00342007000000380d003110541802901e02c40c80c0207a8007408150403407110007010740003988100d0740e82c0c0d5401d406030020081921003c842d4500e46007104002e02c0084d0055000381d0041c441e90300d00c3e44900d103402c02054201c1e403030704e0320036000400014030080038000381c0d50b000320740028000084041c1c000e00e4000d01c007007956194161900a1b0201e04111540070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 738093390 1250 738092140 738092171
    0x18020904060902041805040b0718120309210210031503020901090902091b0301090b1206100f0902070203030706090305160f050d0306080606011101150807260d03 71
    0x604164000e003050201d956a0405840213400c5031048040410f4030080c0700385600f90501c68180309a45c08542020030780c03079035941140c02c40140d8281d0304000c000e40c0f5011980840780c011240043c1d120340c0c1c1e441d00803030400c80c07542d111590324900f50a06104000c400d00050380d824008000d52511440e00042510007555800103984541e807000c0e40040e200300c00410405000e400100c0c0950082c1c895010645400e000b50310f6083c20755081c503111040070b2005101070700340c0e90040500036a0080900d050202000c001904140064071008103030485080100220302d02a4010b80040c14510f8045003851526000709840307110f036100c01072220390394201200401d80681d0560300701c00881d0512000c901210718002c013480c0c0d81090305440c00d1098151000d83c0501c64022101550695800380030107456000041d134241c582d4203903400312075486548074100138500065010043c00101c004100c8a0724202070b66000c0400498014883c01003800c0c1c1113654100068004104c44071860300180d16990a039041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 738094640 1250 738093390 738093397
    0x3060b1011251a120601090621090204050a05040506090708121608130806010e130210020c03010203100f0b040602070512070302270f040309120224031f0f1802 70
    0x3c901e443c0180744502d003072542d040203032000121030410400141c69010055a0002a82c0308045c0040c0802c10540c14010081651000d0945894030218004042e640004c058800407509019010354460800c014000e003000001d4000275031401500000c1d04045030750380c8a24240b00f644005010008603201c40152a9041400301038010305220b80341c48075110301101005003489804901d108550000c10241c1940040d58003409100000000c40140c540c284041d2100860081095001d003022500e01901e0078001580300b451482c0e90002c03400c0c1041c03100120100e0355006001221300c14001030040b1900020444190f030703402c60700d0b840c6248056401078070f03203010754100a40001c0b56019150100403c07144580d280340406084800607030740d8401c0c0064042e001c40b40600044ca04080c20420036805a9002c06018000b9202d04941c1d00002ca48003505420b070341400ca0101b01c00020030230404210000035144121828000032818601443c00e0301401c1c040c000c00f41c2c9003140d0740c3c02d0f03000d450241d4101e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 738095890 1250 738094640 738094649
    0xf051e150a0f030317070201020a05041802070b040c090606030b06030f13080d060e0606091503070908120307030c090e0403050307030905010e0106090e0703022b0c03060b101125 78
    0x1519042c0e8a03450f0080200710550b000340100c0144001040c015130040c02591507440c0c4a940c0c141c1402d00d4802007889000001d0007040c811359080111401041c02c49130441e1140340074205441e1028901700d2035004450f404e5002c10205490080051300e96642c0030f00f165049052400035400c182c0b101d220000050501d05401400c200000036402d02d0445190000b90407070762054060181ca60b10502842054030800c10007591105c460703001383c0301000c909406503401c42c80038984250302d40d4540c4103580c41d2000f661000c005044000c410000000d9140c02150303020041b03440e16010552401402c0c28420740090130040c2800b0f8084005541d5901c43c0e4080d203000383e00302c070003840f4080155182c5e6000300038038040e0420309401c0c405030152203200064118101c17640940500385001c509035079070072411a40b440f0b803580010540c20300c40105644112400185008520001d41e03045030400b0007081d1030b000682e07076003400303d0340000c0c00d40e92001140c90f60203030038080b4280d641e101c1e041c00106040740550b0031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 738097140 1250 738095890 738095909
    0xc0b0a0e091305160503210f0403030207230a06030f112802011e0b0a0b030108070f0e0c1b0a0b0c0a020f01020909070f02070302130f051e150a 63
    0x104900c00c1080e002d40500e0600403002d07144600c4641e0b65800d0850b007036000305030309640724280c1003081001c20842a84c40c0000c0d0050b0604181042504000d50341c450341c4140d0059000c40400e011a55141c806040009021060000240c50310400300e800020588034040601d540c8002e106184846070704421203410b0b000c0d0b0b407203070744e615041c05400007010045a44440007400010845185005210f161205200c5003403041c801503036110303400040c1480c050180d41000705d00b07400059291401001c3c50103880c900d406410590708100c030104009105030701102090103980c0a111002510070200d40902d050002603034a503121030041c1c01c1c5400b001d488010100e1020104000401911a000e411030348100e82c00c0d00d070038028042659082c1c4c02200c0c006a07210002d5804a503c81d402589ca20180c4000703401561541645da4000031150704040300003103c86d90312a079506121802c07a11945520414141c00d8540d29010038802e262200d000400d0341b90515001202d0701c4a0343d5070801d0703c2004041010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 738098390 1250 738097140 738097159
    0x201170714191e05030a0b031905060132040b0402090a09020306030d03150521010c0504060e010f0c020f04090b15040c080906040f06020c0f0705030601080a0c0b0a0e 73
    0x11404501900b1100b0314000408a4003040318514511000c0624500c030360350f44a081d915403014240003400790580e0703c0c2d8540b0560704810014147c034a94491468055800f41c0f88543c0f40404064005a62002d108010030400025000603000b81901d5941b001094600280f0b41c80c0003800700f4001c1c440c00200b5603000f800c800300012a466503800a500c1400142c003a41c0b242c291004083e41a12498504078a648118030014010790034040a840001c4042c80550032182099402ca50300f150451180c040000c0c0000801344203560b004800611590000c0c81c10044c18100403c0040011030300d107100902c203001c1090340c2502c917507590f04180516904a0401c030b079075003000004c800c0c1500c00c12044500490505102d00c3c0120301654280c0e01c02ca414201901070341d9195070310207161800c03800048800701e500b484460348005003080141117440290340103020481c20305080501d0410305034001029940a8040a00010380750602c62088800c42c3e90500d0b01c0d245158001e40c1c90b20514003d85400c84481c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 738099640 1250 738098390 738098407
    0x302060706060312030b0a050405090a02130c0e010822050c060408100b0d0b07080a15060c0212060105362a031b0d14090102041406070201170714 64
    0x3644010101e81c07150308404807480c43d03100c1c2170b0240d82121080070391003848080c0030446802d050b080f1551000081c0161801440345d40d002038642e81440c200c0e401060354400120400c2a00300b00d42d030300360030b800342080c0c1c08600c5c001901e82e0950b080d4544680e01100c3c486500010004104191a0101001491036840c0c40d00d401c41c1d59515030140c0d044040306030a205800000b400d00e0100320310038540140c99440b943d41c0e11602039924010140a00103001d5071584054620605e514541c40548855130343d42008035010f004202203460410104005034004000410941d9152020000f0103110008400b020180d6100403848441c104c0c01403141805a1108110700904220425142c0055030150304106000303c215210307081c003040b190101000b9942002403440c10074440540382c00a00d003180415840700c4001d50045001c4113560391112690041000e000068118003036451440b01511030908081682c2c0000300764490703d62000800042c3c00003c10f1041e8400e080c04100741407843d07040d41e0740396200d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 738100890 1250 738099640 738099653
    0x7030e01020a05030f131d0c0a09050306010605070327050d08070501050106080105030712051509010f09051b01020c060d0c022a0a050301050402010804150204031b03110603010609061803020607 85
    0x50300d0201400181210081a045035110384030551610034540f40300c107580c0e01c3c20f581d2340e20341c8503103121003c1c04003203030000a5a503010030155028010aa6480743c0751015441d0103400c0480343c809525485030782c6a01206944000c004080456004962160001c01c050912623007038400c00c203020745103500742030012400c90b42002c0103a0481c2c50036001c554034195941e42c5982d541e0000400181640c2100c4c1000c1900084c801c145600000d004000040120900d940c4404480751a402195141c01c200030102001810011900385c80342c0a0024120320600301c0000785940c403481607640d502c207030b40e51018003106108014110a0811005100400c040400c00143c800e940804100d8403503484503002152504060041074080c69040e120120799407282d503100d2a60b00000304000c0502130b42031000201048101450b0301501c100780c5210300c9002e04508102002300401d4024900510040004000ea240d0145511044034813601c0c1c03038202684c8c2c03070f01c45083c2000c0a50000e0346c015004900507060060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 738102140 1250 738100890 738100897
    0x1b0a120e0a11031507140c0a0b06010e063603060925122d0f0210020a0302100b030118051f05010f0905041514010305010b011407030e01020a05030f 65
    0x40010041c1c51040004060741c44840b29401c80262105801042c917403070143c00c1c8040d80d0f080311007031030381800d01503d0340900d40b44409805076068102c8005015a55030000b04084840409840c4d141c1f500510f210106002c07030384a000c4130308080c0e45034028a0321294403080c00d000c10000130309407407284c02c00c0f020241d41d5055080807440040d103012281044403507591155000c881060385030780344010564907800f0f14407060b40c07a40c1e618805550380c0901c0e02e00e00315202d010428824801c80c0c3c824800b0740148010081115024015903104880702c2000c00d40010701c00101040000010415000400c01b1a0141c000f03121441c40c254102c0701130504020b00414551011101d0340b06003908124204080c030240c40d02803103049201000e0000c24032482c2c0341d80c2c00140d880760060041c08070300c1114450400c101ea224038400404010803500600410400f0700509400c5082460141000300a0b043d062050740f0440800909201450f850603203140d0003440400741e04c0d50801c0c10303a5100e660045880c0103d90 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 738103390 1250 738102140 738102143
    0x1020106150e28030b0f010e0105192402070504091a09010f021809070e13020d0209091305070801021206060309191118090307080a12060f060e091b0a120e0a 69
    0x203001000030303201d41040445641210008043c4c0208c692810f414040c2c190b164241c0450b00d03a61030980401ea00c00301c4000b0350400c9900c0f8600204d10b00020030024180003417508418420b60401e081c1c1170101d40c9060b8580c003180581010080e0584520152900411100c030031064818004180405204d00c0c0c20300f001040c1000b5200824665104141290004d900c2120150700c080001550712985107541d000c0e141032030140301c0c018981403180001484030030782141d084c1084881e1002d100308100041c000c51b00102901c100a5040080c0414148202000280031314040c52000c0001039000004010344a9003541c0d4203180c0c0070700d2015052202d1900008280341d030040f01110580300380d02c007041600078840c500310406581051003a90b2103100c1580000d070508100201c115480c00d412140d84601402042c82c10400041186011406050040600e508510074100c00c810054187d5881180c001c80c010081d8440d0b0303480c02e4004c4290342e0307402580241409c030f500c2c0100c060407a510000d007038842035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 738104640 1250 738103390 738103403
    0x403020105011802030610080621030d0e0303010e22081204020306070c02061602010e0907120b04060b0a0305040c0b160203070902090d0f02030309040e100b01020106150e2803 77
    0xe0709403850071004c2e031200f07450883c4c000b07403c299201c9030140300c0d06840d81c0000740149a80000310322884043c04201040c00e001c02540c000207009805040301c0c0c418114140c83c0640a14150761600101c00d864520007001341075505400600801c480102d030b451201615803010515842d044020b200102c44801180c00304c0c081c0c82188045503a4901032005600ba032540245403a2070414400180c41000072900b0b012130500c1075044e00782e000c41d13986400d4540309000e80d07510908040c1400071881c09940d261605240101c0c98440140031580446086400b00081d908001c0350645944c6040c0c110029543d204140301300c004500384100d0103c45508801840c02201100c0d4015250b0003039100700d1040345207030351380001003845d494001401c0c4000c1c40900c50004007642c4c103011055004c90700f500d291090300119034000340c0e2a8150242c07a88610000b0000030f1000b00703c080e041a00304845e48680703230309800a002e00c40010154540c1e802200c0a040210050201c070600d0b011074000406642e540801c0315031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 738105890 1250 738104640 738104669
    0x21030f03180c011d2403131a060d03050a021e07030201110102030c2203021f020f06040b151c061b140d0c1206150908151803040e040302010501 63
    0x661051507440c4c3c0c00050070207104410400c01041008200c1a801d0410a40c0001600c048460700504040c5100d03800340811079810b07480c1c0e80b92005207402d18a400724001c0f4644018094a80c8440c000789440c0747c0c2c1814000e80d81d5600318010307490b018074103296a880c02416101d035600c000002c10104200d038801e881d601245003e48d03202500781d000844041000701c10500800e2107580001c001000e001030711103000c40645880342c0101d03a15629001e42d1000302e5411010007240640c1c100b10707001d444502d00020b42694202a175400f504140b003d000c101c1420f1706021313480b102da541c0c05035040d040040c0641c242c0014515146c44c40203003210496560b810f01031a0203011560740510010001911001030786840c1840641d0780200a0400048140030851040418102c2c212039101e90009070207000c1034900c05201d450401000c0c0301241c3c1110195410104030f09810f0354658028940020190b03640a000c5012491100e1443c050b540c8864008045141404107068065001505944488069401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 738107140 1250 738105890 738105913
    0x3121b0f030904150801050f1005010c02280e0901090318270209091311040e07140102030f03070e0102010c0f050a030b0604150302190e21030f0318 65
    0x115460028040303000c0390400c00c1180c100d443c003540f0800341c042240064007542e5444850003801c40c0c41c2220381c0c02e0342c0d80c00c030f00c24050780340c40490b540c0300240030034039140f4001e40e0154080381030311100218080e1a42c0d04904808000c15500903045c01400c90003560b9a80381c50440812030181c95070810030f40201e0004500460b210503039000d031900340e4400707100027a000d00c50300d0101c400701150460701c9d91500ea420700c40003142d43d40d0242643d00440c101c4450039003902c5981010300c3d41d00a240303d043e12a51a0045c030308220b482c040340c034100b11781d408194009006243d0005074114403840c408400e070700c0030010400015940010300800240800e81c020403050089401c15580d0300900780090010580a111402d40c1c14032039000ad404902000e0601402c0035551213401c0780e814000c002c124003103a00450303015003100c2078a40398107003c2c29a03c0c0c840740049070b040100f10b100c0112000103240c06101112142040000c02c1101c140020140400b540c0745007070303030108003088121800541d02e4052078070100d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 738108390 1250 738107140 738107143
    0x1140d093507030c030302040e090f16051810080a05060f0106020a08030c0c071505070512090f1c230c030d09120611030f0402011101020c060f0a02070203121b 70
    0x6100e80e00070100149016400d0320240e40f84c440116048081507003c20010400c0080e1007000707800707200c01c8001400b0a698001d105410148501c00700300407010440010003055031790101c605c5402000102030296616203a107401024182c0e908403c0d50351007aa0452405c00c800003407868862040c0040030071059880d501c0883e25996903403400340003500e051005c10000b800340c000038050304401d1000c4030301c5a6528a5402030a82100402134042500414103005100040c031001d94004403229031246058034413800a1102407820b00c16900503440e910001c081c0a41c41c4c9071035241150080117101030155008011807800c80760404801641c001d903060161542030000fa450281e400340d448021500d400d00b201d8500d415182034047e80d909031a0914a2840440c0d0230046004443e00c0b82c0c1c20105240030300015007080d143d501030500c1a032040041908425000c03504980110003a00c01e42080d446595200d0081e01613410043d6140c040e103030b2078186404680c00109241c400000419807250004600c42c0d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 738109640 1250 738108390 738108473
    0x20307050703030b04141006020c06030910020304080d0f0b040e1504030f02070902120603240f06012d03150e0112051204080d021002070201020c01140d09 68
    0x5901255080c440ca400083c0a60080b20340c640c0082d10006414100750081c490109007500c0100c107001d011301041c03140c26414861034010580039100f062440c20b0042e8819070f50a00d4035401d801e00e0b98007001280c204036000381241c280c2d403528141030108801020403500200156034040e8800ca140c103070780394030014010a9008042c0501c4108080c0c40d0f41c1d40d28283e0f500400500d0b404114024030b0800b02d00e10710544041c1c00351444d4509079074014904903042c9454801c0f1610021075014440804201c1c00d07011380c02c455404080003027040c45030385503540140d8001c9151811600e8a0711300c2d14006880038001ca00a8801d941295400c0c401865403580c0603d8003603150058401e0880c080c1c00610080c2885551401c40c43e100310120f034120220310503180000d412540048c02c01e078000301001583d5650410a0b8070020096980441c608592031340040e6407803110401c0c0c0382c14001150b220000140707501d003d4880405590b80700348940c10051904000010115100101106a01450703405a0b88450b415 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 738110890 1250 738109640 738109651
    0x4090f05070507020d24090c050a080604080c0a15020d0c08060f22090f3c05070305060712060f06051b03071e150b010207050103021c091b090203 64
    0x21185405444d400780110031119a0064407800c1441049140304090b200300c000c2640640c1c000054a50700a280001c00350007182d1110744246510030081c0b08000001c070b049500030b680711203020750b00d000e03401c401c0d802c109804201605880c4040440c1d003c82500390010060011401010409240b08810039170f07030440700b0740e900f54210032514061030450510612150740e61100f0880c0a611031b54440c1806d0a0341c111400c1203644030900000f00040098054600e03441c204103950150104111582040c9501d94209928658030300720503040d002d00400307004075000b450b009070075508903240800340075000160b4603500300d00c018500500000c0380d1501c049800142c800315641c8520f0701000503001e00c80851003070100d8408e03000800c40400001c01140100c2012102c9150b6005903411900301698001e0701d031100c0300307429410940008141c0c3c1e40440c0640a8540900780180c680c980e0f014402c4010720303003004001c1d106281902c0c02e000c0c013140c2100140d54400940003e44100d0f150031184042e400103903036 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 738112140 1250 738110890 738110897
    0x90501080d0201091205091c14060f06010e0405041104060b04140d05071a04121a090a0b04240501090515030d020613140a11010e01090e060d05120f04090f0507 70
    0x3022091710310440040556042c0100078a5501c0741280c11210200145001102c0000c40c0c0884030444803418003243e540800071036040c4005191190003e030561800d03a80c141e109907591800a81040003111141c90b4140b005001000a02e1703c072941074009038080e000d024408005d80380403049910f4000d000081e01507220000c2d009192a041c82c003c09030134011080b00038004103001c045542c010030107800580358000c0d41000003000d80c85440880700781000d884006644c11200d012004941210701d015000b581c00030300d8100500342e20b032242e4079151101ca0500005800c001c0000754040898000c45c0c003490b141c10560300c03640c03280310805940d0741201d580e80c405a0001c02c00580700c0c02c00c50034100310090103690644841da1420300d42c9810710307044405c1161020350303405400c6820b50303200300030120f88102803c101c1c402034145821000031100040c800c6c0d01c1440d01e08410000c109043c000602e00540700f103003180d118580c0e60101100c0d50040d01900e4840c514051b14078100c074045010301401130200d500c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 738113390 1250 738112140 738112163
    0x302150c0709051513020306090f1314032a0610030b01060c050c091e090102043203150108150c03010504020a1701091e0b010807050c01090c090501080d020109 70
    0x840c0b010f0840180810210301c64a100390080c2d440b11040b0751100e0003200f00060b5240351040801401d100050014040c1102c0c0b002000b6030002d54903550740d1303807a801c01210300b030061200d9005c40c40e5101d481015038040e16100700310100b40040e40075038584142c64a090384ea56075504a2003105924a61001800400e07645004021b1103009101000c0c2e210b00800c02c2c3d0b40c1c43d184010200d40c62100927140601e0343d044140c000c01034619640d0340c85801500140c000e600d040c1c9822400900d05981403d08c0d0162011210090200322400c80740c4c903002c51014007075601002d031008008519980921810b54580104400b400b41b00106a0703100d40710ba01c00c240c1d07050840c1d00703003001e100c001c1d08600280e206020143c3d5080d41241100d018482c020a110725000c50110b03058100800b40c04a400c00c024940c030f04003189241c4981c2c01002c0f00380d200007a460704c0c61310b80d4800b603c12030142c8017000d40a00600440d03103001c214580f01c1c1e00500d040c0d880d0402140d0b150a03040707204a08031421000090034103110316 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 738114640 1250 738113390 738113399
    0x303010e10050d0803010806090109050c060d020702030a0b070f0f020607050d0e0f0607090605040305030406030b1302070506041103210c0f12040602150c16020a1203090302150c07 79
    0x10352403940150300e03825003528054a400c04116025004030080d201e03004084010000e0080411a03264402804002072007140f08a0f510309079603c2c040590035105400201d500a990341a96040e182003a80003811610a80c2a90400510620341a1808400921084031211140b0b01903045885240b1545d4004d0030240c0e100707403046410b42c0106400c00e442d1034486001005031813040100100b8450600060704581c244004003521510182d8080300c2805401c1c081000464000f10a6408032800c038200450240702030b100265071490461135949c00c0c10b1001c1050b07014018000342003881684640060140852081c3c02c05541d030f090242201000e4411a901c103a400c0c003004082c040c0310702020100c42100100c60b00f102c1c20705020032078195540744041401c0000e90fa04119082da10003210540381858140841400c0442c4075941401e40e000c02d0030003504086454044c0c0c140700138442d11044c01c62400c66450007c0041c001d522059109034040d1070014203c40840f400c031401881c072400106000f6140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 738115890 1250 738114640 738114659
    0xb01051e070b0c180f130905011a0a0303050301050402090303070c081609090f06110c010c050306090f0c0a0522062019140120070510050402060706090213020d0e01060e0405030301 79
    0x617522080e4200140f075000301d1295130780340501480244504000724040030403070310250038030b41d9040c140b9115034200b403400c00101c0c1c4c004040380e055440940d005039403000e04c000400d1841c418003030014605061000c1c005180c41020440d07003a601c143d03258483c12155151441000d0302c030b403c0d5000e440c00706604001d0002a005a01c12a00600c0307010702681440206c3c0280360840d0f44540c242d00c0814800000c0042500d81100307a00d0b0301c28410100c020407410401019200e9024282d0300c2801e00200245480144969544940e80d05200880054080d500d80e0b400030950301c0c01220084694014541c2c0108120000c16200c10700c400c000c0c0c00b40700c0c18209840d05d800101600305044010355803006030300503c0101d8401080c035041d01c000015a00c0c40d00e171405924041c41d03820300302e4900c1e1401c0305020040e964501181d40381c54104101045442e401d000140041f215840c040102c01d10000300304108061507000880790076141c000070007a00e9030300c481c040c0841b68101d5000f051500204014858480c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 738117140 1250 738115890 738115909
    0xa1406070f141e160201020f0303040b0c0a050c06150102010e0c03030d110f040e040b0f0402090c0d0f05090c1918050403090b120a0b01050c0706030b01051e070b0c18 73
    0x641822043c9074003c02030b030070200d580000b0080f1552814165900b0655070100462403c4840101c02146146041d80340c40c0c80490020344800c40516001660b45400c0c0e21800548003030004046c1a2203060400000c030004003145880c07268095420405190003180c004502d00028500103005145000c80d102ca049008202c440114400810240400c84141d2480409007000e08580e40e0707401020706150400309080403004100003a000d01001c1000016100c01040d40c0d00580c0f4190226101e0341d000e503240c0d029040c0c40102100e410303d000d080100100380080d401c40451403c0d10111107101c42c030006200d403050180255036900900d82da1441082d00103501095201d4040e10708400b296845081c51000340c2e03c448807100d400e448581c00d100458203d07201d4151810001d08110349080658071070503403a40d1031441010107040c0c3d100107801c850303402942110340c00440512584800b40c5d100481038415042500183c80c80b0000e1740005880060740c0e0103d5000c4000d4441c40b1541c0b0108004014910a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 738118390 1250 738117140 738117157
    0x90b09060103051b0901030e100b01140a1b0309050d0f0b0c0a050304020f0f0306040b2706060f0102070503030d0504110402070302030d051902031315020310260a1406070f14 76
    0x5585041c0c8d05c4045800307020301c001554041d000410000d03a82000102418004061152110310400000301000e820200c18400c802c04100b051074a07211500301580c0041890b031147d40c010b1900041070040003000c1d0341091807641704203280940c1382c40d216400c0300c690044101c4200400d2040003c140940760040060104810081003008030031820030109061000540c2c00b00c0e11a5005018003810418402c80d4207920841250292409000801c0907940d40e800600b41c0d90141000b0740d504100c69100703001003005081c0103000c49a075403800c40030500c01440d048400307689845640c0c90404891820340200c0d030006806a0045042c0018103648100500014010548941c1120b11580349070340e0a0014610030305030001241d111407140c4c107154500c0300101c90f0700380040344100100004d00b2086c840e02401d039002c130750ba011029906081c101d102c1520410100c886442552001420040440c42c450b88620461054031704135200d404c8143d540400443d00c282c00700d142601c641044840f2080980fa101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 738119640 1250 738118390 738118397
    0xf031812160b07050f0c010921020a080307022b12180308070209090106051c24061e06051206040b0d080409060e090c0f1306090b09060103051b0901 65
    0x5a040307610801070044940c041014804082005000d00c00e05101d81d4440341c56a1018081030b1080c038000900d4861070340601c41080c81c09402d03940b0203001071203280316030a0303000d0841c243c040e8990102c00c2d9a5000050100c2c850b012036824815820307012811042480344401249043c0c07103066036907075600844a00c1d42010420300d4034550b080c00200740c80d1070b402036005400f540c2e80c60146005006121900500075582030f810410108081e80ba021404d00001504140104141c1200c0c42c202800351504002c481c00142a421200718800c20b07648400110383c000c254102c010002c4101c4140c2d0840c0500c00c60000ca1414000e4101340468448000d51200c4000c000280a110402c00141001000e0380700340c034030f04408141401a140755104100107844661480c02d00751400e0b00d9902e90b074000d0816441e01a44903a504240c3e1a2166038800703509805003075007030183d00c3e2540c99140003410500c403086c1c410340031040030960a50282c400c0358000c40710010881801d00707000382045500d07031108a045040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 738120890 1250 738119640 738119653
    0x4031205071b1706100b0d02220801051308190306120614010602070506041e120f030207060509100c030e040906141506030f0411100e030f031812 64
    0x2211a0340001c0020b03501c82d50b204a20341000c112841d070150100d010010b65104030f044c01108414861080e04661441c14013666545507040200040c1c051101c1ca4404007490005030801042d22070087e0083c0c40018000700055603800c00c01860307401d420340016040d018100328514040c102003003041505209c0d4100800c22941d190500c41e40400302c00020744840e95141e0040400c040c611006034010049440201465414580020313414860340c4a1010907444450f802e5908a84211414000300b0424010003c100800d080140d01c0d2900170302e007103005000c0c0700c0300810b04e00e0043c1c00350341800c2805081c0c603813a4140c110003502e1030760301504140d061118504d00415a90307694001c0d0355156104d100c0108207a481601418090380014100c0841c09421a044103180e0302d07000c0540e80e002c440c00c0022600740d200e03070816a10345144500100d80014180c00d8048100303070012282c4880d28010744c2101d0700340220140310b83e12409010204000c2486148201d21545000c44030b8007811121907060702d81 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 738122140 1250 738120890 738120893
    0x3021911071505030901060e090334080409061e0e07020f06070207060305010510021510030f11090a0e0316060b060d0e0d05030103150e0c09150f04110403120507 71
    0x2c850030708842e540000d80010400c01c0c050820b0083c2c1004180011421226003802d4a40c0da8490190508001516a8050111100020400c01000e80442601030340403150028105940d603070f441030103100e24882c2440800200d00403800c2d40f01651212200e036800c0064107003105141749000140000003184a0045d0b081d440c49021700c0130390300511a6400a001581c5440740250a4400590045100c0c006c00701d0480d00301900481c410004204100040c3c0c01680c400d020b422455035103070401303071000c43c0070400307182003000c20243d070b1140b001c0c211000038060791050162030949001c0465203a0359003003030104000011220101101c070512800002c11640b4104000c2101a000002d070000b4558071510401c1090200780502004406a07140c80c81c030355811a101c1c030598649a84200344420307030f221101c1e4035003502480300082400000f00804441d0400040c0484083c0034804014400c4081d24241d034024940b602c84d605030b0384204130160741800d10316100c00c110350100f01c54800a21200308200d10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 738123390 1250 738122140 738122159
    0x9040905010e010f1a0409170a180801020d1404050d0e0a18020301030b06010c031d1522050406140f041e02040801150323010e0d0e100302191107 64
    0x341e6035541000020600860711400d080b0425010b4130302d010318580416540408c0720f51b003202000210b80390a4507503489500108803044090504400384c828101c083c0442e43c0035064004110010b4040010321003a02c248584a000f82405d8400404a900640f000c8168600410010348101402400a40156a60a005d68011022507060500d103603000005000700320200c5080303904094286020386480c0a83d903409481410724940710a00e4084c034110080d00d80d0f0301e05003000d0202e40411115a2030300c0c0c0003490f0084081160010000003c80342001080e1030802b84268421603000e500111042c2508005102e030b42c2440001d51900252a1010034079110355400119031300f00404000142c0d0345180c08240341c00c65480c1c4900f101802c0b2054001c2020800001034140700c1055224000c242c6070b600100c0b1801806605030350b07002030086d85035240307005030401403034264103070213691003030030791410311003c03012441112410f400b0440c21107890000140300b0020403111048400494030060f4440c500c10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 738124640 1250 738123390 738123401
    0xa15052404051011070602030f0d0b241b032d07210206011217091306090c08010504061a031e01032a150e0303130602030408070b0f09040905010e01 65
    0x5020030400c00403030702002d04c10050840140740b184065030506090304118422031103914603200380d068842c0000c4145944403c0300d4950a0086451001480008101b04160380c00020412a10b41284000c00d001e03502e021045846e0001e0710340c90341007018500c0011410800340100c41c02c646400920540002803a182441d49010304802d103004050404203600a00e002c40513004241c0410a865003100060502c400e901b64201c0c2102e03200f070700c3c0e40760400894014502c00010600c20303401c0c000006401c0030550f20000c04100d0030303078920820781c2c0c03928203002c103440d16440f5800c45800250700c20029241c03240041c5410100582c0c00724401170101400c942180d1003a0800da500e6407242241d4401a0009080320255155003101d44004919004807080a881b0768401d8800f1300503030b20b045000300e0742e09104513000c2040c401012001d02c1e0b10360030300035600d4001b405030307081a205034038000c145d00302c4000030f031107007800580710551070b02d0806024403010f0804c0040c126025921b0301499000e600c020f00a1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 738125890 1250 738124640 738124669
    0xc05150601021e1f051807050a0b03063d0305390325020c010207050402160c0b0a020c0a0e070c080708190e0a06120e03130605030a1505240405 63
    0x811603060006d950b0038540300b600352010060340030f14810482600c03001c1116045a01a000791600d9903900c4010641d00f03403500d00c081d25804042d41c240d541518070b420321502055030788481d040307021110300416400c88030203481c2900c8031411007039180b000d03d803032a0000c1014000007003030390030168500700718180b03641090311010900007540c01000c16400923003a152003140510303c000c0600c2c031807880020f51681094003c040c011600050b00c1c0122a00c0600c3c5025200c0d4484605940c0c00c1c0c2d588003980994010054000c010302419140003007a14080c51b0900544130708451401981d00c1d407440c00d031041c0b002400101c603c00002d0041c500801c2102c0040e011241e841c85040481003005840100141c036103003252446000944800e00095500840d0b01082c01c040481c001000040f4562951542c02011500304441002c04004610780b64400003841c000d0640060901400300034042011030904980144d40d0003103160078081701f0328003030390400038002000f84a601c0e1605841d000030440c9401c06151 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 738127140 1250 738125890 738125953
    0x804021e03030a0c0219051003111918090e060708040f060e0a050c01090b0405060d140c07060b060906120a090c41060d0609020a0c05150601021e 64
    0x9925065040606c1d00418140f1241d9020221500302800190441e1006088001700b6a40d00d40c00c0b191403141c40c0446e40c0c110070850b807440c2c1c01d80c0181801081c2c8070307030480100071482c3d41034000152001c1e18001c0c071485010410181034941c2e0307040421540340ca0003e03c2604d012000c142c03c6008076003a0f201d988092a0450083d00a0300c0710b0f418000c0c074242881590714100a20030310100100c01c080310540b026260104c460716a82c020500c07401c800742041c032901a9241d94407900344003100302d86800901c105485241d050240c0c10420003042494010556856000700b010020b011116585c0882242d100c10202800203154800b611005020380d5550403140150300264413005038891301c21444040c1c02d5501c440070390600c002100001003a02858011401804007090307800603800b1036041000507100003802151500381c007841c000c0140b0110002034500703008110380d581c1c0780114549a24811601a00100950707144d139040041d01d50181c0081441902661600c01001400290031200b080400030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 738128390 1250 738127140 738127157
    0x4050f04061407020c12030c0105090d0810080c04020a110a06020a0e0a050d0b10080f0705010f030b0108010612020403020303160b060a08100507031404050d110309010804021e03030a 80
    0x2400310115518800621111002e01041041e0698001040e40402d542035504044843c0342c0d142141c514000c00702200155401d103002c01c030b4802c80018080c2c1c0b8645407503031500740741d45440000740c1c0382510600401c180c03504a400c080c031103410140c008001c00d00840c074040c03281421009142d07040058000d0100c800c00d40004001c113001e5405541c0c13603048a822100d03040ca4500e0180019004400440c006250f0042c0030700040c001c00076480c6060041543c3c01c2514403110039201c0f4240ca030500780c02a58003050f20710440407202e500c24400c1e102c0020041c0c440c0d172400d9080090603151410521041c6a100e5020440070005031814005041d00240d00c069104100e091072503c94100c0d04018a02070046610f66403c120810000410110715040c14500040d103445121044000e80880c0c0c0c4030001700c0811b00148010000006a03a064406483d6103d855005d07241c19181d8983c4a9000e10304d0010740c0e01c0d0082005403070304000404541c40c24440d522000020320001c03030b0031034000e00b0040303011440c1c2e01d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 738129496 1106 738128390 738128393
    0xa0f061103070e1302040b161104110909090303071b030306120f14060601090b220f030507050901030f030e01031e0c090803030709031b0504050f04 65
    0x12240340d40d4a150150001d0302400b44900020300031101190078094407141d501c2075405032810088068580221300c001a0080019901d0036158484010211401c035691441001030b5401203095036070b10ba00d40e880420140180040483c402070b0802c108100d21194002101e48040013108240150b940082c20128020045031300401e103c0020f4080510600102030759002d00244903d40c114105078022880d951100300541d1454003044084800380718003117820001e0700140c0c01074503d556103011440840e00b00007010368420040020721480038000e200d4140410006040140d840c0744035945543c1d590800503148001c0503003001500301d4180c0340c0e03038880c0d0410303452006149000e00d612200b60801c20300800e508460f0b0000704080c0a0005039040d00802600e100e040383e078899114491454075030350303048c2d44011200050000035400c0401d8546d141d104050041520307040000c01c51909 = true := by decide +kernel

theorem cover : BRFrame.Cov 737949640 738129496 := by
  have h0 := BRFrame.cov_init 737949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 737949640 ≤ n) (h2 : n < 738129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
