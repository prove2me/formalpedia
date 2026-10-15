-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3848
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:51:50.189033+00:00
-- url     : https://prove2.me/submissions/4b511236-c981-411d-9491-0b63b61ebf7c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 691906474 ≤ n < 692086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 691907724 1250 691906474 691906487
    0x30106050c120f030f09010e19050316030504030c240c1a0709090b0909030a050c1f0c11011806020a050706020f09010813120c0305210708090d 63
    0x420042080008001d0200d510500040b00300780c20002c2c225507126140075074424641c000344c4212101032000030204030b055a05100d08135010550034080c1c640e10091031240c1e004030b0306002059545000402641a82c0500040a8401d1902c6a124541c403141941080c808600701608142c00112055000200d0b280f0002e039002c12503a018a48689213071060b1400700c0c1d0403000b014803013170410340e86801c1c0401c40d50840000e000395980008200a6020703498100300c40e104007601c03d0f00f0682c10801c034011400e4400d800070002e9040e1002120114040781e87c80c42c0483c000c0e2120381c142680e41c4c80e219403201d60301c84100c0c88014441030003030120f60042190102030401101d4001d211541c00030b0126991030090301610081c1d904000b0031500c400100501904990205485c50300141c005400115070075240c5900080890308070000605076040410301f59040d10f0810802d90501c0814000b0032480b03654450215110f540c43c0040110504041d5000342c206403000c1c1c03458400750004801101250303402003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 691908974 1250 691907724 691907729
    0x507230a06020a020603070c05010c120f0c1706150403030f090f080d11120a02010b03101104030807030c0209090a020a3609020a0b07030905010302070809060c011526010507050301 79
    0x11401540da072031f4690705580c24144410002c1c060350808035030901d056005682c120220b40d01400500139829015803010484218020708008a04040d045490104070036200c1584107102a1244905440000c42000c160300a54401c400181c1d22500005103e9481743ea010003d1149100c14481d0f10b060203039254440c800991882c04100c210352408030702d51800c1000c002d000140080039562800901c2c8000d0103040b00c815414041c2c4500c010b4901e46030740b903119900c00b1482c120041810a41150b40714031a03540810400d40c00c2002506d0040c0242c3e80c0c00309414001c1f201d4030b006000e0b0010a1042c40098201c81e800300902c0020310103044e071203441c0445130300e117040c681e4050001d1048060034980020300e00c600000c1c1d00f01200c100003184a044442c02044800d002e500d9140c0c01c15503400044050307119a01700100050307003d119070199420080080d05d85020080d0022a460f50341e40040703865401150302c100c0c0b072200103e12840051500800c0209254004c00091002d4944040090294841071 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 691910224 1250 691908974 691908979
    0x180c0d0b0709051f020f0c0f060703020114071119020f010c0203070b070804033809190605011a1215060f0f0315190302090c070507230a06020a02 64
    0xc80c00180480e1051540030040c1500500c07091144081d2142c005522008404550140c8591560507030700d02c00010340010052402082c6502c010168410f000345078028041c01c800351742d01c801c44c3d400ca00302c030361380c80500c10001070b82c1e8a01d42c10780f410344851401d07410300c5840e001d8111103195030002d030719500902c001000003070900900760441440401d207011000d5000040e1000007003040c1041004900051046034056903003080340d00e030912080c4400c040c030409c0ca008800a81083c4401c4003101e0398080307a22500010a075102600150765060044068540480c1c00995078001804905841d404441c0c4d4054070040d03450130b00c5081e072200c0c030780860040d000b5200383d518906a0401a61150121044800807016181e110400c44c1c440d140250000e0f91080c1d04022069108005418401035130002c1c0300c0031f0003191414501d140c09105e0781c008050a462003480041010300301040b010427582c4014210500702c04005801407136241800c81964038242e1007044100020031200d9800100080b036241c04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 691911474 1250 691910224 691910243
    0xa0201030b030c060301120b10150c0311030c0a0c08030a0e041a03030a030f0b01080c07120504080d020f07050a08060c21010e0711060903041e09090b180c0d 69
    0x1c040000386800051200581e10200000000c0f440314400605195018451050f0841c0c585652600e502403400a02881c400031042c8504039031007901c1b603c082d0b8100c80c003c0c240158141c402c09102c0c3d085a00003004a0fc040e0300c036885041c10054501e00d10001080200f0285040800c2c04a000b80082d01103c1d034039200d69141c41c5aa0400c00368241c099601d0500202140e6441e448504007038040d00c0e0030039580c1c0301149400d600b6a0a0750050340400d2103042c08000039803030314055030303550140110041c0e60070080050074400450f80020400c11540407142c030341c00604101e2500001c1c0c40c036008550b00420300440621804100035400000c0309030300000a05901511800f9803003c0071480308002c00c00200329400079000103104003010b181a400307000941d031a0340301c032819000b001c1e64030b5400b503a00345901d40c002c000400800f065844200c1c6592640320704003080e141d8892804041d40c2c003520080e40c60715014020700c106540200f20000d40c002080010301000210301c0c0005c0c681c50310010026211080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 691912724 1250 691911474 691911491
    0x10828020c0f0d0917010b0105090d030201110a0306080c0609060f0a260712050412110c0d0b06010206130305090927030c100203041e030c0602040b0307140702030a020103 75
    0x2014000035002070450001c0743c4586001c024000d240b80100e00c180442d02114284a4107400b5040c01000c80682d81a1161450058100c0510010641019046c0c046568805c0704041e0100c4003002001e4820480d5004a851801c0080c0c040c00e08545080c1c5da031040c0c50400080599480b03400581e403603044580803450f00e807041840d090b188101d100e2400c0c4d04040301ca00c400c509180c50301d21014041c50041e80e50342c0c018410910700c081180d80580740541429941c403024520f4600c509103240240002070140c03403549201e20081600000d4900c002c4130084212000c0200350f5a040103469407080302c040d260015410592400303060761142a9800340104074840010384603140d03100905030100c807512820303044c0102000e011501d03030b080014680c000b80281101c03131096034140c1c001d690140703401000030040607144000b64500c0c207614a400b1402d0204c0d1844010204410b0b2021300014822010f440f580c0c1e180044005026449401d030300c81d4020428000b00d405600d0000d41f1072404c540c2030030002042c03103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 691913974 1250 691912724 691912747
    0xf2202090a020f040801020a05270a1502030904020c01060311010f0f0f0c0210020a03030b040b130b1507030206010819030203030f2703180603010612050c0910080601082802 76
    0x10594100350178030760000a020920030b9002005000070080f012080480c2c89440c1c54840030042c90076141a405500400140721a00d164424141459120300480c1c4c502062900410141d80086000e400d907070355a50010001d0002030034200342a002c0919060341a42c04031345016000f00f1a40545408001c0c140030010a0349024482e0703202c003140c000745440c6503a41c1044000350380e103a4104049000a041c00200c89103404c0c240141002486d0003881e5540400f076180c0800000c03d0808507a036880a080190001500701e00b6005001c1c860095001e04019810010042d283c40000c00306c52901e41040c800b1900030950100c1600d80081c12050304c03500645401c83e240381003e9803414085080d421610400304031043c0000280410b40100303540c4201c6100003400c01806010910800012560612414015000507803005d0341c40380400008500b010140800301c0d46000c0c501d8800c001140c0800203014696070400c0354030b9809a40d003054031031016043e18804007644800211424004d402040301c0382441c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 691915224 1250 691913974 691913977
    0x30f0a09020913030e04020306060d0e070b040b040f0503190f030c0b01150801050f09061306030602070f021309050d0f020f0610150201050105010f080606070b0f2202090a020f 77
    0x1580040101c540d505041d03000008007a082d03c41200441e4003a51001d02e203041ca4003d0300d2042400070005030030110396406a80107000d100711110064000e0000108180b0104030280c0007401c41d4400444e00d56052040041c0c40c20303a2904664440d6000502106000140e000100039159114050880003155072078181c800c81d0044800900300c100c8000040750090214101c8080d015095440c1070040e640c4805000c2c2044140c02c1040c1c021404e03800007505d83c280031b41c25804400100000044d01d0365261100d500302c0e0041e400441c1c060344c2a89541c4250720344950348810084c0c02a10811503400c090b503441d60303540d0406e1030b03285c01d00402c00440039515009000d902500b00b04a0240c41461074052a42034400c4d641d270084a4041e030341c10364005c250a10520529040c0d42d010b0b1940c40c0300308000d000c181c90501e4001c180990000080180800207000a10880d018000d180300a400764241000d184030720b41e0744403540c0700c5900000d00c1c1640c05a684c4d145c109400c0650404010790f51040f000d241a000d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 691916474 1250 691915224 691915241
    0x150b03010b1e0109240318470106120209060705070e16020c0118030212150c1e0c0a1a0f01150203030402041509061413020906030f0a 59
    0x4040c40800045103030140b450078840b090303803032140540d19400105990080c2240300308880009051940c4014080d5210b0ba045024511100101d15113950360030178038401003d441c6c45044548003510000c034003800c6140741d0b01150a2041d4404280c1d4a65850b09648140714031020044408281554000254100d0700c0307588014116581e034075540c0c01d03d69a182010721131075040728104000103084059003001120405820350240c04054200c01c01150301c040390f1072000c8a81d00c0042c1e00040140e0b1000c0126615000c02405001e60b2000100342c160f902c2e000400c46c00559400700804840740c4498021900091480d45406445000c055012450182d03d5100103180d03500d1100410405044a00320301e00c1401048041c0c10541c2e2100c80c01000c0c040d19160341d901690060020400614080d080656038036424849010000d903221800300595a055000a0314130441c0c40780b00c2918101407444c800d90100804055182448650100c0d9540c80003c100c42c994070031005c003054900710540c0042d2035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 691917724 1250 691916474 691916479
    0x14031f0b060d0608120a05070f050705220b010f0f140d0e0703061107030e091f06030c0905090717041b06050c06060d0c0614040e090304050102100207150b03010b 71
    0x86070200a010078005040c41d0050104d284a480b07124407031059010102c0315200400e41e80e850038402d1070b54402c0d0544200603c11141c0c0c0c0203211001c1043d8454940309103100025400c210181201c20200e9000c447e00c000e1160704002403a504d01c0c610755000074003111200e403d172034894104800000306c0343d403c0c003440380100140c81c14512025850000000c550059902444003002621180070103494644542240100030a0500003051110302c0e0000986078000c2c4115401c01c04041c182042c400c0691040d0084404aa81c4000c01c05010f54482e0306603002e80340640f0603004506140c880642040b81c02c507015036440200c840014200600711400c5800da85d45600d00051030394503007034040c08540004111008610410001030513a2030198030f103001d41500720010761611400e200d8116201d00c2c814070010101d0004000020b010360032010480e01c90001d403c0516211030030000024280303441c2420750420706005002c0b280100d05114001034000c05109000644500700314086400344c11480301c60756 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 691918974 1250 691917724 691917727
    0x110d0b0a06211b2a051207110901152c1005040e01090501031419080f0912030d20180f0405040605060f04060305190c080f07080714031f0b06 62
    0x82c01d00d4020702c4040c10061149415140303607005454104c064480c421300648541d014a103070000729500c0d1300051047d00c0c01a6145506841d000007c070b04811001c0c2d00141482c1e1700344500512265205691561869000103001d0060044207280342c1c4041041c0340580c45410300c7c015001001b4003078800c8800529030750041a01d50b603912425100200001d02c025034401030351088808441c040422100c400c0100c42c401c00840c420181c9030740c40359420080d01421004802c100110059032145000c4401c42c1c11a001140e50703010f06240c0d0b8084e500c0b070300010020312100e00e005905240c07032903054400c14919800d03d085001203150004250b010710f41c86040e0000d10305018081032081a0300107900c901c405131440200c0c59540d10034401183d88503c40906290409007400b4401c040c960f801804490050031000c1d15640c41d01080ca003098140b080c4d81d2155801684100640803050140070000c0165991103c441c0040c000401e407100300c944a003200083c9904c8075000c00b503e15501c264005c0d10080c040700d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 691920224 1250 691918974 691919021
    0x1f030506070801090f060302060a230408100b01091511030706050901020a020d1805010507061d150105010c0f06050a240e0c03040f120210110d0b0a0621 67
    0x42d100d20b03020302402d09154103140d0501d6081800d0301440003142d034007800207858003e0b1880e00b00c601141e4103d140c1d01100050a41c0c040007031040001e040506141c2c4050300f00400045002c034100e9541c60304182c14000062000c200c6400450b0742030340b40d02198103100103180c3c40088004e0a601c180d01000748142e00e40014041d45220550290105107900c2d0202c800d8030420310b205981940c81c00f480884845120901480507500c900d01424000b4030441012644040a01d00130300180c0b00c4051a24655009520380304110f181160702c540105030a00b020b00120307130981c407825522508141d0161401d40c40c1c0001ca0543c0c08a50f20243c240014000c81541e007001c4c0f098035201050040c490044a60000d01c0807d10284405080300d01442e801030580054032501d82e502d418003d44503803a80309501800d8071000801425028a95070202038151569548030040030740070403260001d0090780503021804060005541020708000c084106204003030f43c01c00340340360040141c40010018500000703c1500c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 691921474 1250 691920224 691920227
    0xe090111070614061206070309020406030b13151a09250f02010c03020c0a020d031403040b011d09060f06031204030c0305060f1b070c1e0905090f061f03050607 70
    0x140390480440b4030320f02d40d0307111802005422021a80304814030f8100c00c0c042200c0600952050000718405040421107030390340d40381d84015210031500f905100300f9000001e420881d80c0e00e03900f02a44100791040081d1444423880c1c1c02d80c002c1c1c0c242210300544140d4003051010020400240000c4000c4800c661a002030b05002485900c071000c06401540c01c001140340d103a070003402a03641c8030380c1000082c52460310320780812001d488110000d500b807003c2007820b140d1402808005500c968083d8805003030651501e14800881c1c0320008020001200d41c400f4000c881401003025900040d2007031000da070545511001a007841c00c5400c0d00c0c041c0d1440040d0000c1001001880d800450340074405440841d81e0b400800040280f08590340843d4522070040b0f0002d041018024202450284007107024454503404016010350014900039651801044100022082406650307440080f034000340001c00d0001410565400c4040c102d800c60a502e140071000c2c2c1603a550f0070700001d540102c12a240c60814800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 691922724 1250 691921474 691921481
    0x903061a0103051806040f03032a120e06190e011d0d0e03030f0d0209090a09120525170a0906020601050102060f011707080d05040f0e09070e0901110706 67
    0x9000340420306240003d002c41c4000543d000090ba03d9001178031140e5940d560b020701e06446404101c05059640f0460600361108820100440c600c04900f409181d00e04e100180071580a100000303080d60074401340c49901c40000c40d803c1e410cc000304001c0400c82071107030301e5040641580e0405030260340c0381041c01486040954040c14508600105a40d108442c848040780d100c1020384005405520030070a01c2ca904a02da802441c0340c4100301c900600700016600001c0c0b101d00b054500c01c044a4441100c4801d11058201448480499091651810200d000030142c43d041010340b088030200800c4640050101c1d8000740300740d074a078541080b507560000001c007a1404000b4055040184902e40000c2515400021000e00500b143d04080360640c0c80c0800103d08034403150241080d900032510001b6030040c0030001c03440e944005031202034480307090000c000c003001c540d50b02c000074040f1140180031600801185003020f6802d90201001c403070761003540e810302402548032226841040019908280b100d69070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 691923974 1250 691922724 691922771
    0x42d0201030e0706080c03090705030d0f020f07140d08071a09060903040e0c0306210304080c090103020d0f08120405010b0a060f02100c0e090a020c06011a19090306 72
    0x7241007080c03600300c00039035654030700e140522408030394090049607402030284060b65211044a04940119803600046420852a0b028800109803100000300c1c01c2d503010702201d20f980706a9802002901c4c45c00301026140842082c200740155080300e04402846100307400c80e041260442220030404a0310203020f043c450048540b4a501d00902021880561002c0201c42c1102e03c1e1140c0c0140783e0701c2d50000c0c54200c0d0300c060301e10f91740400d48000485c01075144280c091319546c485070281d61141d01c1c02c50b2480c20002c0c00d10807588100700507801800103a4401c00e55100351a040202242500c01c0c40c504803540340303d10000071000c03141070000c01c400c200701500400128501681c0e030800c10b80d9500000d45007468405d40010158010107003246084127541c2c8980001c1c0c01c2868951061750b89800482c009c50815078260f9070164000420b0250848100400c1c0c1c01000380e00940d0300d809000030700c0d450307250051408810042c80c0754020901401e1040e0301c0180511342041007000080d44601599071381c0c001c0781 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 691925224 1250 691923974 691923977
    0x20106031a04050d02061b0f0d0f0c08090c01080c071a16030c030c050d0504080d0c1805030718021309240608060a090504170309150a15050405042d0201 67
    0x103c2004c2c201e00c040358150142049221a841d8047c2003000c96150f81c02100c0c005d255140e051150b0180c150042c041e003c10f84458210000f10407904400003040c4900062224616a10164203140c00d40d900c13039451940080c4407442252691b80614105c001100700b00192100c42501c40b0510101104c642803003410804151000c109c40c02411000381c0a44208040f108003003a02840302007071881480c0c110503440b44c818090a494002d0203480300c0102c61140c100400000c100f00c84c64105084550b44420242030120002c00c0c145103805040301c0c0d00401d01003440070840c0c0101e0030220030a20400c0c4400505025041480410080003d001c205c040c00c02c007008a250040c2c0d00020a1801801c0c05401083c000e0106185507081c1000d9101a140146c012101320003a0344a0111017071907103010310b00582c8440040c005828014440c02c030b03130420280152030883c0c60240e41c04caa20000301d4510f02250300c169404030300c0390fa5a0410300441d0300c0c1074140d0091490503d0400c04040c00a02d001c0081354400d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 691926474 1250 691925224 691925233
    0x1005070201050c03010302060a171f0e061521010306050a180c1502070b0403051c020303070206160c0203011401052b0f021f1e18060f020106031a0405 66
    0x940008078240c1d001035402c00e01c444000c01c0107001600b800d4005001c07046046c00d2001c8000e17070403841c0c07204815003160340001d842c00c40103020880c550768203e40401400b20b81c1074504c1c2c6003821000078940600c1042520407200000038236050092000580071400f000d061a841c4081da524100003010b04000c86484101602e0101d4003400d034841200b100c01130315000310071043d00074244030714800300b80106910001984200d40e0005405081d55008101552281c0d01519550780071800da42800d258680a00080d5041881000a1301c0da00050555002c1105081c4107a00c0c801443d09a450f804501d0313019416500b0102000240340714414a107041b550161501644402008001d15200080c44100440d0044060007180071801c0b021401c200030b07000414982d4002845d454103101c8501852402e40480c00e003042c45021924002c900d18402600d60400c50f554040018408038814110b0081c10140088403800300821807003540104043c40d407006028180c0010009080d070880c0d801c45080b11140714 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 691927724 1250 691926474 691926481
    0xb2a0303040c080a0b0a0c09090f0b010e010912110d060507110d050a021b0f0a0906031b030819140705011e060e010e070c021e0f120307030c0c0f03051005 68
    0xd0000701e200c14140c1002480140d5100c2c1b54050001d441d0070381c1d4150400621040105458074144a8004016680800018454a00743c00076000c081280096414004031a1003000100b100607881c1640301c1d40001c42c2450f07000380c000000c21000c0d1080700505040c2c03800e410009202e800054444481042c2c008035070126801b800f040700d803403140306409401078010352080351040054441010b101070300145107140e4004444045905180c440e07000e0042240c4965041040c4581d00c0549220310760001c02242d000c508540b5900c02034030446440b1040380f84295044010503208178207901070480c1d24940c00e40d403581181801c5001c1c0c03e480c500c0d982d141c521a0090103040e2020b2203541d044942d00c0c0340e50402c607860003460103e1910001c2501c001e00c024403614500603511500711581c0c5050b031170700110b10a0503540901409200d44039145000340c0340e402003d2900d02e0000f095030841503041c9010980c1c1c0c1c0b410300d8081c00070109a40b01c12100e00d61081c000c0104680072820444000c240740b020409a40c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 691928974 1250 691927724 691927739
    0x50301020a0f08040c030f0305180a1508070c0605091b0402090109170c0306070906031a0312070c03120306080f0115060503060301022101080f0a020306010b2a0303040c 74
    0x319030000d032070109012001c1401e00500800801d076102d1700880c208008180d0380d85410316480074441085000441c0022210a440000c041e120910305040e2007039141e00741007840c56649031005204c024207104000c00080c41c260310a803a48140c980e07100000707200d03e040a01c032465940ea07082c03d420061001108961200b801c00f44207503039001034160745a03484140f034100c1e4210701b0358404015000ea4003d03051030348016102004035a01640301c80c0c0d90040000d2404100508942e07190b60110391900f03141c1c25090741c0e1350380040c07002e501603002c904490b5500d03085c0c6000880705d809603100603c40e22156054114094040d840300d030403929101c05681d0b40c00c0c0a01545401c0341c2d40003842840121440c002403040a10400180d6801000030700014540056400349038810035824058501200c043c60060040e10414051448040704400044c48029280d5001a40712001401009141c01d0080b41c5507400c041440d91f480191804604c42c1542380000501554681e4421541580c0d0327858071110014440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 691930224 1250 691928974 691928977
    0x6050d1103061305090a050d0e041a0d080d0e0f0f010b090f0f0402010e131e0204060e091003021005072006030613201306080c07060c1206090f0605030102 68
    0xd51005019106100e0f00d03a002d10001d02d0060881205449030b0440100064000c1181e41e0941d4569210501044110b104000036610b865403001412f51074101c002c10a6100d041c840603250351700c01c2c00340f516604460686001005035013040689032040007098021403101081e06405450007800912620603120203020307130b028059600c050761000c0c0000060381200151590b981043c81490003203c404640d5001541180c05013a21030805940c50f40c00040d554080003103c003210807009030542c1401d18009002d00420120f1a00901651400300007400f404500400c0101560340107200807071002032010001c00980103100100c0d80304200c9a440e02e005660158081c85000780100068910350300c14045c130050304000101000c44d1900c0d0080507403040e40318040c1544000880c40501e803141d0b080c46134500c5030301e030076804003040c07000c04014440c403280858100c603040342d001140411ba0086080044030381d02880e031040a4440e24103070000c141380752543c01045d4801da14101c18040d4903244d40401d802c0717 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 691931474 1250 691930224 691930231
    0x10e0c03070c080f070b0109020c0c0f060414030a1202100501060201142e15080f010825150302070312060e2d04060e07120c05150c0706050d1103 64
    0xb0404145080001554000042c01401a0a4005030811605946020703450000b070304102d00098001c5804054541e040184070140360080302d07005c42100036031b804a03035a8401ca008404c103a440c45152002107860402a20a9003540520340300e4000490210003034031401c08007204174005090900014040b4030500544402c034003244603000481d2503c01c28140c1b001d184500c29a0800000e10454141802c22161000240355060150600500c1e401700108031060080858050581c3d0300300501001c032000824403d0161424071341c555540c04540b04518075042c90b4456501e071a0a418011a8980d0680141800600c0394654201454980400d4402d4a055010313070988280c00c503001888802c141c60307001c80906464541c0c541c5550f01911204002042214191021601d40c40341d00d88082c42004498003d1000b44034a80e4a0615641c0f280c1c4d40302070324407031a881034045018941c003420400c4220303598980c0c160216a2490303643e91010b0001d8101d0500d640b41c5925107414201c82022820840f4030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 691932724 1250 691931474 691931477
    0x50603042d02210a050106080607091e03120516030905010e1210050604020708070f020a17061906120b1602010e0c0d030e150c0610030f0f020f06070b010e0c0307 71
    0x480c0e0003000d02c11003c4020020242040780705902840011840a204800c0984070700d0014100728070307190f00054600e0707606038010303111640f1410a12030408074410480e416640d00c81e5030762988244841c000c84141c001c01c3c40d8507030365001005c0d54008146d040754a041c101c030001e880c3c0c4400d030400a02000f8080c1021040d801c0d0a0b004010700c5103072100d00342c0c0580d0f80400700800050405036940c6030104250072500e000c0300d01210300c4c0202d2055240c00e081c150300030010034035034548800b88410700c55181d48015200e500903160311100d940b40b60350b01d03401c2000544a600010180e80080b400c1494400f1010b90300309030300f4000d44c07903420981071041c001d400103821243c00a1903116404001c2c450540549241a400c02527403001ca01c0c80303580d8171703021180c6070034030342c40a1a02c925000f590320742000303000303020120300320303003058081000038998524200240d0300080c00381298155400450f1030a2800d0544a0780300700300107040c0e810840e1403030395070741070380e0040001c80d903130740c0d510030226001d8171090704c00c0030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 691933974 1250 691932724 691932739
    0x1020c1210050702030d06182d0c03020909043e060903100203190b0d0b01120c08030a2703030206010b130b070305120702010605150c07050603042d02 66
    0x1440c81c41c1c00881c0c01c10641d10460703203000003e003100011207510303402003600c0703c407484103007000300030075010343d04894000038440d03001170040c03c20155503880703901092603c43e51204030a01542d8017a5054640c00d19003d042c0036905d2801e450151140000700000310f0301d110505600040d0b85c0c820348000c81406800c42c0b601c1c1e00e458074140c10000305800c40e030343c19a41846100490000c025080c009180181c00071081880c1e010302010081c81924220f460340e9001d5808904500301082c96801c0c50f50441d050b001c0c18050801480c14030400e03108040d0090209807000040b00141241e1000d2030541500c1c0722064603210644044505025a00501c40540140e0242005001030602900141280d010080c01c1e40c0341075540d95170802990300031010960100d600859100002c10b85406200e501036118402003115a08002c001403400c400b0740c142400b03807000800d801c030003580100484030141c00010221500d9241c0391501850543c1c0003d25041c500b644c495117003000185240306034852a60090000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 691935224 1250 691933974 691933993
    0x50d0c05030412061506020601211502180a140f030c0d0b07230307080f091002090109120807020f06030108300a0801090606020a0c0e072007030201020c12 68
    0x10100c08811800c4ea502a030341d03110001001810040d0400800294014150075854400c0596100d048030440380502c500328000c000005035046c14034281b40070031290060700e0700001d680b440c0e900003054001941000c500000420781130401014080e0840c3e048420031100e0b85040c0500da00d840c14403910913005900005207900017250045c503164022101d2918030601c03d20382c09607201d43e42c0449004c91a0490001c288070303031503504c80b885d6235209071041d05d40f401c0d9007010b01c100383c1d427050918044152254042040481c6031703c119000c00041c04002800300b0304000604054a080c2e01c4828124414000c03168507018904095003524109c0d580750300540030300704004841108664040b903610200c843c00d50280400d051000000d03010080e103542d200c003030543c1001c0d1294101c42107900194155031206800a0004446481910039544902103240080d02c80450070350320f20b400c100301c03980030050410104001e07006c00281f400c100d074001d0b030807524409810300921003408090402c041840e000034440 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 691936474 1250 691935224 691935239
    0xb0f090d05190e030303010e0a050a050f151504260606030601060e0f0607050606100e1003020d0e0d0224071b02120f0a140f060721060b07050d0c050304 67
    0x5000111502d0b0410620341d550301c200003415540241c101001d08a10041032000d0a07100703200d229840307410410200010f081c80700e45020103840007495001c00d00d18508000c6040c1d00e94240300d960a113030700c0d8400798885840345240fa14011000c0442400c400c5032014901413068000351050103030b40090043c0c52280d00780300c1d08031440c0114144264009015091541081c3c8908005106490281016020381e0400004110030385d200450076204006841c180041260744140511001da01107007001039403480302c020382c000034114004627000103004202040ca0078980100c3e031050134101c61604014140360310312112501c03006c262505000039088981800d032a203404080401c616000070640714a040c0305108140ca49490000440da480d0012101d10301041341c0c49500300c40403004900038004c1407490003803003580d8000c01064201000700182e400001c01e90400185185101c002c0d500b40300550322140014915032005400300e45510540175a18103040c8941180e00c25a54800e0107035240619200d036 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 691937724 1250 691936474 691936507
    0x3040e06090a02070507060804151514010225030b010e070906030b0d050d050c0f0102040b030c1e04060528020a020f01030b300a08030a091502070b0f090d05 69
    0x305240340d01308100c1340441c4c4104a540c00402d0b150f510700e80326107001c0c504440e074180e01d041c1340100d00342080a01000f200102300782c182030320620080382d440491b00c1c0d0300403441c041c1c01d50108500700540071520400f81c6841603810b001d0300c1c05020284070380d903a07030030412000300c50444149000038400c01090011901c207030800d000180c0d0051600c0000d0700c0c41c0d1210f81c20000c9c0900010042400009c4500e030b030103010300c0400108055a0000c504003461300201e90b4891100a02204810900080d845a40281c80c049400601c003011030f8107889540f900c102505607400b500c0f020307200080d01314414040302c10403c448046800154041c0100e2010b40e03003802512414440e4071414142c8480c2d400d005030300e030080c8401030000038017211400d1441e8003200020603060311001c000c058103c1c004c4000460f00400480750090b400312000a260030540c14040b2004082d40d83d00130682e8000501181803058092016001c1e02380c0d8a2081e195884800c0c800c3e503135203446240b000100d0020700003010203080149 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 691938974 1250 691937724 691937731
    0x308040807150608010c180902030a1b05070b010f061205071b05151e0c03060402191d0303270609030a0c0603110702060d0b041b0f02060903040e0609 66
    0x80c61141004002d40d280d035051454000c0718601295110020440c0741c00c240100000b100150505003007140e60351441c460000b03c60b0185240203500000800c00340034450380a207002d075081c00c8680d04c4010300500d00800a0740b00100c1607a61540c3c40700045604440a03400788116601c58441c80034a02031070305010080c0038010418424002e400696040041c0c5581043c0d400c0c0d44503401030b0101ca07000c10700082c94043c010b403440c041000456152480749032015855078003c499451fa241e100d03540c0100042c041e01c2400c11050140e01303443c00c81c2516681011130941c5400c00e1400c0c804803d02d2040c00d041e0b41c1c0c0908010320303a060030310b10141c0b0403e03080c20203006010b0001070203940c40c0140403804280740988000044506410311481000001e0b0f26200e2025000c10303800113945440d04c40e800046941c01840f801148041c0e0700d02c240407141d941e5500c21000c249000d511101c05006c03012000d000d50180d003200740c0160054200003440761201100700c2e410340340d070100d00c03490a03200d28050004901005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 691940224 1250 691938974 691938983
    0x90609100c0b0108030406020709050105030327030304140f101e112e2a02010207061a1008040206031807080a0c3b1e010e180609060103030804 63
    0x11011400440c88402e4000d020749040360046654602d00f980003494000554400074603207281c800144026540441200c4084510144215807087d402a00102c64504800c401c1d5041c800000c00041648442d0301500303900c081150f07038041e252840c1003406a000c6404074450006802000034048004107043d00050035540e03445e0030041583c880416500d00300b0b0018581c0001c03200069101032180d800d210443c0400e16404061010b582d40c484143c281d040004289283c0c18a451205861103100354151602e00343c10803800d20075004006240600020038000d4503000b81c080106484015025814035405158090b007050305e507550301c4d01c8201c64104800e507054200e010b2480f00045a40c003c22241c51191b00070b40d043d03c007441ca40040400d0341c83c003003802c007450305500c990380c8140040c4440f48a05a5021070300b00d40540e61f15041c0c5440c00c0142a1074440702c089130b140c00803406008240126200d155058410b04261000c4549690344103400c89642c10103500010042c0b00003440754189c1604503105 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 691941474 1250 691940224 691940237
    0xb0f041a04050a14040609061b0c03050d020c06160905030d0504031b150e030105150d03030515100503060301060f0b0304030f1b0f02130203090304270501180f0209060910 75
    0x715906600c040080e50281c1d06c590700c82500006000940c4105d88240e00d501c2d020b41c030381d864803a0014110302c0140002600340100070401003072008054045449203802c04c401c3c1d41c410319000c20642120100d81d010300001460201010495050001c0c00c0c2d0714988039505c0f441d041500d0750761010709130f100001c0f0b01ca01c0c400000d000018038400000903800c0400003031301d43c2d08003400901c0034542160310003820003d05002500312508142c072103a0450780c105800d03240c040380990300c40d002a0904040f10740c245401c0180b100003c0350855102024601541e021070003405800d513182031207400c40480d4042d295513410100003090000c0d000e041c44040e02d140c80c4c1019009001c0312000000715441000d41581d0464035a5900c00441c5060003100070310300700c103220850442c10020710b020760301e000384e001d000c890700d82e11075044114200c1518281180e112230744082c400c96840c2d1a404074004030710844644840d0603c040060703218070394001d6864502014090a0400d10704004020440d0009584541070020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 691942724 1250 691941474 691941491
    0x1202060906190b0d0c26010c0c0f0c1a0406030f050106050a0c05010b13020c1c02101e06080c09101a0f091008011406130e040c08010f0b0f041a04050a 66
    0x4c0c22840500280300c03078000840c1c1d515a603c51046c40915524080761164909099000001e41100c7c0e03080d10180c020240c24406591480d11902c41e501c2500011500040300c0c08613038586011000410031f41d80980d900f4002c4410701050002aa5800e005000100e513062040c0000320703204010051104ac000c07000803551100803c08203414180a00d03039050b03030a4000594000e5548100f0485e13401800b03d01015210703075200e40d002501e032003003480104203040d16100b402c01c000740c2c4045000d5025410450410a9664039100180e89076900042c07140100c50910000d020300f215a0450030071a1344030520b45010000c08810040164058040349006070b9040c004184680c645410005042c80780381c40d414000e50400e019640c56040b05010a40701d0001041528004110014404100c03002544038066a89942c58090060401500306407415807070403100c0f0b02040c075650044602c500058a810131303200710720414403043d601c7c04008101c3e4619003242502180c02c0c517030f00c50f0360302c01c00c0c160700042e1150 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 691943974 1250 691942724 691942733
    0x50c061e0f070201090510090b0f1b060f06090106141c14010e0a1a040f02090909010912052802010f020705100b0616060510030c031202060906190b0d 66
    0x1004018070316240000400c420701156000055100a00801c480c20780d000d00300c410000b02003100310300460f0310440340420310508421203441528081110a503112b903500c2c855440c1a60fa07880c00321141c0f1590550480460340070300303001029038141c880307595865540244a05440000f580f140c4000c42c3d207000302d00540c209014080c07242161003c00390400c40090352411624103642c04010b02000c40b100d181600300000310034180c2010708400ca05450100b1540070000c104002070103020015a00440350f00208400c100045d0322020989108620700f09a2541e008011500c0d0301403910b00d68514150807084102500007201d00d4681c1c03003128800417a003489103d4a110a07a04012000c40c0c031940030340c082d80700601c1c0f140034101c0400340980c0e49500340310b00c00181e64403150080802900480d942e10103e0415105106d007000a16040048004038545d60318080d408680200e42c150010b0050700301045a074100070030154094202104070080d03907203000c0c4201006081e003c40ca60b43c007200c40c484680014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 691945224 1250 691943974 691943977
    0x40b0a0203041a132604120501020403170406140a0e0919151809020d0b04110306040f0204051008071404060815060312211e16030c020109050c061e 65
    0x540c010248400441d03c03e01c1c011013408040c480390007401720881284070300d83d104102075a0894155203c01507121000e8100280284995080580f10087c081343c907600d1204003d00030001c030382140d60380c0f4a0310b0f42007c00182550140890590000b40f06584201c840d190030075040c0d8011000360720301e8401c1d0840741e04200c219500200074007060602c010080000300e4800d260301c004d050041c441841360401c140e00040441480700c400a01441c180408a028880c0c000440c0303903402e9016003224003904141c28426100701124100f02d1040e410200014608442d030801c4100f110140350050441c541448240c0080200c0443c081d07030480c0e03803184c0008241008201034605441e250403402c2c1e0300d003410018181018526418003110813410410384031900030b0720500507249000c0404886650700d803030114819503c10383c064a0740341524007003440b0004c504c11202407280c22058404100c0c4582c507050903403d80350041000707040e54210b80c7e040c50131400c00750020a84d0b102c0702450704008902c5140c1da030f0ba49 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 691946474 1250 691945224 691945231
    0x301020d0e0c01031401080304060f1b0b01030b1518070e0d12020c030a0309050f0f04020a030c1d0a030204050702150c0403030315151812081908040b0a0203041a 71
    0x650310440409000f940c15108039400c1002c1416040015814440388582d68441d034891481040354090490200c98490a1401103605002c107035407036881558186285103500c00c0c0416a20021540c002c1216103e49400070460003601504445150410400c00c00840c94002d003001c007848107007004403801da038035481302e070145070300c14030200c240d020000c50001d01e03048210031114001d41c0882e064401180d046901c180c110f80d81151142541348413003011918180c070803c1082d40007800401d0441c69a909900300ba040d00b25556070310141c40326035410190100c02070591854110008500a1001d81415080180d000d0b10a004480c8240c1e400e042d0071070060000c0b00c640c0580b5002090900805505000b00d80d0b030201801d0022981c1e500b002e24491229602c0a03860742800300741c400306100504907170211030007454146400301d80b9020b98146503000c3c1d4080c500c101c1c0440d1050342a1040d05003e00f10240c0502d40014071105e041e40c0300d001c1da000950000e8000d0f1a4180d040c0e40422441110290040c070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 691947724 1250 691946474 691946501
    0x3303060914040b0603060705180d0b04060222050a05041a030f030a1403071b0303110f13050a150c0809060a050c0d08010b0a030f0f0e030c070e0f0609060301020d 71
    0x1242c1c645824061182c0340c01a1001c0e01c20b400903400c0c4407070654004207031403500640411555190000000080c5440015480105042c0400003000140022580640902180c4407000416608440e054483d146031034054103501c02c0c6101c4040c8450304240d0300402000b00d0bc2203c8445408408001134607241c40b9610313456880d0720015001302590b07404100c81d44051880100c0b14210b0420440240c0240000e044000305814160500010301d80b20386c02841170404442d40051b038030480340c19800025408000340b644200c2e5109030010300c0341007a00400c4102c480e40d18a242031070315a807908607008810345005841009041c06070f04039990b03c00c00180244681916035540d84c941d480350803810709182c2c90707409042c00400401041200102030446005013207030300d00040d200c03940012040c010310510010200700b5251603d040ea03c03100020041503108000c0d021500502e640b4184081841011500c0c0440100d80c0c80c081206414a951501e800010050000d070400d141c14000c0e1b412150307903650180 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 691948974 1250 691947724 691947761
    0x1052b06060b0a09092901210507140705030406030203060316270c080118020c0106030516150c0305070c080102070606090606050702010507150b03100f050133030609 73
    0x60391507400030840c0d401844000c10500580c0781c111041002d9906950322100b41c21405211180b40d82e104100000f060360423a08585c2e68400ba40c070a000050000b100d40300f020039074183e4141075410b520b6058447d00ca600100a42c50f2500740b0300224041e410251060b50144200c0e8207982003603000554800c054080c6203030101d841c4000620301d20303400c0b424081d07603110355241503000115264060b056a06582203c10011780307481e0b000103000d000744905041c0e24002d519020f000f001300600401c1083c20700c406009000c40c0d044d00d8503a14044050f407581050f000c2410040840006070150004d0f11945000300c400d2800d0f03955445400b42a40e03c91241119943c1d82c501080c0981c0b80b180c03140d400548a0303860804d0401d0b14580c000f802038810840003500d0b49010b50444c0c01341071403070340015490f2500038041e1240c143c1041c000501070802415074441c680d090100108280040482c00401582030000ea01000381242c1e60303d440a2140904110803d0707110781d0040386a29140c0200740200c070315204c116 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 691950224 1250 691948974 691948987
    0x40b0d0e010b0105070827060a031e0c0206010e040318060f090e15060c0102090604180e010b010504090f06080105070908060c04050f06030903070b130201080f01052b06060b 76
    0x503401c482d140115241030000600c074030004140b00d01e0035180403590f0005a1701000848288294100002d4282c43c0d5102000080c440032465060700f200d008064208090006550641c000700d00792400c103494074005034480d0004100d0440d10b64622a0418040d0501200600003403490301d281000380d400800202c0c00b09034029518a9102c5103500041c001381c5082983e40c20500610b80d060b80140b100c16101d2400410402500d040c00e40c1103a51034440100b040e50b4441e81c42800c1c0010103c806101607041c0c0c50300c1003660000006010399061800140c4d0351078989414039608a0040504007041c0ca8116030b070f000d0110300e64400b44510350240d14651164000a490a03042c2807134031400074104403035407000303010802c004d481341410780031103030411200103480c7e684416142d480c0d4041c08a010b40442250300600000764249000d94030181d000b030b603808030969600e00b5074600e0800288282900049140c03a84d030b1400c040d01c00748200c1c0480f00780707a1380c00712000c5071030703140588119030007500704688005400d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 691951474 1250 691950224 691950251
    0xf0603070f051614160303021902030f0102031f0e090604120302210610020f07172401050a0501110c13090b0108031305220b042a0e0d0c12020303040b0d 67
    0x18203200002d00201901e442c6c1959802501d403101038022070803102071b066040c021903070b0a01803100700d040000021510384c03400b501c900c0d583c241c695841940490f0b440002080c0b550b200c400e42485500c00d20000d03c460b031500c0d9580071a00214050407800c2603401d12a03010418407501103500007460404c42101d0340d091804c00c01600c2013410101074250b511030007194005039004202c0310100d41c2c042d4810900c106c1c000d40294105041d41032000c440200b05400440700d9500c83c3d015038141c880566048901580320b200540c0d074032440701051007042d844070208a40d986002c0e054102c001b94018000b113491160359a810812150030b030001c0fa1290804075a179202c00c0e544400320402494221401072400803104905000f04240070800c0c44c069807180748a108640b40c43c0c105160a11100e40419903981d20b1500800d011710300007403114009101390070802803502d8601010044650002c0000703440900c0c25480c0740300d04082d91b00c200e0305400103100009404150700080c0c915400080000704d0080b028050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 691952724 1250 691951474 691951483
    0x503010b0316030b0924250503130c0906060302090906030a02060307051e0c010212010b180405060a080a0506090d23030907050a0b070203010b0f0603070f051614 71
    0x1a080c001c2e88084190b5a00c030310704950b4001229080541c0d00c0458503020301c407608290301c003503020305404c0f01308942c5c4144920fa405900d00c41c41c0a454801d020080781003003210180305814845c00061818004680c6014552142c0c1e40d01502c078100d8600306581d90007003003098424643c001e10200b540420203039143d06200702c040b640240210041c1803405810790008560f40030140114040101c0890f0074012404010300500c800c40003440c0c050740310448042060301035880b4042e03140b029200701c030000400d00341e2001a030340301d003902025103070180e01c80b001480b00400c4010101c60780078403c0c140000307000c00e0a2243c2c43c06180070308050b14052405c0a40c807460007803407400800c03c01c0340d11103511f425084003c1e01041096040c54505950340c0742d50b84418030f002c490340c2000e944540708190000c0d004c0805001422454400d50091080007100d50400880907007410619410800400001e0341161081040d85002a81424414100020300b003401c9500340d03980408850f52401d8890030303902d9003420803 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 691953974 1250 691952724 691952741
    0x10030b0c040b0307080712110a030c0810090e0312010618061110050621010609140903071e060513150b030a24090506070f02030a090b0a03020d050f01050301 69
    0x1030380e0a1600740b6041c010700e070600c0000c0180c41008403081c0400e00c114418181c11140940c03c0c0b00070700c01a1034028910708613a2280490b240824a840080300c2e10901036900d06e4402c50202848144161901e0030756401f0381210058803807580004c100c0b004401350400085e90203441d8641c0c4080f00c094011042c985d2405190704000180200048107100401000030703840d8000b20f0443c00444c071501d0f0390740802d0742010f2882c449858015907517041c0040080540c0300204039803040c00141301c4014451244120b07200b05803800c45990b0801c002035804903082c4003003690303110a854000f002c9840103032a10002c4400c150380c0c0383c0b00075680480b017405008140409070700e00700442c2800c0118500800020795140d042034002002c00307981091080301508003041c88494240342c40d00512402085147c410703141d1004035128800f241080b041c1040700d174400019103502c11449d45484040d1401e003150700082d50071800f00082055000c200070306501e8114000c16000c3c40030000125059410b00c07042609552941 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 691955224 1250 691953974 691953991
    0xa171b010e0a060b18071d04020a020c10032717210a02041d0402060903030d020702100c05030318010b0409030c02090a05091e1216120504140f1810030b 67
    0x4905d80b01c0f020094810303481d0421043d00f01400548490340601d00140400f24000394480c2c40815035000a580105424031942011202106203400c2c2040540450b00038a54910001002900c007241c1105007444401e9a80c1c003a4010039050b44c1c0d01075048850303910070040c4a44840708003400c0084075002d42a03c1d600011a44410741c100360600e0304d14006030320540711520140030040003040030354a40340c04a03401080c025040e43d40e100320010008010f90b000c1c080c128000c0118030350381020107105001c2c580003180d003c070295145460340c5825405200c2c013080d01e448603541e22036070607100d607840348144298140304c0c0e03c441d10305079050b00402c0b08001e0020400c01850b8102001c01943d9040410003a511040381e40810590112107030f420381c40c001181e50050000000015507012070014043c400b040f181c0708a0001d207040841440440d20340c021351050880c0a10325440400541c900580d52103c81e0102414900c5104420751031740c000403000380e03100d0205908500d424028032030255201580301614 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 691956474 1250 691955224 691955239
    0x7060305100e06010c0201030b030706030b1c02010e011d0619020d0206150d0312060308030103170a05030703050c090d1416030f0803070c060606020303011401020a171b010e0a060b 79
    0x40403446000480700902c0507041000b001e51700004c5a009a1080c3e10700030300030b0101c8541e0707503c0d080060002c1101e820101d229407105040015020080b4522100716981030751001100d15076000151540c00c0c0e942c000740082040031001c05060344036030010b400703d503030340c0002c50b40d1084a00b00003a0409a0032851f600454110344100407002c0ca56054140c00c140003641c0461134490507003411036004550340e10f4040c0345428045c0c000144582c02000d0350581e4010001d592142115100460461003041c01b4080891028400168014081e45c05140d0002521814501d0940720500003400b07420040d00032941e01225001e810b4402d003081001400728010102d480260300c1c00c40d01d0b19890480020401010310500000040101c1c0c41030360001d0455921140501c055a1520030194485c1c10034021501002604641001a90300c0000c46041e29500162a0084d8420203001b10205502405820181e070b0f0601440da0a801c030244601020002010041d100301d180c1031034504180c4080c1503469118109 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 691957724 1250 691956474 691956479
    0x7110306040b04081b0709020c0c060310031101110a0c03112710080304060e1318060e390315190b0d060506010e101b110a03050706030510 61
    0x501850b1590081c0e088042c240d100c00306408098204020300c007564100d40510000050160f1040e0060040c642c030b1941a600402c10803c00e01c00e00d40002c554402014103942c000704042407030164100d50000d018986500400d2003400071a1a0200d001402c44a9000c0424204140100212044d03400c440c100c031100140794808121900e00580030500376140f244c100040303100314281566501c010f207907002c141c0362100e0307498001401c24031940a481d4018034403001411050304051107182c2c2e400040031b03440e0841c0382c0070b0b480c4c0e840100901100486248187c3d004201703107524107415180543c081451407114082c280000b0b40c10003420300318440c000c3d484003920040f07240c0e092103030030340c000b440f00030240320201c03c0304d68803000c0c202080c403140c0c0161401029500b07018842e0040c0d8400c0d2400e80310348194900c010b040c00f2211000c1d10320603002500705680d4100392203040d084051402d0103003041ca0301d400c000000180d03076000268011a016130020104110503605030041651021003104600300051 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 691958974 1250 691957724 691957733
    0x1214190e0a081b0a08041a09060a080717010906050a0909112e120b0a140d21030207050f071d0703090c0602060612030414041503170711030604 63
    0x1004407000800e051808289a800001c40c00404000441c400089030880e4000b420301c1da22a5010f8020b00e00958004418000b482c0000400c50303070340080242c80c1c00e103082c0014200312041e55005c1c02100804c0b410b6210b401c00c4140c420911030180c4580780300000c01e0307442d00c410084211590350103144030504040b6020042030356a4826805140280c0d0b00c02210310a4401e20740720013180303501c41e42c071018444640e01c005540c495039000e40015002010020000b802080046460281c4038a921902c103821000001c0d04009406100c0c9a2003008040402202115400900d126082004000a60209a503400c0c040d00704003610515000d940501203003420030402c071050503198602c0d04081021000824000f49c800d5100d103640a4228010031315040c0c86200080d241d000544031148902d4240001c03501c2c0e0f803804000c60781102c4a0300021142143c1120500002d8084408141c003040380c030040000200f600000000d1000015400b210755a403070b00d150288070f078003030300080c18060303401a03003040b0009 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 691960224 1250 691958974 691958983
    0x170c04030f02060c120409051312030b0d05070e09070f0b0301090b01050712030903090803120112020f0307030c180905060a09022107090509010c09060f1214190e 71
    0x894200701491103100301800411414032400c1d64410591092612411441100300c001c2d10640e407042000340500d84480b8201c400d40c3c10328880103411908071610b1840c1c02c1d402640807504e500800703400e070301e8161607644a2508010b0260311841c4514141804c0181c200c105100e482c0140c99108501e9101d40c0c00d01c1d201c04020302050040c1d4204c60f60b1461052520380c02401561a40c5da8060215040001e41e24130050140034000b8003140030491644000c900d90701c0110540d890003100c1464404186e2908002034882c00d00d0303403030a0b0b0b0850350084d11a1680d460034002c0102441c0501001805589050640d20515600d107101c030102c14a0a40c40030005003001c0340c3c094101801d8103001c20411020700004518400a0303003842020701100305032040980b0702080420440d10084000c00103556910328032400d80b000020020000f505005041c00320a0040031a400c0c282d0081c0341400340b031041034401d0000c8601c1c00380012030450300e01d010442c0000464603450b98540c03031703840144140c00c44002c2060740e8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 691961474 1250 691960224 691960229
    0xf0a0515190905010f11070201030516021b0a0b0a0f0801080111030406050415020c0106060224040314120109020c0c03010b03060a270b10090c0207060f12050c0a170c04 74
    0x245840310442c0e01401030035007010040000000c07003000110401013030201c0c40c1d406003400300d000c40e00301000184031003035804c10b2100002c250f030040c180483d041a8041c00b80e00c03564440039404111076201088055010014000c0101503880343c0d41c2004041c0009858032005a100c40c6242c1e0520051180c3c0c86014230690b500640e00c00c0020034107817190701d403a20040c010000203500c400c0c4007155400e10f00405400050443d00d55400762074420181201103640c2a20200d241e40c1c11608200c04500040d110301e280d2040700703405004150a00c0b440262804036000b0a0307000b40c0d5150f4000c81d480d8038172401071040902184c000c40c000c006039180100400c1c1c962000400da08602075840141031040541c00c005006401058907800501d080c0034581050540740c00d54a100e001207400350b01007200c1195110b00790000c410741d002000c000e8a440021103448900c2d061500c10001301c4050b40b0001051030094a02800c102008a5100d034050b1000400e201000750360410031004010520040401b40d0044805 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 691962724 1250 691961474 691961521
    0xf0c010c09141503090a050f1f06080d051c230c1207050c030d05010308041a070512090d06050f070311180d060603050604060504060606050304030503061207080f0a0515 74
    0x484c1e5451842c0c884c01c011403d00301901c1c5000302481251214404102d0f40c01d11903000303151304007003440070200d841280c1d40c41c0112080395000040c1c2c0c2c10391f140507101800f4400208503613a1415541002d216061700c020342110780000d080c90880c0b9a0401441060651060100380709a06105002901603441381f8080c040d00180403002555540144050089810b8542103d105100340c0d41e4031315001d00c00340e120340b00314a6503c1505001290a0b14828100d0b041280c0020003054450408002d90080c0e5103e48400356004008007480400113909000d05882403034103421201c100d1801d09000f4051728034410212150361000c0000107002100c0c8600070095107c20303200400b501000e80b41420040031143c0002e000c603c2280108002c104141e080b1a11440c41000d00b4030480341d813110107075800d000a079001804a1010f000241043c10319014100404084404032230301940c1da07014540c1042c1036281020f04a410082d0340e030042c40800c102c942c0c040c582d0804d031201c040c90115110b0989140103a0180ca = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 691963974 1250 691962724 691962727
    0xf0f020a120203160b011a041d2d04030e01090515030402130204081f020310090209030705130b01020c0d0c0e090c1504090516120e01020f0c010c091415 67
    0xc07205200f042901d12083d035541d412210507009051000e060304091042c3ea95010403d0568800440c5940554088905031071311150419400014003000590081c00345042c498918801c500700503842c4003481082609070a03021450405090007825040051030850506c100340804129503140c07021902e00c14400c0e00300441e1070352540c0c03000800103014426a400081c1c000324000c2000c2e5030215400b12080a044401843c48401140300c10680c041203a202047c1b0f00d5404d42003105007056001000394000050a4449407038951001035805208000e1820380c05a071008004881d50301000903440036441191100c151015595600165101a0081c00809107070074020454100c0b040156054000000300b0b030b0711200864481e100d441e038000e480342c40d65203030521020500700d46a600c4145d120802c945c8c0c507400004203625850002d801e4039100103075250b5081248000d501c1098000c0e21138020041c00210721615040e40080c0176460070303000441441d00307001340d90405981d140754070007660303c9514642e07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 691965224 1250 691963974 691964003
    0x20c010b150d020d14150a08011a0609010302070f0503130b090d0f03110d081006030b1e03070504050c0304060b031513140f0a0501051f290414010f0f020a 68
    0x34264a20300c5902100c4a54140f01e50b1078020b000e0900002411f50716802c0c0f2941d601502400e0300d0b110201c500182c14181d0003116641031007802055210b1060501501d03081c400e60301c2d2020b940e1100d8040d00c00741c0001c1041c0c40400c40403144440203150b00c003001c80c1820f500000040850b1101200240040008a0100201801501e0b500007003903800050756901111894054038030a0100d0380c1c1c0811500030940890000d001c0e1040d840a03950251041c0303101014a14050071540d02c00c1b00301581031141038800038080d0b4550003490b1040504285181c0c40b401c2034034002003682c07141c0603c02c1c402d0700182c004181500e4040480c5034400e8903210340c05500344060601000b08210000e5114190054103955241818001041c2d0040391050000304460707912500c0940c3d81c00800c2a050200600c030304020404086030103071407145a101d100700640301080d0400920150351159201101c44c4c20890707a840308560700030102040815071400d100008402f0800c0003500e41094000061200100d080070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 691966474 1250 691965224 691965247
    0x1006060f09080c091b07060506030105061e0f0a0f0603060f061110110d14250512190c0f08131e05010902040e01092003070312030f090303020c010b150d02 68
    0x49114001c0344179001c0d581e44520300b0b01c0009040c0890b0010b001b9820000440d52506004151210b500e10700207035180b40c1c84c084403c0085c400b1410940340d0340b00c8404e01d0b01150320350881000d40e0042039691000038041d458039210303c200c0340f5194045411b114001489104c05440400c0200c40701101410005000740a0038105116005507100030724603a140c0428510124660484580102010740c090780c40c0d907600561800482c50400c4030900000c01c2402608040f0581701c0fa0990410340b44030b00c1d0300c102c0303101a442c507003120303a0310440c500042d020142d81e0f95001d4104024a400003200c3c41066249100c0362185004d0500403082d480b40b8010751420241885801e5002c0d94085074014014803000002c0656107000c0e00e40c100301a110600c510100700424252959043c09024018000d40059032541e100d110869641d25001c40a2585600803108031802031f101d0300390502d100380c400580350360741030400a00311116040882d001d40800c2c425034940702c8070041503034801c400010001d40d9441d0f84040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 691967724 1250 691966474 691966501
    0x5011e1509111e190309020405130809040b04060302030d09060908010507020a0f060209030d20031206040b150403050304032013111b0c03010c0203070807020415081006060f09080c09 80
    0x122051003054500c4c07405640c15082400301a0085800340035640700ca04c450020300000f1000185504400c1020f40f619040c41c0c8c00001c4000030080001680c036503242c001c20b080c14a801d04103000a460040c080c4441030b0041e84020107404014000c00552500c010065520840c5050140c61826031010b800100152a011140c40d960301070203680f01017110f440042c0945850a8403003401e024111104d10265074000240d4000308400700282007242c44980c140b00060400343c01c01074010000700d425141e928035400c01040150300c0340c001159510301e1030621102440e108440704010401524258640396a128071180310341c490500c1c0080c400b800d40760b41d6403c40c402c03d00c1801101400da81c150610100c007080034190810b00744c0081c031190807113400481c1c503889051001410114240f2500d0f0140c2004da0240d040e0043c060301030507105407140d21040c5000c6120503103551036511000c0a0101a610802c11040d04160b0f06101d21018106205151618400200e2900500c600e50000d17900d0b214030170 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 691968974 1250 691967724 691967737
    0xe16050910030818010e041a060c0109080307170a09020102030307180503161a070b0c07050705150309010b030c01090303140f0c15130b0106080405011e1509111e 71
    0x4100f0360f5448100c03074036403c1644d0003d0807030104103040031241480c10300d4003a0b03200b0381c0d40c0a040303000040c2a240030000550490f44034409103650b00c11a03040058151401140542100e0f11844542038064500f5012601e0080c11423a4550400100c100141d80020542c3e400034402e040c5103038100356102c00c0001c02c2455510442e4144640c0c8008540644408860310544041c007407070351540002050754030b00f20b104a2000920310782d02903002640240282024110262060040c0d4121503550070001d48030a0015a540280c101c0000034004d01c02000d20581685410603409050074000c4a4000b070101490780c4405000d02c00f01c4107140e000c610000c02101d84c5d001e000d030710107600d4118030345581c1c1e61112607a0f1105418000c0c1004100203a059901041055074001113440b0aa030030000100c4200401030003c0b0345940d258011032084034401032603c081401506d6001590600024503602d981840350f003c0e001c050b140414103e4000840400c440314030354003400c0008100140501c105c1180b1801 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 691970224 1250 691968974 691968983
    0x304020117010b09130b0d200a0905061009030b0c0c0f100c02070812041401020a0f05060613140106030504031709030306040c0f0c0209070306210203010e1605091003 73
    0x941c0042042d0980602402c4c0c1c11000383d40c002400381c8040703580f4085400411105502c00000030022002845241c94450708074030081d03120003e035039100e01050301c032243ca4022400b2251134208000090420300c403140f021074000e01d4403560705484c42e150510b1669000e0905503850b20000341c05001040108102205a0518002c4802c5e0310010a400c00080c411001c0a80050043c01000034044000040c00911751011080da1450079282052680208034504d1596056000d100e0041c004181003184003045a4002ca024050310701c0e00b40104140301070b03110f507640490b41c903100a0301f8003851103801e40c5041da0024140029207444074141913950020205491b503609205404111003041c0104c040c500840c0180c03402d12074042c4442e0256001d505490354036001402028103580035183c51048140c000501d030500048e190307124000c01c08050801d14401c007140f83c00a441c20110b003800d1094461410300c1070003420561400c000c1c42045040756102d0f02d84a0300100010a03003801c0d841403000021a0b11 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 691971474 1250 691970224 691970267
    0x15040b0301080309090105031f020318030c07050301060812070209040501020c030f19090b0a080c131d070c0b13030e060a080f0f16120605120a060e0a0b01060503040201 74
    0x542e81d0003580e039804603481d240103140d0100009404c1c10001107140d492008a094103103801a0704242c1c10003904028180b00200c0c07501303440302840c85014802031680c440d00740d02030621541890245030a40d4a658811902d0f60b0000c00e408a51000c588180d07182c2d46e504450040464959003050760180c000c614420501d40030015000d2403c40920009055500d070018411541400001080ea101c1c521413140751665102000000e8172507100c0c15200b58441880c0181608001d6228175038168010580c102c40c1143d038000d07002c03d2460318011300e00f9510281d54a040c0803003141c507903205208400081c003540040741003c00b0352020107024280381451003001030455902d42d200c030310f001005640141c40c40c40b100320210010414030940c2c041894821110800d0421a442607007900311842d50a466090420700c1c0da550021034582d0f03681c201e40041003034040007000b02041138240380007110904812002c40d42c0c030a0140600155421494904450704c9040c6203851355590b00050314094801d40004a840c0031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 691972724 1250 691971474 691971479
    0x181218031e010c031122032f060903120a020c0405040b01031e2111010e01021b010c0801051309060516030c09031112030c12030a14060a030215040b0301 67
    0x440d603103010001000400074000c01c0c861074400d07400c5481054556130005d004010480c0c101401d05c00d0f0030b00030050400003540881d130300d40300c2d64542c9000148100404203442010324204150000032020210119062440c14082000085d80c4200712231001a4103400410080311143c000d02001c9100040540203000740e00d0b1514144816120074001100c404021412014031000c9541005846a5001c1004400c1400c44035108007034460a000680030406550318402004001780645503600d40b103a0000b580703640075052400807920034148415460380c584a01080d0b40c0b9408101103045a81c00d4079450940b8440c1000318000d0003080074090030349814542813101d92070405071145036036102035508000307102703001c0c404403606080c91101601d074040ca01c0f116401c520b01042200090031000381241d1520451080c000d0070300d40001c1c134001c407a28000c0b0400c1000e264a01815015001d00c81103000c0703e02d0b00000003030340d030301c00c2c1d010180c00b8904540c2c807000d210341d000f170495014003a16512142c0342d40c1d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 691973974 1250 691972724 691972753
    0x16081807030515220206130909080714060c0f03190c080402101706090a09122601211b03080d060f180e1e100518121803 53
    0x2c0c0030090203103200101c20f00103502140403000310202107080c92510b166402e10744d000c1000345e0700185000b010001041c400000c1141e054400d0346082031145661740d40310001c508280035081640012004142c109004120850000b132080302c07030407a4420340140d22511621112160589403442900240d40f42c040c1c181c0d01c50b6080141644140d01c2100d4101440490300001c0314540044442c00a04240310404100306280850009910181c1c1c40400a0051603a440e545056102d9050081c0814812032221034007204000b5011056080800382c40310319407402c0fa684020403c3c0d40d00b10318681504e054a8003c109072000c1c2d9034161070241e802090b00c141c590404540302c2c0c0c0700880400d8250f10b028000200141404011021a11640e0303810381d5014080741c003440500400c8003102c0b203e0086000d03142d218082101036030000400c1000510000801781c5a03841183c40180c00b90651a0310000407440b0070600050040004101500a544075905807214961b00308040300929850f002d8841182c4808 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 691975224 1250 691973974 691973983
    0xb0a0e0a200d1a01050307081509011103042001020c1c0f08030a2702151308010f050106080603011a060d0f020f03160f020a080708070606060806030c09160818070305 73
    0x2c800301c000c0c1c00c0d43c990340c4000b0556640c14500c030ba00070980102c002810210750321046503620110307400000c1400d40502c074400c410b03070b0701c122001c549041c0c141a00f41c003d03400040b00020030140a0000300200b201d55000981980002d0382004982c42c000f200800400c03070a6201c03400340c02d07400202c4075200c0c1401c040740c00c0504200c428817008200b06181604c00440c4040001c0c0c20aa00603001c90901040711160030065845030b03050035100300c0c51140026001c1000d2240c040c10101c0600d0010349941403080080089a000c0c000610076810070420f25030741c1c0c105c0711034814414001c80d0195655440342c0340d02c074060002105030400b00f41c03020030b030381800800e1400118404c4803d800700810310b41c04c1140c01e4a00c03248900e02c003001a40300703402190000341c0607001005041c0c0542800c80c2080324698460060303c5541e084140085c00b0710003446501d0404000f44141341e00708032000105071410b030900d40102c40140f00c0000410101c08003040c83c01c5100d580036403801001405841500e6100d04020703984 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 691976474 1250 691975224 691975253
    0x161202060106021603021020030703020604060c0534050f0601050a17030a0503041a161b021e04020705071d0c04060804020d150f0501030b0a0e0a200d 66
    0x58091380307002402003004100e04030b058940c001c0c4480c100c900d20300c00407943e0b003000b4261070b84400c9400343c07180f40e080c3c0100050403007140319074000c02d114505403500d20291030b40014410184141848514801650002500031404201c0481011104807100344c1c084030700c82c260041d03c80d0054000328100e440d408204241681d1043d90500b01c1241e03129510490728400e1803205906820030311941800d01d1040b0001c0da0458083d003035400b80c00305e0074070318040c0340319041d2689030586000704200180035800c00280414282c103490704508c607100300d0300410f950300074a070006204003045680003010f40c0d0751541540d40607604582201e2407140c80300001c44003003413550140180c101991000548a8031540b048905aa00a6031001d90a0311207900340920520744060468402c3c02c1c0904200b00543d492051050120390b8510104095143d400c15210400b009040520901d0401c01c0700e500000e400500c4190142e4003228408510f082c0405401c0040d1070565114ac1c003d40d030b2410042449500f5112801 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 691977724 1250 691976474 691976477
    0x2060d060e180c10030507200d0315080706200d0906140403020d03080406060306020307050417030c06040816053a0e060d0b0901060507170f0f161202060106 69
    0x50780c14090380c52603520b503e841c080a40c0b2031210040c031304440f0301c070350000303a0408400d050000803444425410040d07654040350003095a07114503c01602d150381801440702003218020f149591900b0420150380316600c0f0b0040c00b081c01104000c0343e42d54080a030308182c841e00c1c41025686c00c40f4000b000141124450700c58400083d18001441a00050501c100d03422203030300070510075410b00316940c1920103400017001918666611100000491902d00040d07100e81455550b40382e490f420130748201c141000200b813030310b4254407d0228218404000a46039002500080600e40380d49440c1420310800c07110308401401c5020716140804ca8041d115240e18000d10000c0c09243c3e144150313060124035001a4081400050100b403000285040500041004d00e000c02408690300801c44040754030983c0030ba01004c00118002023400500c100f8a1440b8030040b40201c050f4901880c00e5800d100a0044800141d40018001000043ca1a41c070103000d561030780c0640e003500c280551210181d00d4540900c075800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 691978974 1250 691977724 691977751
    0x303080a060510030c032918091203040203160b1215090a1109180f090f030406050a0509180405010b01050702031515030604150b0111150402060d060e 66
    0x5010400c1402070609459000d0000300c00e20f4111242100504814502ca10900d540d0b141d81000045505080d011070080403440d0035503181c07000c0d00b800140300420144400113403e0400f0301000c0840482e02c516000b100c0d0813072a03165111070000074140009141641003054180d0b2001400b400c514026001c4e00e49101c1038400c1036500c600c15414981064000c09600254038000602c0600301c50f4040c081c103115020015062001001c00b05607088171490290028003070113803c101d001505ca80031030b44c0c410030340c2c000341c900300074901489070340d901036401800180000807030840c4460b40306900360f1781418002421000c0742048072010b05100c074002d0320103071507650038807060000550003a0100c40d03005901a00401a071030342162480c411150240c50f0051040e041c143c01d480a030380c10403045004601502c48001c5c007800e80741d850400c9400d650b542905100c07000380d0746500c6001c04035a1004c651321024070492030b59075510015007684503c1c5110508540341c02800308041e00d00c031810902c42c080c10415107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 691980224 1250 691978974 691978981
    0x7050a060e131d01022805070c2108040b070204110a0e0f04020405040c020d02010b09070f030e1c05070c05062a0c09040609061503201207060207030308 67
    0x844400484444140c0c210440c03008100078021039070b1090108181e0210140c3e003240c04411120300b6170f401150448030a0081058030b401c0d00b20055003a83c0204040d0070240d181c84115600d103110b4003142d226000c131030340059042d8000c181c01000000c0301e10f036121807082c1d903e0791190403441c5903400066080e4002ca00d0b190302425071040b4801150000812034540c2c4820009034420407004d05580b07115141c02c15024040017906440d140544083c600303494018104a48117030b40004e017103a1600072494400d940600c03c1c408243e0b00140c0305a64038441e031030301080660f40d0b001c503140360201c6001d811680e1a010607800c49299886005800414481c10b60b22031480d0703a5034104441402a258a0320341f408841412000c00444c0c00070315418880368100340c981d40f084200024029080481d015108241c50324104010850a0320030243c8501d801003040d500341e42182c5800307a10030070803c215070001a010a007103585598010446520140900482d6040e9071642d40003500d41440d440101d01091491010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 691981474 1250 691980224 691980227
    0x1603050f0706090504090303090206030406050f0a0507091203050c1209130203010b0409240e0f07050703140904090803100806090d120b0d320f1009080903070807050a06 74
    0x144070484810f6a2020941420281000300900d100a801c80034581c4d40e100240041e00c4010255205070700420b0300140516045807800c08159000700251038103840e007002c126495400c5222401520900c10b042415400c003031a0556040c8075a4000d03403054410503001601021443d002049001010b466100001d0191070004083e80400c1c0940c88010300140400e01a00c1d8103544142c13010014a03030000c0408001444421b24030704140c0000d141a01c05804005e055012541444d03042409480d109207805881c2e140248183c404000c0c2510307604000410b440c01d940d03039030030403007040e03030080d0325290b507410006005c5416110038401c81000b80610b00019551541c0030504104030111612100e602c0720b0002940001000c0302c2c0c1a1507031052085544001180d8048400215080030003100c400045145019180705855840c82504a60152410480074030b004180084e0741070020340d002c18009024078103403000e03014403908260144128500040c1c101e0000648070203e620030740342d1081070b5440380740 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 691982724 1250 691981474 691981483
    0x51c030f17040807081209060103050114010b031801060b0d02190309051c090e0c130f050105040b1b06040b041703100e1f0b180609030d201603050f 65
    0x1214061403840c400010040f0301d005008140c0345100d1039109180504079417859070305003070554850304a076200c00018400c1010034415907200002c5030040390307440d40c904040d400c21072000030032070303615407408141c48805441e007500034101030a0100b621986540c00d05603000029000206003c1401d00840301c6000403500030b1041d280c00381e412001421011100b41401341040300d41241c0d407020040c0c5c83d400040c071a030030301042e03e008009001d40d05698101c0402050f011480540000b24860035002c0c040110b83e801204581c01c030340c0c1c29a036168840c2400c0b8400310266600c215180090301604040000300030344c15034170600c0f42c2d00c5548500d41280405400c0f20241c041114030311a039442c4031a0600410f88541c8000c0da0081c00c0601a40d00e80321524007244009820764032420040e079000c1581207408003a002420344152007610540d0400c41a403000959444c41c01105d54184509101310030300002041a41c1d0b010900c80e0302c00c031101c20048054650803024140310643d81e07400354074407850030341c0340129 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 691983974 1250 691982724 691982747
    0x120c0b0a0c1b050703020315190605031c0314070e03120405150c0a020a08160501020c0607020f0d0605040f03030e010207030f20070e160504081510051c030f 69
    0x1541e0405407050614100308007020300d40140d4841c07042240000042e41c040003e8070f0015503100035800c00b800c1292814924401d40e82713113802690308014080c407064400040d07020454200d80e211044c001c09110080d0000e10960b600303101c0c5201048100100980c1021034409038442c05d50072954817142c541c1050050340101d0040a0348807206000c1c0d90200c00c101c40144c0504119502901d041603116800555034040a60004c07030980c0000c44030a2141000e8201000106000e00140440c20400c20008016200318200240b1074008510040d8240e00d44182d50030300d00707500031020801d50030142000c02c911452200c01b100040d0034071603851007880041c0259489181c5c180c03103402c081c101050b0142c4040c80d4084030b003001198a0060111440410400300303008000d40c0403d4007041c01d14141d1050070480519400007440803c00c0f080218800c0002c40001d0b01d40b20003d152551f891f101020382100c019030b404a90b00441c0035805068800351201000d034900c3c80382c1c4500d6481d4003140c10540e0404d4005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 691985224 1250 691983974 691983977
    0x3021807020312190903021005060a030506131e05030c01060f06121e020f090306060d03050a08091903030e060f01080705040209030102130e011518060f0c120c0b0a0c 73
    0x500c4205202c1244040682d045400c2c1300c40031000490689020045440041054005030700407178500d806850148100e42c4c002c502541e408a080d400c40e00c0746540e0714400744c00a5800e80c40d02541c00103105090727240c0c02d0384c0010301c240e26042c0c0000d42030032a540d0b040b15948040652805070300080d18110700007040115103503525a00c0d28003007003d620030010520f40e60286400003000d100c1c0045100c447c4000d040082c0859078032611062100e080c90b1400b5002841d481c051103032005000c012039000f4003a501410319502c1c2402c16691900c5004d41070981294162141c4152494114200741d01900300350300a4604c2000c941ca07550760717061104103400c42031040540d01d030070015040c0306506081d001041440c1014001510309541d80e903c403034082940c2d50001500311403800043c4415020340c0e044040c0c8800720700e00080d00d00324081240443c40800d100300d03070a220342036506604050081488010090700840200b019640003a0040c0900036821005c82e0031101440006121211070301c22000e1000382e9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 691986474 1250 691985224 691985227
    0x60112110a030c0b130b030f06211218010306062c0d0c050306090309131d0109050d090b13140d05030d0b2b030e04090602030a06030218070203 63
    0x564035111562941008115003149848802101081e0740c41d4152004106040e20907a441c040051036030005211074028a00422040050205242868098070b41128040354645266000044481c4020141130b084900b80c0c010b070a0f4000101844501031b0401503c601c80c4640107082c4c0d10011812105240124000314030113103100380c2c0c4c01e030007104000b440c00941d036000146d4603080070028407042c01c1030004072074076a2900da00b84410b040a01c5056040100310005500303041c0c0400014180d4240d44640b00883c40c2d0354048900442c070800f030720111408001c07008001e0b4034060b08116440b204501e203883c011a00e071042c0024241c80d01011101500c0305042c0070340c5820300b0302121020454403100c260340d021001541083c00f00f401030000780b0b40c11a40100000340964590140b01c0c0809000100c0307503083d409401010980d0380d44100d03110f45140c5c18540702c4240d0119800043c0200140309000c0d1201d44040f0802100d010b80f5400507040d83e00840e2079506c0f602004442200c1000116a1000160030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 691987724 1250 691986474 691986509
    0x403030b030d0801152001090515010609030b060a0b0c010905190b010e0a0b060c01060f0902041203200109030c0b09030304080d020d0b060a0c03030b060310180f0c020604050601080601 81
    0x342c41700444800d8005141c9100c406440901c090441d4101008400c03050b507440226808001c400c10454401005070f5018100c998074000000c8d0500c086440042c10a068200014109544039402e50018050980300b5680303400d182000c8034000c00002000f114a4803441e4403902c4800e03444100c1060044c2c1c002081c82c201d030700b0041d010b00240c6018000003a400d03141d00390542d09944840181c1a0741c154000000760031071802c5000d8144401e60f502003005c00f881044144081050740f40c5000e034107500340c1044e0b508a00701d1190742c1b180c400c8015a80d10194038009851040590117407003060b440340282c0c003440541d00c403c40340d542c0324401a2030041c10b241e41001a80c0d41c90501d0340203400380d400c80200c00181140d845000c07a60540c000b49000d000650611070580800d50140b1400c2040082501c402e400c615141900203040402030080c0c5896030500462180902e1594001e0f4411007072462090201400c60007010350345100a481c100c0c3d140c0900c400214000d000040c9050480c3d507400c10402c40141d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 691988974 1250 691987724 691987739
    0x4120f02040c0e034b010f09110409030e060414040b0316150e03010203070806091b0a030f060f030503030f0c0c0c1018060801091d0307080f070b040602030403030b030d0801 76
    0x207a010405050740360a0000305681c0c000032901c0e002c00e804c085040c50401440110305ca07003141ea44154060030685130200b40300210b0b203000d250090b00c42041d41d0005608003182002d442403402c4c0f650050b070013040018081144000003010171600e80042da401d00c4070102c0e071000c140e19407200345405020000c05100822005400c29007200343c66109042019a00c2980070101c2d003668411515400811032804c05c0c06802d007441c0f81416031011342e4500e49110000c90b922000040d02c01e1231b12440030103854400310541d0400b0740c2d00c1803005059001c07006c000340d5920318140e40c030f98208407040704514203030304000381d1804100c0080f070b010078002902038114500010100710390100b09644900c10030520010110392503000d1104000640010344594140d0340c502400d80081e20008882c99041c001d07001440b417602c0750004250342985030700c83c8109449140980701079805000311070010b00040d0aa0007030200f407106907401540500c2c042da43c01d1014a10030814142d0790107068064400050b007403801040b061 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 691990224 1250 691988974 691989013
    0x609170102120609041502030c070b01081f0b060405040603061b1e0302070807050d08040b011505030a2d0b190503060708250e03070e0f01060e010504120f02040c0e03 73
    0xd0302c81d860b120802c2920241d00f104a03003080b104c410009c00c2c00111401030109803150103006214490090200c41caa0010b450126a0f0654900c6101915170411040a81c2c840d8155070260002400810105a07641402d1014011403464400d2404060240300810381c8640010b00e500340240000320074007020194101c1c025408480c0a894002d8180861b00020740c003070100d082c101a80760341e00102410503060030402900306922403524a4440c07244170104039003100980fa40310310341e10300c0003a031a24100c0302040c441040e00918140d07081c0e20b442c00b081c580169400385202e14801d94001c061510740d03400e40e0f980702d840c5010307056040c0d11441c001010148515040e81d401007a0803078410700384100b00c0250002d105186da400012640c07850107101c01e41030401c491130040516804040c07917821b003c0d01d9280d0f00001030041c0410818841e10395580c507401481114014130400070301c012002094180002880d0300504102d1165040c00000200c00d44111045842d983c1e004010301860b20f440462036188 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 691991474 1250 691990224 691990231
    0x60603070f1407060204090e0d030b10030e070803131707050d060f1b030f05130c05010c0303200415090f05010509120601060309021f02030306090703150609170102120609 75
    0xb0400208020b03000a0b5090000e0001032183d00f070301080760712003900e1481c03d0114905030101018601130030744510f07946100d0f80c3c02956210b403c0c0001c280180c5030849041c103000380c10a10061000044e040a0306500c07481020840310089115440d8203c4085416164112032241d02c0d4004200c3d0340080124555500069095210500020382a0041013103c41e613a06400030402c0400ea0303c010b102481d920a0181a60007a07180ea005502c014299842000f1342c040c6d405510b040242c103822041c105402640120103c00000003208070f0000c3d2045000e01981c0503000c0c3c0d0031a91200c0920141d1140038209035010740741c3e0340c0c80e0038115a04000044409410540170141d124444500300d0101c0e842c00d008071307400782c0b03100c0e0b8001c00d0400e0207005000d85504503000e0700e602d5104052020081c3c0750f0200c03c3e070fa08914122141c20540d02c038544104c01505600c1044106440344d00d0300002d400d070300b044002d4101c807a4841003910410700044654201d0144880c0d0600001c000000140c0b145440503807280d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 691992724 1250 691991474 691991507
    0x6100306240906081e070e0c0c03070f02010e060a02120c01140109060f0e0f01030602091315091a01120b010c0507120c2301080411030a060212060603070f 68
    0x1001c0341c480301000941000360307101c0300303009980380c1c414800c0c82d100740441003d000d07003c440d80c420741e40d43c9840940c1d1107455110301c2e4440543d66000c07803c0c005034071045070222982e10b41220380310702d9141001840d901c450b000c1280400e0f40c8030589002e600f07225056861a11b401d40246c0030000c070030048001954400310300507905568402116112010746d0f0b8030796002c2c00741d0840000740d0314100f080000140440b5082000840418001c101d00c15089a1180b4103480c0c0c04600581c0b503004c80ea000c6903403205002041260941020325400080c44001c800200300c8a042c0e60905c280240c0d0383c4405000b82c00d10308042c0c00200c0245807a051900715410000b06403d0614003900610040e4481d40d051810279000070342460100c1c000c0c00706211040512304054986810f070210307200607071002c0010080542d18030a041c03009041c009014080c11094180da0560050203231071f1195070903e090f00080d40b2011412040185d15004212075007019000d50b0f11a03000381c7c03910b485910f90040e041d00e0b1400c00f0484000c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 691993974 1250 691992724 691992761
    0xb1e09060a1e090b01030209101d061b0d0e01020c0105030408040b0f0d0b040c0503180c120123010807050d06020415050c1005060f040f090203010e03040806010806100306 75
    0xe442d10100d600c80d4010b8a1000440075550915441805940a400d507041c10140180b114a920303a5400c010400e01c2c07142424002c0200341c2c0100a809407002040a0ac1e03800000810100f07511083c41000c0c035030101750001074031032a19061900340e5000600c002d5482c01a40325000401041d4061001140c119005481040c2010350702d69920b47c180e44a003940902c1c2070804641c0000d8140c00d0700070102c8130a030459003400700d1605a0720041903400300815010300c031115818a64006642031000450302540030f07000c20001090004024041c0c41c40048540031402034908400320b80c244c86040c54140c51410019240051411040000001c1c001d81d01340e40c255401c100c001005807056500c1c3c0d02c1d000c8681c8030342d5100c41e5024915410490382440210b81d0a00b0314080000c2035584140210b1710310030441d00000c802220741070413001000f000d18000e4241d0b20f00311340c0c0b03125094000094411910507008840c002c2c0e0f02c0e4154580c40e10025030343d219031512040401e000240264100164410000e4080e0303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 691995224 1250 691993974 691993979
    0x3060103090f050105010602010606080906330a09050106110102040302060306040507090e07020d2a06201204050c010c0305340c06080709080304032006040b09040b1e09060a 76
    0x10f0307007122003e03844800940e640f10000c02010350000002130740110b14a014046034940302364019000b168a4001303401d0020100480387d0015812803001c40c5494005e071201e000c10303490b001035000800080c0174410120342150034408000205008a0781aa5030140c941801c64580100740005884050409030610201c080085201c40074404e4039885210554002c080958640101802c002c8000d02c0320062400761900e0b5070700030148902c1404080b58003420014040d40c1c000072032020321103411104501040c00180404072a04c0d10746000c0d00481c0036809640da09440d606c0199005c500348440200400c03002d03c2424605c0c150380307100d50a805000203261402035442c0d0102c2c1d400740c0e040381c01140c04400040c024464076501c202195031094190520f040d0b202c2c28803280550380e028502c00100503800584d403c01213411001c2110950a40150400380c5807501c03030086000c55000b484049002c0c0e494101841c480b40307881d0380900310004201c46240c0c039500b950803d004002600030040781d0400800c1100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 691996474 1250 691995224 691995233
    0xf1104180504111504090f18031413080c04060b1c050a06050a090c0215190207060e01090507030b0903091518131d0a0308190e0a0f0218090303060103090f 68
    0x1059503503030104413180d0b91141401c12200c2200c006a600b4070200b4941000991441c001d03d034030304545501414010360903480c00101d08080d108403c00041d540411410008207118001070341112480105d80074002203444103d01d0200740105040080c100d42d0b2801c41d1280000c05503c016080080e00034003007003482d01c0b01c020884110301c660090f4086603960344c104410507410301100c1d001c881e0700310021a40341808a0103d81d501069080b0014032940021041c0812501c1e510045103e03460800a2286411900b0141e403a0f50b060320083d0351488000e4005092084040200c50b010440148500001c1c02200180c0322035400464030b05202d410404420992076032107500030b1003141641400403440110700200c101020401854a04142d84034000a9000903003085c1156409111007121861403840c15051101a01e0042e10130041c1c1d00405405070f0500940100c21110103000343c030112060080c9804280458400f00c4030160f140c0c0081c0049451580310f40c0002d40414016055205000340a80341c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 691997724 1250 691996474 691996489
    0x10170709060e040b060a03022409030f06060a081516230309071d0601030e070b04030b0f06030c010e040209010309080f04150c050c210d030f110418050411 68
    0x240084481d0b0a08101c200070010380640d074000020798a20030101e02d15400b0400e84002e20180000300c0001e000300000d04240074040e1041100002d0442d00d00d100482d410540b2050207650b500e000b881c010201142c1074200040f2413001c2150307070007104020340c2c0340b015804204600e40504010001101d20561041e4221940042910300ca051101e60b2402e054200525241d15a4865915a0402e0201c0300741c01140e140d40c2c0d5445203082c2800301e06e5031000d0010701e041000a4001c0b600140000c580442400180b211a903c1095011070b003c0035501c9150403d580c1e140302c001d96030b0000700100c01e509402d0500d80c015120f0844103040114068616580d074662903080b0300c010b074062540202d420840041201c0420510703088034100b944005003103403520f0b9205d00c200c1201c24020b502010362040d0f06503c0c0c0c00910104080701d4290707403c9044030b00d002809821242400703a89a414044001c0c100110340b0200c804590b0040c030f040111500783d4a5a03000741c0f0004000399000307040070100c03411588480c20b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 691998974 1250 691997724 691997729
    0x3030914060720120109030507021e090703050601080f01080c0409170a050d050106031e0e03250c05030f0a2a060c150603081b0a20090c031017070906 66
    0x701000811120405014200d00e013101000d400368180315051000c0798012044071485070f0140c034240c40004400451030300f07425658000c80d4010002c0703010410869855803006e4007808090341c64020304e44404078544d10401003805003d1300e41d00b025801102c50324056200801c12885061004221080610368150f150010a4000c0100e0400a4203850020302ca100e09800340c501c6090411070042c2000c5104252010710350022410b565911106041e1300003082507a140c0341d81b400d6001d5000ca0084014140c092001c50304842c800144003011910b40343c0070904911040d8244020054066a40c588441110700301d401c500d000080c8400c00302d80031036004c1c035500c05001c5544522240403042c4c54072886464a03881019021403400f0b1003800002d45041c1140d070002e01d0003020b0411346180070142410b048a000f401800d003000f20020f60161010340d8550181c204045403104520b64850030450784070311088bd003003058a640070109000b030301c0c1c100e907410a6810140b801c595006413030b40200012101181c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 692000224 1250 691998974 691999013
    0x309150504030201093003030915020d1a130b1908010903200c010507021801090506030c030c0a0626072015071b08031915030309140607 60
    0x1400c2c010341d40c01540c0580204800c0c801e400a56160407000402c121100104201c080e4071041c20000381482078000d038680070340180c0490307401286104184001d60044501e1640703e42410040082e4076404401500300300c0c4050501e004843c10034a0a43c002c1100c28000c0d0782c01518100c403000c94400d2041580081c010383e5000040b04262402c001c1c0410804e28642095040c0040c4a84000203010598041c0600e0030700b4050346802d118030000301d5040007003684441030307112200001480c80b1107810042c0540d80a07000d0700c5614800a05140d1030f5007264160710b070042040c00f0700f04442c92055140f01d280c6d00c2d901d54441c12042d21303520510200b01c025151480000d0003905400c000500c41e5400c00c5541c02c0c1d52005040c0c07a84024003406040d20010075a5040c03050b4290030b18052540501c090207015844813a0326602d00d00304142c2c85810044115083c0114030380615041000920a100d00590760192540340d0780900d0007a000c1c0014200d40c2c41079822120600180000031002c14442102c0c1022 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 692001474 1250 692000224 692000227
    0x303020d02070b16090f0b0f03103602040b090904030903081b01150509180304150206091603051f0f051302090916140303070c0b0301032001051603091505 68
    0x46907001000e20172503400c05100c1c2500901c0402000c2e00c0035044071402010046025200e0751484035001e0130300069440030b108034028025510303400c105d4000c81070041c80c012510000802202d01040d00320301850240c3c2d4010641000901c603e445d00380d82d699801817103413920484171030b00c07555900540d41180180c01a00e503050380c407560010100380a07580340d03282c0d000556491180f41000082c1d039058050032200344446000107864031400240101c3e0054036060703006210b0000e803210020355441084680b021980101d442d00c480103001580075100702c035000001440040850945100c1c0070408030800084250358442d0038841c8510f41c014603219a001c02848a207039660343c0180300458100070540e9409400040300c4900001c4244054803d540c980300c012910954a040880d01c1d5102d203481c003030822000380b000054541144002141030781d12844c030407003401c0004100c0700ca2603010003074064013045081c00f03400145942c041940e10787c42e000c3d02c0c00c112110703910032004445079052042813000500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 692002724 1250 692001474 692001511
    0x801080703080d09050a03170a02120a0c0c02060a02070609051c0b13021c0203012a0c051009050601080d0905030304030b0604090f0327051c020102030408060703051b0c0a0303020d02070b 82
    0x220702c0f01d1540b002480c04d084d4980094200c1d07949915100800cc80820b84d6115208050b4074859050020420781c0a000316695040040d0087d690b03a41ca0f00c6020002250300101248a080003400107501c0c43d0044103102c00c15400c1d0b9030301604280010710b00551002c00b500400056560000310741ca42485032015031038801d4807801454255100241007200f04508581030007084000d01c41c0c2401a5811b51900b410030025900d0040d045c2417020366000b43c2c0b1814803c1d410280100850260304860342d4400300c44d4100b410300703020745d07281c481c51240c554160410b020802c04506085040343d40036078003d10002d05607005503240310f0318125105040d4001041c801d54081d0003040b00340d00c41c2c400341629000c00303041031410740042d00140d101c0740d805c6020607112010070b0843e4020010758002d042500c040c4c403020f03c0c00352002001440100d5141c1010009070b075212401140c0001100d10345c15408000d028140c0d04d90300c1c182c0c06036001903030307903642c05508021301f40c08140700224060140d0a6204402041403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 692003974 1250 692002724 692002757
    0x20c09131721090615100908150631020d06050d260f030a0c03020c0d0f0e0603190b061e04051207060c120215070c0209070801080703080d09050a03 65
    0x18000d008402581c803c001784180c1e841204a601489802116100291400190100e07000144e0350701210582c0305500302021826184200e01d4402c2030203403020316001c41c0d00700c244250200800c2074240c1122014a10702c01034800ca400900130101e110343c011444030741e02d0b00030410080030325000381c52002441c00342050303070700100103080c8006043d940340b64100749610000210350b02c0301902100d48640c0e51940c0102d0305000350150340a40c6034a40640d045410f0060014101450f403001d01d400140080d0031700c102c3e610709441668015140c4001300c035840c95074910040d000b4440000c072240d10030340c24000f0300c001c0c0d550300300c0c00c0302102102c2840544513031526040c0805141ca01c14540c0d02900020821302001c0d50040c81b5102c81908011404160300d145030b0309a0900901868030409083c03440200620310303400071101d4841d44d00c01c0d034010b00695591070b4111681d50003030182428036000f6200c200080b8032840041e1001c030644040000e01840c280d035800703260807403d1400f10041050b40e4010000c02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 692005224 1250 692003974 692004037
    0x8030a0c03020405130209031002040b03070f05120610020c03071502070801020901080c030a110a0e0f0904020a060c050f0f070609140d0204020f0c0a05010203100501020c091317 78
    0x1403030582002e40c02d00d404c090006044078031403964242110342c00315003091966002c02c1081c0741009800d404664481d02c407900d610580c0c3c01101e42402141448944160084c842c00032500080c5000c8584074907901e13000200000703005451518021446800c070b2840355070b60144244301c01411283c107a003c24000e100006818220341340c0c0090810791040c458000540d03005150103601004101d00f490392a50f420260030000c203445e0601d00920341e00481c5211410b81c005d02d0610610804035103004d4030700c044204216072082d003110020342001402c1e00030060b01c0d005820708000c4600c12015a2035020364100040e1038000d403000410003941c01080200320340ba4110314500c01820822600000042e81300c0e000c640c0c902d4041d2002400f40d13a0000c0c50384070b070b22202402d942808a5101c2624481103442c01c200b030103900306441e200b1008051101c0001d0ba5030000a44c030594960240408260b0350320310303070004180030510727201380ca0402102c9440d8500c50322610051024030b20340340c801041b4034034003020002035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 692006474 1250 692005224 692005241
    0xd02010606020604053a0f030501120c0b0307120213050a060203030c0909180607021b0406030507090b0604120309090515011211251b0e0a18080708030a 67
    0x41d50009024040891004201800402502148188014a840381089041c2c03140340041e1206e050714910300125079404121200f042d01203a4060160707076211401c0c290b00d01040d0000070700d101e0302d0043c104514007110002c1c41d88580942440030000c0071030040321090303a010b2030b240846080c504a0600c0a071501d0020000500b06603c000c50641c5481d003d0b55030365128080c0503c1c0708880a100182d0710311411440c111840f000001540e41c03a080900c00656603004000c18841041e00c1c170451007609080601c030742011240c00c02c000f060f0040c40c1c08441802040180b003500d402c2681000046140e01d50305140d040700794440e0f07540080c450701d404510811140040c20f18401e5a12010107450142ea000d001040f1a1030f03440800641c42c1e580700101e05032442440703417942c0381400200c4016510f084805990001d5801405c40b400542d10343c82150003010441e0050041c101200c40120314481000c1c0c0c8015070907400c0d01c81441d44030704541c40340b01882c1c224030001c4458100c00402c2005410741c0e8055042c0d03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 692007724 1250 692006474 692006477
    0x204090213060c2a0510021e01020a09180e061003030f08100506092101020a180b120417040329090303130305250c140f12030c0d020d02010606 63
    0xf4407210707690300c050400c4503140040c222540c81c80068001c1c01d80c503d80d03000c002c010003040320580301840744000e5255202c0030600302c90403200001d50072100300c0600850f000c00e000e6035180c0000a003003440074510303c3c0d03000c250b8000d07450365003010609440c01005168040d440d0240c00c003200900c0d5150080c10b0365002c100340004c0007005014011990341061300003060703030421141141c948200c4004500310114030013000900c2c09402c40341c0e8000f96419070080c00c0303100150b0349010702c441d4074020060450071944505e200c0000c041181ea001c400d013101400e070700948120400b00020340b0400140700c0300d07041600140c403803035110386880300580035540c50407503081a00c04010b000c40c5031410f400d03916400020310072200c4c01121015082050701c40d80480b5181c2d140034264140010301c070082c00301522100c400481d858816807101003005005804040c1604500134400044282208240015034640000c0c1515500c0284042c004030b030800d00030402c50200c1c981c01801c0741c5042120086c00d54109522050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 692008974 1250 692007724 692007737
    0x507060908060c030726162a14031903050a0b030a03200f0a032c1908011802033a270603110a0203120603070504020409021306 56
    0x1040301c10204a0703a0b0701064042c092030b00d139a513a20b01607a0181030410003007a040f01020041c1041c85040c1c444074000c04a0701501c400004a61a0644402d41d0003110068000080724464840c50444034400701c1d42d0348103280c2c840303221100700800c5156030440b00d00d0000c01200818031012080c0e26114080c2d00c842c14107400d10100026101003516800c035804040c040210307035010100c1c1c400c1081a81030602281004072103102c0b031405099034451036041e03c11800904244100a034260b1402508158401050324041d000400c090030410355600d4026110b11b2120506d00001d440e202c21320070001140b90302610354125603030900c105402d2142c0408000c443d42003141c43c464560118612414034010308001140190350380c2c4000751886403501d83d1090140c0201c101d01020360141e19158070444a0b261006c2c0318190036481d4690060243c0300500006034405e111481c1040b13906000036230072170700290a5640b5a520b94010030b0503640180c200340041900000c3c0c995a241c20794020b480141040e20704070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 692010224 1250 692008974 692008979
    0x60f1210120314190306030506090c011d031203090a03140301150c0c05031e071a07060c09180c0e0a0501050f072d0506060d0c060318050102120405070609 68
    0x3441c0d401002001e4104140354100409698160080361030300040b40ba0811448421500024007038041c50108940c2d5010b58000309604031170004400706007510507104e500700c0f0084421858684c1000216283c1d040c843c512640d40030216040041d4020302c03d60028010501c1c05060180400c003440c0040100c03100100010005030200c4036900c40140c80c41d25003420714040d05d04048000328400d801c5203505000c1c22001c10f0580c0030f05002222064490825510404d6840d1180c141c10480b0908526840c01c0c1080741c8000508903900054424441c0d0030170300110364449442820064440f9002504256148130321085650007a6000d181d0071030031503841c0520303428100001c02d140107401800614400c003003510700401ca82450b44154103801c04110201d400c1405c1c10210040403861800c1d10036028070004941541040c0400c0700307000b03802c0309280740d8841c41d10800f20000d2450b4103205150110501c9030301c0003d0300a00040c0482c652501d22010b481c00c00303080060a000480d400b400901503141c008 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 692011474 1250 692010224 692010239
    0x10f08071d0303070203010608060f09060412030b030a0615180e0304050f1201020a05030612010504020f01050a031d0a050c0108090d03050c1c06170c180603030702060f1210 76
    0x41c82400c100e516821400c1c403848501003071550007146030007035165080c80b0b0003042010000401610880004480402036100c2c00c0a054070350f1170942c0c01803d41d2034410841000c05003e90010b040e80389001c0e0450b02d105200c3e8448070102c4032085140460001a4602000001c0d92148001d0b210445840e0422120507120140d650342d03c201c0c03003000c3c0920000d13010466a82d540001d1b0401e8150884002e560750003203200028950780c011500144a07000d6030000e40045001441001d03c55580a002115880ea07000010b40703058202112003801c16807224110788003904961002880030030107a004290010480c604035040c0a000861941004059420014822030020f0045050030103070500003459112600a8606407180041c2c14541101c1145144210f04d03a0303a01c040c040341c0200e10b400d06c1e07000c03420010031348440c03a01500b43e90110380b20401c840025092041d243d048800242100d1505000d64003055454200416904100e180801c410311280c000022440d8003181c0c0484400710307a03040402 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 692012724 1250 692011474 692011487
    0xf0504121202070305060703150909051504110d141e030712020102040906031b14010507020f121c03110304170306040e01060909060f11030c070305130311010f0807 72
    0x2014040e04581c20741c01405070b0080c4124005585c022081c1c1c0c55518026001401810003040744603140a042900025030b9501e41c803424182030740c800058020240002501c600780900900b0540c2e94403001c00140c00c4a540724182c02c0d40007407046034944084140c0c2000d180c01c1c0001c80c103490b00750028030020303901201c0020046825030769000c0321107240b8001c0c440c001c82c024081d641141e00c455103480400b200303100449102c10b42c010394091510070415200d80740c52402c2941e9452207408180306202d0900180303412003018804c8078018000031001c4c0102c0c8103071450001d03941c2520041d400c0d11065110000c0d494011140000d250212035407075070501c3c1d940e01c04aa6070f182010042e0315070100114495540301c4d040309200b22404e80c020300100341c8480c4400b0003002c0c1c8035400c079000781c03801d01102803100f1036003d4580390908140d403403411503517420781826440d03101d02e074114200202000000c80007103401d5005c0000d103010340a80014410484000b42c5150b40b102542014003c690041200080c0e1020 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 692013974 1250 692012724 692012759
    0xf0306090d050d060e0f011509050a0b0a020c090403031d03030103050c0d0f05060a06140a05060901050c071d16050c070306150f0833010302041802060a0e010f0504 72
    0x10b0700c10b076254403a028020040c0749981151030565107620600c8175008562050605076242003801915540c54080c09941a440c9846030f240c000482040400424a42030098429a90a8010b0303421004103c0001403000e80300b21021004a9620020041888000c2c00c8844030007030120001d52455041d52074041d507841d60010b00c07074817640d040100c40081002e418101500c2680c014101e81071410310b040d401e400342085006103102c070760707200c41440e138545011a01c0000311a0081c241500e084940401150309a001c0203080510740300302c8000081550320340b01c18a03c4410051140101402c2c200c154105004141c0980320401c101030002075101d00004c203d8604032540645c00140c01044046482c041400591020601686800000900b4500403900c0b510414000c250f0614084512136140d070424002d600c000d0090041704c00500040c10154808004606910041806d500c0d0310b5000400980c040904500041c0c4500c107048002d5801c403018640b0051b407814814185801e106007000443c5126 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 692015224 1250 692013974 692013977
    0x409061e0f090207330e07030213090501140a0f060609030305190e120a0605010e0903030403030e01090204111201091b050d02070209010602070312030c0f0f1403070e0f0306090d 78
    0xc0c1c58420061036102c4405d881540009002190480440e80c0070a40100c00c0d240040314180310b0407455040c00400c11030103603903000b001590100f21008400c8014601e02c4e008480c075658404054414401d60902d0600c901c40c3c1d402c000c03600b0360200313404c00240c40c029480901485400001400020340000542c0e503214050305054464104980b01141c1411260007a507800c030032005040c4510801c04102441c1c000d002c0c4a0601c03e90360b80301e50b5061101011501240950424030204000901c2a00185100c0216400124000e00308e41c00040c00c565295241010740c2100141fa0b0700043c4940c5607050040c50030309010081c414a071180e140c0011030487e0007400300400000c0c89035000711198190b4001a4018045680750740c2c461310043d51700c0c00e0500050300d0080b4441d002c150031500c00e010300c1641c002c1503030301d8032107001c1e44d50003d48000c00c10590a100b03015a05021400d0b400c0310201640c0b0804d401d540700d010385902c0200340708201c0301400340340d07002c2d800003c20440f040100040c80155140b19 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 692016474 1250 692015224 692015227
    0xc030b210709021b010b150702120f100c08070c030e010e06070b0a02070203060f1003030c0203211c020f2b050108011a040209090103170f0409061e0f0902 68
    0x444a6441c10080300741c0200e420640b010540006030040e40154159134410600200a8070b40c0707036401c00440321070030004183c1303074142081080e0050420801d0380e00f4072543c0d00b0489980d03814154440c3d0515580c284801c602a42c0c0702003060806034003218168100c0038506241c070348041d290f1001803c1e0307200e20504505010f000c8400103480c2d11003a0444203480e0304005042884e08101d0240c07000b95101c540240d00c03c1c850100030400302e007404040f950003500340000e16a80c5514694098504680241050740d03d4022880300815018035680a085102c0700aa5401c1da10340c15000c51220742d10100b56103a0b03000c0d10500c2188416040481182d80080910ba0b10003840360303261005c41c4446052034041c403c518103000002074217541c150441d4008141d010700550098401c002813200702c0c0035000a2561185626004002040d45854440540c040421034989400701d00846503040307500540c040c02e0305070b60b110010000c1c2d01d600c070002c060666200c03168042c102d1a1840908100d04030303009a04107142d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 692017724 1250 692016474 692016529
    0x30b130c110304080d0e090f04060510031a06041a032508031b0607051215061b0a021302270105070f12090915090207020d061d010c030b 60
    0x140002400d070240c00701100c1c1d0701c40d21128041d49034002c170503c141c0480c010403e0340e5414503100c140c0501c5004844a25204c42d6250740b108009004040c0a9129601c51041d012010a500c0320100c0342e030100d030720642e4446082070003c0c4130444203428005160403071584c0d980e0407d96400704030000c4040720000041c1150950701f8001405400b15803010030302c3d00c00058414254144000c103c40d6490340c0390b040d6031440d5150b040c242c50a01c60000ca1b840c922841100080201d5485102d446502801030221420a450b03510340031a101c1280882c402c0d107034080c20b01c10085260101041e6495110f4081c19800c01859081140400c100c1e10710300c0303110b0140142840d00c10b1b48104250f07680300d5080172041c41c0075406414081c1c02e00c244a00980001428220302054110b0180a03035402e20300703800f40c0c071541e0342c0c50406064000c1d0040f50040368050000c0c88204081000b40c02030081020380300c2000403012518903000790842e80881204000e050524144000980e01ca01c184481c0e0190741ca0340009007107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 692018974 1250 692017724 692017727
    0x7020c040b1906021e0109020a09231905090a02062b060902030f07020a03050d0f110f03011502010c0207030b07170f011a03060d171303060912030b130c 67
    0x402d03150111962000000d0201c2d4005190000c90684003038038010721150030001c2d8261540c3d07402c0a174114803e8842000464001c0c1d0210703051362601d04040c0d08080c4c004844507001001a91940e044254416810501d0310b40c601c10303e07800c106031b036000700b282301e540d6808221940074a81d03903c0543d221840f03007541910300c1ca000c002082c100070441000000d4440e07080e44003d401c1560380c0f0148002e9000003814440c0001a098201d6800d5140c6d2818901c01094a80140c40320441c2c108c0602d89841920401c1040c507000b0785440303183c03690b50641303942c1041114100000c4002002085a041407801c680080e00458420300741c0f600f0140181580c3d170b85203410369001c0c06a800d504c100780c8250081140c0c2024807220325060f107030409400c08900800c40d45030041408113403040c42c3d0190b012210000001d66a070040d03403005a5a80e8902e00b01407140d2139046003e5190391065030443d8903850303142c1c200703c0079a03003154003c0244c0c02c2c10051101c5503c0801c0c42011088090910340d0307546c0e00000da17041e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 692020224 1250 692018974 692018989
    0x1609060f030204024b16240608030306190e06010e1c05010b010f1d042a0c060605040c0e130b040603030207080f03040b0a2105010603021803010507020c040b 69
    0x1210400905c0031148402005808003c80700c2e0450011020030a28410700320f584048801c090f0820300c00c0d07a4543c1298841105a0303501c2c1002004e484908104000800b1150040030000d0024101850301c03850010300740600d02510b0221032080c0d0048a00034040c802c003100c8441e42010081c6003400040b001e9038042050382c40780c5540410200f031480d5420080100c15044a081c0710720a99482e9420105400305581712103806010024801404071554003038141035114840300085140c0c14040100c9100d0000a4001c0c58101800010780e0848020305000c43c03401450002c1400340c0c0d00b00440c0c580102c0c02060f007240c2d007003d60301c10000b640407100c01c4400340e0082056054020810000c003a641d2402039500c08581c410400240245000310b42e9454000c0180d40403100b0940640d4a89100701c00201c40c410b14103540c3c01420001c003040b45445c148a44180360281c9074a4400595460b081c5c0e410001054009980c40e209038180800c016016901050704001408180e0700455410002400a01c52 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 692021474 1250 692020224 692020267
    0x601020a021309050f0d0512060d02061209010b010f1e030609050c0711100c02060a030213090218030a0201140c0a0203031801080f13080f09030f1609060f03020402 72
    0x310000c2c080b48800c40b103681d40604400b03071041007100c400411152200303803540d0180349588046002481a80c40102404440c1d40c3e018100401c10729450050750300003039054001c2c410040c2c400c40214100545200240b08071365800300d090804140281840703400030001e60840d41c3d024808201d1516181d4080d001e03810020180200b4003003480741c1d1a110700c01013060b8020a005a5200a040c1e143c00300900303104507044420040c5950340303004071003642c09015541d40180c400204041d8200258400400c0d0720b00014054812100c0c007580e2000385074400c02c80c132030f088048184207411941524005170f801840100c031864a200c03400c2d45813031041d450582086420760000e505400002131102e035036100210324061400e001d80b10300e06651130707035880b151410740c046458100c008101101c070b2010421840c00b90000940d00505a40f81c10001808681095109100032104d41c1c05404511802481886228050f014000701000b420b8500104000c1092451102a0090b640001c2c0c100101c3c404c0c8026103907 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 692022724 1250 692021474 692021479
    0x40b0a020f070e090c01080f010b031e130201200c04110708040b0a0306150206070e040605031501170d0c06020904020c2b26061c14150c0708030601020a02 68
    0x12059a0b808502c4a078500484070340965000c0e1740400c0c0b0444d8020500c4c58051040b12140f0313100340e03003401c501125507480a801e0500e60099140c410155a101003066072240d22425026082090184005022140c415441da0305650000c12002a00c150020740741c20456011100403805031944108000340d8407840310060110f01001502040c140c800d10001d1411607855070b801c108840e0f581c103614a4001c43c0307450800050700710718080303840320b40f0079900701a0301c0c00c0013040040c00c3c543e02d0380041e2030011411008009142e00c000100844203900c0e500988164400e00505850703801140014440b07480e0340e00007485903034041054002c98850b40c1c141c0e6141d03010041200c29050350360000c0e1240d40050041c48544c46031913090001c07250b202c1c507102e0321184200503440001d02120f9140d0407082c4001010950044010351020070003c00e4042400001c41c055107044d181c0f000300044a90829617000d210a20b070283c4042881100510142294902a08111680d03100d85034940102d080c00c40c00c0c81c0103035 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 692023974 1250 692022724 692022733
    0x50301090303020301053a08040f14010f020d1416170310090b21010f0c0c29010614040f09060819020a090e0a082d0c03040b0a020f 58
    0x420940c260f401103050710303000c4910540006007895000340d0701600c0f0b0400d465010040007400c0700a5545e2202220561080a4490800d1b441e41190f1030030030355590061082da145048004031f6560000c800715507291491014090a41400ea005840c800c03084524551a0200284028800440002e150803842c0c0c05290785225811951000005420070f03209400748154002c0001840d240360321402e08600300103003c1c0416407a281e040485003030380c4030401207495500d80201d01904041c91150400000312511404c04030307005414514501d17544401e20b15100010980800c0d02100355602950440700f01d407906440c01e004001c0c03502141d0285620a0794400004140440d10080c13541042069032003010850304103001a0b9181c0801d24100d00b006904041540c0050160b890b060b0400d400030840e1000300d8550b00099981d4103203e0b0b2000f4030074902500080340004102d120040400030180040d144507017008207010a8030740ba44142e1068000305540010860b11850081c4800b8142180120684 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 692025224 1250 692023974 692023991
    0x3070b010305070902031e1801110d060f0b0d05090304080f0601050112021c0b0a08030f03100f031515170609010b0a060212070204110403080703080c16030f09050301 73
    0x250144000c0c04121481e01844602140303001044c4241c2e0702c0341d1085007032011042c2ca42c0f01c2071503c060001e400ca140e803000c0c0040c16a03200307a0900a81c0700008100c104070340d031050401c40c0d09080324807a403c000c4c0040400103041107c0404041581ca80703155000000a41c0c0d16103440c0c00d49507100e15404031645020302090074042000115160b4101c60007a00d880c45200c421a509508a200d481003038034810004080b174800400581d4018541c41002a040200d026210001d01703165400000c0303002c0702d02c00000f04028105c61b80c00282e0340100681c86a007415503013035581e131152880c01d1044007205c407640d9900106e420350b4480c601d50018220500820701c403405903946103488101c12618580c496007040f4180145040c4082910200c4210f50b000c3c140312000c4041c4140980c0c002d0900740d0f800790301c5804a50305841c3c0800180700640c4104001c9039100b200d0326000d01a03401c0140305c00d100305400e00000351300002c1a258145010b9247c81c2c24403040707030444002d40340d00045401003a015887d10208 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 692026474 1250 692025224 692025233
    0xc070b07020f0d0c050d0c02150d020706231f09020c16150504051e100f0e060901080406020304030c06150f0b0901051c020f1219051611010b030307 65
    0x200038100e00c4042503d844042002c000e80b1503001004004000d40e0101c11154951842188690341c2c0c00e1008001d110003498100c3c070714290340c03c1221076144c3c2e039900043e598100103051103000000880c0802140d000718040c0e0210b111114010404640000c6141c0100d05010194140c01d000d810b1203035046407130340412216203035101e0245040051440513810080b4070000e00344c050344980075041e6161803416042c10148020486003e00f0a41895820003055103540e40f2451901454030f110340d00d0701021201081c00404454000b2040b40c002ea42c100000c02150340d00c02410b80d44a5004038002d65651036038582110500701c03a0764054103492610210381c103144100d1203030504850307203180e0707101a031929035010f034a140c41030183e018003042d03041183da04040c0100d1482c0400c604044e1005044ca03801c03c6610312954048600220071411003810484181c00f0b801c121808840144010849440d041404005221158200303005002c1c00d041c458048120075041295600c10140c10b9984403541840c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 692027724 1250 692026474 692026483
    0xc061b07120303201608090a080a05060109020f03060d030c020406090b100e06030411150c0703060f0207150b13020d0501060809190f080c0307031101180503040504050c070b0702 78
    0x20490000782000000f44125007805101c0b0710a1000d880b902e0314208980305c2c010860121803004554041c024050b8032030aa0b50103004000404500b405801c158149103031441c00c01c10146c001100c030038414000c50120800c900f043d00c0d4420404e6400c03441c00c000a0800740c2c2e442e46242c400a52103824460f0208a2100c540c0000300d010310f065400e205025040e072000d4035804c0c807514480381c00c84803d200140100b8031800c49600c204802408807450115070189240142c2c0c054455400740d82c2c883e0342c0400401a00b84031389900c40c1d120385000c50a200ba243d941c0d141c0540e018030055890380c1c550500011139900d030f4a628400454406045580701c2401d200c6201a050901c40c400105170b4120008034016130128000030700c0c1c00d10010760261590f055403040d5503001c0c180400c3e82e10385010311101f05509020401090b80b50300036140e0300c000b4400403103002d01b52425081e140512020300040c01c40002c10000542d000c1c4c0310122004070b040d41c1d8104c007000d001d0050b44005081c6020b41e400380100300e500803c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 692028974 1250 692027724 692027759
    0xc03010e041b0e180c010e010203180d140609060601031407030c0203091905030d03061a0304031e02010e0625030e10060308030f011415070615090b1f020c061b07 71
    0x1805da88801440200540ea203508500e6614007582081140d84211000c0c0e5940813202d04006041d601ca1003c5507e40c0305030304000088180c45640500c040c004d440d8402c10119511441c2464140070049001413505040131001d07010300203168490180c02201802031041e1000300300007a00e03100072144080390040300410ba6200d0746009004031381c161022284640240002d458800c030001440207010801c3c10340c5940300400039410880c03a80c1c208100071201c08120250010380b540003184241c6d038401d5030380c2040c002034904101105107400c0103070710401d00c080352030402440b810001011b1840365400d9041c00c82d440c0031650024545507000c010044010701031400b60880021012150380c03206604500b4180704141968840300240c461009118104002e00115200301c0000c120103241001d066000744080d080007035002d446180c001b040b41002d40c0d0384050002001054041c141c44004007a445003c800081030090000060207100c0241c1c1c000782c00c03c0318001400311405190348a10031054540e818 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 692030224 1250 692028974 692029021
    0x3031d0a060f06080d050d09150509061003230708062e030305090405060d0c09020301080d261e0127021c0f20070204050c03010e041b0e 60
    0x82c0300e80303a001180b18481c140c0304620000e00c1000c00064064030250020620b005250351101c1c200c0e130000e4601001114805030036003000c555424440c0c0d80c581803c2000304612850580d5400410105100042d0403240c007020840c1c0340c118050b50080182450402e400c1703208684030305020310200000e110182c0742c54403002084030040620560541710411054400600000c1d400c3c0b14400701d604c2c05038400d41d0003c0c4002c0000c1b4505500d030395142840d1150703911043d0b00f254003100401829000b440040500d05891074000c000000caa81004050300c1085c00314851036010070002940000a0102e103480040807900210040d83d4038680c030300050301c80b0f2100801500d402c01c003a20f0480700b280280d881f04e1840009030307032202d440340758558010032071012030040351030719803034035039020380da20300b07010600754404203006544401c0c0380148000e0350400341c411000780c0d00800041102802e01e00c07103070382c215500180b0030322001880d10590440600320f411103003925600d6014410101111440480c1c40e6030103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 692031474 1250 692030224 692030231
    0xc0301060806040f0314091018120c1205030f07050a020a170a3909051003020627061603020c03070b040e090f01141e060607020d03031d0a06 62
    0x100c1d046662601c01c1030300c00802180b041410750000902459001105c401c502d9240d80c18040104009004401000300040c04119050005100c00d803880010002600d02422082e06a454940d80c03075401c1d021500c52018082d0310012200308000d41402102c00c1402c0340a1b4060300e030034107420102d0302c1d1003061004a1041d0310592000a8129403800c081e0a1001a60058249401d0a8580045410000b104801300045c80407000100d220b1000d0742001c820441c40c01000c0c1e040c2417000900c102c860240444041e8840c0d08420030040c8d5034441142c0303540040c40068030899134010000500c864031050f001d94800800302d485191101e9041015031594000d034211101025000c050680f02c032000c2c0129408a40101306c02c3c8141000d440c00190059a0401140d18a100b07402d41c0c0390071900b8520031400e80043c00360030320020b90041d105902c109030907881c60720a203003400342c0002c0703841c8600c0b44000d004115a44061003854000e5011903da840d100b01000d04e059222114251075000070030742160707464038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 692032724 1250 692031474 692031479
    0x70b04090e06040b070509030a020319050606030f03160c03060f090b060d08180105040f090e06070203121321080105010f020102181203280306090b030d080618090c030106 75
    0x1690600998112440100175150160110f40c0d50703102c1e00c841505071055050040041e102009007407102600300b0219008131002c0e01d81035042210140001e84250b12003400e160010034044200c070300401490704403000414a83c03400c040b000b103071366002800d56072810450400c1e4005541000d50942d208541100311940e0720010840200120400a49602030502500410442003503007807011181c1410710038209a40c0f004205403ca01640004071056120f081c00740c1c0030740003040b0302a0000c0c0640082d40c24010f45040c4000411343c0148840001441128584180704068400c0302d58611b080181c442200900400074000010a11070705000030700050520490920620950300901c168a070408404000d017410844401d0a0f44110000d0740010807400008801c4000c0a00c084c0101242ca014003c00501c405401c550075036001c01011410060900d00550b07000c1411481203409003008022600c800000c62120030b404050b07c480005c281003844480007000451000b00001103000344102034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 692033974 1250 692032724 692032751
    0x5120109110f01050d151d0702030f091c06050f0c07020a03290406051b03150405040c08010e16050a0b030a050405100501060503070906030b01021e0f070b0409 70
    0x1500c0d05006800d01c104490031000307516040051010b54101403600394101a100700714802255036160010180c021807100401084104010002c2c040d101c04100d210342e8a01400e01079200d110b4401000000c0000140d0a03245a41709190503c1d1800803249140c9110b00914203680107041c140d46051803800307068001201104141c0480d00011360240c40f410480d0310715560071402c00496601c2e41c000701c034550305c048148004204034510403802001d0100303072410a0090f020142c0c10306942c400c503400c01001040524904441030100020b000d072000112551542058216a0065080740c4141c0d420441c4040d00d02c0c10004810004501030b500c1703683d00c0e41d6940100003040c1854480c02c028400d0501c00036420040a074006079025000c2d40c1a1202c02c038440d200d180c1160400d03001540495030200c00d105c0001d91002d003044c050300303403818200100110000040d54900543d540034107421000e1580f2455000280220600d070050082140d54039600c4810b21805030b0001e010b040403240c5071240c6007044a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 692035224 1250 692033974 692033981
    0xf070801080d090b03100506031003030e1009030308070c080d02040905090d0806011d0a03030c0b0f0906060613080d030219020a0b0604050406090c0602160f0f060521040804051201 79
    0x41840e43c540c0861245480001400350708010405420152030500c0011306440310740013580701d0701550401003c400c0c11444e015003a50807002a0500507192019001619078000d44120252501414818001e54449100f00d401d08903500e401000c00402140c003407004000c680240090340c8030740720b050095907948600c0da540c03003190345441e10015060b8000300b2059402020402d8140f2040011040b2064840010603442c0101c1e920031070025078104460790174008001c0c00e107500881c640e0f0700d00d14141441116580d42c0d0030083c0043c0d114100c000b50042d1039a41c5010410300900c1c0071800d4503120041c0d084054000d401c410010010140d050f101000c10600c0032803810303002030b03028229403c1c82c0c442c2c070148030003040018000c41e49941c0c1c03403009001103400c0110510043c806a4010a012010308a0501c2600003960104a421880b014103002c1c03071960a02900035590b02e03107009526480c0c07080c5200c00c0c000d01181e0b90303c42e80104c0d5041c8020300080d0310041c02540d00543d0040d00c080101160f5900704c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 692036474 1250 692035224 692035243
    0x10b0c210c071d070318050f0a11040902031b0301140a0e15040b0703090303020c2508010204030809120703170403061a10030902010e0a060305251b17030f07080108 72
    0x1010f0800000844241c020380c4084030344c50409600501c003540703594449241c000002c604802c1e03544042506401c11815080390742150310b040e6010301c032101d502e60100ba03481825030301c00c0112032505038030782000b51425406651031482405c003075415410100402c3c00200841d03030030383d01c2c82d000d0005207941404880341d4060090750f208a00503050b0b9250360b4120001d07c281b4204400b0507130200182d50100d0400c02c010010303203443c40c50030303101d9542140c1d000358070708115413100d01e0690040c0800c10203c2c101030107a85040310309684403010314080e184d0711800c00405030002846849003201504c9a079150301c0180050768032401c400c0060700c801e1008080203a21081009501410a0f8483c5448030700c00d4003e035061741e106040820044104c50005502412645c20020009986808020100701042c4e001c80c0c2c0c1d0162125605034800303040500071301120240500c03101e880d00c81170388281001442195844981242a0003a48a06000303402058440c0b042e500600021020340001c5440c07100410042070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 692037724 1250 692036474 692036519
    0x605030d0513030b19020a05180a0b040e040f0602070f120302030f040f0c08033405070302210706200606090123040f0608070608010e010b0c210c07 65
    0x94240c03030742d5a11000340c07400800c0d80b07903103010800111605c1ca5050010f0090140140c441c541c54040c6d06003400642001e42515070b20940010f00c0400035155190100c4d0b060360b06500301c03a8000d42d86d5003800b604940d40300d240280386602c000350400c14800819910318034188100c01c6c8a00fa0700d60030104030306a004c2950350b40110070074003002c0780c002181428070100c2a48900c243c0c50a01366900700103421134204482d034a030108280c82c004170700c0305006207080d40c03184282810411074044540b1403542d100c002d800002c0c001c4840c0c05080200e90011201c0a08505c6040122420a074a8600c028a020390b20103505c2d14082e00082504040007010401c10310500000d00003f4582e032811071b110120581c05101482c5460055078001d9091b06c1e14081c508200844000100c0c0d554500071a003494041c650f40001c0c2003000ca00c0050010a4200310010b044a142410b20b549601d030b200710700c2d404e03c01610107840e6406581804aa1203450001c054162864101d040e60856a03450045a8a64444400640c2c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 692038974 1250 692037724 692037757
    0x15060305060616140105160f050304080a080414070303031a06030420120609030306122a04061203110c100e0603070c0b04030801140402040303170a0f09060605030d05 73
    0xc4101501042c1e007000b80f40034500c0829131030411041c1600b11041502d150302e12182c85000441100d03000307043d03600e05c001c20745821440e52404d0f4552640c14000e003032000c404c1000d1030340031506000441458052040b0030500740c1c0c209541d0b034034026000b000d841c10076030000b0703114284d80b842c00d140c214152032042d90482d02c09080c01c0d00c442c4441d076540000860f00d070350140c3e43c50881c01c1001801c0107050310030702041000b19604e00f420745c00c10910504141d00021a45e010920841c48482d141c5c0403180c44213503181c1501c0301310840c41c0024000d002903400c44183c50242c0c0f40c01e00c0915a00c6520b0001d122484001c0d82c00c5007180005000740c0c030030015500e0300441c41c6c42042c008a810100011584118640341c50013648150b5034990f43d00440a5400b0b5001135480001032003c00000d41c584404203000f1a02103240a19554000d4204910385506204801840e80064200c1a040e000320400c0e5400f01d008001843c0d207450410028003250151501910411403a0380c0002e0050080701d02044810a186 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 692040224 1250 692038974 692038987
    0x5090d03030f1a03100b030a030509012313080d05041a0f04080607082d190c11060f040f0b180105040c05031516030f020c030d150603050606 62
    0x6041440408504041c1da528001d0b40142c21031281e010644a12407981542ca032664081504e0000c3e010804202a40340c600401d4045c7c0d0300082610445a141c2007190310351030070a0044e140280d0825001c0e060000c1406540c1c5080d82e400c0003001c0055a40707101d50405612002c0003503940c10160014408200e00300000c0c04080da85180c2c24150141c0d25001e9460602e6090303031703000300740c0095202d079000364005030601180c150420078041c0e00848084820790004080142c050102c203110050f404481003060100d00001000e544060031100702c9075040c400c80a00d070500070140200c03400c0313144280c011031000c21354003514003c0d0b080c0a250090f1b5025400d6140e901c131060000000f410604811500d190098401d040038019a481540121030403c03250340390500780750906000d800d1202c0407010358010402501c000f2902405a000e035841c0c000b82c0c03120440f507110001c3c40341c005082c107203200215140880c0d00c1c50340c005524000000b09208400382e0703603120603010790b0019a60240d00003400d1004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 692041474 1250 692040224 692040229
    0x60702160909051207050c120c090a050711010c09180b130b030a0f0b01030c0509090a060c02010b130608010606020303240114191407020a09050c1b060712020702010509 74
    0x40404030340294203a50f101c0350703880c01050b9141d2117a10111400c2e0000b00d22400141362920314800c1404e5090007030703c0c26842801c00503401d104010040c140455a85c000701e0840c61081181003c1c84404500802071680c0d072040c0a00000b20a1246103d40e0410f4a100301d4618040d0241d00f9012001800882152512502e035802a200442205825101c0c03040b020002c103d4040800305200e0044000132519411810401c0c1e01c00c01c05c0d00500d00854030320701407110603803001800165240d006030f4005075000d90410200e02414070340c40107540c408000c8003809000c800d942d0080c1d04a500890003082165510314040e0b88a0000b120700c0030040944131001d580c4140b0350007083d141008145020a00354024803021b007101d4100c000e8180d03004500241e0103106541102c40c004010740a1905c0c141801c0069001801c4080c2c0c40c000c420210b515100441c0401000f60262080c0c16110729420b9003540c03482851541c2c0e10000c6a1490010f000c040700d07403504031014030031110040d406a441741c0c50b25120505 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 692042724 1250 692041474 692041481
    0x306041403070c060309150e0d110c04110d0b0904080703080c040f0308090f09241c0f0c0e01030206070638040b04050c03070f0e0a0e090607021609 65
    0x6420041d000401c50b110000b256420b02c5000f0700107507200010081260308111800f440701c0c68805c014589003100c4407144100c00500015244018a08108070709142e01180f410540d000341006e402ca4107020714620b0056141000c1d041d41550201e007040b2903c0007000700500d004c0140d1f40903013940410000040031a10924440d83c0c0f01c1d9200c0780c464946941c45c8002c0500111503403054804081c00b107152905032822444036290380707904903030f5901c50f13040400d81103040d6a01c01c47c241812083d03c00c0c91901d1600c030941500d00c40f805624181900200c1800d0054107112941d0f021039095801c500d0100d082041007824505980e00074003801d00303000d0f80e55950700c001e1008440e0942d0022902d90071200f5142c07085107050f140715400c03c44000008000e0300340002d55040d000d0a0f842941850104400d039058401a00d0341b1000328948105c61102155081c0c540c0c51081003032a402c4200c40d200480d005020742e0419004105000450300307240c0d141311040b80ca507030b1000c00c04203072512218800c1013004030540 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 692043974 1250 692042724 692042753
    0x20a0c0219030b04030e130b06090d0c0302060f07050d020106150c0f0209042105090f04020a2105070e040209010903032006150102010605030304080a03030c170a09140705030604 78
    0x5032005029183d481d070410500381140e040700068803d44204005052060106800120903402441110320b01000581140103d00b5001d0050354a40c51050500072544029401145c026100f9540c0b802c410000e9103141d44052401c5e01e051141c0402014010320501c0303410126040ca9090420382d500c1c0c83e4007110b00040010701503641c412508003d0000d40d0380c04500300c2c02203105040c01214403175004252a02001c12080e240c003406014032140c4601d071290060800610021a0010fa4a00c0041d03010b40700d8542042114a0b2921140010b034800d070381540c0702c10301030101511036104041d591401c21069110340420940003ca10500800000740910140c0340c2038001d409003440100c04602d211460240211001000003490f40000346055070203104000c003a0409030007442c5050305105030700e65914a0761100808242e0f80b0b00c08003410301d01c181301980504408400d10710a03400e2810b00c0c0c00140060007420754030f09840000c07260071040005401011a580035002e010640c2e104e45500440c030041c00c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 692045224 1250 692043974 692044009
    0xf09010302070c03050f010b041a03060604051e010b0a030b0f0f090907182306030a1203110a0804020306010905010f030303020f0c07030b092a24030c0a030b04020a0c02 74
    0x1803c0400050014080d060081080d1800028280118020002580d01d0f2480001c845d8000125007400b540b008141c06034400303001d55010501d515899040043c80516211404100000000100300c1d40591802448103c189503400d00403005000e080000e10540d4032000381d03000741300e03840003075141c1040c034071190744200400181e83c422980e036589213031842000348692801f690b0b01d4141185201d0303c940144079256a5a500031030700d18080340420ba403403c041501130703c0d1111908649000a1003600306855007900000c1d81d54550420406c00303454203070152000c074805d018003000455150124820181250200030100100504e1503e05400a40c032500f00301880480070410b015102c0f40070411000103611450b0281d1252070300c40c2e5168280302116a01280c1428044207454000c00c1e42c000344942d24000301c45130102d1415419030780a82040240001d01d0b00b001c003000700048001208041e000d103045544050241c2c4400a0401c81284130390079506001c6142c2d200d1020150400c08080024040031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 692046474 1250 692045224 692045243
    0x10e06011808030a030204171504030c1e0f0302100504050d050c03120408090310020310062d03050105210a0f021216031e020121060308131a0f0901030207 68
    0x44010b082d0841c0d00c100e03000c030f0100782c000408101c50380d152075198111000c03410280000300252041083c0103400500054200240190036200b0721461240f81e01c000b030310b0040c0c00c500b01400751400560747e02512000f54090700400000c000c14003154002d85102d02c6d84107020700081071031460151525080010390044a100a004a9030b0340c01c084060980114016946251140c88000030903181209800b100c4961500500900038090300d003000c8481507440d541046094850004900c01d04128111108130290740c41c4100c0301005c0c0d03010b51215050b2030b002c1c2c9481c10400141d2042e106a412003007181030080e07104a030b10001240b074024052005070b1000305405151941c402034985490400d460300204a28a80410410400da11a000d91a4514041500e48041d80c0d60000784c00c0213400c81900c0200b080000468a180c51154400c20165520060854445a000119441c100c03030314000d0300c28803012040b00c94079038100d9206450a1103d02c52045140040b010011401303500543c008032800803c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 692047724 1250 692046474 692046479
    0x30c0809010b15130f0b0702100f050301141c060c0e012f0a0f080301050102060f01080303040f05010e01320108071a07080d2307020a0b090c1903060e06010e060118 72
    0xc242d0700a0000700a0b11b070005841e0b40c0c85004111402c6149150721041c440da810f030301810580c001040d03d0446054907810b260f10003c40300443e49411048501074000220f10318442c0c20001103030b12014044400d07032384449600700040300540d000181400c0c100c6070761584414901030442401d031020300302d0403684144c440c070301d10a5944151442d040c010488084c0d5022005000b1540d040100e15800800400e0642165240c4040c0c1602c1c0c4c44082c001030101107142c2c11704020710200750490200c10091000800401002d40c5d8003e0050342000149940e0b101c508008010070014403558034141c820080c00781941c94500302d81c1100c10092a13205402110091050300045400c0d000a041007003580b04010440700d21f500c000402c000340d0b85c10001e14502040080c0305280da8002a00410742d45d0081060659807242c6e02c007240b0300001c002c40c1543c8100d21464203c1203da420071400100d910400d010300c0207280c5115006c1d1500d60901031040f10861130320015101e0340c03084900b11030b1a00c01d500c80301d6480742c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 692048974 1250 692047724 692047739
    0x1805060d081201140109030c050d03020a1761060b1906050a030c090e01141c031d011e021b040908030703090213020a030c0809010b1513 60
    0x208600e00004440600b01c004101c1c0c5500d0001801d03a1070400d20303111900909660304c40820614500543d03004102041d85a0704240c02041041010350304030ba040e2038055000c4444051540c040c010604220040100c1c400094076012101545500c42c49403c5d4202000034541c001c001480714000c44048031241802c80d0502031000462030321170b008410118440d020311040c80103114a0041000b4804000001008825880415903928581c1454042488616410200c40b80d00c480d4128601050190000003000e141c01007050550300c0007600e151030041d80c40840340000c030341c3c002005004036040030503410940710080c0103942c9000c0141030082582c5540c0390340c60211600440d08401680c04090624007003c413004c09000c50700c1007260248040003c81c1d940c156107000240c0341200340358a0321400e00031035564016a2004512944003191a0046401c0040107000c00080c100e002c20340038804a070920206004903580b003000030704211002c1e000b486801c0034550102040c0b52641105100c0417611300c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 692050224 1250 692048974 692048977
    0x904111507031d03061308090f22060e010803121b030406090209090a0c0e07020109050a08040e010e1302010f230316051e0702010c080a030e0114011805060d08 70
    0xca02030360741c0003c2400e101c2900c12600010b00748182c484d40c03250041040c40311102e012502010b84c0503031056160f04041010604419402078001d40c0300894140c0c0850042000c01c0f0013a0184900340c0c01d001141c0d44520440000c002809108a250030030056007000c1111001c02a03008004040407a8000080c0990310020307401c0ad990032030700c1d640c039040e110f000d5141888003140c00042e0400509030100d941d69030810b070b2841c103100e5031001c8240c110000b0501c5000b13500c400d03896900001910b60750f0215186c10302e42a03000d4040c2100301e43c46400041a0287d411707001c2c92049610a10030403550072507800640b21840c2e040b1010302005480212085c5400c40100b00400d80700ca800004d541360300b025291b0320246c140c001c00040811000303011800c81c90701400000d01d650203550020300d0340e5076050300040300d584031010000b0700008400913185141c140d15501803031527625103400070450904030b090325004120003031094203240201900d01c40c440e180c140d444550000700040000c50012810340d10710189 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 692051474 1250 692050224 692050237
    0x304020d1709031203070c030e0f100f020d0201231503011118031c0807021c080118052e051201290303030103030f03141008010b040b09041115 63
    0xc0ea01c010848500c00c1c01d040240ca107026000b13030300c1340d811880d100300010f10502c82c294000d0100100c50307944400c1901c1e80c09403180000000761549006071061070300500114030080c0e501c0010301c10b6103d0160894410322032003015281011000c24600c1c00301010421401d4080e04c40b4440300750761803000c01c0681e004d1040160050b001c40055454034140c0f140c070110456007140d421b02079003110040d6004079810055038540b00400f404d02d4449911805804ca260116240c41190b04c101c1006050901c00e821903a014121498400300b0f561600780301c1c14907401d907031040c0e8100d4100c5d00400c00c81d01e241201c0c1500c100b240c980c02d403c2c43c910603a507000040c0089844800e0301c207280c0d54482a1041d80d402d201500346600ca0620f07134a1041541d044003107a6244814880035040003002c503030705450340e032180d0404041c0700714000300c004050806090340e114400d120f11400e61250301e00b03a000f0301c1c0c9007414000d140b044071000344a07026684d1651140c109459400d072820b44c0c80803048100b00018403515000d00030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 692052724 1250 692051474 692051513
    0x30302010b0f0603010e130f050304030b0f06060717030601022404060e031206060f040e0907090e010e070515160308061e0f0f031603060e0d090f0b0304020d 69
    0x1032548414042c02400c503032100b0954011002000180101031140c0321158000421034502180000c80f41452814802004401002030000050002c2402441c5a81c18003d00244031a81607548900d1304005140c404c400008280e800d00c0e118441c0020390410246a01c28010700540e040380064a0b0300c02e0b0014040c9441c4034030300c81c0860602050103114032492142e06030300c000131407a01c05480003410540c40007c000c01c0c45001d00003080213490381c01750203440003000d0700728811b05a41407514960b81c44860301e01500184514240c0303e821039880c14010629048808070243c12801d0901045c00300d45c13450300d030b02e405210300c080215026030711501c0c043d01031050003030340d58170100e00b429001c204a8014101e03041d00d45c24490700d447c0e82c0c581d1f6802c585c1080711038100c80349450610300c407021038104000c1e540d51051301510342c040007040c031145420410602040e00160b5a0700c0c0d420080941b010b1009018546540e0705611040c018007407100000c0d0740284c00104210700012480e1364403401490302403190301 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 692053974 1250 692052724 692052731
    0x1803021905070902120a0e030901210b0d0501050403080a0b0a03020d020301020f032a0a12090f020901062f03030c0d0e010908070629060a05041a03010608070806091501050d0603030201 81
    0x10325072a052217088204c11f1403801a40c641645800020071804c1906000e080710440d19042c0346c90b405450b401803411342c1b070103003404040410760305007580208411101078000c40d21480006200010900c03415a80000c0280200340c481d00310340030b2040b42100c0d40e00403a01994208041d00441c40321402440c410310850842d401c0401387c40ca90390820380c001602c14003400300d061150b0150300d034100800b18411101c0f8200090b95040900340050f1400c4c4090000c1d40024520700081062a44800c03000d03182030814074481c0441c2c2c0c109581da8030300c1a9040860035550418408030b003039148154010f00503100c81100120300903020050703103401c481c559081112544000950442048101c1c055140480200011003005a109000c0c80700100203415421b485104005002004d845c0100d080d50098001c0210030031106080c2d4000d402070b0b9000b0f00036400892208070002d802a0f201c0d04240c1d110308005001c0d2041501e900032032000400c51103098038148503083c0120302c90300c1e5462192000942c0a41c1c00071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 692055224 1250 692053974 692053981
    0x2010309060911030715021b030a0c06030c110c0303070f021206011427041203060815041e0512030a11031003150b18060d1401020706180302190507090212 68
    0x3610f0001298402442c01821601d18086e154000c2140e500c0c0c042072100e80343e076204046000030704105440702c004141d035070120b5021607000c0d4103038010b010341ca15030703101c0e040e40303180251740b85540d05000015203038141d20400c210700000705542807941d001440940311410310b26a15410a00740503090304a03203e400302c000c00c03030003040c034015496a0300546034146c510000a512000000c442000500141c501180c1c02d032811a25442307a80030200401404040c1ea00e200031901d058007440c0000d41e0180d03422100c8890300008600c0118941081a9110000300301c02c111102000b6510f401c010050032115685204100b000090040218842d120b60012842c0860440c544024200c0e195413801302121303c0c2c8100301c0415110308a4420b410030800d1001c1c03d0582e5034400242c0510a8058018082c08504c80c003150f501c041500500b042c030784104402d01c007030042c0156400c080c5002c900c000d00141d100800126041c52030a8112541c2d0303000d501503d50490b01c03040b4007007d0f64440e01d0340701c88110010080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 692056474 1250 692055224 692055229
    0x1b020639040803121e06090f0c1c06080705030d0503150f2125030803042604031713030602031009110a09050d03020607080705040f0303080906060f1c02010309060911 73
    0x140540e480520b004044508040e00030800d40b01300104480c4400082c00d01250301d110b40030b02512190fa400030844c2c0ac02d480c480c00c1900c043d1034540f00350460fa110b081c2c0082114600842c03112008641599071034151b42c3c0c1c1400c0040b804100c2413041d50802c031807800594041c0c4170b405440079000c128101140031403090201075854410b404154440342000c0244003001c01005854207412030b074000d00c41c0c64403a255030911001d00c100381c034001001d1540f02030892569200f801d026004881c010340d2107030384200861560750000d200e141c1c04181c644501040c1840018a594059504140c50080200c0c07a65120a150811551307103090000c0b00d49400301d44a03180d180c0c080e11640c0038060540341742040981540c2c0181d80e4800181004041c41032040000342d4040c441e800f03032801040303042c01c0500c4a0f6504d041c0a004000103075114019805404d000400e203043c0006041040c0d2005440c1a8040d8038403500c1034a0200410380880c101500c070f0900d080807a0300380c040c07150803d024104074613062800d03208 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 692057724 1250 692056474 692056501
    0x100c0218180714060913150806070f0509041a040510080d02070e0c03090f0a0c030b2d07091e08071a120601050702041b02063904080312 60
    0x101c501580c0c0148010301c49080342500180c0342c0c510503140c0a4540703040c2000140210008014030700e481c0e2400300c824403240c05202000701100c40340f109031100c036100c0420448a00b512075245e4008544204000b550904241c0d021180c44d11a00c01c4c4100340745985000202695801c0d645a00380c07034642c60b000d1100b0038050044c049151180e000030701641e40340440f442e0099030003c148000809010000035400c40040c8441c01060200c801900c444401b64600110102e0701404265603150103200000d8400360903144400500c0401d00084014801c01c412151003140010680c808005540d100040c5a245028003070030080090b9095080d15070030140864904802e40c0d0142182400710340c802111048040101c44547e145034400c07400c1642c440e0016110381c424a07000075000340c039118401c603402d054410410001c000c59400d071009512508100c8801500b1145d503130002e2000d1400c5c01e41a01d407405004840752400b00ba0903402d05030380e00708903405c58003d941d0488005040c1c1080180c0b075040d200b0f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 692058974 1250 692057724 692057761
    0x5182706011a0706020307030c0e12060f04020d02030d0203030a0501050d151a03030a050c10021e0706140a0e06103f0f0516350d0c2609100c0218 64
    0xc0c2d41e0902c83d001c010100f42c2c1c4d80c3303024140344905c1074031710b01050940d01c4810007040074039005811a220301e82500002507a980c03040392801c15840c0f500c2d0010445150241e0050003003608800380c101e00508000905006050540500344e41444035022091039850500141c0755000c0640c41d400c0d01d440d00900020b0034049101110b10f0074500c100b02e5141c2c0b9503e940010803c20481d0039085885000768600000104210610000748641440410500e4501a04442085079408081da08036440c2c42c00074500f11440c6000e01940c0703220070610842c44400382035203441008000c90341700d48604a00d445071504c06004e0601601d6064481e0030550034040108280021046087d00c03a076013841c6440c1d400440011000b42c4401c03401c41030720030048290b00214a1450b64a99242a03801d28400440050826814200120780001c485120381c00200542c1952084904500f44a0791420500d58100041078816085250034030040601803070158551302c3c0d406d10805840104e09616080009002d0403002449 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 692060224 1250 692058974 692058979
    0xe0112020c0a0f17070b01230102062a03040501050f090613140c040e030310080313060e120105041109061c11040605182706011a0706020307030c0e 65
    0x100004060110001582900d103900110f10308003010a500e06000065a60034010700d407884081105802e01c204041d1541c101e68041208991680340c00280b4811103046002282c0540c10034000608580072030741000c3c1c40c0b0050843e002e68600e00003801c5607140d070010758054074140c2d5034504121200d03004030412070b0004c2541c402000c2c1858051340c14180d140804030001c06181c105441c82a003d0070822424100320402801480b0300c45041d408203a40750001c84105001d03401d452000200301c58040126240f03800040010203805041200680f081d05458004c0798203c2400b0784001042c030003c3c850b07180201c1c03041d9145101c1942c3c050030001c1800026103010f21072030030690703038100c0422030300140c6881c0c1d07500c52040c1c02500302c0d00740010001c0029900003500207500c0200d00e0000041202502d100e00f0310030030281800750001e100c1e00c46101c4510050522030780808014801c621040500005000b420b90382146003115a9031004166042502d075140420f46031190424050b401040c030f5082c046c800d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 692061474 1250 692060224 692060227
    0x11010c05030703140c1c1e0c1b08341d0c1e03040203070e0c0304060905030702130e0d0f09060804110603010e010906090b010c060c18060e011202 64
    0x5a86403503803648034030400141404280c0d540b080000d14050b0a50741d5178545041540c44585840c22200304201c1468100c1c40020300060501c441e0308041143e00200d200d031551a00c1000c405903444c1801c20400c00030f4540802c00c00e00c0d0010b2080800c0140c205504d25001041151805840703002e6070711501002d1204035801c01803018841c078080004000e51a807d02c40422150f40c46004030915140f29507420b41b0f1301403520310b010703590740e08140000794001c603c250204e44001d541d6079200d401e403030b106441c480d14024080000c1408103126800c45543c4030300610135a494401c2a60002d151020b0180032214616110802d43c104c6d09814440d40c1c41051503420005100404000003c00e0b0910900441c0c1c144138282000c2014054070030b00302d4262030006003c40ea52940c542164054a00c004d100d000d625605003100441d0402e45030203480010001038688c010074403c166203190181c200c1002200401c112035100e03200910030080701100902060300e40c400186484000100407941c80000e00e80034600 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 692062724 1250 692061474 692061497
    0x1e060e210a0309080301082a151c02120a0c0309030503220204020a020c0a1a0906070f0221011107020a051c060507090518040b0105190801181101 64
    0x8288a1081001021640e069880c09107520030741c0108a0007602078034195001c40003003002c06000401503184600e4541ca030144881c48641000f056900c0c080145d008500b44001c10801035507600905103940d50043c01e20000e454466030402260440401c24003154251001d105421219204e604103031040c0f07103011300c990191a100075040d440042e01820241c40e030361554040040640c07040305043c6078020002d6540d044170f014002e40d21791500018500c51404040c1c0040ca601505040c10702c51080c00c44442e003049603450400207150000c01c0c0580344a4000b0501000690740e072842481e00c8040c906a04140320100d841031800c4420512450603c140100405000350369005c010208607041182c030440d0f9000191030f10309005800400c0149200e0500043c840b07042c1d040010079040d030380b064808800099880b00030911503c0c0903207000e001707419010018001400e26008070901c90140364540b00503140c1d1940400d08584640a031743d286140074403400300822046403180c141158003407814195002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 692063974 1250 692062724 692062753
    0x1b150703030c1b0515010806070c2018040501060f061205070509030115031205071a0601050c0601060201050712061805041b06020312090f030d0506032b0f050406020d1b1e060e 77
    0x180d405014005500520307103040d8609a2410080710442f02070180040d03080c0304164654054402d0703400711a00d5003042c0e0003003003d08040c200301c000c40d4030740c0e81d4a0b501200b00501200c01050080c4c164003c000e010072509030f00d41c509000345100100b03c84510240180b0303508183c1c41c40c154482240041180c1084120041200140c1c0181090078041014070f4a440d8200107032218410038000804074040c54000090854040d070000e84030351100d4691010007484600100221070060044a60a45a19810800401d1140c2c005940a4800e14041440b8002e5221020b50540700d58042d00c0113034070001c1c0c1c0a00d0000b102c15a660000c991500030f01c484000c008415489006450303000d21495075400005507a90b0301040303504c440300c0502031902c0e071000982100d0015402c100709800c7c0824140c05c20300507014071441c00c503401c8032015409400d1514480404580028070510401103050b2084500c101183d8503031000555080c0701c9080307a901345418501202030741c040c06050003181d0800d610552406 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 692065224 1250 692063974 692063987
    0x907090e010605090907080d08131b090608070f050307050307050d03050d06091a0307060f140c15040c06030209060403060525021b150703030c1b051501080607 70
    0x1140016400305814a414038103900401040c0c0c005903108420b9004e00004e8500400c00e413054400303003010340d03000f031000c1c0c0000d507840385050f0740038100c40d03248940c3d0760082aa901902c030411302c5030b4600280e140c3e40e00c414030790036211560400500c5030040e401c104803640d07080010f0002054140c014040191034800040d403656010300c24640107a4800c0001010903110300c04a42e00350000c150f041140c40e80703848000004240910064105040c4100b116180c1d01d80050501e049500554904000010f40c0f42c0403035000c04e0903001c440020350240b01800c1246000e02c40c2c3d40400c01c4564941d001480e00741004130b4003079682c1d801035050510401c2103021584920b8121400c0e2504094080f609449141002441405688070749415410000c0c5200741682e0229802c82c0d110441c1802a91805140c1c003041a101c4000c2d0185206110410031500000d010740c01c14110890981403182c032040002c070554117241c04e19681202c240d04803401d000f00b0070000d0b060079800b4102d0100180203602c0e1000018044 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 692066474 1250 692065224 692065229
    0xd0804031e120507030f03090b06010509150c010c02160605190c1e0204051503031905090d030e100f08040201182d1a1204020103060b0307050c070e0907 67
    0x111810080c5401c64400c000a48000e5554030018641041031826001040d44d00812011030015490003075000b0641e10901548084c2038001248210b982c0707a9400642d02544880d003016040040c0700445001512190701a00c5014603c01c0007007002c0d5003144000341000a8940c1480c00c20301821810300102d503100040d60050890021140e0451450301d0040d0382541451400803e029040710040448400c2400200010340c030030343d0140620f84540405038002940c0a04050701075000388010000c1c4064498603010f00041410310740e02d00b010210118058079070340001640410301d0600e0040c428104090064600d803207a2800203e001ca520000a1407a900070f40041d04000320001d41860011458050748018a00407004800740790000091808001c56012503401039120800005002c542c0808100020b1003021032540c5800e50700c55802e48680006482603041540e6400301103280031801000314010840c9403201c070348912850745224517040e40c5070044121881d006090005540c00003c51109 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 692067724 1250 692066474 692066483
    0xc12070f020a200406080c032503170a08070201050417030711101a0a08060f0c0c030403030507110f3102070305040e0f0112020d032f0c0d080403 64
    0x1640c91100108070b2901c005034a0142071010032051a1118050500d54400d82c880c080d01d0a11180c0c0c1c6d24400d850b2542454556a0340682041c1543d10100701000c031b111041e002e0442904100c141c483d04e0305200101c403d201154920381c00903036130884d00c0e04403031480e0b0b0003400c9100a02281c81c1c26030302c120182c8012500e00d042900040041940c05009611420001c0942d0044074510301d5046051307005800d8100d003040382d0a43c07250b44104507003007051900054030b503010000c1c0510303201e220906485d414000c142e60b40c03401090080d407e03551410f20040005500999805440d641603003020450142c9034046144582003d003011101612900129071080100c2d01c02010020f6500b03840302a03040e00c0ba150b11925910000e294000c1582013030141c010340d03c0303034401404140d590705190f500d250b8003802500702044c9008440e42c0145003011084600c6c5101c1d1070900600320400d80b031030b04c0d000c90b05540c0d510700c01c100301400c402681c0200800e0710b842d94200c800350312102403611140300b24440da000281 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 692068974 1250 692067724 692067737
    0xa03060c050c0105090d1202040f12150e070608090105150415080109150608070e0c2b090b061507020d03031407030903030b040b10030f0b0607050a06050c1207 70
    0x10203140140291090b0400040082c0950300c0d01103d00390311b13900ea100708a030105e1700c2c001d54010780d4138940c4240c41c1070f03030408510342000d02d003048101c004440440404403007040c941700c1f00c6c218581290080c0c00541d58040014411141402e0300903059150041100310503a1404080100c2d0000542c00980060001d0f2000030340b52880400c0d131543da00c216040000b8544c2420306801c02c104011002010816100070204102e075250300e13000f5203940c0075108104080e0060004140340c07050f610300500b040c140c1407000d00764a0398601e02c80b0020706404501103076440d507203500744020b01024108941d440b0307404851101003103042c980c010042d800360f104041c0c02a0391134280802018000c1c1d00401c51040c14149484940c9040040100580181042100024100400105c46003402c1c000c60703440031401010101d5001c1d003000100c0c01480e6000345880629194000d107003ca4070b54800620a16000360041c00411865080a40c140c8401400744182d501040000410007201d20400642040482c41c156 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 692070224 1250 692068974 692068991
    0x30f1e15011806080417460c05010c05090a1a13270c050706020c15010602030c061308120403020307020303030a0c0f020d050307110703050a050a031701050a0306 71
    0x100c0e0103000041440342c0d02c1c03009240104146822070545441180700d010020800c0034104c0d22001c1d580141c0041074810000c0c4411105403400441c01160b0000340d030f12200114201a007a0792030307403100c140a010080340d10203c1c0700c7c09000c428011100151000e04201c0d03d030262003804580042141d10034078461184030f152417885088071600325040c0d51703900f40903815002d0701d880c41c9041a8503281072814180c1417011080c10008158026802c001180c0d440741c5040081c90345407440a58041260444d8500451014042c804011420b40d0301071710007640216180c07100d10380c070946130900192034a142c1641c1000e00d00c0004030194220303035020010740380c1200c7c42c0e00c0764a01640b450040c440700a40c54000803040240cd0b802681c40207000941540d903500d10584074400990700c8502c6484114000303101040010486402221216940d01c2c0e4001111903150350b9450310703828100b440e80100c03402c0d0001481c010a0540c004407180c0e5254181e208085070307524101c0020f0811540d80710007400d03240c651910 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 692071474 1250 692070224 692070227
    0x80604090b06010e1903050d0914010503220b040b06121c031503050a08120a0c12230a140606040f050112022208100b0a0302090c040506040605030f1e1501 68
    0x105c1403401035120305142989900c0c129841d01141031154000900c441000a0b00c8855003640528030a0181c65682c610b45804444242000d080000c1c070035252072030070035540042e0f080e041452165005003d20032407800e10b407040003840d41016402c0f11043c1d10034511001c900444601c0031078003080a00303000032880c9a9162894a841d078a9002820314083c0310a4042807081c80c2d00141005040c0240e2111141c0e05c8c60f1060f000c0f642141180c500051a81c0601580d80c100c950040084c094441c8410300b580c12182082c45090901303e810140050300c9580c6030f1180d0101c8148140c011030119401404c2908047e0390711000300c6c40d4402c0c6410001060050041201c1a0341110131140300f40d01c0c14020000500d1200b40302d6203191089100c50700c51855404225801c512a0301c80b0b102e0b00074041c040c200d245408001044c40c3c0504001040c02080000103802e66038080140000c03c02505c6442c0c581c640742c03145c0515454024070f0344008040c608031003003801504241d02580803030721500383e40302101003900 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 692072724 1250 692071474 692071489
    0x201090b090a030804060809010f050118090c1a251a0c120c0c060603071a070204020d09051c080c03011e050301020c0a1b080a030c0f061506080604090b06010e 70
    0x1801840000070f0106e281584a20704034440c0c04030400070300c11401f050754541c04603442482448403482011880140a89080d04010501805414140521522002c44031028900c1f81220407054030001383c090b0031f01c1c41129081501d00c801c192541c0c00c003585501d030f401c0c001d030403200d40100c8450002c0000b040c007080c0070151403909921805203011440c0000318601980d0090141e0701c03a5118190002e030042c82c0001e0000300340c1c5c2c610560522215010000c000580e00a40400c07039005401b40078000c4041d0f03030ba2040750b6111f070046000f841d010300140e4031700800c1412561100e08101400c020000040c0003d003c8070f04403000c8400e20040181a02418194110300d500f20f59030550000410543d0b50f84002010a14a40111440800b0f041c0c800b40585804841d44140003440e00b100d555500864080d80f10748208170300810004180003100c0d942c0204031000e108180507036400d1900203020081d4004006c2d54000f805940420034800301d911070034185203006041d02e0400011100300300d041c1e1503804 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 692073974 1250 692072724 692072729
    0x42406030c0e0117120406050f07062a0915080604140406020a09060203090d0201050f0f03040b0412020d020a0209062d270c03040c120c0e070c0201090b090a 69
    0x65205249615644240c02c8404207108000d54110051421929404017140480c06100941c408601e441e14151081e0b0301c68015401c00d40c0012003d0040704042241400761007104580b0501349414100b052881090755415280800c0c1000313800d59050141405002051103d40c859042005159035040c2c00103001e0502d100c100181043c1500621040210503004ae00d4110225240d04080300d448500490b03130381c000c202d140d42d8062020f00c1c2d03038800f41d40600020480e03510118410303807800440c0040c2c80441d0348140c4080351614440b10800080c01500c00001208820a1002d0940191a004004c2da28015500c0281c400e00048021803070380d64178040e5034080343c8944a9000e03500e50300006000c241090020a103402a00a0844030b0314900060001d5039107022000e41122854039000d046400c0c5410007041154140001c081c082141c200300c0003400e10192040b01000101c5003001140844450701400c0202440848642403006030307000100d6005981d244000552507990980018008107a181d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 692075224 1250 692073974 692073983
    0x406020712030902010219020901050603150d050709150e04060c030e1015140105040b0c011e1e02040f05010c020f04020a02061012030e091b0d02040501110604240603 73
    0xa4202107000380d010307001203200358000d03026500100780da04004000510400e400940c4183c004005001c6860050f01131900001c0364405c09541d540704101013590001480c50507200e560001100f00401a01030044080c00443d036425104024034080324801c0480000d0001044540c07215a0310706c10521942c40024010700d4003045031824142c0201c800f0081403140341c0c1a41040d00c00c0004900c440256040ba1550301c010380d501464107180c10285100c40e0001c826040c11552075244204c0d00301c0284040c02958006040005543d2040214000510308100021918180148410442d030400003101404641c42801c01c0002c00c003841c40003501c500c5001c0c107030b683d200d4808142086d0803540000c1caa4800c2010036851000c2d1511034803c031511a0320080000c000a100742411401ca00b03045003029009070706807902044914918510f0511500981c0c0d906503c1540450300b0841d03981d0140321001010814005001d803401e2540343d6000741105400c0d01f11540c86040c103042400b2020781c1c0200000c5801 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 692076474 1250 692075224 692075243
    0x60d060b09011d0a0204060507120e031c080609010609180b090405010b0a0e0910091a09030c01150b030a0207081c0b01110c0a050f060c07170d1e030504060207 70
    0x140c6501d55108640d40c41002c0340700c00600f0000b50070420510865003aa642074a8090805009940701080b100b1602806020488410702800c820340702042001030060b07000b40e249111401c403420090011200400151003064103100412083e82c10900d00c0341a1106026400080800401c0f61030103029901000c07500a520001003105214040d44108450007044602540d41581c0f0344171048500300035240361030990441c036900506180140e004180b003c2c0714400742461081070b007209500c4494201c07079506040c1c000003075041d500d00d401c1c81241072004450380010300ca00d0500034004454000100800c3e0120390001da24828440031400ba201005940c80100c0103503400040d19102a0a00040c80b078089200114407204011011460a00c4290302130804407113246004100142c440aa4540ca900316000b000340b002010801d2248102600d140d01c4a210303071040c024801890100d40060040800c40680c0403000400ca00450b42b4400f45141d15010070940c0319414448004c0c4614000100b85194 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 692077724 1250 692076474 692076479
    0xe0901110408071d040b010b030601110a0b070801081911060c0a03030606031d030d09061d0a050c04020c070e09030f0412021305070c02090a181505070504050108060d060b0901 77
    0x100180c000c00344e401040c20711108401e4080500600b604c19503004003142d04000040c86810703a9000555401030052500298503601c1c1240542818070b581800c2d110030341b4150400199a401900305401005400c006281c0c00030040310840101d4400704008080c40c3d014070b0882e080355590320030344882c00140c00544550281901c1d0240003800240304c0c00000c2030801035080307c7c0304031080c43c0c02c09c03140d0964051071074143e0018051000300700421080ba000340c2e68400b01005642ca0303001d80e822598155004200e00202070400900e801c0686942c144070343d0040000790300002010401408032108848105041d44600340c201c0d040d40030b003804d1307405480004500001c2d90040c824180461500aa8496400b0854052110305843c022550440854942c11105005050403210141c0c41840d44078002041420340c0c105024981d40da59064440e42680241c040e10705800d0b110700783d00001241401441e1a14140001c2c0c55000000c200e6031103501f40108603418030109130420341a025006000d40010368 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 692078974 1250 692077724 692077739
    0x180503061612050402010507030309061d010f05130f290709060e0f300d02010903120c020c0904030507060f0e0d081012050f07030305070b13020a0e09011104 69
    0x100307901d078808006107490350580c0c14031405100f824016a0181d40d1140780448948080d8090b01d640030b001ca03002070391402c00b540d0600e901655014904542c6001040d13100c00c40381600291207000c0c0000010750640030000000800445108a050342e2041e00c1a201c80c8650003c18045050250b0350940d0f41c416a0400c0341e043d41c072000300700949081e80c80b01c2004410b01030074444100809110242c200c0c007451400c0d5164001445a0600d000e602100c1034a2000d1141c003031400c24001611150160791205061020560004200c1403180c4540808100d0809030400003545d8031042c062007409801550003141c1458440c1c0100c0f800650002001c0c8281809100c2d02401864a08845081409203036400e204d001c1c803402a29010b00080aa0b440003a814451002c424000f13000040329584620100282500024016200194000d132a440d8582c2c1c010304144041000081c003100101c19000340c8000180e072a020307100241e4103e40c41c15003e41c0d0f90b151480b0300410031a02800d06c403030b03808030300043d215 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 692080224 1250 692078974 692079001
    0x180a0f0503040f0e16031d01020d200f09090601030b06070308040203060703020f04090b1c060207020a090c050307030e0c0414091005060603160201090b0c03040b0c0307050a18050306 80
    0xb03e0142032102c2d40a0356500ba44400e41400780c988400384642c5407000c000d624485e41189000c980c510b081e150404494200180c2203078459201044c44a032600d408001068094104014401004050350710300392084900b10324620589540d00d02c0f600050000c119564460740c040410868060b00c44da58540a50801034641c207002c880c00c905ca0311481000602c450312074003c0e01c040e0b8180c03000803801d241c204241c0e04042d1940210303107900300c443c0e004044001c418030100c0c0c09138540140401a940d100c44c0c010f0241d10600c0d90400d40341c0702e040c050302d0319416504c14100c0f41d025805180005900e542c0841d20f0742030401d00950198403500740000401d484000d039007094003c01c001403c903181b070714141c80d0303100c2070b10400c07600e09a00140902c0015000035040300510807204c160304c00000d0008644c2d07245078070588151049903140d94040100010402403440036030300450080c00e80383c110300d040781c001442403141c0548070003040201a030300c940f030041651604000d40001825564145401003000005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 692081474 1250 692080224 692080229
    0x1021206030c03150c19051305060f030604050613110405031006080a0b0c0c010c0e040e010e030301050d21020606100906020a121b23070e180a0f050304 67
    0x100080840810114540040e1814000d400074020b0001e2419550080000302c2c001004402d500401300034a5148440551004002c1d0340c0039103a03d0344854403c001e02001c440540c21803400380e070b4108401010404d0f0310781540c0d031102e800c41d00814240d60301c40208050001c0a5000149913042c4122041814008000340003a03d03819422103c115010103009025203885104200082d0445071261010507407490481e980400e0010715146041c1130064018210b4204080d500006070120000d0800c038039180c02a858149240c800a20002054000c516124401807050500c60351507000c01a040002c800341c5802a0981c2121516031b401000d07201a448401c11a8080d100c1c4d4040d00d4080c14641c080e03a240320070780d825a03004103e0b00c00701d81d9503511242c1d9044803220070300517004204290307206050040f918081c410381e404030101c1030509800d0026030b80c424803074140d600044030034880c0f44003001d419a0310600b00b101e0780e0840e412400d1580e0038906d032160701a28040900b2221000d006000000b8800c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 692082724 1250 692081474 692081497
    0xf010f020415050301140d0812101403010515010305070903061814150a02180d151d0a1e050709050919050a030e0f0a270213121703090102 61
    0x154411100700403290f5202c24011500940122448081d007803c2510959000318801e624891030f015103204c2244c0031110441d500c404036034500b00180085860441c03107205101043e402409603080c902080c401c03881d1108003003410541d556001506c0244101c02c070000641e04480d08005042d5042007180007180300308000c0d940c0e00b50327030b0841c140c02100005080c00c2ca10101d0b001c1c1e1102d170310350f035001d04041d41c401e88a000a1529a0000340b1565551104942010b8441c40c10325000003189000141901c4031012102c1e240c03048589111002ea402065203000c03a6444040c510804203500781c010000700500001038045e01c41c4907404103e034010303944818040ca040500300d9100c500180c8016045e0745107004010300541000d41003038002405022010740307880000301291030390074812000c514000000e61100d440ca03071328070300500035181c03d10f8001c881c0303544a00800c0d031504811b1174244c0714101003840b8007007025016041c49800d0150700c42248651a03845071086542c1d052042805000c0d410001c1c8500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 692083974 1250 692082724 692082749
    0x206061915022d0d0e01030b040c050705060a0608070303110328110102070c05060903070302040c030207200105160c050a0902180102010501030b1305030403060903022103010e0412020f010f0204 85
    0x160a10004084520441e00401032502aa00602c05c50f0200341e24a03e06050585428a103203855959000d42600100150380c0c1988031072081c20140d24240000c4c1c005071b00170b03140c50414401c0240100b41401501e416003050f41041c10041d803514694407402e540d407800b0b4092110464100140c3e072048441c010b88680e00c03515118980704e549400c038030070b00c180180361500100b000c000c1820081e02910301014010190340c425541c030b4010030181d13a0007020905c0002d0340041e2600400050407000b1603010a4155408003000caa00c00281151003040c01903000200c151100f0010410526545000303414040c08028100c0c0d03980212502a420015020158803008001c20829504c14843e8a040b49d402156a440741c0d2210300134003451401405042c1ca00740000c001c0400402c249004122100f44640e0041c100ea84030f5144a00c06d505003665a0a1072207804c0004200000c5412406900a07070044200d03c2443c10000040c0e140c58150403250321310f0350174030201d0200e025040c0c2c098801c4514030000304 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 692085224 1250 692083974 692084023
    0x1270609080105090705132405011404081203090f01090807020405092a01020c0604031a061c020405060f3007031707021504090f0f020a020606191502 66
    0x2403d0700d034102c4208440b40d1204008001d41c0c034010801c40c0c0764039203c29000641c21030480003628920954241c1c00c0c0703d0f110b031180c2002596440842c66030350104a6959904080c1048205502d83c044804400700303210010020601300d980c00e005240c0d6109442c00204403a0302d40349401680358029210a034811850003002940795413001c00c40d00f08441e50185500c810018000040844401e0b41d00b06038114450038510015680307408000f803025501620074906010b40f85486803148140083c0554025a0012101c8400c44111580b00341e01c0d0340e0464002c1155610342000c03610003601c089034140e004102c9540c00001400498070240180400d04048401060003542c40341c1d40c41d401c0c80001e000203d1540c41c1c2c04000000005800005d1004050840707000b0200c40d410b101da04150458003841d0381d0354201c40c0b2418481c1c46003a151751450041507040c400c803030401a40340c0c1030041c030060140414100e0000700f80c11113140b20001e0084801480044009098000d40d5400600d8941e0711090460810 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 692086330 1106 692085224 692085239
    0x30f0d05040210030605061e0706050c030703060527090304170f0712020d110109030816060b0303090a15020703021f021b090c070201270609 62
    0x1240500781401000400c03030718040100306051610204020640f6220f00b07607081c4201d299080800c0c444044c0c4144801e2090130001400c545c5820708120501c074404020714061403c40c0e500300251600c520502001c0903168140300c0c1d03031007189110034903030325a4540f005512841800a403428030350390700e981300b5600c00003c060b00900c0d0000c0d07180d1091144104480c000238012805102900d020640101c1d10380003883c8005448044610b9141940ba4002c10070100116803119805030740d100c844c0e078040d100700f00c40c420031640302d81404400c050502d0000156055084014540744409142c021180c0c1d014000c11006000d41c042c4450000140e6202241c40400b0303e03c0240d141f10200b0f500d0b0009080071240304100100d030174200c0e4103112586644504540c0203200c45c0007070350390790007500050702d8490b4003091504041e112000000b0605400e404503c040b91515181c101d801502e4220 = true := by decide +kernel

theorem cover : BRFrame.Cov 691906474 692086330 := by
  have h0 := BRFrame.cov_init 691906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 691906474 ≤ n) (h2 : n < 692086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
