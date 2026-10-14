-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0259
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:48:12.300097+00:00
-- url     : https://prove2.me/submissions/6b4fa447-20ba-4081-8cb3-06b5e0298a12

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 46402881 ≤ n < 46582738 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 46404131 1250 46402881 46402907
    0x30409110d0606080601210b0a0f09050901060f050909010f150602070e0c0403020d1505010e01140102010605010e1903020607030f021009020102120306010201150e0610090f051908070303 82
    0x400205071110310444c0c3d880412039445000c0baa503003071001414025140ea152204010400c049500c010600100d202a4041d0344070001d0315040c1d84082c84401494021154015400700080144a04c0c0a20f000880c01c2d003441910300600009000c600d0202080d007160b42d20300600d010a10046a5418813080b202c491071003040c0042c041c4100215069024492450007518540b4199080500319003c0104004040001b02da00301a800241c00c441b614a01a650081c0440038180700302c0d41c50028109008034030699001d0442e4542207040c001c907a0071100d40459650103988201c00c1040180c3d0301004003a103508040e512450116002c0109039001d01c1141b0983d00a600360b03402a200d0310f9900080c1c95080f84000d0250b00504035000c1c519083e88051940b0900520012904c11080ca041502c0d82a03030781c0240040781007007020401181000a115000d4070503c1c6442d088040c50a0010810749407103000e580e10422240c0031900011446505030009005100140c030181603507450081c1900d400444 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 46405381 1250 46404131 46404157
    0x120a030507020d1e1b0603090b01090b0d240b061908090c040e030304061413060f0207020907020d0206012709020402090603070206060a050f030a0b04050715080907090509030a05070503040911 84
    0x1c400300311b0600c00e024840c0150b40c82000030740c2d0303642030032582006003818180860700000005480004180708501c5000d03948a4500c290030619111040d840640b450301d046503005100400c94000825400300070111042c6507031410941ea0f032212a88130742131090603020150b0003801c21007141d81000000c0b00031402580301d00d00c10031041d10032980b0602e55560813a540410a0002c0c0c010001041c500e402645074400c00c1c100041c5400701c0e42d0f00048089200356418401a40701400c0504520b404000301ca01508aa6126028806034183d6200e005c0400205c8584090303201c1c1842401c6483d00c0d010345002c110300600303540d00c92800920095903000b0444185202e03603048080000c050400300800801404060b0140c519104541c90300c84107c14041c000326014445e0440c00941d4200b8400451400b0040755280d1038203040444285140c0105900030010644ca03010030b0042e40c4c0f00000840d4503420032424020344a5041e428624114001c917844a0151410403031303111040c6040000600344107180311 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 46406631 1250 46405381 46405433
    0x305030108070f050607030509010c0c0909050105220f0206040e072312160c0203010501080a0501050906010806010e10090614010f02010e030409150504140402120a030507020d1e 78
    0x60b044801c03e0707002c0c8a241d030003000c10007210001c00d01ca60020074062506042188001c40c1075512010100300d60391000d450790b6038441000080000a000d826000038041020581002d01104400203d00d80b009004260000c1900c01d88110345428060f0381c001c00002410843e41d02c0e2258018003004845c211400d4640a807603032420802c01840705072801c120460455850340d684160f5035446a200703440c0c030102481841c00342c110060f5800d009203070181541c02c0191405040e00d00d407181c20365101515440594019600600808100048060444249440e41d0581c0c0d21401c3c0c81c40e4808541d234101d416402c0c1404408079104040c2c003103001000c0807c1e65040f80340d03180000b00b07d00301d07042e071401040c0d00d410030442088101c4954001c0c03070400240c0e039684020b46988100090440702c81e00e6020007a4050b6104100951a0028107801c010340c13004050714070f00d101e5540c010054400c0c01d034000d2081401401050600003000406034170a0590482204032949900300417000300d48081004803500080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 46407881 1250 46406631 46406639
    0x2100804021504030f030509130c020f0c0108090c0d1403160c1d062b0b010509010b0a0813030912030207030b18120d0b10050d0501090605031b040612030503010807 72
    0xc003c56040303942003104180052800d54040301d0f2640040c0e40c1942c849451240c2c3c440344503d500c40e418440c449a00180f04900c01c048445091000c0001507a050040000c04c103c02c001d000b00c2c1c0c0007156a030480c1d118480112a01d0a000900d000e40b400d000d6522003c0707401a09900e048a21080841c0507501e09102250703207540c802046441c0791004a0101c0c40880030031502e003821803552040d0a4580890148480c480e9000c0403184180310050f6054403494004001d1400c00b40c035082d01401d4089804c41c40e05810540c00790a0390001380050b0780c03145c0c0580001083c103120346001d0015085101d0060b450407042d0800035660500b42c08182d42803d000ca000c10301c0c1082a500d000401e044040c0608a84101030785d003001c440c0c002c4c1507040d040bc2d407502c20f80c070600e50381c0f030462949039003954440d41e4841d0400c0c40d4010441e0016040301d41c4e0175190002c1845999400150050303440e01103e070039201c440c00782e00880d000e4425688010060b4454401c0001059081009141070340d40140c1101d0005681b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 46409131 1250 46407881 46407919
    0xc0f150909050610030507050903030d0501050a05040204030201050a0c03050918040b0f01051806040219020706031401050d02040e16060507060f0507080103031206080a060f0c0804030909180210080402 88
    0x10f54116a100ba01d00b0300c2006114002c3d0805a4031002c103051190515180f103002c0303821640440a8090b240d50381d0001400180f0b00106280b000d0320042e0703001c604203419907001911520a111200c41803024501089040602c61750880368444801b0300351384030941c100c080708a00c44d0030580d4202c0d0656107903000950303a48890124941250340082003840803040c02c41d40c0c10001030005d170084c0d07009a000c00140550081c0f8a20400840c207a0364010f0851500c1d00600800315000030040419036941c2c840108403a9a400c20300004140d01104d00091001103003900c60b103045900400070310741907802000080d4064111002d0708146000c0c10080c40390103889100902212400c5a90b04041195440103202203031290641803401d501100340094444c0d140d031040e5142034000001120366a8071104c0c107802220175802101c40c02c0c26242010700b1503040c5946e01410301070240c010400516a980e01d0ba080c80101c1080300d0010310780107020080700b482114001004540200d400303900844003548144031101c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 46410381 1250 46409131 46409141
    0x10206130b0604020c01110301140102060f0c04060509040b0901080102130b0309120a050c010e0c01201b0301060504050a090c060504030305120612030c0a051b01020c06070c0f150909 80
    0x9401041d4154981c0c4040800000350007403010000389642c4d5a07240318000b62140010341c043e04420384520020702c10807000910380900103000c02c004e510110107110082e210b4006803400c0d5580f9003092507c9120b0f03d00810010a1803d1205611a61660002620140640c010038005a14404c0050816141c09894182e4481901c10304081c0d131005104070348040740300703014198002d4146001850058000ca105003510307503851040074680c0020007141100e60300b1809442e09840c002013801c1b04498069400c0ea00e86410b0090001190003031890158141d80070740c01500034110041003040701d424681494001085450821a400d617600788012510720702440030f40d411aa4580d881c0c5e85818690131664a9851021342803c0d000103d0b6005101800001d20141101c81400001040a84480e00700b01d8170b8030030085505820031107076015441d40ea903800b10b00d855a880007625900d9407414036290141c050b00c2d00740d102d1400020003113808940d032070945040c4001190075540d4021140c0d101d0350001c04540d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 46411631 1250 46410381 46410383
    0x1005120a020415030b010f050102010b0913022101110c070512100207020d0602120603100b060d05092b020c0a060c020f0a0302030d0329280b070308010501020613 71
    0x64040318148005207015003000e040e028488031548050360b0303a6921400f840400780c000c18440d1003c0300c428005540c0c2445021200c4804482d4003185040811448103000b281240c0a8003c00b94258420134030000c3c0365031070141c0000a0000c0100c140084071108040c0c0042039a40d0303050181103c00034042c6480c5010600009100011304110506403d1a800071740c442d40d000c81e0011031240c1454040358240c0b001c0c0c80c20004110008900307140c03000401d4144241c0c603154116042ca00b001c03401080c0c440c0c40581d03070b00031180800019561285c1c4001403406602d200200c04040e481e044141510b9012105081540802d400b00c58148500c181081140070741405200000780d00e40c1c5418002d46001041c41507451005013030010301d15140d80200c0e003080d07040c40300d14004c6615042c0d1150200803600b1500fa80300f240210441d0351a802000240d54044400c0012240c0300d80030b010000c94000880d0490010140d04000d95911045850080d1880600348641030142c0a0000001d40c40b501d51902b081c011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 46412881 1250 46411631 46411633
    0x6040303020c061303050613020111060c03060d03020c0915010f030b011b02040f0c051801172a03090709050603010504110907020a080c012a020601090c0c0b0f100512 73
    0x40c0c46520603c0611341004c5201c4280074801c0100001140b000c0c40240c0c002e0003200011001a01540000f5013050400c032030f0700403c3d501c07810801250310340220079030b03420000440701015000341c076040807454441c40c41c1009178441110000d200100c1c1c02e00d00700d06c0e0b20314000e80f0340c14589140b200d81079085a0a00325213a011401001480005403103088050014034402000001c0100492000f0000c440d42c5449800118800081c010340d00b50502241e00443d881c00d1800881c2c01d1021715001c80018000b40c01d05117180141b101d218014809001c0d80d01d141d007591001c0ca030700c80c50031068199032841a84100c00b07005141c1070216100c0c2c01c0601400c1c2c80341da04144180c9443c0082d00a01403d050f00800d02003c5000303401040e00040c40e00f0004010b0600703c00000f0800b4541c4050380c20700160420140a84004008030820b0810303004101141181d015400000b05210f10020036200007d211500401d20305605080041d5503001903469802824039249480b2025140d10034007491501025088040d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 46414131 1250 46412881 46412893
    0xf0402010503040c1815120804030209090f0303090303041b060e1002010e1e07050109030b190204030b0403020105090601060203030903270d0f03140301030b16140a18050604030302 79
    0x2550140000b580c0041c89000c62019496440c42e0200d0755800015085015607207441d01d0840d000b5a0030042d6015140701c6a604142d0082c945c0c2c0c00c486c80c441da20000340201d40610001e00d0202e0107000c81001080d03e032050781e0741e03841d00d07010b0309860f913004650865070f8003101c91a02c088125005250400d4496684444144c0c50202e410009050340c86100d41d01150b48174002140081024805014060003103c603440995003043c0000c2c1c100545030300304078104075000d48100003180000580c3d50f0401c071202d10985a5880f02880240a0311440c1c10180c0810901024041015130540c003240c0705e00100c20907560642d803a01d60498a902c400d88103026035500c01e0040c11400391000a006103502c203541342d41948031501c1004100031100203502551017001200059083c55040784001c941c20090491540c81c56040d59150840c4200c0a01070308840309503015085041c80c02038152413407400f000403100e500c60581c480300400c917520007190f0464110000b00c0015407400c0640640701581d0307154000e024 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 46415381 1250 46414131 46414133
    0x5090c1c11070807111e010206010e07050715060f06050403050607030b0f060a09080a0503030106080c030103021f020c041a12011806090206040314030912030c100c0e0a0b0306030607080f04 83
    0x55030003071541910820083d17080c2d0702c0d00b5910200701c00c2c81213105142c5501c1c032100060004e03040940c164010081540384104018410364400200c1e40c205501240001d88401544810402843c2c0303900326404100404002052141e08240a0170499110382c1c2200c2095464010403000d48801c1c0c0d242c6600030302d007568080094549030024240c4d00e075030703440c0c041d201b655544c80c15454408a0346050700c039a000040188425944541500d520041050f0032134595451540400e10303a18070449504c821201c5083d07072100c081d10a1040340c40500c0000c0041c0302c110481114201e16940c3c140401d4880e44003071180c080d00150600a0304d00314502403021030407030300944d210007001d00140001240d110318104804400228048922442545030f90015901d450282e014880385c480c500d40703041d100f039200748650019003400140d1114210100700c030106000c0b0100780180c0d10460021100c50340440c0d040008221f190350000918411007003241184c0858841e00003c3d075000c001a542d60203141c00c2000018 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 46416631 1250 46415381 46415393
    0x2803020603130501050f0405010c2d0509060703090609050409031b0204180503030402100804120e04110a021c050403020604060309020f041b0e0303030108070513020405090c1c1107 79
    0x503038055512450075000701000e0f076030701c1c0c2180d0040b900108503060480c14401805403d20482c0810403860401003600202d090080030003800500c130351000c2c40701c2c00101c0200644a00203032036080002038411501c8494610780036000c52254080d50340082c0011000003039034540303800349a8041c0d825841d418900d13100507600c0c048515603048142d0b00903440f1400800a840e910340140305d1140501c01654682c206403040090b001a100c52440800c400081404041580541c0ca4181c649041c1001c4030215854004600a0710901005001e90000458114000364010400d4012461050200700003443d000c1c106684500940c0000f940251307051100340b00060081e44003c0c0007500003000004400720390b8000130180d40f40c0030340e190403c542060b0100d00c2582c05c04218956008214065811076040c0f20080d5a43c0c0780a100342481105c081184902d03440703040e8100c071301601e0003528680b12071400b1403070150700f43d01103000700610019100070590100c4903407045a410015500d0060f160a4060702c0344 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 46417881 1250 46416631 46416637
    0x1101060b070201030b0a050a0b1b010204030308070e0307030c060c03141602090a110d02070311060603061f0302030a061b050c0307020906010e0a03150c030501080c011803140105040228030206 84
    0x40d1b41000d9100390118083d51865458001401c2d400c0641359594a081c011030010101c0c0c1c522040568010b0005200090308245840d40c4941245400c000c07442c2e00000007407503c1036652026028a81c015400b00e48140d21030005802d40e4029121081c44900d600486180c40c807034811070194042c02100c210700107140015016420021201c400300314180120148101544900e4903001103d50000c1c1c408200740d00000c00c2003c3c40d00b420702501c01450110702103603c0b44030081c05107084504041941c44400b61043c582000b554025049544040d000d1078010000c02d031094512040310700601c52410389501c1074041318188502c7c0e2002c1c5043c15090307402e00c003880b40c0c043d101c24103001007440e0154080c1c6629041100540c080c824002101e8607812031101202e0200103850101400c0500602101d00000740b40340c5118028a000d001d00c940e0400c0104603000c407604000e001465400c0884c0c01c03041c0540016000d203000311040000ca504c2d00483c092a82c0e0070445d11043d04418450410140c5800e8000d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 46419131 1250 46417881 46417901
    0xe0403090801020406120614090a020f071a07020c030303091216060212010e0703061d1b13030b1003050c01030c020f03040801020d0e010908030406020a0c020418031101060b07020103 80
    0x10034034a59031074801a5003607070000c0d004200000d5403580005490111406050010b00000c6040c3c186820320002061081600400700c10400740c00042d0300355807011000845640e00d821000300403550b0b040c1c1c0c40750302c0c401c503003909d83d9001846403902d10b080ba86800304c12030740204612030050625400b8150031900a0b04122080e001d50907800840f60040380f45400100407421000540d0115581425a26102480040d0503041018644001848102d02030541da045a10034043e030310741c142c0e5803c40d40c070040ca40d01c00490244e102021400c9490941000c01c9101034038401c603130b00c070450f954031041c401c0b00200500c40601a81e000c418940c40d154003a0340300c400d802d051841500e56024203c48590328690156000b581d0a80d400105250300008a1207096007001c0400c00900070b0080c2500c03041301500024001030002a4000790b103401041c043c030640645194050700500018640070f26214644000c035005801141000401903100c01040c80344000b81d60b10a4026070038130703001c0c1c0c004400404803880c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 46420381 1250 46419131 46419137
    0xf150e01020106030b040609050d08010621060f080304080c03030f0a030c0903020306010f06021b0609010f0309022d010c0203070b090103020d060905100803040b1c1b0201020306180103020306010e0403 88
    0x300031000c241c003185c00d00c0c8107a000b1040414020403d10b411450700c14100240420842180018010035074440b1074a809540900040301400c035082c0c140d00024075150748a4031061056440c001614200480900300715040c10040e24504000031050680320300c40d0381000e0411144c01c00c03c1c410464060b070301c4480c100d038035803429000d140c0d100d5012900d094001c0e00a04010b100359442005141c3e0304005803c24403030f0361105050400751090204415000d92010369042c40032000805810510a502144a80c0d40060140c0540541800c00140b200c4800c1351116082c1c51483d40250594090b103068194140d014005180440c82c0132441c01ca55045481c40a04140c0c0800002ea80390415025800150507561000501414420728100f000081c9500c034240b0b030f4000380010000000c1c0c000554402c1d00131050708145c4c00110311307064070040010283ea00070700c204501c0d0342c0c205030b40d0541c09184214015a8a64444001071110001004007403000035496444000184091400c140c42542c2042c803c2c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 46421631 1250 46420381 46420391
    0x90105060f1c0f0e19110303070c03290402030601060e04020f0409060609150504050907120f1e0b09040204020f0405030708030d0f0204080307260d0f05010f150e010201 74
    0x40761114555100d240c040380032038032100d00014412081c07154080d1007004c0b9006040700128104050700c04c43e2540d00180c55541d11411402d00c5850601c100c4040581c008201c04c01180c170703460800a090795101501c0100d000000a440c0c3c803e181c1038003a401141c009004101c0c5a28140d81218401c413003003002a00b250302404104032243c240c0024001900c00000007096990420b03500500b41131899100c06a030030a299035180380740c1d401c2300448040e10307010756401c100c9513603545054543d18156008501054541800201e80900e15404080a030050f000c200c05140e012242440c203984414003242d6201a03080c0201c0e00514bca0350040140240900c00c0e54241542c4500003410a0190f9002c0c1c2020f8000080981c8031101c41d1207035000d07500401504500313190901c1034841d568041e0050041c038074960907412600c020405403100450010705510a6941d1031f58042da10003808129400307021141c20040040b4440100010520035070340300c0c08021803525819001200d6100b1034401881c150b550750703 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 46422881 1250 46421631 46421647
    0x30d090305040b0d06050906010519080408070b0a020a021042030506191406010507020109090c1206050603060d0201080c0909070e100f120e0c030a060603150902090105060f 76
    0x24001428603402415000075160b4034002c1800751f1100700418241c10020100004070907480003c0340140c0758489480d1011140d80c3d07a01d821000e9116010010b0f1482860030100203880406030010b2850080c2a07007900c161350241c014400c192407022961031034512400080038031006028140c01c40300002c6401003194016034242a203901c205603081968a41c00c410104220150540d64084501ca02c440c01003003402e04880101d001c0c4d40c4c02030106810440c00250342c0c3d06583c880c882c400d000d01101d400c100480d1403400f0024000d02071070f070402c001d003e08200c400501c0307103400400c0e070340b140c10041d0404c011010954011100f141c0000c0c61200c00700000d0060720f42544884040c14402d85c20354850740900056401080b0030752a10024900030000d9401002030303040d91105030300255031107004d00030403803007441a00d0500302407200300502d0301481010b00000a1180c40c0c2c0001003207070b004040c910010120782d50404284d4544c03040c040d4000c180240100054100000140342600c1e03020b101c1400c203600 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 46424131 1250 46422881 46422899
    0x819080322020607030525020303090906030c030d03050601020f0307080f07020105040803030a050106031107020112050c04091a15030708240613031101030b030c0f120304060203030906060d0302030d09030504 91
    0x121130984c001040444c0e03440408182984440c0c800b1224400e0160440e0242d0009030f40e403144460b480d000b15035900c081130f6552403c100e4407030351480c01070684203041d40d000c1c0e0044c002c25040f9030796070042c03052a04581000d14040100c0c0c02e5247c01c6460f4500d003c82800d80040c09600082e012810003030b0401c4000ba07584800d1002d0b5020300801c0c00041015407400c800101034840c13810509048150800c83d441c0181e812044000c081c440990010901d0368403d000e050403402654040c1c0d07031250502c21302c0c4001c0307290034a00902c445806c41d80c400c00f000d651401c54510380800c03150040812492404600400c05100600c2e000e500c0000714146aa481c0501084c0550003c00d04481b030030001140c00e00411901d10900c1074400030a28040000420300310000359140d03503004000d40956030354a02038050b0b482d000803008805180703004590342c131a901c0030001e42d281c1c000c6601084a014103000309043e032824000b8a101b640c0c1550081d03041c450704e844a0350003045901c0d000c40600c981040300085800c0c1c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 46425381 1250 46424131 46424137
    0xe040807080c0c0109050411070308060f0d03050d0c0801030c0e06031c030209010f02010c020304060c0c0e01031202011802060702060a1e02010c020c24030411041508190803220206 79
    0x40d0182c05480881c1420300058007007640350b001244120304103d894600e054419094a0220303070103242c00b00340742e02da17a004504000c0c040c0c0e040707603003240c2904460024160400003d00700140c25403810050070003980c8040320801020301004104d1800c810b0108040b00c4c10442d803d8106400030140e8160541007502c95050707500080200010a4000c036900ca070707668120050010600781030009000b18440114025228811400b0350814070481d10224018461910136000241c084402c05410341d503100c0c03c040b004440c5d80b15820300150b0910b190010000c0e04a48038512035036010340200d0811456600700506900682c2203541040000001c04421120207580d80140d20886d4000150342144004000d00b4114190340341c0d07000f044204141e983c050701d0f1108480072405098070045d02c0e9262850402c0801c2c1c5140c002d65801030030991004400032014245108231907a1004480c2009820011180620341002d00902a10400d10010300d419810107149120422002821140290240d00040300d80e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 46426631 1250 46425381 46425397
    0x30c060f1409061006050a0c0c15090e10180c020c0406030c080f0619020714071d010e041502210103060608060c0408070603020a031e14130c0e04080708 67
    0x90092030902c250390070240705058001c0035059402c060942040000741007485119008001c100406d00b03070b0303400d21140c07140f2040a044e1a91b00d081c40055150401081b401c02402044410008880414103a505903042141120f640329581c00500300740c0d108020003043c950340450f040d40208a100c00d520f5445200d1000030714411015500e40394140200340b882c012440c0c0003c44a039004006101c03c1ca040742c9a4890719490401d00540e5540c2c4d54501205580003030b50305200c2c03038810100c02045000d000500c80c40d400300d444004120580c0d030b82d0300194590b50182d50143c12200e0a01441c10004020703002030684c416819200f600d03580c0c800000310035906090740142c03144d585d07942c41400700c0d800900c2481c0d00880c9001649080a042c096143d803900740794454001816030005010200500a40101d104000c0342012082e20202203030151000c3c110b2000c103408045840e03c0001d0401880341004646180c200142e03400580c107104d82d014408001500c04c0c0d80390a0309011680008007120300502101c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 46427881 1250 46426631 46426661
    0x60e0403081b090306040b0a0905070608010617071b050c060a030e010b1008011e09050a0c1205070509040f02070503031603050c030601080c0306040b030304230604080703030c060f 79
    0x145400b502070b84a8408092400070035001c200076010140e940040c0964116401c59005910398482c0e012110080c113417400014180e020b110800a40c0580100a090403a0440d403182c03080012814030202011000b101c0d940d021442081080410301e405010791f4900e10f1042049644600c0a5000134500e0f810250601d0002034031940d40d005422000c3c011b0081c20002924140005140030b01e01411400d01401030801b1440c038091110118841270f640302004144540701003101e8182140e001d4080c0030740c2d05001002c600b80e240e6508020b426823140c51300c07c041350b6988605045c09070701084094084100300c00030581c0c0078880311000c580240005d600480f114841950400c0b03c0d205d014041d46c2c001400b2620016044c000c111560740c1010903c1c0d0702c5542c42410b15666540e460001c1c000f0404104515098400400d01041040301e0703400c1d220324151252001c94009080030104040f40c0b14034001d15031707260850602080081d00460902040b6841124085a840544030001041b41c1c8110940c81c0300c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 46429131 1250 46427881 46427897
    0xc03010513030e030c010f080405150c030a0e06062803120804050d03050f0601030c0c0507170f0109080703050c03070f05010207020109150903020f010203042c010f030f080d060e0403 80
    0x30150041d200c3c1010090540c06131058145c07030800a401b10740f4800c3d4280900110300c0024042040900024085104000510701c06040030341041ea2a90400c4038480081e03032a00c0c10005845c1c40c005029803141c10006e0140ca001c815004015041c41410412510318442c1c01c40044005950002d030070354a0921a40c542e416031034076041040c500351640c0d54082c2031502d4034042c0102d0310051801103511032803c6c00c0108404101c03407000ca800e001c05140103400d5004001012400401081450802d11100000c4450090024240b10f003210304c0104000c0000c2c5040203d8000a4050000b501380700404205690804070305444201c0c0300384002100301e43e80d07540082c0c0a4210f60b0131001942c0600312107500c55041080550000d4107000c800c0c040a8491800048001c0050380300700119000f902044840801040b000c007042541240011040c801040030b410000c29180c50200c903800890f81c22001c07031401e103109500c038058650720409a00050703540703a0a000c40c110142001103402988260b82d82c1074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 46430381 1250 46429131 46429133
    0xd030f26060a05060c030a0e0a08060a0903030b010314010e0a0b030303070c020312040b030604090809060d0204030606150215130f050f070911040303050306030a020301051e0601020d0504060507050c03010513 91
    0x4801078054100703511407841882141d203020000001d940d85100325048c614650800300c000544a100141e20405d400c0c0b01d03031010004504aa60008198030303120391824020f28500d0780042d801e84103180e0207081ca001c600c400400c5810380d0007070b104e81c000c601d220340055600000300100e030452307000700c60300c0c804603103800711400031400c08000e101250307a6400303c441c1c1007505000301d0100510026080701c2c81079840e09007503002d0180201c2100c442e1701d030061029039940710072248080a50402d100070f540e2503141400014483c0b402d148450036202959019113096008400c4074100401e002c2c040b1801c1041500006001910300c0100d01c440c00d00940042400f1001415a42c2c0340c2200c9800c400c401da820f00c15040d0101c40c8200c2500e05407076060415a849a50343c0c1c0210f0318010f2036040107035142d800c0030148002036002081ca00d210080300d6080c42010303500c050059131303100b00810010b400601c0812041000a124002030903c20740301e0000e03120303c0c502c6040024252042070300c100c0607030028050080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 46431631 1250 46430381 46430389
    0x303080907050a030807150501060905030c04051e07091d01090c0f050a0e010c170306130209090112020609040c11010b0d0b06010f2a11030303060d030f2606 69
    0x9540049054010460142418003107814041c0c00c1c4001400d40401088080811201405951490f07050410810541d0380d58400140711401d81d12503240280a03100020245041c14025103200c3c0d110103d1080b102083d9004d0408900d10042141c401c0120b005000700d6101c0c0d55900801141081c9079115900d541412403030000c84403801d0b0903105011501c3d00c01c008064010301a01e002c0311060815846051401005a070440600c460040640742811020a00740d0060805103000310700071b4405460701c841003a10b00e01203101d083c03c1540c0c00380c1400010444031406c00e50400e102032001e0126424243c4100118041e00c03100d01460700464182c0d07040c041241f5091041c80a010003c540078410625036484214a84002400b018100500107100c08400c60103241c42e0810000101c0140d550345001000c139103103000f1520400c4801d8580c0401d019424600002030720b0203080003e10260716440c0540c1d040e580c014482400505001e403011080400c800258000520100100800080b5245c044208 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 46432881 1250 46431631 46431647
    0x605090f030604170d060f15030c05070b010302040b011403070801081b0904110415030f0605010b0304111011012a0305011d0c0f04080c010305090f0a080d0204080703030503010303 79
    0x4207000782c0c0b1030390070400441c0c880000b110800c818040070030b40e078200e01031200026080c80e810806062610200000e00350071121102c181550342a41e0400091324039400840d07c40c40f0b028000b0b0035100c03100e130043c40546050b0348548910401414902d064401a010110f404c0d00205c0d04040402c02150042009207803d05c0b0480c9240120340000c140010b51000248520078094005000301c1d079480100300e010307120741c0d101444003190210003160032541ca02e0504401b000b00d481c2126100e062a0002070500064025130740565402001c00d041e914903c0c00780110380c01e55400d0907041102150501031a002c080c802d2030001540f96140e040c07000500e0b0418a401d001c81c0203004101031a100040085810103ca4004207a817900381c0c040117a180e441006106000e408246006c4010001d400221410001110030411600382ca040c400e507695540070035284c40d918118940030344c020500d1100001c100000400110841c18001401c1c00e44420b046450300d00380d908100c000c40c000000510916800c4545 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 46434131 1250 46432881 46432909
    0x40c0e150a0203070f020a0503030c0304031e0f02060901020a0204020c0f01050c07030e01140904050a050712110d09030c0b010f0305122505011d070f0617131704060509 74
    0x31440c01101d6000250750344592030020305031a242200010843d0380e807041820040c10010222602c48485404091316075109100460701c84400301d5824110f0201c2c481d013502181e4004e48030400d6a54944c0034813900d54044542c8074114050594020016503a034400341440442c2c0c100140740c41c80d04030900c1760859502a001c078514a00501524000075030105c81d00c5d112a02c02e01e05458403904041d40c50485001d2210f200350f1090a002c108010a01c1561066104441f256201d031260940b4500706011500c2c600c070071390440002040454081f010700d4011a021a2107032801c440700302d440c0e440f0388034180000e80250550000c41c010810510408000074851861454002ca103000c042500349c00700701c4011083d4480f403055149043d018400203600c00c09084801404000c0d11184181002c0c1d100d603124010f004071042e07816000700c1c50f207104007035029010030140040000c68a07010840c1c03043d41c2caa42001c035044c1e64840b40c41115907502c0c9000e40018038040e26210344a10300c03842004400c0d070170004e07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 46435381 1250 46434131 46434169
    0x8030c010c021b06090a03050307080316080402031e0a0f050303010e01050a0f0e0a02070f0507150c0308310303020a1407021f05130f05120606101d040c0e 68
    0x1074030141050003908844102804441d41a659407480c004105081b20581c0b028010780008510b40062141000045100344202907148024403220380080c0d40b4140700780d40c042d41584c8101000075101c0059040d0340d5060340030f035045940f41042a9501c0c45009240742045071260404001005644614440e29000d840b00f00c0700c3c249140d04051140d003101d1102e104140c804112f820124a0200203507045503d6544c20a411045a81560800300c0e03480c0950301c03441c0b450480042004070f17154850b11030b4002d065030681e28040c1d50740350301c40090850102405215181004080c5d0710000401c01010f8102051003174a016842c0c07820481c014007248503004c0c045403041c9040000c040141e40701540d000c920003032003400440e00c44a8500407503540c0583c81410440c031001e814045100c0050800390303011600101c40030807598011176070345130700e400301500c02c1c40d00030300800403000905014070980d04d0000b221280d26500301d0640c100141c150703000ca54803400868070082c906080c2d4201440b41c1100314000c09 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 46436631 1250 46435381 46435393
    0x201111308061b0a0f090504020d020c06220314040b040e0906060d0b0402091302030709021b010c1713060f0b01020c01020d020705060f0c010504050607180f061202120108030c010c02 80
    0xd54207120f5032044084000070070914480c0b50010a004240c402c0240c000070300f046441d5280310301c2e487d0084d4850800b00c00548100341c0040e800d0010911484548408242c4800054050b40d5052340d14158043c0e8a5110700c07401e21020540c40700b0440540028028400e00d0100750801040321030034036a0242c42c56000f0080841410013040341d00313962580095054440480300c0d510451551000d8101d284001e5260055150004500c54260060024122030485207115881c5512115080f614022102030224620f403c012101d58004820203920425050150b6002c8a05940d00e1003240c4c111007c0001d100e6540c441050304c0c0d40c0c1085504041c0c0c2081c00140301200d074400000c0e40e142c1d0f941c403a16100e410001020341c0900c2141041c0c441c4018800028041c0d401e192801c940c503000201c0d071b428000343d540c102202020480281c007000b00e441d82d42550108604184045640e0840c102d80300c10760940030052020301d00001c904450003081c0d00001307503840d4860540b2050950310f0031075045c0c2c210341c008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 46437881 1250 46436631 46436671
    0x10f0906090e070c020d08030703060b18060304080c010615091e1a04090203090106062705040504021c2a0e01051e0a0f0e0601050a050316020111130806 67
    0x5039008040d0741c04451442e8070b035070350380d5400c850100607a00c000350080b10422a560410903000043e5010344042c1e01c0901089459030804165401010b00640c05d800d000d4030000d0060610b14001c1d41c10038040c408440c0f5080310107445500303441c02d07030b03003c5010303403100d0040100d0f001d40c0000c0000251900744400c001c5000d054038110b0b444259802040c0005081c0351709044121100c1d01200d004250b2041d0954891a00c465840d0003881644201004141200f40030203281c1d6422554081400758001483c200b281018107000082000410480e044400a01d0041d0002c14001d00110703510300c144002010b50481c1c00d6120301d0401c04c403121410030721103403200340070a50b41030540c90f0545005a40320201e520a002001c52159a04913801d50810851500030488182203003004c07050f902c00c075541160139110b080045881e4030408100c1c0000400600200d0300c10900011020a0101b040c40007041d078003a0500c0c1c154280d4080c40c0e580c494011110800c00141c9802c3c0100340e40071050f41c03a404142040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 46439131 1250 46437881 46437887
    0x703021005090303061210060f050405070c0209010308220806060102150601090303120906050c0c1902010909050405150915011a070807031403070c150b010905041a030604030201020405010f0906 85
    0x3c0039104911030030007020101c2c60000101f00c01c51060521020900085c0d0307944141000813241c900803203004506000003d50701c1d60184070141001940900752030050380ca1516107407800e4000c484c0c1050200c100501110119042c0404034000d09007003009480d05003030007000603103002041001c0b4540c50354800200a030603a0082c0740681200d425042c031003144110048450000c01c907016009040c02d241400780148644c07000c02030b1401600c40c1048800200101e55803410340041c0c0d2000034001800c1d44424442d40c2c14507040650033502c180205c070b01c0031030844007a1100c00c00c11503d01d61a6803103a6041843c004a05000b58018160700402500c461204c2059480c0761042d564041c145010000c1c0c0841010710403a201003000120011280e00c900345018010018802d5460036140c22544945000c07056110340704845903400161a00e010ba64072b00014800035005100520101c149181c0c1c6540e600e440c24005244501e04c217500051356031b81064005440389043c4004d5208001250380706000140d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 46440381 1250 46439131 46439137
    0x409141e0c0703020a08040602070509070309081e07020411030a150302030c040c050415020a0303050903030610120902040204090522030507060921020a03111609020901020703140307030210050903 86
    0x1003081c903581c1c0326241c0c2401d0b031809444420051038200c0000303001511603808200d01301039580c03c86100c641d94039517413811015207000143c0900180d00403c0001c440044038a0303200180c507001018581080820b400243c01c035000c0d00000a681440041001000545841401201c0c071201d4640c100903402e64022a50300c0401d03403603590050380d6403582c0c990541e00407019580145204040800c02d5090014000d4503100018011000b2900340b1020504200700071080c0e07071060801410b0b205032480e61440032074558a1b0210805521983c0d01a103c0240e1110f0000308040c001e0a4000f081d1424413020300381c8521406007250250080100fa807800280e401400c90b45820741000000c2949a45814080704d540140082d2507209a040382074a0141900401d04c00241406034603002100c8c9c1071141183e44840000c12082c0c45d10031854802d000d51400341c5d0207800b000c8410b00c1224003103922035486500048541c1c510025607030011951408041e410060804041030300c0009201c54103142000702c1e9240 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 46441631 1250 46440381 46440391
    0x10615021b01090302030703080c010b04020712081f0608100504050c030408090301060b0301031101120605010e210313030606050103090312050a11030a0e1504050303180106030501020409141e 84
    0x40103500c804001a84903d0581001c1c50b0010150b0348415038170301d0509200e503c1806603101d154240352000d85503150074400d4a000980001e00303003d0034012128200d48040c0006c06e900340311000000b180c411a4011460310001d03080c29142c180c4581405e103c030507a0170001c0da2003288100e05000421030072469100650b50010780c42490710b42c0310002000040d016000702d8114403410a004000002031241d10000240c03000d20a0301c480600c00d410700a00701c25102c01e40695400300300d9121606045003401c12950015014a6641c00d0749a0748207021942554005402107561104400b411b00c1441030070700c00d81e001081c0034242041150000d5a000d441c0346155110000c4165807640001e001042039006603075009082c1850580d07a20305080d48200504241c24841654423850fa404083d0060f00d6600750b015a421a00840c1980c4c0c2d03c0d030007000145924003040b0019500c2d140c0020009070240054009007813000408205840c11401c182018030008080150b064034182c0d4503e010161920803d4000d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 46442881 1250 46441631 46441663
    0x30708070303051e090409080409050a05040c05061602041104030213060608010306020c0a05073f021002070e040605190504110105090604030f0c08010c05070503041401200f01061502 80
    0x41c0c9104e408600e42401903603566900517081104200c20420580d0040c403e0303480c80b038810821a100d0150140031903004440007005881c080c001800360780340803005048200106102040d46003a142e01081c191180c0740f001c108100300204041c802c52420a540c0200d0b203030050300420049107840710007070003010184405032585900146030000384c2c0c000e02500980c2072f0810202e6940d9a41c44082c0740c070a180b014210324048258030140808540e00d03140100d8a034a9280b8820301c010340503002c005192110503071400547c0f05000d80064a1800d00554910440c081d9100140a10701a0702d800c05d590b181c0b16080014920346000c110019403014042e80c800c2c5001e1a01030303100d88000c80400e080c0e00c03540d04003030030001340b9003107100400104004070b05c140c4807600001e004202d0301032415951030007000340c020996001400240080c850751034800c2d4520105241050010264400300818003203880416245070300010a41c10f40c0a01c06d0040780e00070701182c2140c0b0a1808240d10003501d444450000c4018 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 46444131 1250 46442881 46442917
    0x60e09040f03050f0d021c0606020d050f1602130f0b090702030a030c180f03110907171005040507031b020304060903150b190305070b120708040201030f0e0c03070807030305 76
    0x30207901042901c400b411081811907440b121020960741d01c854201100b013102c4d0402d20041040762005c148800900403580f40c0780d09100c42d81003600341076003008064ec0c0400040302a0f440c0036070741d00d1034842490181d07000001390041d1004100c0c1c060390814020580541d01c62003d024585034000208d40403003406180010b602418104212111415540014428141007a010501c070361126042800c6900c280e05c40c2c02c8070100201805480b071800c941d5040881c490280501c2c02590450381c01c1d503c00780007514003401c662034900007021078506561020000b592741c0d0206001c81448525081c60b10018001541403518003000245000d203980401001c400d20004400e0010007160481100440c006200c3c00401c01d198903441507441c20f81c8000c2c2c0d4244220840011004580c1049130407504002c0301c00d000c90703950042c040c0c1d5003003000342040341055175441c0150031541ea40d105403244880c804014021484c2d0a40030540b4003180390700009802d4001501c1040001e800c04100d43e00c14075404c0701c0042c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 46445381 1250 46444131 46444147
    0x50607060603170909090f06011208090a0b0c010e061510200d0f0504030201050a05030403170901050a0605011e110709050109021201080114040209190213060e09040f0305 75
    0x10300199880140807070900c650f0b100d0421030080280512070004d0310400c0440c2d13124014aa0755802d1065024450303042103006201d1461158021460b190007400c039503192980308004a00203030841d52140f500350702d021581d070154140a0050240c803010783d1008044d00d042c20404580010040707000640b161803105084038005014220b080c1001c400100340b100c00c082d0f014425616200c0e403030044000034400c0c0d0010761026001d8800d0703405030303038041e522a13050200818040d5215030000d80107809104208180c2d00c589441042503900c22410034001003901c0c01c051240f2000e940294102d581800340ea08040c1c0c0000c600d01d059000319109078070349840200401c0301390b070342005402e422804000e4145000032500c90466001004410108141d06100e60b9880c05100d00301c035216110100009041e00214001d0b02e0130f002d4158009120358441c80003803140400c91422a07100080c403034a000034410f001c001d010340094000c2e910741002d0b03036604031624080c1e60300031a1001c45030b002000d201340404d44c02 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 46446631 1250 46445381 46445393
    0x6030e0109050703080a02071e0902030c0c1902091501080402061e070f0b06010507152703030902091005090708040f020d14060105040608100519060b0a0801080a0c050607 75
    0x78440da038000b010b0300e05881d101d0070410380aa03c81a080b00242c451100c0c00242021068003040f00854000312010b8234501300541b030b80103984003820f00100700230244401007007010107201166041c8614801c03440c07641d9588c41808440d03c030080c0060240d1400181c1c0290070f0348c10004032940103a0450f00c0e2a81c42034918694054480c801e10301c0c807280440855000f04006101030b04806803400b403056024990389800c0110381c1803040714001440c81c038084918090240c516001042d0303030510704121f2800e410182a0904a8515002003a40043d4032280c81500758203002e421240c0000040036590101820720000c1040c082d0003524020410000704e00181c2171003a403400c01c0100c01d40c011b0090900380100c0c1408010314038030050138080d0340a0400000f0300b030f1829104880c05c40360100f015022044c07000d05000000d050052140740592140360349019000607610410f0041c003c11840c2588410002c1402046800140c0050f0741d56446003212001007000f40c007001e4101d62040740c00c10350721400c0d840c1013 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 46447881 1250 46446631 46446641
    0xb06070501050403080a0b0f0f0103020c070515040303081b040b070303090209040f110415060c0507081014180a080304080d2903070f0e040f050319090806040b0106030e01 75
    0x10300a9440d180074401010b42c40441d06010b1a859502400280507410400c50140c030480051507104000c580005440e500075001703041c042c0035400c00c0e1042140c0d1031f0041108210700c02c962080c81f00740041c01340304164000403101c1d001420368000140f408241c40c511041071099000341810510045000c1c810113100e03421504010b6405081483c160819140c1800458280e10045901c0b844001c04081203003000d10a131118449528070008056290032002e48203412203413002d44803802042c0000c01c645904200c119501d01c16614009040060003103448030b888409094130700600740c4119138820500c13000031040c041c1504640e040d0742d40d03103a503d02640d09110f0701452802d10340c2003428858550b1086680d01e0911540664031780502c00c00b031810103840300d009001e80801300001c0001888075005c7c1e0001c40f548680720764041714902c0b00035107036246107811450200705420070b444007501908d1b9002e940400100101c0c0c00030907d90a00d1340d00d51004403014054901050795480c15039401460075004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 46449131 1250 46447881 46447883
    0x40308040c0b0d0b180f0f1b1801030507050309060c0a0e100201060906050a0e0a0e0f06010806040c15020c0907091205070302150a0f0c03090504050c0d061401020705040b0607 77
    0x2115a6421000800f5006840a08807140c400c1054840e07940c0994a40b008aa2240f0f0035060822050765482c2104441c485015003805201c0b180b0746522440e44901000074844620a0080d00c0b00200800d00014181c179001000801040024410b200f01d41c840014495002188140f405494461a141c00c450203298442d0641d404801080b2000c04c03d070301035210a09458246105205064840341402001c7d5410b1159140c45d492a1000036940011580122210315110060f5144600200140c52902ca030a820580c01c50b000355050004000c0d051070500c000307105041c011903000c02c140c44042d484000c1c0c0d05805005030715030740c000f032440d52140d919000a0201c12942070308111060605540c0da0002d800f0882c003c5040d0802c2d003e00e060001c2c2a00e811003190b50725846c10816401007103580301030091085051002110001c0307026510381c007401c0d21461503650b2183d01c5040209820301601c2d616840280110342c00c495052147e6408104e01042d60000c0d50042507920032140811028891448 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 46450381 1250 46449131 46449149
    0x3120f090a08120907090203010b09010537111603060b0a090e010606110c0906130923011505090c0f1b0d09080607050d0504020d02040e010e0d0e0603040308040c 71
    0x160002160f40154541402078204d04110341040d41c03901c101c40200e100a000d1100850b005024603202e640c419001403004150300c000015816201040600000f00e0344020407102050440611410550085c0d00f0380080301001c00918000d101e07407500000ba03450071b00000d400c45858035810041c5444c0ca200d6400142105501040408800c08040c4d00921990180340f000540c5064030b4600e20780c0015040a203440001c0001c0240c1c0c481804018400350240c0001c02c1890722140c801020034560f00c0c8400214914004008420840030015400c40c0da6201e2422001c1c1d0840b03000340300648401c80c2407540801c0b18103c07182d54071203003110219540155161542c400c8505252002160008514014100000d03103a030300606841c1d00c2000e407a01d0003102e445002503c00c2c00038015080d204d4020507042030018000da80c20f01c210741c0100707040d20840904d040d0160344403e42e07800800800c02004200f5250792500c0700d4030428500020301140300140028003080a0000860148074116071101c0061400d80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 46451631 1250 46450381 46450387
    0x5060304021c12110f0a080409050702071707090f140f06040b030f010902030c0a06050d0b0109120b1504090b010e070e1f0306060509100c050c060f0301030c0803120f090a08 76
    0x1003801065134913000e98010960141200c44040d280000400089140e0320070403032801c00d41070102070342c02404020070510851107165400110441d040100f1302504008a000c1c18600d0b00341412201501e10344d0042c0c803445440d10440340c04090b44a020150400c03203681c2201226218140080c000c6c000c1d034400907074140030302c41c50001507100540c801e8034010f200354180d030741807100d100c100803030400c1c54410302010400401c410b03850800581d001d80c0e1390400c141042181c40d03840c0e4641400e28a003030482240c8010040d000c2c090544c81c881d00501c52004100d80a210801c45640c40892828041c1302e08060b0345000404610002d0007000d0404980304060000071203008a081c5100d034001140c43e00001080c13078141c011810b039200c0c00031100074900292054010300e143c040100d1300011012401d03905400b80365204442681e03034030700801b86103004030071a81d101d504504010300c05481c50f034072080762540700300101e2500e400d0583c81c85a0000805000704d1103607491881050a1044205008050403800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 46452881 1250 46451631 46451663
    0x60708150f062b05010e060d030309051c050319021305060d0f050c030412032a03060b0a021b040203040b0711030f0714010b010e010203090613050d05010902130605060304021c 77
    0x76031401c10f0069007120040c0443c0c0d0741c40305c000010305000d84a003034000c141004c8990101c0c2c007a4001e06005031155088070717515814225406000d03413050018900058002003404240070184004488540d58007000b11b2511500384c0080644440c240b00f42801a1000704000c017049603958002951185561014011880d109000b440c244d402120119003030307000403600c186154404d104078484c0c00141400d0a05800314810200c201201c011803d4041503160032000c1100603020000e460b480013036070024250001aa1404003110540694150196206208000125902a43d459000540b07402d25854a8880100e03c1c0e041d4403442c4010b40862078001104020065602c2c0d03a03403000c8030160000c10a078011140115034561075005094016841404038040c13514105000700250100b04180724002a994008584103550714402904c09941d02c00c031103015800c20410020312150140402c101c82c2d810000048c24601015001030300600d50406102c1040c10b18401500845400c10402031f030080d80c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 46454131 1250 46452881 46452937
    0x3030a030b06160602130608060d0803040206070c06080129040b030603030d06030f0204050c0c0705060a020307060615020105070219150605061201050a0609031104150b03100305060708150f06 84
    0x101301c041d0440d21021b00340010b0428445e0b201140214401420028111031984030750b045504043c0040c1d074009420402c2e08005211502100c003b0f040c1601da5030480d602d06110200c0501d406a00c11914000d50118445140a03c000322070640300c213001c995840740c403450301192941c002d04055401407803911001005001e00000c12090043c13084030244400c0c4d0781d07060b1030034440c017900700000200d5001032030510085c94001c0180c00344240601c1264145411522401c0607035456a101814050381455545103543c0c1c28010180d20402c1400103060080c0e00360564540e00304541d1024007c0c4080500403d034401140d040f075002010020416620f80036140040e550620080c071a0501c64030701820002122030050f0121001c032600140210070540440d0240301c0030346142c861044c01e070102014007150114901c0c0140d40240310010246866500f186006480d054014241005006403581013285011400341140001e00301a104801070b4031215010a20700e0003071484582002004c1c9000c91722000d8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 46455381 1250 46454131 46454137
    0x405090c0303071b061d010c02150a170a05061008060a030605071805090105030a06090f0204020403030f020c030c100c0303060f060c1502070c0e040816110301050f0603030a030b06160602 82
    0x11450080480a0b40d0b11790058420a0001c400b000d03000309050010501756000d1240c0804540c0007900303002c00f60f40140e5140900d64000c800c50f0011070401074141840118040250368040ca0403078040105d07040c1100010310b5014070306094410802d444000490340d848911010b030045507c804148030505003c400603085202c0340c441c44001c2c2040c0440007806241c0300c01a10704881020b0064566060903485810103040c05c030340c0964044240500f440c0068840b0310003403004500070358802c4480c00c44100c00904003002210010310ac2d40c40070ba030180b41c1d0b503205400d4080307003038003400d1503202c404240c036080c0d0207031151707a0201c000c00031000c0d0001030b2075400c014082c001074403411128250200c100e05040407800303091805010140182c10078000340e80c0e96800d84e0340250084d040b450401c105050340784017000d00184221000c11044010824504003400307940d812044007e44081b240c90081c010940c0ea0241300044010180c45064400e91030325910202c070034000c0d00b20180d5201005a061a40280d8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 46456631 1250 46455381 46455413
    0x30c091f0e15030105010f050607020d020603100509010e07020c01050c0a0204111308060112020609010908061510020316080306120709050103051903050f0d0b06030f0a06060e0d020405090c030307 86
    0xe008020544003030303d4184900d40c181d600e0545008500c1e820407080c89841d4200d01004c03600400c1407000e0101503a03410001d58810540c11410b070050504000a100840c1c40c1a802075840e0901d51041c0000e050b008155901586400e18005848503020840f10b8a0910181c00194110f480c040324504660708060041103044194125102083d540d880010742c0e80600348103400300d00d00c680000d5001441c2202c01807486210500d0704604454907000039030309107041903403011900c0201515044c0181444c0c00816503055240c000f8504160404044d180e0b4030252810040840c1000000a201036980d05001042500b00d0030854040c0d0751076050b80e0000340028003091701e140c4140100c03103424a40d003811211000390b00d80e40b598240b41074046030b80c01a403c0500340030161911443c2c40d12554491402561117070140444960b10340c20241325003402c44041340c1040080002d0191040c002c1e80b2600d0f800f151160b03065a00050b940e4a500d4040d003000e1520550607414000040c1d031034140540746580703030700d09 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 46457881 1250 46456631 46456651
    0x4120306091508160303091401140f091005091e060d06030f0506090a08120417070809010e030304060c02090c04120804060f021906050a09080c1005010f05030c091f0e 73
    0x100400422130820064800140040e11440c0148110410f030500c1400e491010f0400c4c0000c00400052406150401c0764410102ea10101c1c00c20101e240180148480080508100e8513246006d8086002103007130b0b594180c0c012498048038145a195130b01214480c84000c0e02c1000300d981c41e46032405803642c00290940715482000003040b02001c022861405184d84182c102e490030003410510000d0110080068070f059145138006407009140000900b502d40c41107a00325990070b008400035024001c81c40034a4080e900a00c402d0007515000314005d000e5640403254a100c82c1c1d10040000c20034801c5070824081d28134866140000c202000d400b070b00036110300d0380712034070300e0003d9030302c22a034403182e80440ca48001c00910300b10b4042542984001d4110841079000310f00b045007130b22041d6032640000c40d0500c2e20b900110400280c00f2061007028050a1359109410040b803070080003170b42c0c2c2e02c5c460384854410301010001c141031026105070246d20f20502c512695885585000440384c02208035030324015 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 46459131 1250 46457881 46457893
    0x5040e0a02090102060609040302160b070201031b0909020d020702061218030c100f0e06160201060501050906040902090d21091e06180509040b070f140304120306091508 74
    0x100c00440e0080e81e4090506074010011595200c00700072200c0006001601503000e0030242024024690519802402d007864015540e226244001001c80c1c0355400c070621281e024007403c082c05a840040314044035031038600540c550a04a01000091180ba14020340c810b030001458400200246480c034828480303003680301810303c9141e03075075526031044400d580c50f15001810504003a06440d80a460a464096400990440011000340c60581c00b0ba49106800e548441030700744850b03090140318060315080c0b03045810305000c580419154041c03401135154041e0045481491130f10744180308695503400603c1050680d021198101d41c1404544140d000600303880070102e11030182c15544502130540e00a1109124a068801c130340c481918840c02510360f01e40b1b60300145036510040114000ca0003256008080d0804d4203002d018000102c03109810b12443c40c0200c9084424641685d41c013580100503041000c0b9096022801070440741c010300f007603e04d4403002c1c03100001040c0c3c07010103540c952011140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 46460381 1250 46459131 46459141
    0x60402120a0507031b020d1b0f061a120c100513060306030b0a020301060c14010204090e0c030114040203030f0307030617060906221707050307120909020301140d0f06050705040e 78
    0x25410303005d4040d200250740f0008021402c0e92003071021111501e44e0007103010707002005607109070700f01108640030759000d500d504003e60761240b00042646c038244102d61034001c141205c0c540d680c40c0e8940310002c602c00d640581c1d02c00001c0e40030700222080046d6070500b504005403110b0b40034000b081140000d072885110b0038001907004070140700b224107a03a0203450b148c010036010350725100f00b100500d80c05d1003039540a22000840740750900688228000080141c159032250a0a03d82100d039605141030740d5000c80d006200244e1000305c101da00c4681241d000c92303a039581d00318098028140c0c1c0d520820ba0300c0c0f0820010010f101e070105810303028002010507508507488003540780011004a45d2101030003070ba502e60340000900d80491944c9200c0310301c000281480200d884050841c0c01c820000c0d50910140c11600710f01c181e0084035000030300040203003141154102040d08400e055106070060044880381c840806100f00700348183e88480d4040b80902c154504118000d0968000784100710800c20501e001c14 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 46461631 1250 46460381 46460411
    0x506090105011509051c0519050c0d1707110907080103110109032301110f040501020f03030c04091d070902090111190308130c030302010207020111030c0601030803060402120a050703 80
    0x80849010740d528003129085c81d080001200f04040c1c03841c1310000303224000c000100306001e0403d0b51160f807001541c0c00003540c10810b0800785102c5071544110610803031034002036130811403860608131007446c0340d44809080c913100c4040a51900c0c0258072494107400c201e0302c541d100041605a0f441a00c50000620030b0380010368400b00203001c020a0302010044c4900c6100009000107801d2032500c001040f032094107159001240e01621003285803001c0003034103210075601000203070589454403000350700e14904602480018007507400f40841e51030300c820507400c0141c8040401101449090b05a41440ea942c0d034898009500051445001c600c42da0380c0c030a0714107804520f61058401d00c204a0303000c6115550100c4d583c04004099440c07860441010754081041c0b0303008640074500c41d400050390707401c15000140101444064106290348204994441c03a20301041d014112a401a1500e407a81c85100c00607000e40200e01030030002d210f1791000c001207040c1030b03000f0750701403003480e1001c10060070411010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 46462881 1250 46461631 46461659
    0xb0402011b050727020c0c040b010c2103020409050f040303110a02030403060b060c030c01060810020306030c01120f0e0a020f090c0f0a030204030602040605070c0b1e0304050304030f050609010501 86
    0x42d00b02d8024000400440050990903c0d0004003400681032003900390041400301d0f0851032801e4010340c03000d0518125401c05101d01070030318200342414440c440440d070701c2c100010305041c84401c1c401c00d5114a142158040c1d015100a403141600502907840c1c02000181805005c4409600003800c00004400c03041204040710712051107503010318030302415070301c0700b1300500f1688440c503412a40400100740c004c84140301424400714450000303d50340c0d00d4801800c0c50545e540641b654201c0c810004d00c80166000102c4840419003820401e134003114002ca210000d1550219407411241490540800d48402213031507400184200da800e4044020203007882446281240c0c500c000c0d4008000c20500040d881003d002d00501c0c1c0c0ca4003525040d183da42d0a41640c102e07620040c00300740041008030030007070420101d02c0900074242c0424101a03800c43c000402c2c20444007102c07031248001011405201d0140700321405140c002003400c2020308a031402507681c650885401c5142c1d4030300000807602190110741 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 46464131 1250 46462881 46462883
    0x2070611190503090a12021b010212090f0316081f050402010512040f08070c23060a0302090105090402070803010815060306010b090120010203091203310c030b0402011b 74
    0xe4205400c81c820410388055001a1014505110f0340c0c08100008130a82007581c030500196016040e0f185020b4401107481d10480f41c02410354004940e00c0381f4440760302e03060f501500c10403180b11050003211008a401c0406a8100c8010388d502103101143c4108005100d1107440c0c8503102c4402c40311980c2000100722001035500900041082285490040310141d000381c01900440c10003001200640c0c41c00c00e103074401c0c4d1084484d085520020000100c0c04480c0c5d01d01c4044865484c0907910b43c0c0b60000302e00c0c1c403d80c49541c06040e8007140b0703414142d10641c1582c100311006401103698503224100001a50030034807170b6440901c1900e06099440e045045494010800070b00100201d9080003041440d80c6c012050301030400c5a607840259507103001d0840424060344403800140d40e414000c3c80541000d1100c0003c80000e1002c005000b5000300815100c01c4084600f01403460384d24943c007200012456818003c3c0c0b03184c0c0d40110100a200c2019600307401107100340c03551407407002100002101003a440340 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 46465381 1250 46464131 46464157
    0x30f032101050a090e071809030f0809060c0309030f040906030203070b0c0316081204060501031112070504050408090303030403080a0b04050112030e12070e0a0501211205040905010902070611 84
    0x10801011125401905c0d0003480d18080e5802c854513010044811102042a84412616a401d000502d500203282c0403c103480d524100c0702a24004410316a266005040c818100c41b00100049001744240152a01891072180d5282c2c0c541c2da588840c1c0c00340c001c3c4d0000f039200c1e00540400040a0003200110391034009070a01444c280401e24918200e02042c01c0c3d0143c441c1c0400300514051940070300901445103100703100c0010f007541182000480100f5000c0d040c1c0c0584581141c035207403401c0c00a105801c8bc0c104480204040c7d5a82c0781c0015240902c122517a00f42c44080284420503400a08031840351a03e41c10810000c80c000c030400c01620307420310981e80c0c514055020103002c24031618138402a01c0000c0c2540102031031034582c00c0d2620400350b03c102c0c982c1c049213003440030400d0300e40035140c01441c11894400340340d800042941e020361422800100b00303d40e800d0000142901600541d0001e10700c00c2800c01c51036075103490450107580622411108039241c003055030420007602042d40c088199080d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 46466631 1250 46465381 46465399
    0xa030303270213091b0e041106030c1605070e070f0206060301021e13170c010e06090102060c0d0e15011509061b02030708030309031201080a02060d020304030e030f03210105 76
    0x30309000003000001c3c4d094800c003004411407000c001003004d411000f032441c910003918520703143c01e1040c1c1807001c82d20442e110304010814805141ea0903005d07120716111940340041034540d0f0f440d045150807042d6004941d2105500100800070f900110a19016022902541c4c03c6079034000c100350807841850b910501042106001c3c4104d5250f500c083c101d0540c200102d0320651b0b848038100203030302c4004a6504110303440b00da043d00955900044861030503005558543c02d10380102c0c0042c0d2a035100070b102e080b021b480070840ca40b86840f2a045450210301001c186c1b00ca20036080300d0100910424050b946245010160848416100d00e803100c04603181d076076401c641d018000318603580c3e541c0e44c2103043c4d905204200380400c00000520042d402004480029a9a5410000e0f01201100c0c140e1104070650400000b001c05a2694022114041002d800059a9607a02d2505031a402071070302d04560107120311a441203600c00e00200910b684e04c1c0c61100b0780c400700320010008802d80f100340100c07070b0096060 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 46467881 1250 46466631 46466659
    0x10807031a060105070c0806070f03090507050913060212010f060f12020a020102070c1221080f060a09091104050a0e07050d03020102071a0a05070806012c0a0303032702 74
    0x704034a2500148140340941c60b00420b40c503001c1c5507600070303040030040307030000005d1101c40741c3c0210f0048104002818203100d4000961100ca4440b6001e01c1103034011000347c0300007003c00d007180751001850b540c4005d086403640000710030150701c034009020b1080140398845010038041d006140702e0302d0620060b681c00000c00b83d46070034800030f03420008860065640030f011900005203022255030241c8000c0580c109a910030b400c1624000c8030500040c04408440424120313020b81c00b400c0c2a07440095102d03400140d89503880851603805185d40620401840c001c14001006000480b001c80d4034030848003444a91140c660302400c98040840b00c2c00303e40d01a80d001c1185081c00302d4203015081c00307800010f0420a058440b2844901c0e1561000126015501003000f0a01d0354451290000154034000e4000d1400d400003a00f00c0484c411082c01168007102d2103000784000500b981e00501001d00380140c0550307a132034040c1c0a018283c096200500c100c03200c7c030307407011a40981d07414020b4001308686804254 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 46469131 1250 46467881 46467923
    0xa1d06040b0f0409030509030c0105040b310602010504020906190611010608030f0703170606121b0d09020a2102010f0302090a0b12060a0e010b0d06080f0303010e01080703 75
    0x20721006940003201c02040e4081540c680c0b10715502c481c0a503c07041da440c0d28000400d400c010102541030f05000b02070105004d003032100720550b08130030740501400052a40031b40458400c04075550700181c504071100c40c0490319590641000e0700851007a80c03601c405031100402c0081c0603030030214586420380d00a1013004083e00c110700001c0c0c40541040009a200c2c1c07201c11960540e0f0100361031071001600000e02504060740112003024105000704080c1c080e00382a4009202880344400400010810078046104000c0c041e41150b17642c48034005055941d0030b5900c985d07001d091110302c241d205012080340000d03d80551100508102e216981d444042d011a42c010340c1c3c030074018410482010360912800c0c201d40c03105240385000d4032041080c030740c9514100c07a900c6600030700144094012070140c13800304422250100c0301740c10350b0320080900e0b071030311028901c1400074041c540c89050345100340074032060761041c00b000850617541c1e44c3e841e03843e0613038031081600e0303590503c2c4c803005290300e100d00f03041118002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 46470381 1250 46469131 46469141
    0x60807030605031c0c0f03030c1202040b0306040c030f0e0106060314091908120103030801030213020a0c0303020901050708030f1807030b07030207021206070201050f0907120f03031d07050a1d0604 86
    0x84c07107080c01001e1824544030f1707940d0441c0c2c2c0e01003140860f40d290712602d5030640004a21640054080302940f906051041c03030303501804040c108a010b103407075452501d02d4500079080440c8414803460104a0340c0005c100040c041d201601c903c0300440d10300010994040003061001f8071820f4404006c202c20801c00c00e552040641d440015901d0b4201030004000086d4482c0441d402180650b803a41090350641c010440b4a00000502041d03032881000106110b07600709440500c819014103006894106500041c3c0d01d900c1000310082080d0030010811888581d24061103015100486801b84100c00a00c0760035540ca200d4000a031004104100049080e40300b50002c040d01c600c051f20200c7c09460315014186028802d031900400f50351204108410100036030352150340070001c44000c180c3d9600c1e0146105c95034556120240141040300f0b143c5080c14001d8106035942d1400900d01247c0c2256a0006500d80e0300a0242c2d600c50851050002214239400543c0f207072800c2e9200180340142c50790380402000301 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 46471631 1250 46470381 46470433
    0x9010e0c070807030804030305070503040308070806190b04090b0f0a09020913140a0f110426030307021605011701090905010905010c090509010b070309030308100315020406080703060503 82
    0x4108142800200390501503c09284283c03200c607098107151901500340c07070f8000d0050742000014010071000c264440c0c0d8650f082001c0d400d007000b994072400045505680c000700c408054101c2d18030300041010040d0b00600468410000810088900380108000d8038020418540c0c8041400c03014400c0440d04c0c0d0040c042810004d150742e44140701d00c480c0800340c2e8150039013449148224410858501e40c00d0042e03101852600e4010402c00c24400012900c0d4081c80c001d841444540441e001c0074060103411b10107100780c50900302c076101c1c034000c0e100941c1d6410103c0d0011f0960050400000c0d154002d04211000c070025040d010321984c04c0c007544200a0140000c16201d03036403500480e9001c54000e1040922840c403995031401014101400d0001c065010b07440f90500604c10801d140c04242d001311103405491b8149011111501c0f00151000100c0107500043c0c0740c180c1c81e0600449803600c80d0300600846406460700e2001c2d9454130300550444a26105143c0c054004441d0400c0c03414050b10000030b00d0f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 46472881 1250 46471631 46471651
    0x7051203070213050f090f030d09030201021608040501110f1009020d0b0106110c0111250f090204030b0c0c07030201050903120309010b04050603030304050c10210501060e0301090209010e 82
    0x8281e580000714680001c4100740030701c3c1d0740e4030b0030310005922102042d5402400c08004052170200d030010345549100d000800c09000b0341e0348a808040610030340407208281c2d406c881c007044c5500c0c0ea092403001c660040c421180802c0c0d0a680c1e416242d007001c01d500101c0c2e20424042d0807520720006540002d00940c0301e040f80c1c016002d034031000c00a41c150744554040e05060703a501500151503004c1518010b05811101e043c031100111842d403407500000c4181405104071030010395280c20041400c8a401542c105260070000c01c14041040d0030564003400c2241c1c000c807001140750710b81d09020140c521030300e401c2c81d41c5a01b02c2c001c1400594042c0000380300d006000b50450b41441124000303400755400c04c3d5000c003101c1c2d44035038040031986014000c01c0e4024504030080c43c55802e142d6036541e51402062035450107115442000c45420f0f0240444181c000000100c00d10322204030841100101400d002d4007010071030554000000381014820210303001c0c2e01900101240c0d0a00710342c0e50b16608024548605 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 46474131 1250 46472881 46472887
    0xe010e0109090c02010b0a09020f0423030a080904060e01030228050d050106030c08010b0901230d050606100801150503060d02040608061501080c040b0711040e150f04030207051203 79
    0x288241621071103150072041d0313000151003403002d003c00035812034a0b40040d804c540140b141c0c2e02d12071010301c202d400322502981812034114200c0801c14080824840169160142203500d10a00444100500e5454021a41004129224508044118030a000c042d400200410b1401035480424001d480c68100f02e209840e18582c0e1540028030050300d10381c0448159450b4102001040451842403000d0160308000b0322502500d400481c5803a501481003001032162440c200d580c44980314182100808080e10004201c1e000b401c0079030303403400d0503200f8038000c410009205107800d10680c0310301c3c16036402002c0000c070586169400ca400b608058200c0c1d90280381d100420f40165901d00c185402001e0500280c5290700d031040416079402101c0c020541481610000c010f51800300004483c1603c1588180b1516070346242000348121102a1505800610f040500880e4600000784d54170003011195018400d5521452081500e082c1924001c000d64031158050006192142054030312030f48910032079007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 46475381 1250 46474131 46474139
    0x30c05010e1f05130905070c03051b010f02070b100b030703091e050f0607050c03040b030c09130b040606030b0306060405060102030f0304030905090601030902010804120c050a0c1d070e010e0109 85
    0x1041028404901c011842c000341801c5202c0d6810f131400014402180f04200b00e242800d00034290182031040141001000265100d0302c441414512000300c3d0510000c105075400040d00d0780095021900642c0c0c0c034181e820010364048480c02d80f01e026200c003200181c2c00d6489041055002d01010704013103079043c028007040e001e454007185500128034005e0004095560b030012065041c00c2010304500100a8108540c4004e18400802c036400c541a0101441e80c9507204000910395010741041c0580c08480941750517103800700d0390000081683c0c211020800c140e5210401d07801c4a11200070703540c150b005200040d00d81e24050b4000e03a4060700c1070041ea807425040146d81c078269442154210302040c50f0003010300990600300911540200c01382020000611240c0018007038a074002d200518030740142d60b0080445100e8411401141da0000c11030300b20720010b1800000c2000607004030031055514560350820310410046403400f82189440b8203114180741e000440305a000000701034144425200005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 46476631 1250 46475381 46475419
    0x314090c040e070314030d0b090f010303080a0e030a0e040b0d020d0f02010c080a03020a093c050d0302060f0604050c0417011103040b060909071805180601060c061401030c05010e 78
    0x1280895481e000c6c5070b6640078042d854013220441c0400304e018002410801010f0607a060095054903054113044440b65a41070204000d00a00f40810300e40b8000410a50841a00888e1194113203500300c0d000c0c00500011428443d02d0150190040c2d445012076540c10041340365010f42e40030761401803504818800a549900046a12400c0000e000039800654803900c01ea1060001c0d0190494100c0c042c1c01210b1301d002407405c2222412010711181e80c504104540a48524610009090142001d031002600c1e0034043e407150011a00c054400403400c00240c542c0c6840e128a81c80b6680c40c0c295075041505020f0752008a421004001085650300d10203158440000b42c043c2d481548100900c04c210310f030050074002e03015000b400da4680d40e841340744140303c042100392024154140001c07000441c0c0c0d07540c9801000c2c62000d0910108140902030022404540c4500c284011714000c2d8028051020f1108c2102c02c800c209110140c1210542c41d000c4c040b03907214600035810301000401d5030030b60b00340c0c0003001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 46477881 1250 46476631 46476653
    0x5030105130b010603090209070807111c140702011403130209010902090f010216150c14070f0803090105030703020f0c0105010b04060e0102010501030515060102030714070302010314090c040e0703 86
    0x1410400e84038404400400c002c850080303024040510342403040d0f841c00d41c0840c9005002038028001c0c8040200028071861040e18030619403810101181c420701248a03031042c44034500301c000c800003490301d40840c0c0d107181c50307804641c0e04650603540c0015800700c40d0f0703810075181c1028207210420707440c0300407410144c0d80e0300030640e01a0826150040c2d40344401c0c81000700031145a241181550010300002a42002401c111821120103e0304580380c1e08000c441252400c04444000f054400111002c51910b00001b40a1050307034406000d007192261103951260f0f490040e015254000f54040000070324540c40303900070384072403200361211a0500040640d03841c25070720b098000d8980c4050202c0c3c100105548200c08007440c40b001e000822003941140c80701074541c05500030744400301401b440402c425901c200b04a4036119009065003c5242101107800c0d102c138003510040e170000f0704102c3d01c441551469007501303028031401d0000300030100c50a400e1201504c614441902079015400b00000403842c0030041c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 46479131 1250 46477881 46477891
    0x40c08060a02040603050f04020d0809010c0803090a0302160f140109090c030c080a0911060703050c0706030506030c090106300e010212010f0b040303050f04090911091501052205030105 81
    0x701680b514201840202290402424800803032046020301c000360700da1442801000380c000c03030b109a845650f8001a20994400b010080c00c60b8800810403203001408150814010f1103607082d00c0d600d5441110003102d0301c1c0240280c003a030b00403080c42041601c80c00c6003850900304060502c18090ae641c1c24410048580b80b20f012800b00fa02c0e0b46c00c1001c030310ba12421140d800000031800f001202c4180c0c0f500d0304225165052540136520000d20701082c18060025181000c4050b41115103082e02d910004004d0841038070014000e01c01c01600014902c1c20844081c181e503e240c2d201d1504030500d034000c411000c3c0888a40c404030880942c40d84c8800d403c1d000d15410300511000269444404105580030440141d100881c0034411a80c1480032203c0c0780102c0c3d04407909840c0c04c944680102c0c181c3c400c01c0c0f281d548507140e103e2a0400c19420440000d800640300700c0201c40c1a0b42d680c0d98034505080d81c1d08000e2440780043c00c1003201f0300b100282d005202c1d00e10000000240681901c400c0842c3c211601611 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 46480381 1250 46479131 46479151
    0x90b0a02030f07030606050702041503020405130312020a050304121211040e0a060b040501120204051e130b2803120206090d0c08030609130b04030503181b0603040c0806 74
    0x40001070803080224540100c82031a017000380e00d1034890010814050a40000d00c0759071540d280003000103a4803088009150010000c2205042241030804e00b6850300361b007200071846001501d88002414401c0e05c04640d802d0315203c0ca03543c0e1b1030360b812025400e081118014400f44c0700b1500e480d98a0b61080c007007000340780034095507103909101c02510700b41e00044c20b260b01e460404a00340484803070796044c3c03400c8900a0030705004e00000301001902900070341c1c20650b01b006d040f0500040b5481c1e00203650718011300560300100b115001600c61426150f01100c01c89c1c001c1c65070400010341c81d0400a0281c0c00600d050201d084440d00d035031b0f0701d0340080d0024580c480164003030707414002d10300014081402c603040581007034010040d0b541d8481240303020082410b48142000c00000303030904503c4482c0304032698044c140e010b0300c2c0350501c0c0142c40360f0801e071100c0e440d8241d00c02d54000c0111000072000100b0f100e1404290203403442c4c03010058558002002241c4400c0d070402e00248205003000654041d6803011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 46481631 1250 46480381 46480387
    0xc0a05070f05120d080702070312020109021005091f030b120106050909060709140a0308271905090604090b0f071d01081305010b100c0b0f011a0c01090b0a02 69
    0xc000019005154214900c1424408900da843d2a8000b40c4940001c5880c00d00c0d2101d80c1d00c0c140309900703241c1c495101910424041c0c0e0b110b244c2c1d582c10f61103080741c14802c480155000380c804000f21030b5805801040f54008190051501e010840042c04000d4441c42e40f8001c02c020a003103003c200c481000740520701c0d150b07450f09414021440d15a4a0a030321a07484030090044e85001140148020014070504501841c48404044a5100c21541002440d00221296650f800846028134808031202e9106000906e055565400f0300d000c3c2854040d500c80d401d8a80c400c68241010485c00d2100544010350041e516658000000d00285426102d00e20074180010189005140901800300c2a0030103800b071a50b15003450200d030b802c49901c40c0c01c07500ca405100090703025072501c28010b200b0140c000b075100717030303d04400314109a001403070000d92441404240ca0b140c83e4a003640204c2c0f2400e00459000c5c1c40700813514110000303002d001d000800080300020803600706607100c8541c28181551820707140c80d000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 46482881 1250 46481631 46481639
    0x3050c1e030a060b0906070b09030f0c0f0d0f0e0108060409060501030f06051515070c09021b0c030a05030a2703030e01080609040b01060c11090903040f0b09010503160201020c0a0507 80
    0x10740315000c01004d250440519101d032000005035144208900102481d403045c0201e00d031142c0400503242001603003441169a084603200c4d01c2d9680400c4089038140d4421100404e594031711941c0d1509205586850f1211407460500c0150b859a400500c0031360800e95504566000c5855030103a00d008600030b030f003020f01600d0141008429504014407142080520302e43e60810343d03c64042c1c1844001071440315a032904498a082056a0f20b00c3d03005c204c085001040d02d081d407208030b407030102407840f0010480d082081d0543c00d15483e101e00702d002808503001800b08284450041d40c924a00ca0324000784440b078668442000800307a219900300360000f45a5040300c00355940c209045a03040201101d50040074a00355071240040340050050404019807100904200440d00410844e081401840f4442518110480c1d039a2900140300381d285a404a200014446407408100c9410b9401a5901817861b510b10030154200c2458581140441d9420400c030384242406200540c40c0c1403056002d4420303e0300d8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 46484131 1250 46482881 46482901
    0x6030712090f14100504050a02010503061210150614041a0c030a020607110109020a0302010e0a03020312070b011a040605130504050711100c0206041b030f0308040b0f130303050c1e03 80
    0x81841d400c40103480c10f0144001f0907400613030324104541c2481e1032590780d07440d54041074040b400c600c1c0c1441d143c420607000862104a81d00a810b03030000014003041d0603607941c18200c07460826510051200c0c041040180700c807960801e424101d000880c1000ca10340920311310b00901e5075020306030384801a00420188084182c0c89410100000314410017480712a60b2034000580200c0d03d440000c0c140b10244200c2c0d880c0f9103814074440002c6030000c0c180d03a0b03099400d4020045a03800114121803c40ca10f0002056103003aa0f802d0640320300031907059600700350500c4030070748883d0300c50301d545c11201e0718084d4002155034460088510401a6507640300b85030484001c4149452406e0f201c0d1840e00d81011049070204d03500080c400c0c1c0c0182c1180b41680700c0c403403116003a00d440c0c92540000d0850031010b120720042c50741140030b9074019845503078443c0039655059100b41c126001603c0b41045214004a43e001092081c0c02c072540081680b010103142c00e89980c0a94180c1010302203048000f403002c0104040520 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 46485381 1250 46484131 46484143
    0x80309030606010302040e0a051009020a0816020d02070311030307060609090507050f060d050415050403080f0703090804060c0507150f03060b070c03020d060f05070302030114030c06030712090f14 86
    0x13824194100f5045c81a40c5030502002007180c90b2255a0306d000600b00c1c4c10303050a0700024000100110340e295480d510082503418100d80700d02c0741e0260740d0401603400388000360303403401c600b8160f0180c40b1a0781141d4540082900900c89079925120a01c1000c4c0491401d00c600401800f04003400991590031786480e034280b00c42c661020b4498103c2c2e010712081521404101c0c0d01303007400c1030300008241c2d5440c030381402d503030600f01c40e1124854588402c010405400070fa1950045041e03444544941c0e0324480d0072030613590383d00e000070030010050000300881c50140b004054014812010342c4c0c02d454680741c2c200c5100c0b01d01c40503880042c91004400300100c3e05481150040c0c081c190300c5501c4c0018940b1461410b01c150700c03000340074404007800001400300c01d031b219140041800005203d241440b08000b0081c0d0428040c1c07411451402c01040020710740026409019400075100d00c0c1103a480300300540341d110001c83c2c51890b050f11080e17454001408654412905881008045030944064100b203103811 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 46486631 1250 46485381 46485391
    0x190902130605091602120a1209030c03090801090c030b04110d0b0109060f15110f010903170603010902100f11030d02190206010b0d0c120f0e0c01050702090105120a020a0803090306 79
    0x82003141003040c2c0c29030110302003040c20303403c035006d980d110882e4104903160506848030054151070300280c24205544500b0b07084100b4003e40c1e8002c5840d8540f00d00c0c908a888010005002d01030f00c42d800c00c001540c003aa0b50341e0107805244880407980842d0040380f000d44c00980c08454108500300103120b1a44144610009401c00c4043e4102550900440028600314805034a00340071211201340813151007005071402001241c002444841030903e0040c6c4000e030710311041200080008000b44850070140700702e443c42e0390010004075000900742e1064908202113100d807820030007542041c100c1a94200020180592070b014011380e25003404500502e4600854031640854100c00300411410011006840c8103184038240001c1502c0f246505a03004d4004180300b03a04c080c24102c0041204005501501d0420000400d0303529442c8603100441e10b520078800002e43c0200d40000501003401c00780112405842c00070200d4945094680014100750141d50000c4840c1d440000d03451001d080501400e5044 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 46487881 1250 46486631 46486651
    0xc08010e030a140c01060f080f0c0913060b0402040f0b0304060501060e03060403180905090f0106080c061219090b0a1404080d050603010908040803090a0509090619090213060509 78
    0x3102c856030041c045071581c0c41c5071101a00100d5486101d034400c2d4841c40080c1001c8a0590010f603944c00c00948610300c004800c10980120383c82000c00307060444400d0700c2020900266401800e26603038000042c504100c41c40d805c0b83c3d003031001040c003d40b8003003031202a000100300c1c65120b251505d40f01081d200d05070014400c210701400129440d8600150070782e002503050800746041c3c0c40c07100b5070700100c81c100d502200003a4100300c18040d49407008916903080c2651500248680d80e02c4a290698072004213881c0c68008130f0401070750110200e070342411508401d9078a0010030403400400d0f00d8041e0f592810081c2c50041c1e03110b09110f014000ca10401c60080e500002000d8280b6290711740320000e00403460154402c513260000602e2541d820340c031040c0c0c0b0307980c0009401e444689a000a03aa280c1000240c24000d11103641c0208486c5045980640300b00c0a0f88003c014503503d0301c0310701280c0c80351406040200ba84440d4441c005a4500c4280b54503001c40f8040010742c03924001c100b091001000d440b04081c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 46489131 1250 46487881 46487887
    0x405010206040803041509110301050a060605030610020102160305040e010e0601050306060307031e050a1503050d0c0203031b42070e06031e01060f050301030f020604050405040c08010e03 82
    0xa9801240d040e034001e412204064803607840b0f0501040b200b0f01406c1c100c49451800f80c0b9002005184c05080000c0003054000700050b0303560100d40300441e0880c0c00341d4004a1418000a0308500d4040598100380c2000d10000d403c0c01c030a41312061031110800301c21070120748081418800c107806100300d50f00500e00401e00b520070f42862800030707040d40b1010f41058025400000024440340c0241c0107a0510008603a90a0042c5d5510f50004010582a600455502e040010111070140140811003d90b03070840b000c0d108081c00100706a03060303010460304a8040c00140901040d188020503d100300c803103440c01034918890740c14070906501e562042030394242c41100711312050101041c5401810004070701070950440c2c94034041902d400008241032030f07012800000300b1000c2403409041c2c000071303c4030180d400b581d40d0b00c9160a41c3d0400c480020400020020300c01003005c105001c0545a1041c0043d110500c1c0c5500e881c0850b0568808a80c10380300144103103800c12040c0001d00c6001080b8890002540c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 46490381 1250 46489131 46489139
    0x117010e1212060a05060d090201031b090521070902040504050f0717040303060503030703020c040c09152a05010507020709020405100311090d0f2105040b071109010902040e060604 79
    0x4075001c2d5040c414108414640080ca95484022440e005401c0007802280c0710b0000160007406010102005c030700003402e154400d090601c1c6920550120141c9450390000d0a00308000c0c06100c10262000c2c11a01c0100d20414101c4841030022401030f0001000160ba41c038180800d100a82e0401f5209403460086c038130420520550241c100c0030450840200c0c0101a01c0c7c9041c1200942030710b801081e0f040c000020000c1c00c068000407003101040b000c0d0340522905048907030035501e00384944105030002d800c0e684200205803140030442c8880d010b421440805541d54880c8154002c84c4117002c6410b07039503d0040c0000c56404218002c0100201d201c11340c681410071000c079404009510284080c1500d03000c180c1d0501c1d00c00d10589010b4100545140c5590f09141040b00c000649281d0544109403000c034110407401e000c10000202c04c1c516107446103810724140d4800780c20740c064007041c3d40d09869003c81c150b9507941c00030050b008201c002c00140c1c0383c90500d01c103211070003030241c00c0074860007007080100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 46491631 1250 46490381 46490413
    0x90304050607020d020a0302150c0f210703090305120304030314150607030201090209040f0b22020f030a0c06050a031118040b1c030314070e090613090501050117010e 73
    0x201440d905413004800c04181d48081099a0690303007000354090100c41c80d00c1140004540640140e038400b100321400205c2001200341c4680760051118203c0b00035000451b50481c1200050110764841c0c6080e080342c55407601d40302e040c8501841d1020b800c640020510040c940e260050704926400c441182c05c00382049010284c55000b80d50b056400303a00c020a0f030006060007940a041c075282c011f4440c1100d80350038134100c0800418000103e0311151444046016000d16a28031007905011404181e020002c036001c010030a084000300d140c1c540b0403000070800140000c02014010015501c1d229204c0d411214050107568541e071a00304008807e0180300316200720aa480c51041ca011f40c2d0000d40e04541001140c1054010001d41801d0f12540c1140360402d64594005441d60071250710f04640c948902c407040b42c0e1501c00b514115801401203020500d58a4800f0400401c59454000069148156075403e801d481c1c09130f2120107501003201c45103150400a0103507548000010020f0100b65161711806 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 46492881 1250 46491631 46491637
    0x609050702070306111c06030b0702160308070602071a0106020d02031342021009020907030c0e0a0905010e010f06020303011202060403020612100e06030a020603061306080d080903040506 82
    0x13605483d111003520283c501c20a04444d6442c01c0382e0304929480003078103018809400d80d1312040301c000d00303e82c0000b8051407011500780d40d130b609205065980d542c590740780c003044c0d03410905060310b00d60703820001d0320006004968000c408060102c651480c2d50f24025001e4280b816403040401590000c10101091a00e00480b203402c1d0b440201465612201c0002c40c040e54120064540000c032020056024a5038498244003e8404456080f55445810411000140e81c08644001c1d0401d25010201d01c540d0300076041150744030700d18941807008640403800611401c156621100500e5072783c10041c8108801ca40007203000d042800d040c6990b45291100095481c80305209028003015040d41460456991504640085400400c42c1d515403440c0e080300d03c90729030292120700c5c4000995900050180144184500c0380c50010060701d18454182c0031302000d40c1c0028011a4040e507800641d424514841c81403401500c4036400612202d07034444006880390202030200c00103135200380000c018a80c0c0e144e0032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 46494131 1250 46492881 46492883
    0x40b06070609051e0a0c060318030302211609090504050703030f02030f0f040905090a02061c0e0106080a020306100509010605090103021306021f1a04090c0801020c01020d06090507020703 82
    0x10000d030700c602e03504200d070400407004000307407880d992842180d021220000e26400000e00881e60790180711358400094080351404902c1d01010050a12900301090007a1b014041e00c0001e14170250004001c1120300d0782c0d41d07030200c03a82009085021920032907958031a03102c10140c000e841c0f0402c103900b096142c80341e07182041d100040400c1101c5030640c40680c401d00135100c20440340100f40d034882100190010711504a03000701401980b0700700000303030303241000520130003100e4026001c2858074050f9038682c210034504070b841c00f10494680d070300c106c0709010901c070342c60003400320301c1c0903100b84801481010b090001c00fa00181180140c014280050b0340c40005080c111507142c00c1030781d541c0c0d400c03100507000390007110120140706820300f0000848540218001d0028a400040d44c5000702d214401141140c1d4068400603000b52492138101841c10305910900d100c03400b0312403e9803100c5c0d13a46107040c2aa0b000280001a03139401150203c465441401418060b00b410030050140c0e1904d000000c0d903030741d02444 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 46495381 1250 46494131 46494143
    0x33180f1504020f0d140a0210020d0c06050709080316020102010605010503040b1317030403270b03060909190501060608010504060303080a0b040209040606110f0303090607030903050909071805040b0607 88
    0xb201501e5513a034980306101655114050404c40d10311018481e13214441d06200b40d02a4080c01000b6521602c08a101074201019440740e1301c09400f135846140003050002c0245040c440c0050001c50104000c0004d0003400c03420803103903403050481e80300090a48119912180c1406003c5c010320001071200c0d000242d0080c65000b20410040050503e82200c001242e6039091200c2c00000340001c0c1680001c03044040c4140881c800910300120284a010410718401c4d05a130300c6003440443e510b45404042c883c5c10191a404583e0600361005500c0324204bc9a0b00c11a051380d035400c0108019a08000f1a500400d82101d0401c1010b1442d2400303401150000d2148480d240d44800140d01562180d0648402c220040c0041280c991603280143c1580701155090080c1d01c1400407103000c1c044000100d92003100c0b960081d10481c0c50f1b000b02a00985803800044007800402d000d00c2c0015202e01d52154441c07840b903034550417007004007484030001c1d48451704620b005a0400301211416100d5408603501950f1002d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 46496631 1250 46495381 46495399
    0x708030114030d1202070519060213051c031107030c06020607020d0306152304090b01030b030f0706050f2214030601141311040329010833180f150402 66
    0x841c0c070500323001c003800c28050340312511401c080c180606503029140194801c10344120490f00c4000b0411302e94510320710805c01680e0f405101d0006445040c81c440703140c105104440016480f41d6840c180c0d0481500454016802501080049a410400501048a01c2c00c0820240b41800c820b8101034918031001c20a020401100034045031004804908112140f9400341d02c89844090800281100401c0b01d800039052461164491801080e00c80b0b1000480c0010841c175031a1010a03034090f00507004000c0c0c000c605014200076440c501d4031030495a1403d048006841c3d05160040c41184900301d0001d000e540401d006100744604190a514000d008a80095001c03048030300c10310103444503041d0b80d14541c2c1c0200c0c00004005120712000c1180e500d00c81c19030401080d0fa5402c1c02001000d10030719000f80c1c055892015400340580c1c14540c988420703100049007544603c0304000e420015a418071611003072604030140d45009005c6601d4034503e0300064003032402d00b5150030340742d0600940081c2c440e40444d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 46497881 1250 46496631 46496633
    0x3013b0d20010c030501060201060603020306030303010501140f190807022d0106030f06050a1103040b0601030c0e031c02070611030702130b0a06090e01060507020904030804050c060708030114030d120207 89
    0x21240384608154404000c2c044580f8460004000d80002c0c410308001d0b600b000b6002c1132246c060300a481c400d810103001141140e180030011600000d0325044a001c4840c2004442c207481c01c400e000b4004802c2c45034100b0044850160001e208e408010622802c54200e0040100d00c1d6481d11042d100103256111451214055604050f005002c40d83c0000d01da02c1440c51800104102904403d22403445404200500400071111090394402120002e0007100d144001441c1ca40c000d074884649640b65103800798510034800c1c0402e01e040400201070b24000c90b0580050305a41d41000740d40090419072414040e0754051342c100942e02c3c050361400031f114242c01c6003401003032080d40e407212613046002020340300143d0f65040007400c0100da900840802c260543c0c00440c0f402d00900403114540d03400751890039250389548048407202c0015004403035a00400c4456009036a801e409401d0082c042c006042c0e49515010305940c1c2100c20084040c002e401c40f0f03010200064002d050b909051aa03808013698480712 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 46499131 1250 46497881 46497917
    0x20309030304030c0c05190515070b0f040f06230601020106081518012a05040303090902130302060307051218120c03040b04030c140a03080d02070204060503013b0d 72
    0x986c1e0040c40d0480d860a04824007001c042105100f142c605491054584401645a044604c541c20001c1d10b0090b0030b4003c244810351007810107510600803502c08200d45150358814040e0b4540320100341c54540d400070110325030b0105410715038003d50240000c01010f4030308091039490321282d204100c00503814400090b01c4001044004005191080080140e198480c005102c52120380c6164040d088078407007003404060042048400b0b03660151100303902546071500490196200040034101d4640500b00000107840d0140514041d1015446044e100d5181690151010710010800250310501c51010300d07040304085010003e0f4560314a00c990b8400041c152140b07584110b5001d1070320400001400020f02c072120721507509a44402161608640e00070080188108132400007500f280401c021200d03400069a009001c0f40d0310181c0081109581e990029003198002542c0010030f5403612103d0408540700108021246180c0c5407900d408050714603029a1005103d00101c2405807203011303422140d030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 46500381 1250 46499131 46499153
    0xb0c19051c030e011407080a091e02190308030117070b070305070201021501030305030103120503160318020d060506041b02120a0c1401090b060a03050c0402090103020702062b020309030304030c 85
    0x148040007408134540c0e105d503030240c00000303c8010300043d83c2e031400700701040460f00030021400e801518851000e40c025064010308005211304981c04840c6403548041c5d0003007503849034011409180303a1502e80d890080c40c000d0000b04940b101440303400405080c411304140000380c40c10b4940501d0540c2c3c41c0e0f099840143e00c0d05172000501c401543c00040000209070344900110b0503240b1440c3d03582043c4e991400291038602080e90b100f1448003000a104840a1090344078004a61044940103020441500441c41c040c072100400d0381c410341c1320f0003001180d00382402226492200e00407c1000b02c5042240251620078000f181c0c2508500000d00d48000c070310801c08042e141d40c1004080c0c421400d8508068000c2c010b8110868580d155000007072140d1922814000459401801030106d15000302d0030000254051007001c0e05056080c0000c1c005a118070010f04030781d81030030080d0442003103100c2c0b4128041c2c41031020144030500410070000890300c084240ca8102c0c0d40360806540d0303200e803131034003141d01e02c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 46501631 1250 46500381 46500401
    0x201050f0d0b090a0e0c0103090b07111e030705070b03010e0106110106090218030706180b0c070806010602070602010b030a030c12111002091503060d080a03020c03040b0c19051c03 79
    0x560500306206030070381e02d9400303ea5002d0001003221b4040300d60b10019401d03035410204c0904001c68260001b4282b0340680f075075034111100941500c516803a6002244a100404080721215a2011551800f00a4200890313006411101a02410740d85030994104911105004000410100a004550141d000d4001030b01820751201d007552210ba04a00003103441286a07442c52280c41001000620345028252080c408204154007109240c109401c41d4910f40c042d001341c4a56100301350700003d030f0751030038401d05004c0c00541c0c0c007815070729203409002400d482041c01328030300c40d030841c1c840f4800281d0400c40040280394800805d8110812300b000c2511034034165103001c141c1d4000c100c095403441540d90b00400e51500700b20350705e071890b10750410a10f2181c001183c209810401c500519800f1648040c0500600c200529000d450b111266280134190b821540c04611003c0020411856041003804040c0a10082e181c0328580301005441742540c0c0c070045400710f1000024001240c2380203129420000c104 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 46502881 1250 46501631 46501639
    0x803160f050304030821010e0a0b010207091406090106020105070207120311060c09120601080a1e08070c030c08013812070303140a05030604110c010e010b01080a0204030201050f0d0b 80
    0x544e60b2400c3c5181e09a204031504010741c2001030200140d06603400d0f06c0ea0590707084030a041c10315600e00d031112000b4500d40c54014154890ba800c000b403440343d64041d4a4080d422000001c80e14100401480b060280c1038201c40150f904050030004039030350006208044a017240030a003070a44048c00c0c142c6034445511042140c0340605020042280396000051100710010384003805001061a4000d858400a000d2107001d6009100071501040d10b510443c840705040c2203602a0304021955910b21a03803010204482004a584040040c091080741d41001811795000a101c2408400031490058808003e804050071754050b4900350003111859041c130f000c0300508034100c040b260101c140d82d200f0072341c4000c500051843c44480c0345241c2120958503041d50315190710b03045031940c0c420000030744884460380c1480315050100e04e409140c01d000300c1d14585152000000d04110070390004244900003480d01c203410703004220820040c5d03404000c448171084a034074129203070700b580c1070780e480a0f0200c4140c45030300c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 46504131 1250 46502881 46502887
    0xa1a070303020409020d0e0d0504030302150c19030b0319030c140106090c020f0c010504120605040809040c080703051602150c1306020319030b060301031101020f030307020d08100803160f0503 84
    0x520380440d0b01644580203900d0460b8569001210300300d0301c40c40342f8007009005030410681100e544684140058102d40c80c1c0b0700f42410071031045444501032010010240009841e00c2542c031060800788402060f0303070802d0030024200052610050100380da110300c020710600c01209124440c007000e40c13003030028002c40c02d820300026a10500081d034a80290380b011030240140780c00c5410b40e40c002e030101c40494082034400480d2007280d48030b4000400006101b685c43c04c004100c0078505648504c03a40008080580f03e07a080e0742007241c00102100d20080c91200101d0300354190113002a00003409010300c12200c21003070350a03a00c01d00000b4013400b518140e40002c4074589008510182c000c400741076091002c2d04410740a50b508072045050310605811550070640400041c00883c50090600c001100d041c01111a50742c0f11001b03240c61940100c0c1c2c00720040e0000c1c2d8180703a80941c02000641c2000c00c1c584c620904a0802e400c0d10f80300c2c800d9140020b00d030b6010004a0b010030408842c3c4d600402c2d081415251 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 46505381 1250 46504131 46504147
    0x3050f0309040e0105011202060a020f01020d06031208010305031b0c1203070302120313020103090f020901090b01030606050c25030c1401110a0b0a02091801150e0a1a07030302040902 80
    0x258030703000a41400c0c03245007030512494940f54140318050481d040c60784c0d4180a82995028002c066111000550450107904801c507a4550b090000305043c0c0f0345e0310343c0050583e2541c00e1001000c1030b041d07945000c22040b9801003000c508000b0655000c0315040610043e100860140c0e503180c0074a800607543c1040a624002403a150040082c140c15402030702030f1414148596402d950701d1000704d8007100c40c2e254030301111002d540b01c2d43c07010302080e21940c09421030290313540001c0c0b2100c1090307020007199a2130b07441104c61540d00d030180700000c140d9420860705140703c0d002da1544403180350302d1180031134949902c690421090000c0d210021500301450f8005140c682e844c0d0072404c1c00030084103000c54080352656500010004000d07a80c04d400000304426920396481480c0030754012051701b544940b10890038045160b100d07084a00070300c1c480070003002058442002030509801503140520422410300d00700400811b100f1400311094503100700d82e5940140c4d00d0300350006d0107a40c009404c13191001c21210 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 46506631 1250 46505381 46505383
    0xf13060f03080c061003031b1a1503070603020703080c0c030f0706050f130201020307110a08012d02070b01030803060409080d05041401021804021c020f040303031a010806010509030703050f 83
    0x42c9031405400c4e070b412540e4580248030000a039201c001c0001d2640c50307044c1c2100b0700c2c0e45140710550b446808944c0302c19250744070044c100704003602c010f000c2c801400f401000301e2030100b03e840010f2105003801e5092245a4074041d1100724000d1100307180010003c0d03140b80a00041c012035010180001075241c4450031402e20600400d011a200311030b040c600340105040e4598a0600c000080e4164025880e14003181c0e0b503582501c0907030907003a4219039265408181e9280030700502c0c4503058015000449a84203402e14400e08a40601842680f0700c1000710380c0104080309440f074103581d0000e480c0c5035a40c90710004200107207400c0f130700034180380404261000420059041140900d0261a0301c020780301d0504216030803403040c6000761019928541d00c5d542582441e402600d108031851507180d80c075010b011000400c2c1d90003414403070043d10000405104060301031051103240d42e010304c200742c24094100006441d80c1d10240c1040d040c4400461803c000d40d03410008640916408400d907501082500d61003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 46507881 1250 46506631 46506637
    0x303090e010e06060a05090109081c080f0405070303051c0207060905010b0916030b011206030305041e0e06010507140a060204090b0405090d050310030b07020601170102090f13060f0308 81
    0x6608100300540c0001080d401240d20203004040080c141e914245c220002074581d5404a450305041c0f082040000030b6140b001c0c4504c0c02041012034103840c00d4031140303400a18220f4000d040c0301d82c282c0d11105001c045540040e0101c2983d6150400640d600000600701405500040c51403c4071707800001c10340c0c100241a00508542881a0300030f00034984c40703038100101030308205c075401ca141030580c5a03040c0c42c512030340101e0341d2a481810a8901d015803030300d00d0703010f03900950025400304400040402900000d1740c000c090145084961203202420510566600760002e4410f604003c008a1940103000040416140b08101030301211891700e00c03032900d9406500701e0b00c11101c1d89450070b40303d42550300b45405203d20440e54040584801d900d1a90141c440ba0405050300d4101048004007000045400a5850182d46550000d01140d031410f00d80c4060009000003500041c2d0040c0134011640c2c54a11410410200840d00a9003141d11035072504011300c030b83c4c1e1100940c0c441d22440082400046401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 46509131 1250 46507881 46507889
    0x302031305010e0f0405060f042301080a050601270c02060106080105040204050a0509040f05030d0b09070302040b090d020102030f0d1509060602060408030901060f030506070f1404030f02030106030b01030309 91
    0x503021620303601c00c01564070341d405110640d04030070314140000140c50244e11041d0b1242000b0051400c00a508010078111110b030300c07885200c07260058140120340b0010901900408100303000300310325500c55642d00d460300303010712441070a08580b1404081e80d80307602100b04400700d00000f0802404400d200000e40d110000c2c4904800300d45a04000b240e0750038107008407000d4420107004069240c0c500014000c4208000b00281c0b200d05a0084040000b002440200404910b482c00400c2090441c410020000005880c0c07006040c030400041110b081400c0564021502c01c0b44d18224900e03090005074117510800035403502103200020403c0d0000042c0c0c0c440361288207194803006485450716818022500e55000e45405640a82c00080c0050340c03210007107030b100b07146d0800410040ea07107080d80c4c03540071403641084030742c0c0c1c00090800c1525603000c0700f00300241c40c1a180034901161100791403c4540b190740006001c03111b54010034400c1d51002d40040d402150b00c00707045283c6680d40d040060299081e405 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 46510381 1250 46509131 46509157
    0x1060302100816020c0105180310020f130503060f04020f031203010f09110a08040b0403120501090203090105090105040c06110a08030a020c10090201051611030a05010e07060201110a030c11010504030203 89
    0x9943e10140e01c0002c052105074010b84505290040d117100d0310081030300d00f4001c0d69040c4144040780c02a0041c0c1d00183c004a0490b600c8036440f2003d0320750714180404c887e04441d00035800103040010a041d900075854100b0f4060b0baa00c0c6802c682000440d0801d1041c64030700310004030001c0009103c19460868004540c0200810040703411124001141031245400c842300103515000030074085402a004103400520909007401800c60859107201a65400d9000d201c0b400e90100030072204a00078014180e000802d0300c000c100303171b1406956050b040f082c140a80c0d41005803682c20200c003070104006241903107030840718550700e038075200341d007a006503010000c0702c81c0380e010703940c09007003180e18a004029a5070317130503103c1e0343c28104091841c910003440c412080e642040507009000382038034144448c00c2254040d400201b03804889170000752800055a002c02c1c11607241c84405840000340105503492401645800310307054141e98412104140d500981c00c41d95440c0005200802d90004000c0000c284008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 46511631 1250 46510381 46510411
    0x190602011a03030703050a0504030f06090b071e030c0509190302151c050703111303020406050a030209180a0c060210050109050f060415090f06170601060210020705010603021008 78
    0x20528444000d00d4070a064040e4420b201410009000782e0280901c4002d915085003000e540f41c469107100307070103528151001d50380c42c0d03214014000d204080c260b0161280c1041c001d07400300c4510740030f5942011011041010303540c0c500010354a100b00d0880c0e201d004000c11103000408102d054401007821480300701d10408803804000d051000b4002929a0f8044c090040e04140101600200c06004000e1485081655480c5107100e2954484082c00b03400100c0c3e020302c80d000f81188140421256030360000c41c85003802800804c010303614400c085500601d000c04a21704540c3c0c00300043c0c900000c282005014016001f00810800c1d0700081011506a103804244000e90369201c00d10200c91040d540401c215000030001440b03400c050f080341036041c061210b4502c030720396144549030807039200c80c00350a0003584070001000a021810031140140110070080c03c4154507102002e540c0d0010003500c600141e4000caa010140482035010800864018244070700400d03c0720340082000b442255901e840c21210 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 46512881 1250 46511631 46511651
    0xc0309040b010c0201080a110702060403151104080a1502160f03081003170a110601091d060105030a0b040809040c03020304020907111218130608060901020901050706051519060201 79
    0x20f00410704030a80c043e1102c03250380d01e0f0400040e0180901c0c00f40d001c00600c08000301c50040e21240e000384011405032000030041c0c1c02d107803038540035101d410001c101407103428042402404008201000c040d035006248608503e50449a000039014000c0c480b40d902500c1c851140903c1a62660f04202e24401d41d552821036443d5002e08000002034007000d404640e030107000c1d09001084c4001450b40e4032031404e01c840881c0d00d4103100d07450900260090710b00140ca1f20604400e01ca01203640c240403164410140c040c035070508000c00d542c4d00d800040540558088004101400b05131070454a40c0580900b09001058410030f0280195100340ca04901402420000800d211300c21008011700c4880c040181444400c07441600d41c8540080c548035401c02550316081d000740e40c0f0300d182844040282080400c1181c42c1402d03560078008002d020850340e90040080554681e0311404403484a68803440020b0681c0b1307007400402c1c181500c1c3c00c04039040a900314003140c07083c107a000207504489540e40203010321402 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 46514131 1250 46512881 46512887
    0xc0705100207030312060f060c0203030d050709050a09022106060d050702070501080112050c040e070807031103060c041404090303180b0603010f0209061204060e03040303030e0705010e0d021e060c0309040b01 91
    0xc47c0c49010003000a40c4003e02c02148100c02d680c83e0b01e40001e0840c1d0511500501c0c50003180d07001d941841c007107003010004111501300110444010f0040722021824404909240d003d004c1d061550040300000c21000243d0343c0c0c0d10001a2100e4010482d0200020300d8040d01c013950300c26480c0109030100b10404000210240e0158071036a9480e4440d0142034590000c100b484080d29407002c0902d25405100710126190104005010045000e0024180b01a040314249410210050040d0900f19410401403201c544c2410742d400080500b41c40000300d1000702d080480052250017144200c01e0000e8026205210281c0101d90007110114020031001c030054403000d04a104600030039030004424056614003018044030700341c0c494010351001c18144c01d1404401d056074042e80040340480d40e59402810f0401c007c121200c0030740000e086c1201c105081c0c01c00503201004903200207100f0103106c2110004100140c0e24403501040181003076032240c41070b007134640d12074001c0b9240b90300462526503403840540c8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 46515381 1250 46514131 46514141
    0x60702031305220b060f0a0c02131404080a020a06020d02180f030705060904140c0a0801050a060c390503010f1a0d05010b0d06020301030210081b0c0705100207030312 73
    0x1d03103d030386000ba0390381c1c80da40405007920200c1e081d80003c040c855107000004080062040c460b45a5410f00c02d29554810425001c0005449085191500302c0c3e1038136003251052100d070416002030486072141c0c19000101e16201d40c00700c008205c0d80c000704e4680d00351003068025155407030300009042c5881c1522018481c00b001c6000c00c0503071560011000300040d003842d03c020425040d000e84081040c220381d500300000b09400303a41c0034402200000d589402c940d1b12005003409800308072042100c1516041000f481049a944050541c0041c4000c0003030300078415a91031300550720030402e461780f54451609a07002101030b10445000754202010890410a280302d006d40c0a00001c4641d1020421403040c84a20102c0301e004035915966071641068036541ca600c48000c1a01ca4200943c1d80e6056205110521003070304845400d002900052000034800004d80701000e0b0032602075030f6160750a40d5840303403802d0055405250429407050001c24201da010452006890003500e40c0703070064842d401c030001110 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 46516631 1250 46515381 46515409
    0xc0c031b0503030109020a17070807180f0e0a02090907020d0909140705250b0a0605040c140c010908030109050a0608060c0909070c0b0f060102060601020c0607020d02060c060702031305 81
    0x81c000b0030050005d00355a6000d841003103401d242c4201c1000321000080f854a5040d108540030600c40d0b010084950341c8a446220100f5140301445407451408171801d90b4a1000e005200d00018040d00113880840d007030f41501c40e01900102180018101040042d440300080100580066103410010039011050700983c1040b40307488000e151203a96400e82180c054010b1494904a04041e12620000160320964064014010341d01c40101d800c001524204892440d40140c0c011810030480904581e04030038038407604c2241c12440c603070300d8508540260051050700c1008102c40703400b00022030f081c3c2e45079000b5881213042c8a0200303c004d407901c1003141d90301d004940c10800d180e802c0000748980d003808078001d80c11010904100c1510300b00d0341c1e21000c0410007141d8412050745007000f04002d96904005858200c0000c0c00a02030600c120400304420744038041c0083c2c01000752102c481c0031515900100c803031602d4460113403185030410ba03078020b48a84c400d51040d00e004041c6900810300c3e00c1c200f03002803941 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 46517881 1250 46516631 46516633
    0x507021e06150d05060106020304050333191406030705180106140d050a1a0418080304150504081809070c0312060512010f0f05040f03081305010c0c031b05 68
    0x640c0d10301000400d00e42d542078110340c000c2c414007000070010f102000124040c0c14260003842d01e6909040605103400000d0818900d02000700140031040f003203070181500465131040300c11b102990350f0080026815100c100c0100d9880c500503000a441c120f840c80c40f0302541e411401c1c1c5000310356132402c111030000d0401901d071240501c0c400401c07140d40115241d00d100010081c0303075403c10301070400d16000c845085494500e003c3d12043c0c403500c011102082c900580303004440c1008291345286842c502c1d003024030002401c0f904004003203001e010b84450012410003900300306029034039003483c00b80c810f900300b10354401d070003403001481d02c1440c038025055030b01c910a070741d8825007030408035201100d0f4202005c40c0e580030580d46807808101c1791100e45d440e08041001c0400030800e0030000d04c1c504201c8460180091440c2e24101c148000583c1d0282d4507050301c0d406152440b41a154511500d0042e01c10050007800340d0320345643d4000c2140c0100308200500d0294440f001048008540c00d0300408032400000c000e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 46519131 1250 46517881 46517893
    0x603070e070309051c1e05030c07020604080604030903050601080604030e0f040e0d0503011503020304020d030809030f07060c09080604020a030b180709050105030f0d0c02010c080c030d0507021e 85
    0x28048885040350340c8000a03140c0840c0001d210789a59090101204001882181d0307540c0322805160024000c8152100e030701c0c0502d06e024080714009045010141070302200d00c80018049055548520903140030740381d00003e941150610740740142202d903251000f00d541d03018900002074600300114503a440781e9090380300c40703850514000807c0500e4401490301039000780d4989011504903c104180114120180c84030f5660394101011540c20072805080c4004240c0104100001030300c511382a003007025818140000c4c6621404082400c40c05429140300c00841c011841c0c00c00e00c00799801500d100e2a0359114010000e440d82c018541b81c020031a0043c0d00505295001c00028824a400c5c5a200504c0c0010510541c912400d45082c0314130fa0740030a0150345c940005012924041c0920240c1c80001c030014120300b244102c01500f10029020064140b100150f101c005000d00c40007214a101e460b84d0949079a07101081000d002000c0a0f85c0100040c41401d905526140b070a484500d110800700d4003c002d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 46520381 1250 46519131 46519139
    0x206040b0135010b0a05030a020105070b041a070e0f0108070509090406060902070f050712031d03071809061d07050607060905030a02151f0510020f03030702010c1106060307 76
    0x220754400100e22031660000c1d5015150031102c85001455001003160012134402111010401d14549a80100388640c01030810800103030303004021030711103d900284c020b400f46c0c0c5900b03048400c03828448607640250f81c40d400300441c13250700200d42c01c0000c0044821007204020172004680c0303500201d4018000c10020040c03500545002500141d016228500104995495420540a076080a04103d840a443c000d0000030410700f1300c14000603000e4890403641c504081e40b4004c00c040002c0d591202ca101c144030b1007803022f48050000d100a05010f144040e10762400702440b000a040c465025942240b030030203040c500c281b100f01007100304888a802064240c0c1044200700c0b956105010441701e80341c0d10303100e03000044d5091000d00201c000d04d4000d0b1405505060f02d2a9010500804503000080106600b4003c142c80d440200203940064441607400c02a034003040c0e00d071114170303401c0140c01d11012080100d001d6054004c03600c46c0b000e5654810555904242c80c2d5502d050507250168181c1020f28180 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 46521631 1250 46520381 46520399
    0x13110d092a15030e011104090b030c0607050d050a0905093d0b0903030904060308040510030903080109050903070b0c0a0e040b0901030b1b03040305210601020c011101020714010c020d0206040b01 85
    0x85030f442080c130000990a403020b00e10100542c015482070540940707030340309241d070707481d0a0000c1c0c03a2610081e20090f03d40b01c0140c0d20281c41c4c1004182080030700c500425100302281c0308060100203450701030304484081c100800c010018142c855200c42425a420b10410203681403503114203e00341079110107641003400c0180c1005540c200c9040303070f40c041c0b0003070140300748550312402440c0c019400f81480700d56039810b01040c00303100b04007941444141410250700c40002907202c0102c0d4111082101d00003000d4580c5410b046c15803156240280c604d044440501c201d6000344002070050340c0c0c66440e55090354805105010a0f107811222013a031200100d0010008100d005040d076034031080d20400030304c0344a0003010341c3c40150810755058001810106802e04054075440e02e15154505070000342a282c540741000035990401040e10504000322440060003050702501580d02c0d070790b801780e4600200800c06944900070300c680003c03a001841181c248410507070000c01c006c0e0040390000d4411920f030303082c45904 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 46522881 1250 46521631 46521641
    0x200a06032003100302040501080a150c05040305010903110601050a1217090d06090201020106060e03030307031e14040203122706040b07030201050a060e0613110d092a1503 75
    0x1025925800020818000980d60000d5124118503d03c51500e5801c1d070040c40708680058000450700d134000310000022a4011301030492101e0300b18800300303a290070180100d4580c000c651008042d982024810b00130190040c0f1107042c02d01c0068102c1300300f680d230f0f0810840200b0803442101041c07104d12a0040204540044041c1078110b0380c0c21692401c03c801000c66118400c191007958001d0b60380310594110742c3d080c05040000c0019180c026144040c00c40029228400a86403005166950b070a502c46000c0c5005144404615100b00300400709070060080c60036181191308910a0040c100c1c0da06940341c40c001640c4401c11380303506041200ca000e043c1d0183c0d82c41d8284000c1c2c0d00c1041408002111440c030301c0102a544d11990002c00c06090500c594415074019420040720014000d0800ca011f480e4124150b0b40c40481030004a12010450f103011034a104448666900904004006051040f00076840d80c0156004082c01d205c0103452200506500650140380c0072024454143c1409620036008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 46524131 1250 46522881 46522901
    0x5010b010306180f09080f03070f090303050f0a0210050c0d1116260a09090b0a0311010f05070b09150f060117061207090f060605040509010b0c10050c07200a0603 71
    0x3e040c092511500607c2d04018100d8104190010412114644c07000342014080c02c20708280c0c202a0555030003074054020801c0c2800c3c008000310752822410310030810540d2603d01c804003004203041541110740c243d40a60010340d6424200840c9040e50201c1100300c4102040035205036222040329a034070911021142c40d140503400500d40880c5003021400000c040c524040e4981c40c040d146005842c0065500b01c91180d4481c00044000304003041c10940078681c214024a040310610340c0c0c0c2201510140601a40544406d80c201c0c108510204009910036200003852101c26a40d0350320040d0328100441240c1080c0041c500010f6031003001080c9100341e07008000203004501105070303a2202031821021354803861156848111131100042280705060151103603103031a600d040c1c28500419601001071250542036007000450b80c00c0500180401c00d40b03034000800c1400705041503114a807240d004482d080e07a032505440341a02441e8481e40d9035003a03601d0094910001a881c18400340e0040c145908 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 46525381 1250 46524131 46524161
    0x70c090c02030c060a050a11030708011514070605041a0c0a0e0d020d05010c0e0103111b030906030a0b010e0a030f0201111e15010f0807170c06120405010b01030618 72
    0x40f100820303c0610401d84960b49408000526103045440c40b420f45d45146d14240070351004000b4441e0f00f50348190f48a040d40c0d14014840d020002a1008035604400c000f03a20070100004140720003000001d0b00070741d00690041200070136130482006903d1030014280c0e00e00d50402001c0180b06c9842d4016160500c4850004080740348080c5281c01080a86c0d403010003c5800d0f9548807100c903203003604000c500107640401c0c642000285807900c0c1041d80e5108805481e42001c040503940c1c0d008440400843c0c50401014002d079440f810032040d504050642140317182d0220301100341042c010b00704002d14004a0ba04034040d8101484550010340f070040398040c40c4102406a10b041d5641200c04d04110742c0c00408120040a605036240c900800c840c10603003050f583c01030802810400440300151030b806a41c5d000b01d0308800c070300342c402c0305503e44130f00d841400e40c01c00e801041e404d007503200d1642002c1c403550040c0b0080c010141018011411220280184500a0310041114480c000c081d4843d08107410b11071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 46526631 1250 46525381 46525387
    0x14010315090f0609140f0a0e0a060504020a03170d0b040b180402130203010602030c010f0b03121b070905091e030d0218030102040e2e0504020a2d030c05070c090c0203 73
    0x1380c21350050701e000c10f80c03181012080406100c0100008201c95500507061035041003005010119540c0340e160280001d0079141e00c4202090542d650b610401c001107610079a2416803200700c6203895015080702646600c84d6140005102090034607008400d03914070024504485070070190036044010a024209a0300501005042070421f0590f00c002d41c0603007010340081d074407450520505400c0d038110700500305140f424000c1000042d100050490741d41075a10001ca0703101c4480b000c0016508101400130050f03807040000009034074485074040b9006443c1b900c26110b0620205940ea62071184a5200c0040b9600c20403241c0c55407241d03a4040c1c61403244c09400031015102c010300103401c0e0780258015801d04145201404034407400c9140054804110310b20607041920300e8900c210401c90309205060086800080e58414284a080803000d408160303400c0d10303d038480e03c0c03003150b0201c85524190b1010920740100d10078120701400564003410352101007035039107078249840480501a04400407080d88818 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 46527881 1250 46526631 46526639
    0x1a0a120b0403110c030f06010510050405060a03020306011103070614090d020706081b0304050312060a0b040b03040206210403091e05040903020f03030c0c070b090108061009080708060114010315090f06 88
    0x11b002c18190460410b00902c02c40d41000104800c02886105202c2800410441007040c4e0f290b8100344c51000d0003d0500580b46d80d0b0300310060b50001004440c41322240000250041000300d150300c600c2d400f00d0001e003000351650f901c1607440c0d55900c0710100540960b1000c00d081114500c20b802c02a40104060458240003640050b65007840e0001c1d07c04a41c10780000c180c2d013540070102c0000c503500220496845511610b0210042100c0c0f089001d902010540040010195142c0c101140e03000c0a1101c1850100d00c254a5040c001d03240685048001a201003000a207140030000700401c501881d01302d039040c252900007000010020120110154002e500c08441440000e0000d1481503d9100b9506e503a100f403031941c541084c0454001105d080743c1031000d036a407642d01c012400d5100b40c055505004060b8800006c1d030329125294000d041520138074030003217060540800c07036604071103400301002c0403264424010340c04c2c0c13403c0c1c001454001903044402c000703c03902e45d00301ca055070011400000e415512 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 46529131 1250 46527881 46527883
    0x8010603050705030c100c08030c1209030a02100606170406231015050403060203040c051f170c0306151201091a0301140c0a09091a0a120b0403110c03 66
    0x229034800c1d11903420400080126040502040c550301c04202c4080c003420484180103000a07111181c06000c2880c0800043c0d52440c0d50812220202c110700401031326858a092000c0d42c0c0d40c00142c42000600810759450150f04007070061000341d03600c50715280042990114004c800780c000070001c1d62410b8445041450b030080348440d43c14612406204450245020718a4100d011202d40c4191220700c2d460000d03442c4d01c2c0d40202a40c007626030001c005603032501d130b50412a10503074164008551090303500300d80321807481030740b402c60028803800c1d110100c18800d0301d940018804022514070104800400000d4054a8100c140540000c4c03e41001820a4007c554012450707409812122040fa0384540809444003c0041d840c000784040b4004c1c00b03403e50041003520780e40b078040c00395400305001081c081d080c030380201c038140e0280c8060300f0f00b004500860400030014103c1d56a2041c000c1d610081c010900b0000c0d1a09000c401c1e400a109080a403180d07501100c0360b000c4102d030780740540502818050301d550 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 46530381 1250 46529131 46529141
    0x10f051015050304200f040f02030106170105030318011106040c05090108061005010e01090306090f02101103070f020d1e1103010b03190602070c03060903020606010302180f0a0801 79
    0x500036421082103003001031404058090300714180c18040c1c10700c10480021940d251000011440c0f64003508001510000720301322480b1715000d0b0398414141021218184641d5020710304903010b0707075203900c050100d28041c110010070a0180e1609604100100c0880117001031b420481c0310418500005402400f501031418030f841528111480d5002d00400c001030300d0007520780360250007120301901d00b50a108004111003403840c801e150510000c0c1548007a560302424400004680102d000e000203151441e001e4013600369031500302d01c07943d107044140c002d4900c80d040700c04480143c00c005501c1d01c15240c40d82c080103020ba49003268440c18101c98000041d41440c00406407941d400c40d401c060740402e1420710080ca0414594034000c0c1c0c5000c01c0942c003581d00082c40040c2d4408204000204c050a040201c041c0c8034010014150b00311201d000420001e05500400100d0f00035800e44890761a0840114264410011610342d40039405100b03015503d804c00c1719040c1003030b000780ba803412541d440380141d00b074403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 46531631 1250 46530381 46530391
    0x901110a1a070305010509130201090807080304080706050903030301090e01020417060a0c020c010e011805030d0f020d090609051306030b0720030a0503160203091f030f090b0a0207020102010f05 85
    0x454100c0c10048114200e14409030030103101c3c1000c0c000340d070400e0040341c020400100525030040c09110000203690040c000d132000380045a0a55100e641c80d1a0f0a82d926402840354034950311500380300140c502e10800581c1d8552500030040c5145903e040402c40c00b40421403400c0c4400d560030003000403150030382d81d807d101000010b40688810300d0302140100840c2d20b10460401503410885d40031003a0f030f030300c0b15078900864801d0810110011403da583d4030640743c0c1d80c01c0036816100d5280c030b188040340c112030320b0500c140c0c096003210b92000070700d80c04440c0c006482c4560008100002c00512007403400c155400070b6028414800074055503252103580c0360403c01c1e2502c0d00481c0440815520a03a1086070100c6402d402200452500c50242e000901500c4014680003500c0358460600c071400d8428801c5520307020006000c2c82da00e03101e121810a14411821118000c00e151140366454a0f54500500350b03219081091a0a10780d14002c03040003950000d50224110f550361103180308259402c0c0300711400b038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 46532881 1250 46531631 46531643
    0x4060209040216060506030106080d14090901030309151b030507030e0a0902090a0e0402060904051008030408030d050a05070210180b010b090906061801140d090b10060e010e060901110a 81
    0x20580318102003003105c00c0a0205800782c0d05200050184040c0050400d103403003501e2815050280303503511305c1c0c1c0e524042c5180e902e6200402e0b82c000014180c0c007003100010380c0c4210004051283c591482034800b1000d07100c0001050200009076408203001d03001802d074860080c2010240c07100e0003000104940b41c1d58004c03500740369021810f26601c0c01c048080c1c0000c0d169480c22880c141c00c1a80000c0c40f2401504c0400e48120b4035100012444a040b960300c40c001c01d40d0b001140d0700d40d6200c608098aa4000e84070307034007150b846c0400043c081c0b0083d0144a00610994014010b01803001540e00098059618078065000070b8003014030015100e030241c58000d2540c041c00c60b0701c400c1080104140c1c0c440140485126000a01c0904142c14868075031130a6941d0909102010625680c610500b500540039003104551801000b18148222040c0780c0384900a1894625410340c0c950505890818503540d1550000700144031601c0507003800030060404120504000341e640508528280c540800c20a007160a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 46534131 1250 46532881 46532917
    0xc0604060605060c0604061518020306100804021c060b030304060201020c0607020106030812040302010605091501020105010501021617190f0b0105010e1f1e0c020a0510090b03040602090402 83
    0xd01015200c1d01d40030300400c03030724240b03010900480d0641c1c520303026001501c5e42c0e0b0340340203070f2055807516845400144180401415007503070000c1c9590007900200d070310901820350021420f10712481203218600c119401403001c01d4450300b0700101e18070004c0034101120110b41d01c00d40d1824a9804102910080600d90300240e91001ca4258050030203a002d4580340039a030505005100284072502030310403504a0040c10449035039a418101d0241c4060350000e90401035100611510b20f40451000305004020380003071055982e160012030362400384460481c0c035074a20500502c111481c14032103403000d40d18042101c0000c0311a028451074040031030422030b40e41461415075401c0200030a504c0d401000242006030745200c10b03501044813101e2060320560b022541960010101e80074040d0700d5406440c100d4160b01030114808082c01c001c0420794142c0c420116124002420700e0803010400c40d040c1540c1e01c4c45400c515020150510b900090001c03600c01d0f400740520a11901c1300d10141400c0400140380c064 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 46535381 1250 46534131 46534133
    0xf060b0a11030406020a0215040e07080402032b0302090a08030a030501081902012a06050f01051e061218030a030507030b100905061309140106020115030b0115140c0604 74
    0x1154001204401c0d904180802c10190b600400c2403081150141c4401c1c2d07120fa2004c015141602c52074010407030f01100c500500c0200c075404044503210714801d400f181c042076050900101c0c22030100d0002102000b0b001c8401c41d40e42d10130340117001d0b030220103030074010140e840310740407802d50b0044501a8006a42c550040241c048200a205401c1c150445070103030501d02c5400080588840603c0c84035040d000910401d00c000134081d041e58019004541008242000c000345c3c14a00c0d000e101d02d43c03059409880c0c034040c052088903081e01501004084a02e8512288840c10304860002c021014182d0007003030444080b032040c0024900940c09030f500113034525010034007a04442c44004030714001c103070800a0743c01c1941c000c189102690f8040300c2d0262034081c00c221030416800f2981049161a040c41e10468070141e43d00c1000e41a1812500240680d2110b1b4601c54600119448081c200c40c501000400c10340c03040070749804081205d4580204490818000040701d940f00355280c00143d070001e01040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 46536631 1250 46535381 46535387
    0xa231e010305010608090c010815100c03020105010906050a09050405030405120f0105010e010602060403030b03010b0406080708240106140702060c0f060c040605180307030209090706110604020d14010f060b0a 91
    0x10301404031342c20100e40d02c1c02e002d080150b5502080c4195414006c2d902c001c100300e82012010750702150b0008003500f0f0880f5003014014902040300800b1005503091500118210581d030085030b00351400a03120428103860407500d0000380c0303c003070b200f81e0f40760204000210701615200c240701c844d042c01d4001050740e142249026405c5540503403042100601d200c00500c641503000c600541c1003174040c6008204c03a441e03038000a0040030501401355005281000000792044040384400403681c444d001d036828100b50781020b201c400381c1d00c8032882c4210304880040c45054090b50050501c1a92035002030306100da02e6000c030b12240d00a1814103015441801800440a000c04c052a03001d603401110341d0400e403a141001d0640c3c05140035850040580e0004130fa401d44013086210000c6800803d040b4080c200310344601d0300c43d24a4050000081e0001558001100b80000c0c42402560f02901c545204003064640160303400300401c40c40c0d0039540364450020142035601913a8041e01301c0c04032499503840400005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 46537881 1250 46536631 46536641
    0x209060f040f052704060b1c03090e0103051507090308070f11010e03060106030c0c0506070302030906011a1213050604080417070311010c02060c0105092a0a231e0103 73
    0xf461081c2040782c003483c0403031900341d48000182d0000303c4900c5903031560314102d005440250401600100c1c003607240c1c2c0c00c0c181000c4005100a0180e200d06903c941c90740d0900840e00d03824040900194843ca002420205103a1603c0703901c020705103000c408203030b10381d6540c080c1079100000a44c1c401c1034411980c401e104d0b0181d103000c424034090070880e859541000c00300351506014800c45050540d10001201424000d00ea640340160703025082e11540d140802010380290820381704681f051158200114001d40d040c0071142841d00e143e01c0c42420f00c420f424002c0410b0100609092240c85441100340c002401041918000c91103864025282c2d070078900c842001c5804044c1e0346000380d10107841040801c0725848156034060003883d00205550550001c20320310321810040101c10340c81e2a040001c1c0315004114154120402071100030706c0e1980b020f05864010441c10f00e140e001422150400c08080d03100c0c00d00b110110000450031300d070364a06000803421400c0003541b40c203500384103803403003000d6a151041d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 46539131 1250 46537881 46537889
    0x21b0301022109010b1306060206070f020a0605060418030207030519080f0304020114041e0b07120e1c030e1305090303010e150409030c03080c0c0c040f0209060f040f 73
    0x21400c000100c1c40c240c2000c4030950b4003045024442000c504800020f40262004070005411601c3e005034042500e0000c1120f48a42401402140c0c04260458451000000303802c41c0c540c010452400f00c2e44801000b408043c0c207040e4050b980fa20b00540c12243c40e600c085542e4060b40103040d2040c81d5003000343c20f0100c40c0c030480c40780c9403414408000160f201c0341030341d02d80035444c11026140e60300e910059070b00500c4c120181c0400f51001c00c00040a0884e0b100860518a19910b60944195102480c07a01c5018022000b84803640480d204030829214507034088200c81d005026000c200c000d144031081b4440282e40540004441d51820549810034420b0240181c895800420031845c04545082d12400107006403030f504c0303103102c011580700718001d03850403030380200100200000003961501402c541c0c10b00e0070880100e078103140060340b404205400e031240030010340c000e081e5031040441040018021a0001d602080d406e01007070503241c4032800a0f00c1c0b04229401ca00703664905295100001c0c90003540 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 46540381 1250 46539131 46539133
    0xb07060e150403030903120501080a030c061103190b03240403090302090109060e06030d02030405060304060609020f09030615030c0f1926030405010c030305180a030815011d121606021b03 82
    0x40104500701c40018409643c58142c078000400c035054ec074040b80985035a00100028080c08030900503d00345040e16141d420304010b004001900110b41810b49a40c100819100d4141200c4250404140394a030000e500c00d10a107403080708252a40d0000d01403440c2070304044c240740c1d41e552050180c1407491240c01d4220030101c0041119003000c0c0c200030b6481c0f03d5802203038040d54010001c101009066000b0310041d15004c00e0640d00ea520700d030785c503e065030800303c41c0500c240308100108801c1c01c1c0500d0391141000015010303044c018800418858515000c1c0307085908000f0048015440440140c601d038040c1944901080d03038041c0101e801041d01184540a6550350020002001581c0e00295100e08541c0d0504010845a81d01c5050828070100740c50200102d0084d45070003410164040080d9108140e040103c21701c8031803c5004641d00c80d10100c0c00840d03d030500040310304926001441c2000c0980c080c040f24003024071819031400e100c0059100c0b002590049041a440a510b203203402e10381d90041d8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 46541631 1250 46540381 46540391
    0x30f0c02030306150a230d06090b030d1407060504050d0e0907210e01021206010908070806150d1202030a0906030b090601030905010e01020f070c080105010b07060e15040303090312 79
    0x3c006560031240c40c1c81c4040c24140016140c150601410000340511000011121070b9910903118002540c000c1d08500c158600e03000c030201c0c030340110788120510340102800408541c407403420180e8076003400349101c00e0034580134045800090202c2c041c20303100300c0c8a04040d211111943c1809490b80050300d030300c07a2243d6004070400c4400c55004d00c100e00740441c1042d0440c00c08041910920082490b4640c40c2241c3d400022110f41a03041010194003441c400e90311702170300a50314a401604c4182c03900617044503030460300200e5502e0010206102044000510390a031013a0300d560f030b404105c44541c002401580002c00c0e00028990440c40c000000d01003801c05201d01c0718602c0000308403030710040815040c940d807003c40e20248003003540502400c01c021b030000c564660401028400e039401405040300c2070441e81c4008110f40c0c0d018058941201e5881d03140b50b06104042c1d0b81c1d0780217460041c80b04001032043d4031a0340d5442400940e20340c0124040d4600040307002040c2401000c4090711203100d26071900304 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 46542881 1250 46541631 46541641
    0x2090c030c03040b0709120b06090916031104020d0212070206070507030f1101060b04060c050705040b060f07050f0303070302250203060c0a0509090408040512060411130905010c030f0c020303 84
    0x70841e5881503100181021907621444140c8240e002504404610203003030344190b040003180d241650003804200d450010740d540d002109992000828003200141c003404a0400025401d0300040418800c0200098102000344081601320b230400e4000d030740400c1d808070901000b9601408a40d070000c0e098501035180005540303004e00160018002d003003c1214404c40342810130030070351040f03015120003600240d50310340d640780041c002808010b0075940c90060000001e00c1d840d103441804011140035100310700b0907240d160a145682c10000083d1400d006078096400800300a0005500c02c200f691001030301c4a0600c00004907840c5800c01c141c41c078000c04041000035030740001d4203c0d80701002d6011150355201c0c1038401c4615020b2031100d107030000901420b000030070008001510540d68140c565240481641085a07079544003590060965100c1c1410300403a030400030550f00e0401282c0c1000b044003039aa46d9644d003100c140c2d0708958002580c030b002c40020340d2103500942e0380070300c0180700071400d50600b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 46544131 1250 46542881 46542901
    0x302010807140316052205150c0601140303040e19060918060507020304030f0b0a0c080709090f0605193b0402010c0b1f050603070e0f0102010b0409060902090c03 71
    0x242c610030000f20744c4401c41107001d100b0400c48406103200d82d45154075540fa10409070841469000d1390b4410022940f41604240b00c0c102a01d071174054003002008181d00c0d0075400d6003055500c0710400c0e05404108004142c204ca0141442d0180d6500d1849204c00364150b41c40c0b20440e550354001c01415402c2903240c41c18980c1000507030390340c550841c800082a40301c0c444103030718510a641c4004c10306280c990320b14082c0021803071701c03500c5980038440520060342000000c030707800ca0b0212014400f0418508050002c0041a84a091005000203002030300d0382d11040024000c3c15403e880601850a000091215500c0800c440484241d100784000314009885104440e401103004240c50080c043c60011301568030030300710501000e4101400207024141481009030305220248046003030803542c2c400080342e04018003200c4c401c14082d500c0800c40001e5500300700800809000b568115034032202c03006001d0b51540300300c8030020702c07680001a0004103072044c02210140181100d04a0000740100040781c14 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 46545381 1250 46544131 46544137
    0x302010203120601111509010c0806010c0803070c0803010806071e0504050105160c120c05010207120201030905160f030615030b0103020d050f06191401030203031b0309060c0106030201080714 84
    0x80b0074800b41125030f0794100494188460842d540c4039031145840c48900340c1c501808082c001d0081c400288940256100142c8506505482160006071030108080100b15100080c0d60003030440d14103210000402c1d01c0300d00d280c2d00300fa0403244185e04402d043c070001c0d540002140b421581541ea41e0000b0645103800036206000b148039a40c1032040020740c105600e400c2030b20035081582e02112494290f0f0700e07150341c0442e00300110002c1340d81c620000d00c042082c2d030001031340f5012a88580786000031515198011005010105011140d0384124144c203042a41c00041401c0600000c48100d034800380f031801c1190aa0700b12001c000a481d04c10f03c0184081150181c132541903075015100884250058030f021460820151050107940c010b0a050280340728880100000d561480f1006210700540c003082000100000e100080d81a03204004c10382440c0e501c2205244040c2c0390805032820b000c1060302083c2a81d1210756100c00a940d42d4809004668118500035040030407890b2410501c0b80e50100745903188 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 46546631 1250 46545381 46545397
    0x1005040b0604090201030603020d03030b090f040f02060918040b09010c03020f030406180f150b0303190e0103110c0a0507060c080405010e0409061d01050a1a090402030a0203031207030507090302010203 88
    0x30b0340701e0030f4400969000360003c0313005650140036442070264604004000b000400409440740034140c0200b110101c1040806003d550030200c00048058a5401c20034160b000c88500c0ba000f000f10305e043d1803c4410070780b8142c4118020f003070603081c9190102000f42107d841102c542c090501c10320000303002030345243c1502d5100b58032400020b100080100c480e421020501c10091004072801591010400c5200c203803400d0302106001444030204100416403640a20500700c5024203c40031090905440f07042e0b185507a43c8107040000e0000b141098822090344911104400b50340244299810031008015100040c140340c501240d9124107075a60801a1040e4460981000010704000c01c1555459121859240e07000404002c416145211aa54843d4500140d079041d446d150005408200c0c82c05042918000d05010b0300e16805400300708080b025001d40260f030188540080c42006840070401000c11b5401507104070920700c0c03c0b90005041d900d00501d0303030741000841380c820030040c0d80000583d8540c1c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 46547881 1250 46546631 46546639
    0x30f0715030204030b072304120213110703021b030c010903060c0e120a1202030a09050d1e150b060f0a0e04110f04060912170304050a050109030906021005040b06 71
    0x421011008074060f020755000900140e034070308140300b030007a00988a08501036107181c10310510110300091a40030f000e1403041c0f091a03032890184800601c0d0420401420310018000010a0343c01704c0071f4034507690824101100543d014100c422510681803071884ea00c0e61041b030007010700b411200300081c03203044548402012aa2141a4848068020182c64440d20000b400384c1468001808926039076030150315054815180b084500744a843c408021541007404c00e40301c00ea01c161500003801205114030105440c2d00f114094002c2c85000029040c025103400340e0441040417543c3c240c01812114185001c6219036410046002c0804210702500c0c02020141009408100c001001c10017800030045600200c0c0c0c0b000a040520480041c0135205031002540c0b65008141c035a49240396840424002034418622400941c403079090702401564043d1040701900d083c0099507076418251a050102200414058030741400456410080040009080c80c8148114103294640801c4208090105405 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 46549131 1250 46547881 46547909
    0x303080702070305060c04240f11010e030d0e06012102040911190f05030a080d180c03110f0319120e06030906010906080d05030a090609120309060b030f07 68
    0x300500900106004541000a58809107802100401d45500c2806007001d48159804101c40900c1014107c424000d5145c590407400e00c0c41e24000d943c60341300808600324a40d29070101400c480d109101801c41401d02d0140400c07612240d0500c98104401608550790482404421a100030740b19a40f014209405070380000d01c42c0101d0802d41d2030300002c0100b03250408200600c0842106200a550041322015510a44843d842e007082640302d0050300406000d0041c00d0001d8510300c05198410480c10464172200852849180c0c0ca10407541d5003640309892504041c1580f501c42d040200350700f030300c0103011405440c22441d81e00880a1401812001074200e09403c0c1e84484080d01484034044115001800140c50746807840c2040d40d960002d000d0741210302e09081c400034040c90000f4251040038015281d4034215a6050f0140c1c2c002c000309403094480c0c0d500d40c1503103400b144080b0312040b8160780c41c0d5004507100071141000400e50b940211000c1c000e03880441900f1040201080700c4003038039441a48485 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 46550381 1250 46549131 46549141
    0x50108040f020603040b0708150916020705030d03060503060a2a0504090e061e090307060f230f0c040b0702090901150f03030e1e04050601030e060702031e03060a030308 74
    0x241640700e000250440310020511080c020101a600d02c5a1210340d00c0042907a581b149068800c05d5240c0700982000580c400300d20b40410101403d03140c1901c0744101c60340e550360703003001a1802c2c40c030000034000300c1e80c0c4003018400c60800748203660340422260824810421000c000452078441790740e030014142842d42000c04030520032012035009041d603560500922010402003510740405640805500d85856980c03d800000540000c3c802d0158001850a000c00c54450750083c2c0030220200c8500c45d0388448a40b20360501102442d10313040a5449046540b40c02c603102030007840c0180c0005003002050104000e84803d500031030346030b0390b4103484c0e00c1d040c5c0e01c3c2d13115140c0c0900541c03078a501c4491600140800c007011407130101022240243d4030001816904c3c010311040482c024040e170300160b046440c01d000760030305030001504a40185000070301e01842600840c02c0000130b0310f081c5c005801c005911603c42c0001c3d68500080482403104605d542402800109111903038031009050090200003e5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 46551631 1250 46550381 46550393
    0x2030606071433060907020303270d1e0905030c04020901021e010228020307030c020d1b05030705150405041104030c030b0f070e1818030408030a0905120705010804 72
    0x2019540552038203516810082088106402e40e0f032101c16410408000180c818a0503a4010303000e65206c2d0055441c54032030b084501c4902c0710440c0c80c0d42c0c0e420110f04070000070190400040203840c2982e034070b1000000941c428200001034200c9828100310000c6000d0007030b990041a10350144108807001696040b040300107174100f20540b10100c40401010f400740c0880d00040d00144613509090504805100d1a4584042410120703a003820040c1c0c0107000e2080000d0142500388071407400104174a001c8111a50392084002d1100c0c00300742036105c2c1d40c20401050404000b0383d00600380c1165840e0800445010310b0805004a01c01c9034405c98590300100d0350181d0040449018581140240d0710043e00d07070030304a03c198015245441d03025801000600c0f40c42c828940e01d4802c607c000d0410010480c1c0c407510304d042650152559207188000500081c1c0604100000d04c014150742d0090350301d4407000c110242c2028030340d1380460702503809800450602500455080300341c410900700880c168031142410 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 46552881 1250 46551631 46551643
    0x402150d11030c0705070605070809130207050115050918031c060b0c0303090c040b091b090a0f03050c03060108030f030a0b0d03051e19050c1005040b01031203020306060714 76
    0x84407400e90300009000340c00b220709000b4034485004000310350850766a04011a90b80c4203000002c1d103c81c0c0c0600c1040039a2400062100111810040150030100306803512400c440354086112061071344d03103604003c282001720841c0d6004148151640c02075100c0086035441e44100b02151451088088465002c0e40250307100e000506400d034151130702c86860002207a540e51068130508054896041303401060f01d02402044612400039003001c005440d0301c20030740552584000c89441c0c000f001c1c0812000390301c504400700d004090780f10040100520354140030342010b14035840c1c64026000680103004401b130020403034000d003542403c0d07155a9526048460024102d52070116800070128240200f80360740207015081c200401c4803003012401a0501094251241452840321300c426045410113040c0510042c001814402050b655a005119200340860b00d044400302d5090103000018000d0040d40308040d03010b108207040c210b2950820b00f00107036450092140040c4a102c840c0b4164000e40024041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 46554131 1250 46552881 46552901
    0x106050c0d0e181f0b07120e0f060f040e0c090a0e070e0301060611011506080a0b0a0f08010203071404030506010b070602070b09060a0e010605090106200a03020c1003050402150d 78
    0x400000e400d162075410803100001d031420950039410240172407454208811104007580c800d40c0b00f00b61a000100581c6c0c400c2d407401e41140d00a046c400600b031541c1343c4000030152851310242e901d596a040c00c807000e202c6040500450040320302807211045544442000d00181e6107010b06032070301590340aa00b01c504003a208110741d059400c041c400a01c00e50002e0310200900b1901000f401180001c0d414018a400316200303510005a0700e9022544141180d071101d10010030162441e1080780d103892f10244101c2c082c0e0b000a00c03d81d80041001000b680c8107402d51480000007203c035241500e03603114159500700c1030040070101e61000a2240400040f54101c6041d29413022864095141200403075845840451b41c00080724148132804018034030612610f81690f6000740350506907400d03c20210382c000349108031640c3d00184c102c0c03c550030079410050055003d01c2a4000d100d80c280710b50a000080d034000c1c0c0c0354803d25007080103010047e43c0356040c640d01030100b00307441c540700ea803007088004c050203103944 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 46555381 1250 46554131 46554169
    0x203030c03070506010609050306250507050304080a0c06080c070b060f03010e010504170f030a020a0201021b0a030e101e0513030311120a020a080903071a030405060106050c0d0e 78
    0x2d44035082203030200d50581203c2e02d40c0c84082c401079039002850344a074011070b1503801d80d401050310020340ea0603508180740c01880c40d2400d01d041c0384072139403003507d954040d4000b2540340e4002e0500c071341084020308481e80540186e14102681e410089d0941085008001c001402c000d400da0018400c3d40320581c40d10031291004001b88000311010268030300805050300e007545c0b0200c8010350302003010b0002040b511610483c039406031440c2d56410481c0000e400c62030700709003107540030820b000f4042218804400a0728a200280c40d0921071443c001e0030300814201c0103401006030f4084040c020b90411781120405010340980042c610072030300c08503000e11490000301042c040d02d40c0003000b8142e000300e0030200d89842d00d003100c420098007014016140614020400160701c101c3d9644006071019001c0c010441003d0200c4900588a4980c0c110402c007a404201c204080070081005002e81004024014110b50601a20340390030034a589469080c2c0c0f90903a004d1090b00780408010382c450070204910608424 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 46556631 1250 46555381 46555387
    0x30d05040b06010e010e030d110a08070510050a1404030f0e04021902060f0402100c1a010b071101083610020318061e1915060f0504030213090203030c03 67
    0x12420704110101629890b00241c099140302a10754002c0e41d008100c000010700910032560000030445408c16211190602c2d801110300d02c0c030004021002420205200e81e0140101c00c0d81950401e0894000a102c902640e04044942c40004207080c0c04c190420741500c2e142c103000d124000c003a13807125920740340c02d40c009100041c0f440101c940c110031030340f941b101a425030348940c0350302c60005402e88090b140a54018001410b880c5224080c112220940780b00300d00c009440c5460349004004450241d100500301c01001500d4400c01011010111039202d007400d00e841242001c0100c603441440b91006007243c02d4802c90028507400f4444190034040414200315000e1116503400d80010b0741040d100201104909105412600808510b1038401c19407003004040f50700380f290081c05600000380106280c0c46010011011801c0c00340643c0c41c40d401c1607400f08030320714a00b0200416545082240c3c1041041c03d100600050351000e40800c030940340c01c200072030440b00c40d0000a0861003548850503944c4400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 46557881 1250 46556631 46556633
    0x30f03012d0612060b0906040b0a11070905010e0705130b030c070b0901140603070b16030e041803120c0507020409020f0a06030608150403020a060504060b0a0f0906050d021011030d0504 81
    0x100c1c070f9080342806a00c405009a41e6180e05040150141e2020503901140502040c06000e500300090038514a40780f13402c43e062451a00305505140a03030300482442510389005000c4100e9282d03a03181c0200d01440c205d882e00101800580700b00c481d070b003e54007013008008003080c4901025010303926003c2e0841128400c6003828143d65009210b4404001910400e00c400540c192601050b10000c4071191403000d460444e055403100e0704860900405c406104106000244507200c5204082c020000580006c1d600e00c0a8280508801d440c0d501ca00d201509000050084a81c04402d55040d0307981524007003510f96071440018007410070b5655040d00000340d030900140155043e000002100c243c0c0c0706454541a015a02c1915810201c038050090703480142208001282c640c09240c2c428010440011080c20860010b00014501d41c0850306058440c41c041c802c8049912444001300b40880b10b08101020320b6011400b69080e441000090000307a01620411101c1401110070a003e0ba0a007044140b0f42 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 46559131 1250 46557881 46557887
    0x3051b0606040c0e010804030c03120207080d0f0204050307120f050d08100501020604020a0e09120a02010b01020606030606030a020111010209030106030305040603050f100902210a050612030f03012d06 88
    0x1ca41c9284201c1c203041d80840e00030301607101071240e40360613542c0b0081075996403810ba030340002c00a0103c0411110644801c0640e0045c0301410036240714000c81c941e01d54620040400740e40340081d40080b021b00c1008200010340d400202c550813291000040c501c98912824490002d40d84590003070701900130030441d81d1142c0e45c0181c20a00c00c0141088100303210303840d02c00480c0d8915048400a4111080300c20501c241c9000e0845140d001c1484022101e0041325031454851135002041e80c43d0150b910380100414030368041c02402d91102c820340060200c3d180c0207000a42e10f00502a0113030510844504182c0e424500f07404070303180ba060140c0280306441e50381c0b40042c00c070b51003440391500003450a000300d24540890140a0300030300d041000c85a0250a20383e14100942c40f10680d0402d4401d07541d0f1824161105010203886804400c5002880f80b0b040d500b1b01c06860421600000d841e003041001440e00081c80701a01e0645008800301c1e0610580d000030b40031880c6045c00c611240030300c1214000b42c5954 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 46560381 1250 46559131 46559143
    0x12030d09240603050609070312050d15091a120c0d02060409050114090a1b0e06160c051804170904060e0a09050c012109030c0206040305030324010206070c03051b 71
    0x1311403011103031643d40d01c421003030b181c90107400024071a201c00d21256a1091140c0c025000d424080c2d000042d010b440e01c002d4400a022941c08110a0b90b101d501e8004488154005425009020b03500d441c2c10090f044801622440940203684c400e030708840b02e11080d52100b1058402a094042080000d03503101c141d5a4040845064000d02c0341d080140003032405c0001d401041c128207030034818400a00f1100b041628800614001e440d04250b0521824815403403d04400f03d00b140102d801d000300030304000521440001c545000c2640000c100c0038880040c004182c1d01d02800886003c0c2919882c040d40050090000d541c89042d800303000d0400d004141849600104859100b40e0490b0418405d410040d50f2601030340a80441c454401a4400b0b45190300750030042c03090f4441e2608000c01801c40d40001c2e51a00701c0d0300140e50355840030081041e0715590226030810440034a03140e0580420400000399075280041178042001030154904041502602c1907075450b00c40e00d5031030f249a058103c41940c2d925 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 46561631 1250 46560381 46560383
    0x20904060e0d030b0d020108040203010f020d021305010e060d0506060409060902090316140108090309030601030f0309140a05131d030703140408030712020c130606080612030d09240603 81
    0x40204090810b0729406442a2040c46401825100b00881c1e1074006456100001b00182c0e01075403a07550a0101514500c0148070402200c080182c4401086c00d10802c40c00103030300140c1c14032501400a0f00ca0340e5581040d64440600c104000c5920303920032001c01c015008507400b460840b4145900400d03c0d00f12078015003041601501110b901843c000039400f2216450b100d203120f002507440c16126079512544020b80d221850204482c9044d0210010030b16200c4241d00545034411500c00740003c00d584281c0407001050039040981070031306c0100011b10540344522a842c45008910242c14040ea00c54000c0741506900c0245003003d00f142e40950380c0c59034440761045000a0740c011510780001c000d80c05990680303c0800045062428581d942c1075080c6203140d034941503104241d07901080d0b91754040c4d1f120740c80071007103c0454003070301d440409015007102802c464456011700c0b0b020f14000034004107440740c10b0b9503038501041145160a140344101c5400c69880103035406c880100e8800c000343e4110741d080f2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 46562881 1250 46561631 46561633
    0x50904030f180e06040207290103020306070801050f040902031009320c04020a02070e0c0a030b0102061e070c080c0a02010917070317040801020307090603050901020f0f16020904060e 80
    0x8407600a4002000d00c0190041030340b051443c00c0820003030304040c1d0261030b071030b07219104000c2403100000e10035100150f007000b01107056084200600450609100c0315421400c0f50400480301d505000005e016001d0f8404a10301555031070030349400359502001200501d10505801300900318107402e1a800c846845810020103880c880e00102d000f540b024000c000d44219040a441c15039600b608201c0654846101642180710f6803d01040158a8402c6940160399250ba01d80e5958003a0502034140d5910030103941c1590090001c10241c0c84e0035086500c611074180360030700310302c5e601d81d082a10185040c0c03102400301030020524103010035001800300b05440c000d881700e2901c15941c1c0400d02041f48010b101400541103040300704001001a40c00c002c101480d1a41e450910381c9400e03041e82280c01c11070b0844c0c0000c103498030400c8410f070075100e0560800c1505c4020b52410b854001d00c10710501c2003420103028940f0000e0590369a0045a5060091550082030703070480303007010305251001d0440e6000c44501 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 46564131 1250 46562881 46562897
    0x70507060e1c020c011b0f0206040b09040c03061514040b040308090f030109150c051605060412050406020a0b0604020405040e150c070f030806010c0501020307021605030105010f0509040606050904030f 88
    0x102e18000603141004140507940e844c4400b00d0882c1143c0002e60100e02100d00340307601c2000e00016928030000d80b010b4807404005030344900f00309040006903044000a031007814540523043c000401091004800f501d031505050356250390780650f1044a00c0340d644540c5203203001080100804c0515001412032503000c03282c031000b41d80e20308201400c03100100001000142505a80c00002405804c0ba01a42c1c08a0034010b00b80303140d050b001da04190101e40308440c190030020403c01004018180004c0f4800e140c50214101401c0100c065a00c0000000c0500007144a4000510940e900d80454024041c068401d20040b0303101304006945500c141a402c1318003002c0000104007043c85016103000682001a02001c240d00744c4090316081000381103141080039070010500418400d00081d805800564024038489d41c030360280501c0d500050300503078071903410480100b0000182e07103584001d46004507103400c41c646451600c00001c0c4160f912154201c01000204000e154018001c41202d01040c1c4034205 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 46565381 1250 46564131 46564183
    0x90c090c04052103070515061305070e0607050a080f03040309080a0c0306020d0b041a0301060e0907030b06011701030b010512150f070c0c0e0a0c0503090c09070507060e 74
    0x11030303004500501c0c0d0401e5110b5401200150700c0c070745114115241d101624500f0341252100d40c14001e84100540018400c08241300741400c0002d85a480704245100070850341c06c0441d4000c014040050150707206504c003050040c04d0040c2403264100195009c04296640c01e01400181a1900202d40c1a400304104080000786004c0c0480c261541980c021040307441d142c02d5969110094005000d85030f607855850200440c9515640f140403a01c03020980c04202800200d0f0416003134903115008060840b50304410b100f401c0d20000f50000540e640540c42129555400004035008440e0001145564034036034000410700001c2c0c402503040c0c5005964040042e010810100d070344000b040040210410311000084516189615450b003140240c6403d171100d10079a11050780701d048035048208040c5d8883d05000e031005091040240f560350034140241149404e0001540302d41c04042d0050003092100c00090b1f080d4401d00031a0324a6074002400c0101202261080f0780c3e6030030550600c0718006c070740f03044070f2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 46566631 1250 46565381 46565401
    0x60801060e0601020f06040c0902070618030e1509180702030f0315030d090b0703030c0203090301230105090903040306090203161508010602030c1f0204080d0c150209060301050108070c0605090c09 86
    0x1032013260402322140d621031038449488003c1d84010000e44000da980d00342c55100e4502c3e4030400608038007a580d0038401032500743c1003001310300141c084180f0341c641c1084412825107920303004084a00541d075500300302d83ea07022000c1c0e0840c4101c1c1d070807400100e400001c0007810070509400b545048001c2c0c0844d01c2100d032029042c0d94181060207880054082030005d503001a1090300b05d5910b900952040e00e0404000d080840c0c00d40341101c059034030003400c00010101d6094403c00081c010802240c000d48542400d1144d19101e101da0b010140040e9250311030070065407400c00000c07082411781000c10280d11340d80c085c3c5110400c5411300c100002004400000380c542d100000780c4205081d180c0c007820480749107081c1e920b1051300f9880840b02e5244c00340f100196821080c030001c05820030a4591005030511031400544090000400302411481070181d40c8041d02c0d06029281929000e0034200000d4803070560070359101c2134400b002031500d42000104400102d000c1030700800742c40d041d01d6116040d11504202 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 46567881 1250 46566631 46566643
    0x90414160c031707020c0a060c05010510050d080c030f030a050403110109050c0418060e0102030907080d1b020d0209010305010605030115120210140d0213140d020112060801060e0601020f 82
    0x140002c0d80c40481240107843d0159a90f07007100031401107034600b1034140302098681c401d41d44442d01143c0e0380314686003402021702459034800c036a800c60171000c504000000d40c10905005014010304070105141411140030401c0f12204000040150340302c0c0741086254000d00003c46040380003903610b0f8800500454140914188183d00030007600c44d041020003448010104c0591a82c2e0a00d81c29880700c01260710740c800c0d5405401400d0025a9902d48a4500ca02d0300100b6485003005500c400030100034140c1c002050f41580b91030551404580f810b50001545030348440c640079601404000002080000c1548254211001076000f480309550140c40c1ca508442103120346803041c0d00b80c1c4840d200501c1c08001495041c080c07070a10a0035090102841c2c4125001a180481c81d00d60000b4406042d50000c00400c00810303089007445060105034002c54800c622012000781480f07007500303095920804a403c40d80241495200070005a59030ba01c4031085103101782e030154007502071000e90050090020443c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 46569131 1250 46567881 46567883
    0x40f060627020307020307020d0f03090509010f0605160210170606070503090d05011e09020109240f09080a050105040b060d020a0614071a0703062907020402090414160c 74
    0xc01d41c5056040896403029600003000002140010884100180e0300c00482c00049801b40301700503200c42c520329000e060b0004d1038220a00c101348180040000c0000c1c08071040c00d840705840d000c0c0e00c80402c29103407021414100c000a6208020480240f002c6a02111658601d000c0803041f038496102d0f40140006031260500207072850700100312165490800c2e0140c0f5141500c02e100000e00e5400c00082d05007001060b5076481c02094a8040782e40070b43d030388001034801801404100c1401107221f02d41c01c007482803400b0100b13004d201c0e91300680c207c0345004400c90380040400d90140d510b800003604d420743c024042190111003050301c0d0b501242f03850512101c0895420b078060a01d2072370a0800e03006030340641c2d2441c201070101d2801c2040030001510120b0842c448d1040450125060030642006001d42e140c82d00440101500710b50041210f141004000c6038481c1042d08290b902c03056800410068032500d80502d4010341010b030340c0c03403910290031a0030f4440c0c40741e4003c0340c98005000c2c0080340c1d10141688 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 46570381 1250 46569131 46569179
    0x2030a050c091c0f08031312050a0c0609020a0e01060e010306080a3903030507030e0d112403010b0405012606040f0b03010f020a020c010306080709091505040f0606 72
    0xd0074001c062100d0340c2c2c04034490090720310304c002c00100d5941607051351080340c01d1107015180030031070010803140c0c001070303101802d0504010742415000b90f0010034548500f00003400301902c03001c50f9001e6455114421010b00840c2d180248550b8640e1310281c038103d2200400360000c0e10300f44000402c0500480c6500e0000d50001b4103281c10585c4e2201c210f02c110001d003000300001090744088244050016503840110f100f901c400340c0340c1000d41006044004c4045c0d03141e000722944804140041e249181390740d6007070005c0354209240c649211010580c1703400c036004009071440010001c180041c00d10040c00448400340d0f035803201060b01180c00d0f03080c1c42070220002d5080c0c000d42c01280c0d1a1500c0d42150464818101e000195000c200307001909440e90040032418195000644080603a41400205010303002802d0034401c039480c013040c0580c3d80c2c80300d12540012a603124909000c00003038407110074591000000c2882181094107102000c1091908100c90aa1030150000360741e5040000718030502c01424 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 46571631 1250 46570381 46570399
    0x315040206120601050d021305090c03090a060c0c02041515020304080606090c12070306050109170304030813080d082a031504020f0a05070203010c080c07062007050102030a050c09 79
    0x281c0c0b5002d102c00180200b814004240075103040003429201425454114014411019240500344540444003500c980100781c0100200100c4036000074000380c01640c001e4000a6500d208041211010701c281e0000b90f100b070420700f01c440e00c1c5a50a61280660b03c20401c017810840032101c05903030fa8421072103800e0180d04800700081c03040c9050ba040340c0d4401c1225554600c1c1928110051515035022104040420340c0d6010900055078001c106201030300c0d20300115003809403c00c40d0700f6a00d004070701c001000301d180000c40341403041900442000500c0205c080350f080758045400039040300000ca0302101d00342c1450841312443c030008500180717600c881003003052454566581420501e120003514a410540030020b09a00840140043c4407468440c0c1e21103031600f88600c105425501d80481010400000324280007104403e24100c80d507640d813090000407000c42c01000030003200d00f0021483c4040e400800c0031000d01406400071481000800b104101540e14a811761203180504a031a0360003034104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 46572881 1250 46571631 46571647
    0x411070c0b090d0308040f0f03050c0f01060803070605130206030403050703140307090b03040c170703050708060408090909011b080405060604110910140f09010908070e0f060612070e0315040206 85
    0x2a59076603007003402000507c08106840c5c0755400c6458032103504400103a0b0016040445040a100707182e030180c2144001d0040b10320703000d8560340d24020008040d01082d56000451140c16206c10102842c640c0900060788170b14103801c011741140c01c040029000304d0203490303065860b0000c00e01103a02c00c000c0c45c0c42c0c0c225000d043c0302089045030030042007201c20403401840880c0b21a469100e801007200c54000402c251400d6280407030030150389500148803980a1b42c02d1200080d00142510401002074915a6a51b503411198034050301441c0500c580720381c560040f001d0390b1540040c08501c120300800458a440d294942808111442030140d04a100740c103105c10000d500d0015207002045255203031a01900c0c2c1800180841503100c540301850071200003510b28815600302c401880244140409800c05a181c100c480f440f0910080501c210341072088001021a615882610007181c5c3c0507850504600c0c2145014080440e0f41050318800d114003030b8100d0041d00070f484024807481c0d0140c4818100052 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 46574131 1250 46572881 46572887
    0xa050c0d05040206070213051e01080c010f02070b0d27020d06020319051503070602070b0301060c06020705011811060405010e0f011b060c030609020f07030e06090411070c0b090d03 79
    0x41c0049130b00010810840c80075a035032050000c1c554024031070005040c10044100d000860060149040c041c8049004000e940c00100300058245030a0a08e4200c02d180d0640c22418040940c100070b25500011500005411503580501b200d1650552210003000a0b03074400d09500040e01c80c000d51028012060300000780d1a42c01941e001317403d40741c000200b17098042040042d150100d500022022400000030340510342042007c005021038009080b03941d080146028541c0700500810b000d120a00f13010000304007159044030707400d5030000001c0000c80940208215038480c50441500d080c1d4803054000940e00e0f001c800c581c21910140c48981c004000c50061040751414451401d05004031101004103000c20301070040ea01c03610070b0030b0001d00c0b03055001c4003504581542d000320ba00640305002c507041d42d01e40c04003192007154060609210301c00300742e40010079921940540c0f40d0414201003090440700b240d80080c140711842119410000d503100e0740e2014071b90140700d4216501007005000c001c040380c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 46575381 1250 46574131 46574141
    0xf1a1c060b030d0203070516061409060712020a02040c03020a0504090914061e0a05010f090905161d06040b0105040314010603120905031b011215030f03050702090a050c0d 75
    0x3218500108040c04003400290400004190000260300001034500400109101d95100529100500c106103410071100401d1030507220b0500c0d8903264002083c2c4640c1d5903250079541102d902c41d0960780409140003000303484507603101d4100c0c02142440800d207841c80c068000d440c3c800c00c2c82d0351800d080914181c40c4d0800740800c0d42003991601c501000120b0501e000703106203481050400020034081010303101d6002c19080c01070200d42d003d0318140050051400c0075045004581700d400340030414007043c0c10068180b004003842c010305115000c00006103010304402e00044400d01c0c402c4a170859036510107220907101742c401d605d40028800c110510014008410a403441c50050000040300c41e141d42e07030361926400e0000b401000c0350098404003c3c0386010403d0740c03a103d1700b40d20411007400f04030001911400342950200c511546030080050450b0540c101c060003190080d02201600c40c03d400c2c040d0407944064403d0b4002ca41801c0003814025280c05102d019000b09a8018a080014050080208 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 46576631 1250 46575381 46575383
    0x70f0201171501030f0e03040801230f19022704111204080a050c0303070504090c020d020d1b0803040b07030b010c0f020d0309030f0c151d151c0f1a1c 66
    0x2031b039070b00c100c03080064200003402c00342c003072200006180d03a81840040c02007810ba40c1c080b102c3c001100e0401c9a458100c0d000c403070f0010440885120070182d01e1041c04042e010740210440380040c00305404580644ac40700020490200f80d07020405a02a00480b12861040c11600100c4402c01da0101d000603070740d04001c0c030300400305280060400d02e00740c1031542150b1054646070700040780801c0a102c8000740303114a100240d4240014a036001d58200f001c2c0d00d0781c00400b0202d00388058000103014160f02c0c080c2e00c0e030419502000c003583c0c0c4e203054903064105035030903203140000a103040e00003021540122503030880703985c03c00301040d4103401a50070410f0b0b43c1c8101030210100031003800000001005c0d15488050b55120f081d0351440c45040c040c00181d403a5240010604015400c019141800d001e000c081d000c0704000c1e03801c0c10010303c22201e0401544100d01d102480020304401d01c0c00721001c20341c041403500165440c24404c00c40b5140603c0500020207070403a911100300e5000c0185d4601e2410780e40740301 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 46577881 1250 46576631 46576661
    0x4021302040e0f0a0606050702010206060405150a0602010f050f040506010b0c100204140102012f03100302030f0307030e01020727060803041d010b03040512070501020906070f020117150103 83
    0x810b40794a80d075440a01c003618804000420101070100c1c0341002e008100c041c0c440e80c9802810041580c000039074a007001303001c3e24012955000855244001c68080389440d801c0a000002915a1090024000c01664a210001510701b10101e16a59443e10407a4011504200248030503401c1c1303403003121154464084c1107217030320800e240744040000303030300103040107010210003419044155000682550141e10b074401c0c80d42040031404010000e20941519000d40c2240f0780f41e00c9030b9030f20307c050407004040e8001075458410600704024141e03000000b000003038842c1d41d030010200c0d200b00059035948003e0141c00350400003c500302550120f820150703110b0380c81d8004081b9a95a980d04801d055600c1504817100c0e029481d184091402d040c082c0081c0101038441c000d903d03528058031540d031606421001c1c000400000100101442800d405598401d10000e00e26030b0f0300c10491031302810703280c45442c0c12070202e6800d0030281050200d170fa02c61442021100180c9811070020401103005024031030b001c03510 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 46579131 1250 46577881 46577887
    0xc030a030503180d05070203010e0c0109091805150402150702060f03040302011803120605010507080435060f0604020a020a140a060f020c010501080304060c060c05070609030f11010605010804021302 87
    0x12030f50801100c0c1c03c031035854441341d64559031401030500f56140c0d021080034613030009181c42a140da2081c03062085810f000030014101400c000c100c103141e080d401d8082c160b440f62103202162081503051050040740b085400315200c2c1050b0038202c1e0507024070030010358086400d220060329030990130021a4407a2091000007010301c203e4000390b8260102e0081500043c87c0800380100d126403510841d8040c01003400d025042a4103540d81034014450b50184030b072080802400d9031b9a40807081b80101d0100c500510030100303810a803800383c3d031f16941255a080d030001c070311000c80c880b81854421654641e0031640a07050f5020107490311607141140e846480014403402d440c64020404520a08101d0040350740003603603816446610314251801a0044c1507203810030442006005d8001e00b2611b0701aa1180d0041159418030314251640e006404010300304078240008a010180d02959000c440307851619000404a600d104c124200c654600410b4042058140800c016207420541c041407049907050242c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 46580381 1250 46579131 46579171
    0x306010e1f0509090a030810080613060b06030106020a05010f0513021002030f0a0305010807061403041205040b1b060c030c0a08061207030507060e060304110607030c02061303140c030a030503 84
    0x3800e00c401321800fa1268111a224604060388500300c00e41100c21038040c0e48110381000c6d886600e4410281072220f0060042031400c04000031600808801c0c00024102ea4480d17a5071300303000c1e407560345001046034030354a0030800400c03003050340c41000d005664a0200852207561507083c4443e40800d400e4807010b48c88103020034002c20320010000c00603800e01c0c0c3e4003c507040d4940a04540703001020780000d010b020100e5500004884c0c0a01130365400354000e0741c00c0a00c03e2102c081603540e40f00b1a000900c80e1070300020b00c03169030690740c0000303100006030104554042e034551660b002140070541d4054003080d81003007aa400d540c40794843e19084100140b4100d414034a81c01101e02d030103442d40c01280c40390490542000559000440075100d2141602d070b035480c6160560366030140e80704919445104240c08212501031502c0f0b540711000302030340070300303240e40c1d810070700b010605251180c0c4400c0710f001281644480b504000420080001540034008001104081c1c2e0281d460f0303000248030444600840742c441c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 46581631 1250 46580381 46580389
    0x901030e010614130603121d0d08190f0f11071805070f0206060105030609040f02100206100602010917091807030207120806090601110a0b010807050109050306010e1f05 74
    0x100220021003101c1c203d075409120040c00108a4061002e15052080012030f243c501c0400e0481190302e00b0500b5003415542110340b00c88202007c1b500555054848000c00812030700400901c2500d0700c3c9400d1009030043c0c00c0300c40300311000d03805000902c0c044803450707800e00a1042200000e074848c156800c1c1a1107010800203030b054005000420303034680301801400c6401a00380342c8002c0251010b4504c9241842c0041c100d0321014040c0c0b030050034140000b8040c40178a0681070704803680102951203404840d88000d5171900c090b641c00c95981c190703440c00540b290051140c0104641e00c001001c1001a18a201c1500380e04030308602078106404181c0c000072003031402146480341072280c030010781700e034450b0420101b1044403000600a020902c13050118a41d98541c00b50390042003442c0140340c101e504841503091681d1694000c00342601c0c00000300c1c2c09003000ca20030054903002e98444c1546642c84040580d200d60a219000c59246100c0c0811035010601c0ca0079081941c42d8000d0440d5541d950001c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 46582738 1107 46581631 46581641
    0xa1710140607080405060a0306170606030c01050a080c0f160501050f060a0e0a0f0b060d050114090115050f070b040f0b0a06060518031e0a05010c0201021303080901030e01 75
    0x7c20351244030340c111030094140a041d0556030230100714410b99074441940c0980c446c0c010584520f0503548900c01345c50801d0000c0d034030900c00d0303103a04000800c560b10411410b80c41710340c02c0080d980d0010704001d03000b007011700c44d100004e01c038544000548496100509407070710440503c401001001c902084640c2c02118800c4d002a0891010104000a1950740d40c1241c2107400411803170000c272400e40c00b281c1211591201101c14100c0e203070403c50809024000c0d24050300c815248581540e11602c00740c24107c140500a0746803080b1502d0f80d200c44041141e084811070745901398401000101d03c01c064101003221403c5c0001030a084024015005000c07071016114208011200c1d6a54104580801050129075820001403007210140e00c9482c481c1003030700c030b80d82070407415100c003481442203903641204401c1003125a41150383e40300c002c0e8419440ca84c101501d0350a060090107080c40380d = true := by decide +kernel

theorem cover : BRFrame.Cov 46402881 46582738 := by
  have h0 := BRFrame.cov_init 46402881
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46402881 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 46402881 ≤ n) (h2 : n < 46582738) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
