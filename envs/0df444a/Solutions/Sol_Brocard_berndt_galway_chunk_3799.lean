-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3799
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:42:30.248537+00:00
-- url     : https://prove2.me/submissions/16cd3df5-ca40-4385-a617-57510ff551e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 683093525 ≤ n < 683273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 683094775 1250 683093525 683093549
    0x312030703060f0905040203030901050a20060121050c150f0403051f1a100e030106091407090e060d0602120411040e030711091e0108030a0912050607030f06 69
    0x2042056159204100b0707141c0c200e110501d802d07284c281c0607088035001c803002074141d4410081c03000c131980120050800039145180410aa01e40902c00721882c481024841856510900051060102602081c8907800c029429030b4860308040d140c403503941208544003801404142d5500145403507050803a0300035100040e845507142e0792880d010342d0743d400b891070031123030300000d40c08030000680c0502424411230542e90011482e002c449013007124404601111409010000d40884c030580c82c2800b404005003114070340084c4840c07851003c241448002003039001084491003042c00800401140b10303801c02c0b01501d242c40404564a4000c0080c412403495032010b003071103c00c00040042c54601003440340000e440070f02181c01001c036065541d0240106c000c05090220b2a504281d0401e16841035001d03800c04240c480560400b485005c158000382c01030040e40d0000030b00590015040340c032400040c456a52015100c0801e5103556440f042c010f46103104041c0c444146c2641116075400003005004010140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 683096025 1250 683094775 683094781
    0x201051902031e0a080f060d0213020c1f2403151107060917090a0603020306030a1211070b071e0f140d1103040e06220c11061f14031203 60
    0x85400c3d50041c55000340024482e4000a007644150b040700350140801401a800170003880c0d080282e1103c2c060403204010342d0901010810103400c1000c0451103a5003040d000800d0031b40da1005090303512007420054a550111034400800b80410041c204598100116082d80303500d803003840c000f40c401d01410290324200810790303405110159000d90541842144504a05003070f903142c0d000d1900a030000e1036800303492550104036190080d0011940100d004007034403800410355640c03004400c401001680000c40590200e024007108022800180c002d52845600788592591120f10a081205050156400351164081004132003246051010360229042c9440040080081d547e40241c0d00ba00001524205011850a4010040740c06540c0610780403411903444c1400e1001d416131003a4072280440542284107408000c5105210040350070345c0c1c6d43c4410005c000b142501c1c100c409810b1a401d100714610383c401c44510840c6c00c4048a0707200c0c3c0c520350144411b100090078101600c5c0e01d011030b00c07000410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 683097275 1250 683096025 683096077
    0x5031c1815080f040215070303021e0702010f0c2013060801051504090213110f0a0e0f010315140102100e011b08010605041e03150f18020105190203 65
    0x1a070000d00780c1c60382c82030482c3d43c2e201041c5080789401d80d80a90004043d81c145e0400148082c010000d09009050241c40d120705c44030340c0da816041928100c41c400d07002140100441d81d11400001030711149240c04102c0308416160a41c2c041c0c1890080002200c0b41780072840640c45201d038445030300301ca1034001c000c540d54801009000e030200700c5405510400780c83c1c901c080780c5807a100300c1507003580150049509540c0c42110300014402c0d1000201314500c01e00050104010000c02801555610355550250391036203024828818031040403581414203001101181040d10500311080f2102403203485454144a00141c0c10900100d41c0725070020700b04440b6603101c0405400642d4240600010030208004541040b1040312080c018040040e0b0104002c0141c520944094051000b5400900782013650325901d90131030240b01100c00c900b00e901d03961604036a04003846100e40046620712064803c4c10341d0350000300244100110044504041001803070b60301e20030001c2e10316403640399002600b450060b40c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 683098525 1250 683097275 683097299
    0x509033a05040c1412060121120906090e1909030509040204030b010e070f05030c030c090d0308060a080705060405061c050f090d05340606060302090a0e0105031c18 72
    0x300c004c90744a130044d031242030810100215403013080d42c0c080c110503401d180c03662207081c16051400e08072000780e5403614041001051901003008070b50310b0b980c0c0c849240c483c0180104205030310894003940d150080103059201c031f030549040d0601c0c0361400a030b250b0240c9020341d554010559001d82061020502008210b0200355040c1030301c02c0561080913176544e1f040215070900b2955506c01c0024018404505032846c0d0f00051030300f03c506d0014103410140c2c07c001081d001c01041d101500003402d560184402ea06101c00e60710040d208560203403102c14103020101d01d0920440c400c507809028000380080f824402402c80b0505411046003d001a00301019030b007135105c0056030040e0487c099501c0018409004000b1101a0302003c0e2105414002612100c0c200140d030b0440c90344c90140c0c10810300000307034062088a004e0841514016118a03044042c446c4070ba83c02d17004148403118540040c03125580000d9500c4601e81011180780b081080f06e10221000c900200f1384000d450343c20174000c80c000010203 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 683099775 1250 683098525 683098529
    0x1a01090603060b0f0102030a08220c0501031d031603030e0a05030a1701030506010b0c010f0e070f090612020405131a0402010f03091505090c0a090c02010509033a05040c 74
    0x8005002d00c0c40f0781400c00940d8045140503c1c0581c0c420811007003003600804404d6800014020840720000203012900b072140744010007220b400030254014401c41d038251048c0700140d01c203000b45c049e441031045a22540c91084132840380300500001118400c0501c40d8120005d070740c4404054078080c40e400e1825640d40e41020407000007041941c42c0c5264101019201c59040300e030403000411959217808020b1615501c91960b8074415503c8a0300108402541e019504401040750300401c0000c0c503140c250000708a103600002541303410704004120789012000903014258041f280083c2949401c021b01102d031101c03000051003080307100007070480c0c51212103415105900030f88801503100e490500c202d0031600300380780082110820380c1c64084000c4080e888903a01c070b01c00d0021264519009000242100c3c000d0340705100e034a845918000c07005a080c06400c2d048440c0000440c1407100b07100041ea2024030b280301480020740c400e210803840d0100c2d08240003000200c10030401c4281010f0500e0100d0742001c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 683101025 1250 683099775 683099783
    0x1e0506120907060c0519080712020a03080108011a040e07120c060306090507021b0105130b0301030c08011b03180204020a080f060102061519170304080106140d0f1a01090603 76
    0x400d90003d80c2e0b500420b00410703210343c4480908250000306607141343d40d400c5504191070400d01440480000703030383c084010002c0c20b06900280380c001040e03d4010103000e01600850b44590400b090074440005016031841c0c01102258041842000154050b281c41c003141d0020030440c4150100100740140c0100700c6041e00c0d41070b44d06003c02e540b03400600c0d081d02c40c10703140480161711140064140f010080740e00039400300c051404503d0a171001035000981180e6400204841c00d0000041003000300c403d803510014120a4001e10000341c4041c04030f03044202c50308010041c9611000f03000c07070000d1009400300300194010005c54031101d03075600013040d071042100c2d07040c0442c039650301003900c0b980001111071090100d203060108202c404010b100038400411210407079500720714404292001c140325100c0159080e2401540c03100e01d0f00c5009070039a01c0c03d90104106002104603036100d46c0f03c13142c2910180d03800110b032010700c40040c54026002c0043e860303400201c1e174000002040c1048950084000c481c02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 683102275 1250 683101025 683101033
    0x20d0311160f0605090a03020603090f1e060c210106050304030e01091809050f030c060402090f04080d020304050c030703140d020313030f050f060702010506090708040308011e05061209 81
    0x4000494056081e80901c04801c2c465480401109100390300626041c00c0140102541d280e40760f02080d071a400c140c4180700716402c15480d404240e502084440386a4a4640482219403600b800355511004c000e003502400480009039000124003007400540401c4c1c47c4148006c2969480d00000c03d20303042640c0480000d01c816601030280d601c10200a000c0d508000d20101aa52002c10924004d180080c800c132618042c005400c0e841c810103001802c20380c42240e0150460780b425104226070030500034074940303449450b03506010104d074681007a140c8901c040200140d41e41c076141002482c1001e100521076152040100c08010090850b41220318044141e08580e1803400c0703001c01303a0320390156088044031000e03000d004201003000c0302c5500600e44d0154083d81e4030007500d022028102071007101c0640140c0c0d121400e00540f030600c1a0012341c00724a610f012120350410f582c0013040242c040c440c0904807060310707030040040c519800c5068014640101183c1d914003c0c440750f44418501110005041d000e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 683103525 1250 683102275 683102293
    0x7020d0b0a140705120f09010e16031106120103060506131b0306140f0d02011403010902070203060106080108100c1b0c080115061b03021603140c01110a1e020d0311 72
    0x405035098940e6040c56a5170711035140c0e00e01c10301c1d03076840e81c1c000c201040741e40d01c034200c11448010030700034602400c1204951007482419820100c10042c81a02024010001000b40c05c0c0d901803091025415030341c0c0013101040640756240014496540c9000340075989190000c0040c95802e80c0c4d440e5141456152001e00c03070190b81e0103a24100b003203030440564003c5042c0c1c0c521046480d0610305000e00030700c14181000140240d07004a90240c0090b046984031583c0000c80205620b020003100c2d005080720f1078126469070406c20081c3d04c90f00302100d265111910380300c103a069503000d041e4002c0d180a030302c41078003008041030070700800e102c00c2446aa01c095181220b050b10f00c0b1609840042654442c0d00d401c1c04008641c1039200c0055004d40c01503003180034201c0c1f203030a21800510704000541c0550b001d809a1845044100d0609110110341c6040c40a42085001c08210200c6c0c1080c044e5000714250304281c0340c41c8151240c0722603040b80258070403c80030141c0c0030180c02541c00c20385642d452003110b2500c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 683104775 1250 683103525 683103527
    0x1517090c01031a180c2802010e340803030717060307051011030f071211010501050a090216062f070503071205072f06120103020607020d0b0a1407 64
    0x212900000d07038200c090568040030b03400f441c0c2e403802d8102001400807440c091b183c90f580c0c0040500c2045080040311a1000c0c050701540c2406100c2c0005610750280034041c0b030f0001c02a0381142c0744282c003c00d041e023450320800e607a215518000700401c84103066955070b1030400750027080268020001c00f5580e11510100b0346a0500048160544001a00801c1050142d61040d5000a6031085403c402e00c010000524a0b1250764090203155100c0c44c00e06501a40f800000307080c105541140b55620303032401b40100990350f11310501000b2103466440051743d030450001440485122004058456400d00f0009103418004090b45c01a002e208000c2c01076013140d00da00390240e8800c010300034066030700c14000341000ca07440d1250b4140c4000035040a0f45007910950701c0c0c60b0035540300311810030410109500100b00305204e24000c840314104680301445d2407406e905206050a040c0000790060f440450a8000c54a0700d81504684507000100c841252801d100324501a20701d10b116000d40521800c0402c07a21 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 683106025 1250 683104775 683104811
    0x50102090a1706060d1e05030307030c0e090a270f0b060109142b1218080709050402010201090209010807090b01030c020606091f0902042603041517090c0103 69
    0x103082c62002e05600d0300c8207420000090040042940c0410004180d469074107000c0070302c0f2040502c80d0010b075480740b80c5580701504507484a140803081c84408010b25a10b5918003072021b40c04100b620b0000303401c0384401200f03000c410102c22108005940040310000388820003034100170007840380303c090900781e4648004442c480d46902c118906480b002c6550486440e006180c1c43c82440000313500d8100401006241d040702a00110560360b05444a11480d585948040c078a00848400748030540e41e1460805120303607600c094490300882d82c0e658030203e4210381c804e4008030591500103144031b4142d40c5035030555840702500c9c845e1189a5240107000100380d4024010010f50590b40c1e0060003d581c0d5884c20b00034002002030171701c80d01902203045007504208402c00703500a080503081c010380350380c2411082c00e083c2c0c041c0085991000540e00d0840300c0b071400001240c05641841c0740025030440c1e919000d80d600c3ca4a41c1902c2070f14100101081078140000842200300300742640e05010400c0400380b10101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 683107275 1250 683106025 683106059
    0x1e0f12091507060902060f0d0b04050601120e010204121b1401080a05060f041814070b19030609060909050105240d080d02031303022104090b0102031303050102090a 72
    0x20269056010800c603040c07038040e000c540e010300000710303070760f003059000030815407240964406010300800c039007000d05410b2189402082060f00c04000c5401e203840040c2004107070403106180780e600d8640343e0960302400c0d01a00c0007000540c00c160210443d529048500140c0c0c1c00041900f081c0303076031000503000b110302c2c02030551803010784501d04e942c1c640e000010054000108441d07003005030142e4030400358032144140700c040314042c00717a240c0140b00380c5011698546042e40c1c010309a0300ca06418040400000e00302c07820b940c03502000310b107010008130098019000d43d44c050708107145440400200058903801900101c0d2050000f04981d0743c42c4040c032944900030a07046003d00044070784052003800c2030039404075114001e01d121401c0100c0104144180c0c1c0c82114012089103c868600702019010092100040c00090b5034034800007015244050314025031041003032081d260990300c400c40e40240300312040c0d15900340c1d000c101281c8900b00203000c2d50042c2642c03805050286000140c1094002140340 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 683108525 1250 683107275 683107279
    0x18050f0f030f18190e15030309130b010c05030c071706090d08070912080a1e0807140d0e010b0112020406080c0a0e0310050f07111c021e0f1209 63
    0x4240064050f10503426640c07444481e0b00001100c0300041401403180d842c030000c02d12288192140c0ca420718200100c00c0785000c0f80b40c001d40c802d00c10780c101541d4009904100e000341601c0010b140a080004960711200c2c114044e05034040010600c8804a02003954400c0c1c401c0c440c0384007402c100c00d90075113548440440e400c101c07075003190901151051280e00040c1d003091081c17500e40051034544910708078540c00b21800700c440704800102440b0080d080154072044a1046a440e0525101e0300400f40411600a100108100505419000700980c0409855859210200801c207180080d96418020300e180742c031032030225007441803034124001d1030b008540541d01306507184601512030207580b05458021215041c1030002043c40c442c4c0c1e40d00c00300710280c440c520301c1c140458071b4105a41c03c2c45041c10041d107103904201040c900791049180005103100280b42c812020754038090040340803410b00b0041c1e0304d000c01c0c40c800d019030310550104c001f555005c40d07410002a07440101000310b036500903104040e19030b5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 683109775 1250 683108525 683108527
    0x60b0a0b0703080a0f1d060601020a1502071509060c110c1e03010b0627010912260a090e0a060e16020a06052805010605190318050f0f030f 61
    0x400240710350080f68001e221250041044540c00b1900c00036904c440103014580803801d204060003080400c58142c01aa007030016040f082c1080e1540b601c1d000000f6a040b8005400058010800c250b00303800007040c00d05110f0400c038000c000d1804201804004203850005141c01c0c0c910800001d0208440d2113002c0004e18001e10700c161303100001d8500000c22a011747c15581d0b001740c0c29842d262140140080d4140080071400001d5000103054450380f0843c1290400c40040c0381440340c00b442102c10310a180d089a031828040245003521f10200d0b4265060303844041d00030420303c00f0603400115600644012074103044046e038800115800f100c500d481100000d9540030080f5400d900051540c1c04413644901c1698580300c055110102503400c00d6034081c5408060701001c205501c29110781010b4580d1a45040c81307d5490910010094011041001e40315400500030788280307400380e4040c141d18a402d4140007404211400d140b81c42e000b100e540d0015500441e204489040e4022040b43c45d843c100c0505a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 683111025 1250 683109775 683109787
    0x111210180903021c030e150907062109151a091317040f0f0506090907050307090915081504031403060a08190210050a090b07020301021c0504060b0a0b 66
    0x8000a450220000d03001d6014004d020114061881204002c981160300c020440959000e00c50389030030360320f0722010b101c043c804080c4101d200011440f4021a88a850310b17a140e04850302845415a840003030440c0014a86000e520401c517410900310890f200d5480c040148071310b5000c1c0b41c0d001c0e01030f0396209a0b004203410000f0740721502525000354054003400c62103101500c0d0041240703481d44140c0080d28010006802009554aa4100c1d10007410054908a04090070711020030328150010f083c01050101c08000202058415a80d40f801450401c0081c45802c0340103c45d000081c02e14000c80c440da00401e60000c92800798801c0443c021685940c8881007800c0f0310b648081705400150599038050419500040c880800300103100310144a000c40b084944413500c1080503050b02c6451700030600009205404003250000e0000c0704540306850f5659680f002440024024402d80110041e04941d1440074a6074240c00da0240c0c1c4a10711540c410000e00e44203034200280d94000b48102000340b1020018 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 683112275 1250 683111025 683111069
    0x90305070b0c040803030411030d0504231c03030e0606060702030304031226060f0316050904060905030c060a0528020706060e0112210912080d111210 66
    0x1c0c6a034042c888600d80707401c0c180c80340800d90550f441510203031101140162009072924003401080da00c145241882490300703140c840500300403240c03404c100fa1640d03404080709007992240c1c0e0390300b4070703d00103400c411440d101c4602d80500282800003900320240f181100113800d50402c401215447ea40003001182054519030714652101100d04810040006910301c0e06418100e400c92099400003607140c0306e40c917160120902c04170b5100f001c02c180c800d1b440940807400801c90940c160042e600140c2d4000b045039680d040007005410341d050f0003811888000f40b9084401004a0040d000d00c04008050006458054207030640809100840c071b8080350101d60030a001883c2c0d801894101c1c4141c0000c00e8007695030000c094216002d902001201244c85000c1042208a03c0c02254041000070101e5100e01c05880040032b841541c025604d030300101e000e1600502108409681c407000c03258400740809030200d00c404042d50421f0400d4048201c0e0a40801c00640c60210741c2802e650700030303002c0d400441c09420 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 683113525 1250 683112275 683112293
    0xc03170108150f0633181206100909020d050d0206011e080613030c0f03081503010e071406070b130c050d05060f0a02070c080a0b0f0f0f0c040902030406140105010309030507 76
    0x101d101d00581030000c0602603590420050b04894020500307000d06d5803091014042c83e503c42003024010ba4001004003d02181c102c5091402e403110140001000d040b10720210328a20300e0301d00050550b05c01c1d03509007a402540020324505a614103010b00491201040265100c01100d005540d03907038000e90000f0310217407141c201c8c1418040c001d1920301401c6c041900c032401b206d08454019400280d40c0d80800c03014040800c0d400040000a0307000700400c0510038891516200350340100d00b00545081c404848555401050310800e83d0032402405450911415240310710307118500071500c0741409040000c0c00d10b48078045484954000020b0000d5a41d00c40c02d48009982c010701c0100119130034003070f10010030031003145c86010b0a821001000145102d0800200c9514010044000711a44204006064102444064100007481000c0c0160b03100c40301d005002c0c0c0541c0d0003480c0800d2010082009205040d0403610800141180201041e42c07120011020346e58610409030119204108600014074291 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 683114775 1250 683113525 683113579
    0x118030306050306251e12053318090a031205041a0c0c122a030a0e03010b0d240b03120d060509010617010602060411010c03170108150f06 61
    0x201c0c0c9002c6ca0b9108500e40c24000d541d8445113400250782c1c61800314041a10f10810390840d43c101224003a03505054400301a40c150b5500c9002c0b064805103052840307031561000418803a00f4100c5054140c13070603000b0035980d00a0340c403094000801e0780081ca0900652032180ba400f69403c020301c5010110002d08a40716200c0241c8600b00415040020050388901071266414041d01c4d0404ca6580d00303d8001c40c00441e0103038081903155a00c000001076481c44000003110500441030801002000c2c4200001b40184016a02e880e00681c1120b078035010404241210320112203404240030215094400324002c945840c600181c050340148610101c4d200010007402082c04500340201c2c9a41d181d00110380383d51002c0e8400000b00b00c410200140c0840b003d150300c0d005d01014402003280740340c15221003179241170184115044c4000703440340d442814441c4607102c24101d480301d80c00a00b0759650f00c1041c3c1d9101400780328281c038503044010420000080070440e018040040c803580c822403540780c5c100b03114a440303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 683116025 1250 683114775 683114777
    0x303050601090509010f0807050a1409040f02100e01020f0705092205031603230922140a06050301060506030a1e1b0e0319060b0a08011803030605030625 67
    0xc4800084030b940e02280d1360301034244c40041d40b5140c0d00d4503842516100c01078101902c159100501032010407400700c64001003400c00c5034040c0c0b81d5140c5050a13050005495000382d00400c55094006405410000c950503640003a400ca805e6803000c580d00b00d882c1c07401405402e501940700404528484541000100b040c055424100d00d80451130b0368161440d030022400341052014118040c06041d0400c1030300004005014114041c0c424003039041e00d651003843c01c203610a41804100090401a8100b00c00000940c10010421200c0c0160400d010180442e0a81e5500e400e0203000314240c10107000396401c40740007406090860301c0c2c0c40041c10242081d4818192840c1d60200203104a002a01507402000b120148503640354208890083c0b941420744100c0e8041c1e40440c0044d10710303100080c2e20022403500050b0020303509000000246003518181c1c0310354105d40c01c00810780130013018104103256070742c82520100044c90340c4000381911a0b10858001a110031106070070302e88088903404584500c44e00d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 683117275 1250 683116025 683116037
    0x190b120a090c1401021f0603030807050711060703030915060e130b0c070f120909050115020303390912010c050304031214010801140109060f0b0c07032315070c0303050601 75
    0x1000c0e8103954440d90400c0000304030707107d0700100b0a150f000b41500b5000782c0185002c81c9032100c41e0b290450310651079070780d1074012400003403a0350905100791305c007404203940301c1404c40d01a410400c9003c00b421482c01a0780084000c1c401065140c01d203641d20720141a80113192082560b0b07200543c0d00180c0044e002680d00c0300341d000c078000c00074400c88181482100c0c5a190111440d042051002c12580140c0060165013144851000b0040e000010350303520203d480340a81110107040054501e44401482c0200400103c014524070380c607a010262612150075503824108944483c030306400d0300c2e42a0741402c00328004001080210344030305812a500b041c51f100205e0a91962a04404842026407054480740d5440031032410314500070354194010120b030041030250f941030070780c00c150056a500c21f200301020001400c070340b19982808048025034220350380c5034010804251201030f501c504c1100018038022a86141002003030707003070080c4c080c078060341d03e2040010b85554250010000904081d051040c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 683118525 1250 683117275 683117293
    0x910021c0f11040e0103030e0f090613090501022a0312040f05070e040b07020d0309050c01050c0c150a0f0504061d1c050c01090b070f030e190b120a090c140102 70
    0x6014003d0004040c0d801d1801110341c5181002408100b0f00c03c180e522400651404a4081d542ca1801507003100b81101c4415000b100e4010210091000c0100248175500129840380d00d81204600c84000039008002100c1c82c114a091103a26031040e11044881d40d014140400d01060724110f4800030a88154112200b580c0ca034143c044112034110740446107030048804002c01c10380e0510405c8088591400c0c14821540a6650203480d002203c2010703041000100d201040d8880070003120f002c0c008080d00c840c4004816448030301d040d40c8400342d41004503c80da00301c7e41d90188243c0c211000c56190ba51071310030391800a11210840b041400c45035602c01802c07450210600f20307606c33110141e14402d600034800c2100110014100580e9075011501c10601480380700c001c5000c00700c030514041d1345860705000c2001200c0000e807011030008070318034102c0807400c030100384400a10001e010104082c2c070070b0105541c507807008030107039040120024156104c41d03904001070840c510038064064014010303135407948 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 683119775 1250 683118525 683118551
    0x31d1203010911041a13051e010e0102010b0d1103011d0a020103020f0d02120a1a031b123c10052a18010e0306131a010305060910021c0f 60
    0x820038001c6072120354800031b010b000900e0103100d9100145020b88180301210f00c1e80314502a103401a541e841d041c000000341400d0280c0c070031751000c0e440d1280100707e051f4080b07040c205103c028841d42d105902942c6410a03021411142400ca0744a4052200042c8051030752640118081e4126114040001105100d00e94100325103001400c0002c1003020720b000c2c40d2411045540541d0002e147d0480498181982d00c501c44e1804200c01490520150382c0310f2801840001003803808202105001c080e001e60b4803205854505c112850a00070b00e08040d04070101d00c10b100304403034000c00c7d511105c403590140d81404078070204d03504266800036032403900e4134540c00600922604503100e00000d00200000003458202100001c410202c1280e080c68140c0300014207001003030ba59040a0800201c0c00c450480320300400454506844003c0b00502641019582d42e26003256149415a041c200078041c0400e89804902c007482520107525819054821111400c4403040041103501440c0b00101d8580401c10521 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 683121025 1250 683119775 683119799
    0x10c0c0605130b160611030c070b09030d020f07051b010c020111010f05100602010e010c1b0f17091c030504300b040b0c04030b0406020c0a0c06031d120301091104 71
    0x2001d130050640c140d00401e46003400c1110100e4078074198605041c0140049816101d0a8421107940b0542c460056111091040c2c40e501a604902d034102d4000140085145020006410404e101d50101c030300b0045a407000401454160200c140080c2c2d040c1404005980300d00881642c4030f00c0040002895080e113071505050b02c408407014041d079080032204000c41982441486200b0807244000c00c135907ca000c0b00207000f03002d490640d041c0c021884803490140b00030240d080385259804403038191024801901c026079a0040c9104511034170310724030708180e141e07040d0400e80c801c1c0c6c0e03160380c44520309818101c62403010166010102c201c07444080021000e00d91600410b140e0034000c0041800620b0725252a842c085030090481d6444281032108100040440320040e0304290311802c0036888107003800e50f10303192048202c4064007002a1920005980d50554080601001c400c0d0001925482621199581c0c242054000b82160020401001b00704180c0c0d100b100800d40c010b45691a03e540c4a08400c40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 683122275 1250 683121025 683121037
    0x20a0914150a0c060507021c0203040812090a1d040605070509030606060c07030b0c03040b06031b130b04090b01080708010207020d0f14060106030b01020633120d02010515010c0c0605130b 82
    0x964001c8d1051948030011000c0005c082d0103600c010340c034044c1414880c589584541864620f68040801c00d0110780d501c001c000b0000d81003180d0300d41401061110108075404080d1010b492551611003c85c0405125204640c0c1030b420250080c0107a0315503d040c8001540030510400550080754404800518a0342515001c3d880c82d80d60340d516400c05007020851b600d070140207644254441c81200c100e2119a88010301084000c4600c403094064108081019180c12030703987d68001d18180988040000400700a41642c00e82411190110b8031103048d07a00301e100d11100698011506447ca00c0003880c2c2241942c0003034410300399501070641c0600544e1400e07a080c0c0140020a8451400500c90350f41007261540c00001d0f550303948a44404610400d12884030406003c1d20344000007842c0e120781c1c50710000c40960350021011108445182c4800034020300c07041c3c4201c0f222070184e030322804d121761007071900a180541041e100180e16140c00f005031841d80c070038403022501146603078001503490101005410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 683123525 1250 683122275 683122277
    0x180a0b0a05071209030b0a02030a021e070506012312120c031806030112030e28081002090a060c140105070e010809011e1518020a0914150a0c060507 65
    0x180358180343c034058140f43c0c0c5162038034003040058081000841d07900c1c2440d5401440c02ca01c010307a2915900314a8019200b1030552058441c0304202100c00c41c6403890007414614020416500a0b03600d4800c10510340244014400e04081c0941c030b802c03507038a4501c00d841c01c5495980200c4400340340ea0504c00c603003134000c90740c002d6150b040441c0c00c0203044a26101e640010780103e8059196604100e8900042402c500d8042e0030082650f080c10748076140e10880c15100050b415000c110492000c07608514100f01d03014a00044c040c110341100c00c0c0616000355086c582008210300425410000304580100081d481a82d20742050819075407030300c10070b00c1994042c802d150b490241105210002502c0c0c410302820103c56685040f0710141d0f0000d00e0090220783c42c8d045100407038940c483c0c0c803460f00c1e01c03425500a03502140403210075401e011425402081c0c14800c075103524a800359580715001e045260401019001541801103011902101008050a110508042c10207401c1034403000102d0b042121000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 683124775 1250 683123525 683123527
    0x7050c071518140d03080403020109021f0e03030304110105070c0b0301081014070c140f011b0e1c060b010c08070b07030510080c090622021e0f180a0b0a05 68
    0x5590322902803400050030204a03c804414551800b10782e15100e4401e02401b00001036006c901014400e4002005554000b008001c031107040c0240b050920703450650300b4010401d12040d4002605010007641e104070b400401d0390302080c1d413040042d216940880b000b212141c0002c680400e90381d4088000d54040c1c0b114000074150283c0301207001c0101c881c010207503004142d40f9030800c0500e541c0800c00b00d0300c50703034800700c0b451180560000c418039102c0045510b80c455420302140f1040c043c0c01d030702c0841c5c907100301c0d0340c50140d0b001201082c4516042d818880c004540300f800007030317000320301581c010645401c2c061514041040d245d855181c0c19030850708085070b05104020034000d50950502415070040b2800c0500b0b00c011b4a016446596180011320a5000310386440c0010105d503100003c26050301a80c103003003086074141101c01e800030740c849021071a05a5240f48801581c0d1411360903110a504d0003051107251030030840c9804004081c00a42503400451200c002c1104c60164015000016058580b5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 683126025 1250 683124775 683124797
    0x909030531080a02152b27060501140d030e01020703020d0602120a0e070314162d0b0909041401150905010e090a0b18071202010210110307050c0715 65
    0xa042c40900040c40d1a05c60103011440f800404011018031060081082c044500980d030701c5280039007040d02d5034000c1000e020781c0010f050440449088135580c4203034801c206a07070700c1d011801c0d0702407d1a196540c100d90070032400c41c000390142c0d40050201c1c1c0140100d458003980d0303500244409415010441d19180c004c01d0000b0004000700b0f00b84c0d004600c4c0c2e0f00922000142c0c0010a81d505014030001c1e2000030f40c400a040c0440040c000cbc007600e5414106029603041e242d4940c02c0700d803034910801202c00c6c0c420752181030250b80f80c0681403095038150341000d840c0460303000801244000140090361162418210996000e9003445000e45010072880b0a180a903c1e05640500316074050707020040d00b0580b0b000b00030090724081245142c160340503146001c1d40d00d801e1031442400d0201c2003503500b644180d0401080c10356800900c00c0c24076100b41d0865050b005042c9034401918280c0c0c0400321005d0382400071401040c09100948007000600c0110740603590317184911550243c820b6100b0001c02d00704441 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 683127275 1250 683126025 683126029
    0x80a1a06010801210215040b03060108070c050a02040b19031209061b06090f06050c0403150b0a1a0c0601170d0c050a20030604110a0909030531080a02 66
    0x148550010342400c21070700315854820880d105541d0941e6015954507825460000c540d0b83c8440d81d002c6040da110300c940c0725070711014824000e0b441130340e103a808118000c002400b80e40c03081c010301c20003c0d2311001400550061b982448054940c80194550001e0785140181381542c103000c51900860080c4030940f41d070300c01040c0150a680d416000301041150241c4446a001c1c00040c0c080c0358030ba4001c40000c0d0f09000c905054501320001d00c0020811401d190501200030b08803400740c01580d0080c4844440d4480940c091011142d122080c503820000c9000e081100d24520700040456500fa40c060514084400ca10642440000d0300100030b03000d07041000320b00c10b6008020100204000b030408402410076901c0e010366451903240024080d8169103400c0c00b044a80302070210701d021000d030851300c00d030030603141044800300c160b07400c50b00440410000080c500303460b00650390322507015190503180c9460110014000c4481c60b0b4126030201ca4200044040c000840c40c81d030081040d40701404001500d441 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 683128525 1250 683127275 683127323
    0x10314160801080f07031401091208090c1c060b04020f070c080f210304030306120f030e030325060e120c070b0301060905040b010306090f020d061212050310080a 71
    0x41460b8441081a501c042d0f001405c1420360740c0100b50300c055480c100304034a0245c4a0b516005082015107210303070484540140140e4061a481c0e400c0d00c40b20034446043c081d1500307200f10300100110000d00340700086100c0380c0c0030320620310006c2c001610380302d010360f0341840a9000320021207424001010070030400c0f105001d007a01e482c41c1031020b003c0b4401851180315a803404898410a103210000c08201014000e0717003c90002c1100c0b1800c4042c00e00541402c06540c10042070071b03000302e41d0012030b1088918000c0100c80c0740034403075001407000007503042002d8440100b601c1c04641455030346809241c003401c20400025004030b01e000441c1e81c0c0400c0841c2c5c03410040035901c5448104018070040c0110742d004007844083daa019100004c2c454610f00040700035000c2c6a00841c00f0500d00030f8010307456032403900103284011510105014803651449041840d10072400f014241e02541c130701c4030f0300c610b108000440d08400d58011100a05465a00041c20030308580c50403990001d2007500482074090402e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 683129775 1250 683128525 683128529
    0x1419050c07020105120c0d050403050c0d02120f0d02070204021303150b0108040b071710090b0306040803010b0c150115030f0902030a0303050a1e06082107080702010314160801 77
    0xe4419410005280d001801c280680c00040640b0100000000c5da032002400544122003010070007401541001d04000d041c42d0310a0a046030203014182140c1181c80c00080d2a480120800140c0e0f0303d4800c1102c400349840d00301c0310015521903001c2141c64007507600c2e400a401e05004828081c5011851031030706010304171501c61608030550401c130b40d0f00c2c003030307a001040a41e20a400482411042c1d58034201207900342508e5040003442041001405003046032030900e10107441c14103404001c2d46110b5402c00d03031b031030f0f504a81c01086207100f00014090036030004050301c5c014081c08226481c603002405040c28210090b0044d207102444881d80042c4903a15010b03282c0030014164003004041c03025008240c40300c440110250030b060312140407030200303201940a10340d0000c1c0d250711034040140121421014045178420740350140306004c3c5105103080b03100040d2400002000781e50740342940942d10700d031040d0410107003030341855a1208419851140030349082d11510651012045000505030302420f51030040e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 683131025 1250 683129775 683129791
    0x601051f0e18040b040210030212011e031e02090105061602010e030709110702030706020105071d06120f0a05010e011a070f081309060803090105040b0904141905 71
    0x20400c58205a00c0414518944035407030301e0301d20041660041000380480d08440380d041d02d104010403040c400c0c58003100f80201c2c4221030090251551440407000c2e802278410111699405c503004100300000c62a128510b01c01c0002c103040582c0d03480d101c02c0c01161009007d41729a50300a1030322021440d001d100b444c050442220130508100445044145242907440002c0c1400317050303190341c1c440d69402c00540c0018600c0031400e00c61307a0005101184644c0058004030300038400c03140c020070098010301401b44606220ba980101485100011007804d414000070075070410401c12140a85811500c40c07240310700c1000e4074103026401d0444102c4218ac605070300c05000c0c0c104c280c0041c000c0720380840c5100d00065016030b00c00d44549090a116158020460b0003d094840000391010075070345c01e54034801124018002044003c0c0d41c2c1604980381d03c20b02420600045040105005081104014041c071031340203000052500c1001008154150090302c000070141c1d855241d00c0c071241ca080c02503642c03003102 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 683132275 1250 683131025 683131039
    0x31505092706151905010e0a03060204080f061614030705040f0906140d050d11070902041511010b01020d050d18030e0f0607020a0306020703050d090305030a110909010317040b0714060105 82
    0x401505040c8075907485c094030741080052440d5800070340e90040c59001031504048110741c0c803542e401040340c1c2e958008030500c0c0c1c81d004032800030310803a204030b0100402034030355110b0b2800c11a0001c000411940300030002c4050020903c00030645140003050344025000c11440007400f10700700140c800e0881400808180721303c1030816060b001640c040f40c144444001e5050500941080902141c104549604441c007102e00c00f240020391300c1440a4259440042612640e8448500d012440c0c00c0c3c40c1074000039405644142c1c40880707200d114400802e061245000e000541d24001ea0091860303101414050f0001180c00250910910b454680240e20304812036000c0d01d841725940c04035445201c13912015000903801302c1e0380c1003410701030b0003155907803030418804015a600e1840d02070f0140d002596044120b52424100c079412060002c2140d0325070200a189140c0d0780c3c80d507a505003407003e00e044810902c12041c0000500e44031104060710900d40b0a400010041e00d8000d87c01c0e160030350581c855489242 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 683133525 1250 683132275 683132299
    0x308071e0207290d0b0a12050307021509180402120d0e0d17041211060c101a06041d091c0c02010203040e0901050403020106050103150509270615 64
    0x107000105041150b40e24500d4043e0b50745070030746601c0003681c8001000700566000604e204c500603154000610650110b88105170301c2d03165a8080303da074003a41002042a0310402c048800f41c64070b0080c0d1a807814081d40d03d10310b86400700020411100c50500e0a00c2c002c603260041c07004503d8014901007200e4375100040927070001405000340700b09104100c850141c5075070300740001071104000c1400c0700c04941d101e00d640c1c0c590b1390707002d82a049608003c0903115503200c08040c400c9483c1c010200c81401c194180102441758000210100800c00d001c54040c030070003014038544003900e0741c00180009207004081001c408618100440e21600028001c18403500200140350460082e507680c20119142c502d80102c404c561480141d14500c1280c10100f048074450040200d0850150010b91046220368000d018155650340107605039800c0c10f04048814107406420720080c20451100d60f405003060344001e401000c1010018a443c0040782c1d0700825030801002c101d404d50060a110400f25000d844c0340b00350b64 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 683134775 1250 683133525 683133527
    0x402131401020f0d090311030a082208060403080103080c0c10020f0f0a0803010303120633020c0604050f0a0b0309011d07150809030c2a0603010509150d0501090308071e 74
    0x6500d41c01b0040c1a4185003d041e0070a440800c1556903680c0c1c484060b03591040f0000c20a250f0100ca00c40210785850b103000042806007021880a00032030341501c440301c4076400c0d595030418a82000346000d4040c414468150000e070b42ea40c001240c0d00d81540c0241c082900c000000304d05001440e6100403c41e4003130007140780001e19200440707046030b0701450801461082100c150001d041d9640c41251031801305003030f944414203130051101c60b548140c0e01201b40b0780e100c07040581e1031340d0f1201041b66000c501807200300501d0900080000c10140003c0c103c1c42903644030341d00814250029a1005156992280610a8413000751601c03000c0c941000001d007403080ca0400d18403c140d500d10300346003c00c240b10001c2a003040007001514883c42c07069003541c140041c0d03d100342c2d504031025421418100d404540003103050400c03800b01c0c0e041c2c078800b03405a80309640c0c0709240000901c10034000c5401c807244000c4140401c07002e10911482d28401c1d1340d003058501306800003d001c03000110401601d00380103c0d00c000d503d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 683136025 1250 683134775 683134787
    0x23010e0307180e06010e060904211e0e2b0203120c210313020a150201090501180f06111201031506050405091e191b060e0a0b07020402131401020f0d 65
    0xc035104a6406007180c0c1c4514000c40c3d0030b0f003100081c040b0a5020b44034407000351b07082010360403c0703015947d8040388000001c8044a00d030cc040c914058211030800c0d48080c101c400c2c036035100c0420350b10910058a42800b0b0380400d26110310411071215038600800e41009690301440b41e04500c01c204107030652020740301e1501592a20014003070a014092100c1943c00315164100101c004059408a007400c0204640d0064060540c0920031250765180c01c5425010280959204828541264030240d107140303103541d040001c1451180190300e81c00e042c041e400138401d842c00030b680070b1445541004030081c1d1050b041d0f800d85545030050351049080504100c41e400e0005445580500341402e01202034201114250800348601c40400c01412506058001d100c0079105241903400081c1c00000e5841d0b0b511421a40c02080c001a143c2c41042010100117480100026160311400140011310b054050b009241a1031070fa503000041403413604e01c0c1380340c21350b8040c0b10708503600b070700d00001d40583c4900401c02460 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 683137275 1250 683136025 683136031
    0x9060f0b09010e092b0822020904170301080f0c0603040803160e04020d0c1d18090304240f140a0c140a0f020a0602030423010e0307180e06010e 63
    0x290342d060400101505002c00c1001c0074500e00c02c00561403074020781408017076102c801200d040031510000206211a20114000d0380e0300c40d43e60642d01c9200b0040d82007241e40d0304040c0041d22609501003000d8004110b5400543c000c000ca400280b562240781ca00641c104641200b409104e180c0c14030030040401c401404590707110304030380103512640c00075810075a5051546032116420500c0403400c03220901d071603484000d034101e50751100c000d07190a2040c040701d014801e440351508030b0305404262013281914811960000a01e005407070030142c035031401c2c5c036841c1c08106500c0f0300440300c1552403000c00e030060f070789401c24003080c5001e0a03581030a00c1c0581da14416604100d007007000e02da0411040c4541c0d5401d4800700070a8005440c18440e041c01e103405028503603081644100300000c2c002903014000403c80e41181e078807070300c2c2c201c1c411203010b10001401c1c401203013181840300031030075030420340e4090000c500517040310506141c1981d03640318003c08607000c110010941c1ea008070f006000d0354810701030681d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 683138525 1250 683137275 683137289
    0x8071802090102030c07140406090522140d02071502010920010203070614040b071110110910080702010609060e010308031305071202101b020d06020c070909060f0b0901 74
    0x203a41e00010004030728610420400d40320034000d40d840840c0c501d01182407040c101100315400d2060584901c08242100e0040d00d20306152030f8030308819101e4071002002d400e20315010f4501074880d142075400050804102101e904010f03005840e050103404090b00c58101a5800c0780f000300031524540c0c1d107580c1703c2c002d9801e04510480e00d40c810307094168401c0086440d603136406641401059040c602c5601001001e0303c0c100c60440320751001461a82c852a0341d10354a44d00c00340103001c07941c00e08860701c000b880d60400e088a400010030480b801c0340c4a00f14030301c0c07036a00309540d00d060360301e82000c000f42142c481da008000520700b80035040145220444000e41900e400422840d40c03612480744411241c01180c1d030003041d5000340800000e48d5007035840d41000345402074030043c2143c0b0080c2c0c401c58120281000000c2c91190324424213016042c5144011580340c45284014540310300c800c1914504040c0340d0240300aa51120000b0040160901a58981400b0a030040c0002c03c45040050300741c0c181400b40704 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 683139775 1250 683138525 683138527
    0x120a0c08070804050a061a150c0c040209010912020109030807030809071a0a0806130603030f0f050f030a090201140c010614100f0507031e0f0e0a05031023071808071802 74
    0x1248a8005880c02102c0b100300812185c0d40150710760023002c00b50080014203525000303089144a042c20507000700c0701c480505030749080c800d50030203001c20fa4481c580702050741001040d40000c13000500040c000c103800c0d4000e0311703500121f2a2900d0020f01c1c007141c5030420541074803455910413180c0304107800c0d12000c01550511442543e00e0700301041030703c50f82c0d1109800d264201440042415000002c20444074915513a014114103400416103141c0300b0303a58900340408042002540004031a880004807d10514080440d00b240c0008010039400c5892040142e0b50740744420040c0d10500c4210164047e8203030f0b48110b02d0318a03144007804045d10300381c9002c1409000192030701018841c801945150114610303007030486011400040075500164142d50204000340c0303040311140303070030805d000848100900401c0355030000c1000c0b001800c0080c92070400a10301103004186400300c13080e03041c420f04081c2e40e40303000303051002000e04134000307540e0140c03049800942d8103210000061131500018a180710000d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 683141025 1250 683139775 683139791
    0xa05030913091505040c0f0b0703030b030322170616180b07050606040b06130506130803040801050405010c08070906081b0c0c0f012a08120a0c08070804050a06 70
    0x1400160501802c001c000c60390481944101d5003d81d0310040c0038138005c2c41812001078442c41b4581c10652540958441c50b001803150100003886500075401b0220060166810100b410380c40d02d0000201d40340c6038100d000031810030b010035641000441020390302800184001d0601ca80c03088010314074448546c003007180e0021400303054080440100d00130071a80a500d0340c4c448403400c0040c2c940c5c1302076580d140b245051480c808101d14080059401c1840084c1c042640c65160000f00300851b44030545400c8145400400002c014105101800c01041c0f2100085003034034003403034014211106003034480d003440b407002c09001e0442d521210820666843d401c1c591144d13164441094004015141d00448008000601c0144858046034522103840301344c525580c0c1e00030320320055030a101d0f10040101d400007503401c0440d440d10500c0390060518054a0b041e0300e0810996004004171a00711103040e400340d00c0354012503030180d201c03480c6980f0100b6480c0c0088d081c18145d590f55119600e042028050946070500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 683142275 1250 683141025 683141059
    0xc09020304111527090a050612070803041e03080d0207150606030b10020102041404050606070b072001020310180f1802041b02060103021002011e06030b06030a050309 73
    0x1101840c020001c05036600e00d816407190260640c002c0c21950614a5101c0c103901044e20078000c644111540100303031044a42c1c880700260020000100410303031000b00c2d840c000092a005029800203041e0000107196298208109840c4028003840d103140104141042040800c0d905000c2d20300c0011184805691025070b8100f901414494001844045282840000f1983e40582c071241038000195040c4ca0302d00d550034400d80c02c03800750740b14000c40c18001600910891816034009544410f00906c2c484c248205a1120301003540102c80b032502140c01d650580c01c0c0e40710f10803420710303050081200a6180d440c0c00640c0d03e00503c030358400d0380d07881a903503a11a1074081c9250840f480940381d9110030001e40c10b814811607010b001e40340c4240c0c06107140c03c1445206c0484140c02e14000c100503002070030140d1841d824411030b01c02224501c1c0455603104036800d10000800c0c0301e84d04490443e0000b058141c21824190000c0300e0191000c0c1c4280e10400c072200c0010f00101c1687d080d80401c440c0541e0203c90b101c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 683143525 1250 683142275 683142293
    0x100f050a0e04020d29210a05010509070f090e10050703020d0c050d0b06070c05010c0c0f1e060216060e0d0b0a050f0906090c040903090504020d0b030c0402070c09020304 74
    0x300c0d00b5401400499a00303100901a402180300c000000e5014a080f144681506140401101c0c5141c0102c02c032032100c5240c2c00c500201e2108298014125000c04445440f41421184140c54a15450f0060042089050000c010000107003030126030812002003400380960740e8681d51444c0040c142e8031400080c0c4658000d0f815199040b2016806220720511540700401a5210b402040401d6180146058444c01c02406540342d03603510206940419042900540e8a941103890403100065191400b089400ca980d02901c003d084070003030701c1c0040d00b80c2d800d001040c0103941c110b1400c40d40030546c82c01074a20400100412100c0c0b60030700040342c0c500480822100402d150002c0e14011801d814040130390b002d40d110307034441c0340301e180650300d15110b80f4440b40d120802680d2696195000501c0a60319207010f500c5207203d2442404c000010954900c00310382660401c040011500d641e41013090b441341428004500c90785800c9608501e004035540d100c1031900e0b024002d400540e80c0c080001410016410 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 683144775 1250 683143525 683143547
    0x106231218030c3009040f390f0f1202040906030812100302030706050310051f031406010203070f0f171801020307170a0c020924100f050a 61
    0xc801e5035581e030480c0d104141c0d50245510801c08000080c10418201034481010101140c007004c4800d280940740420080640210721035102c90316a0f07440760b110780c11150050545004040b10a004203490171494039103181540c0c901035000c0c0150700707030144a141c0e405000040d8200c018207008000401ca003010400a0107190842000d4501c0c02c800801030000c0580074024841032000c42c1003c039034031200b00c1e00000d0041d210081d010340c45880103001c44c5010710301840d40480d89032091048507030307904002040a2190659042080100c503100b07000c0d41c1c0d140c015005041115210700d9894202440004d68a10034840050440e131b4210682e84108801502080309068100114030303140034901690180c0e0740d000c0d414034081e461110319022080d500220a44101c2600450741c88400150421039207074a601c001050400c11100c0c1070a080140d507001c52403070003080b141d5859502d0840003031070680c009001a000d01e2048044400700d0a01a51001100d5103090131450255100c0f60015801d8034240541 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 683146025 1250 683144775 683144821
    0x13090c020a1502040801060b071a040305090301050708060f01020c100f0203071208070207080105042f0a1517010b0306150c0105070e090f070801091116060501062312 73
    0x5540030030510300b4a034001d0000e6842c0c08008100090744c60040405503c01c02c880240344088040d5808c452194010301280d01a0203801c1c101d203040c501d000000d0849600301d8200c40840d403032005000b41410000e0665500070030a000600a520000000840380014109000c040010711901d6a1542d03100b807094507005640240700e0109130110000113082c201c41141d440c401071166540000b80e5020501510780070307980017144102100140360f024590640103000f00c0755403211504446085403545110103000313000c652502403c0c1146004020005501600004400070083c40140013885c032840441e500902c1c12180110704011852102041d4000c408012955528100400c0091361b0400310b010400081103480d021190749071094130041740310a0718100d0000f050074005024948150b401400c1511070035440c0c50030005044c5840b005201d22020031100d1503107030001005600d8000c42c0341110720f000c059141444072400703000100b06004026641601001c50000304001540c1c50004607080901 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 683147275 1250 683146025 683146043
    0x18171c050f0f0c0406051606020f1305010809030403051e0a0b010e1f06020613020f0613030510050615070201170103050a11040e151b040f0f060513090c020a 69
    0x118001c80801040102c400d00d818204510000e200700500c031080b581540e5040d1206410140700604001d07691041e207904a0300b49500b08003041040701d20101400303000380308203e40e17250f50317003420001403a01001a100e0050341e0320030b00003800001c0c00403400c2d4403908600256901888840c900c15480c002c1043c030042c20710803040d0000700d820340412510600c90b500e004040c00700304110302ea064946070801c3c801d100050b049500410100c06107400e004840c280014110300045c400c01700080c48581c09501185c05003015a4410001c21078184200e06100c42c2101040210f841c1103008941c100301440401780750600c00080c1c1904580c012002d10482c6954001e0039001507840f80b4000713a403485003540981360b101381c1045654061810340034808001ea401e20180c070007007000340c62060210f00c001c2c10316003081c0340c5012000c1c8151200c10240008054840e00080c01e0ba01e4200c0c1001f00c00d40750f402420400c00108040e40c013000059509a0441e4603070341000942d41d0f40350b10b049003002c1c8480f00080c100341c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 683148525 1250 683147275 683147281
    0xd09060c030e0a053016030201080a06090606090302190302034b06060a050f010c03092d0f120809030c041113051c060203180f010c0318171c05 63
    0xc000c00c0112501070f22000c4034501100300c40181d641b03204c4002c00880860031103005100652040b00115040481c181c008220759495901440c2929580d401127400501c0041c401c0041d860a803007004002c0708121400d9044904603000300fa1180c4480441c41740a018011456074401384c0b1080b016079948180620501c140c0840c0307903002c0180006010042c443c424140890114038003c207103141181e42c02130002070000149401503171001c801113000c0e014414442400103480c1040381a221b051081e5010300507440c8007811041c543c41c180f82c1c00c0001c8285040e0030600014011446082810307400140090f2541c80140000f8035103030b201440280c00c6410903000ba078900303a2400143c100c20994912881a440d140c005002d107031002460500c0c1611503a803060030102d010342d40199008a04200f56000350064503425610b0540b4880d003240107607640b00329018105e5494414100c110818009811072070f0310a4542c6c0071103680d40700102200c1c01000521081c501c203c407000d02c0c602e08081c14280242c0c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 683149775 1250 683148525 683148559
    0xe0a060e010b0a0512190c0806010e2d06040e0102040e010e1b030108100b0a080d030603050706020a0218130807030c11040203010302010c0201030f02041d10090212041b1a0901020d09060c030e0a05 86
    0x1d40a40f1401020500340740b002007001c813300078108005041e40074100305617441d0001c05c40501481c000c0030761745550802c8042a001020300c000d038082d16201e2820307407040c2440149001e511001a8410351a1041400180200100442e21414400300488080b481304148400200c2d03000580c0d111450314407030b0313101030700300075416800260449000d1000d440580d59914001e036103850b916803000b1f41c402240110b0000006140c907c103031b0001c1181c0200c81e040d1402d640d03112119841002c050300031414400007101000f081e0b12003000e0201058800f5411540345034000b8058040c482c0d0020306240d2600da107034070500794980c10f540050200e103445400e01302910080701000001a00c01a424a90f441d1004ca69883c02d4000c46034140c280c4000b08070030b540d6071303140c42d0f041d100f0461410003100c46401300094400b0f81c00038081c00a4461001442d80e5113401400a407034480c04400f01c20600003001c0e4200005c5810141d0f182d034050b094189040310807080310000700140101d80083d0b0703001e800e00b02c61180707032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 683151025 1250 683149775 683149799
    0x100b031b1c0c03020c0c010c0f08070b0a06050a0302010503240a0b0702040516050306060c01140a05070e031c1b02030307030f02060a1404060e0a060e010b0a0512190c080601 76
    0x2091880701c02c0103902d0001004400343e20800e58030b00340070f50050b06002c90651043d0301c0704800c28007400790450324082642c0c4e0240b0030351154000fa0f801520280c02d000d5803441902c180802000200d4031150200d1a49d40040c0c454080144503107071078000c2442c4101c82031000301c0c0900a4420061408207100d80341e180d055011780041c14184e015074034200c000382d01601020541c5840303000300c0e1120380c1940d45d0030341000610352260701e0703c611300d549502030100300b0780100f849030b401000710070004900e600c0c140c840104446c540b980814802e5003c01501d0440911003483c000c5d040040e0710707140c4007200c2000c1a45040c0711000070000c0d010300c0f00050802c18542e00014505440c074141d0700703840301c80d00c82640d20030030303a41860315900e650403094000c0340001d083e44e4803002200204005440314100141c40e104102d03188070741e03481c8080c0d4440c150480b241c0ba241992001925003190100061382a2038a680d44c1d407081e18200068011f51810030302c003402640f519820081841104660096031244680049 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 683152275 1250 683151025 683151067
    0x30601050702040e030d1d030403062004121e230f030c03071101140a030f0605040e010e010f0e06060910050603070f26040f020118030317060306100b031b 68
    0x6d55182c14a081c0c8511100074010286607410341c01541047e040d5243c000c020f00b9084100b8001051035101054080c01c004050b0004160802c15250a00c046003411416080850545404030b200340c26002c0000b5501c846088503052011035803604407554060b050300e054110307401d555135403202081e8016154000802018803612407102c0103d0321841c8001035600c0120800307040a06c1d00c09000c0d400d07080340b0a40c130000710820310103030214540e80d955000c00d00300c0f01c0103610982565113130560400041401d00900203d03c0800004024850300d040000c0d44418000d04081e108241c20720118005070f14000c0d00b04007a01000300703925544e04209101412003408001c4e00d901007409010b0b00040390880051980320000e00b442e01d90035a94507581c0c1d00500f0b102c00b500890610010000c446400c0041c411610081d501c241c50314054041040503900070980024040da12951000d070401c00888484044181190500302c0c41079202d1711380f81403400d0317081c0e18145e01242c800381c027099900e41030003400030b0415 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 683153525 1250 683152275 683152297
    0x13080c0f0309130e10091e050a030207060503240d0501020a09030c0e040c030602031015020708300f07020402030f01170d050f13030c0e06091f0308030601050702040e03 74
    0x1030150301514400a803012191000340e19080300364500041c05c400d070401c0080078800c0082c040c2000f00c00c03100b00c101a40c251015030341507200250680816404102d640044c0607030381006821481c0c45880035290610410300000010001e0765155070301d440d9544800701c1c0c0743d403040082d51906d0b40c02c0350081000c1d10301e01c401d40b01900c01c1c001c0040d0f0020f2203901c040c05a50080700540301e648c11030301c0701c801950000c0c2c074400c00d03403010307450000f0100c54074043c10328082c100b980501407071460f084085181881e0031881c41d01251181c02017213201403c12584081441028403402e849988107100001e00d80511a03029402c00d00000801c08802905043e03103058501020b0341c00ca4444815891a6503000c0716131994022810404c0b1070382140e64850050400440a2020398410548944d14603840c40b4890f0300403072500301c20340140700752417034100c410584c0001809186a080104803440050400d4288400f81c0304000002c045074050344148121544150082c000748840b00c459880c043d900c1e480480700e00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 683154775 1250 683153525 683153539
    0x5010905060c0309102028030501170102190f2303060405090f0a0b1b130608180601050d15020c060103050f03180f010c0b09060604110405060313080c0f0309 69
    0x419184540700e5080d846c1459620800081c02099180085500ca16101006501030320081e06411016032440e01c0b012015a40214165141c0242286450b000c12020b81450740140540250f402560328000101e090350700e0079081118801d1400c0c0c803040c40d251a03000f004084030100075900042c220003540a00c00079201001140c0e180300c0f845445000d0480846020f40000c402040407900e004003098000c0100c10003101e00d400c0070801101283d0080c000e6101e080500c0341b0802030137800c03490003a8440005078042c066004041c0d0000d40341c41e4140180ca10070042284000c0c2808001c182c4e80c151311403d03100466850403100d082030340d0b13203409100c103d40314807070724032824070200010095440d65001184648454846103041014040503e15081c0c104004020064041500e01c0c1035180641e141078003610340c509004084c081604c00d003c0382d0440c440002c010400154440a085a07805022140441c1420202d072511040740d2042c211100c9981c4035000003603844d200c1c00f200420380c10008844074 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 683156025 1250 683154775 683154793
    0xf0210391b18200a1e020c190e10030c0618030807060911010e06070204020d09080313031206150516051b090a05070e0d050f07060e030d1701050d05010905060c0309 72
    0x11807552040500100025810100c42130942d26a030403044045c40d120300546001e40f00160124003140c0e60031401d04102c02079040c04000c4542e0302d41115811044120804003058103541720341c9501b5503144106000c0240c9040031900c545a007241120203035900c4010360340e4070021824402d01030003a00314182c56051080c80c071083c040d800b40500300481400074100a00700f00c01c54003008001c0d00f010801900c15900d482e820800a03a000005601c62038501d0024a500041410300a0507182c812513604000391501c03030203010070711a071203808800c40301c503141007641c440c1080400030144018080c02440c0d846a000c003c00304000c045292490701d03100f503c0658959964030f0100c030a4410503034044000c11100d54851210307043c056a1708907500d0040b011030302003480000e01a0300c0c20320564450000201c0070041c0e519a4503003440344000301e0855181005400861001c091104841841413a04c101800802c1c80100700b13080d00892225a001002c1d81c03490301e480e290080003640100d80c84903e50184c2000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 683157275 1250 683156025 683156081
    0x703051812100c051b0307030f030b0a030f05031204030f0e0409020f101701140906032406180f06010f020d0e010c0f0210391b18 57
    0x700c0300c000d80c003840041441071003804040c2c00038101c0c155035404200081000d21001e24111800340c0d07000100c480215070714000d5080c0100042030f00c0400c2407c240c2802107280c8203a42c1c444201d02940c1d000401c0c90b50b0b030711913880c0031403461055600c0c1c103170076072501010401415081207261030100c03030a446c0c840c02ca45c1481d0402c803c84041c540c000f54000d243d134801c8019070901c0070007501c1c8100982403600408410450304c619a103400d03031105040041c85007212915051180089400210a5000305184146040780070100799140400c100000c8045001401035500c0c10b0100010040c00e00c4048030794104503100a8401c14100d03101c07808203c01c0b94108030480c0c8000360160142c9156615a65040074030001110100140c1070140c944900710900400542d4030007111f03603000301c0107407200d181c805003041c1403200003a518100101080120000d264014850000d58603581e54401e10f001300103000220180810f40d06600000d0400099644605000c141580144890304154075044044410440 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 683158525 1250 683157275 683157289
    0xf030f081005400c020712050c1e040911030708030f0d0504080721121b0c050106030b010815150d021c080d2304031b140307030518 58
    0x10a5581040c2c0b4426040460000c1d00030120008030880400b203660009868480554040b50b9443c0c1c104503520442c00442c942c040001e00d0042c00c0c1fa00c0028003014058a800703442d0311203004054003a8544100c0c0d680c40c070300c21144c0c01c546a60002e100700402c014a0030880c00c0d20300c416450500a101d49980800c84c00e80010a940000882c040000d1400440752400c101070705010b841101c00d42820310521000405440038000703400350185181d103c0302c0070820300401400344400080c042614003035224036184660300307024000400604245520ba821440c015004000701d40c4042e000507041000800e4445002c1245242106100b05d40081c2c0c2d140c058911105012401115038043d05960030306005051018807003035010303070382c109a801c482800d854113400c0c3d5214101c0310b49000c0d52401c1d0524041c484081100e02100c421605a030140343c10380d800b9050320004608040e0074254443c030401046074018000410400d500162603d902e603628000d401500890b407094134a070041c40072031f051410805 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 683159775 1250 683158525 683158529
    0xb011202061603050d062d0f050d020a030231050601090302090406021216020111040b040e2701050f0906100302060a03240305460f030f0810 62
    0x201000c2c9005220812880c0c21000d00300e080303040c0305041c0210341740440ca610840d0010a0105a03840d500c000014902541050451305104c03840800d0301c041c8101103007102c4410507a10150b03100c84509100d070000504540c103aa0000394082031100361128041c40200d4060000d0050020b5a40140d92800701031060390700884070180054200c800c104003518040000d20303046800f56800500c2c01d002c801c00c101d10285c0803600540c000c1a804440d045050303092040010034291042031134200b030704107a003c42c203512951280403070958540010072000101424481a89030001c801c07030380100742c035511144c01f074a41150900440d28003440040c1e030040e4041165441086610210000c00d82144d08000c038681004009000705039495403203403070110f102c2c50381c41042840f01000300e20061551400b1454241030b064000c280f00c2c84880c00e151002c100c50341c3c02681d00240654084040100c0e8404030303450b040c1150107030241030310035201d00034035030040d009404610080d9180c442d0780e9115680c401c070f44001c074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 683161025 1250 683159775 683159779
    0x1802030708032119051806150102060903130e04020316080a110405010803071b120312050106030e0703201008060306010e06060d020c01110307170f15010c02041410030b011202 77
    0x24800616140c144e036000700d82c0b259200c91904541c060004000f0f2901340b040b03401056616050200310b45943c1c0400200d580044580010361a141d80e080342c0da00304c4080e512503802c0c42d0303251f030000c20110340e000d12500040040200400381069075800d481aa5065450801e6554818160541c016400d02e4099031341603403101401549800001d980f0a080040c200410400c48000d158000c62091048840c18005a000c0e68800e1607100d81090b10030220350040c0d000406240c98058514089880070590004036034005031115840540400c55441e0341c02503c03010fa0340200304071002e603041604040e9032400785106404941980c4e88a10380035485083c1a513950f035001c07005100c8100c500115070001c210052400d400404c04000b000c140d511b041d00161101401b04810100c492441d0301030b04100c0703a009070f0320f1000f04028200811a5a1a6041c00c01d41e14100b240c1e1004500645d00c55130421402c10041805d1000e441c034007401d001d01101c4c000e010840d15041c550000042600405080259641d00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 683162275 1250 683161025 683161051
    0x1b010507110607060f021902190c0e1009110c010b0d030504140402091816020c1008070e0a0b04150905060d1503050f030a031407021018020307080321 66
    0x3144041210a40195a00711801c0740c60300012145140d090015101c0b030008401c6210200740003c001a04044206d007040107246481270b108400700302520b07070400803540b08860440080e1500038907103d04d40368903005502401e003060a5145070100503802080707801754444c0200648a62801040007281c850100500010014401446048003801c0325016050004100501c0c2c2821031300810710f0607120038003d12004032a1420415802c0c0c00004400ad40340700740c0301404c9041c079a44006030b10b45401200910401081c840003c58807805800b0b0a180600c0050003000040d59540d031008a40c3d11901500e42006002d0700700c8140b05000d03040711000d0ba00002c00712403d042240f50300b0802020350442c5880d690591207030000101c2c50a202041e044800000a550744010610019043c1c07802c117000c41040c03420020412190f2070f40881d020309411440c04001c03880c281e1004000d00346151200b0041e505008422000400290000c010030115890090f401e0604c10040e90180b02d031002201c0d40d80180b14 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 683163525 1250 683162275 683162303
    0xb030f010509090a170d0534030f090b01090c0f021c020313030614100e1924140402130902030603120f070201020601050f0a090b03070909051b010507 66
    0x10b40201155031158004003201c0c41e008454841001000d03140e50125644540001d11183e14401400b64691111060911490703a04001500e400c003034000713100d120388080f4002c5460009920a80040341c200061280030b109641c00c40c10006100c00082c0f24468001c0c0c41e052806106030300805c0042c86c02c001740d4020300743d50500c0040000d201c0d07000004c9201180801c01400c841d0035603504005010b14007a000005150881c2401806911405072a6603888400c00c3c0d0100255030342203141d81c0d40005403012850003010040c41542c05841c10103420b034a10303510781100700e01020022075540219500d400074603180311600030030b2004a205243c0300104c1d006003804180200030041d00156008200a8103c603915520301103001e80540002c0e130380c0140d000b07000521000350b60f8100511400340408071500b2817a03c18210000345521140e103e081d80190701e4251001d0656010700c2031034001c005020061022a10074a401a210400424140d08040040c040001c2551141d400d98004903408595065000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 683164775 1250 683163525 683163529
    0x30207080d1b020601051e120601240c0809120c04020c031c0e210904020a0c02030c01090609090e0a0f032a02010f050c0f01060906081b0303090405071b0b100b030f0105 74
    0x110f072014041d41c11a08d540004156050200201402081503d0034001000c5549a81617a64142080840c00304101210684003140d811300840c0c09801c003c660015100d003000038403d06100f030100724603500ca880442e548882c0c1c40003100402a03152013505000c1c00340349698841c01150b10841c03841c0c10581c0403d08503640703245020141020b900a52500368107122600000809991080c0201000181011468021400c00300080d14600d0400d080c4600c081c0d0911307000605032442c41c407600e481c0316104c200007c401541884049202c41e0408400c84120003503041c0a40404240ca02280706032420741c0c9100840b05910300b40c0c1a1a950594886020480703650f005c0310583c201e07001c51a4a4003d844541420f01000d01ca0100100145400401c025247c050703010b04149001c1201c2c00402400380040e031255501004880100808840014a54441540442c1c02c1e9514110002e281203003064400c00344010828114401c3c100390354145205600c1e00e100c02050b01041ea1500c1d580c00b03098005102e0340c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 683166025 1250 683164775 683164819
    0x1e0405100213031707061118040f0e060a0b0a0602030304080307050901090e0a0e06090c030c1c0c030507080709090305030a050c2b180201050a03020307030207080d1b02060105 77
    0x101c41d00c0c14500380103449440b000a204010120010703070303000000f00e14040000328051f0328003180c03203040340e1420300d103100c20382003420b09000c01028410740c0d0301d843c3c44180003103d6100d0301100c00000200c075654070f801030b01d100081030310110761441b03210002c0001420380d00c0081124400d0b076010b404182191203080e010342d40368011035252418840000c102107440a61a03006511601441d81d001c1030400c0520412030400d080a00800140d40007002044c000b40c40008c0c00d0200c1520503150f80864044900007420010480c140041c140300b110100042801000990312090703c482c2d10940b02d803169500d03518811115003000c000d0100c1c90503c0058100d0583d6400307940d00240c0c2c6001c59140210701900340480380d008480008454448107140d41941c0424400d042240309a00001c0300074103680c0c0c00280482c014010054101034002000400840c4a83c06030b51015520445151322940088030440c0035003803000f903e001e0084009401d643c01c51002403080e0480f03c0103081501e00321110a034040c01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 683167275 1250 683166025 683166037
    0x60708120a020d020f090f0306060a03150e0703080c060f22060e0129090403200309040903090306051014010323090703031407051c03140405061e04051002 68
    0x7035540c280300011904000e030004118126032504041c0d60b89010703104029018940030103082c0258000c00800a20b5240e8203080303425a80c11a50b5120000d514260301009804e244000000034000c10000004001d40c5802a00320f43c204903081d80c2495459100c0c1c0c0700d8049080301c044a107510709545610010b0480c03400c1c01c840c1802480d0100303184c9440c0c041c0c1400d681010001c00300c0c0c0c0d88240c0c1c02c0880d400c407110a02510756002c403038030540350601ba01d000300f4440101880b128007031189030030719440103010000c50b400180003074002c1c440020103041c0904034003824071060b100c40c1e01384000511801c04c204040b40a552107803010325045c4c0a240011401070990003404608141000c000b070070010410341c0300320300c90002e503401410384508501e0700601010b080c048080c004203017441620006a800b0400300d004942d460b058070b074066500c12049000c2c0001c8220f0310090b43d900c4003413105120020810fa031089804403121200e0712140340a408014100707c4016010703400c030700c40c00b00b40c00d16070303030010301d1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 683168525 1250 683167275 683167291
    0x50307051c05011404060603050c180102070305070602011a040203100e102417040b1302011707030c020d0f0212090a05060c060103060b09071b05070803131406070812 73
    0x1940621118040442d60700703820892040042a5a048803440c090207100041c1142c0c0c0303000d2206040540081c401030090071510006221407000100443e4800c0014600468001081f01d15841d0f49500103070081031100031661100b03040c1e040600306400e09008403400751541000e1640810301e000024800c3e4400541444140c44910b4000181c104881020201a50801040f052244400400689104041d008000944c00684104404a800c0c070405c0381c0d0081410020112640241c40122601c1034030441d5101082c2504040c07007142e80d45a4000707280c903500d980842d1304614038944281d8020014001000c0168400c03800e007039400d41c0c10009044190360240c01310900548440c0040c65542140640c1400b41d4442030040050000781c3c020003192070f000ba101e601039414007104c028185003808000654500c09800c50303404000d001c00200f401060200d080e203894103581c00004038020118422650044080f1146c0764491402c60211400c0c582c2c0038020038503210302c0c0f0803036400d81580180703000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 683169775 1250 683168525 683168557
    0x80702030d060308090f04090209040605090307082d130b0d0e01110a08070504050a030221010203161709330a05010303030f0e07091a1509030d02010b0105030705 71
    0x34081d524010341c805188a2944c160700c0d00420414003060f0031007030031400d20803401c001e40c41001d078540720072007500103030003500105582c0d03201d0031007038514813030180002d00000300015000d001f5029450200306402614071180070381144e2041c14811801000b5030003001019001003000b51010040091a0088480101190300186126114211007a2030b40d01c071110f81c40081d2605200e644100d00b01d41c8000b807800c01c11304182c10034001c03d02c850054000240030f5203211243c0310380204580034010803100d280c4000d5649240c86100f040d140001605a00040750030309a00e011890100107081c0c0c8036101c03c00040086199a0300c820104003080c0b40310703054540706c280c1042e0042d8281e03541c443c898103a0b1440400c1c1b551440c5401400c55124140b110600e07072030a540e242c0c01d0b40012407041c1c200c80e0224000718200c50910f04003d0303040307048551a0303801075050080c1d10015444d0000703010b90000031000d4561003444050305900b40c504d800300c080d000410800004070418040c40180c80090341038500f003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 683171025 1250 683169775 683169787
    0x33213031d040605031c1116030308090102220801060506090904031b080d0b090a090f020118080703060b0f1002190c171e07230607020d11030601050f010e0108070203 73
    0x421b041403400010341d140102c03c0d00d000711446403c08540c0d814440a58014008140c100000c614404281d00000342048803040100310740c01802d40648000400406105801200e5031001c0f00900c1c41d24803804031694201034000a40c0d14120041d5450f20b0300c00f600c514459601c42d0303022106126028100458034007a41c8510700070495103005400300608408000440b1aa5101000a6004011301000229080c9440000010b10303c01c0c85109140d42801c10500b800d0038104e80d07010f1021780750407400c050310640100100f4049150800e01e8200f900f0703550302d11040c00e40c00521206841c04028080517a004840040c01d5024200c0c1000100380030790080c0148036102c1060004241c103084500c41d03540d00a81502160a1580214004d2100d503c002020a1131425840c1c0d00c04a541c07042451513800c044120028030344800c1e04440405e03900424081740d420080c03a0444110b40a1003403d40240328120005c0f406080c01d41c2d144001000503192841c80e4980c0c400115050740e801000030045000c00d11003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 683172275 1250 683171025 683171029
    0x180b0a03090f030e090c0a120509031b1c03090803070c1505011e080303161808010c0207090b0306150402030421020c03060c0f030115033213031d040605 67
    0x70341c0207a0320a6403004035903030008080203145e0b1409002c1c0d01032480200701c01408603402045103400d41c600110041420303550348884900350f008484005c0d61464401712003401c50031003c10003500c03044440c0030880c0140780c44034040b0100c0721428030040c03282c1410000708850b180036040545003a4031030800d00420440031000f1400340d6000303038446842c2c50050952203035480782d5491200041c00e18103009509602d0310001c01c000c0c02966039400824003503100813640840c9501a96035014042080081c081c0405045000303542d48128480c02c1c7c915482c0400d0118030b86400724100303005011305100c0164840030001004001d51001e0710484224104c1c40080d01c041c0c0c99030240700c0c86030300c83d030300544002d42295040c11f00704080140a109100807c1140310550180f0505807810740c2c4a544056604080540c1e041e0000c00c54102050303044081002c1c0c40b444c00e1890410300d4007c1442c0e144441d090b8444c0744905c41034120412005010032902c003841c14008039006000d61882070014008241c0941d5480 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 683173525 1250 683172275 683172293
    0xb160f02041409061f090e0708030a02030c100603020a140f0d0507090f0603231e031e18060904090c0b0a0e0904051906140a060302040b01180b0a0309 66
    0x1079003004001440040201210090100c554088017161510441103188002944000c4040c014042e4403903941a55280f440810050000580280003c80340d40e0b5200c400b000c3d551760000c039001c11043c42100640a1900054021a4100d980c0900040d8020341014000c00ca480c400c1c170300468024284800c3d10300e05980d0300d540d640e00c86005030b0203000550304106481003a9101d81c8603108056090007010000101124100c0c80c1407001601800c2114040707181d060f0402d07590b4102042a42d007091410a031201000c0300510703030034951005071104085801c0444042d13006201c0c6020b40702075400c1842002d820080014188450300900c0020032811980e50800d40c00202d40009040d000f01180400702981c001e1020441190b04072260800791400e41d03111551505003c0300480c4d4200c0d5484000208109900206200d403e40c02010f40140741203000000104424401130b482581802840803465000d05e40c0303c22280680301040382c1180c00e10f4000791144e4003070041c11080517034812055010540c140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 683174775 1250 683173525 683173541
    0x1113091b09060e0f1c170702131109030303040b0613090809010e1f030510050f030a030302070312060605070204060f1202060c03070228091a0108060f130903180b160f0204 75
    0x41568405005c1508041088060410001c01d8001c401c00c21580580d50300b1546035004c80c0d508101103002d41d041c0202440c00d0285492240e0503200101c240410081e4003405903100d41000e98800d80382c0000345800780e0580f1001040548072103800c100c0400ca80d480381c8942013080c00050541e00c00d943c5002452902c1c040c4c4100c40300000381d42d034000d2254454100c56040d0007004121601941c3e00e011000081d110400d08400800745680000c1000405d1b0044607001c403180388820041001a50b00c09000d0080e03444184100e200f00e14001003c9803240f040060841507900c1e2701000004200d2542c01d2015541c4083c0c2404d0b9a44000d004180c0140c0d20361840c0208007040050a0902080885400c445400c060b00101d1410f42009290901c1250b99901d5a00c062800d1800450300d44440c1e002c5064481c91548803a0019000309203c991000b854010700025880baa07100c90400d841c501e4420020030840c007400d20b01a20030070104880031603a01d2641d5070940070300100c800442003a400a0101d840c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 683176025 1250 683174775 683174809
    0x10e0901080d030b0d05030306011b02030a202d060f040f031a1b090f040e011b0e0d0f140a03021005061e040e011113091b09060e0f 58
    0x21440e046041c0350f2600401c07401304400da5410a01d581550f84268036800000c0c204e50411043c3e03c5200415544004a05801c50b0080d0986860049a08004071000c640f00d403001c418403100207c3c00454200300ca2502c01c448440d92040b031a5a507800c91100010f40d00d1000c065000c0d4040c8000d0200000c480010070040034000d1000124500d58640b101002c4107c4440c0c80c00b02120380d04202416450f8285a0700d90700004e48200c0c0d0328004040040c8249110886068000789080c0032180d083c40c05510481c9150514103c903400b0855442040358911a50b0342c500e600f0184c0040e0240006803403440728204a40304a581c1c20030b80560a251600d465030491064005030b002060f4821000c51520400350014000e55100a2072030182c0020242d600000f0741c00b0740902d5070360410014100d0300794010364520603c0e421403582e80002101400c0d000d07690f40205c2001d80c0c648090100901c0c0f0000751603411800540759448020f10f451016a0705485031294150001054203010f81380f5079405003500360290203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 683177275 1250 683176025 683176033
    0xc0a0c0f15080705030a092f01030e0102040b040510030219020c18090d18091103060a05011b0605090a08030108060f0a0e0a02060304020a0e04142811010e090108 71
    0x40c0581c07411404061600030410310201c2c000f40500c0560044c2125407143d01d180340410040c0340e901c0c0008044081e10000e82e4245039403002c803a400000800b601c407a00500743d85c1400b00312454850700303080b481544500900044100700030091400c01c01e0004118400d0341c180182049850103507111704000701d4503601d0050f08040403031290b92920504081002d074028030314003418640948030030f41d10302d403428500c01881005100080b1000c002e0b0b0304200a000d0b01c18003401003c2e42010500c51940058a049128039500c60020856501c40d002204020195186446060320a40c0b1101e00412002d444c0c124a030140b4000c6c50003080341540110b0080403220024a682d14010007060724465024100b2100503040080c400424000000c3e03e00301c1d00c0c0c0448449940381c45da44006110604641d100e103d002030100200030a000d1284d465160041129080da502000e6601a00c003c0d51144000c62103031080f5207000d640440d080f980c3d22440381c80d0606000b82103031041000503006103005d9100c2036031031b40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 683178525 1250 683177275 683177279
    0x60e0d0308101a0d14160e0a0f23030f1f02040f063f020d02090406080102070209090a0209191d0c01020111040f09110d0905010207110d050d03020c0a0c0f 68
    0x40b145c800c0881841c00811062400c4c03d10407030004031000c0c000f4008040245070b0344003c00790f41e5181c9001004003054021070840682e114285801c008499000c800c07140e8000400340c1e02401c0100301a0100d003c2880070b4001890045035000c14007503c200c1c84080c103a401e010120307908050023041000713414180c8842e0f803000340200c0e2030f10000301302c801d8201140304c001145c156025801c0c1c0e140c40c445d440200b009600e640700d081641000b4095803604550050500d00c0000b8040010b5006008050083c2d0f0190794503075030045d0442c0d0740c250784800290000d240c140091350452500304d803401060690b0300301150900d910200e10482050001e544407035500660302200c141d43e0240301d001241c110000100b410310b842e004250041205502c10258040c0e259900d034507150a00c0021104541eaa0340340801c0501251f080850003500003003030884480340500b0b80c095503481d2201c1c102d411154808000c02c000341103d181180690408001c4150038401e808100b00001c1182107101c028246000c6441c501034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 683179775 1250 683178525 683178547
    0xc060c120703630e01061715041a032a040b011707020106080a050a03031503020609040902060d0f0e0d0527060405060708030709060e0d0308101a 64
    0xf100f0f02e0003400c891040024050702007481030349415140d034800000300115190229800341103000109444800020f000494440003880340541a0b5030180d030303446050026200c42c001003800a447c2210305804400204801345080c0d003009509131171205190248410038030100c0d1600b1445000d0b100a172184901049901d960055491328420341158180145514140045c0481b40c0486004072440074032000a21818000d41051004100f0703c011100317210013505050f07454000b1250304800180c10030700340111900360383c00b04100781c0340c0042c02245060340e81020003005050700c1004903001138041c810315915524a2103000d03504041c40801040030b000250304941402c0301a05d5500901509101040d0304c0d82c14804042c800c60310f04c100c200c510b000c920001900c3d50096520082e4007007030006071a401c000d04440514010216074465801064840b1320980e1501001080580c001081110791030210341305140f2590810115500c5403d01921260003100d1034034000d1404001d05000900c40c8052 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 683181025 1250 683179775 683179817
    0x20d12210c030e190609050a0b2d0f0a0e101a010206010503010c081605040e070c140f120d0b0d030207031208010302060405042a0807120603050c060c120703 69
    0xc080f80e074001d0210680c1d260311001d404240200c0c044d004c0c56454002d1410003504220031403405410001e40205803402061560569104240741d01882c8407441e140026040c0c07045045000340f000401081a9903540b2403c07200420b40d1a802d0000c41c448e40341507d600451503c1000d144a004900120b803804818002a01e4000181d001c140a6131400040e940b4482d48100d000d600070802e00507401e5054059003044a084c0603075082000314560b40c2007404202c5400107c1c84540c4c510030036081024008517480651511280090303c4081e4011200020000000d280148100502400f0001d40c1104d0b2502141c0f440103200d50440c0942d1122a060003400024010002011203d20303003180305604540c00710703516002e6841000e01032070b190001400c4c5440303da030f4005d1841481000c05003807203641d01c0300104006d400342e40300404151100301044c00700c6014041c07182a40e40200042c102080c0c07100601c030307660380702c4400503666000b0114185a0001d031800180410790181e03440099070340282c0524258 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 683182275 1250 683181025 683181041
    0x203030a0e2107020a08100603021e0315070207030f12080603030c10090c18050601090510170408130b0307080601050702031b120a03050d0f0504020d12210c03 70
    0x5140d000e4450b040c00048103150121094164142e403036103035001440402d04290702c6070440c81c024021025001070001c121f5000908480c02212040500700c807449442400e0b50807100e05a4154112a81c5c44022140c5d2426607604001c1c6c6104690340030b95251035451588900b11011240b10440580410226920018030764000d002140958584407503480c10941e25050f016040c0c0742581c803080079070240500c0740f81c6540200a01e41d840702c031602c40030a9000061a0480d00d05000c10880e07000454207003400744100159030703015115004a001c0301d02e030038128202c00500c21185c5c0311040010424032009050307403200504440e00300c50f07102d0030a024090300b0010001d118074104681408600007580e00000c50b115198a2238154040d00000f120225901d0807902034615200d205200032441010f600000030f1000780e00410381089203042d0b45c0710040545d5000ea80113503101081e601e815010481e80007a040e41d000950420070510210004c0c48101d09503440c00321a00c0704d42d900449542240c1502078a90 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 683183525 1250 683182275 683182301
    0x601140f040806240a030321020d0b030709020a0c1b03050114010303020f06040b0a0c0c050d09050306010909050c10020c0a120201110a05190503040306061217040f0501121404030203030a 82
    0x2620300c1301e0b400412803d100e00d10020f4208a0031282083e000d003035001c01c103188610500c509640e81c1e650008035002611070110a035010744111100029081c0291017500e0308101541c3d9198005c441c15143d2082a10710520b048010942c15080040082c0091181c01c082d0900012403443c1d81d851401d010741820a420400c8031940c02040800000840340300b600c590016205c440004c80041800c0100d0301c5120044004040380309003030340c0e050303001d402445850850b04102c044540c140c2e240d642110035542112401031007070f80132002144840c902011002000c600910484440e40d000740001100e4401603880f03509001609205401035581c008480707141c0c0c0c0005002085940300c180e03284d0f40d9070440981051103c07500d03081702004001003401168015900440140702d000d44860800c44c01810703212040741e007d5508030362202407495207802e44044420401c4150b41280c5441c00549610380403c240c0910250340d421030b800700b0011090441d01a13402503000f1516407034050b1229085030881c10001c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 683184775 1250 683183525 683183581
    0x10b0a2f190812180f03041e0311090916140f060a02071703090402040b030a0e161503090602030a0b0f030a020906060f1b160b040501080601140f040806 67
    0x7010580400c01c075109481e00d0010350041e079031110030400c41300d00612000c0c010350140c0818141c56400000103401070710800b00040c030312603000301000032140c00280701c002c1203a0503401d0b01071502c0c0381680136141e004800c00c0944869100c00b20b4032101c0e146260700516158141c2414119660030304120b4001400703000d5074010b290a403603690280d5a10410301c203001c902c8021540500c84508140300380c0f584250302030000d5423110340b903030055211908103d45030054545000110013441710001078030f01e0320045200c1200b490500b407049800c0b04103205000039080c1030b2500c50345000980c69200561182d8a084030004041840d50704020400440c4904c0078400d62216030114090b0f648c1040540e00504100e13031031561031280895000040c064010280c24001c9003840d070b130070352440c0410310080899010910207811500c6000c8107500d4001e03402928001101800081c9503540500c40c204c41140200d10020708098000303500d02c619034425008000e0305d40100b024031220070b400e142d00c0141c1c120070354281 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 683186025 1250 683184775 683184823
    0x706031808030402090a0b0312040503120915030a0b100c0501050601090b0a0c020d0c1d0105240306040e070b0d060f03030f1412270c0108010b0a2f 65
    0x2020b800090800780c4200a41c10201c0c2c2000000d80c071030144c2e8038024003a00e1040c2c10b140b5201c00c25030094401e290107405000c0c015003024001104985800302c0c01840e034010b2010109440c11035400017804140312603039420b40c090041e078903a5a920214640c1c0c2e52200c00c002c80074030304942980c1c2c0280c041418018019001d00072034040030141d4261a1403440c10000500440c00052555904448060b1030425040c0b404071f2609802200007601074489145118a640d80c1c03c240310100401c071041c04c0d0f0700d52010300c290607001c030039400441c3c12010007000407514001d030300c644904150850f4400c40035040002401c4940307980f80d000b0301313004150900019a24528584026001e0380303020300c4010410030707070702c0202d2902d0007030206484110402100710100391410494801184402100d02c41000758402c0c000102c501c8002400030344408180d40c0d91500d80d1804c0d401030416000721b080071003406400c012540c1c9030314681d100c0007000070440020b601c2040486040d5803d040000e00a5080c025010a607 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 683187275 1250 683186025 683186033
    0x60603150f0c0903020f1917071a0f12131a091006050901050411040b070f02011209021f020703140a02180906061e1e1c0b0a0c031103070207060318 65
    0x1c03c286c03d9074281d8803500382040006c16014550000b9101c0b4400e00800e0315000d81c0000c601b01a04e80e1041d81a9011099803a0341c210b5001da0125000490804c220782e003007220304403c8450304081d240b104086620000e6958a031078112074500b020141c101403041290380881004001c007007032900c040030040641802e02180d1141c1d0140220707406161170f13030030114001d10710100301c070020041c0344905611498585410009128441c1c010303070004591005006000c466441a03050030769004000e4002900d00c030300c10030010003d4810304420341c01499400408030700714000004515204d40c0140000b084180b041055018042e021b00c5644280102005030031a000102160000790443c0c040004a401c0691941c0026480c0040c80d0001d404d42c0d1a06c00c0d40494421007030800300308030340032040075001d40c28110500c000c00001400501c8100041580c08000e81d21a444000c1c442c507001c04c0c00031043d00c43d1030143c0d1003922407400590114104001d000e80c076100f00b1050011600d0040b00d00307806515 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 683188525 1250 683187275 683187289
    0xa0c030f0e0d0b061903030305040309050402120721060905090d020102070309140f130c23070809030102040f030c17070b0d02161e1a09031204060603150f0c090302 72
    0x402003942468902144e203d0f0342c1d41007001e2290b0b407032950b08104143c4901d8024068141a2005c4001c962700300c20108880c60300d4000c1e180c80c501002040c05507941c3d40141140c6900301c281164114020050310180c600540d80200405850980008100781c00c08500c84c0b072a00586031404421a44180100000640c0c0085120101d808140e580c201d10030318140050074440146c0c5056034450b030703c2c00442d03c6d43c0350103400c000d02034240c584820112029180d4100c15025101da1341408100041005500251000e40500001d80c800340c001402d103520750079414440c240e150420b0f2035143d401d00040242c0b100b01c0b81c2d005a0b100000c0058045149020000c2c00c0c103000e00705071a40d110f074000c94208000e8980003070048109802c2183e01411100c0321903143c0c418030b5444025034080b03070484a411a440c1e004c05415004102c2d1100544c42c1000d1003407001c2000c400074004440c800d441c0d04000010441500e91507642d9a00a81c0004104a58901c000210760040c01035805111441c14204050303a182d030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 683189775 1250 683188525 683188549
    0x20a09060f090e190e070509070f030905060903040509090c0d03050309030c01050c0c1608030409050c0c0601030b0a0b03010507092903100815010b04030206070c05060a0c030f0e 78
    0xc14180030740e4a01c18429034500c00c0307a400c0003640003034401c01c00007441c1440748001300030f06050404120a00802c9070907525000301e0700800760080400808205031511030000605001221315000445042d03d5890030b01f0440280c462110301d510110302440140b8190744001c1c5c0180a103c01000103407100c201140c00641d00748030160074054080700041c08500103008a84071403284034000c02c014503100d480b1a10701e400200c42e1070340c188a681010102c0060209401c010b96101000450a29280040f0303900030b440002c01d61210a05c0c2400104c45030701d020000b89000c1e5110300f08035111464880c001034100c680020089100744c3c100011720401d26042107582e002d98000c4239104242540701c00c480d0180741d08814031403020010010800032101c4500b500311003030303030b0300324017079481e213074041102035800000c01e0183c1601c840c0c04000420052605c08000c0c039036944200b0000340c1c551742c3c4800003482c0d03402078102200482e07410341c103c208043d400340040c03c481e4414101316006803564401324400074001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 683191025 1250 683189775 683189777
    0x6010302091815070c06090b0f07050c070e06010c02030a08040501180e0f04020109360c050f09150307120605090c0d09060e0a030c06050906060d02190e101404020a0906 74
    0x80c601003000544a41111240f486d04010140f0441080d407410003042d880c01c8405214942e40c01012420441c41541200c000d04031110041804038100003040d00e030100098512230601017150403503c010384013417004400060080c151203880c0d80c6040d002411040c1d500e039088048002c000300a0090119403403456420090550291126a440f48010b951182c6a9003017050883d014101c0400d42c030b95a481c101100040030340916001c154156040030503607c4540000300824802c2c070100b0511405d00c0c02405800390000c10200c105180c5a01c10304103030780f054458000081c3c04040a0520041c50b004070401840c094910109c42d00d4014080d00e11030007007000c40360600341c94941507401d1058070b4109400081da25010741d000355000c0d24001d085402e14020445909080100041c0c4001010698521074180a40651906035480d42000000034941040c0c044002e00650042801613282c06803a00c90700f6401285202e2506000070546180c5142208601c80c500400002185551207081c107400c40b010703 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 683192275 1250 683191025 683191063
    0x9060318200405010909060b060702180712021b1c0e01030207020a150f1106010323150103080c0c0423040c090203090303060108070c02211e060103020918 68
    0x1d84400c0648442858000d40c040d0421002041200342a80b10320803031880340c2820441c5074004400d1003058081d4444c0030b940708241a1500b1100b40c040300d1740702d5000120785400749200d01034404100483e0004540c114952004000c0d41000c0d420400c80800c003645030880d15030046030b40d41d10040010a201005604060b001314500f8215151028104080d14031a80f050340b0554000100500688941c104040083c80d0f00740c000c6290711021480c0c1c0c1c1030b203400c6100320240103a0050303942810740202d420511382c1d21a040c0c1c443c9800307500c0e80c0d00d03d0285100b84041d6658a1482a100d8600819050000d01c5180f410301010340020300783d030100320100c0ca202003000a660380c41c01e00904500700c2d0303130100005600000404c820458040021441a542601c505040751954242210320600394200250800c480031940101140541d10000400c6080780032220000f01710010440703080302510000a81c1e40c4850300600c1146090801141e0020320040c4058400c550440825030b2500e40c50364149a890b1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 683193525 1250 683192275 683192303
    0xc10022a010509040e0a0b0610120b2b03140c06060409060902060304061401090501050f01300905070b091c060213080c0109091a0114090a0f0609060318 67
    0x4002c0d8141d41565400800404c0041c20011855860b2032815100301d40740018440010f0f0645000f0364185101003a50b51103e40c1403142c2c100c00d0f0002d14001041c15440013010a400e04060000c03040c00c000c540241d41d5107600c550780c07803074060610019468160310203441406502d442c04800101c10b9404241102c02003803200301400c04000a080c00c1001a420140000802042c0b08403078021129a4440d551043c00a0fa615410300307003220428014903911120f21412440e8662240c0701b029040301d00080c0c80341110781c0c0d0003015400d600c40d18520403e140d0300d58440109005003803001c18021300b01d41c07514070304e0300303115200003030310000700003250310a641c01c1c0c40c400e405001e0242d0649007981300d40c1c1101103090392140405580d410061240a00151f0003000c04100107204ac000c0c5071042081c0072024076070650700401076413603950070300d207010702c2d05414407a010b015991202030200800000601203486405c29000500e0307041544c204406140c02c1501c0411441c05242c286100e1035004021100011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 683194775 1250 683193525 683193527
    0xc030e0a15060b0a0c120903031202070c08010e0c090105240a030e0709060810090209270109030806030f0a0b040809040f140702011d0d08040f050d020c10022a01 71
    0x1036190469024803001054003001d940d04417404192007030042c055050141c01d0401c0c1140e40390740c2404000d00060251492207841041e64001e080e040d4403810342810600d44075502d4a084620b15a206032840d44080c88580840c20010341a902408080d0703000714140b03051050410f0010307240c98038003440950002d603a14419102c1d902ca0141800701c40309a40002e075966200401030710280c0a0300c6514011003c051842500c64441c043d0700c1035025240801c00c0d03540f0303003014450b10440d51103664078241c41c1c038444007213240070304c5058140c6109899203103c9007403020505150001540040c00550700c680e031854040f981800b64554010740c400509a60784500d0360114001c0c203d10fa0900c00a10b0420328a0303880140118281c0d446584c0560003080025010f10810f2042403c440ea8a4403d401c06076500110300e2240d280d141c1d00c180919190890440a030387d4071483c4c41d03010b55080005030018440a425450007010300440940340384001c0c1409000c002c1982e00c4103111844a040c82c1d03056503110405a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 683196025 1250 683194775 683194781
    0xf030603031201031109070f0903120909020f03040501060f0608040b060409050f010608011a15090a1e0312030905060a091416080d020a0506010317040512030a030c030e0a15 76
    0x4607124504902540d40b40f400c5141020044e05881c825007400c80000d4400b481140b23400e00f03003291a0b941c990700c0c6140d9141c00c041c1c07000e090442e800304001c0e4034010a948501d4001032031030840d0341c48510b44c0ea140a08007142105c40a410602c01a61001c40c00c0019a6000d52259006500600c0240180c2c90300305c0080c008004085000300240501c0010113070140043d0300c04c400b20ba0f0100300074014080309503c05000c08642c40d0141d54000b855000345400b507005d001c00307454001005001602501e80783c0e1681c11140109680741000074103010350070b208101461080c4414012142000d01c40105903645945d16100002c183d03080341e60b65500303400140300000c6a03200d0441c40500c15504440d01c6a902e020060315036015000c050700c645000c42c2c00040c400190702040c0d0b5001000b40c01c642c3d0840d5110300c41c04211003044000c2010501c8085001d940d4045d102c144206030303030019275480c9258800038082d52000c40c510828035203401c0110036901001714048812580c01503890700d08040101e01c00d030003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 683197275 1250 683196025 683196037
    0x10050309010204090905100c030507050d092d030e0a05011b050703120f0201061430010f0e1504080a05070609210908160608070c0b0901061403030f0f03060303 70
    0xe550500440745c05001c03001c900e11042d000031981c00c0c00311016849094041d1002540c8500c0000c0d420018800719841a40c080e600d00b0b0311030b074201007002034070f80c0c8110395003003c08040c280890507244c4502c0c20550448402c841058081d40c607151140c1c900300000c3c020031091080c40c40e000b441c0f40d0a0382c04010050210101441d84126240c0c03ea0301e80c420300500e080201c24811002d5868000c1c0406c1400148508411303803040101200801001c2c04440f041080400d00e805101107d00300c0c01c021164028010310b6103680070000d001a021440d030ba91985040b50508042450b00000014000400e0310311007120152900e90401a60700e4000d49851b00c01840b89140c0548010b0204121000010005481c4106010180d445c0c50307916442c4c0c10301c56211442510700003000c242c18a020408180201c5c04107510010354209000c0c030681e29264060240d20403074028800740d5481c0d10501190042c540c4180100d9400d400540c201010700000800301d10800c5143c22225402000140d070703c0e03408004480b2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 683198525 1250 683197275 683197289
    0x21e061302180c09040b0f030604111f05070317060307030b0c070b1015170429090c03060a0902010206061c0f0819031a0f040e03040f0312080610050309010204 70
    0x30b80303103054090707615039801c442c50303480c4038038241050035000349000c2400351001c0b00d0007005480140c49580d1101d1070721800c403940070380111280072248400000c46903c2c4424441c1912034941c2c43c0902d26000b040c541c045440b009896003035000707111460301c0000302c40741940c2d800404454591100329003111940600500140620189001c0100303e1590508a10403152101041410000d01c040140c4002c00e035505a2103250811200103404107201107a2503084000415001d18944102041100001d10848951000380e200c058040c0d540d090810400b42d110320314807401c00035841c059000039110800541114130403c0b03007072036007140400741c03440c0d41e916141e000042d00036519441c5031501c0702e41c20880700028000000e160b0f001c0014000d01842c0001c11100c000d480300ca40c0044200803e40c0069003180f034000e591210900361a410070001413001c0e1907010b004410300b40c550315020202d89901c003541e004001c45e03902070110365102c1300702144000080d400e0068a0342e4a1140f071600a014641c4401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 683199775 1250 683198525 683198569
    0xb04030e0a06031b020c011b060609020f03060a0501090810021b0a0b040c0e01030b0103080318032b060b0909040501150626161412040c06021e061302 66
    0x70b5081d0164801003603d0001c0c00302d240b00101240c0141c4c0c5a181d1130203440d020400c00a19402c2c03804060030781c1441c00c0e10507100002c94a85031980c4404070f030001c103511007082c50000144023423807500c00f0b1103900a10033440c0542c00e4904148400c0d442d1020006e244411540200724155805d084207a81807000040e0400c4400850040c10903240840c029207040d81c40c803100d2040854200702201d9040e068940000d1088004e9185984062040d400100440c42564800d4020318090000340010100400c5040480d8003010480d02c416440c2c0d40d4440e900084103140c66010001c6c80c0c10602176544100d01210303800c450340e86d10308045001d030480041e0f014840d00c1580c808500c02d50003260052807030f03458180199074001032400c54042c000098852440070041c01c0d0304040c0c1188183d5107101c100c1400500384c0d041c0040310030381d000100700a44040742c450740041d07014010030b64100802d901c000c441c00b03210308200303910b0801d0a0f12181c000e4103082844524404034029034030350101000031013034066135038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 683201025 1250 683199775 683199779
    0x903022a1302030106200d080a0207170a0e0603040f0f081209060a0507020c030a020f04020403060e1e150403140c0303101e05030309240403052506020a0b04030e0a 72
    0x4100294005d00851000c01d002ca014841d80b5000c0c5020354924004010080018004809060311031800c004c0500962035001c104010000d81920540d1040300544030110741c03104480c0a01411042e01c00d144070b4002d010a00400011403c513103207452209411485d22021080b11b824000946e11980340c0320007400d480d920030300c00c020600182451041400388800c002586900c0802c0340c44580c8425006d0381a400404184054509001214140f007401480140340070f03520307600e40701562015034031000240c00401e901c1d80c0840c003210b0611000000034001d000c1c022086491041c0c00c0b10060001780c02c004017030a9000e1480c02010880b103500d0908021039440b8078100300f10300750a00590181c01001d008215170002c0130504212450241c490040285003400003920a104c10884e18041403030703115507080c000301a0612010000d201550080025103007550340407c14000c0307808202d501940d906c0100004120182d80407035107820740356114040a040d510b5600b01222604d49080031309610070142040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 683202275 1250 683201025 683201059
    0x1e03020c100c060c050703050a2718051506030703020a18030b0702160b12060d060903121b05030a05040c03050f031b010212012106050711060a0903022a 67
    0x11290788944901014813030a1841d05080b941805038250040106009001140b00030f401000000d0b149074044e542c281c140c4183d040d40075240300355071b40440c0040d5441c3c045400002c803103024003644401e81040e855070000705c01c404034800d8440181500201680810280710710381c4103070000465910aaa0010480b0707440c0d05003440c2410040d1345000252040c40345000c0c03c100189504412078905003034513428220a03c1808401510081c103041d03011440030018400a441442480e0800f800703a651150302c2c2c6a034841480480d86500140c1c0d480c00e04000c182c06100f03910030f003200d81c007030a1044041590b80340c0b40b610314000e07200c90308020254041d0900e080c4404100101070107038025902c5003404d0380c02000c20424200e202c0c1a1818000010100c0184840c800e4485008280c01d64424031402449003501c9500440f04143c40c40350001d0038081c01d0113060724040040a801c9036501c941000480c9440d60040d50302c00521041c0588064510504e4009546482000040403406860080c0c10800464 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 683203525 1250 683202275 683202287
    0xc0409050115031b270513141f0501030906020c011109010e04020c0a0b040c080304060306090608030901210209041406121903050328060602060606071e03020c10 71
    0x541c51000a140114422802c00742c224041e4904e015038440481c800030300c002040610b903003000c1d002c1001400301000105615a07180d40d094141c02d4040020362010942c0203240c121130080c2a0080e0207402e801800220b0751142540000c8070424200001c104070f092604074040d000361445002c495103008889084a682d100003440d50080981c0d980400c0102c94003004101c2c0910a9031340c01e5a4044c940c12000100c042c1403250700315014080c91890b1701d03902c0503801d02d940d22541261000a07145c000400ca4017029010b110007074581c2c04099810030b00741c100001c2400c0c4001d40c03640700f198181c0e40303122340442c907540c100d40003194050401d22103158126400c05c0c1c2140f0540369203024580b07107801790b189a07034003090103001c01005940c4140c60303815a4500302c40503000a80130302201125011460407c40342500700380d1040c00c081c507002c104c0601e840806828103000034426806080200140c50010342482d81108120244448100c591612800d0491508007455141c54000800c04c1035186440c0d0440 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 683204775 1250 683203525 683203559
    0xe06180109050d0506160302070813140d121409150403112d0a330201020c0a02120a060204060908011b0e13110f070c0b04050d02090c04090501 63
    0xa22124200740d9103100340482901c5014000e0200c2c0c00180210700c2109200c14501a0100246005070500b0556102d221580d03004d82c101d103e802c0e0310080104034500140b48580c200034001c0f00c54850b4280591a0000320303401c050101010440644a00a07a51001d40241c0d0840c0394040c3c400640380e1031080c3c11454962090000341c6080c82c031170041080f240740041510f01c440800c0c1d46820020100040d00044408543c4100759019200c14404549000071490441c15511035140c045158059003503540e0007005520010401c69004100c50a0b0415002031034a102940c15070748146107100080f4158101542c0c04001840c2038000600020260f82c043e05c0c0b1002d5a42c900001c00403081014002d000c410a50072840d404648455000d10700f501c0d0100000300a0303030402102081c01900691250102d5002002841d0501c00129a0b4001e00a41100000203070100894103480d00341030100103002d4115003c1c00a115454900004034007021707010540380108981b034002d1110f540c458200103000203c1e4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 683206025 1250 683204775 683204777
    0x100c080c0106061e2a020d0b070e04060807050f0a09050703051006030c090512010e06040605160e03030313080412050a120507110405060609030f01020a03061e06050a0e061801 77
    0x4010041074016507901080941034507110b035640c1c170300e6a101a003042034000800400c040b6100b250030300581c540079040c1d00910b100b5040342e60303689010a800b414510307011140e1400345143c81d10030300c1130301c600045810070784804851403900c01081800142d07070002941c000c1341c001401c00c001c3c01040340e00340e000700b400b0303640040f40c1102850700c848003181140c03d14400ca800003500f0010420280c2070603201840205552000401e503400c241c0700a070301d054003d40301110040c0c0d0f90b4003084100080c0001c942d4046201e444c2c00708210b01840000f07650ba0101401111801d07a05000000030004d00b5401c545c01080280c0c10340d44c007003840d401c02d9a00c030303680d407401591071240041103010a60300c2501260a001c1c0c1c8600e140d104558110700b8000106070003004950425000c1141c445541d90030010103418a08120016960b400c8490740101904d460782d121911344108404e00d41da035280c00402403030664400b031030015166140c50100300c4500d08894601c682100300091244820702c46203040d0b488140b42 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 683207275 1250 683206025 683206037
    0xf0b010305061e06010e0a0905070903140f061b2205030106060825021002040b031b09031b03160803030a110c0d030b0609090f090c06030f06100c080c010606 69
    0x40c4107481c032907014000707250080c00a410f000140150301403822142e0844c409007180c101503403905459000c407042524058042200218104100000d491809a00b500104083c001e20201010019a030b28005410791145290086c01c00854010380000e40d00982036807a091900c28030120400110700d009400340c03e009500742000411058003402c580f41c007840c01481d0141d0080c0171000301130b04801207a03a49034214040d0507082466207540c3d0004c3d0016211110a0340e50380c2c2004d000144043c030070700c0c00343c4415410510000045030742c080380d02e1036056145442030700f03501c0d600d1300043e0500b2880f21050489022044d004a800c001c0000610f2051a8881003004105050115015640500896104164019102d00740000e100781c1120354050380c09410a420001c08000060044404a50714400106240704002c1801e000f0040c3d220880700a484440c80c40c1044114400140c10080070346015001181c620300b01e0512403101240015080303a1810b40303800c00c068400d40030b041144500000200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 683208525 1250 683207275 683207281
    0x7110414010603231909061b0201060f0f0320090411040e12040501123c0c05070803060105070533060619050d0c050a2601030303180f0b01030506 64
    0x130850040801902580704022003540c401180404c581c118040014040d40c550001000198080c02031b180e8406d860481d89601d112030040003070849505901c1403071003c10034841003040320035048801060b00d4102180c02d4042e00e04600011030044082c6125400c50900380c01c210510501c01c40d404080c2c0022182448201c4415828035650748140849902ca00e07420001040300c5d41c06089441801c0e00d94210101d501d0850601c811034521a45e4090030401011107500d48604418560495a88100314000c00c081c00d00090014041d0181c039038010f140080010124086a000302c00341c41040360b000c411101032051600202a081040b042086203c8440520f403009684050940740c2c4201c0f40a842903003400018024041000031150111091080c01c100c000c00038061030240921454154079040d03920507500c60000c100c040c01894009811903040c04005024550b03c001e10304494140c5004030b103a900b408000314201c1089840204a00109118030703003089030f03030130107141268003503400c1c0c0e00669 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 683209775 1250 683208525 683208551
    0x100f050607021003020c0703050a08031b0f04030303021308010504060e0c011b0f0c2105060a0c0c0201081b1810020d081803070c080102030901050124030207110414010603 75
    0x80a0510020f6200f034880b04120507180c0300b54058031030002c1260840310607030358a0316202e00345100c0c40c00594041900100308098803039060201403a22264078009031500c43e0b0010155014062400300070b0030190001502d030f450f81d240e41044009024801c1c001c00c210300301031a00500134000c0040e074203080d010310301c0340d075000398040d129010002070320205008500d00543d58a210351490901c0807601500038140105801035075894001d2031b4016044103184412580c10003514041c002402e807084103040000c10300c4000d5001010802c55682820708802079180e207011043c2c006407100a4002c51354011440c5a1101c20400402e03040000548001601e0300c04548101e8852008000c8000411600070110703c004c0d0714071480401e18400002520b00b000444d50700c581100059501200349a03402000380590440203202d01401010728203281020311104001401d1a03807500032020742850741c042180380a0042913035403803001800050007007010606128141162079030a0162400082c130303101820300c48d2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 683211025 1250 683209775 683209777
    0x415031e0c091d070512030421050f1f0525030e01020a050406080a1503080307020c0d0c06261611031b0706030b0d06020304021c03030501060f080f060d050a0803100f0506 75
    0x190210760080c514045c00c0564902701c04003000e10039400c6195500c4900c02088051101c0a10010751001500300703141d40e01d0f04008503c0e144906085402c0c41d01d0f00703101707180402c502640544a03048800e68903500c08420240c004060a0b9450340301da500001d002c1c7c3e1f600d6803002c024002e591503074891404580300c0f40701510484070705000d03081a000d0860001d001080b4800059a8005058411140075046e41404100010400242102e540503401c400703014060300000065a048848000741210341111070b4002c81d242c030702a00744910400001c0040d0815031003010414011021401101c0e5143ca0b4002c1450f1030a120007180300040c09003000200c0c0203803081c055074040032801040400011082c4d125800254409031007241c0c08104004500e134280000100c003e0303482e0003514002503a61604101810280e250300510040001d80320170800c14491031340c44d40d070b0080402d441c100d450980c1890100e103000503038100031300400300c044208a404004e00102100303581a080c0e0500c0215501c0040c00b0603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 683212275 1250 683211025 683211049
    0x702101e050f0f0903031e191d060309010b0a18050609100e100509090604030207060f1e090b0c10060902180d1106120103020415031e0c091d0705 64
    0x1a6404001520ba040c1103c005400780030002000d0b070f450301c00003407039034881c03280300440c00074100a022904a0030152084208000c5110f9802e01000c810000e501041c19840607990070f9118010110104482c20000d510908003c6d0300945501e4080303856100240c815142c0e0024101001c4c20f0000103071580c10800c00e00f50041d165a208280d0890400041c0503042e00b0040410050310032140000a6681d00c0740b001901a0300110f000e460182041d05000303040000a400c88800d22446244600c8626030217521000900c0040c1602d524221042c2022542c1047e146d0000e003070404003180380e40500f81d020502c4008090702000c20085035954078003c1d01a801810400d255158100314948600c0c10a0544050418030800069103022403420004c0c0280e0083c065a00b0780403035400c01802103007028440d04003400c04500c0994000791441e80c8007811101b08120416040c124900107004004584101070041e01445505001c50650000d02000740ca4442d104882c2500c9546400200e9041201072894 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 683213525 1250 683212275 683212297
    0xa08070e011206020d050103061d0309180402040b060a090801050105090f07030c1e03020a121109060f090a091a0a0b090f15040b0a09081203070c080702101e05 70
    0x80a07840d1520341c0b4805140c05005580413602000781109200c014403c03280a98454480055419501203201c3e9007906d280e0203103501907004001c0c0710016507036a000f884170580414551180c1b50f4861001c640541a15241c498004001140d000c0086401110313050036112a03000070031441ea40d540400005400c15100b020302400312102081d0880e20a81183d072440303c240c14015405010780c5003030708041c40e0107280e4000203580420000e00665101c2d4808131503010015040c0120f000441500405105041c40305114040c00035080c2120381408094a40d810360040504440a0340c03030016001400101c0f074054003130301a0100300c0d0001e1400c482c90b032085d1203a050501d4100307a10740c010310a0701001808100d0380040c0000030344135010320540041014150700d0102ca034450a105001800c00c1d1840d4125041e26040040410310f00038803c1c0540741d0218244c0703404c038001080303414101200e00c14200040d40007420042950849604030007541504e003d084c0300c0c58a02d09007100100c07601d0045e503da0074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 683214775 1250 683213525 683213549
    0x60e06010507020d02030607030e0708070f06030903120504060b04050f130210050d050103080c0105091203190603021804021c03021e070e0f06031b0105090405040c080f0c0a0807 78
    0x59040d522840142c0a15071019201200360801600040c0c5407420071122503000070f07110401a00d14110074007845c002032584e800200a02414181c0c00c40c060740f56405040304041e46c1e00c0002d030a2501c2081414440702c803040c4c041000d8140f500b04400940040d80d0464012313820800413810340074021100b14480c06414030082400f0850743d080060452050381d01c4010848203210f4041800c04034400c0358000c521402d035081d540c207040100f00d82550002001030150750044480c0d034160400d00c0003202e9200301541180f2000c40b03a00c00c0410010b00d40c1d500040e400840000e0040000c17401c0031300c010701440c001c441201050b64401850300360141d10140003801600125501094410044541107011800000382d644843d11406102c0b4800021580100965031900a0203001d00381842840c04000003400a550000c050b040060038601c80d04084d03030300403951080080c09000300ca00804000c5c100039130a6030003541841100c2d5a03102d44940429203c0c0c6a4000001514880081c1e44c3c021540c80c1c428170 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 683216025 1250 683214775 683214781
    0xd0b1801050f0f030309060c1b06070b1602010603060e010524061b1c08040c0b0a1707030e0f49030603120504090e0706080615070c0902030f0703060e 66
    0x8058160f8400910f5038143c482403012845598514010300500002000103001d08a20709040450480f502c015450190608001405c040341da00c010f40c80d40856175803c2c00328040705d0998100d005001d075600140a191614940a950a0040d003100d07014400e0919541032010000354804200c004528407107030700c102d00b0400c8030150311f011000254845080c03070030f46102110425203010040b29002000c40010f02d03190130002046507a0a648000d0006004800e0030034040c16005002c80005003044003030141c80d440010340151003030300110a40ca10400968685444010b1260340c0e07117503011000c0007414a41100c0d54010b29007440340c40d05a04290011201c4514000480207401e50606107031410142c48a1000c00420420880509044465a521a0344a24010545048a40540750110650008281044010b9009030b0068200400300e890510200f004802c5100901c40d41c4001002c1080510000407030300d03281e602851180080032215842d640d210310381201203d100740214441c905520000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 683217275 1250 683216025 683216029
    0xb03070e030609031b160902040503060c03040f0f081306091701150603240305070e0a02130b0a020a0510061403070608070810180507090611031e0f0d0b1801050f 71
    0x202e8190241914207030340702c602c08080f01b1141c40b02c940d0401c0500a400181c208020700303080010301d9000104d400707150304500702a42c40c400103d0f21208040c0103540380c4000c03441400041030480e0b02c4444c8a0b141d40d00e0541c4e440d50050045422031048a441c42c8412920050003007040c060020200d25022070f40c101d0078140001940104400083c1100032420a10482c1c06c00c500d5510301c1019600a00042c900c81d468411411366400000b003420302101d0041c428016040207852695040d508240f0780c036510f4601c0c04200b24600188588050301910580c3c5507140b13504606d03480300003510210012100605102d0f42403694500b99840350307600203208400090007680c410418180c1180104201614080d07851192862406c9100c600c0030880d41d0f44c2040c880c0d01350b00118240c00820007070400f070744507011080069441e4022800e01d4010503211941001c1c250054030121840099030400403902c0d01d0740349401200078901d812070340c0c0c02a00e850001da02152144030f0640e0403188000d00ca86c08209195007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 683218525 1250 683217275 683217307
    0x506070f0b150a03060203100b12062806080411041407030906110703030b13200d06080f1e1f0b0102070315270215130305070b03070e03060903 63
    0x442d221020010715100000c540d62020580300841c043d103805030301c906240400d199940482e910458094000f0014120745403040840c450f4060800c031224148821100f024119280c030464101c401c0150380701020404981080d80580500e020f0341d503480130140e5240510044400c1c03e01548040c280b01c0000500103440b0380c002002084c8515000f14040318200f6006080d500f00b0b02c402c4022079100d200e109541d0a000206480e00c1c5c8038044140442821101030041003001d40e02c0c081400c1200041f001220b56040c2c1042c80100b420360107c41c2611650a446500e4034442c03000a00e1117065aa500c0c8810500040c10f41100340c0388065070300c01e220301d440007100141400203034039040d4041c00d440040821100380c40315821030a20207010511580c44158031400741e60030500980c0d0f43d1441c0000b980542c90f503a0703a2250900e4569002503480481c1e0200384101013030f560008040e481090400714140d800c03100550300a458170741360070b42c42c45200820540c5410085514803940ea10920800511860f030311 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 683219775 1250 683218525 683218531
    0x61b060623031203041407031505011401140d0908040506070b09100203060a060503190e030a090e010b2b060b120601031e0c050c03220b04141314070e0a0506070f0b 72
    0x21b82190032556481c1d035154032610380b0404000002d81e0f1540100184084523900000390a824a42001e1442220765001d981b4000c1c030b04002000b6690300b80e191700700700350748007118080c102c0149815103a40091800c480542e104807482d0b402d9000c4c48101100415040c0281c074040e05004182101c05800c09204540c2c41c0c0000300002121184601e4282c42c4401c83c0c8141c00f54003010601540d0384454620700640801e07020f80c0803100e01300406004100c440400c4c03050300d811000582052504540d10030031070f440d28280c850b040c50440d191100019072100190007c040124864160f000995103940044d821034034003c550849660005c1d5003183d41d000c0700d6000c0c44102e03099051544c285180e10490b076246400482040700c1061542c079000403109114120032000344980c58560340360a00717010349881c0071001c03154220b01407a15101c800c6200c24482d00803d841c03004070208002c0a15190340d0040402c00c00b61611030285e07884000100341c0d41405c000b01c0700c4442d0000541c01d4203441641c2e4545a8103001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 683221025 1250 683219775 683219813
    0x5070c050114070210030501050906010207030305120a0204080f100b06030112561303030b060918041106460507061a0109061b06062303120304 63
    0xc11080340160344502c0c48401749401c5a60001d10b940c11321041c803121031005890f940c195031002034100002503200003180d5420001101c0d0303200540700c0d000d5440c082e000d540c104403114002c04d4201d144c0c40c030001600003401a8005000e220a06040c0b05020052000780104000d60141c4104007000c10074140a10101586041501c4844148402100704007030280c0340c02c2c1803d06104e1248292002c40c0141c1b00221240c0e4040500306060505007508002010320b001414541c40780c403499002d81e555000c4e94040000a031065003060414144480c0881c41280c0c02c4444680c071100c10000346c1400001d13038901071040702c0000c02c0d01200c6503d00441180201c07000803030900c06054900361140203108105082c515440b040d895600710b151142c103444c00601c0003507560b0b0600310301c0021a80d1007900041214440d0802d4452080108580c021a90300054094042c500f4000c001448c61109050040b0009132a0201d0101d481d400b0304141d00c61308243c0c50340c02c003290f0034000700e40444d00312a640ca03030404c1e070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 683222275 1250 683221025 683221027
    0x230403020f012316120e1f020901360b0307110105010e190605060c0105040308070c03090905150306190608061b0901050d0c0c0c05010809060f060f0d0f02030c0105070c050114 77
    0x2e01030103500307070343d8103462141b0b80303070083d0b050090b0b00070f03030101d04a01d441e062400c15801c0ca4070b810002000400c082c10b40d80401680c00c28841401041048210720005040c5440301036591584041b054a510658400340000c80b0092000c200340e4041c8a0a81a83c1140c0d00e40101a02c0d0700c00e0b50b01d10303034040310b0781c1c002c001e6a18400010103669445c0103040c6070a101d00080307940d107040d05000d000e08000601450a2006c032045c4040041d502c6154030059849903030001400303845040c10343e030b8001a10b54460b501032150700203205c000130440308003403020b050103103040c850503884000d95a100c01c0305035100542a1441c0810f010083c0d20800503104044043c9441c07418003116072000c5c001e840e4155a03075030100d42c0648102041c0b02c244501300015000a007400009810001800ea6503185d00421aa0010109201081d01581c0b4008d81c940e440e803000788100c12000f12410700c0540d00311205000c134030903c1000707500051540900184d80c07003036400c1094003080034030b0007006640742c02c0070400700301e02500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 683223525 1250 683222275 683222297
    0xa050d1d120a02041b0203090613030b10081e060105061e0a0801090606110a02090405070510080f01140a140d0206161109060d06230403020f012316 65
    0x2a12040300304081ca100c4000c05200b85540140000c0ba0403c0400d140205107400c403d4260940010840b280e8000649400d03a40f04400c1045a80c02203098100801e4250071200380034040300641d22500640b100c81c003e0360041820500c4080000e51040c5a9084507002140104100d00d07102000d4800708503602140b00703058190090004265100d070010301c0200f500c1c44010301480d001031140c6805085142004c0c040c01010780307143c980d20003203c40300a22035100c400000b020040300744104c1004040140400c8140700f01d05901070a415002c9414250042c041c1d80001001d8080d03074440710b81800040d1141d900c0034140041c151007120003c0308942c21181202c14140181c417030000030088071132000078803650601c561a02c007200d4044918000e20403003032a81071005581c0d40981c110602903224000141d179240e40d500c02c00590a501c0300e51509002c00f0810801403540106110380c6000490000b041003107030b05c05419000207078201607041d020f2506000030300c03001301003100c1d10015080342c1803103082c0d05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 683224775 1250 683223525 683223529
    0x110d030e040f0b012106080303161205040206030a24060c021806150304060618020405120607140703020a1b0819030c060b040b0406140f0a0b0a1b05101a01020a050d1d 73
    0x140c01920542c140048098030b04022561012f0b003518031068200303091003d4205500011b00714040900380e41112552030b2204072940c1c00b000004141c80050002c60a0056915240982001601c0d8400d0303006036241c841c83d4441a1a00c00102d2040c0c400812003000c8600e412608032007500b00130011500580e80d204049460000f0000ba00c654000362200541d88034200418845000d000803c000e4480c0d20a0051040b0301e50490803410f0b01d503800f190b1050320b8820b40d040807850b1015521000c0c10220545620101c46010480400182d580799011515050404c000e0141201750310b240241c00200c1a0111500080d00f5407c54000d00100030400301d44a02da10b40024110782c0c60b40e00c0480c40d040d041128905070300340042c484102800c11110003803014a003200c4042180714600c1800704002c0302c0b4004100c20071030b0203100c00b070168104080320990f070319007101c503801030002c038914060000d071a16402c00c882d0702c00501191341660003005003100e904245400d0300c0c078404680710b0513520402d004100c2c0311a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 683226025 1250 683224775 683224777
    0x60408010501031b091a12030f07230d0512040c05120a030906030c0905060c0106031502030403080c0c0a020d082b05070908030a0c110d030e040f0b0121060803 70
    0x30314081e0310381d0646400d1200342d0025854407a800b421121b8100100007946072001c00781c46000c44026070f80e0017070300e043c0fa82003541507116074044004004408034081c02400403071181c0710801c0d041501095808030f07108010350341d1000c92404500000f0020003c5105080b49030400a400c40d1241440c0b000c0c007511040010003998800c04540c0043e486919103405040e40035428000a25041c242041400e581c070000400c105410700407a409090000780c013140d400e50940c0300b07100464000005142d01092244180701039841503400742d00080810021443c6840c2074000c4800409454004100351b09880e800c1c00f00e114100d240640c2c90307250a00000112a8403950140c1b0f0503050004004120740b0007815050440f81d01a003200c04010700d01000f8000703500008212030100e0a41e0034050f001c1511464070840a0031603411007504040d82c00342400c1010f8100381003a8403a00200c8040c000c0c010400100700407200720720485400100000c540403843c40f818500642009a102c0021512503161041c003451 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 683227275 1250 683226025 683226029
    0x1211031b032109060117190510050601110c060c1006060207090608070f260d03141312050f070f06090209071106150d020a032301020307020606102001020a03060b0324060408010501 79
    0x504e409c00031601e280c800c154441e6036403106090030080004041c40024540c3d4003028070416014410000d40143d02c0700041110802e08408070b50240100e03525000025181c0086102e41140c141c140400070a00383e0313010030244c017603c078464401d034003591900d41102c808980c4104148088024000d44032500c00081c03101d2003051000740c4020400c0d030119a107103c1644001841c2840c140a5180c000c40018614200060004c0580c13510640704c1092003c010014480e0340d8008140d00d000354801d408000840d040003140c64001c8030b403000c4a540b141d1003a98004000d81d500d001903080000021151f8144c006074050b03001c0d0185c8013020035611540411340f14400344d0800d5910400e2071800c241b003240000803087e43d03503100000030b50440c248060301070354682000e802c4601c945210b5140d5003000703200b881d905d02032041c942c5410008600b0100d80c14002d6000440c541300080c10410301040ba4031005088a001d04030900100107884540d000c00d80b02c00612849040d13018a0800c000610710800740039043c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 683228525 1250 683227275 683227283
    0x20c0906040c0c121107050102011e090c1806030308061e0909030f030c0405120a201302030a05010924050402070303021309020c06131211031b03210906011719 70
    0x821011790020b81441d24003030354030081c110380c1800190031401c0302c546590744040c0c054100c046002c20061401c0100761003590041100e904140c64100019582d0f9044641202c0c002e0b10b91140f44d0312a0014806091a00c1184001310f012998800740350f82062940a40d21203100720540f07041040c40505200030307502c265032503001030a0100d0207001c28580180e00d032035a076510500902c801ea0702507941282c02254008002041c188070030703840002d074880082c0c0348240051000f045550b40b4009119400801d0280134440c03c40307107801d14000b4000007802e10209403000329a22501680e28040c1040081d61001c0011010940c003401030880c280800ea219901a0546040c0075840f0745c05100402d290000042414980c0465002c808003c110800f003c0180d4082515010402d01e0741400c00300d02d148034051040020127131528503074452140110150003042d41c50500e0651b52406840c148000d0042940c0400311a044400100b00092441c03003002c40420030700080d43c900d010483c80d0200e00d030004480a403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 683229775 1250 683228525 683228537
    0x1b0409020d060b04030b0a050415050a020d0b0a182a0207080c151b0109140a110922031205010605030f160206060d0c03020d0c0e0106020c0906040c0c12 67
    0x105000380b4002c5001401010542a003440c2c81d6440e44842900040d1055074550b6880001c03809001141900725440109800240054108210240700942c02170401c0042685082108229490716218030300440b03100b04580e02902c0325035100d0f040204448090104280100d00c448814941c500b41408410642d540240c07081328903000c4000c1c140080c03020200d1055040000c1704070720300c038000e0964581d4405102c1d10415203007000b0400f8010403004401400c410341c100e4101511410008403141001d218400d5a0b924000d14400d11403081415145103512202e450611101c00219072800070201e800ad2a00017030b8070111100d000c007201c4080c2c0003900007600000070041242e4240040a03084412066a0900c0f180c8081c0e0082d00c400f0040e2905203c0c061001494050000000165028580080c07103907440841342c7c501582100c03518420400517003204800041c1c15070010801c205d0200025003c0c54041c1c1d03c0303d0070031009120407022001407002e002c240d400428103040e030212503101d044d1114 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 683231025 1250 683229775 683229787
    0x1005132403050d020d020d0c0b07180e0106020f0f0709090503070b0408040e07020a020108160c061d1606020a12090801020a020604020310090f110402070f03171302010c0b1b040902 79
    0xa040c1008a1010b805652010300c04007c42c9500c0480b01b150710b0703000030a062050b250300500721602000c00040d100320420100300802d045295499081c1250003e0302150130001561030b01c01d072101c045040c5003245070410380003002807070b80b40d41101408502c501c0c1501c0c070709240c030380c0e4103000981d00f510107656080c4041001d014020300c1684283d0000308a00042201401a500083c400c01004201d815504201c0e0710858240b4050301500b51b8590303010170244518028083c01000e00d206051121031144180310001a20700c0f0801c000c6000c1d1122580a003503100074a40b510f001c1f1a0003040c8500c2013018010b000560810b0038406071003140c656502900b014180350040600c0d0002c0000c1c200c2150349007840380030016030080390f2550426030010808002c000304030002002030241c1c04001e498085c40f034200c6403c05a1160703640d01050f680c1d0385a50103a8a81b105245008010341000901080d242d443c0c0c04046a16144425402855950004c40201c8000740703004250300706a220000700b03900450030b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 683232275 1250 683231025 683231027
    0x30435030f1305030a0f090503010204030303020d0f02040b07060e12121b03070215090f0304031a0c040b16020a0f06090302031203060d02010f02100c0c06051005132403050d 76
    0x1c80c94000c940700c1c842d103660341d42d55110707a43c03244145c41080b41400f1b01c9280b00d43c090790151000394000d110040003151216660708000d4040d52101c1c601c41906480d000c0c1c0c41911045a01c00c0d00c0607035075101400d90508072a980c2d01002440c0f2414611440c1c0f18250301c1d4282c0e440d0440080400007074151242c2568100034a0740c065103005c10982c204502c00a000700302c2c610b68001502030340006002203510321138540944003400d26590080c81801e50000080220074440e040d86000442040c520040b8816907641325240c0c0240994024117000c00c104000e00521515881c5e03942490900040000d44940e44e01c500211f02c0303611a50115003c10003c100c10420f6203414000140d02410608000d4030314034240c0c00003020740103145002810300018200510110348204030105160300c034030608000c00508800080c0803c14244000c0b02c015040c070000070151804000e00000301c2d4800b03800380a8095451150b0001ba0800a0342e020209041402424600f00480554001580107038050f050701848804 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 683233525 1250 683232275 683232301
    0x90605070f241b0516021c060506030f030a0801030f1505010311040c0c0b1602030f0301120c0b0901020a021c0b04061517030a03020a03020c0618061b03043503 70
    0x802c0c031a85a065244160040d08945d1458044c0c000d010400c3c03554030020b0b00b840c034410f00c207000816208854074200109544524010340e400c078110340c1c25940140700282e0f24459401c000000882100040000131a103408c92401e5520504032009400b541d840920205da200341c0c0b085c2c491255011615103141060710030141035504e01d103410301e001c40071900c54a080d058054040f00c5102030982001c59102d10902c15a0800442400c00664039651610a09600c048028003510030603600c150000b4009810021540600010b802824a900560b0200305080411202481456580401e0400011283d011052086110b088002101144166030240b028100e0f045060100458a503080c141000001550050241c610703002d0b9a038590b0180c02c4019010309440f0040c0c82c030942c414402100301d1200000c0f9000801411149543d80700c100c1621841681d403014048028108003190200780458000e21243c81d80c0c1800612902006145219114140c8031383c0301400e50101c140008a490300c9d03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 683234775 1250 683233525 683233541
    0x7050f06070801050402180f0f03031b070509240604051302070b0a060b071716080307111c0e040e06041a10140d0302121b1606090605070f24 62
    0x40d40440c02c24a4042000e0005103045410380d101d1410903134231055959400c40040100744001d0305594a4110030000c0c21100320681d400c14100c0d00542e000400c4508065072900c1c03140c40005641e01281d03c642c12240390b222103c80045800050800c80840c0e01c0d1280c1825510203030880c00d00680c0d6202d142821701280d040580702840e0341c0e0a2000401c6024003002c10b8414242d006800b00070500c001c003c401420b44030300750641c280c95803105101e6040c001200044d601c65803454444040c401d58005400c2c2d1100445a0036102001000d003400c0400340c0300740c03900101101d001d40009004e003c1c5280c058a48641200c04071441d40a220380b49401c1100660915048000803840c4900a814200902d082c00d00b1400c005000e40050a80c400c14940700300315112140500f010511360700c01580340d04641c0d400036400894400e01c500d070408255070003622500001c6074246d03030364801114200b01040322a81d000c0501070b5568051a0128004a840d8541860058650056009022964058041c184d0720f0032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 683236025 1250 683234775 683234779
    0x1806080c0117070507051006150c0507170f0313150206071209050a0b04060c0207170316140321060415050f03030f030c070512040320040207050f0607080105 69
    0x1200c000c0c00d00d81d800014080604400c4605010aa52103580c1224180148403000c0c204d03205081a8002d85440c40d40721005550034101c03c05402c0c09807100603504401c11040040075540704020400801c000b913025211a030401d003055610060005641914640104041450728136600c5002c05c0316941d5448100b09102c1580044c02c0b851401100c0509000c01c130b01001e4a90517120400c070810000244000015140c0c4615585c1e0b150804c1e05060009115600c0a0b0000d032040721408920f050f00720710310480c0410003000031460140510154440c510b1001c0080740d14100740a54559000010b2000d0f200422404080300e06d2002c100703264085480002d000180254a170946402203084034444140c15601c003941d02c42c0d405038600d40840c0c5584542c51500c0c449100100500036400042c400612516010368226101c501d012445038003a8851031100900540c0400c455103248401403d84184040b40108014207003005031312110f081c84031450f070074101500031100300056590401c0f0040c2c0540b1003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 683237275 1250 683236025 683236033
    0xa060801141507140c1302090906210a11011202041202150408030403080c0114011d0403020111030906041208160e03071208070311011a10090f180608 66
    0x505494021601c920894075030140d8250310030860b00440110407100034661050360900d00424a440f116151941a01132512695081c4404100074800b0300a440d00410014000300c0c03140c4413103040000707417008084001d0401c40350307611410403130000340054440c01d0f001d1002e181c4000c40502c0018a09200c038014078018a206100c14803d50420500f5500f40c10743c10713690009240c1c80c44a018102e07000c4c5500c2080c1340e1100203004000c02002001030100c2ca1a507000034030403000420580580030700300340070700c01001548160070031003d00301000d02500240a4000011620380c50341c48100c1e43d9104491000d102c0e40301d5401c0c803003007220403003820001c22036503c0c002245003050411010041c0203a0480c1042019401c0c405080b50b500380900d00051134032146548111010340740c0380c480390b0824070042e07000c120029941d841004060281c0e001400306082c0b12807c104202040010305015840c4002c01c10081810100300c2c41da0b40b0131401d010b0541c402c04032540726000c540036800e0301d01c0c54211040301c0e00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 683238525 1250 683237275 683237279
    0x31602030304030f0e0d0605090a0606120b0c131a090f040e0c0621092103040807020607150e0105090c030708030f1c09080a0905190e070e031b0a060801 67
    0x25210408640324013085c0780c11500c3d14507640000c0d03160308072460054080d901d8070040c0415030400203030f505041d80c843c4000307120305a515485801103070b856000190250500c40f002800c40285a00104331300d0002040c1c0c074a115840f603652084015415034851011000010038202c2d03450401c00040d00322030102c500f400000002c01341e69854112195803039004000208070303600301c0815440182200401c031440c400c2c241c0781940b2265070350a5064400c4911566480c043c0d007030480b440045a00c216080f1500300e00d045026401d10050782d100340c8064420f00d04a210726290303400c1a000707034603a8080c0c120000c103c0d030030403c6046081c8515007141c50310a500124040103442c0022050320450b00b00030500d40e445034400c3c14003038401d80c1d03080c04510a683c90410500c1c03c004141d0042c000c1c5203105d594804071280c41e070b8103014040c00451000c00c04140c550700d04114002070000890f50100191a03c6080d0a10300000309241ca03021410321818844008514175042c01d081e2130001c000c0007580b92000b1154 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 683239775 1250 683238525 683238527
    0x80c010e030c01090302060901020c1503161d19050d0b060a060e03100207030201061205071401080702030d050a0213080a0209090c1f05190e15180402031503010c0503160203030403 79
    0x9811480300030f008103c0231440702c010784e0003800f13a0440004050301c160040108420740a1207039004031400621812000b03171700101d091040f030320384402d028442c554071240c3e402c10742041741c103441f0f1600036a42050346c40001710f125140c80c0403000c1428460000d0380c4a50416004200b91038500c2c0d04203d0400500780390103102c0750303000203088050480307141e4016a10120303400c04a000d0452504400034018034200a0b204001000a0000445091580b03640c11600084011500440291410f4005a00a12108500b480d031395200e20f4021544540040c03408078103021162400045600966070381d0420400201582400030702c0382d40c02000e94020b8000b580e40c641c00110340d141c00c503545070047c40e4502a05030206006a044400d1183c410545500040e5848070082481c0d015070006406201011184c500d080b0048050300c07240c80d851003410401c18101c00500c0000e400c01410320f00401d5458400782a01d0703c0038460841c100c4a140e9515580740b404803509a10703c03104010344000c41d030041041001003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 683241025 1250 683239775 683239787
    0x905040c090512010b030105010b13060c0f060c02070e0109020c1501030f140c04110a030c0e03100c0c020a090c090b03010f050114132601020301032316080c010e030c01 74
    0x140b0003c8401480240038450414010460800210b42661070040003196840700c1101828100c952142c0312041c464035260120f03120000c1d510010440107c00d4070060002d46590085010003419104030303034000ba900d2101130000c00342039000c1c19071140c2c001400e074641d0038144001d0078601c0c08008003040651441c0e8644540c0000100043c042500031400d96503000c02c244030301102204010005c1c41071034001484194030303500682410011034680080b1030003c502481c0a0078200700c0050190503c410800100d001900b1001d18910030042ca0440c400700583e1104c4123000504183d4100254400c03801c00701500e81c809503089205840320a04c010008403561001f00d005a0f44203103060915072001000c000c01a0043e10044004a0240d40010840840c400d02e42000440340300180019000d9444901b400c0f44800e00001c2d041d0f040c0c0c17140c03c0340c409080c1040310040c0f40f0300400f1140403104482000400221640282c0ca60786c2242c100100c03a0340c0d2188900e1a075203000c03005449400c059600103010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 683242275 1250 683241025 683241029
    0x1020f1b18060303040302190b12010e07020a020f04050a090203031c0608071401050708070602120621060105120f07181112040f020f0a060504170706090e0603120a0f0905040c09 78
    0x128035080c08c6031080c207181469049005280504001e607c1d034080c281c000b906147c003406a503441040010025003c90b10028441030842e030042c16841c0004000024400a004003c00000700240c07181500001618104000c003100114000c00752009502100003c0a44007141c0c40801d0f02d903c911424800b0719800110754507074450900b4025500c3c100b42c903000d03040c1e000d011405070446201040101101203412015131140404a074900b000848040019042080b0000e408007641d1000c0300501150400803098440b04101100301c0e085400c09408044c0f0b021040d411420040150000b00054505540141240198646d55080c2010403c1d0604803499000902c0035042da1894240c000543d25110484205024041c10504070760b40c03100c02c09071480c3c0c004d00c43d18411804441c0300c91034110022403902d0070365005503184c1e100c65152511842e031060001e055982d046c00740e20010388020203240300410544545407605200c084da034407006041c0c1071495100300c0c043d606000a50b00201d40c48403410302 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 683243525 1250 683242275 683242279
    0x809060c03150d11131505040e0a060c0c05011518181202030403150b09010b0c100c110609060907090903030216030903140309030601060e01020f1b18060303040302 72
    0x780365034400950411000c19440040c0d089551043c95109022240024000c485001c1c0c80600c400c030520049001102c11302c0594011a400d114014849031074150044a446420003080750091a543d40b1070f80c04486050440d40e021800c07103041c00c1c0400400380212546000010408448540303820a44090301b00040d072148c25007543e41200440c140200c40e002c910182c1c000100004000c100303040a5035950190206070b0b00001811441c40c809001401082c80791030340684100c4c1543d113005044912608001c0484019006681805802041512402005519540d10242410f84082c10301d41443d901521200c034580200f810400700c1e00001452030f0441b418810000740062007030400320024069800c0c80b00010b07000c2e43d5008141980700d4400002c2d01d014055030a01c5400540b0b0782641c0744074200ca0950103400180c010001c140c0030b202c0382d0001207410b0040e1604806100314441c00d0044401e4152010900455203a03078a08140421040340074090400d0041070078072400195490046100080c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 683244775 1250 683243525 683243527
    0x30c100306170d020c10180b032710020f0403150f0513032003070218010509010f03050703020d1707030c110f01020714040608060a0b10090b1c0612081201060809060c 73
    0x101b885102e4101c1202d90508165140b003055190303040d0500c141e000361100304c0306048080e031110900301070100800400c000b480007400984030320b2a15901a4009000080f50004280000070108100c803a00c130207141c0743c040c40028403400711070001d004c40d00090070f182c4115041801c9a0002904498001d5001d40c1504001600306400541b140c510f00c526030b00250000403400e0700c24005046802c820b8180c03074003183c40d40c4090b80c903000300240d00512031002400b95404003100700098182072806400e41c0b4090152913030311b1002c50007041a20380c004d910842c0010605800c20080c04080840c2161035103080707a45000304940440001e644a80f00d020300d18800e50301410342c10107030381c0e194081801480c852007a09c2d464600a21500018810181e4060040c075810380c074400c1062080d605c4000381e44903c41c070941041c130800582402c0024070709015018035034a1001050016100b000c0312500b500c0b901c00c0e140d540388840030701d02c0c03c1c03d01039000c0b000340621101808030980e804160703107500801188c001c1d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 683246025 1250 683244775 683244799
    0x60909081206150d05040c0e06060a0e0f060408030304030f0521130204061508010506041503020309070308040f050a0e0903040303180504060b04080610051c02030c100306170d020c 79
    0x69003001a8100c1e070f61480c000000d008134039125035000184030764003821610003000e503210a40d035608201120020307404181000703008286070142200340c111800160030203001020920108240754000c1c0c0105182d0b60003c0100410564000d01010844240d0b1a02504001d5510350040c1031904102000d03c0350000c02e8001101d0006410000f14155002801405803581d55149034000b554096060710006400340c0000c1a41e0074285c08980494813103400d0321110303a14509049009400c06040c8500d00d000c2d100d400808a041d038400383c406031845402c2907011a02d88010040109059400300205881690812411280200542d8103c98260506148401c10b020580d08051480c0d0807894ac0149010740209038507150300064000c0d91001c030201c90007500e03405208081c5825a220312030344000d0304081c008150140b8250424441c1c0702404403900c8110980000d14441940f400a03400039607181d504000c00030400c08110b45181c016400341007681c5e1003641c000e480303200030b651042c043c4005c01c0076 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 683247275 1250 683246025 683246029
    0x100905010b041523060307140705011509060f0b091c060c08070e090f04030e0303270a0e0103080412020a031509020112060f12050f0718060909081206 66
    0x4141201c0020810004101c0850034105504494040c0c400d0031107150740598000041103a20409049000b4400c505507610110f0484800d0000c2c611360006107401d2115a001070003d0188d0520010349900c1d0900040c148148402200d6191703000140040e8821b004001c030b9083c07007003200c1d010365040c0e992045000508003449140000340c00001c1035203140c001c2410320f4640c840040d600420035a51030780700c0305070442c080004006054400590fa001000041800240609511030300c1c0c1c44090107407420302c00854440c02803204507100c51401e0860501c0080707442c2ca0420b6040c030240410045580c40b5504544541c1e049005034010380c1030314200e00750314030705541e03548030b160000b16404481031075071244910040c3c010700b02c011012404200c0c140c4100d40007280e1030080bd41620381e11807401c1030561a26514220128a44000380d03031034083c00003c0e109880b014006040900040744a8602d070740141141181180c44945c400c102c49484c10014400040e45542152804060614000c8803a160340c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 683248525 1250 683247275 683247281
    0x41b0b030a150b040e0114040902100809101d070602060403080705030709120501090b010504050105030d0e0a0909120216210615260c0105030c13050307030c17010b0310090501 77
    0x10b480f280d08040b60010300c0392100b61300c440c140c4e841d280200b006001948103000642e000560002e6100e0303602040e040400348a03000c19036200c0961811a1100c90845140604985440c0c03461040d100b0400d4120900c43c0c002c10405c0d000b031466100809992403d51002010004041d10500c00c0050000c04501220300c24500c1001a01501041150280c1c40d071401c1802031540743d00481f540207801000007264600703441914102c071000303405040d03003104018086420350500c1c4242d0b0b602c54400300000c1260038407407255008661040860712000c080202000e4507041080805402c042441801404001c6015100d001090a11045008000d02a1500f00701400c885c412414124940030000126160300300c00e0580700380c200700100c03214007100c00e001d141c540304808159070215108201180b14950b0000044c08401c1d01d4940d21103006444000007424007216a105617010220004240200d0440c016484901c00c1050001c1011503280030102c1d031110240d1008200346991506814180b0100f90 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 683249775 1250 683248525 683248529
    0x3071b230d0303090230192603010e01060f1d01050a120c080f0c070c0605090301021c201e030c070b09030706050f04020f011409030a0f0c0b030c040b070821041b0b030a15 75
    0x99012926903031181d00c6542f908009200d03000c0000c0f00000008071340c90040c5000e2600c1e01d10315680b080000c2c04200159041d80c0072101e03035000c0003031074064142c466500b40f09860004280c0ea4030170030103080240900410f0a000b80c038107154040b0800407900020300d1420404221035003418102d40380c42c07814002900900134014290030b4000c121608243c8000540c0c041e20300c40080c9881c400b9903091a4030108042e01545010306001ca42d00140c1f00001d518000c080e50307006080f503803418a8042e03180da0b400b441d03480954080b030745640b010441000704103080c098564091401c000542c400d140980000d40088140810f05051000181145031012642012900414806401c40342c4914041c41c0c02c0c1007010b9880e50540b042d0328880400b04004c0d9120702140d0103014200c03030315800c2c0380c10b14203d10280c1e40007107011100008100442040d1605000305044411750010068245103002e040c0660a21000d16580695a0b58501c00b800202603070350640c4d401070310040c0000740bc8800c0c1c85040f20701d44515 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 683251025 1250 683249775 683249843
    0x40f0203090c0a0f030b0105060705010605030a0503030703060e070f030f15122109091a090a02120c0f181203071b230d030309023019 59
    0x100701c40c40340002103940d520102520104010350b0f94890240c0603020702e0000400f491950801001140380c240090321401e8025000010503c1d176410000b458842036560440f10368001108206055401d440b030a00181001c18001c4160702e898000100002d00c4080e462003856510080ea020400c002e9101d80250007000000000d41d0703454020012030345d503101104a0359003402a820585180c0e03038045030002020992911305501d0b06183c00d0700081c040721000c028070745101901c01c20b40b036902c12010b1800707651206001680ca2007a962103d04141d00140300021100e4100100c004e00f08103031003195030005100010400349100107000030303000611030070000400e01c0085042000c1c46144070600d20011031422401030a150365060b00c88540004550200e40080018a07a00c114107103883c00695080c0b0900d0000b40e00c1c02d00b0781c00511a80944c030304000f001550044a0307a43c0c0011684191000300c1c41c48003d050a00c0d113101c1c100800c1c0358034007000305551005600318401d0104008d0400c1c40d8211 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 683252275 1250 683251025 683251027
    0xc0e010522080c130c0801050d1a151905030d03021c0c0e030f16060c0302010e0706090f0501080c040b0f07051002030a060e07020d0f022a0103140f06040b040f02 71
    0x40c54076002c0d55a500c4002807441444d9032108200c021089102e0000110003907280c8a0b0b40d070f80307004100154141c00c01021313600c000b0340c9600700c0c40115a0310781c8580308010082411004081d071100780000010300ba20031a2071400301071424440303036400103490244d40040c1e203009030b62042c1408403050010002201c818540742030030400185543c0012a40c7c806160036000c9800080f4104101c40c0e484c004d00510784a01c0511031418071015108451a40300f142c02400040740019040481d18139102d000d50007000002c810000c144402e00035014403c00420b404d11300360b40d035400e100c0300600140c401c51282c11400c0d00c00140540e104444042079825040d00541643d40c070a021820301c0029510031105444542d250800c04186c50780202c82d12401511160300410011948143c142c43c9150081c101c0c40039407040280100d040400c48082c07504060400170b103404444200400176003981c0c00c1c2c56403008154a407000304405015130380d0007030b9840001114081440302a0002150003003041581007559a80 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 683253525 1250 683252275 683252279
    0x307030609020f0910090506120a0302060601080c0a120b0d020a06050706050615340303060905090a2d020603090f0609011a01180b0a02060709090c0e010522 69
    0x1205034001d03400c05000f41e881d01981c00f015020015950300445e5240c00c80900000c0c240302030311030b0798405a401103000d810110400681c0b80d14510380b80e00010201d00603408070341041025680f11002d00e81002d07040c030307016007070620203031010b0000c0d20f0120441811941e101c111807402c0e9a20709488460035005402c0302907190721035100401c0c80d4050401aa4802e0070b0501090041c2000c2c90200ca00000341e429190134a00c5110040805503005100001d12410854031000b135480c071840c0d49414280710340c9002880501d05140b43d0240d820003029280c09070081e0f41840e0214642e2074951001e000032140c06c400400c0311071907010075100d03040300c065007141002c42080841c5400080e00c1050584030002c559043d91100c00d5035007610b540190304809036219815008240d4021661025503603041c1440102054032030140d4a85c4c4d4101c10800301c0103030301180030f00c03074031540040000e4090b000c6400300307000c0325452850280c4501741c1d204e0514104030000a03402d0544400410910504c0940d28000c00a16 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 683254775 1250 683253525 683253533
    0x20616080c0f0705010e09010b07112d041b0c031b0309081009080f07050712060204060f0c020108150402070c080106091a0a0509070c05010f060e060d0b0a02090609030703 75
    0x20071a0526800c2d0b21a401000c03d081d8003032840d00001503802895561180c2c00c0c81d91818494008400c12a49410f1000614440756681e1410300202c0d02000400c02a00c9014202101000408612240104d241415140380075036540484000a815404c081c410725030146800c8a240281e081030b00107082c003c000e100201503021140c05d048460031800c8802007150484520116091010001c0c50780004004490201c07603009c016100c414096015500c086a441600c031031051a50321040361801c0d4001428021550440c0d0580400c0c1c036145002982d110040c0c1c0080d00c0e403907015200700b15291545070403a8641d51290100c940c400d030301ca409010016500c10266010f448180509601641008940d0383c2e01d803650441da4001d810000c2080d40c604d4605014085a00d8028200c40c0c01c010300401030101060090007110003842011f00c1c005201c0d4a0548080407891024200034440ca10061440d0046001100d08035080b0190a81c01a640d020680010300c41d841421580c0c0d030907002d0000000140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 683256025 1250 683254775 683254783
    0x61201090b0f010605180f0303040f03140f06190216080c07060e010509010203251e031d1e01020c03011d1002040305061f0308040e06010f050412020616080c 69
    0x1400d8182c00c0c1e04003a40c80c0d040503102030085103100013800c10b402d0b8031034a0301e00d411220b4140b0400054141c03454242c803010302d803c2c0d4051540040c3e0b00025070040b0194400c0342045842003100038803020b408281004114903403849030191032081d4554001c2201103604c0d003405110328100d640321917100c2d030341c49051152545031821403040c0d0300442c1918015400f0382d4050000c462044005901841c90001120710600c515243c0b5200701d171000041c0c8101c0400a480d100c040f1001c200301c0180000354000a1900601d55154500c4003144518100c1f451901501c401e03a4850341c0c8020301c1040040b08500c900100d10f400509400a581582403803040080040e03440c00840000035100e069904070800c0341c2d506070581c4240d03c4000d02c60b911600019809809192401c0c0344662983c1c52414000d540751100102c0c0c4c1c01c940c000c0011000020180419580c101c514400080820705046061600c6c15018002c40b40840b98064050180024071032182c0003440711248a180d032002070140c40b0080001d01d50740ea = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 683257275 1250 683256025 683256031
    0x309011409010e0706081918170906070b091f06060e1009061223190e0d1409061b191e110907020606040b0604030c0e061201090b 57
    0x501000c00071034038868040c0600d0365038a848070018001c441c41d00004442c0751a009101c10400420301820050740302241c040c44589415000b8400503c030030508007402018400d07602c00e44041c0040224a1203a222481581c4415410450841007075131140c10003400e001c039910030100c015580503000c0340703503442d6a802441034440a070303101000c0c00251002e004440c5461501540030504000041210a01c1404403032204080c014000c2900c02c0d1031400f10801c0c0b1904d0403401054050081008040b001d251002d156400c1c0c1b0b0303d0301780304482403001c603d5201c4844d59018020032a9510034903001402c0d4070200d420324000940250758800c040c000c01101c01e500700907160316500841510f41c0001542c0c5504c010700c280c11290084804409110741340c44184100c004031845c41c9002c0302c0a80694594044c244150303070365000b515451402004000841c1c1d0700302146841034009010902c007190520503110f05981c24074058400d251201d40000303e035117101c00140782e50b039802c0050300d100704000b0121244c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 683258525 1250 683257275 683257301
    0x141207030519140c0901020a140d1e09090b010306050a0e0603070611030421061508100e0a0f03200c0907050705251502030711040203010b041e0902030901 68
    0x20020074259084401e480f01c10940c4860700e00540082000c0c101d5620081804260500440f502e02005a50700e801c0700122204541040e000990f00b40007454010a004000100621640c6409c1d0b4000c0030203040d400040c001d920140c0c1d603814aa83c1940d0103540001701402d0014888401c040c0da50f19205020982281c5480c041d001c0c4000000d255400780c400400d030503040310042d5040c241003110790503103600e110341c0d140b44060005425002080192051003801400f00c24020003190070100c0c4245445e441c01c95400c0d010b49001e4204591520205d2504942030344078003030304800f5010382000c403501c1c2c1c100c1c0986141c040810540d040390b0400013a0740c6401140640f011491079503035120a440302c0c01540409043c0d034000d074292000e035803e0840c81000da69480b2040000090300c6c1c01c80d080344000c180c5d83c01030260340000341080030301c046000380312100c600840c1c0951640d81042d0200059025034030030a000c020002c840b031410807030070720010340c09482003c030115100e2a12200d081d0107000c3e082040a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 683259775 1250 683258525 683258551
    0xc0203090a03150e0606130c02011b020604030215090a0b06060d0c0801060e24030402150d0c1b030e01080702030f070804050f030c06250512090907051602011412070305 74
    0x4080c0d01044040c0704030001071042d812440301e00030750000343c148c4800303030340031556901d04444000188075500042c01c03a403607000b040580b92901d00a45450b8500d02e030348c400241c1440812500300000640c030a2a10352000c282c03010794545002241050181d8440e60310002c0c02c0c001c80882c0c1a80c040403041c1290200c0d900d103000007640c13500b48842d40b84e0041400d600880c01c180030351a46003984004540240c406081021782c82c2d01c0c10801d0b081a08240f0b060385011740c1302c81c6100601030380145410303411180c1e005c0911003501d003a50b0182640b0182582c0b9410700060f6030000351a0741c020300a50311001402d02d0301c25034449443ca418601c5900c5402180d00c0380700301c0d0030048c400b03040000e5a28066000501007501e804a50850074144c0340f561030b02c59a070802d00940000c000382c0706101102000b00c000700000d0301c0d451403104003c8100740003071002081100074001c055038a5042003911042507020f00301400b00c813140341d10b2031405100310302204400007150320a0102040c3e0560060f480b64925503488 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 683261025 1250 683259775 683259791
    0x911090c131707050d050a0f0b07260a090305040e010807060809300c0f060403110a0b150103090b0f15010906050403020609061605030d140412030c0203090a0315 71
    0x3480055a50000000ea0b4060b01d01400319045c10042c2400032070086046403405401e0f41d5850280e40301401b01156901004001c1c008401e81140071301000d56407403003040c41180d60003488104e4081004007510f60301c40d101c410322403c0c54092001c80f800340c00d844040e081c0035a12040c5090380c5036a184120f400180e403610020722a035902040d0316864200050041001e030329202c0c1c0030104e0039600032000c00b211004000001c0d85c000c08102d5841600c04900281c10245003d0078050810100d140d0034a9140d007103001070200103180711000715804010209204181008280101c00400061000800c031100a03c1801220852070f6141441442ca00401c0001c2050305c0340111414074480c030655001c100180001d000500d0702d000502007000c00034103414200280e564240000340c00c68641a2215007000800903c0c00440e8022030304070001c4050050003605041c1d444200c148190343c100c40800d0369401820301c1d0140f0074004c0301c0e0620002000c1c20200703500c0b41000313955400803501c090001071400c152b07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 683262275 1250 683261025 683261039
    0x703061d0106050d0c030e0114060424031214030a05100902250f060204030c090e0d12020315150903061608180f0703060204031a0606030601030911090c13 68
    0xc003038141c4a032540d91070304005900c525000541740b4015032109240c4c91381c1c00710078100024071502c0004880f01600711210b041c04002c0c441115540544030001c07110800c11031500da449014003004581e0700c90f100091074500c642c800c48890305076018185904c00b0010910500058a410590003160501030385541b9030380e40e0301d0b001c00302d21580c100f115041403440e0560840528601854030f00d42e010f0503a5104e8010a651150308990140d0801c89110b02205014840700e4014803440700e1001d640320041c6407032442040003601509500040c81000c60700000040c0c4011074481410b42420700280c031800782c0340710043c04008107401141e82c4d0b900078402c4034009542d03503400c0d012600651260f44c80710100c5480d1420f03841d1550540b08081d01084c824000042e82c401d000700160700080d4014000143c960b070544c035000c0342000e981410840030340180000c1c46001c3e900d11007240c0e0441400d0074001440380b401d01d00341c40444850b00ca40d070b9001d02a402003200001141009007428006103162032003082d11015 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 683263525 1250 683262275 683262329
    0x50a031a06010c03021903210c120c080c030a093c1101081f08030d0b060a210605130b0f0a0f0b0d1425231b06070306 52
    0x300240041c2e1003a003040391440500c2000c01c031b0150007481c1220582c4804080c00d1b040321072141080050750340d2a81d0b10301499034440c45903c1c80400f080402c2c019a1424000200381210250011350b03540400404a11001c16550048103040c1c0d00114806825501c541101203028134611085607480c560700c101401d460751320f600c100c40e440d88411480c1c05a00c1d00401113a2051000300343e8812085000c8404140b9104100104c00801002c001140d4070b8804e10081002d03900750344c07007190190383d0a02c00100010341005d03031807007800c451850b401c00300c03080c08507580050800e5500160708403890203001800e540c0d1075000301c0c840600030344020480e03400301814401c0e01c10040c4250650710109440900a805003a002030100e0803428101041912180c0b0001800079000e552810310441c601e101100d0751601c000f2007000150761400c10300c0302030781c007060b2001050041034020490910700041c2e4400300b580105103030f400d01c140b5100719013051906d200701034000e00b000d002e203119840a0000c4c0030111000d40b5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 683264775 1250 683263525 683263547
    0x9060a0803030a18021306060924030b01020c1512010e04050d0e040f050112050706030e0712060608190c0e0c09060a020c09190b060304110108070504050a031a0601 72
    0xd009624540d501e07a503410081414594000802ea4110070080140e6038203c00d1a04181042000050883c40c000024000e00c4840d40107002490200c01c0d03005252443c4000040380d219641401318a003821140100e050500303175a0026400b054842d070400c410440c110140032068004009100c499803240190072071400100d800400320750010000c1d442091144070703500b040c1c01c0c01400200b1052040c0304c5400544400740c0001440d081045a400d05218040264100900940c01c0411203d00441d00440c1c90b580750740a0f080e045030040f0802000c02c8400d0780840001c4c64003800341c1d20180e0300280c001884e00385c07944d802d441003a019000496400e500741201809840700005141c544880d0304240f182d01d030014100d21043d40070b90030f6001d04544540c0c003802d20505103100d10004c1c114881c880c146c00c482c10000b89a000302028010000043c910007540780c00300401f400c0c60042c558404008503024071440e00115002507400c4c03400810014030398400a00200ba1910042455940c03600440d040c03111070f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 683266025 1250 683264775 683264789
    0x40b030303071b080f090301050f07080117160801060618080706120f050106020c010f030b18190905010c11010c1205090102090909070515040e0412120e070509060a 72
    0x8002145200c1d004805881c10141e100300e010f0500761042d101c03000282c100110300d035000c0e800014018560b01c2e00380305d02a84028001030a45443c208820000c01c0310f001401681120484410303140c0000314104a803044008141c108441c03104d442d608201e0281c900740c4a0b000c0801c8120b850f98000e5034070105d011040e0b0348560000c1c20076030f281407012142003819010405005681d00700c0c2d000303001c0d405e01915000c4c04064004102800d00d00b40014101a0100c41180030985010500002540e030b0300040341e807405c00411703030408644400d03104100701014210683d055078a0303c0110410040117422842c5500c42c0da860303540900d4003150303003242a80c020028071000184c4440214001110316440103420580c240c0005040078898400f1807a1180250748a1000d684020b60401541c03400744900c41140460f414558281440c0001034810b9107006070004110504580e46006007500c16401820f007240e1410042c4141d1801001032511003030705020703c0340140c1c401c90009030b80f801d00101c1d0600312050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 683267275 1250 683266025 683266027
    0x1030f0504060c0207061e05031510030c1b020a090b1f020709050c0301120204150f14120f0a03050a0e090c0d0f0509100504021c0b151f030e120c01020406020606040b0303 75
    0x60304004840b07607840100003030342b166205600341c90a500c54207440f01d600000d0340c0b0005054841660064495403600c18211a00322920501c0801a11500c0442d82181e00c2c00c10040f03020030100d0009243c0301807880400301d20f0401d0107192513140d0b900062100c00c807145680200659200d80582c03c4607444240109100d840c11017035207000500b001d500c00050000141c0c40c91212a8540140c80c0e00020141d1140d07120556444255002c5d180c01c1d00c3d41400c01c80b41400800b03840301021241c68540d01d41a00203414480c0114a0103880360040d0700b41103509600815044c41c0c0d1806020a009030b401a03484406040e150500e5030307103060690300c9401e0003001400e005004895429000c403029080003031040341c1054052002015200421240203a540e101c2d82e1205403510f0170001c003c01c08201180814440e50000c100701d00404807103104c002002c0000c3c074000c81d81c46480814035181940c2e20503900c50640c00003840c0c11030004194050b1090720705ca07609592107034403008100029a840700c0300166041d00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 683268525 1250 683267275 683267327
    0x12030703050618190905010509010c09241107090f0c0e0301090507051311071a10140618030a120e121002130b0c060f130b0403030b01030f0504060c020706 68
    0x407454514652400d40c4d60701c081800d800a5036903c0c25500305541e070410030b86d1602c2104404d250001700320800381041010000340820303150034140180c15401d00010911141c0c1c400e03915000403d001c482c1c094801824244514008407503504003d08511030403200103980300b0315660720380c94180115400a5000b600600c1904e003401c082000da21100002414910740c1c661442d011119400c1c09040040d002d0348040840000320b0840c80f401120052403a000880c90420070311240b850106198a43c040944881ea168040001c040c50b5085000304510351511400c9000c070100580c40c00840075040f060780e41d040c04081c0d40018064201e01e000c44010075604800043d0402100f613902070b0400031007200300701d1900366882800100652101c0c2080703606402000811289038404850b60350003a01e0740c00e2491403002152211201c115025000400301a00c440658003660700c07940041042d000740040801507800d00303140c031030002d28007403032050b016016881d000500035000c0c00d48501010841c030240e4030302d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 683269775 1250 683268525 683268541
    0x1260606040203060d0b0c04031211060109020d020d1a03010c0e090f0702150106050406090e0103200f0a09140114060301090c17070503071202131802070512030703050618 75
    0x3400040c669500044417541c544045150071114030300490031600903581c1c0c0d82c1141010070020181000d45824450f2104581342c0c0c10310001401411994030003001a2100301401c0154040d1084c581a42401c0b810104041c2c1d03642101034441860b105d0460003000801099207054a124120110300c550180d0342c1d5000038480c07000d90ba551907002140e44140d41c00c02111418480c0003040a030004e80002d200030070180704071500030320003401034092152507203031542c135580d100c1c2071013004000b20042c000110340756040107445082490300c100c08014940355905031030740342c80401024000c02c00401c0441c0c0300000200c004404803010440c040280900d072640e0300f071885003005001c444c2604010482085a00280805481521402054503a03101507407410103190042160728100003808134103204101e201c141258040305042201c008070034560030590308030104002030080c01806032180c05074600c2100c1c58a03070200114452090342c1c60802142d241c140134407a801c0365038030003071610728040d0004c01e00e85 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 683271025 1250 683269775 683269777
    0x12a02300c010608030a05030711060103210201060503010c0e031203010f051c02040f0b0103150509011a0d02040801150b03010f0308090f03010f1b02010203090d2303010b03012606060402 82
    0x1003030729000440e80c5a80e480c9031a203540d005411803000110044203201445070b0240c0d0a403440b81006000704025412340d224201868079080589582c0c3d140340130200c1d0954002e400810080c03a0040c0200b080c0d03800381c0400750182c403d034800d151190165004181c031111080007035038180c5544000b200c5065003044240814044400e14000c0030a07103a04e007040041c0e90300d010300e0062503450b400c041030741d660301c40014058405141d01049000c160301000e11064a60860301411070b21084100a00044416030f50055407007420030030b26802d8000030300400c602c134054001d6002c0502c0051110a150f80c2c0c1c00000e0300c03d000030700030500484c4042c40f082000c40c540b8800303007a41d80001404103030951000400030f03003110203082c02c81305035a4958030391900701030070402081800d640d140002d503c3c5181c001f00094542521101303190901110714074007440740d031245040c0d00300d00305003e800d80d40e00e58468034009002e410074402d0810700d1491522641607450003045418182443c0c01c005c02c041e8581c2400c000207 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 683272275 1250 683271025 683271037
    0xc02071a1303300807021c030e0f0304170f030f131809060c03020903100911031f051005030a2415180501060f0e03012a0230 55
    0x81841c11103804804a07240c92018141c940107801c108240706001500100250342c0b5004680034440c0f80b0080204040d000b0810a02c01c0b1002541d00c1801c000e0500160010b0030b81c00c420300c60520660744220318040c80000284181ca1900d648805000d01d5840b0480d03942c1c2c54618911880d400511800b07803940c10220190002a442040380b5510385c0d00e0300c20720141c0d015003480f40c40040780c89412400500a55119000c0882c3d010315082d4605041c85011980e21030203410ba00034010b655039019001c1c8101041e0301071f40040b0080965482402041c00603c2042c203420540c128075103802c0105201640780e035400700440748043c4c06030010b00f107544c4507000309425083e500c4c4000d046041e81c14451004621a41031501c1c0d0000000624900b40041c0a2000007102412145149080014020242c1003482700c140c60310300d454055045a8001c000c82e001d49481340b1007070b1155004104440017540000c20300d0701000e001d5401c0316146400481659400c810181c4110318070f0707212101d242030075907010005000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 683273381 1106 683272275 683272297
    0x120f2a010906060911181503040309030308070c200406030c0b070501200909070c060203012606011406070311100506090f0405060c160b15040c02071a 66
    0x4030b4440c1c545805146d40e6501c01d504c1c410b545108004148103000510031762a410b00e80340c0540801c1d2075000440100c1c40d03100014169503c50140c03401226040310207100c0e0340100c0a400e454480350140e0041e00301c0d49a60010010404c0003903180300400c5480d40640e6184118180300f821201a49019241c8000210001c02c081e42d80c201641c8180e00e0484000070380b9280c250b403e4403190440da100800680c0080700000d00311113550a4103010034240d030410703c030480500761050344802c4c003402004658001d040c40c0d075045044c10005004194801c2c2044088070720f40706601c0d89050728802d440303d0100c1d15071041002ca81000c0404940042c0e51903006c071070906107a40c0f00b81c0ca4070704c01040704104640c080780b81d01e00302c0c050b480007880707040c1c00140f084044d00f8112922b08204080603a5103000c0c6061181030a52540300160400445000780401c4c00c02202c0d004100000d90700282c901c0e5 = true := by decide +kernel

theorem cover : BRFrame.Cov 683093525 683273381 := by
  have h0 := BRFrame.cov_init 683093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 683093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 683093525 ≤ n) (h2 : n < 683273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
