-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2248
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:07:42.277665+00:00
-- url     : https://prove2.me/submissions/822cccac-e5fc-4744-a6d9-b237c3349984

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 404136690 ≤ n < 404316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 404137940 1250 404136690 404136727
    0x9061605070b0d05102702070c05130f0c020f0c0402070c0306060e010e070c200f033007020f0d060e06280603120c030201090b100f060302030f0a02 65
    0x2590b65500d483e25540701e0040044d0105440e401c5000802c100c020621525854002d1a90003000c40e41d8481001c0381c165a600a42c0000c00a4808140000e030100b81615000400d003101e5501600006810340b401030048101c40320100c2c80c01c11900560082d00407108001803441c7d522070200c0d00140d0b5240c11740f03428113080c40d8982c00144010f003031180009049164401e1a4101c4807610b501483c9130b40c40060803250140b000034010030340719961300701041e407000458a0200f08100070f440ad4130107032000f2001a21f0282051400f0718040740c030700030820700d0801c04040a06011300d50100e59041c081c0071790000341d04c05e01c901c0c84140540b481c95a030509001c00340d04030030052031003078058407c28109959403185613000f0700b02202d86c4c100c40c80d070b44040010b40ca2040c0383c100d80c1c112201c41c0e841420f55a0464403100342e070b6003d8085640310712411700860400b0110601800300030110700686031070104801c4425240342c1c00203050502c140b00f0098203030a040180b983c00006001c00682e50039100143d645002c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 404139190 1250 404137940 404137949
    0x314032503120b0f10031d0706090b040b041502031b062706040308090a06020d0606080117120309100203090d080603070605160320060609011403100e070503060709050a0b0906160507 80
    0x22000c00d43e10510045001c8d010303150140e6800720b00319110625200c0e580f28910860406ca04200400c02c01c5c0c17004250354021408032481a00d18240e00c5420082140100d140a5a0b05420400034020070180350401a0718045c01d81c002c0d6030300c0740070705008247c071241700400180c02e0141800006000280501003514000d90210701151101407055140000f003070b079400341402003030084002240a1103112283c51a0000750b10007045044a0380451174142c8d0400b506510040c0704c1c01b9241080c001403800a036106501d45c10040241080181c001030405c04042d007074600a8110306000d014140e400380440d28021222018030101003030ba0300c0d084076100c100d00000020070100c1f00340c04184c0d440114005004001c1100c00c4140350343c07912045018040b04e07608055050b0300c0440622034516440e005414402c046005031841150b03148046400c04000711400b02c00690500302c140000d01d411100780d00980303002d094150502d200c0070007041480c03203220903021000501e02d0700402002404c024040241 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 404140440 1250 404139190 404139221
    0xd030c05060a050118050124051312050618100b0604030210020607020106050102010b062b020301060c0b0a0203100e1008070f0801110703090314032503120b0f1003 72
    0x303140401d0300320b0007070001707004101d01d02c0c14600348880180500d00804d4160b0354403000d010b0f81803464181102c088442c0c04c00100030b0000070f202c05000144064829001004c15002c090a0104c49281c018101100245100b2036450001a00b034000c0303900107501c0b1000d103900500000c65100c2c410004146003d6540000e40c0b180030003c43c080740031340c085103081c041c86483c1c00030f000040c0c4502c0168240e8480003501a04540c0902900317000019401440120130304031210808081a04190700060740e000f43c0003480450340f4407603007108200c3c04089141e44108001021821030404030207400b00510b0910a00b80c43c45220710101d448414002d610100900c0380000b1204101c1d074404041800070282c1c45100c100d03506e4500c00480c8042503c0881c1e240320340c15034070b1415850440d030345c0034091505802c3c0381d01a44070910280c3d0500400d00074210720208904601c001c5a00180342c010720b030003160401c01c081303c0c0c1040342600309915031b08000e0324408411160102c82000b0307201e003113008000541501c00700 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 404141690 1250 404140440 404140453
    0x12060a210c1211100c08180109051302070308010b041805190501030b06011202070503030c07030903050d080a0b180402040209030c1c03080c0a020c011202040504020a1806030612020d030c05 83
    0x10480c50603d11002200d05a0744100c003a00c1c90401500c10013000030b00540b1400c1e003080190206505070782054500401410300424098a0744041030452400d01d0140342c80941c0050312005040c0c11100003401004142c68040c5414181042c00c82080701624055143d140c03038001040420800e4002e00c0c642411580341040300750380d02c0c03c02203c40030041da03007a404500c0040d81070010031190300855012a401c503008514540312a100380d401584880c00c103404118524038003000003003090111300b003140301a54800105050590129045800c41101d481c459500c1080c1c89400048480f102548a6011600140c03911810f8010078140100c446010754001007400700c0000f4603e810030031311403140c00b0756590380c42a540c3c400300300a10f100707030442d0a0142c0d0080c0c140c08465840b9850b0103c401c1c0a04c0409801c013542c0340089002c0c2e800290800001c141c03840b580d240112007031860f14009000ca482c0500405142081e603058901c0390f20710290044042e10041010b15024908004040c2d5000c1c04680302c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 404142940 1250 404141690 404141693
    0x10050f0121062c1305120c010e1603030e0f010909060b0c1216080705030d0608010e010b0307060c020603091504140d0311030a02031005040501080312060a210c12 71
    0x10031043c011402c0d800b02491100c0302c0030300c01c80e05855505002d554000900c0e21062081c0b44800c0c0e1610003180c0c00c0c401e54080b440d82540b240040e04826240100205901c0402e222480c1001c801c660884296a408802000801c1d030000c11b22100007404c0c0c0d00303018034100200c01254560b80c50b4104268131410118001941542c4e203008140110303400041c0c1e002d44c4042040554940300c1d502d104200c00801001000c0400d0380500108511449102203c0ca00300c0080062010340d80d96511400840c0d40d03c1c4180781c086c0741c00303024006440c03100f140a81421400c0817405411205010800790040a011000070300708034003001003101d80c04030300b0080380051a0030303e011000410045180c04040c00358013041e201d000e01a01612041051144089003555644413400d002504003c1c641f08004865060020f66070701c0b11301c00c1e00e000e0700303a10001d50f0703441086184034000503030046e01441c012401c81c8010002e600f04002040150300c4040c2402150f240030f4200303200c0b5421036420055104e15040042030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 404144190 1250 404142940 404143007
    0x30f03020a0207241403010503031b0a1509021915030213030204051501270308033d08060c07030f02031912050a020316050c0114040609030e060310050f01 68
    0x603c0074259501e050766030360981715500e81c038002846a6505684244075a01c1855020b285158000c40c549007226284a003584905078030007610400001410f986000d094158140070403404030402c20a000808a1850507620307140e40103011015004040d07000c2403080c507400c40a48041d0056400400500060620a1a00082003000400d903801701d0b085128600003060b00d08001c03000404c3c40e4442200d0b031491501c61104607480100425918000c4104028100e21054140d1000b856440c580c942c0e010b140328860784000c0325030323040240e843d030292081021948100048408043d414901590038901990302645180925020110785402c41c040c8120300ca41d01025401d490703d1030b540d0510890b12400c00090491000b5149070b0b0040c4051410144014000c01c0248554080300000040d0220381d0358100c100d408054030125103180e202c520349800c0c590b0207035039280c041800300c03080e6140d410910b0020b4005515885020701860044c0c0507080607a0040340002c030086200c003940e01d446850221500e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 404145440 1250 404144190 404144249
    0x2043206190605030a180203100c02060c090a18140c0901020c0f09060d170a0203182b05030d0914160501120513062306010804030f03020a0207 63
    0x40c0035102a0000e0021100710304016402c6a0098580c40e01e50388030090001c000e051084240e40e952200c02ca01480103840c20800b0700e43e200403002c40010303180c1c41280000c0c10040040e1882400da80c041c4402c42840c0d0b03a035110201212891050988500351750084d00740545072138294260358102c0a0200034040744504024a010f96007607003a03071010010a01088010004c403c03803d5040183c1100151003814400c3e402d025043c069552420507030400c1407106c000e644107204000040c1c001055180818035070140345c2e581844100ca4a0703480f444441a414201d04511444c3d0a20817884580582448424801c403401c0c070503182028031691541303045c00c022110700d2800c502402d00c82d03001d4004400106001250542d00140d448440e149227100b00e110103001c1c040c04c8200400d801943c0781c1c0008946109d44503a80c0c4009010464541e56a100846141030040c00d0a05001d070741410040025800040031000c1582070070010b807280c200c40e0049141601b01d8008407500314440149401c00c04084248 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 404146690 1250 404145440 404145451
    0x13090b0108070608014709040b030a02010e0907030e010603080a02060f01080d0f1701060c021e13020711090a0f1d030703030c12140f01080607020604020432 69
    0x49410541d515074080741e80500034819600702440140300c030641c0030245901d0045265250061b448480400b1030701c0b0328090f41c4418a08000d01c000140281541000d0041c4400c2d0201103001d00b5840c1440c0d000030784903440030740c130040c80b0310300e0f22000860080c0641e201c00818800d48000b002030031344900d00316450381d1084413000050f03c904000904074802070118503040e500500c02400d80c548016806466000d05100264140b19421100701265115404014000c25803943d5018201c0360300e0060010201041c0910104e5440900704103203d501c6610b0b20103c1e03000c0a0b5001030f903d858a0409054620303184110341d900545000611420381c0351307500729465010150b0745c104001c44022821401c10001d407251504290400d0007250003003070195110003075090841c100204001c50b0711680400b110030510f1680c1c100c20020080c481d250990702e01260141a410000306010b0900d10300281d51003100610017031245072900000020304600e01501e90f010b10000300110000c40c40346614010f1b00310100d51 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 404147940 1250 404146690 404146693
    0xa110d020f0d1b0c030e04020d020d0203010f06140901080a060302120a021018090203091501060909230a09060b060d0e0114040201051801020a0f060b04141e040213090b0108 76
    0x16143d15501d29921480380503d4140c944021001590360199034105014010650041e4244201c00b0040c1490004080000c4a00b03030050340e80d03040912549884010f900500204200000c40ea00c80742d2a003030131220550000d0808101c203507543d02d1001d01400c01342c0c03c0250800d500401410b0705000006854000038802c8501100500600408445508028102c90050910311808011001e419402181c2103001141500d22601c610002006260003e81c000c2c000140f03900c004006860701441086031917104814001c0e005116509a216180301c060040046a651340803001e08000050b44145164480500303c10344584006c4219001401014040c2d02e1550818100da1400112096118031a940c140c60b81c5040043d100c1094447c011644009810b40c0714015100002c00d0980d111403104510034440444c21031062414442075510305e1029050022007035090042c04100320034440c0c0a190b081d004c10342d260750b440c0005034084005100d100340031880d108400060020004140741610729050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 404149190 1250 404147940 404147951
    0x120207060f15080d020c060f0c06010605120109050c0711010306030203100605090907052b08161a010f150314010e01030c0b09011e050705160f05010203070203060a110d020f0d 77
    0x43c0c84603240e441943c10000180c1050800801c2d510f04100075100c0031510842e00c07401d000107031018624080c000e0300301e0808030320b0100d100c890070850038a545014240d014401d116a00f486001341c1000d000e4000c3c004d24000343c100001d01c46900c02c2d8001d400458004044417070700010b103d1035a004050300d00910b405154810001030100c4000103012003101e501420307140c034000d0b14201409003045012078900040d2284100d00c004250407001401c00007208201401c907a81e01443c0c0f1070b04048000740d1514440703494600411862400768140001c4604001058203101c41164003240202481c811007030010016100204020404500da40d0581e0302c500c020281158560040c07800c0381c0030702c02c086400510001c04004403005142515190b900c1181001400e044036662450709124001015000341d0702140001c01c000b50107051316000901c030a0001c1c40c070b4a01c0980100c2d03281ca400070040d1050035203948010103c40010000c03280e0301c129010046407102466803d90100c1d5004181002c002d50401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 404150440 1250 404149190 404149199
    0xe071401022b09140a03060209060412060b090612060402240d09030e1813020a090c0e190b04030809010905030a0305090907140a08040809060703020c13110406120207060f15 76
    0x1502c80c4d20705207400500400c407071031841c0d5581010307511801980f07811420501c4009a40410141c810003064462080400c114041da8103000e841030000709810701c00d01006c115075182c030801080a07904550107407003200d1404001c000c090545800516000e501120005080614004a6218013282403190340d800c042c05040a0400802654001c83c9c1e01011081b030b00403415400c4080310b000302c0188050021005240c3d9464464219000c42c407503e40400c9040b03007076016a1920101c00340c03160580d404c00b505040c0c1000505403090040f808000c22035000064801d480e0fa01462440000304001012214208107a190003070250308150b075031a0294802c031001c00c240500410020080031250026141019441c2200319010304028000b034418000030440045591200320080014500a400034160507011006100d8003900102c2c0303a015962818111942d440b9010040741e0403130b10280f030282030f80c808070001c80c0d0080c800c0a1000304032510b0513441c8910f91111740c101c9200c1e01f00002d80d020340d203643c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 404151690 1250 404150440 404150459
    0xb180610050406020607110118060504020f03030c1002091f020706020609030304110d020d140d02070506090a05010c05030d06030309150f120207060902090403210e071401022b09 78
    0x1607024140c0960030000c00a03600c24491184210320148441c00030071809c19a0080e281101006681581c025417038404101c103505241172400030402d420b9008507d4013181e0000e81ea02d51a14514981d09142c000a40c0b0096031b44003172400c4100404081c0820300d040101d54080e6540e807061040c41c026019240004940a03c0407066070301c1240c0001714181d6010280d8204400c45c1c00400e0102d0f408050041844081244220b60300520340c05080102140340342c0704400f07031a106c1d40f0340c09541300d17030020401c40d0215210303552000111502801c0c00c4503405561720b005429030241c41d055280152829400000345a804203400d0201c0d000b0701c50310410540700340411540741b0040110080481c011605641a00c015540103188150040d40b00140c1c80402c1d50000d002008151010781c00181c0302d6500341030105180d03014400e9101e0900040002841c1385a80c0b549824182c405c00c40c40b40b030002d800420380d074004e02441d14040f0400e5007840415070340c0c6410300c089085106101c0e0004800600c00f181e102030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 404152940 1250 404151690 404151697
    0x913030221040611010f0507031e050411041e0c05130e0f0117011e1b080114011b050a061b05070b0a05070509060d02032203051c0b18061005 62
    0x1e10541c0a190500b4484243c400440002055015640e604491605a4424840c1c0c501a10a59a000c10064912031114ac003490030703241510152464401408001100400080d01101043c1c5007c103040600d0321240c203214082040c1e0001460a010b00c2e1407203680e0050003080c640e2012204082c070261500001c20b40c0d00740c00c80c0c51000581d403c00061000e2445030080103a1582c4080001c946c40140c01003951010103a0480e1150840c2c4800b1800110341e19102d052024004500d010b103415031510140c000c03144180d0042c0c0b4144187c04101c0f000710001810b0301e180594110b003c0301d000300a2858a00b009003a8a10f10f1281a82581e0002c1d00e011b1145044801c10f90f00426640d549072680d20b003120003844c002d8900406d100040001088c140c03291000780c00025207040d8016200c1c90164120100500a02000c40340e4941030442100025040003c0d40d400300d1503030210503c0e114417170b41000c0007003c0c0c4001d9298040118007100c41d0f61504415003d104410945281c8104903076610192032601 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 404154190 1250 404152940 404152993
    0x20306030a030c0203010b0316030c08061003030311040b030c070302070e1302040b03030d060b03180102130603050a11040b0c0f0708071a0706110301290d0e070509130302 75
    0x401c001111070200384540588103005000070700020b11650110002482c01c1c1c10f0b540b01041c440100c0341e0030420300030344161040080409101030011881d0800310038541c0005e900006081c90350b03034001c940c641c0303181c001901c024000c091200d41e0b507030408480014480e00010021030040c400d20f0400308050008620850083e03120626240001d00ca690030040a000e000700982d070144030038007800e4a08001405844010304104486a980b401c0801d100300702e40c0010600101a80c0c010020959420b600c2c00744081166514600015a03031641a03131781015008505440d0700540020601280001c42d9200616a146400f41110301c4650754848054486e80d06108010b032940280d003041024189c59800071500a070501080c514211079030303948404464180396043c030881c0780880140003c80c00c3d4151100e8500d00c3c071a120600c02c8010350070103100d100b0310450014a9456480c0340e40301d01c0e0200404001b80c00300030810794061030001e08144521309901c40903030040c801d40140c0803001e0b0840e2841c071240d4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 404155440 1250 404154190 404154193
    0x3040303061a1830010e0d0807080f0106021c02031309060f1406040303050a0c06151805090d0e0d080f03040215070b070c020a080a05071502010c05030121050706081902030603 77
    0x440545200001000c4401c01c0074904c0d540707800031029520300c18019010110300f0303500e400d00582000500144100c40041c14054040b8030b240c01402496000516403d00c041d4101248050a2414508034150300401c485008102d031400000705080b80c080c0c0191080e01d500d8030010a81640e40e203100381c00c4408080d1040e41056040000b0320100344038070300400756441982401d07841046a6621042181c0ca04210003502d445015014007040013080d2001031121040c290070b02041c03c2c060b16158a0f081004411001d011102c4003410964a41c2030101c0d6056402c0400551180149152108264411641240304a03600c0742d815290010200580ea4070a40001280d02182c0d14a041a40c822403040420790784000b5070580000c0d840c104106000d1000c0c4500090400b0703503d0b03d04001614450440c815040da4100090206da82c0d034001c080d02d04592514280031090038100503400901c042d2804060040c0c0640350300840e8507034020080174003a54464501c05150380702845410200c0c0015a0141d42c50b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 404156690 1250 404155440 404155489
    0x91303020c06161727031b0105030a0509101a0f1503010b0a1e1d0a140616060e06011e060e13110409150801050c090603040303061a18 59
    0x11481c038200221018a000e07460514017007003a104035004e15a43d880900110141200e00b078001d01702440808040300c86051504041003a5200181407400001c00141c0703500ea8036000980103460411800c80041d464178020010003c0c1e41070001c1e000c0d01c08001c2d007809900707020300c1c0c2c82c81c5081984440d060a59001c8071141141d08202a40700c56a01084400e010081d00c40c8540c00c03002811501d0f442c000141d602c43d8214030001c0041c1e4500d40300744400c081d00c034a80c040d02c20051410300000f90348d144041140c400e641c840b00302c41ba45201c5000e841c000b60010345020002c0420400c002384841c103841c00050341e4070031950160b1421003208114010003000411802070011a42052400300350b205080e10000703c0c13584c0e81030113114003640043c0c0c801c5000c82c1d26001031080c0b42e100c12864030042c000110080c0080d2501c102480c009100360500e55010b8640000001c051510903403010010b0240b1a80e034450380c4441580c034560a401211b0348564507102607059100500d04070b001e082c41c003440710404054 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 404157940 1250 404156690 404156693
    0x6090408030c07050319020c041a0607052d070b07050d0e0609030f061b070507051018151202120601030c030609180515040b24091303020c0616 63
    0x100c940014203007480c608010b104850004005101911211b41501031407030302c016102e60004e00d40035610032081c0c003440c58444070040c0b005603001010b0748804c003640c03241d40d41c00c07452610038039180b490b403101c0c11140a00700e20401008013014141281600317103c1142c4d00c043e1621580c1060744902031005009a2092060100c154007599842d000c03200004e100c0307418000d1140110b07060091504000616070010020070241c5002080d544a02102c3c0b2940c0380d05042103581c8484d56645940280ca00c951622130903000c182d0302c01d890120511510780500c103650380c2d80305141c91000c01c3d0046150041090000400c880074100e20a6901c041507605070220280c917902c0054004048250101042548820f0003240d034194a000320f003c10101c0010141c64a0240e082090410b00c00d5a40410180511024000070a1076003441503006000d086081c141c404191401d04044000700300d4564014091208101c8013000b04078010305110302330740035601900710000411241c1d20411034075221250981400702e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 404159190 1250 404157940 404157953
    0xb030606060f070b130602030a0c0212120606030a02070f050a120318110103230105040b0604050a03060e011b0c11010201050106020304030b0406020912070f05031506100c060203100306050609060904 87
    0x3030b040003a4a440c5c4c10b0801d02e90700c52200342c2e80200d4080344400d44828400511035070421450700342029605400b4209103040c0400c205240780546a01c0c0700d9080400460740003e0942d0495090641c40702c0c0d844074400da18903009403503d00c00c400544001160000b05040d441c000c2c0240c0d06003010542c10034030000541d0b6503000c00c074902c0240580c10986e540444031501e40c1c44240c51a158002c0c40070441c0998508010003064401c640400d500030700b01400100a00d844c0c40c0092015681d00840202c0c0300c04143c0419401419280d03158103400301c0c41814400c0080d048074002050900520446143c500390b00010382c2600d40a215001c0142d108103c1003011880f01c420554106204080c003520348040d22002805070310003504640d080b6004080200280004e603500300c40140410b0f4041c4c000c00c21440407551400100814441c018403200700e000c07002520072044c41c1e0446034411402c40d102e0800c104900759200880c0800c075459880c00c00401c0040c0f41c074102041c410140241032007071664882e900c90 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 404160440 1250 404159190 404159213
    0x110a0f1b151e0612020909031801080a090b070804111203030615070c0609080609010b01140901030b0d0c090621111c080d050109050603070302060307020a060207060b030606060f07 79
    0x8200140c060490144000b9030103290010400ea910000c2c2010b840d00400111030000781c03855030540d100f0044c158a00c444404800c072400d4003402c0c1410140d480001840c080c08030003800800324207244c0200800144c001000c1f0b801180580b01e42000c051141090242a811146043d01c00783d0050000607850701c0d200c60100381c500c100406440c00c00b07000350784840d1002c000e070704010089105a50140300e00c600801c01d4a60005115000748400da0220002038818280303a500300c05880c80025500c0c203564065040080340440280c03508120b413030070b4100f480407403009003d0402020304041000503c0d11450391704604140101c1c5c80b500351140e0703559660385c854400c070107400c2d0441c2003001c05100344401c14240b440c0c0903000c0d22001e1313542d0714014880b03030844605030442540345107040705102c07050b200040d100c1e0580c2e6066940729a6602c400b502a8030b000712001c002401c1c1c2d400081c4090070401150400c219843c801e4003150a2031312183d00b000310754001c4203850310340b420040c084030010400c0314209 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 404161690 1250 404160440 404160461
    0x180c0308090103180501020702120d170a0e10090c0605091c050703170307091527090c03020c011407140904090209041202070f15050904110a0f1b15 65
    0x1402c8400307842c0c43c840c9136800000c15103641e580821003909508280c1e030010380d181c1c030600203010848101c0d01d0103001d405110b03900900c80140710000030388810203940500f00040c070754002c450740480e20300d60040c0a041c1942084a16014401002801600070380580782541e100510702241252401d91503019036421900a0700d952040080000c0482c004131004c04031420380007185541ea14181030041c04040403544021801d182c014602c0308880da00003d10318900201a0305508400c1c5601594024038000d608030484075440c0c40900010190180d00800420154400910031400000940f1034103941c115208408246041150790300501c0d100000c045450000b000001d00d186160045214141c082701c046840c544208070801503281c041112034014150074005070005400d102c10580401d04d81e4009900748a0042661162503850303800c4040302c2480000c0e2540c8901403454010041400341c4d1401022548c00c101d40c1d0f00c0d4155401000c02b1242e00004040d032130400700610782001700300d001c01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 404162940 1250 404161690 404161697
    0x90f050d02180106020318241b120403020316050a0b0a0903230f0606150703110f031c0b010f0e04150f090b010201020310090b060c0a03020d03180c03080901 69
    0x100b074080d840e0041601c0e07001c0c140c00d5005640760503014040d0483d07c101480c5140c031803000a83c22908082c0d09041199800f170f41500e02c19203c401808020b44103a42e40c20410350140220383c410b0121005a401410440e8002c508a0b401d1000208002c444405140a590b0f08842090340621a1203090002042e40000c640743c0442815542c1c6c4880350802e127801031035903449224285988117844208400082c00c544a4040c01c6d040c04c100c00001e192003010403461228800100d12402814010454549412900410b6895079040504e40315240da110060041494054104c07260180c801d43c80380c902c0031001038450756060140804113541c0c91204e011500c1d03100c0c0c2c03581d204140000c1203042035030003000f40740025a803183c00e101d00001650000c100311411a88107208212142ca5510101c1084912604002400700d42000c0410f40a00c0b882d40300e400c052103190107130401c00d81e0000b000c6010041650f000c10a130081c14140e02e2002e0500c10003d000e0a03813101080c070120ba8004001d1290610504 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 404164190 1250 404162940 404162959
    0x613060807180b0703030609020c0607200f01140702121608041707060e010203180906030102040e041b1202030a0b060a1e080d030501080d05032706070f090f050d02 72
    0xc1e201d182856994005408540000c65040c4c205a0907000c4c00c1c02901c030020056040c44480c8022990324078000f001c00c01003007044004402208802f00301e82114002d040181c41d0104518801540a04090b201602d9501300741d00c00110302e00d2000c1042541c101c41a10308910700103d180c801100c031118180282d82a0408100000d002400c0d0f03104035030029440006880071916111002c0c0240240b8206107055400400048542c0c0054440101c243d0104441d4160162a400c001c40d00a0050380c2003a400ca448140602007032228100140289400303044007150306603100c00b004504200300400003500740d84000512400607141140560b0700400152803048000c0d0b80b0500c0300820003402d00b8002010004407414000346506200350030600c07103581000d101c2545000892036840e001c0394088002c10030040089041d1109244441d40781c46070f101100b001407400c8940c05919808251141004074035180c2c1d01da65828000c800b402d080ba80020b580d0308801c0d00e0310051100080405100320707405412381 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 404165440 1250 404164190 404164217
    0xc08130c1d06040515030304060c380603030f0d050403020c0a06030f180305040b0304030c080f030118150512030c1c020d0504051003270605060f0613060807 69
    0x552152414000624480801d820100c041c031007150b00180401003103074a840c40c00b50203070720004120390403500c1518041c03c0c094071900b0420301c1a0b014401b180040d42c00800141c0e0762080030201400d103401d0b134582d0501180c40e0041099564031504a503450b407900144890080c0000c02e40c00303d07502034080d00640741d07142c41c41000900407609130b81250000c680e9030b17115680b0f6403481d8440da21104413456061102e1030181d41700036005d4010f17485030781d401d01d100100140805210f0f9291050099100b0b45007500c03161a40350501d041d410034003900620298040400ca01a40070303000d030103510002907860f400244d0600c42840600c0e00d440381d030700c1c00b5844200000c100a00381080198070385800c40c0907840d010300d80104000d09264058000b6010440c0511041c4025503640703c03030b2031a5801c03c1c1000606500040405144001503001000801144049000a0145641110b480388804881105c01a8030120030841a40940c80c1003510403041c00d0030a11809025424143c0c101c07640c0d060128400c100b4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 404166690 1250 404165440 404165459
    0x20d0204140412030f05010f030210090e13060b010201050403080a1104050303070506010504111903050a060b16030212070816021912150204060206191506030501030b09010c08130c 79
    0xb40c1d42203e40056441c0040d503030503450b10511608002d107402c140903e51411401c40c50841036800042e105079000f1580d004014041c003c42030081c080c0a002c0740c4146040711090243c80c0340e04100f40c0d80e242c280008891590f10600c01e1610583c2c1c1529801c0c842e4542c083c10000825582c52550305121080001042c41e980810250211501c2100201001d40c104014002a100c84444900380340074240140d0150408080403004100103d140c0014103036039101022014000c281c0c062540ca03071000402c4690724400d100d0b500d09941c0030360201c80140040c040307164803600c21080f003e40f181b03001740001c15030444581d54020310310780002c003980407502d0200110f4101402c0c5030f00403010f9200f801c88032002c00c01400c1900c049060035074030860a05140c80d45c003030b454140007000c4070114989401c0c01c1c01e00c11780c1a8084050001192060900c040d200d0f08040c0090000380820b9410a0900e0001101c151050140c800c58851030317942e001c0c0c0c41d04d8540c3c2c1c5c0ca8a050040c2e604076003043c00355102240c46c000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 404167940 1250 404166690 404166731
    0xf06130f2304061803081909080a02030d0501060f140702030c0a080f060c030403091e0b0408010b1c0f03051b01020307090312020c0114090402040906080f1c0804020d0204 75
    0x30070000d4140d0a08091600d40126038010300614000d20004144c440825000705185900084504424410b020251410720091401440042007100041400800d041e03002010b0201034582c41c00c00c003e1a41c941c0700c2620b0a02401c40c41400054400211000c1e03989000080c0642510140c02ca0301001d40410008030904050382007140c1692008452244e059001c0103940d4014070800700840c51801c040d03c000308001c0050203090301d1a6454940480322121400c4440010084084019100c0707407107003c500d003c0c0c28500348581c4913078a1451080d01d0003071080415107205600001d1604d80c3d0005580503a15500110303e64150307007000b0f01103005120700a0000390301c503c106654041d82c40d4114981080e90800445500045600901444115980015200884d41000905981c0318494900003401078821038000c00d2604e801c0c00400601e40c0000105940800e440c0400d443d031004e04075a440d020391781d5000544000230320200104015013403a8140d011000e00141000c20b144001801203100410b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 404169190 1250 404167940 404167991
    0x402061603020721050d03020906090409031b0302060a0e1203010e13050706020304030c06080609040b090a02030703060b03061f180e1603020f0f0105070212160303170f06130f 77
    0x12416013a4000300f00c02804003448008180c00c00b1810008c085011405e10b0260042550283d5951b040b41010315000d5403065000307841303803e6510001945072900035203071081034481c40304060a1807226034035001d020a0805840c1a07c0c02920b0a582c64a03424901054001c3c000c501400800079404003c500b0030305c0898041c1c160760300190342d190310f54549541100f0440d4131a2081142d41300500c9102d0340c802c031030302d6045500100340806e951100207180e0f003807000400c0c0c000c0d410b100e1600004101724044d040314184190880130755249641d0400c030890302110120310504044803810f400d200c100021030301904c0c43c000704200060310200d4180c40300c0c500391400002c425270101c0003030100210f1501034902880c014080d03a640c4c0184000ca40040d1150049200091046000004501c1c00385810010203d003028103020340f040003666428040c0040d0b4055011030058500c0200281081000c40381d060b006000292050004d1081e080162004055006000f01030710744854400718030401c0d1004010509 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 404170440 1250 404169190 404169239
    0x15120c11060f19060501020c0f01030221010906080105130b070e090106080906090d05180d050d0f030f0501030c0605130803041707090e031c020403020a090f1404020616030207 77
    0xd08102d100c0154021140c6050703e015810300c0d1040c4900e0340d000c608420300210903a080366690003540d0040e00a400782608003e01c0794007049241800403511031800c3c4c100c8800c5c010412445840300491820b0ba40111740c0c031541016103414600010f881c2c140c5503a407080c120328002c0345901c0d844c00042c0828000382c0c04940020000001d104407502c05014050300048850000e0a1411855102615038000d03154080c904a003241c103410703000d031610500b00420a600000362181503030b019802500400d02200300100080c9420080f404681d940d100d040d068030b40002007100c0d09440c00d40104c07032650000c0407925000c805803800142c2a00100050806041300440744110b002c0c072913038018903048803030b886052518146103040e0518900403085500340300112040301811145848400040c3c400c40d80002e4009403000c00016000203d90300800250b400048107006c5288004100c07600500241c8001c0e40c040f10400805244004800402c10704602c01e005917082c03d0381e62075042448801c084c4905020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 404171690 1250 404170440 404170471
    0x90709050a1b08010303020d0e01030b030f0a051204050607060b01111c2c06160b093319060e130302010c09061d0d0615030b0115120c1106 61
    0x40203602d040c038008510a1808102661454030025a10502c01806906224103910f4618140c1d100750841c07249000050704481182c2d01e080d48480c0d86640010382640c1900680841d82c0c441a14502210102d1b0402007c1508099154484100506201c2161410301c81c2c441521100c00d80c050010800400c00a42041700408109230007409042000c00e941002c4010400c1c0810340114003c41c00e40c610506071030550701c0d415001c02841881c5d01002c4040d01110411082100e10701c0c0000d130010b408002c049000070506580d45404198040074400e9a110200390400103440c4000c05648400b010f112640204900b0b54070151042c442c40c1c15241d1406051144a00300d0500d03809001d403221007440c906d40b0030f80365407409034018540c1c85001040c40200401d5400c00ca11580e6000040c041c513900200704110004030440a00201d4609120032202085e50328000100014085a09410a01191503c54900301c1400c0100300410541c0d2100301072111002464005440800c5041e100d02801001e4144 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 404172940 1250 404171690 404171711
    0x1218050c09070c020109090b0a03210e0103060501051e0f0a0905040e030304021e1504080307020a060305010503030403150908121e0606070b07030609111201080a0317090709050a 78
    0x11201c40184442c0600440c2c466190060740e0080d080021141d000c01c0c0020b05c80c86007400a81119950382c8050024420288480b2041000d0076807440c45d020907880384030615100c5401982560001d21034a40418410300144040404c0d00640c10088648041128684021100c40c3e484941254004200160a41d1000e000718101449101c560b41800c600a505601d00769002906808011541400c04601c148141420761209801c0c484184240a12603488540790241107a8a40143c0e80907403040f4404440060700c1806442042c1c1a541d010300a145410b0440e140c3ca02119048103200d071409036102041d1021031070f4980a03008501d41500144a9401d00d802c5803500058031204074041c24421409029099480c030007201c1c1c5c03040d0701460314451039607514030550007010282c0c0b00c903e141e41011040d50690010000802080b00d501c00e102d041a40c80e1586c40b030f130311002034070010b000c00c2d070040c0f1b09098100400e0b91103a000740000215034200b600c5049040548101362203042885889034004107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 404174190 1250 404172940 404172949
    0x801020c0d0e120a02060f09090109050f070c03020316020609060d02130e0f040f1a0c030603012f072a15030905060a0f0905060f0117030a0f1218050c 66
    0x125203000450f8003202c0a01d80b0360520380c407040038020003032103070b107002030216111100601514076111008241002d20340c3d4942c40c06000e090200c610b034890b0280c403130001c0c5506000307109094215805078015400c0c80344007040000c00c2d0101b6801680c0c0205d0500c607183c51941c0e00c0d001003000002c030040260301e503000f6045010740000d09401440e180743c0e1403010010828250181141c1c0140c000200b241a140c0c241031443c5503200c40680c001d40000c98408020300300400d980250f000c0c4000b45d000b04103000c1c82b0145091922046000840000d45d4101084100804140540641d6010740780c00781004101c4d0310500c0751a004d50003510403010000300104a4005440d162426114550505100303114650781c642c0d403207a00003425a28001d946240b00c99410415921641203194404100c616a0900e05903540c00310310244510300072009a915117945844010003500c0000c07640e61110310428407400c42c261400348200b02160f84881e036840243d2140030800105e0a0807901031005002006000c00500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 404175440 1250 404174190 404174207
    0x70902071b12080f0a09080a030206011e060804080706021b0a03090f0513050c31080d0f0c050c1c0302060a1112041707050304080105060f010804060b0102070801020c0d 74
    0x150401c02d0b0002807201052154040310004907005000b155549081841501d100c0302a402283d414401c201c1d00c0c1d420942c0004174079050310103000265424032510403485802034220f018020000e41b0b5640480c000414000c02b84c20010322440c00581480707100004962607401d441c00c05c0c050796020725050010b03d50002c0d0000e010f022078880d0300d0305041c04c01c0c0110301034040003070380d03800d00035900c1000038412090300059480c100102c80e03160f0041d040d10318000301d01030341e04400003050700e04074440002e980d500062011044410390f151210b1305260200c041d80d00041c1c40c0c0342581c2c28000e2007010041582d40350001002d803d40c1c55400c01d011005410700030700d44400140788000711b07460207080a803940c4001044d101c010400310f80e0b12403117541c4c4d80307020301071b1501c0c07203056050031500850035004000c0d01002410a5400c0e18000b0000e80e0346a02c1000356400c00440400e0110744502c01007008600a46c0143c01d00d02d50600488035480d0340c5401f0f0508a2740001ca03001c925400c0f50f205001c1140e44401c48 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 404176690 1250 404175440 404175449
    0x90e01080a11060d1e0207020a0b0a0f12140106051b06010503100908040803030a02090907080f2d070203040f050f030d080405070308040f030303050106170402010e03070902071b 78
    0x40c400710150340e542c040307681c0b001c5060030700c5094080354001e514049071308060783c40e00c0035151301c072140c0f082008008065041014103c0c811001e00c54040f0b1228841016502841c400b5910b4549100d140001541c0d400f4281708070721081a190100610112590848180281000d640d0503650309030542e0b2146451142d143e0407552500003100420156600081c0314000b0083d81100007103000603494039510511807030f401f2400501001c41001000c49260f405001003230403e4407544616920005c08546420045826030b849403c1c4102060310050207110b00042c40c041e01d40600c1d21840c00301c20800340913104031010b40040c0d10000301440000c01010440740104000e4034502c1c0d0601013900083d407620019100c4800300035009000805001c01000103400454103e032941e130703540340c0740d94050300100c441d40429808a414a4000030740c00b441401a008074040d0302c00100741c0c0d500c542e8011034600e140032101c540d02d80f045050214070300e0340d944010145071b0320500c403c00f100501d01d10318403801291a0b10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 404177940 1250 404176690 404176693
    0xc1208030103060e0c0d170c06010803031509010b07031809020c010f1808030a050411060f0a020d09060e1003110d09120c0804140103150605031906050f150f0a090e0108 74
    0x21400520748034041b01d00707602c035440310181c07031614040d0140b8034040c0a2400703405028441e290001940d100003100039406440e0a00310131814a41031424080905428071403025011000c004000111788590304500c4d41c80002c010203002190754094000903604010620f841e145d664000e0090000031502ca4070040782c4040240c424500c4c0191910a5203020003441c12301541c3d2250002020400144040d00007500000c0c5034540790401092041582d4010500d1480035118180803d20703402d0241c00320b84216580c0d60b4811191802c680c00780440c10500d07842c0c107028191100343d12080c84c0307081c80c0686108084a240020190624100004c001e0203481e176450a2041c1030b040d14020074810b404030390035900c204210310720060366823004030000d0600c6516a020f8002032540891181d911000440c02503281e06030f070015224030200c091003114071354400c82d030740301200a05140445c00c04050844840d0b03601c1201f5410041c0c0c4054151447d40105023100c00030784242e4060014510100d40300703015202520 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 404179190 1250 404177940 404177953
    0x1401270e0a020f0307030203070609030620070201050901020c1c050c09070c120c05030d14151e2106010302150f0405040b0609210c01030b0a120c1208030103060e 71
    0x2004207480340c00101000c0d00a9004107640e803900d440030001c0900442e8060b00b1201c85030b60b44c42c001000e0107d41d01084681500342004010394a42c00c404160b40703d60004051840c1100d580e0040d11160702040e040e074154010b101040005030380308102c40c900c4c1004000304075007080b12861b186051155452555128103d1501848451680b084044103000d0b84198030491304401c0b0b08054448004101008249200010b035075096103520390806808861890010081a1203c2a5541100408175070068020410341100c104200c080c411401d5a28006003003901c43c0d2a003403035042c01041c03008140040d21341c400c000401c11403c2c20010394544aa60301107035400c1407072a12000f65648505e10425200710b4860304660503541d0b5003421203141ca4030092030781c0030408841440c20b00401c0400081015401150307041075980d4068010652461401424003041c2400c0c1700b15909861040b9a041d1240417050703801083d1590071003c11035030240144800c8ac1c4075803462405100359845810300569680229 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 404180440 1250 404179190 404179211
    0xe040203090303012907050a0204050f0403022d0604060605010801061d0d03091806060801050102190b0919140c0a08060f090f01020a0306050f03010c21140127 70
    0x100070f40b81580c03165420344040c141403450002c2484040068040d504d4000136001081200000d40c1c3c501591081d40c06120707130381e0b43e2105032500d40c030104d0b009409070b0055000906000c1c1c8104205510601203148480400c0403804154940203003160125003990f921002400551b800c952194010101403400b480e801d40b8035490051031009142c0214021940b22480a00f050702401120018002e80d1203a2001605107849000140c89284180c5001c08c40400004c11203510214202045281000009081ca40e807690707070220703104000304108024011140814910b0030800000c40c4802d000d4401c40c405c1c996084c50850401d00c1c0070511f01c0c411a100441008a100049500c0b98400c601481444a99980070b00640c100000c034420000070354030000d592000703540c02d54003c1051f0f400c19125107028618000900d82284d46010319540401d004038900d0380c581c0050031426401503900440842d81201c000040034112000780c0080440a1003800c01c0707480300b4050b171044056180301003801d10044141 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 404181690 1250 404180440 404180443
    0x18030903120711040f021207020f0a0213111201060216120201083d050402090117090f060c03071d1c032616050306031906200a0e04020309 61
    0x14030060310509101003415424000b50900f004218003001e0814001c1003804107906000703502c81c0307000248001140300850f82d4a48001428104c50001c0d0008007040122902044038000d8001e0001c007800740c07a209560080303584c00f8050665044d90b2603502c07041d541450b0001e400d2403040c00c10303e4001010b01101f00008406d0705d540c0c0c56182c1d02807e10b20b00350744480c10301c00510880400d00c407400040959511360907810040140d200c50032030010007a001070701c54003008164400c501c1100d000803585030840d480070504031600c0382c02216400440b00900b60b108007040c10320a04949250f0301c80c2000c420030145540042d402d860b02d0042d03104044010391100006107802d040c1707050007039100e404d1020381d41c00c1600600c00c002112014462502404c101d6540704210000d040b01c03807004078010b0410040300113000714240d81c01010020040c250f4140d0701c00c0700b00b070070102031003058130040e40340c0140c4c1420180307000c0c91074901400e04038125610140c156024143d000c101d10000c0c00303644100104a1035050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 404182940 1250 404181690 404181703
    0x20a0b1b0d02061b0c16090b040203060603060913060507080406050601050a0210051f0816050a030c09020f0f120906010506070b0105190b0a0315090501180b0105190818030903 77
    0x1000301c1c1d041d40134009206001c000e005803641003650380b007440d4003255554001484001201d031001000c0c8680f55002050206030f000558803140c00040900103d0a5441c1203800700b584a1204081300841d258640c0b107440c00c2c0d4800b0341e94000400c040200384018408180103681e030002007820700d989440120000255505240c10a5110066403040401e810080b0b02c03c582008030034000c130071503a040e1640702c0e680e29902183da40000d5608078107070005150422114100849070014100082e00e40703001c803150003940c001d1140320007020041241106107a010009880c0240d44104510720030314002448524000042e0801303071103803006011090000d44d8074100a419964140e8002c540180200316400c614402c980040c0c11001001c41c400342500da0580c800082803d010001118084d0b642d803041040317680138010020507001c4600b20006108060700241c001803810314015280c0080342288600360100c17040030b20002801c50042c88100e8030242c0d0203103162034001c0c0203545404182d500007075a682 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 404184190 1250 404182940 404182951
    0x14090109061202091005060408010609061208120903040b040b070b010e0603250b1c05060d0b010302012706030f050f100e090109080a08010305010e01090804050607020409020a0b1b0d0206 82
    0xb1850780000c1c45c0b4081205e00d10008020192a8903169130320b64000341c0c043c2213140100a4014a06403000840c404626640303002a5000b0f200035280001038080c03240e40440013440030a180c4010000040c0b030003544801040180320305400703140c880c00300c1c0c03801491282060303220311020383c084818424240d502050010100c1c82c00420b0352851014024000301e0070320980d2000a00380ca000c5010800038020340720006ea034142c400d50400c0b1a50300d0801b0051a40e00e01d41002e001030500c440140010350003022022020301c890f01c14032440d0002d030b480d012030402094101c03030700294030f604425400e5407881c01260340000c00510b40d41943d20707002035214040d107201e00c02d16804510080110302d01601c294003500d2855002305e034041d61000e084030040d0a084082c40200c50541c40c202c00707044c0805042c444e01c452140c0c812022481c1034500000c00c40140c0007507a05a034000d036181074400c0185d4940100900030040020f503951210500c585a4070b08a180e848480b5003504003950b00304e02598045030740341c1e001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 404185440 1250 404184190 404184199
    0x1e0507081605030f010c1e0e040e0a1e05070b0c010f0608070f090207052107050601060315080a11090603010f02041409060a08120d021b0f0d050c03031602011514090109061202 77
    0x18440008c43d054002001c2141d003140c5042d520302e0b211315000c90b0f00741c0c03444d00804c000e032040305151180003015400380501810070f8224640c10f00114001d00024450b5404444c00030681c025011040400c076002e0b54000d003041c2c0e2001908004c040c1c0a065000001c0c210840d0841c1801029182e03140c640011010810310340e2040004d0ac3e5410005600784c40249400000301c40c0c141d80c46081c090300504d00c2614402d18141520b0001139040340000710344410623403000001040800309028004010b5003c5e01e00c03079140d5201c1b04141039000051004e4001003880642c801240071240b800c0c00707451403001d041540039888201c1b00384404007000a4080c03002907810710496a4503c1c003030100c0300a016040c61382040c48001e507040c013100000080c02d800d0b001700040c15102e84c500154000d441501c01c510320701880750000c0c800035001c803500400e130941d06400d500020580c1400c0007801e00d19100c0580100300f04892100c4c980c9042d061440e00c1ea030152144600402825082401071a840d04600800034401d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 404186690 1250 404185440 404185487
    0x1f05061c111e030403091205030d050a050601050706050714130e09010b0d0f02010c0204020d1b0305060d02010c061b09090c020c0112020918090f010e07031e0507081605030f010c 78
    0x101407203580200000c0c510005c02801c1f20f41ca03440c1a64503603005404130700410742810040b9141c1c0c02c0030710526010324416141d16241807400e0380d0388006840c00134164818011103440105101040034000c002034075404440340e8240d401c1460140710303460080c0148086030303d001c003400d6060712000f11412481d50480c030740c50881c00d03091004031200031441d0b00094000d800455241c8051241e40c100c1c405c010300d121403c0d02500842c50044044800c1202c40340d51002d03092031030b030025500a1131b0b0a004a4000c60001c40c450f074002403d01e032403071503480010000400a1900304170244107845142607105003440500782681014000070140d40300040c480400c035074002290081e0380c0e10140980315401411800e1001c074a0800039a47d1a1080c459020391075500304889102c01400110f28031042d40c0d40040011102c040503402d0b54850081e00d1022a06485500c0380400c44d030400b040000c501441989070040031a00f00000e2509001448886800c01c1c1e0514807410340c0c00e0b40148010310805003c5405120 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 404187940 1250 404186690 404186693
    0x50a090e0f010320030d1101050a2a0c1e0c0801050c040e0a09020409030e040b090615090d1e060e030c0c01111015030c060203121f05061c111e0304 65
    0x180400c2c0c20f6442c50f170520603140100a01a005500700c066401c1d910000c01c00c0b683c55003609400d0312141d00200840e03c403041c0108a8104e00d0720b500859a60030380c90304d452601403903030b03408400300900c008140f00d03000400b10071402c01c10911a860060001c5000034007290415034100e0044d8015800349580d8000c1e400009800512a940840702d12070b0000c105009591175420090600b0640c9400607005034180280e41c10380303091000c03e1600030701d805000e002c040e040140c507884080e00205000d55006205241410104503100b101400741c10b0550300c1000c9a00c1c0c2c80c5000d1045400c65071008401d45c00920102c0424107001c00c0202681e002801d12895a00c9840011030801e19141030801d000c510340001c107111190f0717000c80482900d2254446040700350729079000b40c7e520702545400030503000c9404000794084407448001c0c8684001d060541110b070ba02c40001420540105000040701040c1c0c181c02110044c89001d4004090320183c12a45040d607180a481c0e03940304491655261600c00001040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 404189190 1250 404187940 404187983
    0x1a030105040b2d13140c0703050c0d0f02060709030b07081f0b19090b300a0209010206150315150409260a080a150b0a050a090e0f0103 59
    0xc483c60610b41c054510150301c01d1084141e910b40c468103071301070701005011641c58907282c42901300310324043e58001c0550740c2d82030801c00c99520111003103003040400d10a2a40020040209441d038400540b02e00b081050000e030000c0c9415802030500d42006131140781040841e02c8200b45a401486a1402048a42e601d108a12012040b6040d1042d4841c000400040c1d4404450190892090841107551281c2c1d8800080b18001250f0190b920316940400c003a4004c1404510b6404600d030144110f1910040d802c4111070098804950300322902d6000a2a078544d0b40e810f000c00c6a000c05c3c81c0503014138501601002caa5500c5030840701114010701038000c620001008945500c11460040042c00784000c24a031860b202d07111007c3c8601100310401803114480c0700f80302907070b05400c8a0303920b00315075944451050010340140403400d011013900480114078002c40c070006003103006054440701e0340d40309840d10017411081642d01c003000c0ca000c040c1c20302c000f0054204000d8112500068580c403940425503811 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 404190440 1250 404189190 404189209
    0x40315050606123c130b012303011109040e010e0715030b1f0807030c0210020906130609080714030c01030b030721060b030604050a0204020d0b0405040803060a1a030105040b 76
    0x1124a20581300b800b5031849090424100000100e51541215200c0301040c40000c036141400070042d107500d038018000030090b200042c10100c0502e01100d00e6900d0800464211040554103001140000132a1441c2d41810300594403000c080b80020006030080305200b907225081801200d076602074908040d0f000301d1007600704503c06040145525056111020080b441980c0303800c105000c1103040c23001541450291040c0d101c2e0344902e401421142c20112480c0340294004910164401018403280d1200044c119401001d040c46888040000341032080840c6402d0003035010b1500d100d01c03a03480240d03a403408203000400c00020300b80400e204100e000000c0c1000c0c10b0707401040c000700a8081c2100703244e074112601c01c0c1060181c4410445000c200062545030401190042c00b40e038095019000141881d50043c00c8010010b00001428405030300010240c0700c0541d015580c6150100901a2900e0802201c000a0203c9100722000d0514249650360600051003980c0c40f46941d050759100030b4031044085e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 404191690 1250 404190440 404190481
    0x210080a061e05100807020604020d0201121e0e160902030c0c0a030c110108040302150903090a03031e0807080c03060a09020c030d1505010c150603061104031505060612 74
    0x840c441d0b82602018031101c5141c600c161403080000304011540b50f030241524a004284941c0135184641e42e580070700c41000c042460480c100105516410605c403224800c40303049140080b590185500010780d440251075000e040345000d50881d01600c91100080a5401c0840340c0f007940150310303940c07031424000d120702680010308860700400c810442010382c418400e0340034603c1440043e00d141144c00044036054021100140546e01003000d44c0d5000c460a03c28613803010a42c400c403450000c1c01404603038055440c2d4411070100c0d160301c460070020421015030301d80b50107480c6420310a515007100c006106d500050801441f01d01e0000c08600103031a4840c1c0b4201800d41c9079015907442200c00b0b18940c0e240c0c001418100c0d400d18183c4a1031445110005070320499105a40340320310505291202c5800d90088211100340603074a48002000600d98000c1c0d0310603584010845032a2451400d00701c0d40b428166201071501c3e8640000c11040f580c5040030380c4c180340b207824075003403042d50340510403c0280021440b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 404192940 1250 404191690 404191709
    0x1306110a050d12060905060105070b04150c020a031205070203030402010c0c03050109030c0210020c060a260903030f16050a030f180606170a02030a02040504050a06060e06040b0d0210080a06 83
    0x1d02e90407503000b00e003648031114958010404260b03100600b200f1600240d5801c1c1c00a403081187c01c0115602200003500305005130315109500000409100441ea0640c40740c10242e00941180c07800e0542224a0f800201e2110000303105911341804025203903c0000c000906200101c03100c102400840d026281c05140c0c418020050130b03a050401900444980d6404ca2140e8420b60103100341c14404601c84000c048090803850030041204001d44100e07869440300c80310040700d0341c202c050f40c12080c00e405028801d004050750fa41e04040c14521944480180684240000e540e4400700c0968441c040780c003600302525001600c500c12441800203000d111a40301021054100960b041c040d082c0d01580846040c0e40d241e490060340a00c020b0b84880748090060350607000a01a0780140c2455002947d10030301c22000d03191802c08594440040303e0690300000782e81d07019641007000b11b081502c1000c1d54200211a61040f2414582c00510303488100240c01c002c015903003006c2210302c0c40540192026148003003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 404194190 1250 404192940 404192953
    0x1a12120d061802191b080d0e19080a0f1418040b04060f030f05011103040b09060c1204062403030c02090a151a090a12050f031306110a05 60
    0x144019201034018100300b41d100c40c503485520300c2c59108649000c3c4016240003c1032400c00810384001040803035520240743d6440d002d038000b074203d1000f402070344190240040c46a42d0003c2592406000121001013402044801d00101d05000c05031103118811349050043c8a9000e00d08840382e000c81c48645000a2000c0f580804035094032400030018042030340e0411030000310108000a480143c41000c0030071551010920104011080d2000c0c4680500e00110b0246196113842400d81e104071000c1e00c0714503100d014130071004070600038103801c84032003d60f55060580c403403994480d094024000512032540c9541301000040c3c141e030241104496882c084600c4c0395a81070240148458200c1203105070364010014518180c01d1103003058071414400c40e151454207054940a01d550700d03401c00303580326100b403010010300d6407004d2590700a000381c00115940d2107886d29001c8e19083c0b02100d200d4081d0800e108254401d4a600001012a191403821409a000303204800b402d1203a078600262144c041e05 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 404195440 1250 404194190 404194207
    0x14060d0e0606030d0f0f030f0b0910080f01020a050a05071406010612050108070b093307030e0102010c1b030e03060403050306150c10020307200615041a1212 69
    0x100300750344118802d80948103d10140300c000c848003090082c070038010030790510a02e207030070303200c0d5100c5c1410130021100062658860400034060134402c841159403140281020311003c1070a10254026640c0c8600030341c00c02d001d07810040c1507400ba44c45490104080400c04e8000c0c401d044070082c5119504c2000c2c0e603e1961141e40040c000034840e031844844a043c03600005420030001151822100c1e020900f500300b0303444004000480340b06c1b22445080a003294251f80b02c05111160001040d20030700c000c42c1d600c480c03914015040410020f0081d055901d0044030403c843e810010f01c01300c07500035400540c4648031030710702954002008121a505841030204010405030001c0003580142c00c201c1c0c03601d06030001b0312502006481801c40c81e00d4990003100c5d0442c40300440360055604281141800e05400f600d120490348c46c00c000c00500c4010768001c1b000d100300f400b803d2404a044100c2a201803100c5200d02c2840000c1c03403d42d0302ca40780119120400303608072000a105500011a240d1038603039542d041d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 404196690 1250 404195440 404195443
    0x3050313120c05010c15051608010e1e0a1e050714041d0c190305060f011103040b07020301150e010807050a060806040b03010f02042c0108030414060d0e 67
    0x445904002400444030204206103110500400c080e4020740c0000d107035003401c0044594104003441210b809035420500044001240680d83c4520714560105c010b150070366070020214a4181d00124040d007001c0240282c40818117503100300000c2000d403000b07086d01c40d00c2c0d200b001049554004107018900c100003155621041c0c001c03078040d103034079680c00841a10010705441c180c440c038490306c1c1c4080ca516200042d84030311038038002d0344520b64650060900d1244100d000c40ca00716060340000190342c8401300300c00352800140140c110f40c0c003840e0007100c2d8a4140c0004d80e8910450007020201c00000c40c8040031942d01b50400c11111443c485803401050781d84486580002081c082e104960182c0c44010515081502020080750074640e101480340d00c8080902004000d80f03c0c1c0180c0554840c4001040d821a134001000141950380c030592030400305245101c84030b4860500440703242c00c008010080c201d800410345041d00d24003440100c02014030000601c0320320542c01c6001c660341c00c028245030200f50 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 404197940 1250 404196690 404196697
    0x4090f110307080d0c38011410140904020c0a05010509010203061305100b0c0708071d04150204050319060506010c0b1f0f09020705070e06010e040504050c0901030503 73
    0xc148201000c0c4458902090345541c1103000d01951544107681071441d083c401d90344260102e00030019410005a9040c600c0c1d503061401d00646500511802c8103805040300c04000b40c01040740100311107503180490000340071010328800714400c00101d003d54100c204020000c031a500d65004004541e10500c290511381c81e4240d404050741c0b29481e000015200b680d0600850344250401040742000c0310140c41404000c00300a4039080c0c545a00140105960541400810310890950001d240041c6030501d0640b0307001d20390b0050a0400c00c000030940801e00030075016500035601c043c444007000000d1001034001c2c040c0d03502035a458030913180b121107c0e20a040341040324034080c0505103c590349060041d9000e056010008011091000004400b071408403039105140018070506401c06603100c81e00d0150303a0043d08070050703803540021007074204041040498005d0000c4603082c6040d00d42783c40041d01d01901901c240d40541d80700d00008041040601c41416480401001b41d11556101e0804990301d40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 404199190 1250 404197940 404197943
    0x40303030902030f01140402040504140d09080d140d1e0218040f0b030705120a2001180303020c060a0309050307030c022103030c0c010605180714090d0f0c0504090f 72
    0x60140c4e1904944041c02000e080c40d10341c1c42d0b1801141c031107038280f100134100148242c0364844441c03040504490203000240c1a107a00d5500d1a100b681461446420314500100241c203121540030f91902d402030f004152105420720050000d904174038400041c4043c2d6206081d82032891001a40342c40c4e5040582e40c01070105001e0b5420403000f02c01e03011000890310401c08103a4140c0c01250108143e20700300c054501c808c6d40c0001904c00030102c90341ca654200300038010b410345611044c40104420350380440210184007900001001e80351954501a4442c18a909120300800000519020035806a004081c030a50300c402240d56032036190400401c030541241c07040703214040c180401c1d039155011324866100c06140c20042d51950300d810000c0c1c00300782d10030b1003446115501c3c0c0b0400920b40da2001c0c1280c0d4588260860740140d0710300b101d0001e0864140c0a0a0203558505000c0d46070740b51134176050034000a9001060403a0713402e03d07081c007001240c6c01d03030b0210340d00c0750030030195100b0070009040c1065104e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 404200440 1250 404199190 404199193
    0x60403080c100504020102100c020c0613090c08060108040609170705010b010207050415180906060e1e1b071b06050703030b0a06020a02130b040c110f01090210030e030d0204030303090203 82
    0xb0034101d94a0081d039000741c80c00303401640100c3c000704035038049a029600000391401224040440b0401040040d080000e031030414145018040021004a0065546076407030b52900101c83e00e04800080d0a030303600944040d1009549545000c20060841c203240001698041103945070f680d00d1412501800343c026100d0300500503618006401c0c1400d0190411020b03501000b400d44904000d052030780c07904469055060366803100425404182d041c443c0002401c860a000907403844c01c01040305074240f8499401e03c50380d035211b0407c403110425441940392488040c072219035481c00e609103070701c080c22845990100802029400140380d030300900100b911900c0781c0c82c28080030600034204010850b240c0314001c05a000401c00200600e40207030655143c12404600281d0103501ca0b01081c1122214040c0030085803580303e9011084004000d4034000340c111074000d110503141a40810200d519426402e410b040d1a0b22013020340900500c156400c000312014119203030340c1c0c1c904005010f0914840142c0c003130f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 404201690 1250 404200440 404200453
    0x130e0408070614010308030a0e03090d0506010e010e04050a0f03050c010c090f080f060708090f030d0c080105060c0c010e03010e01050c090405100b0f09011b03200c01020a060506040b060403080c 85
    0x2080101e0f4000c40c100c1e9008a041e9045507100804c00c00503202190504820f804100040c400781d5650303401294031140103a005000781d40c1071011815992030182c101041c803d02400c104000220002814416154000c0d24625203000918080e251030099070384003e481d5003480340c0e04140c1a07210701c108003140c1710604c07c441202d60350701c1307030544034444090041c2140d0401000110071500400302c15070080050011140501010b20703a1a007140c104140401c600d031b848a5400f50103541c0542001d0140c0760840d03116161220101b0116958800e0032421414080310b040b61001550707080d0300c0340388442d002c50001c0c81545000910910140c2c42000e000b44918644400b16900300306e0301e00e42c1c0301900c0c00504c0480c5400c541c0020001c058020600c001c0c100310400c20207005200d9120101c41016120744c590045501c60007180c104001088400c803002070340288114006607a0010b4850b005940001002034617464010100f0043c0c1864102280c0003003001600208007d1060014000c0100001c10b5918 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 404202940 1250 404201690 404201711
    0xd020412060e1b03060f090f0304081b04110304060b13020703081b030f010b0f040f0b0c0d08150f150a02150f0402090103230106090207140105010308030c130e04080706 74
    0x83c2d81e01e0804082c0d42540c004000039082d240e25032811500040d0450883e6500703286410900e20b1176115410160568024030070b07061011550081e40c482c0194115014800503003a01e402820b103000091010b40029252010201da81d12000c66040d00b0596400c1d042d543c07100700d420041d02204c026544203a10031021801540d00d5203000094030300407644408013504591a0200c42c4980e03402000401180d84020480010600100056000103245500e103882e129240390718618240406c1040a00c244920f41d01040691036000400b000c07203010072500e020307a0029034004540f0300c10303822110540c1050001140d1900c550001003504021249014420302542d4550310780344a010b050307034000e4004070b07854014000902c414003551000c605000c406c40c0c1080703044541030b00b900d0481c1d0240c80050b5001461f20148003900c0d03030520002c0791110092100303514590b1b400c0450320004002030b00d000d1010031003118214000c1140c100a00c0d0010798241c040c01d1600380041c003035200f02c4c0101c492600d810a40e08 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 404204190 1250 404202940 404202973
    0x12150602210f0403080706240e0f010b0d2408030405091303121e2c060f0619081f050a091a0907050d0c081e0a080d020412060e 56
    0x810a0b00110b20040c02c00e891039590308200d40240c901160556281c02ea0324204110b5003c2c00964205031103c42c1039001e10706070551a00d007801400ca001c0c400500c00c010300c5000c0d030f0300e022079a00d500c00c28400608520008410b98095196001c114401c084603c0c001400360170010182041e40c5041780d141206032161095000600031070302000700414404a4424842610380d8040840c0c1c060000c0c01d01280300d4a40c03989000c85c3c0341c02070020380d44a02c0b0b0b62200c2e0704c00900c0004003200e402d100002c0c00c0a0034909415800c04a000b07000e9403060b54902101d17203d072129041c0002c024456942243c1022413842c1030303c1056a82c1c5410004981d02c1d00d000200403410341c0c0201c221868011400d40c0e5031041200c50340b4450080101081c4081c81080310000d003d807103054044115501880031020441d082440c0c2d1410211700c5080314412882058001c02584804141e0040c1154086501031741d030034180c1d00c41c02c081d0117640d115800e100440380440c020b1000d282c000c0285440340301306854945451007400c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 404205440 1250 404204190 404204197
    0x110a0e0103141c02070506030705161a090102040503190302030c070b04060329131e0905010c031401061101110d0c0809060c040512010b0616060c020601151215060221 73
    0x103c0160700c949020040ca00300701d0000d5030011020310f4400d15003942108a003086403944c00781140e0f000c502c0000c42100c1004460115000940003000b9071070545454006507403405050700c02400008103050000400d802001214a5a400c400030356100701c0c0d1758400d01005410074420440441c3c1804208404207004803c403140360f86000400c6041500c045003401100c066109111603210b0356449503601d51000107080c04041c2482030004a07000c0340380d1034a0b50035a414038614405060600383d1910a0403812003035603040d03442500c1d10804218080410601425110b4040341c3c121100241d0b0110003040c2e500700201c03902c0b01d6120024540c0b10294681d5841330203c2d4414603240c010301060059140c0070114182e805060710012903220701903000100182d005c051070040031038504c3d40020812045e40103845014400f800a0841503260140412030040d19004910420019420152406d002684103080304800c0b04c40c640c0c5442e80b00d19019645001e00a0145100c00b820b982588100f203010707048 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 404206690 1250 404205440 404205493
    0x30206180d0521040605030a15051207050f060a050a053001051801051507060603150605190e04080304030315090204060210020f122701050a050604020a0903110a0e010314 75
    0x2418510741e20034050400428240749400780340c522609d0001250750342c08070300da0b40e002c000402500c1094504810880d900701c50101d000c2c06100140300000c804c0343c0090a0b0b45030495242483d955680603034140c1e00d403582c4e071404946071034080c40c18000800304107000000e041c0e5000796003550085180c0144800292000d10401d544800d0301018102d0103540103001d410130300c4c0b260401241c815225600d110302d84402e0034030510034070360b124010072441c80e103210112410050352000800d20350501c1d071030007040e000c028405030508000101250805100c1d074003a4442c005044a03018110340c03110100c40c040c0d841480798400600c00e0110044502245100700d403030a04070b0329280751030803009143d60162054010003c03071404036880900801820090741400c0c408850800006903032412444440440f10701428041c02617105004010b100d43d0802904800da0f41c103c08134050300c0b18014009050350f02d01d5001b20703015a840000010400216208000c0c840b80c9003010b540b02034500d00000021203030030a11 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 404207940 1250 404206690 404206697
    0x40507020114010b2a0105060f150304110d0b190b100903020d030314010609030515071d060d0218030f06060603070813060e0a060c050310030206180d05210406 70
    0x411040c2e0101c0c006100000d8090304040800100c1d180812a00e040d0503440035840c7d440360204007042c0350400c0c00d10b10744d5408a4038006100816a841c002c24000104010030078884004041060b580706607810500540c4850010018a00115815a8070100c80c00040011b4180b006501c41031600c41c40c822803540c01d558854480d81d03e55002c02591f44007024040d814941d0b502c041078140c18030107980d24084e08050304c2d1022898039600d0310500c0c00c03602c603440c0128400390000707202429900411440c000360100c0e41c905601088540001c18030300c659401490324034800590b04c0740d18140799101c0c040c4480c040307064850500510103541c1e22800c00b107800c2a0700803001c01c00070b05c07018001d05890b034025683c0c0079042401c1e10103507180021910b00a8004d1142d502c80c8650380c0411249000d180f0600c012032800505504000d040740340e0420560000031711a810216010492815071074080a034218004c12411090460307003030103521240c81030b208000d2400030010a10100303d19004031401c9810039a03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 404209190 1250 404207940 404207981
    0x140603030d1107021f0207141c03091517152b05030f03041104060b041202030a0b16020601080307021008070e03060f0a0c0201060509010e041b0609050405070201 71
    0x228200300a02c2070400d000a1010103112050140e112030074807400040007800d8201040c4041c0c0c5000c2e2130114958400b4201c0b11705150030101c2c0380c0398580c2d00c0d03100165400104c05d0468042c5030a80b08002c0540000e14148500380201c2161070744648200178040c424290282152610742d45500e0f00000220040e8102000314030158a08100036500e010760f040d80905407400001c155541405c550005a4007503400d54003005220600144d00011031251004440800140e8540045604107015510800c960848101c0001056440c1441090251130b48a290340c1c0140c1380030000c4141159416012a00510402001084010000080ba00e1664004019075074003103900c031045812941c0100000100b018a5a01c1000ca880c2040140e02440008800e00b9091410341045005c40341b82d03c0c0c89200316070404100300026161409403a05503440a2041d0380103581300e05116080100400348c1c230102400400c0c0c00a00f056211000704140c4d017003141c00f40314503240c51008030300b6074240d040308404188070303071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 404210440 1250 404209190 404209207
    0x1a0601171303140417030a1205040b1b040b0d02221a090111060f04050c0102150c0c070503070902040e0a09051020070b060a06030c080114040b060705010f14060303 72
    0x50f1050394420301800b01142c9441d444081000220440d031409030301030303440422080c03845500700e403000c204a20b4045042080786001d803280c001900b400f42c22012a85d80c0068810816151390080710040c1001251055544e40c0f03030b04000340254010858030f880540e289003554424941005440221042c0380400610071443e02c89500460b80300c4510765050207404c10150208500a001291045481220624040c50a0708199081c44542000e03541150060882c00e51482c40405d201e5030403040b2000102c0d01c80c06100101d51a2001c030741c1040c2d90600c507000300020411841d4000f0800d403160808420b80c103880d00342c007600a6821010b40200180c002050350b101c10f05c0140d201c401910383d220322030034040702014400c0340c0a40c230040060300c080444104104503420302c11070240c0100140c4c98200302403102c40c0c000400c40c400600030500350405603000c00701e00743d443e0b400055245400402640d9191168a00907000781a41a46031030887d04040002c81162401d0945a104001c050055807801541 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 404211690 1250 404210440 404210447
    0x30306090f0c07110f0904111003020406050714120c1e0d090506030601020c0a0f0303080903030402010203071202070803040603060618080c040b0d0b07031d1b010c0f1a0601171303 79
    0x80d1130129008401140010300f19a600c06129001e28000c22102e44220700c40c0060181107101c8178507900c03e01d401004100700c020b9200c001c03640b070070b504014500d055648440341030741454140501c0c290300c51004070381d0400943d004200c0340d600704003e21600070381e015001d60071a00c6081c104480d43c041840c56a0820607402d0550003580d020303005105661000940c2c1002803105d145940040c40c0586004806104154000031255003011810b4021400d514080d80000d54a1192080040844828040e0030019138020800c2101911846040d6900c454a611004005100ca403140c40d0024841a0302d125001c10848a04170a650358040982149009182440040d045c60f004594000c01c64501c40c4000c02d00803200703180610320a5802184846854807801e0a20b2100306884426800c603406012102c5109010294281800e0805003031800c1c0724244110b180b20105409080000b0b0114140e401d032202d4107450388551001d8031000b42080501c21202860281102c01400c0d0070903400c0035101280c003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 404212940 1250 404211690 404211713
    0x40f2c060112050c130b030f030904140103020d081b01090302012307080732070203070e1302010807050d050f04170f16051f0501090b040e0c191502030306090f0c07 72
    0x5c0712002240405002c07003c00d1a085e080e0809171182d400108903800140340074011200720304540d0940c40525419900080c6252064510091081c80009a000a070030755035600c0c0061100c000c0003c1202d080307642400782c007031708131103440b01c0040312105a0111040ca170f02004070702800d00c035504c840725503503000010f8603400c034109114070070f4410704072041a030308001c0c0c0324403081c0300603900003952100f4551041c1450071180e9040318099881c41380c10003001d003150030b001c0c070082c98091906d41d0003500c0d0401c080d616403141c1901c80300814240b80400403e4000920381134043e40c80f8002d10800c401e6410782180d1140240c64091810007002c11040c5500020400e580e1096070091050340e156000c107005004c81200072881070315100d6240c000400c0254000c1c4120301d4160b80907142484824480317500b483d282c400c926211351083c42007203001c5840e82889440e2001528810744104020303a20036001039a260012581c15100700b600200040300502800b07815405006000d22843c00c0160703550382e8104051 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 404214190 1250 404212940 404212969
    0x32102010b03031317011803081f0b03041106090a0e0c0906120f0603163501021206100c23010c09050429040f2c060112050c 55
    0x19200c8440700003594060005040302c0d413200340c0c2c200e0310030b2a00d070050303012080074021088140d14041100b200c191040140c0015103906140106881e510300500c602c0d070041c2d44a800d40008110000400c0c000c0b6400000c5005501a04482c44002000d4003003001c03d100782665960030403003012041041490022110b508032110301085401c18601201195058001010641e003a449407001c0c07002c0d10002d100241d40024080d400b0700501c0200714040001040d40d0701c0340c040d40d038118455001c040800d0880d0904c1d4000300300b083e404524001040c0c0c902035001802d55080300714840f80482c90505d13000e464100c04004c284c4951950184940760301c802d60005c0158242c60602031603107994440c101707218140050880781c880062586c1001c041c0003c80307891280c92180041202070076200e054016000421550701220f011443c2000e21310300c2009000c2c44c6005c0380c40009403c400501050040a1070a14110080304480e900e0380e0324074002c8a4411042e00c05003450700100307ca2035890414100070340d96507 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 404215440 1250 404214190 404214193
    0x5011401062003122d060a060f020307061a1e150306010507051c0807020a0b0a0b030106080615010e0a1d27100501170c06210709091401032102 63
    0x20110303205009a0740085917100c00c65100380c04400703060200c03002d082c01c1d00560b1140881c120300c0c154010034801d00e0340d40140420711201c030541000c120710810840368039562040c420700c00203c03841500c1c080c130030a4404180c0300700260805160903410740310504001c44001058058a07005118003018a640040c001c01e04001e0100180d0010803810058102c0843d020054418450312404000302a004060010400c40d040000a1408105c0c1c0750b0304142c004070242c1c1c0c00101c850300c450000340141145c0e130180741359000707040400207604a031100448440000303032030b441c01580190080120402003401601510750030b04000c8a4420000d04115900070005081012203062510002c04044a000049104d03507000c0a10044e104101740a42da0040c00f0f880e80201051012050143d00c8240c280440c0d40100030104103e0100102942c142c0b6400c8648514404941000007008180d200c5134000d000200703041400d400642e4403a034002c00e040b40e4100f0405000000d02201083c2210703070b607a00c0001107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 404216690 1250 404215440 404215447
    0x90e0709050a141e01020a030806030c03070b12011401090e04020d0b01080309040c05090a05130204031a10050d020f0d050703060e1b0a05030c190905070c05011401062003 75
    0x55449072402d5802401000702c0200c8080c1110041003088040c10181d08000326054500d40e4050760000380e00614590b0500300340b0700903950503002c649840d604503c06a858450f550340000c0301141c080c010000c2060601052209030380302c101c5040303400b082d113072100d00040c043c000c204000d60800e045031341c005200515001904079540c851096485c800c0e000700c03445030000140c0051905e0103204550798902c1a0030300c20308240340040022020f4085200d500d000d0551041c1ca210004125411180070f5984607d159414840600c4a045103010807500303e80c00208941c80401c0a150801201e564664010006c0c0c0c0c66862100510100d602c00c410110f038a07124410011001178028046c2051440c11000100800a420300d4659051401203003418040c0b8140300c400e22a80c0ca000c114003440f07643c00c2d1401040b20f4440c0440100d0350b61030383c1c07118040b01d02d05000e004190358018050041c0c02c1c0260024021504c480609002144080c8914804501d8120143c3e00d54540010348249048802c000e0b2400d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 404217940 1250 404216690 404216699
    0x70e0a0b031c120926070807051e0a081801050909040302100b060c060106032307090e011e0302221508210d050a09050d020f060601030c090e0709 64
    0x241c0089203859007080b541d44450a2203036944480380310202c01e907201c01485080201d0f1600080c0381095407801c1644000e0007201c94060300d01d40d00300d860703181d8411501c903560141402c105807540301c4449015500e0004244403c1d9980b000240314400c035810481d0705260102900312440000b48100a041c1840b1051110100b10b944494035541300354000c0d009007074145034000c00030003200c0610902c248203140502a0a09000000401c6415507000e8200000d00c60f01440c1c80614135a1500000203840d01d58008004030355a1010300d0b0f0007101c0c5843d50030009039880300783c4004c03c0c2c186240704a0360310080b12000c0015241910b0101c40e6040000c07285060036480c03c0010080e5480f04c001c0d064680d440b810704100c0b01c074040050605104412070f5108401c03100003c2506984100c0c0744039200640c60748040303841c07600360349d008000c07695028044680c2ca10341d6000285d10340e590100241480d010b2030001a0680d4064015907181d44155030300c08040c0c9080c9903e40c01c00034805805c540420540c4c0d403001c00d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 404219190 1250 404217940 404217943
    0x32705041b030506041109040906020715020c01050c071a0718141002060105010903080702030111070b04060b01030b0d0b0c040e040c15030902060714100c05250203070e0a0b03 77
    0x2010020701e8164558525504090299000680218019841c0196810f005c103801c1e02a6408204111030200d0100e0203424107030081d0048640c082c01000348441589460b032003075401445c011031803100034007040d0388441007420280a00e001c042c2c1481031410580000c407505200080d44003005091800034041c401100d10115012170b002403140700d420310120b00b0b061400600c280400c0c10188000c1000d50b041c980002c0140404e07110013012410046080000c40d5000c3d004840d454034007482c03460b180c607400c2c00c151031a0602174509450307440c58070035a440a54424000c04d944020080d0000c444107078590b542a10050000300a60380b5100248008120580d6081d0814092402843c4003007206081c4036007202c04402b00c900c0c030428145408070b802d0050b22880c0948520315003044146003214400c0301400e06210424004080c80b51034003510308d22098001010300182c0542c1c00d40900c00101e010408072091018500c080d500d0383c04240308105159001d120950b206078001c501161003080701001c01d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 404220440 1250 404219190 404219201
    0x90f1206090c2404060c110612190605030601050d0606120b07082406070201170711010b0103090510020307090b0a020a15020a0f08131401020910080403270504 70
    0x20085400c240b10140c05072422280b89101c05112181d440b50054041c0e5006250344910301c9440c091110111105042c0218580d80d0416040c019000c1c80d42d45110b83c101c288a000c04503440d61882519094941c03140d41d191191a050340d0303000e002040703982d09281c1000b0060380441c40885180e61181c80c082116444661031035103191081404152604042070050094040240382005103540340c40b08801905012030003681010041c0c960583d51152400104d4140100055070303401c004a21003805225a4009588241142c06000800147c0502c03c01103041c2d070f40c01c09016281c3c0e404840415400c0340140d0041d6005031140c01c0100009594812100d09034120038061405604064075040c2480030001540c0300c0400701000841c0307010360040026294070b140058100811046a000407480007080c0d0400b050300e600b245891600d68070180b0800c2c040c2d80080b603140c3c020300e520243c0c95680303805500094042d603496101c0746000c84400c0072f6600c0f000141404511071180c0000002401c0c0c0b11480769 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 404221690 1250 404220440 404220451
    0xe010903240e280309050d02011e0206010f08010908030a0b190801020306040f11030403110c030703050a12090e0f040c0e0702010207031404152003040f06170c090f1206 74
    0x1a0080d691050311085900d40041c2241c00640d42d40000f032000030f681310b0211825100212501a0254024001202c0030072041c0440500b500003100f41d524803c2e000181d560484429144074981d06480d029054240c4540c40801081c0300002d001258610000f5003001081010150004440500c281c01d50740740000303d0b03480507015950010034441c05040c84e010340d0002c241e46090a000f42402c50070911500d20004101404100c404852412001000d00c411140200002c04440c0c000e900e90030701644a00400e001140e103441e810003060a054010400141258000b4031020716a035110880da1030b500e00014421138404200e51008600540728460302409401c160380016100c0c0d0503890301914601c4104044070088005000410041000d80e100000700c18151070401441d040b902005201034446502d03060302ca00000c54046620b03c298001c40084442c50740d500e5090424402030748003001c20540311029440f00420602c501410704403068012504080c0900611494031a145420110305950 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 404222940 1250 404221690 404221693
    0x609060919061b021f0306420503070f0e1e040b01080606030a02160803041a0106030203102d0306050601112b0c05070906050109060e010903240e 64
    0x302070041640c04145510f07890343c1140390035400c00da03d4002421040320580340c03001d2004108042507a903446500000006c0c24242d50b02c281d5040003180803008403440604401c00284002542d040ca090314802e111411034290710b0741413540c1c5070b1040450f442c100402605060084502119202d42c590306c800c040c00c000d9030901c081d600c200c00b10401048e1000c91b40000e0411003034409002c80d81e621716044030780180f80c07207030010b9860101080e030741c402111a1101030580100441040700744020740c8401d08040d22103040d0140280c2e03da02c020b40072030000740c6002008002070301043c42802e00744901c840d07040ca148030202c400030b00019a5112541400d0b0011030345a0380f00e00c14007200e56001b400c8802c1ca0940800502911000861209410b416020f01c04091005041c0684085800340945150031a00203090343d004c43e441d24600b0000e0004c900c24580003420048000a031280300380c40150915005a42e81004145540c5440e500817040400e90144000300100000b0303008218450021007040700f00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 404224190 1250 404222940 404222989
    0x90a080a0216080a020f040e01150b0306040c1106062106091f180f02010903020d08070215030f1612060905090c0603010315020a0c1a16110c06090609 66
    0x309001010b0500c0d40514020b901010814006a4178225824010842a03400207142d01e100c0f04660301503d00803000a18950707401c1000b04900501400441c4030360010380e030a00003045032040072101d88001c250361030752680003c004140b1a00d44400300507007400e20180d120206001c1480b030142070080580304996550b000580b80500b204810f04040d52143d2040d5041120300b081e210102002048600010501c0c50380004110031680202016030144d44c0251516400d8111880d016041e6404510141c0c400d0910090003105418200105c038815810b642009000da00d030780d0300b400c0a170600307075842ca01488040909540215030501c94070340103010302d10300851076041108003141400a0010014003c1c00100010300116005004c0684a44180c07040160359031129401180e80200c400b50040032903042c041030725620303880319085602910629120541402c540b00e404d6074480318042055196030000ca00c290002d242200c040c041070540a021240b42c010b444000911028040859506480880 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 404225440 1250 404224190 404224213
    0xc121a01020105150604050126010f08070b09130b2413080c1c060b0d0b0f242205070807110304060203040b090d06061514070f0209090a080a02 63
    0x90084580224002181c010705600b030101084e1648950f005403410b004002c06800160b03201056140f081c102d41c200850700c0d95071665014142f44249116503a028032a50001040412150003112402c0130700500003001a200854440050324441c10080d50000c01d0380f0b4400c98201d84050b40c505650405111301d82d846003400700c2d5a090007440d810690080d406141c03100c445480c0d8044003203403654140c15004040d0034a02c0c2c480080c0c542e00c040550080d2507440c1d48420020072001481c0180030b5400b10040c81c0e660145040301c00a51004805203940610b010700e1010300300751000507100180300c007064a0703140c0225004019181c080e542c01002484501c10415500c0c0e100d184030100507402400340d40307031603c9e0160080d0341c1d00030b500030700015050008003c0c0041d40c501121425080d80304109211075a0b454550182c0c00c98000c480c4404a680c0c0d500b0010300302c41440884020603400143d01c515900c40d5004d000d00c0f02401040d0b10451311680d004500411450405014240403030780c010400c020f0403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 404226690 1250 404225440 404225443
    0x14090c0a0608010b030c1b10060501080c16061814150603060702060a0510080f1b0a0810020306030f0a060603050c0402032e180b04060b070203060a0c121a0102 70
    0xd680110204280381006100106070700c000c0b13a800411ba4900a0348034410703c40d40541c00d02e039881d02c0b929184030f04d000d08450345a01d83c0003281100d00c26243c142aa640d00625a5400d1090312200302c079030a00c400e60300740044e545078001c9103510b0004c1c07280481007000356a4551218a990066101c0b0340c840c4031405040001440342c0c40c2e20603c1500503001904240f5070181d40c0302805450b00c82c0032078a59000038002d080d1051b040c402842c05004aa00e040c0d507003410b03503841e14804420a805500415064012800c0a00d0140e08980c400b60040000d007480316051802034202406041d45802001c045980120003002100c81844c01408002222883c500e456458041c6440d0524001c0340180704001c0980a09880c440b03442920342040c03405010285115107170f940ba51b030811003200064a80c0c082109032258040160428240c0e01000000e44412103000f943c015044000c0d07269101a0020350b551101b41c01c400c402c2a101e0a002171303d0112129024241c8011241d07240701100c14002a040139070b130 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 404227940 1250 404226690 404226709
    0x1230d05040611070b04080d1b08040308060109060c080913050f010806010914040b090f03030c1b0106032a030803010e0708100e0615040b0d0c11060105091914090c 72
    0x104603602e030144c0c0341c0e10240d1201c001000a40800004522603401c40f12170703040070525012201c6205075000c001c0c0d4001d0040c0340c0942e4182e001030704000c000345155000d190300c6001e8501948030206205e0740340e80c0300d24071540034444803030300040217028000c9461704602821340203030354241040d1925810840b03024902401603204121442c200440001040f0407402c01d15080f581000c100800d558034031800c2480d0207800c40501105100000c10440141c0e1640c020b40303e011045180000c41c0c52201c0c02240c242e4100d4000903003d04c401602c2c2d071007218910006113005e60080901135228558a0b12428425003099115502d0100f59004011400341d07c42c06055110005900600c03546043c42054611804c0c0241507900880040403031410140380c5005030b44c014100315445580e142e0070407520704064078045800d640070440901c840c0140c43c00100d261070603504050582c101c0c55603190891101100c0400501500e40d5580d00c044900c0640f04c0c540c24030170820900241580740040381400700020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 404229190 1250 404227940 404227961
    0x3030908060901140103020d140a060501080c031f02220608070f17010b0a0e190302010806060a050f07140d021609060b0d0c300c1b0201230d050406 65
    0x91500440c40c0042c12030f040c130380e8192074068131600b20010080c503000d000323810321000504040c42807208001c00c015040c0c0010341a540e0f100182d404014211040c11f58405510500c1e140c003ca222404040514690740038011456000d04522a83c0c0340b00302d440c1c01810b001c1c3d04035a0006006a040019045d0003115114001c034440c5040d041d60340010030341b00444c000c10b005109458500060340010380740b14001003d040d500c02807250103114011140510b118001d03110880c013040c0c0d10f40001d412072500c14145d5500741010f8544038070780820191449120b0f4007142044609080c1c0d2090000c003c03904024030503a070000c5e50001e02030304c0c60001a40d610f0710b00c130b40d10107800b00c0d0400f0030910201d03c44d081076a100911a00001c12021003000782a02d209207041c0140d24098031100b100300740640c3c0446410007007411120208400e01521170205c40c5116002e82c04550000c960150300e00551149080c1181d840084100d03818648032000060520740c060400e41d1451601e070024082407040341e100318807501 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 404230440 1250 404229190 404229193
    0xb190c0509010f0c03090b0408070e070806210304030812070e040605010e0d020a08030f0a030e010204030c1e0e10080f010212070c0507050901090218010e01090b0a090e01030309080609 81
    0x3a00d40000070203a031040318084042001311101142014000c1c40c2c2c2c40040d01f00b000145442d03c0d01c80341e4241d40c0749074a00c544945000c085020502c060300841c2064000c14001e0310040c1031042002c9500151080308005040070b1004000010100d815040a40800e4071400e014407444d0a000200800607414581d41600c5640303450400c00a40ea044003500183d0345054480c0800042c0b00e0002415440c0c07254041700039808001040854104a000105030201e49078408102c920300840c5135900700e00840c040204641c03603c1e00c045c05042c170340701d00e00c0302c4e0310f0f500c0e142290005486044540041400b42d0f020008507810410500c01104144646401503000303500071800c0c80c1c00c1c400c08100c0620050000740c2400a000854824041d090151401400f0041d00f010b1281d41e40395003c0000354801d407842d6107514464100501c4c0382d84280c001429a0f04140d50b203a1469007415004d0f6a5a842528000e09200c075510b00012820019030038180203501a89520b03626034606403034107080084c0142603106a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 404231690 1250 404230440 404230447
    0x1050111120319020706060801090516081209120f0717011b030b010c05150402042a050d0e060408041509080a11040b03030304061d030405010e040b010c0b190c05 71
    0x4041e500a603036104503000320a85800740801d5070030009201c0d003030014003d00d0030808003007901481500401d030058070520071030748a20040c1c0005524039009008003445900030792682c80140c41c414001e0141c6030f0340140510a09401400560b181c8800054a014130741c000c98020040c40c01d90885000c1c000e42030800a0003403c1001a02e6a0b002c41420792610905540f0345070107072581d21030b00c3d044d000ca680c40000c03116840044502403107256001c540491103a42440c244412080b550401c10500e103d00c24a10315920020110580700c40d0800c005410451360340d016041030b010410400103001c1c9010344034840d0340d07608102031a8440d070b1124441409100f0004800c100c1c03010000351000b00c480d00400d40f00004a0300c0d10000d000340501c80000c40d030502c0040140000d019641d072222024001d800440c0150244520003241c40340510b02c2224041004003403190a14142030700034000d03c0d001450010104901603884140d03008080e11740804160800403a104205414800d041c00d00081e810080e04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 404232940 1250 404231690 404231713
    0x15130b0616030504051809060a090b0601080a150608060f010203041217040b040b2a1905010902120a141203130309150315120803220501110301050111 66
    0x91500c58454000c1c0c50307107218141003080c503102e00c05a4001d042d00806006c680c1d0860001c000c0c141106880c130420500481b40843c0740d001070352045100b00741e400801c01e8507603600c0030010750761344c040180b541d07400ca500d1711650f03107841c01c02c442e26001805007605c518a0600748a01840f00640724400308606641c0b0400c001e01001c000121480003060307201c20b002c0c00c5d201b40c401c00f00c0c00b5405181e200f0134402c80c005c900851900b003024007402820b2000061042ca060115000c0c0000c0c044c6448507110320b40110140c2072926100342c16415a00d40500000300d915022580440e0401012036014201307608001c110404104801c200030900d840d1610052004000158500c1050700c80074003c0b07000c50107482041d80030140035000c140002d003441c002001c0110544d00010340034008120000d03a40c907900890100e8913481143c14911169042100103007980c0d542891400c1040010248440f01c1c605041081c00041003401520700d20380034500b4040e103a5150400150a500010f4901903c07500504050344 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 404234190 1250 404232940 404232949
    0x1c140c030103230a0b0619030c170106031205070c17060a020307020f0106030506011d0c030610140a091a12040b0a140903030405190f0201080a0b040515130b 69
    0x905507504000610740114822030f0700042180d03c03074100c1d0300c54012001030805015900c13024a2045105403011b8030300c1c000c005080300800c1d0a0f800002c181c0480d8060501440013240842100b40d02020000156561681c854600c0c1d094206080ca00007203000850f4000c01820500c0140180307002101c907215a110010170640b10b400091941c800291f0210001d45002e00c2008446000001003008100d1039480341402c2da1210300074000c01900b540c420301860b9829140c801c08508ca411824880d50a64070740c0c00411021380310760803a41d030411020788154034002a0071401030500c1c0c20240c0307920400310324003042014402400c00700468046000e2185071441d40f40e03144040e51040c2d101c0500505652101c1d2540000c24090100034441b548a03410424028400002180140c4c0100d045902c0410000c503006140d001d4900001e1070042d51100c0080154000e04203071350005428400402c010714100045801c440b030441d4906840a0b0f0440c4255050400161048000e0100181440500210f00114 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 404235440 1250 404234190 404234197
    0x120f1106010b03041e03110105070207050d15093504230604090e0a1a010510050f090d05370803042303030702070b071211121c140c 58
    0x15107082c0380010004041004503041c054904100c4c841c440154045814010f2090030030000c26005c0350b21344004254514000920402202d030700400d5003032070b1002070f5102000001c040710b04805040c0c075040d4100004d074485030720b00000200240c0d0150701c50544200d50008684001c804502c1c038400304401e02000f5100741e1011082d06041002056034031203880400c00500c62507106051b010b2401e40c178200690400700e07150480500403401d54004100503455400e203d802880f44980c40704403070080c40d0306140504042d0540d682c00080543c2071070010004904070034150350080b600c07038200c0556044101a0f90b06030f400c004e50008000c0100e0318050041074106046451301902048002c000a820800d59420003003600c1c5152161038151681d803100903a42c0c0d00300380c440741301500440e01c011809010400644c0c182c60b41002400302107071107890701030340c3d060a03268040d9541e001d620000403103c032501000f000e0345541044100c5500002c04411011100d0000c0e0352616030030b010050121a6200b501074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 404236690 1250 404235440 404235449
    0xf2a14040b090102070503010204061706061201031506050a181409030307030f0b15091c0206090d05010e0f0607030b120c0f22090309050409020117070219120f110601 73
    0x65582c0c0c0c001c4000181d141661a9011545c59800040c01103180755205401c6060400d4880303900c04241c0301c0c04200441409003030000c14410344c9450042000c60280d59503207025103000000007038016100c0300427400180c0281c00004040c0c80b0304200030012201d034490304450701589601c0c0307401da0801402240c3c03240f00180100041544a0160540b0301400c3d61140f03c00b840000c0007031000a02124903174845400c0782240508c900140344000174443d00040e010403020340d0080c900d51409580c0b1040000c0f100b1013540c01c1d1429982d4400807241d8401c00c0210000481c621401080540b81c80d06005040d902c82c141010b001d01c2c0d041900d1840c400700080c003492000801c0b9101946018040c010030456000700300070040f5009180d201807400707010390f440740c900a0f0080e0380c0c1d00f503d19181c0703080c072081d51130b087e43c000c0c0010710100d14110071400c0c4900150304407071584140da410360903001840100752a00b01054440c3c0d510f11f24800805500407034803044959580c00c004148014403000c2c1030701c0d0b6070b0502c00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 404237940 1250 404236690 404236709
    0x30204380a09091d010e0d05160f0b070c02040609061a07030e091609050904080315011112030105180708010b0a05041a0a0305060f030705040e010f2a1404 68
    0x41d20035545000d60051809090720440c100607102954550802c0021898404002e40d4a4102400d00000c0003184404040a2585038503203400d443d0015000000f003a250240d452008114900707000039400e403051409418507945410400000780100401c5880583c01001454a854030400c4100080c3e015112002890311300507445038a0307414140c95030103584420765030100101c0f0822a00c40714100d080d00c6241056503c10130020344070b10920000c500302340c9016080420510000b0040103411018590109040c5420348070042004541458494a080c89034840340c2c001c00140441e040c01f0409211807010381005040c02d007060311001e40400c00c18020300724000c20010701415854020402c41d0300804881c0b00000039070590180c00f4034690005242e12000a0500d03020402c00e190541e1007486800008000d406524908002c02c0000d00c2c00c512494429500d50208584000b0648104045030a005000640360b005002080070840744907120181030114252a40350b08108007020343c0d065600061 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 404239190 1250 404237940 404237947
    0x1090b0d0219051818060c031807030b0a020d2901050d060510030912110309040f0612060e0d0c03050304060504051504140712051b0a031203020438 65
    0x100042d15109541085401020350007051020219403912107101e0b84480003a00b0b8083c03840320030341d900e590b000c3d60021001181400801d0743d00c0100c210016404000004540000d9521303507070b1001c42e103000c94034050401e5020900704000300c298002e101070488034507418401c0307002407030f466400040d00c1d000c02c504100000c90202d01346480356011501606006007040904114150014007a0094002c01c80b4045007800000c0d64040c058050410344098140c0554249894002072000901c101d006558145884917800542000d40031026450b07140610350110b000c0c1d122424541c070b481c1c41c1064943c100414803e0f0000440e9100c415283c02541c040d00101d02138640e41041403614044402c4174800c41d41920a0200300204404c11701a44017548007941e9600d070340d071240890f0342c0880c0c0402a0880d0849039441c2a05012031040c00703491355008001c031100c40d4032900c1c3c0340740040100c542140071980c0010103000d4a001c07441c0305844901800004c4250800c040f22036072003042d2050394251016400b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 404240440 1250 404239190 404239219
    0xf06030a180803090c0a080c030a03031a0909010605270f070507020613031e0507090b2b030206010e0c0a0f030f02070302060103020a0b120c0d0902060c0a060501090b0d02 75
    0x607410120380e4110296540301d040028900742c03114000c202c1d69103d50381e0b003080041c01e480045a0a103c141c0c0040c0501012803150700c00350081c0c0f00100007101501010781520b6401d941ea00d08060007031203032100019103031741008180b0003c0043c0601c25101e1000440303030060f48051103800e1960100c0d88200034011501c4507402603895000303400001b5805170300801d41d0fa001540c000034040440e80554080c00c20266880920180400184400760140d00411014000744542c0d800070909103030064030140d24140c122031012050300000b050443d409043c103480f0010300d54100059400341c4190020700c403050074444641d07501071203035044507001c0c000501711000c0035a00a034008103840e800003a049d503441d51681ba000392100003d0104901ca000452004285481440141e0719001035000c01054191202001a0000c2c8c010040c00c0c0c0c0c00e26141c2540e02c005031240c00207419031403218002001004a58038046003640c40503000307100f90074586041c0200300c1c0e48035031064840c2034041e15804800c200c603 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 404241690 1250 404240440 404240471
    0x3021204080a0c02040f02030a1b27080a0b09211912061202130b0a0e13060614100309050d05090402040f080a0b07090515160605010b0406020c0f06030a 67
    0x15070f080651302c0351620a000001251640041d413040b442003000b040100b2943c02c90005180f040c00001c8005420326010700c075603c03841c00d034207001e24000002c0d44d40300321fa50303011403440d0822000088680b003102c6824840d80380d804010f410340c0e007140c00842c1c10105016400544442c02180c1c00b01c0250b90048030011810b9024049404100944010904c02c80327484966883c502d00103a40103d02a105a03582d01c0b0358203000d4400c0600c0b400000380049842c4e403070035094441149026100608c0d520ba4014000009803480c8545030007414417910288804103407408004803180008030260a00d4201103500f40065400f040906040c10f031402c0050b11074111030b011600a009903002406013034405600400e010a00180054041d07120b140848003c1e40c4200c0200c0e070800c2240b050540181481c0540f400b907107074423005020304600d0b0459014680c08151614003e4070310a900514000e207002800707103c1d16905002941108400381c4007041c50384040c1c00850120310009203072503011350741c911807241000361 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 404242940 1250 404241690 404241707
    0x402040203190c0306060e0315010504020a120e07031101050c070b03100512010207021903050c060313060510080c0303040f14010203040807331b05010221100603021204080a 76
    0x594210400220702c3e454800750042c03000340184804204108004130300e43c038002070008040e2080d0080700c032203a4a00b4050001a4004030b039010244502404012020002480341d00385040c0038000829240e4510300b4460715100c1c40c50305060401c84100100302400c500028000100c800c0c210100b0b60b01d0380c402046444103c1203400a5601018010048050040c150003514516008503200000012001c5100196100510000b0241e0b000405e03250468035240e0007a5502c60795600400c4540ba0080e9501d000b21181166940914070303d4103405d209840d0104010f403101c5005500031031409090210300521a00107104565020401034a03500050b4400e1054a0007400040204d640c02501c6078815105901140000f031810a4140400410040030340c20f5650304c850540c4070481040316591440cae8826244040607142d56408000400a000c442d598002060344201f182403894208043c080c4003038a8180d12603402c00d40180200030310000b06e40b410641059004000c2a0341d0802040152100f0701d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 404244190 1250 404242940 404242981
    0x3120c0f2307060203030f07021c110a081218060903040e060619090e07140f0a030618090b0606030f1f0308031305011d0d03021c09050f150402090402040203 69
    0xb0302d14002815600040658000d41d405100400075681e9410201c3e55140305031241c0035844201c0c00e80254881c02402c500b01a202e01005460a010aa4a4480303559101801180070301e0109000c00100280030070911807410b0004011345201c0c04c1149030940c1e240a1401200c500352842d84c0482c400da900d81044407001c5070303200c804c1e182d5115403500152007070920f13104134588160030702c00191003988500c00150604406121f20341c04d00a04500c60340854100e0340d007044c00c1c1a940c0c9004101c1c1919042c60307002c140c1c5070040119080c052441d06040d01007020b0000741c040c403400d00a100d03520000b500141d6014142d2281c82001d8521007802200614440d030014180780000801e005102ca50940b0444400d800b610090184903000304540314051046103010185420084100d581d4500c00e0300100031034550303c00700210341140c1d80c81d900c04995800c0700854403a44230810115030158148180651004200100e21031840d080c6c000c0748200200800c0248210f900100094031120810341c64443c03c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 404245440 1250 404244190 404244193
    0x180504030e042c03190e1f11010f02090a060518123406110601140402250309050d1104090609050a03020601030c080316081b0a0c03120c0f23 62
    0x22001c4410f0740e51268080d1700c50303440d080514078802144900400c6003d840140c0500b50880c0d00c07884c858107400a00d5131050400420100d0309464540c01000d0260703c101c1c602c00304005a807018603600f000640312055200e44144031061103800f064013640d400000c0e51071801e07035100803800e0503c0702c07540c10003010030402c0f420500424540d461072036502d6155040c492003c480c580c64652242c0c001e40ba0328101c60041f07942d80e40a20018003441103c503102c8a0f102201074400360604103500c221924003400f00740841036203031000340da00080c940c0c802c111500400341902d00710089800e544402da02ca88044160318003d5413500115030401c08590301045071990014280d03148500c3c40e18000791106400e120a480756240404003003403a000220886001521640b10b004000a0507520bc072010b03003007000109030094185d560320540d0700c001d02416088034440c01081c0f10791400c605c1c0c6001c080300112640710410840191980010b07241342e00344182207410468200304018281000c0201002460a20030700c3d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 404246690 1250 404245440 404245511
    0x909040804120606030302071409070c11040e031806070c210c06050304030e032802032e1410090213091b0306050301200c10090c180504030e04 63
    0xe0150f00e9101005403403003a429030b21801c1e6654801c415a48115800c10351200707108020688180c0911100c06040b8400c02041c0700e19400540081c0807104907164090280d0000200c204044a9052075080c50010450f006420a505511283c4040184c0d000340720b0401059400046400752038100440201d50103c0c2d01d000d00c03a142c20b0020300c00d820039201200892030441c801d610500d008611070840c0c03001922000e03010400c692290002c1c40000d14180c4c1c0600544000045491001d0f03086d80b103002209001c03a00ea1015424490100c0b9a40c20b621450300100001b0700c003100754a641c180c0c003242d050360800342e19207140524080c151000781d403101c0c82191501580c1a0300201c1e01c9070540d0003008941b010404540e0340d000781403e8444030408102c1c8040c81320156600d4164510140c0180303486401120b0035442100751000444031050801d03030b09282d1008003003003842120000c1d044454583c0a0611440c20196000703803080300881c4d0400d103e01e841d40318a000700700a120448402440080b5480603 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 404247940 1250 404246690 404246693
    0x3140a0e0a090902091003150c05120106110d0c0803160224011e2105030403060c0e130c0c060b151803190305030403081302030604060629090904080412 67
    0x3d0403002c5049019181400c00544200d11001034035086175001850154040d8030a030078900188601001402404014441411190071040c040e60207484181c540142207140340503220700d0500c144800000b0800703050800d000280c11901a29009065202d00c1c0d0f00000000034143e040c480150003410048050880894000361042c801c941210f0300640001050b203c0801a645150000d02642d900703031a0b1100c00080300c241c40d558840025000c0c009690030503842c0d5540009885621602e170700081c0403c0803540c4a45424420107078a0f0040c0704081184a082a401410807440014040c005a5841c0c64180084c0c807412015002e100c00f41c0421a683c0004039580da0000301e40c0c000b11230103403040010020006001c200b04100e4030b5090740321207080d99030350f07502111108802004d01d20800750f680100801038808000460240340b04840201d00c503410080c0040304408892548030000c60301000301c03031080c030100341103a9120100f0350711081c282da95070808889610651740010380c05d6200255100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 404249190 1250 404247940 404247959
    0x90c3a0207121e0905090c04030209040602030105031b01021b01050408010e0f0d1701030b130f060902100e0a1a091504211e15051f0503030703140a0e0a 67
    0xe200180da616004240902c18554103c003041c0034488801182e9102424040c030710b4100401c0c0d0740404000e5042d40303010b0310781d40030500c0120160b40450f0080d030040011b01032440c3c2403000c200d404403071030f4112000321040030001703542d01501e003518415a406888030035010b0344030b03a040302c0181900383e000b0710080b40c490117603954070041106105091300611a00c48107040c0320b007509075109006210309500d240d0039602c0702c110350240600307228400703008240f10030002441d023003142c181c140c00f540000600c8205401400314540e41c12004004104070400042030700e1362514542020345840380380ca5040400381a003c00c40f244145002c1d40e0b48503045042010b00046544010019100c40c0e11802108d00c042810f6250244001400208581c0c02e0900720b02011040030800501540240e80301c0060084442c02001224010740d4800491841d00f0302c03d880000e02c1403504030081500745c00941c580b1510340c8004082203a9105812000b0f8000941005c190740b24042007020046c00806040c15190760380040c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 404250440 1250 404249190 404249213
    0x30b09010f02031003050c060406020c090712110904150e240a081f14040809040b0a0906080d05030108120901020a0c090507080a2918090606090c3a0207 67
    0xf1102c1d41306000d031801c7c1c1410090150740499007250014500b0001c0f4100f00400e00c01d004102d5810881c1030402d20541d2009402601c0300699042c203000c0d503800b045428042a150002e400c0010180212001c0100541c0c5505e1135600a01104030029005640c1d031f218880600d2076103410341d110114080c0890a0702000c200227003406031400c000c100c0303c1c3c0740086071000d07511080003103005171081d00d00160116401c50300510210340c0c003c1000680c20039000c0041c11022890300306075801a0790f00c1090000c404c0802c40c001c0c420702c0c5130034818111341c50040c0b01a0f840005a41d80601001e0115111600764000c101000109510404031841142c40720070280061008803030740f2001031711000106001560503c08d60f2038000c0b00322501110041045034404007890612115500b2107002c0480c034072105070840440380200c0542000d0b05045c1800da04000c0d5140d000b42507000426170400c5814040c8842c2c0110f01103003002d40c1304030544121811064200054400700c40c2c402c06000149010400800d042d0302d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 404251690 1250 404250440 404250443
    0x2180a090507260714060901050f13090f02070c03021c05060a15050d020f1009180b040c0302040e1906090e03120106020309030307060b0a08070e0405070618030b09010f02031003 78
    0xf0003070062070711184503a5490700e0344690542040ca050b041c04043c00c121006000c80c400604105140c01c0b10180d81d0425944001e40c03031071045454590a1021604500465046203c50003040d0709010071901d0f50990b00015105c000e1042d0340001a118841c014400c81080c0719420000b43c03400351030714145000240061100b010b1032840c54101c0480c05140210354410000d070040d03d4480c40c4645034045c00740305c0f5800440102841012540098011100200200103804030b40010130004001710601060303500700781d620303418135005000611050141c5c40110754440122443e0001403e42c01c8040402000303560000e042503420451101c0c0c410310000300401060022101c8031200380c0ea246804c036140d0041e07d2485d98950401c100c4080481d80c0358001f4142c0541c01070550418544c0e401c900b602c1c080843e030080690b89984c0c0100820b0200a1002800800150078401d85112071036016940c920181d010081c80250100046403598400b540903030a542c4039180215503071309050300681c1c0380f581d4a100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 404252940 1250 404251690 404251739
    0x806040303050108010c080105060c100501080c01090e0105150a090504020304030c02030c15030a20030403030e0d0809070e040614040503030a0b12300304060c0905060702180a090507 80
    0x51203103052050701c6c000ca100350344060f403903402c03c01004525400980308600300e1048200d139603900c0040c3e114150007442e07082c1c000c040d03d80c0075500251440d0b086521034040382180000410003922800106840c2160815000707980303030204d450586103034403d500866045840401040100341c0c01400c8003403800d00072021115040c001c1010051580d1107941201c0c600b1009001046660340c940c1c1080b4a1a400b00111000201c2040b0214075580c0044a050f00041d407600c01c481d00d00b010601c02c411040249250210080c94400e00d51039442ca0580b00364000c80d00c5070800142403244a85c07080c244004007040c55030301e03070030b0034105565a1781055440c01ca0861811860340114603145480804901002010f0b280c24070007484d840340c03281e00714452105030016a0001c49110040240118810307407140000007880035040d04010a140c5841c1c100c0e6006840401c010801340e40c034640c000311490380381d051080707003a5070703400f4900d01030520303608002d1840c03240d0b40300458600c0034020080034040c00c04d01c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 404254190 1250 404252940 404252951
    0x1005030a11040506030f03120609010608130314040b0d0c0e06070f0f080c030a020a0501051e041202010f0c09090c050f0a0c0f020901080d080702060106090b0c0a08040806040303 78
    0x1410152514200100180800d50900501030181090341016500031801030540e80790720090010581958031500c00416030700990b004201c494030b441d4888901420040ca08001507251030b0212000c10f4000c1c2202400740225041300c03184d071412030001c441c0945903d0413500e131030b00c0c1400140805020141000070104014145004550a020080c0c49039241c000e402c080d0440700e80e407251a4403940001c2c081c1c0300c4110400100c09084000c0000385a4000c82e94000c0900351514203000c1d08540700034050016231041c5409091000c1c0310701404a0300280c000c0707280031110078001e500b80e00620000a80c1d0040c24281819501b04c0c40e0003014031000ca448000c01844249d1015404661034810030030400e042d52005d101c0c0c0d40642d481450000038642c4070707042102101d1403c0d000603100140c00d0b0b001d03607100d9200240361201e00f544400b100d81c0084441c0010070b001c0d410700740c015110400d02c2c01790384040103012521964400082001196103030300144201d40e9a40c03a61585034841e0400c81d42034000c00d0418 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 404255440 1250 404254190 404254199
    0x3040302010e01270f061d06010906060e040507021528020f1909030206040e072d0c17030c042d050d0303090b07090810140403050c07080d0810 63
    0x180030700051008243d03103030101000d564181840009100d04c0c2580c4c215000c006140020f51184600c0d0014141c80100140ca00c901ca50741d103281c40b81c140c11104c1e0140c00d0010410100b074100c04205c5001000300c5001ca8281d84480040703240603e0310010002c2c1940c058107220070100c50805101e01494600c203803040308100410000207a114400c031031554400200700d000b21000404c900389144613181c0c038022080590701e4001a00c07075007280c1c1184211020315824000c07a2500000c450045001a2000d41e80d10320128500018216005802e0401c1c4216a01c0002c00c025801d0040100352500f50b08080c0c40341410002e00d106d9410030f00034102c61401c0a0400041ea00010f03c6d080404100e071a648003030340c3d05210900a081c11950411001e054942c0c0e1130100041c00c0b400380e54850200c039600c54601c01e1519122602d06055201d070301070803514210390840c24550150016a01640604100350b88030101e5580e035291202c250702419441c001c0100306240c4030360000e4120b014070411015014034036143c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 404256690 1250 404255440 404255443
    0x51b0601030f08071a0109020a0f0c03140c1e071d04210c02030312160e1305041106220e1e100504060e041406010302061e0403140303040302010e 64
    0x7070101030100c0c560030401c4400515140002c0032030034032030b010640c4c2d1580d99807407807000c285007a040740c283c4a0300400e40803805540840030503d980c40170324060140045640b0b0142c1049600c06602e901380b0320000700c41813050340c10820404514505401d2000d00000c15003100c2e19031a940c02107101465502682820449200e554540280d4010700d10740c1c0b501c4946105410020070390344a00040c04440b10003940540e5013400613202201015200c49001d01e0000c41c035101e00005032a001c410700440000740001c0d038032202a00c0416040f40c1900088a84a60800004000090015680c0086c0016004103c4140082d0010780c5c4001c4410129030141c69041381605c1090460307008042c1100b48503041d00d0703c076414581c07541024020118501080c1c4843c0464151303003541e00420900919001032004003c1602e4440e0310003600c0c3c3c03014042550666001440a2042411900d5111604012800c103034904070102d0f070040d5400f841a01c0d1014074210019205c0c1c108440550141d403a195403900769120 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 404257940 1250 404256690 404256703
    0x14060402090310020c15010303030c0807020d0c0b0c2506050603010c050702010e1f09050a050303120105011d030102031017010506210f07080106031b060504090b12010903051b 77
    0xb0040c20001c40c1c00c0440100a400420485000b48916440030110301c4c115180300d4040c500942d40400c1740f801c521005420b152024055208540c0055581c10b12030b548201c2008007598403030500802c80c0c60340300c102e480a029801040100080503101407110403480754501070700354418001801983d80340c1c02054200c07401c241104c404242c080001d00d006610404c0d044144241c002c02d074803024240120304100c40b80d00003200e10041500480140000c1c40c2c4400380e0401014203d00840c541000410015111074061081505211000a5a0001c0305a80000c858484000350003152285000302a0a030203102a208030511140d2a40310940140010702900b8400c2c003010b45541171188183d00c0d40c1c0c4c020300c070003842c0720514010041e5540c0d42c0c040038000d80f401001400000b141c180d0940c18a9001c9071300d8402610340f815180401002150740280503202221540040040c8922510300413130b0000080c807241c0403080d445d2240d910708040c0c209021b0310b0003140a21450040b611400d40050b607641 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 404259190 1250 404257940 404257957
    0x905180d0e01140d0e0f060106110703080a142b06061e0807020c0402030115170f010501031a03010c2d0921172706030a0f02090d030314060402 63
    0x20200121000ca0481e1500180f124050b1040e000444600d01a641810f1080741b18010700190007140040002c154403540e9048108051400350070780720b1075980c0d880664441c0444c1d1001f800300103413001c0050314812081d10304620381031000c4c85500b0650399019101c40c18030a00000460314007400030030003900c40c1180303840c410108100c030310103242c6026041d1400d00c0014000000c500c1940d038081126101e03800514001d00700e200b40300220159540740504204c0c09003240c0d40a400c2c4000820421130b01c16136006045030700a09000031070188030740c14501c03030034480702070981c056081004c40b07141d10342c3c85485040422003034003810100005001c440034140e415482c5c020006829001c007880b5810a14a08110b2082d144006804400003541c0d010324800c001d4400c2e00105501040d0004014507003450070145011002018048410701d000041d120b000c0075240080a13541c807002c0121404865040ba45540c0d4020440c1c40007118a28000b0f01400b20407414501d04c08202d40401c0c090704140c000e0380c0713014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 404260440 1250 404259190 404259197
    0x12040f0f060f0c320c0d03200a020a03030513080d02030d113901060e0c0705011401080102040302190b0708030903040f06051210080705010f090905180d0e01 69
    0x10304244101e03104441c0702c4080d60407621500d888100030b03132150f4101c03455100c0400925014031000030003e04054900c0e40140c000c1150459520001e540003924203091f640e00c510b030030700f0f00221030102850440002c000030f40140c0210f401005064006d800313000c01e50410390030207178001d459010340b42e107030400241404096030003480f00100c1002141c0080c2c0c01043c008040c141807880070304601700406220003015800c038102c000351043c00c6006c0500d00d14075030005070081c49003074505203007004140320040c0000814100400c0107400c0040030741041c0d00c10080c03241d440a0300c0d611950454000d62145c84100d00c00c0c5158446000f40d1041030b0b50200c1264000d00442e4101000b540700c580981c1d00081c800403031400308000101f030b105074440b1124041c0c4503554030720b604c40f000304040107403181c405091a0310240249008106181000540074180c500078606203900344440c040c140ca4485d03041e000031b1140c0d414601085071145c0e2105030b0600f8032042d0001c8660121814000356694a510702c2c100d07000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 404261690 1250 404260440 404260457
    0x90305040806460c0f080f0c0d0911101d01020609060708070908010f051e060a03030e0310050405064008070f060f05060307050f09071112040f0f06 65
    0xf85071843d03008104100e5008981c440d040d22007000101111110050760002c00c1080500d406416440299a070380100307030f06880340642c1050801c010250103400c02078612540c89829030710030001181b10740305240304050010f0415001c3d031400540011190402c81c0e0301000c051b8026a42036100284007802406032201034060740d2220107040300d5554004200a0510460b418009200c1000748151002e42c2c10407000044c1a06044031402c100035080d6034079480041e028010300049a03207000c45041140d41c581807a079030340f140761300100e030610001441c445070541c40c0c03004004c103100003c240c1a00c100ea1140301032040411003840c41c11142c030003203500307a07400003080d06401444c5114000318002c0790088507214282310b41e46d910b000082181e50000c5994544400d030452014013640109a0407100880c080c1c01c40c182840081044100c990700100d02c00e00740140820000782c0580000c41c81d028014058800c901d910340c4201c400c1d40e00134441c02405041880000070031684004400f000d039075883e03070b03031401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 404262940 1250 404261690 404261761
    0x105010504050c0906190903050715031d0c091807060507171207050a020a0605070e040b060a020c090a060305330106051c0e0d0909050604021201030f0602040504090305040806 77
    0x1b002c0c030300c91040f0512511505c0800071800802c00d0704010200c0c41d5103001c0c1415503001c010241c512110401502e004090b1041c107400c640401c00c5e60f40303c281030300c0c1800d0039928070384100c15405400101d60958020b40c40045003840e407180041800500491807641036105404a4000c50f201d4103002403541d074410804140c51030f1040d8000c11900ca294030440e0300761082c03925401c049810030b54611010a45940d80401542010b000301c100f4403c084500c6410080c10318400382d2a6034828807550302c6050085c00043c03c2c80c2503a413210014540203801c440104240e98056540811107071042540c020003200603001c0d100401d1541d40c16199540c0d6624180108941d9419400c0c480842c42180c594840c2c9002c01c00709010058080400500e03520402024a455914402c8403400760600e40640d004006080390b468103032030858112070b44400b03200b45924403428040c00900942c0c200c40e40c0b060420580d0414158040080c1080d581c45000b80c64041e2940d44c055040310203a000c1c0d13008109640032041c0d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 404264190 1250 404262940 404262967
    0x904110a1119120f020f030a0801170601080601091d060702060601120207020d030806042406030f0e0a030e060f030103080417060f070f14040807080105070503011220040e0105010504050c0906 84
    0x7100013441e0f00440d030509003130070341e4581103400c000184000a004100100700740d02c030248001ca284600d1401501c20340d4180340105031518014050214104c0e1114404441c0c000d056801c07021000030401603038100c1c1020b000080d15103106032445030000f028141c106484114038801c40d05285d0f03004060911004040d0380c1500c0c100c10080c131007a401942c406aaa0b141a588244003c4203c03441820205031420000040c0031155640c803000644c9244c40301401120b00001031480310f068240c10400c0842500074001002442100075186140d280840004104190754004e8030554a045046210b4807140c904100d80c6d482c0119001d030809203003100412400b900a11040c01c4c480c0c2e01c0c0c07401a201060042e461109035000398800038040d4054401088a18030078414503800114614041f07213154900403040116501f5075001800740300142e20b0011045215481004502c4005170084c4803808445511600800092081038012420400000c4400740301c00b00b02c8900359402060942041c3d5410f0b00034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 404265440 1250 404264190 404264207
    0xb2208030a0f03180c030b0a140606091908070f06050a0c030c1e0f0209011409160e040f0207030e03030307140c0f19050d050a0909020904110a111912 66
    0x48051603921030b5138044860100e014442d0f054040d0070301c0d00081e03282d403400c0c50704000d00824040c045071a0145901d1100b80969155070051400c5610f26210240000081d1504904c0b59000b5460307a07404a0003c2c5078a00400e1030b508607030110032070a80c115603800c01603900b4031803284503100040d200c43c1c01c2e5000138040e10034160340b1400b8030003045000129032030901326210381417002d403903d02e04001440110b00e40380c0703881c5001d00242c1c0800d0740b18a980b071000c6441604060016420131110b4041029000e1180e200d02070780d050010400d1044c2984d05400d500207500ca64804d03000294034242403000340c2400000c1380d005101d296034100c0b0507034860b0b0005600e0303041950069101d0042641c081c100d0a820041e444c05400800d4445049a442d81f070b11a240021902000b4103004041c003036040040d411800e00022900f003a1005072342d86044400107002840321003a403249400c0d000c0f4100b00240e0f400b607828aa4002518100c6200340d041d5681d00c13421041c24400206662010807400c0d14861054104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 404266690 1250 404265440 404265467
    0x30c050105160c06031e06050105030705030403110a11130b060f070c0308030711070602010c0203030f092118030304031722030602210601020d2006010b2208030a 71
    0x208020790300d030340f20903042d54011030000392102c20711a052072660342001440d03011103408106051070080041d109010041c60b06042c8007000c00003c0615005248105040c544a030903104100c000d40352400460b038052480c14015014408400141c50241c803840d002c04000600450510401c807a0003a40c95100d103400b25501d2101800000000d000d000c051405050503488565440402c04811403420007507a000d04116810300d03400742035075600881141d801081c8240b100200d551780c050840d14010740380b2500120031417003a49140d00e190405004d00555110300c1c100d00b035003122203030030559207001c0d0b80409080f1980c800c006840300b00541c8028a12501a07002d203081007007401c80085010700540e17205a60301500050b0442a2800c10340002c0300e00c03a030001c0c040c1a40e050000000b0740d1089980000c0f0280890100c81032254841c04c00341d1184185008100c46140da10f034070708c403c5180c0084404000002c1e40d4010301a520390382d0110102510440e000075418540801d1084459601c000007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 404267940 1250 404266690 404266717
    0x50606120118090b0109020a020f03070b07080408070819081e181501080c0108070504030b04020d05010b060a020109020a0602070803070303051009020a020105040203100506030316050111120f010f030c050105 91
    0x307403c0000b402686814000e200c2a0001621006400d40c080d04010452050307800c160802c0100e10005078002c1d07005900301129161890300c6036074601d880503003441494000f8180f40804a50080b0744829090141e0b40c990060741c0300781c07e0b91255840c01d10124400014041c1c1710f2041c10014800b4007105a10880030001070040380d00c400380c0c40c649200421002e800c000110781055008215039608a41100c0d0000010714055150618580b102030287e00044c0000740719000004c21031301070080c250484500c0043c01800c03980d480582090290003042c0c4100c04901681c099140000c0080c008150035084415240295281c40380c20364046000b014020310061201c09612004142d0a1082c40545480d0f80c00d070f000000c580c00c007401003503c0c0414201c1c12090490800301008940d88011080e0341084411041c00c2c120720241d0702d0081d000d04040c84480c100380d0710116a4503030f440940300483c0d0084100354229444c990300d8a00340000b950f001d0101170030000c4900e03001c00440d4806c0d03000300080800c02c0c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 404269190 1250 404267940 404267951
    0x1b090a0504020f04050a080a03020f0309060d0b010903060f0f150815091f020a030b0a06050406050d140928050c011b06110c070609050a03060504080c01110d050606120118 75
    0x50141b4503607081250190700010f440410550104020094401312500440c01c100841c03000403500c0c41481107162240b030b04c0f603542e00542d034060190603001c0d40d8803800610034105130820342c10060040c4461a110a42441e0031075940c40202c40700328041d9540a4007518010324540b1420342d600e84040c1c420300305849065081c0481000c0c03004c0003d0001131009015a9a009085004055418859456100b0804200d04000c2550404c00b1941201c20505016442d0398107404c40e60b0080a20303250301000d18041c58104280940042140c00d11301303e54a4014000c003020300c01350794110041c0340000f4030785d6001240c6003190b580103908480150105004034400d4030744a55545091b910f0500d51810102e101241030700300c040d010702a11020b441c103032070840b03001d0345404000342c40340b41d0a10004d0201070707843c000308051013001000c5070b111440174002401103013160702e0710206d5a800842800345103840d02012a00503e00b003011500050020720440d440d6900f08001e100c511040400f8401c4400e981341c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 404270440 1250 404269190 404269199
    0x150801020f07060507031a011416050724092601090b10060c02030a080d090f0f0606090b092716050a0b0712050a030f05040b1b090a0504020f04 63
    0x9000800480d100e0401d0340b615808903180002c10b45030003504043c00c0c142040481c8541035084400080000e10918010f400d00070b80880e00c103403600c43c5898080c0da040c24900f401080c000e000442c002290142600c070703080c0b25006104021800381c00907061000440300c680c01c0007000310030050041c02891071003000c8856402c64110a003141c1c00c440c4216040d0400d8810401e8150f1013018003402002241842c0d400080d0b1603000948801031030320000c03d2410007240030300100709503510000c0f17070580c000d110182428283c14504005c1055400c222401030504501240c0e2003c00d0040604210029105012a459030005800036141200020002c00c0d44101414240c24040110140c48501003074009119410601032011041a81d0000c4c1d202c403000b0031415002800d44910281071b10411b180141d120b134031280088019000140d1f481040b05e007040140028407000c00c04041c080c0362140c81003540d2039220200c00c40c20303003d02640c840d40019002020006420660020000c40510385882d9180c180c46 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 404271690 1250 404270440 404270443
    0x30322050705060d0f0b01020d0c02010503220506010e06040c0e010c02030a0c140f100c03110a0c0914070e0307140a03020a06090317071110031d03091306080a061508 73
    0x181e190702204d59200c0f80c642c030280300d0a1007556a08502071002d4124218074041c05082c94180c0b4500904100000001502940c64511000880d10b080c070302c0760059001c03d080282c0e903540f00b0b0050880c1a040306011854038502481080c1426842e501c40f4060b1072440b20054032011000601030303030140500480e40b40040ca000420070043d11082481c610712031f4900f024043c44052014143d0300031a03500e03ca441c070444e0051001c0c010660700d03252501c0801c800c48265070a01700c1c0101c0013403000503604400704200c01c0b0784e0000c03428890380075540d02e01c40c0c0c2d60104c2150340c1580c0c0610f03980c25402001062192101516a94a070240050b080030001592a8040b92001d4520380c04480010f04180084c07040106400c040c40107042520002c90038035030b554850a00a950400c03655104100541e150a02e542c000d4201256a545203040652107500c440364490300d9501c2446a203120341940c61510000040c24031451091f45d400d113008041c00c100991311403000300049070449403001d43c08640014130b140d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 404272940 1250 404271690 404271697
    0x801021603020615150c2b030e1b060a091503020d0c0e01120b0103090f06050603071d010e04060902190806070201020a05042102030a110f041a041d0a0308010509010803032205070506 80
    0x420782280c4c01f00130100d4001030441d107030b0080c2100c1c2d64001c2c00402111488000d03040c502c1c0741c011501c060380c41e20890b00c1a1101301c11940505a0080c59109441d81a50103502810304903030030650070b0200d41c503d010700311a1010311281d46800704a41d40c050503800300740c3d40d0001d50a06818100012459190b482d020342c0110b13501c0c402c8441075280d07810007129040502807440180101a01400c6008031422144022007050203540c460507803a50004041c0402c07900484141500509640703450390050005074041c2040d80201002403240a0208640e184148201c45030700f1025503d1a0400b82072900e41440300c1d144e0348440104680075221100940e80501105218078820140d440d005031148003408000b46019400c98861860000d54909407642d148610803030f03203011900020a0302600b0b801e0f1003920503103441000180318284545007016000846541030b15800c07100e1080a81c2d84030f00e41c03596071000b11449007907215992020316660b80018030318801c0600c550141e0344000d8030750f004950242c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 404274190 1250 404272940 404272993
    0x7060f092103110417211602030309040617150717040f021032031501120e01020904050a05041e030324061106060f190801021603020615150c 62
    0x81109003000f4103070100400084014240000d11b601d80100c8007100c031a00948590740682641c24568800710366040c0102e030380a00004000f00441c68548a841141c0c520b84070324030615220740071001c05000c00301d2030507501c1182e142c4c0da561011500207189581e023940240040310300110954080340160740d140c8200c07165040356a1001c0100c0c0079040c01e6100c2403058070b0700c50343c000e05a80000140c142200d0490754040c05107210b840d031022003c0012a00f803519164075800842c039200e44513540d000103400030001c0300b204540c1403107992a0350407a001180e02c181c8005005241c8038a2921001e4172400b400c000d058002c1c207000403881c440c1d1381344024241090444410510762101d003808040c3e008441040c42e40f0842c2c00419862600f50301140b10071070300100641c030882407000b201051000038506100074042e840700964440c001107a03c4049585662070450260107400000381d040c900d615811010b060b0700408569050351045c0081d00140d020702000011401107130035008080c0c0305650800da910 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 404275440 1250 404274190 404274209
    0x90102030d091a13170a0e280605160b07050705030a02070501080a051501031d031c0e0d050304021903020301090c03060e011104180902090c07060f0921031104 70
    0xe203d141e10200440ca00201204034582c0c4005514020130b003d4551310404000f5070340343c6580e68050900541303500034402113142c0c1c00036440e4050f6140a29081d81100d00035000c05105802c01d0315560166118090001e00365880b240d00603103440860760b00304c28250001e01604100c0e1500381a80c9900b8215840440114003503409440c0402a81d680f0480c402c2d440352003e4400c12003410403010580e41e542c0030201d050f0406031100103c880420a41809254105007a003c80f940c2e241c00e1084159880003540080e124545081d5001c010b000e00418524501344441d5112403071555950b08105c654920282c2106104501c03a1000c00162401d1190841444c040c5001d0a46a0324604c0c1c500203907580120340320901d9040c20b20f181e07042d66079001541e003aa2142913141c04c080c0f4051041c00c1c018221044069440140d0f035041c060300005040040c09442d020b03020602508500700b105034182d54668200604c180c251140c00283c1000b011680311500000f40b43c045403441c580030300c400f419003103034003c0c407510b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 404276690 1250 404275440 404275463
    0x15120117060a050618060f0307031a100f09111207030212090313030b06040222030c06080c0f03090111180301150b070b280912020111090402090102030d09 68
    0x300008020386039005200100c00c1c402450000007203218980c0d0703402c02d10814040f41001c81c200f07075a10442048003020141c01ca4203519600d0074810524941103130000c1c528000080400c44400384201c2c54000c1d2028940c0c0c1c1540f0520341030b0214020a401c030b02d0000044010303c0b0709002e241d0032114080c01444156070158039940f4141a9101c00c1c800502800305552080000d48408000e1000328002c0740c2c2c0090101c0543c0d030f1140041000380c82080e50300062a0241c80440b000003524064000980b40a10140420640c554034243d5195038290350110300c64005004600c45074515034021a405805e00d0004188044241d200c040f0720381280c0d5000100b0826018510b5113814248a41140084548411400c1524000c00c0c1c804ca80b091140203000500d030080040c0500207050310100200c0b11822825003030b1a414810700008003450041142d0101045102000182c4140103c6020280d40c0e481070b1300d44541075003040000c0d4001008181980010700c41d0150806a5100b1442d441d8041d0407036901 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 404277940 1250 404276690 404276729
    0x17090a06060b121e06010509010c12080103030216081902030316030909361a0106080f18060721180210050a050d15240e01110c151201 59
    0xf40d801000b042e2954000c141c2d50082d006518802402e0303004402030031314aa441c8403840c012239014444100140c50400148030341e0f201180d105500764100d03800fa03800d507054205009003030700b0000b5207441f0b0703c001548038041300802c43e100748209500c000e20041c112843d2003a226000050b0011143c0c0550100d00d0391641003112030403074000d564100785603c4120b9851388004940310b08080c91106100c3c210303210b0301200002c0000001da0340c03e4080c00007990000b5583d4682000b0a070a504440300c030070594418001c1609400f45000200c9440c00c108050907280e651001304a40c012000001c542c03040700301c00c100740c10100032442103e24402d042c3d9140c203002c00590040c010442d10000a80b8100202000f03101035042e40002079442018004401007010580c0795819480e46007503403c05544100300302e20510403c4402c1e007030341410b11060707201c01045038415801500c00300400c0701684265000352480100d50301e000155990182c0001102ea0b080c036a24000c001c04a0744240c01540851015041201 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 404279190 1250 404277940 404277967
    0x70c12051603020c0406140d080a030b0a0e190506030d0c080d0606091a0901020703030806030c0a0e0601090807050a05010c0c08030a020703030206060a0f0306020a111b090609040317090a06060b 85
    0x4061f10040e83c501240e248002c1c08610700440f20031026201071008031740c03410510b01c650440b032003402006200001551310740807881ea0301c0c00107680440081c050802110a42501070168620446008000e09204502030074142c510340d1a011080726040400c02002e540b07a8114031410018140d10b684503200d140c1401103010302400030454106580e07a0500100c1c08a80c0e00240240070750740e061802140680391540801d2a12166050140c5c0c0302490303503c042801961000c0040c4a081d00b42d0703455115a80d550300c199102c0c14207000b00768004021030402d00640d4041d6611a5805101d4000c0390105ea983d038070f6103070560700407101c1c40e00140c20000c0f003003090560400c8015003101c41200c1d071820882c0b400501c0b0100d50424400140180e4010803480e041d40c0c02150b400c03403240c2040054a6440c1c0642000390406022150f5191041c072005000ca012810402540e91103541c2c1901e0320301c03208840c201c0070122244002c210b040c451040126440025a141c02400018451080c0c810b84501322007141c0b1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 404280440 1250 404279190 404279201
    0x60f1c140f0627030412060f0b0303191205130b10081011070b18190f030e12030c01020a0f1e050f04050d0503130e070c12051603020c04 60
    0xc104035445140c200041c80d101103485908140c25509a03c0450b80c201201c400f2000b104000c01c005000100380001d0765525081c00c58807203485804208804803654801c3d00490304c11208080c0c041e0300c1031280c2202540b01c0c0d48101518181801c222075151003040b00141540d4084501200e00e204042e030b00c00401000896160b00b0283d0712640c902c170301d03003421089981c03524452811014070383c803440446206083c420456840e5a040f00a0201d00d00d07015043d0a0b0080f00d0039040d07601d511404070b1450741d884242010121440d801140d0440d4071917651012a8010b990b2040e269100d184e003955846000c40420040c16440c005e8000542c8a03103007078101800500b4561404800c0c08540b64003805858000e40581031003400d9401c1681d218004501d4090032030040e84c2040350407882c50881c0d0024444c000000e02104000c00d1403191446440d501c4a00a056041d40d14001040c0344104150008002c1854013642d03d00501c6c00d54140b8106440913804400e04090603405a0440c0c01503801504150251 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 404281690 1250 404280440 404280473
    0x2121080c0301060c030e0d080309060103140c0108340e01091406030604050703110406030905010f0603080d02030405010f090b271e0703020a030b150114070b060f1c 72
    0x40c81e055615144001d080003021100003030801003801c003407001594402440c04030442d000610396480c1d2a21040c0c0c0c0356200400c0c0429240c0c5025952491083c0000150a468041040c0e5549155889a00a4283d02d9001e1811a03507035400c0c2c1c0794019418000b00380d1829200742585da6070141c00d02034100141c035655094210051103500f600074801940c81d031104a0f6006a0151000150760b55868006c03001001e800c8244110520000790019101e5410341001c07004600a000801000341c04202400c01c0718542c4c800101410000c1c06000c142c036002e0790265a01ca40500001300e100c0300700d01c207840c1c01c0f0380400c0011104411031130140511246a06441c0121b03220354078085441148210320b06036a0025016014075502c01d502011040840c2441010021a8080c1001c59510385a11340504500c07404c0701c144209034400c07151031519600c00c4075100d8a051394450098500149600c4440c140d54000f4501600100301340628019619a002c13402d03800c2124401d080d00034002450401c194032905902c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 404282940 1250 404281690 404281711
    0x91510170111030103031b0209010f0806010e091e0106090c0503400302150f0103050d0507020f0616201e09130c03050102040806060a1d01212108 64
    0x202102c003103210411203064036018284491405031a00001985010480009402000d00e0000292000d500c25840c8281c401d088181c0b8503980e00c9e4004102040402c07185100d556000b0071b020180c0c41c05404244043c035001d60004100c0680f01c009010a89404c0852500002d0001007001241704094122641820004615900b40701181e420440030400e410400242000d030302500008041c000c000017043c110321100001410704c1c0020f110011071070f0034402956280583d6008401481c41003048440c000e600400e01c400d9540c002c41800030302c0d000021100b80e80e001c505084400b14500700b1041018050840e118000e2100b1b0f00c017848650074440110000100b0780e0350942c80c603a83c802b00139a0344800c440e000000380c82c4581c14410411a140d40c0040d00f07035480000e02180c030300c4021580781d2250000765558118560b0b503015240b1548881302c65005a4045a00103001884000c40e0360240701c150794038411100344031030703d800052020030b96034240f4910390030320780300c1500750031062142c1e01008020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 404284190 1250 404282940 404282951
    0x306010206151801140a1a0f03070504051903032a15110c0c040506120318150408150a0203162109031d060c0c04050915101701 56
    0x100203540d5100c050302d0740d944071100c44850103040e2104071500310010503c0d11240f0703607940c0d034541e0000c1e00360b250151680100385000d008660183d40a44030460403200d030141501e801060a5404d4942d0400303403c6e4410060104000a00381d81c034041c0d000c8942801c03030b0409a01c0c1d4594030f80500366814808900204420f172008408240102e114403000d201c1d0000104c14400b09108504c01c0201100fa085100301d14020034102042d0f6400074402d03082001c255410003482d141e400070000c24542c110400c0844d030340304002c42c46441185040980700104007a155089640c040044d0a480d5007080d00010f0039a400000c091501070001c05115401c25840b039411865410007583c0603001c9402901000240b26502c2c0e02c0005150b1600e0088601d15031038501001003440c503150043c516400095004204a08580419100e10b082000c03100740030740810081c1760002550042c0405480028240c019901424000e18404118206c00b1407044010040d00c0da030740ca08005185a01d83c0508024441a030703d0034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 404285440 1250 404284190 404284201
    0x9170f0f011a0f0f0a03210e0904110a050901120308150a0b0a020a0f0c0302030c1203030106030911090405010e19150b061603021c03020702090c03090f03030c070201110303 76
    0x42e00003419668241d8011140d001c003d008504c0716141d2425007070304845c2c0d40c000041404003c60400268506054000404c10581c11003140c030302506d0a1080c0c1e0200b41c0c100454005071b107012045541401c040c000c0350b641581c85000542c0c1c24803d9004100a9003806111400c060744452142d922590703040504a510306c00002244d8820305070300458450b48000650140b146000f044104401c1c1c1d448041040d005180c1e00e000d0440c02468801240284180800e9503440e2918042d803020120809009505685c070781a01180503100c01101130300d5455401170b1b094095100e08003490b00c40c0740030700b0000c1610020084800d251800c01c2c1001442068251100e400003102c4c5961540c81001408000c50500c2d8428000703503241c4035201c002c0207840c0312000828101034011030300d2809210401079484401c20140800c0d4103034420030500070752081c0724000203425034003010051504441e078034003150004414200750601d1a44255400d181303c0c0808602c060441d0303403100300200140504e1000d582541400b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 404286690 1250 404285440 404285471
    0x6221b020a080f030714030112060608030306011706121c0f0c0f0305090627040b0f0d020603040303020c070e22031707050d110d200f0a09170f0f01 65
    0x83e03109000141d400000440e640030b2181007003514402104a480d07649581d0b60303105200080130380c04c0480b2803600707101c00022580c00201c2074920415060b155011410903442040503106001801250300045180c94691a458200901c000c1d40c00541459155107042d5034010301070707800e401c00400030000700707507150790000d00d1100c440b40f101c0c0e80c54140305803105051400140d15000e03140c0300305c100f91410800da2588904044101c2602c3c0c809480800c01002c1d48000e00442e96030074440680c001d011006000010f0030440700030366000340070b450018103021040c0b4805090407036560080c071540c0303400e01c20300c8651440c1940c580c54950000d0708008880206a9014000100c11f04c02420640080c0001490140c05002118000c02000604100c0c210f070070141c004441d0420414601e501e898a107804426120503c0c1192843c00001c0590f0704028250309100465440440204200a2030f0800000d011010000003091549600c0182030105800c4541520b086102501c06019a05044094180300503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 404287940 1250 404286690 404286697
    0x2e060801051903032705130c0f02071d060d061407020706170f0702071a0a021002070809060f07050102070807021008040c060e0d1505040302150103020303090906221b020a08 76
    0x1000b40d183e1043c17aa103a05c00101c80780550b801940c0249174030051071080b4030b0580c09200b040c801601c9041b000105410704a070750358100d01800c1c0d819401e005c82c040d107034030a2149242d80040c000303080200a500a41d1000103650101d1116503400e009002032040240d014442c0780302500d1149050b0fa80c10141b0702c6100086d08010708040151501c130000b09094501c203024040191082c0c15880b9045800025810b1980d0722000517980140503841450504081e64000c40303030030303d401500c1181405240720030401194406d140c17092124404000c8980020000c1c00a000c00c280114a130a07291302036401405941040159410208450402040005141500c0000c00d8030303030618001c1000b150f410301040c4c071125100d0000e0000144a4403c82e1085855040701d44241c1c841e84c00d903020309407031700c90703102c1180320a0000070351640040c0300713084035800e0043c050790340568024051401c1e16804d00c401400e1070420b030315104240d511125081481040c140c2d00c01c980490610041c848042c19486004c2c2500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 404289190 1250 404287940 404287967
    0x18180c09040b04021e030601090b070818030712060b040c03140106080603101b0e01090b0301090b15070606061e02030d02030915090a02090c0307082e06080105190303 73
    0x242c0d6090052039988403941601c080d10040044554400c814140340b0b16690400c0790014000741c03091a000c141c140260041e02d080542c000c02007420812805032011542231300d41900f40e003605c5042d100140150403110804900c9001c0c00c0002550b18a001c2404142c5401d40343e80028907091a1101d10842c945e0900c4a04596403458000b403c0c5d101c91000908100241c240d00e807081d41882100c9126031f16100e00c0c1d03080c0c480292500310b0091070500040d21190411320881d140d19909000400102056030480e03402c68030018520084022004091561600450f4040c3e941540c0d03041e0030300c0341941109818180e0404841840e542103ca910000d5591140721450310f0899004004290301000800c050440403a055540b0102e51900380700f225540c03411201d00b6031164403a80c0110305100851400c890041603035654038401aa03d46a540e030301e9144c14106450840307140901c9103404450380740303d40068042a070740c0100035403400f810031804081008440c100300010310380030000280c00410100104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 404290440 1250 404289190 404289199
    0xa0305040c09090c05030c04090f060b030709060b0c0706030b03030403080f13080d171e040c0b030115020c03190311030c060109050402120a05060118020f18180c09 72
    0x1980d5030700d840c24811100d68040081c440c18030700701c0400c00c4001002102030354800d070201e4120086400400040d920381a50280aa402210b103050100f0441e400040503810098112110b02c0d0f82d2b001c0d0a01100c8640d0302c544c885c14000319280e0003044051020900914141c6814403484803110002500c911a500c001050b040c0001001040105501c2c15601c05a00521602041d5940c46544075101c55418501e10001043c2400c02041d64400d135295601642d45001f888404000481c0e048051003805401500c4981003c200040c00d0340d400300095000e407000c881d0070294516040001ba1a0410124190b0701c241c20041021401d441400d03440850141c043c0341c4000310080010240342180b0480f021016240109000841d094155400c01402180b00b5244045110b030740080f0540c4a40300d20078000c04541004004119055000c400401c01c0352600034010305d0301601c04540f4001c0d62016a080303600c0d08040e5030030461864039450b600c82c0f8003c2c130010340c0c40500d046800d541583c03103100c5106214 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 404291690 1250 404290440 404290451
    0xe07120603050d020706182102041416020c010311090d0c0e070503060a09091109220507091407020d0c03030f020d090c080a030e040902030a2411030c0a03 68
    0xa4819400030002942c101d41590316040021100030749507040b07030044c034001c00c681070100c1e45010b1446c042c80089a14905051042010380000a07810003000c46081e41c1c03280d16100e1381c00058016400e443d01405012840d0300311000c151501074100800080040d05151074121140d440d00303100e00c21a44131031310864110100900c01c1c64040207440080c3c002c002c245401d8400c1001c07070341c1c010004500410085035010126542d0b580c402e01030b60030b075001c001c11440315000403108074102a01d400e9007000c90402010034900c0515000e1800c40c0b1501000d4403242d001000030028482d40b0f00c58410007070b040461038401c51400c60f00282d91280900303c070703100b048203445103601414402d6001001b0107003032120030740d41e03030720080c2d1202c010b44012201a00d5000f801d61000950840003d80071012a5041c0c0301d418804180000300402088841410398160261038000340001c2c040b031203503080c3d041c1c8a0351008490242d111541003100c60300d401c0082c00305e804009007d800401d060540300291002e00d4003141 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 404292940 1250 404291690 404291717
    0x90312040f021801080303091603080a0e0105090310091a0f0c0327030c0c121b030102090409030c0b0106170f0712050a0617070b12100e07270e07 64
    0x418070300c2c0305502c80c03c0340d00000100b00c508020006500400c4040f0403520070344000300d8454002c031403a12006249030410030080c1d0003640112807040e0340080c141412070503c400000481c0c141241000e510030115540d143da2030400069400f0140c0910000e01c0c0f1414070319000c038003030403600c4001d01ba44444407408000901d03c099413420900c0c0e40c04d403021640100c2e0311452101903494000803804400c5024030720440000c0e05200b00c443d40300c84280001041014150b62040202d44004c01d20141c1554082100c00c80c1da403500d004103403a081c440c3d6035421044c00071742814900d00d07606820072030411190140c401c1004121b0202d954104a03100d40208154550490030384000c10180c10041c1c0190600b010840a55480da00c40c0003181d48510700616031040721002191280024000c410701030000f07010f80d4800120031410558032a086200042000303072244124000c456049480d5400142c8151155051b08000000843e40c1880d030110502d2150424445841c803075002890002001140030107482c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 404294190 1250 404292940 404292949
    0xb07020d03110102071a070824120c06070305040f0819031407020406170106080f061b040f0f1d070f0f020111040b0d0e0a030509270f010608090312040f02 68
    0x1c41c0254090f03621101c0091503040c8410071b80086078000e021400e003800107000000c5030b41a2042d50f00b85d266958460f2083c0d0810017201031130f4401021030a2045182820b416110b03c03008041180c0661038071038642d464625108059509a0451401c40d04802c403100e43c141c114424000803194181000400e01001c041124058003503200d010b0350160604c0b0000416032182009540600c8808000388846520343d610155220000480f5082e1a07000b0400a000d0200115106c5641f44003000c06a240c6a41c82c84031228124542d04a440031080d01d80e820040c03064040b60101441000302002002c902c1c00c054090000b820742c0901000340100b0103440351900b40f0039070040301d40c6410380e801c0756210703600c076510880359820034460f0b01c030960300d012120b00c132258000580b201410351640e00c0c40d10f81401041840303002c0e0b80b1652503d0120001c811080e0600310f48114661050140d20540760441d13241050041145c04050010318050b0000c0003030b0b6044441140485600a812014650980c140707440400c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 404295440 1250 404294190 404294197
    0x6040902040f02181003231b0d020405031b030c120c03010603061b030528020f0301080a11010525050a050604030c05011a010c0308090a02040e07030c0b07020d03110102 74
    0x24511240f0000d848102c02d49010000c1d044104143c8405201c00307080c00e0309074110380c0100440014080d030100f02c5400c40400f100e849611040c3d2600307503e01207004032848429a00711074401350041e900071809110a0604100c290202c58114160710034619001010030748920348100c0706405120b07d0313001000d051804100380f07010038001800030006031382c0e24285800144480a50180c21034440400401280d2080c000c507405000101d8440c00138007041c2048520b4481c1c002c080c6002c0a40074000d200c00d0a030407102460091402401410300c250243c0341541c3c4410000603200d050150621a07644102e084021682849207460350504450440341000c074600440100e001300315208a000b08410035512015030802c5a125038002c0c003e0b24406e1680c242080c1041043c0c5000903400500350340441c2c880d03d0344640044902040d0307002c04007181c000c1415910f90600c03840c0207074040207003081000680c841041c014000020042c0c203000c016400118045170b9000e015042083c541225030fa90a001e5045 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 404296690 1250 404295440 404295461
    0x41e0f1409010207020406080615100e0a0609030201020f01110306040906020d0926030c0a0c1103060408190507120809032203020406120b0a0c02030705240117060604090204 76
    0x464040340340c54510719020b503000381c50403401242844000961400005039003401040441c00c96030f0009903020502041c2448101e90700304100520b03413a030242e034032000900c9001c0c01480d614401c0c643d081d40006460720013002000d0324541e00d881103100c0110b00c0d0406880d003260048601140d08156070501c40e01a01039607410703054840c07a00600d4800c12013030203610b644120a022181a00c21084139044015000898404a8030385c1e00704007400e2401c0c458418802080d108505280300540c0a80109103404422901107884560000303915400341c0020720030310145103003850524030f08240c5d03545403c0590126440720003801540300100380440d4040c800e0311130888030010300000002c000500c060403051184000e03409280340980c04585803070344081c40c17162640c11038035803051a181c1911010041560340c0041c421030000b440080300044081c0120b2108500c81e01020b50400084e01030034a1703440041c1d00285040c085180c1040d800100810295400142114005440d0040f40040f8019000c000a1b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 404297940 1250 404296690 404296721
    0x2070501020c010f0608030a080a0207060608010227040c0207030605041a07120b0a12120207051003140105090f0103030315050a0312020d3e03071a06041e0f 69
    0x81080b01d980c015400321143c200088002d0100a6030f40e40c61948a10801d8108070000e1150710024206403056002484401e01c40c0a0010381c450740c07901480c0c01c9070850310120310708000e201c95490010301d00a01c40030816034211000c10240c41e25580107907880800c0c1c40002c01302a2140c0004092180101c0059440b0080707540701c031040c1ca84850700070010318a44807601072051a002120a21b41060030001d02520102c0748030404021954450030b040021152028045104103903003c139598866400d00985500242c4000c502d400743c840003c14a039505810250203070741c00000300580c4907100310301c07941182d03010700380084c03141d803144981c1030320702100d030001c0e90001c101c4a40003080000d90000345aa0700059402d9810400641404a80d448180699589078500c150040080c059108400311085c139072603540319114800001a8a0841e00100d1060303c1c3e260f10346040d641d6081e00c14074241da1004084a00300304100254140c0070041803982e4180000390303a140c000e11240d034016032256105004a49 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 404299190 1250 404297940 404297947
    0x6012304141215040c060e15180a0f09140903070f06060e19050f010503070510020c12011d030c031603170907061d09070516080708040608130221010207050102 70
    0xa030f00300c0d40b00100359001c4401700441200016814803e44650b4421a002005040d03244000380f141c14540d0004030035a1904ca07440c2146810641d1009481e400610203440d808803490f24080880c01185c40c0c1e501003103100102e40701040b04040c2c022003100c0019074885601d2078a03946074101407008140d00e070012103c40c28150141f05814501c801010044401454240f01680c0c0381d40d9400b004000a01c07503543c1544c40441d041c4481d00d050310054191100c544101e40001c4100000194068151104042d9507590707420110b82c2611110604540405460020341c030b4102000e108660703c1c81941392204d80b40c010280c0c02e031b041510492120b141080051310390303e054104141507648580852103030601198100c01ea035001000860000b50384000c00400800c003940e42e140058445a00004040c1409550315034000d00240c050070141c01aa4010f100e00c1e0746031401c009000e03004a0707000e8582040105081c15580050340d40c0f000d020001040d8030070303c001744182c01881d5806130103004402070aa50011 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 404300440 1250 404299190 404299213
    0x309100501120b09010911130b0402130503010608031305040b01030e060f100f031a090c1c120c110d081c05040b0f0405062406070b060123041412 64
    0x60b285803400714040e400360b200d55100c44a030b4508030b40c505000207042080d00701c00f42c0410700d08050b083c0c03800c0300c4038880428000038010004e001c86c0c0c07050349994022100300000b4080e41c10248540c0c070142c21010021450030310048405001001184195403165482c0d0b400841e00e64070a400000d03151400e00200e0f01581051164280c805c98101d441d4504425030300000503692405000c0344041701c0d044010041e90115140b44c00142950007400c5041c0c5200e0009004549d13140c030030071507444c1000e448100d03131600428580b01c24500e4020144500f000149000d07500400c0c1c4c4003403403200d5004d040f40c0c8112048210315210813280a00403031300c01088007a9201808442d180d4204038842c0f482a89103040958540080c0e03900c8800513079001d0482e80c02030700007602d92007203951943c031458108540c0d9580f0300740801c00682035620280c0111000030b4142d051180c03035600700c5c01d01008181412041d20f0601c200100d41c40240c0602c0c801d04504c018100b482144580301c401c0b00180280d50181900d8803e0030300d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 404301690 1250 404300440 404300459
    0x908041221020105011802210408030709090207020604171204090608011803051e12250c05060a0b010509090c19050406020706080a020c060109050a06080604170309100501 75
    0x86603805071400d008400381c01015031061241314181c0c1e641c1d20f4001c2c0024051103940c4001d400c099002c5001070807108003030b012440051205e42c4902e00c98070304191380707141a080042c91407520b84e0101440302c1c018081c800040e920031081c0c40550381710440ca95000e1451011444ca4210190300c004001d0340002000301e4203500d20b420002c10390345580004d019a071040c000e0380820640d2142d0140020b0000d0200001d8002280e80580700d01d2040042c0c21b040610014044035603020036550050b1f1000400c0003281e0700c0c600003690400e410aa41801686110701c0c0e111161030300402024000011350320361100e001a8052015140a1207000d080f03004240341005419403640d02040c8a202d0a0301e840c4845560a4420741c2154280c0d0f0b03459010f413084514082c010b035404180905482d602c41c1c0c00b805a13050300d0004202540c0203101c205070104850404a907013008030350030760300440341c0da030000c00030000403500640007117400d40d00c0585400c2c0c0e00d41c3da01c41c140e400e01c03c10125000761070b070403c00002912181d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 404302940 1250 404301690 404301713
    0x504030b0a0b10320301090b0607060e0304031e0c030303020919090527071412030a0201140106090b040e040611030103110f060301080c0f040b121606020c090a09080412 74
    0x503004144c1380300c9401200880c022004040301410032101000140500b08164000e80c00945010b0240382c1010700c26500e600a6450006042100e0b80c400300b01002030184141020b0343e44518101444481781c0c054070b48240359000b5004c05402d041c0c00094061803520f840782c0704080120001c6070000d609894400c40c5011b0041610f0300049030820086c5070104030b0343d4042c412610000c500003000d88030324066103906401031000031641d20580d0892080890360b002e10003001c090600340c2c00020580c01c11084a008600b06802880400500140c10301045807000b0842e000ea403203404241840d40d50791301d4484040c1904001862400602000010070880c21010540508038100c583c5c0000b902c0f082c023400b074540000d201b00052903108201205540c14405004400c0100c0508041242c84071070000c100c100b1100354881006512000c400c40440540b00601e602511052014006280055000581c00c41019000e141c1082d80c0b10000404c01c03070740800722801403042405a2200f000c0740d0810a0540b103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 404304190 1250 404302940 404302967
    0xb060a05060703030f050f07020d0804050111030c0306090109021603200d02030406110c0f09060f0418020f0d020d02060c0313060504030210030501080d1b05100e1009030504030b0a0b10 81
    0x181846c01282c0b20303d0b41c10031a280701c0c49043e802014074400213803048580c1800074009554656803003418a10342100ca42c0150b124000310440703a91790b420958140644031005a10040d40c6602c14440706202030304501900440b607030076250001244c942c030454895080245511030305640718900000746850380110240040b1407ca8030740300a0f0500c05c885040d241e81c4146403003507010980030411000b6183c5003104640103107000e030084148420040200301200c1030320102c04402145201440c2c00c51501d80c00c0f40030b0743d203000e90714410082d10640c0421019426034034005d00c00c010110f4505007901003001178074843e0344614100112299a800e001d01541c0c443d000590007890034400940d14030f8080e0140e64121041d800060143d0748a485084544461040303e03441200700002d03071100070400410290139004494000000c210140c0f00b5582d00c2d1a10403032000e81c4043c104030705e40340840e411038103440403260412000490341e926000c660001b045143c0c0c2007940b080c3d103180d070780c081d071607000703070a908a030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 404305440 1250 404304190 404304221
    0x3010f0b01141c02180a0f0801200a030c0c060612020a0b120117011d150603070e01060f0e1011010e0115120503091e0a0506090303070b060a0506070303 67
    0x402e80380c64400c124482c40000d031003541401441c00b08207803040d90013030640c0c0200540c0c0e8041604901c00184030070400e540218902040c04d00b0911000c1020306c80d04903611508070040c001141c4c1610080710034003030b040c2c104040c10741d281628000103018180c0200740b564810b00c2088001d4607104503220141c81407105a0007180303413100118442c00d095084596120b00758460b410260710707081c0180c20040c1c00c213178621415500e0325010320100d15400c0880d550003050802901c0c0384080c00311407a0010b0340c02003040340b05c0d078815041000010603504800303043d2002d85c07810320a03c0c5002131040e034405034640c0c402504844202c1c0d070070010503481a015680c100004000b40040071000c241503003a90040e648898070038440030010007241c8440d103400106180700d1010740341407140c00c4000880700c611980c80904150300010b1520900e140c02040e12018144c121070140c1000502008a80e69000c1d07001c00414541c0c2030b00c0440d04030303504c1044a50040100514080d95000079150041c042d0610321300d0034610 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 404306690 1250 404305440 404305457
    0x30302060606030906040b0c04090903091502010612060c090b0a020c090f010602070e18030a02070807050103050f1f0306022101080d08060621010b0a0e0d0305042303010f0b01 77
    0x30314200e01104d00440040c0002d10181e100d986490348014400740c800240004201320000d0104040c0c01407001e0306010b900c1d2101500d1802055030804603013003140404592400c1d8080c40040e003a81c6e0040c54042c1c20800000341519030320b0f019035800c015070f0005005000082411100c4640c006402940d9001c1585e1240395500c901c078848600380000c0c00b0395405a0041c50f0140405620840f46540c4050000c0c090660010961031f5141141d010106000068204c08020301c41c0c03d4082004000800d000c0c80d08005074035000c8555625240f0250603010000c45550f0035160b44042c64920001554204c20115540c1c012036200064400302e0794094070340300c521200005001400401d03103041966258407034140c140d40754030402c0380039070103c00f880b048209504034111101c112094028060112400080c2c0d4406103200d0107051510341d50b0700b161040e0002d0b1401d070006503101e010703602101c000011610b0307420741d040494015071342c81e0390b12a5010341c649560310340a05516040010001d2003030322418003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 404307940 1250 404306690 404306701
    0x170c0304090b010f11030f07050c09010806040308010b070c05040b030307020a0f0617041211031303030f11030a0c02010509030102160b0a1401140603180d120b1e09101e03030206 78
    0x34246078040c510543d1b0341061100c0c0701d0300c04400e07005115851081c8151740c2244102c81c00512a5442a00b2258603507010004110406030454512405040e0506155051150f030740e80d03520889040340141360240342c407aa09a203243d203040041d540b1195000b403070301104c00d80791000809903981c24803941000820300e40c2030004848460040f5030041d07400007208065030300c25002c2030300d0010200b50359140910040100307007600c064128003031010358400c1d0744000c101b07100400c004040c8844031150f40e41a810030002421490740004503c51240c0c0e0a00b412501c0d10b2480b00040d0090190b0b0052050424443c4040c9040062940c1c0f060f119a0001c10100051128012002010341d000d0281d00e81c814110080341a0304d00d091000340d41d01001802115480c004048040b0303080100c48a500300c04146000100e45484065000c0d03d031160106885c03600040510394141c560030440c54040700d01404040c40400c50f5001401204406072091407440000341c1c40500c0032061400d0b00307110580c01400340c0004510b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 404309190 1250 404307940 404307947
    0x1706130b072d11192609030a0803161706101206080c100e09130203071a030f060301050c0d020715021b0706021b040b0301091e0b090a02030a170c0304090b010f 70
    0x1030b00a500b220751200502200a01d480740403146201da507241c40014002e070740441d0790230062400d40c42e00c110301450301d82c1403a10044030400c001d03006002c144030361395014110340c03d6903282241d84650100c071280e90091f49104107581c044810040700c1030b60b50414901080c40480021600c0030124152035048090b40c0800c4200c0b00c549804140540c4039803464042030071510260032048145000a0a8815141d541ca03120a501080034500c00351948000c803c00c001e0614421419a00c00b0054000380820310740403841c01024400d002100d642290701290a100380142c10400b005a1041d440c421940c1d10040c906c0f00d81241c00d1f4000340010f52248141c085400e41c400318824140340c075404142c400318942481004050144401b0003a0903643c1c4a058402180030030740b01550014881ca1115a591503504240c038100c2e05c0202140f420364820050080182c50008043d40125000860300d08242e803508c4040c0d800740700310410f03a0294030000c41c4c049608001a803118011440989800c81040c0100fa0180d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 404310440 1250 404309190 404309233
    0x1b0f09051e150d0303050103031b080a031e06030c0f14060f0f0d110316020a0b070305040309030b01060305010f091b140909011706130b072d11 63
    0x30208980c080401e25034074021050181d41101c0e10055600c41d0341c041c0400b250741c3c0d0003e400c080d00001e44800040090542000303e00b00c2000006003d01c03c0300e505925900814896540620205035882d00c60f401404000b012595201c8000b80e0180049039a83c10304004034111401252108a280b640001301502d1720b4504071020880900214103140d466086c840c201c3d00701407041c0351111410050040042018461900c00e18421320a058881c00c5c002c90410f040501c0d4000c0d1815075003c4405031010903880c000e0b0707544c0a14145004203031640c0e03d190480320780132135a10080514202d0000030801c07941582099043e0f40590460b540069034691040e01580c000803201c0341c1031040d24213542c0c034581c860381d1411321000c0481c0c42180b07802481804120000c000f60700000007840c6400c408407200809009040c0c211003c440410701d101d2450729018030107400946400b05001011400c0c4080d041c0f800c540c0c2400f5642010a01c040c06c6550034080e05145405440040c24010030007070b6940700c0c1981045 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 404311690 1250 404310440 404310451
    0x50c0303041202010c170a2c0904060f110406020c030c012d0201061a0c010c02010204061e02100509060411030d0c080d0213080312130b0705090d1b0f0905 68
    0x100b00301403050f400548200581c204140c5213500b8015880c150010038070018400503100b5a580520181e020200003010b043d0300c1000c02d41c13941880491905551503000c4181c000d42c110300000740401481c101a030050440090380401e081d0b02060002d0010b4020494000380394065040e00d54030410000115a03d2000d126402100d02d81d1000e002959810299104240c40b11400000340003034413680200c081001c1d106840780c6541c00050110030080081c014403d003074101d400254101030600d070015002e182c0d10501c5885440c200d030884042d03e0b2080020502c1c08400e41c3c0100150306004805988412013140e0958031200035425801450500140c80c4004148a64032034000f41404e6481d0400e0340d000c001c807100e4442d02070100303006443c00200e500c00244001002140e40c0c606203810801d910500415400032003008101c010041040f0900d4a503200c101480d00c155580400c000044500c10481030150000344800c803002c80808688010754143c88580b000c03000a0340c0c1e1200800260344084a8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 404312940 1250 404311690 404311709
    0x123c03121005060403080a0309140a051b01080c0a0302040e07270501052d0a05030709080309010507021215090115050405150d0201020f0102030a06090e031809100509040f050c030304 80
    0x41005ca2501070252420084a250114420002ba00d5134840d801c1d08084284050700b10b02a8001003080401600d070111900e49000722203e03800a0010f0140c8100034581074402c01d0005451290314880e0381110050000c5148450180c10184c1c070003003d001d10b510b4050046026121002203044801d240030045444c141d6440b4500f005000c688030305d40c0c40b4880e0a0210020b0040303140d041100301009401c043e0301c3d941d5525185c0c682043c0003050f18200341e00165807a0002c110b209202d992140031140f1850701520f541c0300490701c0c50a440d290140703078062213020780b2400007481589441900b110304124031000600100399210000c0000300c40f000d40e00765009081c60b045a07241030400d802449403040c0140161000107011250060a99100b12070100c0c00940c2e81d20140b03c0c02a20b40300b0980814001c4005505241c0d0b851002c224400b4005a818491140200040c0c80044e103180401e014100c090521092030074189011501012003290480755401034030114401d41c2400400d4808850381d510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 404314190 1250 404312940 404312947
    0x40203130201050c01020f04030b040318060c060207030905120c01030b01020309011b080f03040f0303180203061f0b0403080c060a0b0d0f060b041a0f123c0312100506 73
    0x1401503d5a61140d083d0784843e54091042900304018200948020350007003004400740e1134185002020951b159248400e480c0c511101400940ea118950340388007603100500607541c80860405442d02400c0ea80800d41c05046107038601c0f080ea0707010030a6000c05a080c2c0301845820411001641c8a028030000d090000c1c004014011a00406034a112a01030107244801c3c0303040c1c5c401074500c1c5154400c403030603114841d140a10b40101941032041a51403152120700c0a11000180c0c0000e880f03c0c4090304c0302e44003801100d540717180200040070702c00040017100451559a9900d182108142d08410b5908001c1d005040000780031081501985640b900000d09080d012035080da1420701128003410280e4000e030740c1e00c0704410b080d111449003460504106003002444070b080010800c00000b411701081c00745010742000d0400384400131308074940c0c80c91910072140940d900c4282d84d038140425940b0074240b1040d01414613012a000c0000c102000d4150080ca10381d584041111403014803074800c4980203d07080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 404315440 1250 404314190 404314193
    0xa08030d050a05010b2709071707020624030106050307060c0b060301020c031b0102070804030c08010b01031103060f0d080f0a14130b03040212070303080106022401170a080d050106030b04020313 85
    0x15910040055581c51b48220403000f040810044181107480c03c0100360103900a00750100d08440c455485400e40c0300504441c50501528180c20305910440343c10884090741a5035969020341001c4040c0001500300c94255990f1803005002030030080c1c1c10703182c41d9841030204419040600846103200d8040b0015860301414651039142168580a14129550300740036a00000700c40303600810085002e04081803802d42440c00150031a204215501c0c18185010441c0107141080c0080e07960240c02140d1901c2035003007032004211321407001031008050380c0001513401494081507018041c4808595920517281c0c600d0340f4500f405c0c0c03162030002c1030740c194000303420410480301d10010350340030303101400020a072900e01042502d02480c44c0c00c110042140c4030014400f0315410480c0b8140c02c000c0314180700c0c084114030303003036040c5d40e06c103000e107841d0104540d400c0c180c140e00402c000300601e5400140c480d500c4810100c0440204001c2c06140d00107414442c40740ca243c5024004e8038050100d40803c0c2c2410501d9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 404316546 1106 404315440 404315467
    0x120905010f050a0c0c02220e0d0e0303040b0d05060a090c0908012324030a121b030813031b0f020a0902030103170f07020a08030d050a05010b 62
    0x1c1507040005145e001c810034190a4040d41e01c04c443c6082c11000c01403c04901800c1f680c0d15041c860f001c40007800008066080f11008c2c0c2d500030114007440d0400d5168800c51082a01685c411b010070803a40741c0540c01940c00c41070040080120300c0e5200540d0082e0380e030040485005c1219502c0420025100380101c041c1300c0c18190b02540030303492400f514420b440303025100040e100300da8a164000c40c0e00b29900001c0e91781d8000c00700c411280341440c0008500204803510b8001032983c2c00d1075160980d00805180400364075403100040307030340c8200a4180c1d142c3c0504041d81000014102d0b03688175402c0a11200398180158520700c108445401400941c503250b50148401c203104100401c04540c2d004405110a05140000b40c1ea80e0071846103040c0f503024000d4060340c0300c950f0503400104148004002d0401ca81060030074005a5201c0030031404443d0248282d00700e200701001070000740030781c = true := by decide +kernel

theorem cover : BRFrame.Cov 404136690 404316546 := by
  have h0 := BRFrame.cov_init 404136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 404136690 ≤ n) (h2 : n < 404316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
