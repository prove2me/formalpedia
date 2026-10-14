-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2909
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:06:23.553245+00:00
-- url     : https://prove2.me/submissions/3f0bb610-32ac-4721-9656-81adffa45119

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 523021582 ≤ n < 523201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 523022832 1250 523021582 523021591
    0x3050c15090c0f0420031504050406020918070504030f060b13150803070305030f0a09050a03020a02011b0b0f1503010c08011d010b120408090d1b08031801050717030c030a05 76
    0x83c0e0a0003417120041c1c03054000080c9072522032900603120b0b038800780b8400c9040c6a98003031a800600e060180b20621415030010180c1e4101500d5545104006190306510342d00b003124103000044041c0400e100080107803a540c4a400e000d00301c0425080e20364000503400d4055201d003020000c0d59841c10f840704110515099005207902c0010b1400c010f0540c6000e4454403005001c0f0020344103840004008444552180648540180483e145a0540e00e0040d683e414121810b90215101d00084010f950301803260040103a03120301d00d2286501c032102e050080c032001500c0300c514480504048803036610244034622001d8640c2d65040650352402090441c1c0310305c18419018810b401d0030051103041201340c11240c030a0320491802e841c603a11401d1015041c05215180c60303004a05410740018404605580070301c1d200419980c01e0107640c0c5401043e541d2003011203401200300c031140482ca06600400142c65114045d40da21985041ca44240400543c001c445440c42c0386008014004260494480c8903401f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 523024082 1250 523022832 523022839
    0x304021801060212070f0f0804030506060405130809040e0d05070b060d03020c0616170702030d020a0c0519030605010e1009110f0a0318140d170403050c15090c0f 71
    0x55505149009494203101c07070703c44d18840304c00110002004009000d034100c4d16040340e08100118400e03c0c0c0000280c0c8a88829a658400c500202e00c251500c2d00c40c860090340d00350605041404907076240b40081d00113030745003940181d441c040070510f89428454400705481c20b91368980d4482107460956050400a0807150207403d610a5680c0000d400280189a10b08210358058032503020741d007203807040c03000e8090040203c00d044003070f24900d81424000e4401c03c6d04c210140c6400424007a0100e0340c0714000d81c8041d0100300080010810b9061585106461040d44a842030701162651200d109960302a8050b501181001e02007000e580084045c804c0605202402400004159494020a0f01591100c00c10003040080d0541c0024000c1e404140000c0302100c1c0f00d0221010382c201030544666203800300081d4040e0a29502c10140700303146102070540180e84004890f00d554808560541008490132100c1c0305001b0000d0303526008850b131a1165010300004c01e40c0b56000002d018082200d184131501 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 523025332 1250 523024082 523024129
    0x1030c090b09221b03050c030f01140102030c0307050a020a05270a0b0415060906110a0f02210c010e180a05040c0504020403061d070f06030207060209090c030402 71
    0x300d0340300404550040030700302c9081c00481e41d030740c0030110000101c404220505142607642003064000c130712000d15030b00d910f882c10041a914603204000a20080360300381c5240c2d0150380140300703084102d1210044150184112400c0c0000480c0c0b0300d25642c131945c1e00f50340700d50000b0800021460710841010140c01d050b51070501e004980c3d058040034005000360310b0b080c55169400118040300130741c887c50240e80300500501000d162941d083c01151064020040013904400d00410068066a01c1d20780e10308101c4000c010b00401c41d1628200c0301c404d040d08983c040b103d030402d44c54100381d07821131f19003041c89003001c0d0070a403040d9000908466500342842d0f000307040d401c4410b205060020301c0c0a60086261001082a50716842e1828610741070b82c005903402131022a02006100b0a035020718001100c41c041c080906140c80301003540c8800c4c2d40328000781c11410f54414080c60380f00b80c0180c502144106005820494010006141d42d07000302d501d285100000300400003549030030052895160200c003520311 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 523026582 1250 523025332 523025339
    0x6130f11041502120a0309030e0a03062a0e04050408090901180c260402030703050303070314090a0203061303090504020301060e0f01030e0606010f090305030f0403120206060d1e0501050f0601030c09 87
    0x28a4001c0241400030306d5981e26084041c18020801204e099600400d20030700d90b510b07850100010302d074901285250620044810360b5241c0448510242c1c0710f02d5860341300381d803203070301c01004044d10340100308540c0c1110038001595180c403201606406440c0c100c2c1c00c03a0b40300080a8a02c03044900d50b200c81410010300030060300f080d405944010f510701000c07250b51241940c4a0001c00d2508401d03a00c000c00b58840042049202541035021110304482529100f0380d0b03031540d00860766101700d00f01000c0d6158100314003003140f0b40c483c070002d5500b0740e00c00e00384024000d0303580c40040d0403a04243e01c40c1d80821900303845202c07a4901401201d9038040300b420100010080b02c80328035035a00c00200914140b042d4109090415402041c6100046034030408590703071460320315103494140d049031004803860404076840010b403500110b041d038440e21003d442c0c802031041c961510585007400407c1c0c0300d00c030052516520b0200d0828010300b880754101c08000700040c100b1a00040840380040203d03820000040c0c402e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 523027832 1250 523026582 523026613
    0xc03110a0f12031805070f06050c06070f120c02150109140103030509010203090d050f0c01020a030210020325172d0405031207090305071502030306130f11041502 71
    0x1ea565034100840b4058848001c50540083c9403c43c44805940f158000300410070078000350f1002681c91110b2010503140d0382d8102980c05000f000d13010701c000d800c0b40f000076003c0351084100304c0c000029440c05806820311a50003004030340a030306104006800010a10301c4c1c0840500256004001040080180d40d03501c501c220140e240c103020040c03c100700029401103907803003082030ba000b400c1d005103011031400852070300640d035008162103046076000f581c58035903143d0b00200e0b22004a50f05a00134246600e0b014401c8002948000d02103903179201b49403091092801d203941d0002610190340c49041240301c0540314a0482c001c0100009001551180412030303d02421201085001c3c0342c020781056512140381c140d0460050a080e2024801d0020402010540c0300a0784130480303010340c050b41c0750301e620348800c020b020002040200c00340c0d0080000c201c2c3d900b04900c10101e1102904400520b0074078000900381030340c007802e0100506a00101d010700048441d0108042802c40c180002c0c0040783c005581d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 523029082 1250 523027832 523027853
    0xf010c0212030d0609050a0f2715020c0331031b03050307150e1501050f1f0306050307051f1209080409090506090d02191e030c03110a 59
    0xd0103408000c207884800002002036070b07003044142d401030000310b07181c0761694001c04003160301501c1c030350030202d031390302c0500e4184a1442d40240419041d8000c02020001081e0762035400b42c00c0310602c026006200c2c5480781071018004034024107010395036584461070700100359680320000c0c1040d40360504e4005050550550342c41c04070380d405440010400b600c42d0b0b03d595030140f00c1d400035050780400107045040180102c08140c0b0004600010002140c4102c05269624109481305044084d040f005110350314010102031580200280b00505980d8000d20000c0c12042c00c00702100429240c0e1002e214614041c800f041c00342500f600d81104001c49103101e890a01005812001801209007a4486005140e040100b800d0b811a96580d0355035a0f86401c0001014005410780350f500074140800d10302d1002041590040c0e80650040c001d41001041c0100d448411103806c54010780030102101c04103c0c050085040705000e52211108202a03050203019014102081d511319049081a1f80004907d07914 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 523030332 1250 523029082 523029107
    0xb01090515031f110a050702030613200303130603051e0c030a0509070e0103030f200c0f0a09110310060810030602130513050a0f020a0e100c0b090a050c0f01 69
    0x2a40c19040d0a1881c40f000140042d00c9400005007000502c4074100745c1000003440c070760f8429001c0750380e0b6a41d05000751402500c0c6010081c80c0006c0c61954880b4680590b1000d500408010140c0b0700d400f41810b1a10703a26509580104046a20b900c02c000c01c0048480401041408103140c11140d40b0305041241100d20005020b4584269984081f5010b01003c00217480038003074030f84144019503107a007009000090141c51883c00111003889212000582000041052013548010a0700c0c4041800f0007030184c2d031100040c0c0d0490001c07400003601000d00d014070341d122100c2d1441c09549042c44100c10b403000900390403c00034410700344140701c00740b144405110300300c2e50044401a100c0e5014074207250711310b02560185912110b100718102300c412a5074003203070049021000821244e80e00403580810380c029203194a020036842d1060700d00700c2c140242480070760411860711000410b161f07a12801c52171000e0307480c1391040d4806045142041001c1003071226002d41102d04100300d508241c0020210b048040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 523031582 1250 523030332 523030363
    0x105040507110a0b06040c1b0f0305090301060e0f150117091006170f010c0f030e0a0203010603120207060c0c03020415092f0304111e0603040b0109051503 68
    0x40001e03070214840c40311001c412101c0d0054508a03521800d0a035001a010354030f42d4400d500d085440040c41d8001c0b00c0c142030303009444146420603000c503190a001c0341c11003c0182d043c03003001c201c000795640c2d0138822400604200403000324541002d00e4620f410200003001e803c84c20881c00044461a03802061400c603e640039049e08289030340d81e00b00c1504207060740400400040c280765011807201c142441d006481a001b5080754600c40903015018281ca40c07a007a0080481d400e4403510804500c070344c00c440a5804294121291700301140d0201c0d08603203d9620a031487c0b00d0442c14040100d50610100d4010f103250311b8800d80000309520b4006944100d40300007480340750703140d0714000280c2034a48468024100001b00f01b29502030500b000d0100a05080c5981c10507040891901c020003000c81171300d008a422040c5c02560010310018019040000e01105450005044454100d641c86d4001940f045200c0c5030b0b01e09480d490080050b0075204050031007801e141c00548904d0154a000685001d1064003c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 523032832 1250 523031582 523031591
    0x21e030a0f020304030e010f03050c09061303170306090901060315092105040603140f041103070e0c070c08012315060301170601081606050d1d0c03060c070308010504 73
    0x41800007401001c0240c0c0d80240040100020b1582100d58001280d0080c0c85003d0b2481810800701c04070341701110340d00d00c4400280060300711401d01d0301c05054181050250f200c00e098403500d07200b104a007144407981710b4050001c10800d01742800c15003a42c11401e584002d00c87c5c1821540c0c0e0b5030b120300c1806c0c3c070422050742e104003407414040d0000c43e10380c2d9503000d81007994421081380801030056100d805004082410460310520300060f500380c41e88101071010301da0001e901e0b1683e810860011004480f43c0c58410740c040802d080710000c4100d4000c0500316940e0b43d54034a03a18000c0d45441140d03010300c4c1140d2410821002605403e50b82d40c01c0c8401300d10f003081455030b5082c0c2034640140d0560100e50440804000402d10600440d4951580c0800000b1034500d40e07a10b40d00d899450300760f611415031091116008004d0070307019802030007403620700450100d0b07101e12a440018031240c2c0c038100301d001c603030202d840ca0b4000e00b01842510f4201d45450411071510005071000b4000280605c2240d019aa0300c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 523034082 1250 523032832 523032841
    0x606060f1701050108150603070306031b1202100207150810050111061314010f0e1006080a03050315060a230406050f03130506190b0108040b010b0306040f1b020709021e03 75
    0x8102a0086d100240401d450381880d0034010000c040c50b00007114a0300c0c2041d0f2041c1c0b8904103100c144102c851400400140f05903a900340143c40d10140440310039403140781c0303003c2011440444040c0881e18550b9035048c8600e01541007805404241d404541070120507940080c501074033148043e8010104420304d851030025160400208151288000700c9518007841b40a90a0054100981d80c11a00c801c4170040001c0910860442d6a1841581e4203680103020042c00030b8002c4002d19480b0701180200d6618803c4503020405540c41280c1120000d062520104c0e0320040140b4181600465050103505003820103201803c02d00c44e10403628049500071000461411840c0403c07015154041d081d900719082042111030382c60b514900020f120f504000c1510400c2d48103155003031040d80c10260b045910b03480c00d04020320542c40a000c0342d800a8030350314140c00043c03040c014150900c801c040b00700340c9a1840070009040440c00e40240800f10700400a041455200c020700b003540940d00c0741a03613625160f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 523035332 1250 523034082 523034101
    0x2030f01122d02010305061e0913050613050d140904020f0c01020703030b0a0e09060a0b030109020a1e0f0f1703071403070213050708010e091501030606060f1701050108 74
    0x3008001d00400c80c07140d40800b61102a4501000b91841c400c0c0c805110342e0b11035400b00300c020981c1000310f85281c210070001007201d00d052101e00360020840200145080303080e44a060811108640c0c40300798541c00d05003c0204a820401d0320080f004a00d01558a200580000c40c400d100e05c0b022076108039004070b080b4009105100840d034520b1900c50085503244c8103850081c02502046812900c6480182c0b000601c4c07000e04c43c030652196250754080e00040d071b2050703204401440c114034034a406650392240c00005881d00500c1e100038105807010042c804401e0b150782c0480f007201d6041184100810b6104000642c2c6c0300740d5100550301c402c0f056a0050701d18407000c900c0c500070301c103000d03000c0c20046090100f9a0320201c003d00100d40241c508006140240d8503102c2070f00d0042c0c0b86030b000689135800400c00d01c0300d03c10910f50082100007d540b081c41d1070420071080c6000a800680745c80b9a0381c4010846160014940d041900941c24014070381c9845e040c1100742650144034142c1030180b4400003443c1480d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 523036582 1250 523035332 523035353
    0x140307050c070f03030f020604080d0203180109051506030c090f07020309150a03060608060607110f18090c090105010903110a050409030c0b01171b040e03161502030f0112 75
    0x200014100e9407010f40c1c075500d01d5030b180810310042e004151106181442c43d072022400510503030300158070600c0c040405442600039400109804551091503010460186082c000c8014440c056402030003484a24004540201d0010341444e01c00c0d4030200800501303403034100025a02440081c81d5240325035130400300381d0031440b543c0e54443d4032258031014041005854000b0b810041400d40c2d04001c2c641d00c4003030903940807005540c40d035404041440644001010001074292142014040c00c501e40d80c100c000c030700400244e020042640300700000700718040604210480c40c011040b1078440180d407400c00060450121404041c11140840500c20725540702c081e80d40e0001c0c4400b030410400c150050070300410b0f8401c031310310403181d1210311000001c9528105034402c460712043d03030103040000c3c0003031958101c003140401703103980203500d45084002d01031040c0702402004402c0120070120500628003213410702c0c2000c0542c1309040c4103205111002000441c243e0554000c042180c1c2811424104402c094 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 523037832 1250 523036582 523036597
    0x180f0a020d29162a020a03121d1f121b110d03090312020a0c02040e2409030307030b0616050709061d0412090803031510030c14030705 59
    0x70061000104071000c41038150761081e01440611140710a964800700c07160035022055603102e100113071000007082d50206600291900c020441c3d00c1b16a500e81e00c03620b000300700541d10750120b046403a0061f003901503105a112500381c21280d06000c1000380e5420f003264482c604011040144810001003407440540c020342c00c1003944941a0015401444014074640c0500d0300c07460f050003140045c0c5c12180c040d018003051268141c45150032840c032101e201c1d000b50403074403643d0200308140010101607101c511130a40003030120b50140c039141d142d1500704444c2d0500c05140036580315424007000403030500030041e40c0e0015464034010030721150040000b05039019122000c25030224108182e000c120002403c40221040020244003071582da0355185190322940080d550140405000540040c3d0007803045803002911303044c0312501d16201d81c0c1441c910780040303819640070001d40c181d23050580b800c8400720a000e40103103002c0c8928055200014a03a400c07041501d42844404004100001d00610030703038030034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 523039082 1250 523037832 523037873
    0xb0d0209030f0601030f020a08060f0c0f270907050a270506030a0c02190302030d051b0406030902010e060c0a0201080a02160303140a0203041a0a060b12180f0a020d 72
    0x195849007086c4a4105407000120b100b0591040b00041d0301c03201180880c4588100c220f01e42c071654801030f00741140e0340300e804045080c80041100034150504600d6a410460030381c51b1007140064032806108000c10060211424000188070300e440150703103c90618013010309906000c04200c407403a56540750f6040f0b81c0210354440000300401c54803202681c840e51480c4015401c40b200020000568081450200005001a0000c00096044a000ba000990462400b0200b4900340815140202203a049078108800194403032080f10190360b40107841500b003180032181e1500d0b008868120603914071564100905201c00280021030300c041c5030741034a5107499000c861422000c0140f0f0001c00400c40c03101014859210340780820101d80e994404e80f841241c0c03041070395900365803103641d24001d1800100184800c0380c45800220710001100050072807000b86203140d00c2207042c2207141446c007042007206412598030005034003d03070322000200c0310701d001e40544400145880c9820286103100c110a0450300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 523040332 1250 523039082 523039093
    0x3040b091c0b1015020c0603041b06080a0b0108390412151803114b06060609190f0e0a02070302060402120a060f020d0f060b0d0209030f 60
    0x41c40541541c89100310b15603400d006599844c0c61543d04040040b948a10040c0c0c441c0301603058a051901c01140c2250042c113110108240b0042042c0300704055400500015001030300f48071703120216004003694003209007005803040c40c0200d004c190003508204146141c108161820101140360110707205440d41c150151990b40791a14686c03016608040001c0761070303601096a0420054041c491300310b000030b9482d00c4002980c015102240d00030300d40080300c2ea140c090340f101c056244080d0881c008417099503810001102e9400c01c6524058105004d8000d04a030103140c0890080901241031684800304030760242d11540600f010600b209400886441c0710200400003298102d603c081d20412112110140d9072965a141010800d03400780c2d000040c050380c000d4010500516101c0c000d40d401d02c098004550f0f6401c1a0b459400c02d03150a10f4042803c59400502410616a640261100c20802c0d000500890340fa01c2134102c42445030303013410012103a02050104169909224054519030400c00b280c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 523041582 1250 523040332 523040389
    0x160e03071719200315090d0e06120c030a06211b080c04020904020705010f060314161e03080a020c0a0504050108031615090b16030b0303040b09 63
    0x70082504420240c03500c56400545603032407042c4140c1d01c2e140d07070015000f54a00070404500078a4a030b4005071643c940074450800c1d1205040f0043ca600c5418054000c0c0800c81d106140505401d400b0b00e44280200410070801e44500c00c3d117904140c101c20b5090342141d80b40d80e035000c5000200101e4000006031200d01c1406c0084c6014641042c030403034041c0c02c0f605050716041d0050018520309118081c0b107600803104124a0f45420f40c050b01c414200a0405445c01e402c6558960071030705000002088550380350428002d01c402811a00300c0c0b6401c0b00b00410003810245050941d00707000d481084140c0100d00d0706c4140c1360b081400c0500c02141e02501040c2c41e140e00d084040d445a0342010081d000d104c141100090502e041c1c001d69040f01c0c184000b951401e040d0f1903611303111540002054445903400629145180b07454454000d003d4000e030101d48113810040c400e21000c6441c241c0c010201800c288600b51150b801100f250111614002c806548481c0c0c100450603002d01202003a010307100c8082203c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 523042832 1250 523041582 523041599
    0x3050313020f03031617160308040602040e0a020d0606050a02070e0c1635070303051f060f1205060307060c142d0f0607030f330f030b160e0307 63
    0x35020284a92050b406c12a031916402e84680950055401d051001e8031000021900030312031640c10a000d484c01501e000d4480e030720301c05141c00c1540c00b42450303980040c0c00409a000e61041501030105440e102d80340245000c3d00070f50707928840c0a5420b80000f407901087c440700c5442c08813901a80c444907082001141c50070f20b501102160b45400180040d4141c030401d509000c01020a070318000048040c0c144030158904a00402004050749400c0071044803e0000750780e51460741c5c0052620b81c1d10340320090040c0c2c00082c03240900d480007c0c002c60034072040c409640d07070110311002569461f2415441002c1681021940317880304a00740d403060b00030000421100040075003c0074415500b40d29a8100246410070305641c0c0c81070000f01c0403150403480100749110701c241c1028586150220b40451400300c4441581c1d080c141d02004880c080c1c400240c060005986240c95400912280240e090081d103543c4580f0030700d5100030408441c000908210754005800740907880410913002d0222800c003522a0a80c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 523044082 1250 523042832 523042867
    0xc01021606021b030304020901031e0f08030702012706020f0d09210c03120c0e030715080108070e041b09050906010611070503100903030902100c1203050403050313020f0303 76
    0x9a03503403c4404502c0b00c03402100000301da0140da07003e0100840d581c030b16210b05010501c0c0916480c0c0c1c0400c40d412140200e102c1086140e030082c00f443d907007681da040549020b42160414400c003c01c40d82c1d4201c902d005e4026407100ca030741c0d07990005005656245508040c1f841449008104201c20b481e200c54413003405034190b48400545544540810182c20340303031090311500c2002a00800044401a4560541c0403541000004104509003040c0f000b00f20310006c1e0a007699500311010901c0d59080ca86d2026a0180c5014010046903014041c40c9040820700c011b1540000c00c0074181c045050070f45c006920440d000c80005203c124020000d506103200265182e4070f00780300303c400003a42c051800840c4440071034001d04640c0c0090040c4251040d1000c2c01016044401c0d042d0181a40c40011001588a5031556036001e00c05503100c4408400a181051030307000310503500010589460308000010390002c040381e800c41c880c0729007152a0704681c40020004c2c9444410f40d50103010101d00c094006103061407 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 523045332 1250 523044082 523044097
    0x70b07030f110316090b0f0c07150203180117040503070201030b0405011401320703020d17181606050a0801090903050714010b0a031103190b0109020c0102160602 71
    0x341441006007280c0072400361010825150070360032040011802080b40c10303c011084079070f9801c100f42e00c00c1d07482c641d11130f80360070158135160056070005824070035000038800500a40314450892242024011009642c7e02031784413008910b40d090f0007002c080303038092035000390796910441c45d009092405240c907073b4598100901c05c80c0840d0811041c1c074124038142c003a890503259078201c007400b44081d10703004480004152049001510b01c00054842c0d01c00380f80310b03e40b101d0003003102e900d130b8480292600a140c06c08528440041100c810444060350241c24403c0e501300c0600881103503002c060410007414030040e400d1a420b45000b2120008443c2c0d0045e01400c0782180e2078688280d030740e03610301221069803001003000b000100100004000240d908198104883c0182e0000032034540354070114802000e560019608403592051082403032034104903102d122090035680781c02ca04819a51200d6064040c001c00b10b002c3e4000c92541c40740d0711b007541903968440c1481c0010340300c8803907400c10000a622428 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 523046582 1250 523045332 523045337
    0x30d06150305010b031512010f060e0f0c160302011b1805091627081f0c0807030f0b0409112103070318080a050708060601021b040b15070b07 62
    0x3121055181d00034461103040b0381007042442e140d941d44440d01d4406c9040c00200c507521040a4800c00d540c07002c240306540b000e805103c0001120341c14285c040380c018000a1005c000a5a800204500902c0309410307100303002ca582e495a80c810041d071a060b07025007100741007004846865200b07811003551080c3c80740c2c054441c907907101241d19264030520400100844800d0510030140743d4004d4698410ba41142d010700d04130f030880b00c41c20188072140520070f0155200c00d10307650001400182c0390483c4018901035901040041107007951400b0f0290400134018101c1081c507985d14482c1e055109640c00600c03444000034000c00000d1820b241c81540c0000d03441125008802c2d01349a80b40c100d1101400c40840e030000402182050500d82d0701702e40e82400081e40a000401e10100000e84442c00c0081c42209440303040a44078680c04d01d120740c2d01e08040203001c0c41c11544840c10041200c0c00b28003031205801c000352000309090940c2c0010072005151540150b40e04c200000d44d0f0814011000350250103090b203070b03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 523047832 1250 523046582 523046609
    0x40b19020a02030f1305121c050c1902011806030e010f06031e020d0c09020c0c040606090527090f1011030a020a030b04021314060301060203030c1803030d06 69
    0x15245008a000381680240903074810030207032025040d00d1000d0407850f10920b80030703840f2548490202d001000b09114031103840c1c0c00070501200740340e04050b51881c520861701c1d005003082445082c40381c0c0e039102e02c12084081180c0b41080002d45e4495060001038030344042d0036640059803031310020003c1c04001d07400310055180030624041d440b80381c003c2801300e9030452035803100e0b60100e079070517050f0400822007240d110b0146041900090311115865000b420b0b10303007006880d11070b40d0789081c0c00c064400f00710901c11032038400144010341e0001141c20586106030307031800d02d07100e4806a080038030180c1c40700407030b42c10105810041015000580c24562a90300c005443c0c4075a09501c8007016103010039000c402820301840043c0403000d143e030151844010524001c500c0c1285035002c50103c0e400b04c3d06402d811220694240800c05100b00c0c1260345142c162406460740d807501a0003500ca00000e404910440400a08954000c006950000d81c18500a05427079684c1d04080c410401803010748100c0d415010b10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 523049082 1250 523047832 523047871
    0x120a090f08070f0501120f05040305032a04090b0103090512071203110301121a15040c14071103070f080d08070c1505060d150605010207120510180803040b 68
    0x40b0b007110071550300d00e007181c1055003841c1c01910f0740c19510044101c110303039a0145d520300a0550003820301903402525140c1da01d09040503801c0b28403009500842500e03601140b26000c4010311400c880451b00000c0002a0180048004034058032a09101070000d1185031307a0705840c1031101d4010b18141e4800ca90a0340302c809240c0c1c2c20760584260b070f4089028094144010014161f81c2c0312183c070424441c540c64800d607000c2d48402018408180c0e52081042c1c2904111403290616101c3c03000e0950050402a80b84050210310740360610030fa8000806044d0280e0300380c117460300d007089540e0142c0042c1015040c62034940307141e50307030f0307001c00d40c4001001a050360041403620f4001d1210342642604140c0c00c51002c21001c030860060080034000350303000751881c0000700c0441c203010325280b005403254801003117403480c0400081c0b41c020541c000d40074895441d003464000520014000350003078561500896105584c904211120b01c0040c8040c3c141c038000010442000214040c140c482c000b11501c00c8215a42d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 523050332 1250 523049082 523049099
    0x30c0f0f030624090f01051003020714010519020909180703080307050c10090f030f120c020f070518040b0a0219030509010507050a050406050306030a020d12080c07080a080702120a090f 81
    0x4c1074842c074000d0380c4440d0046c03203e400e043d403020041c03410506004d4546409a0707640100e0365520006640c07180d654000f400106900780c400d0201e80c01750380d0b0082d030402c035180300080c00400003d4540c5500c0041c0003c208480c0200703001500c01107403c0315115441e031810f14809051548a034000303680c03138011319107864003c00d81442101b9040c2c0d0800c2c1500e008008507503040d50030091104440c818491511081040d80c541406070300014803856010708450155500d40710b1815506800161040c40f0b42104c41d2107580703005000d658850b0700502c0054140d25009140002442284101d0b030110860303102c00c80350150540c00080c0150120340007004031380d69145007103400d401804a1180040c20400040082074422009140c2020300101a1420f40c03003d07900054060102e4001240c007041c07411400d81c10190403040c41a4416140000927242c071f0300c240c1d00e0080510480110805010700354000c07030310a40c42004071000d81403540e20f0381951915440310190603190b15108081e01c0090103040400c0200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 523051582 1250 523050332 523050349
    0x1c051305090c0901080402011701290306012f07090209030d090620010b0901091409010507121a0405280b090703050405160b040510020c030c0f0f030624 67
    0x2c0b0380607402c0c24a480d00440e60282c1c00b030f0040c1d040040041d40900071403800581c0c14001c00161580074041302c14404404843c100b04155404d20210034410881542d130464001001c4011800c41031807180b60060701e2041d8101c00100480017403050940110307901001d07074001e015100d402c80444406000700901140c1178030842c000d1030001420324140840d604400039840b20041501c07000481d108143c007000c01e40401c400d900020100b91035102c001d2210503861034064006800900a2000d403610341c40140140074040f0120b50346560b01d0b0700241301c080110403d0014000c004105001c40d040c00401c001c14210b0042d69200400540312060308401c1d81c0e4801c1d10666980588081003550f02e860003603005200007001079a003800342e1003084540c103017492141c001501c4189800d548039400c0c082403240d1500600d5007034042d94803d1010040e075640001d07100c07100240840b035000c211080702c07010801100112100d80d030584114414401304440481c0042003245640311821aa440103004028440c07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 523052832 1250 523051582 523051591
    0x20301141e011403180f0a020f010f020606010507061d16120201091401020a020d060501060201181a0c0c070b040305060609060907141b16080d120b031c05130509 71
    0xb6448002903e9080100c00280da442141c43c22402c0091a60091642c18040c81340c2c4092600e4105401c240d0071407601104400e0100d4081ca0254468400150042e645510242005040c4003010405400b0800e080d000704403c0420018070f801c1c500d0316000304a5070b8040006580620030300030340c004100720444804005000390160b484c010283d01d001a011034181300d14844034114040e0720400c03009a2100200001c881d4818100014191f142070700003802c4600300f0205405058a0303a2592000c40c0e5084020202c1c8216280410542e440d4000a030720503104080700040140101140001d042d460b0740e01401c101e90050017582c526981d00410049190012288141d0084079140495100c910400d01001a142c08031503091804416070312001018800701c0208810364000310305811a00d0380008014010700c0d5540c004e10300e658042002800300b05182205007660307035079400300a07070a90b41081a2420b032824500480390130f41014400501c5a070080d40301131000c143d6120009010b00f0045039142c440c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 523054082 1250 523052832 523052837
    0x6060301050f090c010e0609040203010f140a060f05130e0a0204140a030c3c140405040809150d0f06082407030b0f030706021e03031006050c0a06020301141e01 70
    0x4034185400654446106c81690741d0849814010101191034a1000f14060704002100c8079005260000039074940901d106403a00138503411104018243d04003019900074095814001c0e2142007407095144017041d075610040c001c0321810240049124141d0045c0240c1d0740c000c0307480c0380ba03145102c14481d620007548001071081908006c01c1000f00c240d1000580026202080340091584a09a41c01c020102c074059010010408100700402841d85005454142040d00d0610940c505600d68101070f000340203089014024500134a20f1203511041100d086400f0000d0803ca503010965040703008005070302410300c062040e442c0b03040d18510804440031544580c00c1c4442c00c42e98400c0320031409024001d0304260000e0312451414050b40d01400302c04050f050a070300900b012030400124040c007203170403490441960400c0041c00300e0384140c0009102501c405041c844ea448018059003031804561b110003415491003c000851030034000d40b8100b0b01800111240c854604d20501810290440107050701d02 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 523055332 1250 523054082 523054093
    0x30816020f121b0a05010209010e030c1e0120010e061f03060c051c05090d0512060f18090a03080a3803010606020304050a08010603120c0606031406060301050f09 71
    0x20040c0a48009210010f080351040030f400c414400120314100e028a03088a070b03a50003284000075940d02500c0b85040c4042140204040e240300400300c3c00d030300c2d0b10130030104203000e030600a40050b0b40a001880e81030031000340340d5100301050070700c590f0080c1028040398002e801030402043c0a9110b101158000c00c031411004645d06240d541e4400042410b000c2c0b81b070a100c021f0000b0f01840b54544035101c83e0103ca82c50203d864504460103c0c04c01100001c00c2045c0102031046520f403030083d0b10400d0b4010000d88040c0c1c40e401c0c4820014129400869080310030038150010444c0c1c01e00007154030f03181d00e44030f0303110700307800343c5038820344c201903502200b40e0f810750785540389043c2c0c5007035030324400c0500031990390942d0880c4112040209007074400ca60060301c00b44c0d00010301000141050b2507414001d111040003000310a01f556100003102040356030001c20882c0003051071042c018550702c060011a0b01441022810140c8201d49441e25412500d86119500c0d200000b0070703400c103441c6168421401c20000c2c0c038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 523056582 1250 523055332 523055353
    0x51501020d030b18010b03090705060408100218061b0106060219030f0e0301020f0405011d01141804181b0332010c0804050d050a0f120b0d030816020f 66
    0xb03000340900c610007540641003a40e080310711309828540601038144c19070804da4910381150507526200b0164803603405480300700f10400c5000d80c08103110030814028100036945114071414920a072800e090003592100700026854212021400300b0382841102c20001d02040da40d6102c1642c0341c1d00755000c20151940c2d40251314000030b205800890341a032003810640ca030001d0110109089800c50411000044c02c0060180600e41e04802c241d0f00c0c024000d454066140d04c0710300002c0c8050b0456800380203009000c250529001000c0c4c0030b000c0b5010015000f00b00340050a5034805a81e42c03210010f4915060f000c0304c8a4252044080c0a0240c07a0007203403422040325100e000c0a480d00160009070103101120300321001c81103003800b40c0e031b0202a8654640038142030a0400a091a84c5114000144841080380c6000d140e04006e680346070070b02504061088030315040041010340b10f0000d10940c03125004524108043d0070043c0701d4003d4083c800c641da1000110720b420f903520310303000051400a03480311b041c6e403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 523057832 1250 523056582 523056587
    0x904050c1207050306030f07081507020f0a0b060f04090f1104020f03090607020d18091104030816030809160e06040b1002030a230a300906051501020d 66
    0x95084404410100e180c0a421000400c0d80c01080d10b02400161000060000764501002288900300f1140d0151031098039102e0102d076140e0309041880c500d4220403000034581e41c000d020039819042584203076001c600403407074000000070084034890310030401014040703c1800c040c4603100d10a03504c03030400c442c0306c0c10b19110748408100854516a1042e003c024000e40d0400c032501071030150390403500409141c2002080a030421b4207510000003003008108042c44c9140d000840c2e04225614001c000030101004042200786200d00d400250619800282d02d00516050031000744450340241e071001101c0d22084001034448070313060b4240700f50780e294810034814014511030298001c01e009000058000ea088003040c4000e142005038005031b003000c0703040c0741080d030001c0c5040300003d525842070940f91001c681107581c0307000701200001044141111010202010198032545c4401c6050b808800c05840340508080c00030040219000e90800010035000c1c1c1940d208042e101308140c024211008004c01e04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 523059082 1250 523057832 523057841
    0x703150f0608032b09060e0106090219080601050d0203090f07080718150806090a0b06090403090303080621030d06080307050d1d0a121109090309101101111314060904 73
    0x3e804030718580c1d45103007992030402c5c8103d05119105a8022404040940c040c0f401c40381d0756031005a00034010820a40c00000c0c4828038544082c0c1c0c0d0403c1112070f140c0c0c400403580c0e070042c29a01e480051000082c0040180d00003200090095100d0444034030603142c1c1c245075111030261180446a082c22203181c400200141c10403140f88020720000325003140e50301c2c8800d2405005442c5076400d500504982c0040c000c00c003a41c6903202c00207a0b24100207050665008007900755500c0040d0806c54020041001940c88500c200345c203010508080010000005040342c603a40881102c52a103850300070005140c01002c41a64001c0e5040000f0340180200150103603100410380c0e0004150380c0c1561070070341c0700350b845010324400b4190046c0c800c2a4098949404200c4000700011288950032a8042000c500d0000084420030312b000d58104c40c031105e0746078003900c5455141680d01d15a5082039101c0e505103100c5070140c10b241d11941e00314030000b9600c8812b410203486050784075130032030307020010b004190505400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 523060332 1250 523059082 523059127
    0x5010206180a080d06050a0b03060901141309030915021c0f020f060c090f180406020a030b0405090c0102240a1104150309020406091103270703150f060803 68
    0x103482d88079215076104071603680401c2c55030310b42079907403507041c403082c104910244081c055050141e491401d1500018000c44014410802800301e0700b4503840c5a5200c841c43d20f640e04400600a20080c1003501d005000500b4030b0242d0240222940c00d01300d0928400103034051150165520007440c4c01d641c40e811500440340c0c41c1d00c1d10940c40f0f0202001441c020420103288036010030400540c64001500c200010135a074111002c6c0300b989041c4111981d400c2690b00d031508650f210000603981c4000c2001940509050303444942d0140c40c000400c0250f80700030034281a40b03082642076400014914622080603042d240310130044001c03d500103007100085074014054510310451130350900380d85881e0302600503c81650540040d80f1090210110308003406400081c00546109200246008480305810b0000a1810640c0c7c030300705a800e202e00411441a40100c52200250386031640c4900341202c440803c03520b02004d413454819228800b440c07034810b8a059034460809145132410321850421401008407 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 523061582 1250 523060332 523060381
    0x1415091b190302090a1e0c0215071407230601061d0102100e0d0e030c060702010309300f0806090a0c030e03030a0902010905060f0306090a060b130302091005010206 72
    0x72010002d40c0c2d980240c24411049480003040203001304001c00026600d03000c0e030074082400c0c4042c0307806064012408010600347e0311070741c080b156542c40d02141d406e1181c41c007552505c0c50000d41d520512400400220b43e4482404030082d091410740d1400755219824032410f000280c10805403400d07401402c0c0c031020a41d20510440340d5074551003884400303d07804a0080b40c807581c000040f1008054200e000202001e100302c01500300d41942002007039141c42540b800070704065580c850344040083c0440410303001e0580720b690709070030f1000780e85100075400504800c01c00709055119200000744202c400c14800d042c0544590700c5a02c40241450140c25441030713179001d040d15401c07140d0341ca03d070800243d40305019140000c580c1c0000d038000075194614582106000361001c102840311000004100c90b0800025108841d860740c0301007803c40102010f411100b200c28000415800212a1002d0700040c1da000b1103010165844808601e0000b2020f407041c2ca015800500000e4490070030420310840401101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 523062832 1250 523061582 523061629
    0x30507020907080403180b03010b07080f0c150a020a0519050c16180e060105010f11060c030a0b0603040f020118031406010e1003081606091415091b 65
    0xe6000900e004021240704000401072020002415031207400d084141c00c189001e00305980c01d11040d2443c620050090403950100012004100301d0450102ca404041500b034a42c1c48183d41b894481d2550f4120400039095800c0c20f0216101c80031a100711030717403000f20361105031810803001085091290110707111814040309002400300c00c801400040345006514049050160501040b00c02c11000001251a8a0714000b0000a140400161181990400d00380000840e0518000310b80d94404e500e0703014440e002c0c440c18008054000d4001e54007850b0000d10034040c00961a0500440f80012640a00b00002803080726025501588400c2003910342c01ca030700e01d40e507602d07500e55030080103000c10240700d44d40c4840010000034403200c0c0050b4004240300c128801492940c0c80d004e00034003444d0041664950b03124500c41c20040c0701c1e4000706d001540540109a0030726a00d03070aa0325400a4240340d1044044100002c00724000030418101c0351038035402d503944900c03054052042661000740400d8210801 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 523064082 1250 523062832 523062847
    0x206100f18021204030c03110d02070e040c03120206150409030206060409020a0803040b0304150e03040b0f1c0b04050f071202030901090203120c190215130f0914011d0606070305 78
    0x200800c1904c510701030f4492024000443c58000d000003805480341241d034004510007001181c2c0440c152040319001000011541c030b403030610003044c01e00340e0300080400c07086120b003089540c0c0105103540f00b02c0d00380c065141c0d00d450300c005002c1030316a035050050050f00a00d00140c0c0074942a804100d403103001401c000782d51500c0301c1c900c41c03460340290400400038401004110420017901e000c80b150004a0f1018000e41c88804c081c0c40d070341d00031401100113403440803640c54180034860040d14003907090440c1c10407085c901c0040480c01001410407907806142420001418154003015007030140c80385603a154905140740709000000e40025080d05c0c810b548600f02d03180969404c1000c0320b540340b00036417580c0c0d980784202c00e410b25100351041864064007400280e400581d89800300008a400c002e1000c90742c1e20400d01c410f06044802c0d800040c1c205940b03100109426055034885410101802c5041107140d80f1641c00000305510000c00704c011100030360000f80030f800d20a0140103010310a0074801d05003405c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 523065332 1250 523064082 523064107
    0x17070c0507060c110d03230705010617011a06030105100314040c05132304052e060608040f0f15060b1206040203040b1605040902070b070206100f1802 66
    0x40d400b88000512400602d0180500703581c200c450000b08861800a01d4000d54010308961810030305040407007002c0f840c508041c18410101c170001d6034000000c000817a2030301440790215080c5c4111300129031070041c00c0317108040113003e40392549030002c04e014103584c40e00080007800559045200201911170000210389140d1010586c02a0b124440b03580880f82040305021119008000c8607046508200761000882c00c08003804a0711080c0c690244c0345540c590030003030300d040e03103d828001e000c100c80c001d40320111300c0c0415800c840d05580340b002e001261342c411089402440c2910702602020b8035502c40f40015900d41c51120410780f051100855003100181e50a0480303d0a900c00303802d0f880b000803400003000794010340c00e078403070b10031102107040d03040c591152001c0c102e00030010160321080c02c000d0100180583d050f5401440030620039940c0c0c0c0171a1810880350700b4140c5450b0051300c1800c020804031103c8441800c04e0380e1280c0800e0000c4c5245c202032009040c5910180d5107082d60800681003141d5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 523066582 1250 523065332 523065343
    0x9030a05070807080c0307030b0103230d120b01020a02030316052d010506150315210307020a0623030601032c0709110702061b01060609080f010c17070c05 68
    0x180001d800fa4601d496401c0b810702c000221654400d4020020620004007002d0381941900e401c20400001c0520046000e0800c2208140c0e00031039204212042d04251b501c1401c0744000d01c98035100b0b0214014220041e43d5036402100000d505400a002e407180b1b5a18600e6489000b0f03004208591548046042011301480041d06030f0200e001c2141644040030b00900a0300d400c070200b510302904c0c1410545c030082e128000503005501c40007520310300d000c290384c8240c000da0b00382420241000400505030034840d51396001c4ca1003280241c03028480060301d140a18130406100003c42d0201c6199034001a8001081e400200224140340c0c0d103442181e2000d510401da0607403900038224050058004071203052418140390701c016006800c2852500c01c00f07804000750344600e541900d5803611080200e03d08440101441c00d074084a45c600100007805c1d541c070800c508111200703142902d91031071042c400700e0309a0b840b00c10b500e0080340800c0018031030000105230950340502c3c3c0e454605c040034000c1e55540d0818 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 523067832 1250 523066582 523066589
    0x15040e2502060109141303031a06040b070209060301050603150703180f03110a03050d0c0c06020f120109110406140c010e030a020f0c0d06020721020a030e0301180809030a0507 77
    0x142d0101006119101d032500c40d54003100301e000307015607151600c0c045805220b0502040103040544480381021095014a4040104240100400e403510f8070f44522140940251205921800c144030104005080600c00d0364001c80014001d4603102c40c00b01e0001002140240441040694901044201506050514145500c5244002c25220940c14000c0040c1030070688108160010314019000036000011a4441c401c0003d004c21142079100c016251b072030300e50a024002c2400010f210150922003401429810f0500091b0b40482c1d80f14118141214401400c40c07828100401050000901800f81502035003050b281035450400d40c080d1881c250f581100d004609a40081400740410340c060024a200340f40d910002c00d012170031000012118501e2480140c41c1e1940010030780c0034003006640c2c00c40351359508981d4074542d80300b0140003940c0d244001c40990006220010b052014617040c010307100156541008168003001c940c0743c1070b0699118024141c0e040c4291920075002030700602444005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 523069082 1250 523067832 523067837
    0x30305090a09020a121b0801051207050603130611040f030204020d060b0d0501080c10120c0306081506090609090a060b03031b160e041205070804030c0e07030b15040e25 74
    0x90511751101c1809940c01100c807040c0d00301854480322075090740169801d04513001101c42402d82d4212032442e60030000c6503082280c014000204021842d08032091086545204000c100320104032041188960300850054608400c800001080945416005071408501d01080051400d55401394140340e03522000b503038002d498a5034010040c002061040c2451002c05131402c0300d000304d045a0062545a2210110644565400701c00d10524400d5000d10040c0c420078080340c641e84201048a026600c08682441c07082c40c3d040d00007201c90800000036030191801c00b004000d01d446a40d1600c025201d042c404a416102c140301e86009000180004504021240050324054450759251b012072344a0b40c00450500703905400380800680041e0521400110324070b031107512001c0d0340c03030608150310681e88040c041c407080a5000c18199a042d5003107000d1051038038100b201040210070712110346e0001d070703030500d80714801d1004001d007100040030140c1c020901d06410304220400420001d40c4041c601c070300c000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 523070332 1250 523069082 523069097
    0x4060f0b0907180905070507081b030c0a06050a06120201030c0e0a0f06110c01170405160e07080619150c050a060b0306070305091209060d0c0225030507030305090a09020a 75
    0x1070341c542580816000c1e00700c10000717100d5803800c000040e21030310501400800340380700000e00d503072210040107601031314450304020b40f82e0f42c08416501e556251a1382d401603400d940b40c60007095211034036200c0c040844003052010740c4480c007280c00650080c4402c080400c1404070010005985070b07110784608020345520308411394002e0810030001e080196a001201d00c40d03000300b000070f1403070b0303000108a03110307500b030b407000400550381c601d0005d0400314800f2a8903150040c21002140b00c25090f0179151085000707035074000c0669102420484442d881e84500300b1040f400c1142480311045030035210101a00b581044049030589070348187c030f0030100070400c1e5441d40d60341d100f8156a107001d100c0c44d50040164603050010707080900d41c81d03856951a11700e8040701c2d100080c1400d182d49408040d105d9658011000f04407885000030065100c1d42e803104041007980118245140350b00c14001c510341580d030050010305400d0708654094515510101035198400d0300ca50000505101c03d000134a5200a035584550 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 523071582 1250 523070332 523070357
    0x3140c04080d08060a09110403080f070204180f0312020714160605040f15030b0306040b0610051c0209060c03070c0303090b0307020c2b0516060801050904060f0b0907 73
    0xb410310a1035040079003003148080a015540e41c035281c2d09000e42c0c606280014101909004104083c840d81d80010031196000c10034600030940a0007900003d0700945050002e01c0701e46045c40b1044814040c0246181c04050308000482d1140082d42c90794804104014a401c2c40780d241c0380030000405160340400d91100b00381c03a0700d4400210100009000c0390801c0fa041c02d040c50000d4030040201c1c0645100b82580c83c466008013882500408a007a00240136915142014200035461100841e0498040d07488110720343d002601c200220b40280041c91794900c1001c1d03403040102c0182d400000000d500210512604042c140e060000700070442c42115030800c0d072451407502815a07051a07000c400b41769030910030000c2c4181c0204400304441803c41d880c0707844422813200000491040d144002d103680b4140510380c20844002098070901041c080d020b605203580d0401100c0c1c904003401603e410000e66808a00091010341000071099004074022415030300031004100244c05c1100c0300c1000a880c807085c1d8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 523072832 1250 523071582 523071599
    0x2106080f0f0114010602030703050703030605060f090301061a070f02030a050105011503110702150a09090e1f0203040c0506070501060b0307121a010f1b02040203130201110601050f0d0303140c04 85
    0x4041c101d60f4502c00c942c13036151a4019481e4000c1600107400d020300001c025081501c40da010304043c0c9001800c25864001138540d04d80c1d103411240320280a03601e45100403404640d00300c401014081c0007280709103000120755032003802000c1c0b200100d03054810307a107172240041d03070a002d481c0c082c2051080f401d25900700200000c0c1550b0038401c0c08184c81d40c2c1001100d0258980d641c60030003caa0346100d450783d6220708442156800820b43c0030f06401482c0241d92022020007040d00958500402a042419510708420404170b200c1034078001d00b88054240c0802c66420f10f08080c01038107000350000141c4550720b07511803455034411100d100c0028180015002140000e00c00e1104070100000d50101c0041070f00c0001c0d00882002d00f541043c402d02599520010781c500310f4002a159010300255103e00340110818802084010101d0105038044a888118040025404d040700c400610a280c034090200c20302107000c44101d02a02050b03100c40821805c02282150180070b80c1018810340e0b610307458400324 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 523074082 1250 523072832 523072841
    0xd0c120c0b010b0c1c0807090509061806060d0c0206180129120714040e0d02031e0403060507080103330e2401081b012106080f0f01 58
    0x18201486000521400496410040d05055507164552142d8520315580e219244c000554031074450310850914034850b4903885007515000d04c140d512155000c2c1d840e5801c1201c2810110b81158014030038a96218550001c50070644c0c1098022304010716004003004404150b45450a1080c0541d1090062007001211100383c91240321b4060000c019451103000c0c4100e5914101c42d0284e605001c0c05100c1c4074950b641d551180c4421405d9080352102e903510303441c000e40186081003891040e031424404284210300850b071440c941e10b050b0301540c40c12540505042a80c4444ca240c8908000c0510010001980034416907001e800c8540f2a09829032451822115681c070410080c14044400003c2071100d101001c1c00d842c214081c0c40000c9102d404184c80d55242c4440b29955004020b10064040c2c88443e0818059060714401b60969642c1c01c803100503a82012080e8076941d0014620448000800c081040d01c000052156440841d4095a8070700c80d03494621503e04401d02ca030001c0e10101c004c10800d204 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 523075332 1250 523074082 523074113
    0x2090d021c03120b0d24020d0e07060207030b07301b020304120b090f01061509050a060504060309020d0b1602010605030a03020a12140a12050a0b0a090e07080d0c 71
    0x3c01d1200030049400701e604000d4010004102c2d4054081c01c80c5001d0003465840c0965100b0041151200d02c2c1c0385a81010f0102c1c4e00c0400840d0049002c0421a680b003c21300c00190303500108030300b0f1540c841a0301120010b040d6020b403814050007000c181e0707401002508400500c409000f01103000750981e00740c0e94400135000000da055500402c4200140c01072800f2025555410601441e00390b900c000c846824030b0741c880051005540384c0000401c82c00100e401c4914150200d0303448480e03ca4403041403111690b010b01411001c00c0092100b00241442a0000401c0a01c0074040481c0c038011644d40d00c2c0c0d4007500361900318400c410355803c550300c0c590901c5030f42c0003000100c008000c007801e03d440187d00d82e807a202000c2c141c0a92801e00f03012039070045448560704072070421013a0761410150310041491030b400c0c2d00d5402d0a82040003107034000b0158003881c40c10000c01050407107060704e8001d44000900315400c001e5110b0140310800207205038140700e584031105254582c41c00380742241c44c1580c1c1a04030042c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 523076582 1250 523075332 523075367
    0x21003091203020d0212040506090d0503010807051e0307032d0b0f07090e01030b040c090e250305101a060c0c1314130c06050c1002090d021c03 63
    0x942040128010000e110081e5038582401a075075204810110041c0c031420703044002642c2840188020407000203100742c4120024420342c0c0710307100c5a08088a05110070300ca524000c1d40309007801d00041c503025058800c4502d07020204a480300340320011070706045540d4010b6440d4070314000031030028034400c1890b02c40b8603080205000c0010440da140d44c02901c02400d901507150400300054a218000d000d00382c09040c8140c0264070940c0d60789032002a801c0700b00c0d030407950000c014500152048681c060301d821410341f0409400071440200e00da40400200c988611400d540a410006c04520140247d0408010480001c28400c04029451039100015a5030501412040117001e294050105803032481d03e80031141d40d000c001c10f400d07110010304070250034094440392b0a0284400b1030720044155103042d01c21080d9904080d500d00c03003600c0c3c0c0e001d945903122464028204401a0400d60307030050070740c920001c1000000e1510f640205821080100c0c04030200c81246a40c0f030249900800790140c004040c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 523077832 1250 523076582 523076591
    0x40516020c010903051903210c0e01050c0c091b0c03030615090a0314030f0a2706090e04050316031215060903080d091506061d01020607050a0c150504021003 69
    0x160b440d00d0746e0314007070350900d90b039016146803141c101485201c01c0c0a80451700000d4007101885580b1039001861050f0750217000c1a46164100600e50050043e10f0480407004040c0440d00344c0001031001c9500018120b0348100e005d41c000048020050780581008c06807500103580760301e04582030142d074000c90440c1c2421010288030316440b0b81c1d250903004c0141c030745c081c03080300d4480115140d240c07130340c003a083e00311000390404111400420392100e101c0014110007081e14016074841d404440038021207006280010703c03030303003000e2001612500200340c200380304608692070120f8524a526200340c40f15021000201c185106c2041c01c03849020f014261103099010a40d41440c000c0080c00e0b0554500c401800003c001c28800900000c603071000c808a42c015501c81c0d001400314200300c000304154050500032441000d2260505682001c0e03868176004c040e00100785a480d10b101c00e0760181c00003a8078400f000105080b603030020712a104041c2c00260b01d8480452035080c1807040001da074407050741000070903141 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 523079082 1250 523077832 523077839
    0x190219030b060d14060c03070e0d0305190507060e07030b100501090302010c050c090411040606081302010806120706031a04051902130e180618030403030e0f040516020c0109 76
    0x41440c1503000030b0200d54140740e072052407030500c5600407400388042890107100e042041c120174410041d403150b01196220901010701c80b007004080819000050f00040c42070003c041110410340d03800350451200e007001c6003840815034411003544c0000c01c1180040c0c000c05030800c01c001941003c19044100c100a00d29500c0c00c020000340522154440a0704100c0321800d01c00500609104941050001070f1920359640b030306051103824031140040c00340c05281303000d00015a00e0b20071401203014030490000040481465001140c02c0c01001d428141c5c044101c0b0780f200c0d24006d041103008001c04203170301e002c50380e68002c80d85100c0c0310380c041d40380c00e00480c2858104100c2880c10380b04d44140c101c3c0c1e01d900580326030500040040040c0b558004440500341441400319069003031801c108500300290407214141c0d54142845085103d044071034071658010700060000074000d8980c20490040039243d944458081390020341034035401d035000b020040a6466030b8031015414072801409160a080082c0c10390325 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 523080332 1250 523079082 523079093
    0x30e06070606331e1e0216050109050906040e01060e01030605090610120311100c1808210d18080703030c0828020408010207210e060901110f19021903 66
    0x34400e411210740800b003c000344d6000d0049a5108615081040e0001d040c2813412001c0d41c0c8205500d0070b078010501074980014950310410040c4140c420183c80303807e07161141000d01000c0d02030f0200c280d40325520b450700864080d0700c0308040740c000d50280b04082640d0501c00340f082c0c14001c0c0504500d000d20308140060100d1000e40100444a50381031500032842d070740c18ce604a08107006c82211000aa0a18046458071648008425444074080da0102d841555400d62035a40b9036218003c44081900c0c07041680740c81c52080701914030100030f17080200d0b901c080d110101d10608000c41e4100c903083c0700030450324185949480352441900f8181004003840c02c1114001c0c60881074142035130040e040d42c4d00318400e22072184e0156001003c400f0020340d1159140e14090080380e452650100b23600c2c021645900f03101c2c0c800d440c1001760910160040d0318200703040b401181c0da1100ba1001445c43e110701540c60b01c1c540420441d03003207074560780580819264a1441005180f02c0c030604903902400049005001083c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 523081582 1250 523080332 523080347
    0xe060907050909070e15091207080a03180906091b0c0b060418080a0f08090c130203131b06030b0411030a0b01090306050a020307030506010c03020703030e0607060633 73
    0x400f101d511000c3e07030340c1d0041115044440010142c002d0081d9a0840c0c18480342409800038542c100c800b40120406442280c3d6561490311904072143d205019840c0401c1c0109c84807807401031211074029410b600c503640c2205407a410382c015910555034456101460707200c80c081003055100d600e40b000081c0c01c1c98858103007045000d820503104507503030f0700c100c21000110641c034400384d540001301540b40c1070051005010220080c1100000c0340c03082c40000c40c0d2000c04200702c3d4288000501d580d2094400c035070f048000f504020828001c0880d405441004140c03407801c1d02611050740403c9010f01802c0c0500181031350b908440540c0104d041002d41c8001c23034010000d032503101d0700306040042c02045640c01250000c101d43c1c03010740802d02e444280f103d10080760700250b1050505031018800c82e29450011141c0340e4050101800503008620700b030000a100d2039050301840d030003c1605051990944443c421940035a2188640301009a4003007545550085000d8000074501c3ca080421011100d0281805 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 523082832 1250 523081582 523081597
    0x21b01020a1211100e0d0206010e1e0a0b030a0c06030e0a11120a12030f0c09060503070807020c1002070302091f060309030c080a0c03080901060b16021503040b010e06090705 76
    0x40165440b80c1d100c06810041002084820301d000d22405400003d820380392101406c150005000b040000710781100c0c41c500d5680200c8074144840503402c10318007001030030003020f054583da158445070940d000f40c0d4100010b400b247d0140044111036441c142001d0111441c114054180d50441910310011a0402c400310039040415940010303243e024203000740c20182c1c5018010100048290390658242d895400b4840e0888185000c0180106250040d43c82c4802481550001030040001521841c858060250400800c0c0100c580e01443c040c00905496051500356005034400300e010025890300809140e00404840320646860380c9480100000c0450343c0a03040505480301100d4003014498990001002d4111200f0b50701e481030b4480c01801e4a268071019400210b4140200c1c204201c1071040404456165034414504a034041d09151b141c03040381c008ce40c2c040341140040c042c040242c1d00940c8141d2040506007019810302c2164001442c0c041d26183c0039011010401170702a8020301180d002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 523084082 1250 523082832 523082837
    0x210020c030904090c030b01080307080307030209010c0b0109091b05011e090911180f0102061b04090c2001060807050d240e0d03090c0b030c0c010606021b01020a12 72
    0x15269003010291952150950a54000b86028401401d0001588085094a10890035041240d82c0e03040c1c0203a8034000d41501800c06141040420301c8240294000c0054001c181802000400c0b245c48007910060241d0007074501035105c1260f80300f001010b20a400c51001d450351041401070410340020b000d84030280610710003050076240d85e2202030240501c40001c240b031010a0260710a05540e0f6074194201c11082d152114072030094032007e1034180400302c0c0c0c085041c0d0081103240d03030305031507200704041152032503034861010000440c16200c54040c400714000141c5400c0ac0510385070008896040d814051549280d14000003801144400b05980c01201c03001c80d01c0d0b45c2e01c002c103410b0040598407030030f41c0b01440412a03000400c1c1e1001640080d801a80c1c1101900c5d155455800140d05554241000030300701881d00105100304400f0340c02a540042c0d103034070070900f855444501c140c00c42d003040e0803403800350788103000d0400b0345489001804940002840940200c800755680c1c00d843d0408520450107 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 523085332 1250 523084082 523084087
    0x12010f094403091f0c1101022106040b03010513030e060c150604020f07050607021b151b030726040e0a0f0e01060e010504050603070e040f0c172506021002 68
    0x80ca540800c0743d481303c4c07440c0b01902c03040505070086132001020014039200104030030344600c0c080020180f00b42c0e01d87d1403416002500316070000c0c80c5030810050061545510a0756103198094645092007428801c0ca40413109110308030990401801000014580700c1c407071001008000281540483d005034080c10510039841719807100c0c40041c0c00b034011051031850908003ca000300c14094006031003401a86036809840030508191202c1040d0f007686401590051071710604c0b00705544a100051040c44141441c94000b8070807030190381d0450380110000d0b100607400342d0010719581140b2618003140c0b0f940b030305400e24191401000204440c002441000019502d40ca0289016480d8021071240107540000b001869122000004004c5080c080d96020702d20340b2001030030b01d04000600c413040e203004401d509144d950780c0ea100300c241e04031807000300d40c1c1e075000910010b04480541c03070214441c601040901120b240071983c101a40b24052010840d085880e01c0400416802040000d00140c2107540541d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 523086582 1250 523085332 523085341
    0x80105070203180d021507110406062309060f03250813140f1b060f0304080a0c15050114181602340e0f010512010f094403 54
    0x505a000302000650413000d0704802c03202031b11240c0018034a2038401d00034072003c40e055105000442d000c0740a104089104901c2c40c1c41e8411a0802100c0030840c00e000c0d4525105018000c20910303040b0300c00303800386813402000344070500d5561180c0550384885031815000d4010048030003001541c000c1c00400540d541180e582082c010310641c508440c02e41e4800302c1c1d810704403400315a0354400780c83c0305603902341c0c908240d08001c900c0c0450031526152211120305041d5211500d03242d5a0b5408944000180898428154001040d001000c201100c912400244030f40c509500401c0c840d81000b07102e482103241c12072421079014522511504050f8003454160441c140c4103090786003003480ba9519400d45850031400c550455801026030030040e04890165403241c0e0751a51304c4010350700752001c11403c654031005004604041c880d20b107000c82035000110301164100d1240c01280d5120a042e00c14045010108031a50050180303000420301e0150200150b48101c40c100f00041007020016241160003c0442c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 523087832 1250 523086582 523086589
    0x90307080f1b0132010e0a020c1c030b090703020c0715030f02030103050a031e090605130308030f270c0405060a03050d050a03060b09010807230a080402090108010507020318 76
    0x421500c018400800c0181383e41940035007000c80229080c000c03070030b0390a130804108050300480c038103c03201c2c0305141da0161109070140d00690001800d0800e18440d004103076035012242c1a0306900000e0580b00061000300d143c00f801011003004008005041c0100b184031140a0700044079011149901030403201805642001c5002d8681c14101c04045030021002009206d004200c1001c45442511802030b4802c4511220920380e085000403000700340c00d12400c0220380d000c0e400034914084075130840c5818503280d95070300409400c15941c42e8030140103102080080298260316489041c00616110b00780408010040e0341e03070b4105528107028030380312000b0420366100d180e072040c0910f52010a4481c15030f40d41000820340e0f00304503810700009040540024101d5001d201b184c0d040304040c1e403204a40d90703c600003031340e800c0d0f000e040440d00d039000c10a04501750056034004e0049442c0c103640f402680d040c1801044550501038011b403c09915110900c03489503000030480c1c1078110b22001041c20b030790303100001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 523089082 1250 523087832 523087867
    0x5090d02090703111b0f060709030b040813080606040b0402310306290901030c0e09070803030c0c1b2209051209031b0a05010c0507080115030209090307080f 69
    0x189800360f5002c40c0c100000f00c804140e05500000e1700b02161420f600c0e00c01c109a8a907003d48142021494050003480481c2d0b4100c50a40d1040c060a00a4601404500c10303d00400d42d9903c59403450b0040300078000c2c14a0325008202905008440550800305498105500010b0102480c00800d000d05030410100c4042c41c2c2c2c010095401050030040a010301c0815800005002681c1c1c4017004600c03481406071030a0380015040e2600300713041410701401d00181da110710201502c02c01c42481051000a5032203c20401584111008038420b40c440c0c68890009140c0304e444032084020044002c1c560500d40c0321121450001c8100740214000c03080800d0700e103001030088042c080c03c180203010032103443d4400d44000740741c1a60190115030004504200408040c01691165940207148560800180d88540c00300429640507009880309075941d0300c201070031618403a540109116000000304194036002d00e078160720084a0f0b024628105050b5906901ca1085080c1d000c8004008120340381e902c6010640d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 523090332 1250 523089082 523089101
    0x180112020c010b090a1104030f080702090403020106050a0602030f030705071b0f05011b1511090a080a0611030c03040f0f0602031e07050412061a0d0b04110105090d02090703 76
    0x8219034030481040e469020302140820580035011250204010030700c644101d054000e01261030301d007840c0c2150785041804000150688440710180301d00000359503510070541c0518404e400020302289080c00340040740d030071503220906540090005281c1c128140301101e5200c0d03d549480c0c1d5541c0900d1510012450181c01560800280310f00c0124110181f03d03454801c0c0c4e04242c0b920752001d00c2a0700c00340382041c48402c00400751104d18a01c0070b07066406403c0b621001c540d01e0f0b070303a900300018031317021a8a50220b030388103100b9035120703481400c01d1160341c2c1b1420b140c8404041020f41345181092403080a4800940300a001841e6406100c1c00e0158010715aa2039a900500655030382c186101740d00000500c0010304108001148086460213020341300311001c8820506d0310852281c51619698010000b80980c286581001c059000301d079030b030b04540201c0c507600c9210503886608050814100000520400030b05002041240c0070140e83c9052a403012507a040b44d81000507940c1500440c081e102070b44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 523091582 1250 523090332 523090367
    0x703081b0c030c16150f180812190804050618030f0409020d0609060f090b0a0807080d0e0a060e0909010605120a02033003091c11061b1801 61
    0x407103c074001008107110920307841440c0000c0030551140741e8243c04a01e801080d101048180142d20010360194040d195200912010005455940c2d681681407891189030901110000200902039018500c686000c011181c80c009129150665a20b80e403000c000d46814080707003005855111100b4104100c81c041244000d483d034445030b90700850b401a4001e04540d90b01c240c04e1540c00b0075030940c179101b51000c8600032540180c271a03180c114840300070300c041c1c1c05143c1c07c140f40783c5004c2507000007080309400400c480340c000c0c161a5081400140b601c0b680c40c004d01d00c0344180032406c014450703100d4018000740600702d85c045a1625002c5070309004000304d030701c07e6400c80c1c07800d47c62203401c580129800600074020780945e50344c21031110001004100402d120a08442c0340e84082041030b204001031540180d03140c0807154801c00c4006540d075140b62002c07004000070f8801c0300c400c0d00c00805209051b04542c0e2801081c904520740e9650344043c0c00707800f40b0040c14102072448002240c0c81842c144882800c1b00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 523092832 1250 523091582 523091587
    0x1b0303120c071a0411010212090f01020c040905071a03070c0303020d2903010f021612020709090b010f060201020307021b180f07141608032805040201080109020703081b0c03 76
    0x801000952800132a82501c0e241c80581c100300c901c1d4000700308105441c080c68211460014054100884045600c0d5400d0451140103035400c0341b91241d00c0b800ca0402c0c000c50040900c1407070018400d03e000b08070b01c13000400100901c00e0164464000c00240941517160a003d40c4480c40740702040024003090b44182c5400c02e40c12011114100303201005041e54000342c0c0207210101a801d184000c0e84655182504191048400030011402d1210074404443c50361040c0c1c2d0003140d48600b46015182001810354618103224010451164903022000040c070b010700080d801d40c54800740194807008015000c800406901202c5e1802d503032184880c0c00e25100402c03a9507164202400c0300c2002c078000321550004544134482080c17504a80005880000301a01c0400500e0001d684e50040950406400400724019400b403000c038204583c000c03d20f1180640900095031316241c000100b0903034041c0e1206003400d01c100444400f00f41e010083c141d10038088044941104008044500d4901c5220070284150201 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 523094082 1250 523092832 523092863
    0x4021806030f07020609030c060f0604090b0a0f06060f1205040c170102030a0c03052806050409050a060c030501060e060c03070503210c041211040605211b0303120c07 73
    0x494090328002c01c43c69088814136030329040b007940c1d0b0f4401c42d03404c20140d03030006002603c03000411035059400031001e080801d8004480d524000c43d841c090b26602c03005500c469103144241c0f0148030340c030300030041740c9131409210850003005007403541500300150305d0544403c0060103000700c4c5034401e030041200d141032035082c2d9410101203000703410540304a803100d800c05050715a1144640501c9000703404109a02d1307041c1e800401b60003882010301d80c20b0002d10b51100300009050380c89228025115000c0c00107400303c5045494144100d40001074144149071418006000385a445205034042400648d104cc0e80ca17000c000c01141b440c081c038030005160344400214007000c0003000c1c600c01e00c940c50002070620300b6122100591080e000d039004190b0f40081c1e8a01040100b800a0300005108501910000d80c442c0c4500124003031080f10f401c81c0c203c0780402140c4600f5040d0030040a46907411590300c089010410030700107500e03442246190611910203101080c0792114603021141142d90004451001005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 523095332 1250 523094082 523094101
    0x40b060313140c060306010c0f020301180b1b031503030403120c0b101401051809010303031b050c030405060f040e040609030f0c120f020a0203010203091606090806060402180603 78
    0x140d2070021200700d9030a00d5620782603074000507282c8141a0041c90241141d13948001121100c0c4000343c01c3d241946c010200d01e01584003072151401c94801da500c075403440744480c1000724501c0d10203050a80f0903070b48250f40b005602c0060054035000a03450390407610040303046d40003034518081c2c0c2e0030140c81c50035240503038604650049040210700b8402d5850040c145c0c0c07a4901c01032540014131a021160b0000f26904400c2e41c0320310b000304603e0701e1503e02e56144900c0040403d030814400d80013140480d994406c040003135000c5c044d003036002a03000d140844c90700c100358115640320b0085100b854001d8078007240c086074003201c010a60b4080c180b2009004498582070030840040c000c9008282d02241c500a4041d502c0c034403400e101c8046a80100200f807038400c1448040f64400343c040349141c1107005000321032005a40c203000550090344039800610307003502c1003294612800742030b901920030302440d1982000301d0400414055802103085030f0040e04c8030780d69161030100003103070b01507030b0b0b80144000700f04950500c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 523096582 1250 523095332 523095361
    0x30f15010207030b090321040b070309060615080402040612021c061b0905090708061f02010605130b03060f07020a0b071202071a0a0e0304140613150807021501090902040b0603 77
    0x401000d032081c03400c2c0414500980e440000d6030060300700d60310200095144bd000e0b03000b044456111b03c0e4001803142c1c0e42d0700424142c1e5210426640052450418042985028000c000c09030150055446203000710754001169602c01980d809002c0b0070703021109060008030b91009021149410b400c034447c410000e80201400407070f00034644203403141004a00c0d43c501c241d041c132f0311038440030b401040300d0074400b0401510b0000701349075202150340781c040226494035465480d10000301d1082c4040782d240040d20401d414a0002407001c038585031810700700221581d0010b110b640b41c44e00040030502c1d549503003d00711202100706400c154818000644c00c82040024410901c00791050703a501c2c1c1c895210350381c1400989044002201d001e61080c0070500219001d02c2c3c0c0300070790001c01098140f0700a259070314841e2140099210340c1c0304540001d812403519401001107a0300850390b2001e03194140401c40300c205000018016448802c3d178402540085407502d038004000300c0c4c401000d0035180d00d0140d90492124 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 523097832 1250 523096582 523096597
    0xf0b04080114160e030a080a170a050411091e13050f010b030c040b01170421021c0807050c0106030b1005030304032d150605040e03030f15010207030b0903 68
    0x15860015070501030a1802c410b0b50040342c00d5034190300e000d92010402c807822900c00c031107182d05009940303000c0002a419002000758401302d03180e40c0c4058628001c0c0c0b2180200042c4102e00150a14040000061840341c00c0b101c0781c5011601d2420320f444203602100131103100f26103080e041b0074140612040310080c0e00d02920051027201260400d42c00b2030041401ea0702c1c210405a0198802e541c0740185107001d411840c6900010300d015418812041c1500b100c07808291020303210440444410081d0314070007201c100884030f0340d000405400702d100d6002e4200c1a1070036480000c00c20341801141171035204208a62002107803a009000361a12070401c07460b948400d44a043c4904c40200c0005030707d080200030f5504580e002221007091b42c07065440d885400900030f1b02841c0c6421a40444000541c541c4400c04d85c1d00210100050070f28103000900c0203c2d051206184141e500078410803a8204504101d180e002c0c0d0541d61a0708040081d800503450081c480e040184103122110401a001c0400006058038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 523099082 1250 523097832 523097849
    0x190e0a0f061d010b0d021c0c0206130b1504020c01020a02070f06020d08011e05030a0807060507030204080a020d0206130e15010918053408010e09190503040f0b04 71
    0x969a41c140035408041d0001402d0303240700d502004105203d625030181610482c901d80c05468032035005460250b021340840483c0c1d40740c0d41d0300c1c0040e04180e41044441e91003c501a07c50711303444d030a9244c080c40768000800504200408041d8140300c1d840341c0d010b41f030054800d4070007991620003240300071f0f48518050290085661004000103000e510001d0074080c601070390745400a0903424590207403088003c128000314800c1500c030b00010380d034900300080c5030300300c6c0240300081c0c0381d0010349403c900fa15000b9001108240c0180014060f4140208220446c15030480c0d0b004660032651010401c1070040710a021300380c0715035a5000136030b00f1008000c14441e00c0040860354050004400544e00042c00740215541490f44801c1001c042003075600c15500010702a120407041004100a03154200e40380304d07801e00803121619044102d9030130282c1140542051980204103240c0313010007a030345115580402010403181f8070407009200050003128081d1a00218a1000c1a22041400d43c0c030f42c00380c402e0451 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 523100332 1250 523099082 523099091
    0x4140103080304060b030705010509060c210c15070909050601090e0a09171207140405130605040b030f2104050306040501091a0708070e190e191802190e0a0f 69
    0x7400c0c6070114287c419100161a41c0f81850006004e00c60603030040c1408000031320030050b039911101c4800203c5086005c0c0240b51541d1000e02016071824952408902d03180700e0081d0f800d1041442d00206502c00b038402c803942c000b400384d460100484072645140d00c9001c02071101020b00010a5407074000350b8503240580722203218106900140711903403042800c106846030303411000c540124440d0b80c00f0004440c15542c924200341c0c4500c009020b005403a00da46800941c1c860f000c01c100e0409010b6440d0b00d220840203007000a00e08400300d030300d07034000d200140d60007601c40c0b601c06103c541d41c40c2a0760240c2009800c640307452030949001c500030000e90406607007204402032404056644a207203140701da0b10580d02e82e40309441e91001661062103510305e40d54020f03e41c2c0880d04004452800c000000c0a4410300c1d0082401c01581050030f8403400201c01840e141007004441510141d109a0855141d050300c05448401c111003c8482024481d00040c0710880b11303a090100f4041c10390880310104000072420031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 523101582 1250 523100332 523100351
    0x118050318030601140f010c05030a02060114060702030d0e0d0606090b011407080f1809090109030f1d0d1407030602090406050604240207080d05070b07030e030f07020414010308030406 81
    0x41e0f680c202446006910464521410014200400509415103040c180003500300040d542d25400d6800c50740020005034410401081101c41031800c007800040c00b5a11030740741c01890340200707454036841200c100a100428545807800c0e150711003600700f001d82050341007280780d0715002d120b000340003d802054005030704401c0c9100c080c0780360803c59a400d40c0c0000900d1604860345400c000711b4100c000b02000581400fa03100740c00340c0b01c01000610a61280000150301040c61070090060000a4004800c002643c01e50075031920400c1200c8501003000c5400302d100304440c1c901600300246014071090580071b00c040003c108811600500002c0c00210303000d100d140c1e00d4000780320060081e842450307a00c0440c0b045040510240708419801c1855a1040c0c0718142d440752146407410380b17056401000210001440c0c3c040c0402e00c110140c01502915040c410901c0e0045002d50364000c2151a059500c4001800c1c0304550341c80d03010040541180d5030002041da502d003415002d503002200d05230f03030f0345081030001d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 523102832 1250 523101582 523101589
    0x40c180905070b04210201180306051605160b1f0602071403030702010f0c1713060e0402070f080c070e0a0603050d03140c090402120f180c0112020c0118050318 70
    0x1541a21500d0509405159a626000c1d25005d02c1c0c40083c2c0c1400080490604841c08485105010714090103012401c1d051402c0caa021015604040604100301480000b108510218042140c69007054510100741c40f0b40b01d5040e0f00b65130610300403400c0018000d000516a070080741c031000f195064202c1007038055001c0107250320b81c452040d0090000f80ea60050407a001c1c01242c1066a0301e000c2d000422038003500c1c040726505588940a4000050306440c01000300581c0084030318a4864151401d50800d10a9600c40000e02c110500c0105400350220300e4181e00002040300300020302910081403c7c42c1002051071004200354041a60319000718a406500e503406070080c1a8185c03103840d00e06859980b200180186d07a00f00e4424a944140c007004000180301e0704416a602401000303800c2019804d007540354820010446000d89071507082820000516038203c070250365282d85621001d80c0c1c810381000942d0049c03030040c0458101c1d0502140702802d11400001410030202903100c040031001040080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 523104082 1250 523102832 523102837
    0x160b060a0819080a0e0d0b060a0506040b0301060e030a06051303080a0504030f030c02010b03120d05011a0301031704120507030501110c19030201061809060605060f030f040c180905070b 81
    0x140c942c60103960807890006440940104010145481c044550b0a52107000070071125510300160743c00c449100500001d0320f4008886001044111402840c052510b0290b40e01804144611401d02040080400c001d440c10b001c0c000c0c400d13078400d0080020303207001e042a03241e8540c008000d030002000000002c003020700300d00c20a4003550b015110904c007183c41000c00c5001c3c0141c02d41c050115521080050b039191001c0140f088401c4440800c5c03611038040121030000c551050748050200d10078403240e1070784a8203540c1100d0540c0e8106120300202c6005624a50481c86540c0c0851a0082410a0b00091007400b18411003500d100c0c100a101c04104a04949402d0299414a401c180c01091500300310060203031805000c2d900c24000800c0056484c040c070300d04030f003542c110740019944a100e20410401c041c81954042c002c222201030400a141600c002035020007404181100182004030b0b0610034400320142c0100315001c800001030b05045560f102a0510300021038103442541c80219070401d50350305 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 523105332 1250 523104082 523104103
    0x60103110f0105090909030d020c0715020a0b01140a0e0705070506060130060b030f1006030513080913051311120606060307030608030307050a02100902061905160b060a08 75
    0x12614181340744603042008104000e406030440344010230000740d60034a540081c0160003807440280c482e40e4603006040c3c4910034452100b00454004c150140000b42d4040e11040c15285d00d41401c01003803000c0c0380460902da01c1500480ca00c42a50740801c56030329400300060080911480544450392109401503d0540088106001450040c0d5030300311b4071402c100c5000015500c1100201e911a80d03140501c1c0c03107a000b034402200304a1142c0802000400380106040240458a404c205916180000d02c0400140c81c2d0010301e10400040c40c85019514014241130400000340b01b08590b061144030001c100a01640131520545c540103154900d00e021060903080b082c0000103824580e40319000c20040b9030004000b201456500c02d07000c20030680c100080c5110310505d44a00d6515144264003a180460b002d10800c01c80d42055034580041c4c44100c00da869042c0e0402182200ba03c140a0a0340c02d4015100d10100c03000b1403035005400d000510801900820041d00c100402d65216036503280c51b00b48012 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 523106582 1250 523105332 523105337
    0x161b0807240c02130e0109080a0906021c120b01180b03060a14030604020d0503070c08030405040f1503060b031014010e070c0f0206030709030219080f010924061205060103110f01 78
    0x60304c0c4001300a0b50007810030106020000175070350341c01d81d99064030364101c0509500041c20200b82800703125010424035450a00d41255480d90002e042c0e0020001c0c50380c04c1600c4004e503120499003000b0390040c50240014040c9005001286494941c00c030b055410454282d44a901215400507042c05482408a88290042c000e8509641d9517024000c9000c807807802199644030801100c004507103070341c1901c405001e8000255076a50301e00002c200a80e00c0ca030510340000c0307280c105042004142e04042e00c04590b030040000c507007007881c0c00009080281c000091000c0380c0c146040c40c2c0404da03406070359a051720380f1005440180c1e2a10f00044910900c80c8034000d0590941c81c0001005d803a014000d07503800642032a040741443d031207a002c02c2c2d01c040c0815882502b0140c4035800d0040080501c801612483c40c0c0380204445121a250111242e05c0901c00c51989005161021803600080d0040805040c007544000201043d1385000e59488600340310642d80e1710f0060303118002e82e251190307410b031070100140d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 523107832 1250 523106582 523106599
    0x2102040317031302030d1101050f070e010e2d040c08091906021306020609011a0303040e0a0f020c070608010501030b181005030d02010b04060b161b0807240c02 70
    0x1c442484440e4800740000c0701c0030000042d0a0016501003000d11101c0601d9914403100b100c0c400481070035110301901801c030081040c2c1c100215150700500c0340210400c24a060486283d094000c6100030b00103800c50340c51b01841c84c10032003560488110316281c14074159801c2003009030716807080340c00d0300c81641d40001036040b0201c03101840d2800390040f96414000c070001841c004051058001c004510303444500542c1084c003c2001203602071091469044070b030301c030441c0282001c50000c1d4a9214500496071000900c9021480a41499201c0110f000d48918110750311740129002c20f030760783c2d820720420000403006800894079522038098003d0035040500108800d104010701d1600c41030f00208000c00000c0e20341400103650380c0810003004031801503000040d12520410910050300d801d80c01189001c0c004004182c2092210254810350981000440503034000301c0000804490055000039651301c2200780100782ea801c0d49205000140b0f04219a45070b500b8207040917030340358070407081c081e5114040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 523109082 1250 523107832 523107863
    0x50405060619050a180b030a020102030a03020f04080109050a140d020703060b030a0510021806030103051504050a080c070e090d02070314070306060305100518060a0b150a21020403 79
    0x200918010320041c0c80002c01910782010640704070f110350200c0c2149840010081c517100e042d20640c0501042900030b480284807940010307581e44103080700841010360004070181002c0c4c900c03081d50040d2422900074000384044c3c0c1022a42d40080c41d1098540c0914002201103908001443d141801ca6540141038039501d581c41d42c0006068008031180c05000f6a610100010810700808010a80443c00140c582c0f04608851002c1041907210343d0149208000500210b81d0000b2241c1585d08603140d81c40e0695150300e007503810480208401400e801c004180c4184500010030340300d0954001001e25100c55a0f178008040c0d031510001c41c1600135803c03010082c4003080c0e0011a0505c007803261001c407a01503a4a65441d01240c1040d8015540c1c2d40004070443c904031084d014041c4c214085240c1100b00c0000e640d51643c9410000c0c003000c4540ba42c0b0b00c8820101d0b1140240411250340b282241510b03000201009480e0014407070104880c0c0200d030840e5225201c4600c00e07901030700d802040b0346114800 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 523110332 1250 523109082 523109089
    0xb0c0d17190e0d120e010b0d0204020d110301090504020102010f06270e0d020307020a3302190503090a08060106051b010216050a0501050606030112061e0c090302030f010504050606 79
    0x45103038a141800d41c6584110021030707010041851107080f556a0f03410040f101040c000e089400203844010184d043c082c0c201e6580c0c6c0e50b4810142116011600140d881030551a0300d002020000e504030006031001c000051401000c7d0300040c8540e000780c0091009510720070310b100c02c940c010b018a1018814100741d86405000d4030741a141185031101c400186459108103841c81c01c1c0c640e81c1c0c104016400012448110b00f0302c00c1440340282138075800c0280c0722520701240c41915a01100202c540f690000940160314401c1010f610001880103800489000c103041680d1030754003141449000d011300341000690300d500001c40504171103042d6a917074101030b02400d0301441507980201e8110159003c1c8401c0f100d800e0360807090764189200384000c0940d801c1c107141181c01c0d00c3c070041c00244681d00034001045031444000f0320b107070001d0b0301410009000700240c681003002c5204040da158501d2800c0b26055040350003030020301c01e990084084450822440c042c1d20309840f8200c80043c03540d0405400301c0d2040c02c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 523111582 1250 523110332 523110361
    0x3040b06030d0912110306131709310504030e0301050708010e150406030b0a1b021b040b03031c050a181a040807060504050303060a051f1809060b0c0d17 67
    0xe00c80e801c1032178400344050001707143c1042603400d00c1191010f0b581c0802009548500f4003012880982c59909248013080040d0006155101d0211210b2189401c00c030503540760b9400c22007001845004000310300b005c2c180103001d403090003000d5000b5843c060206104502a240d0340303040b9100c1506900c400d944a001c0400080034206049810986403c0088002100e0800e881c1c4141c000d0500004c00152850207c4d0001800c541c0c81c1e02503401c00807144d40660885103113071a0200050f03c02041c2c004109003c24a503118520403082c4015100305688008082d5402c190301603014071005001c0300b10901e1042c500d0507200c1c20700514952102e1500401d00d50b0484e492a8024003e0700c4917424505552940c0d0140c550403201110160400410070056103810b4000001420058481410149100d01041c420388007444a1400b407201002c0c2c0320082030070802d4044003405000c0c00500c016507942c010540d4581104050021501411055280fa0340c82110030101a14105a801e4116265128440d00a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 523112832 1250 523111582 523111619
    0x80411060c10110702030115060207031b0905040f030e1903060b15130e0f07170a0f0c080f010b090306040807020402210910060b18131103040b06030d09 67
    0x502807280361251002c010300c90100d00c00c0e081d90490755562040d104040c21035150300703146800c1007100c0c4024840385070300090766000d9903803200d0a40b03444503030a921044041002d0b4080d191560400040204210400007001d1241344603850389540d55020408104041c5040320400c80510140c02082022410940015400c00c4c4050020580c40d171180c40c0d0030350564007440100d550880e5041080046004010009510a856240f10f0402d405e046600511502e001089460035041c5d01c80400c040031007a502c8900302c1280d809040101072101c54028040d418115804461050b82200000b1084082b10444401031401005084075548507a9000300c00e0b085141c0c240d03005582800a42500040c81c40800340b511006640300c0b50034a0440b204c18036140d1190f607812440c6040c070804202e001134030030542d900304164681e40d40d000941c01d00410820f4001c4c600103044542400701a00790300c104a00118041c5000c2c07040c034400c82d40c5442c24550f0300d2041c181090001103028001300a103004a842e46c1510 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 523114082 1250 523112832 523112857
    0x5010e0105030d1815050408070b040b0f0711060307030c09090c0e10052101290a0c02030f1b12070614180904060506031005010f1e09020c010204090c08041106 70
    0x30703444582e805c5000150790130503c081603000070705109840c02040302d48010b1010340d100e6440e09060050024080c0101c00c00c5201c2010701040302010821700c0e418aa0200c0340290640340c580c41c0410008000d8200c21410902240c0da103e80415014414000d01c43c4c64070071510755140c445004410300c030030348101e00c14110800c02d00780617506034000105012008650401150040c039410006030b00c45900401c03a44803203010040109220f148140420340e80640c48030700301105c05d40e003980003003800c100100070204203d02500302c00c62004200551000c040050a9a00d02220b0a21042050351450980079201c045040040c00404d20f0b01620001d005240c3c40603400741c2001c0203032000c03600d204c0090300c003224029100c404024a500b820007880001c18078040d018000c551500e0302514000790745003d46400222a00188a0641c0700242c84400400341208210f5a49219040d014000e41080c0242a1002d04000c1c00b03c01481c803070000507000f203802030a2144032008100401c0072690145810b13540713 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 523115332 1250 523114082 523114127
    0xb090408071707050a06050106020d1e170f011505120c030a0207060c1706011b11210a0201090b0a020303060d050c0604060203120c160f05010b091905010e0105030d 72
    0x24100c102d0041c0c410b036440b4900800a462040c6848070985605801000444d0f0104420420440d800700b0031507806454070301c0032010550000001c81d00d888100d42c10000d550003074070030710a111180101c0c0e18101d80401340110326800c905901210107104000402e41c801e1050004a516000d40d00000c540100941e80014030b40a1542c4e901400d4422402c20b0402086c00040d54a4070800c0306031010794407840919081c07019128041e410a02d860442c1c0c400b901b25850a030080d8941e44444070600c20302850184120022030110f56010303640e9008036422030004400c4140051502c004000b503503903080c8a900035600710303030320a01802030707080c590081039840e4401c04a82c511035840f000c0040c0f000c2c01455025659841c01d5000d008003034940a080740b20001c00c108101d9456030b060968050702640d004050001c1d0401a0070444e014103031541100d60301c03200a03c1031101c0006008502d0550380c41000e8140010f03070342c6c0c2c191559614024840e068050704047c02e102c40092040b181d00c03050b0300c00d0061806 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 523116582 1250 523115332 523115363
    0x9180105010c031b021f03060e13060e2401081c080a0e0c0a060201021803070e070f0c06060e010501110606240715020913020406020703020618040912120b09040807 72
    0xd40001b0021084062401c1c50340f0300e0820a5890b010310006490388800074089411705501400403440f01c213202919055850b08104024081800090718055160848040c503189a00ea1180c48070300a2061808600c100802c04000c13404c060f0600c4001221034440100a944000d000c0c0c000e4144d1502e04021405550606041d6542c0c8070700803005040c0681c0016100ea4094108802030783c84010410b02c60350242d10108140020840c070b0726070040344c5107050061613201c08829240ea4011481c001d211a040040216a81034964142030407284240d03280314501f80c030740d801e294403800c0540304160445418003000c5850112500380c025000c41d0f845d22185040030584036a4481d0800f002c402d1421900004c1d4a001b5240c0702820004008035880110325041c0750110196951804e440024020100840e00120031220900300c003041a1000d003044c0030402d00c0e0b140000549607000d4a450225000e007180030960485407107592803070030b4042c045005646860300c480001e5045404200c501a0040001c04c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 523117832 1250 523116582 523116589
    0x6120212100509030315180a020a050f040602030703030b09090a08031b0c0a0b1f1503140406051b0c0709110405100801062d030f0213030809180105010c031b02 70
    0xe0f02c0741ea065800f0715280e0512049007155030180c5c640161080b9520b84020801c900540010342d0041e8503001e0059030386c0ca41001c2038074540900c18240c0514440454001145078000c40203201c0b10344256001c11000786444100081d040b806c0d1070542e12a40462202000101220025034108840310003000c800711101012000960161417059255004202080100419041d64540040c48441d041c003c100525006da00d4442862103412012000300010301c3c1036078040c1d84a49034498808074110494509828044054813054079540e07040e82c04420042c150108010a4503a541904005040c43c11701c1c00c2071585c0644400b92101c0c070502002c1000180980d070300310b00c0310794211094885603229031411801520307000640024050040e00b0b82d441c40d2241c038400030803245115090070006820803583c04400002d01500004c100c42400c23100f408000d11403001c025203c0a4011541d41052881c41084001034036000e100f0340d0b01142036603e22600090280b00420000040b1303240109107641145c000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 523119082 1250 523117832 523117841
    0xc07030c1b080708071202180403090510020102120703020f0702040915021612082e080d090311030a05030714010f050c2208030405010c08040803040b19030612021210 73
    0x80307400b942c8450400c002a1005001802c01000e0601800c250000700da00440c0720854180e249a403ca40f60b1800103003090302441d140340c0506809804480d000c50602d4000e0b00035440054142c406109241c00a84030520034021200c2101c034180550741094034541c00d02015107075800044030740300b0504403d0340600d038282c0701a1561144004e5880c560152a0070000c008858001420040010180c100700300c40500c00b08491000300c5c900074841c0d80b00d4007044409136071b8201d0b0f0040c420034000c0003131140c94145d04c40304003c01d0b00e00490072a4000720b0038100b007607039601d000000107245400c00e0119070080391014003282045c5010000120700840f451005604550301102c4542060750041504043c00905001619032896005a2209290300301031a0b25a00c3c080e5228440c10004d02c2040b002c1004441da00761401003060f481200d403590b480b011400f4291308181e900c02c20419800d054140440d00c2801284111001c9172400412100d0b160284903130710315204840c1a06200c1d041c1c109800000c0c030300c207 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 523120332 1250 523119082 523119089
    0xb12010c0216140607080a111617071503050910060f090b0f1302090604030b0f09010e120d021e0310080c030a030212090411030f01030c0603050c07030c1b 68
    0x506000340803648101d6005a2640200504810840f07a1110a458820440b80956008034180740c51341801141100c06003a48508002140500909031070404043c1100c0400d070741c41c100816001c201003520040d500c03545442407516180d400543c501c00d440c000e40c0031701d40002c0d902041d500200000304e10582a00c4565025004980c0030210070000c6500a125210185a04842944142c0035002c001080c05010724181e1101590001300071800e0342c3c0781d0048600035a4000401802460b240c01043c521030380850b40c4858039401e10403201050800410440750843c00e91041c5818500ba4030940307402508100ba1410400a0720f0308810344140c00b40b00079511500060b041c83c003c1e01c0c01c02845070304100345402d0306e074060751007100760600103600864a140301d5a0308103144e0342c481038406c000901810b083e0182050218001090000c40b2a41888440c1628003074241c0800c00396807a1011000c80300c08649142c9000c600703000c400c4c0064450003200c0c0c2c49901811141b40100c03c2e1100050b14125242c0c07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 523121582 1250 523120332 523120337
    0x1090e07120c173403020304060b0a03120e0406030803011203020c2403090c09130605011208030a09030e03010204090603061b0c2904200f01020706030b12010c 70
    0x80c04000c1c102950207a8501581a490114040540803002d0043c066016105412082d903c802c0f4000c80003d425420040c07400c3c54540c50011480480050020351090754240c40d4103042000c422658104501c80900300c9032310800300b440d20030300b0403401c403180d003a8a198103501170303200c1ba4000041010070025501800c1840c6c01101c0c140e00514000c0d1400c899500300c0ea014ad8003c85110031002c80d502007942c2d02c3c849031600a43d980d921030904c1030601c040d0050301540000c1312402c0c00580110754007040d40441c4501400c11a070790300e44501e48042d2618500092441b80c003000002c00c0207034660400f4010b28442d00b043c0011490000c006030982c3c000e504100e00503a600c040810500400d030241043e03039440c40e00c1100038001c105500800790002d0306009001c41409020b5a40c007021081c07407501480552105a024134100352500200140100d85c9801044106480744009464010119040c40c10305030020040306160140a03070281400000390760703211040b46881c15604800780110f060b04021035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 523122832 1250 523121582 523121597
    0x1e090712091a1f1203030e0d05030106080f010509061c051c030c090803090d0201050705120301032f090709030212030a0206010e04080901080c0d021204021f0e0d0201090e07 76
    0x5890081d5034860041900804400790a11400c0e2020442c1d001800c1d126040b1030001390a4141c24242c1c0640a42840d0510502c2042d42000803644d000300510b0580c0d65590700c96070b4503141c4a03d84000392a080c01490760041e4144042140b0b8a810307480b01103070021000208040c9041074072100d080400840b0b90130100d41e070701001e054185500d4850b044500f80c040c1402170019081000342541d1340280020316005022520424055a0046040e02c40040e4000110740e4101140e02c80030703034903410a11044a03801c000c071584d6130740090035600c0c2880e85042e9030850842d83e01c00c81c2c200040000003a1030b0b03030207005605001201617212000d2101e1a404130000540c0e4446440070000d00d0844160300c2400d1a452800c14071000607140e004803107001030309103804070081d00c0c4c1035020040780c8129056010364510015806460b240c0d20450310740729070300803a454140010f00b40e11403594000f02c07101c800c000400e1120544154a0800203004020380107243c4504c545498000c640f0714101c09941420103d15039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 523124082 1250 523122832 523122863
    0x12070e06120a050d020d26070c080a0507110405010308071115070305120604090512071506080a03140a0929070b010f080c0a09020a03091506050f1e09071209 69
    0x4002400c0b01480f60302d81560240c0f07194404100b030100801c54004821060004603d105116224841275031790094042540d420003021b024200d9030214104903114004d032100c0054501d824404e041c102d9030070907030301481c100c1240c0d2680071050f0b04050310384d030000c003252601003080c200e0000780851510076101c4543c2c4039007000c503100590000600851055090110120000f00d003c80e505240c60410b00c10192546054500050400011110400d000749003150000d0390703803000a110700c02203004e51140050400d0301c408625040c825010010003080410104002502c4c0e042c40444100070a00401d440903449032607602001d80c0b040c40182c1c1d0300d050788001403040070f4040075500c0040000304004d181586117203002c1289084103215000031654049085002280260085046c0765031104003035222800000340000100600e0003818001e00391440ca9901d00e0401d12000c00c14005100e06850741303030110301d00700604150f005065508000c00840800d03024815401042d100030f1040c80400300c07a895 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 523125332 1250 523124082 523124087
    0x301090207200d03120e0d08071e0203041401032c060106050405090a020c010b100302041d01081b280302041406010c020907170c0405030c12070e06120a050d 69
    0x280240c2e10300c142c01030800380402c5950350a0b43d180351960b060809004510250008400520700c01a654040703000b241c2402181c1c0b540709109602c0b0320495228182c00c18825a14903002480c0118400c015034400c100074002d01c485030b620f42d030006c60145000300300f580fa05034003400b031864542c1c294203441a121684401c581400e000060140025283c014101850300000132520140074203d40c03003082e80003e101000b0003084d00108070085003d41000c140c50190f98001300294030032304ca245060005460b03515044001403031010b040368551802481104084c000e0400c2e10640b10a09680c0083c2c045440141301d20090200b0a0468540c1c50f1a001c6910398014802500d2500450060541c2c495040055a13178000c2d0843d46002c2e019148d521482e0f441d0501920100c4010884054100c04202000030b48080d01c0c1c01081600c00075004d88580010400c14800950031148c0e10243c590482d150038441e1440c100c01042d070018000701803404540c03803204024101b00c100081a240d6410855803007400f01d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 523126582 1250 523125332 523125353
    0x20a120509130609091103120a0c02041407181203090e33091b1603091805090c06030c2b0c0509040c1d06070807020a0e04151a09100b0301090207 64
    0x54047d400341041080c0e140c3c2950300e9100f4507021405104039013001c04150b4650358403109041c490100748000b24107000802505214044050f01030f003d00000c0d000c00c22050f5944428091940350711101441420000640d0308410000c01100b8a1503030103103900901081120310501025115005030000000e26050000416008082055074800105000359801e4000111070282901c642a00104201d518040307500781080d0784041070840300b41c1103207191889a0b0b0710407405050054119010104100e0a1140070301044642000c200010700000725003001441c070745604800c8802910740804410b02154044800c040249c0000900200d401c5015061502c24040c2c3c00210341051014400c5003400050b042400d02500740c0038100206031201000b1550081c0c6216a41c0181103030f81e0309450314920907407040110b4041c0e40303c0c40503090742600c0e40c6a031310484100300c4200b00c0003000440d0503000c0c0320070400c01429001c500b01c90700354001040148038001e540070701007000340560313104010304003602c1c0c58 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 523127832 1250 523126582 523126613
    0x3210501030b160918090203070b03011412070501020d110c0a0603050a1a0609060a0926190b0406050403020f06010306020306030d140a181505070210020a12050913060909 75
    0x445400c0c0140a032805044d00000c2c121005d17480400c0890740c41c40440d007002c020740c3c8010349651010001050100601e907803000500d5007a1042c4903400c1400714119919109c500c0b03414056044031440c404440c2c0300302444425071400404441a114015020616401080c2d000400007691b41c0c06203d1180500d0080b40c0410803004c0443d90903660080018003540b154056441c45482c1c00034403002860302400c0100002c020094101c041c14074000309001c14440c1400040001d030280c0d1040380801c0074244015a6045d4105601c0e04290b500c07076407400020030000d802602980b203960200c858400e0308016040c041c41c4203030f03030144c0c036410040249441c000c3c1d0310841009124110350901c880b6200d410540d12280c07050300d003030703a10520b0302441e0000014098121014660300c0d80210301d0619082401003100b02d1099800c2d80303c84040d24012a120319903600f00510901e140c00c917600340c6902c5130000d4500604002c140008900003046028100c1c0c000ea485500150780300c4851409211103174100a040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 523129082 1250 523127832 523127837
    0x20f04020c0a050303091f2a0e030102071505061909020a110d02100b030d12050a060b0a031509061401030f0e0703110906010809071a040f06031505040b01090303210501030b16 77
    0x30100f00300f2300e080c0d0310303a142000300c11418600c0001d002103200300744100c84181c014000b15070310442802e24400551014900c440624286000b0417640d0414510780241c038035600c80013110300380c100364006010754415030710f40c420803011280c54001e01d0410f11003008495a1900101500241070180105882c03001081d01c0c482c2d004841c0c25001b0542103460710b8452000c048000900340d4a0340c8061000304050b40188441c1500415030b100039541580c0214140c80b074082c10282c1c0141e40d042e07042c080d02e03a03502943c030608603242100c1c030301540241c000881c070304418040840d5901c1c801096502d4904158020b480b1407914208100c0780303003050b011668201c50280782c0041c02e49403000740700d5a07400c3c1610855a0341140c104507106100e0044d01078401415030101554100d030358452000b4007404112101d00d1100040c4c48000507986031920584101c400d040c0c41d100c5a961039a1025640c5c15007604208246080c01ca4222200a03214460b6038041c6100d00e607114074509003030700c0c20065140800bc98505 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 523130332 1250 523129082 523129091
    0x9090b0c09060a080901090b13210e060703090b3c09010804050307021509040c0c02220b060301030b04050f010903080c1b010501090b120a020f04020c0a050303091f 72
    0x4182c0c940c0001c581203c00740d41003030707201601d80e500c8450040c01503045c05010070a141090140c03c480591038403402d14090300b4961011550074409034400d400500140b030110b59804000d080c1c600f092006400c055000b0700300711854560b500b2a100040c0c1c4040710700f080e00c101c564803842d00c0c500845500920758079440080210000100022001071041c0b40400f41400000e100241c2040780400441d0407940d800341a42c8005448040c604050342c01c60b4103190300c0343d401c0886807072215104a02c5051100c2e002404c0710714025401407903590040c520150582e469407540b0701013106440300c00085000354030480e0449040d1034036003003460034015003501a240d607904089842c1d0209901c030084903040721404400075038500a0240c1d0403004081e8881594180d400c040c000210010790740c0c4200d0300310303d082e65800c02456180d00840e45600d81100002d5000c500401c4940803420144d01514078040203404403035020070785441e0a440c40c0c05c102e42c484001c1e0310440a803903640160007a60f039041c0300e04100910 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 523131582 1250 523130332 523130347
    0xa29040c0f080318120304090912030c08091c05090a030b0405060c070b010302090c0c0f1609090308130c080f011505040614040b0a051e031203070c0809041509090b0c 73
    0x1026841135a034558494010107a40c4c5040c1c0b50184201ca00810381942c1c101700c03688852070190603000c44842d59002192a1040c4c1d02c1e151806061450b106080500241005095210b14801c01e807480c0c01460382000024001c0140d152150411000038500a401c1c0505600c1c0030700c0c0c076500d48030004080c14042c9109120744000140c10000480c152681112420426a5011710021140c05402c18822862040081060a603c0042201c2c40c000042d1800c80000d180c444200c541030b83d20711080103001500c1c0740b00056041c00300030f2060208a1051207641c1d820f0b59101419441d0000c070064480e902c0c1d40d134080c1070007986003c3c1814030033030409807001c0c080076180144142c0c0310488004418082c0c0d4680450b1450396885054520280a00620756204d103007800d07050111669106084038040d2013204400240030a030703903090fa0301c185459920165081041d44e9603212681003800c490340c200340c403010141d0707191107207203070807000b8142800000a0700b1540b403c02da4448580072b00203038256a000c00400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 523132832 1250 523131582 523131607
    0x3050d0903020616030e0901030f050d0201050c0702040b0d06050c0307030b0a0e06010c2604030b06040b031e0a17030601020c0901180225031806110a29040c0f0803 72
    0x19a500131410003a00e54202181c1819a0090b9094002561195550380040204825242c03965401c0d809142164608002003e00b1380c200e0b94155003180d0000b1007882904018a400d4004000d000b40c00f074080c2d54141c4190b950308040d52815208041c0303a0714040108990242d2601c20b1100c42c4a04541006000d031900351000100e0700040c2020f8100b0480b41d40100c1400403079501140d8411071070300d95a41c0100c0c92071101c1c2e11a00680400c45400c900b0324080f480600d4903002e601d180b648000c0140140d0b088104054614003170b07203002d2201c2800303000c0980300401d00c03400c00491840303012180c1c02e64030b14010000a040c05940c041d058030500400c80140201d1845c40d030451820818014010f0781c070710b800f9040901c4a0484c40c0814209124510580d00b010790260360280c0c0340c10002204021191925020344261440103540c0c0669803241540601041e086503034103075403c0c42041c0d800400c502070304581c080b05004907800e50300d08000600401c1449801d0f00c2d414020001480034500b407000c0310591 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 523134082 1250 523132832 523132837
    0x1507080d020c16090c02010c051201261006050a060f020622020406030807021c17090d060c0e15040f14012a050607030501062708030a080103050d09030206 68
    0xd00e04100c0d804900b000001d8010401c00034a00515081022020b5440703035103002500c0301c030701c81000650824058215560140003500c080503c5507941c0c4d030407070303082c01680c03d80303043c4404001c40d01c14010008400c56503018000e88003003403103000b0041040c900302011b0001a00f07540e4020300800c00c042c08040202603000c1005a0003084a0071304408004002441c541039407201d04029620603d441000420825000014a000c1388261079803240c600344421040d83c4822080c0c406855003610740310b00c035a6480304000400304400003d266550b0544a0b403541400c031683d4640c4880401e1081116450615103103010184d18030014042916050914060b808141918400c0309a0350031082c2a51807140e001d00741c0c19a401003a000c48004420303002d00c98103803180012038103950324000c2001040c8994441c1c051241600c4181e1640807080004080b108080c80d20559010481c802d041c2d004107110070140001c004840703850b81c1d0304011b5415418100d06040540840c0c0040c04040740d020401619141c06 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 523135332 1250 523134082 523134097
    0xa0e1303030b0a170f010f02190507020105070c172b0809071a070c06050a140c010902031002090f030613022806050705061003150911030f0c150708 65
    0x601140d28800800480e40000b95604010281044030105030b041302000100c1039420a1300d200244032040b500840c5004a209420b43e0401c2044440742a0030014050001002003c2c8180341c828504940d03a103c06081c00a02d8011b007081d00c04518010740440010041e00020110020030701030220150300340160403030907045401c0f09020016002819140c002e21083c001072072021141e0b000b103081c001c0c0900580d44850b070121090320b1600350101da102e21503801d582020005071100722090b1100d02c42941c1c0d0783c002d243c03400c2c0d05640303440c03403000181c0b03052190300c42005a504015031603080910030041074072650700d0518001d910600c100051801400101c6002c2601550358041400d00800401000d400c6c01c240c040c0304055001c80041c1945e4081c00410a45000d0000c1d18010345400800d49040d0b146880054088007909101004440040c1e1000101074881c200c4950704407803007030100b0300300032108091070030503001042000c090381462110300d0540f1181e0503072307913162060503926000359005103034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 523136582 1250 523135332 523135337
    0x3011d0601140d050316021504080607210e03090f03010207082b150501170708070f050405182502060f060d1a0103060b0301090c090e1612020a0e1303 66
    0x14006800b03495040b05501c43c41d800c039060300c0c0e540c18440818500041ca800c4101d018210621a002941c400f202c2668243c17564203001d4012604c031807504488001c100349291980018104400c060b10910b0301c508008802d22001460729908184100003803142c50900290290340104480000201c0c1501150306001c0203626000c0036094018803c0c1c0004141082c0250940c078208007104c0d84121050120211502680d54098845180c140c52000076016070700d240208201a01207040a4094030f49085544118030707169040c180c2c0c1f4400601441c22001400781c00c0c8400c1ca007400811020b01440c1620784869a50f8440700c50000c000003075032002e00a22481840640c14041000f65a0341c640b242c02981d04106041c007895004141c80e02134100030702c411540c03107182221108481c10180a41c00031680c000c400301141900d0032042c038000d0300c00b04403011310303501800c0c40c0c241e21108145511805480804100101c000c40d501c140030000c00d16402290320700c02c18102b0001c1c105d981400880d00d407545407 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 523137832 1250 523136582 523136609
    0x3080d0207031115010305160e13061118030c0d080a050f0708040602010203060a0608190203090c0901060c060b01030b0a0b07050a06020d230907030b101a03040203011d0601 76
    0x1c0c18200d0300c0100840100c1058002d0410400d00b4011004c0b146050300d0044e011795440d190b08805000c25540c0710303c280030500c010400043d070844d0700e10740c010340d1090141c103020420141d0814105003960100381003008040c980d0607a03035868201004048201801528a00751642c1e603034403020604d0180103001400c000c0009800b01d01e100200d0151003c0540c0401f8850322140c44010207070103504100c40380c0d8080d8540800010302c0c84e1007210424026446409017a00070941101200080d40c001020b44a15204407240700803107032070301c40300c00d40200081e98a400700c24146141040617901d03d4000541014101010502544e41d0039a41c8411240c0c15103507170f942c507401440d05504028144401501051010a40c202800b0b40303a0099684003012407840f800040d03040041d41c00c07909042d141e00d1440d510002c01480003958000300344d50002032030500c00b44000c0d683e0111184183d0301c00035015600d0b41c00300c20307c41181024002c4030310303401d03427412098007921640c0c00d0325a840d9014450705071244444e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 523139082 1250 523137832 523137847
    0x70f05060309010e0712140c060f090d050601080d0206010608070f050a0c0b010e19051608040c0f060c0c0e04050a0b130f0b060109080307030806011d03100c030b01020703080d02 78
    0x1d41c40080130403012400e44031070a50301c80c010041c1070b002e0b08003614075150b2188030300b040c40ea01203403446090500a00c01414045071130300304242500500f5000c0c0e0402203034030700c03080464820401c00b4000e0140c04c0003407a80c005251002403d00006070f110f41c06204022092045040e0081050207503001c00340307042c41d2079440401044410894990010b020140003900118a403c940c45c2228812181d59542d01c01f05420107401900b124403c035001400760964400010782c051280f807916404c2401a039003001c0c0303242c56840c202e807580215440940070a040426100c10041c1c2031041c01c0c01070501c00e442c02d080349410b407202074580c0651300c00140103010a0001400f4181d8021904200942100038030010840034a80441100d0094507811702240500000003081d503800021507900d01d42c560307124049912803000644040d054016101902000142a0b103c591810882d04a44c03c60500c1c1c0402c400601000c003604070380001070031a0440d08042c00a201180c9003104a03031294030b000304010b036590721 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 523140332 1250 523139082 523139101
    0xc12020117070e1203090a141207090b041802100f030204090c26010501050706051003021203210106200c15040f12201305071709070f050603 62
    0x8030198892228604040c0012141d00a4a4403a510015a06a002d1a420001085e41e90144040071603000c070b42c65106000307040042041d0042007801510030702d80c0071104003038141000d03829045520141c0d0b42e0004030900d0300e014000c480400040303902d01c10f001102600881c14181c0c02c8240d00c01400844004e09403002d100e0740c1250700410502d8010408140750440041c055800411007040d19201441c45421060315004014104d6105840d13080c03504180b0359440c00680b6004100f10054a0911800001f50300c45540000d180c80302c11019660741c3c01c51107520940540c007400b40c040c1d8000b08100610a01f0b410000f40403114403103490710354980148040e01c61828140258007a0069005161115041e4054001c2c00036a00905001038801b81c4403048400c601c450300001802030740713200c101203400c00101201098501c3e0003400e80b00f04078103500c80000655105940c0d880025007096400e500e191207980826800100a0002c1c19006180ca1a00f0103400641d000e0288510f0b0000003152450701c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 523141582 1250 523140332 523140347
    0x4060b09100c140718050708011205071a0903010f0e100b1c05070305100216020112090b16021e0a0308090f01050403030f0b06120f180610080d09030c120201 69
    0x59103c400c885121100840f110b4842005215524445c10301e880c004494070110301400384150043c1d030710620b25038600059041d00f002400b00c10b031814000d80801140c0c421862222070407111454074840d554501c0841490b085480030418503141c035140c0800e5854640008c101d050750050080c030007044148903000052024180007020944000714000710104100d40810040102c902520a0315988030b2900d05210581c0300b04c207418004c6605807145400158000d580b00a807580c1080c07000110070a050340ca1002185054403c00840085482e0380030b0503580c10410f081c00c0b551804070034040626100c2285541d03861800b0002c080c031100c00c00040b00e001040140fa45242d81c014000e200600309410060001c00c2088030a412260402c07100c2c43c02806c000b03007151000c144041074804169619880c500184001030304507405000140b0faa8a40744000304a414081c45000c01c5c030500c003e150181140c42d00c901c00380c100c0709000890204001154031405400100c0305103003040282c41c0e5084c40120b4005c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 523142832 1250 523141582 523141607
    0x40b010f0332040b090703080403020d1502070c03020307080d050d0b0d080a11120702031b01051303030909180c0303032d090308070915120209030304150e04060b0910 73
    0x700088110034880b8416021640281d002d8410003000c0d460b080c12881d198056804044d080035001c200030401420000d6001c40d01c0707405003040f80d500310f100d40c82480985c1e000c001d060f5803030415420240150310f4140f1401004000c020002c07c1c12604042c0d000e002405040c0419a0042d6501e06180032a140c043c2c3e2541501d610902242d5240700607000641441400207460826102c5c00450501401513801101c02254000700100103c0d42907012600101070b072210300604104040c00f1003a04500c0d01c23a00b54000d10f2003070b121803171a14140034035402158112250060030320110028072022030000498041500e0301454003103082807074401400000e4460060030444d04240300b1a404003071425601c1405114400e60300c07001c050710b580c0d03000c490a0907540180382c2c4d540a481b1040765050701400d04024420310a80026051164000c0003e080d45c005610482021040903001407c2e55072103190203420729410ac0f001c004d494204448000310703020b40c4503880d000d140f010101400040c0980010b4210 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 523144082 1250 523142832 523142891
    0x60a06031e0f060812040f090b090f04060902030d0f12020313170f03010b0c010f1b0f020f120405030d030c1e03020705010504080d0e010b030a02062a07060905040b010f03 75
    0x1003040018079142c0d43c0c07244c030920b001c4101c9401f000c11512001d014607090040010581c000076103400304010080034014008036111555503c001d80180ca0a000d140805001d170f45458201d501d10803000780003c00071001c0c40d0304043c81001080300b01064041064040d0381c103c000711001d6005000d646a85100f030303801c0601c401401000001300047d2140c01040740c1c82c074145c024840369071803140305810785580490040c0080008040821202c0c403a01c0b28401004403481201c41a2240b43c00007030929040c6409000d10401c0050140440e081c100300442c120901032408212042c001b210041215154600710207495001c001c0380440745200c0d0701911314407a0080005c008600f820b00e07003914554440202d03640240d044c0451702c03c0740603041c4100301803064040c0207400c01030903941c00c01c43c290f800761021105082c1c42101914584007250304e043e5410f07a0b60401401005c0c200840640008003da203c180700d2404c248545815984c029940d4403140d101d424041194000d0024481c0c03004041c40d40e0303161 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 523145332 1250 523144082 523144093
    0x1030f0b07170a060302040b0907090302040507091d0406050606030903070b131506030b06010c02090406090515040f050709020f0a0f03061a040e060901120b0402010216060206060a06031e0f0608 85
    0x400714511382c00b28080301e02c02c840c00c00c4a030305902c080c4042460100c0c1c00d40003048031160100091b05042d0010380c0d011001e0300d04610760310380f11440070b90b1b2420304100c4003151445640c01c000404c40544a015040071045440a0440c6000540c3c3e03540c034812410010400c0c00c0000101d9040d003c280300d05031582d0741c449443e924032150b5248010040c2217907c0b041e240310303081e5008a90a075024507946000b02da0007a04546040c0c2d81e9840d1030700074040741582140d1074460f001c00c070f0009000f0fa411081c0214402c049981d100c01c0b507810030b80c2c90b040f0690071250605104124044404503850104c0d8441210b9041588680e0b0344050198020001340c0e0008103603029807508104003a19074001881034801c0000c07420216128802446450b03035003405103110841d502c180003c049901d08040e00d51040c030502c100c0301100f40502c08641e8494440c1d00003000b5070700100500c030b0b541c90101000c2e8054150344c50b00704801603d24644c0303d480031280941c41255a641c03241c0c0c00404400b900840041d001003c00c444 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 523146582 1250 523145332 523145341
    0xb0315040305181003090b060103060609091832010221041401060902090901080c0303030103030c11100801091821050d14090d0206060f041e0f0e0106080601030f0b0717 74
    0x5d0141c40f9002d0120360701e03042d43c800140e4540c028801c0609858481e81e03100049418008044010161013046800ea603208100070303400542d41c0020f210203028030008682d0302440384001d246001703000d210b0301025a401170000e0f118000c0c2c0c440790501c00342e583c02c1110149858074240081e00c40107000d0440d03402d500f0f08801240c02c0340300303030010704140d00c003950060150f0b0381c0c61000c079886650f600c0316941c0c1500700300010070203c0d1140f4114100c41e40544c24401e840b6040354000382004801d04410000702e62502d00421038a05284034141c04440314070288480da824a0780c8050188201d88115814500030301030900030188164103444500d171184808008002e03203110407a00600049a6440c01d070306c42e840e2541903017840400e0f62805070350f004e000c0201410b040390401000d0003420142c0c2c7d0480841200d201190701c0c007401090480c1c055803600003584814030001d2401e42c0d4030307504024015402000104001a03513a007240c034078150000c528949603200c910048904140f0280120401d040d11004d10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 523147832 1250 523146582 523146587
    0xf050604080405030706050309030d110f0a08011a031611150103061401080d020c040207020607080a181202090c0a02070e041a10080309040e03091309060b03150403051810 75
    0xc01c143c61003101143c0c0b00d240d50b500c04442501c0100da01004517003080c002451100c011f41c0140c2407d000ea1101d06003814801001d040c5180c2000b8001d42c001400c40004002c26407107644403011201168022030b1071403814460034054074003800c994400b0000c1c06020f0152600d41402040c00e801c041d00d0040025503500d06160026108020400c5600f1350310100004840c0030010300c00708804c0f40ea80181c0400c501d9503040100a4000c61002c0e0707000f032001c01084c0002071076900141b041d10303095190f08902c41540c0c00d01305c001e0419074002c121585420540c1e0320150344c500780801c1c2d004c120a80340f00e40c0c40c42c03100e00407405d0444550000381031801240502c01040003090000900c1c4a401502500079501c4004811144032148030380b407100d4100701324190080c10715410150104030f045044902c0d011608010900300a155038010349850307a01c4000380100a101c1c02107440e1500100c00a129400c412400618564000317840103045c024001586d00c00c2c00410001c5902c07980d1b0041a1400007c46403802 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 523149082 1250 523147832 523147837
    0x1116080606040b1009061b06060308031b0427020403210e101704030215130314031b031b190f030c0503011701200405100903020d020d0f05060408 64
    0x1c0d40d12890600900e5080d030b08041190f0180408140d9030b8182c40d515003e010764402000c0c460302c071042910074040e4004555030780210b500075445100b8007952460b2406030490704821413003c449203014104001c002511f5842401c20318018480c10040c0c2c8012140d035404001c0c40366502c000c3c0081442d0000200781031080395494450341031ba403151080d42c04103e04200c610203000b51b201001c030342961111541c88000c0c8030480e85c41440f0340112b0341c0301a000da000100b103040484108000180624070b07002090b5106500c0b84010802400d0a429400c0c204000b2280c5007085400480c4101c0100004440208a48036449008940006640e407600c5021008070090141d40c81c020104a1f480700074290613200340310f01000540580d4501d82181d00303141e030140c16448030f000340310425921240784000351000c502c0d804541307943d030607503007135a4901e1b09044c0180303280d0340c1008005000b0704c90350410150302c450001d881e00d0340c2d04541c07000c1c100b001480c103551084403a001c06013152168100f08400c01900600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 523150332 1250 523149082 523149091
    0x10204051315061403161101050907170f03040e10030b090a03170f010302060906040306240e1b161b0503010f09110d0f02090c070b0105061911160806 66
    0x61068190f078031807006564041200c3c1a081c4d140e18100001180301c810162144a508041c1c50041580c004401d10a82035800681d0f413104940c0003104204406880303c0c58907030f1083d90140181c02c25100384c0741410746a004074814452004c1e03925002400403001c0c51020310103143d0156642d2030b40e0800c4111b295403114008411404218214070801d400a0034840706e52203000d0980d184d00c0303180c1c216800e010703841d000311500c0350700241d003840b011001034140e000b8203a0500c115041d031103042c0402c0c3d000303440303030f11103903122940c070b245580f081c0502d91400d09031090a0504103444a5580c00c0803212059032071250581c00343c4050908400c41d00c81c0c1310301640410031240d00f14000d02510350444103100496034045002885e111044081840c2410180d2814448c6c40c010b408601c088000b6401007220358504496801100c000020001301b046584201c140c00752009a459a0030480400c0d94649282013041c100c0081c4482c1140c03c000c0180c04000d80404001d031001ca02c003c0c02c2d40c070341640c0d079503800039203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 523151582 1250 523150332 523150361
    0x308070507081605091521151602070e130605090c0a080c060403020d140f0f0105100b0301050910050319020307080307031b080f1308060f0c0315030102040513 70
    0x409004041c0f00380100503080e5400100103804030749441c0b030900005840124101d410407848040c1d01c100e03421344021480e0710b40421000d860f540d1111f00b04040d081500808082040c8102e000a2600351f0740050fa00003625410456182952149058174414840c02a0000c0ca400c1c00c100c10482042808039810110b01c00070760ba40303400b90351203c010b41d071240d00c0c0d58091500404148003c2000d481c10420002d4900d003d60320500401d1b00d0121150b007008586100c12500358001c02c1c4040090209101d100d0380894410104010282001ca401d07450b44011311a1a20543e200800704800c0c0b103900a4103401010014110f4600082c881040a994110314000341d100e40a4000700080108020044440c00d55060740d4081600001c05100440c1c3c1007500000d030780c0000c050040140941d4110f009020800d00040901507080c54405541d00e401c0004213090850300d180000c0c096141041803e40303402c107000441804d400a40d841c00300e0f00902650b4030680c1d101c201c0c8460f4541004a86d0710820b41c141030301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 523152832 1250 523151582 523151593
    0x70c060309120908030d110909070201020a1706090403030c1b05160f180903050c0a0c0510030e0604081803070312030c1d13022808070f02031b07030807050708 70
    0x406003a40c040c10941310340e1180703400401040700082103d5102c1d04051001300049824050f0300000324414590172141400581c2d400250941341c240c104802c1c2250842d100c56107500780c508040072601240002e44000c05040d212902e0305012401100c040752049840c0008140d490018140a0b40d14681c03032140300c502c94500c0b000072681d0b141580711441a0303581d0030702c29481c0f89443c265810003880c51030410350400005000328401d0700414012980766601541100141c54141410002d0144032007810320145803030310102d903210b03880114041d640160000000354480d14a0306940310011000000303694180a090030120810540c58030580790450299000c202c601710340601981c80075554641510240500d0902c43c58a29010707a640c40f01e001917010140c105901c40c11050800c5084001c0c114107128040c110380081d42e485445554420303076034034121b00c02161008d0003075103e105071003801d52604c42e044000d070003258003084100d00459000d22182c0e0b4608523401c0ca19115030301401000e00c14001c070b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 523154082 1250 523152832 523152863
    0xa0b060123030901060b03090604020118031e080903070810060512030d0e030405040f0905100203012102030304030209040f0501050c0301060f030c09031e110d080306090c070c060309 80
    0x780c9510030410a1081011658101e906104115800060007000340799200e00d004190070442101860255241d1001005181441d10000d0b211000100171307880900c05410040000c40d04c81c04003004080d02c90207240c1d441040e2410301e15464400d1000060b0180309807040040c1110000404504403d418102040302a803200100980c000c2564240080c0d640180500c40440200b0380c4240046a07080c41161318280da10404a000d440305115101d0850b0b0355201010b06000084c44440100c56005008610310360420041c1088118800756172003001500158003001c64400f00100d501541c1c00030440100c6150030300d0b107020494541001100d065003000b02041d080c403110b01c144c0781615410b0322010800b1004202c11001000204200d404202003c00c000010a0300c0f0203103601d00c0c0c5181c81c40c103204508103040584100d445400c040d809004422103400124005000707598200808070764040351501d4019034034855029684001d040718040180004000d038165000000441c0304c0c10000000724031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 523155332 1250 523154082 523154087
    0x90c03062e1205011703070206030a06030506101503060614090307080316020a3003021f0c030e0606061b0709231f09051f03120e10020d03090f0807050a0b0601 70
    0x7141608940303251b0091005000504e170010203540d210440b043c2c009440756032522514031700003064952040080d81c01c001480314030700c030401c241058210b5040c00e111483c03804800030180c4007000d85103a08541c001c00e841d00150380c21b10040c2c000304040d60840340c42d00d42a240c81410542600c13422440b69842a500044a031058600c1f901c010201c0400d24010180003100d880d079408080c1c20480c118002d020a02443d90005600014805a18080010b1220240b18054204c9149588005250f03126408002c00f42d0b481204813410711700c103200403086184040501d41e00d040740d1900100d080b54104000784103162400c5081800c80310220296500d01d485400005554a0140b0500784642d5280b1130280302e2400e19400040c0c01c1314416520400e4601c400c48401d40b00c0020303410403108980c035080a90089944255040000a402c6a05082d003400d2101c1c0030f1740d204071101c82081410740b24900901031002c1005864400d580000700079582e245030f490110f448034038044044402c507528001280f00c551 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 523156582 1250 523155332 523155359
    0x26010b0909070605090409080711090718030204110c030c0a020a14090a05071b0c080615101b060906020d110c071a07062306090c03062e120501 63
    0x880740001c0e041c074a083c400c0c00c030382550041c1241030b0400d854040d004000385100c40100101d90043c1c1c03070307501c81b52140c008200310706002030038110411400d440c4a011242003044075204882c0c0c1100d00043c0c1d07008041c0180310358080d4240aa15030702012810b42e841910115800705050303c2120601d11b002c0d1140d155841500c82540125003080400c030005881400c00d5225507046000e41c148001003403100c1100440ea0f500c0d041c000c8442c504903a000300700304802004442d800a1800b4030122840c91140040f03441d40c4003e0f40090708009028054902030640c80c07141c00b500c40e0304544140100c0043d4200100030b54030041c65100d201e49422000ca541400c1d02c07081c1e8000801c1d001c050054203180c24080108d1820034051010105410850300e0300040d0700788200400141a030014507202481c0d6030003807005a00090a43c1d0081d6001c108001c01803900c0340480f580840c045a0480d43d540d954072141c1130301c1008000702c00c6003940030320740001d00b241c2041201400d0710b500601409207a032200380401030380 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 523157832 1250 523156582 523156591
    0x60612081908150607050f010c050403110d030f0f170a060342060f0e09060a0c020c0111030702131b030b0306070e1912031e020607080a0626010b09 65
    0x4200001003605403801200400050307010b42c007141d803124a0340c50000d00312140e2000b244080ad00000341017080100242e51180030300300c11222030340c6824807034034040c20b001c841c102c4450801c515001104c00240c00713030b90bc07802d1100803201c2c503400e54500545a80c00800c006d010031f4074030f4102242d9165900301c141030504560400c0b030413010780c003c00c040307011001d0201c0c09000311200390300c450f000701d48141c481400310010300d030b04a56900385082102125007031071009803031600c03014240318090700c000e500065125210a0700f880c002001d8016815142d0650044c0c4a00030740c048080850028440e4543d00940611640303041d40900c0c0c06440c8400f60111100c04079011307050380202000031402c034000c111500c00618003030f01c143c2501c0c00d100041d85417444035070050300081900030b00a509260780b0041813994020b440d1144024100c0580019554407030040031882007000d104006030303002d0001d810500081452150740c4102c0400701c9100b11124a20214a006940c40c00342664154a0094003541c0035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 523159082 1250 523157832 523157851
    0xc08071b1a0a140a021306090e060f120607022a0a03060c0203091008041104060e060409080d0e01140c03070f0f0e0604090203040b010b090604050904060612081908 72
    0x6001002040314000c44006200d521401d41d40c40c4a4039000c0529403220f131040c01c1244005a80d8084024401a10340444d04031008018084005128048058210031780022003255060052035100c8000350000c1b41003140d4040900480092101035600040c060390350b1080501c01155010302d0180421060100507141c55004402c4802040820030f203520540a03a40a441941d10f46a80800411994058000c0180009518100704001c0c04949400c849041c48119410300c2014501040c60054179800b4050500c00d0365188680030070800008105c90001310148000e02040c900b20317a044c1d0003030800746410810702009000290300c0708619000c0721302c14a030f50b407140ba5201030030480031030300c0d2040342d000a0300f48044820940304a59407c0050402000907000150341c07894141f4252041c804184d00c40c1c001001c041c42652034940d01e98080e13406803a82982c0342081e03540c850801401401c0e4039440401030000400c0d10704103200b500002070464406aa4001034551040c4030f04540701d08045070f03085031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 523160332 1250 523159082 523159103
    0x703060207151112070e1008090a050f0604060605010201020a05121306110d050c0306032505030109080405010e1207090902190e06010219170904021e031914071808010c08071b 77
    0x70a0088e0700c05900603409034212105001e03180c3d038152901c9440014001d065000d1030420081041502540c0c02410080c070080d418003840c110094440d01800240302400075411000a41c1a40280c40c081e9066070080001e1158509450142a8503802949078034041802e100015529a1a5504583c0102c00181c02050281c2441000f0400c9482c140300e2144c0c0c000c802079000070075036424000c5030003190194900c41d503160301d09030000d801000e40380340140c02200d130152000e00041001c070b20803049680000340810702c60201d1000404401d01b6a662000400e00720b003000c11215070168034075126080a80031206500480c2ca03d485404444020081c1514101d07490300302a6558003000c4c0850344805032016081002c6041e40848240342540703007590380d0b038001c0100100c403809007104410000143c40108046d0001d8141e400d24020001c1c02c02c0c041c4504040b0b8003140c048540c507401e00814285000700300e884040d031801000820140c41810008011904504c40c0c00c2c08030451040d95541b1000051 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 523161582 1250 523160332 523160359
    0x20d0803040c0e040b07031b200102071407080c061611060903010228030905060109020f0f0c0a0309150203030411011e0206090d020c030703060207151112070e 70
    0x1205540001c0040b107400100400018019030080303019809948501c00524a920304030310001c040700c000c0c11941d250010550524044140c000308106130b010368013124500c8044013030026034003910500000800e094140700c1980c030381040c0802d00c1c6040d84d03150020303030780e0700811582000346600490802c8440391080700a40740c0020489a007264211002a01c0c40781050340141c0003e00b26005544807500c1c82c1211072188640e840100c40c4041211618101000b00d0403580c3c84560307441005003d00521641e001908041c0ea0030340100303a83d118a95180c2c52541c414a03084442c0d12408200c20850200d9410900072030450a0040d1784039100d40103a0045056694544a02100e40c200c280010b050203c42c02500c06441205490695155041e400400b101c0c2004503259140c00c002614807001c5400a140b040c00c0c59a02060400880c1c0d080640980c5412301410410581c2e02622041400035181508655070f4056134800340c24801c181203410f110583e5001815502c0d40c021104856101e9041d0000c0c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 523162832 1250 523161582 523161593
    0x20706021b010c0c08010515030d09031709040c020f100204030f031803140309030c040b03190302012301031b0324090f03020c090a0b0f060d1b0f1b020d 67
    0x154007014540400701409607201c102103080380340c01488959454104111415114400c18000b100c000d40041c0540101404005c2036001c06010040150340c50900c5483c080180f94151a84904003d100700500c00503030001940d6007400c00b000e800c05004c5e1144032001200c0c18420358048030380000b50308203c0c0340c4a0b03804a5220040c1c442c05141000c04a2010001c62043c004400340141c04000941e0b44511450401d4901420010ba441c4a00d09155103021251004980c60316031a0f0541400c402468941c03509a015040c00c0480c4456452044038900a081040c0c40103412030303001e2009000400705400d203030a0040b8503800060503000d0035810701e4238444401003140c010046000700005401040d5581d170106410000016001680000030344910792400803003168102138811810006c0d5195940410811400c2c408001c0c456003020407105865000c40d0402c0b05d4002180c001d141c0c405103111005010a40310107140400107204031590781e2400070031408148103540081c000e0316441603036942d5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 523164082 1250 523162832 523162873
    0x120303153d050d0c0e0a0506160b06031c080103021c030f180b030c0405150a0212071a090708010509150103080d02090a030f0203060a05071209060b0a08010203090601050102070602 79
    0x101010881d04010101c440b1115205250b80d030102507540481c5c166208080216139040c541140b0300c03454040143c3c402c4206505100c0c440c03590311405903e80740d61141c001038185403032010100400382c0840800203845c0d03400743c2980e058a100b100c0c40c2000103010780031001030010000c00100407402e010003081e160f41c01818103030100e00a003a071245000e0f850b0020744085e60400e481100e104034000c02d0901c01c600c7c00440c001d4181110550712420b200c0811002942c8002c0c41b220511750400005e030303180c28441c00301d0208822203040e850062141c10030520090355a21103108230519546001c2c0412080d24020403c00c1e001113603e50710b5000c903401c44c1c82d6000f055001000361080d40e603007000340507419120a80e080000710300400380e0502260060041c14140000202801c10b680d1a00b0304205001c1e07001100c40d204010700000000703013002c4d180703422401400300054007513002c064040c000401110540040d481911000251482660b980d401665210106e01031040580c006418010f0f501e13140500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 523165332 1250 523164082 523164199
    0x31a010e0c0a0e120307050f010f090201021f02040b03090c041505030c091e010e0a0b2b060f061e0f05010927020f04150f08060d0212030315 62
    0x100c1d1300701d8103601c06031459035120301004c55654210044102059000b0f1090280140580d1400c0c4203000182c0c5c0002d49074042c89015006a20300410100c50031040c0c2c1d41070f00c01034503094400e00c0daa81840c00d50300da0b0351640c40d41020302c01e0f41040b85459101d40c0c04400340045070400b80003004003203902400c005011400038030300c0380751501c0c80c020b000c8464107691a09008080312540081ea0382400080b840035501d01c2c5d40b2040c081c801c0143c0311010011200c2c07084401c101c00800790380300c5200e685040c4000d03001a901902000d814040080780d80742903002c50620b080c1940e055844029903810300d5507000c0f003491256601003030004a04000d604541e0a02e8141030345c0141e0380000d414041c410707403422038100c0c44850b140c000d030104092040740c84621042840440ba81484401c600101c0310003050800003c003202e00a040905034030013152200c0381400c2c40d0113900c00599480c0d1600c00200c0b81c10040501195100c0d0f00c1980403001c10000007000d8407030503590a03800c000b5429024110b040c2114112a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 523166582 1250 523165332 523165339
    0x6040605070602070f060c1101090c0b28030f0e0a0209060d021c03020d0f05120109020c190803060901060c050d050a090323060703060503150402061201031a010e0c0a0e 74
    0x401d00f00003405c0d0500f6086650700ca1280001e410000d482d000300020003003200510b0700c0e0b00d026041c1c0013240f0246180c804480d0030040941d0355050307000c200c220300400000d507108802524645404240e4060b08061840805c1341000c0000e2840c209070380f541d5254440c1e0280d00703e031445002c06e641d802c20000b030056030390014140744c03050700c8504462030721910000d6003600140c20008000500c1c551050203072100e04564030702682000000c004240d0811010721601159540c0000c06170300d403a906000c1d0a544210349c16510745410424100b29000354000c40b1440c3c0b14040720400842d145001d0340e00c001e800f41d00540205031794902c1316420f072910f600091219080c021841000000150ba011804c2c070304021501c48004071803e40c1c84005d1078002c0c00340884091600703080c014801a100003c580c0e02d55801903400090540340d900202d1118860740301c10040c983c0c2c9a90000c01404a0080c01d2103806000800108d560ba90b03070940c000c2e410f070341901c03103449e90141004004101845550120010708005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 523167832 1250 523166582 523166587
    0x72a15020d06060f1d09151e090a0b0319140717010b03010c020a061518090204060501031e02130e161103040303140304240e0601050a26030d0f0e01150506040605070602 74
    0x703c0002d41d130040ca2044000e040301001108c815506201e80241e801081015050100b50850030009403943c500456905400d0b07074101449060040108003080b0350415074065410283c0c86141c0020304a00c414600d12301913003482040007981c14144030364a0165155805410112219502c52000d021660703c940d0f81005600001700d07030204420415103000d40c03980800901300c40740f481070105a649a030700c6241458608403052225062841000020100030900160b80d0001096201030705102d64200f08003070354190040181c5c01e843e21018100c0184540c80340c12904000c07065269881c13159020040001d8800c11003141c0308840708000d142c1241c4030391f8a0700d98a02c00018130001210940f42d1002d15542c5030110106280424450b003405003000741c410a00726814040c41d0703598071810400c02c00803075400a902003c10a410b00075118288440d902c04e110620380a0846006032942d01c03400112546891014003051820b0b80d69401206d00150285040034503060303040c1c410b604624010b45d040ca408 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 523169082 1250 523167832 523167871
    0x907031e032a0b070e12060c0315010314010312020f070b0409110c011e0b01090b0909090f06071e05031504110708030907030b072a15020d06060f1d09 66
    0x2243c072441496240c1d1803c0c40721040404100b140354400004201030340080301031002d42c00c0003104480d80100c440c401d0903521402440100c1c01002d801100103404070b0b030700d0000300030004800c10001d00c02c18035900306c030740705100c0440c610380301c07003007445181030700c07541003100300300c0c401e96a0006100190200095801e01d8a40c078495801d4035181d0f10402482028002c00c400c11249610805c0324024081c60600700081c10010400d40511580c004144150540b0001130714441040114583c8650840103850321030800c1718001d44a0030180c0c026072446505c103510204110300c5441036a2080010800c0280e05007050800c2c40001c0c5001080c2c2c0c0c40101041028001080514009500a03050000140001c03071450900904000d0081e200780c0c02c020901010215503882c0750030038100039515004039080310090f441e0100403c2da40ac074002c0c00082c00400c00541a43ca1a402750080340c4072910340114500004404861201c0389070800501c0c9a81c2d50610714403410320584466100071507500e00380d1314000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 523170332 1250 523169082 523169093
    0x1c060608060c0c0a023c12030403030e091503071401080a05090a021e122802150903010b120f0c011b06020d200a020c090c04210602030907031e032a 65
    0x6443c102c0386c8040c84c002d0108402424008808801d41450001541c2000e0035680c0040c442e80c9856141071003802c1520100b0706452120100401d0303032100904a41d45a9500d220800f4409a420900c1d4041880b02001480e901349600499102e10f5246014140a4565508004c00d82000303049201c1c000d500e80a01a079140c541c00c00c511030b0b50030080002c0c108040751603940013010f00210340d03280420000900d5800162034203d8031004140700f820a007a02c841d81d60010900420441e812958488103020319100c44503008540301024220746010b40c1d1500725090010754840200791648403032110308010703000104a0765030151080d007040f80c0e03020800010300c04440034154116070907440540070004903001465010012146070308000d03160000549481525850f29000310300c28024501e646c1c0c200040c0c2400e070300e6403840010707038418021174503070500112a07503482c041400304507a14140461040e00c04a01020000c4190b136040d070b1520684640c0f074000e0600e201104031f000e00081d802c5d000000010f03d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 523171582 1250 523170332 523170409
    0x909050703140f070b0406200c0303120a0e06060303030c09040b0901091e050c0a030f0b18010f05030a050304062007031a160c030e1c060608060c0c0a02 67
    0x1000c401821074410203c04203091505070352140d035540380104001c020780d58204002e442d1400801e030141821f0a4484400b90502408902184d45400005032120f10210003a000a00a10441030108400c1c075a503124680e076a4800c2c1c03859940355000b030000543c011000001001804009000030410a00e50300c00321710b003010281c2004480d82d07120310400944407150380030f4501d1408100d0061003181400da05910790ba1050382c91840c1050340b29602040c10400e13580040303003040720152156010441450340809074040130b0085001d050400e03a00044e1625000503484205ea80240280d4902807030050140d407400c40c1c02e00380c201192036800714112583c00500400c40258010890559040a80d4500c1d00c502c100051413079200103a41c1441c048003c0d48240050852a89410001041d022003000643c0d00c0401a45091076500c402000300c0170044035400500450390340208466564881990050b181d0281340512801a40115091005854509560500d581000790000301c40c0c41e50108000800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 523172832 1250 523171582 523171613
    0x60801020720100905061b0f0705040606090e010b0a0903080c03031506040308121f0803071502030c0d02250308060102060708150411040f0e040605010801060509010909050703 77
    0x1030309492805082c40c400c41e1600d074246903044034080700800320020003400c01c4405020702d9010701c0340416010312454074500c0c0208250604400c940101ea142d448031607540c105400303554080c81c1003010000d03089d070151101c3d03c180e4881d03130450011070303003040b460403219000504440100400d2078400004108114006e26041d011000a55940d20b0070340300105c3c14002c291240360041c10100b2040011031203c1080d500d8400b203155807007108c4d0b1116000103900420121812400d84103880780041e0340c101c00401070144a200e4003403032030a41d104003445001c074002180c180c001e1807802c0005d000354243d103900a0461601004c6c0071090445804600701100d6001c00c0c1c00c90210b005d640901c510b540c0c0410545520200d5481c3c032410a28059a5030b03112a80300030103950140b0348440b000c0161070444c4003a6006896042c3d07448201d40d43d502c5c02411120001e03102034131154505400440c00039010700428007a104090440165a40380400c443c00400301c0d0340069131580182c4001100046d000703140d01025 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 523174082 1250 523172832 523172843
    0x30d05070816020703021c060914071e05180709030c1d090f1902030c0909030a1b050d0503040f0204060306020c0c010509150a020a050706021e010e07090e010608010207 74
    0x2640380a0368030712007010012200301c080d90304c80b9900b000103039603044841100c0d04500041c01e80b003510a1400e800a403210350b100401c5411210a180d0b07403524005486000c80741d840081c40c08051040c01d079554020b200c4d004403034110040013004450032980780c40315a044113891820423016070740e0b030300c1d042d45045140d041003581c0201c50059543e03210002e0182900700d0510310182504207513a00d00540c2c0c0344050b1078110000301c404549201035580600c1010700608014081103510310b8440751311512644803000c2034010800c009001824181040800001c4a41c06401400003000381a01a5071a40009108035450700d0b407442c48a0040e103c90240b000214031030f410150b25100100032850a05644022440c1001b030180304807401a60f464002608500d080780c00e46665801244080b81030078880900030388035102d08080000c9040d40000c00c032680c2080c5c0301c0840303c00c40a60780c01c10300743e54102483ca106e0750302104060007076920541c810410106100d00004070340f96074295080c00e80c0c0040e0404d448 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 523175332 1250 523174082 523174097
    0x4050307060606030b010e13090506130c0605030708070e0607020402120109050a090c210b090c010e0105030f150301020405030a03020c0a090504050712060609061820070212030d0507 80
    0x1000303407038064000074154a050034403004417448002000701c4840c880303c521401080c950540d0030b5038181c2c0204460707a0841c0a0354110301d0880c0500c054080c113101c0840e00400d9003d4001101c5218109690080c15203547c1c260b203035141c010044074080303d032620107a40924104200001651144020f24080307102000c500780c0c6603d040d10035011180d008003140042410000c103400050f4801322600f080e10b001076008001c10103032011140d04242d0f0400010040c914080500942100020761080c4040f0309a0740c020000e80040011161800290350010001401e40041207003074592040368405903c2c0034000600700750f0754000091074108115002d8005d80c020240403201170510303001080145c0717041d04043c4114141075480941e109614822501c4044010061008201942d04920009c0020725030900103152039003122004035a42030300b0003506614121064101c0c80c550349890400382100c0702958100401a0207202c00a0340001203550240020003020030070b40d12a00c07419008440b2940d4421 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 523176582 1250 523175332 523175347
    0x40e0a0e01230412141b0c0603042d0f02010e01020a2103060902090109051c210e0117060f060d0c180f211103070b0c0c040516030e0f0105040503 64
    0x3c3e18107040c03110b0001000948201c8000605c1075800b1108401c402c01039060100f040d00100d141803d04c0003802641c040c10000c1070005000341d04070360611002c5030b074060240d002c41c41d03c2e41150382c01c08040020a03c02e03180340000003540c01424080c3ca0f441040c01070302c070384030301aa5417900140c140c4209000031050b045804d050140c1e041c03140b040507004900d001c40c54800124006080030314603209003445884200e602c014401c04044204074403590010f49080c9490003484a840650010174070030700000c41c0c01e00d400d80c07558440c0950398024410340d0300446458480c08180540700d012441d49940011b02000814504905440361020f500381d80e981e21003a00b80c5500c04d582503059503911422003024482030174040402169030781240d980482c120042d2201c542d25040c1e8480310b1078405540c0c036019140001840810407001010507403140d41c19100308211400401c0100c400c01c2d145504c0000d41040010f220300d020b030f8030030300c0c0b00d02030b0904440081d00c0100c030813030035514221811205c40e0000318105 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 523177832 1250 523176582 523176593
    0x101110060f05030c03210c030f03010603232a130f0b190f0c060903090e090133030b090c0114191419051905040e0a0e012304 55
    0x6000100d0142031603101c84e00c0040d580e10a440d5080320b80512512005800c0c036030f80340c1100c0c06115108250780d2140781c08080c0e074440760001d11801c004281404600110506a0709402c8401d0640249016564580c120416465103410f62541e0b105401040100021005c05014000510076600003055160518001040e4000144e011401040f824044518900008070081052000c5840d0511100e09480f5044400110b411805040b007440c0c442e19400f4194007000c4482510310b001c41ca02280d4484000880c01c0b00c01c8020000130394104d070458030305420000c24103d8042100e030102c5890f042e0312510380c0860020103443c081341a601c1300081d00c0f01755030484c9803410311740503003424941040728400316401c2d810301c17400741682005441c0c6081d0708002801c400b9102620011000d1220f0b401d88290054084c2e400f0300c2152800f120a0224001c010384543d08480c261420700c00d640c4459155194444050030805002c80349039500d40742c0400c0780103010103401482c0310030350501d0780580c00e060601 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 523179082 1250 523177832 523177859
    0xb01050a08010203070503070e0604050406031203050606040503280b01060203030a05070206040b0412020a120201020414030111070201110a06110a081608010612110403050a02010f0f0c0210111006 86
    0x1281e1690042c03042040d10b0340c11000b5241d201055040031103106800800040c960300c225000381e6445880c103400401030142401440c210301440752410030694441000b0442d80340200d01c00d00754141d01040c98466045491540303140c0320b108403401d880710075080e9628032041e444240c010000680c004030070089452884e01455405c410b203800a0f00c164141038503060424000204050446c0b0400c2a40c10201803003003080080c219041000904060021070000b4081d5120f0301c540003090f00480c0c03804e07030203181c10305c6086000020302001c0c41c03602c11140c0c010f4540d48100701002c1441c2c010703204e500c8041440350180001710414000780c0b40e034405800c4e030050700350301c0e0240140780300140010034a10841e408c0005503064400c5406d14400c1c420544a245014200b0311982c84103a04000c580001045000940120524400d80311860046044101101c07030401d400051400a11408402005401c040c0b80407e080c0081e031604d2302406c64002113240c501922040d601a03540c5e5156400c10003d4a00c82e00d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 523180332 1250 523179082 523179089
    0x12090f0609020109120f1101170718050a081e121c051303170603160b0d0606020f0601120215031306060f08062d010b0c0c010e18041e0b01050a 63
    0x2c140e8241305651b260b04500400841e4014010314121710002545c2c1c0c010624895451420503501000345080700004041d007418131480c260300501c100011825240c201244401d40b6000c0d0700502444103520310b42ea50080501045200d14007588500b0024001484000c140c000440c003424182d0110344001c00c8110341d40102000b00c1140c04943c000000383d03105e074501702c4000388501000015181d4100090900c00030081c1e106036502d015800060681740039000d001e002d407444404000182d07548509980799030080aaa042c5a001600180100704505420f034191034000381c50b00e00301d000c03155100c842d00d61069034203140c0c0400741e45100382084454042c6101405116150000580c40c102009549030409440566002002d14070924000800b01d8401003841c4050341030100d0703594814280348903503c515510300c0c40340181c01c0720704002e50103181c14140c1c100c40a41504042e9600000342d00f12604054011200720381039541011506403071782c03000180c45000352101141c40d40350004004600440c1c0c3c3c07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 523181582 1250 523180332 523180349
    0x9170a031512020915130204120212030c0703080304051e0c0a080723040e010204060c03020f01110d090302070b0c030c0616080c0a0c02030d09060e09090d12090f0609020109 76
    0x502003001600c0d80c0c44881c5e0040c0382e4601c030011040e0040c0008226942d0700303120440c0d00e8030100b00001c2c0c0c40203080000b90004d00a0b10091031800741500d409449101c3c1d600c08a019a10842c0c0400018555100031640036014205440c2017003200d961b900c8010a00d11111b4010398410b0410062500c1d154242500520181c0e00401e0558500380c41c3c0c5810365441aa04540c500d903041d03207040c40d520b498101821044040000310355031515048060010300c0150f10541c0181300704241101d1302181407040f91007518410200a0a103440c0c111040081c11a5007401c03011070154000000d91491f9810190901d400e030b00000e543c43d103020f02d10b240c1c5130000091080490b601568000d0100b1508441c0194002050244030342e5113121030b00f070036541801e06510080d0180705006610b40480c1e4803442c1c000540b13501d80e444203840041c0804000c01d81b00c06881d0b241d80ca03004024028900c0d40a44124141034404900201d950360840d204d8041555000205071145a00c7e402c00030300710340c0d000d045030000c1c12111 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 523182832 1250 523181582 523181609
    0x24030a06151805040c0306030b01030503070b0c07020105030c21161d060301090b0a1806170606030c0907030e03030907090b06040815100e13110102010e0a0609170a0315 74
    0xb011240d1181814807816019543e6200f00741001846900400c007d9030304801000e01550707503407410b995641d03c01c000603101c03480010702007255400910200c81009405940c3d40d81940c440810b5000e46a0040da408500c106030000d1047c008440b00742030501c2035618087c1ea001151208501410001181066090a041d12181c0c4002e41d510b05c030640341034407050350000a00025910200e00310b0189900310640c03010203650700c1c2c40c1082440d004203040d503070200d0303407040300c40f000b44007499540005648903641a0040300e80041c403400c0104146034014400e00d0f0105803601140d0b000c0c1d05560003070356001c3c0325403c6518107100700c100074050203965000035501c15103001d10f00900291a840030402c81390222140001003503022450001c1003000d402022403981072400c0c8160034158025290504440001602c8401c04c1958010322403401101020f0010381294941035503154000d0681c894200c604101000300041c0c2503111901501c00c0c019240c40018800c000584c1c000c2556003264803040003600303c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 523184082 1250 523182832 523182857
    0x150905070c2114090a030804080106080c040b03151015050702090601090315230711070f050609040f02040801020a0503010806011a120a0b060a12050c03060307030224030a0615 77
    0x1190380c400b514003e5840c1c58849000400241d11016168030140c0810400b1034003113003081d419072200d01265003100480d0261000d0ba8107001c1035540220b05603505400c0040f000c1182e106500e0f134142c0c08184c03c03020a0708140c4036540c1c0c000700b44441000600080c4045004400c500300100c006412103000d00345080302c1451a41c440318036003000b81d0380012003600c481c41400303500e1182c01905014040c040c81250240307040d810003440390000308001a41d9203d11a80001c0c07140001100100f65400079001c245003208034014800075001c40041c00e003010303070300f00000074001400707202506841009580701d990701d514001c405403400b030041e01304810a0a45541403110180418100e03416146107825032a0580e482480d204000c10544189940000e400076180116a0384106682048440000f081040780c8170f046030b01c00140821034203a900340d40040b10500252404908042e150f02c86618180c0d80349810300b03000030043e0419503c1d50300075529048180110041d8000750101000985001d5100c00365 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 523185332 1250 523184082 523184087
    0xe011401030f06060e0f06041b09060f1b03030504021509010f0c02031608030d1a0d0605060d150f0b0603070e19050409080c0717070603150905070c21 66
    0x1410700c0010010b4000e490400200700035500303d4801842c40c14403144036450304118801d10048200c034554070882c036086540d91160606006020402065a1444049030400b0402d9880c0000c0602ca003050040b9001240045d1001040d07202010340b0a6070b012515041620610107002c1d1660211844100c091000e0411642d02c2206202804201d151013400032401c2e002003400c00280643c00510300c42c40f40c10105910700000014001c20040c02420004410004a400056030480d02d08c280c2c48001440b5030800b0034032a0700070341e0300104014481000c0302102d0380e40c1c08176003400d080c6030b0307850640722051410881200e00c18017200c054165011440c40c03074041d0b0001e15070070b81e40030205d01c03640a02200d50303108092486404040d100c080d00800c9107010a007004125a002440b4019891240702c0000c40d00c2420700680b45512401d80004180320360415070290090558541c4261244640b1000010644264040c09000d50b0301c0b503c50a400c541c103810041c0e204201020014003041d05840070007661a07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 523186582 1250 523185332 523185371
    0x1e0615030f02060d02090402030702010c120b0102120c01110c0d030501050402071a04060f0e01050f010503030903120a02010213090509010c050c0a060b032d0708060103081801020a0b0c07060e01 85
    0x50b4125010b42d84e07080c0300ca40c4c1d41d00134000c0ca241da40c2c11601c040b040094080d0154410810b65965469006000b10516400b00984494414240c0140c104540a80f4580c42442c05030403400d82d18800841d00c059242d1062105400101d102c03c8107a1002c28182d9945130076204103400b40005480562500d0180e44440102c01c1d1011a26000300501400180500015900030404601010300602142c060386105a010b0b1000b03440c04039203034400e80000a821b02d000800c42d002c04802030060484500510207a404540003040b1900a654003000300840b6981c08402c403c0152211440005190400404407800c48100d18400401e1103c2008081c5072200700080349501c00e5844840400e40007046408030381421a100b00f00c40003e50800b5100210001d0101d1410100c2c40034000c80c1c1c0e64035515041c0a0b50790b103080c840640b0f803080401900c0c001005400c1107100d205410700454404c4200c60b07481c07283d64482190340b040c0544010400d4410049036020b150300180e5035200071b00c100e03024144040c0b50f42 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 523187832 1250 523186582 523186613
    0x60117030a0813210e151e341b060e10020313030809011d01090501080705070c0602010b04060902120708180307080406030f0903080105060a020a1e061503 68
    0x107040072000c0810040118010380d031300c4203040342c00542c013032460030050941c85050f815a4441c28500781410400c0f404403040d18480000710165a101c0d41101c202a444ca500c15070340d04014801c5149028000c402c8a01c00004616141950506c8607800e03080c1984041010104c119041c101c910041050640c041444d03001500110b61500d0840e4a07044180c0c998440d0b40304041d1040402e2600000303002100303000d0011620203813909590001c010703114400c1d4095000c8036601003240d4039000d04c10340d4429041c4a5024115007413291030152030340c46026110f9415802900140e4407001030340c1076401c060151301c00900b100b04056061483c0f0394120303401d00200500b40c80c200700c0d0443c00071315500e20306501c6411002440044d2943c680403400d001800e5841802080d001c2070400060841038402c0d80301d148007003a0585da4002c016400c2100700000ca60120a8810840c4100c01501c80424001c41c0c01c01c520202c208003a8044c2d6506142c4001600c4c9202130100320703800541d02c200045001c1c6450384000c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 523189082 1250 523187832 523187851
    0x51206030a0f12020c030105090d14040b030103110d15060f08030901021005070e06070c1d060f01080702102406050703090608041e0b0a14011805060f03010c02060117030a08 76
    0x2403e03403615080349086078420242c0d90641c24901070006c8018003140f000e40d1260103070340d10382e0844030a0f03604031024801c510501901c00750410040020491200882200040003044034608081c603440e042c1e21954850060200d0955460040205410101c642e03030052001501542c14000120000703900e41c00b4200188004c0d07900c07500010f041da4403c000e1700c0003128001b08a2a142c0c426410000600350031405071441180018031503110102c0600e41c000d205102c004c06200540018400440d250314010300319001707601c1032050882124402e4000d5900356030050f5000e52a40c584104212641d6002e54070a03414000e08200010220f80d11041d000250b03462409d1002c01500c840c41c0c02c401c072101410000510031015800f041c02c00007008041806258104402d1095903610310340a1340c40a400c2c8503103090311610114850104020350810b56001400078442c210030380032035002c00d00b0740d0032000e000401030b00090010f11251900b070207261400b0f00340500660801e0300c904d001401008014040810 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 523190332 1250 523189082 523189103
    0x3050306120c10180b0408031215062d030c09040f0504050606240f030601030b0103270c0305070902031f063006080313060c050d080606120403051206030a0f 69
    0x4c641040341601c0e070080900540080d0f40d140d0ba0040a41c41e030300541c0081d4003030602c1c00b01040c0c14002000c19404203d00040019107011114810110041a61302410103584854654030b40c0000d5102c02079482081070320b10850703541000004100466030144400c1e40321618101c103010125600060541d4401000c0e01d800f07403948010123250f4103401c01c0c007030003140c603450004544c5c04840700070b07000d14007400e803e8800f8801540c0241c015030940d0200c3e140c00062800c484200800b9030303404407101e61054041c10145450302e0701d0342c54550504400d40c000034041c60700002848084000c00110401000c06107400c0950303e42003900041074031583c011410314091000b03d03e00400d6454110200901340300c2c8070304010301541c65005584a4100c046000500d0090200004899010ba48107240455004020340648a25824251031030365002e40503a41000080c031100c4418009200c0c807a0065000e6140c1c252165450004607445007401850f00f070003600900c07144000252180003564619504c41c54001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 523191582 1250 523190332 523190357
    0x810060b1b0a0503070609021c03080a020f13080d0e1e0603250905010f0309210302040e0a06290901320904050a060b030403140409050403050306120c10 67
    0x620b403040b1904090320b03d000019030b240030030403280d000c8a855071013601c03082d0403404000351484204401d0140900410f565100055520b001d540c010f10700140c2e0000c00c68149954007270024070f200d203a5009a02240d111900440280f0380202220140d11400c441407000300000040708104100c842420500030040480400d0641c1e07910300212110081a1351641805040e404000701403904500c6818003150021030380441261107805020100c0741c00013598082d2200200d4190402030034100f50a003010f90038070001c0f41d40d8040d00b60301030180d0f01840001c6045c5007411300d440341c42410801c4201c440c40104c08000310440f05602a17406005003402c101462100480c0d00f4101c1d0007030040601e07110480c030141e841a0400c1040501903041054408200b1942d65100103821200b8034018181c1181090000400203403103040b1050a09120011030380c107041c2d032a032859043c0c0714140c5048002c00e0020081128500709400d04164102298000344641c00115001c20002140ca241d40d404114090200c3d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 523192832 1250 523191582 523191637
    0x302070905090105070e060309030a0c0c0806040c09060506190804060b090712240302060d0e070608041a04020112020c010b0607050c030d0c0b01230a0605040810060b 73
    0x140000d0225032018415031030904205402820704650100200d07014080d0000341c1e0034503001b601e00c88c1003040d004620b000751090307042c1c0b20303002105011a02050b80c58004500482c0610110f4002d5100e0b918001c0214240010720050320280e81049014440c1171080b028501c4e2014240a03c0404500f86045991038606103500607203000c0441342c0d0410300c403005002d2011381c00008036102c04e00032102044803201c5070721050002c0c14101d084104a030390505003400985014001400d880b40f55190003d0400381d8522100e080800d2a071229011610000c10002409031801c0c1c070892802c0621040d07040c071316250b0b0010300340402503840501c02c1e0360b0100b181503203280250300c5820190002001e0540343d018510340301d40e4130000000c856000b80120030b21406440d00031030108035180d52207261500d403070f82405104c12000340234000e01214004508003e42c016141d80218101400560740e801d951b44d800e00100c04d04d0030181100b0f070300e48249845070030440c07030408800b0b07a4928206001105900840c00410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 523194082 1250 523192832 523192843
    0x150b120a051510020606190305030702100c0c080a020906011715040908040906061b1101031a04180302010510060816030e1014010f2d17010509010e01020f160302 71
    0x245800c5003c80589442082d000980f641c429403007201d5042e0821507400320202400b21501c0010072945c07040c0076200040c0f0340030702043c09410051800d41310750b5041e601c0b090030b5200594062203084c3c01840501065091184420b94080300a0910500c583c201594851504400a00000900f4050200f004440d1f81d6908075418141d00401d1454846860b40c2e0301400810003071103031030082a4040e034844040492600848900c40d0001e0b42200d102079100c2c010b401504481d4041011000100032528217651039114100039403915003103a000700740300c901cde0103400c4400240c031034403801840385400c01c5000c1e44041d04951100c41c0e4203400002409410054014110310000f40e0104d01504c003076200d0b6807100c0e900402c08d19003561001c004a0760703289132846000c49203005481030b9011520f0080c10b001c5151811241d11014401051039103540e800c143c040c0070a107900d0310780880c0d4442c420b014104000340114030081c8201c3c07000310710748108510890b1803131007000501c0ae08108211418010305000380700 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 523195332 1250 523194082 523194121
    0x4060902121203010503010501080a120e040b0d0807050d020601140111030c0f0607030c1d0405061f020109150b0f0111030f04030602040518011a1312030201150b120a05 74
    0x8940b500c2d40403406012041d0001d00400e40251718080000a4441c1b000986e492000d4028090462080b2515011030310102c801c024180c100751070751007107226911090048102c084c0500d250980318000c9141145c1400c6034014070404640c8203800500000c0c941d00c85c844480342c000d007070030070728419034100180c2107029001811100d0b000b1340f1940070441601098031403281c4050380c1d0800010003140700c2600e007102d02c5100464410003c4c40320440505183d44029000400102054940d102c111812116100059110030050351628101d20401484400e03030201400c400006002e480414004030702c0e43c2d107040d58940d0400401c0c03401c007031180d00180b048a4034450b140d80340c03a54864032400d040c4060b5105206440c0100f00140d0b82000d2030404001d201e040c2d860701e00e1800c6405c0c14110f40500940c000d80550b07140d10703540c0200000c2110307040c0101c00700b03980329400104410f800001c2c42a81c888050303003d20980d00c410000201840c0e105450543e01040301310000a454407491742801c415440d051 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 523196582 1250 523195332 523195369
    0x30c03030a08160807020d0c02030c0d0302030a03060e15010c02130501140108071b11010504050d0c090605011d1314040309030606050d0c091a1518060a0804060902 72
    0x120048402d601030314161280035012400820301800c650102d680d00c0f004c0300c010005130040140e82d81141d128001d0400c010b40018121000c3c0c0d00000c00007103044003007035000ca01503400002c002c00c14a80500130301000b010300c000e0740d00c024030303217219452140c41c54181200e04100c000380f0107100315505d001c84010105246c079010001c035070315243c7c42c01449001c0300c9098007080201c00080da00900c1911300b00c01c01c80d020b00c01c400d1003800a90381c00d00c0c1c5128400807035040c040103000210306500c0e140f0456018a000b00b45407600a4544800c40b011a45540c004030304000c4000c40400000000044400c0d090005480c030401d08910400c10000034400b8100142002d9511070a0005140e8001010070641e401840100203007580e1310704010190303c00607801042c500c4218000c03c4280201d80c004000c030b603440b44102c10340700b03245000920140740581c07503441294404518502070000001503d068103000392211450100101400703800d189004100911064543e00180300715100c2c440401000c100b1071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 523197832 1250 523196582 523196587
    0x213030f032a1e03021212010f1502032b050103030201050a0501080d0c08130504021309200409020a02010b041b0e0f210f0304031217060604090209030c0303 69
    0x40c500200320340001c4000d8056442007a5880080c1151014000100d562282c50b101000c121100d54200183d07042c08103409602071003034043c1c2c420310b40100400414010680300c29440d81495140150400c45070000541c200006210110701c07134000044480f451560030590740b9806007010300c09402101500c1c00c21200381488000070030141c0542181c0c1c01038601100070301083e07803208000c907034400d003001e590030001e515040580003003034480004140282100300291000c81d190300104042e03038454a0003c48400448004100a54041c40382d10b85058400400045070b6280100c0846680140d000b41081607600150743d904e0780b4003d600807000c420700940140201603103400720030200315030780040300081040401d10201c1d51600d00c83c802d047c441d004010104800c441d0805507607a60503050300b9000c502c07564447d40d00f0940c2c20001341c80118410b04080d150300064500040020900300c045016803103c850a00515a0b98801980c013a0740c080e40b801030b112a96400040c1c540a00002c4154250100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 523199082 1250 523197832 523197863
    0x3010204090c0305090c030c0111101a01090b2701020a060c11010b090c07030804050a1703070e01030506150d02130b0c0106080a0f061d01051512010b13021303 70
    0x1e03812500a214103038400700829903c0380700080c1c403800c07140103040d803580149035400301075030103444218141e0b581d5808a40380e413404150700000301c4d070300c9c04011402103c1e490300c002e01940e40720702403101600c0007100ca00d003440708405c01800c090041c0c9418280d602003403413214405034420000d030980310341c2107003080c01280346801d00604480c850050082e801e5003440164480d500b060358005019802180c0f8a5107070410036107045682d110090403c4a090240076284804145000140b06880c910045c1c2940d13a802d000d030000d004060740b01c0d01681410f0270f010402c400760f80c03000c2014400a00b41c03032406a0343c8a00c803500100900c0f4801140d2400308140700d000c10400340b82400340458514090080007204d45844825683c5c2c0700085008107855182141e42d03002881e103803c03500e49000c2462108280002401b0080e0a5aa0881d992941116201c003c001240350403000581c0e0042d1400081121403502e001282241840c070602005154000072018942d90a18100100540e0403003a400703100e565 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 523200332 1250 523199082 523199099
    0x30c150b01031b05031504020408060c0309010b090103051504060b06130509130b011502030f0f09040506011b0605090a0f1a1f060e1201020a0c02130c14030c0903010204 74
    0x5400c006140001d1400c001e02c03180030300e40708401d03d0b5503803c0c1e1a4141984e4030006841030039041c014985811a8081c08002a80101040001e01400c1080b110a890b45010421f02e030840c1c54907807905218011900c0100081140441d0419200ca00c83c03000400f580e03110b082c90b0014000038900c15801a00000b01000c0d20400c070a0540c080e14800c50755200346403030b02a46541d10400f003040103412450810010096601e03880f0030490080b04170300640782458600200400160803020001d070b40c10400040480d860314240c80f074a6400f40c0c0900304117810f8000640200052400500300810742583c45010600c18a010090081c01036803111b440380d0f55185600e8070382c000182d0842c901c7c0d500c0301c00301c000c00c4640b08042000140404020300d4080302900c1c1c000115800e20110030702c41c1e002443c000e4440701e15035087c0002c01d0381c0000307912525080c04217403040c03010020305200c3c1041100c0c070300398000180d80d6208e50034840504107103200c2500c940b5480c078400300e644203d1640c1a03048d880050009034511 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 523201438 1106 523200332 523200341
    0xa1d061c0b010603020d051321021905010e12030402102609010b18060306010302091803040f150e030601090c0509031504110315060904030c15 63
    0x40c0e99488024004000707070440800250005034581c88a10b03d4043c1c2900072081b8211080028025101c00568540c44148c96146900c291210502c00c0d00c20802c0540c4140c11022040e0a03070050319050303000b084281070816450241c0d1030302c11000d00049042e41d115035005050b95480961103031003142d603408103040b4500e5405035541c045c10882905410248544515000000c0c03140d840410000d06102d880301a00ca0180c040c0d08004136510040b4555044982c144c910380c1e6281c41b20a56030081c070010042030400c0e0b05c000315001504208403040030088643c18054000240d02c211411a014110080116055070140c8010025030102da03010400e41c0005280a90503c20f00500190070994a042481207804003541403000340300c40c542950b1804d11040740141070740400b0042041d12198001d00091081c03010700001014180100404106203510440c07142406650500300c40003031 = true := by decide +kernel

theorem cover : BRFrame.Cov 523021582 523201438 := by
  have h0 := BRFrame.cov_init 523021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 523021582 ≤ n) (h2 : n < 523201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
