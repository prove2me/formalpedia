-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4318
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:14:05.422772+00:00
-- url     : https://prove2.me/submissions/bb0180be-db0d-42ed-9bf3-93767dc5843d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 776438848 ≤ n < 776618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 776440098 1250 776438848 776438863
    0x6060807060e040203090c0907050c15040b010b030c09060a0f1805060d0216050a050f060f01140108072105010528050904140d0806040509010218060c010906050a0504050d02 76
    0x80b0703220031000860120070b020195000a02c40d81c8076005503000c0c68a2036844824482c0680342950f0f90b84e889040ba58041c40c80c00b80c406829011004c0007004010000c0d0b14001803d0668240169540e00d94031a00718651036400781421899200380c000c070300030b40707800d51001d0342ca003030080590b9611425440010540c04414030341e0144d543c1200041003c1c1e040d080d59500149824442c401e44d4100c82c0d003451300c6090600841000444c0c140c0c006206410445408025043c0c002c0000480c1903115403400700d1808502509510b130b1814801e9220018545034000c801d2040002c1000c0760760f5001e401e001807464028034003406024410640440744040b40d980c07107640100c2c1e91003c100c1012105007000c040150541006008030f0701403045100405010405016610034008a0b444100b024204081000143c0d0340041001044ea0f1041c005502440c00c407041c03c4201d050203544080c0c0d00e00120910b90301400203600701900d018184414044001c016521141c0302e54090310503200d8650244108980b180c61 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 776441348 1250 776440098 776440109
    0x503030f0a051005040209030709020c0f241f0803221a0d2409020c1b100c290133141b06060102151b030a0e01060f0306060807 56
    0x56403e1051741065030042c051800002c046071110359907010f80c0000d81c0d101e95940e0520350019138600820813000c20440d24090710742d800c8004541260070403c466400b0003406081d940c0700319260071001c200c60400800c0a001e8080540c4d9654005001c00c2c40c07030764140d480c524160700407140e0000c2d42c24a85808500071003801409585000844c42c8000d020300400c0c4150740001d01c003005440c4c0b0a42e00d0900c003000410b001311000d6214800d814819045c0380146104240100c02c014803d0b07516902d032040120b0750427060410b0a0304a4590422010f29070180001c4000040c00c0600d4110b02e034440b28265040714003603450b5a0070001e6505074080f8a101e0009280e10102c00007441e102280c0c080c1c004080c03041c80203815203040c2007074444000c034071400f6005078401c19041801801110350741408805072100c0000d94418503400d2100506002d0b110200350a8500b45010000c0303190135282ea04000030b08001c8034020b002c0309889007070314440e203120f41c40304403450352514200284007400440c05904035030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 776442598 1250 776441348 776441371
    0x6020703080306030111040806160e0d24021303170c06070f05160f030e09040506070c080405030a08031603050c0a030e0a0204050c22140d0f0f0503030f0a05 69
    0x14950340e01c401164101034040b55055403280d44540710303001050302800c01003c0d120000c00560415aa00050b1081c2d04041e507020410401c0c102170480e00e0b42031200c103000e540712448159400c100c200d142800004603681000c4c040c000a429125050b0b41022282964091461468244450b1040211610510500d085c45800c40000284054000c0402000990160900c1864101c040710102001c009410713049421301e0040745d542c400d141d44042004003034042629010303414281906c60315540d21000380030070204105405a14100310050080d20000e1402408030f400030310161404008a406c00c440844003984d4850708503031524400e0081e24001c1c0c0480c50b01c0e600e007000b00a01140036082c2002001d906d0320907203100ba8016246c40c862a0f1082074034200d81905e03103103006081809030b20b48800b5013105603700c00d42271200201d6581c0c1200460b004071341c0454216514640021805203062000e41103038151f04141e001d009020000f03502c21004084130003000d5039250155000c850040e00d2515582 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 776443848 1250 776442598 776442613
    0x90f14060906120a080a020d080c130b0f040503010908040305010c08041101081308030901090201030e0114010504020d060b04080a02180903030f0a0b060a0c060b040b0904110114030405030307080c03010602 90
    0x5041c054030400843c00ca480946050050644400c40e465200f04c18000c010390140c00341d50300d0940e00102040d0441c81101c0b62910b4a98088400f4000d07060038006e584203428000f5501002a482c142140c0003810050001d0110059a04103940e9581081c8019201d87d400c0a900604803407141034100c0c4038560296a40b840c6008500045a000ca4010f003159150444c0a030400c1c0840c41c0032000e180f15a85410000c500641540700040c2a03424106141c50960f0520301e07180c0da680102e680c2c513811f54101355001620380b050407100d1809001036a0181418420026001c105848085441803040d0300a40b21074000c68800400848680001c0790741d01c419070021b0011030746c0d10b130000c040140c0020100d0740214036a00d0140009031150f2008440344040b032018203c82c42042114010001d20711421034041100b10200030201e03003031800045c401403183d0310303500282d036080e0b0041c4403840001500084c0340f51a803900e40761181e41ca42c826100d450201c2c01907800110850600800c40381607480700da0241c5001c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 776445098 1250 776443848 776443861
    0xe060a23070c0213150503031c02130e07090e0105090606032409180106090b06030103030c03050c03040f030219030809040209030f150106090b070c050906030a0b01090f140609 77
    0x200c44040c01401c2003024082d001070150340c410151190103044203100058944010200f1488084241c0c4800d000340c0050203003040c20a40d660b910000101c10020140e80c0d25003e510b03d906240094007e880c24400301024025215481395211003610410121055666203460810100305401c403151070b40088100005a03a1071600c1c41c800242d0540c140c40040c60028200000e504080704a481d0381070309805421407000803000340510802090216400c0110450440101e04644414000541482100c19140003094414030484120002c000c0940f5201c907200e130200708851007188400ea1060403100c2050020b003200f500007900300c03507108008910b808091418003002e504200180703903050081072015180c0d0300c2c090054011180e05c0320f562020799810407801a0040f24030f9040b4003500702040c495140042c05000a90042d504112103000d9503645900c00a0b10304801f03120018450000c4200016464080e0342007070b510b018401e001800006031450083c031080e0b4003228a6a40461a0300100d100c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 776446348 1250 776445098 776445161
    0x6030f060b0118031514060d1101090f0e040309060806010c02041503020d050c1f02070603200712020106061b0206030405190804150f021c09180e060a 66
    0x1010206050480b03250a40c120700496600c3d8907030040d100c035650310441c8440d5019034450150f00c1c00720b24061409604003400030800305412001c0040a8008035064800c203a8020700c0010000c0c410510648030303032030701d0b43c0e40c420540368142c07411408a0329400011450354096161607208440603542d0351000b42d956000c1001801c80403046030040042102c020004da2107004801443c980100002d20307a03a21400188000e00c207455140c0b01c071440e180340411044650200711a02291003519010518494a070201c3c031000000e08900d683e0010006505020454101d038540e0034541140c000308651036454100343d9809a64503150307981030180440e5a40140360227006103410a015208560030511074482440e4080c00b401426102c000340880c080010310242144e10003600c01500e460054038291791006540c0780e0007412010303000303050740600090040c898810340e00207001d03e5001000825116243c04020021007400117000d014000002d60080802d00808000c040e402502c030051440300e0f044850b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 776447598 1250 776446348 776446361
    0xb0a06051c0f0e03040306151202131e0603051005090d0c0201030213050a030c090c09030209060f030a0209340f0f0c082709070e011d03070605031906030f06 69
    0x400b010307600e00c602c0000a60802c06800a9031145c1c20004116144504400d120340040c0c1c03290088400403903421005031100380c40322851208448000c02d80c410002c00002c60109401000e425251030301034004144035000510b0320785090140000c20080e2110b00000d612214031003440008074000c958202d0040d482a40104104103903034507821700c11030301d402c00101e83d1101680151b4071070948240030b0014030524420328189008c14245200a1840c590101e094903000034010f61154640e401d411204c3e480500040b03045a50013040c2c1c0300e00346403124091560b00320312021801c0c01e0500d199400004180b4801041b0008200d48810001c4036007102c0071900708a85140ca1820411b2030b0008030700290301400980085140210104100d112010414980301c2c110340e40c02d071003210050244030351282c200d041444200420300c2c044422012003102d0900d48801040c070305405114400c400a02c1c50382c00005503003e01000200d5040c540c0151a200050b2582c03400090000019000d14500140c1c0503403021 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 776448848 1250 776447598 776447621
    0xe07020c1e030a060c0908160302030703020d051c1107060309020d02151204050d27032613140111060f0a090228091e09020102010209130b0a06051c 65
    0x94003901800d0303413150243d8074a51003000100f0111074080c80122000c0c000d6040b08140071490701801440c0d500040c0d0749069602c00a8041e25101c8021000d2100078032a004030088a081d580030001304049004000aa0400300c406036401100d0000ca604d0740700c1d0054020550b001804012155020303003c0000181c0d403405404660007040007081082909401c11601c80d0b03019202030108403640040c081c001240d2807034036000800401d80100119120256818240da400c44811442d0980c00102c0d8002038881c100850400d9201194411000784c18107186401e42e030001582031441d00c512001961505000b03228400c10340c02c503000082c5043da00d41c40c1180d0000d015a404180003115401042e0050050228070215000c09408903100b0043c07030002c1401001e07250000c11071440c01c03c2c90354000b020b054201032000743d11005079106583c802d4045e280c08110003440b0201c1d1107909128040103004015801b4010228a8000902c0500443c00d032490075244000140c0d00380010f244100003400003403001c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 776450098 1250 776448848 776448853
    0xe0a0b030c0a030e0a0305040f0b040b070f0212012a0801060c030530040c0e0601050d09062d0608010c0512131202070f05030a2109051305010e07020c1e03 68
    0x7130b8901d41a00300807949189000c1d80ba484d0341c031401c068014842c074001e50040840c500c000c0004000340000e4100300c1d0141d50704400c5404100c05070780f000860340741d000140c00c2c55541c2005070300c102c00340c0c054401109001662503e5440c401e074025040d07031110340074070400011907011903041020a0141d0010702d01c4244010600c48000403801c240d144d00703402c0b201d446045080703400410080011004441c006011a020404001c3c078111000a0861164100ca130541d50b071982e80070303001c20049800c40f40722541aa020408a01c03072a04c0000005841c188142c100d9a041c214001100d1030306100310010300c001c0341d4070716182919214138109091400380035040918060898500030400001c91454000702641c06403c990385440028100b031110380d003015120ba00043c0603131001030448102c1079504e5203404600408028800c3e000e80e4078a689038002d90708241203071020f0812400b01e03444a07040c0c410081c0489055110400120b80c2d07202c01c3c44030079030004107a0051050482e02178800b54200c0000404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 776451348 1250 776450098 776450111
    0x303110c0a03060b040515030712030221070b010f030c090911030d0302030601030b03150411010504150203092b020108150d0b040b090307050706081b16030e0a0b030c0a03 75
    0x49a00075915500a80303010f07070b95841c003804901e041d01800e50094000602c050454241ca00040d032288154815060382c294803150002c1094000d1103184105804100c1c0d03404076102d02d81040180c3d0b8000803007150b00c0000c4400104240b02000061401d894010b0303074910360281803010b17401c001d08143c2d105490300c10072941c80d2840c0d0b03a42040440c2c00700700c0d070b40c0d0003503242e05280001506075442127217414481d070044901000040005180c0d41d51083d08203002c2501140c92030016030341c034429038102e0303903415800510117039459030000004c0500340000d5a0400d0802c04a406811414480e403c40303154004600c0740200140d0b2203990750603006010909500481442000080c002e12910032013143c40f800c0c014100010701101054160340452420051454040a5035070541c6501181c0078113414000c004c000304d400030354144082403684008064043c0d0340d49030f5505d203014a0744210000c4002842d5801031043e2402c103801c0d60070440e154038041e24115114403220301d030a50407104040e02056901d61 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 776452598 1250 776451348 776451373
    0x917030306090c120406021b1f0501050102030a0c0221030f04030b0f07020a0209040809040e070503010506010e0a061b020a170f03040b1c0b270c090a0e100b0d0b0415030c030311 78
    0x42216127514480d04498020f0400d59507a2054890590020b41550401e1144e075003003e4001c201c1c40440b0741e04480010f80c274095444d081807501c5400701c08803254440800c5c0610702640b11001002920f000e010524269070301d14050400740da404450321001038000340303881c000500303082c40941e41041c0309203d01130a081030350300414210388490001d50110361040b501000f40d803c0c207200781d130303000b0200f80303802490319031300707201142d1414510701c40c0c4410418605036004d0190700344c800c10000c40d507009106c07102c0f4a5640c50601400c2103178014180351806040c03c820490400001210100d400008086080410403041c4d18440289154090400b0351284196411565944036aa01543c023000c1151049003403040034840c8260010f1151035112030400038070100390781d400504411641001c40d0b80c200c6a54500081d081c40009034002d815140c004146045240380d40c0e0041d220b40d80080d50f00b00a9902c4030440d1440b40c000070702c1301409011000c102400404d1040c60900b02d07a0054904841034200040f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 776453848 1250 776452598 776452603
    0xb0a06120e12030a06031b050d020607060b03031201030b1018110c01060312090909020d15180b060f01090e0a050717100501090b0a1403070917030306090c120406021b 73
    0x1284c90b00750550f070b42c290900403c802d0880b5400c0380c0c0c03421800d40301a41d00303050200b001100d8901d8040c1c8241408240c420400085806c04544030390042c0649490342e45034000c80010400a00080303c03068032200c0051003900c05448918215000350010011402c00c910400c8020005125a201b462104120848411030b013401800010b5101d8110b0000c110303a098001001e82c1c10a82000c8022818101e412000d649d032902d590011035000f0100b801e062500c84a400001d04070b66668243c214030300072034275090040d41e40c0d5051059000f5500b140c1e40c2c2c1c3c1c0d010700454512020703006000390103120501094419103158050703a880a00f07820041040f10601c0d90486900e00704513008103505207400c4050007903583c000800001407049082641c04c281c40c41c0400340040380040c1c0303040c401c0354001c0f00203500d0303d11800d074200062090407040c62001380c0b180d801544a50080b0b4100f400707a2048008120102241401c035038a0790200780300c0d8099a200c0341e4600c0d0196010900105a0101e00910512907020a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 776455098 1250 776453848 776453851
    0x603040b010807061b11040f15060912030c0f11150301090b060403081206041e0203011401080103230312160e0f03031204051e030a02010b0a06120e1203 67
    0x52452003210361510004030310302940313a0001303000c00c07010504030f44c00d4a01100b04030130800d501c5511803030138154120115000342804c4d000302d43c3e4139061030038010581c5880d0b07080206a412566a035085e06031941d160320459100c144005000564084029000c40e4041c0c4003059410310695149188a0701c4400080e40110745084800c00c0990000c0108502c034000d00c80d00b0720007401610000e060500e180c942800034001d20320500e25429442c00001c0b51175407541d0203810b80100845002210004a2103c4d41c02074009005104a140040d07a205246601400905040700d6101c04507407007075048100a480c1c296050b200703400591005118011240303001c081424803668100b09e040300d820b80f10003070040c411404100c1c00d501644003c06d0381c245586004c07044941c120001c4040044644035450814604119030908444c0881814980003003c0b401100404081c1e013554000e210260b01c0d081007140e12101d501c609000b00f8004080805091560740103040708000038029541d20340b40368000c810b03c0e40d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 776456348 1250 776455098 776455103
    0x1b06040905101e060807080403270b16110402040803030c0f0c0105070c0308070810140f13060323030a12140916080609100e0f0316060501080604030806011b02060304 73
    0x151103810701c00d456005d0a8581c2c002d403145004030780d41c01c1645002e00700100c108a50740151788520031103400403900c06c405c507005092016402e07584491403001d03109113400c95681215250701c243c0c5804558540b80c02981d00340d50300f9002940c5191034200f9143c80781e07802034803200d0750301078180f114940609080c07003824440e04042d142c02c000c50019203030081c080c0300000d14000502106209000c800c8d0103050300e6100307482080310032082881010001a00d2107408401d1591320801d07004400c0c2780e2031240e401000c01c8903c60719800c226800b052000c0d00d41c08120000031059540140001d080d80e5101d1058410800c21141000031801480080400c800c40c0407111102e842d0702c0001d840394581ca8410b080c000800c1d00c040600f4142c1400c6512644503a80402c0c03050455481c0d1624900c0c03640c050101c050f17480d14060480c0d90750004411601d000804600007500d030349241100001c1c0b00c480c00b26141d40320f43d5141d034940b04c469a9280064805c45005c0c049030705010881c105400c0162980c0000314021030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 776457598 1250 776456348 776456399
    0x2031b0c0609040e1908190314180f0102031806100305060402060a1b0501051f080c131b0807140a0f0810051005070203100905100c140703111b0604090510 68
    0x3004550502a205104215102054500000c208060209ea104c540c0c001c40042090460718101c0420540f074184400b440b4091940b000080c040300340010760607c2150495801036500c0703503540407884500d402d1342d840003410b560001030015005191102c02015080410708241c1c140516002c9116200d0345908411100d50f075556042c406030f1911041c07803060481c100d0350182031943c01c01075256107803407201580c1d80c002c500d0401600000700598003c41c1883c0718640e018003c19010342c40040c5581010380385400443d08080c200d40003052410100c8085a0283d01c41c4c01c400d0041d10b0084801940050401007000c880c0d0b0700200383d41d980e44464040c030f403800340d1300c042e15810640100741c145501034112411542ca041c0c4010005800424400106c035034148000449400300c00c0107684103041861031041085002038010b0416170803200500302101c03000212f40445610b01460001b9150403814140d03c180e0500040258110315045954060352000544005a40d1400d112074038290b00041c9480e01d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 776458848 1250 776457598 776457607
    0x30f022b0b150703260709060908070609050d050c040e0a0209010b03071e0201020c0a0c030302150105150f07120503040b090d1b050f0a0302031b0c0609040e1908 71
    0x4030540a00100144221042402a0081c00981030140301e00c200003000d00c02c00000501c901504100c03240000c14203a15a82080c0ca4111402401700b2443d000b401d001c80c840a9010039000c100107540b0f0181c84540e110560414103010400a50f04502030040703d042c46100d072184040d8990b0302518030030411210040c21001503a104100c4042c005804c210100b0200f8001c024030300b07500000402401018440d48104100074080c2240a8451400e80c041e00788103803e103034010001182c0503103045034020360941c3c0344c480340001c0007403903d2028441e1680c0b20504418203803145000c4801800c42d410741030142d5240c40b0740b03603a925801005078603003a00421404806c01040c020191003441d48151140040c08221905a40203030100c00b07000c01644a03240b4011000c1c0410034100600d28120720704000700c664143c2d007031a00941c1c80d408000409600c1400b145111070b4840c1c001600b0781d00100013410941071100c140240402001148041d9000f03100b5580c0340307501403049000c264400b50044201c0303981d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 776460098 1250 776458848 776458927
    0x11030f0a0f0b2a03060a0b090a051c0f0f02101b030e06070512031609030b0c092e020f01381003060e0106050906030f07271e0e010303030f02 62
    0x50640e503000013047c82040200d90460768402040e1030580344100c480201140150034450310404050000070000f1502401d20030601c0b00ea0703a21040d07900e1088910030285400d030302085410b940b240c1888901480d085a54100081c080c01550000308001b8240b1810306905444080c9055207040f40c266284000106014250041c017244141140c42824903c0810b4a10b94074040641d40c002c0561410200105e0141d44980d200301c0076240141031030070003020890641c4141c1c0500440000340c9005442450b503003000c404018020101c2032000d00302e280ca4410003540c0c00d20a095030120b2074103094a0080d6403c1200d0303980c0340b40c0c0206500c10362340006036a4284808941c5c441010f03041300d070501c54103001125590b90f5000849501c0002e1903240106a111020f0680b00c200402001d000104403213184080c1003000210503d04450346200c0e09541c0140c48d40c02e404050085016441c2c1d01142c2c4401840407034001e0700020106542c4c0c0310010300e41040f40004540a0710103d402c00c0e46114110140c000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 776461348 1250 776460098 776460109
    0xc0d090e06030703051513020a0e0a0501051002070311060d0903080103052401031e060501140414041227030311060901050c1903090b0411030f0a0f0b2a0306 69
    0x90100d015401480544e0840d19103d0ba0f489070f00213080c0b6601c0240e4001002e01c80518010f0011582c080c04043e10907890350700110651030102d411039225850b000001516160000d01c046c0900002c0d0050f0040c01d08584844040310200c003101030304400200024444400d0500c40c0700301d21402960303800010f5042d272401c2400c2c080031a2440d440d8624020026485c07011a4122a0441c0d502c0b5010310081c2240860030840d045242d24060304840c13030031000240031942401c0044210030100c4081005d0112188034100c480d5042e80e016180502d05007151201d240502d540d680761092511514084030124101c031645080242c00440c001000c2c481b4440b0b007090100308903900b00703805400038001031418410614403400349070340d80e8294000344d5800d1304c9590b010b80d00c00001c803a0489800d552038501400c001c1002c0120340c6100e0b01911501c4500b024031500412076010f4a640000081c2040200303494800c1c81c8a400741c1040128400551030454250f110040006640c41d09140d0a4891074803404006 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 776462598 1250 776461348 776461351
    0x1602060a050a14400f0810020f04030602030c13140f03010c020a12090b030112110306130602030711031803160b040314010e0312160c0f020103050c0c0d090e 69
    0x100c041004d215010741400c00c5000458801c0300d40c00000a14010403000205410701d1041110030138001c0b001c00300d0484042e0385010140e80c2c1c01e10444008020b010f40480880c4519a07175050b00f00010310050002582c1034005681261108a200d402e086500c00001c44c8200544d01c141000903180441d803055041c04c0c528140a604101c00801c000500d01c00040d4a0350043c150040c25810344882d0500500d029644500c06041c02c960415100c0d80c503800d40c5900300048020507074801c239094010601900e80010241c0c03298209030805007421307006541c0c913400381d08003400e5a024040c0144c0045080c04040002e8103060426100c0b40c01155204014581040815600c0e41d48110401105020411001d412203080303d0f0f025204411b0306032850740070f43c01051800320082060100184018203000f419510600400750400400081a10300100b0340b4030f03000012005012030080a4035401542c001e40c0480c3d403003080321500d00d103803404260125042042e002c0c02c0030040b803108a01803241116400c4241d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 776463848 1250 776462598 776462627
    0x903070509012306030c030a0903030e0a0b090f060910020c0703080a170a06080307020f0315010b040f080105040c09090309050619030f021201030210020a0b0a27080a051602060a050a 80
    0x45c55418903040d0703011907100040c840c4a010380c031070110400305171003030b8840b086158000060764000c0e43e07146041440b950f0195400e002d42c0c0310b02c0b298201c40201c007164031801200100000d000c2c0142084840d0003070340294402c00910300034030100102081c0050000d182c15401360792200c0b4001c0350340160081c1403e02800c0d03400c4c01031410006100c0c140300001103600941d0101c444002c41d0f03d40d00000391030300c04510450301c00d40d805480001055004103000e001940c00c0a0b4007000b0352500c904c0300c1c500f200e9007200c2c0035000250750041003240390407941c40304103524000d1500b9100d2986400100740c07198040500c901100011118604406500d03110f00c0321030002c0c000c1c09520b05501e5076241404211f041c040640301d80c41040f0308801c03a038001c226901129602042250181c984166444000c0101240400210801c4440501c00e40018881d1803a03640d4000c1e0b100707041042e1170004441b5074004c00d403e5215109042403140260795050043d040c0d540f080d1b6112550b440284a00a24098030306006 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 776465098 1250 776463848 776463859
    0x1306020a120c020715110f01060e060310090f0b090c210c0d211709030414030a030c0809012001060306061a0a0302091c050d1404030b0c09030705090123 67
    0x80c414551000d48845c0ea05000740f400e10410181d0640700c3d403c0801745007460707503258070b0241c001440c050403040c07035489940110251034a24518007682e6058940c0048010060354006035440002480c0500298120070850210b84040f1100303000300303c404d03041001e401c880c103401d41003a0810304c104001000c1103c0098070305600c101280d6071182211804074001c0b490400b54140302c00700f602d104400007505500d0040c0039440c1e60904502c030316160752041c01003040100f020a12000d45080028404003610f0341030343d0700952440203444019141d00402d1165042102800b0045201e001c407060100d4456905400000d1551461900314111000350380003c15884141c040803008090782e206584144401e4140940c1e40c0424400040e8040007000155110754145c00c00d010600c13400046820740c07604541c0760040300004000d001001809203100050103103442c8000a1622003052015003e0042c014085818075500c0d08005241c03010240c00848103207200090070114030440d200001d030310203402ea40b03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 776466348 1250 776465098 776465113
    0xe090c0306180c10050f0403030e0306060f131d03070b091504081603090302090109020a0306140a061107050405090d0305060a3606080703032a0b1306020a120c02 71
    0x18500d0f00c900200300700c2c0d482802c2c50240e01c07808a00507000c0b0b55074540d00000c1d00e583c481d03c2c4e00c0e014200e000d00e01006c500900c00c50b00002c40a08160000441c41d10000b08141100001022002d010f400280c03040c22000f0149588480300740c2c400c0000c1c0059510034980c50700e5074504046a24580b0705900902c01d000c060640503c00412110301c1100c546901e074403215941c5103560b080a44a200d21540000d42081b280c000010310740d4000d41c0a0480e80510369030500180b0307501e40e0040360b1810000300c0300d903000c1d02704c08007009140d0262a41444200d611415a0302d41d582d180005070480300d086070010350782d4100342c5280321407543c0752083c80c0d070001c0111038031881c590401d00180d0030070000e110544416501001c03907148000d1000d4852a940500c014140f24854503450015141e06182c80304a01060b6586001e000f03070301c3d510003940340c20048054100442c281a40380d810814102901d9120b400500000f070b103004c280140010402c0420035202c2c002c1c4d0880c4003805508075251107600000f150450310 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 776467598 1250 776466348 776466391
    0x26040515070302120a0912050d060b03010902071101080403080a0902010c020409050106030c120320031909060201060e010305121e16020906011d1e090906180a030801030209100e090c0306 82
    0x60a1080585023464980240c81d00f040014641c0743c100c030001c05004000041e000744190000e00400f44141111000d000400d4015131f1402d0081c0c6005001c07600a10003d01d0030009030b4440d21469005241912190025030049008c50b6003030b0707006990b0f0380d440e1102802444541c8070950024901244001c03034191150314010040c0d03801c0310b080004200101c500448100c000c00645800e030940c1c01802a60354640100940042c0d401d01c140000355090110004541c0e204108072030403650800f0282c83e9086181108413010382c40300c566202d80c000005a013810301d41001010300f42451600140b290550007900420902143c001d001d64100010100950362403158a01600100f0388252a5291440c81c071a0f2061201d00c0d070302c00382903000710020003088450000010042d0185074681408c0c0c0015010780700300c584a40890301c0141c00f056002c0010001820304000080d84510301000542e4200d840ea9101c44481c0f0080e50f40241642c44000d020a2620b42400a02c1d0856400055003d1829094 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 776468848 1250 776467598 776467613
    0x1e050f09071a070602130b0d0905010b03030423190905090c04090206070605191410170a080f1c09021f0906082a13050126040515070302120a09 63
    0x502004180c19008141d401c0350034090018140500387d0b0b00243d0780c6510030b2900e400c00400c180c240035a4950b080c031291010b00d0501104580540e16007529211140e101e42030008141d021058a0907000800650003035007000c0d45854410252070b11290124940c02e002c1c1c1003524200b5400748562180340361485100041e17544000700c0e40c1d06680b1440110346959120400c48900d01c030540c4a0707500c5070034a8200e2000c038112040d40c40c40b80c64071951050b0480c0e2500031440c40780c5a4030b07026003400d40c0200ca031480030840070b001030701117001310400191030009902081d9039207488410f20101c205482c0c82026003140707071809000d2166942c01d0041c4640031644a4014040030310740c4541e40030302021501280491140024514421b00041036220310503c00042046d982c0e4002c1400c80ca1ba000010f42c085110342c0303d1640c0c01c2ca401c0340da00340322407a180a50030103041824052300c219824030038561040c810070038518040744900510b890040c0c6031004100111041d06c0c005260152a61030100c1080004180 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 776470098 1250 776468848 776468857
    0x3011b0809120d0515060d0c081f060809010204080d0909230114031905070f0e070503072d0906090807050d0b07090909120f0e0102101e050f09071a 65
    0xd555012131240c680e00b00720458800000a450f0b08100002180380ca0004244c00c070780f00001103560343c4d41c0e04d540c400341e40e080e000d0b03108140f201407c85940d5081010521070078039542c03c002010001450310b85d0b150111850490900c9010021031007140c0108240ca100344a051a200400300130b0030311205241050819000050059207010184940c1c0c00f020354400f00080c0703007030f0041d0703000d860340d04144e41c02c21640d10300061142d810b100d03a00100108040c0a040f000e0b50080c0543e4480700c1c21500c4018054031600c40e40c5403080303002c0500703515000140125503803415200f11340e500d80d05512400c0c1003000700188050f800c186d80642c003d540402441e2070300c40e44003900c203810012084c01e41e280c0d603508450141c0140e000d00449030815449405004c02103a0300da030000d0380380e111b004030b0a900300410b80d4075849181e40e250150f0090300c000b224030f440c144c02c03203c00018001e0f02400180045045e031000c82e50291074140b1040c900074200142000100401e102824400305220502880d5001541305c6104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 776471348 1250 776470098 776470117
    0xc02070e07030b0909070e07020307050c0915032a03011103010510050c3304231606120c0c20030a0b04060b18090a0204021803011b080912 61
    0xc40d40011a607501c29030100407000402020101a42002804240d541c1101d00071042041d815901141da840d00000865242c1c90f8440c01801000040307400300401e10304000c1c56a8503000441001205580d4240403988528843c641858801d00c40030070541990324102020768026854804104030401405083da03045501c1203031302146a100e01d540495841c05261080c80c0c00b80300707400c0d079a00b044001040118690040c3c025005255a116003101e101c2d00713003071701c019140401c49030341000c802c2010305078a1072010700b1904654200c400301503a0041548164813007c0000c0c0ea40d040c0000a1105000f24000c80d5090315018803541c0894540c10001544408984e0310005410f003a0741b0580c0f41409803020781ca4112461020f0383c03510341460006466000119403062030215981e408a002d1450b009000300000001842041180e5003400300a600035000060803100c141d890614598090050381202d07551181485001c43c84008040c1c4903c4014055191039048850300c8040007510001b510080318 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 776472598 1250 776471348 776471369
    0xb1c1211030301080a141009030809100b060702100c02270c12130c050301150501120606081302031e0c090a0c0e060d0e0601090b0f01080105030307020108180a060f0606030c0207 78
    0x581e21b6440d40340c00c01c14000d508420341044041070070715422500e184d1281c185002520b0180103101074580440d08005040340d0700c05814405c4d00007504105059010822960500049092080e00082c006a1041032018900c403100c0c6030043c080410907440035001801d80b039070b4505101c44c0c9544040c80da00b0003001a2100100e00c81c255080c84104d42681d001000e01400800c42e00d80ca84401c070041408a000740c078041441c140d040d4160108512a071000c031a000c0e580c020090300d03101810b00b044141c0b05010790340b620503041065a1629032640c1d1050400880c80145018040b800602c00301c8640102a172107010f1400c1d15040700b0640201000400d60801c65100b03940700e064219074001407145100ca1060f42c070483c000480c110015500c502c0d24090f040340c6d1007011003180401100c0e0350200b40038140d0103030424002d80005500503d14103402888140801c0380c52401942145c1c81c201c06c10303000346d0395543c48503804514a480f605c6458013901c0300c1c0c034051000b03407080f9801070364072070a03807140c5031550b03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 776473848 1250 776472598 776472623
    0x2d1903020d08040f0906090605031911121207171e0d061707030c32060c031210090509151005040914010501090606120b1c1211030301080a 61
    0x4002c08a401801c03850100e81080e07034030b1307521580003080c16010f070030aa00c1ca042001f107075134030780020011070500c00a2402c5800f0010380d543c486004c090813605540240300c000c0c07620100142031218200d00d0b2081c4216940340c40c16410540746249824141d1041c4640411041070200500d108171215400c004400d07940c2e032403031421400700a00d003e41c031000e42250b250704015075046012411600f00d9014510400f8516216201c4030407a00740000300c00710300100312082d003c00c0c1404201c0e0303401412004044c58105016546181e046d0341c0045602440322400d10300700900600051916000740845c41d104100c94a0300034501940e481d6401c08002006185400080680440100c100007070312014106210804481c0740c03101c00f68808143c102c80315401d01c000403825424510980d011a4400d0380c8518060710980072407801055400340264000b511b0380e407103c062448810340250758500c01d6040c1100034850a0004004022604400d034283e04100b0040001c10310009903000515000814400f10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 776475098 1250 776473848 776473853
    0x100303110a080409090209010906080316020a090c02100509010501030206071e1712010b0f070f08190507151a041802102304060f08070e2d1903020d 65
    0x180200d010000b002c12400107000b207980c52444c1c100c1c051080c400c1d5003860107a43c0714454501078074a50700030180550f00a01c050544208036517603810003503001070140c8080c1030700d61401406407501c40c600e02003da8010a00000000c00703d1103182e82c8002003c0c02040341c1d50459000400a100c0d5000141c0200c6000403c24621145094903440003540420410503603050540c0c9030207245c02480301d000d840360b015400080c1c04080001200e820080450419203401506d0b80c9001000c111030909a440c4401804080302ca2610a00c0e0703020318007130715210300e500c40c2d090785482102112218460240c403410000c3e02160201c1d0b59009950031241100c02140412100015901640c840e800203940f0000701c0c00d44d20320f80741d000034280d000211368260407041c0020300c3c0d00e0819144a513106d004000387c0680e4461103000d04c6040350540212807032034000c507400c0300c0e1000a00806c000e08031540f0188404400120600c09210356075a03010300655800c5450a000c6202d82c14100c89444040c0c0034441c1b041d0180c08 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 776476348 1250 776475098 776475103
    0x302090612070905030f0601050d030f02030d050c04090f0207030f110a02130c02070522020304110306240d0b13060902060309010f0501050114030711160306090b0a0510030311 77
    0x5004914541c9a46410003006007141e24511489019026081c0070858255002c201c590513100c0c0600301d804080348907601100c1e100c20001d854030450005101803030a000c024000c0c00e024000c100061a00c55007800705400445070342c0407414290300c0c4104036650000e50441c0c141e2030030403c103040000c50340d0f203002c1c4807a017412071010000703501c0380c0001190350b041c81580e40160782c2074000b9801c40d2141520fa4003402840c000c8000342c0c6240011502c0031030255441c580055500c240f2440f11102d00600d19800700385441e0090b03600c103e00b10f0b094003030001d041d07018a49030580d581c0201c1d00c9620841c466203409400e164044c10f040c0d14000b40c148a032040c000544c015000d5164064000c0703a5a103848001a8000d08c00d1031260752a01d4208000082e03558420301d01460a05d0002c0c0754107166803215401501c0b03d8081540c1c1c8880d6004881441005c03090900d0a1001940520404254000c5500e42101c00d000c00900c441c8045240400307005a50a8000c6090152541410100c0c21900c0c035482027071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 776477598 1250 776476348 776476357
    0x103211209020f030a06090b01090204030803040807020301150e07031406011d0f06270414070806010e06031e010b131a1303200d0b060d0305120a0212012403020906 72
    0xa805200300380c03017401088140e50065003030a0040403914145c0c1d0325200804164800d034030020700326640030300208003c41d29203001008524801400060b03109400c2048a40200007075004001c1d00403c0020404004e03018040c030004000107401e20300461800c1c40010b003010340303001c141d10145c1501c52100425600c40c0a000b81d0380c064002c0c0a15200c0c2850b240c80d501c1031603402400000004d028410203a103040134000c0414140c1e21000d103141980d074000040b81c000d440101003d04001d0b0045900701940c403800000c0d03000714001070000f10b000740110310b46c3d680942d040cbd1005010040410a0307000c0751191610000035203402e00107850b04c5468a610450b05d9002e0014940e075020340c241000410081541d043c0c01d0910740c0102d0380358007004a001004522503115401410700111100050b89501c0c0c0801c0344841940f00b4280345082107540c090020f284007003111200b100e40c0d80068034035821084101c40380e004150000c080307244c1116003810202420340d402071800c181074001c01d81d02c00307a03510750040d05d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 776478848 1250 776477598 776477629
    0xb0a180b16140408030a0f0804020102030304060f1b0810060c0809090403021204060e0405220b09010603080d05070e0901061413050301020d05011509050a0e0702010b18010321120902 80
    0x59860f0303500c07036614680383c0d40324030100004100074a4003800c4079401941e0281c406c5805070091401c55843d41c442c400a030260002c8000651f03602d2001d01d032200902410000360303950643d42d990a078a0013a003030060415050300a502170200084040002070350000031940140000e0390b0ba458552514a0160700d0010310f0f070902d240d0a18041404100980e02010807881c1d2101110244a1501c0d01c084a000b00040c180241522265501d040d50200d40034000e40760700f0940140000030394669a450380003080d0403000000120316182d500303014506a00c04969070b035560084801807060f514207a0040c000350191040c0f503240103404035075004402c5404138800014039000c2e00956658226108030f10080809000e8604080c155000d00c0c1400c0d440780e4109410348034050070000803981040b00c2910302a1005180034110b40d00c5006003c981d444030032001c1c54034107003815419407550452401500045040d880c0c1c1c403c1384003503c40e440c0340075481815605041120940000c1c03a00c45800860300c09540400c10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 776480098 1250 776478848 776478887
    0x1e0301020405152d0a03240b0d050115170621031b0c01201204030c0e090105190e0a200906030106030506071b020d0b0a180b16 56
    0x3da44199004500510048604550540c1c2d0001004400c51040903201180d183c24082400a40d60040c000e5201c00c115441d00e400031101d021032440385034186001d54012a14298001c2134100d2a50030341e0203081d025010f03140c0380c0c0981ca0aa03200c010151628059031241e00501c080103e01c2070307101c2e04407120440000000d02d03000782080a60071aa40d82c008800d04545001c0c0319024604114080368103076003e881652107441055aa03031072841280c01e454208120360040a600d41e41c6a800e06c00107100130b503c2507000342111031401e402c0351105000182440f8103a41008108080f250b4800405513482d2140700002907080004440a032404040c01ca004144903c118020032280c0745c0c3c0c4065148055049500800390390f207a00506087e01c807140700040041d0312000118404c58020004a0381c015071800300500070681c20f400107480c100c17814a0541d60442c650f011301c000038019004074100c284900703403210f4440070315079070b6076010315002045811208400521818240d00c148080049080c88c40030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 776481348 1250 776480098 776480119
    0x705071a0f150405190c02011d0d0809070501140c0c0301050f090d050c0a0618080a0302030a0b180402121006140306070807090603020d111809151e0301020405 70
    0x1410003040d10705545254192248101d0358205180602449218a8030340392040d03590500140020050014111b8000035952601c21482d005104088000b81441540d001090f1811445101a0480ea001351081820741c0000e8014027690b6040301d940055002d1158030555240000d0309841d08260011071100d90550070107080c400903221216000e406044d5001c2550b219180401382503034076103d84a0075500d20740200d006000840c486600940001c25071a50304541b0301015130700d0302143d034031030b104040c080303503001c800d02980340701c28443d88004804c25038050400c1ca01c02c3c0e242e254215001003000303100b03031445003050003400b1091007a22440010b4910910100c0c1d01c40e14004215604850013600034405c3c10b0000e50b4180c82070031140d000c3d2620740c0f2141545414103c04074080d41c44107481200b12519114521110a01c0100070064041c10401040c18010148100039034000090101d40e8102c410008030822030b95a100350b4400c9800d41e0f5a0700c14a03500003000310340603004a5002943c07146a41a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 776482598 1250 776481348 776481361
    0x61803030e0105161d1503070201021201050f0607060f0f09050f010f02071e0503040e0c0c0106081c0c0213020a0c030e040c0e0d02012102040815040b0705071a 70
    0x10030004450200030020f021566500c1c42c03513484880c40344010b40005150301c0e5940811040ea1880c07007003080740501660800b946c80c03070003030b121944180c8001005030b5000612454004111280c2409000100d9040c0b0200b0390312000075465024411015204a90310080c81d144105546d100034241c0c10f04100c00c0c400c0e0621801c00949030948080c0c0030b4015403d01d149400342100c1442102d8200760301c9040c2c03102d840b1046208030084181803a046560340700402000c00c414001c0242c044c401c558014400f5036800884480301c2c00e5840b035134840300322680840014080c1c811104007024403601146441405000540001070880e51a180e034191190b01c0090810982e59010b0a041e420314000c3c0c5511760903801032018070048030059a60000040c01e008552001c51818403038105182d4014900b42c0182602c44203010144c1c03246580d662b00c0981c2c005810030000805000f45c2d41e0403500c02c41200083d28160f240c0f00158040200300c5001c01800151010402c82d800803503140106980b1503d0f5664641035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 776483848 1250 776482598 776482601
    0x503060a090b0108010902151615050103051504080a1110090303090512070f030305060d02120c12010908030703020c030408030408030a140319020307020307140a0318060f050706180303 81
    0x1c042961046030030000030590780c1c014001c0c4a0416070103080d40050415400c080e000708c0e004610740d0030448001c6102140030421060201404050104000a06501d986003c81c0381216220614058003450402c11001c00d01010642340348007039a00f050102c072128440740c00d04020b088151540e040b480c015840040c113525a029008043c070442c11a41d1400078101ca00c40039002e00726006020b00101c0e1310120001b0710075000341c0c0e08000c000e8040407a00c00c2c02d0740003c6520030710581c40d0202c2d034401101d00381c8a00d050b840c3c0c07403c8040715000810240b4803584500070700c0d100090600f024540c000a140808035800c00444000780424029251070b2070700c0340740c995280c0e0b00140c035920016819a042c224160007540c1168001d190a60110304c040305070b26145c2001c0e400c000c0902e001e40c00140801804182800303101011004014060300281100c0c0c0303009805002d40c503091040000341018148481900030080202140d4103062032a10b901251401c0c50191640220b41c2082c0b008075a807150806070103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 776485098 1250 776483848 776483861
    0x60c0c080c1c0503150103150321030f0902012007050d110a150e0d030509030321070c50151902030a060305010501030f03020d02070510180503060a 65
    0x407407a00784025000c0c4141241c83d80000e64121604080d520589400c56000303520003041170a00190042c81c4903030781d490718070b9211100700000c119180c1144403400c44640c54441d80d00c007150041000c2104440300d4000038040300791900517181540c2c0e4035807410b0390341c43c04000746001024001c3c04070038a60418a030090000f4910310365075014103485140410790180d032486407100340c0720b296140403140c1d00d00f81c200152560b03400c4094040c04000c002001c0e0b42e84083c8000c1c0300520201208a081094042c000c9468400081a03a41040400b800e000002034a00403004850760216400b0300310038516001c864001d2003040348400310071908100400c10898541c0280603404064021340321042e082d42d041d01e0440c0c40480d12900c82001910885408079402d50146420424102e400281d20352039644045c2111070a82050700c03403000414440040650400070b0828a10071440a0314032585084003085400080f00c2005003407040e0502c5e4181c0a1000000c84c038020301d002400c480042c108042460000c084 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 776486348 1250 776485098 776485123
    0x20d021501293f06060f031f080d230901081f0303082215090f02090103110a09020f03010e09150c0901090608101202030f0a0b24010804060c0c080c 65
    0xd03140f05960310401282001d00c2402d015091600e0311038440052000703030340014030f1580346040300745920f2944065694514040c1411000030450000d580c000600349900e014851504aa0003001020074520841c080e6100d40000703007403c070340301d444688500e0781003a008580180d00700c17a1080c00005255010b24018054032141c44800b407203100030203021651100c2c0340d8000d007517041a400349980c1d049044e80190441070081c204841c200c85540c1c00284c5c241002c2e48191801840c840440143c0d240c480c9101c0b00401361003c00b1480c101404460400500051043e0310982c00c40100081c41c1c494103014195140451414501e0741b071400c2810441190007820000307000401001c0045201c0c1d00664282c0e00a50b600412400614070303100d401c0c0c81541c0590b1040f2303014010700170405c008030f404002029869106400d09a45442c00340d0910000035040190b0386207000030180c409039107980120507103030400d42141c000300c0c05610843c030564400c0746115004102e02c2001482034000344011032055107921 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 776487598 1250 776486348 776486437
    0x10090804030b0f0906040314090604080106080105160e090a0207122d09030206070c080f0604051204050d02040e030f1602090114091f0f06020d02150129 67
    0x440c0c00c0296120088226071600082c0c3c080808207012230f00400c1c1c0700300c80e41c07140f410740c91074000301d8030100d0060b400660180480d40e4544600703104a171000e0042e158012041c480349083d6003844100101424034039050b85018014040114410f0307181d580440341c40da1380006010400140a0100410541120b00380481207003040306909403c0a5022209400160982c0c0303030f00d0414159001c104060b80301000846004056000002d000013040c82003912654080c0b014055501e4a818154105542c0715691407102404100900480d590036940c01d60080d015500013441e07692210520340b441c421581f581c80640b001250344030220005401c60706604d40f00390303840e6586927a5140c038001000c0404512030b50040074000024240c4c00e001c019401c2d000d0030400d600c1d40e041e51300d2a1034400407000360000c1c001604041ea41d4200c65404020702d02a40c41c505510305001c0d03140400f0481b0045003078080f800140340e0226000c5180c00003006980c0e16080464013805000000000c811128110300c01c82d04000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 776488848 1250 776487598 776487601
    0x1006080919081c110414060c010e06041b181e022d0906070f06090f080307260604020702010210020d051008030a020d2f0609010f0908091210090804030b 67
    0x120500840d500d9214250355141411b0030140c02c030030030503402c44110750440300078040c80007844800d0041c01c210158200140c44541400c3c05c11903050b410720140100d0841d00c1c0482081266004200381c403500d020404000f88a20030f82681103034060394001260384c42c40c0041401d000c00b0300c06048040311030000040c07200a075004180703400064083c49050690210701802208003040301140d1602c24a403041c1d40c0020046010354404400308018481920b0f003c0000c420001400c4d00800b43d11152901c44805108040860204402a4600404507401030741c000c1013060459008002d1000e03200c035101c01c1507480f0740d1b403010301c0c81c0181000c84103010000701c0d424000507121008001c0f502180d0b80f541c00751208021140080d41d040002d030111122130003d603032a200400c00036006150303121540c200034082d18240b600e44182502d403489103107a005881d090301900024500030803104424020354241e040c4801c80d2185038241040c0d500b082c0803650400c603407081001038031070003801038074440c4a40d00d00d40d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 776490098 1250 776488848 776488897
    0xf0e0d020307090c1206030c03020f01090e04061d0307020a0302011404090f150501050c030306010302160506161d090604051015090f12031d03070503030a021c0503100608091908 78
    0x86d01c0d0248000b509140401c202400503080038202800b03480018107001ba180c60707685403007038042c0c402107d044c0c44d6240d8415032034605d900340d4002402d41c0c00080d001141040d5a68000801e100b1140c800241400000c02c0954600b0500b0b009550007008110410840e54130203484400c09040c01d030301800d0400c0551b10303000c6459800303482503840d0f01c2226030082d4115070b0f600c80190025440300080b40d150103003007042d4600091041003040d02c01c4c1040a91480001902503000d090b0b9074a5100e468441c031414001002151540c203011a40031004417004030701d40c1c441216000c000840ba8005490681300c0e406d074581c0413030b04004100200e82c116401c01a4940d0b850b00c1c40080c6841903140140082c04082404007084d04400d0745107210400102a10703501580d03038000a1a50f0b00103040c5a000d07030082881b0803034400721403421300c41e040800e040c030b2032441c50503032101841c034401d5000380300602800f071021490100d8100241d071840c00803c3c00c40038240b08030341000720007a0411a4800580306503c2e800040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 776491348 1250 776490098 776490101
    0x1406010206270a0c2c090d120213030c0303020601081c030c030e03030703060e01050f180a060e040b01170706020d0f0c0206070812010b0a0f0e0d020307090c12 70
    0xc00c605206900390200300a5842c0b001191101c03100803424072401d0210350105200e000310383d0060a400c840320703000c1c0e4a149056404000f40000b0800a480001c08105d0017020206881030f18203101d1808840c0c60901c0703c203441c001e0192254000a50510341c0d408020403100e141c80e50103a034000e0302120380744d070f0b40d410403c2c0d039a501c21440e0009004090350500202e0340650402c13805008141000300e03082004544d0f50346540c00446024001039122801007003030203009410305001d04130540c0e107403c2d40060039010031075404803482088015140d84002074840101584698040e043c188041011414107080000c0013210a0160303115689001c2401d2140040001d07190007200c0e8180c000d8403110034010b80030340301c0c00b4030a45503c0c14031042910300700040c0c0c0c440b0014441390780700e0607062f92943d441c010003160b5610705800271401000100640d07946c46402144007811070b034151400500b03018000b070110b00c1f90031807a500290144142600812129903c0d002446d650606e640c4d440454020b004042c1e0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 776492598 1250 776491348 776491351
    0x31081e0601150e0102012a0e010503061813060e0105060406080109050c10020102090d0503070c0b120c0706180f0b07020a020121091b03030212030f070c14010e011406010206 76
    0xe8810b1200c03895003415402a900c8940d0210305000010384505100c540700b40c42103030040596080104589031400541d0480d4503060078000c20301e4028254034204001c102203442203580d00205034400700000d5030391281d100161000705d1340082c0601400ca02c1d911058040d08081d50ad85100b2806d180c004203c0010501c07481c000c45401c4802050440000028002d60004040c2c80c0002c654007081903801c151a00324020049512540065940b20035034208003040c0314080d04030340306c1c0760000c2101507803442c40301c10410341022006864654801c2075241140040244807903a0528110261083c401d026200c0072811920340654201031550341d034414120b0f160010b21100902080c1003483c00c000c00c4030900303500100d1104624000544107411f8031804c0118007454440b15440c01d8001c0107000701a81442002d212810400c0d03454214103240c09952255900203201d40200400c040d040300c24000448051604000e00302c00030040303240310840300c038003a19104649420031005400030400729440000c03404e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 776493848 1250 776492598 776492609
    0x9030a03080f3702190c021009080a031809140405391804080a030b010216030605090a080d0b03150402010903030c03020a0602031005031006080331081e0601 69
    0x3510741000303c0710711003261914582c0c60426400d114921542d03494800e0544080030301e46030301011110501c10481c004000104100c10096110420420740c000002c804e44503941c9410704403400c41c0e0b52040580354150541c00076000b503003400310868204590300e000c14080ea0082098520320b248096a1280201840800c100a8109400807540340301044408e0414010300034405c90100b00200076603d06105c05440580f01362a000a0680d5941e4151041e28103180b403e00240c09100100f024400f104621448090b015580f81c000040e10210140009210954841c1180f5100c0c922801100e0040040081c982d0081c4502d00102d80d8040800301080d01c600e905a442e5940c89003156000c40c0c03070010b0940100c00354864980084006207050001c0d40c0724003042400d00300c6951900c030800d417504400d0200e0510b070a203400400c1c8042d40c0c0c00310481d10000712a540300c400c001c0b800140f001e05070310240d50b024200140303c50041031030a008031701d074000714020038080008848045452520b80500b84580c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 776495098 1250 776493848 776493901
    0x1b0d06240309051e120c0d08010905010b0f0a030b0901060e0f150f09060f03150f0d03080f06120a0c0f0b0c0c04111b010501080f0a030813060209030a03080f 69
    0x3441902110f1301880d1500000d035200750303240c10f90680140150394000c07500c920095040b0025801d11503a0103c0242e004200c429018004c5514100500c4d601d0300c00e04c02250300d02d500002d410441c0c0c40c0a50442c0e5801c44000e4090a90b541e0341d940d0040100d9244c494807807060b64200d81020091034440d0202a059002c801c5540c50600040b9040f20150b000340d802c960400c0b024010782210516540145225250154044903034410354801c06c02c941c020102184d2003496868588030100b640201a103034403402c42d545000c5203442c0d46c0001401c021070384011034440d105190a41d001c0000b022510f034222520100401d0810741c88402100d800c3c001c0b0f403002101a4411010f031481c030300d01a0071103001900c100302d8481c58240318000a5030540c4e0f1900d130300c8489a4468004103d00131042201c0980a4035a0014116035101503800801015016060590400301d02000c0814406654112103145100604481c4040c074140340c0602120421a20341c452030b03800300300190803440d80c0984100f414803284207 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 776496348 1250 776495098 776495113
    0xc06050901050412031b0b0906070903030e0111010b1201021801020106061d04021b030702030f0c13240807080c030a020112090f1e02040b10081b0d0624030905 70
    0x1070498060142c0380c090382040019038144101c00303800c03038100c54501e004402c07800b01f0345003a00c2c409181000162124080051103041000440d80c88001111181c2003460002d03021a58120307514003500404002e164011031020415100302c0c815801400e49054100710f11038030301c00d03502c01a0300300d49492295001040c100040000701e40b2202e04611044000188010f09060001240403480082c1c41c56451081d0f00003d11714041d40303006c200b4840401e03030000083c039860300b1a1003c5071101c0413803600d00c25816207503001c808071150b52202907900c0c50817031070b1000705071b50350741d240d4554441c064410311143e401400c0c0c4204541c207011a0102841c2d070184c4070442018a800b0703811000307000c1e88074159443c03641948000002a00c220380c07103030030b0289007107030120395001c0c1d0042000715107900141500c40c0000d40865460907030020a03ea910060910411001c0c40800700c2d5100d0601c2542091200c55107071039004140305100c0030182c81ca03492000010308110b694184294111101c20360040c1c4203903c00303103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 776497598 1250 776496348 776496359
    0xe0f06041401110d1406040603200604080a05060f070f0c1101021c05030714041202040b15070c1410080a0510081c080f040c090c0302040816030c060509010504 70
    0x14018100e80724000900c1d44400001c460054101c59076031801241c40e010a54003003101d014006400c01000c5074104042807031035031084007510260a1140d00b0514002d500e8060340d9462096034010050305055480c144440c1c5045a00c2d14400ca45404031070410310042100300340f0513141c046031800c482d1242c440c02113080e19555484103240d92600d0441c455031100c5070402000c01000030343ca0170306071140c580b01e04099102510000d40e030186590900c800303210400461403a40e800d084416011790300080d03124185000f14810207200141c502c11800b00207800030400074419a8081150304c0382102c5c03407125019404000201d07001038105000076000300b0104410607843d9101d030350800c0e8040040c4082c41c2c2d0b40c000d0030f030800003018603403801c080f80d460040c4541904408000d0303210101400c42e0f02e091400396118040103000d805007800281e659542007a10f103000740d0445001c0d24010b011500440840183c80e500b078a0903000840b0840303880400040d1180c0120151441c90030141c456a04050a00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 776498848 1250 776497598 776497613
    0x30406060f0b1c0b040e190507170c13021e031b161209080115091506122301091a0105090a0509040501110f19140f0d0f020d020d0e0f0604 61
    0x801016449680c601210104580c20401c107810055107c0c9038468902450400c14108032442e03002a21040d044844800d140740701107140078815600f25410844400069803120003030080c8440148680102d05000030111444805544244030720700c1041c00807004c0b40744043c07050240c5c00c031441c0c01010507800100041d44146e14540d00130068941011030720742d03481006081d1000d2184002200b407101005100d980a980a8000d01ca02080704a024003031a040f00100070000c0385c40541025907488044c0c2c12482e601181d8040c0700710855242d00340703958403490201c00030a5002d02e181c07541c1c0310801c0b0348000c9500407800d8400d41c200027000400340c20325050601001641c01081120155a1100c00e60750f4020715102a00c2c00121022540da01d4030100c51100d0b84030760701842280240603803502c404406c0000300007118064a80b6096092f281d4552001460141c00e10f0710805400500101e85100300c9441580500110059a403081c4010040b8114094403080900210305150b08404002030115004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 776500098 1250 776498848 776498861
    0x1050301031e021c06060b041a03070306050a2c16121104060e010206100e01051c05060a02090a090e0303010e18010c02101406210c06030406060f0b1c 66
    0x4282c1203414042603a000030303000c8620940b095050100b00b01d01070240070b003610412000d0f081f07489459107010304000001c40d107204a00603a4490107000400109a14400c5e040351005001c06448548003a480d450160703c610012400403e00e400804204825101041001d034068040030384080f00c60301c103025081344c648040450380180d45446549070b105007524140104000e001e030740d44000005c50300100090074500050501003039400c41c40d2050041407084034401d411907070111080ca00042492064030b004850540340544540a55001c00918800d150020640c0d904200e880110707150b102e001031401c54001c4445102c07258803d0005000a902d4000c3c003503001504880f2280b0724003181c111490a54900c1c640d0100160452194907100150a001c0ea846000000011552514140c404207920030708401030a000c1d1092201550740c003440a2008108915000d86a184d50345010306014001d02041e104000c4045811200080c08001d102d06903617004501c940621410080702c02e8101c080c124 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 776501348 1250 776500098 776500133
    0x4091b140306061b0609070509070905040917071214070314030a1b0c03030516021c09090c0507110301020a0c24020307030b0108160e01030221131e020105030103 71
    0x304000e40d44000740d131450290382c064a000014215481c000004606282565200b039004400001c01d2000d2540c2100000c0c01340c48068900240044230350402751081044250a1400c9040001c1c51030b0500a03020031160543e441030b1624040000d041c2c0c0145814886c3c03201c00360002da16500c150401066100003160000001503012607170f0804210b0025454400c4450940414030010542d400c150700740c02550b9024180070004802e804005802a46807411225001c41119500e54900c0000b03001d050b000f4040c0c4444801001300034107024000d803070399014010545c2d1885004c240420310b0318050003100d0f0070500a0b0381e40010700e1080e07a121800700746030075869104d0b090310880c1c00104d400b051014612030b04290354081010700e07031080007418008020b0014203a002140303801d002c0c556041000941c44c500b0a03e8010f07500c070ba4114041410302c1400c0055400c0c04c0c07800060010b8201d0110948103002d00806c1142c04004100c00c202d540c090303680e0340003030201740280300400c04904198224440d950 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 776502598 1250 776501348 776501359
    0x51f0611030d0b131103100b070c0b07150e01091403210a02160308011e03020603150a0909120206150a090b010c051f2d0507090308030c04091b140306 66
    0xa142c5030884d00352265190744403c4541c011080081886942003e0720080c402d04601d240380010356103c14140d10228010540c0c04480011310f20300304408411191904000d00c3d50401c50340c680280c00901804110006a0b026a40e00080c02a00310001c01125940856000013a203456218030b10301a00c030800400c10b01d916a802e1105c60351f02440e41d65214440380c443c2d5150300b01c07907040c08030307d030505140c501d02220110011002480143c50360070813260080c070b0080c2050314900c0c00c100000c108500a4000012107424914250100041d80700c400305101010380a440c0d5903511000d13900b040341c00071850243e02c8145400d04101c4800c165001590718070061501c0e05801c100e584541d80740c081201c0e010310060710443d01e078030384210803885088812146504450040d020b4031001d40c80341ea100158031060a90750f0710104500d5800b8540050003540d01001d865100d00d060303000054190000c1c883d4980650034041d00306003101c0f0789400122544d0094461a0080105078881107840d0401054030750483c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 776503848 1250 776502598 776502619
    0x3061d3715060c0f030311070807142404030e04140702070503010c0512010e0a201809040b160318080d0b0604210f0204051f0611030d0b 60
    0x2800c405000c11890a81000082161661140c0450207407085a0003a020018803007481ca000400305944602c415800d813401164a000104481c0140d00c644c440c0144039500c002840d03810025400781140b99154803006230769000e41405584070102d140d109a502040800000060000b03020381d00c2040b421002a02c00079521014401040c900340c015610000540e20203102045586400d02542c20740e201c251503c2801d01110780b02440d03000c181801a640e005202d100050b50a181ca9401080000701591520550300d4030340c507003850b107a80640344110420f10f283c0c1180219081035104c4500403a4012045481c9a071104030142c8045201000789080546803010b5080d94071005480e048a14000c200340b90380c400822503444101c414500406c1d0003100300740700401081c5041c0c5a5a80e14248404001a251006241c001d10140342c0f104029445403500c01481429059401e2444001c88031801c122401c60301d410090f2640c00080064009a5000304021000c42c2540c0d00448401d02c2c0207424104c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 776505098 1250 776503848 776503921
    0x504141b0d02071113150b0304060f050f04030e03070f03140a0c08070806090c0609060703020c04021b060604110904020a0c140303190b0a03080c10060308090103061d 73
    0x80c2c0e40044002c4c2d8400c1c1c42c106402000307180c64400403c10038502c040401c0390301901c0500c0b02d103145151007035002003e4003000150034051180c214480401e010382c005c11191401404034003239101e069501750005484103040800b13500340020600251020741034601541482c41d03942c154111103121180b400c40c010000e5550010310303c900c003c40500491009803544070f040040039071038000000d2030f074400d9500070342c0e04900b1900c91034100c42c40b519041d41c90590b00d40725403c003a0b240c80780d4102d909400c030303100003a24409221f07910380001006050000342d680310388841040106403400704a1100c1c203250200026111468075600810a005080c06e0840a980c561b03220001e01c050404403845094200104228075012003104809009160b07030020040e00503400c01281e400c0909000c0100000000140303040380070001c12411210043c4210140040c2e5100d140c41004d9801030402e95002c6400e02d00003103078003c0c1e8680d210316034038900e01074030b041e81da150341e500030b07200804518150149040e541d11810 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 776506348 1250 776505098 776505101
    0x301150c060504051b0105090f01050a11030309010506040f0203101e1a07050106050102060c0901081909120201200d0c0c0b072f1f2c06010504141b0d 66
    0x4180d01400141c4179000e44011450009070520b42e4940c1040020001d03500b00785d13107840c00c04003040c03020701e1b005450b8003084406940391101740c1899086440302000300311020605410040c41138105540510900205d0004801603000950b9030342e00b0054282c80501c06d40c4038607010504230308404039046100781e64a00c1c0041124114090b54407502d4000200071040c09802d002d85c0f80145420b200508042c40c012182070080d0140f6042c0e641000001c4020460341d4240e000c02c1035105888042c100080c1d080b51405490100040c6c1c102030140d401d11040b008a10a44480c0400507807900081520300001c246601004180d90842c182c14442d480004e4030101d1810300000e0f10031409912501156092084141802c44512100c0e11284042d281880b003402d41c040ac001a070b50f07140c02d0103181844a01c6040030050401e5000208006402c01091103040d6129820160000f40c100242e0340c06076210390038041a61050186583c40348820f5001c951040501c00d0760002040c0d03020340c102e0528800201900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 776507598 1250 776506348 776506351
    0x206090d03050318030a020d08060307030b1f0e100306091e0812060604060f030c030b090a02120117070302190306021b0c0d050616140424090b0301150c0605 69
    0x700042c401104004034140112001c0344070103c4000154100a08110000d588001d61580075041100150118410741c81c10040c01002c3c550100340d82e00c0b80c6c5800705241c021880200079130314885101000c00100100e506c001e450040007048150074009041d0345500d009400002da040360100509200d1590f9049035050f82034146202c0c9012903520b03052581e804111160142c41144100d404120803c00c082e0030294060944142e414045500070140c4001d400400382024035075003050001d410441c00305403642c001c000e9008074080d9a501031762203214102c0e500300203200d01030480d03201c00014009440c100d030304080f400101e180d21804903620799490350140d801c243e00c020344810460b540010110014483c3c46401e02003511113120b0700e078807a1220369a4440103010003100700d1204100c03502041c814000c64020070220b4041035a11542e40d420300d425218948041c03d101080065440003032445280504119111400c0050a41c0d08000c0b45800e650001883d0105006a091024002803000d00850303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 776508848 1250 776507598 776507603
    0x2120307030b0a060509060d0e0a020a030602031f050a0303210e010903031410261203010302120303070c2d0507080c121002090f0a090e15040b0f040206090d 69
    0x301e4190060800c0c4000f460300c5400001c248032050010b01007685a50080d192131120014000c80d0401504101782d042509400010390007100080010092043c5500250b0042c04103560108400121810040780d120450040130307408080c030101040405e11807110742154040d000e09248544040c28040e1044407150312007035009035103a40d030b40e42c14590540700d9042c1280180703502030402c0c50040440000c1c0380780d07030007a01140c10580d4106103880c40d1490148103000d808108544480007001f402c070066420911049205440001c070b00201d2100200070b0764001d22181d11200103142941d620010340d20424002c0815a02c5c003078000382c0c0404680000619682d000b4806012043c2c20440002e00340001017040301d004003014285a00c00e103000068a40321070342d22000040c0c8481025000a0900c9580c00c400c690080801101091000c103071ba02c00c81001031040c040760403900d444001c0c00b03400c003001c84001c1c064030601c40c005036400205d03c0c1c03840e6010344000d10302450581004c00043c0c4004941c1b105 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 776510098 1250 776508848 776508851
    0x90e0c0421021003020a08060d05010204050a060804050106060e0114090d0803010e040c2111131508011803081f170717010911061e0a03020d05060f1c030212030703 72
    0x50900b07609103203081c080301d1076444c54294a4008044406401044003900650050991030032180c01c4c000c0c00e40c140c1d4042d1000411207007031070780d0351070008120220a860583d00c9502c2c0c07600c00607140e80150f0340710741400300607154008090320621400160790003500c1607175044840702082400059542c00254040c000000b121a01e038101404d04c04441c0300b00d03400c0143c20300380015181140c011010018001390f5400305079500302c0c0c0d0b03031100850400c0e0804c1c0e18402c24181040744084400040707a0404050f2500b41008004410710404001008844e959014020490b03040200d0100001843c1403010400c0d00c0111461a90340c620303c100d00c001c0f0f440012100b540001105111281800c00b4404503400400000c2c40f5094150700c8404001c1c600c41081e5220f88400a00218903042d940380e104000d40e4511192074803004108009001703940504600d28080c0d103080b0002e0820300e096919010f0030640644030408030000c440c500458841100b03000d42c10361103a407255048000780341e4015032040340e19540 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 776511348 1250 776510098 776510159
    0x28050a020d1109070f0f210915020301090902090a02090108010506030a09050a050102032403120309070305070602031801031a060f0904020304050d0936090803041b080304030201090e0c04 82
    0x50040142c6d07008002e070000c006000c1c0ca94016469644600c0410354000d03c0009201902c614141d148510b504400c522117900100000442e102030381e011040850083d165069541c4d0303070320f066404a1054141c018003151420700140101d0070010013459001c64040c500248c11007858a03102d18012560400702c2c0e60380c0d0008100f05403411040024500006400b00e424541880d00e0000381e2585130261241030040c81c044005111100200f203000011078203c01602d84181e02d072701000751030758080070200c100c20b5492032418549520030304c0b4200c0c00590264596280041050401015510610941075004010b200300c0c81c250b41c0b0740c40198025032281009140c0c00303603045409840e41318242c0c4596405825020302c04c500100700700280010021003c0e4801c0c01070481c0d6502030042c402703003070b000c0c02c01302021007008108103e15410140007903886040c03211241d03a070980d0945d02d02c01d50100070700241d40c00e0410800314008905843c2c0150208041501306074850514030500c0041d840d010348102907807203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 776512598 1250 776511348 776511377
    0x5090402030423340e0f0a0b060a0c1115130306142202130f0e06060a0f0509150907052101060806010503070201150828050a020d110907 60
    0x1d4100310701203003080900428500c0c0f2115980812030610303034603a80c401c0080190140005448940080e03c0600d407a50b0aa0900100440170038100304ca20209052400d44290418500841541d002e5021360743d0f01c425040440c0d8402c214400807424241d08004440106510dd52502d000780c1070401c003001400e05468914282941640c1d60988580d5918035054244a6841200400400c100d450310094080700c1807103101162040350b05503c0c0a584034588600100c148145800800b99441c42c041260601d072100390410034101c041e841000d42058102a00304a0383c1420f20a40c1d0380100041c0093701c0c2e0400031030203e42610360407600f290018400203904030302814100242102010b10385012803507581400310140045001600d0907040c0440840007030401c1e40300f50003006003000e80e901c444c115140c0c3c591280d655280200105034142088007000d00b01816149007003009181c0060007007416003803603000c2c002c051902c0c00090b112102c2c040706074a0a42c55201a40d0b02800d02e59441c1e44000d04182c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 776513848 1250 776512598 776512643
    0x170f100e010605090f0c1e03040602071a010602030a120f020f070201080f010e061c0507082d06010b0c070801060b0a0e0d0f02010e0a0503061f0e2203050904020304 72
    0x1500f2941c800c810710b500b030005011045540c80d501c6581444a50340e10b096054000103d40010004d030304602400004010801c41c054000c0c10000e40300b014010325074140b40703c1c8184124800d002c2c0f40c0c0103034010710000300d02c00d10809240c00300a003002340004150484d031024400303992028803980b003091400101d100455074070400305503100b0400d8544017500c2d41171540d111110680900300038402c40c480e80c0f8903e00c0c40703200a2040171039a80001140c038001d031707640c0e0390b152583d40550110404003501009a510000c045140700c410301040800f800150703003402d5a0102d65080640b003001c15126441010500200c24030441c000390400101d01c1c0d0300c500c0ca01c40e00034140c4082e0545580100b0401c00840c1c002842602c2c1c10442d581e090030700a400c50000c5020810811442d070255a00d031091505000b14410f201c26205100030740f03080007281240e220401002951403e0350624100e03444030081c0800e100032424207010242c42860f0951134868400f00250990f00207407405d031031004078000c600c85c4c04401c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 776515098 1250 776513848 776513861
    0x11b0b040b010b0f090d0305091e010e010c0503040314150703021801090501052d070606030b0a0c0f05090301020f03071d0406050307031104020708121806040b01170f100e01 76
    0xf03e42d55207408100d00c036080050040307041550040c0100c561420426010f20252001c030807018102580000000001c03291012118400d03502290340050034480300e510a29180d804a0b800a008514091941d81c6040d0300744d003032801c80c070014003401d5a1400c41e208514032890140c01d645e50050b0b02c80c03048079991050100c1640415062000101c0c04014690700241034074a55a122034008070310014a20f080d5015002031000c6096202e40018003404100c150342c481401c0d030340100304e92801c1c0d030303140401c900c111401c141078040410000c0e41611002481140200100310300a4005810108801d40355150b5070429101c00000c039030441b1101c1c07142c8200401c2c81306110b6040380c003805000d15010110344c8031009400040c0124600c4c2c0002c0c1040c1c0c5a51301243c941c01c0e4000b4500c4d94840308180208a00c03401521144070078102e0300013160102c0c00029080e800707503030050742c255036a0340303030178402c1c2c1781d44c2018080e2405038058800d84001410f400d02070000d00010100d40420021020a240c3e407c68a4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 776516348 1250 776515098 776515109
    0x2030a080c03160e120d020a05071d18030f12060306070c03050415020102041a0928180b0405151503011211030a060618060b03040b0a0b011b0b040b01 66
    0x1020300400a000b8402c001c107074000c0c1e0f0103040c40b1000c0035440011030426250203000d01818400c201c0007842c550b500180440505009400b65105942c0b01c1c80c0041007d03007105034110b480307002c0c040480d0038001030340042c0daa0104e501044074644140040c084885800800011008030188420400c26043c00e01c4086d601c02e011345070a100b9403141740e0300031700710b4005c0c2c0c00ba0740540f9421101815400c0d000b5412140500031906000d407695203803091000c0686d000a20450280006c69210030054200c0d401d1003011a020102d103000707090911800a1b44145400b800c0070300369132100d10440103a1070703a100d81c1d40261200d201d42d11181480205002c0741c04100f04070610f001500700f004104030700030740c01103071002c0d81c1c07280d80c1408214107070380000d1412403c0344000e050b50717141c6940001c40b01c000070301080340c030030808405000320787d95840218040e010440703009d0510540c1c0070000c1c4184510b41d210015160701410101c8081c1001d0300441d15a01c0b5407002140c400345040284400c1c010440c030000d00401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 776517598 1250 776516348 776516371
    0x6060109140307150905060f0c1204030312090c030602120601021603110910081c021c0c0b06190308270a060507030e060c0a03080615090d020f06030702030a08 70
    0x1c00e1040441d07600d05461040b074804400c6010b24001c200d03c0303000808010040200442d440c0c4140d1103503004c081d030069554406600c2540c0c070824020400d1410f88048a81517101c941202c03009240600c0a4a808041110070b25030340040400000d80e0362010b4031242e44482c00070012031904400280c50480c000e078060650000e02e04003080000c6211355401d4080500f500e10010355124066200c150b103d00b81c010404500a00441c00008034214404810001040d17089a01040707420070007035440b414001651001400090603c001700e807120342003030740242e005031020500d80c080c0c070304560010596406c2111049000500411030748101c50040c40385054000001d60118070000009058161a110748814003030040f4140050500500050700c1c0f00c04007520130355a800844150b907071116034040c0e003200419030351408202c45040000700c4821120310b0300c100301c2c5403101c50002c00c5101104400201c3e80400040041401511114041c60096015400450300d03100310810181207800020030f1140c10341c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 776518848 1250 776517598 776517629
    0x807031d01020c010f151a092805090c0904090302070e07030605040e0601060c030c06141509070221130f171009150e0c100504090b06041203110a1406060109 69
    0x952010401000b102c0600e042a810303102d01010300f01550160310225a4861252001c3e0714400d08504c009d04480d00f0390070407240c001a2100c041120011b000e80d01c214580b1000d2104041350308017503100c100450b01900464120b5a81c0d41c0d503910100c003046a010300041c0d100d00c410415402d00c1e0040c00c0021480d24090000ba40c10044010044241100041c3c2001540078891042c8070b4242d122580c40c1b40c41c40100107491070001410b10b56042c60012490123030840c82c6c0064403981c40031415040007403d0340c12045520b4140700e5681c2c451b800035400703020074107480c04000520403694080f440040080182c240041070b00f000c0090f04041259140f04440c03800d10751400005042902002868290300c4d000007a502c2c07522210b24542702050ba00c03260030030415651065100e80110150049400c045418001306002d50140492800ba512440e03024040d510201e000280c050512844401501d0b011101c51403116103925900308880c420403501a000482400210750380060384002403c6071003803402c4503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 776520098 1250 776518848 776518871
    0x20d050f03040b0717090d08130512092209050c06031605030a0207021201050910271a070e0a0501030902010c02040f0f0905280309060807031d01020c010f 68
    0x1448001c01c01409a61080000b5002030700075055a4910780b909020a1000d2a200d1b080a9949450821107000b0403810800103402034100600341114940c031102500e1070726020681440c890300503800a030340c050403e5140b00e0056030302d0210b02080034880c40000c2947c4803281045400c000001c1c0e025400392901300204031410b04820300304e1601c0c03041454415aa69076414030f150090003103b0000354400040c2880d080185015040b0500501014041d21803204901294000b224000d02c0c400400e000b1101c0c207148203602d1000c0030018540100061412400081107054603a40121901e802203000c03905101141c0c00e01000b02c0c80540000e08007000b02400b182c0018290b9070041c0802803140351a0349051300c0c816410f03005104003580110703003804240301c20715000e519000008680000c55003071440600b60060011000301c1034039050340b50203c1c15818a0b60490340b070711000f446ca006041d02e904052100210180e4175072424450038000603121906e00c41d40d1400d40d401840001c0000b4101283c100e032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 776521348 1250 776520098 776520127
    0x506100e1605090312030408030717061507060f140924040f0c09060f1403123001270504050d0c0c09090501050103170a020c010c02121c020d05 63
    0xc00d9650b410840d4440e00c0383c2001a142296180000c082c038000481408104140e83d00518021549a01c90429240c131704950009401000c0f2040c0d584411b01c244001c4d00c0b000c500005108950144001003059410789504c41d003514940d42c02c011078081d00c6820443c0f1840280080c0c824035114240052421850769050201490054005004586510b06110401401026030030050002c010244102e40e501c0408144640003446007400d50420f9590042d035901c0c1c081400c10103104240303401400d008030034044140b908441000c407414541c030400c0e07400e10340c012080c4541c020080340186809030202286403107402d00144007014106c50904c414880040d4003c14089100b5415191040300e802c118200303d03241d246658000103003286454954400c1c0441904514140c1c0c2c000c17102d5114040040740d103001e16101d140a80d10050704081403c103350f600c16031071148100d000400c80c241d0511800030f00d0b4201101c601c503110b454501c801c9803106003501803001e00304030482ca0800504007412581c10a1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 776522598 1250 776521348 776521381
    0x60603060412272922120809100f0e0103020a05090a03060b040e03120a09020d080a02010c08010b070201080a05060321031005221e090506100e 63
    0x208401c0341081c1c2ea608241c811203207a102d1a5200c0340b0b500c400180c245009980c07080380c4c05100b040c0310301000038500600405080098410140006a150100d007402064450030701100d04c3c1c3c001e80a144000422046140300310b0310681c01080c80b03a80d601140070812112031b43c3d035010f01c4240000507001c0c0414642103540031021040038200540d0355020320904485511550041c2e80e80541492404401c0c0300081d80b1128540505507803c01a040d080c0645a6990159445646400c240b81d00042c0d05c508480e004100040d202404500f03024140f682c2d40e6556812011200b030041c0c1d512010380c01c04960081c0c02c2030040c445000800d03c1c100d60341e00000c01e9082d008056541c840e0700e442c0804d9490303c08007c1001a588003030209298040e031030041188642c400d030342c041c1901c1000d4202040a1401e014420307004800c00d60148120402040500e000d440c1d0131040c88403440e0b99262150014040b801240040c0744a0400341100c0e05c5e14004d012149a00c0d034021807042510a010803070031506814240c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 776523848 1250 776522598 776522603
    0x50f041109040e030d060803030901110427060509040f021009080d030203060d0c0303051c0203010513090f20041d0601120c0b0d02030601030513020a050402130f0e01080f0606030604 80
    0x3c18800c5000e21120314520030740d800c01d040c40d4609400061408404400b07140100080b500a109012845101c41d50714081c2d4000c1c2203440f20304480d403c00861808000281d04020580c010483c50781e2440000c1c1d68107412a0240c820401c1484590708601e40810b00e45001d13029410301c0904c10b410700703216a598072501b5071300e8004e050380000805d095680710380740f0392a02544031440a10403510ba1030700405c2c07500180b4100901d07405200c0711249581d0325000f40c07810b03180f0240c058606040b40c0f40116001e082d034030a0a490041d69802080d000c6480c0640460202c80490042001c88010314180412506100e80708030500c001030110100744100840e256044441c00b8801c06d00c0b44000c0d04180941c0303820355220b25059000001c0b207000c1c0c142c043c0c0103588182c000762020000e0f0b554000c440c3c450942c03d00c0e00203602c400207035414085450300c1c8c0d0240800c0503032021002400c1e070b01d43c1d10104081c0780303640280910b24202d00041050314000c22400d000680040040c216034140600403039034501c400b4000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 776525098 1250 776523848 776523851
    0xc120210030911150c0d030b0307090501050d2d1b0803130b031b030a050403170f0c1b01060306050610110706080703090204020a0c0309080106080316050c0316050f04110904 76
    0xc0d4030044d039000140e540b4409074000351a6690360ba110050010203926840314003c0c05950800503c0422a01c05c4074121600509181c0901c041a0350b00045901c090694200c440c80c0d0b101d00855030407541d07074039512a81c0305540761751201c408003410f0000c002c0964415a2103a100300714050b00d0100982001c0e08445030140d81e151a6103403d17500b0710201100c040120031184010040210040064020500941c029201c28100c0c103005000d903081d428003104c82000b04e6001c0c0001c50200b80000004000c1c039800500344092040e40c0040043c00d40e60240d00030780706d50352607006000c114902203140205109880c14070a40d05500132180640b030f0200e51081d0010300c0418400070302c03041e0180c0c100c1100c095008004658442d45c03208068030b40320010b14141c000403e00d00c1c01243e42d80c8144656400d90701000c0c021810803000400d100406480340368219540d029060400c051a20100003010007040310320171144d1901d04020501c42d8100c03050200502c118181f5441c1030210b282c0400b1070f244c070402940e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 776526348 1250 776525098 776525119
    0x201300f111b1c0309212c06120a110a120506010306030609060e010e1204030b0c0405090f070f02010c050a03050a110a03020705011505031510030c120210030911 71
    0x10014105003030340702e2920b2800d001581d0800003d502d54030a98190b4420f802a502d0640c1b1180c2d842c84e10764000380000c01141005040044107204c0c20108005074900303841c0803840d400350102080c400e410801d045e070410010310080c85061010780c0030b6803a01c00480310781541000c052140c0101340c180e07180400000d0951b5035001c540264869040f0703a000d141c1220040c0300701c05840c504500101041c01c1c0d440019443d0001800200c640030032008901d02445803014181030468452640640e00a490158040c604000c00142a115104901c5c403806002079901e8081ca00507202801242d00b1965500841e45019007030b00200e50000b091340d100c841c891400040e10f81c0d92440d85d030001e00342c1385405030400801160b1225902c1d41500180740c0140301e14000e000c604244541503280c40a6400740941c1500806480c6000c2100d5524040e4482126603085241a0756501c031200320b41610b42100030828904840380065080050294a9080c1c59240811403103070030b0780f100e500407268000d03070911a500508 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 776527598 1250 776526348 776526397
    0x30f02010b0406030804030308060103050106050f1c0507090806180307060b01020a060e06150604030203030a110a0b09011d34050618240307030203040201300f11 71
    0x41c4018207014000e0070820500303403030703042540d441e41041c03104a0010b035000d000a031341075100780203c40c100c3d29191a014180440c44032aa40d082c1c01507081c0c0c13841c03010b100e400700d040b0403e2402900d006d101c25885415407242484c20702810300384014213165020000904e41d400b04039000085844080d000070f40000c0c00322551300102d00304101014060601c0703080c0880c0c101202030100d0060300403001d1990701c242524440c4103024240c01288400b9501d5001030120109036402201c90034002ca0451050340e01408556450103070010041e40d00600030380d942c0307000c0078113642c065203500322103958100108221400351011001c1c1c9001c00406d444210344071070380e080d24603030450f01250140030014502d07a00d0f444801c44460008440280c098070a0303450680c0d800d11034403045092000d0030f0284071120b14580e9520700c141e010b584090400c90410020305001e02c0702c20102c04a0050800389a01000e1001c1d10350a140b130103440341001e54082851902c5036400500d000601140d06039003020080c00075030040031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 776528848 1250 776527598 776527601
    0xd030b01091e0f050d030518060906031311040e0307030e130e01050a061e2d060c02090a180f0212070b0c0f0109030905060d2c070905070c030f0201 65
    0x1030340222120700400409080b01c9102d005124140ca001c0c504020070141d44d4000c01c100301896980c0034001c90802c00040c08070298000002c520044041c05491401e420440842c0302030340101c84100e00b074540b0510f2101000340a5034082c5400c01c00300c6090110000003042e090f100d02c2015002002e101024081c3e4030a0340341d4428030310f00b0f060000010800c643ca072240d414064a01180c105204a181c08008a80c4514070000c00700148000d01d2800e40307890420700c00111070b1f1050390500100e03032418608000201c3d1440d030702c140503018aa17030b0300082400e82c0c414460060700c080c184180007820b0202c918031804804164050b01a0040345110300a04a8004a1125410003605131514010302c180410040b005d20300810703207202c440c01210882c03c07040c08040d00f210054900100081c40c005002c118900e0404050721440d1301c01d4900149481c0c000711001016151607990094800c080145604250000d000f490000c22413040d06000c0342c548950000c000c881090002414002c03400c1301000654800d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 776530098 1250 776528848 776528867
    0x7021605130f1e11070c03080c0f030d09231c030e01051f0b0a050a030b010e10030f0f0614040203040302070e07080103150e0a08090310020f091507050d030b01 70
    0x2604200110070125104800c190f41003280c101a26083ca54083c0c40000d8950884038050b800450480c0554155656100c607580401400c11441c424011381c0c5844510600040c001400340c584001140280c034900300c2461100e90700000003881c0784c842400850398000c034521004100303c0b180e41ea548007494400780d0080c18080201502076113050100000300d80b24007007031000700324841402c440c4565160740b03140c581d03c0f8480784400010340512a1400b154081c0e04010030541050400d02031010212000c58400d000311128100001d032103c076421209540740c031514030320785080c2030705000c2c1a0400c82900c030f4502600602d0b502a0307500000150500d13209000c948007810b14a001c80c0c170682071114004000f450300703001c10340741d103540503001c407402080f58400c0800101052015001022442d00d41c8004c40e0864050a074043c0a83d503a03100c07412815100900101c4050f28001d80c558807a0010710212103520308108011a50030001c0c3c0300810800502c5000c2a00c0764940800e01c90240801210480e05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 776531348 1250 776530098 776530121
    0x41a090c070c030507050103060b071a060d0b040506060901140105040b070f1a0f060406083a031d011404080304080702120d080f0c0403080705120a090e0702160513 72
    0x140244007001300900070484a040b00c40c2642c0a01089454064456840c8290840204038031f0380078901305100c0115034a940d9003d0401460b044820441d511344a510f4042182c08603107a810074401c0203030b181741020196002d007482020342140185000c0006e4000d20031405088107182d80810301c00d041000142c20303061050350001600c4d800031004403511018110995030007080c0c1c800d034400106141818407506044604036001050801690b0340c06041d0412000f040c25000c613180b03051300c03008000b080e2600c059240950340005440303840266110781d0103980301114955904143c0d290f4050b24250688a4000b5003004016960361124540500240702e01000290003200000208058103008240768100000303948551519503600c0f0b50340800700c1011503c4030700040c0144001d1008c80c0405000d80802d6224008581c04007140340b0602c040d68200060348000141c10490521800403400c11094100000c3d0000300b14848042010101031003450140034010b144000c5110003404007a000b8807150751 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 776532598 1250 776531348 776531363
    0x709142e0239030c040e07090b153112020906042d0b1801030b0f0606041e031a060a060f1b030c1a180615040c0c0c061d041a090c07 58
    0x895183c0d1b507a2035140502c1080600d501d80030b100511810628618041588000040c030324088016540203c01d102d4900ea00d40340075240754210b00d8590000c01d91030080d00101031550042110751041001410004204900860900e0740300e1100203091b6010f0186000050300855030806440404001003142c008503552040c04555051350b440341001c0c066060702c0c018200303d10190b640740380c0e00b14951030a840381c40d04130504000130084a20b10044220744080c01d10182420349541c1d4440c290340c0361441d03440020fa03d0020301403041c00d14040d0500c50040c805411b054400c10160200a404039810100598400800200001c02c0500c10986400c159500c019518651038662100318002281100ca60b001d54048130b15851060200003007162049400d906000020800d150902c4060320094008000303000c20a01840005514004004040d02207030b0b940401c0907030580d103010f8a1907400b88280b405103180210b01c00d41206400704000c440101510b44100544907142c09140360b10540c1c00260940 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 776533848 1250 776532598 776532611
    0x608250e06030a1a01061d010806060a0905093d050603071110050109060605070510180506150102010605040606051605030408010e0c0312030709142e0239030c04 71
    0x2010704013402c2c1a50700643d1000324805240c862442a100c01c440c21501040907500044c17103a00d054002041056035514103030304c00302c0c1d840c070200e1070400040c8ea401c000d00303551241194440900c11148200000c410b940141e00b008415803102c0e190006025240c000c41c00080001c1c1064020400f584005402600b01c4ea0003c1048941c100200000e00030202613600303000000641e1403044081d14480ca8100380601788100690442e40000c0200d10446d440e6100701d07402400c0422401e0210500c101400c07100406d5800303400000a084480a4200d0b5100790b103095070500c442c55204050303c88800e00c8500d500349045403070510740d19602603039110702160f6090030001d0802032400300c4e44a4192005070202c90000e401c0006151950100b201c1e80400600c4d4401c080010004040034841c00b110041d00c21400d003180341402c44210090740400a00c13603022560f220204640c10451138803030044030a41790f43c1c42c4000d00e1800c0b0a0425054221401c8491213440031040d94052280c0400342030000d0042000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 776535098 1250 776533848 776533883
    0x6330705010902130614060309010e0706050d141303050705070302031b011211030408070c09020307200105250e0d030206011a190f051c0608250e06030a 67
    0x80d04000b201240607225480d02c0320f0801c001401010f040c1c401b0205900c0b00361486106211581e00700a06000e9150340340d5041c842403907424030030030300680074580c0c40c1d1350754400904884007030364143c81c9002c054140f104204000004500f5070001d0180c1c2c0751130925030300c140e9420010715200c400d40000e0740c1030003440d02000c2419001c94494004c00001e88544045c804100070ba0411507011400381c5000e82d20800004002640d450f00820020f88902c900325080d60b10381142404030f800480781d40d00840c0e00654032003040b80c102260181605000310081c001898800541046904240c03210486020740040010a65000d1000f203203804001a10074140600c080c1402541c42200784070b042c8030002c1c0e15006010494004c4102d99101000e8040b081c0e404112001c100d446541c03003c0c0d0310003003010900001042c59843d40e02d07040c0240040308081095410405001d003410307503046068140250940c202c001c80c50030518184216041c00452484590354080480c1c2812070600000b0f00c810400303124503a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 776536348 1250 776535098 776535101
    0xc06051812030c010b01110c06070c09050106020604140102090a03060e01020d0908071e0302060708040c0e04030c05060703090c05060307020c03160f12020915040609062301080633070501 82
    0xf80e1408000091040300c0742a0300640c1c0000d1000303900c10039500440419061401c00d000140a49880380007400e0500d680c1d80c480d04201da03c281c11a500581003c020310050081d140c2d1591014071000300214500306842c40000c64400c0d8030b01c0014030103926001c140340030340d800390706550300d07400c1c001c10510010125240035840c0741d01c40705003262060b80c1e0000c54a64800c0816400f8861a40340d0020100d50b1180e10050762403030b40040c003c0f00d00541250700440c910242d80c0c510340c020f61003034903010401041303442c0c0942801002054902018075204400c03020418403001034040300c0042d14030725625110001c0c128180040707810f01a41508c12810003017440b100402d0003c040b1040c810f102c698258980041d072a0003d01d048010750301c0310404000c03d5101080d45a0142480c400030000604556201e82c1502681c500d0303802160842c50404450200404020300c15100e10024644100d440c1340410018030701c0301000c070410141e81140840c04c0c0d04003114045085440c4500c0403283e855940c01e01d000da0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 776537598 1250 776536348 776536357
    0x705090a0b210f19090218041a0603030a0c0c09020a2607120510050a0801020a08100302010207030b04061e0204180519090305040519080601080a0c0605181203 70
    0x900008000c820990a02e03a220400e8010b810403070b000080382d101c0c0c8180f280040b0000d2800c031911940d0300d03020301c01a51001c1010034510b211001205252616080204040d06124500fa10000400080209030381d008012103010b60510306000c50218034506000444d5103954004803005c03440000e803402d64a4000b09131070f02d00c0d41c440c01040c21205c810403c1d0f40071a081940d11101081c490031101a80740410b0700019482140e40002800c0ea5a9800c00224142c034140c0c0b1110081c1d600184030202c80780c0c00b010695100346d890100c000d14504d1640000c0d5a16501e2001400c241e1a101c04034003080441d13001440c0740420080b511041c1004180c05d580203502030f01c6000100016a241c130090030265004440c41001c2949651103c41e900c42c00c480c01a0091107400c8040110030130011985135a41c200d0154140c40d40000508010b06180429240c0320b0103802020a5030311282000000441e40340e0084155050742c98119128206e41550303030366a14001c0c500076804034007608030f1668014000040d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 776538848 1250 776537598 776537617
    0x3080144070801020c10020304021201050c0306120f060703020721021c17061009030501150306051f090f0209060c0109120507081207020a1218060809030d050705090a0b 74
    0x2509010b0740c80301114200d2140e5103020300c580c4c10143e02004004495405164864000382007590900040d00206003141c00480e140103c0e85004024441c01e401c2880b002c1c648d81e181c82e4010300d9030808a0200311703500c19004141ca000c264000482d441000b03001e00c0c054040750700070000d04400071501c81019480e0f250005230030190fa100e040215829611076881175102c10b0706207503250b84540302e880500c207e400a031f16802e02480314500c80000062400d10462455401d043c03440b2004c1401c3d481c0c00002c0c1c800c0078091843d140205200c00300c1d05042880210215190745000040f50001400014040c0c01091191a400702c0003003407613891801c06401603c5203500c62504206081c82c602e2050313400c0e00420102400513481400062032281c1c805141c6608003a803801115013000255880058100420411800080c0f807002ca0304d031800000e078000800b80001d402c01e022940b40501c2801c0d0349000f8145444411034480000c00c045a000f03038101d41c15408003070185c1d021543c581e06c0d00300d030540c00716690 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 776540098 1250 776538848 776538853
    0x702190806070306140409032a050610181a10030504050c01090b070303022101120507081902010804020d0c0f081002090906011409060703080610090303080144 70
    0x35000c601c00d01c035880c1074078051700828045c1244e240a01004010050003141840120700e000402c2c070108190080100081501886242c50145000ea051480c060b001d903040046030b1805100c0307a103000346c044a02c46011000060030084015092003503010100d0200d030800701e031040510499070306800840c8103a015208492924100000440b20b040e094490581050424030420700001d100782c0040c040e08101c086c00242140302e103121030100d0002a448105442d01c04010f01080280c103125440051001b60081c0207505c607129800503c0d6a80300000904105031038000a0440d6926008100030940080c0d00c1c06040d81c841500c0c04007200b440c000c0c82c0c03c1d80318516451200d500076008860185002030240901516043e00544591090305100c00800c14184084845910f514001c2d04496009a0300d04401741040300500c602d40f80003040c00010040c05c84000e0001c80d4005108604581823401040201b01c040c88151051540007000280c6d28800e091004080d14210700d071482c010142b2005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 776541348 1250 776540098 776540101
    0x4150624031d030301090e030d051302090c16120c200406050d02030a08090a03150b0a060806100806060904141e15061803060405010903030b030a080904020a050702190806 75
    0x1c2040381c4040210382c1c6080d036208000602810b9000c1c0c000c0d07002c080102007207904205801501800341c0d00111600180902428820f000f50304d080c2e942c050300141e00448251809030b040040c0764840c4200200540707507151000c26005103074071440c084411503800000c00100c400841602c0d001001c0040c644a1059081101c040b8140c6840107984542960080041068565a40c1d403100340307401500400f9403000f42d15a0001c04142c0300001c00300044040e00d0005881c000080c200310100001c6d400070740c1004041801c0042a446801540d50034074030908200c4501e40e12400020800d200e070741ca1054110b428202c4850444144503150b40c081c00c5008108040368105207081180600b049a280c90a0b0590459a41050a080780100f01d03102030306020f1500040040c0220340382100aa80c00c48141e0345d560700c882c06269251141e0440103c044015005c441c107540c60789070710781c007d150f1603c3c0308640c00220764603240d0150040718071095000d41650924501d0141c000340d034050a00c1462103a008000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 776542598 1250 776541348 776541371
    0x303120105091e1503160303030213230904080f04090603050c030609280206121b090f150d052a09011b02010c0c09090c0b120415062403 60
    0x88030020f07581c620038042d055500d80082002d110960240d254150060080714500c0080c030021100196001c0c0d200560384801e01c41003c10680140d52061010012143e0039440c1c410b50b11404e2610800c0c101c503104150380365410542c1591081005e820540d0301c00207000a00d80c83c030344c0c001800b00c9014100380c4101604410905450f56811599140e058000d46500070010041041b000040101100b03610041c407150b60100d029640700a082c0c000c20b00d941020071012103200c000307840c0e02c4409a1041801c1c41080e1022818400e0600305041c45031450381c0b804902c514580043c2e0b40551701c00d4a06002d2070410807001000d480469241c402c44aa034100c440769000e18440c100c486d29007069484225003600c03114256035007610381c4401ca040104104030440404e13a42c515140c003501911100103060750351843d01c8201220030b680a0894804180306604824a0468041d544660844006e0070300c46088140c9000074120ba40080e94440b0f504060490100d0154115990782e0001d610100815030400b03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 776543848 1250 776542598 776542621
    0xf051003020a17011b0e280b0c03090307060903020118050d020103091112160909050715020a15021201090b0d030311040317310501030903090302030312010509 70
    0x40c08069001008418100f1110828501c4003050194031000061100381210702d110b4160581030500700007440e04500c2e0741c0c0758580b10000c1e61107880903203042d8601c400341420744d0480d03203500d1081c46484d001c007007410350608400380704480ca00c0900130241c8103005e0b261310001d482080c1901080c1d0000d50300e803900f0064088207140d208145c0340c008121030000042c5038011800362000fa60b044440070400408800c294681e02c9000c0398103036155015091000d064002000e90700034540c40030517214244420180450000310b441400c1e503441e04002442040024801d91600ea095140201400307805600d02d0400b000380d03400340c00b500c203e00f01000d03a903903628280e50702540c3c6590240303075204240d84200c42c0082d000c0da00c00d00c03460b50403511043c101036880c0c452410000a2135000e2240100001e0400034801001c01602e9036006002040881341c41c807460004501c03169800340a060503641e84205043c10f00a01036040195801801c984d07441d43e4443c8003c490020030f1103918000c50b800c0c000310b900790150 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 776545098 1250 776543848 776543881
    0xa0213051e010e0315241e040b041d0106050306240d031413061e1b110a06120516020a0305070302011e0b1509062d030c0712180b0714010f0f05 63
    0x506947e5400300904200001041c162031880d900c82d41c0c4250003103a507204d40351803c90100348040001085450300c014107042074001460400e01c500a540c4c0415031025099821100440c1501d10200c034a109244c140c0b1203402c0d500600954550100f503043e5070200032030303240054070300e907035604e0000c0320440c00c403a00340b80300717219550000c580041007141000c0411000c500d80240680303000060740b624800411079510360f03500903000042e0341034030304254200317140610750b008803206041050384003003480000c0d00c800509000401304440041d501060510135001140488400030200c40c09941e4880c2010003000146840da008140002c410707982602140160344400768007031f00d0300b86070110400710100c295840034202e400340e01ca207190440300c004014001e94881c00007100c009070358084a00341404003485241e0301c0c03000c0000e01040403e215251841700c0c0101e49071500e0841d160407080c940f0000c482584054012075618040354021074004c9900107a0040d030842104110f1511507044000c4203010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 776546348 1250 776545098 776545129
    0x6090c090c04060f02100e030903070b071101080711011406030606090705040506070606030602070305071b030c0e09030c01090809121203040323030a0213051e010e031524 75
    0x8240420007586000d041c61010540162055074002d1b00104641ea00b113034030324840042e0300e520100e8040c1c0c0c541403c0140c0d001900301a144242441030a542e1140c40500500d442d60420242401141c4400c0c05541c92080c0c0c0da580c3c00090082c009800303e285420202190b045220340f00d44004180c00e41019140540600d42581e0707010b03d0241000c0910035180d000344411184a65a00c4001011900e144080c001c06482035482c5903a40a150500701220320b032409401305e003002281401c10002d01491181d104868025985441941d248103886056014030702c0d00400341d5081c084603908010514000706151001250318a444195001d03005980c3c1000360f00c0a542c0c20700400100e804a40101881002c020700700c0b40b542c444024402c810111a0025900036160310f17008074034130f03c032400d1280b0800e014040586122051140c080038004c0700c0e6040724070007410300000801402e56602d080c172080b07080e002d8001c8062001d0901c841228403502000d8820000300e034003010350399200c2c500807182900000307 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 776547598 1250 776546348 776546371
    0x7060b0d020d140a050708151f1e181b0525230105010603140f0609150d05060f0901151e181b0206010630020c06090c09 53
    0x202c1a81ea1146407510400c001c0e80c403031240c0e41812000602c200403150180c001c2c00080e00204214440c00c16a03580007038000c0c0030400c103082c0c030f403200030745109101400c880d405164602110455040c3c003512a680e03401c4500300840d101188100704c1159044000789600e44201d0518505400c00c0481d02c41c0903807540709003401c0c4c85018090b0103902d5501c41e480c04501806684d01002c0090b00d52180044c0c00b12038040c0035075101e4004200781c40d054420720018041c2036010140c64a0109500c1d01d101200034081c034440c80c0e0413404034500c9195602c40340c815080140052030340300c4072410110784e9041e04403840c0110550382030008405136018001e038905807155480007a1880c0c1022584145041a0b00241103614148800000c010203260301c1c015154002c031100041c030701e0490340b448981c8000c1c020b400c015035102030010071146601104001c1a5032003000c10307224440a1102d0004440800c0110002c030900100d80484041404240c09006014101c121400c4510070002c1c016906411524641001d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 776548848 1250 776547598 776547619
    0x60c03180a18020d020c01020318070501080c1912050c2d03011203030b030601060f1106071d01031404060e0615060304060902030f1203070207060903080d111204060207060b0d02 78
    0x51a090f0041d18014414200141c2002c140803081822a0421a0308014a07524210700e06614001401880003a0000b0300c1c0c00901d9190240075941700d0b200e05440110305039080c5a5480002d40310b02500c1003408041031080c861400c1c039008a903810307001085c418000d424403a894014449854070322108004c0060703012805d5a02c1d10540d00d6981c0382c40c020079828591101c18a88403982c09012882c041c10181e124043c0c001c02e280b41c0200203180f00308049100f680054103004201d50070940d601d29400300d1100080031400000c0c0100c000d4043e02c00d40d0701144402d681440104802a00b0030900c607004d034011210580d0b0313503618959000d051951229089007040010070003203402ea4004110460016084178516403511038154a000758810100e81c2144000c4240544558144004030040c081e41c9050003010b411511f410b0320318031807004009060390b580c3c03084a140060704001c1c0c40b00800b620004950350310f01400c29034040e5010032401c9902c1e516084011003649040103c141483e50054400c0d602c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 776550098 1250 776548848 776548889
    0x507050103021c0c12051501020a11041d0321041703150d05010b010f020f070b031b07030e0301060f0e0f04030306090213050901080712060b0f060c03180a 68
    0xa501414401034a1080081c4680c4140a98050104007130000d9562010203500049100c0488002600ca148040c000300050010750b07a002440c90b00e001e4000d604c111440a0b034000140041c640349011607400003400849041e10350000c13002c4d007050265030199411201d01a003080d0b20000c01110014081c001e0300c0c081028000001019590040c1201015003c2000400014070b15501e0f10030110340030b079100c103036907241c5580c050952114454640000c01184031a90151510740c10180038402c0c2c5440040001500301c100c41820020010319409083c5d601e8185080040c9802c10845503640070350b003442070018404101410040858504501c2401c00c0e45421011102c000e070007030016002c1540340c40022071040031a200800c814006010701d68501c91510b024800080e0050780800059041844100881280c08500c800d04590000700064407071202c20000f852240d0005034030ba0408001714042c2005103002000b0301ccc4081107650f62100c204004000c10846030300302c2c0103100031084400d809110 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 776551348 1250 776550098 776550101
    0x20f100201180f12091d31030905030c010c030e03010207020d050a03111b132009040f0504080a051605160303020f0c06090d05010603020909011407050705061824090c0406030507050103 81
    0x2000702d000c15072002d00101c66000504c103080d100a542c1031546005440c1f07020150080100c0006010039000b400030300e00700301d001a2142075810740c05011300041c800410740513502981106d40d1168010118440b400d060308001c0d5842c50005801c5010904120311070548000006520440c24032008035000c1001401041c402c40300300118206149030b0b2a043c10182d00841c0e00d0346010001440b40980741c860344404104401c0e290b4061300e016a152074001440045210007007141c25400842c1400d0b603a8000312403012808402010b006043c40c040d1102c2858444051812501101c1c000e130708031031411981d80d00413070321841806c816079400081008840000d0503c3d031382d1410058099130000850f03683d01d801090100c2d000712003100150350340d01030304d00d82c40c0c0052400c203800c0040d510707007642170101c61750700c03640d9035140079049a4114241103514402500e04001c1600b004030806040001c60b0601c15045000080c280c505514070b0241c03000381d07c0346041910801080b20341000c028070120345000010740 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 776552598 1250 776551348 776551351
    0x151c1a011b0b07200f06070e1206072712150b0a0522020c030409062705040609020d0507060306080d08010e06061603020d031107020f100201180f12091d 67
    0x4c455198810b000d0b031142028840c011082c5060070140c82c0c07a151000c40105900050515030744180c0b88507c41f403020711800110160301c030140e410107070200a140342c0301c01e010360103903c800c1d040800394010220f4031421005441036600c1c030840c03070f4035041022103200405a5130400601500b00d000050200070510f4030780d40c17101c02c1424802c2015107540004403030800380d90001d011621140d100085c1040348130803510504005045e90103021640c0f05010091041c074402110415041c141c9500208007413252075441801c249030f0003413215112450600d0a1a2162101c0c4600b0010a291540002d100748000c210314201c0c0055680ba150b0b2a8202640c00f1409880604880c0d04500c040c400600c8148648c03100c03103002c038000c1c0c00071300482e0030106009056031420407002035144000d020440050321020041140040d048550002c0980070302c03000c80c0146420003481c0f0728500070b4450001400781a98500409034085d24940e21001c108400a450600f110720442080562029045041d0300302080c005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 776553848 1250 776552598 776552627
    0xf1d1b06040f06200d080c090604090504030c0501060e060102100905010923120f071e1e0b06040e030301030b070c020d120e03010605151c1a011b0b07 66
    0x900349900c0e44520340042c0c98642200d808204481d0388006410b0440040e03c090702a8000140341c040d0301c14000600b5814042c181d401108004120012595110000d680182c000c02404100300d24143c24000c1102c0364000c8140d400e9403034042c010130401d03002c03001648100340c10f07001814100c0703a004141004124402c01074642d55a41c0e12010002151040c0e0401c2c0c0144c100117442020b200d00c2070040c2000d18a45c0700820900c42001041c2000085c1c109484485070412400c1005610f0100322005580f401b00c1d004208150200c0c1e000b8001004480001c035450086904a00c070b55201401d100490f0b1a09030403501c0c1d988240010030002c2d840215207907000340d180c500000700e804503a011a800308407025044a40f82c041501c2c0003a519400f01d00b90814500882c0280311052601000c9544d109051542d803050140020703102141517142d6103014006003581c1810080c001044035103c5843d05080010360005407500c6000308050700d000b800d018155001581c030002512000016110b061440052 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 776555098 1250 776553848 776553859
    0x30301060c060e01020a030b100f0c0b0a2a03060506070b04080a02030d180b09060412030c090f0e040209182e050901050f061e1512010305010f1d1b 65
    0x1180c00f1000780081c14200246460214140102e80f0410081000313007000d10301041800703c400d03408598403019848610380c000c40310305020f444442d0003801074800700c3c00e103101e83c60810706e0a03001910104120100304a241d83c041045036140d00820005101c0e081018106100c00c4001c200490204401485001102e004072071600020300c0030841071f41c2c91001c40340c0d8049038200d4044244030840c00d0082e4805120805000031349800d640e401d6500880100c06000c06565520441c060ba0040920303c015180b03256070440002d070303107904400c040581200e04138052a181c0d404610152011301101c1c2c01d0f800c0145c06003004004082080e005003200100c00c642c244444c030000a4900e4861203120f000d1803060001040030310300001d00c50441f60010b001d450003844900d0a40c565030f2040424201e40325011070344540c003155081408003250103125051101403450784000010801d0541c403031007105020f04400c1c40000c9201c201c0c94010260f5060400c5540c0003820003005004420710104c04082000b4003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 776556348 1250 776555098 776555111
    0x4020c0309030706080115110a2003030c03130909170a0309080d0f0b031612080417100c050f0d02031902030702030c120c19060207080310060e030f030301060c06 71
    0xc0c504400c642c800b00100b10614010300c1919181c846010309a2010b040c84110950403041e550b07542c14150270054149004045000b000d00b00c010710392100c019004040301c0d151105501c1003500c07940114040044e42c414064005000d41d21409003042498016000d0803000c2e1002c09840c0302940842500401c06945228600004610381c010300909805903d002a00a161080110841e0060070400b07100e980300c0009000c2100921415a0641d1030301e81c000081e00c40ca51070006628000c0d9086500341204031109070841c2c00002541280c07040c5440401d00070b002c0b5450050300e8500c64134440501c042010040c848250805800843d005001001440e0310f00080d042c0007400c80c0c10076144400181c00014601d99a00700400281d52010200404030707107000c80716a40b450b62400c4114800008511001c500c005114860781955421a0400c5980759a0315010f0602e1010150f0b902900000c101085e074155101d06000071184c003c4034001c00290328603428100d0076100d001c1407000c11119542ca810 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 776557598 1250 776556348 776556367
    0x30d1b0807120b100c061a061b0f0109050d0206010e011508070c0f05070f0b0c03040909051002040905010501110a03020607121e0b150703121a040c08010503120a020c04020c03 77
    0x1c3c50303404c5000903680355051001d440c540b01e8240c480083c400c0d00e55580b44080e1000503501d030703000c135110301d4901200038264011a020407418041d09808001403546010b801c0300510034041003040320780b0b609609440c0d075aa2100c011720381c01314080c00340c42e5025090581284085001c0c400454000c40142010405907090355504121150040000c40780c5400400c020031164201c10310000c040c0511040040c1408680409250389000d280700b51000140c0b150381c0c60303061200c288a4520f218006107820356669444403040c5014003401e00c80c15000419a035240c21042c5404907500ca1110f071b0650140c000f541301c00004866401000c2001138005584821045075111130071807001c010a0440000f042e104400c6041156070f242c07120312000340d100c04000140c00658030540b040f81c1c0c00e00c103200000c0c00d40d00d243c000720851070151035400d800034688108601c00301e800c0244c00d4100c034000c80480705c0302c1071202120680390007082c2891016a2240360180340034a02a000f420b1018031000480c2d08128a00c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 776558848 1250 776557598 776557609
    0x705031b0711060c1b0d021c02040b090c130e07020a031107150306080f03132d030506191503020127060903051218040519050702030d1b0807120b 64
    0x1005130031003039020301c40d54000b564840039820103e400486204124003020b40101c1d10789180e42d8641d0780c600c4140981c4004554655000c4c0309001c20180c0790f000e291030903020030032484d0310a5240c0750810916200005000c28021100b920400e80303a40680f0700d0fa041540c09035203c08204419880500a070040072131030a54651507014401700c0b980d00498200e1610202c1400c04c04408100f0441d5041003110141405040410204072030500024110645404483d1000b81c090b105a020015513500000010311100107a02401012100304445000700101e1003001222001b2800b2030560782c0440c0204059070041051070030242e288802001d40d81010003550046c1c02c040e4000d1804204241c6e401e20a0150400004a0300b440c00d0310250711702088080c103550130610301d41c450b91084c2d03103600c006243d40c050101401a04000080f0610050601b240080d4498001d040304c164464500400c0c40500e22900a28805e1107210392112442078503660710854810284004440780b890700c6600c4446280c460 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 776560098 1250 776558848 776558857
    0x110102090f091009020f0a031103010f0e090304030c030b06042306040902030a0f0501091a10050f010c0209010b041802070f020111070806070519030b090105040b0114030c04030b0705031b071106 85
    0x1400b001d1f1341d20200e08101500b00c480c44080c008a02d44c003803005200d0040c0c520101415603e0348007044205681c1c1c103001070b00e1407027181c1005240d40102800001002181000c1c5030007140c04990038443c1c07652102c400352401c20701072107107003c107040c0d4004035000b4107003640312500841c009415941ca4440944a41300c460140c540122080d179522095841400b1210900654500c004601d02000b400c6c0302c030003801c4241d154041c86200b86241c5d18040c01903801a941045210303405055040706607502c0010030696006442503151000e9440e00040d1343c201144210b5580907804402500384800d80d800441c1c0060b038003a0f004509219030000400d15070010406a8807a84440d0340c0c403a81c40d030030102a40b1a18141a20710420b260a003440e87d030726940e656a10360305544080c1d4000601007642d00040340d044210344096200c50400105001948070140d0080003542e009801e90201620340100c212079510044a00c0007006030760a8208420981d1035004241f400d0091090300310805500c00000c440350f00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 776561348 1250 776560098 776560117
    0x23120306030732060a020604030836010606030b09010e060a08070f06020d0824060d0c03050a230a0e0705180a0e0c150d0f05010303020d110102090f09100902 69
    0x100f05480c01c0300c001048441c6034061005640880c10210032103c040d6603801e02900c018188002c01000884030341980780c8581035860702610001c8805040c144403600d041c169040b0000c2542007400c0402c005010380038422544102900c81c0406a00c2c0000d8000340c290003401c61580000d41c62800600c00c10100041700c00350029512504146190070006860000009420b000b8014146c0c00c00034003001c9032490003030b2065280500581010b1882c00580d403446241403481d0403500e801c400089080d4107034401481608400b80402002006c043c5060322040c650000d61800c0040d50b00081c035100e210b0b00414201180103048813441600c60000900e41c1c19841452109015806d0401041c443d450244c542d10644110142052251003808211340c0c00e21494036100342000000d0018510009038046e06c0815020b01c01040556140d2400035190828000c081000030300d1540c4c0c10031313480f606100310f4200800081c41d00846204e0802030102100c1e0003451902c81030b003e0301d80007410140d940001d00c034958 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 776562598 1250 776561348 776561399
    0xa050604270e07290307050d2405031510051017010b070b060f0a0b0901050c0601030f12020601050f100c05060f0a110f0f16050a03080103231203060307 67
    0x2824010010210000f82161020400404980c0820400304c101220f4000e00f803071900c596140551000c00c0054180c09010034a4210020005001006564000301c1a150105d0a90340c07441004000402003017019680c0902921364401c00f041540707411070700062840c646003011805e170a0540c9441c0c030300c454268441603030034400080c10740800c030102e0288c82e0b1010013100c603010b000310803001098103001c45004500c61001e0006490440781c0c0102d09540b5503a0442c800c49003190303103901e8282032480354a00119100400007009080280c00428800d05032240541030f485048801000c1000a0254401d03000c14010900b4a642c0402d9050017031511071014030758030070080c1c281071a02000300c1c0c01030028004084002e105a8920400520450341002050100b4507103450360b000d41344e40480500d1000509070300c00d64942e04201600104218100d0340900c82d50300c41014010501a400e0a18090000c01500506044c030300c0c61840101454010300040d0458825607111821150407000e00f2440d4032515 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 776563848 1250 776562598 776562613
    0xa26040819030c14090105040503062e06230c0102120601090506070b0a02030402060f0d0b18010302130914010e0a1502040302090f070201020f0a030b01020c0a050604270e 75
    0x550790a0040720301c00c1c1c640e150401c415040040002c14456005202440409000807031300704aa11030000c0c2c03005064010305a4800e410f003030408000c1c000c09005a4440c465400c03500110504109190000711580d94484052149204c0c58024211814080140740203405111200e0324007824800351200e084003d880307040500704580007408030001940118805c14040000c60001b94002c2d82c4e6030b40001055801503140d0320746200281c5a80503010011805840104110740103901c0f540000000740750641c0c6150036003074642d2810b00050300901010750816400e03182c7c03013404411503114200003070058100f00c0299691060590070741d04046820740007503201d90b03103e90501034540b480c9401c82c8182c007021846d2a155074003040c8070040050103040703940355040014881c41e00070b4040380c28403668520550350b100303000d101c003074024500c0c501c1150040c814048843e410b07081c0140b41c5815164014255403c00d46040c6480c000d0703610122610101108403603109202401d039008845230b0f00100805089070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 776565098 1250 776563848 776563867
    0x1c0b040308100b0f09030c100f081f050f041b09060801090c092904030803011e0e160e030312091b010c020d06141f08120a260408 57
    0x1c1200280c4022280940c088080110b00c203002c00325114031100d41905511062810f00103805d200a80c1c00c81500f011102c2c3c200305207070f5070045545c400030402e81c81d1504d25885a111080001c0c41c10400c102c0e641c0039130701080c06189041d0100c4034221000070301c0882c0001540b08612803404081c401940452017021041c000241c001c0c000702d015080c9124200b0824855000050508209104d54008a82c002d10802498051010700b1010500241d0907941d9030740d40c1c0c1c0780c4a030450340700b40b20b1091500758020144034a00000841241121034142c0319500d00c0d00ca41c0988d110f00c1c401c2c042c0340010300204407103d82103a1014130180c81c111401d480c031030181e460305480700d9080422903150002405a10181c4e504560b07003200326445410f0b0141c40241c000007442c90400000c0142401a801150104041114004100c0455440301241c0c0f200401c28507a18480c0c4e564480a03001b072440141402d220411220b80701d0400e0f40c0c000d080803141d0710040700b071a10302180c4280302500d041d40c05540000d41e0144 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 776566348 1250 776565098 776565107
    0x30a140d0f0225170c251521150302030a0b060306070809250b03180c0a06090302040b0f090c0301031a010810050a0e010e06040606051503010605091c0b0403 69
    0x220400c9084001c540f00c2113540d994a40b6107100621005048000c19000b0411030204150603011030501d00701140018001056036400c0d213a40700b00c010681c20003c034021b20742d1242c001a101000d415240c1d0504076002c2c156003010b40400c1c44c1d201d003003001c045400000360340c0800400402078052041d140403828600d082c5420310000406d01c10a0000300030511002c420009510255000030709a0f00d9640011100c1032307041c0c0b49417640701c0450180c0103c06c2c865140070007844030119010b03546c00c5400e0880345e8014440c0c549418807802000c5aa80c0c1c40030005030400ba00080f010340002070029041480354400241c90707040940700c0c2403004030048018020004094100810011803080000c420344c5001a02c503580c98001a042902c261554003180c00107455420840d4501210780c000c0c00080c003400c000350f41d21b490031901940c09034100b01000425040000010540e40c14103050145141e00b414070039120366100c1030030203401c07920311240048200091200c4100592248488500c00d00b41800c00a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 776567598 1250 776566348 776566387
    0x7110c0f0105162a050a03030c020a030209010e06030d0228020a091508190b060d2d03080f0408070807051f02030601030c02011109010f0c0b0f0f1008030a140d0f02 72
    0x2e9013418660140140d03619840c111084035818a0444c60f25a21407000c103503411040da10080d000b110030710002c1007100a161800d4800d8506500b200c11502c02c4190407071795000581c900d500988000d410001c50301081030240c07000a400035014109040d543d2101c1022601e0740d14002c2c0180b48480400d022005003403004e0a010051000c2100b0044800d48510841c2d000140c2000d1048400403500c03c104003004251740b26103400d1456415214070381c40812410083c0c1c1c01011000901500c0000307600482e044005070089030440c0b0341a040c0205a035590f00319501240301680c051150301c00304403400034100140c004100000c04090703164108140090b00f621740b801c50800541e41061000d5900140b01e00a66007511000d00e00310410142c0d481c015a1111400040688520b00c03520412051480b0102082e0144904c0003a9655031340e00c914002d072400c0014000c3c0c4030385401c01c102c02400d0b1031041e00c06038602e103600c002061400c03120540100850b01070411903142d450b004100e030001d0b114983c03d5103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 776568848 1250 776567598 776567663
    0x4090c11060618090a12030e210a03090507171b220213090f05011a0f121801020a030902012304051c0212060f07110c0f010516 56
    0x240001d0502d40c00091144075000b03c003410320701c2000c00040110300304101d0303000030580142903410041038031480100605003188a218440c401d40018001202c0007003900d00d0b603c00c144c14210f0501c00c0c0d950044000d04030791032040d41c0c1485030724004240c0c170340c0444829000c600080c00401c0c11800540080d511a000084600d11502d6400d490101843c0c41e41eaa610600c82403000041e902c061410032920030f0000ea410070a456441d0451840785151681c1c401816912400342c4406a1003000b0500c01d00c501ca120400c00e0448001d22a50709241841140642c0120b480440b020001c80f44400290898000c51040c50029840f100140c056580041d40c050605500100c903145041c16000c8040c01c6110318840c540c0a10040c1400320b120700071004400040c240d00a0200928500b070b950700c0c5036282c1c000c1c1c4544a03024000c0000c41d10290044030f9140032108202c000d800301441c10010030004d0890f481100b4103006007045101d18a210305000044414482c0d414040c1c054a070403c080210b203081c1c0c084 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 776570098 1250 776568848 776568853
    0x6091d06010c020f01050408030703120b0f060a0e01031b0c1b05011b0204090c030f1505100504090f05160e10060512041a0f0f091506101404090c11 65
    0x9215081c0d034003050455030981c0548204203200c0358640129800d20540d4012807050001050b041c04040d400f6074a8200c0303503600c00090000312803031020422005e10400581d948101c042105482c904c0c041d01e1909090441410002081000f054101d81d8180d03100422800242d200340040f4200400c0e07840d40c0298002901290309528181000a4140302400c0d2485a44902c040158001c540e101d40000b0000755012480c0240036542c1e2600556011002c00102d5141c42074a0b008407511400d4800d051180b0011401100414600000e00006108034a000c1c0c445080940b00c090108404000006482c180d5070301505400303103054440d4501d4100641070745400c0c0310b40d1804014495000c0250b0341880c01003030841c00d0783d03240c5203070640c08041951007801188405008202469801c0c56581c1d100e030b1424a008403617035564038212038444a042c80c22551100c2031001003421820b08529405e410021030a2248448002c4421010382c3d400980c4a00301030343c1c035440001c682513806011b00c03414030f04d003200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 776571348 1250 776570098 776570101
    0x6070c020603010902071403040b3004141923031c0203070c051606090506070507211a0103110102060712050c0f12060a0f12141606091d 60
    0x14075148018032900d41c401d0303000309014080c0464031110010082010049a6071569500b0341ca0040d90003502403030840a01d0070381c603550030300e41801c00b0326000700780c40718003c0c000e981c3d55844a400d0052401480001d20481c0c0c034040100c05080d0f4400460f90041c6008000c40d1000c0071607035001040d105005c4a0b5810a101607204651040000740c01440c0300800562240d0b140c0d0011143c0d042c070071001400f54481d00d189101000742c1107041c5019110705945a4180d1519541400400c1c0320f042070007007042d0300c0040100303c5034044010b14031200d07680d40000020131066480c1d02e00181d0a00041103040c13a8a40d00400400510103130740c1c0c01075507082c00078025078948104040c1c102041c1c000b9459016481e9000140140c2500044031001d0501c01c100343d80301c440b440b038082810300003180e1080c000c2240c0003000c20101081c0d0300b0300c01110510340002040800f2551000102e401058a01f4100e100b5160038115002e000c200910150400d9600c0300b4840e0300e0040106104d2008001e03c1c00c0d59400c400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 776572598 1250 776571348 776571353
    0x30c120207050d0f0203150a05040506010504060308071412180909060c03150a12030e01030e1f02160b0412020d17010b03070207090f0207050c030115031401060e01061106070c 77
    0x20343c46500d03540c204c20050324440301400441e042c01a142c1614032060360a50421580444550200d40542d00403000c0321116a01d0700e060004503010360001400c82c100034001e1100060880f81c084000382140c80035250510003c0c140100940c01200c0c3d40d101d801840c8120301c003141403039106154864030000042c031060520383c1c44443c4034880a003980c051010525000c1d1001e4030303044444401002c001ca400e48507a069070030000c0410414400c280e00181c100403645a000400044070b428500c26408a416091084202040254000401c451692080d0138101010a0300c00611324800d500600399811101c0280700000c2c100300424080505000c124204101c200d110440d00d80e0554140d00e001e035659441e548016441c0446c0c0c0d501c41886207042000040d0009942d4028182c1c49200f00c2c200e078207901d032020800d4240c6154091180410240c030000700042902c10b445001100200d200010341c0b0ba46a04413175501070300903082180450990515920700d05020409280e204c035544c0f83c204003240455 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 776573848 1250 776572598 776572609
    0x1b041107020d080a03090812070e090402010f1b02030318030d031506050c010b1207060e01030e15040f080c0c0a05030303060901030210032a0201050f0115030207030318030c12020705 80
    0x100e03400f078095000400d441500c540264010111300f5080003083d078580360600004003409100321021000640d05100e40110381c201010114010f41d1305840b10140030007210001c4070200d002111000d44021038000c0c10001d614240020201c80071400c81d0810b000c4140000e052030004003c0c150020035103840c0b6030700407031545034010700c060315038524109603140ca0443c1c4c65400340c05001e00e01507120380298005586e00c0c80001d0324500716590364444880003c0e13018019402c44001205e000710035001200316240d0b48011000311644544a0040d2400f458200c0e124035082d07800049402900d944a40c500782482d01d08201c0d4640104000c0f4001c51a5181c590081180c4a4041c031000340114440c40f45503200c40c0c080c1e0002c540a00003044070780e10221000c04007548651013604082c0c0035528100214400501203d50181131320203d000f00110b68511507402c80c02903000d0700081d0201540d89501c80010340358056601482c601035900c40e1228101820070307003680448207182c003080d544110420803254603034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 776575098 1250 776573848 776573869
    0x7030308131e060c03150923100915450b040e190b19140a0605030f07060c11030109050f0721061d1b04110702 49
    0x6140500a94545404403101c10161900c010414000080c0032960742c40b5000703444540743d02500040c4490440e116094003115540c44019400d02c414480074400280d440d0081c0047c621089000c1c0001d041000d030000c04044c3c145c698841000030003404024070b003500d01483e40101b14540309900070314a0441c4960180e22480d016801c48409140400c629001e00140c3c500c10081005281c40e50304440a1395000400742d0f959001d2081e441e1003025003580200080000440e01e07100c1e50300440d01c1650712032501e44003008200000c1f200789100c0c140404031680c02180c0018600e0f07031407214a800c00d03100303130001d030344641d00003e02a900c411000c5038107560000300041220380a0810201909490600680b058403005035181c041d8244a8400300300100000e00002c08000303502038503500c42d1a03480c0c80e54078030250000390500c801c071400e50f0004207a02c0d0384803107000c1d0041005002c1141861640314217000660090b8550644030300c0754003034542490700030941c01031001c481040c41d2000c0b9600003043c1e03e04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 776576348 1250 776575098 776575103
    0x90610030b030f011b02061e19020d090303050f090a030e1005090307080d08011205030a110a02181608010e1b1204061b03020702150d060e101401020f0703 68
    0x101d5900146907900c00744060842d02682e00024000f09601c040c0081080f680c9010010051007a0b02c0022545014559482401d4044124140c910b0b2181080e070a140c0d85210b0b04c09190a608101c80c0c0290503c0b44100983c4e144640c03800310307140c82d1180d00000507100040031000706030044a04a40001d0340311102c810f440d44104c540c9500d404000504407154003401c01c00d40e03003500c07800001040f810302c0041c4066024a40d5601c20006a0b26030b608030202c2041568004e002e40d0003031080c000d1403405840107040000080c03040b60118019a00025a00421f401010454129401c14042c00c030b02c0300810701d10314900c142001d1501c0d5140041441d04000010071251818008800050208080c20b0458582c141e148098001034240381c2008130040c10b141000c030b58035021038510802c4190281c001d03548000d4005042c0250880241c502e444c8a43c051901c010100f680c805c804031b002007055100c6401015000f0865003644d081083d041c0410300c000c04689e0565100d0314100e00702d25400200c0c0c80550b40d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 776577598 1250 776576348 776576351
    0x21091e0619051f080106050a050a060c0f0609050303191a010e120109140616091409041103010f0e0606010e090c0a020712031e0e0d110a05030102160c0509061003 71
    0x15a0955980c580008800341220403800f8007000140b40703641504000107681e41241c80700100350380c42c0100300441c1f5880c03140001241c00742613440e011401e072a20404a06008100c046203150a950303800d41154400c6850130118a10225854007070001445061000300d2404501400107a13040c0c0081c1004e0107160a0706c2c0310300500d080c0300c460740b1404e41180306e031154048988509010035821154640c00b04448210b0240c03140c909541042d8805d1042904490742c516001a0950109082c00b940400003403042c2c0c0d843c100700c1c54039251074500b40b142c581c54509800000139080c10446d111414104040c24240c1005030b150a040c036070340e6541d00b4160700f001d00706807a1341d43c0e0f0401010030b904261265000c0aa203819100f005010703d9044400c241441d03046199404401d4242070054036203009012030141c00010040344080000c0205440e6414504000c140c0d00d01160b450f40080d09990140c6a0070210604040c80d003020403941822000c05004102e0300884985000c0c0f000c01c0450b0510b1191a0815 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 776578848 1250 776577598 776577601
    0x17063102070b09060415090c050402030405070f0816050d030203032206050c0a03150b0306120709020a18060806060706021b0715121b0521091e061905 66
    0x8256504aa51050703002c50030500526040901e940c490b04102c0d015121620758403221031803854240302d0341800030340c40500e041803a824442804029000204112554840c6100100e20b0503008151b000090203c2c900805183e0031403241e0141d1040c00b81e102a0081c01031406040000c0c0c0c022080c0c0c1d0b4090510745000c030041540c241c0115400300030007009024646481d041c0072400303c41500810809100352014856016040c0c10340700000d0b1a880b07030401701c2c03600f440400d4440c544175854507081d16040c0200c1d101651a850f903481240e00c040804000b080d080d45075006001001d00e20341e401002c007820000d45500d031920200d0700d10f00c03170641d00401d459400070b51319100c400300c3d0501e14403400c01441110226505c0d40d4442280711075018114003c214400404041d40d0f132107000e422114846000c48100c40e41000c182500c054200896260240b014460311130030740214182c526102e81d100310001d145a030302c900080030a05a40f8041014590450400c000b070070711030701e00d41c0c250f1100485400101ea = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 776580098 1250 776578848 776578939
    0x302070206040e04060605181501050307120203010902030106032d0b040f0c1205010f050109051516050703030e0406290d1a1e03062e03031706 63
    0x128800e507040480545541c0080c4010310215920040031f03182c0a59100510150039a01c040c2c2d03500040f104140b00fa12040c03160522540300d80091500442ca034240100007005422500b0140d800036000f003030303403164088010442130358503001d01022441040d0034650b40c81704943d01810922144040504030035243c0c0320b00651903e84d40c0c030260b0303880c045132070400c502481c4240041090a140118031081030400300045641c180080319001200c0c0c0c141c560340051072401044c0603032030750541000c2d041008103011242c044e40301e4401c80d0709124850701c09020200c0c11407070043c20030b40403651117500551528505110000f045080c211480c201c41c950070180502c43c150b240030a2242c925010541c2d42000700505040155444145841000307e41d45503800302030003001d4104156500030540d1503800303003003c103806803110310800800707038807041410380c80d0940348041768580c4a0340d900440c001600d03020221140140101b98942080003100d60035203035003101205035170b4106001c9145a2080c0d51128449a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 776581348 1250 776580098 776580109
    0x106051b0c04020a021b1c0624150305070905090c09040603120315050f0904031d100818060103230705130902090906070903060e0f06102c010603020702 67
    0x20101c0002c105554689407844002c2d1182c0140032180160041280c420f4418034101450030030742c4a50410790403083e5521703110040a0070000c40c900c0820101e002503821080754010fa9400a0001c100800400c01082030000f011100c0007400130082087c0e003c418850f541e0780c404030719040310015404948034021940020000c003101d0340010008080400240806905600020f4158101605281c84036a03101c2c10310a0f10502400e1b8554000315942c00180024010f40c2c0886428481104419101e00300101041d1202c49028108000c10105010011441d0840d2034401c3e01700c0221010700080c0d4510f0303603a14010a0202c408008002820110021444007000000300500000708018850144d08480e24028082001d05901420021001030040c140020708540601ca4980e01c0902e01d42c590348603c4c0c002d040e0311215003405e000c0d03401c451b10100c0080201601402d5501800840c0e14074008598480c0100410440d0020520344100f203924641801c0a60441e0640e0901599600382440040c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 776582598 1250 776581348 776581363
    0x50702060d060f0915080a0204020c030708040603021218060f0c0c060408070204060e010308180f12010f0c090303022d190c050a05130b0111030c01150b030106051b 72
    0x441c50381c545040010040101c2200c4000c44204001c10082103200340c0d0101184100c40c0142c200c1507108000500c01820540d000f4180d0141c40b00c10380e401d004242d83d60100c183d010307038031807400a070700410484070410002481035080200604203001d51001105082e48500d40144413020b01002500014100c502500884075000040e030103071040d030b1400740340c00c1055821a04041e8007840c602070022801d11a00440329040c0c80c2c004d0080c0f4100030f42280121301c2200e0713070305440344c201540d0516802e613610b442c00c1c01046c4400c82d80021415040c00f12648044171410202c400811030b0a02c0100046600403500d080207801070540c8907042000194031903183c80004c8000c09a6101d1003008038104112080140f01c12407290b102d13611800c0e6580704100700796605004030755100e244d0501c0300310201d0300c2e40c2c440304410f03006040c00305214500001e13480c00d54020041c00c40850751540d03030f8203100124520f1301d50040e16900e1062801e40d41003e000030b04038020414580b1020030580c10b551000703002049041c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 776583848 1250 776582598 776582617
    0x1e04060f0e0609031e0f012a090e01091d010b010c0b090114090a0c0f060e04022b1d0d05041a0c16090506040c0e010c0c0302130c1103030108060705070206 68
    0x11171411181d944070301034005c0c684009800c0b074000d0007071a10000c0410b002d521b0708001c40d0240406030201c0e189003207001c01c003000e00c9502400070f01c0f4400508083ca00c200b0034001c08a02d4000115a03a555002c101c40704400e600c01c42e0603914180d020500780c0c4c0c010f015010b039039800100701c2015642d02604140103181c8160405142c844420801c1a19407000510000041c85440440b6010742d80744560509441c5a0081d1000b040e41c3c1c5080040e1810568060003121100c0100340c580114134107420a07100f400205010b480c1c03925032500d850100c03000002545c8803055400204220400e00c0c000504d20701030b9000360221000000446c40c41d0301100b40c1501c03010740500c010f55005680d41880e81b5000300d0144a00144107091000003034061400b44282907014249864054074401c1d02c100444201140034001c03669290600008800358070f400c8a010350f014a070710400560180c40c4c0001410200b080040385005500800040c8181034001c0f039055000b001300e0030400e0300c0b03003443c0c400200c8500544200e0f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 776585098 1250 776583848 776583853
    0xf060302151e04030b07020d0903050304050d111e03010b18040b040c0e0a050609070507030f110f010609020a02010506061c0903170703091103030c0c060702060705121e04060f0e060903 81
    0x1300a1040c100610760040015400312036100b6103100702964070f24400e200251950300103110400c102c1c14107825081a03544250203805400b00d50400084d1224240850f858090307028220814140c1000d1040c200701010440c4e41da25051540e03d640f006118000700002c06008150012070104460314206002410000c01c03000e040d0f10700074440c0d83c010a000c07680c1c0740c41030300c02c44086200240118206e401850b0503030344251400101d480c0c140c5414102480840892049007010b4144802c03c2c468003000c4c01c003c81c40903a0f1226405802402e40700042c158611801f030400030071405c524907400c060041c9040600101d030f41940c605040d143e5210b6003046c0c00702f2070004020440c1d0075500d60312240680f40f01d40f91105001011405059590003024aa2645940121414101c40c5000070140020900c0104500e01d03000302c40e41d0f03003410f0040650080e41d41040c04a0000148450100c003400c1300c0514181c0c072230805250020050160681c0307802c8a05114184030652495113800c000c848990002404 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 776586348 1250 776585098 776585107
    0xf0803071e1e23061305070518090609030901120f2a021c0c110303130b0c072103050304060b030f030901031a010801031b03051f0f060302151e 63
    0x10018844080c040f980000035002c0b040d01070154a880c04106080403004001e55070b61400044500025410b040c1c07030030710444400081d107542e213000c00c480c040049607400c41542007004103076141420180100040360414000300003940d80c8151042c0c02844400d42c0840d022020088080003050301c820300340384400300c40006050384401c050a41540c0040344c1d0032103651000bc1200e4105084460042000140b40c1031469004104605031a55041c1c400809a038507010080010002413030241e4400c0310f1042e004140c1c01807401040c000d040080c5020f601410022291011888980c0c40c20071005082c00008008103042c00f01071350241800e1780015007218045003007161110f6580c1c02c22200140000d0415984da00c240c5695a0f0114410a060315851116405e566074180240030090074940000f0344024004040340381080b4a0f0815414080641114580308001e1400c2c2c508821146113803d04101d4108010385800d21480c80940e43d5900240d25000d4981851050b0080c0304489502080040b4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 776587598 1250 776586348 776586383
    0xf090406140115020d0f080a0c03020c060405060103120c030801170c0d11130b0a050f12010203010e060f100906110307080f0919030b040303050411030f06040204060f0803071e 77
    0x1100b1804000303507000c81e04282501170381100c00422104142c00010081004680486100d400a00b4100301138100907003800100b651540c6048030443e021b840303036409607004001303000e0f003c004c1d00600d42d4580380c604540c50340d6482c0a00300000c18854086881003042c14806546824081038062101c0140643c000304d840381049120710b2039250f2a5440341003448902e4030240800d104884030040c02802110805182c5030402030390f806018451a08010f5119040d011400203100460180c00803100340000c0b400c0103001d0040f109083c14000c2c0c000e103107281000044a812041d1a004c0b91000c4c42d0484054a6460b001d50a601500340e00801ea004041640170a00552401400c190342c81951020351170b841040b042c4411034520f00c80642404e6107640800c003c03038480c4e000f0036441401599a080c411010303c0101c3e1900041805184090b0003401c203000440ca001d024403401441000e202c0000700782042481074580c400e46200504c6050a81281020000758640c1c502c0260307001020490f1001260 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 776588848 1250 776587598 776587619
    0x60d0c030f06051b04240509180103030207090506030613080f072f0d080d0b18060103110c0c190305030a020706020124060305060f1302120105030a020f0904061401 72
    0x151840004c04a001c050569050300b1881640c003194290b10288140b000152540c48040e000048401c0801204000c0c0000c140c41d80b00801034080d840c806084015891030070f00074108041500204812070610060000d40c2e9000108fc9400c40e4040b10602d64150245c03030842e1482c401d9030301c081a181000311b480001d00404070004486419845080318500002c110070030704d1154581d060b5903028840d6a60369003c208042d018107003802014000143c98141e4a0006200540d450321350031400300e100d420060156418020301c02201c4510b0744007820f28140303000381030711004030b407041c1d0340a00c16110141c42064408008074004507009400d6aa90320710083c0d0081d140c010300c0c000d00001d5800c089160600102c000e400254000c50f84125058080c01c08100b140a4178000c0c024540c040440702591400c1d07035800c6000300759980f051100503906e8100d051020740c1040140d116500c40d401055061015032124403083c4038520044950719150354840c0740100091002070320381e0194205010001c0f80c1000c91 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 776590098 1250 776588848 776588851
    0x120f07020109050f011d071d15040906060311120c010e060f0706050106020f0a03020304090c020307050d03060611150a0203091507020624150c07120b181203060d0c030f0605 76
    0x3d500700e500d81000440d0392243c0d651414800c0c82c5034040502300058005080900450300810720306807103082071396000d00280548444001c02d641082d078499040080204001864106103010b89464846946a1800c240c50b00180d11008d8140105030001581543e516021205c0410100080c035032260880c0c140540100024003d00c03015119100807031403d15800201102190b80c15802035186c00e00307141c1c0c040d000e0003d03101c110081d840103001e20300c0060814829165440460ba40024500e49003100003032001d1840326940c402034100102c0091a010340910450380086410000740c0e90b9203c0c01d058500c1c0254032036aa2074503030248418070a2242e80032038040d01841030040e98610040c40130700144c40d10302480072166404801c580d14a42003180080145c103005e0b0444c0259400da503940c22003105200e4004104a500e103180d0810803040045017526851843d1181d0020003880c550082c05160910028095034451071303240c0f0f43c031030400c00d4400103c03019541c05200a890402503243ca82c2c042c100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 776591348 1250 776590098 776590121
    0x90705091501020c010512041704090e0c0108060402090307030b070c05030412030e0402120403201518010603081605030f040605030402031c0e06031911130b120f07020109050f01 78
    0x70b021074013400d641c8204d09507040006507040c01c451540395550717003403403210400c0306102502c00305010004d0303003a01900c901c1426100c081e0203400440d554500041c06c101c130050903288514418042d0440305d4900041e040262580400303124015220080142c2e5440b8803201c1c01403d07840000350205030f4103611089504421b2282e150510500315900810099008100f03910145d06801f10005010034420310180c40c102620154070040302c2c446041d0a42070100c0124450314007400d141c1849007007000304034003803110b8411000070414507007150748904e290f1045114000d40808000d896a0600605004803071601c0700c0d103885643d0b0b46617074140282041c1c004035402e038841d0166403031f6812000e0f010500800c1d00c1e84641c1d0350020a4000c4000c2060941018201d5161254602205802c0044521580011408610701d460b21110524505071509042e900b0490501e00c040c011098040c10208559400491250a83d0b14a64031048101c0c01080c1d070b440044d00314440d410840c5e80300a0107500c100200789 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 776592598 1250 776591348 776591353
    0x1b0f040317120a0b1c15050702162918090a230f0a0c03060317130f150c0303090501140a0612050d050a090e07030f1803090e09070509150102 62
    0x549800310700c0101e038804103c2c0e43c0c2010aa20120410300c1c005d0101d60718840c4101c00407080d01111a844100300e45c2c00b1941f400240e44600d401c0318140700150110303001406c0701e0b061255004803064621590004250075800c84c960042007810f000e0a40018050f100b82c009400e43c1710030300c1c041d2000005403030f840000720188404d01000d01010504a1403480c89a0005040b114040d11102110b60042030010000340405a56100c0480013841a641c203140c600c0c00418560b440e00e1405442006005481e0f001014483c61440c0c200120b101d940c800c07210381145420702c09413102c940c3c182a4040c100c2d03160018065440c041c0f400500c00301c0100004e00503003000c0010001d40da100c00c01c00c143c2c50303500e030f9020708681d2100240da0245032148004088141c0b50346444214180d91710654585428140e80c4400401e841d0b008041c803400640c03061b41d407200441c1c0350f103010010b0182c40151406a940c000d11099003401400546040020050807000b480068046c2c40c03941780240070007a0001c1c01203801070060 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 776593848 1250 776592598 776592601
    0x1412012306150c10110712030b01120b100807090801110307030e03070302060f190e0d0e0f090c1602062106010f0e10020f19020f0904080f160602070602030615031b0f04031712 77
    0x315000c1c030a50b041e00c6405000701206500444003622020000fc0891081184048000c00c0c03c41081c02960010b1602c01102501c0742841c100180a513801d40c0b146940c698000e02c101008aa0f00052045c1c0200300e89211143ca030311007145561800580f0743e01d04c001c850519000e00324203900050b030b200c3e030101180d030b41c108482e00b10810419418420008194000c0f46240400c48143d0140b0040c2140791211010504d0040103901080144d0040250340c02409661085032240d4403e402c00150301c1402440c0c850740c1d07540c401c3e9020305424210b5002d40d000b1440c484407040200e00800c00c1c89400b048940403990390b5401203114000104040340e0490040980b080c1345155420700840686c000d903403002c80f850a005280c0f510501e907812400e40c200e2265800340821004c20341610040ca920380c00f80f000940c0d00c4ca03001d414800b800c8003034882214140780810406c65401c1e5200030380500c00340701c800b14680c1e841c84241466203900071a00f0251076040c1d00c000c0e10000940c840300401240e1581518480e8a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 776595098 1250 776593848 776593877
    0xd0b0a060c080d022a0a050d0201050709090f0b10020706090801140c0315031207020103060914070c0305191d0306070806010e030a120305010608010803041412012306150c10110712030b01 82
    0x1d0b514103450311004501c0390537003800440c240c4e800281044900400015500c9400320004046900364008940940c0100070203001003a44001000007800c900e0307000340b0048140c4820580d40140042000c04440c1010000c5885020341003095114014010100e0310b41e107268480c080c605a102d0035040b0f01180c44e050000a00c900d0038042d580780701c080c400d01c180b600e0351440002d0f240440320b0b0004504000d806c016904141080c40c0c02c2d5206401c56a442d008102d62035160741c0c0d42e034001300b14400d1095005004001802d503100c000340794042c100b13180224010306e100340440d107800b0301c814008015400401c0d0305c0c540d0170b5150b4003050483d009540c40c81030300d0343e072803989503140e00c05e03400385c00c011507112126400182046400381c0c0358098440e00001c1c1400005030554805140002e03100a6a1441000d000302803521001004a0424481d012881c019118031641e0303680e404404c140c2c02007a119010030b2a000c10600030340d201d0030f800c000101c030001a03044004000f02070300050180490a03500c0320b01c81 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 776596348 1250 776595098 776595101
    0x806220b0414040b01171e07050a0801050907140d05011b0810080c1012020d090203010b040c200c030d080708070801030305031503030904020d0b0a060c080d022a0a050d0201 76
    0x642e009005031404d0307400c145611000c4103008103c4c0301d582c800c0c524142c902d100c510701480c102c42c4401001d80040c605010030009007843d02c1e400780542d030303040c00c0038841e26030004203035801101c01040194108002400100b5a494110700d0094103a5281c0040f006e00d601c40c00480224550300c1d030b80c800901d40d0710404608000842c1c3c2c003a1180b15402101000310030304015101c03410001990815101060000d0210006c0e0b910152017200b0b2652200c82c0c01046060034000d60700d46010440b814006451909001080d09030b00c03000c1c80e00c16014400c1622170148040c4005c490400000d000e4580702c401020014102002c150350000c001030760140000c21545c0714a5406050342d915a0720b0302c0c615111000c1c5e02038100540e08040380c3c540410440100700c1da5840c4001e1407000310248000c0ba40b4260002081000d25440c4e00440030700226460324000101071404491004c004e4420060312080c00c244c22102d420104407400f000c05400c1d410000f292840002c1d030700a0300303120381d046035181803001101302e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 776597598 1250 776596348 776596351
    0x601090e060f0406020a0309020a0311011706061c0b270606160308100f1d0912070f08070204060308190e1e0616030f1b03050a0806220b0414 62
    0x1c0e501a0100d00000c0313240c0c00820f40e40900c4d01c2c000c540c10a80d90005400b142e01680111103079005a500c3c04140d581200e4004070055105a840c2042d16008010510500c12101c080c5032105400d11420302212103580a15454100a044c040703a0515040d80200c0c1d0b101249504040204403500203841e618084045961500c1d0b402d00f0b548628206650666a103100507244500c41c40d00b00402003140300c140e406400c0201001150042c55030480440714a1151000d0030034062a005208038456444201d0200c03a455684103000441080080c01d203441e40e8040d041009504c00c0c180000041480300c0203000e40741d00200150440b01c00b440c031032000c4c0d5070300441e510103c0d00b280007440141c2080311a400580300685000d40304c2c515002103c6802080802400011004600340fa0044c80060740e0205002c100380d40c1401d614110b0144503200036000e07009040704101044101d400046282d12103040c03402120000c1707a4501609141084004083c1203000000d900480c509114140d01d00a10501c45 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 776598848 1250 776597598 776597611
    0xa09090503090621090610080705060304141c030209040b0d0f080f090d05030a081602250803120103020310110f0309030f070c050315040503160201030b0d050601090e06 74
    0x4500e0405040d0034001c0c640c10130031596150501c4080c200c01c1c42c8039840c102a2140c003251014040301e1600706100e005044d6543c0141c0401d40c000e500a0006031100b10441c0e4005405c04820501101200c41003450460300001c1808070b95845001d488102c0e400d80c029195004003202c0c103000c0c0e5074012051146402d25500d0152040c442d54044501080b0301070000c106254607000040d00d020104c5012540070701e99698111560340c80000c0c101e043c15802050950400c07007464160700c0d00c2608441c02540c80c80290383e10ba02c00b4014000c0043d0449200b24900b00800e000c0094079220800b289298081000901c8241d0083c091644901034001440c03207200350301940c0811540c1003600000b1030154a80009220601502c4200710080c0750200c81c002a04405100b20300d81140e9074108401d140c02e02050402d2064040301d0a014440041c502100340c50032524605c4a03001c00b40b01e5800120060182c46e00d0007500304441507000c03000c0c0301c070118032036043e281e8080301071102040d58480c0b283e0b250030803100b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 776600098 1250 776598848 776598853
    0x6091b0313060e0313030203101103040311011509020a120b100507020f09040b04110f0a030605061504060e120d020d08040c08030f09091005010f0c1502030c04050a090905 75
    0x441c0d881080588070340142c022400000d002d20700340205071550b802022506800e030a8204204210725040028000040f0740500c207004040021a441800d03010103400181031141503a04900c0d0000300354403101400a1030400c081c54581c0d82c41d040c00c02503102031004000034440075424002881d203809548032a90001d001206502c442c0c140071506130300180f0040360b00151540000d8405d0b61011101c40c010787c02480b07418000e04262070b24600c00c441488585015000706000f15840781d8400307581d80c049035040310010946a60303030300000c3c003841c0c001c1c0f84200240c40c0c0030078082413250b03220074aa800c10303409841061041d40c0341035805903168010848180140d010381c0c05a4040c0348104c01964101d84110154000706481d610318a0a5030040c000180d00c02501040310310640c0b0740a000b00c0e070041c1d40d01c00b0125182e81041c0009148c03400d40e40700036041c010250059001c01040582840c1000c0fa090021526070500b41c841059550040c461544102d83c0e030900480c03800b44510483d1034280c0e01000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 776601348 1250 776600098 776600101
    0x202a0d030e0c040b0a090f0b0909070819020f3006071413290406021605040509070504180b0a0615020d080109051005040516140c0c19080a080306091b03 67
    0x1070f502402180700c00e50240e623210400b40764241c0b40d0107460303030050514030003411025041c601500d240080d0b0704100c80c0421020250700016884082211800d0030090345e10103d03115004200c10b50f03041180c1a221203010082130309001940700803840c40d014150b02e40c2c40f0301001e52441c088c0482809804084864041c91450801002c05045160380519000c0340081c0d04078a440c2c40303002c141c1d400c244d10001c0540c02071800040e00040086060340076003000c540030004d03030414580389a504c1e5460300805004036500e01020a03c00e022208210f0180e45c4203c0c40645842c0c0f01c03561401528440c46000101c0048248140c42140089680c200d0b4400c1c03941c60b010641e1a00741400050030b006402402003116084002c14035850300e0080603c10204100511910448110000c0c118450546000a20072090044002e940d03804030707400f841e01d2021101d114070680714806440c02a0195804080c10317210308140300301003110510203548200b00444038552559120780305106d50b0802c804290a54034070820 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 776602598 1250 776601348 776601359
    0x1a0d0b10170c06161b06120e190201090f080718020a1e1e02031207091a030a11072a120b041b0f09202a0d030e0c040b0a 53
    0x2000c0c007001910f128114003406940d0b220f041030340c607242c240562400d88016041c841c1982022226a042c110381e5410420315808420680c0c950164040c45030121601c1151b000c150381c031941c50140500724030dd02120101c0d031790f004119901c07a0184070380a5042c40b240410303940001d9620039615011440d40b513080543c607008100081c920f19056085082c018140341f2050010149029a0021402e94000f03656400544100d02010207009204500b044103c120510004c180032001c41641e840b142840c80d140d0711564a0030004d0441942d0082e080302002c26800140141260542485203680500c26004d2000c1d1060040b04901405200390201c0e0014440300001d8403c1151030b4040d025100300c3e80d004070210380401080489601120413120780c0142800400c05a00c00e80c002c01c110f0320580c202c4400d07200710500c01400703142181017010420003d4525046508001c0c11407003d140c006949020b420030700c0c050014010360300e104846200700200c04e00305003410f205030006a0b0009100110b88ea02d000e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 776603848 1250 776602598 776602609
    0x1021009030c140703060f0501080f0c03030d0f020c0a03021c0525060f06030c1503060e0708100906081b030303131502071403071b0e07031a0d0b10170c 67
    0x500300d5203d80c460007400001143d0184500c18160f801c00c000411154582002e8901c0d0400d01c40d506a00c07500078807041c51050b42c0000c200ca46151111a01140c10113401c001c0354020301403052007607694000c190100d4101a40400e40e0740d60300c60802555858a0b10960303041342c2500560712045c22803445940040001401c7e2080c10b00c1d0548214004210b08145c60002000e685103640120b4803140010300034480d00c00e07410701202900082c2c0c9030400c00e540c81e105828105c40c101801700010b2004100105288189415034040a0305045030107011041e581c400d025600e9031031550903160710141424603002d51030007004803406040e110012100f4409140c0305c4284000e044040002c02e29030810924000030001d1180408154858000c0c64036000c035804c3c0710ba04100c1d25010007004404150090114002106d0f4142e0480300d80d150000f075130114109840c0944030f54680255001c83e140c2c0a10b03040207114448907104810401e00d50742481c3d1350ba0385c500500d03d100c0e80c000310280c110184440450604 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 776605098 1250 776603848 776603873
    0x1150207030f151503060c050a1b0c1509060305010b070b0f0c0c191110080103030507050a060e0a020102010f020322230307030305090a0201050418150b0901021009030c 74
    0x600056290040307000f0380d031800c4880710f2014203940031064404005102c1c5520415a5000b41c0341000b82c075103003201000a142c03022280f41050a0041c903082d64040c0b00b802e0709840301501c00304610311280101084060408019031141400180c201400440c0b001c40c11001c2d01c04441e448158030243c4d4461400c10307107095070000d1010b1b100ca40b09004080c4141c00400c8454a414a5003da602084189080c4034040603202c1d400d06003d00032084560041e580d0080c12241100d80602d0002d4607403505107049820500200c40290405003850303246014004045440360b0f2240c0b00b41c00800405c00401114020707400121188402d80b060348041d01c08802c00c0084101c0581e1241222000c0150500b454042007101a2424003142e1f00103d100c0e42015010710039140c01040f0000100011070083c3d000030031038841d5001e0158180000100000b041129800c03c00745c088007030031068a0f294942a200382e0640000b0021401031080c429010b500c201c0700d2194a040d00d07090707544d0004031003a81e03d0f000c015141 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 776606348 1250 776605098 776605103
    0x60f0312032f09010207092318070e06103608150403110105060f0d02010e030d05030703141603020a050c011a0f061c0b0a17070e01150207030f 63
    0x38050003a03001c980c0b548010001e02d0201c20341c03039107401424000900c0c2c80ca040e0005050715140c603012a824600e117081c0058141d0440520704419650240401070700ca44d4402c01411314450401c000c925008004589071290348143c0b141110f0711500e82c41210980407103002130107207a210151842c8040c00c403040907482410660b01c9520342d036650719011131401d1050101e070744000509100303110400d0b40c048800003d980721030000340a10306040c0c0005184003c0012500c0c85090303820070150441e40501c1081520000c000c1c00e03962166601c20b4060450b500448142c400a860800704981140d9400c3e0b0740703030042100801a5084400c1100c0640007548180c50003014000f0902a400070041c09008140010b520b01c1710f8130645501c140140325400081203041032140c4002d0002c0185c40d0031841c244102c1c449106004141165844c02084800d07905400c010116080b035208108030b640005054800c0300e082242e00034860b030b40c0d8442070843c004c0074544000141c001c0302c010804034200c030044100160 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 776607598 1250 776606348 776606381
    0x907170f0c070b0c0c07050303071101051b0d0207080f0f060105060d0219030207170304020f13020d0c1806110601120c1809030801051e13110c0709060f031203 70
    0xd000781c80e20031035820215010344d0300700000959000210018054a001014103400641c1405080c3c2e031381501c5c0384002001c080c1045800b01d070b400318001c02c2c03032400020b55801c03409880707445056900003911070100340100c841511805070900030b81e20000402c0920b154040c0c012b440d0990801c002c0020542c8018006819150280044400060b807601c0410501c403050301e006996042916200b10b207144103c082000c045001c2c000c1002586071041124030550048681020919013000c101000340202c18402107140d15100306c0b654041d0300612014011800c0300360031a4495a50b00341140c0d1012035402e481c0d00360300b00c140104000e0044880107e4070034410540400f81c04e45800f0441c81c02003032001c0c040001901c0d80181c3c028150050b081c40c0c058082034507490816018609414198040700300c54a01446048071070448000682d4441903141c80c04900031a0b8584a040c04107030740391014055000f803146018000503a804402c80c2d020201c1e54000d814448020050b8410760003003214402100303414 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 776608848 1250 776607598 776607607
    0x130311061902160b0a0e010f0c0c0605120603030306150304150c090e1503070b07110411070212030711060d090c03060606030c080405100209190906050907170f0c 71
    0x89589070324691406030381e40d00600c40e50303c10342600d0324100203e0703215540401003042010001544515500c80c0c0d1103080c200346084210000088600c07607070a05c4080c0c4009403400300400d0860380400200304117510003101e48419107500302007580700d10007559600c1d40b1020190a0340300180c290390145034818060403507007076002d105205ca00241c0746135441d01030001c0d8404c00144001800d8018554000f00080341c500f12110140c40400c2c0e035003c1c5401546210403000c0b540e58100201d00c1c10140031994040c0052092190303100451000b82c00c0a0b1049108445084409030390040002c00d5a0015400030741d0002040168000d10006030301900402c006103454400e014042803081520600461040000003030340ca00d041d8000301210340fa110303101c0822280ca014130003c1540010b000003a0350360420010703500c50b600030014401100f60a500d003072100c11764000041c1d200760350b808007045450540780c0034219070740c080d8200d50100588004503c1550807001103000c5e000d0001c0500d611407501038609241 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 776610098 1250 776608848 776608867
    0x1b08010e1b01050d090507090c020a0c0605030c0c030c1018030203090f0d0605240f0607201003020a0f140d0e0c120304030204061403150606040902042913031106 71
    0x503030b0308499042e0741b01c0e03100030320802c0807500901c5268400c03e124400303810003049664072030703080c1c0d86144204410400e0110104000000281c111403800000030b08403680d03808030b02525603c441401c00c2c0c2980c01c070300d003210604591006118000d07172aa4958040c51030402d403032007000980500002656041032002101c10005240c6120707050044102000c0319110f182881c03040007191601204046c0110860440140503481e180f00fa20004c07940a400c40905a1039100084110402c00100036070050011400318091501a401085815510761710701c13242c3e100805050712150100903184503003840401c142e40c0c01307410703682c088030840c0400d10a07160855000c0001a054058960300441c0303035080001d0800031850140318035402042d80c01207200c180400c00300026100e42c005a0a040454440000902c0b01d550fa402102e0113002103001c119160f80d203540000c0e10f110448040071700c0030b8401c0c101d0705901616400584400e49840c0c0041d070a042d04566545226810070700c81d150300711a050185440307 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 776611348 1250 776610098 776610101
    0x106030c0923120d050405150d2d02040b0307111204090221090a02060a23040905070801080705120102040e09010e07060e2d0901031b08010e1b01050d 66
    0xb001c800441ea40300e404407240b0100031864000c002110074a51004120a05140d04001520100c50041f1032407411010f521405503036600c19034050b200300341c0c40c6c20314000741d07038002000000c010080085030075103040001e00c2c81d4040740301d540615003601c5014800034030710394490a41850f00d82c090205440082e03a0807a03903000c964005802407041c20342c000c01d040310200500d1900c102e031501d9040e4281410304084900b00d4071000d1045000c3e02400700001c001c041c441c001c494142a03840d10186c0301002c400000c1c0345e400300390014000c0624050900000c00c0c0b03080d2040340303410b05035041580545280e6142004010300c5001034005400955024800010340c40440615907100c0c1c0100400440c400110480300c80c281891500040b0a000f40940b03002141c3e1290b60080c2030648407404a01c00407e210f078402c40807000344031300c040d0b40004810300110400007410001d60b0001041c000c070703072401c90302c800c101c500782c900c140100825a48000502a103042c60400191081c04040c1481071034060500740d800b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 776612598 1250 776611348 776611379
    0x31e0f010b0c0a21030b04060b0f07021504030605071d1023030a0e0d0206070e0618041a03120412060203070e0a08010212060f090f0403020c04061d0108070e0106030c09 74
    0x4e0541900010080346816001d0070ba51610200ca08000007030a16486440d6401440004415050040b40c40070441d11003a42c00b4580030300d0321012030b807a640d4928014000e00401c880c2000018159024010200340011011442d010014000d0488040a440849400c0e4000b0036040c1c1809401500c410100154801540030303080c2901c0100e800410b030302c9c0705894420724071040821903018004022200d94062481110b060088030203c0d80e442002d10140350081007440301990040c9043c1d0341d8003590b1541000328035111019801d883d21501035030f80321803c9000d5403141541030740d2040d07240000200f4079401964000d2072401c10010848004020600000e0650080c40742690700141c199155030300000c1c40380d840b000496130700e9a003030700040106080b143e0242000d4220090900810101030003840300d081c40d818045d104105190b5945072880c14122002d07040410074030310b00c0010a09400104144d010395410000c0440d25900c0c0100840040c000420800200944020040b41e010194103c04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 776613848 1250 776612598 776612633
    0x5130905030910091221021501031104060902040603150609210f0f0803011403061306020a0e120d032a0f090e0117060a0c1e030e0109030203031e0f010b0c0a 69
    0x130500348034403103406030190003200d0321b04c041d9409401d00450b07000f000b522180c1580e610840008140c030003a0042005080690040c0003200d001060105400354943d001192528039910310502e155a41c0d501030fa022001d900070b801d50b203c4101d03950a074007028410000d400500c140030148084803070b5201d4a0300420100e0044404002c000300400094450702c5440441d00402c03809056581400860b00185980540004048a402043c203805803030080c1c1c0581001c1d04017500040207810b1404015480d080101640c40c08031b468441001d015415850529000d001019801c05501c9000402910343c00700110502d400c00042010201d81c0c040100101c500030103843e8940384032136804410302414110000c0c1500c20007460000348858840d80080302c030105040216800c20700b4203007800f00318060a02103003408070941c01c06112608065002006501c02c2003000d08940c00e5030b50b610300c0f960180a0076901e403086e000310b41c00144000240c120043c8840e1162a00f1906801c0709035950f07405015004052 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 776615098 1250 776613848 776613863
    0x603050307031e090303200708010b010f031a0d05071a090f011814060c03120f181b0d1406040b07030207030525051006051309050309100912 62
    0x808040e000300c4000c11100c009854140303e500c064400401418880c03001808100000706559182e0595100c0c48551000da60152041c4a498000c1c05018180e0604201d00240003030b4800d40d4110f20a114014043d0b01c030700245070005107460101b218045402d141070722540035205002031481d0700a075001e03112000b0b201c5000d0300da468003000c1051644c02c00381000e05011410f290320f2203142c4c01c0b070000300954040c0d807518600f80315044085004c5008100e00000b040c400020750903110300480d0070072889058111180149540e03107149900c80340390040d90011081e485140d400e280804402203807100380402806001e4064a242c448040001d02c004103120700b600881e041c80f007804001411070781d0101c0c85003010362a100c2c441c0d80040032880b46200b40b10818051016062101c2195a900e18415030820f045400070075000a421004000300d10820748541c074030b080407580d000070501428407801c5e00000994105201072042c0134015614002240801040701400310350010042150385082e4003e502 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 776616348 1250 776615098 776615107
    0x9110f120f01090207080703030c021606091a0f0403060209010e18040203070602060720030426011503420209011d100c050f0628060e01060c080c0106030503 69
    0x103019407949410703007200305018010050b520100780c2c08402c40b040700340d0502d00004c80c444010401c078184030992021205003c6035080c009000740e07202c10307900c1c250380e00450a8080c000d0a41e0300300705588650440c2c603007800c000b80010000b15003075a000d840c0e50007043c100078001714142400500c01c40305280080c40b20390fa84406000035800c2c00c00c4080d024200728002410241095000580437004c20501d038200b511461618011a810030b00540d030040c140d520303004d001d0703e00105594800c2d032026064603000350b02c2c009a8850746840034054034202c1c1e4114140038040c1085001d940380c8500802100ea80041030540c1c40c070511601441c1407104a081c00301e0041e210180707540010404d69a501c9116891400d9081c07600342995424400180b04005040c00f0304c0e2264a0f1a1190409110f0040c070146400b8a80420110000c803112041e50002c9908001803c02d0110b0340b0070040320054001c1c0d01f10700c00f100005000850081000079034960044131405c0c1420740041d0014251620342d00106c07007941010a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 776617598 1250 776616348 776616361
    0x20625150510030c0b0d06090207080901021203070525140304080c04090b0a050405100204061707020607020c09090c06040f0e0f09190201050c01140f090c030709110f12 74
    0x42060b400800198840c41043d00d0b41d01c40300d100304280d014581e12442c00003225000d00645078800002040402410340d10348400e814590700c07a8120106d82405401b0f040302d40c6840000e00d504a9100c1c2a4a4035000c4c1014079800010608040d080100d01d000700310001200c1c0854607520301030595072280c000856445050802c4a41840500c00c0365502841c00c0c041800e001803400c85950f640b008010500081659560030040c1c908890764410029580c40082d02049040d402101c09580f040100740d400030035110b1080890303480004450503001a0059001000e00b4545a000c1d80d0300095020211114444a00d00044d0785911036808105291540c0100300502401c00d00301c16400300c40160070200902d803802c0c07055101d90003488200000324019030741c0c030b046a005000340d900015441c0002c10241200c1c0768402840501a1800c901c0c0c0015040040c0040d0350020300d40211071000b03809085118507102170100505440c80c1c840031320fa1414808a4000c68280020b400d0740355104814000606200c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 776618705 1107 776617598 776617601
    0x204020a090b070602040821030406050405160905090105130b0f0a02040b070b07080603191412030c130801050412210507030b040f0b090402062515 65
    0x410050f007440560f0307000c6c0065560400485102e41050040300ca65060000d880c80b074000002c1001400084c0113801c07107a00188038408859059804c01d51143c0c080c0066004020f01d255507100b0002c5049090003510b2300325042c0c84c1c10000c1180300d13489041c0b10725801040d440d01030030880d020440c40c00c1994101e5000f4a00e44003481c0d06c4003181e240204c8405030945c2e04500003801da10220b03030203203004180580001c001d506061200b0045a0303408075a801d036001154414003a205d02e003026543c002e0000c5102d03002005070a950b0308007100110032400d0039034202024582c581000c000004903c803025141400039030900c00c40201c584901030880b0050050740c01c20b03c0c0c0c102002d00100d540c2503002809074540484041c0884035070350042800301c900540c80e03203501c0b07041c08000c50094142039004001d400c14400541105060000240d040400020001c6501d00c1008412240b0300065 = true := by decide +kernel

theorem cover : BRFrame.Cov 776438848 776618705 := by
  have h0 := BRFrame.cov_init 776438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 776438848 ≤ n) (h2 : n < 776618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
