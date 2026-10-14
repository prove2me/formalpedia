-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0539
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:19:59.788059+00:00
-- url     : https://prove2.me/submissions/c40f397e-2ffa-4e0c-a696-a0d0a82057e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 96762590 ≤ n < 96942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 96763840 1250 96762590 96762593
    0x30304020d0813031110031b0f0c05010240050906011e020607021203011208031003150b092d1b03090a020405010e040b040209062805010806011110020f090607 70
    0xa00b0400141c0084400d4104c00500c920241d0441da1100c4840042c29114800f29008c18014002c04000001e03506001500d034030703680e0700c05003a68081080c004400042701d00303031011400018800c400b125200100080010388003080100c0c5400700e441018810403115000c0b503c180d0080c4140d0350307010004032080c1d0f43c210a04c24007956881042d114400148100360200a11600c12810b0764141c8104584018024140343c40301c03001d540016000d254a200c00c241c0010025540e02a0280c80414400c00803e80120b018108107241030010101d40021048012443c03000510340340202c01c2c5401c0d4203c03810b1a8a40c0100325409a070008282543c0f00c200209100703500c03c0010390f030180b50b80708803810b1000d40e8a552910320503600a840c02401280d5020120b00140b0f44a65400d81c07120020701500468100c02c000d540b42140840342021400074010400d11241d680502a0756012800b82402809039280030121a82c0f03420440c0700480d8940c0c003107141649080c1501c200c641d1020014450b0352160060b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 96765090 1250 96763840 96763853
    0x60519020a08060a050103090302060115090e091b0402070b0a0906022a1002090109031101020109080417070605030c0d181b09060e040c0506070606171006080c03030304020d081303 79
    0x58607510311544d040800041c003984280582c0e80d515500d6806005282d2030103840380365441c0c00c20380352400d01440c8000403d07101c2e4400a1148158882030040080c4803410542d03200c944e15030307100e1501441c0100841c40218218510480d000b000c0510005591442420540b0087c001c04112000080840300c10010342d48140380300e840b45000e0700081c0c03402e441c0c0048180040384540c01d089400b10b0740d151000c0022800c0b0401c400f29405060001103a2030b215550751500035400340c0c02c0101d0020440c41c021400c10800c0000e0006000c590420515600b4440110106800340d401040c2945840e40e00c24245441d804200c140c0320f030390049000601c0302d02c1e146482c690228034011a45003c0c47c4c1040000d40500381c07001a40201c1d00704040c28007a078200424052254842803042d0f41943d01c44400040c20f105120340c44029412040c00f5022801003a03580d81c05071011584a203d15510070b4050410668021085039049a81110104041a4603241000c0e40b40501d03503030302d61025040800002803181 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 96766340 1250 96765090 96765107
    0x70f03090b0703020706050907210302150a0e1c091202210606030f07050a090203090f0d020c040b040207200d1a0417120a0b0604050a080d0311040e04060519020a 71
    0x446c50090101c0c0c0d07200d1b6582642c039102803081c04041400308410188855440702020b00c0c1a001b413040c0c811030b0400c42034200f134990040d41c0d6064401d65680e0081000c480900c08111b0350200a000e862941c2000d2400404c4640c0328000c94a50007100c407104021540c0d240c0d0403041940c26010395007002802e00c12803580f00c040840f03e05010380070f84008400324406c04103000c02070315001070281c900c039420030750600300940000702490f0103807261000305583c252007003205007041f41d01903000f4000009228240001e8800c00080c0c103014070b00610180300084c0d80341220040181c409680040807441010024803841085040500b11400c4070895000455017a0807551007580a40d6890300e0201d03100542c104184105806162483c55400100d4186036440e0801018802e0052045003007036101e6000500424184d40001841d0744802e10810300c0036014050340c6000240c0e040c520307052500d005a102d200302e074002d1000780000e41e102e00103907221035015882c09407004050001c5448410340304014081c2c20 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 96767590 1250 96766340 96766343
    0x40e04110909030f03070e01030b03010911040606170a0e0c060f040312050304031209140f03070519150504080d0222090b010c060509071203021609090209070f03090b07030207 77
    0x8003100020103202e0b000045484081c06807003001d03d181d6440c0021180021441c8244c1d04168072a860a400c642c0c09025064900d0b00440c0e9000419009070100400c03111194460000c4c480a4810000f52050840a40b94001040c03400800c80d00300460700d507410300c07107010507880c1c1c00340e00800c2d510418002000a441924030440ba1003100500d14401a02c0c580003c0790000c0000d120520782e124500580c0c0c0000c4030442c480c0750144117801003103103000d0070802d03070310355150030f6500100c1c1607030030301c0002c1001000c4c401149520141005030783c2c4400408032584000b4103e05078440c0041410071411904840c10002411402c546500310621505440d400270380440c00388030203c0c44041047c443c070388144814420140c55044080c681e580d1031901030400108505102d00075440001914180158842e114500c00c0d800f41c02030444c04122400e80c8500c4d500308240c15480d2000e5800107031201136102e0b810620604100c682028400421030180c00b42d4040217104200c00d000f4010350325019000b800086 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 96768840 1250 96767590 96767599
    0x109140a030906021506061e0d020c100b010807080903090306040c05090a0c05041707030b0403050901020f070807060e130e03180d0807060207080c03120106090b0a080a02030a02040e0411 82
    0x700e0f507402c001c0769140c62030500708044010b000049000c92405c0c1000f0700707444582d4007072034047d4a8183d400c004660404601c66080c1e076000207031088002ca052100c0960f03526158003c001001c1c03e079000070074122000309070030705010764800490ba1380e11080040d200300c10401400c42d800e6190610309071006006510402d40030b2402000411003a12a43c0078081c4070303048641d122410103240c20881c01e0316114900c071b020124015100088082961125450703ca24041e450315580c0300101d0000a1801220300171015203500801000c0c02154030200781c19049680501d00340e03032802c0a107400a0380c1b800c0b0149001d03452614012014082c803001001030700b40d021820b0400c07c107a107180c0080c021030548a0300006c0002004200700400500c6e6940030f010000c3c02040740d182040024003200345554444d09262901d01071213401040481d6111400c003016104081c3d0403828400d0f110f2001c5e2020202400030341d409500440080c845109942c1038600410030401101014209406d001140c0c1c0405400341c1e001c0d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 96770090 1250 96768840 96768857
    0x120608030a020d0513050402031305070605030108100203100503151501050403031202071e05102306010f05090d0b06190b0a030213031505060108070f200109140a03 72
    0x840110a4854004254028004180800c141110b4590101c2545a00140b68003004100ca84803407000d9445882c003015424011621410a107140c480168080390401c1803c000600c031804000c1030b522100158a800940c894540504001072180542c0165425201c1c0c0c00d42807401c0d0755210407150140020081031400c00c04d4000044460344180d000140201c0e54510840e006231840ba4018551a03004903080ca6040c4040340b0040200802c0c07030420358940e44a04003007014843d0620a10302c2130382d005080a814100c02141010404000502c0f00d814002000400388151b4021011142c40c08401007002d10b0010303640c60080703075007002682c2107401410021040701004c8509086101035440040c4901e041c1101c1c020100c1c0a58000708404411084481000000030302c088140501090258000302d000d103820400103040d110b0003080b010411102c0d400e4002025009071070040041c001d0100c5040242d0f800302c00c10301500741100000d102009840c45001c403240d012078080b102034403a43e500c445 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 96771340 1250 96770090 96770099
    0x3050a090906051c150c051803010209091909061104061106043f080103060507030b090105130b0d03020c0306010f03050709050a0b040606020322080316050a0b071206 73
    0x854100e800348075000a05030136000c8640c07002062140b038a502c50340c0c003000603031310360543c900645802040c0d4002140010842901d81d8084600c1921440c1c1c007a0021030414181100140c0403080c0a0039100502d6610074610503404459080100840d401a005205204442c0e142001e240d003e40326460006520200a40c003203000030481901842d000312403d4040829058101c0c60704040d91500b1500f0400c566482d0041803604207255202021394817503040942c51402c0000c1951341c01001c11003014074180e44090b46d50740f1004e880741500c0c002d5800c88405291018a2070043c4001079489a010207030608032010180e0004100034080e40035800d4480f241da8480c1c070100c00415030b003c028482c0d000746006000680b01335005c1c5a21401c81500440c2120440003c20111a501c1e004807005803c005031000400d0307880704684034240c6807603036260301d054680340303240d40c0700e024002400d100c805400d4030301d60a000c0b080082ca06400d0b0040c122002c1800c0501014102084c684121040c0d50f041003800075 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 96772590 1250 96771340 96771359
    0xc050706080a0f0e06071b0f0b04120c021e03070b0708040f0e040c05040c051207090503010b0f0112020304080c070f06031107050604020906040f181707030219150903050a09 76
    0x90750a02c40300c020045511045810340e4104021f0803204030800e0a2008070000c2035100c044070b0401c5010b001e0004032824603050080d40649030000c2c0109025126a185005031501003000d8001c0d02000c91030042a09910002400c0030148d07030220f080c284020410109010020009004540b818105041c149559601c81c00340e00340c04550140c1706114568007000282840d410400f40300100b4a8010b140034803031158012011000d0712500e0004407080b0f01488582801d1082c44c1300500212075003081c0b0607000700000c20b04565026030802c0701780c0220102d000c0042d42400d9030424a0201c0668015940724013442000360203d02c221030000b803e0011120340c0c1d020103401c544c10688c004025201d1a82c643d001d200807440c005d4006030300070f941d8140e15045006648107501802e5031803460801c456450303081110380850036603540e00c00500b0800c82c0b42c00098000548640c40c011001071101c1c0d443c3c89061030403000d184102c4a40406050519410030160b000004041335401a128040881d03150301421 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 96773840 1250 96772590 96772601
    0x12010f050604151e020d030506060c0307030e040603050106030f0501060605031e061201020c1e060f01050d0f17071a0609060609031603050a0506070201020c19030c050706080a0f 78
    0x25085401000705002030200c041c0340149548040c203004803010301c00c924016041301c09500090058004008032a0f80c80e906005054000c2001c40f146400d0801c01b202240d100d100707201c40103042c0320038461404101d44883c0c021030011501f180081020b141c1d01c2c20245c2c40c04154140441d1294a81403020480070b000d02c00752800303a03c9602d880c40081140d814081500d180150002d039000c07200c131442110313003402400242140ca0414000d8940045800340ca400513880100c402e41c400d4000004201180c411130380194110b41c02200c83c07554100407414004414000101c0251440100e9121170305030740700c2034005254180c450788603100032051482d0082802e980a40d4020381c402031807400b080c4185003090140580b500c006098035120b21400c5c404511011072688211950f401020f0403506001050084a50217440b6000039443c00d0f408055940e01c0da903144c00c040c803001070020b20035418184560800c81c003140c0e01c10308440b01c050701c9903405490b20310110703151003403141488601802101035000d030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 96775090 1250 96773840 96773849
    0x80907120b040f150b01123c020f03070e010201020c0c090c09030601150f0816050d060b0d09050d020c010e09090109020d0f02010207050d1208100f060512010f 70
    0x40d110303205000d680740c1c80184030160064400316100c0342c5400104003011906000014600f400013042160040050981c0c091506601d6a851504995055180005010385010f03d03190f042e504480396007100e0707101e200d03500070101c03100c0d1840490500c14600c1e403003000b0341c004d036800e4681315020b10852004a090780310341003400030a60004e2101c02102c0c1031059840b50007508e4504003505040e042d81c046464a0000d80c07203842007001d0001000149900b121801c00303000028544041d180c90700054092508185042d030300d081041c0090601d0032101745a11082c042c00e017181c0c4203903945610300040c0303006e048640e01c103079100d001d4013621140300380c00002d04c01e0b0342c000d068442c1c21b00c1d096481c08018200d000200fa110a41d500e41102a0060703030390f00208481644a0242c0e15100350341030000a10f03080032a009540104080c030a94404107010150412451180d4a450460f9a9685882252208842d400310401e80c01c0c0c0300002c9038a0b904900a0500d03000340c2d800c0c1c010702d40c0c1d850b104060003a81c3e5205 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 96776340 1250 96775090 96775109
    0x1080c03041a100503010f14061207030f0602160501090b070f1d0a0b07030c15060303050906090d060e030d1a0f0105130302130e0d0915052512080907 66
    0x5100706000c02d800180d548440301c0c00741d9002c00d940e20380109003510b140c4d4080800150381d46810103040e00c1e01c201c203250070010503100d4080d5061054051590b03002140070103080b40b1500e0001c03d00f041520740454a039914084124200c0320124035015001e802d881d00101c841044110008880c01e121b00c0002003400241d584d4504d50b900c1000991441e06103004d03e4a8100310200c401251141d50b2034028022240b180d82e0b00048030151f814540c8000b4500340c0410f0035642401410001700350321070266804441d007203891a5507015105e000601543c1110341c014900d901b480780d018603000c404806060f61001c2c0301c40900c40482c44030490b88000c201141c50a521a4ac52400b41a055110f400a0918440d10759503551410781c0700d40002ea5401030038210b00b000c00b511081c0c1882c0c4100b0512405000000c141030107142c150520384500040805001c4040801c14003181801810140c0f0300144170303c13018131507400100340c141d0903c80011400100081c01082400d0702140700c1010000301582142c440c0711 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 96777590 1250 96776340 96776363
    0xf060806090606131a09010609060809030a0207030308061908100b0f03060408070c0e0f0406061401020a060e0313080c010207050907020a02060d0b060d06050f030a0c0e09070b0f0901080c0304 84
    0x110840014600c81c5d080110b0b08200008100301da0b11003400c00c501804282e154500508d01d4000020401c41e801030200050f600309104204000f03800207200002d680e07150420100a544440115201d11807c01440c0c08426102000045d9980c02041102c0851030b01c2e40d003440100050014800010403414209030113502810014000c50b1148001d03200c458030a07800081200d9640d442e800f0362010540e04104032207050414042004420f1144c14000d10911000084243d20f443c0042d490300030120001d04010741321804003980e14003d10880301642ca04005030344ca09620761305001e55030b0032000c02c0d10703000d4460b0010100c0c00c0c1c94692a49480b0780215802031110381c09650074005140c004070191a02daa4032500b8550140d561400503040a006000e8000b620f1482e1600b001400d000d040096030080d00911101130110b6602100d4070203075001c404070203d543d00c4a9000700c0c030380ba04507070000410000109601421124000c02481402070998414002e500c131b100d44410365100075903000b070080d001c02 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 96778840 1250 96777590 96777619
    0xd1407120507150e180601080a060303020c0d030905060a09031406040209070c0c0521060a050705180a09060b041404020a050715140109150801060b0406180302040f060806090606 78
    0x390408810250b40c079002000345544ca01041c00c1c50180340c1140b1404419108104440d6030009220360b01610040007440304500d151000381d01c0b034080040241c0180045c1409c40107150107030006400408000c0d0405654502800c0014403409190004440c8a20080014403800760005482405a50024003006564813074203400d03125241605800c45015003409400242582c0d0b10300554105826811480c041940000700300b03040200080c003c05911380f43c0424015655442400d484c0b840800415042c5040307540400615012042e6114550b0903041840200f002c40e81c4502900403101803000741c1c40039656040401060340907054021000903000d200300808100d00c3c41500c1480044d019001401d0310310002d425404403c00d030420000c80c0d859103000e424103c0382078000001010340c18020000641880619485845a403050504020f8000c401805482d00c402d6082c00455000b0000c0240c26140c400302c2000c4c0205124a80c12030080000145141001207001c51203074800070720030405807064 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 96780090 1250 96778840 96778859
    0x60b0a0f03060902190f020607080714040312030e0d080105010507031215080d022109010f020f07090c0e0103150302060a03020705010504050a05120c2a0d1407120507 73
    0x40880c2008041e12144006564206840100b02985d0f042c83c2e0031244910450000c1c0460592211a034115807148081280d0b041e1302c11030030f40e0013000d0fa00e071203c90300c00e002c91807044078001d54001030088804100c22000007600b42d0b100003484007088060b28000000b40009450b090024410280421350400c15600003902c41c507601c1d030013848000780000c4c2414264020a4000120b030300b1100310366010800000500341c0400c28030800e01d00302c04000c16803080006c030355200703070181e0189581840b03107024610748154003e02c1500120888141203032400c0b9a00e11040000d4801b1201590101c0d22040e05691554880e0058503030b9071454188691400d8a143d081c0403c0c3d62181e01d5802c200340d401d00c00000024000c1c0640340c00b46004900500c0f65074a941041400d0048481d11801d07100d0b810002c0280e01039003c80c1a07840140e4101406100701481c825038003000050742c201680c4402080e00d8202000a404046c01681a400d0220380c01a43c07284c1108020b0f070b884610161a0381d01910040011480 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 96781340 1250 96780090 96780107
    0x825050108070507050105070903020a05041e0207060603020306040c031b05030303070e040219090801050601022107030306051f08010b031b130b1b060c0909160e06040b0c060604060b0a 81
    0x30381d03e402403502d101d54075030786d00711803013a144a40080e0441d0000c10561070180c5000e000382c00b003201c00300402405003054405181a86514640c0700b0b4000c00c6460900c4000e038880c1c8011030b00074058a00324070f0585060014a40c4a000c1113500c406040500d19042086580c0103050301d00240c001c40c615199242c0c01c2e16460280710b5650350040e02049540c4001d0107419060214503ea5202c2c200e00609048030031b401c6d2800100740504560000b0845004107450418021880d51244020740e984e00c42801c04401826081e0403590300500c29a03555050305001200306409242c6035a5420990390700c42da0b8008880c0300c00e4030072603640c1985818001505903e04001c1a10101e01001002007960311580003141e0f401401d0241c504c60849401e10082d07000c180400c43c0d100d09600412441e0040300700004000c0f00c0098002c049240c01c11030315600d418025410225503e2000300100d40719595102c2a44260780f00c8004c0c014240030780800f2900508084c050361055601c5800118102000740c042100c0490 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 96782590 1250 96781340 96781351
    0x3050d0507031406010c14030406021608010b0d021201150608040308150906060a03020d060312090f06170c0d09080318030720010212070b0a0b1e01030e0a0c0f0825050108 75
    0xe24547c4100e02c40c4030204001c00c02803005030041c00010304260001c084c0006c240e407080301c0c1641800c1c0b070500269500c045a0000550454801c49103a87c68a0841d00420071106043c68541c6108404140c3d103411031101d5200e144290744050041e5911581081015128404642c00411031030200c0d24524205020348000300ea2031a0050604681c5640720007640c80030340c030a8648003400041040c2041c1c0c45080100134284440060200c81e1402c44c00404040c00d601400c0310744244900802c0108824000311940d6000405060003104440d051605d216030084d11002030f00303c0340400d8903040d8107000c000d0350715071031f00145505200340c2c1040182950800581a40d41103004a03260500d081c500315000d09078030f5000c0d42100d500c41c42e00b0104d4a08035031004521612500c5440089820f004200030280d00450080ca4007084400f03185024038540310b0b03640320007040501302030300c082411240b070380d170f040122080842190419044084090b40325004111400c0000d00c0b4260280015400ba10071941c210 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 96783840 1250 96782590 96782603
    0x2070c08030909220b042a06080402010e0a081605040f09150e070509040b19051504090501020d0905010e0705040b0306070e060403080712020609070f030f110405010303050d0507031406010c 83
    0x4c0581c2c03510400d003030403070b002c0341d544000c546044200030390701003801c82134016140000c0704582000c10140c010b21009000030704001d00c0303000d001c0e12a101c400a0358000c091420071218039030102c0344601c0c030a01c110700079140920302d440d0b11841031151500850102541101d00340041e4a20416950058245116450f681c4d20a4100c00501ca4955a198034440c6005059043c21820700820004c16100d402c842d180c407403418002403043d4460889100c0c3d8036084201c800240752601c0b850564064000c101407200c1091070000024140001074100c110795501035802d0b00d40c0c0351744420410040764401320038290154000c0c1e0000386950700400080441101c01040142016a260b80325101c80d0f1000c2000c85107040c00080e100540c2e5010460941c10000d9400907242960a08210003100c0c0141d00c4003410006030701d050725003444806c82507a00141d03c0a4014015981c4a0401801c42c0d03101c000070f201d80c9031a01c000158842d01c01c0c45885903040c1c03102321041403030f1070746001102c001148400c1601c06 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 96785090 1250 96783840 96783901
    0x607050c06120a060e040c05040c02010f021809010b13030212070801110d0c0f08160c0210080907120c1203021606030b030708160603021c020d02070c08030909 70
    0x101d569280151400d450840d0b00b000140ca850000301043d190154000400000107200344000916401e407034000381c40302550f001410743c0c800141203015103e071182000405200140d01010621000c079a0f094a43c000e540311442a40e0b2281d0003c503070b00c29008440c600b03074100907003400180b0b0842400203480403414100c41e1181c0d15014410300311100b1040f108028400042d41904244079402960801c054605064640901c0d208002d40748100050242e0f048080c0d0b45c03e244042c60042401ca082d03d90003401c003004504800d0b0000d0246003064510062500c2044400942d6601807006c0081e001d40c0300c16102c81142c40c00503018080c00d815070045055001d6440510300c405402a07401004000d203590210300d0b0408982810706158982e003200c240f981040d4000c80058a040180400321141c9140040e603440170910541030a40308245200d08080c0006803156040b2002e4014010083c0600d16048805943c6c4042680c2e03849105001ca4001c21601d001130401c0c0982c02d10818034405116141d82e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 96786340 1250 96785090 96785113
    0x90f1404150f1d0a09020114031308040b041a04230a0506180a151d120703030306050102120a02061b0409020a110c01050412080304030311030108030712020705060405060705 76
    0x8000303071143c000c081c8408182c004905141c0600a00c9500803000110030413420825400007002404c0e8503405550250000001c00ca0780565490380c3d003221383d00901c500341c449440b080c03002c446510600c554038804d10710a44090b1030803940400c03101254004401320040c0a20108607207540a4000801036004810100004450f15548000e18420304402c0c10038694003d100100b00c075480702c68102440c403242c1488070401c984d81085a414030300249528403c402c89041e00016100c244803143e600c503601a0f0000001010381507045a0300b0380d84240c095070341c0c0c070468003014200340c0941ca8151300140d01c401c0100f00411602c10500c882c0d0001a0003192421361121180310585c2d1108442ca000191420001c541024080c042c150b4440c4003407030150b242c1850030803115004800b04402500d80c1c80000040340405010790702c51101d803041c199040d42c40e0f603549e95056899811058041e50030105240c50072100b40d01c0071540c8030907104003d1019040c1170600084c055590000c440c111038070300c0b98818801 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 96787590 1250 96786340 96786359
    0x703061d04060f0f240515030405012a020105060d03050301030b07030912090303081b0301030201111c0e01020d080405060a09080d060806010303200a06020a0302120c030601090f140415 81
    0x401c441506803002c10428940305c40b408135181c41d1502d9101c0841000e10500c0142c0e256800d1209001c80b02c00b910707460751240d0401030300400728035501c004032030b184400c41c0d0456985500e0b8000001a25002080307580d80308002e112614484120080000d0810801030000501c101c21303d580025040c9030009010a9076a5244c1c0305d5038000314041c000c41c0e252201002007660041505601240042c14101802000d0803501c070b10703000601000f818040c4081050b02280030411100c2c0308048c04094082e07400b007040801070729000c619828540180200d040505a050185d4040c900843c0d21078020b10b101d51f10100701000505001c6002c580c048800c00c91010480c0140c0511409400c20500ad8580c2d5455450050080e1140c1f1501da1060400395806d13800345400030914a414617000480940c1e11882e000c411002403003020910341130b40400d28140504c8a00b100d0186215035002c7c0c035080469511494004485011881080480c40c0c044241e40305a00302174101c1c02d01c8407440d0100d003080548856100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 96788840 1250 96787590 96787601
    0x50115030804090b0103020f0d0e0a1a0106030f0509060a0e0c0d1208100806040320060403030902210703080903160909060b0103020c060a20041d0703061d04060f 71
    0x240c440003000714040c0043c00c100e204519a0b20b0302400c04501c0c002d200500c11815002d102002c004140d038a42c00000d000d402480b1840640394006442507000c0c8039000c00b002010b6081c003c01000901c1c082d42ca4680c0c0b031071807040d54015078040d0700415581d680d0803070580103010304410030710050041c1c130102950384d114a41111041c602c103403010158503586e107400030440074004009051230540880c00f003101c3c9901040b07a03900507400d403400103000803d00650b281c141001000d020510b104410410060640c141d00c0b40303440902c22941070b50705002d140d990b0307103a00560254a1100c1c0e0400c1c43c007000000c40440c0103083c00400581038400c0a200b04130b000c481201c0c164802c54040761108600c404000e01c0340704070800c5510900703045081c541c115000d00c0d90f403d001804810401c1ea2074401c41c0c14041c4a0342403083e0030000d02c03202ea90719501c400c025404c9040040d030344d0b51211070b042c010500403070182c001c420a82d5000c00042c100e12000030f03c0d113600090003800c29580582c0c0e4040d4061003070301e0340c040c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 96790090 1250 96788840 96788843
    0x5010f060324111b060f07050301030b0a0207020a03030302030a0501050a0503030a031e05040c0612050f150a0b191803030e0603071e0e1008010b040501030c0212070b1012080f0705011503 82
    0x1319981d001400001d8200740008058811040c44c074810041d81c290808103032410740c4d81142404080790382e000c3c1e01c05c00074071403004003039401600c0c04000410154190000d5206100549040c03100e81d980303800b849140d00ba1800f440358075410074014014034501c0707580200290903241400d0240842001500422a134081c2d0b01595000500383c020300990b90800c424135080c002005041061345410100c1c0c4109850183c20030321200700c201c49540704c0e40d0340c80c04054042e10104480d1540d840d440d0948000e00e41140207141c000c42d110381301940100000c84103100449405071112081c1d420034a0030021654002082d000c103002c010b4000066080340c030f0700c22540b41e01450b1580102490480e00300300e8156010004201002805c1c00180f000b000f40c60180c0342180c10a007804218040301d1a01603041000e8490500300d0341340080380c92007d001c205400c2d207015104140621000c1034a0b4480742d40302044800010346141c50801101c04c0c0300c459030008204542c02103000180da11003802d01d1802c0d122441e4030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 96791340 1250 96790090 96790117
    0x5090d03050d141b0304080403060b0f040c080106020c0a03020901030b04020d0c080a062702010e0102100e0307060b0904050705060f19030504140f0a06020708120703060305010f06032411 82
    0x1c01c40c0f1000031103030406260301c00f0100390303040d41b81590b942d21f40b40c0305500006000d5520b40984401e42d071603240488503003100040045c4802d1102a00c001c200c05024402e000051045501c80512030528000c0c034810342c1d80141c4800c00300d80c2103880d030a0707003414054000c90300710f440c41e020800820000764a4501070141e0f42c0c043c0c000c440d01401e01405840c561184004000b05150480a20340c5406102c481ca0701e07420b0130f0111400706428010317424904803c80c4610814141074040003c20f001000804007907215010801c8107880c5041800705422017120010100e51080d001402289000805841b14424110456103444e450444d180c607400501d0b541100420340300c0301400100aa00414400446529001000c001e408213080d0b990360740c1c044070080c0c00c2c3c540c009200014004140101c800c840a091030000060825520080081c10305100c103890a51030540d64201845940c040e050440b80c200c1060307101c0314000c0d0180d111075400208048403441c0e65414a040c1d03405404041d00240305800b1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 96792590 1250 96791340 96791381
    0xc070308070813050609130c05090a030c1503050132041103070905040203100302010e0301060e040c08150606070201120e060a02040503060109020a0c1b03081204030e01030c05090d03050d 82
    0x19142440c20b43d942200f441060107208000b000e4070303094541c1e04c401e040d4000c0071600d20b24600040c0c4031485105601e40d041515480c002c404d002d00c400010049460414544242c90300d8054101d0403500f0a016030fa2041800c0c5400d81044d80316480300000100c58910103214007040c840006003207403c0d14841400e801e5020007041140361700a0348250041034141d406500d18a0614114000c0100320b01000f411301c98000c60140c11034800750b216601a0a240b1081d000e581041e00781400181101d21074001688954018128000c40c10300351036010b8107000d883c050078007405900558032051180e040c0404142d640c0300490130080300300804c60148414100040c2c0e11810f12080c1410010141c100072421b81c0100301107041680d02210f2000c1e02e5030080040b0385a051035010f60000d5140c164409020203201203422480a80d141e03095a000702c1c413a4561800c0b01c2034810064081d00d205086180c04210300344480030fa0390804604401da42d030f119281c6113203080940390312041103548240d4081946140304 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 96793840 1250 96792590 96792607
    0x3040b1e07030501050321090103021c0c020c10020703051f140118060512030403061d030a03020912010507171008061e01061403060f060f120709060c020102120c0703080708 76
    0x5100d401f030b5a550f914150200f076500c0b0301c08110207101e03d80085d410540e0000d0b101c11030a081d119040e5008001c1031050200c000794200c001d6441c80081031040c413481401c1c0360880d42500008800048960040140c0610200819001c0014045404c020400c80d12180c820940c10210799205010300703424103000c01c0409424043c80202d42060b08228001e401514148404080000c282c0d011203607c4900400c2e0b901c00c000c45d0104142c00c0405508643c80b012604600854141e001303810900419103002c0594075040d014a82620001d44159002c510340000c89602d0010300c90089500c40d5060705070016855403152031a01d0444125078400c0b200300110600780042d100c0d0141140140707243c3c54501101d03480c001c1c40070840c0c8406085d280c401c400103034869a40b91607850546407e440300e8008140c0303803981e489092855807412100d00c000140c0b180c0e8041200c41c01184c15101564041e4010120b4440340c0340e0454590380b0050740354a980c420200000009001d0714001d0803072a1242c1a495151181c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 96795090 1250 96793840 96793843
    0xe0d06050906090d08010e0c040b03040602040501081506070b07031803020a020a0803030115050a0c0b01180b031903030b0a080712060f0501032018130510020304050303040b1e070305010503 83
    0x60030f05003103a003124201003405940b10350690705540e070211010391a5100c10208056601c166800b910308002c02000700418001c10307501800442d402a21103010a0b669041400f0141c00c90300520b40d40004280084000b14003501c141580c0101541000a2030258141403040c040c5440c0d4000c4005a1190710703070b9000c50408202903001400c2c242c00a60031941004400394043c0b504a0701e0750308110000c94500c00c0345105c1c007e000c04903900201002140c0d6140c413503451800c0c80c100032a100c05820301d440100d250600141202da1401440c1c0d0345210003029590450160a240c0b0358075034001108200481c0200c400d01112380180240400120301c02c00d41e241810603668603110301004149010010030100e10348c12440c8081d8041488110034055021000640c180c0815040300644001e4800b0000688403c0ba031305419607000c0d0042314400322a0170103003c141e1004480c0200541c0046c07005c2000210156884c0307030010301c01700510b0303c01a08403403401c00c210002c40b82038002903110780c0104901e090 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 96796340 1250 96795090 96795103
    0x1005030c030102250302032503180302010f0302130e130c0905040803040210031d011d07120605090f010f0501060807020a021e01050c0a14010b01051c0203070e0d060509 74
    0x1416002903013011010f13049083c500d0b00001002d0255411301084108252086c4102e840c05d11316070791312100c0510144407000794060b01b81421004151051440081c59200305019000c03640d050351140c18220041c00101c000e0341141508917102981100080380ea10141d01216224119414511000040d01d0800c1d5078a03404940c4901451341c0307403005101c00700b040e074411a07a0003601600d9880440291113800c038000c020051140005040054402e4401030040d000b038408100c0410182c07092104600046884034168411180c5907104180d00c44006041500529405040c803c240c2c2d40780440c55a20300c5c02e5a2070706501100e650340e07680045c1b03c26a0008a600e4201c0d80e54402020245150760100744039040444c210711112003506070074912a0712a07401c07a050120800195101c1d4119031800c05119000c0420895141d400d000c6084402c0d40b1075410394542402143c08024107000c10b441e60700080d800900044200180036524003541e44801e02030022403842014005820300d03010310644c0c07d080 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 96797590 1250 96796340 96796363
    0x60409060e0f100e060105090d06140a060b0405300703060605030d08060f010806030f1005010e07050c07060e0102011103041109090316231f05010b070c030f03030603050105100503 79
    0x10301c0040c00b44156064111604d40c40082807c10954441c4810000761902380e070310000409035070a150012448460103090a801500012000e104180c1c4039024105035000d035000345900a1070040c0a401a00d10310b6000c0300e43c9403845640354008040a24215080c096281c006444107906c941040105007010400008501c1d85440c0101c40ca090500025a0b0f0072118000d282c1040b40e0100456034a0b5024031420240386a544121052420b2124030300000d030009215a04645013268000303100e45004000f00ca280b008003801810710b05090007800e440703045030507285a04565841080400180380c000007107005074003649ca103d2070340b810310080020302c100052840a017a0418030504100ca804080c42c0100c00e6403044a0248048922820f1203071070043e07242d1500988074400c002102900b10000078012208905400d101580e00c44400c0d080602c107800700109604858142000480c0031200c0a411a900c00d02e008034080360b40ea02c820f401d45030240c80c00e24007035146030410410b61400b00224a05d00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 96798840 1250 96797590 96797611
    0x6070b10080c1824030d0f080a1a12160b04051903080912010b03010f230609070302090f0409030906090e0c070209040203030c030d050610020307120e060409060e0f 72
    0x40a603148140020304408104a00e0380c902024403001134518030080d29024044403403860780e90a00410007064910842c0c0841c500c0800f0a24041c4107018a9035005020004d0f614151821b1040c4003800d203040480c440c04e801421681420140d4414a1714000c0940d120542d817954145410048500c028440303444900842c03003000c0000811680694043d410100c03402010201c81048442c054141c4022265141d46000b540340c3c80e0343e0701544001c503e1200d54640a039113602180380b40403050030030761300a5480010400003c032120310079001001095030241c6540c1d041c0014001240548011182c110049810004180701f03460f441aa504000c007001d492180050070045081c076440d120380c0758041d0080380141c00007010354a04108a40d2123280d404100c994a102c103d042c20300414060b52440d01c41d850350300b4505402840001507900d43c940083c0c524480c0416035405440f450f1041840d40c0e00103005102c00143e0702d101d840b51000516040c10f044403507140544416030f0703011006003140d01d00d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 96800090 1250 96798840 96798859
    0x3030501140a15030f090b09120a0e09040f02060307120c030c0c0602031b030c0306130902060904091b0b1c060f030b0a06030f03020a1a0603190206070b10080c 70
    0x5030782d03050140d000312026810940c0d038400401c40102d0151200d40b074003003100d508002c8103d04103c004c0c4210740c4910f6900c0c040d01d00908500700e45501c0303441050440000035021000c001030380d10b440c3c40002d800c1741c82161104c0560750780741e0119602e07820072582c05012070859091b041c41c0e0203090203214410445813404011030909208058601c42021034040d20459010001900c1d0020181d0448042d0401e4510340352245000341c030040f055802111028000d01c6d05100b402c40300041c500032880f8883d0700410560411020105000003030050420507920354944020b08008810000044000b0740802d008055880a0350121000c00c87d100c0c0810801003450300b501000712600d03821450301665444007072241a505c03010401c402510054001070101e00540c1a04420103070002400105c4c0c0c0c0c13060307a84803000500540d80c00c2c6440000c450743c58258001042c21003810711083c241500340340c4020001810400c03192210080b01d10b0460f030313100c0c0820002100340000d0720100103a4103480742c1160745462 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 96801340 1250 96800090 96800129
    0x3090d0f0f0804140a050703050d020d08040212011407020c0114070c06080a1b0905030c0411040b070311070306140c13180e011410080601050306010b070203070806011203030501 78
    0x401c4240d64456003041a10b50100e0100102d05050b40c2130302c400e5004131403210700d460500395140d0701c0c0c070320040300d0b0380c07103207404101a2074004900488114003688980b001691070b81c00340803c418024044071919582d5464200102c1d90816540d40900300c9030f4010050424800000b4002014105803002d0445013800400c3c0010b41c100c100c0e00c150380507450004003d456040c210b0001d411020042c0520400752410f01c2440c41d40203e44001703c070421811940c10000a1040c0130403030f80301d085200c00d00401000148505125500140b0b2094402e1400c909408441c0102500f00313100c0381c00031a00070751150403008100d080c01b900d858109402c041450324015278001560708a1400d03114002c0103800d090b004111880080e8055a4440b00400003400030341c051610107881c80c0070460741d0f8000300c5000200416503880001e0620b05a94000d0000c0900c0d90030015038142d01e800c6290200e03894850414003203440305051280b5070007883c6240500f5002c030442e01c1c0280a03604140c0251185122403110a030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 96802590 1250 96801340 96801347
    0x605010201050c0703050c0a0b010803070b01060e030709020c0c0603011203231204030504030204051608010902070804120c1502060103110d030c030e013f14010b03090102090409050303090d0f 84
    0xe0781c4c03070391608000b6030780e040d00d41070300e03060020104010300350850601c00014040000700c020400c1501c540c0a075803080e0b80741d801c241d03201180c2e00061500766000c000d061081c00750a074000c3c108600610201ea04c00c103d02d8000507200c0e0b000360031180000103680c16541c100740d0442104407002c48003004e00085200400e0842800e401440341ea540300d4603120000c5801d141c0560101e6025640240042c0014900064010401d445040d103e800003581140005070082e058070988006030351040c01d00d0300d03052418801e010094986202030311254050840052200d001c00038000d03042c1c140da005000c1c50361640c1407201900640e5205d03680105003564521000035403040364101129414201401340e100b400004a0740c4528106c0e075208141d1a0750000504128550000c1503da600840418203000540b144441541e0001181c0c10751b10042400502083c003080001e180d010780c2a40c001403d000e45d1b0000241a55032051098505820000c184803c2c1482401068015290390800f03d420001c01d20004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 96803840 1250 96802590 96802597
    0x41a070b0f0601170a0c0207141810050402040e040c09150b21070c020f040603030e01050d09051203040209060405090c0d0c03060c170117030a030b0d050109080d0605010201050c 78
    0x500070303a140ca00007003803070b8003c100c41000800c4d00e403042000d0345040340450006090010103000940f10f01c2c5000111601e00d100901d820300c0d005051041c021080c48010b01720400040c0c03001d500e210400c01d01060340d44440c0b000e04010003001d0840002c42c20542406d11143d04941c003c80c0016081800c01d4801c104502a54003c60304c06c01942913403428001864007001d900c11101da0685094441801589a0f00a01241d4254001c8648024842e0a00c1c100821686c1d2440000e0100701840c1c050440d540c0541e000d4081c0030491403006c40c00303450f540d4416052a5007203d03580c843c040701009010542c1007042d0000d40c01241a502004181010818942d483c8525900107209040e80c49620041044601d2013500542d8440000d0000401a00000c6c01c005000700c5500c03031029503030000080c010b40303181d8240745908082010f1440c4c00c0c5681000c9001d0b0403641441c0340c2010711103c070000003c90074441c2c501024015000b450300d5503080c02402c4180d41c500d82c07000b1304581c185400d11101e4103100088 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 96805090 1250 96803840 96803851
    0x14120a050703120905010506030c010c120c0f060e070608160905060d0204051203030109050c210703110d0e1608061f050a06020c0906040624020c03070b041a070b 71
    0x45848001c185001c48180b00d0b1840b000d11801e080680038020444150406409410110150f444003440c0c0c01c01150440883c16014001c084803017442d07203455000b90905003c0324010004501d23042450344400c4262069074800c0c0300b0992080c1001c1043ea64402c0e103547d000400008082e880703108001c002080710341039002d02807003040e00141352211b000c0c0590449004090190002a05442090020b62660400d2140070039180c1064001039502440e2801c0303d08000c4c0c001a01d5201c41c00180703141694100082900e024155118200d0111049000c0507120000b1404c0012400d0003002c448103041442a07580010320728402030050100d482c0115510741c0c8502010281c40d1194030401c0100b414400503480280c0019580342c01140303042d8045243c15401005035003400803a1649010f00080394040e03c02e4100060b650030726903401000d030201c5680800c3d081d10440300c0d10310702e210000381020131962087d0300c242030009041003843d85c0c240e81d14520408580342a81045d4064907101ba080d80300400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 96806340 1250 96805090 96805097
    0x20d1706060d0c1e0513050d051905031201030516080106060f0c0206071e1e0f0602030601090503060118140601020a030c03030e12030f0906070e0402090f030d020a14120a 75
    0x42c00c0583e0352140d040b0403039192507448050908021010b01a000d64030580d004043c1041325500400d403400e01000d410015980003008000d40280d0080701c00340704c0144901202c00740010400000c40b0036640d90302034044c60142029100c480b12052211200d01010707400054588d052007410815207411005c4e41c9100070721810001d920462510002c2d800380300d4814000c1006070524503841180a903078054400c924440d0a142c0f020784196404814282c081d210001c04151640352080c0014401d600655004003040c1041000c040d1550002030609a090304030b03004020341e00c504132521085901903100f4004442c49508810b0510000003511078034200c0c00901440010141803040501c2035110302a54643c4005882204190203441d40c11540b05560f0049000308001c0800c41d41d00010940314090b20140d02e030410401c03c50028803010f5007080e0340e211303441145403200c08500d880030301c0b003030035031407110350203042080380d185840f00c98505c601038801030580c880301c1100803d9040001301e4038880d24504 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 96807590 1250 96806340 96806351
    0x2307080f190f09060309051011090a060c0c05060702040b030a050c03100203060a0e040c0306050106080412030213050909030f04140405010f06050d0f021c09060b03010b0604090207030201020712020d1706060d 91
    0x81c81450000c0b030500108e0083e00e0040e4a0314076030294400350001100c1100d201c00e034103a80707a10455000468800141010108031030030001d82c5040401060814400b800100d402c030600c0000906140c00b8150684c1c850f0090380075030742d40b0b24041c0041e4a130100302000850450a200300482d88000c064024204915484400310f81404a9900c808000750b5008100780202c0d83c44050041000c90299401c4940000b001ca500300103d0203402a035003003010719902d421050b40b0704000c000600e0005819110300b0b0000700181921031044200510250050802c1e50707140011883c10700007200c005070b010340d00c07000035401e052000540c081c5c21124200c4000d170300841d440e8046500b070802031003001220362200000e42d0302e00780c080e03207a9084041814010f0b001005002c61840c1818260341c80200c109510030301c100320a124558460f800740210500030b100040c00c1c0407003542c1e0001d06203070809e10740c0003503840030203403c0c05240e00284284980c1c0314a001b441440c18201d020031203900550b001c2c2620141c0b00c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 96808840 1250 96807590 96807593
    0x50c04140f03030f0a020a11060a1b02011103040608060f040204030309060c05191202010f05010b0703110a0204050f010801050c07171b061819032307080f190f09060309 74
    0x10030503289000c0e01c803180551394045e0458065621802900201c03a0001c010103085940d1074000f0603114100803e840d442100d014000e03007113041c43e110072030881c180012402c1c40070071006e00300044c20142502d600c5126542c144a410491402c480c12403242c86980100000e000103503001800c68111449410080b0000065140007030402d10345e000786d61008030080b0011400c0c0010300a10780071070380762500200007100e0212125000c0e244240240c2c0c19400040080c140041d00c100300b04940d40e1b012509551180c1d890340e000030150b9100b030b200d1010300906800103000005080c0b05a5070030110100031031b0315000e00c65a4034500042c1c0c0e02c4c18240d5422010600c1084042c0c8089039070707000e0b51240140c652504c0e04035031059003688510700c1820184220b20003089041803100003001d8003038040e01c9604012659480305014041a0302c169030780b0610502c0782e140000e9a80020f480a04036076100103803210040d1150079038821111036400104620407205403843e68100d206401070344d0407460301050301c3d0401e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 96810090 1250 96808840 96808843
    0xc01050a0509100804060507020601060e19030501050901020405120c0a06030b0d0c170120121e090d030c0804020109030818060f040614040f060305220b04030201050c04140f03 77
    0x1410b1070729400807085000b83c141142d0207418144a00d2054004004580b10440c00300c3e0b8680090250501140d00800c10050a15152030700090340488d41e81d0720000c0790b80320f84c1c0b61401c1d10001d0b100321407a030390003142c140500d1900303c071001284160320b0020070005249400041f040c1c1c0031441040f007810340d125141c50850b03c4c0c0a20800c0020b41002c8000b480c1c41d90b5052018049441c211044010352806400a5112007a05039804c88281d049101500340041d255805500e58405062040801030395070f034511b05001911565849202500040c0041c0c14284101038103840040c04030f842002640700c20400180e0f0050305040a0f42d402042054032001c4000f40800d00c110030160482d80068045001d066060551000744251541540e501350164444880e80006020714050841c03003d004007000e0181510aa1000d5030000292034100c4a4040e0301d00342244415002d1000e41d0358409402c204014941c090065a80110700300c84903a04d4a07242c96020a1a4040112620f1045a0418610700203580 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 96811340 1250 96810090 96810097
    0x8011203120b0a05030d0216050414010b0f19020f06160206070e03010b0409080c010f05040f06050604090b0403050712081006050d02040308030c0c0c0102030306060a030b010c0c080106170a02030c01050a05 90
    0x10064106c84a40c0d0340c1d000c0103580c41c8143c403510390080174501030126603428035000d01c0c03400600c04024040140d08040a03200640c05c40b142c942c4e2004000c0c400a1020045115055450707035407030300945824a0300702e02c1c2d54200180104510502ca40d41c580c040300203a030001c0c6140d03010000f0326010400c44031071000280501500d02805600c0350401400c1c1091000c0d0750001c140c60b2100100801009034603031000ca058074000ca4000d0808810141500c2c0440c4d0540c0180313500241c02800022408941d96801d0f4500c4020b44040c0e0000301d000c1904420072040145c1c800c1e820500303042c1040300b85000b01c1c8070611003405000701c03410041c1c0401c4a180c40381e801d80556020756481030b10252070749070030f00e01c040c041d03000981c7c02a254402c00840014550011084034060381c00904000d1409101d02800c5c3e000d0301580000f581000325003003032040031803d0a0007140240ca14500041072551410f45019041e41244031032020a411205000d001680c0006209280c01001e0800c00d0316014101c4081d01c0b10701 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 96812590 1250 96811340 96811349
    0x61a0702011206140a0f060c0b090c0607080a0e090c160309080729120a09020102031209030405031b030d0e0d08041e090e0d0e04181208011203120b0a 66
    0x50600300f0119400c4003c400000394507405841104041750b680c441c2c00150390191258078003092031040305001085488090f40c4d032001d044812210b50803000c0c000704500780e002460a40d039100c0086058800700c0d40c450408a250700c411516140709080540c0c500010f84502c40000603048525000c0c00d0425002d4510341005203030a00c01d84080a070340d42d20720891400044102c0c01560f090301170000c160b0f08100240d03001c08401c5021800c19549500c428401003082c41401e03030562000b44044000802c0701080c0754800c0c1d0540001d15241c0b4604018185040c03070345920981058440041c41720f494070000340c01c001c04003907440c01c5040d1240182c040380303d06614500c0500002d0001030003091080d0102c1d5900000b81e52500807aa6885d600c0071030310304503605502112230542012040c07602540c03007003049d804c00c03240080c00001e94400780a004da0070301e003000d081211402074040d407008000b6040b81d070381307801040b00d5031640c0300c2034000ea074000b44040c18911140702c0c01c43c0c2e9550302d11415101c0b0310020005d072 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 96813840 1250 96812590 96812627
    0x7020709150905010b0c0c0f040f021b0c0102010b030307061d060406050403090b040506070b04060b190f0e09030a030c0e0d031107091a010516050102030f0708070201061a070201 78
    0x4500c8107405203141495000344901981048000a110381140c021a0250039068005d030030421128020000d445003c80c01d0309500c55202c40c1d0004030180c007403000703041c000740e41c0b414162811040040d440c00c120b0b1111000b41503915001110010307403004000c4a54807503010700c0000d051003000384035980704045800030b250907200702000c00080150344d80c00180a94001c1d1100310605a841c040c0304d49500c40c900620f50441001d102d450002142403181c0d640141c4140408101e420040740801d1000d03443c8223031094030b003020384020014040f800c0b40450151048a81c01e00c1c2170302d40340d80402d0396071191450301d404159698240c00d40d01880703804480c512140082c04900541003904008043d4540c60721340c50541d01440f2400620408944035000c50500070000060b405000c41005540c0340e0010802040521300c03109415000400c20b1004510484114811260310f09010030000c0c08244010010000c1d0789c03402d0001e10041103000380c0301001e56035110403e90b0313030081480105c440c3c1013103101c0b03015803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 96815090 1250 96813840 96813851
    0xa0809011803020d090e0408040b03040c090e07030b0c0a0e090a0f0c05040501031506140d090f050d120209090c030604020c06070306140109181808120a0506030a1a07020709 76
    0x1c041c1c2c0444e1a400da070340c0a9a400c0c140075207a0046040800d4203a400810a42c02000200a1010000701171680203000d203024000c0d80382d640321404c0a50301c0010013030050f50400507040c41002021491190410548400b190800001200180030351a504001c18491000640007400800c0c0d660440c0001703031070a040c2408001c00b842000380558019015035401b00c0d0419600e8030100388001c083c0300494885a984030030034040140395044541c020a010010103441d080808003181001d07400d06030503441100102601500310f200100305d415102c11750f840c12130040022011075070f68142c0d420713044100100d10545c0ca0f103440340054001e01c90580c1003d900d018100c10490f00980513405202161510801000c02017407040045620050a020300720750500342c0d80200c1e044501e140d12001c0700104044c04482c81c4211512102415040f410007002444034080400a850416010306508400164001c0c21400255554001d020b9648a181003e1020201c0001c0800d1300c06c02105000f0113901c03104010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 96816340 1250 96815090 96815093
    0x303040801060b040e01050f0d2006030103050f010e03070f02040c030f1a010e040b01091406090a09060609060f02100c0504050409050604140307051203060a032a05010e01050a08090118 81
    0x3ca8000c0d110724000142100000607143c1400102d066680c0401031040460485d2a5201c4000e07000300002801001d40201c955a0380b03440e8000110302941c000c00051919000e00b080460a45409420401d944c0e0014898000015910f82c8880c2c50a070b4111404164a0b16071441280102892802a00b00a041291921460000a00921840b1003c1e40c5003e0481c61460510003942c141c51032507130010744100e0040299030079280400034441001840c691070725940000160040200740c114100580d640d20f804c01025802c00302500060819040040ca216000d0002030346810503940050b60094031200ba641405114500f214054000104100001d0545041060742c440c0b0490301201c841d00c10300c0c000008028000151b4041c00d40c001c008180d20145c000402819400c050080c9820440c2d180e004070004c0c668002060132001480f11900110b0260300440c08400303c0d661100741403210315a45076403640d13400b030f040b50101e040c5030030000f01e07985032a90442e004003a10f000f080d840c0003c0886040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 96817590 1250 96816340 96816359
    0x902240f0a0c03120605060d09020301021605030a0807020a17161707060f02030c042304020d091506150c0f20090f070210050603010b120d110102030f010b09030304080106 75
    0x4031a00995900640964003800d003003c0b505c1134000d291f032220052000e4503400030307103400050603588003400250400d22040310014109070b1212040f101500042080f0b64003d51007001168040d0f0184001d040c0c03501c164a51090490000300c107406603034800102c004860b13240c03201400c00b55078049100364242c2c038032140c00d6050f0340190314100c070041d0800705444540103c50080d46d00401140724120718003854045100488000305050103281c04690702e40a03510f5540303101400015010740c00c0421440140c2c9001c002c480b5440307000800c040e2414405019006900d41d503d031014040d0708001e000c0015a090801c100921000001e283c012000100419010006a407000303503541a6800007003a1110724000390102e1044400d4401640540c40c1c011488819420040d00a04054000034260500c48003142c1d003c0400e10001c000d81d4404010400002d9014000c00704070f040c002c00842c154106481040d164100c1031042900f00305010900250955040c41103a005010010080100c15550110039 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 96818840 1250 96817590 96817607
    0x52101090218010201060302060d0b03190803100801050411010305090a0206040906050405010512060c0d061503060e090f0a02061e0c0c031006120f140708031803010902240f0a 77
    0x1542d4070310502c2e4a03280650050144200381d0b40e00600c0f940c24110003142131001001e14041c1d943d070600c6090701104148000301d0701c0c164040d01542c030b00e950301d01d0210140070340810305a1080074940c1c50101000040b54480041a441d1102443d01040b6511420341076450b008481101a40c00b060010b030020b4031101c0f41d0301c004122501a181400307560383e00c1d000c2290064600100c0300b1036801c0400000d1492400030010040c41751038a00c00228503803992680c4040c902400d4001c404250745407001d0002c500d02c501c41c0396114441e00002e02c140917460480644030b45800d08000d00510b804034011040441c56103095800c2c00c2c2d01c0404581301ca204140042d81c40c040d9003440360181c0a81c0400301c200003000d0045409440c0450030302c001100341603481003000c000b07040003903c220780d14480e01e1183c26000d004803402001e00c10021522043d040f16003541e4004005440f0384644e01d000705810040e1078400d000000b002c2c1600c5002843c015103e9001400d00c80c500f952480c1540009003040c03000c2c6c00c075401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 96820090 1250 96818840 96818857
    0x5010806130504141f06120c06050904020d020a030209032503030e1201151d0f0f06040e01021801030605040218090a09062a0810120305090d030302030405060f0601050306010521010902 81
    0x9020030b075a031f07440c0d905241d451010003605000e6820b0007441803e018600034071851300c01038401490601c480120b50101c1e008009230400090700024a40380e42d03d002c00c070a007001c0c500d24298145584600340010100c1102d0720008051103010100c1c84000e945165840e00b1081d1900024030030703401c031610030409843c0c55001e01c01070204141e0302c86511100c103808591060b585584034920315252809030401c0d0304c100034502a80070382c6402503080038503000e002401442919803030000ba1101c0420024007034500d240c0245000c1c500c144050211641003101041441c0300c1500c9003c41620b941a99101030403502d90007400042c20000c404c115100b02d11b60740c0000145485a40d80903050070300040382c202c00c0541c1c4507503d9204801091000d04e0040100240c4180300381005840c0c841c2090100c2ca0340050311400740e0200c0e50200812003446002e014043c0e0255103204901110701d4540f001904078040504000c2c1081404120002e104600c4000f05064580c1100e00f05003540c1c1d04c0368000040d42c8032400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 96821340 1250 96820090 96820153
    0x60614030609270111130803120c03040c030f0b0103060b09040b040809010201020721021501080604061116060f0e070f03020d080909070c030206010501080613050414 73
    0x290621a105082501d0094400821150407a114180c203d40e40c00034a02d40c80e8043c030b00c0c60034601d040034000d1050400100d6009402e50719822007048081d01c82e00141d00030307019a0020850801301c1e034050180c0d0396001c42c0c1c00903c1d6469031510f09198000203e0303500000c040f076005c6949901401520b4655604880c85184180918400f20040c02009281910b00900306551080498000342182e0040c2c00b40c168107100041c01c0110944034240001c203002000a4014054403055030100c3e4144400c40c0700d0209000e0050655140c4a106651900f00810203450140d13200d181001d601503000440c1c40c00041e4448600080b03034a8108640180080c00125140c0d500e80540700e621418003165400032a240303500106081841c40d006d000b40c12440c8282111841d030104a07544142e0307a6044a103020340056542e4035011841031038041c1c6410410382016062013204410062030740e59901c0300a03001c0f80791940c00b040715101d524043d8080d03411241031a07503a0046090340c4064811070306590b42003464400703 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 96822590 1250 96821340 96821357
    0xc120c060b060c0d03240906030c0803042301031d0303102102010e040f0501080f1228021203010902090411070201020a030f1704030305070314070203091302130305010606 75
    0x4100030480c40382c500e0741038aa4105984c6424880d000c0d6105c007040c1c0c0404156001148041c0161807240c00d099000390081c05c0c2e4410007401409131030508040903014010040d450700e4142000c3c00c607620040e40c410070003003035842455119039200e5001400d40c13a244d0900044229001c5a50030f4690b0421510b41d034032111985000500081041d81c1b11240108180380840b00e40c20b181c0044400c0c59410b60502d07003203601c0b4045000d1094052142900801c5900050245000d1840407541448071101101020000c10300074240703c2d2002003800010107401c141c4c40d403503e0500640990507c044072044843d403030404000000c0903010f6030010310745000100c604010190313a05000c001d1340d0189410281c010b900051054000038080c01d80362143c04042c1c05d00c20580c80c2c03548601702504604a404400080e100c074240101c542c1c05000d0105210003d0104186501d061000203550740514480389128125a051001c4c840d501a81240c00010301ea0309100c94a94803402d0403400382c481881000002151403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 96823840 1250 96822590 96822611
    0xf03041202010e010c09060c080f070b01050907080601020705280e0601030e12040e190606020c010f021506061e130609050d110402030402040204090207210516060c0c120c06 76
    0x6208540c8030050369106c03c8051800d02000b2204200302c100122407840341080841200c60156004c0d1440d20700c00c0810380182d6042506210a90300040e2000c01889186005d000c0960780100e035203800e4480a03202c044059020302c0a0313156600c40c884480396429020310001c1030b070284040000d840f490007038030b0500040d800f41c03144039551310fa60300c0c1400000d1010f000030b1042c61001044203802c00d14100280105520300d0300302201f1a02d0301d510000c0540c0c0190700910940d6009480321031048480c0c0040d00c0588500c505184030740300e00a03c0c4e50711500001031081c4c00408006140410110254400c9031900001d00c620704441540f8003c0e40d022841c000000032320342c50f10050040c101503018604c01ca19598013810321000c4e40001d04100e030300540030310011034a003420f48060440c2c180940c6005a42c44001c401051003420100d0900c800c0280400c56403800c084030f0034a40c3d0400d98082400030b00e44906d00b40c1241d80031070044000b0264801c4005003c6400d0b40005042c0b41b0307a0082004002078500c5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 96825090 1250 96823840 96823843
    0x120f0c020607020706022a150a02010207020f0a06050901030e010e12030a05010902040506070f0c03082206032c01140c0408070f0f031407050909030a031d071a0f03041202010e 77
    0x281072040320b6198029076981c4031440d200f40103d803c560094400707002c442c1185c1060b2109d07041b9143c00c40c0140e601107038550640c42d0080c600c00210500b03484041c190303030400c44000d05d10f100b13100381c607410b0544900441040020035807164004040400560702e0402124041d0401688203803842c0c4526800c110001c6658890340c400c96048800c024400d41c03a00c03249a4540c8181350111000355940040301e040000440e055500401c3c0684040b050b10107654020707251031140e508141c101307008151400c007001400704a1894400138003d1003182c0c03006da01c01d02511003800f400070200c460381180e80c400c0c1444100d040b0380b00070300182e462100c29a400291150101c6000301468420600c880c9004001000400c0380100d9422105a03c081a60822911400031401081b420755241c03155270b000040009045070b0500c18540714610400481c0e9040c000042c1003681c40c17600e401803502e00c4508401c9811a80a641d00304c50b588032174555007644a00c1c00e42414445620180c180c90007550810f80b4039090703000f0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 96826340 1250 96825090 96825103
    0x23120606041203140c0106060503041a0601020d0e040906020403030e100c08030402060a020f161403060112060509071701051b1603050306010504050d05010606030c0809070501120f0c02060702070602 87
    0x9851589104024581c0c80494100e84e000d0007034031003050b0401006110f5034003806054090540c3c2d441c0e041d80e0341020b180405440d0003031031050080030080418013080740e074081800c291040c0289800c5c69825900c0c0d0018005046282e0020540c620000e4008105a04040b146520000c00c8544c4020502e00071011764442504090090250303004200050051400c0e50207400b002c601441201c0003403070000000c42c40e010b45028a0800214210070401a07000d41c0109154102000c1d00505841d500d80041480341b48482e1034010800381c0c44800003000d0383d20400c00e5000a1403080100c110450800c1081c0c1d009180564042d0b1029841681c0108401c003400201e030810840802012030001044c1c070704540c1604080e01c00ea040103002c2000040a03a41c800c41d034189a0701074400020003520313240b4040c084440c5008988244912101045810036020480b08101c2d0020b081981008044003400c0005003040400c046a491908010055880d400514a440f0700e04503002c031411f1a0301c1d02416a681c00c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 96827590 1250 96826340 96826349
    0x105010611120706091419140304050a09020c01090c0e0f0c0702090435031504060305030703080c0f0c03131e17030f0a02210412020603072312060604 66
    0x10b010440100000e20304c4c0c0c08080302600810424641c8003074a14040d04011640400c0d0704000000641c4906101d10004082903828941c00254501403921001c0b6032250702501c1400344403540823400e804040400c1d041207030001d500400c10380c074003034903060000b29884054a8444103112000300241d500c0c00c00c0c204071109150010407240180c0d613942d948211111440000c1c043c1c14100d2040c418801d2800c0d103101c8007411240c070109403030f450701c6113000d0329140301e034080d682c8078506108041002c01c60200842d0113054140c60b01ca82680c1e00e41c42c84084030f2050b40c0076800b03807007800161401580c030003001620203040c80d00542201c1503501c0035801c4441352095411002030318042010060030303020303083c0050100b401206490070980714951040d42c0784c2108141c4030168120070501d01c40018498035007944c0300c02c18200d040c100b81c14034403050010380d10070318006d00a03240000440c40044c040e0419503410800c50701d204c2c1c0b50603038455614102d03800251059048842c40c0d00401c00600d0804240c40c00c0d00c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 96828840 1250 96827590 96827623
    0x30b010c080304050f0105191401030b01180e0d051b01090b060d0309030204050f0708100e150607020307030c18110901030207030521070f02060403021c0905030f0105010611 76
    0x48101d80311414a40d101810840e6a4490500521621042806520710a4245a02085900d449a4100c8041d99031065203032411840b00001400080c04050806056581da01d4401c0c60b4a1604a24100105981858074256100ba6072100d20207a034460002d180444214500c10f0341c82058a16007401e0703a1111500400300d003010400254542040400c0d8611540070307207810303001507681c3d0300410b04440040c2e0b03411209001d00020024101d03000002e258014100c0d001c0800d0351442e0010745210000050291003044001146100065031450191505190000d090700c0400c0d54074070345500d00001a00c28281e2a403501c64140e100c5408611a07004c0c1001c44a1000d882d000c0704400443c025448172908070203000741440241da140301d9107102c0703034030001051031504210300f85408058001e5044080400455000404100000754041002440182108800340c1c0140048100343c40c810002d4015a40520400c07118048100e81500041e048030482d0312041007088007118a651201d601d0035008112 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 96830090 1250 96828840 96828857
    0xa0c080601092901050a02010b0a0e0103020405060a0305030304030804021f021c050901020c090606070b100501080a0b0102030a0e010504090e070f060f050f09010c021002030304020f060301061b0f0828030b01 91
    0x115406000240341e025147e2000241c00100000021010405038125481d1161050014421802c1038445d0303940111003201d10719012071440d41c441c0d40d40e1000401c0101081406004203085480e080d0714000001c01080400b80d509601c180000d58a0300214408040740500d25040320807540140e0071241c103400180d0140221540c43c1d0148100042c0c064003850704100d04000c58008600c0960000d40078120724118139111a140800043c81c0c4000500707060300320703480c000b40c07102c0903038002003200c91480d11420480c081c5040c040c0180c2d038500850344040c0c0c129050041d00c404c00e04004c500d40003a5a090f5440e040b1490700c5120880302484186c01d0b000c040b41d401c00540400911840240c29240f0052405106075440d41c0d0102e424518070303140c0c03100545e1008c0180421841c28041e801c0f00c250b000d480d22411903141480080c44030301101e50005000d08c8880f0224284120b11104d070f100990041400e41d81d4001c1951141c880321072201443c600a02503640f1000304038828040d140302c20780140e40d0440d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 96831340 1250 96830090 96830171
    0xe0a06030911090c1b070e040b041a090c010801080f0601060503090a200301050f040503090f01020c0301020a0c1b0807090e01021303201c0609050a0c08060109 70
    0x285107040d000d4a142100c11190380d80b640c0c85600c40c44c40b9820310045240c845110101510403240c07400c031300003410340152006008400c03042141e80d52203034001400101a450344c0c104003401428100c20185071511000800c031501d000092180201c110030f98520226a0340d84154130385070b01c041d4103141d19941210700100030840c890130207140c0004144059030b6008200d80e94407010210740300030640000b01400c1c0f42818500d030a100e91580183d40c58901200c0c3d01c0d060380c446071a0b21030540403074410302c0964108201648200490b90400700044c0c000c55441c151060080c1c000780c112032088440d00c842500070392000c00e0903440d0b0710403549094010444207051407400c40140642d284018401d6509210003818591004406001140210030140b10b6604285002007500020b1003524002d0b80c2549446401d03d40015030800711681043e00040e000e00240751141c00c04000c690060040c1e25190f41c00300740080c000c00e41038100d034440383c0e00708100350300640c00050054403605188482c05010a081d40d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 96832590 1250 96831340 96831347
    0x51809030702040e24180f070303180308030c2a030d090206070501090b0601020106090b09010510050f0a0504060210140415061e05040f0902100e030106030b0c03070f0e0a06 76
    0x2000e0700c46a02a04e042002c200e0346500d101717202480c0c000c19600c0c0002845215003d400c0303d0398034040100054240b0b07100c0c081c2c0241d03a409140c40010104041d0320003448003203417a02c0055000c1e5501800742550707030a1043c8201c01580108030b4560100b44100c031002c1c0d040b24503802801c064800a0080c5091080e14802503005014500c03059070840000c100c40000981d0a1060079460381c45010808050709000c1c0009017102d0540e04600b03e0309142c0200100140c0c3c800385840d0450f4821074943e40c015080480856081c06081c80652a52070041a04a0210b811002510680318540e00729005009400c1d40f810075070f03460859841440c0209d030081004110840c40d031120742c10310020013003035199a40302060f000380d0003042c441030341481240040c00185070900030760301140c0074070b038040c0710418580d0002100c10b00b11040f140e06000c0341d006940601d440a41100d4011a00088155481e1074601d1754817950f0351044418200056030422041c01c918024040c01c100e800f0043c02c00309600d4103020098 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 96833840 1250 96832590 96832601
    0xe01030c0312140307050c060f060a0306020c0a05030a0c030201050604090c0306020a0c020a0909050c1806010c110901030303050a0e0708060c0a030e061003020907090501020a03050a0302190905180903070204 91
    0x6802c20801c0307800141840803c0000714002c0c001591915034403140c11030040d05280c0081c0011450b90180f0303042c080c0a6442001d0001aa6044040141e0700e600820040d8a0090b01c802d00510701d00000c80d11b59120f980142c860040a80650001e000b640e0307400301003004403004100c0040c070700004a2018001314206501528100c000c81c240803003c00c2c81a000210b101e091a0b0100e5412a1150810300820030103222400e840300c0155039441c42c01342c04030310142c8405002004d040c108880940700609000f440100102c8403000501800e0595031a401c0060203840c0882d034440f041810680801c4000000141080440b1070705000b03014140c84442c800f1845030700c00c60350541015191800e170020090700f4800c00c2c0c05060266603228000f461841400030700a4010400c80c2480107800b0b08001c5640c021580d284020b9140c5002c69450504803020703030080c010611071a001602509405036400d030054050015180125a2030040d19000004110700d50011500030078613800c2823101100605240c1c015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 96835090 1250 96833840 96833873
    0xe04031b2003010917190c020a0504052a0a030605060c06071d03100605150301420c020102010b030f0703020904140d2c0f01180b040308040801060e01030c03 69
    0x200e260591619540c008101c019241e041c240d0b00051038a00b0a000e141b1119401605401d1411245c0c125400140748800c10344612800b803900c0ea40090014550f040c4082004000e210510105882d2042e1540342c0c0d07048900100e001c2071400794003080310701d0000250340c0002401d000505180d80e403618115110701c40c080028100300103010481001b6030b428040f0840700b01482000142041c50b1a080000401c202c45413241c030040304000501864803100068034040382605070454807440c4120700d0a8280d0f506024409842410881a08140d548400960302c0355000340e0080c8281c0c96036500305038841d0282d202d01c06213a4028682000103081528615601a0107030080485070b4150303049050030021000d80f08000075104010545a080d40f501401c1e5a003010000301c0c140c0f100086c00403075030303c403410401e01d410703c004883c030494010710b500c17101005410611111500d8070b60700c0c9410703100c54205000703014140d420b10001040486003540c03c075040f83e4001c60385040d03851458460228202000e0b41e03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 96836340 1250 96835090 96835093
    0x9041104060801090f02030607050339030106020c01080a05010f060c14070308030a1808070809041b050705011103070816020a0203030f07060507020a0302030a0e01180e04031b2003 79
    0x1c0006041c4000c0c4110034525000e007103070360540d458501c105804d01c50003d1200091250500c01d01022442d50f50740c50004500c49150f8904621011031501500050308c514201850700002c00452211b03030200d0030040c04882030b00c07103a00c03e40303c0384440c4082c0e4000b406601000d00b00c03a142003180e24405c41c140a402402420104001e480030403119080407680c1d0416034143c0c01c00001e105119040303104040d6a00646c856405414904d03643c0c000c0345229051002d403510750302281000d0b059541d0343c091248040003c10203001e22a5800c40a4080d400910301650154039289811800400325400c99102e50b1075540d9000165071440c00400c200e016800090b0118850500036600580301000149040003c040b0034503110f40e0585810070558400404200031034021080e610b0000745c0005c1a10f0707002081d414a05085040000122103c10010300100a128001d0340001008888540b11500890007035541354061540100c0d204107080034030600a00c1454410101d4040480041390744801050090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 96837590 1250 96836340 96836351
    0xf01090b030405010b031605310f060819020904030f02030c0f010b13200c0c03100e0d0f080a0203221103100603030e0f0406230f01090509041104 64
    0x10442080d4000b00d50850b0310340e643d0a0b00d00c1d650302d810025114182518005884060b007484080b503104614022551500500c003a24002d000040440711401e801c242c110801254009001042c081c00c2c540c0318407020780c001e4118405115030b001c580041d10740c0d009080d0101c1c0d51119a012a0400078002c4003070114002030000b00d2060509018490780c480e00304001003400340d0314004200c981083d204600140714540b400075091400d180d01c420388548000035415444038403c1c01c0d200c0c144a20392841c60b900d8050091050381c910060380c01903250035030301d00449000e48641c5400351500c60101e01d41c1c1c0d001c6100c50b40000d04100ba25001076a000188240054491000d83e00300030300703032140d003800301c40d0081c034640100764a0508105000347c0c0c08290030b06001851860f180a01442e85200640c1e00402d181075241e00307a41c1340d54108000522101000c01002100040c1c1400895070083e2103e20609810100e181c4542c826441c0034107488000300706100c140c0f1580e8907104040c4003402c0d050f03001515203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 96838840 1250 96837590 96837599
    0x905030912150a1401050604030302060a0e1006060201060f050409020a0306111603021e060610030221010b0414010e01080708091213030309051207150905040f0e0c0f0303090f0109 79
    0x80240e18080d080881020860a0784203074413070800d800580020380144020b2000b000071076800a9465008081440700160000c14111007a060412113400b40c402141080320004130144e05502810845d01c2d50303003d1142c21611350080005998441001a41c01a91602d081c804141d043c0d200422500031311038484d103852400b135003441400c0d01001082e0090f03088032200440d5516402e0342000010310707403070142c006842e04800081141c0100300e07121b0101075010a081507072034402c500e01004400d03000c890701100e61b9140c008040c103620030701681054009400000e8859400f8032105e9094210586845502c0d0307403405011101050000c0c0260b00c14481c0c02d6030304601c0c40143c0300a0124803800705e0b0700e002040c2103082c0a440301d03105034042409001424041401e003c008030303000040e200b0180000000c2000c0d0001140c2d0034880e078100c80c0e4002d01e4149000e00c0180b45c0c1d4040f1500710886820350744020b041c00b0400100c1d010b0640795603013540081214100c68a0200101a000c0205040040ba966100d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 96840090 1250 96838840 96838873
    0x5040209181008010603060608100903090b091210060510030203040201140d02091002010c020106060207032a1a1e07111005041d0430030f230f06040905030912 70
    0x80d5070050744c147d0ba80b20300a108000c5e0a108a1180040a00050000380d42c143d4004062102c103100d450350402c00429a04016600c40e40c071010301c1d481a00480c0c3c90600c91060710360007410f41d4410148207041e0303030780c010003450701a00036a40324680503103d21280f868003a655a505a02c03500405540039820030000b00c9a69981b01303003003100c100c1b59000140680a5040c0039084135615085030081d548030800410000f109028000303050026004c0004866106a80c803281e041c00300d801101103845103901c034040140c4a440500030454001091500088114a1483c3ca511843c0000f07020354010b10201100340c10030b80720b8801121950328120b0318169460781061122115040d00e268216149401e0106108030000605444442c1110b4010340000701c031844410030180013020303402d00d070311010402d8410000b0742c4141030f01c1e40f050b40001441e0b00c1c1c00803010000c134801c4503650035002d03c00000c2145800e15205001c159075101c03000314039164507081000b086240038103100075541300d181c6c40d8000340d403030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 96841340 1250 96840090 96840101
    0x20032205030d0f0e0303090d15140f091605030a20061201091b050a030f180b070207080105150d0813030b0f1513053d0504020918100801 60
    0x1030741d503240f9000c4000340e001083c0841c0460a50722961083c044100d00e950b8400d0281007590f03001040030040504480c8190141015010907822221840200615401c2c10140c0a02c600c41d0750059030f00c6441580e4009111082502603286c0641c000641c401c00075400707980c5200c000d1100c0341001c1e86100d10030000791407544034500c0e142c4204040e1004000305034042c06814800722403002c02002d440c403031003002441c3d401244070303000805071a088400744110141c0e000c04188402d00541080381c80440c144001c00410030368040005100303507040054001d806104450052010464090105144008000d9103154100302030350008010009182c2c009413620b030304002188200c1c2c10581d5450000003c100d01701000f01540c800900402281030165210f80b07502c41c030f0840700b03c1d0004890704c48888009083c0f80c5800b02100a221a0800364509685403072000380c0e0342c0b03444184001503504e8009010503405a40d00c900d0304180e200c070350268150345c000e00040e4420944a000c110b61a601d5801c242981c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 96842590 1250 96841340 96841363
    0x2011a1c060204120312060602150c160803060f0307150311040e07020d0f030b2b020904050115060203041211060f070309090b0f15030601020a0b040b0105012003220503 74
    0x41200301d4071010950406c405007003d900c0a00e04108181c940074010703407114100c401400e01c3d4620180055512014917080e0742c0e100c6441c522000f0009182d140100a56205444540c030810711078860b0b056914000484c40b051b11200d400c41c404c0c4415448040d009401c2d46d40078010200f8082c070000c41c0d416078101d03550f0f2045040303600800d038805422030094001c074100d030440c408060400300b400e41c0d113480305038180100748080441d038618074200030000e04403054400c40003580f00b00f04070284800e10505400240720802d98400b050069039641005903940e01c02d61203842c200ba01404110004a40c00c80c409030843c40020706420310307084443c0c3d20041c440c1c0c40700380704601081c03803907005010f8485a4030035504403120aa42d5043c544036600001103040c2c140b04505800988004001102a4400d0014941d51a80310f031725030503e801c00380f80040c281a4240140c0d0700049428071603440840707840d10b810140394000400717107240c103095511b40440804268003c2c1d00d040301c03104002440e40c9080003101c03c5c50 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 96843840 1250 96842590 96842609
    0x2d031b120b0f071d010e01120c0801050913050a0213140406060905060111100902040209041d0d031104030b040c0506040603021b0d0504051e030105040c08010c02011a1c060204 77
    0x40c9410002c54020800180020b0200548000c0c1101c6182c0461182e9400c12401d00702081c5200d00400101c60048c5a028200c90700e41c1802000b150700c1c0d4001680c141652011600c22841ea40c40f0100d1201c0c01001382c0307001d40258060ba00c400090b06201441145100440e103004c200c80160700000745862805840845516580d100c0800843c41d052060540140e400d2030850070551210f1280da5551544425180d503055441c2d03010000c554940d8111414828050700500070441540c0003102e904803041e00d0681d0b94000c40c400f91041c0d0307102c3d2141c400c10800160703102e1309041c1152a04007003ca030090040702e03801050400440d1a6443c10050802800c41c2c0d503000d65100039960003003550380310110024045c1e5010f080200640c1c0e8216056071b0681e5070985902010304440b8a00850590115034100c0d01546000140070030722550315007880948072503800a110451030f4441c100c0c01c0b50f101010505031a281c3c940055041e241500c0c1c1c544181c00c40c0307007440240b0960703510303034008136401940302d696003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 96845090 1250 96843840 96843863
    0x9030607022407080115020f061303030501090c170a0f050c09011b0302060a020f0d020403060b0109140a06051c150503070e0f010e060303070b0a02042d031b12 70
    0x50410600b09807a40e9031011400522608006401800e500418011803102004412205c6c000c00d208100b03981640c000d54084611900708107020384e19085d842e5100350002820a0004140500d5500481c0c4141c4120b55410821160300e05001101000c05002c101c4500e40b10301004000c44160702030240100c2e200161180e07034501d14130015000601100000b0181c0050a64000c04a40c000c83d8403580682c2c1000f02696401801c1003443e4584228144505964400314010007404503680c0f10070b0b4458400e880c0c044003035031a07080701854040030101d460351044031030301c050002c0d511172406004103186a02c400002c07155403400440946240500c4032182e1030900108200924003000000e0050590620500550500d20351010350300c0030500440c06080c80040c081011518200119916180c118440440d070f410070f50100c41c06503105114403c00036402006c00300d40407502404405941e200060180f401501c0c43c1e03260240c0c2d0040c4038064031202c080742c00005901440f1850070403140e01c9040c00c0001c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 96846340 1250 96845090 96845113
    0x803032e060e0f09040b0a02030a0e060907060908070b07080708091305060f0d200d02122a18060406050301020a020109140303040209040f0516060c060c08190b04020903060702 77
    0x28090b030f110001d124141313290038407000c00d0294140d15000003a030400540d07240e4a9440c0e05000d0441184503020074070070081000349002c408114201590b0b1903903101186c0701d40d912003040e078514940c054000210700070400704000645040003010103620a420440c24483c2c16000201c4c82c00320042c0003000c0300c1c0c80e40c082104602c0c1c00e4400707880d00d0388110740005107010a80c403200e0640c02e0034082900401c00a000e5030300555a142d0380d18842c180d0080110320b8070721317901d140c65848035400308140c541c134095400c40702c43c03880081d489081050f4001d04030048078072802d24804101c1c400904000e400503601c0d800403400340c03828001804850900d800110704401145440d1504100707000d100c0c0800d801c14414000107a44007040e2a070456049140040180c64a040c4541451041e191211208500c1e5500140c03941d000040c1d9030380c050240c00100440110f46000f907803840022034000b240c1141201c081c002c000115804082e500c01c01a000506280841011a03d000d0342602c040c0c3c00b6a2180040c2c98 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 96847590 1250 96846340 96846349
    0x10b010215071211040b0c07030605090304031a10030507060e2707050a0e060d05150406030308010501110c0d06142d070c0b0f060a0801060803032e060e 67
    0x101d26103580e000c1c01403500550040441c00e031040300701501030300d6002142c00740306640140c5000d8541c1c8002030b5a214442c60030b159944803030b03200441d107a5041100003a8401d6010040e14120307138120994855508200c80105a1424000c1200c0142c039885507020012440070030800d0003030081511050000c0601c0c50402136541880f481900352105444103c040c9250b55042c003e8120555003000b17a101c400c140c005030345680d0010380990308801d003c18502c2c0881d540c3c0d0403031030041110305845000900d000d1f082c80f00350380e264000070b40403411003401040345500c22202d407541c0301c010509540700d1a10380b0340081e04406a00e1402d507440703134480b101e1031890400041010707003007040c0d00d02c2481c1c0c80c40c4244d905211021202520255040b01c01c0004011310300134000d1309900c40d070042d501081e0f031500400c1540c2090003034980900683e4840404a80c05105100790030546503842c00550655862943c4c40c29042c500343c4552150015110b1000c0c0244078008072980034020680b2282d5881c8010300902 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 96848840 1250 96847590 96847603
    0x51504031d0a1d04020a1e0608070323060102030f04090c0f02030a020d050703030f050a060e070c02030717120d0b1c03270503030a02030325050f1305040e010b0102 72
    0x4a100d003400300c104100440a81c030280f00d0803944080035209a40c1c0e5800064004482075100d540c04801110100b2140e003005000d0713805480c419140c84610b6150303407104404561640741c00e0b41441d204c4004180340000e08101c40c903403210341481143e240250340030404bc0c1b070703810a9110150351902c40c0760035007010350440511b1003000074510007581050740004000790368114a01c024401e100c000104401490300c660084031000c14a12014815820010900741c02040c0c1441480d00900b8200041034040d442401091640c9800030010485c4d281400000709907240540c40d0350a062190380c00240740c82c2c8201c000b40c0f101101d40c070000142ea01104c810306c02c0848880c000341b50441e2000d024680003e4110038010707074851003044e902c621401002000c84594200307400c0954940310115015440590000c000d5100d40400c41e00400501984010b82c004e04c42c0503ca028041b980900c8414403e00c00d2802034101d0342000d414003800c40d990b41001c07a089455400c0b05240300c0c0d44a001840c069601005003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 96850090 1250 96848840 96848897
    0x212010f0e150906040b0604020f1204060609050903040608091c110607031b0f210b04110f0901050a0e0a06110615010905011d03030d020403021203090d0303020705150403 75
    0x748810383c035166488035124071000704000e180340e400402290603512a5410380f2900d030460500f2581d18100314881c04030787c46044501b01c4202d8180035011a488207140507240c0910007040c02581801d09080080d1170020340149503640c18440e10b40e0400031b80d48250003007841100e090b00c403004e2980710784451a00307088004005505050902c03010846420304200c200e008400c3d0303490042c8000304012001c8541c1020080b8034070a1102c00754442c918440c0541c014900b105080307070100140f10b40b1100050f968060f4101710b61f0008001c0c003030903055502a4006064010703840c0390000d0f401211800145403441150807020003c7c00040307940203100c0341003041c0754114000c80b409070030414601000a207110303a58020207041145456805460383c0c80601c000d054a00001c0a603519030958000c0e580081d0071a00c0283d2003040e06031260107203140040120780e5903003000341c402e02100902d0388041c1e0103035201b0141291588142003035003003051540040b01d40654820780c0c0c0d112810341c0307050040e00c241c400361a8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 96851340 1250 96850090 96850123
    0x2031303060501080d0c030f030506060702030106080f1605090a09080f04060314060609031b0301020d0608010b0319030903020114251506080604150b0607050d080f061c0212010f0e 79
    0x5225000c660000031190760380c100c909d0b003c80c0d55607a40740440d0340d40c0a51a230094040d0700780170f404100303031401203000c0d02c07480918000c884401100001044110305144030781c80e08070702400c0107d0354404c82c6030413894001e4041c09820f8688200c610b0f200d540d950184c0d01241c0000d41e10402c039015034203003138100707600300504980043c14544030400003611455140500419014200c5482856440c05e4050b900002162030041040c683e882048a028100c441240c91007401130106401d01010aa4602044240c050b42c03000452802c0d40d00640d1038403106640464500c506002504505501c000e0048000d00500368694503111245400150b480d680205159480d0620a0038015a0000075210380e000d90403020412170030030010a10001080500c42154109130002946810b000b00022000c2c1c1c1500c0c2c40d641d01110750f80e40c89007011892801d65040d50b001910000c128014204203070401c198031b000800680300c0c2c04001c03211908685084010b140115103501c004c01000743c0c00d03c0000b482c1d042410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 96852590 1250 96851340 96851357
    0xa0b0c07021809011107060e1203011d070309150b040e010b01050703031e1b080906011401030b0109050402041706010503030a08130f020306040b1f030c06030c02031303060501080d 79
    0x1d0000d000c081c411a000c110b2003404400080b4000001d40000c812081c9070345001c6e61341e002030b040c00009000840807002d03140c0b04801c908103404284004990488507040c1d40550301d18082503a4030aa03503c0030700101c04144c4c450100d80c010803106860800c5041750038000058103000740060009035880d034104013819924291806c01541d030003100b101c1c00035925150010325074050303c00150000141d010030f030103298070b460300300c072041116845145114951511a0441961120b030820b1355002c090140220003015205880102d5000340c2000403450414107000e400c09480300089001c0742c0050b4807008884a0b4400040f840c2c0b981404480e015140a5005c1d41c44c0c101c45080c0640380c14400307001d13000300d0803008012105020040c0c5036031095035401405e0b1115800c01c0d090104840c002540c908914440c20365003810140c0201c0100c8080326404a1703030302d040f140f40940c244e0080400e80001020f50000304400042e403c1c003c15918082c61203054001403550601c0c040d1032400c40c0c1c14000700248900302 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 96853840 1250 96852590 96852593
    0x81b060a110906091c05030c100b0a0b0a051b10140f060d0c030c0806041e0201020c19120c0f0621150b120f0705120f06041107050a0b0c07 61
    0x20000c540b02090160b504076034480c40f0001154140d505608810f110107000e004820410501000810b848130601c0200d030001c83d6108180030445030300c1d42005038000c031121010081a030303401028241011080c14060705000d8604003128003c80d00301c03908100c90300000b00e5030301c44035140d102c0e60460b164020b0341c0307141515014148000400e8082d102c14401c440a060000c02c10803901c400a010390391212040100c00e0b650401c1c2c694400b8190380444201c0781d084e40c1d1008a050b1180c0009109405034014152000c0050520010303003c0042d104d101e0340381c04000811151074407080048041e11030f064403d10540390090003660b01010390052404c20648040e40c0066a4260840b0300500403242da001501050060b060040d4081c99400340c0c10107900440e4150310b56036100c00152154901d0010220b103941c031080d0071601440340102d181000002d81e00442d40c5481400107283c1d21072006400011000c003400c10410064000c0e50003103666500c05801c040030810824405d603000742c010140c20342003d145 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 96855090 1250 96853840 96853871
    0xb011e020c0a09111b0703020d0803070e0907120504150c090815010602100b040b041404060509010c02030706051305030415090603090c030f0303090213060509010509060108130c03081b060a 83
    0xa02da055003298417085c0c1a40710101041c000c00c0300940c5d0080101810401d0380c42d0140c05070f0030481c0d02c00041403410041980600b40843c8480c03040c141640e810100314031444100c0001c0101401c2900c10340704c12a100e407190552486041440021038484000f2180b502809910b0500c0d9800e514509451405c010040315400203080014842e07404c1021034842e801c640482d000740042c8a45588c4941480300500c50100a04a0b480c003440c0030b0001448240c2c1c800b00010700340c2e0300440d400300059004020b95004100c130340c1d20150700510a40701c2c000ba031401a444191035900b05410074668440c01d4041d0828054001d200100204a0b505003444507160355280c4240e0400a0710014201c00d1000313580c0d0041501c290b11915984d54002c006c0b04040010342640c600408840c040c00b4040c0f11a40004078403490121410340c82500160745004150340e17480ca141001020f4408100e640c46501c82012001480d40005040344004441141240c400c001c43c0207881d220000c0c000070311313540c40c183c017401c18501d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 96856340 1250 96855090 96855097
    0x30a0525031b05011b030902010318080414060d0c02010b0109090501050901060c05010209090a1a1c020d14060a09061d0703110604120f020f011806030b011e020c0a0911 74
    0x3980701c111100a003490030300b240500170031000228800340c20708032641c5480c0c0540c000e4507141d001b0b903420816205550182021110788030b20103440c1d01c0c001e0004228060070a480c2d400e010b58081c5c805420401c1c8030000c1e4059070011040745016075106c010250301564880000340040400d0704007800194540008100208018010b8401b04007501d11203206010094046541c51f1801a00d03031106403078a8006680180f10b0583d00004800500901860034130b013500100d0790b1661011003602540d001da03401c00405690106045a000b02d030100080034200381801402c2c8030765003c0c000881c1e030b644246040c00441d0380c900c2043c041a032440c01c94030141e4200050050039a81d110103031440404031640014610f0040d0341c0f0031044034501300c114000b00814000070500c11442550011008103d030401590101d60b500055001f00f1080c0d10204185803003074000d0b41281d20f041c18541c065480c2c4045c081c100c07400180c00b03840075030b1180c069400ca6051800603c00201000d9508112201e07891601c0c5601c1d20 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 96857590 1250 96856340 96856367
    0x10906051c080f0a050408060405060108010e01060b0414040902090112060501120305031603110a0c0c090c1202071a09030a020d0e03030702041d030c07091506121508030a052503 78
    0x34408510800312500550441b8003804002c4200c490f1841d1900c0d00c5a9a11800d01801c48030707500744100c250320a0360501401094031b800301d40503401c0906208074031394485015141c2c3d40c0d005460308103c00158940905143c080e00c001002c006003c01181020740544d41c040e4440858210800450008258001c003a40c1d0803030401c00542108842000c002c802501c01d00e03001c6045840000746030314075190020745009109218200c810051a9106050422900d142d01034801040c4001c10030600000c143d401406c071180310b40013407003511440811714002a54100c4969036a0ba20014000350042e40400400158000e0761034030300c800003100c00c0401c2d168040c2d000c0003800381d40c8035a00104a10600d0818070414001101120788407610200401d589a60b00d204481e1007925145081c1c2c01d070300120b82403509407079180e00c0344014003100960b1400101000120034107000000d03080401d03032030700500080c00c80e542036644003074982e1001a4100040304103000620f20140c081000b103130001c1d4200302c5051059 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 96858840 1250 96857590 96857617
    0x10e010f080604021509031501060201022203020a030b190606030207110406060e1905090f010320030303010303120b10020607031802130b031c020105100914060f01020f0303010906051c08 82
    0x83c101c21b40840d01d01a4001c500c6200085110300124507154158058580c1040b00c140c030507140300903451842405046404003a40107081c42505001042100d603803a904107880d0340d6626801584503e51004507507194010f6000682c0000781c0c82d00780551100c00360741c01041140c01f04071003450302d00f0203040600c00030350031400356010003280c035800f1003030351820b42c01460090803001080c54905030b0780c03000c9007007404101c6116070301c0004264140451000da0000d050050000c61450342161015152403684410b18030b0754507210003100c185c90301e50070070360440038403590001c0c03105040080c8080c064031448849141000c55642000015907035800c40c006118501c80400111624200c012a0800c01405045040c42d0031640031402071b03d9055015900c204400e210402100d51038941c0318056405180401c030403008181c01003109454490810340c1c0302070050040f542c0a0840d44125030840e0401d0f445200d4056649400b0010790500f00818803400d864482840000e41c16541d80410901565a003010309 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 96860090 1250 96858840 96858847
    0xd0606020c0a1a090303040e090f0f19020f060a08040605130f02060d0204050a080a020103050a0b0d030e010905190503010507030903140d020d050f070e012606040212010e010f0806040215 82
    0x308007004007284c030101000780c00da0780e80d19101d21058482003415035050343c2510460008880c10030001c104402c040754030f0030241101483d034000c00ca5264141c0c800607070b41f01180f54801c8015640b0f1800901d00d2800c145c4550765030740750030b04001c81290b20040955040520500400000a11a040100300c85074100c0380240c5403015600894000c1c0507641213990000105e000c04196480002060406240700740c0e000d110703aa6031049800141d96010341c600703801c48080403d400021f0f025010220383d0000614088407200d81d54030014111070081c042801805c0c282d03072824041d0b41428000d4903481102030600f48110041640c008022602501c0200107140d0b003c64640500d400d603404480032040c08550074445d9080c0b88800a024220a5905501203204003405c0708965002d01e607921900032241141c0c0c5076008039212018a101d200902c0550300503800c00100003a0b03544003d0040c0a01225202480c5640c101300145825030305a40000c2c0302a4401405c0100681c1d4201080c607000c0a0b06032090303207 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 96861340 1250 96860090 96860129
    0x201050f18030714340b0a0504090b01020a02040c030b01032007080a0201060305030a08070806010801080316150203010608041403030912070510060b030a0b0904050604060b03030c0604080d0606020c0a 88
    0x706107406000d00d0003283c80c94004000410310351445c000105554401c10000340e81c4070f0400e0818070031112050b0102e42d040c001000300c6a0240c0c024012014180155500c034001303580081e04852102c05101c0c08255915a000da49507894802c8207030b4000042c0007000450600907691505010b0240010082c7c0340000320b058000e40700707400c030708002d560200c200d035255110400040c1ca0b0784022618000060141c400007107056228441d020f0403102540060341c80c01080912605010074141015241250490850b84072880030744000c50007090603598034001e90800381b40203600b07060905143e207002e510074020b01c0200000410441c2d210107003c0c1807540d46036820302d01642844000780032006054071f030410006030007101c1001548074080e13400d03040209c0c40428040000090066030050055480400042e00017a4998802c181003400101100c7c1000000c2103024a0641e088504446801c8003041601d0718200e98041d500192041740080c0c40c1486c011400301e20164414400d9074400d2035034050201 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 96862590 1250 96861340 96861343
    0x30a0f02030f060702030a030c0516120c0b04110301110f03061908030c0c0907020a08070f030c0b070e040b060c0606131b020f0c040605030a03080603030d05070201050f18030714 78
    0x61494001d40140c40140c0b80029011b07440781c001d0b01050011a05001c00000c20500c511704039807509206001400403510f107038850660340135103964102d09019403803541e24049102c40d800940301e503106450300980c0065180c141400e540c1c40a0703c01850300018030000403884540e00075a58041070648100c00000303101e9104403540c90f11544100071034000050314420048002c03800001c03c55081e00c1d921003d0304d40640c01c0741e5803000c000c006803260006110ba00001a8101c40c0c0301c100600074508420280441e464918140c842980e403203012070000d0100b11564241030003000307002d0900711010b50512200400b6680c6500d030040446114580c6201c9092204119500480c0e4070000130f50b588010000b00b00c80650303513002d482900200362080c001e000083d8a401e003c0c0e1001e4400140207040141d80550701542e10900c06024968180018030583e0410f14144c4155407103620540d00204d201c4c100814030300030320480a40700d400c240410760a080e42100000049480315540900015000454002c610303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 96863840 1250 96862590 96862603
    0x9011e0201060512151f03080d0609060e011503020f0313141605010801090e0c01050a02010e0118020f09060901140a0509010611060108060f01050f040e0a0c0f09020405030a0f0203 79
    0x150f480300d11542c03400240540002d48460341002c100340c81e0301689036400800031b180041252810700e40851801840000d1051019041176009030002280b203984529074441034070220742082d4514451000100080b0a02201c3c42800201d00d0800b103150484031080d0748642d11005000740c00b11085003041070100308420102c403038140400410380305c6210b403034070149800300714038420f490005c3c3c9440b00104003519541b00e107800710f807510780003082d4130041c1c2c1005440a03000000458150b56850b0b203143c03a00c19080c00f0b0503401010b1180e9001082c089071040004080c1c00000350790140030300d007042052603143c100402c2c2c1966440103a1007048518400011000d1a0755048a90801901c0d000020780c1707070b04152007003030b180e103281d040c0d80d416038950210300c1d07494004580c0c660070101680300401090070020722445005c031000c0c00201d400403008542c0d51620032229011500008810000c00c044c04904000d9009005020380640c5000d18000019a8030a24078002a10103180c5906040865a042082 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 96865090 1250 96863840 96863849
    0x901090303030b18090309011106131209030b150406060c020307140a0906030c0503150f0103020907110102220f0e06090c040e16020c04060303170709090213140609011e020106 77
    0x81c60040c50030175401c0341ca0b6040b064426011442c441070815448a011410070b10500d500c0f0080c3c844d20362291144071070064510510414000860000300226441014141c814141001c1071001c6180ca501400101d80403940000104440554004016907011070b85a0441d0301c00c1d444810940060400596032465544c416040c9c140390130400010800781c0c50040341221402c5080d212402c40006076441861811540e000d08103004800500040c603202c0e10040e00a000c0c3e1410040b00c00448020a0884c0d01408a0070810312848841c00c0c000340c0c1e424101e001404010356620304d641e1612041d0715601c0b40c0604828880c4160500003a802c407803000a03500100300a40030701c440d80c20f000b080c2c07030716001c00381005a005010b00c1d01141c0103418640a20000c407541a03031041c450302d038110800720011801412900c2000580100002d01c0220390000d4591080b10341410181c0900e445003100720341e40c0e429a8103006902c01d020481c0b090385c010515a64000c0203124618001000c0342007203006142c0d5810 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 96866340 1250 96865090 96865129
    0x1c03030e0705190302090705130e0c130e090c030d0e091905070807030501080a0816050a02040c02030c010501090e0a022707080103110a0b1602040605130905060c0901090303030b 78
    0x11850490f565011540381164002e6a5400035600d68680484042c070400180010013001c20908001049880f4817080c3d01000302d402081c02c0412a1014170501c3d1401d50100c0d00c0d1404403c24081044814001a00c0c00c107001c8000b00030b9180c400d00c002e058101180413081c820502c03100003840756820f180700c0c58141855207d00300b003240b60440d030180c02070a0588107080000d10303240c000300d81d84800281c04088643c0084229081502143e28001c440580240441b024061411030b80c0040c1c45500500f20170941035009580c813800095641c2c3d003113600584c48512034900b410300b8000001e5001c01c00049990301511004070400b00e00000c590044840e4072001c6034426203400b000a590350000c8c06906a80c0f040c403012066404802c03c20a200e14580100c042600342004000940c002d403202c00c50045201520124445980e0f0300061180030703151203034012250726403140c4002c0100030310407591300240f0280d429081800000008015803043d000041c1410f50740e1180c1c40941da00e02c00007000b074010504 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 96867590 1250 96866340 96866359
    0x100504050603040503190c03051c02070c0803030610030b150c07180c14090f040f1e05090d14070807080f03040c0602010b01032f090603040501060e061c03030e0705 72
    0x3604c10b9499001202884104a242900711a40c074803801d005800690143d444c2c508091046480d80110320201c550b00140075400c000b203c0001d055401210000c0003044080c58407482c0040510601312201b00f914400c040c500314100640f80e03510500040c298078280d072072944a01d1305006035450031a581c1c00c1041d10000d20541c450314810079811154607101c4a83d00c0702d608071140c03000b0f0141070065035004c561240021041c0102070419900074148408000740104070459108200406004102e0041511545450800071492402c11078013000c4a05803034221100403c108210600e8080d44600811a1000040c00c005012554080c1c82c07900c19400407240d90f900b058941038908040510034140503500304401641250b0003485070606012444a280041030488003940301c46854607004403803500021310101c185a2a86005144940c0c0304a000180c0103042c9512101039280c01400c0b1441403902182a889a070030b04500040c030b01da454100480d08600c1203482a0900760b0507000641c000d10281c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 96868840 1250 96867590 96867593
    0x40b090406060501021905060a050c0d240f12110103021e031b030105010207050609040f06180501240f091716140303040b0a0512010909050d0206041110050405060304 73
    0x42e4400e10481d80243c084855004000c268600004007401020b41240c000d0000660384802c0b076007019070300c00e41840406203016840e00f05102110703070310032014215104002c080703003480854030103d00141150a540036074070791070460081cbc041c1d10600350003801031014900081281e4001e405503541d0110152240c20200c0040d0101100707504200d440402c500c50504902d000c03088500200c9040c2c070381c1170b07010305515800c04040c03040300e511640949400c00c0d1344080402001700d2602c01d80c0060155401008000c000c2a00d20006548043e003100900d903902e00300e41750310aa403900c0301007001c1d90703a030408110b01c252004040c2c030088030326070080e050440c1c2800e80341c40020000c50810850000d08203003c1e100380d166000c2c4806c0201003a20a078155108000a0001c212924080c0c81244003038544589050401040f09200b03c000380e0011140b50f86400003031080020038821000c0c9110f0a10041ca920314045e1945c0b03203015486002c0302e0141076030710820484a84940100c8010b03050142c4800d42e40e0615 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 96870090 1250 96868840 96868853
    0x4210c14010e09160c0c0f060509150c03040320040504050309040e060412050309030c0f07030212030307080a2c0a050115081b0a0305010e21040b070f02040b0904 71
    0x20300c0340305800916140c240c81c02a00d480496580908000380004466400101055480f8143c901040d030f0401c4140c4c10000b0501413030700c400710241131a07540390346d140d4400302c00b485041d00c034032040809400360030301401c1d1549178000203642c1104d0304000381c1c482c403452440300c0c50480c4800610342d0780c1040c2084200010f002000001f0001e80c1c000b80c40c00c2001c4e40002401c5903d03981c00b503800822140a100400006c64031400146400c40e041005036460004111211490142c0c49509202d10b03401c01e0700304006500e0040510004503c3d00c401452451070181e0000b0000c41005268008181d031340c0e02043c102c004d640040690b07200700041ca40c06401c08260815540b80c070240e40c00c88056017080320035009a202402c4e4401114401802450740603070181d9980f00c03e81104800b6600800385280c00404a0000d000b5a5a5051044007903c000196001c1c10100c600d002c031140484000100700c1007241c61000700440300354540090314810f610450784006400b401484e05442c0e80083c4103400e10050201 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 96871340 1250 96870090 96870119
    0x706020c010603031404030c1a040f0303020604030207090c0e040e0f0102070602030114040606020604061a0604091a040221040f02091006030e011103010909210906030605030309030304210c 83
    0x641c65140d4680005e50741d1803028425800001d02e40350b888401000500c07036140a51400c1e804015402c0d003007607103074085e07001c00c1c5030140d006500690020003800103054051008801400391000148410f07071038000d000d0030058190380028000d40e5a002e00080004082c0180c0d402115504005d40d600ca40a04010004e5042030281c2819101c0c0d4680307482c0c0518051040030211000c5401406442e80c9549a400040040d4000c0c001d0740c5103403101c4580190765040050018051008000401c00a11400001001101c103442805076104000c0d910182c0c0304100010300d000151800810103641d03910386803086a441c41c80081d040b0b0680000d00c040b00361240c004800752800c2c1d590412003410600315907400e0340c001d03006070101c1c851300b00018030020320142c220f5011107026003e421400c1100024203410f00c0140368507030000500c031407010300840342c0c1405608002d00d000c80055051100e1080007940b684681d22954a0804812140040010036005154035161f0011142141d0380c0d59070003a011940c2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 96872590 1250 96871340 96871343
    0xa03050616030b1e0618060406031a0406081e011107030c0b0702060c0d050c071205040812030402100302130801060608100605070f11041413020108010f031e0204020706020c010603 79
    0xd041094403c81428803928554158000180007040c2c1103ea400b402419402a003006040c052070803d20440c0b503c030706009200614140d50f000030a002c003c2d501640030f030005108140314909113101002010350010780c80350028075241c1c00046166140c500c281c014084c02c80e200b480d50342c0c003017004001d05070030051046000f401680d48001658403c0e000300c0c1c030f0340400c43d0040c061490030701c40c01e42a900180d00055001180a07082d070318240b1070383c03225880040410381c02000600300060900000340b040c40003400041c08038055a00303500f4951b0000d1700d00e1700110300c0c480405501081e01e400103503001410130018060103008000c020340300c0c40300400d640d20484402ea6204400c0c2c000082c0c00b842541100c51303251b00100102d24642242c3c1c1c0b21788483c8403955074254095210019041602c1c0e003098128010030074051900e1014400b0700c0050254001680096501c602000c01007000c0b0f103412034049007442035022107480c55803452000034000d0064007006000039102141406000d10154801c2c8140ca = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 96873840 1250 96872590 96872597
    0x2070b19110c060103110607021e030706020a0812090703020604030b010e0c030402030a060e070f0b120112030801030b22060f0b030d05040b09040608031903150f0b03060a03050616 79
    0x241010420315a80b141c00101140b03584104010800b0444180b2259058400145500c1c0307461050740008448107040060100d0b40542105104650b241c10000ea0b0f004004a002400c4050003079100c507017180c041c40c00f6194140721303c1c50019400e490288000b1000d594010001038440d5100e00788035051100902404001c2c08510300421105020801502c0c8195030042c02803003004060f58035000500301c0a070822180c1d06c5035610102e01007100000080c0642101600e068072002001c00403560202c0684c4034180c10040100c3c14004a98070444850560b90030403461449600c400a84400c0380c43c1060301140d100042c3e03507030941002003541115040708080d14052086d070440700c00b0581c40c0e080c40c80d191030114000b000b080040f2071440700a001c6404005000003296035641c0710b01819a0700078031401c0788241031050100800e5416105a103c0354508040c7c1c1d40d07020781010005c039041d003101e00074440c1c00c60b400300000342c141e0b8800180001660740203042c1d81135414071b15461080140e07820031140c0030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 96875090 1250 96873840 96873851
    0x6130e0d08060d0b0a02071401050c0705120403080f03041401090305040509181e0c03010207060506130915020d1506210504050c1210020c0307020103051e0604020a020102070b19 78
    0x300d240c107040c005280e513006101282c1c01d851301d03039510703009601c481c07800c803003428041c0c0d11145584002c0c842c061040044111056031070807030b4038205040400145e0b5411400000380018800b140d5a03070181c40c082c0d5501e0480035a03e440c0d5090203404124440c1c0c85481c15828880401e003095400000380046039810f8864590640341c106c0b40c02104115082c0061840c1e014880d01025088110f0b4210149a035580c07d4070101c0814034007103400c2e40e0155206036002d54a8100f0703c055420301141d0720030405403141d82003044454981d6100c5102c4c454040859076941c010800040b42c003821703030124001e804c01000b089240795071820017511b2015000758001054119020340d440c501d10a004007446554040c0182c2082c514010820000c00320b20900c9070300320721840c0184008040144014841080c601d001581c8550752880010300b03035200100b1450400035420303c241004514165400c1d00200215005601c40e070300c8500403402801485009800e441600041c40481031503030300070180c99001c6250501a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 96876340 1250 96875090 96875101
    0xe0a200403060f050601023c1005010303110607090605090a05090405060a1b200f0a0b01050a05010f0507111311030603150103031b06020f0c010c120b01020d0806130e0d08 75
    0x2220310010100c004410741c0515480d100099400c1c2c901d4024410459a0001d0908c0c008401e103400290755522111543d140c005100b4150091005002503240400610461804410081030001148920300501502040d5402c20756100304050003e40030180441c07500b45402c0c104140e5503c01a508208404d180601552002c0001010700b03455146540703901c000301d540701840c0d0703000003808010320b15540501c00141116850034000c03100e6440c0210300c080031550503e010418020401e0b0301041c1403200b883c00490000c1c1d0007000340c0d100c054003c0c13541d40c844100800800c45040980c0c0c000100c0c070703152100200000100c074018600562041e82154031160848040810f01c032000e01014001c16681d0090103024034207041002440c40c0b080300c0250420500c1402c0007242e810030746081c281c59449801d0200718940c040310903080003403400014000d8045410010b174440400170030400c104050713000050b00340d450340e288150400c6142c80c400c01c840044003d0003a107401c0c07149202c5000036001e402080c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 96877590 1250 96876340 96876343
    0x605010513050906150a020d020d02061303030b010207030c06030e15060d150b0409030e031011180102011b05070b010b032203180b040612060e0a200403060f05060102 73
    0x50003148070a4004880a040c082044407210005040c2d82d440b5001c2d40e00d40d60a0300c9400017a001020301034004082c001c10846000e410246010121801c550141003003109030b50303c0e0b1842c1c280d03003600750500140300948000102c0c01c1c48840d400103041e1411010000603050b41c90360200307449400803415556a1100740c030404d4403402003910395a0388410b0f618504400b203914400c00005003c6182030000c0d41d80c1c1d4038800324098900700e80d0280c010460b0049600810b0409004005211081d00000c1002d0100503010a41e035005182d070980c110340080d50a020141d000350b100781090180e9003070098041a060a004001358041503045070100105d000014840019a00b17481c0600440d044e20440907000c0c0c046614604e240100c243e04100641100304c801c00168131001c0c1c0a40300c440800c594440c1003131030103004040c840400000070751400904101001e0103c00c0c0319049a40640301003020113000304a00a221410300c001d41c4030800004001003040003a070300c044e02c2c0509240041c0082c0e900e640c01613 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 96878840 1250 96877590 96877597
    0x601080f12041e0f0b070606050103051e07050c1204060320090d0606030b0f01030605060d020f0607020103091e03030b040b01020a0201030b060d0f05040b0a05071b06060902031906050105 82
    0x941c074004148402e000143c14190881440c03054844091040c84ea0386071144600c02c450742c041d504039040000c0144c01d018250042c0ea020303100070700342407010381070500f1441601c0c1c140313000c2c40a1152405000c40c000341e1144089a03400703902039080700c0d50f4030340768400d407041135029104210201e032030091504d204046041100441c1d504446403981040866024000c41380d0300d100088524550790704010000500b012003240c040d09030108483e00660661070721104441c005013030b09110303d5200c40340c0c800603590102d25006801c01560340ca9140c00080c030059002d070500c042e0090140e100070291030240de2840100080c100d0184e9805c1c4001d064403810f01084401c02200c860042c0c001503507000144d402030b040854580e202a10052600743c0c01010401168440d8400858258a079000e00c400d01001141d05900450901c070204810f0412078009040141c40c403001400c41d0704005014400c4c000c040d4040001010340c0300c4203554900d0440880c0440600b40002e2611151030054080343c5544103000380c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 96880090 1250 96878840 96878863
    0xf04022b031101051f060813020d05030705060a05090703060e150108150c0a050301051e06040902220803040302120f120301082a0402070203160306090c060e060313060e070303020601080f 82
    0x7145c02141002c1040300c038814000d1842204240d80c040220050300c800304070583c017900400c060354841c102803401d01d0030104040c1149040504200238840c0c1c121002c100141100e0b402800081c45401c48080141480c009034030001d0400700d200d0000a81d8100810540a4000f0002002c00b80d942c036200f16440354044c4212003000a442840103101506000122440309064400c4400148542c4000502180c2c403e4004480d44d0b500450020907138000d5208042524144299503282c1d00d0402c2d0901e5070300d00852001a118201e821441a0590b10901c591a00031003880c0941d050b1340c000003003892240c1d00030700c1007180a01c03644481100403094020986d06012404002c4030001320701070104000b941245506983c180622091a00c915a044070180020b5200e0000451201076904040036000302c0c540c858001e000b9911034200595603044116070740451100080990b10056081280c010000340019480361700c00c200010051640028646049590150450f480d40310068051a02c8e001807800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 96881340 1250 96880090 96880141
    0x60a140301091b050a05070b060607021203040906060207050d060903090306050c0a110303090d0e2116050904080304030516050d180609030f060f0b130606030c080f04022b03110105 79
    0x21f48800166007502c0d040e0048401000942808903a0700007817480c242820415001d9440014100084180c0d0b0003040018051800640301c2c41d49403001003503404000190040c0403603528401d200c200b40c0a203907504080c540052041040d07240c000560b0f80c4981c0404804000b04a0300c044800c2045400801c0b01e01c10f04c04070b0050301c1444e0700c00b2026100a0100d181080c1d00881c0b0009004115400346150080b03d4109402041998401040244440450340090340070341e500344100400300d1850022290400c3c2d01d4505980d40740300700800c08044030001c2c4e000030842d00132070101c0040c6c6640f10202001040c2c01c22103280d02c00e956407400340c4503403115200c020100c14003010100080f980f0396000708154407140102080309005540001c1e4030700146a9200c00340c030342c0c40d00140842c5e6031500c0b840c1c05035171950030006d6450a04805540e01c802c0300030002403040d011100c0d940319850746017034404591080401564615030061a005d001050402944000c56203004009003128200c0030020400325020754 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 96882590 1250 96881340 96881347
    0x611090d03030908210118050702070b0d060f0801020307090b040503070b030a0608010e0d030606020c01212405040e030a050a110703020303030f0109050703060f05060a140301091b050a05 82
    0x29415005002043c10a60b03180400780203411102068003801c41c4546498242c140d4290f04003412407103500300ca81450ba0307405142c1000c01007550380029400d01603030b10500c111a01c07070f50308041d0703007000e40550380040c2d841e0140c40310005003038081500518083da0554030348000c46515800100d40ca8010303485a1685a88a013408210011040009640040b41d4140101d80162260041030a440000d2041001980840c056020f413035850301c1031101908452001e0300040054000007800501c04003401c0c81005411004405207000790742c00340072203107000c10304140c0e64004e0b000644950540c510405003d40e0a0141e0100c00e0385001c4106c0e040c0101a484150502000403411281c0303004003000d0803051b208410011001d0b07501007001d50300c00c101c0c05100403450b6040c01c00f107505588000d0258001d1600b40801030100d00800d130003901c00c0c0c0d4001d0750302c192101400c1404844208000280ccc11000038008008a070f948419001b135540d241d5100c10380303100703601400002c562910820700410005102071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 96883840 1250 96882590 96882593
    0x30313090b0d11060f12090703021f140a0c05070b04060909021c0506060c011e0f09030f05030901020405090c0703080108190209070c0b070309020a06020a080d0b060c190611090d 78
    0x40103003041d5140c82c00300c46c1c20900b0410482c1c59002040d21f14071815031140e40e0030021407800c0e120f01195403078041400341c4000e0032032801415003c4a034009040300304c00800c102d4001031103055000300c0b00b9041002c480104ea80e41740030200740c0e4010b0095000184001e50042040d6820313000300c40398401154620302c00b00982c0c0c0c0900d0000c0401500469122104200d01c40724580240280c00f00c00d9207a00c0c0c456050245011a40c0032500581628103081e0b0904407002c0100f60040d9449402124604041e5520ba65044545009104a4002ca03911981080c144a50605c9070805000301d50301c651100803681e600c1c0e40301035948201080854001e246002038075030040c00c001000c01c3d00540d030b50504c082a06070969401e0b02c540710482d00c84000995518920003585400803451004002c54000340c1510411900e0b0311520f4806c014081d40d030161a20b50110b40c60700c484c81241c502c0313030000003941e00e00e84003c040f41c11048100d2806030f0304542400240b0308640840340489401800003005240c01c0c8249 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 96885090 1250 96883840 96883849
    0x1b040902070201050705030d06141e0f27010305060a14010605280e1503090318031c090e0c0306011d0a0506031e01090b012309030313090b0d11 63
    0x207058203d0400105009a1000a5041005d05a4020500c0010485504140c503034604661680c880500c108031810f080c1c9040d54234107141c00240d440540c0e1800000c0601d8001c507001958940d4800138056030a1a41041e04e103000200e541605c0c851000d032041d039118040404242c0e440101d154003044903031001008214003500050034003413144200c100144030162000f00000001005c01004981c0361128020549003005050138420b401001041c11403c080c0e8450f941c900a10840c0c3c0340010510500e1020340d0340c10400340c0346120000040d02d5040c04903200040404a40d4814041d8020380480496180d45142056a200704010b03951000401d2155000541442c0c0b12042aa000403600c1804a070985406000390300c2541e014206180705000303019007049080c0140e00c40340015180c40103412140c0ea0040a0104000b000401807003e0000b4220700101440b69031200c640c1480005000c00704500c051540804a406a040820075003c8040c180600613024400080070551468600251341c0b40c03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 96886340 1250 96885090 96885097
    0x601050a140307080603011d03030a09060608060108030a0801090c0f0503070e0d06150602011a06070c09090f1101050a14031003080418110408060c09041812081b040902 74
    0x51403074040c81c0000c9614515049910039660940040d940008000950600740203d94038420340880d19003400f2940d002064503800003030301c0c0007000340d01c50007042e0600c030b03242e000500580804800d403404c0d941c1d507000d5203a4a6200d48490801b01e1500000000d551006101e82081125251111402d903602d00500f154951701c01040001403045a00700c001c0543c4540d04a41c100500c514000541185d0521664182d00c130f155011108586c1000c101042030403080000000d8264141c41c0551101c01c14a4519840042d48c2c00035582e00785401240f40038000d13180d4000850901803804550004c0701c20313004480a1144030a080c2c08690380c40c03c01c4200d920341070015039004401640070b0b100c29071a40c0c0c0d615640da10581c050383c0804136100c460359080c88180310320402d917042907826a1900c0c1c80c0c00a04c5441d4a0000c1440200e1031010800c80b2154503103030808050b002c001a210f210f1113100d40303002a2080d900c540008001203451700058030304030020741500c5c034203c4e41e100e116060500e0250094065070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 96887590 1250 96886340 96886357
    0x6130c171506041d0a05060903093a060207061503030509101806030e0115120f0203070e0109021b03090625020619020d090e0106030c0309120c0209060a050108060105 73
    0x1960b6030351030360414690f01090030200c8030304d0002e02079070002824042d20f07001d00508050040d800c20445002140d5441541ea07030500c14445481c040091125001540c00a081e0021400150000b94403020441241e005003030306841840c04109020b010407000c2c0745101203010040c04140708000300210f51624602d000203040d114900b00407246c08413041240d8500c01c5510100210b51038421070b41580d0b0081c001c048603c01c040700c0d00008181381580340d01c82d5880d4800050b2405009420f9013096440c117000030740c00703483c0c5030081c00a2541d44c1c041c182c00035800302103100e00341d01c40c464100380c8081001c82112070b04c41c0000e18003410400c40d04080044405003114807102e50440c14681e00050b105d0700080c20440380725070a621a00c400d1460302034202040242000b08001c00c010050144c0105880c81c181540c17290315002030b13102d0804000364010003020704003508070100040c083c0900c3e5880080494000d20a0301c200d203054540300180000c181d9240200b5002c02c5d02ca200103000c030b500c104058142c01c07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 96888840 1250 96887590 96887599
    0x41a070f03020d09140a0c090504021c05030c060106050705010506010f1d03010b030a03020c2e080703090213060503071a030703020903120c01090b1f0902180306130c171506 76
    0x70149541c0c0d801c004806030a0f84241c6421030b400311346c01e00c440059000004c00403164180401c4c40c0603400582d8009014003021540d214192a060903c1410400d03543c0f1100100125012940c4400340030b4210380000030220394540c2800005405035229a50b4400740c0401d039160345036088010000c015040300100350701d903003640d0307240c5070090320756400c111001445010760061721820ba2070105016440e90ba140d241312055002c0f03810714059585081d40b490410398145480301064458031001c0700500100040a540305810315045c040300455a48402c0c101c980840440ba512980d83c074020000a0140301d24619100050000451841c0030703400424200710018159076075400100c4a00d5110381000401d400c00b80e56508886040121000b070250700600c0103541000d100d54006100021070140c0d0094003840e540200d00900b00307105210061212490040640781c00d854000281c46090001020030f40750740089520000c0c4c40c08076a0012a8000700d039101030b000381c403440728514070200006070189030003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 96890090 1250 96888840 96888851
    0x60b090f01030e1518070501021908030a23010f050d08040311040b0a0902040e0f060d1101020f010204080c09070504031e0c120f05010b010504060e12031908041a070f03020d 76
    0xd0b9044c1100880c4221444100d101851000000540c900004ca030002d505540c41560754005800407540e01000b035961110510f40d03640d4034a02c0300000f820520052188081e071090b400d0550403100390003a030685040b4100210a141c1e0b5004110155041401c0901685001c120500100b803400c0c820789a01c04000d080031400c0d084200201d0002e90300c0794008482c056000c0340070711547c80c0013501a41c0120002d18022000d080020000300c03200c07110b0340014000d0700c0d502c20610311a4002d0003400070001040000719201c699407040b654684414800d154401c401e030b000001e45540c0610251006e50b0381000e040720300d985c0c0c0c0301c55010115440d51016213041c0410b80d070016180c00d420021400540c4076425121143d605ca280050a5850f0103940741c1c1030080510007400310b541c0c00b00e001020900d040b034096081e09943c49106007184990111001c2c040d90801035840450b030032540b540c0c061441000b134621003c2003003174074001d1a10143d66000c00240c0346a99030041c80d210b078001d040c140c440e01c1d0700000c9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 96891340 1250 96890090 96890113
    0x607050f060c0703020c0303040b0904020a02070503010509030d11030412050f070c06050a17040b19021306090302150403030815060d0603060507031404020612040503120f010306060b090f01030e 85
    0x6000001c0390300c22002000003403c90109136052004113400d80050f0002e40c1442e040c030f68007422070301840320582e000c0c2c0d03808603090009520800420700246405002041941040c80d2480c1e2207030302c2114401c11844c01d0000031151840f903001124800c641010f0007100e5a50032250480f07842d84001c2d21701d0a07540052041d40c020552000d00e83d801002c003629150b60307030480d02c50042c10381c0740090780b00c48140e00a201000045941072845d2071744039621000b2000010b80010010009000b407107559034600070422008140c2ca40c00000700c2d4280c900031030b891001c1c50210350f400d401c9441a4080140042c140b0808584648440c4030b0240240f900100382d281800603280b0700c401228401da01c20b41c0d41c0383d140c20034010b02e0350701031003410402c0c02051610b0410b86416004114144a04000a1250030800c0005801c0c000300340b0980d00f411040042c00509404c01d8503111031504028042134400a10380750001076901800821244580380291500344802190381c01035000b40f00d1440b04032050300464440b03a1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 96892590 1250 96891340 96891343
    0x1b0f010503041b15080a052a07171305061309110c010f050106030b04090f0f020109180f0518190312060b0c0106050103020c100b061306030c0305070e010c020607050f 73
    0x401500b5801c080c80041c0c41c0c4c8013401400100090460210546404203102c100c0e82c040b025045ca24039043c2c44035071400d402001d091194418444d0140616141c1d04901c00e42001c0b140080c0f800b6400c80044003842e549860421007980b09030b1114039409070200108100e0096240c2040d607001d80b890401c5418038a083d04020300b500d2000c6c6c4801c01260b550340040c0141b5800d4459001d01d81401c0d24100901c56140e030791404c078180b140001030807554078600e401c7e04680c801c0e001d2201801c41c000108185e111480600c0018081c40a40c250342c4909000025083e41040c001483e40c281441c0300038000c804000c48211008005007105408201460304078040707203082d5014210003880d410380d02030390380d4250000d1a07003100e00b99004181018010005483c0712640025107102507000e61100060b4031980000103501d9200c0d1502c40c0b10b0350041c01c00009002c40e00360b4080b44026107980c0381400301e552842170482c0d100780c04418890100f40f60309403d502508003034015100b0984104115202c644c1200b4409 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 96893840 1250 96892590 96892643
    0xf0126010908190906020304061d03280b0f040c05060c0129090a151e030f03030f0510150e0109050d0b06010f02010b03060412120f0605031b0f01050304 67
    0x40660314183d0b200c08031a19803288804000384524405541020f04004005014242007140c1d4840080003246e0b101c1c1c23581c0c041c049211709031245401448030315080134681942d09200c940c03d59590300540005101c00620060390740c070803684a500e4000c1c0d0750820b030030810290043c1c103084d12199030f03d034030f10b100c40b03805100340140c11080d50b41607042c0d03021440200081000004c1c002c031103040c2040500a080b03807181141d8000e6403840f4110b000c1c0341100c0314170240001d034036902c00341c8a1008001617109054155100020064a18805000390713568800c2e010840c0e8110b03c1400341051030001040c2003d40b033050452210501403424018242d90b49000509000c40130710301b911144040c00078400c243da000344180400030840d000a001000000d00020340321580104068824144513040c50082c41c803d064010071410364400810400341c0f050b81050041440b4000da0b03001e40b00d540e00c0ca038034040b11402425642203000300b0207020301c0f584500458041c0c002410031034a015400000020b401c0002064 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 96895090 1250 96893840 96893857
    0x6211803190309230d0e061b0f0a0c0510030209180a1e02040e060d030804030804080708270d2d1a1e090604030c0c050a08010f050f0126010908 63
    0x1c025030740907000c03a10760170200003203007100034804543d24440340c94130783c00c040c1c0300c034205807030703075114841c50703041007090410160750f04000c80f90203a6000c1808000c641c140280075283c2c02d54030061215000d07181601207118034941940c0c400460f00142d06469890001c0d2a0300c1002d010002c900420b201c4020520810745000c122840b90b00442c09028008002050301d510800c1103481018070034039500c2c06050000d02a0010b070411409000040500c1100d10440d4400c55100704219651400c0e90064000250503100c81140407040d03203000102894100000d4100c9038000f18035080300b1412034520490b1900200c6212486012401d9020105600b01c514400e4448110305c842d0039841c0c07070f11701c2c450702c0d0508450044a0407810014006441c1c00000e1071a030056060400710040b4000f814181c0b03200b60710b0380c80340da4070800703401d00411801c2c07041d00301c0c00011034220360912040d2100c140d4411244c03c01d01501d034283e40c8142000d1583c05000701c4504901c2495400000c400603552680d05469108804 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 96896340 1250 96895090 96895133
    0x151207030506150613180902060403030804021504151b0602030f040c05090f0403050a02070e100602060a2a0905100c1412030604020904060506211803190309 69
    0x4005070811204450f000d00c0e0011604180303410112043d01801400078007514140c0c02070000c02068014040d440281d4003500105083d0b202c40e50bd00d0018500d041c1220124000e800e1103d040b1040031083c030a443c1901c25100d0494034080d041441200d00100349507821003002071082124001c80c11a20040d8041ca0301021200c865250a05184001c02465442240039042880402101024220510b5000356240c602181d07900f0806070101d1410290350400c0700070400303440c02c2c0403503080054900c2084807a56006d4131216071b190103103401101c9510604041030385416103014070b5101110017808034520581003101c810368860300030404000301e111b076210100e00c00400b55800d0210258407000880c241070000c040308909090134102902016048034022030300801c40d55a146d4070ba802c80c001802d0007618407504c801340803440110320205500031400e000700701400725001400c40d020394103140340d0070002076161030030410a10344621084901d03d42010b0341c983c0c205c00043c00407800c028041e1190b18 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 96897590 1250 96896340 96896353
    0x20904140f070f18090b01090b030c0109080601060f05120c031e0709090b0a0302120303040204140108190303060b030a20041202060304020420030403020d0509091512070305 76
    0x8142407401950700702400c05030340001c40400c825000c14407040c05545090000d01c45040c28010fa110207041580b00040003601210300103d0540c046900802030305070110200d071001d000310001518044441d000b1551141c01c110f0040c807015004091503203813051079152031440c0410105840d581d420302511090a0402c0001c18800c1c2104d00d000c4100e405000c00c128100c060070300765405000da603050720680b0101c0303484058032081c0b0b503504000c60700210303005030801d9004a10b00440c3d40d125071084404a200c4c0740385c075100340d03291080010101d042c0d4030030740014078203001c000c1036044140350404400c4040688fc0c50020a1445002010f503000b03031980c18005c41d07000007011003000000c2441d4a8844050300510040144050300800381948540685405580340c0702c034000704010b8004c0d07058545600206204018056201d40011031181d8000c2c1d081c2c441c640c80a0900b1905849030080c01d81c3c0c00f45030b030400b0071040300807039680300d50b407610003000003d06400d03043c081c900b411400d0340700f605c140d04441e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 96898840 1250 96897590 96897623
    0x9020702030f030c070513060806190b06040f0f090e03040311060d1b030c03110a030221010e04050c01170c090102010b030d0f1b0f03050a0c1e120309050615030703020904 75
    0x801c5000420100301034288102414842c008ae80c40c00014080020707280b2114130010a80c030b145e484007541910103008aa42c071908c5d110489888000ca118020120389040c60000b050a400d1080e4044100b01d035015602d45461a12682240144591810b61201081045035800310052261410888140365001581100210041c044800c1c003c0100c05141c142406100d207104488200d0f0720f00ca84c54200117843d1190b2031010720300200704004000c4041c00440012071040b20b005041807080381f103103040301d041025520044a00b80305413070301c0583c441080404a00045004030151400880602c0001030f948140000a1300c1e0100300b02c035000220320000d00101c2c1d12907000c20002c850611207045003d0003000d6544403041707040c1c04003001d0304014022503280e500900c01c81d505032246810250100a520254000e6500340380c4960003210602026001d8600c070704d0103401341400081d0401d0141403a030340c0d486160044600c103541040c0d03050040003000300050b92146007490245002c0c8195031007540c400e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 96900090 1250 96898840 96898849
    0x1803080603010509060405210d0e030301180608030306120f06041b060305060306060603190e0304090c08060a0315091502030109230714040302121c090f09020702030f030c0705 77
    0x4c1c05910441d00100d04010110b0000a0240e11607180c40d8014100d0011100c7c0011035070148d901c0c540c6030541050046c8590342c0740080954142c4c2c0c00e14091801512307402d882c0901300c07001d520440d06c240c0c0040c00081c1c00351802080071881c6403400800d5511505501e0102402d1000440e4120f0b884c00781c0c0c1750507450300c501c0f06841901a1071141000c0215080040000395290f00007001e0521888002000a502c071140d0168a060440b55500034040741c000d03403481d6601d0f900203002e0744803c0c034034002017005994400c6810500880b00030f0f04240d10242140c4a203440c00140580c03801c070742519503030321600007181c914980503042c80801d4010707200c0d41462802029a441d260082c040141c0e2240c00241001c444201e9070b400501b9824816a42c0070300c854140b24034021640080d5000405a110600d480380c007080c2c4403101050044844494003501c542554045407502440c0035a000c582e100b80321001c0c00d54010300f401070004046850404c0c84804891843e071120801c581c0350303000117000304240d040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 96901340 1250 96900090 96900101
    0x2060a030609180b01030618020d05061e1315020f040b040305070801060533030405060f01050108070906030905070308070804031106071109070e10090503121303030f03180308060301 80
    0x1c40c3c2481480341003003512034000c440010300000d0441c80e40c5584030301c0d4000c519885828002e030701400d8400141800e040003512480e040b00d00406a072004031f81120141c44585001b4440c0c41908020344601c14140c0f140801c400b204c1e4281c0346801d908211a82c2d2505045c3c2c0030304000c0c10000360040d642c904510b0141e007069503d074441d00a45c1c1c102401480507958030340701000c1c0030007191b00040c950208100c002c2c00f03114076800c2c0311240e03140000500c0248035010440c02d126900d9a40308400d243d03030700c9004480c103850860311400041e0f0003a9060191a21a402250000340030750110b03001d0300e880b43c8030302009510580e0304a4204400050030030410820340c03403400d24048111a524100640c0e074480c5001d010400c150a8401c00703500c0000350b00680528800e0783d0070300d40500340c01005100c0344800342074084103004045c80782c840c800302c0380e122500c1c0d06c0482d00ba69003041c1507000b105145682c280c851509a806010a040d111280c02000c000e0200103c40c0e071a00940e107020890602c8020b06003101c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 96902590 1250 96901340 96901361
    0x90509030a170f19090602030c0702040b0114220b0c0c0109120c03020d14061501090509130b09100c0302030406050718060e0102120301030507140d03120209010c02060a030609 77
    0x1032080200305200c40d01540e160340c05205041c1c4c40706803000d1116040d0003041c403410002d00e128804014040d040c130b03403e409000f002c0e200750b504002070b0300e000b001569290ba440721200e00780081046103403500d240b03400f048072000141e00c84440d401c03500d13440211410381040000050540c401c50715481150384c03100024004201c052001e0550ba0701c2a103c0b45c0c003010305400080c0c025010001c12401304a800045030180081240c180e81050030104075100604510400f450b000800c03003440030400d4030344000a01d000d010300b03000065980300c00fa520b104890500030100c11070341c00340160040c0311100c03a0155813003443e801c0c1d80050f9a841d01e0703d040011140d001d840c0100300b05a040144c40740c0c4159020141c00d0700c1103401d110468410020040340703007000760310070f0030720a40020000100700300c4009045801d079429040400d843c081181c061080c04e1940c1c000c040d0010b140c40342d9a03412074141c0e60043c01c1a9606141424258820ba000b15400780d00c15030260001a94441c8200025003c0d40714404014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 96903840 1250 96902590 96902627
    0x403140c0102013614011805010e031204060506120601030311010f0608030d0e12070b19091a0c07020d05030d0501050a0501090506090a0e07020304030b060409030903030e0406090509030a 82
    0x3c5075070201081d01d030082560404841a05130119000d000250300d41254501d0301030001c1c0030200003081414000c807109002210258240081c0c084462001320540303540114541c00354995039159141c41c005001c000d070003942c002112842c4548104010311919000c0c42c000d442d800070b0400700b4440c172030854000d83c03c044001c034600242480b42000100454041c8824207001203841c3d40a8103c40e400d01c002146403c2c00030b00001990410881c40c800001d202d001c554481540c11106904080709031464030390300501036000703421040c0070a032040200d2a044103003c02d2840c108011f90b40410000c000c480c20581e060b0323001180c0b03a60071011b2400b07000c1c0504016540605060b190130300180c210102d6000b0702e0710816011030b00c081c442c2c440054200051040c0703915240241400003000c2e40320b9003c0e002c2910102c0001001455504150140c1401c240e4036650301108a4a15103045410b40c1718000600c0d403160302d0340d40000c0c4c90410ba003d100c1c05100401c01850742c0350622400580b6a200300d041d0750361072 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 96905090 1250 96903840 96903881
    0x1020c030324060922021303020f03070b030136091b05151c02040b0301030203120408060103151b0206061009030b07050a110604060f0614240403140c010201 69
    0x103901c992007130340c80e0202d082e40c05d16803103494460f88005074284100040d480610205c0c00000d004220a00030040b20f00036a00d85001403c854107054940c0c80d00c4c0540c000c00d210400040200d00701c0b02d0082c1c131403100c01108101c251081203842100380d0038280d800154040c8c0307800e0360b0014041c041c4400700e04100c061400300866032420001c521201c41c2c400040e0300c4060f01050340d84445001c01e440124640c27400c6021584c9546176842c3d0340c5140c100707002c140d020b80315880740001890007003000c54043e500c405005104a80c656622119075412000c021817150391221881d4900c0004988040c21218568014000500c5c0c0701d000e0207545017184c1420820003828403020000304044e840c7c915042070061403c103643e5407d941c001d0303a0700404214981d0b403610507a010003040c009203921603101c4440c10801400903560b00c0c0d403903154943d4607010340385e80702c07036140e14030200b100143e94041101c00172288004d00f00b0750f4030384070000d51541c108407d42c034941106000d60f400d51ba0a1044205d84c9200f07030320b150344 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 96906340 1250 96905090 96905161
    0x90c080604030e010807020a050609010e070b040b040506030606090402130501031a060d090305070206180918031611032b02030a02120306012109060b091911070501020c0303 76
    0x7501c80c06603d424103000d007407004545018802c2c40360002160300310045443c02d013441101c5900030722200c1200b040c0740c068903d010800d2801c040c2220119a121141c607414903040504204295201500041e0701000c02c11036003549407218005407030b81c2c6d01900c40d40b008440c034003c005420b88a80b184100e08150f821483c0d010251750304400d4421210700701c140050040310754501624103119022003e0350107100825003024042e2402c8010203420070507214103ca40d1a408001c200b01e0301c21460b000c02c590024401151883c1075061901400707400b5661680000c032540c5d000c2070901001400180501d44030140c8094524940d94603904590101d20045140c00810744000f92034940440a0f03d4902c44000042100d41c0e114081c141880324444072011529118040f0340390040a501108581103400d0200b6035846140c42c0d4882071040101007002ca80981000824000404100002c0d0154040a000302004500e0900c042d051050b403050003544d0b42e0521401c1c6a4a5041c0c1204c40080205144403c48 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 96907590 1250 96906340 96906347
    0x906010507060f02040306090c08390a05040e0a17090a0e07030209030625031b050c010e0303010803040612050106050f16050f0709060603060e04020f120709090c08060403 75
    0x881c000d0b00150002281c0d101c84400c08080c1c46140e0004d0017203401d162000c000d0100c03074150107088440d120202c805a884000c0080c54810600191482100c2100414a200d042d04c5142e40d42106000344941c0680f03032104005003c0780d2810303250803120390203250388800300840280860b0314105c0c2c10001c181002c041100080315404c1c4c40c0141c40105400c0740200d00710a00a8041d5100d5400040a40300da070302d804244c0480041403084d544d0030300d00b14880020b0241c2d000c0e00c542e604000c01060b1a40c15001e03602001e4038981d000901c03032000703596204138002d002c81d0144055400b80c05042c0c05075a50b1403501c0c1009000300017481000001515080040000741d800c03070115142c0300c960484041e2100c1c0b10304080398030074201c1003014215018071260108440c0c408116123040d2800f5000030403900d0b407280000c0742187c207103000d40001ca00c0d950300403c000d490310800380130f15007100510350060741c000446103d0074240c00c1c7d4802d0144035180d40b0a4010000510000400fa00c0410010b060310702e481c0d01c004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 96908840 1250 96907590 96907597
    0x20307091e0b07150e0c010305010b030709170709110a0806031f1a0409050c03100c0e131506050405010e0d020d14100c0518090603030706020a031506020a0b0609060105 74
    0x900b404400040c100c040110000c0b0000300c030149601e0810040140b450040e40f1148800c0e4010300191400b40007040d0a214072060364019902d640c1d41d2460141410b02200d410107891800c03601070703c90100d00044141d010b009001c025056001000e84a21300e14030081d0181c400941250301c80d800c003d4101c4c40701a110703a84400c48800074100451600350f980e0b03011040d0064101c0154119040038505028080c0c0041c1214604c0c1d000e078201c9079a44980c2884004130340300f81c00d0200025000001c0013280389041042c4031900c0c80795200007c1c07405000401c100c4520020740c41140400d40104040005682040700200f404009803030301c5042032680d600107140d5043c00180141060002010408152001c001910510186800401078aaa00d980c060942d812403030113030303100030b0000e14000194280741d01c00c10301801000e00114101011a40d490010b904080ea1810415940e060b9010829200c03440d18002010079401070302844050b03052165003084010080350003045d1001c140074940c0d0703020084 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 96910090 1250 96908840 96908849
    0x12152304030e0609060f07110418020d02060d0c08160201021812010e0d03090c05030d0903030f020102070218010e15010e01050f04030605040305040e090601050f0103021b10020307091e 81
    0x600b08410300b18009600e80c000d400c2c003140c0120000c50f180e260400440014420103000b0300c445052011150200300507074414001030180b8a26000c2d864006007000034150920740e02c0100254144a1004d0100c0115850001c0900000d402176041c00b00c00d000e080e404405100c03652000b54540400d904153311170340da8000c0135034011603c207580114002e02c203600c900d02213100c400c160344004103030140060290151304000e40c0c0e8055400800100c0d450001b84a81080d01a52101c401503441d41d00c09680c00018800960150f5400b04040c01c0103950704192011600704103196484075504082c185014003400401c109500d04402d51003101580c4c20803c0040307400024a025545e07015401d5841c103a500036a4401030840d4204001c2c0420150084050030580b40802040b84080d0340c1c1d40ba90b1540e85900f80b2402c1d4111215a4450b44507500c82c1d0010400d840b09940d1403070301d0141411007549132400100c1124403481d408014003800f6503000c406800185902c0c6406004054102c0f160300350135141c1e106 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 96911340 1250 96910090 96910097
    0x801091b0e0607171312021e0612040305031b2703011401080c011106041a04020607080c010c0908070509010e0a0e0d020d09090203040f06090c1215230403 68
    0x707208055030b50315084410040e480007140107600a1801141c00d02c0e0070035a5010081c0742030010100d2540d850300500d0100d281c00401d07440a03900c21b41841d64180940f400c1d41d035044001000180844104248040c1c0501d12a60302c7c0d55482c60054140c0302c0c05c01030b0b095102540c030401c010b0240b81328601c1081d901e9001000800302292801c442c0000c1c018003078601d440c091a0700710000000d082030040748000c0030301d400f070300d5401c400402c0782c442a4880108950090013034140004080e41a291042e54070350040c1b000d0315451400d83c0a1b10760b401d00d038001104d00500c0d69124444032509545c420701c2e102c000d00c0e81000174111039040070002090140c05000308144e915000c00012119241500088409509402650b00303900e2a20402134a075017080001e0030105d8190b180010f80d684092086a100d16002440b400503c40f01c2d5440c20041d01100307405954880c65804007103072490380300c0c5d0184130062042c0a07005070360700258044415110301c0d1118071014030717038400e4511800d00c3c41c00c80580c1c01681441c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 96912590 1250 96911340 96911357
    0x5010305040f03031d0109030e0306090a050601090b13020c060a060506031003060509031318050708070503040f030e0901090209030c040515010c0c0e04080307020105060f0303040b0f04120c05010801091b 89
    0x2c0385c000c00d8220b540c07201c0066081c45804818903400241c15010800c00340c00b81c5090b44c3e1243c1d00c00766940c4152500a050b6405034004000786c071a60b1f0711034005a8801003034400c4040070882c821007603030010322511015401c40720500c014004a80b00d614018001078034440e0440c03810460550340c50005100292000741c8442c00100702044c14800c58a40811000c030b4103940c2da495000b0300703001c0c1c03411049081210346802c01103820f1500030382c1e40ca4407904d207a80d610361855a40c1d98420100c44c0c01e0400440500182c5041071021780d0300c84050a0180c000810010b803100e03180c41c1058603140c681c81c0f03807601503072400f1b0500620f0b082151000c40c2044017130810300c03c0598907107172114010300e1a5001c22400c142d0388051008108256001f18091000c0364001c0c04151a82810004002890400b040e8140d00c100b00410013452404042c2c03148090141c0420b04044d0b66481100c06c8188900d130413109019200343c00e001d290b0300407000740d002d4081c8005c100106460300c0d0307485013407241a001c18070070b00c16031b01e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 96913840 1250 96912590 96912611
    0x302060c09010e0901141003021204110112060e090d03050402060a14070501020c0a2a180b060409021b03030c1c0209060a0206070311090310020c24010603050105010305040f0303 78
    0x10390300c0606030709010303044d21000d603503a46950030707602003090800384205216107079400c08901c00e000755000c00f00b11511a6410303440e60341c2c505482601c401e01d818144075000b409005a40600e01c40d2400500c0c40150842c03442c5410000c04d07051920030103d100a061601c801d220140c2c407503909450031039001d4204a200082d86c80704404070360080600061280d8000503c40c03100181c040350081c0b200d44580c00c84c01014820701c4e00b208402a0b80241e141040c802c0820800c240c84000450104e4441c10540004c0c28181c3c83d80860140d03400b54009201c01c41d00025481c1d0704100000c03a011f8002d4240e0061801e6080989010007580314018400840c048075030b8807202c045c07603039030304a900c2c0f1900240302503612a0410406034071a00300710382140c046403404c3d000035242080320f411100c0c44034005001e00144401d03000d81e0b4000390007810354019144500c9051090744498664446070280104040310313480d40c03422000500782c500581142c0d04060505007030000040c560380d10f1440c082d9041c1000704145605 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 96915090 1250 96913840 96913847
    0x6080f0703061518090603080307030504060204050a0b0715020309120c151504060605030702031b0a0b010602100e0109031b0f0b0c070203010b1207052103040b250302060c0901 77
    0x319042000321103e4030b8001603071a9000240d0900454030380100c8141c0b0703a40c803562001155910300c800741c0400700800005039454802c3d0310142c2d001c5e12980005007020f0312100843c1c1c606499030805040c5240003c1c29000340020702030304140d90000c8000c15440c40c54071007615074503204069292050b180700440c11002009083c8040b03640c981e01c0c081410b16074680200b45041c552280100c680c095890440080f402c1e41c030a0040f240304400c550001e40c640901c10354840c0144100300b50025080c090818031000003550f2145581c02015158000c105214040041408489195814a4a683c580710010380000c0d0400d800c07200f440741400c040c032041545070400b588003000903040100030000b00400c12801d200d210000e002c2e03160094000304881c0302d0038424000c140400d1810800e4035801600104103030b20b049100001900e900c00201041114048526442c4d5006900000b81e850004a10304000340f103581d9102c4d0f6070140c0b0036241b43c0d0050722905c010b500c4241c0900404140301d800a40c0100c039900 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 96916340 1250 96915090 96915101
    0x50402030c0616170d0b0307050f1207090507030504020a0807080703080307120f1a0303040b0d0207030516050304030b0609130320070e040201170108101802090a1506020706080f0703 80
    0x130000504046030520303c3e144001a4001c00c00e28121038500280300c20b8908000035901c0681d5009001144500d600804000c0010b800c1d04103580c2c40e1107001e001180c074801c02d018250144000307883c013003102d0a10784100400340c81b1316000401c13035501100f820801c000300091000126034100200035901e8071951403c54090381880c41e0007214030f043c031805008040c00c661200780d204503c1419454840400c008040e142d125900c5013032603601040c0702683c54013040b83c0c010600d091103401c20a191217020365551040e9520f0340c800b615603400100b1704005200240d903140d58060000c5580c68410b280132900c07000204520440038041240d2a107084844001040c060300c51007226a0071140a199201400d01e0608800c840c22400100e410b24640804400e191405058440c808040d00401691060802c0104011242450b007075140c200a0000f607240c4040c0d180c090401c90401041c9041485410043d00c0e1440c1d101404543c000310302000280c0d405000c0c1a001902c10702c01d01800e807aa00801ca0183c00c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 96917590 1250 96916340 96916343
    0x6090906060f05090f0613180b0603011d1c0e0910050906040209010206070f090b0c0a05010b0102030f040306090804180e0705011103041e09050907090c0504180507090807080a0b0a050402030c0616 86
    0x707920030150f206105000e2190b9202e24030840080c44006804d00c3e0020401e0100c0c0e5560000740e0006a80c3b643d5088082012100c0586a00d0181c606d401d2001c0010003002055410403c0c200c07d40c170741400507090061a10740d201e14107490a52510001e0700c0000d6a40b00000e0441c1704003d20240391508403440303005040004c05400d80240c0e1901000901c2c203031903400c5c2e00000c491641c40c1500b0001c040d4004000e03140c220780945035990402d85503403241c50290000c24421034903041c04010204281c20042d445111160348103000003110103d03030119502e00520ba03044207040c0306c004058004610380010499055548106464800e05a0b21f030300358605010a03000a25098141010011888030008601007103c99610051200c1c50141c50305643c5803041c1d024445035030321800b000c06140400ca41000380c1150b0a40351595083d55100f200504080799904103944541200c10250180103201c0b942c1a00710510f5001040582842d500007550b81044907041030041d100804c004140100222985082e10f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 96918840 1250 96917590 96917621
    0xd0506030a0c06180f030302070512010f020708040303110c0901120503090603070215011502070e1807090b0a090e0d110a050d1e030903080c030a06090906060f05090f0613 75
    0xc3d4888030050001802248494400c0c6080c61000505880409105d0100c0703405401529101c0e007481c2c2030004160a07203420240f40d40d26284000744107203030fa200608401c0e008480715900d46041d032600600192540350041e0035644403216035112030303880c041c24038115031803c0c1c0440e003640700074500282140a1100030071351105001c410080c2c403030340108142c003104070000c0719004e450781c860086950500207450008010b078000e00051040740003560026401000c08801c401da0018903650701c0c1c1c54015580c02c204942d03500c600400c0024109104990050400d0100601100b44080c3d0181d03a6001001d894408000070840642c0d800082030100d002c41c03d030480d06561080d4202c0b100640320003a2100e0b9550100e10040d10560079a00c01d100f50403003d6850356890a59403200345108007260001307813160310085c0d034a940c0000c0003507180c8600038845209007030104002e171a00301c2001010415511590182c0d000e402081007600c2000f540645c4160b040310180c00200c18521580d00a191560b40c2c072264 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 96920090 1250 96918840 96918863
    0x603060a0f0b090a0501090b0d050a030806011704030c14011a04020a05091201020304050d051204200301150e010b0702100c03090f0e04060c03020a0e0111030d0606051b01020f0d0506030a 82
    0x107130019600098142c5400c40d5050000b1f084031800c0c00351a0b86d4544c00913125030402e04030440020300c03e4611940040051400c00740f0b4120086440b03416050aa070118040341e59085034004000422111030800c05e1035070000c02403018038006180c01d000c280b05100d80b103254002050284035000300b05560003801c0203402003281107000740101e4000c0d8416601070350244200c001c03400700d5503c02d10032160061200818981582c9840d030355082c4411152000c003494142140031030403180c40034420f07000e040a100790056940e40c5400d00c2050301c6201a04414481c0400300244400b40c0c075882000d0b480052146001880111241012100c00019801000c0c99098900300020700751000c820003405036016100070042c0c854158000d40c124441c4034032440126148101604c4558094580301440e10000d03000d880c600300c448070310344085a600e60070200120b003002c2580310b50f004003102100002d6996400841c0751070748018400710b850007003100c0c0400b00c5032200005003140d04d040c040c024885900040c44240c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 96921340 1250 96920090 96920101
    0x114010b041811070f061b0912111002150c12180307021c02010f031505010c060f0203070f080c0f1602030a1202070911040311090606310902030603060a0f0b09 70
    0x100403074281070325102c0c01c1180b226100700b492015010450300d942c81c0c5914451401d450400040e61a074019611090902c182610903100c1c141e1180c55440bc55003cbc0900b408000c105425602014068403449101446020f0340c030b81c55114501d400c80e10462802d00342488c10500d803441c40c8215440290433035140c800c000b1a902d00040d858086a01c00d8803061601141c0e41c0088080703c4080d03428202445a80c8020019540a45103102030203000c0c0c01c002c240c46050720340440580c1d0094440c0307030005401802040c10264406401030f08aa98005034601d0b00d4032103401031810340a9205100181040243c1c0c110840d40c0401140c50304075031040f0440320499007010007070744075100d40c484c04152038148607211080c0325415044405895000781542c14080000c014443d03894002000315400c03600410059400f401c0c510f100404050300340e20742a01402060070058500840380d070108031014014070601265640c0441c0c2640d00c400980e0300080d200064290318005450103e0302150450184402d120 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 96922590 1250 96921340 96921353
    0x3040f0c030302070e06010e0f0906040b040501030b060424092a02010b09070c02030303010b0313020303040e06132f040b0a030209100503010f0308031017010207050114010b04181107 80
    0x70200c17510340885a100303907504030064901c91000c140080d4080341c8000c81c0329003441c040300c26581110018000198101a08002c101111000e820690b1000211420050103250a0040700f240100015940301c2c030402d10b440d611082e0b4068061080c400781c580241d0724000c0c00700880100c3c821a81e04d03420b0385401103840003034003c01244640c240101c000c140042c3e030640c0540303c000030403a405001146540c0c030304180c00c9815013026119082c1900280322840160350304101820103800201000d0800342400030030803013040c100300250300a590034a007a5031031031100b071003051002140c580d5201c0c0b041c107489400601c47e441650801c929040700031608514941e49540a400c0d4243c0c107603003e030b0303a480001000359010b0100b4443c080301c68200385803d20005118002031904820041c0c1da5600f05904d80b1008080a42403122900b0160b602003207030000e00209010f07000003280d00f1800c413486541000c029140d64170807800f8158420105016007106003140b075000c50080c107000045103854007800d00e841c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 96923840 1250 96922590 96922603
    0x7050a150e070e0903071106040510080901051509070f120615080901060b0f0f0c010f09062a0c0f050703030f08100e0711030d1508070b070f030503040f0c030302 71
    0x4164850701a0110300301c0f4504035018021915503000718200704150340c1d90b001c01110306180b16001307001440000303039946030140c038080031881d20380302c082441c50600440e6084400052a2900e255031840c1800000e84800400a4102da01407404841840d10f9110a60786042c0045003940c082c0d1038100000351003001c07a076806520320886d603200e1072642c403030360107284c00c4c0e0300580907440003038804022510752044001e00074600d00403070200b0b04d801c00080030b0b1300a003115144440001403d85500c9000c0821100b841040c0462070343e40c0e2203074110424240c4805243e500f00840c04148100c40384c0d0001030106901c00003400d564040101c0b200030740c482c03038014107104100122002140303410780840c00714110800b5400a690b052a900e00c082e55800008842240210403040c80d10701040041c00481d08141c0683d000c040840e00c050060305180c0741e01035161aa581c0e0140c1b40d03070013060181034005201a03408101081e05480c04645940b2581000c01c88400070300b50040c8843c082c1e42000082540100300d0707 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 96925090 1250 96923840 96923861
    0xa21050a060b0903100504210305010513020c070e070c0209040c03060c0f020604080703090801020c0c15040b09040f0b030319030b0d1104201b0f03070b01090207050a15 74
    0x103000300380c1d6900300314546010f100074075641504150840c444800e45a48400d40c06402104641e03944404928044410041c071800310b40000e84440050180d800c0034402d05820a0309000214075011000c104203443d07082602400301c03101d03142d0000c261aa80700301c0314100030a40090600d1400c2c201031401000b101003500c0704441c0c1ea814091040039450040d50740c4803002c015500548a40d80e56030792500041c0e40210411024005504000b259004007480501800c9010f0b0307000345904400300b0200603000d40040f00000300550104020300105a11405465a0784400d5501054640d800240580900500c0082903010b11020480840e03a21070008250b5200b5955202000b009502109009614080c2c00380500681c4601300d1003409070529034081c001c48e46100700480d62100040420424580c0048850218a05034903d11145100c0520503500c0b030300c40e0b180066180c001a59614003003260b0520481c0340e0b0550120310315060200507c800040254441d041014011800481e0801804d49140 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 96926340 1250 96925090 96925111
    0x2d05010501090305071a071a090f070b040509090a0b0c0a1b0b0705220f05030708010606090302150c01092a0317160b040b0f130f03050a2105 62
    0x1403154001c4144106880d0480040c0912509100000d0100d60251008980c0c694040101101142c4880e20b10075004240600442039800c10302806803405030000480c4065400c01d038001c012458a40b4100e40880d0400c1e544d250342030303880c07030b5510341010707000d201c0980348803030351000c00501003c1c3e50700800603000ea5440d05800354206140d11800031020b00070040240c2602c0000c00c2e4a075001e072010708032a5403001a00a49044600c0c4400c604000702d60180f04003d03030301502400380386018071046000d40080780003000b52910703210b00104000000e11010340200080383d0014440445a401c8900301d0b1284002440340c007100b4604040304000201c500c1070303484028601c0c044141f0210162908032904049004101042d00d20303a08482c2d800003900b441100301d10000000000c007026815803113140662001c4605160940346c800c150301e001040b681c04109016120300019580c1c40f054030303000c1d416142040e103400c41c0c03c100340c2e1b444601318030347c440c00c408080601c803a0601c160030040c0b10711118017 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 96927590 1250 96926340 96926351
    0x210f0d080c09031002090d05070602010605040f18291005010e0d0203070b090a08010f0f0501080610060c1a04050d26130206090904120215041203050a2d 67
    0x120750800e40d006110489915401c08000f800b0400c241c1d4014100d0004000c0004031000e031155112460650b080d406800980d440c3c11041040d440c1c64400d8610580e1010b500744851051b01440c4a4209581034004101c207041031000c440c0341c44c3c202c0041914001e144103d000c54140011320141c1840c003445403600050205c100207121741800200751940981c0034004120f15410440c980402c0e0b000800c000f030f003140001600086003c2c1c01d00070002c168400940c0000e011580310944400c3e0340050300030341c405602003070504c248401c1a200400c1254050707d00000c4120b2280b8120384d2000c00800b008400d400e040b0188800d0003c00f080034100040180c50fa047c1041841d40c0c00d1417860450041241030030075400c000b0307507283d01c000c12001200744024003803850240010001480300c801614241d40c00e013241c245041120343c04010035030450064080000551078581c0d1101221140344010404040d240e1003c02c241e9101600703d4807460320051022070085040006410f8542c5a15035818504d03070400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 96928840 1250 96927590 96927601
    0x170406020f070f0b0a0f1e030209090a05060112092102061f06021207110414090606010305040b07180b0f18040203010b1b0304030803010f0305060a0e0606210f0d08 72
    0x202c1c014112404c509655082041d900400d58480040610560a006c059141054410743c80c24028900e1002d076140180c07103030441002d00c445000c1c0200003075025841c02007801074680c0c1140504031065842e14003c1910326140c5084002c400c004041803440b01c4450f070304500000d03000b1804070305c207000030001180240c00e0072003481507080341071042c040941c004042c9007140c10710000c0105601800340c04454002400c001c0810219440207080950385186d00c800d21101482c140038003500040c0034602070025081648900c1d40e01c020240005080c0004190007804005100d0441c070010103400000a4607110360012074900750b0300c814200b42141d084062240341314a414800e40f4140c80d000c035115402d28542400707030504038004c0f190075640c5100600c0b0000c00100c02200860103015850380c3c0d00340070ba10f14500b0614182003d020550307100c3c20001d81915000000460a0340038500301da8800410208994403800c08000340d07000700003401003c0415072007600000384034044181c180d941d941d07140d40380c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 96930090 1250 96928840 96928859
    0x30a0f0f05060919020712020303090d020106030305030a02032503020d0b03120a11100c02010609053405070b04050d0e030706080406050703110a030e0106140303090904170406020f07 80
    0x2c4411035849289000030550303c0b981086035011402d140900140b4001c10b40e240c00c034400211524440c0103a00000400c90032a80c1030141c2c02c0130b155680002d00090b800c2da6000b51032130000510445d8201d0303020000030a07603a03400d941d8004501c940400c079030489048040c01000b9500c098900072225051512149c15401d0008030101100103803c0660308288000108540f18419044564000e1003000244040b00b03159115400c0c41107102d4000082180c54040c0031016900c00801406061810400740e034020f8403010310305580401c50034901400c081c0f8408064459024080000e0600c814600820040000001d09200194a49d8a840104415280070541d1f00c651340d01640c00001c4c2100003103000151150061074202d0b03002d041c0810641c040d00207110050300003854880000381c8504145c50800c1003071040c0c1e4080c041b4001004000d03161440829585c0c804c08040038014240b010008003401641984101070141e49280660b4407a0b88940c0207540310101003104e0700c1401345280c00030304c6412 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 96931340 1250 96930090 96930101
    0x30e030a0207030b0405031b060a0501090b10210c030207060605040c1202030406110a020a1101050c0312100906031a060105030415091104060b0d05060d02010806060304030302090303030a0f0f 84
    0x1000c0c1d0080c8030349410740c2e42d000c60390803001d00304407001d10040c89951184e0300c03007401e41c48a1140600041500340f40a0140702c040d41c1040e444514a1031806401c01015111024011901d080c91b007810802c002c1c400204800030103020050300349551411040030402d0307905400401a040c01000d00344800d0341c884040004458040c0c0c500f00205901c0e640d242c6940c42d59801540c1e009000304400900311400f18040e211960201c4041c80c0160031904201c010003039441241c0c0c41201e0203181c004d0604030400f07481d40d41c0c0d1041c188200f600c0d03001040019504031030310454030045c0582410a000c61036032850320305007030807c9c19843c901e00c100060004030385510070816644656049a0195040038107824100700a105440c1c7c213455610f090200240e454a0324055500145210020030356155000482e603000c85101604c40751080c0442d03400580545c1e03001ea4000d40240c000c656807540c81d2034a00c5c0a40091040314000c6030540804010004c08013a60740c40014681e0501c00203116941c1441c4070141144c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 96932590 1250 96931340 96931357
    0xc0e0106081306060803120f0f010e0c0711030304150906031a041109040903050306010e0603011827080901031103040f060c0201020d0629030408090f01030902120d030e03 75
    0x445000c000341c602d502c01008011801d01882d40010920b032070b004203d00b59404a440025007800e444180610590351940455100044895880b125414a484445c2e9004003900a500340140880c03038100b13002ca1484200b80d1948000d045a581c0c59494071008110303016608540c000c10001203000038a40d01901070300030140310720071181d160a465001000024004001ca0b4a80c41d1410300c218200c903240e41c492441c07000d020b40c0321947c5a1500000040c5410b14000505005000601c010800c008038400c2c02070064800140c04a592407031030540903a0305030b841142c0903108184100003001e0180103402450641402c0e82e0038403d1400d0508030420314032007035070020100e1034020000800325469520020b60400507200161800820108120940340a6000a440e14807800c034401790510301145140100440448070604503d4541c98000c1c20340601c0f0350050085600030086640c5038401c2d4003040d0919402400750640700c141c40760050340c0348003001d4520f0110349090002540c1100c0001500c1404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 96933840 1250 96932590 96932597
    0x6070c02010f0e0907030506040b1e120a0c0e0405010b01111b0609190905070804030c0609020604050d0813050303040f05040b040e060c0304030e100c111210090c0e0106 74
    0x26500c0d0300444044000309510000c00800d600c0800450341c81100750380c0552403507030340407401d410300001300800c0f14101d04850348100c11012084161440300160512091411100c1201c07411810001c4c03400e280c06202d0080c1180320150303001c2001102000c1540c0a140a08000c1003400c6050f0300544441d401c80c1812802c640c007a02440680c0501102c607001110b10140801c0c0c1098040008250080782c08d0f01e402500176081c42080c4402c003840d214466003c1000d1074500c030182042d40300600500c4070a00081c0c545515100c0910a40d207031081100d00402001d010300c010304126040c450200e41100c140001c205070344941c0060700e80340000c15141070b034401024960f201443c0108000060031240b84107908180c81c0c90b0403e40c0140280140745c0b140c1e82c42c200030790f541d15081c03030001d2000c0024072a90784115000058103498941c8807080019586d4020302140581c03412100150442004c414201100d2003900c4604c045421141c00c1100500e00c5508481002c0342c561141e01c0001c1d20034041c4030f001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 96935090 1250 96933840 96933857
    0x103050610051816170901020a030b1c020d08070206030c070203190804092408010207020102060a020f030711010b19180911060703090816030b09010218040f0f15030507080607 77
    0x2058007621040608101d040180f4450b003021403051117100c04403a41d00050b503011407500246038050185000010084814406848032501e84001e09180440082d0045040302c12080421030840e089501841d0000d003030311784903c0c0030740d071001095209020890080c06070040494101e408221034940e44d0354803c101c242000c0c00d2249542c010070306000b41903a9415901d100c5402c00c2c510005000c0a4142d02e4000342e5200440d0001a20780741028160600e128410003007190302c40d2051041d41d81040ca50301c1c00300c1e8503168410445025003080018036034005002005d0f098a007071a0544e4400300c50490300c44060400601c03002608490070b11401070060b070740740b00c280d16403841d00000500307102c0d200c3e0403c2d4090940380d242541c60640981192000c1441c1c0304420f02c144254180155442601c41000394a0703c15a0114005d0b4510350201490207142c944c542650903c1b5903802c400c0012044500401254610414070502004244800da0345030080200120340c0410205119108003959200c0341c0381e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 96936340 1250 96935090 96935101
    0x1e03020f010201051e2a0c010b0904031e090332010e06040b04021c030822020d230a03030b040e01050601140708070602160302010e0102030106020a0b04020307050901030506100518 79
    0x1414280100207004071000c50007426024000b03505108180c941b041d42807030721801c01e203a00a084841000302c0b58403500d00351040000199201c07000301a04614009500070101d4405019100c1e6000d81d00020081c07100310340d040e00102028140d2400e02480da02c4841207500c1c550300098220346142d07014042e990000b50018002c41c4011494540291019040e24041c0e0034486c484680070091120443c0018440c50522409074074071210307951b50b080034030343c041512480d5a0010f204112241002068118603041080c3d07114800019000e1800076401a83c1c80c491442c07900400415810b0000ba01c940d25004000c445043e0501c40c0c5d903c6488107131200496215098a40d0080d50441c80c022a90f0f03070b1040040b4000146603002800240c04012100c0719010090310b0b01a080d07814a6041d41803d0388103100402c00254002842c0b505142c001c032400003d0349035030020904121032a00141c1e006030400000100b0130600040c03061140780f02001c07241d411a02c5008102c255540301ca96811010b1100001c40c0313 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 96937590 1250 96936340 96936391
    0x1407180b03060a05041d0105280e10020a0306030b0f010506031b070203010903030c020f06040c050609031006060e240a260405060619080a030e0a1e03020f01020105 72
    0x160041c00c002c000c030180d00e0b9108005000d8800c8840c4484803100551b9428110344000d00030301d500456510f042468051a144050010300303200300505a219484501c2d0034100e003014020510322b80c92858081d07640d42500321000c1d01500b040e1004840d00400c1c43c001a4001045541090690384e00030714680ca5920b400c40c60403420761414514000c02d920801400006a80c2403248004c014403d8a000ca031692103030030043c2c11710702c0d4002800c000380c01410400c40043c1441003000103468049468130b8903188001d02180c50032a100c100203101501d8000c020820a03045119180d028804848003c105100d031031850148070142c0c040850030010030b21034007654038041c035409001d8486100424101404c000c84010300701c0020340741075485400020521a507070a048074031026003a0210603c08449103060302096403404000c0001d0100702c281c540d00c011a5840015000003425081c2c44824032086e048400c0302041d900e440f0881c402d0740c40c180b40044a50040c0125407203a400c2041c4003095409c03440c4144c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 96938840 1250 96937590 96937597
    0x12030902010203040b03130b07051822020408070e06060a0f0c0201050f130905180601030b100b0c03040513110a03050901060807060305060a05030127050304050402030106031407180b 80
    0x101d066000500000c00e114810102a40c80740c1d00ca2000a51400250305101d41d002c003010703050f202000802c010349480d10900c0c841082842c1015200c5041c520345800300e80078591514481e6181c85800024000385001c0300260b04010794031507048a1415499000401205114540c44a03004c2080751240c205111700610410703200c2401030614900e0505102d8103100d143e0b008070404544c04031040c0091000c2c00c00307407040a5218004c410319403c096000201a980e0340014480107085030b02444c0003071405d10b0030010f10710041c446c48010580310034150880b107807650014042c1600611215010401c0c142e42401080345a10070b20403040c0c0b6100c4401d004501406c0c3c0201112600d40d2a10790004080c50104688001000503580006d02400c00f601001020301095000034440d0307062200c100d41d02400c5408045191040c034000c0c455a040321324002d030840c01503600c12a441803022000080444d0150001c00450070f0307035071000c01c2640d00c443c01a1403044842031511003603550f8075014030001801c2c9005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 96940090 1250 96938840 96938843
    0x3080c0102040b0f0c0d030e030706090807050607020f100603030504060c0201110d020c09150109052b0308040210030c090504021c09210207030b060d0f020a081605030604120309 78
    0x2610b002e44525a81400c2d070f014564211891400040800c1817038024042c010718285189014401354202c41c002681e41d0140100191005079503034018010811003004460741030754020140c8503289031200f4003a4a9407540405402c40e4001c0446c00e0880c0282445070780300340c96054440c070381013909041c000c417100e01ca0803808074140700007013603c4040018104417036030b86014640d000341203071503402050100380c2c0406840091115104012032402d0380c3c00984500c00e60b07105844607124201c00ca14202d101445800c00c142d24142084025024541d105800d40d00c02c600a030740702e480c2502c05c031408030101c1e10300c20b40c29800a11030000500007407405030014820b104160300c007110004e909035a120100c803600b030000ca0340d11800c4501000407540404d11200206914000f5162980c03a6455040e6118030003071402e48a0540000381c0f20401c244045000280e540180c40560b071140c840c5010359840302d800c001c24242c5207403481c00154500e03000800605c16a440251500d000030f00510507409800c0043c0d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 96941340 1250 96940090 96940093
    0x925140a0e031f06060e03071a1e071a090f0a0816050304080a020301060b04270e0d0c020102100905070504020307020f0d02071d060d0b0603070504020703050c0706020c01080103080c 80
    0x10540b003c0007076920089010060100002462407810303c02420030b180c0418080d01175000007004114070038286e551400008003403d04d00341c0da0351001e1412441c1c120709e50311581130a41e02042c1c4009000c110519a9500c407402c0035200d00e00c2d00e030005160741d204200301e1104081d512003007910340000d55140c041e010300810021528540d1a044e81c5190a5030031540001310f01d0303030086802009500c0d09004401c000d05045000c81d140078200322a00c0a1052000ca82d4600d00024002c42c00e40c00602c0d0b444080c1030030ba400152051051691401400c58001040682c0144100394000120109920070110002e900000a11486241c4000d001c042d40004045c01d0540c09039042240000c40c050019204100c2c0b1036015001c0b1509110000e4043e803446810703070000030441c01c200031081d2240665412126000b4045d10825030b03515001030702d08406c070340211386c119001180b64810560048050800807200d07030309030385101d5200d40c000c13a5512242a50207000400f080010000f18a6201c014441c2209040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 96942446 1106 96941340 96941353
    0x1020a0c050d171305030702040e0a031206050f0d060207021005040306060603020f07030e040b03031602090603060606030f040501140c041d09030a05180925140a0e03 73
    0x7004c59544000c0720010a0a00a00f0010307035150310f90041c024011456503401141c0c450607500c10403000315030120b00000c12500f05008110603110090000c3c1403106034001000b45610358110142c60301c5600300034001c003503181c1b00d94045011199071038544d516031070340c1740000803a00308c2e074041020148107100000d0103141a50032940c0d1150186090f590894180c00010010030044192980c140f01c002244c0078605450942890b003640212201421584c1d940b040c151a464120b42c03170399008008000160101502004140d0410b01a80002815041c8a009042184401c1d03403450340700400494100a800c0705181c8000c21040c6007508912070f03050815500755203001d04010041031100c0030580c100000c81e40020b00c0c8074041e000b40440b81500381843d030b07410121041c0507003403000803100f104600c0c07050040d0418148140ca019a052500e0b564800484100c80c42c081496410b000b480c = true := by decide +kernel

theorem cover : BRFrame.Cov 96762590 96942446 := by
  have h0 := BRFrame.cov_init 96762590
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96762590 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 96762590 ≤ n) (h2 : n < 96942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
