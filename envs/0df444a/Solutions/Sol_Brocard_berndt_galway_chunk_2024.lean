-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2024
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:28:21.857389+00:00
-- url     : https://prove2.me/submissions/bf6c14f7-8571-4034-bd5e-ccd7efb303d1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 363848920 ≤ n < 364028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 363850170 1250 363848920 363848941
    0x907060c020a06050309160b03040c060f0807120b0607080912030708031f05120714010203090303070b06150a08071403090309091b0c0a0b2a07020f090a14 68
    0x35204025030191100d5024040f0b1440350004c2c43e03100c50320b60110343c12104c00413400300380f0708141d400004000e80000200002d01901c2c843c60300c010300b4140303044640c2001d040d000400740308000d050a4100540d4000e5800b10002c00e4103e4486044024503007a0b8070b014516002c007043d4019030401d405640c0e820300703422203003030040246c0f07180399042400541303585d81e0803c0301c45251012100f00c140444a8800c04150f6403501c802000c4074081d5000100303010f609246010b0a44c00540340c01c03a04540c410002d4112585020080e40c0816130b004d0f0500400d519038000040700301102c40500c0d030184102241d101c0101b40e011842500a0b010394944480072801448040c59511044480c0740e11580b04004c45280c03410720560311030b40119285d180d54540c085000310300b00300d5480707900c0e082d01d140e00420703424051280030300c1d015400c076100d9807501c031001d50700303a81d11064990500c85041c2c9400000c43c56609548a0141080c011100200210500d15004440c04000c041d10110424003500503000207071030224 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 363851420 1250 363850170 363850187
    0x80f071d190b030319210c020a03180b0708040e07031512021306080f010f1a1002030d0501030605091b0916030f050703020a0813020915010c0b010e090706 68
    0x224058003105001c5161560140816840c1160948070420001710114000b082c840b912810310b56801e4007015400040c102041c030352a00601d2214074041c80d6104240e00005c070100140d40c942032401616000b5007010100a01d1030380840740c107400004419042012240c018425600c2240d040340309a25000780c01c130121131242650700101c2c0d205000a0217401e80c100480808248000c045002e024148000030040d6a1160301031a2140c2c811107118140f00003c0c010020011a030031350800c07502c10b010a0102070b840500c82800d0041743c55019200080b4801e00c101c4500c4589400d00307100c1940e427490288000c103411501c11003140602056401e041002801e03005100d200142030340c1d225210849419040000840550141640c40444003c02c401901400341308107003d480058442a00a001401d514002003003c86100c02040c0c1450041c1e884400075500100400a8405241c21480058503822184080507040c40c0c01c04000058991841c1c255038403c0441c7c5041e00c401981c0c074403054a2500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 363852670 1250 363851420 363851431
    0x10303050c0f07060c0807051e01060f1a04050907020307061a040b010f0f05181201050f0f0115080402040e0604050703030e060f0f130b0c032808150a080f071d 70
    0x603541700300d4901080f0000c01500c400c500400030b44201c0503030007105d8481c00c1c0380d02000c04000e94403440200070340e5058468410080540003840d0007140000b2101c2e488a00c100d0007014400d2a0100106003813606c204103440189500032410861001500c0d0501000442c0200c0c182c0318034185041501e80e07506c5180c2c1c4071319403035042d210361000e0764844a00b60788a8228904403121008a00303410200b541e81c9031650281d00b480c010000441e03040c07080c00002e58110003480c100808503040b0042080380808000c0b100f0360300e07840c54020aa03880d00c1c40010702800f0034281190083c410b0005000600c580840c04404680c0701c2e07240d11803185c92100500c441030181003901c0c441c120041c0a58483c242120009001164251480d4038519450381b80e601d0207600b003024280e600350300100305008900c40a02c3c0c2940740d0080f40207944401307d0490002000c108000f03010798035100c09090101c909407070710346002018007060000d407a14440603001c0c0c1580c801d498802e80803522860400e14a207044142d4400303020300d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 363853920 1250 363852670 363852677
    0xd0206030604090201030b030d03050414030304050316150614040c210e15100e1f03031d0901120308060609100c0f120809240a0b0a0b03010303050c0f0706 68
    0x69480d50704100007098810b10582c141500c0742c1600d403041e5003d100c00d03d4111011b46002036142814100318200c9850310038495840d500400510021900000a650506c1170082108106c0d080524012543c2c11401c2d202492850615001040216801d101c03500310b044203650030062101c080e8400c0b0f40841c0d044106419481c28800c01540710403042c0c011200c1c000d41001101e102d0214481c1c03450224504481a09000311807880500c0300d440407003030301500044a000c440c121010503000100480a241c80014103003c104a000c80c0e040309504440c403150b08000340030456a40e0b46548141d804200c4a0003100010382050001c3c00a141080c1030340c605980c083c0011111280d40c5c4c10075615030a41d00b40540d6403c3c0c541c0caa41000420800840c013680034a907880103d10302342203403000c1c0b0781a414410846000342d04610442000615010194041d42192001c1900d408060119101e00e045030450582400000004014150050010003180020508a42500d941100c0d001d458074068014140003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 363855170 1250 363853920 363853927
    0x1206010e13050a021302030711030403420c0210020c070501050c10060f050a0e07020c01030c0e0d08041d0f13020a0512060105040e0d02070b07050c10030b03010b0d0206 74
    0x104440d50070105a10b4450000c0b00d0142c0e0594001450391800c44168003800c40d000030410001c0346d0312580240d01c1d03941400c0214145030850303440580003408000d0207030780340741c0280c020892180742d009008000345044403c64152084010100050a000301c201d0025116003040d414826010340f00b1610b030240d80d400544002420300f80111810340c001800c440551103a03d9140d03071746030100d10603000148003040406c5801490003041c00030654159010701035800200d01003000306a004106101403640901e0000b80582009006584800fa41004d440c0c1181d00c0900007020081d46000a10a0700c10f20b800300000d1403843c03a180c8043c03000031200c80c03000d9142035010400f01c48201450b0f1000310b20042102c1c20003500c600100e03140c09050800d559550340304000412040c2418410207206120f404054011105a800040d40e01c4c2078504c20101c401e08009100708c00e000042c000c1c04103089000302100003ca07010071006014141070722a19100b546031180d56545890102103850000d9400707400711b0705 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 363856420 1250 363855170 363855181
    0x2030a021504050a080d02062203030b1909050a051f09020901050f0703050a030b0103020301080c010503100b0c0604052413021801180501141f02030c03181206010e 72
    0xe00200359010072411090910000c6529030b2425142406000c0360402082c11120b4100028a01180686032058004800304803800303504a40101c96941a003508011034110341130b202040e41404060300120781c08001c41004141e80b04581c0025011342c000080074041e5442e100d640b0000c031200b894840e00e0101e82c2210400080302507401818281c801418000e0030090b04c081174140b264070052048001072030004041c14080c1d051310a68203000000c0c81c04500b50760408011175a0b80060090075418130601000080c501e480d0b014030a0083c00b8807810703543c2c5038185c00440303a5607145d0a071422a01030207180e902c440c003201c40d0f080b40c0401e04c1010b44d51813480e03161070318251000302076a50240c2c0c0000040394080c080e12892072429000380780c6a00c420207040311280035070080329010380152911000d001c00c0740d0515615072410780500380014480500d20320440c8420381c82d520400c41564024080407070b1110760510507505400e954042603403844440c0300460a2180c80c1c2c070090180f81d40d0820f01001059 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 363857670 1250 363856420 363856429
    0x9030301050303041e0b0d0b0102100504150f02070807050c0a0b03090c010f0309050604081305040207020d03050307111903030c08070f211817041508042a1a0702030a02 74
    0x255403910380d0381403070300d4a44801040c02554400c1d00d03402c6030707e5210900b1b002503590400540c00c1241844c54100070908140e5100111081d800529000e15911581e11000407542c07507045a014a62115100d542c43c40c0074504191900388a02c01701d40b1504104c000080c01600c5102220311074000c9501904212040038015115074603071003e54400c00d070ba20840d8400140e801c201da0b034060340c010b1000341d45600454082c0b49030f400c100c1d044180618014170400d00140c5801c2c2c60701303002d258035080c00c81d226950040d0031100320503000c06480d90b501c40c0b9103a01c08411241c0c1c1c4502d84142c013966003840300031800617055031980800e036407140002d0210000701035040c1c0305680309468039100c2c002d8420103002217105a0b055441c540f00c02ea00810301d00302a88100400c0c2d004182d01c00c4007031541d40e820680780c0a1903d50450000c0c000c0814050904005400c001c0b105000c1039007050b006d8041c0c485108184100152030600d40500c10f6040c0d04074121807140b40752003041c0c031041c1d64000c1c0100048081c0f40e00b8070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 363858920 1250 363857670 363857699
    0x319061104090c120b030d1209140a1a060103020a17040c0f0b0408010f1107060b0d0f050105040203060130060b0a060203070c060c0c2114010606080903030105030304 73
    0x444862007404081002d00c01401114002d040c1c5076215202c1041441018049510f00d044052295105e0a00100c1042d0800c1001c0b070100141100090980041c1c05c14400e40030141c1c0b0040028065850000f08000c0c914050a0410b01c0f9400d958001e82d44001c0150304071f2103034405c0c07000442c0040c440b1030102c41604142642c018410ba01501805a84001202881c425030701b2100300c0540208060113060f9091050f150301c072070218030038022204004c580792000e11500754098010340d202e84040c00c440d110f0404540c3d00c10340c00007010f109062542001030082c00b0598040344640113400000503030f100044d240e28440203031800c00d501c08160740d40e0245040c42002c50111b4031191520181c0c40242d40b00b0640c00e00400c140d0b0050741e40d449980c5480d40c0903464a8000c2070a018203085c0c170b00c0c0030403081e03280304044d941000c5021161030003207403c0508010141100814081401006c4051080190044011198140c0302d801254440e071f40d08a840b80402d0040c5505135005101c100f042501d01c2d40c04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 363860170 1250 363858920 363858941
    0x13081509010b010c08030f060d02040f091b03120513030b040320010506011b050a021011071a0a0c1b17070501091a03071e080f13020109060e010212031503010506031906 74
    0x6580f040d84541d8041400c0d5902d01c6445001607030342c6c40c000400d215140b818440d1034094000c440ed072403415503070382c90b0200300101d41d040b0030050081004640d24180300c5482000e50b400c218444024030740343c41d0042c450b41140d9480038101801c510b0380d01c140d20050090902480050311003020071044040300d81c1980c401c0f000c041c0c9280c899801000c01685640c1c80d094a840c0540d5140d500d41d01c02c0d02d404c28945429540002c981014980c44030300c5240342c8074281c851601e200d02d05183c0b10111400c14000711020034003030500d1a950000006016089043d0011030b01180c80d042d1510980c2c0c2d00015500c01743c00c1d100ea51000c164521204034944a04001180e008000c0e007040a41076400c01d646400c0c9014419000012a10f0070f0305004220701690f2025a0182102d918500b07001400d50000703000505a10501003031050a40e40d01005a00900501840c81145100ca41c0c0b2403800d010104680c8030020703800760080d46000f01241e400e0401007400300d09600196020008000c6030340c1c070000203103070b11306c070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 363861420 1250 363860170 363860179
    0x90a091802090906011d010f0b031003050303160207050a050303030406050a0e03030705070c05040c0e01110705040e1e0a030503041203090b0f0402120c01021213081509010b010c08030f06 82
    0x4940c80142c2e1419281030162603101d000340301a46c1000961001c032118250200300c5540740303d00401c0b800348500040c1c0c090b10500e2074842c1d16138680400f144190450b58000500d907001c040b0801210b90802d00b145101103807a94202d69410341d4030400d112146486014440c0c150b0010030014000ca0500c0e00101c0d00440e500350700140400c01c4041c41030941e0000e4543d0000244002a514240714208050b503000d80003c96003004a0032140310b0180881242140300c038140720002c25021410242030160710000d00000d4020b0206d1001010880e445c3c44400080344030742c0158800d008441c0400044032080c080e8103031078103482e54a030782c0c8803004920b0700000b80804058544d0714490002e031403002441d005400f0150b508240741000c1c41000030114018285c1e43e5903074010303015201181c4e8000b4000c4c13401d42428104903660400d6440081c0c114505401545c8940704c1c0c040722004211040034024400d00142008210f00038002004440c00c55001d54090301245e800c1c03002c00d5031490040117064004a0040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 363862670 1250 363861420 363861461
    0x1911030904020304081308010203060a0504050a0b03120c0f030a09061407060f0204080d0f080613060f0b030f0a0903170903130f0815060a0e090a171905090a09 70
    0x1809a900131138044400d00070100d07101c06909818141007015085100c025811445c1940204411a0b198403e1500c900c3d201d1010034903200352a40824040600031741900c00035049040c20185c140e000190110580c850102c0070701c81d0a90100a540c1c4038500e41d0b80c0c0c05070f418a0f2000440b20000070744501c001c200410004d420000f4a036108500c2e8074062108003680b101d141640490030301040094500601c05600205140240d101c49100da104004a5101c41a00d00710316000703000b01303041d4002c0200200210000304006001d00c0246100d100901000082030780c4e1036031950f05490b034500008021903820500c43e094445095441548541e901c0116410810004c8141c0c40401041c0e011201c0142095010b0181c01024440480c0c80c2e0004505041c031401c0520105100e00320794404c0846022408020031310582042c450751901c6908004480080180143d070f07500f859201207269204410140d210002c80c6004005465100704004c0500000ba85004142006803109400a11084e201c20 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 363863920 1250 363862670 363862687
    0x312010314070815040c0b031e0a091401020c060717070c1a150f040209010c080702010903080705151305060403030c020f01020708030f0604110d020a120e160506191103 74
    0x1040040b090824044c62510f4509086c18288049501c603000002280c40c00c1041259a0b110310034854080c100c20941c803021a642d00384040010700d10389030000d0401c030900716400100241500603150003400c40c415101c251f15040800d9800c58040e000607c61419490001480c00340500c4084e01c03528003490f40507140f044c0b00010003481c401700f2504205841d0701c039400002142014030010b14425002d5504602d8a010500043c1005806060003006508005030310b0045900c901c845400445c0d101001c00c0e21000c49161498071901e13000070030360503800c00c0c1000a000d04202207205401640002c05003c280d01c50b0744088019200786075400c000d5201d1030190444c030040920081040500a407141038a03401d000c1000d50304064064600c500c101d080c1004824449145011203044108a560050b960340d014407040c1d40401090141c400c046c0d150a5081400c124041170b0900d20000c5180c41d0240c494641e0100001030096141100311102030041c11380c0d00b5070243c1400201d442d0000c084a007451103d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 363865170 1250 363863920 363863923
    0x305071a010605070614010b0702041107050303011d0a062103021623042003070e0d0f05010b01030c0203041502030903013602030c010507060b12030a0e0303120103140708 75
    0x303074071a2000a0300084d91005000c0d907449030400340041b020003409654034020319030040340200300001e407145130342c3c09440d51204980c40403944840c7c0d100081d20349a40c0e44e861070f100c95200015001c5094007214000440700c800e248100400d8032078110489608006580780140300c20707900641242984a14080142240c0086560f040200002001e000000d903a20307440c006400c941c0302419002d0707401d10380c034518aa8110040c101c3e81401308a030840e166520510100d403c02000c000d03040e04008041c50722400e0103002a50500601e00a600903c01104188011070844280b642400016001030000b4840540c110000c00002510343c130403a4140414400001d00b11200c0c1fa00d5226000001c2d46005410758500c40141c480254030224103030041d001c0d030007103030f200d02034606514100400040d14500300a0142e0214224840c0903019898600e1203080b83c41e626800754080700c0220f030b110000c000707051400108580320010001e1894495900c6d680d14201c0700c4800c07988901c1e15010b00040452404e90 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 363866420 1250 363865170 363865223
    0x61908010b0418020906120312190b06130b030903210604150608070f0c15050f0c0f16081c14100b03070e060f070308042d030507 57
    0x2014800001d4015030442004101d030740b0701454860340110540c844000d42e541521007680108180c40c0c007114403000c01907681c00c510074401d410494502d504140302030300001000b0420108000b03d8200262040c502c1005558003078007403100d00c0714082100a001d640d0b9070344043c582014a035021079007030a01e040503200701551801114001c0307011710340400440749081d0080f13083c041480c100c200401c40c10407900411b2400c0040c031800622603800c40a0110304c2c82148644201e5170003040083c50301d10f288043c0000f5050945104070142c3c46203000c24002d0340480101c510a06103000f820f8074050745103002c69115405980301791840c80041c4444141c0e85261301d041102d0f1043c038000000c900c01d40101c0302503050030140100da00c0d890204d00500500c040c01048a40001c0c4a0038079843c504c0c0000002007940c40b8403c5150201d00c0045101c5d0300301600041c00c940240c0c840d00c208600c00301250302c42c075280700504c10300a500745551500200480c5c001c2d4020308109020301c070700521540c0d41441000c840e55 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 363867670 1250 363866420 363866429
    0x1d030702120f1f06050a0302010f0e010c0b0c030a0b09100504051b12070801060201021603030b1201020f0409050a0b01050406080c070203061303110a0c05010f03060e010b0406021c02070e0619 84
    0xc4085480c03c1c0c040f05101e10000f4040444202940358255000202450400c821003010301081c5040c030519a07000e01e00450080c1d60000585186c1d2405140c922080d070425103c2c90040c45c100b5000d54841d1510843d0f0600c10b03004c07a810520f169180c1000c02000c0e007000781036011048200c8800d40341442c00c04009111a00c2e110076400018184550001d0018005910070740440e48141b02c0c0e00500e07a420794030358030015010720b00840c5203002e02c800903a045900f002c6e051030035840043c0c440b200f0a40c0c40089d01c12224410001c20040c1da40d88440001d4440205126001410400050146a005440854228070b01003202800d0a07019404640341810a8818031507021030800703244201544009010b9910f85000003038907040815039501c10f100c8089000e0b01c1e0500c02900f0071840007501c81e0b80064000d002041c891919965581d9050b44264002c0c06210010f000c0d00900000e40c0304d001108042000b0075500a100d0546005001150b101c405040c83d81e12101032008080c407590300d41a03003800342 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 363868920 1250 363867670 363867703
    0x21c020d0606170106051c0f05090c0a0611061611010603050102090a140d080a02010e011407170702030301091508010c03061e0302010206060613050a030302070501031d030702120f 79
    0xe060490103800700f03034280c00c02080d004000b001072210b154410150b8540c8802c0e15602d49615080490000c060701c2c6691141030990b103000200415001c000801441c0008103503000840b103034456200300c4500103898401011070b0300441c08641400cd95010048240c001e0303207002c0342d0103009503030694207490f41644240c5640e0f4010411017841d24060300c3d400d004044151003909100d01d41da0124401b40080d28014007005804103c00040f14000c0d0001c840d840c0119000300111010008030281440e0103844460000d0100321100c1c0d4000d080420a5014600c6030b0021802c60b840c2400960140c001510716900c401c3e0071320b07400115000240902d00307441e00c5a4601040c07003070a0030b000e51451640040244804981c0b00005c20241c2d07000325040d60403049c01e4480c0355981d030720702409400180c0341d94407154100c00c89171000030074503902051403000d48100341d8080c4054410b0304416946170343c00c0701c032000d5141c00410404005203080302c04c90090701050030076515156a145001d40c01c20b00600c8215400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 363870170 1250 363868920 363868931
    0x130b0d0c03060506041d040c18021306050703122f03060102061b040513020403080708070b090106060f08070c0b070e0f0607030806120102191d1e04021c020d 69
    0x20980500654000e00740644d02141030074a0040e482d41031136100c0d80c079882d541107140042801d00c001014940081d0840144e43d103045c0c100d80350381c80002e6101e03c0400d4000401c100d0003003281441041100d00c0300e0741540e9a0b42859400d08403843c000d00e500b005e100218580354040e03100015413000c04007103209481c68002d8803032400d0000682020702c014500340050186811240b0542c0505003690242c420030b4403c00b20403e00c69030301c034000348030f00e0b000036000c0480032803007008014180c03000340700d11489054820b165445030380d001e81c2070f20140e01458021074000c0f120150141c2c0310302303012688502c06103000c3c1b55100250b22010010762068404e0400690301110010142c1440300c01c00fa2010000e40d0b046250004640f40200121006400c103440b51900e050701d112104000d40603640e6a08001c081241c0e80c032401d074400b40a001d0100c150034408060506010349610b0440f090a0308000300814544159600c0da040000a5000b2120f2001c801c4844003045040c1c00c4a1001d45814664140b001a4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 363871420 1250 363870170 363870191
    0xf0706230f09150f0a1b120209061c0b1302070b01090b010e0a290f18030703080f070201090e1006050a091a070302012007030c0609020d03080103150902030a0206130b0d 74
    0x1582c0c4001c24504641985990000d69103920100a41c0020111f220041c0c42e507040c00d00044140c800c204881d050340142d030300c0400720600258059040740000301c4180d00c44100202e641e8040e4042d91001900768001740f0b0040160010a42140a11700740514028100390004800100469507070341084d607028844240942344d0a0001e41d50310020401c001d00141805680e038803209181c481e00711b100c01d00030411004001c3d9a101004000301450740700360040e8440b540c958440441c1d03000340034182c3c000f03600c00c003000a8a40884000303501a40b48550300030069400c0a50030340c0c196100604400030800118000240b07038820800421754180d030300328080d9603940ca07414000d0a40d81082e52041c0c50110341449251511190805c03103019543c18200305000328281d041640087c41d1180000c0e4202d86000ca180c0c04041e40b160760349058034419aa100c012541010039401107030202103000390950700c00c010907405450070b900074229104860110302c000780e40340c088c00301180e002130200941d01500d400e4401c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 363872670 1250 363871420 363871441
    0x1701090302010b04090b011401020f0709020c06070c050d0e0604122108010e1f151806090b0906031003060603051c020c060702061c020f0706230f09150f 67
    0x103c54400c200c609000c0c080554a90003043c03841031240041d00600400359040d40c1e402032140602200b10401501c44c143d40d1040d80b00083d52154840860768000e0500240996024200740003003d60040004c200803110200255800c04003400305030ba010005120004140800301180429140f01c2c807903014102220000940420030003a98590501c45107900510001410303030403840d84601684021a0456034219840c565848107804c00d448503460281d0704452035410241010084800c1c84881c40e5003540d5507012030711400280074108400604000744402450040c01450308001da10031082e41441ea6a65004202c8240ea80110354541022650076030502c008400c010200c0200e0011f0081200900002000b034407c40f00001c2c03142000ac80c6007a801101044040c4100010b20380866942e426900784070640c2d000b40c60300311809410a40c0c00440c103066030380c14052003100d2500c2441c40e81c8500990a0300c00000601719801c0d48980f50b0102c0f1030382c0300071034107078060b10a0310741051240c1031080800 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 363873920 1250 363872670 363872681
    0x1303020f071d060a2d1d0403050d18030806010225050d02030304090e21120a180203070e0a060b040e011214030a0e1c0f02040216171b0a051207060204170109030201 72
    0x1106411b0594001000d40c03580c81005640c45945480c10175529111040018014200384000e4295552800c3c3c0340000c058114501d50b0091009800b2200c003110000d601240502080c500035102c2900c1d510204a1420100e80780030307400b0301c02800d581c1000e4a80e038043c401c4801109160050343e101c03814440303c980d1003144044442e4030400f81a4940120402400c42040c0c001d420a4100f031342d1020917140c00385001407a0007480d54010300b0b40f0440d6544040342c243c02c0c101521448000c0d0700d440400507401079008100d8040b0b96500d000d44425a01c2c04a4004030b85040400c10f50341312844400e26598940e0070300007442c0521998640c05540c1c0c2c021000c1c406a884004000107544203496200303008503008007150381c0c0042e4111400b6942d054100031680481c451840003d04060480f4020b0110f154020040c01130007080c441d446070388406594125650700908040035140d9040459a03440305560342c00100aa08d0040c1c5000d0700e02581c43c502807135071440c0b041c8000e030142d42d25041b8504065082c0140c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 363875170 1250 363873920 363873929
    0x1306150f06050a2f03130905060307060c14030418051005040e0a060b03030c0d05070b090604020904290414100203010b0405271303020f071d060a2d 65
    0x21500344640d0f440d0250401203180c0280554511980003400003080000619000e840810141c1c3d4940c268507140d844216154090360300c0c0705052500140356401d0010300039040302d4540d9103200c60740e0b6040d111440d0010341071b01c0401d00ca0208000100c1c00b0840c0410145250802c1da81c00185454038042c40242d807800c58103e28400e42c1407000281002c503000660445240e0000f1000500d0380588002900c0c42c0308030ba0404d60113024010904101c0f98200c030190050fa4007441200c0ba040e52003142d440c0d180d1400300c9009521444140c0464003285403000800950111103030000c10440c0c0025600e2030240302100d0455500f0810485500c94103420b00c03680c40c44540c1244250300359410082030401500583c000d807030296004e01c040310f0311404039181c0000d001002d50250440c03810481943e41e400f40d22090140d01512495240d0b5189100000301079081741c40348512403661010801800da00381c4070207040c2c02c0c0d000c0701254011941c401c000710010b440300c100c441c41102103c6080c10b44401184603511 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 363876420 1250 363875170 363875177
    0x6160309140405042a0510030b040e010902151c1404051501060212161a01150807050910030e06160909090c0b0702010c0b130606090506010905091306150f06 69
    0xc0c131002030010042c08032401100b40050b510907004040c07080b40c5218a0740038551200c0c051407190342d42c0742c25074410040c0381c41c156010f110fa07804003000103003a00c80c0040025080302d013840600c0c000081c01c0018280301c0e01d07208100890307030703c4080440c001e0319110380190f0b200404002c144070420400700701e4103081c5001c2c0701c0b1102e050f626251019440e580d2201d140502c0c010000340d07030400d045d500940c46080d10f9000a00110b805011201c41428800034080c00e83d500045440e0840090f008000c801d01c111142e545007840e10303062005100031041d035401014140350700c032066044a000107000e03041c4610801d900b450340c2050701040082c0045419400f00414616001c0b10787d004c0b035159200d40042d580251403280d95083d280c40102d40018880c603010b040701c0e20410a0046d40210f00b50b00c40b6069006200c18000340f6103401c80c48044a1042c1c0300c0c280418600d03541005241032921006500501d01c003a0456540d0103500e80c40b058592451031850550801d54040c041c0302c0d9020740ac075002d03104514 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 363877670 1250 363876420 363876431
    0x609210305090d08060a0f18180b04060b0d02060d1406100e190515040305070b120a0506130f050103020a0f050d030806061e0a1403090d0806061603091404 68
    0x3440b182d140d52502d0350383c07030811001e01c000504a4455640c40e03c000d1001040403050295901401641c0e2800c1000001d001ca0a2400d0b8001c0c0351030030015030002030f420903040b48e02900d03255070701c03c000c0c08140c000507045240f51010401607901d450240c990000d20b0000410b0341128070750301030040700000740f020b4400c5030b1590030a540b80703a00104d4030318001000e0312440803600788060f101c81342d40001d41c0030552040655030703c000001c0c441000760048074406c000b100d210320b4492070020058002e0f201019003c1101c00000361340c1045c030390491a013141000e4030030840c07a40072881005c1510b0748414940c40883d240e100410840c00d00481c248010801c0c0184081401d05020000b40403045450010381000018000709a0580e138542c110b0b00c40428150080c2c5820302039205e07407182c54000030002c2e0041070811030a03000f803802c284c1c1100d1040c0c54400c0500b486140900f400c0c0c0360141c0103003250360003003c1405210982140440312071000750003600e81c01109442d00d00601070300c440800040740182d0511 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 363878920 1250 363877670 363877681
    0x414070207090207020a0302030609071a0f0d0c14030c040e160507080a210903030c020a050c01032c010504052103070c030e09040605060a0b07020d0615030609210305 73
    0x10a2074010780310303051000f50b550201c0c3d00004100c2c80c615000030b540b6007c0c0800344941b000c4009080300488046031446030000c0b42b0f03803c202034940141e030074004c0008400c001c0e440d030070b004590121410390801c6c1000b244411005c030390541c075608201c600c01d025100014090000340c0039056142e034090714801440c566516070740e10040050003180c600030503009001c2418000f060003003250440d080e00c00752081c41c50303420150702c080144c802517905a000c24a040c0401d0640740c07002c9405058150824000c00300e862610004400528a0039000011b0392403000d400170720402505810781e04032010301d001085904050805a041a903c20a004803a0100340301c2e0250081c0301c2410380c1d50015a6050034100700c000c82c10160303068244010026405000213080008200d03213580a180540301c242e03100780c105a26040d900308107100703250029511100300204400005d1485e00450011401c2803041100705682c1e545010075102c202e54200e444424032a9801c0199101d200c0b0001c4100c054903040c800c60410 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 363880170 1250 363878920 363878923
    0xf0210090c051c051c0f0206070e090a180501090327090506010c05010203040f0b060a0303141b07080622110f04020c0a03110f28060f0f0b04140702 65
    0x344030325405040030020446003070009000540b903c03500582034038400d4107102004044075600500403008a03280d40404074205100040e5a84180d40ba42c0300c610030305407441c04201e0540001070103441210380301d000c60340c0c88070501441240428892400820701a8032880d024000c0100c402542d0400244e40120104800c2140c031080e040f41c401000c0010745440310001221060580d4a001c0c24940c000001d1100300401102480c0740305000710b540304020340700d2104100301c41c2d210344400340004403550881c004c070307501c0000141103055100c0c04103a80d40c03485450f000e0400141da031010403180c0095003000000044219000a4800032041d1188a9015603854101c01c3c82005c22090040208590040f03160300c941c0e0480781031990b60800c86a40c15024940103000b080b941c0c202813002c3c080c42081400c0360900152440c1c104200861310b04080034201501c1050b01000c5006a5032692103c560145d912840e00c40c0039014000e512002c6030f50b41c1d0b45c0b002e11054402c0700c0c141210032803840c0100070324942e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 363881420 1250 363880170 363880193
    0x1e0f020c07180b091e1005030d0302160f05060a0e060402061605010603060f020d0f0504030c031103090607120e01090f05062109011409010510050f01020f010c0f021009 74
    0x6461465440714080b0028a40c0142001d10589070400b10180902604400129001d200c0341c810410004e0981d4586100325414a400e120303668066000c004001b20207030083e00903021401e80020482d440681c10b8aa40000d40c0c04608140c9d0306070442d50a00c0600b9134580034219883c01d1850040a4500b41503000c070340d20748242296102e424401e501250208442900508011a004202800f100702d215840700002d5004500f98504140b0300f0410856094044c0105840749400d601c0e204600e070a41e0700c1c20f445064485080d01140c0c0001c0001a0a03580d582020742000f501440000301c8107004104d014010340075414843d414040e51110811030305400f64822001d955040e6003880d114055001004c0c540030908071940182101ca0080002c240015440403c10310340c44000000d540d255010071a00700d400603100c3c100f12140c1c008080c460760420b8150741d841100107104440300c0113011250682101c2003071013584000762100580c004250b904000101d04a040360004001d40c81c45592800b00520 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 363882670 1250 363881420 363881429
    0xc100506060415022d0d020118060c11030a02070303143402040603050309030c060f12190504060c0806031b040f0e0d0203030f010b0301061706060d1e0f020c07 70
    0x1244842c0318114800c1c4945120303100b2042001041d0240345c4582e010315a002180c003070300c0c0c3c81920514600300e44140522201c82d88070300c02140508030781d500c03803002601080e01d030780051250000c01070040010410060100d0031850380940546070843c40c006085001061041d0540b0380203200c84000b00c0c815905071004a0003a0b509800180141407404004105134000a98040d18281001050090102c024909048c085043c0c52002c164a802c0090324090000780b01203c2e0f10520102018450120901d40c104189600305a03014661701034450a07103200715000c07902203407a551100070b1141c010700d01c590054011406801d00607186403080122504c4c0102c00e51046440303038100c8000344903d03400186071581004c251101c1404161000c0d68940c000d441c041c45c4000214000140c0c5059102902d060354456070360002c0b2280008600700160704080c086941c044010802900100420301c1000d42d04401e5170409640845101a80011604132810644407180108080c0c02c1c0340c0c2c0080f421070180c1c0d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 363883920 1250 363882670 363882689
    0xc011a0f0d17070311012d05090c0d06020a030b0418030e18090d020c060901050708030601140406030b09090105040b0f04052a030c010e10050f0706020403080c1005060604 75
    0x580075824044058007011081c0070814000107080410301d5441301065030407000c140000d05c1000c1c0301000c40c00410010a15602e17481c0c1001403000f46800302c641042e60031081880c00c030340072410040001007441c1c80403e070445106e41e000926140d80c54240c007603030b012064221810001d40c60760416044a03600018401030420440c400480d840c2d0f42c1e055069008603402c0d940040303c514220916070780d11f507001d42c0e000c1c015201d0b1410031300701440c1042c2102c1100e0f0741a5502e604007510f554134900660005400740b41804042100c14001049a101502c01000c85913804101d0070756020601200c13090141164140c0d0b41440c081002243c4080200d94005a8038540071a0f0360b510750410a0519003428440b1000070901c41d550070340d42030344513106d61000340100d040e107210384150720055403441d1481d548682c03c12000305c0805003690054000c2d010007109020348624114250f5034800c101d0740650030480c0c0040f000f01c1c1046c0000820001602941e19880e020422414100c000030298001c5125210b4038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 363885170 1250 363883920 363883939
    0x314010f170c281d01030b1005061207110d030c031a060f030603120a030b0f040c020c06030c092d0a080c041e05090606010f02030a08040807020f060a03020c011a0f 72
    0x50703d002c41500c00204240003805501001d000f1551082510a00c0705880f016060800f050301004010f5001c012900d0080c1003d01d000c409c0043d403041d04000520b0b0f0380a20002007200c010b004814030055030324510310354002404440e00040542100e00c2c403001e000708403078607044802c8541c843c4002c44d00e140024910307440d241d58400d80000c2c40d0a44446100c0900c00d070210341d080b0355941580052001070800c542d1000f050f02d50f0360030f1000311003400e4a1140140c0c40000c04a83c20705200c4015030f0400d101007011481d01032180c010a04580b018a0443d03800b40c1d6541d0f9150842130403850481d10368500321400c0c10070525280c1c00d55903461060340c4113480b0b65a610600c1034101c1e100d01c0c0c0262401181c0d803090041c2c1c074080320101d442d07031004ca40c01c0b80440c10b1000d24840083c408001c03249204c1d1652141d500f80d8a40380c95420140e08212022608290740700740c0786110313035100c6000d04180141c555000d0ba8170400320304200c0c00c0d00c0030b004030802c0e442000f0102c0f61007981c0d140041107a403030064456246 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 363886420 1250 363885170 363885229
    0x7240204050d0b10060305040506060f0a081b0406061701210204090501021902061e100807260105130609020307093201030503190314010f170c 63
    0xa100350350145034050948008031007000810319600340f00721440362200701038596525080d015980c04850080403600002c00240340d5181503207824400c0700c8007a10350b1f00d07640c1c0c580212030304c1e110516203500d03600c40500d2181403051070240122030240c8854036001c00084609100d910480d0010b000e00b09088008400501c009004007503030019241e0010300900c1450241d040c04e5000358010003014144411120512451600001d2114003a0309060300c54561104852081203000c0c0018200001060b080030001940341802c000d280090180420742d5184041c060340340c4403c220703950120408a03410001003000b2028403502c1c00c030050360041c0001c030391400948002400c0110940015203450304c0c041824803a84100c959480000058090410090060180710a0343c602d0910000709603038000c00031701805096945188140c50403d040214103805a1200c0b00d141e800e00b6088405020420603003000440007500e00c110400420344040c1512040328804074038020400c017000a51150401c14440703 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 363887670 1250 363886420 363886493
    0xa030518061602010e0a0b16020621010807060903050709050903070f0b062706040209061e0d11090a031205041d1f0e070f2703050106060507 62
    0x40304500100441c2c0c1e54500d4802d1140909103100303050b40021224400003100d070030600034890554803844202418101240703040c2c0415400074000700e03007004042c0034210526081308022070052103404c0002c0f020750304000b80903160075039640c4003008210b1001010004588041811030070744242150100b140eaa520091902d1031203403001c024000355143c0c20000503c0015500c203400303030808031a074010b80c1c007440e00310711800201d030003110442001080c0468103c0c5004c2d80140001c1c00081d00301820f02c50480002c18005401d035945041c0e50600041145041080e03204000c0c07142408400307242040360140101c0c0c0c1c1c4101d9404010001c000c031070f0500d0300d503e00800a65005103a125110021503004901441c0340300740c103030348107040840b41882101a444031441c41605640074a42031088507681c11030100d44c1540c10b200401305004080c10048224400581c00120b01e40503075100d200c043c0c0c50b40c50040c2c2124802d070b000350f04002c000d011307143c005106000301310031407820440c071940084d2540c2c4080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 363888920 1250 363887670 363887707
    0x30f020d05060717060109080c0907031103070302120a05091906110a030f0b0a05060a080a090b010602010c080708060a0e04050111160c0506030c04050d03030e1006050f0604080a0305 80
    0x152292040004200003030350301c020624000504640744d14004c0e141e48005448503410340c019030a00740c02c00c011048107810085c007826480045860b0101e111040c2d42c00b111404d074010344146000a40000d07505007100f412070242c130b0b0800e82c0000200664074240d50b54035150003104040401c666018500c034401e10229403c00c403480b84006800e1540c4003200c4002400810003500307040045400c000c0c00301024604240c4034012510090311451901c814800110f8880700010900c400c00303035903126100b0204062051880c060501600009860401d00d9070280121b14014071700820000301c80d0802ca62507c0c1e42c0c1440044891029a0810507190752400d640500700d41c03e600c4420720404608040440c812013a032036000e5020349181010380707842e10700303101081c0320407100d5070f8494504120402c441d0406201900d0490b000e843d001510242400c202d5040c180c541c441140d110740c5072038040c00745103090000020f030080100c804c1481c10b407034120711507240c2d101c0286c040c090000200700640391000403500b1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 363890170 1250 363888920 363888923
    0x2110140d03021e0c09010902070b0c1303050a030503061305010506041206090501050c03040b0705120103200301090303020405030706020303041e050a050303010b0307090801020306031c0306030b0114040b0910030f020d 95
    0x20300c00076890703e86140d659444111150700c190106400021075215510864000307071780091002c40195a9201683d071254080740724211b405030080800008030784184025408248030b0703941d480d40e9081030000c0040384000e25800e02c100340c0c03500c0700402003903584008a90441d201040346807504189420000001c01029070b01426070b50804080007040c007c4407000f1413040703100c0d00503400307692501e4004840710300405c41b0800340d401200c030040c0081544040b2030074011030800700c070059610626000c80d0a407000000100d012980116082c005403400b4001c1d00085c148a2005500f1882c25460f00c0c100b5107038040c407201a0844904004003841000e105d040e01040c2c101e41140c2d80c959450300c1942c0c00b50b0040700c6e40d01c0028942da23404502c0d0141030080700d008003402001081a140800084c40200d0404d18914051568500d000000134509c40d50310f9000740000c201056944024034244000d8070562401188103070742c04420030034080c0544424000f40ca8000311204580c88040c40401d0955600590 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 363891420 1250 363890170 363890203
    0xf021201080a051e0c130e010c0201050106030608010c0903020402070f050703030c02030709061d190c030209030c030a020d1b0b030a05040302010608160918082110140d0302 76
    0x20a8020740010220350091240d0210340d4809681ca540141e400050621403040d030304000e20101c507528101380540e0401740f11450015544030801440c908507070001d9401d00260b51039100400c0030a81500c00c4c0002489810000d01c01c503401c4210082c0401c00c1404000e1241d6070104034807050104404400c501280d100c811113500703d481e030401038040450000128801e1080175000b003158035150042004440040000c1812690000c50b0440311050040455503400380c0f013041021034000034083d4110091140d14010303509d171090300501d820702900300c201134040d5002d000041c0042c0c84080e07808003000e8003c60072550000c602101029500c10310350024541400120030b10503000b8182d40128080c1e40f00750001c020301c079034924000d40ca8000c2c0c04001c0ca0f03d0001c10310200070510140d04404240e00c2a0324003402c501d41240e40e00849a000002075203102c62800512402a100010005411203c80f00e08411410b20b0842c5008c00a00c00c0311505000b80c0c88080d9410030907008104c0e071402c210f071100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 363892670 1250 363891420 363891457
    0x1e0103050a2d050915062107060c0b0901020301050303091e040f0b0306090109020603061c0803010b1e0306100f0216180c1d0d020a03080d020d05070e0d060f02 70
    0x246074082e03a002400c0000d07440c0c40c10011410342e9400242ca100e0081010041009035503c3d03204000d44100f0f08a5080041015020700c4a080c4001344103d101500150701d440511100c80d0416440303160008080c4070389a881040180050394000081c4da06440c400c948003050710700c2207103c2d4402d00344840d02068015041c0b446a14515003a5000381e20042c905070201c580e903558100c5918203917072080e40003135002002000440c5450030100307006a0941018140412458020303a5111100c0d4000d81c4420150000451405c2d00a0301c042215140c10f0602c416040c01d60500c00d0005987d038800401d0b00092247c2d0301d0001070014000e0042da2144441100d503031183d1562083d10801070000c880d50f011583e4a0b24006d0a00140240c03111268a51112004441c50045909000070f460040c41c040e070740184003100000000712104001c0c10b045010480158440c1810043c10b000ea400c0079080740306004541e0080102c580396564103220709600800301048503240c07214028001d1180d540900d480031b40c0c10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 363893920 1250 363892670 363892721
    0x11090306011e030b0c0910030c0f0302032716050a0b0d051b1b07061814030a020d06021201060c02221805030c0c0105030c0a232101051e0103050a 64
    0x203001000c1080c7c8100c41c0804440c0c20890855000b070358400d02003a420280303008580d20070b5003d9035121185149040c401c07603082e80030502d000c4180114540076448070a200c001c92850800640003001c0030341c2d102c19400e0800142d201180503d0040498081e83c80001a9681011018001101c00c0f085415503541032030605a42c3c1c08007050742c81d20f0b500d224004001407400d10489414050205c0d0308c00c01c000d902d041800350351054050600035945481000300c08009691240070350703c6200d105440040e40c41960100c2e40315120710585c01801030014000d01c05005d07848409010420f005149031000a40e10074600401c01001001a60104010715003240c40c20004000000c1c10178400d1541103401e084100340044031b0520040314020303031666003406020f090380d01804010b9a9040d4101510034244a103003103410980d00076070300d0740f600c125084825013551401c0d510000e000d004142c03642c43c0010311406071942c07641490101030381056030307400c00540e1030304403a4402442d05110b84100700c00c80020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 363895170 1250 363893920 363893941
    0xa12050402030106270507050405011d130c080a0509030415030e0f0f0a0302010e070303140d0204051503191103061e100f020d030b130b0d1a01060311090306011e030b 73
    0x10401d600003446d182c4404078020900038810703a000c07524160360b2441041c6803407500d084601d00da0a401070b0442002c13982c0c02604039480c0a40240c086c842d07a6140d5041c0b6012207900b041c2d0350050031310001e64200b04001d00c014240d003192040651410b09001c10300c050000b2001b40740c422510118400c5014240610350141c2020400d03242c040d00076030007130200c400c1d0b19240c0363325030300d903840003d000c105081842e80b00042d40c800580001c0d4401d8000504180d50743c0080f400340300300e4030780d80d043e5004000208508051035900394828031401700000c21030100e03509440c13109440040c110620951480c0e8136101c1c207a0300c0303030303403035001d4071005446c903909500b151602410403191808894098020814a2107900c0d1081c407900780c00190007001215118608100c843c001e01c01540041e030001c120040381404200f1008a1041054012581c7c8040750b02d0080c0050407103441620084e0359a104000c10001994006812030540303000b400030548240c03c0d0a0b060b00d1100e03843d80b0040100e40f4110030000700000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 363896420 1250 363895170 363895229
    0xc0f060f0a1d0a02091902161a1b131e080c03150103110a051c020310020f030109020c0a0b0907140a0b031317130f0504020a12050402030106 62
    0x1081c1105100910320b080145484105a40805840c2d034402c11014000d40b908032252a0440342259001080c0741c4112803180507030b4803449441c0c0c840020402e030380c01041146804450b6a1030320b0121f049490a06072000f402600170300f121003001c91400704950200380002c0b040740c0024007d01071030009418002c4070024051780c42d807050307150340c1c000c19403100c1031400c0c08141413908030350402900546030300715a103201e288401a501c01340c124860305004581902c414454a0070026291020102004144101031810811001406410340148041c01004025405990544444c000301580302c07618810140d19020f9100f00c060001038002d024881d0124000c20600c06407880015180000500070051003407031030780c0f4801c000303008800300300065440e4101040c04200d544601845201c400c03190141814582180301444186651500c0404c0b8500d080d4601600405003542c085d4145640c0010160130444801c17005180952201d0002d03085607400c2d400080500b000d86407032008204000080d807482032 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 363897670 1250 363896420 363896431
    0x604060c0c0b0a0203300705130504060b07020904060b0a030812010b07020d0204050403230a08100b03010b0d0e0d03050906060306011406070614090a050d080f06060c0f060f 76
    0x12011900840c0d0004020119800c8110f19002180f5140b405010b0100c0c140180a0242e007a10320300c815140c0d00404d61015170b0080c00c8581c0c60585070f0007022006403900e00d5540c400740c0308034030f011001c0141034044029600125012501510386c1e543ea030401201410981c41e1241e4001040c003808410440c50001400b03a8039601d54104565a88a8502142c28403807428042e6000351103071402801440d0640003641e1151081c6004071542141611101c80b01080c1580c203800c950002c90305a07005a44034540c958401400c6c0c00307003004580352482c0c0c104903210600030f400080780002001303108481c031500700c01070030350525003128040c5c42000c000a0042174180c440c500782d0300442e40811070b03030300e40003544606980703584809000b9070702e000d410072105030700154003103c129884071902451000d441d0542c6218501e8000a80301006d11854581e081581403450102030007910810300000c0100000301650080c01030701c013165a00c006c11219032401d0b18080c2410554800d100c20040d150851080060080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 363898920 1250 363897670 363897683
    0xf030308010614071101020a150f1103012321060402011709070b09040b041a03070e0c12061219020f03070b1918080c030d0f050304200604060c 63
    0x10307620b88808580c0d00800c0a003800d1010400c0c4020004600c000e60071000048050045880c151959030b035035111a800440740c407554503580e005131143c5407124010348030707660f4200750100d185605000514540454450403110680001d05c680c0c401c0b1740303600c0c40b480910700c524080d0501480840c2c3c1007035035520040b6800c80c00030f441c00040160040c01c1c40d504500900500b170160040d5030604842c030103550066071029502c0741d01c0e4480d400040e1158803c000740a01c614010440e004109418540b500040f84d1003c981191303454100801c0090711001d9464660802c21902010703280c500005040108203121003015000b060140c000301e04888161010aa201b80d40200a0705c0110080588038030322842003448421040184102005000e041d4460103c1c030b501b0503101c0500b550a414050038a02c4d0032151441d480801c88078064602000b2895901c000752400c4241d50010801c001c1003400040e1000302500040c004452943c001503100c070102d00c10142c80c1c56143c87e40c51074001c02c441051081540c45 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 363900170 1250 363898920 363898937
    0xb0c0703112b03180e010305190f06091a0118110a0e0f2b0302100209010914010306080f070603060b0f2a100c020625110f070f0303 58
    0x798100249907220036440701c0300040440039000c02c0440003003820301c0103c2c10804e40151000c0c20540340b29011020b442a22000200c1e076043d0f1402c186070000c40001902442c000d4900d10000842c040c141c044455400807000c62102c5031840c04001c001d041c0d81c00310441b0b5501c4000031a03460162503451801c51403480c01070120611300404214188980307030301900000c0c0e000346207680c0d030705192103400b0b40380c24050940081c00b02462483c2402859409000350440320380c0111000b819810450580b80d00c118440c11841d203182d40d000604510b403284205c00c0c2c0014032140500e0141e0195006400070b11a203400da0f5a018141205951500124025000400d151900c040340803a50340d4242e0b001c580c1e00210362490280d00d45504120b10340c941c1848441c002018291407120b90040c403071500d505044450100c3d1040d50b406010f030405a008108242e000c0307502884118401d07008080a64442480c02c2c203214503042e1140490920304444000c400d82d10400c071000510f1400000c009049034020740d508040c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 363901420 1250 363900170 363900203
    0x616020405070e031b06042106020408060f0a020909060909011503030e101e030e0703060e010504060506040b010f05130f0b0a1106072f06070809060117030d150b0c0703 74
    0xf0307821748212900d034000e4018001132010240030b1114522610001022041d00340c01980d80601782c3c2d00541010103d40c002c036060050002c41030030b84a401488880c01503041c011600003003201f03017200601c928419440200800d020a20a40c4130516021070303494100340042d200c1c00c02404003158024024001e00c068014840e080384603025024036a00c1038a290b03c01c0c4040008110003802c0380200c408101d0040036000800103406100342d55060400c4000490b20b4641381c00d04108541000700000d02483c1803030302428142e80c0c068882d038080d001b41c1c00c0160b1070303071030130010b0014145550300945414a0340c00c0000c180c1c070351100d000d072113140304540ea06a145118001119200c2a080c2c0d00b61001c1151110100409d810b8161454031019855803441c00178403a428105143c00c0d4151740c440045010744050100c01da80c00d010039030140009080c1003211460b000101540d17403140940403000d8580d182d8002d001c00251205480003491281072464642007812000b64540c40244412a18100034400c9030a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 363902670 1250 363901420 363901453
    0x20a05040c02030412030e030703110a050607020102150a230a0c0509101101141510091d0402040209040504050d020c030a030f120609180506010b030c090616020405070e03 75
    0x70305040d0103034051400d2500e405010341c5001400301c4218180900716600c0c64203501c0070414070005500880d40d01c4540b0411009115540740d43e0381001d401818104440f80150340c001900c00022035103d80d40190b680d8411400030000c0500c0d1104e00403003076141c1a0713028804c803030b80710b6503001d00d682e18010025181c82000a5525115898000b034002080300009503000340074041009002600400104000d40c100708045880802200c1030400c0d400c152618904500b00624020071500c00303420480d030a2800c100c10320400304011203940000c03040020000d0110744a6030180d0740d0300c1c64054024441d500303003403801c03649400040710b2200c018414039950440740d2400145882c01a60540c540d07501c0c03031002c008121850f004007031902110613140e000c002040c5c14540b02d0307413007d9503070541200195030f490729180e401d0100691180500000a00904ca442000a400c5680c0701d6021180907a031504650100720304a2580c82020358024034190400003c107812000c0881214002c5094840000c480c94242 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 363903920 1250 363902670 363902681
    0x60f1805180c06030a090b0a060303020c0111121c020304030906080f0708130302012d110408060105102102122d091504060204060207060c080a0e0a030204020d0603020a0504 76
    0x4a4a501c00042d2125a09040000715044241c055012031501d40702d0301e44442c014815078060048569a040070800e0681c1030205102070f00007460101e0034403540c0603159a07940040080341c550325000041d0290801090000101c00c02c4030b5000039500d9242904028003411414441d12000c02e05100004591851103030049114103400d40b40c105650b15141460303019070101c904110155940d403601a4400300c00c107844580c1c00003140b81d0f003c20a070083c00c0c103c800e64044484002031031206200c10300c0004008103a06043d03a9060301c0c107440c01c100d094400c03144100198040d422120011180e540c1c0c0003a250010202c03588040200f041030384441440700341c074001d504e005904501400a030078503407110f00b041642d003045031b0904441d07030340a5040a00240300c505940840e002a40020100320036601072143d00c0050400e82070841c40e46080e1380340c2e03082c64811107c580c0100461484081d103103540c0c403115140a190046d2085481710020b0b08848000c20271400140d115002d406000035480c44e1a0161 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 363905170 1250 363903920 363903961
    0xb19032c06070e031c142a0c01020136080c01090302190305090f0a1701020c0d0903050d0f02011b2601060e1908010c090e07050f04030b0901060f1805 66
    0x1035108a511792402c07205042e0b0210300c8a0102020003805000040b00310a001c002d15401400d2486040040500b03403400308400701c414156410042d0200d0500c414032000b00754415a1104040c0c0c82948011051001c1b01c0c1810042c01e015000c42c1801d00c8490542c0002e040c14402c0d000c60302883c1c4952200f444980307110000600058040281138028184511502c85100001d0088601180c5520030340c42d00d42c01503002e0581a03940030424a050010030880ba01d1200d00a00300311000a00395115207496008010f104414000e0004a01d05098800d50040d00342940e0700b020002114140500100188651180c4122451031402c09141c542e44084545048071900e40b9013203000c1503014148004440060545c100041040e180025948020302803001403210301e0f590340a05608007001c0a10165018140d00c04220080c003000d651040d26804403000d680d00151407030a2543d0350445d9a0141c8015088600c51044075100000d03506400f0368081c400a19000f414003442d80c40116515840c0f100500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 363906420 1250 363905170 363905203
    0x4290601050d1407050a03060b0a020a140a05150a0c020d02100903020a0b0f09070e19050a0b031002181215090a170703090b19032c06070e03 62
    0x119a4940c007a00040c041001c0b55a800b040511412083d11a5a041141c2e081c0215a00060101102da07040c460f0070042c00381035402500704640c3c1c940c020766804190800400a26100001170a110420007c108816071b100c022a0000602481c1d002c00b580000d45040d0089810103a11543c02400414034244000d400e900400203064083c0004010740a0284140c0c158002e43d202c0802080c01a21514850340c88840010711030308001165030b00c3c001603940407040142805007400a60801c0015846200310000f10100e29501d0310341c1c0060040c0b40c1e04540560520a2540c2c94042c49540d80181400e0150b20003005200103800007030007000c180d00130310300700c0c0ba80280070000340309010b11b410240c111070000c04a87c0007950b280d485180070010b1a030001981030002c2441020141d01202074400380ca0076841007400c0404a414000c200741150303d0080516440d003404da0319010342d07509a100d040304190000400c00c1e184580030b03078031004140d4006c00020740c8110300c280241000a001002e1401052 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 363907670 1250 363906420 363906503
    0x20d0e0d08041211030d022101030f02240a020d020d090501080f090102091005041a090f0d0303020f0d0204090b01020703020a060f0c0213020a0305150a05010c020f031504 75
    0x7070716801071100c140b41940c28004580c0c40c022030350070100061310400f00080c0c0300690b03c00d00160a110030525680c0380b0386c0c8231000d490040c00003401040130550400d0341034842c0b241256902000860090b00c2d00160088080041152000a680003c00843e01036894003660b0396052403003003c4400c2e415070300070640802d8008001c1000710b144901025800035080c1c1c001802c11a1803000100d084541d540050b00044001c14148001014443c2c10b0b00720010200149142c6010750340800c841c1c1264801e00c40c42240035080102c10325020b601141d05591400040b180e6078441202c0c198000d40060060f04203041c174110b540001175000040d02e0003a69001025040c20754984007040b01c0704d00d6a49070420030403900c545010b0040e244d040c07000608010100001d030f01c1702e0031604002d080b254000d02410281c02c10380ba403280385451b1451008141ca100786021000300d14540042411440d4007a10310350940b08403940c1d804951740c0e1039031042c041d40c4107004078011405e028032080620005164084065403074076 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 363908920 1250 363907670 363907673
    0x90405011a07030c0203011d06041203050f13021f090801050604090308061c120504080c150406030c17090606030d0f09150e0a06230c030a03050c040305030a03020d0e0d0804 76
    0xe003040c0400d548014000305002c0070b0b6900c0788e12003505001100601ea03100005010401810b001100d90b80c4e80207140800c05480c10000c409842c0c0009400160700010341000e00081d5140c0381050a81c80c0e43c28010301e0399030031341c0c0c84008155001b148544022940f90402250341e61416000ea1140d00c4d42503a00c03102e0311b4030340c041040007804100d11540c120b0150500e0030700020b07000309130018240e9025141c0d207480303a00d007002e01030415502102c2c89201c2c0c1c400d282000080c441d00c01c140c50541c0c40070b00d000a01902c1c0d101096411040100c10014024112410071010460020f4801c0c82140143d040d43c441c90209074013078494112400c00b0300085074640c00c040c441600e451400039004416031402d4012608040c0c041481b14410340c00170380004c1c1c0d0361001840e101100d014966214081b0000032443d040040020586034021f06584c0402c26888138049040110850305440146402006480e41c0f10200203000c2e000798443c580d07032025541040103203c2180c80120b804498454282c8882c04903a40c0c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 363910170 1250 363908920 363908927
    0x41d030a0917100b0a08011406330a02010617030705010c080f010b0304020f0907030b09090f0601090b040207170403030f0903050a0f060f090308010e0903041820030c090405011a0703 80
    0x2c01240f150400410140011903420234014034241104821040703669003410f00c14010020a000c856050940d402d52001440b40042c3d44185500c02031007418644804c1c64541c120701401c907076448080445110440c41340a03100200c000c040c1207201e04001c00544c00b50b41000d03908400103d07a0041d27108650801040105d0080e0000c40e4014030003010302030b0031609840004c0d034008094030300100080d030383c801c00681820000401e07900170000320024040c0301c420b1016142d59000c14020080c010380c1b291490400c64403a501074410440d40144002010141c03c040c4d0f01d003030f40081c403045c0d00056684800301c813042d0240003100b05aa4028024080041058a13944e100c40040342007180d040782c1d1200c510205540c54440d40c040c00d4401e550300035955240404100c1000000360540c001034100b040200300d0440d40064900c0104038003600440c0440b80760b0002050040258200221800000200003917000350030000e00c40320504850130009a41c840c401c40c80b001c0d0380d4048103480760380c0810182020a00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 363911420 1250 363910170 363910181
    0x20a030906060e090d020102092b08040806090d03091a460203070519140a0504050102060901060602030a030b0a0b0708070201120c0206070509041d030a091710 70
    0x558280859450a159a14011140d2070390100701581140c40a010503802e00340240c0000401030710082d403c2c890503900080408540c00b9054200b1240668202d085448412400a84a400c41581e6449660340d2207407640b920400c0f55141c0060040207002920131780280315841030b450700140604503044414241850909026011200d03480300b03002140601590340f4480c210000651180d1814051040504407030000d0b40c52848034018018400c21140c154418152010074502d0591041c1c010004082980c1101eaa090322114442002a01510a0350044001c0c0300710388003a82203400c00c0d40c50701d0145089518a000b20030040e0401c1000b80c2000344030360000c500d6034400600014501c0e60307801c00c0c400342c0c2d800481c0840c0c4012010485030306540c0c004a811110000d240340074040b031a49109c0003034440c0401040c103424072901046003034403600ca9500c2800034180341a4904d03001c024812145030341e904603004441c0020610301e8045122100028038458840c0c2c4034004002e0a0481c982c2c0102030f12 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 363912670 1250 363911420 363911437
    0x206060111031603020c0310020708030c0a120c020a0b0606270a050415031208010e0a02030c091801152303060111100207200f01181a030108060a1103070302 69
    0x4424003850f401210040780040f010b5210743c0003401c40759040c04c14107040c20f00c2d641c8420b100d98410700158000c03d480074200c87e8001038000d681c3d6a01d00c0c003076805458104075040000940d03464003100d0321001c0d40005141d41458004c8a071800c16564500820074184500640c104888a040c0b20145e20b008603044401481c410046ca030725030f110740318008241207a1a400701d504800300c221008201f40900c02426024006c041c0c030b0300316a15814044d84c1c5006000161000b8601c940c000300264200e42d003c41612200c6c040140740040d5020700e01c08801e5828420b004c0ca11a0b82c9402c00345404850003490030b1440c0100b8289080040d9103985555506500b0090645041c480c08044c1200b4004042c00080b1100001e448010707207807006130500003803254000e0b45203024242008120050741c0c0d61402e9142901d0000d01e040020f0710020509040010201d600030001e03040c400202401c03600c903a0000c1d5050b80c0d4280211607055484031000360644031101070125000400300041100507201c0e8004000c8071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 363913920 1250 363912670 363912673
    0x11d010b0702061b0715120b030a0305190c02150711190e0903070b07021c0e0a0e07031103150f03160b0a050c0601060e12010504020a06030e010e07080307020a0f060206060111 77
    0x5c0da074a03010310f07000355403110010b4000382000c1d101401842251041c0c001181d01540241851003842ea8094403c0c0304051a8994000d0369206849000d8400c0303c41e0743e80306038054001149120b00c1c0301d015a89400a03a021109600c81394001415400c100040c001d185d1121050031110390b25150908001c0c41000d000d690b01404100040c60102e924141c54a0055100c1d03030080c00a503501a0039215034191112a6170100040c00001d45440d0ba6110461000e031900824011250344600b10103800400c00340340700702d440c0d95000c81080000c0120f04004440f480c0190786070100440da100800da00c603602d500c0143d217010454913051111a180f480907040520349814218601040f0115040c13a10b8801d900c682c0c006650380c0070b48011030510075900002030300f1040c001e01841c10a0360001348451903078000c1da400c250341d4000000c1401c40941001840030000c1090300c400340d8441120b10f0b1698440da000703a00500d107160001501038040d94020003220b036558080e000380d44481e40111003440c0c0b844070300d0005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 363915170 1250 363913920 363913933
    0x90615030c090607080a0e60041a030108060411010c0501050406050403120c021b130603060b2e2d0c02090109060605030604020702030a0506011d010b0702061b 70
    0x10700305d90024841981036480c2ea01c1c200b5411001c028207219455030701002074064034604c02000c480e80600c1d04106032000d4032407055500da4025110342c01c200b00600d8110000401c000c12100f42186d00410a603510507484134000281d007488100944820f115a10182d8448400280454581f50203e034540c00140340140d40c40d5016202e907400c3d41c2e4280d40035610340e07555006000c02c16401c28041c8802071a0440148400c20341508040cbd01c5507440156580340c013050340c040590070391311040d4890015800140070000c140d12400c3c050010319100c24414051651407031250094420320203044c80394030300020f450454025200d400c44403005042c00c004896494126000c02c505540300d800d0380c0c01c1c015680c0d40c0407030340d1060040000400040e409004101d28000e0203115069003d000c0302d5008006607009a03a810381c2d440460310b0540202c0c03001e401400b0360300003c5442d24a9400031590542001080318550743c8440c601c0d0143c1c80b9801f8001e41c0a003040081b0346000380d05d820001b00114078041950745 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 363916420 1250 363915170 363915173
    0x1a09031203040c150804050d0305150607030206220b22081c05070810060e06070b280b01080403030b040f0c020c0a090b060f0d06080102040b040302090615030c090607 73
    0x8503082503400302c1d5032000050f0700380680f103881103204412141c0341c985401d1508068030b81648407000450441e04240c1c0f61070010b503070340104854010780e01e4006040d4036500d14040c140251203100699035100316161000130300950074a01302d03c014005801c88030708445520b6801d06800c44403507981e0071000b100100000700003c205c142c030207000178101520301030981c140f028103914103d68000313240c0018801c400d0144528885280035410a94a040c14034a440207400000138615003d00c0c030004010003641c50400025107030901900700c2c0070305e20610700030b015000d82c8501d509407142c0c00c4944c1e000401c05400113000c21700c03c0e00200001540504002541103c00d0f005105462003291800c01680c0035a45072655030074a003206a00500c2050f1003001350072907040000e00a841040c4c58550125004520201890140e81c0102c00500d100340027103503195039459882344190450320099200c0c10990300000c80703d01b0802c00d4440c2e03000c4a100d0350351960303a0702c40c41b5045641005842c2c7d50480e805015120 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 363917670 1250 363916420 363916453
    0x1005030709031e031701080c040e0c060d090314071104090f0219050f040b06040303031d1c0305090f100c03060e010e0f06011b021c150603051002041a0903 68
    0x343c0c003108401d00480b001e012403d0103854010750f11503160814200300c004101d005008901d5540540044034003185030f5a0450429141c032070541d0400354000c00003c0ca038400803015900c0742c0c101c01e100b61204002c1c255210100d103110b000320344001d84a0850240c0001d00780c58264405191188030b200c5152204506401141c500c4a40004c00107500d25400c90503c080d250590101601440c111018011420b81c900440d409008a12008040c1a222044104c10071511240b40e80704000d54411200c50f90615440140d25900701003000c00030074030302400f081c00410041001c402c1e110049d402003010360f00e031000c100b000b4401040c0701c0341015518800411032003d264044d60003441400100459030420740c03418182e00e000508558180310302c0030300099000040000c4183c43d95011502d80e40c050082da1240e00c00304204000080500d4a908001066410740da801981540e0040c2c0480c2c90900a0100c1141284a00c0c02141161904a040d6080550921004040341c81c00a0180d50001c04400e4490 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 363918920 1250 363917670 363917693
    0x1110320708100305030f1b030a0306090b0603240a09110306040c020a050706050904061508180d1403041b0f080c0406051507050f0f0307031409100503070903 69
    0x120805000414840308a501028080c0c202041c07108038400a40b030360f5206603403842910131260000c1d101080004543d110086281c6000d1445d0040d40c0c0c0d56144844028001c101d6400b030008003614011010516003055010380b0700c90350300d0104441c1d12103040c2e0038242c2c407003400700c13082d640c801c695060201c0c5c1040240210300000000301001e68590600004101c1030341c4103200c0d0340045600c032a01800103d2000a40c00c0c084a44a040440e9619410070106010305415040b03e8120501c986030091070951000c0014424020114440804c903030412205448594001c0004006494030100c640f41d64007030401550480d200f8601c004a02c140e9000c0f4030f0034207031154090b418094001800704400348061080300f06240040b5810402c8500303080000e03603410b5042e002240e12401c080b03038140400000b00180000181280e04580780c407003e040c0d0155032603010180440011314140703030324203280306210183c038024600100b41c022003920b41901241c854200810400400114035000004600d0f03605c00d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 363920170 1250 363918920 363919001
    0x91807060e030f120f071406010312081e0a021c09141002030606030a0e010e161d0112022e0f1121030c0403021201051005011110 57
    0x8a000040d401c4040506140c0030260124968010005420f416403541c0104c0320035a1000708155244c44d02402c0c0001c4050381d4880c82500c61080b0300001c0705000e41c46601c6184001607607110b280c00c0d601e4440f0701c640c1941d01528241c11089110220711854030f03540241014546001c0c6c0c010024020b40d00c000c0c191040400b065911a01c6480c1d0384444275000d00c100340004002030000c0d0328500302400400c14503c8014031300e041082c0d940740501e401007030a401c8100c0030074001e41180e100d001440c0200720045140d11a0807040c1d84103601c1e005c0c2d02a44100510b048800e0700c02900700c041c280d40c09222107885129581c514041640c0c3d43c4060512482178010090615a500d42c40b4950107030401a1440f00c035140307248140d900c40c80750f074480700400380702c41c038191380d20040000e44a0b00ea186254040d0700540c0c100a50084c04103a050b1462a0150b01c0300d403003140307a009840780607a41c03840155006c52a078104403150b6000790000b0100648240c210801c0c0d0032581e00ca1040200240c0051a10144604030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 363921420 1250 363920170 363920177
    0xf09020316050108130302060403082e091b0509060c0c15030a140c0d0f02040503030d0b041802061608120702031902070b0a1b050307050f060112020a030209180706 72
    0x18041941d010403200d50080c038020340145d54400540f000382d501d000013000103040289150000369001380060103121000380c03a100e0410450b200c00d02c01e40000c40036000d40b034040d034900000c040071041d4403000d01703506a19684401d0f1030103088a040c845154004c040118440c49180311003c666181c02c020810318118540b00c441c0c89040160482003620100498401c941c585074051000c0d03003a1080407070302c0161070703080c002504031208807075480039010b0360348495030501012a4031080c12241e038100310043c4008407000c10007a00c522031106294928070002070f402c10001d200701400e02606040c1042e4650040b0726080c02c05000c29480700034070804a6415005800101e00200601d44135070303c481d400d0100d40081c00010b810036840d1a02070141300e200070b080140d400c803814202d01c0b011540c68106e03230f0000d0035207903244200e003001070f83c40306580100d14003840f801000040c103941d03118101124503401405201924615000c1046000024140c0d0b034105028a003900c1c600038003000800e006124544 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 363922670 1250 363921420 363921463
    0x6020303040606080a03080106030b0a090e03040e181f060305030a120c090e15010c020a080f06010b0703051603032901110a0809090403050d09050616030213090f090203 74
    0x180010645005500c100a15030204071781200180c2c01010050641c1c04a00e000107214602c40001540c2480c5540244011458088a1003001d40003200400c2034a050201254603522194103505e606110320803100c842c1c2d00084d45158401070101200d0700d0190021101081da142c59490b85400d45d0f000756080800705007909480e1328110558082d410900003982002d520309464091788140005004114011035841940010400c0e800f51031899002c94024000024061702d40c621a6030300e22805000c403403188194000011542419001c44100c1039040c1c2d9001e0a002c004ac0254042003c6214210285611102c0f480740d0810000400042503809029500c0d1801c4107000142c01d0780c0d1010401c5c034442d000741c00d0035004100c201301140d01c0c3d080c06648600c190b903500d0604035880c1c0240040001e4132420042c3d030318240400042d041e8020740c2d2100c010200c14023400d8068003284a00240c3c060850242c503c1040320348081d91041611541c12140812406c1c0a81c0c000703414603a10441e641400c040d040c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 363923920 1250 363922670 363922673
    0x80d020d090e0609040206031918020102010b03060106021f0608060a090c0506040f0e090a0b07260103020d24061d180a062304200a0b040e1f0602030304 67
    0x101e80c11000301206141403180c1c0c00c005002c039a0410009201a0240f440000811b4030801200135584000b03a000c0d20420401e030700040e520b45940e02e1542d05a0040d0b003800c0f02d940d01c07403030b0109500e03041f21003540081c982c12205d84460120f0301007140300100780e25a50f5800181288090040610616414100058421051828611a03003140e00418000c0c1000d000900c03800c0700f0783d51003c068600c1d2080d4207030706555281e903151400c0c991240003440000000d0031300110ba80c20003400402d010300c030003128104440c03081010302c00d00d20902c006548903d40c0a0003d0100d18040882d2009a514041005514565840a5003900e14a078070070840540c101450450151c040d5517640e400c42c0505880c0201c81c0c1c03050b070f009503650884104c060301c0107a895142c8800d422108403840008068002d422a45280606141e804240d00c00e11a000d0303001c00701311000b02440d04107440c0080c0d8800428030360420b0b0030710380440071a0100034001c508030744140032905c0c000004003540301c009000036401182c0d0b0b0b1501c3d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 363925170 1250 363923920 363923927
    0x61a100f09080705010207050411070f0f0b010b031303031a060c100515010e01111f02121f2106020304060605030d0504050d03031119260108070618080d020d 69
    0xb5480020b050b0007411080c043c43c3c0e80850301c981212401c80f4040f4010034030f10100b00303091041980090038158440c04100030400c850070b500d46805d002c0c1400051036a690090b1002d10b2000b2524071003070001c0001d2020009000ba0f215680042c0611900b1010310200340114031a1f0b40083e5010810354491001c461280c4028080c03a5408a803030310766504200c0500c8000703455505501401414030a00b01c0104801a000b00511041401c0c007000c11b1490400590f08c20000b50f205450041400c44010001180e600f0315813901201c1c0060b805084d0350062814101c20f949901f085002c94401c803140b55890041111800a180286d0061100040b1140b82c4400c041c0703894021044032003402003c2c07200704201d0780c40d03001390f8082a41508010030500d4205110740c21901c1003210550200300400000c2c8007485e807042040c548541015145080190114a000c64100e400d10403400c281d0322807101800380d5446088440450720083c0d402c104215207442c141420891140302110041c0e02c0507001c611541d50 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 363926420 1250 363925170 363925187
    0x6040809100c0b0103020114120411040e0309090606030c0408030705010c020c010c0309141219060f022a01020c030415090603050702030a110c0307090f0e0712061a100f 74
    0x121420505400c0881c1d03540c824450300c3c14070010f41448906010951101200e0007103469158981c082d101541c45c0c2464903050100d682d400181c011842d05200801c5410008215105560003c202c070165a441008005659100030450f0505540c240310015250700100090720701c3d24481d07000880c0742410400024581020300b6a0b43d8100f000300c00e000e201182c2c104040e001a6451244003402e40302c6c4203030214a01c0702c0407076456031091042400c40468a11074000c5141c0b5a0f03c070350b07028007400080c81684800d86c02059009007903440761000c2e034a028074032a1091709040785140005810b1005621b080c40c1150400d80c080c0c660312600051001a180d40700c1c03c640040c1c550703401d0400040c00e012100959a018141204003400514480742c0d034409c0040000c602d00d084000c0031120701c03a03180c00f240c00281000c1c80e0140381c0c1505000121903620070110389901038401c02003090000c1c100c00d84441014100d80b0b5008001c580f441c000340202c6032100320500d80820035680b1421b21400400300f0042c40c101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 363927670 1250 363926420 363926449
    0x140a0f0219051f030b06030f040506011a0f03060418080c06011208040509042a26060c0a0e040204030c0311030d090b0c030d0608070503151012110306040809 69
    0x2141c20205100319502c0180d24804103645034a40303031901d40112415001001c440ca4100c0e40040044200441c1a0a8540c1e0903c5103102d1001d031203403031745d88004540b1802402c018038110003005004020500c001e450146030310840003040412501c0301240960703400348006406440818000174483c0741c40c102048100c3c01001400d03021404100c590711580c42c0d0f070042d40a82c521850320600403609000c03500010345584102d142d003005490f121424000c41c41c61543c031400c24000140c0c011054525448403512680f43d030901c000d083d1580d0340d200c03a034005a00c14001c1c801800b5002601ea0080d44441c40a803010354482e5851a00b40f50540c10310740c900c05c0f04188414400e03031180c08281e480c50f900c880c0010450340703000499600c94000f0200142180112480714024520305100014100c03000100042101d40582c191190110b22040000c082401111a0000404030344c0040210384010710701c94083c94007940c0c1e01d040103035603440000c1c02e28009603000e44440fa004100c1400500c4c01e078034502d5180 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 363928920 1250 363927670 363927709
    0xc1e010f09030b06130e010e0c01090501020a02091614190e120c01080a140406150506030106270801050a1406030d0c11010c050a0f1b0b090d140a0f02 66
    0x2079195a8602c01c0c03080e4020700c003038020640c0c1024490361035083d4110322000090b081c020b002100c14100039964602080000078001b03050800001070550002c00c10b6407091340c000d00050300c1c9598903030740158508540000142007020022841d0300c40700000d0040e2012099400031121040b00c00300c802032003128054403262148807148407144c0c44032000a40b0501080c4c0c207090116165a030303045101c0c000c0c408607070b20305100b80e9003004200c00c018041d4070102440b40600e17002d000083d203440c18080d6501090041d94041201e0402c06503c1030b10074407401c42100d141c00400c40b83c143d00e03100f489003034450540c3d04801d543d8072910724404010414240c00d520002c20742c010494088009c800500c0345108c0c0901900300d2000c98551078042c2d1140004803541c0760040125076802c0340601d044c202b22110403d040e9aa58520b107240b032805c62540d102e600031104540300390f5060082c0b410403c501c840c6040fa080700c4440c0075072030b41c161801c01800158841c0c0e00690180800d0085401484440c40d29610070b207003207 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 363930170 1250 363928920 363928937
    0x80a05060a060815060319060212090d170c04050406060503150402180103020319060602030705060a0504020d02120a05060a06050f1c14010f11030a0f0c051b0c1e010f 73
    0xca000124842c50b03a00707040c2254140e46840c0080380c205481c079407448414404511f102014005503400501c004884010b0212040d0360b0510120f460382000300e1210009082d81d82091400d0740c0c00303034aa582060b100d00039645451340d100001000c86145510440c01304401000308a1110040d00c46221901c4080e201545410011032b4041d4141d0482c03202607042c95808008202d04040106406401c200d81c440108501c0c0d494075000703035580d00408000c840354460301d800507103120300c2400b8680c003555001e08007842aa1141d4200640b6941c048000c01c03080c030410f2481004110208126401120b10080011300d05040c0300030300541c29807000750a80603d1110b807100302d1080074400942d2200750405804809941c0807a031321405007000928100c800c4d41008801400044c1c0704000f540125502c4400f041502c4070401c0781825110aa000c2c64045001030051114140d41c2e512105404d2080300c0607200e12044960000c0c2200030a0440001c2c7c120755061400c603a56040003061a1100042c14001c06 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 363931420 1250 363930170 363930179
    0xb090604031506151d092502010609061409010f0806040f030507050706080712020309060f0603030d0f0606080609040210050901020c09040b01030204140f0a020d0e061302040f020a121503020a080a05060a06 90
    0x8040e4210340582028900749900500c1d41c234401c0d07000e0750181503102024465203603107080b0303914003208000580f803250044c1c10000800c103100300740110032601d882d40600465540e42d00c1e00810504211415801e201c01000444000740d0240100300140c42c2071b032a064101e0401d10750041454a440360140d484a10400c02e1008040740051450b510071100450003006503101d00109040d80550307102d4000f56030800c0c0c050011041513030070a40541d1000d54034140c16594407410405c080100744c034041e40151030f403182040e4242c481c01c0204101e07181801150341c921114404240c0c4e050007140c060303d0640401006004514150181003039046004605e14042c1c2004c030a0f1599401e00071701242c501903400101d076426004103400000902c0050005c2d01c042c0c0ca440d00081d0b060442c50003003244501c0c0381800d008090722403031007960758000b01a43c80310b49200781d0300517401c002c0065600401451440e0200000184e0321364031820701414150740071b40088401c0c0c2ca0302a10380300c0040c0060000714201201800b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 363932670 1250 363931420 363931441
    0x2b05130509100603050108010b031507140c030309010b0402070f11040605030307030e150703140309010f060e1911180a0b1c051b090607150f150b090604031506151d09 73
    0x1007140d500c90400d18900d40754510b09484594400c378105110b07a0000c15000a1000040042c0d880307215003400901c0402501c1d001c0001320310821000034882003c005a10012980e5808603209084000d800003401c5610307800044d245030020442140000d049110502c15030920241031004251006419800c00500f40c1d405850069048400d01c2c40880100c00601e900e1025001200f242c0c0203450204442da48030200f1000b5180100e4182c1070b00b070154002c0440074000340c0705490211200c82c9801c0c0c02c01d00c0307904144001d80581303a100c2e540139001d80c90104500980a00a140150003e4403a020406c0070003008000d40f41c0007441d0070781000001060031011210f80007112004d0710111040340da1b8840600e081015206c9100140092524105007520624011303070041816450a20721a4242561540c08030500c1c4625802070781c21034030600040000540e81b0002d441d405480070804244c054803003405040b4401030681c01000268900349400c502210089900100704007a03850856900d031509000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 363933920 1250 363932670 363932683
    0x403020603010b03130c03030e0117040c120201090905010b03010303080f040b0a2304141b060d27060b1e0d0b090a232b05130509100603050108010b03 66
    0x41c078240c6800000505601c010170140640c042d400b4556085c0d581e140c2c00c1c010300009044034464003040e5900940c0d0100e000c4402c0c8030780306030b0f03105450892480c00d154902c2c14101d52128200d050101048000c1003050203030090314043c0550a4500b82c0f41c0d031460900800144000d01244e41740386105080c807002c60503124189500c8a0804408103409a03203400c4134540095111000b412104100140001c003c400021400c007100002c00310398400c000701080a00103c107400d002a40b1070700800c00d0000300662608030703002d0001120710b0040e41c1210504201034800c09a1011203c0580d5281020719900d02085c2c07580103001c41030560400031243d0b0f008190710b43c1c000c02002e8468400303e03000030400300b420008426015401150b0b4068020700c4480e8100300c01080300851191701500600105e080102980e0380f80744c00440c42c029460a000600569044e4001c1c00543c8801a1151022a5a4642c2a1203034002c8400c503181348016490050001c1c112038042e0003400d02139051910103903941d603002944 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 363935170 1250 363933920 363933929
    0x2191e022a0409060c08072c010c05030a030c0f03020901020a0f21030b120c010503010614160807141930050403061a010c12030e0708030705070b040302060301 70
    0x940264040c0e118420301c414a4044140d00c98141030701c003020402d060b0885000c0c55800d0700d8854440e20b0b40182900d092031218107486280d0265041c0e059005003084100403c0041070410b81c02031441c580311036081d03a00031072104021a40350804100c00550141022144c9002460218107000e1f034580001d4442c40246005041c0b0821100c90205111800340c41c4021001c000416420319a0428400340141c24014095072040362680c201500407000418805c85162050752840e01c3c5a081000a0301c1210b284402d00d000c90b4001c1c444000001c02d0b5448a01600d800388010549485039407810b0b04c0e0401c2e90a07441c91070f9030002c107607400750041c141b800350f0340140c1d208011942c24140c2140e00000811080d01f0030503006035054103000b00f50303007220007030081d0382c0611414401300c01c2040d070307800c046d198040a590000b4440c5651101041140e0300701c817007604031880c010410b003c00488440c07401800b600071100c142c1001526004100b001c01281d00101000c0344081d0500c0e10b19000210f060005105 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 363936420 1250 363935170 363935203
    0xb0f06040f0e0618062e021f11040312020f0d0c05011d03030a020a0c0f06091a06030d03020c16030302060703060602010519150b030405011b0509300102191e02 70
    0x15030141100505520803080300e5140c280060b4006c0c0080000c0d0754211840c281251000c0704981814019540d0081400c2801c541d880c482c44c00e803450392440000540b19103a0303411406151542000001c0074845036000400613a03510340d0018260621500310740315125421921200d160040d645d070600401a02e07070000d42c580005031500100d13031045c1c841400740d003c000e040e078141c180c0d0b403c10000c10381d014206144c0a4030380d000c00039003082c60181070300300c0030307500c0541c994440c40c420b82038140300e40c006103c031811407010740d100300c240e000454406213040d4004401503040b0000300940a98103100b468000c001c02d100030301040c2402d145d2503002e070850215480780142c4401c0c0042c0c00c40f0012913000c00800880e51655070764582410964001c0921142440c08a84140c2c00f140040344158140c0c0e5410500405071109100b4080c180701610018186c440019000004224a080350a2028000d184a19030309030414800910f801094845550452485101452101100d0340e90025041c3c0c0300d000303a1301 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 363937670 1250 363936420 363936439
    0x315060a1409060f04121a0c0f07020402190201091e080409090320011a0d03050313060605060c030301080d11030a0e01120606020102090a05040e0a060b0f06040f0e061806 75
    0xc0200e009403042c3c010701000c90304c2c00540007900c403203581240c3d0361343c42c003a1844c90241042e800c000c000516040d5483c03050010144042000225500024038100344001e00040c40c0c841c8a950040e4a4045843d00e080540d554018000c2846000982144031201412003080300d07100640c5c078800f00b40180c2c024180500e59a40d90b0204140c080c0510400c0c000302034000817000c5515031910b6001e40035540c881c03076060000c0d65421a05081c0203846449080d03042d210f060461307850700c1a9650401684606440c001d071581800101601c0e0480200390405245014591740e41c1002c010303d1402400e45005400c114082201d142c102d1804415503040c21803034908a03222440040040312590782e100660440b031490004001511501540203049454056035410040c80e034513001c0104841d156019030324203030001c1303006c000080e0380341c1e1116a020800414500c1001410001704506170404c0e0445044e90203900f100f0701001d07000c407144540c00001244c80142c01284480070110a281c00b500d11401801201d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 363938920 1250 363937670 363937687
    0xe10050307151214010b030412050f0d090c0e15041505150d15060c031d060d0b0402071a040b01080307120c080c0619060503012a09090c050315060a14 66
    0x140c000d4a500340b1030400d21411175843d4000d004803a803050310102c50380306036045d2580b0a41d003d10284c0d0002e501400035281044034990000001d84000e072011500a140008081405018000d03428094040c800c10345009140c1001031108a62003444035250ba000302403407c0140d955641070204046542580b101d07260344000038101c01410100c0e02d07505040b0300e80000030030080d902c11403101201d400b030b989042d0350804020f40b0b141d218611041c03042c1c100208008600c0000000e802c041000180070f000180f4002194492903e000300c40c2c242c40c038062420344d00307002c00d1160f20f154083c003500644000d9464110f1996411040700d03184a070390300521441c012141e0034071202d00280c2e100f612030002a90090300e8488484801c001511043e880e40a2070504003080c0760405219020380b40d0503020f8224240144100080144102e852400040150700071010a01c84124002c080141e01241c03200c5480b803c06103504080e100e00300300c0d154000c11044c000c0c0c1400b02d5101200c84401a50141400e0740c40319071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 363940170 1250 363938920 363938957
    0x90e1e0a0503070614060f03060703021305030610060206010e070903111309030804051c05040e0604092001090b09030c0405071407240203010303050f03060303130e1005030715 77
    0x4410000c0d00c02d001c04210041403014941009000f074030303c610301050950355281044202444481a03e4041d401540041c590f43d01990050010b20403020707000404c0d99680001170300c1d0450458441c0d40c86180700e1801c0100300d03010070255001d0840031029001c0c0d8548250010700c92080d520002d07240c1d80600404600301c0d22040c4401c0c11540e0b0a4400b800000320509014020502c1510100d03001d1083c50700ca20f00e50b6030a0815459215015550a881d061a1501065440c0c8020302071720327406680d503036101000900d440548400b4021241074050045024000075000c280c5a41c0300c0c105045c001c01c1514410b540208110380007142c100c134000b0fa66110040126000c07a044c17a03440c1c159000c0011076400340031031440300c024268a0190744001021600c101c0105900080c4401000308800f44042c20004030708001a41d030000c17002d07044a060921640203094070741001d07844541518040c50600101c03904d91100007002d0b000590051000c41c0c030b800c0c8001810380d480d091210401c8800c09229541105 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 363941420 1250 363940170 363940183
    0xd050703210603081909140112110a08040b0a06150c030c021c050c06070506013c06030b100509060913020d05090d0201061415190302040f090e1e 64
    0x110342001c0040c140c6074500f480166102d400359030310080d080c21043c08440d110301005416103003402054001f4031200300040d036401c00024480c20711903407504a101c0c0380c0840240500200c02280c0c5d02d403131481c28542000809464050052841e00e030801d1000d0041c00302c0f4004404110321586031038040c40d03015017011108400304900c001d5000910340d01e0001505296640ca000d81801502038441300c0514108000c0c0300d11403014000c0c85900b010004022189503c00788001f140c0441d02c0701000850480c0b290790b1490400a509600c9100c080018007059a26203d84240c01c0003c0d10190f038031000169014200d030017200c80f52407107200001f5030b400030354507401c50b0309405c111031020954031184500f8159010304002c0303454500c0c1c1d11501d4031159800f40b05004501c200c4031412a2a07400000100510482d1098141844000c540801c040070000086141010320307090145d0700141c0302d50074901e07071341c1c00c0314200c0e84500f220606019885422841c00b00c0c280c3c0c0c0d000e00b480b242c00d8000203c040d50504044 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 363942670 1250 363941420 363941477
    0xf02010b1c03120509031e1602300703031e091a0d0f0e2103060105091507120212040b1207020a020d201f030504020303090301091b080d050703 63
    0x605200900905240000150990019244101d5264041103241f0441c9020344031000b000c0d08038448070240581400d24003401c601c06000d904480c04144c804d0803071481001c408940b1030035070201d40c040051542c0000348200d0285d03903441e0500f4110007040020031080c01070050010040d0216a2000045866401c440c6001d40d000760a1142200307080040e0010503545011104174000e003a032040300c012a512604904054809680341035803101401190036420420300315030824071a21842000c200740402900e42c02d4420078555100400b0040028240030061003600d4030a4010302040c0000420340050780c0e07180345c044242d00907030b65a01a08a103403c8480c400690004003203081328041c400480c0b5048903e058661220101048000a101c0388a003240f5020140541280205807054400c3d044107030401e00040c105c0341400c002c40c00107070844401c032401703ca0580c41110300342c0e8200540980310f402003103814050140c400c5034405c0980548100c06004040008040c0301400d1581034640c001c1c0c2d000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 363943920 1250 363942670 363942707
    0x1b0102071206020310050a060c06020c031b03030a0f0516110a0f05030a02011a0f01080a060f060e040b0901120813090c030209010314101e030204090807030f02010b1c03 74
    0x1c40c041c14072a00a500c01d603075221a01d50703e00404a06410100281012110580e8880305084180e840714002034100241c8045903000802020307003003070701000d0003400704000c4001441e034900b4800103500460700060300d0f8a18043c00c0804000c0551104e100c0c0c60040003050504842032883d500c0454104588030200a020b015656171510a1000003c0540189a00c1e40c0003004807a01440d40140b0048418503402e0313100030f8603840c5500302d52280d0702c0107800141d1100301040203504c45541980c5c458207034112200099103190405140d150074090b8800698050302c900c0c40c554100030030302000a010310720142600034001103210021511000c0c8000030150808100080c0c00e542000a02a520040e805400207042c04644c0304011491300fa2030380104051900203140c28603004400746e2000125800301c0d4803400c0b900001025031128051101c0c62845401407994401c520700e40a86040d49524900007160724108010790320f42c4a400707215411042c91045441060b4a40c078080340d07604c40c00c0820b40f110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 363945170 1250 363943920 363943949
    0x3210e0109230307021011031605030a03110405090703050403050708041409012c13150f0516020303010501080c27120f0c0f0f06120402041104081b010207 68
    0x1400400310204514848044801c410300280d240303140d541c4d0140280281d840401720044c9022203010f46880c3c60488052002c0e03c0c20301d03a1f01c544403038060031310350410ba400790400289850310550622a05c1c1a0704413000c8900d003450300301004100000e100034003034800e02d0380c0e0f000030506250158060f660500c3d80044040e1b612511609482e103c4100c469a140c010210383c030000c01d80c4407480d06201156008441004150364035a0003404c512040a0090761a1000c8542c0703650109492034904610b083c00c0100c0414062940c4280004982c0b00905400040b1104008020711560200449045880910303042d034103512000c144d0030040c8680e807000010506441c038991064205210705524806084640400f24800c503050365032600424004106160401440c1c1d07140c500e401e00d01b5410101001d01400f07884901e85004c0388480c1e00c00340011900301201d004100451825000b003042e4040c420702d206080c00d192a0b813007aa01c101c0059441003015014201070400d0340300304a450014541d00280008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 363946420 1250 363945170 363945173
    0x30905040c051213111503061e04061413020c0a08070804090608010507021c092106290a030b220b070e030c0306070212070c050907030606030e0a03210e0109 69
    0x862103c25408540d017114010310000745140041b08807000b21110003215140d9990f000c00c1003d440389003042c1d4240c141e4000d60814441d01d5500c1b910003c3c4c090258186411404901000b29407403641c8240c00002d030040107a510540c001240c0001180d40c8200c0301c070348502151402d480c813070050780c100144141c6081030005d000b000540049014841c05d8013558040c40c5914a0300011b102c12045850224490705410407800154499400c5005800380d013407822218151384110903070f160030900507050007140c0f44441403402c1d4280c10601e91a81210f800040920b941d507070b01d1802d0700082c004c0360004152110240c0e8020341c1e14100061030343c0212040200c2c9030008005d401101e600351424041d1103403402c520043e080005000d40100e52070f0b0001e108080306007003030600ba0380c4040d0040b41c110808440005150b100c1c2900315019120503140855217038101b280050440b040600268802c0c2d02402c0e0007804290025070420346030305405010709106440000e503030061b02a4036032220306c540c0380841c0c010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 363947670 1250 363946420 363946441
    0x32515030203151509060a140705150f07080106210e10060b0337090b0109142401030b090103060902040c050301062c030607031a030a030905040c0512 66
    0x43c03142c00100c142c100c00c480d100003804070080310702040700041401006881c1452074950040d0608130450f01c0c00d113029000c9002e4121094001c40c20490b1968480d01d042e19070300f80c04442c00c0b5400545100b0281d41403404c4074000741410b006202e020b047c400c0700b40c0d800002004410300d2000780840d42009200001040e02000d03696569540010301c028604200841d550208004880c00341014212200b9202ea0400ea100010600d80c111050241d00340110051045042c3c01444005405452000460341c9010042416601d1110604030345620440801c039643e14401404c2500c0403c2c8561031142098a10040c2c00a0050703500003030b40541524000802c1140c2da402405140f403080c0da06000c8100301590580d403600003809500007081b0294000c01078016407a00480300c500300c01400d0594031070800d02103400c0c15800d680c210006610303a05122041070a203c95a001424140c00810030350690b510020080601402210b1203151504102118280b1407005d4407580c030362501004070103052450100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 363948920 1250 363947670 363947677
    0xc110f0c010f0201090c03060b0604080d090503061303020d081b16060b06040e0705070203030706050901050901061401050f0c030903030a09060f0206150f010c05010f060815060325150302 82
    0x50300007110102d2603580c580c41805880012680107031103074651401c0d907035030201070420149101c0d0803a0003031000050a080c1081880a469100d441e441c0755142440149410706100030b080c1c00c5041402c01c0894002580010003581121803031920354142d031680c101c1d8440c0781071100d14040344080c01007200407146520171110a0003c2c8034140c10030008085605204d400e004510481c0141c401401c0001c2c015030141c03000380000780c230003030075603152201e15030768181100c5059441600c0340e0342d244100300300300100b48980d40251440c076100000312003610300001c180d407150484602c6022408964404400407c00965654070030003025070780c451460280050040065104400004281440781540c041c000b142c043d01409042c030341d0200c0c42943c1d0041c0021080340f00000c9041204540d03540011500c01e2141032500e0f00101c00100c5d41d5490000401d2030050a180740001050025040c4a16507600092038060038051100c10030b00409004940900529254000d101c404803038558040c1d1141d1540c000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 363950170 1250 363948920 363948943
    0xb0603150d11090a0b0a0f060806120a080403080306010e1e060901050c0708030901081005010c020f011701060917010608100510030803100f06020102130e06040f020d06060e09190c110f 81
    0x502c42030683e50200300d000207c042c41040302050194002c6a20345c100403407007a40c161a0601101e03070089450f540c044055000f548203a4452001106102096a000b481e5205191040b2840c2d00180c45007800c81c2c1117031400c1d02c3d0680c03103000e000030360086a03400f42042d900182c1c4a48166a034051b62500d41e59102d07400b818205000071004000116003800c40c2c412903040e288103a44250099146900340500b0305125070303969040c02810000d44140080350034815002e0106903032800e5034240f9001003800c0420305086085001e904003001407088000000d0074a09414207214081169210a811070403149401c0c1c0001d0500c581c00010400040c0704900301c04100c1d00011141d039401641c8150880c03c03401040740c04d80301a84410341c10040c60007c00407a540001c402032000400d5030301c00803090300300c1e40003804140803580c50b0f0904000c05a006042100b0135101900c0425192400c05880c100605400c3c6140c016669103510703020225120349038607100b2044d800100c8010141d0a000203a603010007140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 363951420 1250 363950170 363950179
    0x6020304050d051e090d1b05100f02060f1003170909060108060f010f0908010c030e0d0807050f031003150b0406140a06200307150b0603150d11090a0b 66
    0x2c00c0e040c4901c544115080b0314854aa0031040103158640b075141070380a0409a43e100000d2416200884c49004030b60303034074030030301c0441d034000502d840305010703051000e401c01c80c5c20300445d00b00e292840b54000c100c4560107201c1103024003665468007615131120029400103481e10324004820200300e00200002c084081c01141e04040036a41c0ca801184d900c0f400f125055003100c0030a100c18115400780c00a0001c3c854181800e03107401c0e45941c00c1d9401c4410b4503201d400001e440d010b041e0141a0b05000000a0321680c0c50401c0381841c1c0814042d00600c500110101140000000622030002100707081e0085e607400a0654584411880c800c40074000d01001280308910f020000030383c00c4100c02c07036400032000c060980c0810b14a132410a844801360119900c80700102e1140c1c80b035012505000401c5010310503000400000c0a08649400300d81d1140160b03401080200284001602e440070040c0e01c9400840d5a03003a001c81a05e011250a00d84080032038024034070005000244589410241c0d40c0d6000f5207 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 363952670 1250 363951420 363951433
    0x204060203120a06061d01031d0d080a14040215091c050f0703031e18030f050f0303060d080d0207020a090f0e03121302030304030f111315060806120a0602030405 71
    0x3d03e0498901c1d00c100001714400307420260782510002d25124110205040000e034040010008058070a4101600c04868000c0c94500e0201a00881c0040d0030108441c020060a0f00d02c0b5698a002203001d00007034421100b250842c945104000300711018403101500003406030710b0260000d50050200b0504803203500030100750320700041c0c001602d60220303500355031050007490310b9001c003420803603e255032a8108980d90320071060a81d403c00150005520501580e421906a400c0860510341007088034100b54204005015042d91100e8110004a0700454016510030802c22800001d2140c401c0007500441e4581d000545000035030f00803001000e24107414052458849170040c0c0324800d007038040c80319621500210720240c02500802440c948064200d902c0c054490711015401c01d100034045070440f203661300ca035442d0709014040030f244580d4054144800c2010310200d02e40c9810f140900e1b410426002c000170710320f0781c3d009985a008003904050354180501801c002002e5401110203450074400d14 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 363953920 1250 363952670 363952681
    0x9120f1401140601030c0513090b060d0929011505180d0c0302091003021302031e090c0109061704062406021006060504030f0b07020a12020c01090602030309031b010e01020406020312 80
    0x260110b5500e405123814501d0b50505210030080140012802d05411080a0004540b050b946210b1010500d00500000c100c6010380d081050340c0c40385007981c1d011441c001c8001044406480b07d65100790303d2030340c24140c0d100c1401e0444c03d40e10f054171952689e8088050300792032080c0441a1050030980e802941c06000070b81c0e50314100c00c0d010205101c002d41000300945000380518483d4095500a51030719001ca614124041ea0020030300e40548590f0030b43d40207041c4518156811851084c002c15450500306907181c0c0d801d00840032003600410113029561102030307110b80c0000112035803081115051003643c0c80740d210300b002584c901c000003076080040e151000c04181180902c0030380301245d5110142c001c640c12aa40d4900318240003800072020340c03041c0403540000400780404400c14a407181d008218001c000d5000500c41e01590344500b0564204200b40104200040104c0703142c0b9030440c07103821404241c05056070046c5014000d00041d54030100300450ad04d6800320080c46003031a03504261003681c50f40d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 363955170 1250 363953920 363953927
    0x3190b09060906070516050c030d0503091917090d0b0109060f090207020a060f0203120115081501120902030309030109080408060114012f010504111009120f1401140601030c 76
    0x1a5448004a0810300050b9196444090221b1000748208180c43c0b40f80d210101180c90820143e1091010500110400181c0c90f41008120007400740340c02c0c000540c108036114100c4a4021103001006500f0000e42842d641c1c4505000085295000d103000d201580d45148000c0102078901410303100401c128000603d81c100ca001740d074101074009001c40700c003c0c6040800d0302c41501d02c000741c0301940014022030201440d520080c900030200755807440041415508024141031004010303a105c0e400714440701c03a0070b9030700101d031a030a44003074140003440c84140d0000074a1802210400f640c1582010900810040c070840030700304880c041030072100030b03036290b1903030750a005141c420850004800d0f8094550b4815401c90302c4240030f404c048100c1e420f0118071000d50030341c2e8007101c054440d0481117400d0321160814100700c2400c11164a08244d0302800c040200ca00002c5001000d08003045003442e60307042c00f2903107072844007d0b05080300800102c03040c058404001e0750b007240c4aa01180c5014851000e8a01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 363956420 1250 363955170 363955183
    0x70b070f0318120c0c08060c040509071b1118040c03020f100c080f0d020d090b0601110304091a030706030606020c121e010b060c03030f010902070213020903190b090609 74
    0x18440d01c031035091290303800116000300500400380d903440b440c08000201d909042c08048e000b5041c45107020764580c24182801000840035106404205611a052928800841c4141c40d01a441150507815400c0d40e8000340c10140318184090409041b04240020042003031680b008480c800c2c0c8070000140030440400480481c4d0004e440003090b600c4108030000b8110200620601d58031143da6410070015850b07050498104e003000c0030b451580c1c0c09801060044088406a00c141e00b40f808408e42c1043c9480b1a0b140e000e540b1404400548944a148401c5159080d040e008003024048507aa207603281401400b42c0a24481e46000d030207a20f10a0000e82885d103a00c2580b000c1c00001410104002c40b00c1e00b1040001c80d551280304d56071801074941a6540c88003d02c03807031914000464072412f01076992400100c0c1a0300000c1194810081600180c031015504414910030440068a038480000802d051640ca899800c10588084122804225811120038094880380b01102c030250741e000340650ba80e0a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 363957670 1250 363956420 363956423
    0xe060f010317090a030b0405010e070e0903040b03100b0c0a03030f110909090a0b010609050108100819030c0503042340020406030504140705060901080903070b070f0318 74
    0x20b400c0114440e070350501d074018007003c54040d0410201c15520380320110070a500b0744086440c0d9450b00c610703080d01201004008058104200550901c1c1070009609690788035038422400a18004000108aa25401c070180001c2600301c201340e54442c113001440e42c13259a0340108501087c0750841500c1c00300c82038480c598062245003c0c1510b420000c001f040b003a081d008105000721310410066000203080454828001c111139120500103501303000000d40303248001008041c41c40740000040040034400130708800a40140200180100d1031401c0440d0360039450400038002c4e102c00503000078048010082500c40c0410b181d041844c1c00e01d0310701040643d480f94103003100451410203814420700c68a502558659480703402441c141e024078240c00e001d80e000307a4810408a90b07a0410482400200e88081505c91181c00103405d01c07a080100045041c00766109550401c030422000581400c010000c840300700d40c05c40600c03000c603c0c02c200010326065101070881c001a051160010f8117814040002002c80d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 363958920 1250 363957670 363957683
    0xe011113120209010e0a0b130e0118050303041e051f050c030f071d0405011d0601052b060e04050d090909031205070e0d081e091c020105040510030e060f0103 69
    0x13070b440c19800880208020b090801c501c0d40d9000c0d5500d490b924003d40d095204968903000c40c0c85000709901c41d003121000ca40780d0700d03a1805818001c1c001180801103a9010b82e003c0e6541031070b00f80c00c0d880f90501c03420040300103215218100407004078131580c1d064004200c03110340c0300f80501da544406121850000f42c44554182011001084090340101011101900308002c90014110000001425100280e1221124030407211103031103000034101000350b210800782030240c90a029070000144850301740300410324030310100c42007140050650308a04020180b04029100b00e040c2401d10307940f01c3c2c10529052021809540700009e030f40d1824050310b07107280e8040e151100d01810020714840903020050242041245c441c403410203a641d0f000b003130100c05000d00b1849450381d0005010041065554000020b040000d00ca031100c250740740340c0d0340c64050b800c41c075020180049902c010790780b40c09603410031503114040011404c00160303da4080e0004510301e90485005860340d11142c0d004000c01c0c000034100c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 363960170 1250 363958920 363958939
    0xd050415030c0e043b060a0c05040302091e0106020d09030f0602040f0e07170f060d020310021b010f090305040b1308010606050304060b010806010e130e0111131202 72
    0x140668040e250182070750401c000e42548a500084c1203540005c440c5030154a50500c8079106401244004003403a07800a0910890784980045540d030a00100120030203a1a02c012025880c4200242d41c000c41e4092b0542103d410b0100f2400310944200f14200c0c1013409210000820034400600707079a100617182c0342d1071003c504684508881c100c0702102522280d07020000006d0882d09040722000414250400401c60300b8046001410400c419660000c00303110a0b06205401e61000f400a42200301141c01c44100314051020908100360062284519440400c005031000101c0c0d01030b9280c403000400801c074858001d042c41c003c807406228040c7c00a54103000610040e01d0080040c11034500601075104080d40d5001030f035080d10000e400500026001100703100030400310307000b56041448242802500d501d0b1890000701413840d1450035501c01d040004d403006461180b98030503580d0300c20490081c071440320001007104a90b400030340035001c3c1034540140080c41240d2480000c0203c0d41c0105003051 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 363961420 1250 363960170 363960209
    0xc071113050618160e0f06070305090a1d280903200102070804050d17041404110306090c0d14010f0f0f080c0d02280e010603141f15110d0504 62
    0x45805190b6900ca80040621030400100d94035540600211403003550703050342d6403d4007000d10000e41215442818dd01c2c1880d000c00700344c907004e0b50495a001951076880082e00080003000355860003035501d1100e10900c4d00403900b0a05910441e81b202a100340c8242d00d402e0342030461021708034441d81070b0250859000744000e010074684a04100c241c5030050700300c001a9400100c0e024900d5000d58410208085c0c4581c809946003040d0042c42d00c4074101e580d0103030451410a010640288004010641005001501050f6480309600505055100210700c00b44c0b9a140c0911a042c0d440f18040c1a1170811b1581c0700050b100c00841300f01d4181e540d004050b2071a2103241050000c1e0408940c0c00b240d1003c3c4041030140d0400c140e00c022844680114049c1003100e1807d02da41c0144001a0004000c0506003070849125000d841d0f14a50041c9051141c40d0b0f40100c00b41603c0d0202c4999080910407404602541d801c0030350150b00807021141c4041610500207134540207685904c1140f2030847c45100d1540c0585 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 363962670 1250 363961420 363961427
    0x20105010b121815010b0406030f09020f010f090906030c080f01180b07120f05040615060c020d060207060203271f0c0306090507050711030d080c07111305061816 71
    0x600c0f104840865143d81180d00720a00c036181d09801950b601a004030f810000d880e0305d805000c0120303110740780c108501704003a000708150303900c03086100f4103001d40100708a004d00e22402004005012503101003008540768608994500810303c151006031280381c444910518040c0300784001076805100d5040070000581d60554001c50003001042845001c03401603c90307108501a8044100030468006032914142c44c1042c01c80c0c49800c010000e242e100c250500c07209400402c840c00258044482101c8038442d454050042d2050400080516002109220f01c07480f4040c080d5480f0544c4a02034000e0b031003450b031501c1c0d803100d5400f801155820001e4111038002c0241c4d001c061a91860f107004180251540780407010703280207039401c000003180021554180004200e240281d12022400b40070641300c0c980008140c010050010394004400244c40070800c80b16030042c000080d4040e184411b03000d2045028001054202e070070310b000351400c06042043e80b40d0030a0003445000c58000804403a4210321046 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 363963920 1250 363962670 363962701
    0x1e0318080d0c030216091d1c0c0804090c020d111207060509010b0306180d050313110105270a0602010506030a0b09070b040f06030e0601080a03030908091807020105010b12 75
    0xa40070b60043d480d200804201c1c1c1d10458001c0d0040c1d0202240d280f19031607181e5042004061102030640010076051803032030b2023825100030070b541c07450400e0300c00c4a10f00340900e0701d10541d4801c8460714075125910803015008a4042560b41c13a90701c0341007030300b900328900503150300390700c808a4a1355030100140c400085880e07002170340004941c800055031240d0a00401d16042081e10a44548171500c4100c404625040003040a02c00720351505a0841c10503070031462850208440041c03140280d00e00c0401681d1240003910100c403000b42c0a1404c6800350000e41041e03070400621180201c2034414003240381401401080d010344c0340035004020b81442074807406004079000d03080701d0f8240140c41000a07042c2242016001600501c584500c90500e0400c0180854454014000380b9401005c010400ca180210304420a0341c1c1604010074154010f00e04a01785208941000d5400f2034541c208500b01021003d0852282009800812150f40c903942d847c04640034290201c1e440c1401640052a004a1030404 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 363965170 1250 363963920 363963923
    0x90c0503061e2403031804050c0a0801030f0512120105101b11030c0402040608060a050102071d07140d021803030f0f0f16030c060605060f180a031e0318080d0c 70
    0x4180703c003404100001d0865000c5135040c01d2508217100840c2c010703c0c05200d00383e000070300b0744400307490251060070190140e0014400686100340d44405e1405000d000d01039050401c0040b0540c5079161b010401102d03c4150a019490184030710040102d041809000d00514407020400c2401040d6100d0762a401c0303c0e101c0380d080ba501030056880484a0b5101d0b40054000f406503525141070078038008040c058003012617440030b411580020b03400c0000f8201c0d100414444405910402d01c0c6a5131014142c408080004409000e20302c000b4044142a0085e8060152481c4000c0c40e030101e03110a008040e900e001d0341d684090744000800c103c40c0d4541c01040180100c0405840907070520002d0388604920803030700c0f0425808100602c0c1039408220141c804c00002d08000c503915420140000040402401020259404010003003403139807a669445030301e940119401904246103207941005d034403819080e90012030118800304244008d1204041000042c0e0384044001d050000300320790102c47d0501c26820 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 363966420 1250 363965170 363965221
    0xe040b0102010b06030c0d05130201170c12100603201b0f0102121b040b0306010305070c020307091d120d050c12010b030f01080d02061f09090c0503061e 67
    0x1404003c1d440d0240554860f000a00d0f0b8503444561919008058401c000c004003802d00f005018000181c0e048501b544c850fa880000c0c1c01166a10307192410160300c680800ba400c1074121f0801c00c0003000c541040a000d441e00e598040c0501c045881e07000c20280c0064840c1144444240090703000b04410b82c820802c8030800d00d0031508040f40c0c0400141c03c9138814001054a01d280340b04215181c0f182c0d10400c61008426404c05241526009900102d40000340c04141019100d50114203e1071145036210700301500201600e0600307940300740f182c2c010712001d0f09030341090f505d101c140c80365008007042c3c0028102601803284e103020351841c01d890080c40c1c01825900020414042c402c1c0051408041c035010b02072900b0720590f2400c1c100620320a01d14164890b80f00303988029081411664007180c0240c000032021002c07031600d401c0a0740d61070042400e4100c10601450580898107024400360000b04444064081e50016104d004010200900310a0306a812400460104074186144190860101220307030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 363967670 1250 363966420 363966431
    0x108060d030503070903080c0307060b030313090207060f0212070206010f0506030a11120408090901090b0d020d020a092301050303130e070c120c02010305061f1b020d12110d0e040b010201 82
    0x5890b10908d07040240c800741150300102e480420403645d846000d42600c400c4006506101d000c0c1202c400784070490141403000c030380100d12341041041e540c2011a1a10100350250340350b10608008480102046889000521584000041c0d69000c8103161041c0ca0000d000c06195071b40e03550502d00601701030034940e01c09100810260811030004086980240d209a44443c0d43e41c030844100315a208040e00000802d42c5090741d500704035078844d855441030f01e83c1540d2044d0b40404c0da00000756200c01a501840358181415143c0c403007600f104035541d40399404183c140b0590b903210380034565030f40584200d4203c505601041072040c40300b04c02c002d0794046c0e2545441030348500d6554501c90007800c0c80c5122408641a6841c101c119030305030103410713070040d01034420342c0d13000f40300324150104020300462400500060841c08041d400088100d01001500038207132900c841c001e4585001c400b40d071003081d580058001c40e8484070781c0c40d000c10100d0a440d80307507a0f2621500318401c1000010024210400d06540d601c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 363968920 1250 363967670 363967673
    0xa0c1d0604033507050607030b10030902010e04050703021c0605010e1c08070308090d1805191a1b160e130506070807021b0303040e04081b0d0e0108060d030503070903 73
    0x802e00103c4908403481c1207850310518030b011071420070080c1c010303410f060030301900c03036050346452141c12142000c52402042108490005992200f4882c00c0c0369040380c100010442000d8068000348980d1300c5e0582c4421a41e1040c203042c00c00c540c0b0394041c4a00064600c12030020a140003441c4947c0d850050300b02c0480720300141e5910240740d011a40840c04911120200506c585052103800300c942000c0c1869603400c465011201c59408bc0f60095074491940864a140207144045024001c2d0090b21902003100c400c00846c01040d0300910015580c00d6881e0407030301c24000e00414280660503c02000c099501e00700f008507420003400500d0300c5240300b003030f1040c0400b06400300b00f040e018a106d622400300c2410b040c84024100f018000c041d100c80c030149107014200c0d0b140001200d00715085072619801944072442c1c406594420350913614070a184c5000c8603044944045480301903c011520b50b4040c0740600b90040d9000c03a81114001d600c110145000000300340501c00a6a10811900e40001d4141c1c9a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 363970170 1250 363968920 363968993
    0x30308100b040617160906120608100b090c071a0606091804030306050a06080a0b0303040f141903051b0325080d020303191e050a0c1d060403 62
    0x2035000c40c0000e255800340c106203140d00c1c895036411086003000b075099417040000103018080c0a110322401c0080b8055950b80e40340903075101c00c003e45000001d540306200201d000e032002d40100d4044511802000000c24001103510044a04851b8003800c1700d0540402c00385c4184840500802d4070b50130010402881c4020703543c601d03c102031040920b00395099401c040c24000e00b2542980c0145000301c1c4102814071a1581100040d82d1003c42a00085400e14244020905500455009501e40018110040303084060b5044149803a4001d4a2a0000120503003028090b20981e200c050520303080142100a070141d1501007003072002c0003804951080c20140c6626403e00c00c813042d160b45c0c04860050078032500006025540c417081d81d500c000c41c150b041003a84140031302100490040d141c0d9507000030301803410200e0020740e81c5e081d0b4190100201c3c40c10029441c0a006900b10b040c002072040c000803001d1014000350308220b030f140502031702d061506580d5500304005412182e034202181589816a00025 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 363971420 1250 363970170 363970177
    0xe0f10090f021810050f01120203041b0b190503011404021602060c0304140d0b010e090c061908130b0705070f060c05040515030106020a1101110f0d0e010e030304030308100b 76
    0x43c80300d901d4250324041c0c03a4042d0140c03c1e40c00c403920a2045c81c0c03100c5610303030f0f201000d007403c0c80c0b800d080141e890b1207900d00500100c0d0090640c03842000b01500000c4c0078040c1101403c13400c480e010f2482c41002a007441256244824000d8a9406810055000080c00c0030b9002c0d20091050302c12101070000b0f590001500c0b038110724807007001d55100150501c03d8603d102e8440c0c401c41d00035606a8048105c99542d264075003014003809950f84880d000043c0300400401851084241c090304055035252003640c690180172100d00b544002c1542000412810624042c4080005800120300c002d0f5031210b98040710b25a020a200f541d0030503203c5100804107029101d40e01b40c00c0d8407038031144d940b185401c0a00c0661841e40c080c0140e007000c2840108141600410202d4690740c1c009500c40d01400f0140040e1005d01d150a640a4a8800c4504e2401d040c10b0005086088400c9a03c1d411200c00420004440b00f1170503411141d0190014807040001a014200303082d00000d40c003030288161a2a1070701c1e1000d07a003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 363972670 1250 363971420 363971449
    0x1c050717010228030e01110d0b01020325030e0102061b180a090b15130612110c0705032a0909070506030406090c12031b060b180a0e0f10090f02 63
    0x660240b803d9100c55014443c03101003907100d5000f4410b1103007000801d41e40e07005415858800549034031610342140e1086c030864051100002900011401494101901c810840000c9010803000900082c90350300000382c481c41040420302c0610484a43c009007041504010044c407481c2c001c0180941c210342c0c407115a1030281040c858000f9141016004220b109141c24001d281110020421504090b880c01e01200c191415403c00c08034840b01000d4510040c01001040010401c0100300c3c540103200100f011000c0722412001c542e840b02101141d072000b0040c9103420301c20191030039207075111810700003c1c0c0c0394040b901c0001c0d1403600d80c3c0c0700d01003080355104850441d200c03a03491050070304202542c240032000c3c0168001d088000b5525640c09003c984544000c00c0c0c02101c14040380d410000d91360081e6000c408040d02c2d01d074481c02c0c04c13002d4180d08030043d10240c100c0790030044814102c1000050a030101c110041c020140480c18141e000014490072606464800d4980003000142c2c0706e071078808200d030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 363973920 1250 363972670 363972727
    0x30d09060c030b060409020903150c071709060a030b0612010803030f090a021804022404031a16230f09040c0804110411040302030a111c0507170102 65
    0x8800a1408804641e14440000103052400d428101c040c2c403250300341c1d0b0a580303024000696501d07241d80000d181a401820285500d0500d10400010300c0426010345a030a00c1589542d020307416000002549006820340280c004074184080c0b002644a508003100a842c043c0c0307101d20f4450740e140d80c203001a4090308018a10b605c00028000c90020582ca030552203209e21011700f400c1d010380d40c00255800442d450b0851074606000c00700e82903680305040c0c330a08070403030203107003d520092541c0040d443d0030511081d50034a20918a00c07154140f11007a2502c14800181c240180c09070b14a000d42d0300c04003403030f81c4d4400c1106a044074000103030591300501c003410901c1d07446070301c6402003010082550111030240041022401c20311002440c3c00d107404020000488020400450355050640d05000d5984042c0d070600c111344590040c4141c50038400181c0e44156030103002400f11114130540b481050200800a500261081041c19070700f401d404d140740c043d0700000d841d0036600c08021704020a07202d100b4081 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 363975170 1250 363973920 363973931
    0x2205090a020a0903050a080703090803070203120c1c0e0f010e0f0603041505040615050d0c060e030a05010f0c031d1f1b021617120a05070c06050705060c0c0a03030c0908030d 76
    0x5040d00300305044000e254150094dc034003952903010907200c0303006c1100d01a6407840800c90b041d00c400b0900402000d000c0e0301e0003901e4100103c15006107070019000009006407850014050319502c07900700c8205102000e00703072007225000101400355550000b00195040d1601f406ca07101c04034401d0103000d0040d40100004110070b480009000301d407402c80d521692081484600c00c00003c0c0e0b041320110216141c50400d4100c842d040b80100b4102140d0707520041055190200e100980800c60f8410981d00f8100d81d0108880d03116070005240408080b100383d05298411020400c0440c100f421b24100d900614201007141014a03548030804920b07424810056005001c41540041060400c00d00403c1140b0104c8806401c1c4020152101042c02a01c0d002610003e44865003074020750850b044503500c1580345545070768034040103080d5040490112014083e060100b0b0082004100340e480f558182406003a0300491030381c013600103000d80c681d00e0007400050400011440c00c2400a040811743c3d0714400300c1c1c07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 363976420 1250 363975170 363975173
    0x909060103020f041b0e060f070302060f0604060305071e030c030b06030f280204020403120c120e0603070c02040e06010611070905070807050c010b090403052205090a020a0903050a0807 81
    0x41c0c60840f0540d40d8000c903c1c1c1841101c0c8041c400e21301a07201400c40c10200e44c0750041c1e01c0400c000d4400d446414114880c001a5981055400a5040d105d02a5000c00c252903071142000c01083d50007038400034240d03601a01e402c0c092803a02c907a4000846154640745d641e0140e40c0da46510030306599501c15284030010b0030402a0500b8140220400b10600c031015040c3ea203219003103640b000d030f190480f0320300d0814004480000c54032141e0494001c1c5030001e0b0700244400546100504440e400c05003261046141c01c4c244d0341e13182c018060980404070013441c0f94119510900d04680624032128240c2c1d00c0b9440d491580300b04c20b028410300e07020b495079a89180031411050304441c906007156010016007454002000a520350004070140c00041c04c0c41c181e03a4039081c0340991805031206109807035103e20b60009020826400c0b40003418440440d814402c0c8903c2c4c0e0880300c00c85520b10348610f035001050070001991020aa5000307040303a05050903e500d8041e1203440701c0c1d140c18200842140c002c400022100c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 363977670 1250 363976420 363976429
    0x1503020a02010c14040605070609080d05191406010309110a0303030f060f050d170c0f0c09010e0907050402210f09300313051015060903200a05090906010302 69
    0x154040030904014813080b07011041042280324920130b5400b00640450301d0f1040001e682c108000d00d61b005031304140c4903218400315600609007039420800c11078141c4600c80b9858028014005c00004050700381c8071075921800154040d084100d81203030703164000c00143d041e96507000c00c1c0c08003541c0030b9a000140e101028100e6400c5440d260420940e85c080e290040215035151a1003e0300268040b280101d0074116142c88581d5008810108515010341064440d100b107000484c81340400d0121101407440e6a61807400c07010341000e403050341003500842d40510507070400d0b40081c0529404003802d110910440c00381c052004405031a041c0741d03801c1c072105100003d0710070001c00e00720b01803052031000321803440c0e040c104450303900240f55089000088001882c1200c8450100390058206043e6a805a06074171341400a2415010549021000c5000030400902c500551010380350f0050981c55401b41c0e82c2280b8200c04650300c5015400400000c4c082880e444940350b040c0101c0e11080104000d504610400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 363978920 1250 363977670 363977681
    0x18011b0306090e0703020f010e1f0215090607270803090f0402040e0703111b060609090606060403022e020a0b01060302070c0302122a03010e03040509010612061503020a0201 76
    0x5039202400c01000c103000c210086904c00840713a0444201c41c203000703c9030050f2010401d034081182d001421707131440748181d11001700014030b03071265074250303140300070340740300880042c0c2094620210703d921141c0003030b110a000318080d480d0b040e9010760007081c02000041603003904001c1d410220680e0030205003136240b400c01250b404041d1400321019070500e4200820040d5001c0014055402c1584440c8182c100c040000e00300c44560a080404261419041840c80c1d80d0f01d00c2642c61501074210070000032032642d0089890f0f40140002440a89420b00d035408000300041d00d44402c01310780008809044415040c0081c4900360580c5d500544042406d070f04000031107100581c002c0781818010881c180c0010401d5065109807541110b995580c0c0400141d20782c42c114041003c94507282c0d40d80401410420446c04d101d03c003210440082c000c0d0030707851203500e0710f902613031007402d1304100d02c1c000510481380100500400c0184000380020f14a039101188446010381e4412100801c1d0700041c40c10180d40d0a0181 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 363980170 1250 363978920 363978929
    0x6050f04050403170c0408060f060108060a030503030a0b04060e040c060807050406090b0c0102070605040309080c040b03064c06030504051222030515070206040308040b18011b0306 79
    0x400c802c1c42e003510080d102c10b02c25108680b100080c0700024400b40000016038002c1c0007030b1800c41c0c4a5103004580040c5968041c1d400300d0200355590001407151400c00c1100094030b5114002e54215120550124041d01c46682519403280d200e580c0400c5c08441201c190b8800d5028566950034149070a1014000c00c03400b42901d01088000c20080c446030f90060390b448101c2e10aa0b8810350ba070000f02140d503009010f503d00062503e070400060006040e03029081d00103443d000001d880100345e905e810003084594015000b50160891f400041d10b080360202c0041c0340060550203418120a10311305041150030b4598241c40c0700d145070f510440d401c1c1c2041e080034050051410200709904203078880340c0d55805142c94030038204a000445510000f40c11641c9807524040d00c1e20019041e0300c034640716444480480c00c083c000d0070503800180c00c1b54030000d166400b85e50941c0361610380341c44036100c000800c0c00080588d014107220603c02a0000c90074440c003007080c078030500304041070204098028247ea400c1d601 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 363981420 1250 363980170 363980179
    0x41403040e0103030c0c230a05011812060b03030a0804060c0e030a020d060b030d0c050c01030501050d1709090a0902030606030f28060603030206010e06150403030507030c060f06050f 80
    0x2440840400c207601415039405041c2100c041a40e0720f45114419141c0c0c114030306240e003500c4500381205c080c03202d40c910300608441180030303191614011101c07460fa04070b20740031220f51500f003007010b91541c8805036440760041c0000b0480901c4040400c0c65580480031800001c0c0d81c400811060160a01c100c179501c503990302d010103001d02ca0b403002030341c1c2c1d44007408040c2c81041c2d844084010000b090703111605604000e000e5500002040e80080c2c1104503000040c6e800d40150181600c00d58824070445c1e059420003429507a000350b07580c4459500e1014040d10000ba81820802e03045591380e00c5049900c42c0304c0c0d1110206018a1901c1072608144014101078080c1e808019115a503106c08284801180d4182503081e1100b0700c00190320243c01c2410030b01030052442c10303201005040e80450145d040e1505d50b503d5201035113601d001d01c1907400c1105a1f0030040c040a00013400001d1040d0001c1c80c02c24064904401806003540765881100c480c1000c0c0c080075039680c2c60401103414003000300c041c2ca800844 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 363982670 1250 363981420 363981427
    0x2105040b0408030910110c010e0c010804080715050118140f0a02070c031b080601150c020d050a0204050a050610020f03031303090f060215011e051003090b0a0203041403 74
    0xd451003848000a04010300740c81c80400061000b80003006009440040c859050004d00044a010101644407000c00d1041c2d5083c40e911303c50300c00000034003042c2244180e460440d155034588441c0323016013044100312124204020303060790640150007414041c0c0300d010118513903c0690003500044903810718200503980050020481c030003201200c100c0d480314204502680e10000b600c2c142600d81510f4100414220981300415508070807102c01100351400001112900d9898401c507080040d08000003000140091540e2001414110070300d00b2503510071021580300442c00e500180c10b844085030418501c1ea914020408645810076041c43c0407405030001e0107442c13580e000d6254507031000500d040102220418500d0416101d81c180c0002800114840300400352140300082d2220074125507419275107204000440c04403e08140246611400b030200402c40e441c060521901d1400c01d1071400c00e051b510b0025001081c85411220300c9080c035404010381d02c0c1340c549440b510036201a50901345560050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 363983920 1250 363982670 363982673
    0xd0203010806191a0103020322080711011b0f030e0d2414040f05120a0e03010501060e0d110103060923222a0e060906011e030207021807210504 63
    0x100840b4003413a00f80307405a9030380d80f0316508048034000d944d01007904019100b1060248504c00d0082c010080c802c1581c1120000740760011500f401500e00e803c001d4a4041030080002201280c14807050f91082c282142c0e07050090f400560a4501c1c410252254194000101060740300c40c0380c2c0740140d440444040000044000e4208150741d0b000300014200c15400c500d905c00d002040205509002003825a40d0351154000c400912411040704203038007a600380400418042e002e940440d841e43c40107042c4e00d0700040d50351a480c441608403c131440c140b6542d00004a00e42c1000e0150742d600f404450100040405540d8905001e920010012030100f2482c0c8036820030301101c82241280c1c150480401625402400b550940c1d00312900c039141480c0441c800c0008064140308030320743c0300d158100e95208060b07903038100544110b0601026030303c0030b580980494400a009074003034904207002400100503001d10444018000038251103010100c0c0c824195034000000d02016440702c0c0343c1020342072080e818103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 363985170 1250 363983920 363983951
    0x140a0c02040911030a081827041b08010c02120903070b030901021201090b030f06060108071103072a1205070303210f05180c0f060f0d020301080619 65
    0xa800091081e502c0300300e500148049440c150b2902807008065654002c0180b40c858130310740c0706140c41422140e880158281c01d00c1c100c10114508220b0803440c2c040700300d188400c900b03008030042c030485d01642c504c03207810f07651150140c101010b008618000201005a000041d203030003101c0c400c0c075a0380c0508211003001c503140807403d5001c031030b02100c113503031070341c4520700928003a00903d00300700404810f96000090440140c0c008140c062420f80684540d95003440e10652540b40884510780450303030342008144030b6807248900000000c110741c06d40b82804035550300c0140035120100d400040b04e05080710011000c88c8282c2d81001003104007002d07140e6130340f565a10741c0c0715503003440040c05005c0c0002d14190000c980ca00424103000407107104000c0c0f2201c940400000700029540c0441c814003003158088401c500040c82c44259000800400030074184804000f901e500400300e90405e00c5c4103001c01030108c8110300256020700480000750500745445000814025112445403041505212020032003a0340c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 363986420 1250 363985170 363985187
    0x7020c031b0a1502070b03071e020a020a05060d0902041107030809150f0601110a0f2f120307051903170114040b06040b04090506090114030d181a0a140a 67
    0x84000b015072030743c3e0001030b042c0e08043c0c5942c0401582c540010420007069444401d420125800e0b0710701426006583c0d100302d9990250001c000d4101c01504002d000c10f1400901900f11110380d82004500c8403c1c9034003080580d60350f0248180c80e0100410044101500955440c1d4404111001800f85540e00513945800b110003600d100e6212019902180c0e4592180030020f00b64039860742192032030040d51400100881c403501c016a4421030941c414010001e5010303a0502d44044400d01b41c801c0e08070700381000040701241100352490301c02003003020b001400034040c0362961040c40c244411130400509014200340d400b15807202c4000450030040c402d40e1310450840b420004280c500150545031100890304501c1240c010741194a400704000030b5080302da40146116040584c0d4001140e6600d4180e952446020150381764160804800c03410b2040c81303502040070012044c0b02e00b0a42a81d9120030305000300d0007865990f0092000034410503d150803004411814202c581c00514085103004024110503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 363987670 1250 363986420 363986429
    0x60e0406060b07170903120c0d1d0a03020910090905030d050c07080a0c021311091203070c0e04060219030c021e0c0f030a080d0b130c08010b031e07020c031b0a 70
    0x4e9001c03c04480c0c5d51800c204030f298507042130304180d54411400030420303520f0078180001c80c0044c003528240c0e0016414000001840c81d40640700d104104d0846d03003004048600141080d00c040601500002c20342c0c028060b0100e000d001d900a941c0d101c0d03a050700350090340d100802c00705c40c203001084200002104a0b0841c0c003520080d1419464441940c0f000840815030070102445841c04c020381203001e1000349009048400d41207500c3d090187e42c80c800982c0703034060030401070103451840504000c803400c650440d59201c1c0c81914014075228041031058002141c4440c107030002076407100c01c5100150100300310300b5281202d80c80c45040503140a01c03c0e680394003100f002c50040c400300c0801410f6032800c200c01c0c050035500201441d11400038015910084c140088141d119030000200c0c4290020325101d440041c5d241c0355a503141a03807d0403c00141e80d071001d405054140400012030010f05907192110703001e03160310342c0070782034403140d4004141c60f1840500c0410050009280210500c0e52079415060454 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 363988920 1250 363987670 363987713
    0x21b0309130f1b05210906010312051903020406080604051501030b2d09100b0307052b06091d070513060305160302011403060d11060904060e0406060b07 67
    0x15005031441c400703051904205903c140780d00784070302d149541000203001110b1031880c0c0080c0318003425170b0290b04188140c419080310f0700440018400709203c2c01483d9900e80580c1415481c2110504079040203103000d07121400080c1c0c0c00304051182551107185a034200358100c500340550708200400040c200785e20110303181490f560f4000d407580e903140e000804500c00341030503401600d031220355800300c0a089910721031441100140001943d016182010034160b82c1c04150313950031945d4507401640e07030342d200001c120340c601d50313141003400030390241e0040e51100c031190840842c0d41441d02d0424019504420782020510007030451810390303114001f0b10354003140c9086079995407000c0390052042c02820307aa00054060b00514844c0e100e0004c410741031001f200e100b03036554a008011b0201c0c004a1340800c2e103203941d00048500262011406025540c0c4000304c0080031103203000e000710002411200300354001400301e0405c40400051000c0b600c928001014111125407900d112652622040c05007290500d908 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 363990170 1250 363988920 363988931
    0x20d0e06220f03050106050406060f05040e040816080c061825081509060c0702090f180601080106061701050a120c0b1b0c01110309010c060e10021b030913 68
    0x404103088a410010030300c0100100b46036481c3c0c103209010f0010780c0a41401642031000018519200303066007072100d511075031810300b041d0500d2641d00d090035001c1c20030b4505800900043c440202c030442c41203c8248100341c1e0680c0d51074417200640c18030b40020a04c01914002441d8640b000764007285c0b005000e4180ca0404801700c1d07903000c890311b03807000507041406284140c2811561350034118000901a60b903400413110300350380318103102040b1310407844004e4004480d00040f80b100e400c442549908240d054010700140c0302c1d0b0202040c5008000d83c0444d020ba91210001c101458000c40041c90941690021061940c1030401154590110384036151030302d4003410004051102100ca8440580f4480384000d5403803103100c40806c100e04c52150400a94082d21035002e0b01503000e80e051300b074828580d1000c2d41c02d2155a6006403144e200e000425a06030307894a405c04440c400510400d0680d00d1340178001600c400745030008210051075085801140e520400c4450440d640d41005102c0700a05032030301090 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 363991420 1250 363990170 363990217
    0x6030319140f0301030b010f03050a020405062719150b0306120703030906080a020703020d0806061e07260d110403060906050a151202100207080a06050106020d0e06 72
    0x4908035100d008025039507020588201038085003000707504803801044810b83e141d032911140308180c0c00c141b01c01041caa00c1080c8c1000141440c0e00f2281e4803a50051141d074034031100e0a1607101f0a09418500c50610710803400700140928103035a06526860400020041401e08128901d552034090141842c41030f8040000b40203079640b1803d00f01d10060742c1007507481c002d81e44d2602820791180790040802240d21800003070b41c142040c1c42911010740d0594028000f0801e55242550400b40190950b5084401004441e0301c0f1902c4085c0c03803020701051029a65213008900b08000e048600059403614003148408a07410f00300000262000010710001c0059551714100b000c02c414401c1e50300080016041c00c550340e043c050070768441c611480e0005020b0000ba12521038035040040715010b035900c0190720442c480090308001d00a442c7c4040c02e801103902c840e460300d20345860521014000c90f06551128014000d02da070620840ca8405014140341c040d0098000018440c0d000300c4004dc2d91061010f1000c01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 363992670 1250 363991420 363991427
    0x31b03150c1b07150f0e040c0311130e0901090c141f0302030a06080106080d0302030c09031c0e0405011208070501111c1103041e050a02130501090e0606030319 70
    0x8241c0c100c1818894440a0081c2580d0f466020f00e2043c031421120745010a41e601c0d000b403032200900e200c15600d5142e00304100c006c0100a10b5510b00c2074042599031124054100c0c02c3c000200341c210f01d03600c51625081e281141d50103002e040100a00060390404464500042c0707c400702e042500d00c2402034148500d440d0700487e115841c0d00c1040c600b0315200c0550104126010b81c0214054032284005001c155104c0d90f03400d09036196481002c100e540440c604200c090310a0340910b4200e600260000e25080101e00000d1402c0303070412203482c01c8200302c1002c1d080e4036084003c82840c5101550240110341c50041d141c45000118000641000000620201004020362002c0c0c521030306040c0058584200040078020003690b041480507071450705039082d0560a070320307091300e00c01c550182c10030311804a044480c108040703881804551b40e204414004005954002e94402c2a00421030002041d61402400c01c0c00c2d20481541c1600d1a0403004c140b12458401104070340f0004a50300480d0600040c110084 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 363993920 1250 363992670 363992677
    0x80d050c0a0629030706050a0c03051204030201270209010b0304080c0109050f071e0b09030a0602040b090a0b0703020c040c0c0b01080d09050a0b0a0c03090302061206031b03150c 78
    0x10000d6203484000d4021400e400120340d441000c000d454810701074440f0034160740304514083c1c640840c1b020312241e11401d01c1004200c030107500c01c0c9809420b01c86500c040c21241c0c2420b54049015075103e00d8032240f0861440c003060914100c070b01700c84000d24000d8011802402c018001c44c00c00b4800000000d0910001004448440a20724001c10449603581400c54585607104081c076042e0181990014040005006480750558624001c1d0403841c6800000d07100e9922144c1c410b501800764000c04008900c8610180c4001c00c84103444a9941400400f0052002d8407500040511207051080f500481ea00003401c2510b02d10544000445500c003001c2914012640740006000001c801c0020407040030103d05503044941700e80b50610010780b580100004c594850040e0b8140d250b0034040211407038410056500b9160017420848652912600030541c103621001d50303031050646a0302402003d040811040807002d009600d40c80c072030108000040d03101c0184448000003186020046952801e41030100e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 363995170 1250 363993920 363993923
    0x60306070f080f0a0908191407050c0609032b171302010c140106091a030a023a0809030c03120f0c071502070e0c0703050d02030a0b060d06081006080d050c0a 69
    0x71948881190703c40f11030360048080d02034001081c0c4e8204814000320701003640d0700c0c1e132b40c000c010385480207043d010702c556a00140c070b94a80c075120b10460141d20700892030061031110b000390240d15004282d032001810410301c2c00709084814001e2001c11880e028111256031409609107003000d410034840c1043c018a00203500e61501c0e039403030b1450008412801d54407200c450010482c900302c05074041810903840700c8a00340081e4200200d0034500b00c6c1d03010b0100d10180c0c1c070003203028000701c035002e10a00401c54008420003140c60320400151440b031071600700300c011601101203005061a40c01038030070aa0502485100246a0030301103032803851a0f41c24031050000d064800c450145c2c0b01a46035000b5921505841151001c85c0540302041e80243c81034119008581c16803540340c54002240340000003540024580e845165454030503041503a07030b01004024105080c1c10102d0018285100181003120400b10480d0003850041c0c2081755540110700341165540604041b0b494030f40c0c2a0300141048400d800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 363996420 1250 363995170 363995183
    0x60f0f0614030619170c09010509010605070803070207031e021e0112020c07080102030a06151716020c030a05060106020c1e06030702100e03070611310305030c0105060306070f080f0a09 81
    0x40c4105c0b41200040c00a070700e110201c544400340c0c0d80e11024084440303004e004d142d00192041240340040313414280110380007031003403045400f1103640b03440b50b1100c803202000440d8804042080b400c2503103020b180c00e841d003c0b400d10b00d0200302d00301c1d05e001034160b40c2c8d04102c51442c540c001c626050f4090050004000603c9042e000395903a00d000c080000007170000e80903004403251440c1850010512620a4012410282121520640300c0c1031201004686040c0d0780c3c0218840c42e1904065501c042c06040c0b1060302c14402007502c0c0d410f014000e41484800b03416103004a8180000552981d203190a101000c001952099500d446e0035404906001141d000c0103000d60070a1643c1c400490004010b0813594000d15080041d90f041d280d0b031aa03a4420700d0584070032a800c12100007001804107407031241e412114507c5400c091350320765038607007580c01204020883e07940d10002c005550400b4410300750b2100c0146130948800790b0206020301070103030181000301038109007000104100013540c441c0300030540000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 363997670 1250 363996420 363996449
    0xa0608060d0b09012007151512030c0b0108160302042f040305010f062313091a010e101e0b0f07060b06030c0d051306060f0f0614030619 60
    0x20f03109010b0400ca501c03109040e0f004500c00029100400305072010f91380d0007095034042964080190000c0d01c15851180302c1d11418600001e80c80e000c82c82d800904500c60388554002d0105428040c0c501a01607119a040e6002914403240080710f81100700c0a90f1350482d03002411143d20190368800c0000c52411030510b1000e12840c1c00740410140141c802c4a10641c024002c1e030000c000c40000756140340c855115400950141c0c0e8202e10300f154104044410080c01107031036a419540c030002035401d00c98058501b40e80540c084415040d509520740d000d807140c10041e00e000c1c20100d5400f20310f105940f044000801004c060072240c03020307000d0030100070f08012a29035101c0403002d01d506c1c038542c00b840c02254010b1610b0155401420100d09a900c288038604846040042001e40b010107480001c10400c001020000c08800044042c03140b900540120041c00d42100c1c1481052181203c00e03400c50007c2c00040b0140328140003c0303030203c07540024240c03080c9002c6d01550150342d80d080c02d0351300031210702010706 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 363998920 1250 363997670 363997681
    0x90a0210110d020c010e060a031407051308070501020a08130e0a051f030c06030906021b06041401140a111603120c03020f030c070f0b09030301030201030e0c0a0608060d0b 75
    0x4607980c03000c11910640e025407000741c00036030360b0700d44c00540180400d10107946c61040b854001e000e0003d400c4241404074590544803035401c1c5a820880c2c0f4540410f10100d0074212403d0140a000d000d41440c40090820b61309110002c1d42d24606440c1c001c12000740000d000001d0081911204003c001001004507907007840001c0c240644002c88640300e0741c1c5152006190041400710400c022250049a00c0c440c01d0f007415000c9026200303d9400751142030b0200700c010804401010000d06030310b00303a00941560306180c0342100c00c040c0b5104d8000013680c1000d6141200031240c80a140c0c105081c091f000812041c520894800c90195100c8051003204600c0600e082c160001d8202c0800031650a08100d140807070181a012030041011901000d41d0071301c0000c0444050300c00500f48107000f415041807084460741d903840350704821154614180c10100c0100110358043c081da02e44070405c00702800790200040c0c045402840c8074801d5004000b841030105040303880d21600d0800e03240d000941c044a03864103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 364000170 1250 363998920 363998927
    0xb0c0a021c0602070818100f0807020f061003122619140406060503030f0d1802060a09090b090610032a080405060606040312030504020103151d06090709030b090a0210 73
    0x41220760b1b50410542e0b8100c030540703407490070800c4a4a0702d407500a009041d0701421076603084020480b00a502c1849031140c1d42120801c2401c0c814261800d288180c10300310324020301e10b0407220000e80305000320f5a8803400350411448440310700c0400e15130883c092341d80d8900003502660105d03900440603440c0014100807031139084402032056010764410301c61301ea924000d06940707200f010141c051410b8140111000d2121a402611804170003994885401441d03400240c1954050034601e0040340c40c98100b001452458021361405e0f500468804d0841c0c5010300102c0e10faa80f010104408165031080b4410060300000740000360802c1c080c007914043d109205010301070240644050f502480f400c400900c103440c3c207504035002d42e036111030800040c02c0c10302800ea024000c0074004031305150310350b520380b40616034104000e0000d00306031110040c10604413000e0803403a2800f618160092002c002006180c07a0060303080000c40703510070303440111681c0760000d0f0b81c148250620000c3d8860ba613231540b4a0701951 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 364001420 1250 364000170 364000177
    0x2070506070908030909040204114003030e15130302090a050c09211f05100806060d080d050a0605010210090515130c08030a0201060b0c0a021c06020708 67
    0x8208100c44494030740070415550800d180c03060100c07079802000050400e040c10702d545508140b0280c0b02007244500403002041070307000303040c05c00414082d140803184000002490800321b10200701075884000c09440c400e500f00740c15401701506002d03001080c6001510f42035501050381c000881030f162950980c1542842c500c0e282d10081e8410780000e00425840e040c3c41c1700d80d5002e018104110b030b04d0007009400340402c103407001c00889442601203030844803d080610403040041c912a0903242c4104402803140100c3c3c10140c440c00700d02e05c1c0c51106000c0340c44001501500010219a0003915105502c2c0242451143d803002c50041c505090500c40c988015030003140039104240c00799000b030074000c101101281c480910240c4a5444803200151414070602026001400b84a440a00c07000b1519025509103455002e010641c2c030000d14212940d9080c481d80c0c010b800480210f51030400401551651507041d5000a803081d141481e005101c03800c410564031a456103d4015911441d050608011a40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 364002670 1250 364001420 364001423
    0x4140c0415080106050114120c0408150403090b0304020901030602090f06040314071a04030b040201031103070f0912200105091801030219050108070e040b04060803090a0e0c0301090207030e040603060207 89
    0x43c02c20030041415801010801c00c00f098036201c490801142c003d085800392230251490707031001800c100100e158641481044e2014800701120680c0d42498a8001c01100b501e078007000c01d0140901c18040160313500c1d060ba83c1104c0c1c00c22809070300d41407810001001016001d00359548500e002800008000080540012400c240b00c280e5032000e640745000100300100384200820b0030b0040105000052031000c0c0c0035049401031500040d107000c401340029450b0720030780f4a038010818804400c150355a010146e60701a0508007010140c50b5032503a00d080260364080111035100d0311001c20348070036902c1481566034101c0c004040003140380307403c140701c1d281c84403e00044e40100c0400c01e04013010403903070003d203017152410307514ac40c89030742c07449411140c6260022959038080d8072507005440302da0380d030300550b00035201010181d51b4807000c403c200241c03031000fa4060416040361800b0003c6070480001600e045610b070260260341da111a00d0100e0b401b1074007200c900d512624014011052104990203840d09a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 364003920 1250 364002670 364002673
    0x50a09090b0603070303050f070c0308070b04140313091e0501030c0906140d0308040c0902030c0a0e090702060106110106030c12050c010314180102040b0a020616030902030604140c041508 82
    0x1e0310b80341d0a140d00d80c8803500018001c104200900440300160300e0040034240d010312880090542c490340c6003415584880c800b0358880c405030b0b0500082c46482e250300e05881051000851920410321140c104112491040a000c25681e02c00005a030000307a140d207100c0340000c0320400c2550303164680307520103180c94040c0c0b2030090300d409000b00d4030191410b074005465900400c5001c100825503012200d40c0e8005000b120502400e00740003900d080e07940051409900d1041c0132688428200000a0074039410004c250704c2041d028040c007840e03a4000c10031034103407002450118156161720403058054500ca9100826015083c42c5c001240c07480103401c0500c003403180c01503912420201004405461100038031020b080c0c2490007140603e502401c000e1702c1900500000340c1040d03038840c1c02c0c00540c0c1007141c14402680001040240044540f1682414521142420003445a442c4c0119076207004c02000205107070030005216000b207004000000300400f0041061160103404810450340003000e1141c99041e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 364005170 1250 364003920 364003943
    0x302040609150203030a11070f03120f05010e0a0509030f161217011701060e1005180c0d23090a12030c0203030c07020609030a1a07030902010e120106050a0909 70
    0x45001140c8004924003443d8029800c0d601c3c0c0f50007a6000303110340801503088000030054040012594020741280d00d000e9220350707900c0400c86a44a054880003003521340d641d4500320042c40f04622034003402c0c1d00b016004000207110361b1503500c41032444c441c1810001c600d04010402804440030b00700c1035240c440c03103890200c0001404103800e4845401d10204215030041c0d800040c802c2c1d0301081104961060031000100f205079482801310500481a5444603d0840e05a414800381c10186001da8501180d140ca110380e924000c281c0215a00035503e020824986a030f80002c07501c4c0f041444443d1020b81d09240700e440742490021150f03900b25691085035840d000d41c0d02140418002d20500c2404102d41c2c020350320316a520b1401240e542d0047c00203e0384004280302440ca103440402400769403911032885092303082c0b480c40a1115240d0b00803d241e0415040000450050768080c00407540900180c03540d46410140440c424050855a0060340c2c0000120b200005c41c01c1e82c0303411460380e2500a0b01250903 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 364006420 1250 364005170 364005179
    0x60201110313020f130c020102090a0617070804020d021c02040507031b1211030c040801060b040302060901030e0f1b0103141005090711030307200c09010b090d02040207030302040609 80
    0x80d036000407500c8450034a014075203800075080595618002160007044550540c081c0400c10742118150440280181e50111b810b284a0801c2e0b011040035281d60f0800070035204d94500049640c2000518a200300f00584011034115140c50f0b00300b4160384ea00400c404081001c5964400b0f0402d0040400c0e8803441c106004518054024480c0d10350b49202d2500c1a41d4620401134280c030505000c00303031400303100d40c0e403401250f09111000196000f09144042503948a140098560035500d87d0703040500500d02c10001000107980d5081280c4c1c0c00325080c00d011888084805540e03003003d0800c600c0c41100e0141c03c509030389149a54000c60103a1100f62010031015880c45080342910000700c072141d00d031081c248410700c09403800302d400740d41c01084d502e0829024010100083d06540095070680042146030a00340c0034014400d450341c4180885800514114990000050715540e041c0300d07036031302c54400080c2100991a000030305c031100340d009003003590b45008919004000b984036200f02400281c0c200e41c00715 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 364007670 1250 364006420 364006451
    0xd05281a24090705070510090302010e070e100e0403120c0302040501030f02030415020c0a060e0c041a03060411040e1501050a0f0311040c1106131e0203070320061201060201 76
    0x76049103018100d80515a00d40700e099805a010701421343c0c15104070340e07107400342d8004c50142c610340038420303070010903a54640384c1803e2426905d03070840c414a8044008200c203401c138964207071081303921000681d40280c8443c1400e858000000d00f25524041c00c1c00c2c940180160150000c104545003030ba010030242da9100c4d100c0e0106d00041d54001c1014800e10088a000041380d00603102a00c0210280c421406450351000c0444407007600380e40143d04811503001d180c0c1f626120b12114003e03600f0340d941c040040c0d480020b8036018000c0c40141000541c60728000140c07a00e80c040d0f40c43c0911001100c188220f0a600910780413001d00c1520710480304401c010820f0075030840000116940264004070418a450402000d00482100038040041044034244550400c03c800c0307001c0c00d0b07800c081c2400c440260800c400c0d0800030200d4000c44070648050035005072000901c1d041225040300c083c402c590746528417400b041c0d44a002495011a01080c032090000c50902c00d42e040366103030340081207807210151014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 364008920 1250 364007670 364007731
    0xa0206013b0705040b0d060503010c0801031e0302071802090f0117040605060303120103065f280b060403022421060d05281a 55
    0x80c00201c02803648804201d1030045540c2020032400c2040c03c050315061180b42ca030701700481201009071a0102044142020f200e2142d1a01180c60708503059030541c1c0726000203003142130b01c140280304400c0320f00c002e16100380503041c043d03c0d9000340102400c040322080c0020f90024640c6500ca0747d90314020f0060b0703602a810702d46c1000f0131059005690743d966222000245402000303103406010801082580a6812920394043d500c40c2000003030810704082504403401c0340d860071510301c101c0d01038070361115580a1810303e020803420b58130f81401035170041004522000b0b200d80d003910940400501030005640c0007840420110b041488099940168400341520040c46106070001010001800942098080e00b041048038000c5805a0800e100c0220000d03800ba0090303000d06402c5103600c210565052551940100d81102c04100342e8150303480d51511b803100080301007007120507a0880300c6045a0b91038103082c029080f4400041c4110040090100210308840c1100d801491036900c03140d5202a4064 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 364010170 1250 364008920 364008989
    0x60304051519021306120501030503041202060c01060b19141602030109240f05040210030902031c0518040e1b1503160e2218080a020601 60
    0x8101064071012119526440507200ca03a200c40304000b40010340d40c01d40020301e40c0250b070781381043c413a43c070b4104010450011b0b03419100525040c90010000304034000140c6080d14841490044441c004d440010000d11030740024661650074844006808002c0c4006840004605a250a1407000c0d850003101d85080c001d600c1d240c0810180020f8040304080c51032494407500c00b60001034003119036116050030061040382c0c4100449803ca04e140084a580102c803c0e090501c0018082c0d1700305580003071440100754502d1420199100c88100c10b640c1d041100500088414032450000f28900704014003a40c49030484000724000b68851280909007485107103400362045c03018041101507560000450603d00c1d07102640f0500022002205005520065004041c2c11202c3d2803020100400a440004c03900842071059844110070a80004404080303a071085040d107000982400801030361a12170402c5201070142c2c10041600c042141d00000c3c120306a440400d03800c40c950501c881180c920b40340350030ba0b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 364011420 1250 364010170 364010173
    0xd0f0b2106160309050f1c0c021806150403080a1707080619180b03100606080a05070221070302012703031a0d0803070e040b06030736030c0506030405 66
    0x9500c80301c48591800b2500d81c607140c0032414031200d407660b5281065808060131b00c2e412902e5244001d0045029002075880c860621120788881a00000c40c4402e002c9112003850354000b00191f00c0742d40d0b00c1c401c2190034a80c0252240c0340c0f5228209a60580c01a0765100040f0310070403040c0001800000a0600c2400d03075555100007603840e003052002e0003150400f0269240702401c0041201e0700181e2603500180103c030000103c100201c001c0500d071440304440b9464051501c442440007681c460881303503002204002c0400d050b1166071040b460007040400784408032800052034084c040c41403004000c4030b17000354000d012082113441515805e5580a1549003580100c01c40c040000e070281d0442c030803415414003600301040160300490454200ca0001301d0300d400c0004108030316181c1100c40c2c001e050303900359400c00407240090003091043c40040c02800c14010420303902d40300d50350201001c452824424102c86260f4150a5403040d400382140802c07548042564000b0803179080060550f440f4640000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 364012670 1250 364011420 364011433
    0x614040c06030f09060e152412070513020309011506050a0c051e1c0503070f0516060f1e0e03030103060c021603050d0f0e0102060106080a020d0f0b21 66
    0xd064009110310f1a540c0301442d22100b8400100380300c0d1003100b410b10501c10103807c42241c500304030a4002002011040c000d680140fa400c440400324107103000107070040d2000041840c508104600e0042d041e03010a0f0f00c40b00080c0d41000456180d000ba42c062031200c00284000c085280859041a4060003100000f40003408020761b40742c45410103208250260082e215408041c4465003102c60100c0001d00b003950010504022100b2842c104403c052071601d083c5055041981e001080d085055048104001b00403800120500304c2280085c5126804030003003240580314804a0040e006024062030403000c0715500860700c100c03a01942041601c0103002d189942e0940c4e88000043c1407116040342148600045d0100c802e0452011a010754092401010031a140490040501204d407030400104a60b14150300050790b00080c0c028151880380c00d18008a6031824031580090290800741d0084e01c0c01c1c150522a2508164802d10340d131031082e90108003101c00704403072403015042c0380700c602165400031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 364013920 1250 364012670 364012679
    0x171b1b01030209150408011b021c0305040c0e070c0209010b0f0403080a0507050d09080c06090102030a08180a0312060506030c030106030f1509050f060909030913020c03160614040c 79
    0x1e6004080000c001400e0f416101310341a201c3c5400d4215070800c4580d42c3d901c2142a40040b55a4003803406041a48000c160203a25403c0a0070f031140c030180444207040e200d00204007003114040e106000307030915080000306850150f40040c0117208455050b4040ca84c00000030403203d0110007107902041c416030716685400e26654403900603600880c081c0e420441d0a00901000a909115a004c55040c0fa991000c0881c208815681000045091203104110402201009980110556030743c1c10140c280b8030742c281d56203c20000d071020303040d42c0200c0d82c2c0140c3c5000c0c1e0406400958450248202c0c01c410080d031500c6d1001c4c091070707104c2075032001100c88007030004200f400d219420039030000b10604004560700c04a4500004002c0c619003006410035114010001582c0302890700d42d40c082c408036101e660f0350802e240d42607200d20404040c01c0c028a4124500039600051340c04030f80f901030107582160756500911180c2020f03002d41490132114a421302c51001c03049035800c0c0304d240c0519081400701d4400c5152 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 364015170 1250 364013920 364013927
    0x5010f0315090507030c08010c030504170901180609180c1715090f060f0f0901120201090b130609092007061d1b0402030906071b171b1b01 61
    0x42015901820b403996200c10020303409109030001140b0a00190007120706283c1c0306c0e400d440ba400d81580801d0301c0e2004100200320500b41403084d080248038019030781e1b400800100c5082340c20300c900542142c038200000601d55030041c44503048a801100061440c0c082d40206000d443c001d0b4140f00000780070705d09400503880221402500440403e5001c04010346201c00314036500c03801c40301122980a40e00030030006050814509020f0b0108440180c01900f4a0000805208040c0210040044203040e1082164001d00c0c0304005480006442900c3d1070b1055050030500990380941c40000761605400500d410081c001d10558107050140040607142c50480188180c0002e0000d030342154a030303e01200304001e0810003080c107008010281c04040039140c8018555864019060b00a82c030400c200400c60301c0125000b40c2040c800e140c04002982c0c1059442210000aa03000d00f951140c030f10410340707112814000b04240c0c06080418401041611032440c6c881c12340e9265036101c1e0210100b4000035611 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 364016420 1250 364015170 364015193
    0x2060a03050c04150c0204050601170c0906120f010f080703150f09020607033203010b09060715050f130515060a0902071506050411040608091908071505010f03 70
    0x92010b5080e00309662031a402ca400d04c2010484000710300510b440205506142c01441e5110b0028241617011581a45960382c074154000d00c41e00c803810002c04c40c03c3d8690b031114129250b101130541b0450ba00c0c00d00003c0710054207400e2107182e80d844540113000445c400041004070450750801c40f074940101c0c08840c0c50002e02565540480c800790b17036180100051f03032840040c1504600130341c1c4510000809029000e01d280750600700d108006007100c22190110068001c89064a484c100c0042d1103202030400704882e80105100140719503000301080c0303121009a0700c8284202d0701e0035510206070b1076260340c01e085440c3d1114054025048841c0180c0110048008150440c001030803901545d0b946d40d0b10b00342241c006900c200d60880d203450340c0c60704021042c021b40d000f50104a40800c21000341020100451196104a1040c408a20005006504280036411a0724a01042045243c0b40b03031034600714580c0201070440301803896400041c11348880340315043c1602d0a504003e15000d055440b00101d011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 364017670 1250 364016420 364016431
    0xd050d09021206100f0b070f05010213171002030c03010501081003051f0506030127150609021209010b03060705160c0906080f0105060609040203040f0501060b190c02060a0305 77
    0x191910190030060312140d500d42d2411801101902e85401e00b030280d2816601c0e59170140204a0b0068800d002c04045070003210b117040c1e4808410700c900206494a140640a802c000d000c010121503000981152410000d04031a910384060f038070b030206000c041004a020585011400328410720040c0a15409071110302e400c000500c00c040d0001d6a26503902e4a45441c1184440240d18181f414040c2c80380240662a00f00e807085009014440d41200d00c7c8044a60b00d00d038884148468540100900022000f16440001c051106000040c1c031040100082d40c42022614412203c1030b00164000c0010311400f8032441e8000c2c050503541d1141e940488003a0820707025141e841c241c0e2002ca40024030290342800051103102808200b4034074241351941000d0154800b028141d040000704060b903646c140440c1c20707115044a0041e229202c3c0c0c145042038006042d8001c24961901a0200319644104041c0511915601c5d00d0703e0881040c2100316a89060701500a420410500c003510740c96009400403035024 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 364018920 1250 364017670 364017697
    0x609090f021902030c0705030a12052203030e150c1b030c03010f06050a08060c2703061906080d0905060304110d11010914030d0c050708031201051f020d05 68
    0x5810700700210100344403600b40150344001640c0354001d10500030381d0002e000403070181400c20501e490780301d0a01a07030b12805d002c0100004003d50441c070007008070394200024912212500d511380c0b80c050004440365611510810400008540d1540c15030100c801422061000d01170b050f0004031404903619628a01036418020f0441890203074a003442907546030000700101268082ca041e0902042950540004803035401c03000810001c1402d0800b1540300d41440100756000b440c03280e18030302401c2503150070f1607414055041440030113030a40700c4580846107180780c00c0081542e10882c180c1d40340c0005440c9800b14280070010012440c2c1301c0c0145500a0084d04882c940411950018443fa02c48050440c0d04407001007a10049590280400000d030004a640201d0302c0c1c1c5020000e607840010302c0ca07400401c4580b07a401c03c00c0002c148140341c01840d0310b2046a803a405010004807011100740503c50242603c0303d22207080c140510280d0071040e100f40c001e04412007862400311401da01c9011004203c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 364020170 1250 364018920 364018927
    0x19020c1f0b0402070c0e010e0c190e09071d0a05010c0323070302240f01030209061207090b0f06040e130515040303021c0603030801120c090e03130605040609090f02 72
    0x140c503140002d0a04030300c2404001c06443c140508111986010b0302300c001c0c51b4081000304912504044203c40200062601582e900e035205030003211025071000150390017105800c180100b9035040040356101e101c4200b80c0501c4400b040c03081c0000615140304050004840c1b4080f000072034010300001c1ca1032511103d01942c854944c0d041580e040c0c1c0256400c400592010180c1c0c20144006140130441d1680820080898103250351002181d100600000c2d210b1040c2030003240c61642c4216a501841c0820f0042c2ca642c0c580d00d8500c44000d20868a02c140945002d00003041e0a18189003120b065403c0c10010302d0103516031a40c2c2d41c1c4585d03804201158039104d120190176084401d008020301c038034400e98026039134070100c5c440038101c0e0000c00340404100b0f080c408288002900841070606641e10503242c0002d40703800e0b082c810544c0344140d109038a8246003000c0c005808402200800840344601a07403040965240c0040343c6511a81c82100006407138800240401c5106802412000c66001000b506 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 364021420 1250 364020170 364020191
    0x1a0610141e0d0c0203040e071409130b040e1b0901080d0e010512131e03020604020907020106030f0b0103020907180603091a150907020c060304060b0301060f0e19020c1f 74
    0x212000c10203c0030150303001103400c1103942100c000c05039000b40c3c1c03843e00c80101031200090309801c0c014001c0d010301c0750b803a525001c030800c0303010380c8a441c0591000f0414400d007440c0005a503142e16698890117400c1d030b8030112125041c10a5041d55040760700c4c950003011100a1303014121241a1340c4a041d038100700c0100907042369065150000c07800f803604001140d0100d160791070000c3d41d914210404030001ca01c580c0800d40800d40200340c02d50f005406446003c19035580041c200d006002d40d8000078103a8420b0a0f0003c1405400c544080c181c034800c1e658030745140c81342002640d40d00c42085041d00d591200000030320000b4481c1d0070001c1c03150301c540c1c00d949860b00400c001e80024001103416030000d1071144050180e038500480f9043d003055060000e0003810220300040390092000030005480e0a4482017600c025442c258414002825500c204140d03098440c6180b9000c603505071034080d000041d00450007981d00c064421240400c0c020b40092100103800020110b480d480354900034529699500c1001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 364022670 1250 364021420 364021447
    0x5060d0209161d090403270605030402120a0203071215140415050c0d0b06071703091b101808010e030d230c0d091a0610141e 55
    0x1400303400b908522014058072060000d1040c500720000b54011012569014510740b5001d14554121b0740510301445801e0901444403108001503045c061010302040d800140154008081c50085200300e13008002014044842c95941521600c06540b507001032104016a01d00d80d03c006070854499400ca03951740303e007055164121030450300030180c0c081030300040008002d0034030000c10607204107280c03c102c3d03428850a0405240134001c500040c80f951000041c01a6a489042d03503a0990b01891542850309040c0094409070010350340c04120303101d03040c01c030b0b51400004000d5020404000d000d1701a501e000711000c96070f0720354201f100010b000c0c4034003021036070030800e02850181f2400c1c80003d580d03401c1d0520f00790003110200c070b001c43c00700d03400c6c0300d4511080c1540d064603581107002d104c5841c1e200d01c0c00c90202c800420166000403d221400f801a0010507000c0c80300911800e0304840040c02d0800d500c0c001d8907016480310301c5010854003003082c0c4007120807000404594049920f4620b0074440d0191260 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 364023920 1250 364022670 364022689
    0x14040501082d101a040504030504050607050a02060d02071e02030a06051914060a06170a020c1005042d0b0c0a0c1e050f031602060a0507021e0f0d031205060d02 70
    0x200c1041e02d4a022044c0c2000c205400c010b154400d440c100914601600c000705940102d0158a11482c80081c450f001d2007003c0108140b002c1c2c00603c0079640e0000900c0b460002c0d8018903049407201c104001258010600c0305500e12101c2e009006080404031541d01c00004003030050403801d041d040441040b03040c0701503108280c0b541d01d54002580e001d040c0002046507201850340520200004141100004080751031101d4000250010168072418480c060321700700300202c904000c1161034202040180010307150074544040e0301400e400d035000751040041c0300303680f01c401000c1c2105041c84c020a207086070a0000340f2550406140407211594503980d0000595004aa800d402540d031006041c140541404004406400d4000562030002d201803108009655658060711075080407a445002500810854509960041200c451207405001181c0c000078055412400348440d58001050740c100701c0068003d40740c158940803d078003501c0240c100034040042c441c540000031400c81000507102c41003132 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 364025170 1250 364023920 364023943
    0x160f0819020109170901020c15210118020304050a0b15060409021206030c030a0f1104180c0609180908220815040c060f021c0914040501082d 62
    0x100b40f0b889182000c014100c10f000e2188440c00003000094000d07a000078136030b0305080c000c0d105240c11403800011044d1b203009210000307000088001104131080b400903400740c181c40034003850550b442e860b62a001c040313000c200c40050166010800303410205074403601c110391004c401258140c00c0e041c0c02002c9a5150842e502a98446401141a407034206040c42d070b40d54429015001044007a5070740001990700d4100c40c101400001c22520380301c00388140001c1d4504604006041844451405041e5101c0403501c80c50a89101c0340c0401c0c0494901e1040304404120303040181e4410100700014070807002404507810490300014100007030964440001c91802d5030342d038503561160750f46150010141c1000d0742e0108804500100d02c040200040140e404401559064984949006100c01059140a665240144840180c0b04419040301c0e80a00c01d0402d840c66000c04c0d00000e0443d03018441607860a0090602036040707122118100100100300e10032442c0e2400310400c1000200d2811402c26140124 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 364026420 1250 364025170 364025173
    0x50d09150c020f1f141306050706020405041b02012f09040608070b0c06010f0e040303020304030314010801061401030204030507050907090e010e060a0816030201081b0417060c160f081902 82
    0x8124049030708140d0251070100300c014506c0c83c10803664141c01c290300003405810240301001c00d40c1014892075034195400340201603c03c200c552484001d00c2201035100c802d4034019801c0c410500b1030800340c000207038071101302c050706075506000d404400202e40e040b22100c01d4200e036440390001070140c41004120024181c910b100f9545504101e8a90f04000b01604401d84280c43d00c1403c116500251000590041e0036203401a140d071210b1600b24050443ca40003001d088002100200741c401e13041d44a0300441d40a0b00c01040300e48030400040d401d9005070701c4060500d42250340d007040700e8100003a00c2a4800c1c0c15160000c807068807000c10502ca01400c4c2c0000c234144443c1410860340b8181104c41030068145800100128404007070110013900d202d02009040150314008030f0000201c011004117081c842d003003400c0d1519100e0704600c8071850400091032080c41060082410b0880040807203012182c000c217141d04443c210b4940d986045800c0808030740903a000c11140c4107400d001120b03454080410360 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 364027670 1250 364026420 364026469
    0x10605030901091b081509030a120207080309010e07061409100905030d0c0b01050409020f3a060507090609030b0c0d140708060a0f0e04061116050d09150c020f 70
    0x1080d41b62041140d40361029074580418400340040003c00d880485104d807611024401c03185444202034040c00000030030380540401030100c514019001541c50790490400c6980301d983d5404121100544819180f1882d80100840c9040f03040038210070150041906080703007a9030f554000300f0310b0003842d010041e000405601e4001c0800c010241000e0061508540510080d1590380000310004100c0100740d229608071016641102100241240c2c1c0243c001300003a2200c0340d221006500190311324044070441d15210000346051301071920700d41510b01903555100014210340e0f800c0e40354030b005058490110803d10141c02007490364000d50074843c945071010500750400782c2019081c04009882d0a2103404050340c1888450340404115040301d455a01e401c0103501c541c14050000e00e8080c1034400080400500c007200c419402032180805c500c594115008841041c800300d0b0305a40601070b00c118102d007214141802031203456a000100e00007800c0070b041e0b0315202c0001c0c44030a503040c001544d10a549 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 364028776 1106 364027670 364027679
    0x20a0306030507090e0705091e07020c09010b0a08060108040233040306090c06030908090f120618010c0516030f090308160605090c09010605030901091b 67
    0x2d4180d400882d01e400c04440a00580d145800ba50300c101040010241031090509101e42180c16a0050000080e0349900c0c0541c805440d200440c421105145c000e6621100514001c10030042040e9032a40e11141c0a4860070340140f1160510069400f0040075868070720f045d422400b00c0440c064880e010311070810300c1a40c0580071055110350301050204c10031129520104041d802101003094003540e9a80481c240c41d0240740003070281c1c1c424000c050072400d007800c00050071000103001e808a440ca1002c800d16002d800c4886080500b00180e5074200c007842072080000c05c02003403400034a80290718829014a41c03c00c4001010020032618184925100300c042d0000340d588592800d0350b4031328a44051103544007180d4182c82480c54017020481c1070900207404100114042c0c40491240c0c42c2807000d0703030301d600014120101c554842c1d07a21000909950100c0f40711040c032000080120f41403 = true := by decide +kernel

theorem cover : BRFrame.Cov 363848920 364028776 := by
  have h0 := BRFrame.cov_init 363848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 363848920 ≤ n) (h2 : n < 364028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
