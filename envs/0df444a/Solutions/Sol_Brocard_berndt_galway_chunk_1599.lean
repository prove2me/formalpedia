-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1599
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:47:23.465554+00:00
-- url     : https://prove2.me/submissions/86a0ca3a-82f2-4136-8649-2e43fd4da78f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 287410071 ≤ n < 287589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 287411321 1250 287410071 287410073
    0xb09010c06061d090d0f021b031606080a0506030c0d08130306020712080606161101020f10060503010509010207030f1d0901060804050606040c090611030f0307020115080a03020312060607 82
    0x10450f50380d58401521000490300748030708500d06040030301d0746220802209142d40844503a00290f0800f40f00c218420020005c01d000c0b01003804e001c001d40d040c10707950a400c01c00060382507008081900c1603c9882040003c4d888040030951074a115810a560184050f040340740418141c0d002000d03429042680c0c01e02e07441d41ca0f80ca90082c0d030072140c4151159007031080c5416503540c0004015a00c100304540403031425440b904070f50006100068050140040301004030041d07402001400c48034034103c811a950400e0100100f400b80441c0e0142c82c0c025400c007408a112440b0500980310038642c1502e40c88040351004404a03020750500c140c10522102000b5424090340380d16081502030072107030361029078a00d8503040081c9000c2c070141441c0d0295140c0300701d5141891344409400d0944047e440e1407008810401621443c5006441540c0c000d03c1c40081400384d600d40560041031900e480c0b00f8001e560300d6850304503a88031503000300c0140140c0c00c1004295240502090640d0f070001d0020807503403e010342 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 287412571 1250 287411321 287411339
    0x120c0705040509010b0a0602011103040807080706051008010c0203030f04030806210105040c0618060f1701141002070b16030903050f0105040c1403030409020a0201230703060f0b09010c0606 83
    0x1981c0644441c0d645688500e103900300007210b43d01607d411300080c0904901509416820320000f0700103080060042a00c0c01000340c0c4c20100c40702550403480a002c603050240700094100c94501c1403e03020762030f1418100e40c450000c019a40324042200c0009072681d2280c40c1503070131400041c80d00f94006042c0000302c11420481c83c8001e05c11046400001d02460700d0301d000040f40c9030030740080060106968420020007a451020700c00c1c0c582500c2d291051511151003030728110396480449400c2e00d04000041902c401c48046c40211000440780b0007031040803294160703181c55242c013503e00c5040d002c00040d01e034445c00001520b0940c0c800d10701964825500d850311030a1600d44031002407965154414041031006090032003000d00401d042561750b50700680f002070799900ca02e00c1542d60507a00804c59800b940d000b03501800480420707004054510302c03260787d01032a5140844009011905d03041000c40c41c400013101d2881a0780c400016249810f4900d40103642c0d0f207003509030071111641c84400100d00184 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 287413821 1250 287412571 287412581
    0x10e07030b01030507050d020616032a12050304230a0206040902030f011707121502030408071a100302310b1216050108040f1a0402030c030a05120c070504 68
    0x200580101c8415411850020300f8030f25680d014501c501d40020031400965100b07030880d003012108041c1d0004616182c90152204151003840703050b4a01803241290060650b41072144101c0d00c200195040001c102009031601c1c08140d034041c0075040030034810310040f4480c18030102c503038292401300c0e24551490b6000034a990b110340c004075002c40e0080144809000525412400341c01c000002481d098440e05030319941c3c080e076100709003102d0021991b8070248000c08941c500001540344065540e032416084c95801503000d0001150011818642074040e080e24100b00c41c06404500380c000d014030701c2e54082025900303c503810300350f48290018003900540300f40340f1007800328661100c02080c20641d401c10082a4105000c0300e80d52a089902d0681d100741c0e610708240140c4409003072a184035251414040ea050800c5a8010000080c1c0b600740b04d807403000c2402c2240702e103100300c2c100c840d031603060f905040d180d01c00004010074580c0408000710b0700d0701c03c40c0c0140007502040300403603031059980c00010342554 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 287415071 1250 287413821 287413823
    0x3070906030f050c030c13030b15010f0207081b1c03020105060a0f14010c0302010f060f1d040c09020304030504080a11090c1204120203090d080a02120307050d090228080706030b150903010e0703 85
    0x44021000c14032b1540c12001055180750140050a181e500d00b8400c1c58490148040004280c82c000c0800c0380c5039030725040004260103100f4a10000c1d01c980b480c01034002e01d800d0342c409101d02000315000800c8580c6480c42c5042e10b20300145070058039162001503506907040c01c011410344d500d0754003c8401c01c284e440b45034010041540a003183c1d501e032001d83c204889524410003d001001d10420001c00c6411580c0da00711406a0303c01a0390382d480341012502400b0360b40101c02c150140680c4a0103200031100a180c2c41070f401c0711004180d4a4030b18985a45201d1304030410075041100700050f020038414000805100ba1a0040e00d140442d24000a04240e1038401d0441c3c000b4008607406400507070400819a140341c260318482d03d141030601e0090454040c0c410390100807521012450110b498440102003080301030040d2185a00600e00344003075041c00c1c1d0090485603c1560f200040061080c0990140503001810841d4440601c4e150200c860740a140741130f40540d01da0720090840001080541c0041d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 287416321 1250 287415071 287415091
    0xa0519081903060506391908040b0c0c19030203101a030106060804050f030306220204031203020307030e1c080405281506050a0e10050603070906030f050c030c13030b 73
    0x440c8990451612406c80e008082038141034041c050201000000303c054030341805040100100c0341038a0400c0b158400c5130080003201f6004581224507100c000b607501c0030f041e41103c1c046c4443d1880158440c0c441c005220280d41644280d09100c000f80d415032104a0103014901301a61604d414408642941d000d0390207440016038006c10001404403e2100c0c52030344220310007a5140d42460800200200f00c89001ca03a1101c0c05d0310a04010100c065040300c0003154400c407112841c03040e1003806402900215841d6001c1780c01c141c2d04951200c00818208a0b68070008104540d030642d45008540301d10b0300410880709481049800b41004806140d82d4481481d040040400200c1d540740000c1440004c205e141031450814401b44001e40c1e6120100043d02d0482d202d200c5d90755642004100000312540c07220303420000010601c030301c50364803031050010342c0c500752010301c03800e01c14030003071030482d10704030b8080395508010300204034035000c000c0003403150b0003ca2540c003104035240e0b01e8007070708003509a070b22104c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 287417571 1250 287416321 287416357
    0xd0f0c050a08101410030912030b19081b13050a0207021809030706090204141005190509060d05160b03060f030109020310020a0903050f0a0519081903060506 69
    0x140d56809020b40354003004000741c8003c0d0900c0c280450030382002003c09180b0605044450946180c03003a800004196049007201411301007803400a8002d1112034401400341c403c906114a01040840c500012100c95030024102c1e040b5002c0a52a0800d00c00c1e000b951107403607101c0403848584680502800b8001240300107941d0a85031040101d55034402483c0189080300c1c6080000b01180807040d151017640000f00495501c2c1c003480044c00030300580d40704898001e080028032141d072416040400560300290303151403041007442017001c1d0002062295507800280e80c0c2c0058a0760418020141016200d40120b8000141680440410038242c1d00808801440801000030900c0d0612602240010070350007000391100c0e680110703868407010403109011607000103020844601c20101c100041d60003401742c520071800c4030038084d120010030000359614800d8600100c0321094100f002c0444640c0a01c420303103042004643c40c8991950f070090501415a00d51000445859500052000940840f80445 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 287418821 1250 287417571 287417587
    0x60a17070f1212030903050f03160210090f26032e05010f1103090301140402030601080c0a060804060605100f0201050a061d1302180103050d021606050d0f0c05 70
    0x400c0d695500800352108902d2044002c540b0f051190144901c103854045080c245504040c1c03101d10030b808006910180000400804000303007030a03440b13009850f500340c9810f581d182002c801503507404640505000c01008802d00060700d41c45550805c0d2650100309110180018a507100a07002192210a41c5000414240f06001c50447c1250700011010041080d1800d0600007081800850320711401d018112183c00c061880800070f075182d0b0800200244000071818841e0416a5000d89080f4003900c100301c004036007684007107000c6603c10809401500d80500d003240455506d50064000e03210907945140109131031b190b40c480c68403078205a880310f0350031903240134000303007100c0000b402c0c001c01614001013070160f01d211031050f80b940703014840c1d20039250b1910302c2490254020b01000035400050307500e00317005500305210000d041341e0003030040e6034002c00051020713a21460000784606031022240001d00000740141c0160600e2000382d500000c0c1c9a103200000002c03211102074a0f0b000c5003010841d20 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 287420071 1250 287418821 287418839
    0x12070f1208010f090c1218020604080d030e060103020904080a050c011104150f02031c0605030105070c051501050102031204140d03240503071505070b130209010e07020a0605060a1707 80
    0x11004000484c410042031521881c000d1800b00001045011103803620f0910800010805a0a00942d0014000e070ba0304c6a540b102160b41d40e100c3d0300e07600e0211303062041102083c800860118101ea8002d0040c00c81c84d82d8941e80d051050748900a5007050120600c1510014031092083c00da1014176982040d90b60b0303040180c4503402d50209100b07402007103450344841311703041d9011007a500d41c540300d800c40100820080c8843c2d40a810290020382c2c1562900d400c0085940d480380e00b0050550180060303800303601c898507800c0003040f024001d85015038010009210b014154403000d030f61040c0034010300f00c9880354600c60300d400e01907403d40c0400001c3d2034122000c1c1401c01c030880030390540da003a100015481c0c641800f2a807101000d20500204045031080400710031b0180e82210b00344d0780d004020740c80f1031030580881c0308410382c1d001c01a40140c1141c00003160100300e52a81a0190b0b0140c1c000b407201520595812014000c001d080c65000704020074001501d2402c10001c2e807001c61200003903c41c180c2080828 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 287421321 1250 287420071 287420099
    0x60103150207020a0608060a0b0c030a0f02030a0e0f060d02030405010c110705010207090e070b0706270209060906120f010501170703020d11010311070302010203040b010603020c12070f120801 84
    0x440d2510400c001e0005a588407403050407620a401c0084540ea151800511852420380c8030064044000881050040020005012040d02900c8220202030603000c1240e89004a00040010404078204000c440c58240c850303800e61500105140c0c9019003240000d0141c1c3c00940b012116070391500c481030415600600100c003150b0350b8074020000f644c5800c000031342e641300d24400c10303a18503504d80c04010590401d0100c10b024015000d2241e03968062450f02800600d1900700142c40c0001c00726081041c480d007650cd490a03c0c3c1c00512040307098503148108198060b014240310b0340300902e00c45d15802e00006000c0c4003480c4403044000200c942c50704801c0c01100a9440c10a43d05801c558002e00059403a60a1052507035001550404904040c07801640100700070714090030701c00f1020a802c405c055054000b544150b10600110045036a00c1c4d005030117034010010411025004807820760720050322a8050040d0601540040c8007039211901c41103140001001e200d4001118440144400c0c00b0321848 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 287422571 1250 287421321 287421353
    0xf0605010806070c0813050a030f03090902030708070e031501140a080109051207032109050d0c02030709020c0a06140609090309011b0305090a150306061b0605040320060103 76
    0x1411441c50032200007828040003880061045c0c8002c9080d04180345c00c003a0f4040a800050400b040c2c650b00c904007000690b800c40000c80010b4201000807515038150f00a9a01807001c44c1c56118170354a840728207803100e1212455481d003601c2000382d84080109032021507170007440d989005120603101c0e24240708045c0440d030070516090313050201c00c1380041c0001030709600303a1441481c40d507120400d610381161175001024072003c10138088001c8180b4480c10b580944481c0b0701c0754049a540741e030031000c01e58480070300c0b0302c002c1d40c55000318800300840311268004100a00006003983d100a0140d5201e40032100541408040e48003e80d0030484603007402c696041c0c000ca6400011820b0070142c000003003429488041c1c480401104058660426020b44107843c4404030007011040d0f10303511407040c0d50003010b4101e2503c00080c00d004001654034003500c10554040b0414400401c081c1c615120040902006002201000000694a100d00f0b001081e080e43c00040e40010340000d52460810384e071124100c0366 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 287423821 1250 287422571 287422573
    0x120c051e011d070b030c0c0d030f0b030a03080126060405030a020d1713030c0803150108130201021c11030f0a0801050411120603010e0d0e091815060d0606030f06050108 74
    0x240b50322040d60000b003140440b00031542d00e0b5a20750300c0c680680e11b14059070036010350510428083e01e4815030590030940345011300d51b000b00507040c61441010307500e4564080107004602c4100060001d81c070070304100d182d030940c5080306554000e260308601d40381c60f100b05e505490f00d42000c2107941e221507040c0b0480198622900c0e14440d0900030700306010a280300500a0308955910b01c0c0d0250815000300c0100d00c1c0207030400c1c512600c80c50b0580115280f41800b41c0020b000610480c00100c1010f000816022080d8042c0e00901c0300c491000191800429038510781c0e0284281c00c40000d03104a001c10040c02030b1203001c5020364646000100290a140c1d068010070b104a00380f80c039280040740c4e020f043c0d074030750079001c40300b89031680f0380c2000300b40100080d0590b42450701501281909281d001412503040340000d441d80103180d0b44190f102c03079819402d002c1464150304007845c002d6030404601c0c0e81a8100030b00900040314141640d42e503c0480313a40d90720465610030000418010f0000d80c0c418607005000c144 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 287425071 1250 287423821 287423861
    0x6120c0306061d130908090f12030d020705070b03040302031210050d110a031b140405070c02010f090b040e010806131205070f0804030309080d0e030703120c051e01 72
    0x54000c0c050701d110b50400540c5001c040d07020f03041d5030b0b00c185007860502d04224081022080c03030f0801c81e20740d80c0a28801d9010b52201600344809090a00a21205400c2240034605025120540130040c4d030286006071410703c505000032642c14002c04c0154001d80c400c3c3c000b1a541d40043e160107a0180c0014090b08000803200c0b820466034071400b888407112a4840c0312605034201c52400500c4054240d00301030205074004550903030168075146454140d41502520802e4410030908201c00c0c0c03641107480300002104180882c0c01940540b03504241010b490a2500e9030540f11140c074181074101d5403104403c800d0b03034401000aa20280200703500b00b1510300600c44000025199801401a00001c42003003040009404042c419264031400300e40d940724038032654982c3e4030706004090408a0140d90a1809443c08140019000780c1c2e40c0845018003070080c00c1400e20395110070803402a000b80c81420f01080d0f903200000944148080c001101c103032440b01036010001c90000e821a03108054610700e00703400c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 287426321 1250 287425071 287425079
    0x90f0b04030201141c0e010e0613060504020117070314152b020a0315050123090403110607030c090f030b0f060303090307060f120203070f0305100f06120c0306 70
    0x8800c84060700c2c1c081c2080b0088510710150303000d243c40355203402d0015002603166001c0d11381c131503001000050800300003070081203820b000c2d883d03c43d0022340e4042c4103010080050030004149400865106005043c004e1102807001460064003d048640305c001954401401c825808000e81c0c00390000b54219480e10300036852004200101e1081030b54030488004175040c07690700800009003500c171641c003a09054000d9960b181c050140c40113140000301e402e08080012480301050201c0f644a000b07500803204210b05003405015072940054010350030041454000ca241c0c050030420140510055900001c6031103c880707001700301112a8001c0303c06500200010004100304030380c4281c22052070616004551148000203103944a0a013115406001da50000207001e50442482035801c0400e1b100d10f50b40400449180f0200e100480300341011400303940344510403d109500090f44404a00c0504194a4942208114007503099100ca40007030480072280c00a83c51070b00800c5111641f50600384004e50130 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 287427571 1250 287426321 287426339
    0x10c1106062404180f050c0d02031b03150103060b0c15220308010603380a05030102040b0a0e040c0917120409050403030c080103050709150e0705030403090f 69
    0x1000d444944500e0000104805108a11070203148890290b9090359885a4889441e41c03084d1040f5249481c0c5490300462040010280c0121031260a00402603441e1600c900042c2000b904050981c0340840c20b007801d142c803024000702c01075019000c6201c1c5001c2d10301a0400050558149400c040320f030303180c01d02484c1d00c8690b00007621749440c1d0a160300c2d00080c0d80d41c2e030b03100344000b07800422003070342d10b029860310b034007416040425035050718126134050040550a550740114a140420682802003a2500c164560700d00e8003251090902c005110b000307050355900c00a826a0455003203001d0682c40012420560364020040c80004c3c01305840c00d02500b020041d01600b0142684640c801b9006000003201c0040410311442d4090b07049240c0c42501c941d02c504800004040c1118107c002c68542203440946902640c40c03541241c3c0d00c00c0c0100311050410b40c0c1c82020f4440ea107000310711900c403580042209429004254850381250341c810341c5078601810000c1920549a211200705c81d6900002e10503420 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 287428821 1250 287427571 287427583
    0x12c0703081b0a020d0803010e011e0b0a18060203041e030f080f07140a0312090b0c0d06030f061512031d0a050d05070e22020d030c08070311010c11 65
    0x11042c8900150364914040d09005549030021750005400b64804200f0410101440c185c4506d00c4401c10a40e0301c409080000c000e5986070040381c112120b9082208103010401407020300010314141f81c040e1103a540310400224503401c100050b170004034062204500c0130b0f20b0321858080c3c00c48034030700c142c1c03840e00c5031305100c904001c1c0641341510004110148844c040d089074140c50740041c00282d440c50301d4101c0c0380c0351401c034181140010800c01c40e054032043c9a0041c0100d4542000c03001c0da1607141d51032445619801180c0100100d42c40e1f0400102143d004142005402e0080e040400c82003005d01d02200c0c0d503c0315411040484031028045000300f03901c0103003081074203d0310101c1114003401c90002030340d1151a91140d644419660000005c0140219007841210018005500d640d194480d1400046090380c4954200220103264039005d460048921500540203041c100040c10458840303501c03541c00341c141075022070350310500000482d000348290b2508060702d04d05910007265506004d5200c407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 287430071 1250 287428821 287428837
    0xf021f05101208070203010f0515010f090512010f0506010f14030c0412110f03030313020d02060d060b03011e0302060904020705011103090c030601050a05090105010c03030b03012c070308 82
    0x2950345001030640c03038886614030094090359001c40c1404a0900d4003800a91190b10201e00075401c000d0203002c03217801d90188601800c5841421240449108011988e00e01099045001c009540ba00000c103038072001503040403040300c9000821808045d1390513405503a030191042c0e04000640004002d55030748030142010f060b400d0598669a6101d1b0101d403507030341c0101c0e0030451000c001155108104070080e0803c504154055480c1052180c0071410507841e4003044501c885280680f40c080b43c010300d0103000400b00107100418181c107140781c41549400301c4444c4c7c1c2041c1901540000140284100726a00c003546000070130301010582e045034085062401a403448500854001c220b1030200300080d0400c03250143c0c80c071070058681c60320b102503994507654004031500074056100040349606000da500010795002406680c1c1d075920340001156640301552081e420556160382030000380e80d0a001c0c006880c40340300352047c1300c40d902080d4102e08026025000403a13078402c58040002890001c1910252 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 287431321 1250 287430071 287430133
    0x40e1b090f07050313170408060703060e07051b030304030c15020c0312071209030503070e060910050c0f0d120e0d021011090d0c03060e0f03160201170907060f02 71
    0xb6210035044680115940030018603510710001b2221031040741001600c221400003040f9021611f80c00800d404441050040041b1580e901300000d03001c500030701c02800e0134205129054445a1079a50b514196042624214001030708903540c45d090010101b6022700385000c0740000c616150384041d240e03035030748942c0c5202c03200d44080b4000038207a980110f0151304010005081400030001074a002080c56004552510208003403031100080d5090640c244c4041c0e00c800b501c50120003441000641d00c90b040012038050b18031800c4440b00360003100380034030910401d440c0c40d1000030404013004031054032821000a083c1d507110502c2e11091550000b501d000764880203200060b074034451481ca00c85407250340d4143d6007001e00d00700e41c03004200090250108881c020740341045000145a1056183c070100803280800794414045411800a2014091038051050510b4100586081d10305200194100e0340c605058000343c1082006540140c600102001240301a0034201d002d1148030004410592107001c2c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 287432571 1250 287431321 287431327
    0x5030f040b0c0c100c1d0d0f020402090a06030c0305060405070206060904031e021b010903020312030907180b040e0d0c030537020c0901120803070c02040e1b090f0705 73
    0x480207110440705194800402d44061301040c41019016101c02e084113800120011682c00c520450740a00040c0048002c0c40011500e4003902e810b00300703c1d5000d0003a03a00a03403c0040e2203003507840101144c0240300c0c1c0c0e01c001c50301031400d50010b01240c0c80140080d026030305000c2002040e07503010408542c005000c961041913512642822241d04c204494078044113101221920344045e0001500c4405d9400804030a029428000045a00d90381510000f0f406a200e03a0380c0da00f4610040010f140d11101080440d0440344da500425506504407100c3c480f0282c2e41c0b100002d100c0e003041d0103414040b00d8510000c16041100035801004007022140c05410080041007281c514103041404100510310806a030340401c40c0c7c40846d00800465000800240c0b20b0101c03106280c0c20000101412a0803045403000c4007201512000745581c402000c0384100095000483e0043e0f82d0341c8102030004241700c00800d80c85080d4401c1c000c201310401c00d050300c00c0d4030110400228500213018264411110b2403c1c9032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 287433821 1250 287432571 287432581
    0x60a06030e0a1e05160605031602150c03150406030b070e0a030203070b0903061819320d0c02100c140d0c030e06070c03030305090309060403060b0a0605030f040b 71
    0x418001d081c4001040700400c414404400141003400d50103ca008800b40c50f400c018038601900708a40c42e02c1850045442400001c2c19040500c200c00e03140003090040d6100d80c0c26545901491183c100c85264000c2404002d010301440c000a480e0a2550255420400b990554403215143d0340001c04c01010044510341c018426203505500f100211ba014080310344075a1110440b902d41d030004001c00d80648100d00000310501c0041500d0100c07104100003400c1e0102c40407881d424001c9a02e84c040d05c08048203d10110102c1001c02c1c0480000705800200c02010100c0c3c84960501c0d00b4a0300d03080400a141d056840542d50f0f44105043c0c3d07412034103160582040d149040401008540d402c2070301401140c00c0004003603044014040164401d90f0b464100c00d0244003000494011281c0103405038400035030920001e4080e43c05107411090140440b800d05a075000010b00507485604115405920341c0301c41c1c005402d0082d81000035001c0ca040c01401e5203409410008121300080c00640b00e66210340c0456 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 287435071 1250 287433821 287433823
    0xc1903020f180c1215010c0821101d011208090109150206090106080a0c12050a0f120e010c031205100f060309020a0f0513110918040b07020d0c11040e1f0501060503060a06030e 77
    0x205d005041c1c002719441c5107401d54009250036020703c9903408a2074100301300c11f284142c81c80031505803640000301d05481407a54407000c0c056086100314034144a03010340302140754000c8045000b601e001c0c1c0d81c01001e244c90481d0780c2c1425034640d640600c090b035100714000400106d40410302c1c0b003624804400078040000030305095242580d00034010340041e07194180c801c03d0040f19080191030000c0c0351203025440c80356600440700f104c142e64010f00090768144c0c00d02c1001a42d074000e2600520408900c40049454440726501040c0a034410804250344142079021070424a44a100400b02621440025071616002c1242495080c1602c110346a0b10030203048214085020703101d42c640c019240c42440021507120f500200d200752425170b644610100010785d070302d100003200362a0320249d0b41c4501e11f080d05641c42c2004900e009980c0c50b2300540f142c07181d103021101000300500001a0309030741c2c09410709400450741103070f4041c0c111204001c5c0030010021140c0b0781c03203c2c2c08111511440e0020319440801016 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 287436321 1250 287435071 287435107
    0x1204060f020309031e1206010804030e0406060c0501050a020906040501050c030f0d050603010e0f030d0c09120f17040501020705010c02240405030c1903020f180c1215010c08 76
    0x8038640c0c601c00b00601808000c0000900480c018071980c025034010130100030746142c0290f004450803140d1a40028080d94421408203401611070b080c0300314036850300e100050a8a02c00d070400710005403030381c00709000e00c542401034542114500004501d0a0b00940101d000707071259001e802c0c1444000100d01c0c207184c4c1d00f001140c2c0c4c406c08c1c0c071207501e44950030680590003504041c0d461394425030811201c13440c6002c01180300310401640300b0041d4944401c0031000380c040d007405a400014840ca02900040e880180f80c84003403901d01c05c180c1e400d003100041c607007004040d202d0000d8002c3c4080c203000c203200c10390300050200c0235941c0034244070b00c210082c0e02c00502544030346040c048403003c0d01804415085401c00c0940280c1e04d00301c003914034080030355051202c2c0c0201030035440740011140f00d082001d030401031007120861401508841c0c544541c0c1c00441c1c690541a07840000180000440c0d48180c40c45010990300141031903401c600f03620a440000b480c00c01d0f4a140500004e8000905030810506404a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 287437571 1250 287436321 287436341
    0xf09060d0c080109031d010818070302090a1d0d0207030204091502070501060e0a09150e2a09060f210f0a050c0406060c2607080d0b2103120406 63
    0x507450706182c42d000603502a1030000b04c110045015095907011481c080142c0030100f00069648049594540d4040c001c8480000004115800381140100150f100c4a5609118140000700803480010402105544c804241d907146943d40100900302e840aa000c140c0008882c0c0480340490290000d040140a21098404040f500c600c005100010840c06401c900c048507140f0f9a9240c0c590759000c5450240d4a0040c001400011700f5003054200700e103554480301108044034201c4007600c6011005440c0410300e0404100043d8074084c484a040c80c0042c1030550000c4103843e80140c03007004cc008a0000c0040d246045071100c5503a16800b08180d0800101700015551401c654240c0018184140c464154010a41c051800d115011900d82e000b54020724015901c040d08507078160348000700054240d0410310071000280100003d802040d038000241c920161490000900001c0400800c0300c2c0e41592581103034195009201c46c1d80b6a84040155440b41d01c03403165071045540d07540b070b052005104e1007038 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 287438821 1250 287437571 287437583
    0x10506091f02010204120b062d060f040e1003060501051c0b0417041503061406044401050601020a032705030d110d03020403240f0e061906050f09060d 66
    0xc1b600780404001e055004503c240c4101c4222060300580301070705890a02c4120124641032840c40e06414104020251040c4644c0d90600b8075403038107003984203104103680b0f8076076102d182c2c4404e0050007128484d082c01480201d40c3c3c0a5a201594400c1001030b00111020300100d940c90005400d00c54599a00600011040020360750f541d01c5240590050304040108030010749003000100e280c50b4002401c800c0a90000c0400741428500744950b5030381c12600c0c0d02c0c00064807034441c0d0b003842c1d284d40c0c3c40028a09141d10b1120b0310a9442c003004142115401041181103502c010507400100350444103901001c401100c5018680303410f450180e03d00f0106a000d980c2502c60035041c0c20007603520041d850050f1001c041510007617140e1100c102d00707900a0b4000640b09074401c001012042030083c0000c80001d190a02c007089a14610000d0000c844006454141c3c40c3c11032020029006000e0341404009825004100031403414480454603220320f2110719030107610030102003606990341d681c000080d107501403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 287440071 1250 287438821 287438849
    0x1309020904151a030a06200304030c170717030603010212041406060603100603020a11010207150b0103060e040803072a1205040e0a0906061203050301030209010506091f02010204 78
    0x494001480c0c0b180e002a82030842c64540c6040c1c0b0b01d400040e0300c01040800034010901c51040d9220100100780f00c8444050105c036640d1402070030020440a14411400707034941c482e41e1422400e0001002d034025070850410042088070030000b1703549410b940743c06005000b480d91603550314400300b0300901c070301e00c00614001d40740c401700010030a0414001540810040030358045403110018011280015201516862200041484034030b00c07950140100212515100d03200a05042d58503003282e03c0100140c4d602d880d4505803e40100039805465032001080c601000070740d280080000ba01000a40014030044002010505803445980040b861000c15612110080b95031007102910082c07110301291341503080241030899900030402d0f5002c07180c00300c0c1c5880040c0c0e0384c032401c6001002e1800044403100c0c0d035020040384180d03c0c1d10841104600c240c42e041d03642d50560041000130141644624403c11041088907002d403110b03000c4060b150a2043c41ca1442241c1c91026806406150812001c0343c0d00c1c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 287441321 1250 287440071 287440073
    0x20f011103040510050f0f040c0b0f0a0305060306010b0901030b0d1a070f0212040e04240b0108090a0203030a18030b25031b0c1a010e010f0909050c1309020904 70
    0x31001140101e1054044850b28280c068104003941c1048030356029401154002813222050440c0c20b5500034411040400c0381a1110104901d40c4c00103550400803000c086546c0c1480303a01071040300d8110800324018000d640c54540450018855000840c0c10951240c0c40c540d110745aa800c00800541d201d02001c00e4808a41540a050030b0115070010020304080a601081030021030398841d0f00c40b596441e05e06d0141440c1e0003202c11840900b080310500d800350440c01001d1020040d0300c2c40303c120300c81c0200b0940c094030001005032602520301201ea07040001c0c018010313940001150340850007030403c00a02c62034000105440802640701030403141000003000080307040c6071071000340207005e400d4170260040c0d50720f811811505107805c030506000c220030851390b0f83c500400d0418031040c4200c45000940086002d5040342c0c00003070303004001920440300140906e1209000700300c09803048000400820319107807130785a60340c18690115030082941580002c1070006e190003000303400c1c0d0050300080d07042c01d02d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 287442571 1250 287441321 287441351
    0x703170a02120c30070e0906030715021009050309130227060d1410080a0c1211030604230309060d020901050c0601060e03010c030b1f020f01 62
    0x11081005082410100003504025480c0300751203498020742c941c01c039280c1d10056804160ba000002d21420305800103048004800221014140090b00a201e2562400e10000c050030380f042415445200b120124204020354030001449401c850510710407604a10b07652206074144940c1c160490000c0703051120740c0e414808004003d00b181302c010740c0c21035103d4280d09030402c12030045207003541070400c12101110942d41b01409050760032000a010529180c10354541c40200c806001a003411002c0d060200b010f111000c1e0300c02001000040054800d038004c030f076a50748038851a80030b0151740d41551081042071000c4030b0002006414003804071955030401d41020034510b0480d103103c040114010342034100c010070100a0700c0c0030410103000b040c20700803c240f202c000381d003000c11801c0c1000028440c070004000e04000040c024003041d107507421215038a00070305003507455207080c840074075040240082a1f07403980ca07140105d0b642d0460790361112030340f803600413403c100c1404908070083d07081002d61450500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 287443821 1250 287442571 287442587
    0x50706150b04270504150504240e15040302030706110405040c110c1e01050d0b04050c0a022b0804210f3207050a150b130b0f0d05070b0703 61
    0x520800c0f4941144840b10594090300c0e01250020048421403180226031081c0b600407a0f006403003503c60b40a102c00c07010399105840840145c2c501d1490300c48480094a080500480564544407400340d82c440ca01030700c01a50301d10810b04004c240560720311890015050b82000e507409850018410b100d82c101001009060388031070840742000740101c0d81001140c0c545508029003c042403c418941e10582a0055400c4d400141071264810744a115200071a0344038450340388508100501d5075151010318200a11300072000782e0300e40140309103100d2a00d90680d15508030305a4152840c003200703981e03114540400d46541441e500d101ca41c2021001c040d403c0d0b049a201c4800a41503952113001001911502d2a014294901905613a1142c0d03d000008012100100402030145046039007107101c1d82d48070324228880c091070884150362050130720301e28600200c2c0c2160304101c0c44814000c07580008001542c1e2842d83c034110b03200740c0d44c00185500304401403214500074560100f089445064504015144070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 287445071 1250 287443821 287443859
    0x21602030c0a0608070f030e0111120a020301240e030601081b03060c0405120a05031c06080c090a05060103090f080405032103061306030f0c03060f020a050706150b04 73
    0x70003100d031118070a0401000080468009a489074940d0315048001d40341c640b82c1d00002d0b410140c6400328000701c035509001d0080480b04a403d02c5543d0031205980458210028120822207070040004111901c00401801c01e190050030800b654842c0d80383d0b054804080103031416825014040000a611402040d482150001c2500840480341c10714200758a84908850303050a20314140310921090078800f04c0d01c000f10015104584030800180c40d000d1564000000036925906500c2405031b028840740a90002852580010710328807486034009101940000c0c0609401592400040c840380e11a030001512241c122510b00c0c0340c4c101d24101070203541e000b030065601078400d00e44a02d0002803051603d520390741030009898110b8403482c1c1000702c0031a5450340354200c640c560002002085004030b0031543d0314403e055017074106285107060401e8451080000650610610a050704960000300310b030300703090303201400080340b812468082c0082442504011007104c004a00031480d4a0850102c0040d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 287446321 1250 287445071 287445073
    0x60d0e0109031b02010801030f0821160507020907080606040b1612090f060c0204200310171203060a090507020f071208070201081b1809010902070b040f0804030602160203 75
    0x22440750311180f100c6501c0c10100a0000e080300c2c00400124a45e2101041024400c1c8586850a0806030380100d0840d41e020300145580c103007400348840078264075134050940149080c0f5a060071101c1c1c000a01548006120302d06015031403000400307560718007040b500502050b0701995211000d20380740000c140500c6004480340d925103a0382819540c00b0362040002c9600203804010341c80e0070301c21b080b0b030a140c0628040b41c00a80360840c5c0021400401d62009107000304114682d00e030700d0401210078000300d8a9200401c0c4808440c6069050f05000c2100f00402c07c4842d10745075641c42c0c0c0c030045559080742da8080d40080d40b6001c24400c1055000c036072629180109021108800d84070342c032048100d040c0003c01800306400b0484400194010015181c0c8603131421081d41450326545061129644a0198000c1071a2010214019850095a02400b50bc07520004508045542d41d80300681c1c0000f40002c0c0c4030203d0500d0798020807100d0403c8401955203c0410b54880001c99900301030440c000900b2486 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 287447571 1250 287446321 287446337
    0x318120d1104052101021207030921050405041a151c02040803040302040c0201150e07020f150109021b1b0a090203040b0a051503120307020c01111506060d0e010903 72
    0x70740d94050581c2e0a42c3d01c020003643c52a0358401c1326011400b1183c20000065409000305044607140c071a904d0320640031a02e001c00d10001d01c0c070f002110464966880741c01c000c21038020400d1694004240c8050f18002c0c0d40000e80041481d88a24965400203105541b00101c10000d640c400411006032540e034401112a90404c051482618140e0240703004404003640140010805450b00e50050041e80026000000e41480c40aa9200b070f000b049800c1602d420780010f0a1080081e81000415180200794028111610400142e07044005043c1700d00c4e00d4194000c62504000c400219020000d541c609049a2002000320300c040d00001c104202548141640c0d42c0000304241c0c1360007102d10032680641c0f203404980c0c3e4041c0003001000050043c150410440c20911050b440401042d40c140002546040d01e900d40744000a1402d1501d4110b20f0411400001c0c50030300c0000004d8010064031100b40d50b41c5c1030758074640440c8180c0145040b0120181c00c00b2071503140d10006502c900c1c4028040c1d070301e03102 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 287448821 1250 287447571 287447591
    0x150f0d021f200a020907110d2001061a0708040b03011710060b07140111040306050a1b0c150f020d021306020c061b07030204050f0a0c020a0206030a020318120d 70
    0xe5410b819007003400712504a429400014070b0083d40305640700d03000d400d28062000c0c1407800c1c80c0c80d100c0d01810000110341144800f00740b520310344036800c4418130341100a000060a19080c0c00780c003000c460f807507040c0b80d074040b40c0b002c2002400826140a002085d0210b6242d40e56940c102e1500c0b40b40401e4a42207000e800011003020707246004103000da40340b000d5194a00300c07040e0f85009103c002a0700c0440c0c10b56031444407010003503031080140300950013190701103074138109400841c3c11200d10318045014405c820340da80c1c113416004040e003400726801aa400621050b03c808080283c001008010800f81c03000902000010240c2e01801c44844005005c85d541a1100426aa61400000d01aa100d041440349a000c0e143c207140c0e0a20b4042400c05403981c19586c0d90206041e030b030041e2000d5502c1000f54082003a40c07984d40c41006442440c80c401809040b413241c0200d82c3c14440903042003c00f40e0000700041e240e45042c042100001038030b4048811b40750600700040900e030010041403c0f0a0f003031128000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 287450071 1250 287448821 287448857
    0xf020f030f15060118060f0c0b1e0a02040e041403090d0c0e0a060b030a020d1401030303090b070306030f0b13120305150f0307090b180c09010f0503150f0d021f 70
    0x40c0680c19400d17100c24050f040006c165658810000f0340801c111824403001c000845401c2e00500408802c0b141c2c409202040e03c1d0702d2400d0200401c0d82895500c14041000a80a2a40c00d035030842d0f00420710154018241122030b0941c0300300075005400214400009040000c044651400c45a041c41a1946521a5195242969954410b2010703041d028404224485025801010360642c1000c00050515006070080382d000b0f0264026004250b840066000b4810b2068a09038003681c2d92408000c858155555148081c4489402400c0004010001451500c0842c020058075401c542008604201c03284010090923088884000b201d0f00c6c1d41c007503034060810407040b9070b034540300030040c088032810416007900802840900c250302100d194012403c00042c041d40b140a0403010140c1c6039124108030001d040a140c40d465241000401c00802214050013217401191010803518005c8540705c40b40014400403640e88040d51084108074070340e2891140e114140217041c516200c90f040c51510312441c0e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 287451321 1250 287450071 287450087
    0xe0123090111190b1305060a1a0901120813030f120306060c08030c03090102041206200301050f0d030504230a0e0702060f0910020a03091a130f020f030f150601 70
    0x3d041499000000c100c0002c6845009550010002c0c607140e516054030f454a0385400030940c1d54000190b0348040900d0030790b0440c09050188441641c1c5007140b5490701c5150508402c0f0341c2c0010b000785030702055005209a850003140c00940e0021102462070b02103047c40c00709882d207021038001281c035240780015454000d180403c11540c20a1400c0e0441d564800c1ba540b40c1e44c03001305a101039542c204404030780c078082e45d200d0648490040c0300000790a990808501c0a0107500c04014100c02e40500c0104039603580c02f031000304035013001c3c2c40c0c20864000c03524080c0c455000f5900414890340d085524110300d0041d8507501d018248044230000f003465507441100c10703445e00030f541940c0140c008400141c1c15a080e9810544c00040d40350442e15003186907099041280c005800e01000030351215031180500a0410403600c1c0c00ca102c4030011403038200a01405040e082c6000028480b141c00c5a014041d5560450304042b00b030400340030b80301c1c0c801a6416281e12808404210b0603000d102d00c02280d104d52080c40c0d2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 287452571 1250 287451321 287451343
    0x50d080a060b12100305060108030d0609050c0304020402091f030b3d1e21050c0d0c02070308070609150504020d0201141b011505030c0d030e0123090111 67
    0x100b00d2920301d54641e85040c2e924000d010031000b16501000000144003000120700916030b110145898403a00e842201c01d07a00164041c281c03503800d00081c003054220303110460740c009a0484006a03514400c1002c1180e05008410400808a8000220f10b26541507001100980c60484a020141500c0c0d210817082042040c00003800f0414000d03107000803080b4100096014480d8204164500304200d24203054007406641c3c20001098070780b042d0120a11403080091140384003100307103e1450b080403610854007808100c002d406440724202c40b00c40303000b40901c4020f503400c0b41b00160784a0f0f0300d0409101820300c1c4102100c041602079842c8008040c0d920607240541c0c0e00608411040700c0907001169106070000c541600038500f04860f80310151501810031910001d0310000c20340100090310701c4150191640098000c0c1c110b080d140040399913107424400440e41c5030034604041d000910040fa240401480d00b03404461410344082184080a0007170704192000360b0312401c0c01440401421384039403070007503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 287453821 1250 287452571 287452589
    0xa1e0603080d0504080d020d140601170a1104091112060102030a0801030825050d1107030302071a070f0f020306060f10032703080411011106130519050d080a06 70
    0x22401c60b008190081500725009803010350031302c02c00300000b1b02242d00000e00035040c2035543c1c4480d00c00485c01c84520340e00c2070302420500d000307842c00c540060040600a04c903800c1c0503581c032410241101c0c0070b0300b03136409446000c81c200305204510120114503407251342d003040c0401c4a54000b40442d0301c00011101c5c450011b980300a6181d103155910911078129011400d05143c2d02401e1030640b0300000c1035040b00c00c1c0140c0c0240705403052000081d10740640c02000b0620307500300480620110381c0004545003111900b011010003030ba040660302d10300e40908400113040f0000403002401b40000c0c0001b4400c070381d008400351101c03601c9520030001c00d203084c006080e42104100300300d044034a01940c009103219001c4610b039010a85010031070b20251020400c21004600554184005c1c011403034160000d603502070070b0400b100061885402d80c1c40600410700a19103009003200d600b008420301c2502c203600b4030110309107a8802c1c2c2b40740c10b603198900c150703510300000e6015001610b48170083c0180d03400c84503141 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 287455071 1250 287453821 287453827
    0x1110a0f0e01050d11070210020f0a020906040b10020708070603150b0901030908030117010506030f060f22030822110d0c1706040b0c12010e0604090b0a1e060308 71
    0x50180c0c0c4550014540d14144441400a000044014003c04145c0d45c0362401c410703038601061041051900d0007000342001c540c01505003a6501500240e5240e055404560ba805180d49840c00200a0b10b0004c421030f4000d00840d494041d46a00090380070151140c100c01d40d1081c0c0d445500c11421203951501e807c080eaa1904801c101c80c04a00c2c5c000c2c48444d2040c50301140c406180d07265866a94400c0c1e205c01c2c20303001140c040d60342840d028815141c0000080b400f400d4580c85001490765680c20250500e080c2c1d18209002c0b0704548410b0103c55002d281d8000130050b40700443c200500032020489240c01a02c8510800d548280b140f011540e070303c035501200c5181c8003a8a203080c4036011000d00e1040784c4014640c1d5021413030340c01a65031503208a582c030b0010009450700d031400c208041c401400d111545e10f02440b1040d00d0b1241c00d0440d60644a15001e03050300c0790f4883c40000c01401180802404500d0003a0910400c0300390368008804281e00c0c940044500c5d03065081c40e100f203c0140c407014103083c0080c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 287456321 1250 287455071 287455097
    0x10302030406020928060212030402190e0a151202150307050c19030e120712150504051b0102030c0309090705040803040e0403091d131401110c01110a 66
    0x2a806150007901a03803005040c002001c01059880126030724803c6155406489503481c0c14081035042c003e401d540c40603080800c400c46088201d4003018000a12500e1110481d044903201c6c0d2043c50010700802e1425803a41c28000d05410061211562400e050030800c0e40200b40c01c0640403490350100e0303000d40303100d00f0b20750340084d103003100d400182c400c00800c14100460200300000b08002c00700c001041842021051080c034018000000d883d107c640a000c0c01c07071360349100d40b9002c40e00c0c504482c0351807106903035040c0c503241403d41003640d4680002036a24100c284010b1120000d1030082015481030b0410764a0340745401640d40c0e00550301d42002c41e0f4001c100e41995828080c1c001c1b40c2001d441e00780b036418140c982c5145030841e04a900500005c4003400100000d01d48c0c8400e6400c014005c20030b9035078024000701507802d450b050081154241c404501e00321010001c201d600720503480300202c020444a00303101c00302d902c02d601100301d001103982040400000d2003030320740450700350544c7e68540301c0d0844c0079 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 287457571 1250 287456321 287456327
    0x3060524100f021e0129010507030e010507170a020706021209010e031e030a0810060f0320180f03030c070509070c0c060302030610020a020a14030705120a0507060c1101 74
    0x81144000c08600034110b1125480411084124102130031a0003c55251090400300900341025010140c0d0201d00462041203641c105c4104e0300038030342615041c50b1034000d820051752240b042690040400760100544d503902d180040191203185003690075125856a00c1d0302c1240e03142950903081c81010710401640c4070070342c09801d02900300103015050f2408422225212144140b0000701b4140765040081c000c0d59a9278400007895000d2000300c11440040c0c10000b00400c07070304218004409241c2e440d944100c05000410081d40010300c1152210360f21000c09a40c0b20824800324401ca020b8031410403c0400c61602009a403200a0000c000702901441d2100700701e0003250241146050002d070702e903054040380e00030b075200340a0045510003507a82c3c01e100003800b110602d92020a02150401c070ba02e440140d4442c0003100484a280310016415019980083d007080c1d1143d110a0b40800d00b401d5003001c03440007180d0a44c08500070410303511015565802a58424054900203160b1031308150704e5503117580 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 287458821 1250 287457571 287457587
    0x150603060d0c0503010c11070e040b01061d040f02180f06300103050a0c05060c1b03010e06090607090b070302060708190c0801030b1f0b0a020c0303040306052410 71
    0x10041a0640c4100c0d83c2e90080381c21180c003214800002030702510803200c2144100305e41030040418404079400c03454141c0341c00200e10018010f020401071324511110341a5823040607461081e81c000c004010100c0565a080300035400b4a0602c580c0f0310f07038180080818500180c1301c0308010b80181c00c0d28680307010b903a0120300070548040c04190100f600d40030300036282da00308065400785104000501040758a41080d089481a9a21092141d4420008034000c80c101280f0b40100100e0a2400b9400c4a40ca40001f0301618200520900510865080008204c0001201801003503217490b401030043e11403107860100e203c5c0c0b40025003d81d12040204001a1007200300b00e91043d000780b00310385900c02216164040d1004200c0c000c1c0002c0219006000f03200e0b1405075076801c001d41e948103007401c03001d4504c000291703506071040d052842d00100d500c2d54094003d2124801c00f11000741603954407030f12440c01f0303c02031600340d42ca07100040040040c0d540301908808402c41100000301420b951b80500341040380c441c9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 287460071 1250 287458821 287458823
    0x9050609030109170c12030403050910120228020304060504030803060a0e0108060a0b030313210c171002040501050d0e070306020a020c040b04060311090703110301030c0905150603060d 81
    0x99a0f442c0003c003c0360f80f8406240c03406207519240c0c0e6807080c0003a4400d01e0801102c0c000d81840d48100280070000c0e4000c0200c03003242006464005109000c000260355000b00a103986012500004e060203080181d0f0040100580c2e650952460300b02080100b00d0f07483c00f0301e002c3c1c1e0011400406c01440801e0040015503440840100001d02c250780390b409000700807000707900450485e4010020f0141d0403409005140d50820706900441c10702d03030440e5588800384030521400c0010380c2200c140c000c0f1007a032080e81c04601780c1c0000340c4900d100e540b001c202e80450400081c91003035000750034210750a0110b6008460440300e0507940d807800e005c442d040d00e10081c02c04a000548612440c500040000e460380050400c801c9142c025111180c3d17644180029983c294621521862070204244000307441d21650070035948081d10003d0055032691b070103800905048100000046000c8000020800001190300540d16408400c0c442900c450601100342c0c900c00c510541c0c01001030001039a01c0c1010382c0c00200c02 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 287461321 1250 287460071 287460073
    0x309040219020d0c05120702060c032209020316080a02130603060501030e0109050601120c03140717060f0406020c011e05010503010c0c0302030703030513120f020c03010c0905060903 80
    0x5101500010101d90006212042000595610105080d014440c1010a034040e0504010ba105140c1e82c403500c0305c51103c3e044a4a01c4041741d25002e41d11840d060380d00100003c412a596842c0704040103c5c084800c41030744190b65880c10f80855080d11500a03a80030b000d0b00d203c1002080c8182105507151b00c8018001c00388290b0038080062900ca00c0035003070000b001c940e100058034504000004082d140241007080040e0b04150240c8002070300080e000b0704440d000002c0814480c0c65280c044610b0040341d10280c4800b214403c8000c0002c8003081e0b250403250031481490f400d4540495280d1241c0c000c80d0141050061900080d02140550700108942c1e031020000003441c1844480c0414012102d0350100d1060f96500b005006508091007505480c0002e410310140c0b01d00669002596440391070750040406881d5800f28414503060504079034515031000d00d403100c100c0c9583e4002d11031808810148010b00c50034061520a0a040c49640b2507000e00d07603038560f0900d0414041c09007586c0400358250305 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 287462571 1250 287461321 287461327
    0x90421031d030408070b122703030a14010f0e1f030210091d0906151201020f04090c030207050d050f130305151b07030302071b030c030b0a022115031c0311030103032003 74
    0x234000a000071840340b64103c50000c0c46012041102e0001c4205030040c95002058074001c4c0002c6008180c660340c0300d06906e001c44201d0840c5000e80340c40d00050340c00207400c8a401c1c0d101980e90b9411020403403e49200d849030481203415076a110748110b0381560380d681d0a401042c00b007414440345e481d03040320301c41000c0c020a1141080b03510060032a0702940144c0c400410101d030034000000c1b50f004900d059122840c041d8100a81c0c1c0d12480e4440c081c1d00a0001404000036290043c1c86a06080e00d0040341001070307400395036a40f810300c2c0f502c8080141c5c0304131400c900c0000003000001b000214620042058206508000d882e6405070b00a510040c03064501c41201030130b402c0a000176060b580b0145100b2500c004496142d4a80020034240c0500790726030880c0180200750090a5a0841801ca2114204150346648400300250703003114452200642600030380c503400c501c5108001c0e0700e2496007448c1d50100f1821646814404090200303000003000070703002c06004a910a403580030200146540c03001d80745 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 287463821 1250 287462571 287462641
    0x901030f140109091412030f040303090c0b0403060b0a060e0409030504170d090b0a210902130e0d1704080a110a0c090b090421031d030408070b12 64
    0x3a01e000b680004081c5448064000401c00c003c601040b0210802e402081041508590354149001c01810183c1002000700001d007030600c40d401480e0700729000200d04c9443c540304d2020380301c41d82c054002a101181462040d40f5a030070401d4000d811140c40b56182e000e03070340d43c1108010281058440c2a0100700d02840081000182c0d1080314010508040c02052840028030340a45540c0f055400b20200343c01c02d000c05c24035950003408031850502c1c1c14000c0707049281c0c0700e064800200700020f400394121214070a01e81024106c0d922140e9809010001c9400090551004452b580c40300d42804000150319804a1300080240014200300241030510700020f240044255140c4244018162915405402f0030807030184031f0312403203040e080165072040351840d00e91034200b003e41ca625140201401d0300b40c82401c00520a5115201050b60400d0b6601050041c03407807240e694106000d280000d00030a200010700c40300000440301c0301004150000c41c5941c80109480c85060125070450b0095221003044c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 287465071 1250 287463821 287463851
    0x180506100303110304121104020c03160c0506040305100203041a070305040605130b130303150f030c0518150f0907050a17010803180a09020a08091009080901030f 71
    0x144200030006019600300d2442c18001c05101091081c080103030810001802110a003c550030765035034000000c500e007030b03070103030007140c0240b15034490070101c0e000129075003841104070b0340c110303017054000c81c003051805417982c0c100103682c801c1d4400100150311001e60303040404c503d90055944140180ea04800d1180c2c152040201540d0403501040041d0340c5a0400c010001d6034070900c0d070010700041d0040001c606d82c1c0e0320500302d20340c0078142095100c5907002120805220750803c2521154038a0112100b55030380e04044550103050100319040b0040c00e0000c1002c1c2404e0304106860140030240030351948032403107107500300a031800c029500b0a407000c8650390039464100d4070314011459517842e20341d903510505005044460a01d04124040721b200c0040205001c0003040d2000c1001c81001e40208041e032034001075001e0400d0f070000e250389001180340f9081a03040010a40f1904841041d03c00c0329880d41e03020f1303040314203082000704848402e04c1040b585503c00e0380b2203810303590000c8000440ca51070480304 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 287466321 1250 287465071 287465083
    0x71b0905010617191b03051302300708030405130507020604021c0503040e0a050702010603030206160207080f010903020d1806030b031f0c0311030c04060e0102151005120a02010801091805 82
    0x180e1034600f170b90709100300d66458031072aa0700040040840b914454264002840f4038214910110100d50010100040e14500e03d40540768401c0c410848201c25650249a84c4a41240c805c00d03100e0408100000303d25181401010306c21346059000d44602d40d9164200480311038104800c00c6c0a070002d11640d00040d900300000c101038030170700b2100001e9103070841002e000e461006041c5811641801800c01c0040c2d000548903801150030401c00b2424000d14208078980b04050b031200c031003072060185000d1848c17019400f503c4a14044c0d0309607000301c1001da0090b500344100d01000115001d82c02020000c8c4d51195100d0640c450009007550686962038480f0320858104110804510355100714458010382c051207118910400c140b039844c21441d0405503c403290040b4442e44007070121342560460142c0c0709010043d8240c1088422680300c1c14030004c0d0000390241130080d40c2c020041c040c103d4100c00070014190003001d5050b5030300300c42a803c1424203009044594044c8500c6c0c40e034000c80c03d002039030038015 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 287467571 1250 287466321 287466341
    0x3307150204140f030706111002030109050717091504110316090b040b0f0603060d080a0915080103210e12011a060c0604080f0906071b090501061719 65
    0x8056100d40c00e1078002c0c49040114018248a100b251001c081d298034085110400c5074a9030401840e9458100c003041e08014611070204401c0303100000110b251549680003900501d442d61b9008842105001405140401980d60070310950043d0003c1c01020340461440f50310510030414a12070400200c08246064403a480c040e4800d10300700c2e000e10a00c025881401100b0b20115828803101c01c040e408174030015400f041d031030b00410b800070003d5400e481e400f980354041e40d8000d049903500c03008104018045402402072884c3ca88105101e5458248110b81050580380c0205800307600440019401613034a12000806090105802284010b80d0700c586e540a1104c112000200f40042c203000001c8001207810700c8148210010b1182c41000750b00007540d0307540302c0d50080100e07030b0311108c1100109180c0111000143c2c00000080c00302d08110345e41100303000d450303181d081303c21406440d4000d0b80240e81c4240038800c0080c1c00c480c0140d014001000314240c005c2550000080c003054422200303010341e000000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 287468821 1250 287467571 287467613
    0x1b0303090a0e041406070e040e0703050303010308040f05090c0d1d0618070509090a030c0f081c0506030d081303110f0304050907030c05120712050702100b3307 70
    0x20003003404501c0400b01c0c03613080040d0140103507190a507009400716040c020b4050003503607110030350740014038108211006140c201c1c08583c1ca13981d4074500b440542e8030a0140c103c014882000000740303030415200090007280b460310b440341404040f5549100512541420b0142142d400c414a00c10f5002031100d1401501c0024040040d040303134091480c502001d0741e00090240c281d040070400503613400700b07071080026810b280c648180812814089201c4010703580c007800014000074100703a14204e4600c422803111825070281709642c0d841e801c0544441601c41310702c010aa148001805243d042c40080e0300c05c0d4402d050000130b21441e030700a245003120911a000080d4000a03041c49a45040c592155102e916132a0601130301d400700c24020f0107070145501c02d204420564020548180c000e520011003c00803000800042c40c10044c0296141c1c8170143c1403802c01d240c03051400460034162284058210f4810b075041c075202c05000c2d440c0400c0514070702185c807078030103200c0f1100299603000c811010b611141c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 287470071 1250 287468821 287468849
    0x106030203070201200301050402220b040303110307020108040b061309080301050906060c0715030b1309170403110d060b03030705060106090b07110d14030a050706050c030105031b0303090a 83
    0x540041c2c00c607070a4400701541d8611075171003006201c0c9107208507815a6020380b00981c4440c10119840c9900c090fa413440001605004c0002c03400c0540c80c4050030031030340a03a80d00ba071411040022140c81e84282c0c20b01900144001d4001408107016150701d50b0007400240c0741061400010b0604812211070f91401c50341c06400200400040c40c0c20702c82e03550010385c2154910701c2d00c1400702286e6985d01d464850200008034000340039440030f000f83c0c0300e403110401c007500e40f4030300180b441c2068000305465a01201c141012941745a040300300003065030183c039445100361401c0c545400400004c01110402250b00d2030b1101c0c2220900d45060014000c0944500c004001d0b55050090103022040300390020ba405401c01d11044000c02c2000d550381c80b2552007540c00f01001261418083e200804c20410401d02d44000241d10712255072000061060703502410040185440c0c000007502c0031300c000c1c403409615a210303401030700c0081828030100c8410701009046925283c2038001003038006003144d000440c0c8551031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 287471321 1250 287470071 287470081
    0x3030c02030f0c010206041407180207120509010507030302030621070e01051909090302070b13050a090905071e030606061e03050402100f1101050f09070b0c060a0911090106030203 79
    0x800c01c5400203201c440c064402c3c0380c00b070750000b5a20080144007800d00030289150542e04001800704401a1680d200c40d82000c090702085070010394801ca4040360201041010100001d2140c0140d80648a0581d0740c2031070076203192012800f030f40000d840181d110101c40100100e81c8500583d1401040c02030001d441c1080c90504214038004050744905c1c041c04d49046200c0506921172502d00c103079032072604000341340314080c00d08900e0300300c0c542c00c142002c240020348040c80b100d40c02407000480300110303000c003000f54a41d2000030aa410721031006149070b08c412801c0c002d1420103c90200a9020558440351041d9a520b64105482259101901141100c0c84101b2940b8558906590340c420f141020300203400c3c02d502081328480c2d042c10006c10480d0080301d6000b150321603207c144500502000074401400c103548441c01d94242070b64403c48900c10020000303601701c880707000e59001c8840070700075142ca9510142004040d18103840f00b2076800070050030041c2c00c0d60b14810503601a0109540040e282e1030a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 287472571 1250 287471321 287471323
    0x240603090b01080105130609050102120f060a080c0d03031e020409020d0c050c0c09061302031e0105030703150209040212040b0601140405060301120309080a03020f06102d0f03030c0203 81
    0x81a00032041a174188030802400d20000d03408501550b600050000740c0303c4e12400c0050084c0505000e8071104400001844000c511483c1114000c440407140c0c2c0008603a58504a6651500141b20031b810042c421492408230740240e21400380300c103031a4440000c00f41811542000c0ba449034110140700ca50110390207400600d6442509144012400d2140c60840707862a665616000844954420448400020051340340d4441004140140d4102507460f400d1a107041d128a0060042c1408000c10010000600b03203800910b1008071380d041038003500c00c0d8111002d80c502a40c0103001c0b440e0019000c000178560241002d0b001840346028104850807410484001031005061180c0c060900b80b0900050188bd5588021241192001034050588008070b10302502c001e0350b01d611210341401070701c3e030000505801040350b070303071100d80303001511407a643c0d8201002050442e40102e200c101030400d082d034003000c0340340c01000b81840315503005003c03d5030312440103540b120241c1040703000172500c050290844c28 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 287473821 1250 287472571 287472593
    0x90103090b0108060406140606181909050612010b09010e040804031406090606150f030a0b0312190810061808030408011a03011a01120b0402070803040201080601080108070924060309 80
    0x301c0747c190300000c0c10100d00180c0d4034015001c82402140e500607600f01a80d43e1039800d020454049008481600d80c0c0e036502c80000c00d021103a0074019240c2c804443d031401010701c64110603810050042e44140d00b014046035110000400c121028401000003201003403080c00510301c40c43d0614000d0003540b802c40e5141d810701c0e0340903002900031000324030b082980c64406005c0e02c03503001300e058840e41c03039944400000024140102c0c0c1250980039120030180b000294200400d00c20440c0d142c90010b41d41c40c80d900b00d82d41a000c07111b0311080d4a035020b0510055101d044545242205411100001ca80b0b40c0061030659001c1d5220000581d511843e801040d86100f580081400040300200260204e5280c0400c09050300f0407400c4c100203040300f050813450200e07848400079101c040c1003103403159154a060700603580242c8059010a5924000401c103600c07501c1818140d480003009411000d1030308000e41c014101d07030500644130f50f04841020045040d1021402c0040003079681c0441d02c01124245079030085 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 287475071 1250 287473821 287473841
    0x4020d0e150705030106030b0616030f02061b04090513140f240f1003120903230d0f02030705150604050c1306230d0b040c03090b0408090103090b0108060406 69
    0x41d03011000c202000c0d801100f60390469015041c0030502c4089400000c42c1c0b071041c201c0b0210348218640c3c6c00c1060690080147d959440581c085840e80d44480e0711035040b95042d0b062884107400104428450584907070003094200300802310500303002150340d803440008909000201d00551040003482098682001801d03044403544040d2264054503100c4000d40c01c030001e0003a10080402401700c1c0700d0700c1c41c507104c0f04010342d004505488e070500d00c030f00000d0001d0001d100940b00000fa00f11440c0c96401c044119011360f00c0c400c00145030b894130104040c0c81c812450825081940810302000000c82c1080c4a510002d0482010542c01d45c9054800c00084500140c45503200c1c01003885200b03002044601048140c0c0d181d0b0810240204066101e4445905850722003000611f0201c0c52080c410441e41252800d1881280d0521066019140071021600062005030100b1000b00100e00801d4452000b041e0105043c9004036260010744c4a59000503020f910899141e0b10001c00c1000b404018403e07100c030301c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 287476321 1250 287475071 287475103
    0xb0918060a0b031e25060207050a062106120506010305060703050610050d060f1202030c090c04291207020c0a05010c080307020f0f01020403020a08060601050f030703060504020d0e 79
    0x100b0782c1040403990314880d04950300c2090810815001d80910108450050002e030700c00461107825010080c02602042841040d0140c42840360204a900e0085081000d48c0c100717a4615003102c040e03c2005000d140d41c08085911943d4038003001c241d0309400483c45c1c0240b8055002005075500d54580245040402411142003510300317802c1c8006680c81080b04041784104d80703041900e95540c03030740c1e10009101540c40400400c10071030000540c292858034480101e40202c09807042d201401052041d044811202030300301501c20841031040840303030784000e06480000c1c40c0050000d21405400034190344007051541740280c9440400421607410086103401c070f51b050f01d5010100c0d103040006407644075180001480003201000046103c1d10801030342400f00000303c12900c4602c000c2040368002e50050200f030740500540d01010810400014141c0d004040603901c451800d9151003072000941c001401600030035440c1c0c0300014160b9205d0014105020100400141106031003010500d4507007000481184 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 287477571 1250 287476321 287476331
    0xf0309010210111c0b0d030e2d0409030e03030f0418090203030d09061506090603140f0601030b031002040b2701020a0303020a02070b0d02120c0304110d060b0918060a 73
    0xc2d0304105402d403208130001e0b140c1400703482261301c4202c0140c410450240d80100c140c1e21440145580007601c0c0400480607500c90540b6420055600420815290b03449800c05030380001012604196101c204154042e1621030404050000000e04543c024000c1400004010906001501002c801c00e10b0700411044200282081540469201c1c0505500082d00315a22000301c0c0c10b00409811004014800c4500c080d50300b900d400d00505001c2c0c00340101c00000e4581034159120799205200c4038080e6421101841c00ca5440100440180031040f035896014001d1006811a508450003d480505598911162107400c1039803c51185554030350f0001c10382040d29102501d0f030741c01160729040107030149400341e41c841001c00241d16021141d484103416880025102e800410150b019090701c0c0103c80c0f01c01c03000d40703c0b00800c01490101781e60213800c02903c082014003610b05000c90216051045501240d0311003060001100701c40c04561119102070107031241411900700340310782e5512481040302049 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 287478821 1250 287477571 287477591
    0xd0908040f0b210403090b0a0f02120a080c0702010504030c0909030f1407060911130f06080715052b15080111090402030c0d050705070c0608010b0d05060406080f0309010210 76
    0xc0c118000803da010b002621070041000c1c0340c410380340c480c05400d080f03c00c90341d14a51110010007410314084d400c001802f0304060000c1c111800011104c1c001d000f40e4035241107883d200896800c039440030408a0500c0810480000040e0850500d00c00915400c08001405403242c14060b0207a094050300b4020802c0046000040000982c00e072184150824000901c017409460088aa20010f0720040d600840746620b1a510300c406070080c2d03104203441c01c0c060041c90755450030950399942c18000c0020202c0444142034081748541301034503ca02e1034103035140300244426904070341c83e60300700800783c003180d15441502e000d111040700c040020700480008015a918070b050341842409200510341c800c03074001000c10703240d58201060b2020b100210500f000142400d80c0e000e0044d501220003200d03070540082c00020b92038007885945048964040055207042502e0601000401c4020300da19070240d03a41402040c5160200500c5089461401c000e6507135081d50790000e8900401d00515060a03420034034140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 287480071 1250 287478821 287478847
    0xe0103060605032d0a06091401080705012d090303031a01020615060705060f1e07020a0b090a2a05031209060306281a030603060402010809030d0908040f0b 68
    0xd90194041e403828500c2944e40940ca0010756007081d0200380c15001c030091100300202503000c2402c44940c0041004030101c040c80751310300c03035109200d54611908500702c2004954000e410640788099005601080001c05101c1100b10b5007081820318001040c001c014000c05070103204a4110000320443e101d05040c0b481d000035540ca070010500350040c503400c48107030403686502054510442d4400d082d600946003889400447d110b048078100e12113255096854407017401b4504850080555a0103042c260483d0f444072811200c02402d25041841244a00c070301291800d00000d07651028000b1902040d10308248a190302040ca4100c6031207500070040040030140d604c4206c03220003800b0380c1d0603500c81ea2860000358135443e982251804000840c21100765604443c0c49030300542d03e10b0805000040303204000c2c00580c2c082122038541562016000c100503602030211540c1c4603044604407840c002c01100f0410640d88207d00886c0c90300000b01d001c0c88041203402507007004c0c110300c0005a0070044004503c1d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 287481321 1250 287480071 287480077
    0x1005030f04110a09050108160f0308091e060a0e0a0f1202040911090114010f080c09040f1d03030405060f04050d03050c04030204060e100e06060d0f14010609060e0103060605 76
    0x300b500300c2030741241042e40c54400034000200000e013030800007582d65524060b00e50244071078100c01041c420601207510b0307400200300400e032900207401c1810b03c000b0105000f4415072601c0c808000a4a045031540e56a030b88000824032141c40350740d00462414114140305200c10340d81c20400c02c40f001d503142030101e074079081c0c2041c150310340446002c10010341d01d0410705003123103140341c14a41001035840080749504204990080c03800080c2c0c3e0343d0003500c0000d44212851a0150752003506208108404a501e241a400c4034003400300d00480001c030743e20b4030b80e44507070b550034000401c07080c1da000802000f040c0881030001c0c640c0541c008015448070701e01a92010b4a4209102602040c076594001052a581d200400d54020b1503004c0d01c100007113611160001e2110134101c41c2002c00c4105e122020449588000c0c4060040b1005000182440e6203083c0d0607015010022020704d43d40c0c2da8181021040910071011402011a40c1710a040d00f41040c0008241001d070581c1d031414035080c804100b100325031041c11 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 287482571 1250 287481321 287481323
    0xf0e0604120f1e03081e0c0406030e1006090f0f02041a1b07030303050a0506040b1c020d1502030103020a1502330a02090a0501020114060609010c060e010b1005030f04 73
    0x2142001881c0303280c0030001c0c0c044003103001d00343e01600300290100f6800c43d007214040e0b07441d0b0207941c001c4199014014041c130402c81e804150b0100a020070003686000e500700e0036031078950806460003265107001440499026038010310034940c0700e12505c506c031006441402001c80d800b540a40c41c00d0f05200e01079150400c401c0d40352039419000a5840308040f181a550312580c800c1070180c44580355a820004d01520302914154603461030000800d5052410b03204150b81c100c0040d0102c4001801180039090390710b0101010b0382c001c4502900708002a0403214940c0ca000018080140ca95040d40107221102416810807c51518008000c03482c171900006c10050700a440060381d1000c0703407985141060f00c40301c894001c0e00da604041c240304030054a82c015001001c01991034903c900d80d00c100480c01d9491801d1401d0028142d4008210035041030710051804103410306150f111089160344207400c9801600007181265983e40e500e01d102d01c0c000c0c0741c01c0204011803403c28154100f0021a01d40301d800500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 287483821 1250 287482571 287482583
    0x30809030a05010f090605090c010c0b071b080a09060c080909060d15060614090a091505030319170606121f030c030b0a020f04151b030f0e060412 64
    0x54104550340e0104000d40d01c40780d20000a002c00513858100401402110324100c48003070800000640902c00000c4840d04c6a038142d4404420a0072a21803d41d03404026150f50304010007446400328041141c4480d4030024460080316541d00741e441d5004124138984d8200c40208114582100c01082444058501400c411a040704c90f075110000040c2ca80062100014448105c104099180d030b007090744050300700c0c2c81d2601d0f01c4002d402e42000010701441440c1b0b0003940720358108414001c20050f540501200d0100f004a01d85007925007000a02d1500030840c41005101180400d40d2015400f030600b090301041842030f0000b9080410003d241c4d0300130401c0d504148400580007e2a00300a01c000c94860103060142440c190703220705001c0101c0204c3d000960b910400c6202141d98202184216003a48080c004294141401d20b041180440745600c800b0713040055081d05c1c070310102c042c482400480d42c0b09031228500f00032203200c050b08041101161a20410040c4170070005502111040306402c0d40c8a9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 287485071 1250 287483821 287483827
    0x506071e0e0307030c0314070b0408100f0902090f07090f0b0406120605120307061107050705090403090521102007080f0301171207050a080714120d0c030204050a0308 73
    0x20780400c0c50b10040d1360001e842000c0e400400010f11820210100481000c50103440040e915200c0e0280030784203038400c0c000c3c0c59004011041c584a19a848640207280494000c24a00b0843e00080c84103681996004e4810040e0300901c030156810a07a16001000d500788200c02042c03034070000003506c2c0075901c5200300788000900b0720860001e5961001c0040c12004068180d400003407501140c0c0c030340100f101210990300d0500e05180e50000c0c1c409940000354010010001c0d0b6050000f402840380c00500700300c0038040c41890120300c0b82c0c0e681040940380c20b80720b1440080300fa510070402d072400c0c04800260b00210714204010204c00d00031003040343e1980000303011560380e043c1460311030014458000d084081400c04000407401d66003500c6000c005050b498210ba841c4044103012030b84074840e0400052959101c005034030002240744000d00401405440045400303082404540e081c01c0c40142c01e00c0784450002001d05d0301c0c181520034019060b01c0c0e0701d01181090b05110105031007450500000c2c2c0034032004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 287486321 1250 287485071 287485097
    0xd0803010608060a0e0736140301180b04020f180702031201050609090c0a050403020a09020a02070e1306050c0c060405011b0906090b03060303041206090c140607020108060a08010c0c0506071e 84
    0x1941c108020700054480c5207e210795204081b48021240c0c060080c4203500b0700480940b048100c0e2488241d084d00f001c1c2400300c82d2030350780c20000c0c1c8000108074690407041c060399030048511608042c0d44116841c0c0c003d107646201c10500c1c900c040e08160000742c803d810600000c1d1468035000d480c20b5201ca150003505640c0c1c2500c8500351158051984000d501040c40240402d0480d0075801505c0340a000b502140c403405d84074081ca0a100d081150300b508644018401d110106078150807258001d081c0c0c1c5c07006894200b01c4e4203000d080a40485d01524169140c400210419018048205040041d481c0242c0d029040c044000c0c502d03030041c802c081c03400ca008030116800756418022140100400070040f01454101d1810b440076001010042d600d800c080000040d041785046c0401d00b504030010030051500700203500545a4603c0904a035422840c56400407400c40000d00ca4a8a00c4010703844001c07c040a030729042d031820b140201030a042000303c82060668482d444e00800d410b20890406010b15500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 287487571 1250 287486321 287486387
    0x80a0906061e1703030610030c031d011b030c02030d050615070506010f090b090601050318070b0714070e01030f0f1209090c02010e0c040207020d0803010608060a0e07 73
    0x641144480107a4032607140202044030659000f20740d5604583c101194042d500b003034403804211149904406003081d002c190600c030b40d000410802007410005101c40460081150340b14541201e05c0d1142e540c1c03036000383c00f640c1c001d101074000c0100d17280a00c8445a1504025202d006001481b0101900c880100d2001e940e481e042c0414100003070f040300d40794040d50920540c3c0345420702c12210591840100071038940300c5c034040d5000051025080750700079110180111102d9100405061480c000108100b0030600103201c207000030030100407116180e00740d506042c022842c100f41d0001455000c0e000400c06060705007000c0d81181c0d00041210320811541c182007807003454082c00184209400405051410b81145881d0261021003504008031410003e0690884255000a141d564081010b0360001d00d040c0c7c00900b056403000c1e100c100582515070340c40707545800c20b070031107000300d000c5500b084881d04210b94100d0040c40209000281d50038060382c0035140c1040790b81903101e00d00c100c010319801410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 287488821 1250 287487571 287487581
    0x30b041e0b1f020604350c0f0d020606030d08160e0105070c2408042301140103060209090603240709030b1003020a08030406020c1c0503030f0f0610080a0906 69
    0x9007200e090000ba00b035101c003c0d1146800c0b02d080b6840e03291742090580182c0700010140c04140b07240524400740c0d004000d5070440703410080c02e01c2181d10400c0308503024000c0c184030040c81203180340c001b001c06090801c201420103125401e10803c021846003000100361001414044200c42400e10802c1903e158004842d10300c00c50340e0190030b071100040b0004452468280c1300f0401001c40c540742c1c404c0a07900d107084400703c0301070724080c0c0100741783d511485c0441e810918010302d01180c0f000009001d6203c524921035214240e05c281c8400354040f5a0860600b8203030880c982c13000c42200078016508164605108400140c8200200300c9150300010b84054010219000516040080c802881c50b154400034030f0108103000c100e008419449000809520000503941503c43c9500548506008101400009120442d070b13100c41c501c1040d20703900898424801140210b05400030009140340c903850042c1c02d080702a20b1a4001e80c409800c00c280c0035808040d00e900040045004502c02c2c115040c1803001e49 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 287490071 1250 287488821 287488849
    0x70314070f0e01081002210601050910020f0d09050307090f020904050c0a030b0f0f0f04021e071704060804080c0c04050106020c120d0807050c030409020708070201030b041e0b 77
    0x40407881c01291561220000e40d04950341901100c0d10445182d804600741d0283d400340064040e01c6410308201240d0002d0550743c000d1061600390305160b04200015013031030000118030090717041008000c050600610411202c811582440d40c012441e04010a5481c21681318940d8102e9448111f0444558150121601d9803001401030080342451035003c502c0d0ba000f11840c101080c0f40101507426401d042c0318088643c03d00038400403101703402c03a0500503c00c0b1038682d026840340d420001c07005000010150352210410110f1001c3d114146498100c080e6003000403401c110312810b0204008030b07a030025441e58001d5210b00c219850300080440c107450311490785d00c03644c1d10604000020a9060303001901111400048803040303241a000c001c4541c41c0c659a405180000340d000d0006242c241c021700c0204015501482200d1410782e442444404903082071004a690640015440e800e569141c003076840c034403800311401c201051a000442d01c41740c844c45d609112940c0c503079801e05415552200c910100d5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 287491321 1250 287490071 287490089
    0xd0c0e03061b0d0f1a03160e182b08010909080406030e01020706060605270315190e100c05092101020d020d060512190605100315050a06050f010207031407 68
    0x1c174685400c2c04941082030203004c0d00034816440c0c110104500c03910206c04030f550b210042c6000e5103403e0184030700381182e181e0264151088035003010440c1144180414501080d00f441403451004940c0100044010303401304410ba4203244112011524a800729800c9413024203000131707605003080203140640111280542024507008000640542000040c41c00c02c0305444800f40441001450424408121000c15010303800103510107401c411401c0d166401200e000001d401d440b16120142c030560781b901102c42160b0704070102680c2c0d0345c1414040c00490550a040503401c2004400c08980d24000e08010b1b1007036a035043e800020b2140c02941103501079a045074007955183d01119102019140e107204030f40c0950f071003801d0014085400700b03002d550100f08442c10f480c040b219845490151802030051903c2c2d0f02010400800120640301c1c1000101170703060301283c545400388060040701c900d03500c40340c005e40c2554000242307603902040c0c80d400d0b664032035180928161101c0d03a403481c104440c0c00c65090 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 287492571 1250 287491321 287491331
    0x305040c0302180a0c0201020c07090c031e020703080a09031b0221060907050a031212110301080610080106080d051e030711010f020a09050d02040906020d0c0e03061b0d0f 75
    0x3035800070044a510031100b01300e0a01c400101c01c6000c034200e1182a207400450b80000d4011300440042e6000030680400b07a2a003c107044d0707600e004041e041d00c0810065a084caa0000f09102019085071130385510040000c000c1003070011546010b0701d00100070395800103000c403a030317200d504555550600e200b500518600f00403000084110003652501e042d18a0300c000c3c0b01d26040002c040c81c10681c2001034030307409001481e2a00c0081025079000e10413031001c10007907484060040100c071103080518002d0141e07000070b001d1403e000101040010254016801c0d0b41d05007070003800605000508400c103d0101e2034603954440781e0941148542e8040074101d14161000018030806651011003025101c81c01e400802400648200640491041424134008201c44030030401c040d00d00f460f80b15145070f00280010450b060380380e4446040341e1000700c15030900c698822284890300d0348059034007400c220540042c007042c145040c03a402c1da00d02000400f03233828070014020811004540008503ca9110841846 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 287493821 1250 287492571 287492599
    0x906160303090b070f080f0c09010c081c050403120605031b01020f060c0703020d02031201050409080706090c1d04020603150d05030c0a0b0c033312030d110a050a0305040c0302 77
    0x5400407091702800080c00e201c04100c0c54031a01510b17a00a4280c0c1245501e01420b600064840c00c08014054a121307500b0300100351a2201c1c0314a040035101c8405002440d03150520300030b002c001e103210022035000d00d409028409901c000600510401d481445413100c1030700000102d01e01103800c1d200140324042d000c24019298030141c00780c904e1901ca9000c3e01c40b034000407202260b4030b000303200a01c4c0d403100241004100505140e8400d10f5001d0061008a250500c0d0ba21500b090f14407100c422609510311510400408403010081c00e1142401c5a0200150a040d00052103c0c0805000083d01d11041c0c24661f42c00e45e9030014414107030b41d000d000e40307840b507280342c1c90942c491695501c00e0710350f1115107001624a019071001c492040d0103801c454000d2505110510500305480c2d6001c2107103c0401c050308030155111150000b292510000a565840c8a00025410340745500d5102813050400d004203800c0b030780c0080a5412a40003480c000490307658900380854010701c0d560000c1c2d04040c0040d0404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 287495071 1250 287493821 287493827
    0x4021c0e030304060b01050304030e010f0c05010c091e03150f021b0c0f010e0904030c110406170106050301050c25060f090203010605030601230f0a12050607050906160303090b07 78
    0x143c810340c06090308008501591006580034882241c0080c005101e55180b103000f50f004901c403009011745440c020000500c40c1e691781c0c0c2120805940280841d540c00d01c10403840048100b031810032002034044045851035a034451065800321400c1d00c007250344803061000d41665070f9041c4d810043d145024065140c0d007a250550b22040d0300c1c0200343c0140c001030202c0e8659400f41d2444000c00101610b800740b03139a150b032400c5540c805140c50480e01c0f0030703c0324081011a43c0d00d002e03003005490101070050300b20030101e03500da00311101507019602a904100400c01c0082900342602c44210403d02c1d4096518281800d2001360745611744020106480c0c081d42c54400302c605e91242c803840d40300360000c105070750b140e00030180e88190074407030301c00c00040c103201060380039040080708002003402a100008650800340044e502e2640c5402c41031020a504409200b40326003040300369000320990414900e4944500049505440341110310480d481320f494482e81014400d51250003410340000500042d824414402 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 287496321 1250 287495071 287495077
    0x90a0218070305060f01080c0c010f060b09040e0f2806060303080f18100c0903050f061e0106090320091006030c111e070806040308060a0602030a02070504021c0e03 72
    0x21500192420000542e942090b200740c0c090707168141c4481f4440e40d51004a003c15074003003202d9507819520b80d208039600141602a0001803c040c90905440d09246028481218000c03003902d5540e03488000072400803400880c000e00c095000041d20303c840350f0302a040d40c0600d1241540204800d03c0c0840c00801d1580c4442402e008810000f075040c8152142074000c40c1c01890788500c0307c15508403002040364640c42d0f030300c442c0ca00d441c0c9081200540c5e941351112410904251b280c00d0503600300780101301d0085000a07802c6140142031f41c0844c0254101640205000e800380402400b03002074175440c440c21140941690503605c2d0090281c980c0385062100400c11451510485003c00d052001c071303d03040d034000c4d095200c030790403004014000503001c600d030f0500e0b00301d140b101204030303001e0240301203102d4105010035440b490103030700da000310350400c02e0501c6007440096029104541050001c00c015a9011407000b046900440d8003503100c00c065400007680030380440a02110a180c00b4000410344404005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 287497571 1250 287496321 287496331
    0x40609050118060503061c060c0908060408030403050706060510030b150913050a0605090a090201080c030f0412020316030c020a0f030c06050a02030f040e0402030c061908090a0218 79
    0x1444108566600066035488125850550104211030b81440b03070314402d030091540520001d0194400d064a0b0b8880740071030700d22400985103030303888202440070103801089220061201c58003c0000d4500758441c0c000714040a08024108040066140180560ba07003004014000c010421450105100400740c000c02d03007200d489010b038055804141c0c1202c005800c2e2039100401074007480c10f500c40c101c12040100001003440d58030b039a895201080360b48a2005c4148607108000300000c011500d4000509041c600a081088684e41042044180d0408013038040e007183d4002c5007650f0b00c1c40c80d1030040e0b0071400340c950007400c03204600e804001411380c0001e00004c441e000b035401c000342d592940040750747e9400f540401b40107203145603000c0100b81c1c460700c02812140301a01c103480c10404208100c80c080c2d40543d115500042070f55050000b50b241c284103c11201c1000c844182c90a02c0001001d040103000d0600c030000e1201140000d881000c0901180c484594000c1040d00418008442c607007100c0000c0e20 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 287498821 1250 287497571 287497577
    0x90608030c010c05040b07020f06040f0609080705090115050307022803080c0403020607080328020301061d0913020109050406260a0206070f020d02091005030d0516080f040810020406 80
    0x11050f810306020b541160296071200400e203240400c00e40038841005148664580c02181c200400291500a001078202038000b5545001e120f13460044000c0c036048082e00200d204040c248010401031103650b440c032070318212900381030741c983d900d19034140c0c1065680140070144052403a040c5405603102d070100c1c0b18207032194031800010f45a107602100c0034043c9000003900120b00300241e2011800c828051684000124019480c4804e04041c214007266919a0458490780101c014044282c01c1408200100600c8400c0d0300703000c040704001000510050f1103007448441704000c64081d640720301c83d104041d00340580f05004555031403040d00b0507083ca0030080d4440030040795541054550214010710080e03001084a0700740b80d1241c540e113004030120310040380e010f8500440900180c64030a500c44c42541d01d03501079070768140f9110a040c10f100c0d00521450402c10100201c1090792040e44241e00d191750400c100581356018001801c19511075900221002d10a00e400b4065124041c0c000748141d500702d1b0303 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 287500071 1250 287498821 287498831
    0xe07120b030307060e102702090907152303100b0315060304150c020706050703030c030204150201090b070e0306040f080f181302040b1204031211032d040803090106090608030c01 78
    0x78004420303648071055806041f04241c450754025181049409401030b0954068a19041d035912120f209030382140c0b41c11001c00c1000e4090100180702c0c920364805060f08961103482e40c42d110000d42240e20590052a210301c02c088049401c21200e45215144002d02614455072420507042a1220106018490200a040041c02c8000b00e1000c201001242d81e0b40c3c03205800c04405640a4000c1c0c0024420201010303401c0c0000503000151a0141d84502201d4000064442c0c5ea03060900e6132040040038803040c4502d0301e24405080d100060915031050700014050700c115075a24000b807084c883c0a0640d15003980c0071400b0000d09040c00c40007581402d00329012107290000703442c038205038001d80c8a6005011f00c14424110706600d13815056a105200e49410100496603480ca00116041e002c4a4200c02d40d000c0200031103200170103000d10560528490202d02c406c1c45030303940c0d9078104004000170481c041c084085609500d09404c201c0180c56140000d001050f180d00340c00c0c0e1340c2d0300611a005c03186c0d0300300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 287501321 1250 287500071 287500091
    0xb25110d06090605070221030403031806020a090e06060f0c07050918060603010c08010509180106060e090a18020607080903061311120d0e03030f030f0108070e07120b030307060e10 79
    0x820071f40300c04200c0c06c004a40d01c41ca8402c0c030b200b9080100203a00b45511480b1300d02c0800404150042c11611030700300107032038848a0f0f0300105829102c1e041002c1213010101484069581d150550b0040c40d038100003d5601c8115580140c02d28460350301880c0c120b8108028403c40b02c90201806c9000c50703120044582d07680d110000c06007030300c1140d0f6141c000301d6440c200600490800020140e4482080d41ca042212804114014210740d4141d000d6030010713001182c1d440061404200564000001082c00d02c54142c107141c1c40f0344c000d610303050002d01c04d090004500c4100120003040d5080e000004060703d104c0d03d014a01c10031158582c042c12074510280960400d05480c21032040b4002080860050081409401040d1600c200e0440c0c50740d450701c0103001258018000300700031807152003000c1ca0740e0241d514112119141c00060f8021007900104101000011540128a100c803580b503c500881d900d10900086801d600c00e2100281c005418050044081c800000c0d0174003822900c130344200062920 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 287502571 1250 287501321 287501323
    0x20430030e0906032b0f260709080a0f03120e0606010f03020909090c150a0212070602040e1329041103031b160b25110d060906050702 59
    0x84a04010085403001181c040d190800c100820350008000d02103ca105a00c14130742540e42400d003c50030b1600d0320412200c0c420640c4625194510b03065400e0032103c0f4a009140044030760174203000c1013501e29501000850b640c0c0300719122001004090181c44031200c0b9414070161344007059405030042081913003a040c80c5c454038450f83c0c56003484400982210b032551401140c88070310b80d14150701015001d002c40c02c10355440d01040d40c05640008010700040405509000b2420818014400850360510507461072540100f0908030741659980490352742c81c2c00d403620070020b004039006500000b00c0b09042100c0e22007410a040c1140340107800c100c80c0300c6050401d41d24010703141c0482d403a07111031300c60100f00019040c03065460748400c020152400d00010541a40304000f44129400c119030108202c02480d0507490b195001a02c0c54000241c075000d041c0b00da41c80009424180d0b80100c94040121405001151214032005500141a00006902424414050003c549090f68240d00e090b000c15940c0740 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 287503821 1250 287502571 287502659
    0xd051302011205060a090f0b03100c0c061104090507020120040b07030c08040b1201091a09010501050d0603050d05040513060501140715052e0503030306041d010204 72
    0x40c0c169282400032042c140314001800000e0001c42d000110b14802180610300c0340141102d94010300b5000607010465001c141c989031030700e0340341c40449241102c42c100617984001c4150006d5040880862040e100e1980c074000362141384d000b0300b000c40c03811003403003103003903064204110000500c01d0882d80118911801c0d21203104034810000300070300412203140080d010351101031a007401280340c0c60500e507442130420300700ea000303400d45240903c2c62001804400b9162040d900044a90250700101803403001c0070558a98041c00350505000c40403c1c0010310081c1504500c000c3e50b44101907030034100d28900d01804076009401045d2040c107045800b104200c000c0e100b1035080b510b050791005020750446840d5952503000d41400c0c2c4032420f007081003159400d1107005050103188c4198030308000c0c1c264100301000702d040e848099034203183e40c44000c21195400205881e000b00040350001204003004164170900801c150b8600c101c1c0d4000b1800003142d640205091340c1c02c900c0e0009124840e42d00701d0208100701 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 287505071 1250 287503821 287503823
    0x10317132411300405030109030504030c060c0503041202040f0c0201060512030f0a050a14040807030b0a0b0f0f0402091519020712030c0804090f0b040e070e1503010b060705030d0513 80
    0x4802140c03d052440c1540e00081080c0070010030b0f5901d0b0a481d00003080c00e480c40c9090680c00700e0310009040040140a9140c1780040400e071a005481d13a40d1551201d45910031482003040c0402c0007101c0703000390750b00c07a44180c099950202d0108100704084d400a070207000248107103486501100b040300858800441195018212044030520f481000d02c01074889030041555002000f59103091899800c0e0311a0050024004c018020111186903113094031009d100204048585d50420501d200a0344603a8203880c101c4400316009002200b131328000c0b80082c01281e10a0380d110900b82148081c0018100040c05140b1800004008030360141c6001d0703a9030416482100400002c0c0709840c000b00e40b043c1c0620503501c0c8a4900d462405035900010400d4441c1007508200c51030b9100040d01041c5410700caa0410110b00c140a800078a1a004049002c0d40c001804104c41e491074540070100c5a60a6010f0102e1290043c00139072505250308015560ba0040410961a42d1030100812440c10310f00031030507255 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 287506321 1250 287505071 287505103
    0xf2707030921050415050409110c0c0f01180603090b060306060127180e0d09060e01050d0605030601080d020f15160e040608030909010509010317132411 67
    0xb03119400c001d4030409101c40d20a00821405004c0810107580e078042d803684001c03403552003a803190b007428005000c9465600c0741e40c903250010410340f60320b03e10114200c50031342d0341203e600100d40d40706001650240003040c900d918151504401081044e050382c02003000500816102e030351540e824060564030032007515160f0124014200340c198054200000b07454451091880c45540c1d5516024120303e00c000e030083c070b4080784c2ca07480903c2184204000004003240c20b458101c90300c81c0342020180010708010007003410080002100c90014520743c01c448000c040203411100030350307501d2214a480c4e40c44641c0110050007511089490580c0000f01220034040d651582c50440c0c581d50208540c0c1c03028800031700241f12902a02c5a100d47d0b4030b101d158001c00907140074540d1040c0050400c07055100503001284148201001803021a02441800c400c02c174441100d9035030740561110000811a26038480718410002540b402c110704502c400c84105a40c0c90b8440b00a4003035400700031511246130300491003170703 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 287507571 1250 287506321 287506343
    0x703150b030c100f0806060702090f0c0f0a0c0b100311060c071502010207020a0e0f07051b01050412030c09080601050d080d02030103080405100e150313050304080d0908070f0905060f27070309 84
    0x140020f810005600a00003651280c07030001e850200001c5500581001c20120315a903021004388802c0809290380a40070500c020802d40c216a1001615515540500c0c0541000b02d00082a80003c21402c005030142c034051220100038140020b001c0e5005410890180001136400503890706410841406040d00d107082c1d81c815550020110f40541000000c0c070340001540c1550320740d4180a1040500840c0190001b208083c1c101c0400340a5074246425913003040840030041006034000306d49036064075011a04000000c4035030a000c0f2460094203054411940300000000c10060070078002d0044400540740c1d504030f41244001543c0100000c0700d02c1d83c110521000034400e03584c0d45802140d0001034070442c2c40c10201280c6405203190850380011a0903070206c00705010054001c8480c500a0451400519074503003000b422001259461003802030681d2210041400307940e540845c44082d00000c0c01149200107039044001d2000d07409540500034420500c0821200b034824000c010b442034011004041c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 287508821 1250 287507571 287507581
    0x3070303020d121b120e070e1602030c1501060207051e090c1b0a05011b0203160606052d19050d05010e1207050606030703150b030c100f080606070209 66
    0xf40042070b00844501140d516a90361100880c3c0182400110300255148101c11040044c10000c075084105c0b400d449a200c0c000800c4100c84440510390700c20170b10162500e1003040c4100c107074518000c03825040c09900038201e003103002c40741e40c443d00c40c101e5000da422100000d5a41081c410024902030200f51a403200f05454603d070706003504041c0c3c200e01084815850800c3e010913807090743c0303a4803c8450b019042801c031101800400d008202640d07804400110b04139100c00406940c80c07003103041c0b0280b40045001160705115407030703016a0081c80301600900300b051481201c441c044e148a01c01c03068500d00000e032000c09080c82d0800d2680041c101030f012030f40ea410201080320031130080400711595074813003a9030381a010080c0a140110366404a0681e21001039241050030501e00514080c025484400d041021408140d0101425040c0c2c0c00d00040204580700464101610b00365125007010110071640202d07903002d002810081e13050b50b030342c091a4684100f000007070311444c90082c7d4022441ca011036 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 287510071 1250 287508821 287508827
    0x71d090103230c040f02091806010c020d08040302030d050406030c0206010b04060e0307050319050f0a03050f22030302160602032a0a0b01030c0f080307022107050405010305031803070303020d 84
    0x101c0c1240d050103d40c071010402e000101521580d02021443c1d6401240340e50355420405452048030b580d59640d05000e19108000905401100401901c1814426812803d01648004030390246801800703940380400b108202402a911902c0344000003464841d60408442c0301180304e5058822862000b4642450100115203090000707038a0340d4980100c090000c2d41d81c8d400c00100512000742c2c0c0444820410300d00300303170341450018185400d50f078021034110000250712102b1500c1740409040b000b07440344400c449031115420003003080c00c0c051980520202c181500060008941c080c000e294814080e03c2d21022a1240203001000b400d6180340c0140d40c4805180010718441c0429480844403010190b44403190380f4402a4400d803164004c0c028140504032041214801a000010085161105d00c0d07012a00403605a040c00f4010f002c06a45d110641105001700001808014014030035541c583c1410f545a5000c40340452450840c804000110700700440c10b4021a078050f0050940a41101c20075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 287511321 1250 287510071 287510123
    0x7030915120204090c02070e15090a0e0f0a0c0515040302060307051e0a0806010c0b041211010f1d060f0a0f0b150309100e0d030221071d090103 63
    0x44041c0800030380c1c00a400811840500010810f4120110b4215161070b4081d0500c100c80d004400703590b590408000c040340f400380d001031700e048003500c4034902603580c04103172001400101001c81d0b0501414502103848a0300044215802c1c0c000c024152140b59244204071a0460000c2e070700744491000d100410140c0717045c8020355840491410f081c0c6c80c00d100b0303180810b509540d028650410700300c0460203c1074158041e4090358007410a0800d03400c4510306868514980724020b00c020891030120850001182c80b07400da941c07003510041d00a000c00100341c1100e030040d010f1400014445280103c0d00e0f03049a00000f0418003503c0c00b0007401e0301940701c0d44004070103009000f5640c800b40380c41d84c01c584a551940b101d00c180b02c4442c82203c6807203007041d000b400d0404820b02c00308801642001818119210b0100b4980741c3c502040c01d005a545442100c60301d00811020780d080000c02d41c20003040222a00020407504004800b500b80c9a8062031004202200e00203010142080d07004c0c2640d419440d40d41c12035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 287512571 1250 287511321 287511359
    0x20913020c0f0a0f0606060e060f0a140a05070501050f0f0613140c03091015170717010b0a0602011e0b0315010303030b010e041a0402070201050c0111031605070309 72
    0x10b40d50398840d07908095152211260081351401c4a4498150a00000d882101d0181c00d4601c0c01d40c0b5100007180c0017401d240280c036000307a60070500140403641c1c80e005001201c0310f290042000c0351a030341a802e0140c0582c02140c401d90709e42d4200800240012004200c0b02d02c144005041154251100014084024103429000d1071031640c03a40c401006841d020519031042c01002c0380b0660300e00d4038091f110b041c0150302101182450401c1c907891407240e00c0341c0309031041e10342e080802c001c20401042d005140001039403140f03c1c0001e072003400c0c2100610640080d9441c1d88242c4140480c0307036a46030100d00700c810900c0124500310016082590640f095000100c0010000b41162030340c00b030031241481074003c280d100b1404a99210b01c074080030f50f08500440610b840484040184165010003040742d0b011005459205e5030b0b00007640000c42e0b000708203481600e41504020404c2e00705102c0028101e03402030742c0e43c601301c020340303942030406034030400841d100154140d82c1c207100145001901da01c02000303209 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 287513821 1250 287512571 287512573
    0x4140103110d050a08090a120c0306051b07110301061a03060f010908010c080709060f140c0a0c08030309060609370213150c031709011803120f020913020c 68
    0x14411010840400c0a0700c540b5000e05c0701c5a6444d21250100301c1d801c50107a00c103030360001c4003403181c00110f10050051000c0303070f803c500c0100b240e581e0400041041000049140454180817030ae0006101c6c4060b01d8030f61411040d4000c200068884904200407009402c08254103401000011864140b01c8001c3c8510b04c0103041100300b042d15000c0b041d080d1103580352200000b07035035401001607081d44845101d008005c0360030010348080c1c0382000102a68014039402811a4001518141d040d2040140e4442103070860400d003649a2505030303150b1207901c00d80394483c0b540b0440000ca07102c0e1404800790b5005000b00068200d0780891810f11026801c40042062001000038600c1000114180010024115561800031071182000d64818504044651400810900b50008800a13800c10129038040000300040501c5640f03c86003103001d40003030703942c00702120303180700441c420160040000e04800d0071a20061001040e51400c090072801940b02e1280d1040030b1341d56a0220ad282c560081044400700342c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 287515071 1250 287513821 287513839
    0x1e070f0f11030705040606050d02070c1208030a0b0303030118051506040b04061202121315090b090f0d02030d02130504060605070203100902030a02060904020d050901050105010e0414010311 83
    0x2445000320300001010541d25494603807a0012245001e0102802802d0100c40804c034641c20003200809600a80304180e000647c000340381000d0044441089004202801120300d4010ba2454072810035002600c10310000380c00c1c42d0b0700c040b41d0b1402205580c16544c0d24480703065111018100c07500504806045022110f04c4800540c500c0c0d2901001403024045d441ca8143d40c1c0c51030900001d00c0d070035000c036010101a00c10b21068520701011a200d64011355461101c515184e19414503540c0f000b00c6501d61400e51b880c0c101058104006181a58403850411040e1002e6420b2a020719031101401c00700e600060b04204034883d0b46039045d0307010307007200820003618104058641020500310b40c060b81100c00481d4000c100d0504524082120500743d20429400b405140e20399404a42d4600141c00020b125040c04109030880752200d271706465101030f20b00c070188840c2c140444864000c3c0828003405001400380100c02049080c17038001d050250041c0e01e56070080d43c0c40d64036080d040c440c1400040d82d00c60444 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 287516321 1250 287515071 287515073
    0x160f0509270d05180d23030f07050c01091d18031c0615110a030e040b040c0908060c0c0c0f01090e04062405090406051f12021201021e070f 61
    0x70011410700400c2e94071266520360b00ca0701c0303150f43c40c914590110b20401001c030b0f084000401c4481003c160003074414407060b642400744052030440c010b00c45580301060740410b9641c180240041c8c011032120082e201c0c541c0c019120461004582c01c1031a0203c80d810302d180126070b0f1410500e603091030380c42d404802c0c2c90520310f8614080003040d000c1c1d2035005155868940a01c41141200e4140011203040d05001240c0c15141c0804c40d203400003000d000c0d06108e40c0c0200c0780c0168403641c02074461064000c1081143c02020400034004000ea4041d070700c4540b182c0310000f50b03242070070700454004c950100c0041910005090420a0031076083c49002d042010b5001d00290403003209080074040c511480700801c0700e0703260003216400b1000300903d4002810400000308490b4a600c012030303421a8100e180841c10740d989100e0584082803414202d1184400e001d80064030138440b80c45150624400c89407000b00c00c40c4841b00078280d000d030000e011300c440d4848204507240c104c000010408a4462294070454000c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 287517571 1250 287516321 287516323
    0x1e1208151305040605011e091e05040b070f2c0d0209010f1a040f0902090f060c010e06090304061e03090501020a030f0c09080718150602160f050927 65
    0x101030300141e200e0311403091100708070541c00b8403405012100403d4a2008002d0400d0008000d41d10404211641c1c98104241184043d85180c820700404242404241094a405041800e0848600b40000c140b5000c2e0302000f48110881c420944145201305006003044202c040121f106846855102c00d07248103d000585806c41c01c58005c05034650310001044c64003001441600348002c081000f56002c0206100313070303d100e02c03013002641c040040050300e80d005900070541c0104c11800682d80001c1c0854034143d000c0c2c05412100207040038909680654440d014003507601d0045028800108004021120000242c0c242800154590745004102c5c004191580da0880c0e01c1074010b00d000075240c500700d0b40000c02078020400861401d00e0400d4806140c03614203901e510090240099941501d000c0d1005400c880d000580c20401d0017140e062a1561040080c5d601d404284e1311541c106008070001815051120300c2d80222040135218445541e03c0c0e4500c628010740e560411030891084030070791190000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 287518821 1250 287517571 287517589
    0x15090b2d040e0d0206040b0c12010b0a02030903011a0f04020405030d050f0d090b060a1d07030b03120c0102030609010e042103020c0115060801080d0516080412030c1e120815 76
    0xa250b0300174005505090800045600d40104008440f0004011180d0f1f5403e00300c84050454036072404d5961540010841203003184522022140c0c158280801d20b4140701d0541141e10000c0c000b166944849214a010322042e0b000d20301c20f095258120381402c4941902071002041180c4030400f10610703103109070b1300600880b20600016103079122520704001850030107641c0e01c40584810030b2492000b021569a850000000170241d07010161038045542c220384042240f001e808800441040c1c890410a240c1030007074204031003040c0300f0244100001480900c5072400e50149802001c003840d480b000c004c06c1c0ca0400c03010903004040650802102d000500c0a103e0140000349051036440c0f0940b40c03150041400206800011507070b08960b40203440c02c0c0d0041b0840f00c2e50881c0004502034005103041000250140358084a44078100040c10780401d41c1c800c0c400c002140c460280035071301000701c618103000c08040f041e00401c8080741c24044514107010720030255100c0811001d20b16410150008030302010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 287520071 1250 287518821 287518843
    0x80f0403050c1c11010f020c03071e0522230901050f15102105010620030702011b0f0203010f0c030b030627010b030115090b2d040e 58
    0x2e0440c10340a01c603440d054003000459200000301050f10f03856611052400e0b0368034641c190600c074003894078165580c000d10100c0701a00000302582c1c1c0090b1380d507032030035440340302c1000d5a1190301c980000032440d85000710784500007000009080010388050850f1600070a4500a01c20441c85009028078a0304c46802c0c60a120b07001c0240045001e05044000c000c90700700103810048a402c4c81c0800140325200c3c945010b10310840c618046202403004138109002510314019401041d043c64008030300d05030040315800c1ca801c1c00d908a91041c41020007440d031a0b0040700d8000780000c41507115440c60071061085070b0344840c016200b030106100c0c140e0009084503010341c4404102529600108500ea4262103a03041d84d031000c0c1d0140240d40341001c40c0040961114034a005034200075200303910051400d500101c15104058001c0020141c00749003240000900e11903164100d003407100c899414182140c03d6100d01902d4606882c0380c0e032030364214440c10484045220740003592a00d2000c0f000c00d041080307503004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 287521321 1250 287520071 287520073
    0xd051b12090f042918010311100f020c010822030306050a0f0b0406030905030706090f061b020c13090512031f0b09131e1e0b03030d09080f040305 64
    0x244046010b000300381494215542c0f02c0c03840c110b0184c0c1d010b95200054034010030060000c0800c3c030742020010724145420300f007048010000d10004401c2158894810351101002c07100914440740c101da080b14100e0000d8014801a088040780c03c4195005400407900803041a1600e0110804a00c45081410040d401940001d8841404001c3c904180e030494000d40a810300c0e50765040c0c105102000c0034403680c0300c2d00c0100b69882040c001484001d009850030b19900020902481d1400d00300544d04000511040c3c6280d4070302251710760203140c0650038000040e044d4018010000201080241d61b032210000d07100d00035121a140030000d070083c841c44c03145490303000c1030540340c1c103040e05000410f2905404c000c03182c0200c9038091180111100a44000d40812034001c0c1002540c41c980d040035091810341d104084412484401f0310941c941c21000c04800e050300c184000613400b10302c03501a0340540540680640040118100e860300c240c0207000a01d00034542d42c0d14098a103030101c0381640c000e510903141 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 287522571 1250 287521321 287521327
    0xe010b01030f060602060f07050c030a090305011d0d0f11070611010b04050106021002090a050904030224060f0402030a0b0a06020706140304080f0c011119080112050d051b12 76
    0x81581c051040c48800c414040e0700700140c80c18480041d650344000791051400b5050200042e08451094007180c03685000707042030301e440e0302d1003a0300a0b20034809404101da065081446035500400040358180c0c202200000800c109030103c1000e1310145840034400c410418108400360400104000e2400244081c1d62025068040c8080342d50850f0202d00010b80b045042500411049038005a4001d0200c1700384401680c0d060040006011440703581d0006800200100800040c0358021440480e40c0502c0303400c986d85904090391251080c482251000e600250300d41e100d003001e042aa018551046904100003440c070f00309000614080002c0c3d100e007005a001403410307c50300d648905481c00c02c5203821003032415420f040d90740030050b000311030640c400c0003404104699a04825000180b680851081032036450044661041c81314195100860102d1081400094007842039414484265004070103000042c41c1001c04607140e40c0000022204200c4114408d402c21006101e0b00400c81892010705903 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 287523821 1250 287522571 287522591
    0x7080702130218030c030d1403100503161d040b07030c170c0c0706020c010c0f030302090a090b0a0501020303013b0f040b01060f0c061127032802100e040e01 69
    0x8940451707110a02d00980204410b080f803079400c942844100c0035480303401622a510070783c0400e80804654401c951501c50420103010503d0712604000a079224100900b80c034104da94441018590700707031002844201340000040c030840c0301b90312412000c111031a1654080c802182100ca00d064213844408000200103040710b060882084660005c15290001d071001031200c1001a00e01845414090721000c20143c0c0e003010144246e0480300f07005001014513004070703181c1190800800d010402e843c09200030000208040d800007068134121065100a141000309aa0446020751079120401c0700d10f001c651145a400b030080071580d4881d01c5030400398543d80c40c0c14140680c8240d01a801f6805000c001488c51450035401160001003981144010400358106030b00c05545202d4030881d50074010300105441402520221000021081181140c241d810318100c0700d0b41c021600341d12042540d81220000c00181000b076000c40d0740b0344260408a8008403140045000d0350315140320300c020340c1d54598801d1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 287525071 1250 287523821 287523823
    0x308040518041122050a06031709090103140307081204030f0f0806011112040305010603020306090c060d0504060b09180d1e12060f15020118080708070213021803 71
    0x4000d451104090803400d040036295412981c11000040d400b4654208020030000134084041c880610402d01c03c01ca2490300038014801051940411134100d03000c1d0740c1e15400210f884064405414006022501d10b03403866440340d003244003100319100140028482d18002c9842400980180410000443c5240c50546001420340f2141c816030024803241e46080d41c422680071a00b60751280081c00c1181026103401005450600d402c1555400c0403030002d4007104203e0190005800c403442901142c7c0aa1284c03641103031034180124240783c01110a011030341c0204999004a500203009000c00914850078802061020008545a044e040c1d03000e070305c03000c2c181810417920201d03404515004100c04071440d84042a8511200058204401020204420492a4000c100074284901d8040b03446a8884c5812000e1441010401c059480c0030505440c00340c1c200503506095901084461074030060344d45400b0180c00540090785c02c5501e500901c01c0d04505480104a141d80100180c1c10000080c0c00701 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 287526321 1250 287525071 287525089
    0x303032d240f04061502060f0f0c13080604030e09090d02100f2406080106020303010f090903030b0a08060603010e0f07050d031101140f0c16060f020702030703080405 73
    0x14011640c00d100800245a0209076408029034660407401c501588040c001003807401c944541560007450a04002051400c50302c0001d001d1416809640c90b60303031111425207851104450f000150300000c8c002528034607014005083c00707600071400780c2c0c3c00390b00c40710741501d0318000f11400c40c003041c0820080705140c6050034109902c000b07100018001d0b45280c4070002e4845007506ca0210baa991035100c00280425640c02ca4841c07034603004003c42d080c001c5ea000c0d0410f142d560748201000f29a07030200116103a031010084034140c51091031a820100d140002d110002e1031044415420180d8650300d5108031b588402181000f4107020004040900b040320806003142c10000d207030642c03079005801c0500b80314404102041102e000b11050038904400e420250b44201517031304100215480c1c040c1d5645c809030303405e51050080d803000195070038aa071054488a810b129819828400400216001300000e03542d81000c0b40c0c0700c0040901506006141d4007092810585401c11a80c504001c00c0600c9542085421 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 287527571 1250 287526321 287526391
    0xf061b140c130209030a020910030213020703030c170105150d091202010b01050901120e1203041b1205031e0c0109110405100b04091107080a08090f010e10050402030c030303 76
    0x3c42c5450400000a90303508003041c0001d002d40071100010308200d9103140302400464024008040c55011300d00c2420003075002c4c05080f00400c5c1f030400045103042c400c0160f01d28000e840306410410381d007480200a4a2440c9803960364a4260401c454291500340780100c0c010b6034440c441e481a03500755050060300b03441000d00c030641007180a001c0100039a91240c00e07011200304800c070000e0b240c10050b04041c24103020801d0746030400000014007080091a594010301050b40385903515000d40c036108043c8a503001020301034002d078400d200e80307550034942e0601a4401c5d000441d4451910070030411003070940b00030319030649900c02102c0c159500c6090034010f403503110100c0710180c04a00d0505042101900884c040c111503141e4411401d6001d80e88003045406071600041a5030b19000e59040c02012000226041c500758010448007041c3c2c84014007503000c43d0800c1d140945800851032003004020b010091050ba0f0510541e100d501807030f202800214000c490540800070220880b800e40c0b0340d40d40e01040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 287528821 1250 287527571 287527609
    0x10e060c16021207060c1509080a0f1e030606080c0903031209070f181b051e040905090d02160303020d0e01031d01060810060f061b140c 60
    0x42209514401048401c0c0c0d0001500100507801d840c000f090740c46510322400b41e07491080ca5408a407003a040400031040610581c0c68840760410421143c0c250340704158001c01d9184103001040d41c0318000c01c0001301080301441c04507846814100005a0b01003104024000700fa947c0c0c07801d214181d4000007042d80032507480159850117040c03d0201e0b40e0391080c00401e00e400d102090118101074403c2c021880180304289204068503282e0b250b540100c0380b00c2d440004484d203440407410075003400503000041840039450b03090030180820240407850400d0308240040c0d2130108404910104144030b060f000e00715480080020040c8840d01a01d441144c0c40c00810021b06040c003040000c1e030005950440140615100407140a07040050b406880103400c00c002c0b400f140501d41003032410550140c000c039400700003210b54000e10700320441e0468200d03009040381903009540900c1100e00503003007140e82d049413100c1d00784107a1031602d0300c41c0043d044a22521464016010760899840c04100200e0002250b403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 287530071 1250 287528821 287528833
    0x90f150c090e040b040201180b0307020d09050102160b0a030603021c03020d09150e01030603020d05060a0c05121501020f0d080f0609150f0310060b030402150a0807030504080712020a05010e 83
    0x14403501350000300144004d040040540148000c0007100e42110024150640d4141e101c0c00c0a41000c3d440e03103d0528900300048010100042d80d6200041070b407400f00b00e0711202082c882c14900c0c00807190303020b014400241a00c612000006032202e646070001c0c41e1049410001540f11850028100400c9119050030802d100700d09004442e24440c0382c0400444600740341c5a0002204016406081c02d544080e42c0034403100c00c001d00740700005c18454454441800100008402594181d956010f005000d08022400f180001c03003441c0d0600214400c1401401211414144078030a80d2030100880b1210000030240c0c014070503c2030015070304580240c401ca441525031710f8101011a80760003140c000c01c0c4515070303c01d541b002c0c1e0f8078180000c14010007898018000b4503201c5803170000c19441583c2c200d0046042d882d544034400b080c802540c003441c13165640c00e082a16103040441c09814050700507561110108074490001e00e81c034202200c003001c0c42c0c01420700341e0300b036042050850f070090f04e0b160031540002c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 287531321 1250 287530071 287530073
    0xc0a0f17070b0708060114040803030a110a0c0809041d030703020105010501050f0306101716021207020102152e081b030d2102030a0518030901080a090f150c090e04 72
    0x842c50382039100301180703001c51450784d42c480122070720030000e0079900540707800090205502c98048010342c031030110340205022400001d0801385051144003130a100242d608180f00000420141c000c0c01880c0d0000c0010503604440900c0c6240382d4001170b9a0500d551000400904143e020300a40380108004d080c42400c0001c103014580491000420152050f40c00745c492104076030103400c04035402c0307810b46c15071601480c201040345600c0350400703140000751050390b1388000300c070003508200c1d8a40790741a030240c0f2504840303147d12803000002602603440700c201c42c030701c0400500b9891401c244180b10003d400b000c047c50075410f42d04221100614140691554181140c070b514000390640b04050313145058031b03e6003010380e844c450075007564101410490001052019014142d088030f0302a04042203c000f124800303d9856680703204410803280801c10f620005070a00815500000b54980550301d400401d08099980903c511901c6a01d1003900d6500c40000c8031080d40207002c9006003055100b0381c0d00724180703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 287532571 1250 287531321 287531333
    0x6030b100219060e0a05121b0309130509030f0a08041101260606090a030c0303080601180b0313020d05010f0b040c0e09070c0b0915070f0c021201020c0a0f1707 70
    0x1110409400d45888569044503404c04000800c020b640000943d88074110120098035250b102c59444e1200c40528078281002d01004411180072120081c9115109042e9441602c080c0c0350040c06840580000e000c149991400d40c8010304400e220740e03850510b10701d071901d810103051a51040d6a41040980c2d0650b1804058042c0e958504085094942d08565150390008035184621180c03183c0180b41c480c00001040701441c00c600a03070f8800d40303451800341d890400444090f00e06103c100c4919070011410000c1002030b10045400143c007882288144810790049400d01d01190070440d86a913540c5629241e00d41c00b4400c40640d014206c4041c4041c8540030310040c20f17a076501041350310030201440450320480c001d6441061346a07000203054420320304082c45680f1600583c2c0c40c555850090000034904910030b02d2860150f441075121155014800d80038090320b148508840d0b043c0b50f42c01c00c10030810398010001210018460103800e00b070501c552511400014050f2070380d0000b004180598070020760 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 287533821 1250 287532571 287532613
    0x5070c020102030711040f0618050c07080304061814030a02010501080f0d1b050a030507050609070e070f09230114090109031403091c0201021c090504090501020f030106030b1002 78
    0x2c5c02507802280241e069000600901c5401c10450074a03180150025000c80c0203d00c0b0120f202d904402000590b54462003298071344a0404020200d10080002800080d21584040080002c0c0c00101c1c03040c480700e640b10070b17200f1035400b80549594804500340142c164240906130140c00e00d4000b41001004090388542c2d584082c024280922124030355121416a9440703542030342d2030304401100c8900c9040e04001d8980d40c0321602c1030f070f140d00070031002a50001d4001042412600d50282d0420140e482c2176040380c882c003c03042c0c0b4604020440d080001d40036418429080c403101ea04da410311060400130005401c1c1043c2034030120254170107100780c40c4280e030020601002c4a8024940a0f00c2c3c030444d440d440d09600ca038040c00350b440ba10704016500100000000c03906040d1007038081394040c94001203d001c020185050200015000c20300c144010b00305a00601c0049206a002504003035140c070b0a03001c540c00076000800000c1c2e4520060100b4a0445144007100003280040d005031701c49401885c110032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 287535071 1250 287533821 287533823
    0x204140a060f0f230403050709020c030403030c060f0c08060a0608040503181f020102030a05010b2b0e15061f050307030207110d03110106050a061e1701150305070c0201020307 77
    0x4462a2800000b42c010b00c0c004001013110011818091240c00a00305160094002a0340e035200781134001ca4080628801c59090341a810025400c081c907650b0103d905035010b10044882d02c0c3c0304c1e000d0002c030848038029480c0c00030103a2200ca8407130bd045001d0158104c1140d003d8410401c411041c407010500110440c1d11141c0720086210302d24580c0408a40d140501c141d00c550210182c05800d000164107501a5018010103a824402640d82d9a0040c20a01440013aa5207000c03082500c400031314080700f0880c25080760b00034040742800000400d54240302e1070088144511400d482080542d20b0081d0161903150000070982050002d2007900512500005080500f8941d0015080d8140461901c1c0010503510050405402401a00d8010700e10084080703454255804c0220100e5940380a1135031b1030943d081c03556440010b41c1d01c6062069421001c0300304200740178010201100c0007107040945400307081c0c443e50090800c801001d0003000c070740c4000c00c4c05040000c003400010050b0703404003c6074030039 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 287536321 1250 287535071 287535077
    0x90607061a0603010806010608010f230f0d141c080c030601050403141e061527072606010c0204051b03070c0606050a0b03180a05010f0204140a060f 65
    0x100702801071101c4408410700a680e80041e0200000030546000035a0340c2c16221641c1d2001200e9030b035600400ca2000791406280b0345488100344080618003800e10000d44d08030000c01080207100043c0215203003140420094508558180c180401202c2c100808102c40010701510403100c4244100205070181c06072409010321000404154268410010b8070041c6421440b1011070341400c2c184140d40311040510212860b0840204010703d48001ca90140f09000051800d1150f0090702c00b0003244980d40300d1407400045408003882d48842c006d24180388a500940ca400e95a0f11111080008100d03d4800603803920300344504011159900603a01480c8540c144c41c089095180d4641c4001020110003403445007541c00701c200400c0591080c0c1305000a806540100183d6442d4002c1c45001d11183c082c41d0113145040020491100511790461041e8440d10259004a8040e503103550039560200c4c0601d00c2c040d00400c00780300801031500d800000440c2242c04000d020f14120340070f0000403d001c02a07047c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 287537571 1250 287536321 287536331
    0x6240d05030702091003031107060e0607020409120203030f0f041208070c02031c2a03051c0207060b04050c09012c030a12090e07020c091506160b090309060706 70
    0x80100c10400d40d10390a900910f460268a401e0410b101d00750510301c400d9000074083c0e510040041c1001c16000d00f82c0b04141c0d40c00748182505c0c2c0602000b5486004102d0300107990f00420000f080e800700684444a64640c081c45c2c0d03e0810078225240010064490303043d03603d908090100140f42d0f00c07115980960141800540c513a605c00381504e1030342407003401035014042c0002c4003070250f90214180081c50766540340c04043c0c140400f008440c0d40d000b00300c00702c118001030411601081c0103101505e119941720701c00100c60100200703a0802c1c3d8000354001c82c1c41030b1f103038113221110b4541030140329070180052601500701504600000e140780715041010141080c02c80040713104200c0038210380007414010307003144c01007070700c500e00302e1a603a4180303030b9403000908060b10200f110400002814050440c07640140301e03440d281000c1084101010300a1001c401c0c01c0c000301ea0340b646440028100c5242400003011484155090024400074006d12900c40b54000b08400882135a0707180030b0710640d582103180094 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 287538821 1250 287537571 287537573
    0x60207090b01030e011a01110c184602030610080a02090303071a1608010b1305120c0406080303060a18020c060405030406020f0c0619090b0f040806240d 67
    0x100740102020a00303508003c495030400405c121280c1b000d00080e6a140c41141e102c10b901500c4660a440c540e07440151a040c1880300c107400d18851340c0140f420b445140c02100000e4000008080c0e959640c00305048501c00640413140c00f040d01c510318009000294550300c0e09030001002034900c03031070310001c0c4510b0710041214500d595041c0e030310b00d94010381241e546080900304403102d11203510048144441d118000303034904c2d81e40d60707120a0001d4152240f612513401e00c1070442c800d4102d0b4000d0546c0745905030700000c1a0f5038000402c000c1d454010080c0102d810300e03005120989059400c585840e034420400d004a684540e4100000c440c0400521101105c140d004400070b480b03004074140c40340c42000140018000040002d000301c440d190202c0e02070701030114000c1d4a486101c180d00f0750200d814080d08800c60660309014010126902e40710100a44a40b034600700381e00401c50002802b500454140010f10f000c10013a90040242c0c1e441103510b52800c40c861004000e4665018090014501018 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 287540071 1250 287538821 287538827
    0x1b010305130803070306030c0503010608031606200306090711280501060608010518040b0708040201020a02030d020319091206020903160905060f061201140d06090b0106030510060207090b01 83
    0x600040d0b401518256641426030008020b04081d001c142c40803200c10100044514051041074203c689160155007410343d0307585600c90800310b04100f0fa407400e0300e50703103480c6402e010544010300040b18081e0150700d90030124144490280c0042090003848111034801802941c001419182900f1301036100c0c1c043c03000804441d04102850341d0080c1150308201d004243c0681008042d0706840c01583c0c400c03244806a00510f10308135090720060100120507000c11841c80c801c4801a41c0540180101e420610099010a1401010b071201600503080400c1c0c0032014403076510b0602d042e000900d0030084540c10130303801075811002c0d8038008208030390010b419881a00d0031b0154034000425011a446020741c0e544515003d8642150854429201c80044200030719004060300d40004840da0400460b03800d04021107034201c00a00740340d9100c1002c0002ca400140e01d800f840090700d1103640840e145514260025095407800782c40c00c820f1300e0801005000955000030072000304c840121000c1208541c00e0016 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 287541321 1250 287540071 287540101
    0x71401020a0c0e0928030e010206010b07020d060e060901090309060905010504170106050a1715010e0f0402060c0a03030b2707081506180102161206050603010e06070c050d021b010305 80
    0x410785050001401c4031401945002c1200c55000f40c1f070391001c480461004a07140c2200340600800080c0900c43d110140c00c081601d204034500c04c801c005211000845103910b8070804031082e81c0d26a449205e107008142c2e210184200403c85414905c07000c0c1d08000004e0b145000e203010350f000c1c405542400c00c4800402b50081c00041c400506942140d6440d40e421000c48813641c05000a03d218901c3d0040c165200544820304842c3c215226003090b440b0440302a804e110083d0090703a00c20418400468004418860800401c1c82501c0025004000009000d030341400540342c03540c8a072a42e043d0f01c2e404601581c400d5842041446c0180c40c60740c41c0028180c6144591500980124000c038121440202170791038009008426000c03209214115403092a07008100e005517440c1c0500400e14400003000754000e10b800c840c00a00200c2c811000607001490100100e80d0a00000c07900d05a58060200602842d0401d40c030030302c0a4500e01910040171020481c01c01030b071038105a5280001180c2d03400c0c00d405 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 287542571 1250 287541321 287541343
    0x1030f0519050405010204031a010e010621020c07260609070803030f0916091a0a151404050621070e01080103020d03230a110c150307050409020309071401020a0c0e09 73
    0xc5410701e4404559682700c007181c04d028402064071904000315007140603028201d04015020022104180c2a0342c0800c00307508552220032061103000004100c0105030340305080f040d11060f40d0300c001800005c6106180190251086015402148003030041c0307000032080365031101942c05109142d072100e010b11031034030341201c0d81c01d40414218070300401c00d040c140c1c00c005400000042209600c640c06010085800311601c581c1c01d40b00300e442c07522a000c84c000c1c14851a0451082c00581c10715a90b800420841d6100400e00c0600c1d070542c01d407500e180c081c044605600308455180101000101d200042c01c3e5100c10f02002c0e114036103002c0c1c0349040600c80c014208243d0030b2041003400c0c604007009408503941048500c00045a8114200151031000040c00e45040000400c1c08106140c060301101060340050980d4040180800012131819000d00081d4042c480b41070040240c00e240205052284840300e480314110b400801100000c9030f415011001030320b00c41d9089840648803036401e28908848088 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 287543821 1250 287542571 287542583
    0x60b0a05130b0a0e0a06080601210b090a060608090a170702040204050d0b0702071403060c0a03090f030906030b0a0e0403300b100f0f030c23030601030f051905040501020403 76
    0x101d41d6071156004400302142c10085d190b80f110170f030b210481950212801c590960000300707042812800050712700a5410820005540015110b0500002c20703074011048400050250b1151010425a940031499580c0f04202c41c0240101032800d580e200c0000038201008041d56101089400540d40c1e0b90341141c004140003450848132a085190410480d10300302e441c040036000d40c1600050404810301c5034505c24034020080c2c00703942e446100715503454000d0710340902055078813903071040020b403c1002c1100081c0251115524a4035061000301501c008a502c10b015420090042004800151130240c102e0b5140c106140f400807840c2c0180300b48034990503e84602c102c03001e1841545e40e000d6104400c050000d6894040c0ca14282c6d60a0b03a40007520152080012042203015100c2e600c42d51180b544242c00d40f40c040c0680342d401c41c0c000c2c80944031404210203800d0000610040d91380500c5100c40c4441404400c1c0000c4c5080728820b5804409480c51040d15a211000102048800c0d41214045c5621030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 287545071 1250 287543821 287543827
    0x5011e120603061d070501050904090c031407080c150702090603252105030915070203030d0606110106080c0d080c030d022101030f30031509060b0a05130b 68
    0x42808006001c10161407130044440310b4055001001c049068815184103850701840c005810061000800c10580261001850722a012000070309113025540241411002001d1950031310b40481d040c48000c46456104503d600080041c1c05203c80540710120340403070307810307685a03034004c0481d04103010312900302110700300d1019076200316a00347c80d0003007918005440c01c01ea0b054060701070a45000300035409009070740305001700c508914086140303200410580c1443c40c2011400d030f02080c81c5410601d948040c15881e1041401219807008201c4255551480240001d501d04a000d54845204408440c010100342c0380030020701041a0469441e44d0340744080740e80d284418000d2000942100c180d404d10717192107003c01410722500c03620702410303240c22030166007004926070340301c140f000390612001c6c11650003010344104a641340e0401c0b5010380400d072804103055500d0341940d031040030f0075006440807030703d800b40500440384208141d0b10442032501b881c5036241202d03c0e502c0a283d0081d480100e4081c400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 287546321 1250 287545071 287545073
    0xc0611150a0f0b0f24041d0105010305221101030612050607080612070626070c05070b0a02060109021803030706020d110f03060f0f1503040b0106050405011e120603 72
    0x768042603040b410070b401000411810410004040c0036004140c0c0c0c40030820915203280304584900d104ea01e510001400d20306507803000d428505c1007800c00f0207030100b46000010003182d40c142c060543d1103150150007000802c10000c2143c69600d1645000d08094400242104983d009a204c0c07005000961204000c8803264648259659001c031002000202c2c0140410001c0c1000606641140b001d003014182c0d0a08207901101e010180308a524000c02e658961903078a0580d481a00380a100503940c0c10850300700e50b040031490200b465100303043c3d4440c00c00143c84581d07408107d03a810340751620000b680d036400f0b4850304003400002a4809506000c0007904200300043c03039004000c13601c1040d00606c07400380300d406441154001c11031100c00742101040007454a1500700120101c1290041005501129040201d4100700702c0d144440c070380760303000400d00c014400c641c0545030050105141241c82c1904020000700340c000c0800007140485200240c5200c0c007070180756074410707005881104004156a07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 287547571 1250 287546321 287546341
    0x5030a050f0f010204211118070e09071709030d020307050a0201110f040605030a0e10060e0c0301030c03030c061103070c1109071407050c040608010e0d0207030c061115 74
    0x1418079001451048100e54602420306009481c1124441440582136980303080d0b40b5910103181210803112101007038800a019034866911340000d260340902c0d202e1510344841c02802d0445600d11040c4121500c60400c0042a03012000308040c4000c1e034042c0419880c2d040ba03040c0f4502a40c0114658180080200200302c0e0348240030300344a0b0010390007449818400d040f481540e228441507524030241c208400c0c400c0a000e1401160807002658000074201c01010925080c4051142e58120142d2a106e00700501180411095002102c101c200d41c41c1d949596a841c400b45c1e00b0784001400e200000b03072210284086548004051140c01001590702d1605800c014451041c1c0001254000401c090540e000e041500800d80700700b8290b00e40300c000b1403010708480200c2d04880f90403100c504c1200b002107820b849030b01078071004094500021540300c401511650520514440e00340445d8401c1e03004001090540340c21394216009810325004a042d4030604034104800504044400f030540c205008003aa4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 287548821 1250 287547571 287547583
    0x905010c08150306010e15040f02040501140405100c03171e09061b09030c06180108061e0f0f040c0804050d0f0903120e1011070b07210905030a05 64
    0x105940e240c40e103981d101c4110400c00e1081d0900302d50903500807001400990301012a103608440060507031030041d00b460b000038040e120008039070911680c0206081085503003051070b204c0c000b01d920304168101742c14038012814013207500e020901044102c3e041c0b2000d050051841071244030021804202502d0f0241c1460302c140c2c0422908a0707481e8092001580d04400030941e41d01452445e8a900b9014550429501c00740c1c0043e001e00740e241c00751075401c895076030320300004100d404a44600000d18030410b10003d0152440141498021280340c1c211005980303500081a80d40c1c01c01300c42c1240078540d14030105404003440d4850f250018074003c421140c05070002912032185104008582010400c1320301240c403014680c0c1036034086080401c0610000d155078002c0b0600200d00e240c5294401c4400c4001541c100c60a031642011811011207041a041c00b4030401020340400103c43d0315140413036841c9030b1000c035080b04035041d4a840941510310b0610480303070100240030007030132102c0340500303403c0450310b1764 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 287550071 1250 287548821 287548841
    0x304020a1706070e0409110f0604080706031b050f04061202160503090310020c0c240301120302070906030201090b091201050117150417030c040e010308041508041106071401090501 79
    0x1481039151180e043c1703802c0c0154001076070300206001d03a2410003410b000b2a92100030105500500c10b12001c61041c034204a0702d03000709055a00031030003545014001e04645071541d8502c00b0000c0800010540c4840341081343d0840310a4078241c0d0140c02c08004000007405840c0ca504501041e81c1c00306828410004081c1120301d104409451406070860314090492083c80001c2c400c4d0380100201c2466840e003003501c074405403111550080d20407412a0140c1f20b40d8002d0700aa20001c021407035001c2890b0341000f0744005085104820443c0c94110740010309040c600b4803540380b50303100000b0400103e46407140c0311010600140000e00c515610340d4006001e80d0380624030400700744074100c0c01f2070039820341168490089810910840c42002030f81c1c2e00341d0040d8001001d03644e01c0c141c10440010f043c0080103299000703502601c903203170300c2d5030502100d80784c290317142c0a90303404202800041c8000303d01170b140c20380701d20b600c11078640d96111000c2c074050941000020b002c0d4803e501e44081c007801d03c541904591004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 287551321 1250 287550071 287550077
    0xc01051003050c0607110306101511030409020307030905100501181808070203150c091f2f03040b031501020703030c0809010e06070c030308010f030201050f0304020a170607 76
    0x80da1180c5050904942512000d80640d1200940030742600b000c13402400158000d0f00c141a11010b15004a0315005081d1202101ea203d46d4100f0081d03072448126051309074a981c030b0180c02510100004550b01d00a42c002c0c0a1030580c00000b04a0003401b0354088030032182d011040d50000826404050005c01092262241601d040951f48407401071620580491001650f007010b84110741e40c4620b551600491001c0b60548a0000b0711142c0c04c0300e80c155a0f1003280d020044c40c1d039072404101441180510850146c642d003130b5440781c408817990000407a02e06000720300380d00750300403810f500e60101400c0000d05426860100080100707505444000451050002d040c081c121507036020012a40d5041d5848040c1c0015188510000028003003001040503650526100151500440000349140d20030714089540300800070f07003041059040307284a4010010305500c0108103182d5000604603208100005103500c50020004003196601e1341c80101802d441600d10400d5a200d205031940d071340d0181d400c8804 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 287552571 1250 287551321 287551331
    0x50c040f0b010801030f0c050310020901030b010305011d04032006090106080708030a1404050a080a03020105091212040c080106180b060304030e040209040b043905070b09030c030f0c01 81
    0x1000d01240614103009070107a60340d0710240c0c41d5448070000320454100c200c800c5102110005074540d07080002c25500f00c95000c0040e03036460040300240c05c9514950805041c0341c1400300400882401c0090f8003514144242003400965540c0350817216400c0e0f183c00c900301e8bd014401c6402129600050040c4203501407402007004a03102c080c1166100300f00e21504081d5481007101180e09845402155003000081c00040d0405841d40b0005003100c401c0e070480603aa034040480b03101495824028960003072810800b600d02240400d41505c99842402c826a2090084002003030401244d81100002440b082c0000c02c5915284d5814001a404801807001c1080c104001d003003441c86c1840c01c40340a0b69054903000411030301c80080c44042d4000000c02d0364026a035a210b00515150741c015010421003200b800c04030141380b44c0401000440c070345024000008210b620545298100c0c0c102c0d03500c07075000615411543d0ba455092840e40c401d0804508850101142405443c24140040c1160001500003440703 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 287553821 1250 287552571 287552591
    0xf180b060904260c0a06022d0405011805121c0504080303010512010b102a0803070e1219150516050f1b0c0f1008041e020d050c04 57
    0x40c0300070584000e048496842100b04060383d420240380040319078550781d00c0c1092081040340e401c000440030b0660343d0a8000800b0905c50302d180380320b84404184502005619500440103501074000c0c2d0040c2030500c91182e41d030714510b48064121500a117001016080000c0640401d1074442d0411039503110b41d540104800c201650050065400346e0f05d1100046045a00e800104420b41c1505a03100505550381d0b0100c04060304e41083e0315640c400d00b910385d6800700c0100c1c041500c0500d040042090700d0100c140b407020009107940116600209070f0320b4456280452070380011200308104002c0d481500c5505030401c071580c4400e44124149000f100c1c41002c1c840c102842c07200b607400c1240c1c03100c8a03004400384448058001c0001d07080700d420480845041801e0324010541a10141548000f56442008112124039003c181c51404130704c1a07071000012a083c200140540c080500020b044200c50341145813149003001c0f00c40c0c4856001000b104c88110782c0d040164890a8241c44c06024a0410740c03100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 287555071 1250 287553821 287553829
    0x231c020c011524030e100506010e150702190f1518210602040f080705100302071a090c060a120e0303070221220602160f030f0201030f180b06 62
    0xc0450303c10400c010321101207610b140070104a222640c0090507501c0700e03004441d400030807013481c0e51851010000341c28100360002422707a0281145040c032500b0280484101d140c00d00d4140c1d110a503040d1000440d02d0300c402c3c0c0c03002104480c3d4003c2d603603850f4810800201c1f645d02c41c085079110880341e240d01c80141e1070b01c038512030b50801c02c2c0140510841c0c2c07800701d010020203e8a01d504254010710300141804e882d0444014001c6213035011010b651300404040c081450135500700c0040d88907e04046241010b10790b030701e19203100ca07030002c90ba51125460028142d01014810300065100060481e42c2d40c007032803180a0b1800340e4807103508030028603160215104a00020880f4081d01fa1070300113050f00c00c9041900501388041508124001034140b01d2031024100c00004109078484403082c0010041c2030000081c40c02086c030462640480d6070710020050054002203d4083d650000004031040c001400160050b000391210b98041500e00f03850142440780710013100c265035100321014110b82c3c541030200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 287556321 1250 287555071 287555111
    0x3151005090c09120a02030105150108011d060112090c17010507020a0b0606180901080604050f01050103020a0e0a02090a080601080136030c0f120e030d231c020c01 72
    0xb6410720004200000e103d16100d1066003003003407103030111000c0c1d08055002c242544c0d01a14903949210020403000c405681008506015010802030b00c04030200301e0140c0c000102000c0c5c61281844030320081462280015004001140c1d0019441d03000d0554079801402d48800d003920100d5254605004141514400b01c2c00c0c103d03807504003045090b90f032242c00030400c50350f000e49011802c90b19040c028414039129011414001c5c035440b000b40895280c1401c00030305050400e40d005059924180c01800180c0d124105a015101410550203160f074421800e00024400ca40759507034051700d41900084c0c80100020014180c41040000f40300002d0b40303c05014056082c4e01150381070751101a11101e00345d014946030103039030340a40340c030030085805a00c0d00e00a8401040c01610610448460404000e401c80581c8900820540081506001c0114001c16149c170396040340051060342c02442403a20810380554075030102140c505c1c050001c040100000035400100002215401e18142042c00100300c409 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 287557571 1250 287556321 287556331
    0x6080f060c0309010e011404052401090507091214070909150c09030b0a020301081b03030307030b030709020c030c1603050d030c0315060c110301051504090507050315100509 76
    0x141141d44a01d0303031180d00c80d04014001ca40d150350300c81c0e0041300c100b400d006a03055100c8921f5041c401d818203041407170410b01c1009050907102c040a181e252a0f030070fa126500e0450340142d90020b415191650102e0f804a042d03030110380040d0075140c0070000e22620540c0c4500e800c5140007160000c0e41e4600210043c1c0e440710380081c2000400e10800b40c00c00940750800582c0e80214036010400680740d82d03801140c40740503190140c660340d0110051266000800200d500d01000c0d602c41c3c0024002a00002d075a44402400070317041640303490521403251420000400030b441840810344d100c16072620441d581340c004c40d041b40c1c480e00c145c80c603100c1034002c0c50320b00005403038000000e004085440d070001e0b8094114030001908243c0d68402c40403242c40083c0d01d41001c0d180c50303561000090400e04215084d02d180e150a6071081c0d15080c20b2180f1003001100030190700340240c2d40800c2d000b48a00b095030400741d541e8059a014042c0500c3d8960b03017580d0005040c4140e50040c0c50564141d1a807051000700181151 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 287558821 1250 287557571 287557573
    0xf0908120f06100302091f080108010b0a03020f1e031c02010f0b0a120f060510030210020d090614040506070501060503070b0715020f0d0603060506010f0e370e070306080f 75
    0x800140601c02c5c0c00404ca2100003404000842c01c12440c91503201c1c0c1020b01000001e520382d0010302441c0401c1c0100c0080910840711841e086041d0380000c0d1070070b0208500c00c0e2141c480002038000b00c00e41c240300c1d41740c1c0c46402020780e541385400354404002003001c050030b6030040d46444440d01e099103452044402010018110100756030034611406121100b001003581c140c2c200d083c280c40010818010940f0030030300040405a0350b40b4510500440710031a554410543d08040310280881d82d01034955012651949401138803104010440b003040e01c00d5030005a008a400141c0f07d040c000150064030841e0403d030101c0c4c0380c050b940c03150385c0045c0c05001002001c014058280104005090f0040c0a01c0d0343d1340c0c0c4078107160a0415000e03904031a003075407003103e0954a54080000350b680102140c00c000741c40c0e09000c07801019480028519654090004611a4944001c50905040c0c00c1d40c09141c1c0e40720541d61684141c498007241d602d071201322803c000007400c01c1d00204031250003160700010664008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 287560071 1250 287558821 287558839
    0x1e04050c09040318030303091110271a0405030607020a0804031209230f0109050310020d0e0d020109170406020627070e0a0e011107060b01030f0908120f06 68
    0x94100321600502400540030072058130340c4040c80b020500802c0f8000d42c402e80f0009110000d500c1c010281c0890154524420f400070550009110b401c081c1c44069031030002c410780d15150550700303062400500c540111000c5500345a0742e40c440a5044020003e98404400319241d541e25007408036940c4000b00d000034601c16080c070003000050005104410094003900b003404485885d105542203072840c95400d201102580d659040050900100d480c4050100f8602000040d0604011964512030140240c1c00241d0008040c4d0720788030325502c134070040411b40059405403803614070700902902c580141918120014034001d580302c40c2003004c0314101d035804c1d0080c044699030740d28686011020703c2c0d00c0d42140d105d08010b6002888041c0503003006000c2c000500b09a0b42451795810085901310010804a40e140003621354412180e07800392030790140d1100002c80c5204a410048010700000303d202c0c803c150408007482c04108021000d41040600301415505956803001041c40e4144250390454000a81c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 287561321 1250 287560071 287560093
    0xc0109200f060f03070314071205010f050d0308090a1406010e01050301050709060804050a0203010606090f050607111005071502030f07090608130c0b1308070807030503030105040b031011031e0405 86
    0x20f04040c1d540080d03181400107080310b44110b036100204045481100040030f003000c0d140401982e01c80d160252030442c40071034006041c500402c02d003060303010340a41402045000540b00c2c0b4010000d0420540d4001003455007010b0b00b00190740c2d00c020138050302141c030506c5000032500c5e041c14480c941c800c0005945650117149003800660b02c02101030300564060082c0441400581c03024004c0310001e106640e200740c1d109250211703c0300d1120044d0041489107004000d80404500003651108410104403440f101031190002c06032400c0c0f240207070040420140780045440340c00142e01551250b07a480e0100b41351540c4000e001c4542c400309001d500041000c1c600404c5060700c0400e081d031400740c0b10741500060552a04218802500070a103854601406450b0038001000c05110300001130010000504c9a90f00310398032a40c5030300050042070b00540d515200400702d640c041141e80151a0903c60810840c69580309103903543d4000c803602c0c00071000000300100112034901d241e41c0300300d030840b000d400e8403010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 287562571 1250 287561321 287561347
    0x501120c12090212120901030b03030301031211031e120105330f070507031103030f04090c140705010c030e0c0d171b07090f0b030c150c0109200f06 65
    0x102070060f41c00100c81e4041301c050b08010070030805605440c00c03031191101d4074800010103855160102c1d500030703002800100001002d15458500040ba01d00b010440c0c030240306049481d500802c10040c2d1991b01b81c4e0b02e800200e00a0fa8020050440c00c041c94000a0b1303203030303010310100d0f04485441c8800940640c1804401049500d804c030601d000e150072003454104002c4100b0341c41d4201610584094010110400401410302203503601d4510079000745041039182080c1c03200e58000e074815040d2590311140b038030010381d10034140320031080718000c103080e200c01d90360a20300e008004074440f040102c0c0c03034000420700c13803240000d0101c08080010405861154190365008010010400b264682c22050180020301440c2040b85108200c025000b0702e00c0514041001003690a018005000e084ca40000760b442a100850411400303001076a000d1042d4140040100ca0f61042e010b4105855207440700c0e5404014903020784800768400c4203003440d40020070710200000c400d15107015540c0050100464000c80d14 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 287563821 1250 287562571 287562581
    0x160b1e0a020720210c0306130c14030a020d14060a290a08030a1101050c070c1e0902030109020a020111040503030405190902030f041e02060a0309080408010608070501120c12 76
    0x40b02822101803603040b407250034040740e00182c02e14000c0e001444805c803181020811240c0c46000315800064000c855260b01c82d0303606a5004000741000001c2614186440402001c25240e50203007188005010b80d0420021042090802e4a90350058038082042c4201c40d0141e8508401c040401c80d050740742c102120303400c1c0484844916080b4000710400161104244080c105100040d100c07101e0003410013030ad480c21100020710b6102e4800080c050303c070200d08920780e0401652070000c01c42c0c024610401303d014032000320b940078080007400080080b400225a0700580350782205500244070205141c005140e2902480c0a403c0e010380c414807041060789400f0480b80d294040448020800f1a203805079001660300894000c44100484000d200401124505a2550b80000c1003400b200704081e600107107062183c1001e00d0101a180c8442c401031140c00e008442c000e01d602002003002e10390b14040b05440d61010b1042c1c5000c12010f44001003080e50b107014121407a403c607038604d10b02098001c01c80c80100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 287565071 1250 287563821 287563883
    0xf0807050409020a0306050a030b040c0b0705030f070203010f05070339080705070812060a0914010605300117030f04050d08090915100e06030606160b1e0a0207 70
    0x5d5110500010b0586405214030090744c003e5410070458641401c01050009403540310301043d0104000540215001000780c41c2041d0500d00c5442e591042400041d014001e10348044006602e04402d12000a406074481c1280ca00f180c88200b14240042c043e0020908070840105d102d48150481c50410f14840c40d54903602c0279503402d08900300b182c107448800c0e90b81c0007000c4070369100740ba0005100c1c0603d00042c0103801800103c00c24027101c15030b24548600c07a0010b1056005006010445080d609102140b00c0d2020000d50304903e400041c02c800d400e680728080c41522109540940301c20080d803008812982c51217060104145000d00d488203004506081c0314007900d080c0c5007407003000495600c0465035030203a240003c401c40c0035400c18080084c18040d140c00d00080c880340052500c41501d4032001d817039014008407001d503214080d65800409007211080b0080c441081c002c20880c0d00380e22401d018504178089051110f241d5642c6400100724400c3c1e2001810805403440301403101030703500c40b40815807 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 287566321 1250 287565071 287565077
    0x3070c05040c0c050a030e01020601141c1e0803040215041a0a02010615030218030115030b0402060403050303070503041b050d0b04061d1e01020a051207020a0b160f0807050409020a 79
    0x180c200f6031a01814403406501c201c00084c10100c0d100031542e810800700b405010502c440803010100e0f280001c2003c81503006070200e610998040d1404e120f40740e072030400c820001d074a4244040300b00c1d10b0070069551049504038031464090034603400200401c41550103070380104845080c45011103818038859080941000219034942c400820362072030118502866000b45d480c05600c070103108214a80e8032480041c1180280e161860340c080a03514400303202d08681c0c00000f49080c0d42c8030340c00424030030303c16600080d0151000000340080d040d8050000c611035405107002d00c20b00e06d007541b14440d14460b10301c80c0035842005c1440e0307140801c1c066144240c00c03d21917007000a1810792180c1c0f000e03091002001c4c0300c8140e00035110351050002030029510040042c41c00840c41c201c1c0042c0302034894003440c1c1e10881d0f002c441a0000303a005008114582045802440010031480c0c1804800c41001d00c1c0105007000446c542014158240100a0346000340711a45480d800c01342055028802074128074814010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 287567571 1250 287566321 287566337
    0x501080c090604030c1511060a0e01090501050103030807080117030d1d01050903090a0611031b191b060314150a0308040b0a021e0a110109053003070c05040c 69
    0x9075642400800046129030415603485141c0401c030b1b141c64403400740690a200c20f45001110a00c4045080c5a01c240e08000003d004500020752a0040c046214010300c5986450f0000c028560421165803289455550314840c80c1c0e00e0728140814078211b03010380c2c1c54075031090200c0c820642d410340100d8980c10041c4104405604028038550a4900035a60701a00b50000642c0c00c0050601054041c041c25060600014481c50289600c4d0b40f07108241b4011003440c2c040c0c1a100006c803040c40599050111200000481a05d6040c5001114005544c0345c00c2000e20300e04c0021014060701490a40c10340c44040d1003155038a0030562010300d15000d82c0298403922208000c800145403a0291001d0079400080030307280e01c0754540c044d242807090328440000f103a0ba002c3c101c42c20540001c80c40781c42d641c0080c28235803404181e00162000c0d04144c00066010b080c055660520780503082c2c0d503415080003004506442d64944c0c801a403684162140642a80c01c000720621960509801904407001c0614065503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 287568821 1250 287567571 287567587
    0xd03050604110a110105060d020d0b0405150f06010f0306120609170c010f05072109030509130213090b01050702040b0303040306180501060602070e0412110d090515030903040501080c 80
    0xa803540000f941501045404100d42e800c0d034424440c0c180c0c800c80036240550b0300840358000070001505458001c003852a041d000508002c403d10013400c00f806c0d90b510034201c40c20103e40205082c0700441c0e0180c00070711801c0d10700c4100f030311034000c0500325560068204a22a0980c43d0800600341d0040305442110003a8540f80c019044900281601d2400e130300001514403540466078142c3c2c030050184010000300d4603e0400c81040d029900e14813407044503002800c3c210340d00d000d40f84c9019442c0304540c010305a00e940c800c04400c90300100600001007403100f11098030380362400b0440780103610040c0003c005106000c0181003580c010304202034000c040b40d0503c1da8a0340c40c0701c10790308540b00969070120700d0791750401000024006c00014000c58005005014201600082c110400802c050101d0141c50200d401301d5024403e1500715814a0082c0c88172182201009090803006111340ba00820100226403802500751058a00034130b502e00c06145401d15001c011103409101818103141c804040208003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 287570071 1250 287568821 287568851
    0x315060d0606090503010b0a060c050715050c1c050d0c05070c380a05211618030507050d02010203120405060a2427060b12180d03050604 60
    0x410109039620380400c800c0e06102e00182850002d90102c0d02a0381046202141941e4048050065034118501400000424102a071030814070b41d1258410f1154500b800740141d5204004007900013101d4200e030b19000059221018070401c170560030002500c00d102500c00d030300b41a000f0b500803910911744142402c600361181980200f103a848408110001902d03096040c02160a045140d6104d01000300000c0340c1481c2e010356441102941c1c1e00300000000c055011700c2003c0384c043c102103007070010054a8600104c40503035491051440c517000c0341c010740710411494810444002606d92042c042c114481c50181032180002030110200c0c150301013802800740b0780000700d0600d44114003450041080b42030200c1d52004035402c1d03a41c0307000681201005055001c0d40032030400110b0310044540c952480c81348142c421a080740c408540e241600b44140040d0801122000c0c10340c3c030005125203042350321020300e00540c049200a0f62031441d0084410784c2c84550081d44125400316000c0d10100d0543c844900c40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 287571321 1250 287570071 287570077
    0x70e07020f07092703020a06021c0218010e3f030708041805131104020d020c030d1103090a0605070c080c15010906080a0803060414010e0405240c031506 67
    0x11100316076650300080080402d0b0107030904120020200c803c03240d40300c5e480c02503d5400c1984080c000c00c2e00084c043c1d1005903000006012307054102400c544600b202031031041c1404504940328000fa0a80b003136407600340340076a18959542421100e0720032034043c02040340074034140810034541146842c00d0448108806000a2015503c56aa1150741c0c50510034220200000390302c00c48492440c003c01c1200d5406c051a001c00d00035005602d0b045400340d0100000c01920400480503219400032640c008204000400303051101038148040c0400d05039000102c1c41400121520344642d03008a4000700400d440d544030300c1d00a0201e1401ca0911043c83d16004400d51203880c5c515901d03032020130f0000c1014900803460f409071501c5101400707190300c1d0105040d41d03403503e55009403d0308000000b0079000d5480f940550003000c07502e050002030f580d6030f00d100c5c520b8400850b07041e0380d076011f528080c8038a414810f901d80d546041004a01a00d0f48038003100a0040e04014841c100700d0800e071a000140750780340005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 287572571 1250 287571321 287571329
    0x13030c0e0a0507140d060b1602090903030c07020112140c0301140a060f1202090d1a0c0307020a141006170f0102090d0201031e0c02070323070e07020f07 67
    0x464042a490440d5801052100a080d001c10303520344001d0040c0a070780503040e04403030005480c64a4940d62400c0004008040c50f80c03089207480b03000900050801101a007421240b03000700d610902036503541034003684a200840302c2c0380c150042000351000541c003500f51003054184020300000c3c103960103c403000e840d81c401e648800c15500b010004015902d140d000740800d10a084d1155002c017072070084045c2c070171084030f5980b100317001c0b91304041c03600d030303c0da50341507403402500104078202c00e00c0f19040c55928125081d0002414034070010000f410b1002040072280142c0c0e0560081503007040c40c0c0c03500448403c100d40404114040e1031044007040031103000e428003070072485482d5141d800028600314501083d00c50000d060340d005105108039551840c1030101303841c1c0c082c2000b15034214000000001d0212605841c08100d00c0c00c210040305a900198400036284a0385800491444500d1110751444450240380c0103603100b00000e12015541a882a401000340c2c01151110200d42c0d86c0c103428800c003500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 287573821 1250 287572571 287572583
    0x1052202030c0d061401021011090303031006030c180b1e071a010614180a03141b0114090d02040b030f0f0c0108100e130b04050a0303050a02210901021303 68
    0x100343e002610140300304801401314006100c40c40d062440041c0d00c92a0300e489640032142c0d0780708c3c1a80e14210101c00c491841a005064130350368a89a480700c00801c180c0e00410b4002450300307501d200d8150044425600c024100414444030500e002c00044442d40003a480901d0302080c91100d100d0001c080000c1c04515101c0d411503142114142800a460a0305a0010081080c0768512400914400040340c41d03401c0080ca240782c01100ca0408160920300c2c039400180860038618940c0d081080c0031801c0b04029280b45648100000d800c4011203241050300c600c002c0340f0700304004a40043c9030209201088070b2001e8008141120b501c0300180c1011640f4a01400640000644181021080c0041b1000c9603003401c001c05a1700b800400c1d080c50445a0103250b1301ca8a14a012030850200d11420b21080b0f82e00c00d1642c9175518184c6440c580391001d142080300071030f041c00c0102e0f850b45e5480c001e8408415281140112001c5800f03d2100f41c0c0e00e015009101e555800c208440e444c15000403410040d6000d40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 287575071 1250 287573821 287573827
    0xb04020715020d0b102f0a050303150103091509020d0b0118060b070305070209091204061d030c0906010f0e030303040f0512120403050901021c1115010e01052202030c 73
    0x1800b008165001c0813a00d600c07400401804103040703500022103100312110300c0b4400c00307441b601c03181d007540400c92081280664401d2080c100304015001004610940804800d040400361100054083c0c400130580108034043c0d0010b215042c40055028403a076138002805043c02c0d10954aa80001010a0704040f400c03281c03192031401c40d000c01d809008010031842082500d072a100c1d8600829030f009041000b8410b0303000030041610341c0020000154100900300d007003552140d80b03403006030060044012203407810380c1e4040b004000e0316000c20022843c24000d0429082c41d640c010044800444011003039051002d02d002150031600c081001d0751003a8854111035442a0740390411515000d100d140d500071261080003000c080f0a003000c83e003138015500d0304280d0748030707000c020050742004005044040307080100c0c0f0304103106d00d92201c403603040505040b055440c030a0786250165070b061424020b144e14095801c0042004c0c0c2001a404405c1c200580c007000501d0448001c01c04c184e80c42602d61340f420310804 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 287576321 1250 287575071 287575087
    0x80a140a06150e13020c030708030709030b090606150d060b19080c0c0705010509041803080114100914010207050603191401060e0d0201031b0c051203190b0402071502 73
    0x403180401d10b800321410028064603441d8002410543c00e041a100c10a40101d09811104010002c2e04c0d03d05901501250f180d24020000400e503407c584019118009001c01203203001a01103000c0d0700508001c0d04485808094200c45805035100d01150944140d0700d0b080040c5d0300142c0c0b00500610952010b900081210034503008082480c080c0c00320400e500200007541099800241d114112403081c02c00130f441c0c00c07107603000600034000a0300020408199010050400d54007842e40d6041c2e5507199000c00c00c2c60b40e490b05001000c1c498403070440100f00e10100034040141503882050f400c813814411903403003a88400105040b0740050300c1e04611f443d01d4844c1e00343c1c404081d0203155809500d2a44407003d640c500f2a00030b101025548c03410303020700003491008066910a820202d50031103070b40100040c408201c1c50060800e074483d03209a8084c062840d686440000d0b100c100d1f40030f61104111a05044c40c1401610010106056419409039081152034001003a1040003a802c407107400340140c5507202c1c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 287577571 1250 287576321 287576339
    0x403141b010608061314010b0d1a0c0901020c0d020d021f0e06070308130c08030301080f060603010207050a02090a09050610090e0a0321090819091508040201080a140a06 74
    0x10541040303e058004074200b00121803100032000c2da1035000075520442004880d602ca0040200d9041d05401002e4401024188804200085820910204c18031210b684509252156024014083d401600481c0100f801c51400702000e0120703600040c0040855006540000d407050702040e0b12042503a40b400b4691a000d4204021048060050316401c7c6840902e54004180050060548020540700e5250344103002d031030a1013801610b00c0404403030740c3e540c40b680b02d00e40d100c1d440c50110005114020000c2c01074101030081e5240a0351100c0100040c5010750700b0442090b100820701101550340315030200105000300400c9000b81c001100001600307040041b5030080d030302104140d443c507078440341207680001e034050800656003c00d0040402c41e48070580940d4058801660301030080b40010404041c102c000c041050a01141a15144007507681e03042c080317080004013007620011030f0301d00c00010095406280c015520216007600095003480d15003507650742d04000e46003c3c0445a880b2000e20404035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 287578821 1250 287577571 287577581
    0x11061519050109090c052106210a020d05031c1a0103091205030a110706021803071d06060c011a09010f140607031103270f0d0b0403141b01 61
    0x8840e8400c200c0440c24a03001030240a498450520300558404a510713060b07104005a428034100b003490301182c0f4600d107170014841d803c280d50040c81800d4145942c021250080307101601d1203c08001f508080c50140c0030010883c1c181c0c2400e54060008001c82ca444400e1500c101707510180c5004002008070100f00b102c64484c4c1d000c140503060506c0d14402070081412501c2c0d100d880c4c6500d19080744d40759541c20818026200303800c03503484503441c04101441049400d8000d041804561500394005412500070103075995990710490300449072002c40074074604507540007190f0107440503104a00d001c42d001784060841d44a9030030302d50540c00100c1d580e0554a440307101c0b41c1c010a0082c2d5020041c40c10005c40b0080c0b0030000300928406c5000180302e008050056600a2015000d003040d6902c40c101d205a01c000e05203483c5424800119582c6590b40e5858142d400905407500a004c0d190310f04000e80d280120510086c1c416001e0090700c100040c1106129002444000384cad4001e60b190141401c100780382518 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 287580071 1250 287578821 287578849
    0x28050615030a0609110d0804050f04110f030604090c080a1a1006050309070305030a08090c01020111090d020f040204060c03030501230d1e0303060312092301110615 72
    0x20051a400e1552035a001807100181508520005200e125030318086404e22480c03c0d50640001492102100b80115a40500704440d8251080c20320f8070150004c210071140e4507200450b040b10300b8400c0d02101c400d03440c09142c2c00303c006000000c0f080125124240c4131074040e440604150f1251181c40d0802c030100341824069241c50341d50360024105034803c41c211102070f00908040000200000c0da4140040000c44001c0d5000740989541d0001100000c050b03590440d0300303100c58130860b000ca1015500c14820584451100c00c0814102103a11302040304855000c0c7d41aa401010150384028940d990700c01000285890384464040ca040c6180103800d6580580c071100c83d4000d4200352000c1c1040456850003c80c90803101b00150407080c1c501210042e00a402c421511407003088240301305501070740702a09480c0503c4100d402a44245004c48a40c0645e000305402c4038540c0d40301010ba038034503500070b40c0340c1c1c01c05040003010101c0700000da0f0b16149007222444082c0c0b544041ca9210b5040020800c8865 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 287581321 1250 287580071 287580091
    0x1506040c03060f1403010906090506091207030f0e0f03070603024512060c041a090a050112020909130c080607020c0603070318061506020f0a080903280506 68
    0x1030f0b103041a805201d0040348508040e2103c050342d00116a079080d40a086002d501400402120742e031400d007665035010032541c949080c0704180d025001e054124059070007043c0c2c15a074049801c0075141003294960144109250000c82a00d0410030780e6505202c00e00140100e40c1c0c00584034066074078400c140e40c0c0b4049620b6040301ea1525010f00015408029411000d9801e52070340d922851030001c0b81040140c074280380524024101030140810f1104010300c12581c0c2c03245004030540c541d03a100300c030b00d01c920128503a101120140400480d405407680c8046216080c03401414144900e000c81c01c1040d08541003000b940300030b8031080401ca0b5181c0c4000c017412804d002001c0e41d1a0940c1c0103503071408010056480b5500100004002a200f9000b14040e07000da90441039803010240360600103800c0c05118030341c400001310170120b0101e2002507001540c6850a0081c2001221503d50b41c075030741d100c1e1a009805009404000048500c0003400c1c5114060a01d210704004c01c560030102e0030603030041c0c0f01e1210 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 287582571 1250 287581321 287581331
    0x11809020714190f021e0a0e060117060904030c0305040918050106080114010303032f0a030f0b06040504021e13030302010c0e01090e250302040f08060408040b16051506040c03 77
    0x8204c1034862000900d9041d00c0b50340c00f914049603a010321610221a5a0b0700842e02c84000c07e00c6084405560b000303850a803103a8840e1070010384841c406035011507030190004100e40004000ca44600710306050107000b410300503e001e031034403180401c0d99441d194030300814084071019800c03c4024402c2c20010070719100204403a1429a0107002e00034010f02c03015082649034540820945004103801d07590140c0e04510f0b800c0d40340c24034451040c2c5d4100b0200c400201e450101e00161501390741c0100e42c001352001b0401443c043c20203040000035041100c003c15507a2444224400400182c0010034003550360000c1407102034a0351030b0082c01d490003c00484200820105003c144c0d0760042c0c801070950f03c013446040c2030f6582d14800752240389800340742c051110030240c954051a0740c0690040c01655503211040300300035103d584040e501c200c2610024240c05e0708000c1040f0002001c0301074402014407103450317030344860f49850f01440e05401d180c05070700f104025800e1026034981171054090510b101c3c01c040c01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 287583821 1250 287582571 287582573
    0xd05030406050703020c03010f1406030a0c150302070b09060610110606010516020d1506080625021509010c030606020f0c04020a02010906020d020421050c01180902071419 75
    0x9140d0049104420078000045050000c0500a12446092860140c02040a0211a07966002400402d100c0072040620708010070014103021804144694100c000200707994503050803081c100000301500707000c1580c00e00c1107800048420340054004c4070148001c008a05050f020801104040250b042c20320544085105d41400081450f9520200c02d00304036031103048018030b802000384408be0013540300032400202c0040003001020f504600c0c281d018200240b030b0b190580241e880c1015030342d8141c61450759000140d400045000311201c1511803040c0c40880070b540a8140c0083c02c1a5000c0f035042e51a6000c5488040c1d051081800030525440140034220744080f041d03440f942560110b501403a00051b40380d017818000d42140021941c065011543c5000201ca01d070000e40141c040c105842c002c07004000c101c0e07a1040f02c2d11800d2504030001d007070791568010043d40ca048a0b5241c40c00041c4000c100040c0b09030b102d101802c2d40f203008180b003058032007007100e1090400c101203030485925885200c0040c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 287585071 1250 287583821 287583823
    0x10e010801030f15020409021b070f050105070f050102090607142119020f03070f0b0c04030b0c0a0306050907030b0a060908030a1b0507080a151e0506010c200f0d05 72
    0x4020b513810040c11100d1a1042c81884003078400d6410042141d400022214810348284008200030000070003620f0800d034440c46401c0c12000d091054500142c3c2c24804c1c0c50115013880300c04444030380704000061a111010307000c2040c07604030103c15907a01c1054402034100d00750a100382103d2403584080400f05046185094400340076040a480281c624910f4401c0303903500070001040d40300c000100b22034840c0020301d400010364110f01c1088030800324010100b40b100640a0549080e294841100d408035a52607203c0c0c407464100c10703007100400d5220080056a030702d504405030300444091b03401040c541d0b081001e0006400b0990f100c10208406850204008000482980c203000f0b1b882c9068940a000041c0c0d44c46034005e803c501034001e02510340300080391807000410541182c4a4042c0d044168060901441100d81c0081200c030022540c8140e05c50910b090383c01140d100c00c1c141040c02d00e061054850b0406d01007141c210000d0480c5001c0e8840300e901e080380c1e16216407101180c4030043c1d001540d441c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 287586321 1250 287585071 287585093
    0xf030b060712110f16030c15021c050702041508160b16021906020a0c0b0a0504090c2606010201181a091e010609050c0a0e010810080a11010e01080103 66
    0x8080041484160b10180030a006802d400090107040b160340300300c54205c0311000080382c4000c036014050b000f4009000f94881045000140301a0050304510350290311803002c850b006000001000030801c05000140d840784182c1c0d8207000350580b101461410220001c2c50722040300c0d107150607040800030030401015000116540e0001120713610a5500c040d10114a006111503040022107000410214a0f80e500182c0110154081d62491407c107955140d000300341e100300104540003540411041c8007040694101b001c00c4041d510f0544024100842950004400903801144c1c81203048140401503070309004241c1503480c18411010043d4042c0d076130305201c640203a10108100c0e05400042e82c200b0050003100700c1c0345242a43d02140780361013682c0900074400d03030160f0101c041c508000b0a080801140a0300d0b1612000c5d25102c4c1d181200d03400556017244020080d007440e1003001c81c00300e6000020700c0700c0031a05100b07107900d02c4c0c402106030000d080080180c00303460401080703000402c081514a050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 287587571 1250 287586321 287586353
    0xe0a0b03091e010e01020403060b010e0a080712080d02031003062909060103061a04030c14030a031119050715051606020c0a0b040308090606030d1409060408010603030f030b0607 78
    0xc600d40c02c0c400c94071140e0140420030044c1d0380c01c2d440818000280699900000c48403142640e0b41d0380c1d004204010058445428080d40304140c3c0b2000b8180100c0c28640300060081d4000d208050408080c02c0c4803005a900c100d8454183d8420740d1310400c200072840c0940c0054401221084c216800302c2c002c44e0800c0c0c410b01001c903100c0e01048022132507a034002d5120202400d81d440c00c01150017001920303006035a200b40b0003205c1d008042c2100150600013600403019240008000e04001800d030b8a0446200662440404260160740040c500f08800d800f0720750740d01032080018055191402e0040c24850010000310003d1000421000344070050900720074449540c0000e005807285141648035280c6000c0500003001c1c070307204500740014036400034000da02c40da900c04103c0312550386180502d40c980b140e100c5000046052031002a40000c100c0c8082c1c41650700c0038000a080c0703a5180c035440e081d070b400d82e80103078041142d0007102c1c2911541800341c3d04000c8401c0c2ca1551070b115050380c4824018082e036032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 287588821 1250 287587571 287587603
    0x1a0a1d0d1b030629040504030507030c061401120b0114061204030504030b010b030a0e2802010c0203010203012d030308040807020d17030a0f06080d0f02070905070e0a0b0309 76
    0x118540303440c4429201c0079680060041010b0340000b0103c403614110200c000d0400070202921101a140034080c0510440c0e166940605001c1e4503501900e60741207441c0101d8895854070346e50b0565118010000e4006c1101c4181000303140c3c8142070406043c807068014000700c1d404081d18103410745421046070441c00040090b41c000390380d00c0c03d0031540c50040b6013006008158050000840110120103140505900300c0c04004401041d80140d994481c42010015640c00c0d1102e040b180003000750307644072458018100740340703040c1311035001030308a03030098000d801c0c01c0d942c00000d11001242100c011610101107094140c0b29410740e10041d25400d40200024400880080d00c2411520b981070242209603119121111900c0000714001031034004640361200c844c68199113020102035400b0b00001c640102c0081c040c569007442045650807501c150708400d6114010780000c09100900c280f0344110704d02c0c1d0b508005090314400300541920340c0e50080e0300013001401409030034240400d80c48101c410340c00e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 287589928 1107 287588821 287588843
    0x50a0e012307090f09090c1e030204020a020f0f01090302010506060a140a0519020d02011107020a03020d061508010606140408031603180810140f011a041a0a1d0d 71
    0x148010080c101c0142302040942011390040a0f000c100744155512800301ea01503c0c60480646003001c526951080701906042c0e0a02c40d0a41181017103030014945400124010814611303a601845200c0c00052841411800703a801c031030403031840c45000042c070700300c0f040040c3d228048102c580b4099402c1a00390301c400384500e0212002198002d1205a5013070558003809060f94031400d0888030965110740c0071121f41d5580c0f5201005044150002c1903041c02c0400c0200003030294250880c80350301c103000a029050f4080141c540d26240c8540c1400c914507075040840d501900015881e21340c203100903011500000204a920301026503040031310040791060040084144202e52040c0105c0700d410041c800001c042c0c1401d00781d0155804000d081a85420100162115054554a641c440081c005000d0758002c94148424000c1c2c88001c1c3c0314503181e101203211510311090003040c60540e1 = true := by decide +kernel

theorem cover : BRFrame.Cov 287410071 287589928 := by
  have h0 := BRFrame.cov_init 287410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 287410071 ≤ n) (h2 : n < 287589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
