-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4895
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:05:05.112534+00:00
-- url     : https://prove2.me/submissions/fb9a5860-b4a2-4e74-a718-3a901a89570f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 880215827 ≤ n < 880395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 880217077 1250 880215827 880215857
    0x1c09060b06041e230103020c070b12041106030105010f0c330506040515150405220516120c09080d020a030f0504030f020630070f0903021e0604030c06050703 69
    0x4540141070313040e500024401e041c0700150080d45c0304411030b0403540b19203038000522000c260090084c0800182c480041e50400d810008030225041c411148910002c0004000d00c1e80c01078240c4800320303564200081506298149208008580d9403c017180701c0c12038400c3d030301101e1114040d0700702c421414800c00450312202d0501c000c5510454000203904841665102103140586165410360f00c40c65049280a44071800304130030700d034038910f00208032604d4000324a501001c0d01a5035482402c0450007956120766030310082c103048c1040c20038102581c1d201c0400360b2841c8074182c0840613281241c12618400d41c400002581e406a0860030307000030744403c0544126038070800450302100d82240390041002503c3d001c0251541c4001d1403c0740103100307074484500c000080d80328042001c1198015030510b2400c4a006040c82c01754140d4601041000d000500043e581c04054009140701501ea0320012984880441d03240d200c0e0780c101034421104058001213080c3d000c00105102d0340b03c0da0790007a005d60009 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 880218327 1250 880217077 880217099
    0x108070e041a1c023a0b07030b01170412020c060f040602060f0408180f0301050f010f0501050c030414030a0b0c0403150507050304140115060801050909031c09060b06041e 75
    0xc000c0d0b118060100300342e5107000c1520319510b811076101e0300d030b1512094505c3c1022803034281c080880e90460040b041146003a058800c800c0d006200b82000c034048c1140e0f0383c902c2100300b0010300080403100341c040e11a80540c0b00b000003542d820005040b10359500380c10b0700c0d588200c2d04588111401446140b0000c3d07840c00c04403081a000d07a40c40001c42e400d103441e030000c2e801054901a8480c1d0000b0302c40704c100d0160f54007405081c1c0160340040c49011a941800340680c01c04034a41c10081c1844020464125035040020464040760502c5404d9241070414200290a2822410020b88001071650074442500d8000d40200112841202d03803000300d40c1c2500200d800c2d100c044801d940444c00c203100140c007050320100803218186c03550000195584840e0044502d0051702d802200018803142c005001e503062428066401c25495401542000c3c0346503011841007582051400c0486e40311059002080186c0e003050100042c018141070700c0c1c0307448070041850903950501a01b40b4088403c000a2164211 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 880219577 1250 880218327 880218379
    0xb0a0608010e06010f0f0e0d081902060a15170c030106060504140a1503020a0905060c070501020f030702030a0f0302010e030d0902031e0303130f0c06020f1e030301050108070e041a 79
    0x56114070014a03c505011f5a03900b15150a00e40c11040c03902e0034200003a0058000d0145441000304443d90700404580280782c558001e10040149180c18002211403100b42d102208403890386044051130b082040d145403c0c1020350441a815608145c00881d4658008010b04190765050100000e80c451480800489500a1140b401035058102140036002d210303030001e040810460a0007100300744d07242c000c15034035846405801c134503404c4050240410b40c0e05011503043c16411400560620b020390300007907111081e800300200040145010782d01054002c0d00001510024003040d0b84e112111044100003800800d0022071080c003541840f904030b0011048448600d0324650019070442e590b030305906426241c280001d13031700c00704070030020800a03d820040130007901080c0d02034481007080d40c404620301110300800803000d402110010800000005c1a81e0442d503091810000c41e1701c58450075104031107038508494001d03051510f9a10451183c20f08908030344001e03103402e1a50410545081080964 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 880220827 1250 880219577 880219607
    0x180903110c01141b070f0f0b0711010c020102160f0303111f020a230d060f06051e04030615080607110c060f091e03011802060a0804060b0a0608010e0601 67
    0x1024190360740e41240303003004d400c1900380c0100b050040003400b0542803420485611480c2001041e210600aa2140101540081c00a13410050404030143e90302c03246114215072660412000c40301e51000d6a00c20800e00c94000b218049281045848a600005444403400103801190150100307461040f000240210070018030b50300d41c51914220a00c445c06540304c1c81c040720810021301d0348403900000c001840d10030400c0c560070180c1c1c1c52240c80d06100584410b544180d0915080207002c20001c0d40010485e031f0707450386007643c400c1c41d092070300d0140141c2d01507900064095072502da08400b020a00251000951745a54100c0304a42c0d00c0741011100c400718507848030525001400e003403c0c81d007440c80c040c02104110b4460745080685040200c3c1490707c48907a0032604029000e4491303010b0070288101c40703410340468051807440718541c022886034403030109070204200801000506000040c1d0001000f008010840f58100e650f5481c0145456003e00508554084a80c0412442d41c000c0560b6030407d04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 880222077 1250 880220827 880220837
    0xc050c0d080709090c1d011110180609080d0b10020d050d14280606080118060e090c010207050904020d0f030504180e06090c01140c07180903110c01 65
    0x610358225900280604042c1c184410703460007141c01142c45c064000c4103812a43c0e03d8500702c00700c4600c07421484001d207440f81404901411600010008100d40c0c0d0581c01030b100109440018103041500464032000c0079140700d10b4a50303e8800c000e079180c002e04241c11808401d028802c440410401c10030385c410300c41d60141e40f000c01d600e140c49026201500000c0030b8940300048002c401101580c0010040b5030b0880b201c400c1340c401c0f4090614441890481d0b039007000f010040c950500d007004e00202010700401000543c4a5040c20034010503801c080c1c044c20642d40711142c2c0e0304003a8030183d5203103040c5080d14054000c114020881c0d0401408082c42290000d1078401a02116265003d03400f000f41800d0b000c00a0400001c0380419440f81580c600d81000c44000800789c1440d10158280b01c005072903050240c01010100380c0700c0ea40640100e0700003004041065403240c462421901d803043c99400090079099100034048803181c07941c07083d1000d502903185d00c111406e07901e08041c1c484403040d9009000c18 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 880223327 1250 880222077 880222093
    0x8060a0608030901121508010506120708060615070507060905131e090f06110432011110050a020405090708070c030525060f11040609030204051003080408100c050c 72
    0x4d88100c440e100582e1100c94006011101031850390031340165070304291801da464a06110080c24101d01ea0304000c0450000b5001e80f07030815070204d0f12000044c020503c160b02354000c4440980e0f11004684860f507000b0111000036039a250b002e00100c03110300c00c280c070401a1070080c6541c1d40060056030700c030718055500c084406003600c81c00c07801460780050540c3c070030309100c80281c00203542c0c4c4260754070101600b040c3d58455140c040001c00c10583c0c51240c400e540303000441020314400c07050451500580074240400801007c0c40050f10b00751880d100d550f01a8107000501a0955a0760b00500580e00117480c49403981d030f6100ea0503144200199100f1000801c20050b0002117031055002d403900003a0ba030011040340307040201c8032085420460b401c0d00d2103592400100c1c5507880910500605a90b500941800c26144c0765001e003000865102c0640a2070701c903400100350000034a610409550302243c4c40f9140d64030382c0d80d403590710032101001112440c908000341e000c2600038001e89880c01c0d000c4004040907 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 880224577 1250 880223327 880223329
    0x10b030c1c060b06162108040f061e02030402150c030409021815090906101b110a180b040b09010302060c070317211e0c0405130608060a06080309 64
    0x10000780700c00ea40030360340c07200748640543d5884020728840d00d00f2200002040307000d0410000c2c0c1a40043d840c00d480e9035803a4032048036a00400d50039802500300012080005d070504091014200b843d000301c41c480700c044000084090313580d003d14004c034000d4035060a458641c4c6118246e41c450464461080c1d03005000c20021102c40d600201703030191600c5040100540d08001044801c0301c00700502c600104007180083d900c0c01e04460302c1e40d00133011a400c1090700c05c41200034148840220021000c07240e86000c3c18180440c00c0d078000c100e0b00b00500251216580e0760351403582c0c8580c419406010a0519103000d25501c0c20740a081d41d07070319004180c0821640307194204240c5a0181090f03d40d18004d03064008007003041c58901c4500d05110b4442d00d139580a42c1101140f001c1101e0102c2410040d1400034800345810405c056039905440c5001080c66440710740a0341001d029551000c1e501c0704181401701c1000d025608403208460b003e0084407840d40310183c0c01c0080da10701e4042c2d00c4841c0c1c41030100d9445 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 880225827 1250 880224577 880224619
    0x60e1605182403150a0e0114060d11030616120501080607030b0d052d011103040807051219030f020313020405060402160c0509010e0408160317090c0102010b030c 71
    0x407200604180d611500c0e502404a0704104070513141c1160680b11000300100c04105000d404200d8540c44001c0003881118024aa01c0380b0300500140e0181d0005001c0400700100040040b040e244000d045900d1072a050109054030001c0098800026144c0d49481c4407003201801158145c0d44440301401050b91092021001083d240e060b8030390210005c242000458000e00402c0300d07203e089114003503403260941e4100c0810707036112040f11301a81360511402020300290141d0b504180d0003045603690b00080e0070b095241211940d500c507000840040d1121401d10210050071a900e001e40f41802203100352202d00b0100e0104039154078101070303102c0007080145000e0b880079500034402000141031481e914102260100303130381c81c100c445200c0e406050296192801c0942c3c0100180801000f29240554400546002c1d1513180c0c3c6034600d18000380010940600c030101c2190203801d000050034034000b140c4542d90103200944038059468032001c600c0b82d00303011680c200c11100240400e00b0000601d148120 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 880227077 1250 880225827 880225861
    0x51c0315060e300d02010c0903081209010603020a0605090a0f15080703060909060608070e041a06010905060708120c270d0501020a081605070b04030c03020a060e160518 74
    0x40443c0300003003811a43c41d50f103a10103241d0200ba078000c04401d03c04250103421942042a00400d0041100d02080050401c10446080c0da09019136205175403110f00042c0c1c0505019000258802c041d1784002c204d80b0350080290a916908036501030b6041d954034214812040f19019841e51500c2e00da0544601500411081380c100c2c14a143c0000c0d030035501c0e07030840308440c111407049851a0f1541310421444404205100117000940a1541541400e6540c54181120380e284601c00318800d10000d4856802000c022005100282545541c0c2c4200e1a00e41015448100b8480440c603000d804180c1105040e801c3d24840040314170310441d0600554510074584100342c805aa0144440768020300054081c005482d2500711358075200414100f0f507221390709503042c00b00d48400b00030060201002180b10281a10741194146c01c00c0c0c00d801e111818101e062001905007d0049070600046054032080013402c0d041100c00400c44c007007580d03180d80800c603204081c41040c03020340b43c40f480813031104c00350300451070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 880228327 1250 880227077 880227109
    0xf040b040816140703030210020c031603030e1006180e0c120106210c080c01050a0302030703140103050601050114031006200607050414040b18060d051c0315060e 71
    0x100c1c0a680e1200c000f0109014800030310340101004008041e01004902810350407100194180503400540710360f01c0c0103031101c41c48040c00000f40b030b03403d00d030081c0c0c801e50030710001e60291020440780113440d00140009201c5d10a446c2881100142e049005210700c0c0c54503140311002d85104030190082041c50b030b00c2208c001c00070b95600c41000421032104080c0342e50241c1000c000102502d101d003854943d6201da94050784842c1c1001c000b8075010303039009040340d00c00300080c107005031030342c4540c54120300404050b6085280c24100e00d00110038008005203941c1207030401d0780d41080c04c0204424081d158001950b48802d00c40c41100c0c18410039000d903060841402c0c0d400300c0303a180b0040c40040c1030314200c000d90300701c0c2c0070882c000b500340b08040303d0a0034094814001e450500070f040f40d550200d10250300741c0c07000101d04541c0c24042801d540d0361086920300c05801000301d41c664001142030040c81d40003400b034100424644080c05652501240c2040e00302c0d2403603128040107200e000240602c0291142c0780c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 880229577 1250 880228327 880228357
    0x10903082a1c05091203280c15200a120b010201060501170a020c030a05030601091205060a15081005060423130503120a0504030e03061005010c1a0f0703050f040b0408 73
    0x1e14203400b00094101003c034044822140070007d90a480307200b4601020b00e041000900f0b02001040103082c0d400c041c454226400074800c0b944000000c1c3c2d00d06900c0e008045480c0005000d540c503903200b0002140d80d091030804009031181040164222502c6c0c1c4106400b140050a07441c6071103102c001e08590185030400d0143c60100c22a03413080c01d5a0100e841100443c07408424860300317581c00080c10018110f1201a0b5070885000c2d11103642c3c0720001003005e48503d0720303514081014400315070184024008282106d445904450020000c2c050440303045002d00e01d08980d070380d803200060710340114a90b0310000344105916800000e01294407003201c141e60502c41041590340c0400d00816051054600c144000b0350b505184c45c00a21118070314551394481d51020040c1302c0b55030708601100c012a002400d0461004040e4a41420708496a2100c009100070750801c0140c046d6800884d103200f0310700b0790f42c200020381d6040e000c50110041603602604174440c0800150024000c00c00516094541e0445 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 880230827 1250 880229577 880229599
    0x152406130f140d1106070f0b091b0a030c03080309011e0f0e0a23070b0c1e010e0706030506010c05120d0c0e090411010903082a1c0509 59
    0x210380c00d500000d5000e242100c81e0041e04028054042400310710180085803a030010ba02142c645405904c2e900b50010320485000441404104d006004580c107540c2c41201c0a80c589000011162a07070727030b45d0714100c5821010030705030b90003071034800321031000c0c0c0b036002c00079000c4981151900d06981c1c200410000300c5650300c0c8060412110010402000a4480b031000f01724000c0c0b070303202d03641951700e080d0b080c0542e44e00500403000001c2d14a803e01e0030010369014240302802c1c00d002094989002a840040c015800203140111081d02099a121041907040b0220a610441ca0300e203003290100443d0055540040c142800301521940140307802c0343c01458140402c4031251502401c00200b640c0c20058010005240030b019203150164101d507142030b040280070900020003103280c2090062008200d40244400e0001030780c000c5001da0051030b040b07000603071603aa03080140319001c21a68501c0c0350590081c0700d01d0700449000110f1412051014a0050b010a600c942c10303a442e40284030340701d5000c1ca40c841 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 880232077 1250 880230827 880230847
    0xd080c0a21020304050709060504200d0f050a0902100f120f0e0d0201090507120804030f1a0a0b030610031101030504031e0806180609070f0e21152406 66
    0x1940c084d502541c040c03c48149401c0780f4004983c09544500c0c00340341003050000c150702c00308407844e586440f100c0456654184818030100140f0907806071108240c50641806440303000c55100145444c0b090307401010714101003200307a8074100400c4c01c03035000800502c0b9140790505aa00824bc2d01040c10101148000c001d0b0402424680c250000c000183e40d20408030050080c1048180000c0039034641d82031068943d521030a120f48a940405448140d0746026001013000031f11200c210240350207900a80c0781460031903034018200e0540180c3c464030414011403a04410214a001201d6000d60b111800030680001036028280050055003405190b481d0400b46801d450500d03040c0c00c036559106212890302c00c0402c000501d422403c90208049030080140c140c56610485401c104a0f0900405603404200c08694505807140302d107401c00c0c000d81c10a00c24007840c52688864446240588202903140201c01c802c03558100c440c000803003203600d4605065001c10003c4614080041d25281c54800d501c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 880233327 1250 880232077 880232081
    0x1e1204080a180308030702060106091406180d14100b011704170406050919080d08130503120f1e0c07020105041d06151602040b18090f0d080c0a21 64
    0x94404e0310030000001c10411540ea041c0909030140806083c0040003505185920000110528920b40125400201001c94880710480b15040e14002488911256068a403240510480411402e418450043da003600e60486014034910000103940c3c0c1070769000c2039808007190700740c0030b8025103940030401a600c0145a248005102500d003540703840d031303603075402e042801420316280c50390046142d41d0541c00d000c0d0903400b242d10841c0200514081c00f854031854443c40203100c090f88010142c0c800012200c5000c0e4030040003a11600109805094a03661006e411008140110780680a041c101d000141e0f110308903005800c1050042c5041c9083c10340301c80b40c0004d6a40c0247c0301d00d60f8a84000f040100c140303480403a40c0b584072000c0d20000e044c860111040e20490a20384002841f503500c0b00c50038500d0f9144c00e0030810b000402c00c01003504909105d00021340390a09008010501d00450150303091041c09000394a00600500c00e0840c42d04408a404451104008100035003c021250170848107070750034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 880234577 1250 880233327 880233329
    0x1e030e100504050a050303031314160f030b061c080c0a0b010807032306010b0f0904020a0906090b0c0309060c01090c1e060e10030e0705060f1e1204080a18 68
    0x1589809545500703000c01c00504d2080d6071322243c40780d4402c05c108000ca40c4c0004264080c0ea500c00f45003900e40302e8131103210b4148070310144c03820101c407203a4100160b940040e0782681d04980c046e42ca01e1405851300b000740400c1690302c4c4003001c910030100450000140c000001070040e600c81e40240c514114081e40c8a045180080e4803d003403580c0820828024052801c40c1200e601940d800a00f4004c01010030311911500148206400c80c0004600103e41c900407e0403a0008400184115076500c443c3e0800b42c0480c603540a101d00058200c003000ca800c10288003107613002118540114204000c090401c48140d000b6404044155203410300040000c040403581170181c80c00d0700070220040d40071105807000340f02681c42207040040f03090f29a01b486c2c540c00c88000720150b8524010070004040d42c161fa180032942e034081038018000182500155020705c0240030700c4840100c030724103101d0610030324204034018000940e42c2048007802180c00551000004c0ca140728503800e000c040f00e151825610400142 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 880235827 1250 880234577 880234609
    0x209031c02070f170705040c0f0806060904020705011b0e0f06030a0905010903110d0806091512030d0c1e0228080a031407030e07170f12251e030e 64
    0xe404001d8604e03220030300205001d840181c408001d0030810280080140d181c20750001c00740000200814515101d20044880e6018054415540c80b00c980c0f074043e000303000390008440510508070f6422b80680c4245e102a0075010300a12110903c10060b0400420354030292140000555440310740d40010400e00038420702d1070103901e84080c40826888194100072003c5c414800b0041c580381041919035480001c650002c00c0c1c51909000a81c0010105130000500c406803483c80c807000c80d204a41c608141c000e03400c08405aa03904000110710740626800b941c88082c50005a080040c9c8420f607404070000549280c03c4c2e082d0818180041d9440f040740c281d2100e1709000000b80c56051401c903940c03103006415007090003841c0420085034813420b92504c5001c1406080c0000c0303800c00104080c480104041c0604982000a440358001d0b4000c0040302640885000440c0040d2015a402d009100c0032070032038800d400c10045c0c86050302d4085c2c03040b1200005401181404610503400c140c81e11000c00f00301c06108 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 880237077 1250 880235827 880235849
    0x1e02060108030324030d0809060a0e0a12050d15061106010b030f040516030f03080f040b0c130806010e04060e0f0607030903090e3907020409030e030307081206040209031c02070f 78
    0x70030191241c10440d002b41403181c51804c007540340081c0030b00011100f1303000c2d4215401100c0c041c000c5e64200c80c00c0c41501c0d60401d40505103030080d00c0034038081448a0443c0c0450320b540b1803100c5200300d426240d000920400f004d145090001600600c030a60006030321504c90f00580d040c0d01e50001c04c00e8800102500199690503801041004241e00005e02d1034026140598280041c43c01c0e41d20090100401400412000320210780c44103601146400d0001a05018098980a41c2c44009244981c1c00450342918000e08000c0030000c2d00d00040f03401c1903100c4c030060141c9010b9071604070513005000c031072008a04000d05c00300001100e001e41e4013124000c540c031045202400300003010b51907806961102e4216008400754600c2c40c401072200403034605a6040d00c3c0813542d804d8604094580d06000003600c0d815000000e03581041101c4c1350001d0002d90b404007a0100c181d1104000d000403401540c501c544c043e8000000c0c88514940341981d698400700c1d510441d40000d4543c40c244101c500998040982c00c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 880238327 1250 880237077 880237081
    0xf060108060a0b0109050d02150c0109061a06070c0b03060d1208180d020c0108060a08012c0d050406230f0903060105040903050306060a090909031e02060108030324030d08 75
    0x1810b00d0081030020802442c01c1c07851103040500141d9402e00500c0020b1090740040488501c4d82d194100780c40020410500030800d200d06424104094188400c4a03d51511051500d0325246807042c141e41801c2c1d00705001502ca01d0a1814404442d0300c00380a080e071040783d4802481c006481881150003c20280e901c02d101801c2c10507465a1505d4a4064204641c000d0200c5620440e030005054044031001d183c202c1e41615031002046001c00541c00c008015400e003030300ca01d600b10b1020b10803410300d07000021100c0511400104642c48120844100d00060010041081100d10a52281002c0e120040c500c840c1c4904000c5c441340554420079001410031004107500d015482c042c40f43c10300600060381e050101c0c01c059074004095110040c03103584220000304042c1c031b040b4030035221480a0429454100726050300d6080142601103150b8032203414080202d00d420006c4c2c4082140e60480b0a404c0c0118210b864844222549040c0b550300032040c064000e2a503000e6035010009000c00402c29203500c0303668 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 880239577 1250 880238327 880238341
    0x70c0506040c03140a080d020f0403053f0318030d1a1008060d12210204050f0f10110a0b0a0e0c030d1b020a09090b010906080d200f06010806 62
    0x181c0440c0e444e055a078020401e48808030302807000f156210104c203c4010f94440c40c5c0e4180311803500079a0409400d03032140c102042008143d200320f02c210410080030712040e90004001f503d03220200d0201169414000f8030110380700003030f45601c0b034070032811440c00d8904000858042100701ca00301c1c19900000000c1102c01c10040c18001c00c9169048180c0c0b038868481c0c904580803c2646600303100c014071861804175100c01092007031034000303502500c5400ca52341d020391810740c00011f50020302171a40300b6032a5004010413450070009142d02400040c09054040e10031540650742c850302101d4081050280d00403140c00102400300043c440c00c0e40c3d50f40001c1c40c0740095005441d0445050303225000b903001000d5080842d801c2120a1070003002c1c0030140008070041d00c0441c3c00500558800c203038003070906042004008101543c603044e50041d04040240f140e5507000c56664106810010f004030707050394000c08181c4030419005103070482100403243c001007075420f1140b070000241d02a14540e0803000a00c00d407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 880240827 1250 880239577 880239593
    0x1e0a06060e012f070b0d020d11030f060f0f0a17010f0903021c03060b04030302151005060d0b0a05030a050601030c062303100522050c120609070c0506040c03 69
    0x107201e5003841d000c0d02400114420701e900428840d05807480004004031641c0c44441002400c002c0c1000250303880c0c07140020803071840a500b0807698610f2141c201880780d203006620009071791107960314080d9100f1503228141404007880c00c40f003c240d00030962440c404281d40700c0940c400011724036504800310304e007101e40c95942101c0d5101902501c0c18107001c0c056020903800250114603150100019013503030710101c0198010129944040140384002c030700001415008240a11040d0583c0000700c0142c0d50160b044025000502070660710090034898620809400c1d4041c051002018144620003500c07000040d242201c04442120180e02c40d0f40103204000340c0703008000c010080c0342490803061000c1100800c05401c1e540c0c13050364030300c008400100001c01d04201c00c402041c000c1c05511260b41d080f459250b001e1030061b0702c42c0f000303418503010862518848041301c002c4450440e1705000d80d101d82007081f40031700000c1d02701820010890209008030b4418400c06001d280700b0007240c961240340d4501070b11 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 880242077 1250 880240827 880240847
    0x31504050a020c0a08030a1401032a06081306020708030f041403040605070f02040b0d05102a0f02071e0303120509070e1003060207080a0207080d0e04051e0a0606 71
    0x101e03581c010300c40300c8044800003603440d0025622686454417969991025001082c9040c0c44160707090018000005119840710030b0080380304480204201954050b622a402c8078280c411503001854000c00149202c180e82e910300942d61140e040585002c98a071031362910344d081076034905240364482c3d042c0020011140701f00444444c3c2c0c40061824980341100150445c0504180604492000d00e400411961160310100000a00810f9100804281e06195a03910a1101ca11000030f1078940048250480c941c48802c020452094208400070048421a103030001e4201d01c40642c40381d00340100d0000c00301d1450400c90a40725072024190391440c100282540d0100703410b0080546040c09009049030086148016940c840184001989070204a8113004c8081d50018290760303c04a444810020041c0040000c05095401c4603545903c40729013030b40b90740103a0501c0020070310200e1010002d06064000d103030301003940c100415111598412605408a040f2409400030380d50300d2091151541041c0040307 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 880243327 1250 880242077 880242091
    0x1090503060c03060f1302190305090f120d0b220605040525021f02090907171906050d03050c010f11070f060213060215070c030915020f0303150405 65
    0x1007581c1c1000900c0c401c1521000d0074890048426001d50043d6458821000e800c107100c46a0441d5158400000303000305a20818100b0002420107001c1400b401002813212008109140503002d841e00c0f008003008a41d000e2040030344019222201c0200e035a0310038501d07400807280a100790f5580030340186035030209e48040e0800383c4030f18640410b00000800031a04041c601414100c190f08140c0200d1003a460040b8070550228200c03420300030481c0000840c2c01909030524143c03454020ba8540760021354283e60b1001c100040700c8603d0000070102100c08040840b0824000c1c400100c1300d803188081404004050020b0700404c00015031103641071001d21601c00036841808080240300707040b5001403400e1081c0c100242c1441c410840240c14044527a04962160407000d00840542d81c1e80ca00c044e481e0590080e81419140d40000064143c90040c410492180c1e40f550711000c00504001e0204241d000118500046218200906400d800704000940c06000044c072041d035846c140404000c15114024000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 880244577 1250 880243327 880243333
    0x1b1309050f0429010b09130c0302040f1202030a0b040609150204080d09080c040b13090c0f0b211503060103050f010b03030f160f050106062105060a06140408011a01090503 75
    0x2c0c100405401e6103d90644000003031660b940d04007200000c01c1c0710000c2594400d10b42c9050340701c14200760164000c1084490140401d00c00036925a0003261850346036002940581004c20341c0000940a00b01c1d41c0c2c0c0c020b00c24540081c0d00140f50300d0300100d18244500b64294280c0c00101408407a504000c0904d041500d460040d41c05806c2003221503d0301c540d01d420070f0141e6100c0001580710703900c0d841e07144070a030f5452104001003401420600d9000e5418854200f030f04088810100700788100030111000344e98043d8081f4454668844031424001004000000d180c2410008038056a01800704a00850044000740349800305848000c1c2150b00518266100f0b0384100000c0c100400b5a00507100c0340e0860046003c07008040b400c10103d09003103054010115482c0c10000301d21950020f940800035604011500c81806040c1004400c8070f100307540450b44801102c00411080e48910700075240d00c401c0c00f094500703050351804002e0949d580c002e00c80c003c4e074111031b4144240b5644485c81c54000c1500b1802 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 880245827 1250 880244577 880244633
    0x1140112121206090f0207110303040f0312140c0d090b09011205091c080a060e251206090e0c01170f071701120212061b1309050f04 58
    0x38542911560304000d00c02d000c0039614004281c40d2940c031072801411045402c1c0001404011150020750048404030340380342c0c202c0d083da0010704001054400303490392249021a0107080d41c8074240310a02c161f43c05010071102d950100442a00c14002d000c01c3d11003a0014020041c03c1c0d80e000d071955146401007041040140207103011170f80e02c0750740d2111503142c544000400e41c807200502e604104605144044598510030b40e100201e81c05500070b8400c44158004101042c0c6414a0341030003d805d9400720100c180d41d400c0c00100d0300d0844501c00151034141004000c1c0d001323012070841540e0b4180d00080c0050743c3d890703c03082c1c80d00c810301003669003900900c0d010454480494000c030044602a2600e54450104c200007440c0d58007403110704000e2416800f0522641da500c091a01e00d03072035048412802550341c0300ac4c5003036003113000502c54010070007481056100c4034444100840b0790409448480900c84144000584607501c0c82094012458100b0191481c9858240141da045040742c06030610400602 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 880247077 1250 880245827 880245833
    0x13120c1512051b0c0a050d020a080d2d0903031a1f0c0b0c04060f031103011401050906131a072001110601140f040501120f050f070801140112 62
    0x40840340c1000c1c00040c45455401c404a684000007403d45040b0000150108800300300269040066100700d040b40c02c415941c0e40c0880e00c4101c800d00040c0740100501c200c00b01504150040448240710507615078041105051902d0350300c001649180c405031f5160603031418540c0c580a8203290406081d2451002c0c10500f010421281181e481c3c07808407003454000c0c82542d1301c83ca03045118543c21407600411814a043c005400c0d500510908000c5501d0350014800f8900030300804281040010f11141984e283c07001c000c05588007881001e0401900300548038645d80c4400c044c000c00e080f40b004030303e5510b00742a01070425055140c00051040c0d424456080000c502d223541c0d180c400040000c3c00c0180c00d0400040e00c02c60741a0049480300d014460000c190850b02084500c401720702220508041840001440b045602c01e00852a0002031000440089440908541c010901c50421500d90080a200311420118a0781025200365150f074960300d14405141d058a000d00f03801401c2c5401e00030655 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 880248327 1250 880247077 880247087
    0x102130509040c0b2229030604060308070506010608060111030301060f03020706090605090606042901090b03070e090f0903120a0e07081e010203071b0813120c15 71
    0xc800d1500c681c0009000a04000c01580103900900e2130a00094584002a81300c0c400086000161100400f040c040011318510ba41440811900a6207a1b1036500c94007800d2003001c0d600041400750480d849400010004407180e004281240c082c07005000703e54102130f0020f03c1024054800d60422100c034201d1555142c003c01240d044440c0c90406142100740b01e9000e601074051410060107261400300c4810601c69513404c690302c92241c0c5d20544c1d06580c1d61604000449010403088003a440d00c2d519050090b52410034580c511060504014148a656030540615580115681c400050900940501c2070901e4101541c104070074001400c02d070720b00710580556034001e15103100070410a01000c20580c001942c8010b040c4100801940c959644a48807595144001030310003041c0c40406000c07110100701031081d00e002d14880c0e581c0505240c18503405441e00c00b402074007984d10b90010003a00e4040340d444c403040c6c8010220326450b0301d5141304600b05420100081c1d400b440c0c90310307000c005030050240c0c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 880249577 1250 880248327 880248329
    0xe0d050d0e01020a0f050c1e010f1b120905030f03180d03111210320307050d02091803030a2403020625020a1d090a080702121911040e010213 62
    0x41c030300992a44041142180340940d0f5410303045080608d00300703035160610b064203c0d0982c00c544d581c1c01d00001085540342c482c20100f60450764005103095112540405c03060300100582070203081140c3c105a21700003102c60301d82c003d5815013042d011254098040441c1806000c05d1f418207810100300c441618081010f6134072800c0080c0520310388000000313a02c0c1007214103079405010480d000c150941700d160309940c0000b10044024206030600341285490745030029000301034990250020550491981c01c0c42860400640882103545000c00d0a5242c2c0500304080c503c92504210b002c54040c550020311030417400d580030380c060080441c580500150300c40e8021150185100c2038420468032500e504052000c00e1000c00944c403c45141d0001030aa121104081d004504000e0b0240760707032140c607006541d50b54901d00c0141044400d0160724054a007160f505c00440101c20b0541703070b1880400481113a10000c0c0001112075a941da0501030640c1000d11450985d19003c400840c82c00900c22050344820720302d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 880250827 1250 880249577 880249607
    0x180109140102130605034303050105032a12150f010e1312080a0b0432070207061409030d1e1b0f03050408030706050108011401031a0702010e0d050d0e01020a 69
    0x9940004d400249a90a0442c040c0050921a641031f40502c080140500300a01c2400e1282c4111103c05041040010003259800041c4031000500860001403003040f40c20001040b03480c2c0034100c1340607410210039018a11a000d00c0d0f921161541c1042e0b5901580c2002820905192910b03101e08000111001c3c407034982000740b81440c45c89651011884d0002c0c0150700e400941041c03d2042100745407014204024298240700f170820300d8441c6000c60006400b00413240a001640612010400640140d0b4501714000c03d06020605d804040380100f440d0800c4664020006074000c61a50191401400c014411000c54500340d40220300c0000e018105402d100009480307010268006030405008170200c90003000b1000c2902d032240d00c90300f82400245403d1043e000700d0b50914581c044080c6020000905990344501c60170281071186220b00f15080c07000300304801b599030340c0394a884900f00421107011200a10743c0d41c0340d40c5021990308017043e0f800d055048007142c0c2c010310004041603003021444030000b0b9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 880252077 1250 880250827 880250881
    0xf04030203070b1518060f01020a08030a1112040b0405100b01170901060f170f0606090c09190b0c1e0d140f0403150e0c060318010914010213060503 65
    0x8811500e00c084814a4001d0782e8808141c0040d04410a17404103060304c6071a00b2203089041c01f138a5001682c41c0c41e85120020660a070420000d105206180d0218002010071480340703062140700f1241181d12003080e281a100c80f80c85408000c00c00c4002c101c00602d000d9040403e0200b04820800600703849000030070300244801c00400990070020941c001d10003800420b140042c0c45d903441c1c100c85d007051032803590030155025246500440410005140e4000d0300003806040c5640e4039410401060f81014410660100d408204940040400600100a40801d0b44619039402ea00398100c0d20302017100c50a01d40d203000c100d151064206011400342c0e030658981c149500c4c801c10260080d01f00d407244061268040f2004503011050010490749407086041c0c49600f044046103018400c0d43d10a40c0c8201254408000c000003140000c503500c1d07030040c03145200008200c079100e076170301c1c01c1c1486d40d86c040c2803040e80c0d408039020201ca84011007150003803416082852450034a42e580c04108880c19441c040245 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 880253327 1250 880252077 880252081
    0x20f010903120c080f1803070603020f120403051603080a06080a0b0c0708070b041b142805040504080d06050a1503020a1e020a0302061f0510031d0a06050f04030203070b 74
    0xc10720300105c440c64150641643d550300403842c4011180c9100405c601e01078810081e0101d0507600034801c44010321b1042103510704004a43c02d07031030b0100c103004108504025050103074014100702c500000c1010343c42610b65610601e0b01480c6c2c1c00455244c0d07440340001d40d00c40c0003010042000f03001ca5580118407500d0f01ba80e03400082c240401240304000300203007880300c09030800003030000200c3d00180c1510100d80001c0b41c40e585481c10380701409609450b42e402507201804503030601020192038841d44c0c10060754001c45988900203811030303200321403c3d12510000190246081c80034409c1c1c10151004a5549030f1503400c0c02e20310304038100c85510310810300d2b50004202d00c00038095400490070381502200602c1251159000a48465030040101c0c00341c861382020139070b03c02a000c0f00c0003000100c003180c001030310718180401005010010501051559540030541e0329040317414600d180365801401804000e4552400301d045440c018540d9611031180c2081c1305c0004e6000c4105c46010303400c0980050740d5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 880254577 1250 880253327 880253333
    0x15010c0f1b0e07170403270b0406030e0f0d201203010311030114010b070f14031612080103230f060a0c09080601060207030b10030f0b04020f010903120c 67
    0x454188401e10645501410000b034208581c241542c86404940da5141821820b4020b0141c250425200200860b03404d0840117401d20101c0c44040001c0540020344100c1c030342e1080503200c0360344035410a10000762165584600315604200f03909550401b04010b041d81401da4130000c0440c0c20b1003850412448148000050b211001c000d194000306512045661700d50b543d00d4214184488008541d000f5401d0024548442c0354108000d4102c0366840001440c01020703031365080c0c0c90707800c005044807840307008007074000000000c00203044144014952880080340c6400c1480185507880c5e800810010154010702c00500c0c0d05c080718203034000340e0141070000114a80f049043c65a2140c00310035a00c0b81800700905c5c00b1442e003200485d10480c0d124003140036100d0840f42e403035401c00d000b4880583d005003420000180c80111541c1e00c0221480b01d0300240b41c03650b8038450041c0500400b03440c45c1c136201c81032005500c0d1040e6a500900030908002120300e00e581d541c040302c80c0030700d148201402001e4080300700b8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 880255827 1250 880254577 880254593
    0x30504061815050319050c0d0903120e06091c090302011d041515020712030e180903040f05030a05100f0605122d030301030b07050909150915010c0f 65
    0x40e144150240b061003800e01d40040c102c1d007045400b00e010048100d0b02c80d1810507a4841d01d80240c1a5244103485c01000045010160012540450400c84005600c9415030070901c02c100480603c1c101601a50800d00300451030031606681c3c0300d0900040c03441c0012113581192081c4122542802c200406606106203a209400300030041900a030525100c8107060206010142c16905103011080c011580b00500301e0b039038074042c003030b000d950313082e218500000c240601c038160240d000041034000e03101d14040c0f101040380c1060703c0e4001550310205051000b901c0e0502150b000d050258002d00384c03440107440d51540c803403820343e00c084100c6c5d40740d60804c07006030603800640203004081c220030541802030944581e518480116861407840000200d180c06a681d001c04c07811484d610700030360039a42036448500d200700c0d01410010503c202044040800c0c0c503440c00a500c0f540b003003c4001d1140c203240707050041440b0700a2050040c0d10100544078016038205519041e556000701c00080d0f00d04140c601003117 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 880257077 1250 880255827 880255829
    0x210c03010e0115032c1902150c010605060d0b1f0c030315050a06020705091e04122a0b07110307030e04060f03080c150411042d1d03070305040618 64
    0x12402c00e00d841d1107605c0601511072581440740f28000c880c8010041c1114480010392100000c0d8492040c00d100007800c0009005449010010300000410351f56542c0024090b901101c010301c80030b5203403000800580b600809600041c02c51542c401d1043c1c038184801040c4400c9a900142812355608920040520750b1010030f014001c05000b6805158a03a400a0340c0c80d14903101c1c203803140d80038500044102900c2480100100008400d1301d04076200d940e100c0000e001e00071034100400c0102c48042108481c0300c00c501000d40324030f548100d4800b1040c2440044204010078400503c035286801c00c0140b403001048516054042c50601c01c91285e080009001d8400d075449140891030200c0d012050042e01401029950354100072039800307220b58441005012011103010749581ea400280040500709600001c20800111442e030191082e0918101c90303181c00a02e0100b4a1a907841100d0360f140480a6080054070300000158140000c40d5001492482180581010030212003000d80e507001c40420114 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 880258327 1250 880257077 880257101
    0x19030203060c0c071a07031b1e050115080303062b0302010e1c090515120c0d06080118060e1207061e0209010e0420210c03010e011503 59
    0x64507420140b00542803034104031070050b01d90045150010701c040d00003e10f8109441c00d40103441c241034045d2410394544141c04280c41d1442e00344a11540055a544d8003080700d03c0a40701c0030f500d10002e0f07041c1a42110108010525039030909081480019000001e690703100e10300b2909940c80000303030703090450022150221a088104860202c0c1c00701601904120440c40800f400c5440300e0220114801768102180300e100c0100c5c413212420b108504002014400050500000a1070184490b5030400319503000c94401402070f0000c2070580c410a200c0c09035400a001d48802488469849090010b030480c1c041001800b41d5603035041524100000d101c1d941183d113034040582e807036000c2410728002400178840b116a80421880c480008482a8402d80e50780e0181a541c0d9a080080001880000d200d6014011140f443c500f00c840c461442d69002089180501449002202c0446002006960b8050010510048144018007030b0010400d10b40d41150140f40d801921440c80310340560090260070050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 880259577 1250 880258327 880258333
    0x30d0c0c0317190506361f0501050304061b0e030609150f040f0218010e06010f2003130314010c030204180c0507060c080702070504062d09140406050c070f0219030203 73
    0x100805104810300a54664100d006c40c4c0040c1d6103079030118451101c1c4c44191140c5528501040c40554425130140d54020710031000000d00300b2502152400c185801d403040e030005005d01142c80018102844555084000080200100e4000890624003014018200d050420060300024140481401010155030b006031281040c8640c4103000d840d406824000e40780c01d840040c0c01710b00d155206001940c0000c0096540b17000c3c1c511080e0114011414045003602a44414064000880b400840980c004c1d48918003042620713071000c0ca0786083d01c0a00d5560014988140002c1000102c1042c0f10202002409070000e40302c0d0100e002903403039000c2c409019141c2454190004811070f0090744c01fa004030002c4d001c44d14400d60312801c1005607800e60107542480c8034541e5049042d203840540d1003c0070041c1c0501b1032503207034803510240101c520911240304498186402d001c1405110320840b90040b060b0355550703140544a4070790101105e200803000b8028202c40840140348528103070301d040559802015 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 880260827 1250 880259577 880259629
    0x42d0b09011b051014040b1308030a0c0905030303090d08090f120f0f0f09090a050907090c050c100c0801090b0a030206160501050c09031b1c05030d0c0c0317190506 72
    0x1605d11220030071501221980762180103c0c0d01b4103100350a080e600d40d44a40518a561b5032001244042c00143d41500b003404099440403403039540c00d00c0610b01c00e02050b002032500091803070000340100d402400e02c00e11504164065210300c0b90100b04400041170448a0541d01d4444036208083e520601800c80603509000c1202c16000100c40000e104210048401d00f071180c445200c10021038405440000d4554010402005000c11540015142d941207080140c00c101c2d40e507044505010b181901d4007041a5076141c1d0010481d00803690302e001d4444204108034a83c5440d0205069601e2400040d101d10301c045503001e141e09021a54290096200300284083d007002c08400780981c0005d4061b6200b8040c65000400301d0780891140100ca09000304018002c11204050445d42d540c0e031303002690b03640410030071380c08a2a118041e91415004c10340d1180511481400c1c024401882c0382803110181e1001e08c14404480184600880b00003000321000501e03448070f000050000402c081c1981042c5541d0762 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 880262077 1250 880260827 880260851
    0x2041104090504110f101d01020a020d0c0617011d13050109051c1404051e100207050118030317072a0c050a0506030f0903042d0b09011b0510 62
    0x10000815138019500e00c201400315804011240c0104204000001c9070507145048130050030f40030b035805c440e060050380c00c0b04005802040c11900d6040e800e5404004040c01001419401240300040040001c00300c1c501d0b5040c1000f040600a081c200e07070300c6441d106008a10500e0001e0721003a9655400300c020800c3e565285005615801d5100c00700107211441210341d0364042c02606040600001c1010503407905007400e041049045029094a00400c03890b1012036681c0c45041844107030802c540c0040c6400c0d0300d4040014041c0d85020721900282c14a45800c000107a042481c50164000e9401c1603400c923a50f8140803610b003400d071a0b801c19241d030118170741c00d914100604080d68080c000c01c0b000d4882d0b51908144446a1041d104041c0c0054007040060450300e070f0883c240307400480803c20390345042d6990516004180c0c010350180045403244080069000398030180a00512282040342d0920200400191082000c45800c0039042156000b46003004003d001408108442c3d00c400c10030f650100c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 880263327 1250 880262077 880262093
    0x410d03030e1f1416020703030305150901030b040b1e070c030e10210e0a02090c040e07031a040504021e0402130603150909050d050f1606021801081302041104090504 72
    0x19040980301060a80401c0d0f039188130900f40d043c1407002c0e40007064510701d1950b04500a00d03000340314128540e518080001d9030780e242c411407030003180100300b0b03d0300b1818223040c040c20020000e40f000006003990003504182c580300c00c3c200d0b640052641080412080a4102540e03007111409170f959112102544440e5501d40202040031180c0a0309000004031155041e507404444191103403002d85d0380885030840040c9008001141e202d40709032201403c240d9100742241c420303034040c2caa510100362031307a01280001c0340302400c03800c0c040403c980a00503403d054000c101a50004058043c92178843e440c94095501c0e2a0120360360700c0201c401c2c8621156803010010010309403222a089420400b03000098450414000e01070000d811401400300d180c151131050710183d0003071004a0303d240c1e0034000300d004c1c405400112891580180005a50341c50610039903448120706a4440e41440715800500c80815a10401c0c0d42c4010703810b541c0090721000001c040305035400385a010500703150a10040000300f000309 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 880264577 1250 880263327 880263341
    0xa050c011b180305031b120c01051902190e040e03071406010b0408030409090303060e0a0902010806150313230a02011d01081b04410d03030e1f 63
    0x41d40d92212210860b02101c0140b0445100103482540207012200c103141810700741c0c00021100c10200c9174001400481c1c07040c903402c98960101140d40d00c00030071150700d245560150003215170000071443c2800f81e41a03484058440342d844420048400c1a1421644681c0e11208903a80200d040301d8a89000d85801c0c40a0040714500d080c15006203c00000c0e1290303841c1c1a20305071001d15001c0c606041c10000a00024001c2d007406908154481c1e0001460900c0c115041c0d001781c0c02070101080c90325417400058110040500a1801411487d180075403400c0340106990b0046110080803603aa005030800702c0c1140c0c25903804c000d8003800b903002283c21b0403000607400183c80c400e0b02d0300902c1d48050754461080c211071401e2240030540c6103000641d00220701ca50040095032104c0858146919480e403072190034254042c10302c4071480c4000400020801d0340a003000007402042e0a03101c840c100012468550010748020145519085a1038642c2d00a22a80b040d60f00d5003600e07000c2181c2d00e1007046001d0095 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 880265827 1250 880264577 880264631
    0x15090f0603050c180403030b0a0e0109053102091e0c0d05070806180601170c0d0605030a0c030f1104021222170a02070906030809090f0613020a050c01 66
    0x1000007908050074280c02d02500d1454a001308a41940c036a2400e81c0035104c0c0799182e0741e0180d00c5101c0480c0011589000318081c1100210005451914090b103242c00d00300000d206680148150f02c1c082440c103a8041f2113040341d4143c0f4050360503214011a040488440015000510304034410450210002e03005090400d610800500040d100c0e0902500c0c400f4082e170b201c0d60040c0075000c44010300c200c3c1071840c0d40c200c5c0c01031529000c2201c41580704a28030702c0517904105111000213081507562114001e00010700802c83c041e104680c039035a1429003940040c40024860300012420b41c0c11b0008200c1c0c08411010050425581c0b134684003000e86900d482201c550050100c4049942a000050f00134410000e5201c4c0c1078031009518090302003402e410601d5410b0452003180030110b800c1246024400c00bc6204120603601c40444408100d01d0f448010400b0350007440080400040d42d40360094151414550803005a944880510444140c8103412061000f9808c0541403a00c2c0c1e07141c40741031213031882 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 880267077 1250 880265827 880265833
    0x60b030f0c0a09180c03030314130c030204050705120108010e2406010804030212030705130815060103020f1608030106030c110604021c050a24020a17061801080105010806060f031015090f060305 85
    0x7450300e00005421003e00c01c003404c52103400208cc401810540d1100340c0003421820400d041c00c00424296109031002d0300a1520380e5105d00f0321a0140f90108660390819051180d007006490f0840c5101c214414020041d504004518004c10103143c002d1252120504030800c60540da880d1402016125a014100c0100d0000005800251014020450b840d01403451003d00c2203030f45455004401a4200c0c9800b08501e0f20100079002c8145043c4407007101d003521815450b504c035850213002408840043e241503090040c00c5070300389001c80011592540c003641c1103405508400010503104500107240c4002415032107101c030440144041007501050103010f404851003015540f1015100b03030702035288030f0408103621050344030319010603241d05a4020f07400307003030800440f003450710282e1407003020317030124049955030701c018060002d050100f01c0d070160080d66209030340d03030440c1c0200b5590000c885d40100416034a600c180c4c1c20a00e0311110034001c020129050010307507821920740004250300d12088a81d44 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 880268327 1250 880267077 880267081
    0xb070905010c110103050402040b06070606230d080a03060b0c010509010e0d1d060d0513060c0815040e070503010e070e0610080f0a0b0607060b030f0c0a09180c03030314 74
    0x588075420684107190700030368040c041203400c0f00542c080d0102500403603100341c407280d00314038946070b007070142c8103e9000d11404941c10785000922510320340d000175410380c00303012000d802c205a1141d01d000d10b4600c0c0e010b40d00c243d407106c1f003e90840003004d690700803034540c8000064528124005400540c002c40b4508020401480c025091940c0d5210110b00d40c6d02090255490041040c2001d510401404000e0061440c04030000308207812154100d0724080354144005450b07041c800355109183c0d0700b4140b230400d4603960902d02c01318082ca054600342c0602c161b844450070b4982d4081481103d000f4280a402400040400b2404680f141194020308100041c400300044080c42d00300481001340d011500d5032421500c80110000d24800010113003602241c80382c4148050303031603180041c00001d02401c80011703803100341010941010b190f138004d580d056104050300754903a6106041101181c1c0c0e0f4210000c0d2500401482038144800c09102a040d841500e000009142c2c040c0c00c001c1651811980e882c1480d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 880269577 1250 880268327 880268329
    0xb2b020703112505100c050a030f080f040203070302090901090c0303050c0d082707030804091b0c110f0d080412060c02030a12050402011418010e03030c19110a030b070905 75
    0x9150542c0500f003c1e00c4810f10104000d081508040c02d581d070306031402416102c0203440c1ca41c03421480440c00c40006080a0b41c40300c000307074400b59094004000c51351221050400d900080e03030703d00183c00040e100c0c801d1100804c13134002007540b0540c10320794044641c0803d19a00e0078058040d810100e110b0041d03000c1c0780300b00f04105210f44015403250031a84440d001c01d80e000000740103003080c01030011203284198500440460424000b80c0010980503c02007509410000d8031454044110203840901c010462018009900c0303078041c0c21560320a407046141c4d01141e03800030706200e151032000f4007e0311001602180103048040c2c98070440c0e0160303030b050006400c59841203a407807241c400590300180025428801c4400282c1219401074014503049a4505400c294100301e9804656001c0280900d02518109560000750b0500c1c0d0041c2100910700340080804500c1d11810717800c01c2c5e024443c210110260402181d891000b030b1202010340480e043ea5124505640b4030a0107903080408140841d40009003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 880270827 1250 880269577 880269613
    0x71e05090319030302040b03100f05040c02030a030506031002070305070c050904030c08071b06021e16140a0b0c060403230d1a12010f150b2b02070311 66
    0x11520190090445000c0200c0310000e210324042c00302e08250f020000040c4030000000610b0291000d060020909803500480d041c000601d40e01881c015814030814900e502e4000c0165032105105040100303469440c4800281480d070300600701e0300349503c045144401d1681c414040d1026034400c0402103002c41d110000c00c03001e4001118010002448921440c0008242c00050b04880b0b1240458481d04480c04404c2e03040039502d03800c5000142e1050301491300f11145070580c6141c81c1c00060151042c03004005045072a20494001c04000001903d00d00d5510b841e0711404030024040d06114984030a41d4008440d203814003942d087e400505803001c042a0807080030302400c601032242c1e810518041c0e40d44214001307000c5d00020700b00500408540804c07951140004200c510865030f00010705812554605004c85184000c0b545002c2d0402c041400b801080104407421043c8032900e8415488000740c0e0190144a03d8140c4440c04d40045084804c140c0c111800500307615001040c3c41010301007604140c8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 880272077 1250 880270827 880270837
    0x30f0e030a120605041416030605060307050703020c0a0b030610090510030905160608010807080102031e0606041205030405040c0e130e16030c050103060b041a0a0504050306071e05 79
    0x9030000c00c440071001d030080c00841c0681c142c018001c1071542e40e901c0041c00700d51114500781001241407003042101041d0400500c445902d5041c1009046d080c07801168071400300403d44000d000000481105040c000c1001402d0010000d100c0c0003030b2601c80705030203e242c00644006000c0c44c02001ca41d0002c0d80204500800c5d202c1c041c00c451a4185000401c50291a000c8025540d074003420f202d06040d40c0013042c506014180946480342c055250004040c0392264607400411503074814414891900c0c50003c0000311003e00710701c000580c0e159100000d00c140710701c1d802001c07000030079980174042044c003001420446100701c0e42009890f215207000d407a4180d0000100c0d40c0705131301d5503121306245401c0d8040381c414106082118603400e8014a0034405031841e400c00d0714900750485040142c0d6030305000c0c040c090031500d10520304203403800d40703400e4034a181900c891808010124030352160038030600594000b000000d0464a050401c21f03c0a02002c03905d40760017581c1941c100c0741016850180003254 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 880273327 1250 880272077 880272101
    0x9030b10171b0105160201050f120915010504060e0103120306080f1b0a12021002120703031a0612070e0d02180702010f0608032a0102030f07020c090c0f031503060c0406030f 76
    0x604170b5900440d0254030607100791460204c180100420310b00000206841035006100810040c50a003a0f0400a61816071146100340c0c10804140800903024245a044030f81c0000140440c145469040e8040d000c160442001c030712034140c48040d003000008581d400300c611800071140c6200c0d10418010211514001c440d8034185480800e4010b00700040c1c20120b40249106441100344100360594039030b403000800340c0c00240c8422064a29080400020070340202c202c40300c910300032100980c0c80c021603000784032000b84000c02d05290025110585454103003070380104144150220b031a501c0b00000415504000190302e4804900c0e1003008c40c0c800c0409035200c0c04003c5081203003d05003000944912a200140c5540c00c103100640752100f40040c6000d8543c07201061400e28102c00000d00d82040d584c40b05102d03c89890130300501c00415802c4803141c01201100a550f50341c0d4030200c620901c0400d1145405114400401c610080c2c4500500161400c1d0780e000d01c0750124005400d802d507a4820100c2d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 880274577 1250 880273327 880273357
    0x130b0108060c07080a031e1e271b030605010321270e04060b1c0f030807022401090b060f0a0315080d030506040c03050709030b10171b0105 61
    0xf008078071550060107000c2d0701882e01260509141c4090010050900c001d840180e881d44a81018140c420b0403405003a000042c08014030984100040c03c80103104c0d2082500d040e20300090781c01d200790490070030940c4000120100025640b0b20300f080042500348400c0d2403002030b094100d220031110b50410811425039135118200c41c405603500c1c05001840f01c1c00081d10842419000070b99980c020400c40c03065024480000d401e40250081c06800c01d91303c4103070100d10003003032800710008140c881c0da0031400e42c0511309092240d070781c9041070317103081e048810100040001800b080c2e58891059001e90607150910401d0010724850820b1060b14080c512001c84400d07800d100036500c80c0e109900c4440220004182c01e10641e944441032400d0980421540e00000d45800401800e130801d40245a40d000b014541000319180040b0001c003400f03041e0100805601000000c07491800b04c04144ca4054440d03c041890103444000031a55141804125400000d109440d000b4980d8001d0040d0780d484c219442407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 880275827 1250 880274577 880274587
    0xf040c090c140a050412050c10053a0e0a030f0c0312020c34050909100b04020906040e01031101080907060c060212070c060b03071512090b130b0108060c 67
    0x502c50a40002c450182003100600000400c40388000030b00c03150074003841c041c0c46a403048030140480608056125800c1c004104060f04d02d094204c03a00c21074550041c03030300c0c40040d2402c40030340b14000c2078291007403e91070801c800450030030700108052040350322a4030ba20100c1ea101c14801d0302c13451100000a4086520b4603142e800c1e0301081d40061404c0c80d2079100303482050210050300120003a014024031107605009a0340307403100c4112042e41024040458140b22145003150300156120100500c01e40e12986402d044542511590182c84409000905840d12a902c034402069280700c244019170b2100f00310883d600495000303050700c034001c0c1410380c0030b0460035040c404155110406c4c01000c89919500b002240010b009405149000e0a00340c0d4600e001214682414403d032800d503901107100f41c0044804002110b0004170816504540e428000710340c3c078400801d00003c2070110400b9065221420401c07049a880580d200c00703241c0320311f108214503600c0300365407980c035401220040307881c0f002004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 880277077 1250 880275827 880275857
    0x9060a1a0402160c03050304080c010302040f140f090109090c05040923030c0d050a1e0e19050604030305070209160903020906040f0c08061513050f030a08030f040c090c 74
    0x18408408980203c0085820941e00d440100700c041e4025526500042014171003010180440d6140c40170919080d810503003091031701b040944080c8a12094141202e11014054543c0301480c070300d07104c0007491100c8640e561007a007009403030102c4049aa00d1304807103001c141ca117014401c0c514240d0f0000028404541122103550a1000c2d0061210007440300388802002c84a04011071058020240d6039551103d00b5a0405001808044e030002c1c180d110340d401001c0c10503845041507440d0f46c402ca4110f0900042164268603140007600242d411040002c1d01100b45a0004000c20f4180d1007610b81c0303500b560715031508086924035000340d00002548400308001602e05042801d40101c001400080c032220880c00160480d80b80d100d0b144045080d42040110501c0c100020310001c0304c02e400040e01c2c042c68624140b4141049000d034074402d40c0c5510301c3c0e05150702c0030820f1407051540500c08542c0d0b824401154802c9000c00c44d0111130500c15510b0200310f401e8580940c21450b20700752140341c01a13041c40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 880278327 1250 880277077 880277081
    0xf06180f03031b030405040c05210703020c10270b040201050708120403090609051005090603090102090d030201060915080c010332100b030f13020102012309060a1a04 73
    0x80e000c1a8148424005a0003085840401c07950305104440256900c0e40380c0340c01c1c801654480c80201e400d0007402c0c804060090020b442150210544001406465440304000d40007400303103560014a0303100e454243c031600a00ba80c000000186084041209410f5000350400c04c0c520711940200080c031148007140055004401404545201d034210f542890b9448010001d01c02046034140d0000e4205d44e41000866001208180602415038828800400c00040a0b0241c499240800c1c00380d8000000903038819429419103891281c0149084030401c440d0400038060310181c0280716034a4946030310b0881081000042101711401c110180024a5003c2c00540007030100001658501208000200c54001c0e101e020000410340d0f04040481401d0109250036492100c2e0022090001c040090042c00c100300110580e000c00d1072016400c01b0103046c80101d0140001c18644806038100c40070280c00d141d8200d640a1290282e0310451340c050f583e00241c402602d451110490224000e4040b03449981015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 880279577 1250 880278327 880278349
    0x30309120203010b06180f01050f0405330d0b19120f0b091e150c0d090503040e0103060b031203071409030d05070b0901051905071205070e0f0618 64
    0x103000045401800005c16540d9101c05003518041541c100388000e9441c250a901d4044d21080ca0032900308500f511060f01f2901c640d0007100d1181c80d080ba00c842126480350302c4416004441e4102e14000c1049071560509030b04403501cac0b40e0b206404c6c10f244482c1410a010b40710b140040345011040b01d1840c00e90f94042c2040803440554003000d06c21080c002080035183e41c18050448100101401c1503801d40c00c6070540c070750006000003500302a00d1b40c0b600044945c00319030400700010b109030ba1403031400c500600400d00b20500408034040810001036150288680d01d040728000d0a0900c100260f1004041c0c03983c07810061018410800d0003c5140d040c880c940c9040b80b060b1101c2e00f41d10700046200000c1c6012100c0c0c020038002039002801c1010000b20050706908407800308000c2c4468105118840d6118540c0c48100310103966500020300c3c0035208440c46405807424242c1000141400d50006104014400240340502c84400c01e1001c541009402c407803040d005962030040303091055080180541c01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 880280827 1250 880279577 880279579
    0x21b06071e0203190f03180b011a0d0c0c0b0c1201140f04020403050d200619091208010e09070e1602070e10050316080c010305071808060906100303091202 68
    0x1062000c81141c2e150121320101d0001c1c0303610703103400040000c00300405680d021340e2200303000810116800e0000c2e80380c3c10000d05407400302c00c44100e00c907008205422103005013a89102407500300305088202d00d4010704d24480c8240245144152607031181e01c040010b00c201388250110b001d00303500420481d503c000a141c0310720001000c580910807002c0001e8141d8001e82c0007940c0079005403410000e0030b500415200300048140c1040b19050103200000c0340c4484e0020194040000c002d52280b4440c1010752040c5c803400d0380142c0700621450006001040d80c403090103400b8074907017000d02060054030700003050000c86410b06910006907039a252101d5600705010303a003074207600c209030000c100c04010000c0d56114100074890140220300d0041050701c0d00b40100604042c0d000c1c1c6010078086000089529100e0714800c1c01c02140f01d0301d079220122001c0e4a04101c90300c2441d24243d01041400707001c20b41c83c0c00383c00850102c4903162904285000c8803031041c88001c02041882d10b00300042c00c3c1030f150107021140 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 880282077 1250 880280827 880280833
    0x60d0e100c0f140d021b0f07080307030509060d05010306020705060609060d110415080607020d030212040308040c0b1606050f0115080c12270d12020c030903030c01021b06071e02 78
    0x41c0c004c0c030301c109070b070441c0502001081441c03100d14502e000801102c2d4402641c00f009116061600f140c1c0e9840c0e100d907a0340a000c0040c0003c004c40d0a03100c6c9001c4031144610048200720720b6a50303050000c025046070b0b4080f50303d0300a12000c541e4900e420321005000d10341c0240001e1810120703903112040b8035240986a900716448170500801011640701da02d00400035807024081a103480d505c000e0403c801036030048145481031011081c03618464401560080d81400c04c505641c5460502c0005080340c1d50140380c80c0700c2c0000351310820741c91105100401c0c034440e0340700740003c0c0c840380c4242c10981c02c00d009080d0801b02200c01c2215691142c0013040e0010082c0311001d1900844040403110500d0440d20350180c4203d400740fa040800281580000c0214980080c0c00c200114100042c03404038651a00002d2980120380c940c05c520042c000c650300c04600a0840703588081c25500305010790231032900c1a02d29031b2210181b203c0c661001c00c60038406c04a0360f60b044400b031a0412143c00d50241040d0280440c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 880283327 1250 880282077 880282087
    0x15060f010e0310050a0606020709020c0606010c02040f0e03180f370b3c1323040b011403040b07170a09061805071a09060d0e100c0f14 59
    0x10820f880380c503004a04100006c103006007000c070068a440081c3e480b86490600c1008200d41c100070209003160030650901c1d08080f8011680005400f800341d010803d000549405084508400300000400c4200f99038610200d2040010040000003c0d40f0b44880d5000044445518000301030383c2d29040080d2800c0301400c0051b103400d480c210b00720791541c001c200c4004c00050760050075002d404495440c074041c0b075000c41c1001da418903d01003940368412508030445001c20b2407640c1c0308494040f040541000300b014850b03000040d1154241088800440e400b980c5440841d0886501c5240500e000c0364444002c54074540300c660780d1441141d0300500f51420000f1f8484401c410810740348120b40030351034031a030104001489060072000c445c00b40903448a807602200840c0c00158000c1551002c690880c2160350415900070b03040700e4075104181c6001e622100001d0080d4000c01e05500007444c26003135904883c0038002c04001e100440c0c000e04031039000f09143c9062400124803411844044501e840b40982c144 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 880284577 1250 880283327 880283353
    0x3050c0a030507020108151c23030403061d12070c030609050604060c0206130f0812130c0f14090612100209091b0307182615060f010e03 60
    0x40140340403030004400140340c0c425580d10002c20790700018001c1103804401200310016018100d000c88000300b18a0a03a4030000307004800e030015403444c1d05c0840038149038005013206501da52041c003003180c80510340f542c2801c01c123001d403540144103580700703000340041040c04050321000d400040045070f80265088020000910303e00400550354030580c010841420549400c00c01e0b02d99071558581198000002c000a81c105110148a4a13030440480241e10403a808c140c0c6040c4200ca94481001c80c0e1101440b0443c3d0400402800d124000c030480d110640e200c408491490ba07261041061002a0a146c481c152500641d44c0b0340105005100e100304807413151016003002d4074100c2210103140d010586e00940e04180d50348a900c0784c60704a605400168107000c080d41400054184002c00c0107045180c0b030158030480c40417024000130310311107002d9090809106800352084260174082d010f003006e40e402c0500392a852600038400140100c0700500110011904955031180c610340c10b204410120001c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 880285827 1250 880284577 880284583
    0x6110a0b190b060a0f030513030806010c02010327031101050105060301051e04091b05010e030a0b090f061303030c02030a2001090f06020c0111071a04020a0506030f01090e0304050d060903050c 84
    0x210001a40b078103980d4250032080a000c0360801808e1024070281c858040d000298489001680030009080103909040980012001801c480004882c03401c1003101d182e01c402c0e841c0d0828201a80b20b87e886101d0920070f1407059007070303038000c2c03241035040501400103100303038a44444000c0e9122404001c5071020070030072000609581c10a05d061f82d00c8101e825502c12128130020070030000e00400e0074460b005001d8440030994030230500d24041c241e001c0420100320b50202c1401000c025a006400315003550800783c4d070032a070780003400d601240401d00e4107584100d1540044103a5440c0711860300c65242e102c4400242c940340445100c8460010b550700d902400028a08030103c0402e9401080010303161003004900303a0071180d020094881c158018002d0301d0011780186143c0a2500400041c81c0c071a44032031021609415840e00700b0799120802204021412400c650641c0c1252f00b804401d02c140c0401c200c4517901c1c0c4c841c5009003a0000008011000440d6040d008610b44611916025280505545036141 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 880287077 1250 880285827 880285837
    0x30e0d0f24060902040308030f0a0219020c030118050303060108070e042d1e1503080c030901020c0907020d14040b070c140628020f06090706110a0b190b06 68
    0xe0014200d00020051100e00c51071014100e040f20441c5800d0440c1c070f80c82c450340801400c4030100c1101000081281138541c054460041c000070036400041d0341c900010351521584400d840c0290300e04541300d1103083c1c50301c19041c1d0180d0080d01542c82c546a80c0011246044010984410300449241000803a26180b058500518801000d007100314002c0780420000269540d5400040d03083c048094007009210041c0447c60350704c03080004810305140c98100000056600103411110b01003900b14501101100031f054848090742034490b411401400c00c41242c01c1650243c00581c0819644000203008600204002c4800034a0500f015035440b0f040e0030542c0803c03021903030b040c00348070201328803881e0090300c0d609150216a91030502c00001e54140c49003200032181360410085807480c400190003031020001085180d001c1d5081441c00862065680100c0c1c0b182d28005920034447e52980c00e00802c00f0000650700800e0840356464243e2005a0702404001803161266904007003051655800001e01e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 880288327 1250 880287077 880287113
    0x90614070c02090903280e0415030213110307031a0a030501060303090906060e011d04060e150402160b0613020a0806010906050a08040803100902211003030e0d0f 71
    0x100ca600c1441075950f40605030007001ea0007413282c078000340c40c0144a030444108002c00c001c42c11402e6a422140300c0c404100c25a085480c0621051190803e01541c0301503e0094030f03103441484820b810241151180441c040c5102c3c2c060010a0717441d803190b0020b40b544d045800c0000841c07580b4a0004460a12680c0300b1902603640d940100304040d00416070000500301c680342000b0291070608040d00d01c00051507020b0400041c9000d0403441081c0f02591462010050700810400307894082040c00480107540c0154600c092000c2403405180038002c5407508151441664100e031010f6469100b0340078058041580300f00e041c020211004954409400e9070100c5030b5a81030a8108000054850002500f041c02040020000860841c0c0c0241d505500a64006841562070b6a80ea122a1845040b07401604c281800001d04a1001101001e40607a031503a008442e021a1168809061003800510000300451100580308001d4540b9814011209005000e56281d0000c0c1d41d42c2c01c2e101c100d40d413000e2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 880289577 1250 880288327 880288337
    0x411010518031209101409101e09091104032003190302150f0103050604170405190f1d040303020a031407030e0d0f021b1c2015040909061407 62
    0x140320245844400c04941720000d04141e410380038044081180d41c420412540d015a0213201082449407140c03462129401d80101b203800c032140695002044400288602c02000e4103264410030106c10b05804c0310308495000c01c411000c0031451154001125010701a268180181440c541d0700c21131002c005000305110f82e02030030302d16030044105008031b2409009079006400400c01880010b030001865034100d500700a640006240c040b021601c140b050b42c01031504035800d880c44014074030b0202c040c2c40944680031200d4400c952541c1902d2040380c500c001c0800f1b0100c540d030200c1c0101c1d0180c2d0040840e0f00940c90040307540003003c031a0b50f8003d001540c0d41d81c0001da85031007429010030305200b611304421540c40d20281c038201685001b580c0701010f075140c26880c0100261041c1076598160040410310030400b00c3d0b050100da50a15911a001800c11201425514102012540342c00e0440c1115940413036216400e0074107180c000002000760310411694039917600b6400051382d4030020280e210b5a042c3d910307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 880290827 1250 880289577 880289587
    0x40f031e0f08031012020913060e1f0f0507020c010804060b1906020f2a1201061d01381b0c010f030501030512130306020a05040f0e04110105180312 65
    0x1324102440659205c21961038040101100581d68450392541186200366240e04004c0282800401002e020841c0840d601c100041074280c4a91030080c0c061294804204002e0080c0148049080d0707001114903000503081090804910b60042400a4002d4001c040019403032240001280c4240b001c10716015460f04080c1040000035410840b85100b105c058019140c0c02810303038035804101c041c400e00307518810061a060b8040392100c04450b40c2102401009001c03881e80d8000f0500c00b601c1180740403100130118800070901e140900700c50180001074507021801840b6210b1500c00741100343c0f90b09941640c041000b020114003000300300001c0300e030079005020300e2280e002c00503081c038094554400503d81854010408a040483e5408a540e07071811211ba0310004125915103801070b64200a000510100710001744a074000041c00c00d0b1600b207003446003219202d0054060507441110000c1c0608403031803840445500c0740d405002d107400010541000444007800203820107000300d404903005c0101280e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 880292077 1250 880290827 880290841
    0x140412031e050a1b032a02010e060f04020120120901030207021002010c080604150e07051903090c05040203150f0303130902120c090604031e02091302100203040f031e0f0803 76
    0x4004031800c1e803682000c00c2004021801001601c2e02d20310010589a840703541106d4050003900480f81400070401a43c109140146207000ca4070810784040e40020240c030428124202e100e43c0700390010802500070086501060281c2c1d041d40c0c0008171440c1096000d00c0341c800140c841c00400d4808034405c0d00042520300300444c1c01445580014103692007242042c0030b400d903014001c440c0038246c42100028a500351307600d60041c1d90070b1191911803800e940c6031141406400398581d004014541c460000441a25038035003c01059001c1130310408101b0040e01034940482c40c0c04c5105501d8010040c09036410304a9040641c103c03422107070701903603540d03800040788600d040c640710b0310030f50000c0113200c81030070600c1307400c0410714a00990100a221080b000fa0740307840f81d10102e030301c140102d600605c4002546088030045030300e0051000100d01030403c002081010f140048103940a4544940c2003081d142d01d1502e40003186180340260030340d074002100e803240104007131100c0c030100356008124299070f03824101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 880293327 1250 880292077 880292111
    0x709031a0915010b07060e120c07090b060306010e04180213152310030b150d1812050a0507060c050418060b0d0f02120a050a140412031e050a 62
    0x850060015803030b0300010300520340c00350251a2a107400080006025406802d404d150940714244001781da80003050070350f01d6032000101e22042d146190030a004800400040c80701c2e0f400103403100350200b59201c00338242d90501d503114500d03d400110540c1c0400340305402042d076110f40700b11a40e102a4845804081006040c1c00d100003c000200c20b4602d0010f40300002d5007c3d61000003424030031115840c00307296080c443d400c8449926002801c400010814202100d01ca0780100c1440d1107039803c1948261035200c80705040b0b0745558100000b04130429081c102214641d201448010601c00240701d0100803910718480c82ca00300055441c1c041e80c0b81c0c14450b200e07130312130301c404241104241071040c03c2c08000c4c0c01c0f0007500c500c480c0705000403030030740e09000041010380601c4100388070001110040100c0348000760441809001021400c100040d035410194170340000c1154060301c450007134034851200c2c2c2d110358028403503180c0184461101c503c1e400c1c000d0040d03030b0040e5100032034140c4a0081c464199112 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 880294577 1250 880293327 880293343
    0x91306050702030301061b0f0b06030703060606030903090e150603130c030c05031c02120f0d0c02010f0e0109051207050703020a0303020604170a0c0609020112020d0e1606050d02030709031a09 84
    0x42402e0aa85081d51f503034a05864034113030002042160300c9d201245580d14200542d40240d60b0101d003e2100320344482e0020010700413000300b5000550000c200098801288400031300a60041d60b60401c16041c04040c0302d595840900302d00700c042d00000742c290104d8102c0c0d04883c0554031811840c2075852804d020989016080c03005844500300c0c60150043c4036400050102180340e45401c41616500c820000c0d00007070245240510880382003801c0c0451007a4103620854a81e403400320100b00030050011000d00302c812144005105501040b800b981c0502000c003d40100c0f84209d00b101c40e042c3e1603a000c10030450041d0300440160780702006000403c5406491140c9010005075110700f46803028000034681d21031180042e040c2c56452080a0640e480b586209038500c21030b1806660721425480c00710014070f40248003050300d00440803044640c01c06c0c440c040e000c8640d29601e550600d496451040c00a6001410400a00804000c0000050405144d5400c0303081d001440d6282858804211780c10281ca0b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 880295827 1250 880294577 880294607
    0x1050105010f050a030509071a030f070e0a0b250c1d150105070501090602180315130b0c09041404030e01111e0325050f01020301050f09130605070203030106 69
    0x6030b828421019a408019202406001e10700480c50341c9541c40f1a908011103031b01700b911004460341c81d4642c0310800400842c0207040d04143d18140d075660880454203605401c0703900ba84040940020811402d112002d060300500d40402c01510307810090b15804542040a82144d51440b20304c010050010300e00e05002c101802d8444818051428080321002c4042010649051002c082140c00501400354840400b5a50001c8215501e140c01c801a02e001c01800c00018800d209400e1100c00401002d140746002c0e004441d0b44c480421144d6656070700c90780c0000c0c0540340a4200340101c0c0e12694807030240c0142d110447d00d0040d1242482e00b0010030101207140441d041c024003400303a04030b40b600000d106008217201ea441009000c41a58500e055200780080681c0c0e60700d42c24601400054900400005c21388240308880b54807030301410941c00c0c2d01091140d903500c640440b8039054a41800690307658001c40403003d2071624611581d5000460341d09481010050f8804001408001d400c440380d110070001d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 880297077 1250 880295827 880295837
    0x16030f0309021503090a1209050a080312060d02270a0b0405071e090f080f06181f06260f0a0503070602070309030f0f06060b0c0a0609020f0a0305010902030105010501 73
    0x312500801c0c0c210a40c0090035424000000c0081c1c8294400e005031b03400b0300c2d0312044800d0810070344100104800304c030b8043c041c41802104000500c1c400b0020480311b101a800c00380001c103070344400c00c02a448135180c80603600180c40452807038100b580d030740c1252001000d5280d028520b0811002e840115801c88007085e0280e8038000a103d0400d0b0815070046041102581c40c0b503110140150803600d40c501a8000042d0b00800e510100d903940001c40c4040d01d001050003150b80075034030b21202001002249403010840c1d0869403900c44541c03100720400b01e080c440395101083c116a5890b0440040044184210f120401041d00b9230a046d01448034a10f5100c14000400911010f40c40f2a6124803945c0c000800315031340000c0410405000c0c000d00b100070f64000750400403100c01c504080e0703044034036503d08450552502502180050340f0030151232191075010001c1006521a5031158014824460140da1081c0c8844641c0c8080d5103000c86c0780040d610800c008140354101c0d00c141825130340103803c5941440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 880298327 1250 880297077 880297091
    0x101106071103090904061b090512071d0a020403080a021b03010b030c0d0614090f0706090b030a05040c0b0d06081204051507031101050a0902100e0604090f020f16030f03 74
    0x20400106482c52010301300c0d084c510076165854603c0013040704504d616106050007214828858000d070340482190019070740b85040321808010144c4070b041600425001c030320920b01c00c8070280c101c000840e1b8818030003040189003944a4030380d150b158000403140e500507480302007441c081d0800c43d00c1900305490164000e100e00e000303520002c0c4d100e5028828090060440103580801d20140360840c009070301c95007140130b086051420410342c8502030a0182c4026100b940c0e4001a00c2c0c0c0309180140480d01000d10709400d6440b4104020041c010182c82a5604481d4000100701501e12200410f80c64180703907800501e041c41e01540500780305900c1c80d0010030f03080500c010001c94030745501141d40451180c040300d54074a0185802e9408079451006107503c0d62802c402c00121841d940e02c0f4050040c02280c40c00c0071380200c07000840b008160103c505070480380078001048034000c80d400548070513111020141c1000e07240301c94ad024580182381d980355401d0380e05844006150300040d8020343d203002c03860140640 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 880299577 1250 880298327 880298357
    0x2001170a020a0c1a061c08030103081b060c040801060e06030d0f1202030c0d1b0f12141303030e0a1101050306042705011d0a0b130210110607 62
    0x400041804400315000650310008a2042034040d441d00d501c0081d20303d0203c00ca0103511310980c030071610503024040091a03241070454032000c4814132944031490b50300d168250340d20410f01d0340002400141c8860040540ba03480d4500388243c6104900d500340440d03c1c3c500d0020303401e09441c82c543c8200300e12105035080c00030b162404120564018014141900d03c5400003008403600051200c91001240c40841841040c04250004000b03d03207284005004110315148081d00e03140800b1488000324082286820185000c9ca003008400c00741d030b00c40002c0554020100702c45444040306d80c220308020400443d01017641503c600040a40c02e10000d11200210f992280c202c0700d02c0440d980d05100c0040002100e941d21a0030103403507207420780064003081044650f56951074815000856042d4201000c0301d04076415521a281c1241e030240051010348216111102c030014050321034100c042c06902d4010158445c0c1b05085100c8107641e940d642e50f2652104801d007032010240c010703800c011580841d2842 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 880300827 1250 880299577 880299617
    0x60a020a0b0403230309070902121b1e031f03080d1e0e03070b07020610031704090e0a12050a20210c060a1b050d0e0601032001 56
    0x305a9104803041c4003601c440c20140c810320b64146440b1080d6400158403010700c01c00d03001850107004214211355a06841d810504140d000d202e507183c08014480000900c0007000080c400b05144010f2070946ca40507e80645501640030140b0035103980000005001031a0141c201e000c55035000c018104401505640e506107407071081c06007802c01e694440c2002c0d500c0c05405e90601ea0225601e0b08100807500f104181035450360400e03a0f041c1c03002030400380003446040c0042045807081440e0180c0220550650b92503c107420317103804400084000520001c40c0309042403003418a0140c203100140300300d42040ca003202c048118920344400b0000300740450000503400203070806044001c002a01206c7c54450030fa20f1421081c22a0318800143c003992a0520614440080c504041d010003925441c0c0c1d520300000e400c1c0c1d9030000348180c41c44100c3c410384080030f103c0c0000d0001c1c0000d90402107200e5040c202a03500e4094281c0043c0c8018030002d100681c4080c40080038008000300f0709190094880000720211 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 880302077 1250 880300827 880300843
    0x4060903170a17090c030a030e0907110304061407062408030c0a14010e070303030c0e0108090729070507090c080402030709230f0a05181b010e030327060a02 69
    0x3d06900803400700d8050f10301444034442014010301242c103403c50500f4020001c48a22004900500404010400c200c1c441c0166035a082d07049002980f62138a054401c0700c801104402c3e1140f0540f0503c43c060004149001c4d110198005040c411300d140e00040c00d1014a072085c0e4081d80d220780c030030001c1c060b2242c000315080f0700d41ea42140607130186520f10722209001d0401c040c003000d585d0248840100405d50190f03c403a82d18805903076505200c6000d0001510240010f0700d0103243c07a40200e00800085220300b407842140503000c8078a2101800da054190072542000c1e00844203600060000d004940040c81802c001d20b60900d000309084c1060f80229498a61070301448004541f10014090510303c2c1000305110380b1821030010380303949001004150841d03401e54920080300e0411001c18184c00c801e0000307481342c04034100907001030114404031602001100181c1c5040c880031105094032940c0500140c8026680981b03030b8400d030b103444845418401116525248a1303101404800c10007607000030041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 880303327 1250 880302077 880302107
    0x90c10021b09040f140f010b100215041703040c03032309093c1506040b0c01110c060f0609090c1e0604030c0f0e010303050f0306040b0604060903170a 66
    0xc640e64450341000300c103c654a00d00641955041c010b500e200d01710000795242c081203c0c030000c210b20210780040083c3c401e2503440000050303101e91084070f000110200116085849a007001071440400010308606810844064031001c40c008030420600d41c1081e9002c0a1000c264180303000e0480301c48100d0460b0041c21013083c000c00040e40020803051041d180b0080e0074044803280304a8280f80c48000c400c400780079052b10b600041d5100400c0403071240c0705250b800e90701c00412640c00c240c1810710004458004200e4507120359202d035041c02d0000700c420300808819078810007510180c078220340150070118000c1c020300c0c050210102088115030001c80c3d00b6092200c01c41c0e0314091280440a001200f0742003481160f03011000140000802180b07000c058200e650322104002d1060752404284460102440050045402000110381c4503103003000455004500400001c1c600c0a8030001c5003030f44d00b05410102c04603409000038028404070440d268039001c440503145107080c002c480014400040d882482e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 880304577 1250 880303327 880303339
    0x1060f061b0c090203010b25030e0613150807020f0f21040b03130c0b0313030e0d240f0605100318061e0b0102010221090f06090c10021b 60
    0x4581002082c150400080103032103070a42d01c0e035845450841681d4810104041c200d059140c45000281c03038525000d1590342c064803084019010030b0184a0700e070344503083d11400c80707001d00c101203140c00e009180741d00142c41d1607071070381e10502c2d19160291500b030301c244e903120f01c55100d024005036041d400549864a055040c3d0b0440c0c1132080e41800c0021409903030407030703d078414000c804c01a007203032503032400704074a40074035185900c3c2566401105031a2000351007120313070200c00000c8a004280540d8107100d501b4400362010b5440540f03a01c031006451312060422144034000100c59603201c59a00540030f86141d449410880149800d0010740e01d43d0407100c5440525403100001c1d21a94043c00020008603040007051044403800001104c014422000701c00e86a4904460b6403003952051080c1c030b240c1c0143d6080c40c80d0301c82d0a900c0c400420440204404010300c2000c1c00384501c050107100701801541d46000420040324a10101f04800b21014140c1c801c540c409074119005c1303054100c0e041c55005c000d0704c030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 880305827 1250 880304577 880304627
    0x717032b1a0906040c23180d200604090f0603023c041d030406020d031a011215080703050705040509060a0e010b04140f16020a060f0207020301050c030901060f06 71
    0x205541c01d4900e5101c0f00c110748107146481b82241c030081c1c000e2405003007c80600a0046035141040b00d0040d4511010704990313142801255400d2074212800340742c81c0020142410950f0f07640011094807203c0328501d0403152111010402c505007484040701c2890500c01121007a66414042c000d150034005100c0d09460006140031a281c495034400c10301c40101ca0100348400030b59980a983d2644144a00c1005102d4103007514580b910034441e5560812148c2c8081c0b104200c1e000045512100c0701342004c2405903500d00240c100303c40c0305141d03c000e204540103400314600e5401c00e40e0070954182d10040c000d41c01e290400800f00301c041451a800703d00104009083c40d10b80340010b004190120109401524113000b210b03080050a00c003034410038030040810000d90783c1c0c0381c014494440c540812009640040030b6030000035000c0d0030031541f070540b803140103003001003640009095076002e4a2094442e00c002080c89002c40c020f0094901402a012030004464640700004100019034918200b01d9a07802d02 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 880307077 1250 880305827 880305851
    0x9062c0705131a090c130909110d0516080d27060c030c0203150f13150b043e04080c0603061206070302030114120717032b1a090604 58
    0x110f2079410307002e007252516180a00c82002e4640c401004100161482c00d00003c404150b40940d110701a0320900385810b2060503c184011828600000c44440c05103a0901007040ca509102c50002e00c10300f00107000d42c0c00640405010302c00c031074246c0520000c031611940440300070155550100c4446240c660800328a40c00c0880d80c8889079140254103003da40b50009007140303850f0010b0300483c040010700996840f90040480380300e1080400a00030180401424102c1e2110f034040d40075418054404a0682180b5602440040000043c0c124450040190604000b2244000300b1001c0c05002080d103003504015040b03550341c00d000c0190f849504000005200ca0301e4251084203846040c000312145410b107440050040d4100b4080c92210b99141d00c42034038149020301503007040600840c06040da0504048880e2140c0c4d40d00c03601c0d8400340c8001c0061405985034222000d54400510240c012200b400450106c16507501c01301003265050351144044013030b80c451440b1600002c0c1100c3c0050025107001d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 880308327 1250 880307077 880307111
    0x3010312051204050c0117060a0e0a0609020f030f010e0c0d0203070507060f0519020a09090914070b03070e040b10080405070909050c09180a1509062c070513 69
    0x140b00200c1035181061000300000040d4900001d0802d07241c40c1002260f290002014142c202c85c61030340200d80c40000c000781100d0001c0d03a030b0006518980421032076281d4180c40143e9011021011800342e0000400c041e000340d00140c0c5000d0710600018a031181131034400084c40380905210305030f4a56000010a5004d030180302161505a80729405000d042d1511120f180282402c0742e001c203101c0c20b4030b02446039070031141c800c407407404070952651540c06003031501d154000d05185a088a50300801c1e018090750f50801c0100070b0040580700c5200c0d03601c1c900340d08001e0241d00c203400014001da040c0340844100d5134540071030206034442c51130b001b032080d0b6031800d00518040742940300c405c0d400c3c5003550000c14000045002210400181c6201d0301c90b407121515506000a110600100764004107890340002e0303000351400410110610001c1883c02030340d143e01d02100c0f5081c0c0700da125109900c11030304a290141102c2c0550f41040c40141003100c2c41d1101007002c0c881c064034000003480d40c440400000c9141d070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 880309577 1250 880308327 880308337
    0xe0303071e02031c39080603120f0a03240506090109030b1003031707091205101b180f0603020903070f0308031e0606070b0910090c050f0f060301031205 67
    0x400d902c440780001c1c0c0c1014600901340382030801030b4011992084454071009250004801c0340362004492907117070f4188119412030020306159810f00920280850ba81c032448040d0403803002c4003182641d00c0303102d6a0044c0031240b0552425511200c4011000246c0c82000314010488130281d400c16900e549010040b2140c0850f074200600e40e101402c02c3c000592010050101540e22130344498100302c8a08601031a0680200d41e901c0000361008000d003c034200d441603800c070f007610440485281c44195090013068841000c2e1091070060804505520036034401c031480540454003a9843c2c405040c0740d441c5035071007060b006843c14141c00180060254504010000080070ba980a180709292240ba01080d954419610b803850080c0c4040741c1e2021000d04181507000ea8001080c084c5000030580d2282000c1400034402c2c8140c2c041c80045010760103d50080c403d085200b1035600c4641424a02040b800304404400d0500810401580034a2602d44908032410b5a800ca42e14810902c1507000840c1c5034451 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 880310827 1250 880309577 880309597
    0x3020d0e07060203130e010e04060e0a080a030b100309110f0a050607050102040302180f0f060f0904230c030c130605060a09090b010509060d150b0a09090e0303071e0203 74
    0x3070150002911075011001d8120042910080c0c4200c9960f102d07000c51408013800340004411804022a00089841e0710840b43c00030001c0640c2d46c201500d88172130b01b044c0c008141d03400129488207880c2d038444c60400c840007129112070a00f00582d00340c98a400d10300d0034190710f12500801003419032003c1903540c00120070051070018030943da44da09524019002c0d422504c4101d01030924408440c414045001c5498401d00030410b809403182c0d1100b600501e40f60740600380507000422203420b501c1e284c45911105104600405800c0c00170848594401c80e401c1408900700100e811070205100305d960082a084d102c4042200d0b12007034001e034001020003d04942e03000d83d9006030000350440c942d981020f9110100c0311908001c000314405000159444c0c4224480d00c0c0d1700680c00c100400c180b29060340250300f021110318900708903a882d41240c2e4065440395024001180f076950080048150a001c1c81d06001c038076402850450418240140181201c4c1180107000e01e580c05a81c0c18a034420070607581c070703141 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 880312077 1250 880310827 880310833
    0xf040b070908010603050715050703020303070f0903170306010816091806080607080a14040803010b0d0603150b0a050d030e0904050114070507210e040c0201090f060b09100509010603020d0e 83
    0x203617a00e405644c9400310b208804141c1364030b0b000c0c2c0710310030700820607615000c1e010b030051440d66803044c0e412070340707852051900b40c00c0c000010f40110104a190001d046210010064180d03241841c070005059081c00810140c1030601e820b143c00c980f43d0748071134010203e928045100b41c004084190210242105070440802403007a50f0030440b00f203500015044c05080490030030000059071002c40390041d0340446000e015900b08100401124042e44001d066400c006000091400c0d12640d42421164500d00d100002036104e08030090300781b42801a2600500d4119200c42407000c442d0b4024181c5049006228811012000043d09009003908041c00c60480c8141c0450245001ca00c0506203070444d813800e4842d4900483c4580b07580c03c1c001d00d644081046c07902c1d076900090081c4100303c081c00080d8007890441d52614449000030710a10fa00c031440762700c10344e0040b922403260010b00200c1d490003802041c88601c2601c040103a91640761482d810b480c020315000d0795501030400500d01410042002407410f00c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 880313327 1250 880312077 880312079
    0x605031207050c33030708010e0a18030e0a090203042001020703060608061608190c0908070b1810050a03051b030901090b090708030409020d1404080405180f040b0709080106 76
    0x1020070390303030001100e02114003051300c218000742103440d001c2144c82001080c01c92005118091200c2e0501c0e0f44140490004240e84614103000c5d11200300c035410480108400314004515864070390052405060b98050842c254038181d22040404c51001c0750351020310080300c14a0415910038071100c0040c6800c0581400303000e03510f200c41580c410040319030189041802c0741d002c104620907040e880c001c01c40000b80483c0880c94a03c42e90090402031020014084114800114131000b0b1003c90000d0029065060300d40c0300080e0000c0008500040840c401c489440100f40910342000540b00300d201c0034a00040c03d9030725001010b401c05004044403d05003404410040d20a505404c102103c500c80c1920700107030780320700c01c400d40d8422060090604507041800180000e9087e980580003001f954400420a2140c054100c6d03442041990103480c2000002000d014904081e0620300f184100464114441c2c609101095601040a80010941c240344404640a08e12540b0103c1c06401c0441c0204949 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 880314577 1250 880313327 880313359
    0x170a03140f0a0c0314070e0a21060b0307030c0614090405040b460212040f050f03130909020d151d06040b0c1b032b0605031207050c 58
    0x1c84022201c41c00014280542845018483c0c040c901d1480042c4000b000c00f602d4a40064641d0980354041c4c81c3c1151007040300007280e80c0403509130714072005410f84818504c1702a007050010344415866841c080e500011003040040c5035001c00c4030490354145402034070b481d0640c102503a0380c400c160011f50300170308081c140310078000b103446418021031005140018500c1d00a041d80c5164600009800300c07082030310740c00e80889d043e84c0d03402c540c1d810702c1c1c0d0001464201a4803040203801c40aa07010b6036250001d1a2042c1002001c1160000c0000c0e907400460803c0501c911540d500840c601640031150340303070480320003151200401100c0ba1035003c0c403030203001c0c600710f1b071900014007200c02024a00d02c4034058040a20b000495090701841c3c1020a1144a030344121202101e0391210500e03511082d40d0b03c15044a90705c040c0050a284060218007103082c24500c4840c0030100c00c0038079a071805c00d02c0c0c107008100c0e5980004041281c2440d030310055450701414113040d801d0410400c0155000a00d10390a0066 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 880315827 1250 880314577 880314601
    0xf2d0f01050a060501110705010f0509030a021503060307090b0a031104020c011103060a0603020c06060906030a053a1e0c0602031302100512130c050d050c0f01020a170a0314 76
    0x6070382c0c082e6a100c610001401b1080ea81e10302507ca240d011502c4019540c1c02a4456030081c80e04420140803070304034040350781c0401c0c0e21300090000c2e509007560100500c650b13854103004920003804041010302505440e01d000400340900791000802013002d40c0242c04230b548881d0140c0310101c04101c000c1048448219140d40140d00454003030740324440400c070200c0e000e03000f40300f510440d0401c0c0c40240103642c1c0d0003060010140024040c90751520810440400081c010408030990b040c1200080c038111030070307810042c4040c0a041034400c14060007800c450080354000c13202c07007524041444081038071201070070550340340e040501c1c0070348060700010402c91030846011445c0c4a0034425600550655604442180d6030b01030b2490050702400100040399815191540408800e401040d0203500780b5541c00003e02e500f0304007041200c8940096189900915101350f08001a2000780060f21040500d59120060030502481c81c401d15100441d19400c420300c83d510030803e000300a00e07442d03440e003444810285 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 880317077 1250 880315827 880315829
    0x80d090302030708010903090e04020f030307060b04050f0f0a0c0e0d11130b090c0f210a110a0f03020c0304080d020f19020d03080402040b06041401020f2d0f01050a06 73
    0x1010f440381c1000024001130510900d0000c0b0381558507210004e0030070300085207412001e031080e03034014400159290707159401e00040c403801d449101e000030b10002e1f2106000550303a0081030424182c1094041010b19600801c41d164801c120020000c0c3c0c031260801c1c207448860400c21095000208980c110080050a105941381c4c28001c944540841d013026203044195848141c0042c2c008140e0070109412030354000c050940c0f920f603910418241003c0030800c5060a40984070098500240e1051103141d0400d403142c2d51018420942c00d5240151941c0b0180407503c4500499003055400141150410810706c1614042d0281b44292910000e440c48020b5484002001582442c003810120070382440050310a4885a9405045031040160b00c0d141076891040c0240280d0b0029140c0c5c3c1d2115070342d601c2c14010400303042d6400030b51b01d0100c84900020314ac020904103152040d40101480041e82917078034482104c80d2080100c0340c0e80c020400442030b0401d009440c02e50303155070030041441807005032600500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 880318327 1250 880317077 880317079
    0x504080609010c0e1002070506070b0f100302030309100e0901060309051b010918020d1d0c0114030a0b0d05010c03320123031605180405120d06080d090302 68
    0x80a41d01c0e611003032400c035084101a5800b040510300303200083c0c100b0b2003280c10504c4d40c50050b0b07402141c0c0e4602140e4250301280c0100d55001d400b804020701b00145680464201c1c4542c940040304900316800b0a549214001009201740c6407a0300040140f0f106500c0794a111ba4050151281941c2d25207018029044886048520340901070601504000014540b02d02c620160740d800c00042c0b60006074400080034850400750305808000d40d02c0c42554a0242c1c2e910074104410322030f8480d000320342d07182c04c1a03a1803240178100311180d94107020400c181d0058036001126003a0001d200d030904400a01c0800320944018001c2d400c01c9000b0342c0c090780680c08952098031066090b141c21101c07512240c0901007201c0405100c1c4a030200501000780d800e030503c20102d0112990078404c07002180028500001452130414140c11540180036504000030f034042c2e80040c00e0308080c002e0906075240b6071078825101d038090b0600008146d89070740210071340110000301441000e603500b821003214000c01c031121600080e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 880319577 1250 880318327 880318333
    0x15080609012009010f05040801020a0215060a1208090a080a0606050f060412060e01020c0304030510060b21090c0901080d090b040f0b1602120d1e0e0405040510050106050408 76
    0x10482c110049035200075455100c4003061a110054005403900f042080c070300410000240000306170848248000c00078040e0381e4008140c0e4800c207464032510728000820890290104c1d41c0100044a4411000d20742c0350341c400201038440300311002041d03040e002d80d80007060500c41e00d02c00900740003960380050150b8000303440501403110395005000700c6100310700c1a05030795941c8065136008985194411340102d841c0100161402d8150248075113036800c5a00240c0ba00c1d0000001d03001c00c0d45039445280700500e0304000705810001d01503000d4440e0165040c40803103091380d42000071403035001401400503010008007140407a58407610b0042d070741e9080e42651000700e49000b0000ca102200c80c41503404591140d50f0514440b81003508070209074000c5a40800080c0ac01c0003076000680e611130b80b035801d1054040003407410404150b0000d14900b00b400b02c040700007000080c0b00510700c0e440b8000328807410003510042055183e500d8154a004151803040107541c0c6084c00120754980d01c80003d10450341c540d011 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 880320827 1250 880319577 880319591
    0x20d15030c0e250c020d08040b0a030612030c2d2d02031902030c0402041502060c0f030f060d05010903030606021203220c0e010e010510020a030e0906041508060901 72
    0x1142c00c404000301d0f2074959030903224840c01188500b64010504d0b2000d000303442440810713030710040c00e90000d030000d4013810008568851285d81c1403160700018442c503103003515600f507141c4000c7c042e0024200046c2108052101a0810000a0301c40072900c0304115811741541880c0e081900804003000c9062400f800340c010b0a100d04000c440c07006400e10380040281001140310400c0c0709055513060400c0384c26000d900e440344841d55462005e44020600c050b0750006035100090001c6c14180e004001c8898042d0501484044c4484041a40c0d440312403001c81c103101c0d45660f0000740090314040402070a542c24030842c401010382c550886c00c1140d03d40c0d000c031500e40408100c4412540000c407101030601f100e040941543d210001621803100e400344514a0100e0703214142503461032307400d80140248a2554004110354204200160304a0056201070300c101201c50f83d00402040705455514411003014011494982d13690b800303800f0315568000181a92590f0703c20450301c5820807203420031907501e0100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 880322077 1250 880320827 880320841
    0x309170a0c08010b15030a0f02070b04020102010c1e030510030206071220030f0714070909030e01050c0d0e0a1203030f060b1e03091e0f0f01021309020d15030c0e 71
    0x3d5510a04004045d13601291681e0110b08682c0c10041062500c15150458047d80c284c079440201031513801090310040d1440d160001a0a6400300c22091040207044140201079902000c3d00c02c403c420310749008100c90701e0320070600c0703c01001900023030740c040000100e00d801c000244480e056424a40d440c2c02d59074482c240c840b544a0140c0c091310300c405030410010142c01d000200002e00c1340b6442107858030388001240c00c00ea031901c05190002c1142c10f80d29855502410b07004400608c00b0070003460310518002894180c80d40343c42558200340240309180c00c200c0896650b90142001400c6c0b041c0f00085c6010b1a4100200070304004100310101e80c6c545040890048a100300705d40030355a405030000c3d40d051409407203803070b0740d400181590054000e02d43c42050007080740024000c0c0a124100828034403003690081801c0000c01e01400032141c7c410809151144c0704c1c0301004089500f071a00050325900200072400141584084001310004000c0021082000403002d91040e50002d0754004040d654650b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 880323327 1250 880322077 880322081
    0x9051c0c03110706121e0e07060e0f060a03200f13080106050a03080307050903030307080901051807172416020a0b06090402040f06080c0423130309170a0c0801 70
    0x302a4100294550b17181402600980e0010704800611582c443c90f840741000c3c0e20421035006654050341c82d006208104600350f8491845100710804403040e001044158001941343e100b41c0110905241c0c9601e08143d44c030000c4408000d00e404162500c90f616502d00c1c01c014401c0c2c0c840c03104009107460355100481c000740c1c1482590b0036900040c000203945030454441d6025500000c2c41c66007042420840c603800c40c0c0f401d06c080c42c000c40c19900c45000c182805d000c0c003403d4900092034850001c01c25043d0034440080050481c1c200c84031025402d829649080c0e025040000183c1d8807032403807111001a4200e40440d0050342d100340f400c01d20f40f61031204607004c01c0342c985c0310720b19000c0d01c050003040104130340f490244031082d00144010030000d00c40608a4040c0103640741948008070700c6c0c0050b1802050382c2010700038480c14036143c407007284000c88100040009200b01034142480030000ca241c4108040c041c1d503000000d00000030f042c400c0c0030f41004440d03940e5006c1d040110b405c81c0d080000050491414 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 880324577 1250 880323327 880323329
    0x609120212041505131d041a1003060c020309042309030720120d020105041e021c0201030b1804052e0b04061512060503030a050d09051c0c031107 64
    0x14021421065001c0801300d40903000040f12541356030702407000040d4011503c400e141d0305c0c4504c3c1228801d5203068248824011040c013158071400420108018000c40e10b04d0710700080d6584134400048885507403904a1950242d01d9000e5007061401c005111105009085011110300c1000705441503a03403800c5454480c0a50400101000c03090a10711043c1c8904490140c0245005046418810718403408a860807281d9007030840982d5640c0240014410703c4500403003a14090003c424808000d50b001c070340c00b12034540402042900b44030340103003103a100b03801c00c00701d480004202050b41100d050303180500d508291021166441114a8103888040c0c00c20f0744e200d4003000c100b00102c04556400d1b40c1c0301401d10940031946c0a607480310041421000c00c1c0200c000b441d0690744100305642c00700c0604046609603000f80b4403c0e80700b03000600d0121340c4a811107481c500c804078040391000a52409a10b010024290b055002d2030360700c002c11440741d009030246d925501a075a541c90080c010f9804644503d09 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 880325827 1250 880324577 880324589
    0x9030c06010e041b15030c050c0d03051302040212180c010f05090301060b0c0304061209020d29242b0507091a190509010e090307060912021204 63
    0x35000400c090b898007000c096000b4003d00304c0903030b48412410010514021504640c403034801c400c64100d003141e45846140105d08035810658500700c0400030041c0d40300d0000d4840801c254807440064008040e0450a096040e8003403c01c0d5100d282400030360320354801c00c4546070030f4640034070074006903560001005410b081e0103841d04a18807a209800700d074254480410540c0640d25640e00080c071311201c00c01000d6010510b0007941d21282021402401c0341c103103503034000c0c4460800c558100583e44409483d0700580d84282d190324a82480c0c1035440301c40ca1003c04076142001650204250000f889018900f81e0384011541003690329261300f0081e03005101202d001c0c2450079091340030140c14078411500a07941c00f0700308460040d65210360b20020340340b04200140c030b444100034810340142408003900a520f41c1101101c410785050901064405c18148214a210036400d0040780034104180201e568440d0021800e01000c926030800700c02c4243d1601d40305005116240504040418031001c0c4e80540326 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 880327077 1250 880325827 880325833
    0x2503020f101107140313090c143f0a05060405061c03030510030506010b09090907081009150504030305010e0106050a2007171c030b0d150f0f0e0609030c 67
    0x40c0c50303120b60301300042182e000d680600c400c001386c1305040c0404160800400d800c0718041100d9400420040207102c039050510000f42090180d02c02602000c02d5810708420390074055421020100d2811004d204822101035a02c01c001c1d0030320585210580000e4460002584d00388207a4543d0020302840f0540c81601c41c1c09001401001d42c0028400c4d0041d60b088504030305e0620125459803141801c048e400e9102ea60800d10024200300b031f074280080030b0340c0d01501d09000f0b01009860030300100d488644003511304d4011581c40051404100310000f03800200c450202040110b86020b00c1c0140c01080280102c0c510b0349001c10001501034407601c2101c01c3e491407550b07540031010940c00001d00804d0b41301a004050301403441c1c081440d07500103010422402c9081f0040c01c140200042c50340076a100116080101400d1441c1d01000d511418140709400d580440398401491600602c9402040f060a56445c002d0420400703078010205900708440344a400001c3c0d0311140c07a10096113540784110040a02d80c0e070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 880328327 1250 880327077 880327087
    0x108070f14190f08010906050c12041e1505040c091e0203060301060e160f260702070503060a0f060f0f0e18060708091501050a0b2503020f1011 63
    0x1060203a55000800e0141c2050390909442d10f2444102102540024030180e5541c101042841102d004031508141d100061624112441003100c1031510000c1c80608082030040c8121102c0050102254146410010102200c00d408891201400050390191800300c2d1900c070100d68440d0038400e40c11518103048050100440d000f1850001e50401070030203515559485001985041603a10f2900c1890b415010b0a210120b111001d0700e103100d02c400c10010460441000300120510020f0710754680d201c803003036010741c0d5a6920308a103441c007035400c146d805001c0e42080c0b0100200a03000420f4400c80b2010a20045486803000c6291400900c184508104a40c904100700300e01d90a4498129a20180c00160002e68078038103458008240c407000c0000381440c1c100000003409101e1707180b405843c4008031255514090000f910131815000d00c41120300001050707044100d02c8413450207150888489801c0b04466030030048c1d15484040e02c00b080d5130044ea592000390b04828481c6a08401003440c01509003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 880329577 1250 880328327 880328329
    0x160f0f0503061c06020412030909020a080c280521060906151909031109131b0315050a0c0903200103110d0f1d1b15120108070f14 57
    0x4051029503992484820f41107030340c0403030442d00041c0007610000c207020040ea81c091030000c02145165001d90401031041c050007040076403160645d41c1018045071002d455108009120114200d55584283e03078000040b80f0011040c0c0044c00360140e8a10820500e4124074030407410495000115103580d0311042c072000084d00c6260541844080240480b11107041100241001209100c41c08131000400c0c4040010020440302800d2840982d0702074440c0384040c01d08101c0e2114031040014000c268100720b14080000307080324508040119001001b8074000b5101d03556010040c0425100c02402a0900002c6507100b40240054030443e41c2c06220b5441c1c900001c180014061552542d02e0304040d210813500c80b00c28005005850440c1e0582000104504008808070482e00640103e00c05a00180800c8a50000100c1c01e1001c1e15084802012010007038000035420910050f29203440039008a61001301b00d291030102410f0300c46440031241c01580b2164013906038403a9102d00e900c003140c400400f01c51 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 880330827 1250 880329577 880329589
    0x31704030507050717190f0320010c0302070b0906010302180411130b0405330319050f210409021606230604060e0103020114090603160f0f050306 64
    0x4400c0c0245845402c2c0304982d42c8442c24110150f1140d5000000100d801400a906210302c428201c5d401c181e891807a0026038924182c056504009028483d03107034504d00c515078a080c00181c080c45914002c109640541101400941101c8401d4590581d808000340900000041850680742c0041611070315500000070814011002001281c0314002e83c4000340b0103444152841c86041000d0002040281180b400c0c4022940c00500c03011881440c404003a406010014101300103560700da01c804050741101000c6898461104407000e026070a0300c407070a046c07080104001344c0c0035543d10155510307100070044074010f80348101007112041030100410000c20041d0750007010016620411800242115102d6104540c084100d1840f626501000c5e03140305408090100da0240301140c0400059090540d07292810005000003818000446103018404901c1001c0e0368050030028891079a1340303410500d180c0100c20b03950401c00030507200c5040020882c080e0500040d501c06982e146402c61f031300c3d4820080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 880332077 1250 880330827 880330831
    0x3070b030108030d0f05040c0513230403030e06150d390b040501080f220605070905061608030c040f0906150f020d030b0f030a0804080c3c03010213030b06030a0317 72
    0x540c0da17640c1c001002d0312f685640c5031206001000625440c2520341414068203a5410f4001c900007a00900100180c00b96454000034410341c0503100e50000703018030f14141000e02420030002105658040e201070600c4c005c0721044e02c00c00207400f00080c01c259140055040b500840c0201800b141c3c00c0400603880a08210449030300400704c4140e618007609050110710201007075007050340c49541f09c00c00c000d07105d500440200000c01d401d4404038541010751070306003031000b200ca40040004d000080403541c03606541042e100a42044e805070010107030b981440900078482c034401d10480c8011a4091201c0c1030050f501d0030750740621038015107d10100c2d404214001c00601d560203601074100d88609110f61001c000d122480e921075158142c0e21070030205103914010210004a10034400000d0f0702d100411011000388a00c410303030203507803c4510a40c03201909200301030041034140d8230200780140d200e0000710222048a0040510f502141c0350394040c1a2036650040010780458003001d80c400000b0749414042d5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 880333327 1250 880332077 880332109
    0x515070803041a1501020d0f02070b0c0115060e01030f02040b071212021206120604030f05030c0f07030e0a05010302031e04050a0c120b0a0c091403070b030108030d0f05040c05 77
    0x10400343d00304400d00a2650050390407140001d5003100c00c4445513010408151b01561606080001184030740000b0758500c0d05003c0d0203d00c0c000840c0007211190309400407800d4856103202d01007541d1301d809000381035440083c2c1d21400242003950245884101d4800c4609940703207410002e103050701580791100c0c04059501e401d01003011a1100124041d842d1010302800b03c4003000078036940c03d02c40208405040454003040580d00280c00f0f01c800070381c0102c500c00407c0e582d0700b8000c1d1640d540981c00d60f840c1c003415003403c070b4904c0001020801c155011a242c5445441142d115500d00e07207840c01107040b400129540940100d400d20030344076071041d580d5050ba00501c140200c607020040d60ba181c030840c00045c0c0c028401c00c59003544003001c02a100012607400640c80c0c80401c040380c8458002040e880c120b1050040a48240c0c103040d06039101446185c1c06085004841039681d40c0da103503002d07520750003811030246442c0740c40a40b51284411303001da0382c0910b40082c1c44000d21410700d0104a0a1101c41c4403903 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 880334577 1250 880333327 880333343
    0xd02010516051603060b0a0e040213061a0d0e0604050d05130f03081b0d2307060c020f010b0f060304060b060c010e0d1d0307030b060a210c051507080304 67
    0x40c01c0011070400c20980c0f074440c400624891103103507103024015a140c00402c02c0c81903003101c109000141ea2250080d901c1364044a42450072079900c04454010319150b045051041200d00b122980031080703400070040012150303803c1002884200d5400d868400c142e174010031f036421868800ca00a88980064100c2400ba002800c00541d502d1041100c00c903910350044655040110341032008400e4045880d0525062034044e04a4282003c0700410380c624140103091a440c841c0c9000380d80e60380b100140d81d00241c0c000001c0044400d4804040c2d516010740d4030781e404640c01d018442e80c1c1750900c000740c8101d001c009031095055446958802000e00907035000c0310780240c414050b0800801c0240504100041110017a20584a0340e10008101d110445441e4040044840180300d8a480c001140002c0300d803ca0080b21460700da000000d4440203441c1d000d03081411101c2d6a08601d4402c0c0e08607216031074840d080d20800c0664440a0003030a1031485150b942440003404880c010800304070055600c5442180d40b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 880335827 1250 880334577 880334617
    0xa15080406200309010f06080321130209091c0215010e070e03070b0c070b040b030723180f0d0302070e04020114030c0d050604050c0901050f040509041401060609050d020105 76
    0x318403030a40080700c0515041c0e4446d1388040c0c102282e0301c0343e8400340c40303030501071468040841740b02c0c41248031071162036444141c0b00d40020b0b1075180d0015054407459006246611508001d241d0039512180b41e102e18800045989802d441c2e00e00000b914074810981c421010040d07031070541e060101d40c500520b00380034001402c40798051aa8180a07810207001074141e5607484031380c00668145011040d401210040380100000c1c4815529881901d80c03040d024540001450540305440c1d05d0800040400100220042400c02078490301e80507480c4000e009403080d00c12405d80ea800c105000c0e150110280c0940c01c40300042c05540154405154001d0060414034503030610b40050200c02c0c0e004980000d0b2240c40030407103141c800b00398040d4070f400c090122820712035410200b1300420948108298541440b50004a02d004683e0940c281d50041100070240642ea180900b098140604007155070403240d40b9005002c0b421501800210b0305581c8050071080d01340c041a401594143c2c0242c07900ca980c4600a10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 880337077 1250 880335827 880335881
    0x108130f0515070c261b070f090e281202070506072a06080a1a040e0f15040b01121416151418060d06140a15080406 51
    0x24001d010b45001c2d40d80100c0414503003800e021100180b0007082c5030754005c19401e058034440c40162011440320303090142030074001c0589145005140d5020003000d0014400010781131086600540c0b2284920090b20020090f4402c42d10b00402074548100c0101e841d0a81c020200b110491100d009082c503004460345503850320009010b54100075812146221625180e0000c80c1d030f0303024809200712032605000000ca040901c09800c8400041800c004280d40d45442c00c8404624000714285d404041c004105207601001d030382e0345a02f18046611035502c1180d039120b00c1030980380442d62146030461100c620700d9091035032090845d500c0890503a0300038224541040081400e0242c8000b086951608044e11450b052141c0f40c000c05102402013031040315640c4414069111b0101c0d010f0817000c44a480180949000241c854005c03c4400c103003c0e03160800124814044007146850618121003952410399070f0305070001c15000700c4002e04002040e610118001401a0300001070b4514017002035145440140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 880338327 1250 880337077 880337113
    0xa0e040501020a0f020609060c09030127110a15050a1214040510020403150b01091e03061107121d28140303181309110307050108130f05 60
    0x25805865907540001c03400320083c4c001e4051100004540090071444c0b0704a5125a00c2c0c203002008251410340001d01c4004030f59081d03000c603203c0709852010301601d00c0c2421071168405c04203103080314400070341001c004681c50102c403c03400f150a00c000b201c043d02c0758260b0803100d0303800c11807940701841010301c0d1444c80c0c0d4000340210700341c031900d07e58004031070304c0c090810600e40f03501b9090285091f48100810720119144030607107451845080800b0443e2110800101e44800e17003540b1520103640c0c0a00902d41d180e50746a0000110b82c010081804400b82c0c0320740301d00e031074814208001c082e81000b0658a0303186000352864030015600d2050f040341d06400a000c1846104001200031410fa0b16801341d1105469019801e8042e0042c062080c410102c21404690f803403007100c5a0440c0410b015400c610140e83d4022a42c110101075081804030481c0c501c0c10003112010720555622a005a0001096035480f4150f8984240c8610310340c0e0384654230300d445800001c50002d005446900bc0c01c0c6800c00b18210308 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 880339577 1250 880338327 880338331
    0x3090405010915091109040b1f08070801050f06070605041505070c031205060a0e04060f0c120c030e1009050a020a060f080106030e070905090c0a1401030c0806130b0a0e 74
    0x21500201c0c0507101c0d2100000705103580e41010922900d005e01c400000c00070700307064404081d07095034000360148030000021a9011140a80c01464418a44200405500c0190140210a1919059407698070b071410040800c5440e05020307003000c400c0c400c02c0082000c5400054000f13004a040c0041d840280c20742d041a14801c85081010411a515060406510040302121052240303001c101a0034840700003107800708039100d40d00d20006813002103410311290f0ba1081003400011101041f07140080c25024010303094102110881e28a8205182072a502900407280c1c0510140c0c007601074000d0301111171004080e0300b50190748030f1052a21040c01621044400c0020348000d4507000c0300000020401445400140c00c03030010503040260a04100038001152800d5402d01300022030b0642d2950b08549c644500039942681c80800700760009a000141111800caa9034280d070305001446201c6010384441034207540c843d03080404040703e00d07004050340d801400d00a000030900e146840d90380403088020703c41 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 880340827 1250 880339577 880339589
    0x60b0607060e010209031504020a062601030b04020f06031b0a09030f060234080a030f18020111010b0604050f01111e0712030f030e0111040f031106190e030309040501 73
    0xc0090344030054031b000c011200340035140702032019551a256011425001d51807180b1020300ca071040701041a54645c0c2c1d1080854256500e225000e0f40e52414602c24601c4180d800b6406110288030b171088a04041d000c031780c0300f00f6091134400c49245140c40c07076038810740c40706040d2010019000d0000c00000c0e40f48920008a40c041c00025031100007410024401900c11404030700c00c03161070b0400700c07801c800e0000308a0350030b5081700d0b413079844040a0301d007034000e402d410704040084c600d040100d184402942c465110018000c0c0d0351031a917184e00448003822101c0083c0b1907036121400f40402c10480ca40b00090601d0b240741071400350040070f2482d21951034440700400741e2410780f110166a4208030800c00105d030081104a038100448242a00c01412103543e481c030100400da1141071071030801e4805d401c240c0012003210b19846ea50f039039030f84002403408824001110f907110107400c508031341d151210581e88402c0c0b0700000428032200030002034600c0130342c01c002c080c0c140c0030030301174801c07550340e0342c0b10303148c02005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 880342077 1250 880340827 880340831
    0xc040911030606030a0c0e061912050c06090f062a0a05010b0a030206090415051e030114010806280c1101050a110f07210e150a020604060b0607060e01 66
    0x5610420103050120083c5840c0c000c1c0c0c09103d2100c040b480c401c2c42d0a0483c1d4252102c400643c0307501e4089800710300d1080032450031000b0f40c000081d03000c00c03001500c002c89018509640f0440120010083d0302d20031040c2c81648800c14003052416440d00c10b0052464443c00d40b9004180c0800c65001908510b10040c4020580c02c810405014001d0a004580a800007260340b079404a04513400140c2130b016040c1c1941c01107a880d0240381491080000440140400030004a01c04030b000015540032640004a98065400e101d06004440e480e03075040c5041e02c2c500b501a001595400e04019580300404a400f80308601b40344440000c2542c2d441070309601c0b03c0341d5907280c0310684081e10407801c1d01c40150400009526110010807a2410341c010703100c1f084501803695a44c6c680d10b041000b00f2000a01140011402d1884a007111941010369400c8012098030605110040300c40c0c0e1141d14020340f10b0b40005a00720400182c001016907010900b0f0320300080045050060ba92203442c11a40820360031115a9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 880343327 1250 880342077 880342103
    0x1080c0a14070204140609070201020c0615030c0306091b0411040501112b0305090c01120c02010204180510050901080307060b0d211806050706050717240607031e020c0409 75
    0x821f000d004254410704600007527150070a000c8040307590b95401000c84c08000c1014414070300fa640c09010450300d2200c001c00325101401d145090a03101c546680000c006003448044010f4030b81450b014140301031400b9802903080c0b903e404010346a01c201d0490000560061801d50001000c40c0e07109001d1440100103002c440c041d20f101302a049803005013103424070394802000580d881e80d01c55000102400c948070f000c80c107900c0001c8141e01901503500042d04070b208402012510380c00b1a8000b6109003200c3c1d83c1e106a2503a00e07420311881260a00038444550800c20407000400c1d031a0b0012065904090b1801a0000964845a0008101062140604443c0403042005c01c0d40319a845000c00703401d00c0010300321480c001d405002032246d510002d1055803503e0008918900801800e01d4542c50319042450034500740b810381c002090500c1c1c1d400106803819606203a41d0500d101074881041e4582c036925011901c40e025510301c4203020600004601ca5260100040d132920701845400510071070880c0d40300c4d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 880344577 1250 880343327 880343329
    0xc050d0f0b18062818110916031104090c081509060f19120c0602060c070c05061629010b070b0f0c0c120306030c01080c0a140702041406 60
    0xa007102811110784060050303a1841c0154020649640012201c039000041d100c0d10781da4000c5800102d1103400b22545001015241004d5044a414609101e8000c2e24440802c0d2020402c1c02801074401c00f011095840602541034000c1d8403000301440303440146c034101a03a450740d01c2c082e01c03021842000040c7c440f40078440d1040481c1201004028116054209440d149000c12142c0d41c1ca6000c40b48a13144a03840030b0030741c1e4020401c48028180c4c8912003d0310704900d05201d44141030600c140c4006110b8000000e074440c280c081600d0712580c2c019410500c95240008014590300180304905d080d5082c5840c1500240f492a2050b00349220f15415101c0d140c0141401407035040144c0c05144c04107001c202c4580015004072242e40d208000c0d0b280d00c4002d4072549280d0100b8050f6456600382480307110124042e246400d4061403181c90103e0844020720320210044810203000d8519554921b42444891390060241401c00c0100c400351800758141151a000107050343d510988200c2d800b003006040c0070007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 880345827 1250 880344577 880344593
    0x1d09030c1e070312170f070219020a0306051006080f010b0d0e031603032414060c190b0f150a0614070c03080a0e10021b0a08161401031a0402070c050d0f 67
    0x20002600302c0d030214500c1c07c00d002a456000001170502c01320340d02e03a8102c0c02c40d038407491441d02464004000300028540840c46841240c41d600800000c6241140082c8120020b004654180c0f160b140d00307035083c03032140c100c0c07500a003002c941c0d080c1f2240030900a0402081002145c00e160900039030740410341e50b1014001e2100e0510186003100c21900c000744c240b100d09030f814520030760f201082d91f0b81555045c04a070802c0c100003c0210307054140d45245220820300c081d07015040c0c0035030b0840380c0c9084c16850301c212030b0751040e800706c1d44507401a00030402040068015031107041c0340000c0810480c80d09403140e841c4161540c10390000c56018401150810030150b011360010a040c02c16035180e030302500780100103540c0d610b4284d200c00e684075807400c0d0100e240e12007038282c00081a9140450754041d0426144c1a00200c0034040c420841080850b0040345622030f005020b026200313a0f6000e000e07030745010300f4440a0f5025102c240e4500420750b00020f82e60b1190001045664012030124403104100c0c900b4181d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 880347077 1250 880345827 880345831
    0x1e0b07020115140105040527150a170a0b0a0b06220b0310120203030904020a0210050906010506071e120c050114040b010e0604090c1d09030c1e07031217 67
    0x5002041000292060345c004080b20b060300c008031070307800d44201d0b84c004194412943c803003504110b00781e203010f1001c00c1002081040d4407070700071a1045261a211885d800040c0c44549103200a83d05c80401c041c04541c0e890096500145200c2700420920280b0002c03030041e030300034241c41c010903511000f048292400540c212014202c400c40d41031460401c007103110001c406500400c9045441c0581041c1195410401c4440e2040042c1003991250070300c08020303454090841c07040344041d0078040002d05850001c50024180c0d0b1004101ca4188402c5071901280c01400c50100c00d101d00003211004041a0303071030333603d00314408aa07480040702440b03894502c5c291b4060300c0b44a020b0500c54414480042c00600c0c01358150b8031b03801b035071203200e1f0b0310140080d0290030045409419561000000301c0d40a41c0e110f41400320425070f080042c515110844015a00c0c410780203d216142c000060300d06003d9a01c086042c0e03201c482d00119000d150f100e4031900c444011400e0400041880c600f22000c507540e00008840d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 880348327 1250 880347077 880347089
    0x30c11191b15050c1f06090b041103160306080f0106061b0f0f0501200c07140a210b190f020a0c0b070c0506041a130f1e0b07020115 58
    0x7400140c601001948004001c080041c18000c001c00c800452080800617440d0a2000000c0c0007030668820203804c1c002c00b200d008801031641401c104100c40d041030700800514691800105207140e031394654042050301c10060780420552100d10002742d140c01008a4828916120f000246462070404003030440c40e0140c0c1a007140c44ca0400041e008a1421032100302810742088241610003000d02d4a00d0042110f00040254030b180040010000c02e500806003124103580c408070f81003d500d0301ca000071502e1700e8407412640000c2488060001c000c00d180c58606028a40803c4012002980d03908500c209080f80e43c02000303209542120f210740c45034042ca24080280910031440c210042c080100a0040d007140940495000720100e0506807040c3d40c02c000f8070343c00034281d41050500b40f508400d01002da080c21481e42c401d64010031120420020402d0700198043c86400d142503141c1d503107034040c2c2c90110700c00e1841c0408180d0400401e643c407030030502c2140c50b60b0002030400b06880e01c07541e01d03c100c1d42040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 880349577 1250 880348327 880348373
    0x1021201050a060807030522030309141b040b0a120303020309070b0304021f110304030507030209070e0d120219110306090601140d020609180f090105070807030c1119 73
    0xf00680c40e00080060f400c0b00c580d140200e0b10f60340d180302c1849402404081d106044074118000400d1580c144e0101c0b0a80e1710407040d820080320030004603076643c07000365507869104d9400002189285403c0c0c0c0045000d042c06003400d0012980c580c61b140b20091690f6055010a80000820034814030078040305d406010a85410790460406801054240c407102545140c0c02c845900280e4003940a40e05c0e40a1220300c0c841100e54454807480c03c2600d5018600c0128021a040c001190400303002e03080554aa04001e40040201c14454803a000540350350043c040079401200074010000284405500c1514001c2c9a180b1264682c0814545820030091540c0e429401400040c0b00d0ba0400c84003c4010003c202c3d40c84d0355009541c00003600700c1c401d5225040e030040308011440501c0150400c402d110303000c1c0d901500090740e1810b0105090340e0007200c0e00030018124400150310b00b80a81c0c850240702d00549022280d01580c03c0030245003143c2651907400386413100740e90008220440d40d150fa45003c0420103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 880350827 1250 880349577 880349579
    0xd0c020301140c190c0312020d0915020a0e060306030c091504110405120a020603060f01170a1407030207261306081603090507030b070212030a1e0e07090510090e01021201050a 77
    0x10051031261a400300c00d007c19000180889441d44a0300031030403080c1c03c480060a0751001d030311030400230740c0b0210000c004910954000600b41c5400d4058a205a201030040c0c090a200541084804080202102000c09050062400365100d62240d20300303181c82c180000c0e0790380d400c2c582006034001c0c080c1c90800c0300303078041d90650006850307000c02d49030000e0f0103640b05d0b480060000016210801040c0200386442c140c0d008020303004080d038101c84080b070212806007031181c84104049041c0c0c440c01101030803403000350031141840c07507074080760310301c440c004050040c00c0c0010400b44030101426a48000c000842290a000c120192100140d004e0441ca0508100c058102d070743d8140c640d09a031102424040c981e100042c8458000e02421841c0d09645031034942e64a80b6078010002000160300d5440b00003800b0b20610700c3e4901e14420800c0126100000749201460b05844601525004152500502011000240c001014003c071801d07410090000b6807034424042500d5524501640304038881c25080784 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 880352077 1250 880350827 880350833
    0x20f030a11040c0908010f020301090e030310031122060f0603020702180c070c080105330f0303040f06080118020418050405150c0c0d02010e0d0c020301140c190c 71
    0x252480c1c00501c195000318400c07040e1a015a041415507202148a50800002600d0f0092560085040e03c034071820401031840401c00050392804100c503c0940000c0800081c00880c4003401c040c20601c0000300075a2300902644264019016182d4a844100703403290011b03c00b04400c03070241d03400345c00186411401c041603500081c0040c181c0f440010b15108000000c0380d41c0640107400c07903c20382c0d003101c100721100740c2c0c99141a0003400115120021043c13400714043c60a910f41c2503401480c0c0e07001080b08941e10440c010040d1039903202100c1541840704010002c0c01b1220100304c000100019116079000b980b400400d0b003010f05601c2c00c480c1e01140b04001c248000f04d240440c1000e840100500041c242d03960b4030b02203180059071904840a5541c0204100c4910001c2c4000d00040c00341806a41280c00c0100040e8203842000e903005003a45c002900420503c0d2240f0843e000860008001040e10350442403840c40d000c1040d50320f080520800540c1d03114445409a86800004075494131545440300c81e2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 880353327 1250 880352077 880352093
    0x503040c14130513060509030a0306060e0105030f09071716050f0a0b07030509030106150e03010b0a29030c0702011409090a02070f0c06031509090209360a020f030a 72
    0xb40400030625a00e102148500249042c01d01c68954018410421818510001540c80d00038014400c0008e04007032000c2000c038410301c56208000c07410385031981540ca80b030614541d42180102010018801c42c400020030405200c80342e8401c9408c0d0015040004401300684084407180d00820b0041001c0300c900041a200d00b21341c1b601300d540144a0a407202074902d81120301d480380b00e080552540c20f00300c000c60741d60b5070b2010500b001e00c410740301e007885c2c92542c10a150a03150071240d560f5005802c0360082103100c0c0b4402807105112a0114070214010745c101810a10350002e98690780c40e0f803004102c03007007103507042218502007a0080c070415042035083c00c0084c000e01001041d1207081600401c00c1020040c810b0340203004658411214601691510002001021081c18002003120032039000101d0011901c80e4845082e000b0f8200901c0343d44030314107408200c4501005c18642c1d180d6280305200c1940304007002c1a052403110113052020701c0741c0104500390342c0303810400c0d200ba000750001c0300001d0303113007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 880354577 1250 880353327 880353349
    0x10050a0e060c120603070b0a05030601030501060c052806020309060907060503040803011e03240f02040315051302031b04140f04020112060519030506090a05300a0503040c14 76
    0x43c100d8019070f900c83c000300713003000e14941c4500d04400d404680342d0b44c29600000a075104e01401e90b010491aa030310f1908075041045098054440d800100c42c00ca1008000e078801700c040301c480c0c030304a00d2200d40c13a99900101d80c0122065002c03908084140401c25006100a030001c001d40e262541c15800d268981c61450311040c070076202c3d003000d031100c0307c4100c0303003526810402550800480660205004420300f482d00b0b4003c1d842038018039001d00c41c1c2455505100740c03802d41e034228540003685035119025400420026002c3c880350425180075600581e000c1110356842100c0c40038405040800d80d0511065400f80c0d800c13554a950b5140800a400326003030b200325403254092a00c210110a03040d09800240256000503130012103480c100038070003460148030412244a0360884030281c2d1400e0200d5102c1112841c002c10a4120b030310707010b40d00d40d5409a102c90701040141c119200388204032003014140d200031244404140040300f00030a01c51b400291f04020090101107c0300040914002941d800c20 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 880355827 1250 880354577 880354597
    0x309150207050409060c0906031a010507080702120a0312061409061f020a050f19030503091207230a21120608010204030213020a05250510050a0e060c 66
    0x414a0820552003000140000d2030050010422006181484406486000e40d1003000c1801c00307400245070351103880b5a54000c900d80706d001c00003c04100044402d07601c100b80645d08107006010b40300140e50354029035040d0492143c01424440545e20b070251a904103c03429070025480c101c001c1100c00b0b202042c1d05400d10301112401e80c10b4ae1031074002813031030500d80e034a00c0101d016200001e0b60103800080001c402d5004904440e0800fa511029554a4110b500d02030540440504580006030142c005103801445800941d200800c0203460700840350030005e01521074059194070103502c441c00e0f10040c1550070200028042c00c421540f102c0301d51380c09141d034100c0700840091818000c1c5104001c0542d9043c41d60070b06001d41a90380c28502d001c1d401038042680700e104a01006040d100289c800c858002a83d03444050a107d0f030140d2030715800580c501c068804031440d5403642d00050041c03095460103681d0180001c2d65040c800302841c00c48180c4460050b01e540050148900b0301242e0090340c2403041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 880357077 1250 880355827 880355849
    0xd0c0c0501030b01051918172805010e0115080c010f050306060c250e070206010902090105040302091003110409022d06070b01030b0f06010c062c0105090f01090309 72
    0x712004a4041c401c1e04055644200144501c1541e19480340c1c1c09540010406415081f05458480241592a044c40c0c1c0c6e10096101c0c01e030401c0b20410b41002105603a50501c10000350200c291501800c5d07030310307100c95210640d40d103240c06190000e2082c52080509003113002024003003007010001c0c041ca0b10307482c0b1050074003c0c0840020284c1e81d139031040f42e80d80b0a4103026510341c500d00190f42a00b40e0008661440d1140f10340c480460700b25044203029100c2d081550051155034680480b48001758041607500781040b408100200150310f41460342c50294441c00075034450f60b869030030710130fa4000d844a0994030550401c8064005a0744104a0312180d61695007038400d11f002580b2800307800c947e054442d0b50404000714070328090082c4040303818101c0c1c0c0a20070405140c0d0703808001801103c801c0b80c1103804503110102ea400440d00d40d501081c400c2948240e98505502c80d081c07541220500c1001c9040140e44035000c20103611814420440078040100091003034035155034020b041c2e80403038003820011207 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 880358327 1250 880357077 880357091
    0x90501120b0a090e010506041113060c0c0b04080609010b010e150313050604141501030314030702160b0a020f03040506190e1507020111060702030d0b040906021b0d0c0c050103 77
    0x2645025141000f001c031000100101d2030b1091070310f4003074102142e40500c214a03008140c1c140360600300c00c454099642801c0c1c1c0621605066090740d20340c0054130191841d00084201244904141c4000e002811a0030000d14180c68541c02d009c4c00d40314030000d91810440c01c241566029150241d005000003003d04c0b02c1a140e645640b840300c440380c41c0c080003524070b120b000c0610050094000d5601c00c03014007507050f504003550b895085071051a0030320008000921842ba551800b020500241d5000006031041d01c100300e142c500c1a4021235500d0300102c0220b980056110402c5030100444501c054800307000e14100b03843c01c00080d4480c0070300e441c030329540a0b000c0450400d15100c2c00b000c0121240040c002408440d040e11004910740080b8012400b2894440c400c1c90846130008400707100740e0103603008502c1c00c03007001d070500064103800c0c1942d0f800548070045c490001d41035001030b144286131020b0700d00c0c804044004092411602500c80d10522440b02d0842c004590301000c4203040e0350080c00c004c00d100d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 880359577 1250 880358327 880358329
    0x90a0b01060c021201050408090a0b07080a0f02030702030a11210d18080d090302040f090f02040b0301090b0f0a05130c0623030a0b03070512032d0a02010615090501120b 74
    0x1300c0d807040c48044c6254642010041081111000340c8504002034840d00b00c02511000403502038400c030341003d407000405100c0420002d220b007107104040f8083e4810b40c1d040c0440c1d1340c007181c038041204504541a0a00b81451a800e003800c07003000c0c415100030031341440f000340350740da4441d11003040c4202142000442c0824026509040e1075580080c04a001200c02e01101c26000400304907050104a21450420300c214455008a004400400d60450600c28115603903a0800c4020030700451a0f43d01552220a00008141182c83e0385110744a0f9900c0319000c0d150840510b003c030342000341840b503031031210410380011418540510041d40c0580c10240c00c179120609030001142c3c2d0884c90b10011a500100700300c070404480d000540c40140a50840310740d07c2d298410018010383c80301850407280d0050050b00081c000792250b4080b071321103414180b112202c3c184100c020b01d0b80281c07142005030303446010401c850607484154035925005460682c54190500000800c8403d450700450020340e00e85a081c105 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 880360827 1250 880359577 880359589
    0x303080c0d1b050a0311070b06012d08060f15031303021501060c06060504111e220305060105060f12061315051503040203120d24030b090a0b01060c02 66
    0x4004010442e80c44580305000007805a8018550640001c2c00c0c03080100210324450107403000d00340e1005c15224199214401100c03c0d00b805003a1210401003000e802c0d1610843c0111075620603900e0391b030341c102c6141210600c004244601c0800c2d0040c6031280e0201240c0441009690f000794044030000d8a8a0960070202c2c5044e1201203e0034040384aa80002090794020703800e1903076144506010320800369240200003c8030300d41c404003d5075220803c000c200b500c402030502d81d1041018485541400041c0d1205048440000d0518551440c0c40c0418000e02c0300c10001c0900401040b104c9602d040c0c40d120851805001e1025060010004900420156034400b40307030b4014807100c0e040402c052281180c40d5014580d803172003413500139406010500340d1000071404683c4256000b80080401d03015085480e421644014104075003241c3e2503c010b001e5100e070b0000040020b42003018030341d0742400d508100c4010b00e400340080d911944800d03111000a28184c110070304680c058186140c800405001040e1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 880362077 1250 880360827 880360841
    0x2100c05150f07080c090f0103110315030609010b0d0206160f0506180304120b041707050601030c060203030720150412140406142a0c1005040303080c0d 67
    0x160300441849000c80071445895a1140d80e201c1d0484140380c8411005070390f10503040e550b1105802c400c01c004001c40c181390400340b41d00e00d818540003414442c08150030405810030f54820310180c4481310303081c03130f10b19040180e1f940020050b402004238074882d10000d85c446060380402030043d14007040325001006c41c42c0009030440c2d005030185082065a14000d0f0b203401080311580c01990b80b030b42c0003064402000081d0740030780301d00d103000e41049400d0351a03840c804d00f002072007107481c201101c80d0054212001d01c0a0240306200e4801404554110310b0f05a030103507202c0d00640b085600c18400c0221207503020900303140c0b441c003100c0348000703c102611650b410008540c5d0a10919240b400600041082c0082c042d01c030405d072030340c509070050460695460107209511549000032801034007080440078034401414841a246403d081c00c0e000103107105172181012200e40420b07001030131001c0d090f09201001d030710807401c18500b461400342140d40c0a08610b2018140e006041c0001c19841e0001107158015070f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 880363327 1250 880362077 880362083
    0x8010f09120206070e210f0f0601060e0a051203130306140a0203191e020c06010306050106050f0d02030c090a1206050a1104030f08070b2e180209130c02240403080402100c 75
    0x132251659154110740d601050700366005c3c20701c100c40002680d1403141619410540004198dc3e0f0304070b280408010040c11940c034183e03540d00007002030106403c0c119603014002e5118034804104800103162218542600038001d000c1e45004208108000c0695610f040e8855044180095017503524014042082031340b0000c0c1c000d40744000f8201640c1c10000038403904032481028140328681e00e601c000c4841f4040d0320000c4c1d11415080c040b045203e9010340180d03600060b11098a8181a1520005000b20b074080e4001d91054202c0040340003440880e00845902c450016810f00038540a0004005144203910000d0050780c102d0800c807003040b052904690009400c546141c81034281803c5124462005842c10003c80307030300c140107580d45140c1c1500e0404440390300d90108100300c0700c200c140019500c082003659021341880b40d4031411440341c1c4111f0228a015500070110000c01c1d560b000e0851658070344200d041c8009108010010f584403034480c0c0d01a0741581c108420000c1d01c40e0507110910660002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 880364577 1250 880363327 880363333
    0x18050d02042f09090c161e0804090e160f1401030b060304080a091e06032712030c090b0f0901110307050d030f0212060909030408010f09120206070e21 66
    0x34030149a1030029003203d040490740780d03141e030302d40350521101440b42c0e0070407480719808003040401044400300e214480c44801047d4403e405803599070010b90354031a82010020329994060182e10030400c01804900c00c00e42121851840d00b0008600da11981e144a4401c07189002400101c543e44280c000c4101500090162610303801c1920b46215190000c038042c20001c1c4203480001100c918208a031082c1c0d501e130a00200c034580c00e080c803c80c05030401011841c5080c0d60304003440c010740030516900b0700700d078056418898a9401e44000500383c0d000614104100501e45809207c220b03035140031100040e07415040d2656030041580142c81405544142e01468000440d00405020001c10310189062990303900700144040703504040e00b28041e0070155144481002c000800394207204501c56000b2144208480c2444d90301c5d04030700d00351001140080d03000c94480038058100400d10203054070402c000d0019002d10310340030714020803030000ca01c0b100d0300c070302e88041603030180d040600c68034000e106000045e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 880365827 1250 880364577 880364651
    0x7060605120703170c1b0906030706080f0a020903030304050106031e0b0c090307180f0c0516030804050c040903030e070e19090606031e03110c06040506280f18050d0204 74
    0x444241817046e00b01c180036055010000b5050300c1c0200310b4000352040d50311222501d4071600c0841107403440c0108000c00d0282e00300824a0203903020805548154803400010540c6070551034030141d680e205010303a084c0b0f203002c06410b500048404d4041a4403170b0b11000c58545501404000038a0b00d00c29078410100c491070100e200c0c0100d48650020140f155000c42d00380300f580c05000040303880e0300c104500415500ba8a660740702c0060311880311141c1040c007450485407600c0e42c000014080f103100c60000c8000c00c4d518051140c00e558203001d4040100a1110443d40b41c4c0b40400c01c41d58594008011001e58581e203178048820480b00c0e44c032090155402030125603194003a0021004c0d85e902d071440641c0404c020080b00a140400042c400c01aa90050120b03820149000248070071500000170621a8100220000c032078030b014000340c40140300c078a40d00c54040016050000d400100c240c183c8003d10a0141d800380a03944802d00d0044d034156060702c2c00188a00c0032808007040000c404032504d60458040b10b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 880367077 1250 880365827 880365853
    0x61404170a0c2903431206060203090a0e040620090a0518010312020a0f0602090301152706171c081e0c120c030106030c02070807141c030507060605120703170c 70
    0x100020058000d03c201f0000c141d103650050347e80c0c1c007820056941c0240494400d22a10b0180d4620680140c0708842c0410b85286002103c001045140c800c14070316a80499040401e252002040b4000c00b02900c07420810001c01e00c00990110741400068403000c2148511169a032080010b1804150000741c40958001685003000107580150f4210f031080d170038580c4065040b06004541c1003107940d000d02420190070030500d111010300f8a0072005201958949000568480d0104c205011250003400b41c0290804040d900250a4041c80300c6800c1140349000c00040ca05548060703410010810202c05450703641c003400700c0710340c4a000410701d40c81d8156000d1129084102d0041c5040e21400d0f14103100002d0021030403a540c5d030051180c07621941c856281001050407030880d4960317001003d02001018450003108a29504081034100c000440004180080c040c2e10711403640a400111000580c400c0d16610361507640700305020103080d42c13402010141510340401c0842e00e510100e0800c3d80c0c640c29440b5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 880368327 1250 880367077 880367087
    0x5030c030a090f14131a1302040e0c181e03031204030219081b0f0f03030103021507150b0102010f18020901061404170a0c290343 57
    0x100c603801000000300f0002c00c10354100c90800f82c0c03800780035214200c0300e0f1510881c0000350541d4040800b01d507005c0701c408480307501c80c0c100003190200200809a80e036468105401c40c180c900809040c00c445091000c0c2c00e0b4580800481e595030242198140c00200c1802d070403c01030740b40c40c03402d80c1d4580310001c1c0030341c45c0100104c42988a0380c00390f02030f03c154800303ca46961508103008002003241b80104000c816402c1c031034030340300c0707440c45c09004540309580e44050b02da10b0300d8483e000541d525031020004004500d880c107481014691060708140c2030072000c1da13520741d003c00024200300070640c540c89111390992003503114017080384112006200348400d650110385401040b84050307001d4210395001240031406480700003400c0418403081440c3c58500380303035807030350031380705e00d5041154001c1c4030254000c121140d2070328000c0c00c16100c01e80d4039100c916000c2e004c00220000c4807040c001c010300421403200e0f05141000200d541c140104070a62040d42c10508078040051059404050702052a840c0c0607408 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 880369577 1250 880368327 880368329
    0x40308030903463006080f071d01060f0e090a06090f090b0601081801020f041d01050312090406030f0302030306010210050f16030b0d11040b01090f0b0705030c030a09 73
    0x99402d0b05004540c00340c141c0c0354244401d4032080071130002030141304d0840d1404c02010340c1010b032035070003c50340000c04008802e4482940c0240402d078804407140b2540c010030302600004081420500420035081002104c6407041441103e0a000203030144413035090107003003a942c40700f1001302401020704d0907902100003403c590051022861a0010015020419105041d40366030031900b40c2c4210f40c1c502b801103401000040c600f409401c80d11221803000c00d024009081e02040710242180c0304e03414841210169a5500320120030030a11000400c0561800b01d05074940d2030300071102c1d5544034032002c046000f61004d640010900700085601b20700341076020019502400090303007a0f400307500104401900b928002d99450020b1041030000c103440e044800004082c02e0018140420b44002e948006000c9080c607070b4065400b5201403884074168a002e20622982070300034201611103034200310000040c0d0b41c0a003d0b400c0340d880001050418020100141c0b228408014201e036954415000010141002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 880370827 1250 880369577 880369657
    0x50d0b13022e0e0a12050a0c03030e090703230a140906040605010f03051903260f0109060b03160504080304031406010b0a120507110706020105010e070503070203040308030903 77
    0x22011a409041c458042e64140d11002024130f5180c0e030502149100021001c0c00480e120701c91a0a41000210200e0182000318000c0d1151904200240c042c0602207a0040c54803003054981a510341042d44003140381411861441403203559507464005032401030000c1a10401c01c842c280f4100155064000b0720644074a1080710b0a005599071508001c2215107030f40402852500040080d119031003c3c0c4c5001c8003103901034a03202c1600d45c04840e6442084059059042800740c40030200b180407480200380d2401044080b00410903a0b00d009854411400080e150450711452000040185031054040e500607200c0801584d98482e41c138034080740946024215488203020b020000500e0034480019124481030503112100b0301e09049031520001c1200034880c4080c803500d04c541503c509000c00603840500825000040d20754108102401d88282c003e003807104000041042000e02e81c2d01009960459901540f01a00c0c4e803280c940032811405441d120000102103020250440c8401100401174201 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 880372077 1250 880370827 880370899
    0x501060f17060f040c17060a0c0e0f09040602041e030c08070e0c07020310110a02010e01060501051c11030a0209010f080114061606020c0d020f07050d0b1302 69
    0x141e81d1006040e00101c24032121100d8002900090444800c07112090303001e4800c43c3c3c0c22003200e840d00c6944001c5c500180844003180e02c010f0410065210fa4440d82440410b541012024400805e0008401902c2a0541400f554002001c0347c100302d81501030f18054103001214040f905401425a1400b03985440b0903904030b0341e00f0200080407240403070700000f500c00c42100707a442c1d50340b10050300002c2d81c402d4004903010b03c00e41c0081050f0407031610403403480c0780180000541d030310b13202c640003400e490600642d43d10592518404108070383e0080300320b6210a03242d803412070907140b000340030034000c00072604400d10504000041002129250380245034501003600e5107402e500440000701c0d43ca2109000382000c150103800f0508440ca05400076180f210080d04c01c0e54008020359032545c0070390b00000c01c4c3d550260b001d902d60a00c00c81e0103100000010b5041d0004041d02807a14000130710f400c1900101070840c81540c13010501c40c001e02e141c01c41000d5006090005120062203030b41403104501c44039805100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 880373327 1250 880372077 880372079
    0x1103360919020708120a2a350405010f0605061303352709011404061a0c1207052505030a0317010812040308210109020307200a200402070501060f 64
    0xc1f00c556290488a1890780d48035280700350382e2903507285c41424480305100015540350040c43da4003100c088070701c1948035900214804016044010039078a16420080c4203a10502c140c2120300fa00500403002c40b0340080e468130064030702d551034644c00c10907462170703400c00b00040000150300d80810b0024000081000440c1c10322698844150103040508401c45610a80e00401001a000300c501d2546841c1c034014400101180d5036200b110310312481862002c1e000e030340810040002d01003840b034090404069a4864500b050301c0ea556903c0326004280c001c10700301141641008030b110000a50007070640a03007280c0000b412403d001d44001c091007400307500400030b6400483d9541000c00c91360440c45904402606003419680d5500b959080402040c400121500070002007200b032a001c10b00034420100c0c01a982d04080c40300901c01c40041c20105001200c2c408441c040c1840001c5891403141c001030040c0c4079503012240703040c0e900d51900e0b08a6002e8004070300c41042c03220640c072190464507106440d854403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 880374577 1250 880373327 880373381
    0x6060206061c03230412200112020c010b04140a0c11030403080d14010f090501082d0c03061e061009061103360919020708120a 56
    0x94107520b0b14802c00c28900b4114880001c0c060b01103181e2089003418680804103c3c002e01e89040d4204ea84804480086540b05006200803202540c038141d08043d6155401d84440001038040a0195401591154002008070914a00703500800342141c0c01042030005040745441c4000c00e00080d118400114a802d014602042c019843d80c29800307000c10103541001d14544a0800305c0d08504400c2181c42c1d00c50750f0308202c1703000680c0d00e2800781500002d2400d465042c01024400c0ba54143c00180b440e5024100680b007122013100380d02102e056090b0f4900d05d409111071261f0610761000c01c240d4161040c0ba090084000c07400114440e00300c400700d150f64181da2941c080069600f90781c4400404034012040a00207140309904440003c8400822a460440600d8282c0880e191545001480c103501d1704052081d80108040803011904c05c9400d81c42e42d0401004032188a02c44541c101c5003103a000401c2b10030041c4082c02c1c0d444403c01c00c0c490b4405440c004144030080d05a4000030020340034411440301c51 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 880375827 1250 880374577 880374589
    0x30c031312120f0509371410020414041a101e02071401050a020703080f1801020a03020c0f03010f020c0a0302010501242604050106050109050319060f060e01090606020606 75
    0x110350451001092500440014200d440340d81108103004c0d0010381c0345108424441900c9046040e208847d0149a10307410800d8a0601c200c102c480052140108010840d0301d480601e468520001114009510303400c45580e84007080844101c0c503000a41001550b501c0340c2c0107102401d55655241000345501c9121004030b844e62401e0086495460264000e4981e65108a0182040310498011034903502e40b00d40f5041429000000401c100c03036000504227549800300c20010074bc5441c00c1c001044049502d5401035140c80241c00007a0040300103400040c0c1c00d540942100803c3c0340f400608640e01c0340380d000c042e03894603040750041e40035600304000007800402032240003002e4003031000031541c0c1012034001128400203040b40820545500190320500300000702815004034810800010700c280b9000000d07040028550141d8803a4205840c480800c05401f0003007482554442c0d80000c0320381d01030903511b000f041b007600120001c510140001c50300b802e8030792005013a50407507000c8420310b0f60f4030400c00c07007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 880377077 1250 880375827 880375831
    0xf0504150c17060d23012012101505040f0501050403241b050c0c03070b040b130815010f0f050f010e13020a0e120d05030c031312120f05 60
    0x2030b01c1c00c01503140c240258a4507030308030a005012a00107129510707441c0f5070641480c14101c1c40d24032200c100e103040d00c0901c103c804600c3c440300312000040e0104032451450007091030883c202501c040014044a4045482c0d5000e0141082101e100b01c4400d9001043c680041c0144d50b0000000107020a40303601680130388044903841041c1800b118401c02c0f00003200c1038440c064244445d1990619440143e0300da030000191000c5940d1942c4a03044907607080d00c1e1140103e845400380e0084c1e5403d0040c0c2c045042200c01761045110314999a080071414400d1401c55075000d80c07130320f026140b1850310110341109628102c2e07550356601d440380c40d2100b07864507500480e4450140e1000c600101004654041c11001382c3c450300c01064145020143d1582c1c9041c0ea02000040c6c00081807804101d03500e04d01052850b09280452008000e072807020000a030080c030000e01303074202c4c0c00001b20000d00d01c4492420b129900c00d901034964502500443c0003e004440202440810a400d01c004820703140c40c40c0c45880c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 880378327 1250 880377077 880377101
    0x7060609060b07120c08040303121b1b0c050d03020604150513120314010e06121c0c0c0801060b04210201090302060915030405030d1b091809060f050415 67
    0x30345000e0f260342d075448071458207596200a1002d08030a600104e03c1507400f400096010341c40b08101c46050f511176104880307207080610b00e010084a41d210b41d2542c4207132080301d01c8000310307440340130000941844800001c155001e03d41c0503107034040360702c201070b8003181c858040c0b0b2113002d6820b40300c184000c1d0b000569100320382e001884101d030040040030419040403120038238a141000071720038500d02504203c2c45000d0f0400c011500d80c030028050030b0708040030305080310072542020388494015418022200c0c240041d0150810140403061420f029044148a0051461742c000308419507480003e440c01d90800d200341c450000d090440f980068001010816289030b0503902e06811074203540c200203440d0042e10056412404c2c13640d040c050034143e5001180624016401942c481031620340040a031105d400c0342e0005540c6000e5660122908044003000b51640740070103141c541900c541c0c1c84000d140d0b1140c040d00c80c07410681c80c85c0d444015540a140540d000b02c2078909510216003856055a0002c1028 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 880379577 1250 880378327 880378349
    0xb04060b121b030c13090509011b021504020409020604050303030f04050c12031e090a0f0510090321021009060c0e0109080309150403050607171e040f15110706060906 73
    0x140100808100405560040303510010b000c44d11b0302c04180403200110342c0c0011a81d52544120480c020301c6c07440183e001c0d1288002c0caa0360149004c084203101e005040240038a84800380c541c210340c0d442c07064a01804010b001c6984030700c3d09250031018032201f038500f603516001c1e600e0816041e0900002110460141400941ca03080c01c80984001d0110b0081c00d250701c010042c040315941759144000c1c04000c10040e0f1540507403504040400480c0083c071599001408011807040002410b00c802d0440c00071000c40c140c5241c20205c010036410b04208007040030300140b030000020204079155124503800c0606580e480d40c29a414001542d01100c1c5005402031a842800307070f0411468542540055003040e004114206a80c942e00c0038a04942070785ca0001003000302e905812400071048840d60720640e0101000c05401e1035107416240403601034000341c56107800f0071003072052060780f4507800c00085c842c120401440d075001001e0340c0c042d00440012103d050800d5000135040c0c8a41c06810b05480034441e803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 880380827 1250 880379577 880379581
    0xf18040b06070809030a05030f040602060105040e07030b09071a0c011b051b0c10020601061e0906270303020102031602010902032508030a09050a0b03190f0b04060b121b03 75
    0x40e0f0314840d000810415854450641c50b080000d2007030014007488540003c03959102c034108800030342400c4c0140c11042c040d529200103152900000583c00d02280c1d0481d5540e5200c0e01e4103114242020341c1340d007003a04440b5410514a4004422600822140c043c2200030044107a0212031400b03c0c40340c0c05101e600040b414080300042c82d0364201040881040c640844028003031840c00301d1000c4101c500e4130307405604100010000d4941040030741c0e0814000340d0718002c0c800c446c3c210141086229008200030400d152004400180c2c440083c00e80e9440e900d0f500003005507507454024041d500481f184400e41400c0d0b0038018245005001e0210340d01c0d8024003920305065458084903070003031114800642d40c112003800048150051004121480b400e9680d05010350a040502045400323640c05080075003410400c01060700d0a0b44619281210400d8004c5400c80b001150400948003400c5031541c028035000b000110801040014410441048140b003445e9a4401110740c1040003400403003800c0400b040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 880382077 1250 880380827 880380833
    0x6030207110f1c0b04061508030703050f070203191101260c1603020f0c09150f010216090515040203071704051009030c0215130b0912030f18040b0607 66
    0x2400111090098400e1084507040b07000f00c52003401e50030303044e41c164440c44148010302c403450041c03451204008a00c401e625250003600c80c0c1c0d0780310349000a0200301e00460107101c1030300d10804446920390020101c3e00d81c241d030520244800c000505045030302c40c2004152201550203080c04204140211103100e84511811000d0300140c900103155401307840382000000f0840d0450180803210300d000f60b000f00314007554400090301d40307100c8003040c500c181201e01c2000f0101030030000780210000c0070303a00d0440c4000c58200607443d01f2800908240c60701030420380422402199840b00b4801c07050001240c3c0f660300f4100a102c100d2000707503110303800110380071003035484111890039481d0050b2083c0100c410380c0d1402e03104282210000300c030890004881030714000079482c02c05450303000da400920016140610b55240d0a00c1400548a0704a0305e040124104046954011000d031116004500faa0741d1450440701d01440344d0b003c440003c0c130020900b401e0291605061048401084c0081c0080e4a48500c0391 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 880383327 1250 880382077 880382089
    0x281e0326060a090e0102121806090c0603220204021902070f050a030b150901090203010330140c030f03070207080a05150c0d060b090f04051b0f0d1806060603020711 72
    0x4901c401e6400308010b070313100000c803401d0b02d208900325040310380940c00400101d030034107402505840c04bd6001040031682555500200c80d00010f600015032244520740c0c100d00b40d91061b03418043d5000388042490708d44011284000407500742c0607404d44000c99225501040c40482a000d081d0b0030104050301440014250350760940c2001d000405000d403040207100154660000341c000d0300e0300e25004030042041055a0400c0222110342c2d4084505c480941c0f6491a403d0307001064003000c110480c48440d038140364000454540c2850601901e81d10709024134000d80607401a10101c1c01032040140010b5005008a004500d09600c00003410140c0c0703e02d64181400d440103064000c01100070008101000c0280c8079810091070303400681134540c41260200001c20b500550018011414501081710f0160580e05041c81106680041516400720b90501c61243c0900f41640f05002e1a02440f40c0b1503240d01101c000486204113028080c064481c0011026805400001807542e18055490500d41c5818 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 880384577 1250 880383327 880383341
    0x15040e0a0c0203071b03060b1f08070509031e06130309120c091503020915030303010306020d0612030c051b0d170c0a08120603281e0326060a09 63
    0x7074811a420140c0350f864101d9001d5250f80290b481400204041042040c42d000e02d40e81802c049400f203480c81403810781171840450810300a0108030a00c80090316060080c4180d440070b060281c12514000308202d01e02c0080e482220281000d0f1180303000155950032a0f0810303402d21641580d40f014668a407900c03091402e08121004c84000400360001300d14100a4072034220740c1a00071616120317562540c010f004425401401e29210b18040d8020718120391400021641140d038021401685e0303814041002d03008140e0f82d082051176420090091050641c040381130400c050089058403400418a09104c140e101c644041c1da401c9041d85169002140705802c1842a4105a41da03043c50241c0c1c144585081c0040d408013102d030f80348089055030b911301c1b1030441e0a500030816801050404810607807020182c4c1c45020202c44603074000d040c1d00400c0258103181c030811042c001c0001c01808103140c00f0305581542e800c20302041d401030000311650884840810701400000d00b2070344101e4100f01e0303440c4c054205 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 880385827 1250 880384577 880384601
    0x1003030f0c061407140405010c0f0c03060e030a0201240314100c050a020c121239060a050c030105040f180f03090e01180203040311010e010b15040e0a 66
    0x1040381100128901c0e01074048060103c59140c441c07443c00c400050094451503c00e0319103c10244024083d80c0d0b002286508615040b2a00401401c00792800d00c910b00c040d90002000325040031081c14485d00e0000c0513088040b40b43d0028803048100d1519001011207001d61440d081c0700d4070341d08201055200f000442584041000d03110803500b040c90740c8083c0c58490300b46000140c2d001452541950341440703290b84420301250340401050000c040f05949182001c3c0d02d15598600058403200804030503019015a0703042c0840e280e80d00941c43c501d0508030401d070186800b5000c1c000016030550079503c990380c42100c056a5440c01d69081c01c3c2804020003154861800e01c41d540c10144e10b509403019400c3c20f41e10322521641e0002246454003d12402c02c1c1d500010071900040014405005075442c140101c030110a00182c5a58030381c1000c803900f44170001206e105520300011a9001401900104170219090300c00454a100460544180d481503104080c2130201184c003090350f03000241c00c14486100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 880387077 1250 880385827 880385837
    0x1e060603060f1f1805040e0303010504111903020d050c070b01030318051c050d170a0c0302070602030709151d12071d161b0b2e090b0301051003030f 65
    0x83c4160722401580404038600001c0f85118400c0d03800384044c1c0e54104050700c41943c0a1221060480d402a40c1e03000c18064507200c0c40c3ca07030040300007040350032042d100c0c0b4004918091311860900a800b50080d4843c005441015051100007030100c25907070110740d2501d0384140003c0c00c0340c2c03950318202d4158507445074255420b50b0381c040c0040c0c56910280c4c24001c00360564003014040140d40ba00c1e91611214001030000d10840605050001701185082540082c54020101c0c42403102c00d0120004d210702500207021520210500c17110079400211803080c0c441100311106001c000d010103640d60641042c50750031051842c130041b0755a080064140c0c0303140b840b40084903482515000408000b900b8070050b0310200046508100130f0103400000400c400f00313141001000d50002594900900301946800350001007100040b80305400101561a03070304d03012803215001c000c043c04059418107810310800814030300349441600d452906106850048143c00b41083c1c0f8203145650550301c040041c400c50701804 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 880388327 1250 880387077 880387099
    0x180402060405060403030909150e280608030a110105060f04090f020301020c0303040302160b04050103022b060611070e01170712030509040509120301210503070503031e060603060f 79
    0x145030f90f80a44040c61182d260240030078103008071442107a0943c40d20088514141004110b000c4520750519008501c40034000e60b41d9015400803d014240307034046200799031400c440000e40e1800840134202d40c424599500c0b40409000a05600340c0d81c042d60b00d10750241480b180d1000c41d180075030155070194031543d180d003015501d035000a03003241c11044010206400c000100000c25a0602c01001d80103040c01c14412601d0606000481901a50203482d0505600140b8141364080c40389210040341000344c284081400111221005080c041c802e01c004504481200c22945c4004500328056400e6640300740c080f83e18040f584816401002803110305c80c01620004282466011718981036a4007a80307906989400c40d07401e0004680006100700701c0b030740020082c1c01c0845030000449045813000011801c038448185018110040030350001442484001202803c100f0080090351040c05180000c2420b400c190740d245901e04011654103070b2065080001401c40d1500743d02542100317401070300302c128103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 880389577 1250 880388327 880388329
    0xc0302070305030f0417031314041410090c02014b0510090509060a0c110304120501060b030c122205100606020c0108180f0d05040503061302180402060405 68
    0x7544c0b121500f075800c014000340502072030803d5072070b15800d80e8841c0011440e01c0f41c6100c1c1e0740c03e402840d00443c0ca00504142d502c1c0301541c0c0c2d642181c042071580340f2203189141491100b408030040ea91103141c0340f0303600b031246603032605006101c1d0305940000030340c240c0c07586100c02d01201540450944400103a0b40c926020010071301c1001810004a49200c5000590b42414124405840c44070351004202c42d041004010681c00c0c0401c003d40c10a207600f04c00301c0c02ca64169011342e0f80c524540c0040b0528030012500003000200c251403e00d1980c040e4000308182a10740307954030100d120845103004c46000801103400c01d080c1c01400c003640101840c40b803044283c0300c01070480380413140400584252313000050040c560151031090300018403a80c00240310114002c0000b820400d0002c004401c1000c22441d280120300303050000070880340d038800998030158071030003018146420038040d03a4064400d040000d40101d00c41000301145a4000300b444a0a00000700120400360005004030380210040c071001842e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 880390827 1250 880389577 880389583
    0x71415031005190b120a021e03040b010f030b071202090a080f01050109180213090210051b070608040b06150f18042d0e030a0915020a050c010c0302070305 68
    0x120140c0032500241807412042194648030f80305210400000210100700700210b550803180300600c0e0f4180360400350344902403400280503254038040c004080e02e0b2103400c0604000010762080344686080302580c1d80f1a80601c1c100c601e240001000300c010b58022980703090040c4800b83c21400d405102525002d00c80c00810380385c0500d9817080d81d0903800482c01c020386040078080c003805401c81c2030041201c92003c1c84509549844081c004e4090103004248580c00e00190700303e034918a80103808280305541000004119501401340c40e842c0502c690790200300c3d02008500282214003980d140c00913900d803500c130780251160241020b0b500c030360030040c502c00350080714002c0c1c80e5400e09c9900d00f64540512100c012150200965042d01c80c41c501004071820580e00c0740780c90000c180b00040f42c4400c4140b0405a00200301c84260005c080c4000305032140c0da81d610031070030819180d04601c1c4440d60510030300140c1e940c410800d0001c0540c3c00c09002e401c4c0b60b51182c030316040d031035002c1d2045407400b59807500c8080c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 880392077 1250 880390827 880390831
    0x6020c01093005190c06110105070e270705090907050301180e2409070b2107090f03050109021503040c05010e0126010602060603030c0a020112060b0a0905010e0604050307141503 78
    0x5d080e00300810b04101858200600d4107001c0c4002000348590b03c0c10032001480601080c00407881000801440d06000010000c007000c4450b80100c50281d0b41805040508160000b481040c480c155550014607460710503025207049400101d1004603070100c502041c0081c10800008906a100e80c1e80654061803a1000003601c00100482d1301e1968140311307c0490810090f0381001c3c03441e540800140804034082e0144181e17100c07039242a2800ca4450f024201e07000740c6141e11001180c0020000401031080640c00f05d54464070841e000c0901c00d0022061030464002120b007d40034035200b000402c8994042c0c401000b0103101450526612000605280380142600503401d89049044c070062003100e030100b0806800402c100c005605041003140364954030000740000904000c0d002d46204c2c040403654104501038001c035180c0340c2d1100401d0364020504102441140d000442005010078035090010849054540280242c24541d080c2a400300200c0003034852103030414071035030303144030138142010180d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 880393327 1250 880392077 880392083
    0x40602120f150109140d0302071a0a09091a040905120c1506010804200402070204020f0319020c070603020f070c0609030506162a050706020c0109300519 67
    0x42072a0800008102a0664040c41c076418443c0f003400a012501c00c4002080800c0380031125910081c002e03203422403c080345540900a2180c800e8500c00050017094060915580e82c6e1740c5408540341c0e201000c006840a44e140c403030700002c42c548800c800c4d00b2302e5001255803501400c00c450501000509039030640d4803000100f04140c20800301c001c40d54410720101600642d0910707056140c0c3c01c050300e031188040d840c0007540811145c9840300040c00e803a281c065607480d603002442191100001c0981c0c0d0082d0344100c1e030404007204240c801100000b03a5200361084032401c60010030708035003000400d80096200b0004801c0b02c0307c090001074006110800c40c44041c0940c0c1d51030240d4546940340152818401411006142080511041c88541e200100802c80701948401d6a40202d107900111072f105401c0300c1c0070f00300b40205040800d4003a00001c1d0701c0c05000084e61000d000a69580744141800101320411404001c521150143c601101918010140c05202500c80c603031114106500c40c040084822 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 880394577 1250 880393327 880393351
    0x30a06030203010501140906120a0c0e070e040515060904020d050c040807091428060e0612010204050a0303051c020307082203140f0c07081b030f1504060212 69
    0x40c400c50400303014440c01020400b01c641c02100311240020078440000301428010031740f8000e00d01d103401c420054810300326002880419055207440c4a12206102101c03150042804d40c0c0c1040707694102440342d541f00c1e112407841c00701482c01c02003c1110b02e82c03007819007a81c055028002070592115900c01c0e98004c28041c0d00c195619880d0122260070940540c0c0800758007403801e0138180c0303210003080d04903030302c005103410100244a290300240300240c20b140d85807128501d0010041010305441c02810f0040204032161400c0840c0d43d2026800d0f4401e6005c0c0b00e401011b100760400000b40204050b001c0349800e121003818041c18441c448040341c0084528000048868050061180b07941030303041d150401d15080480c2011041d28080c01c80302c0504004004070b14009400d0a6060a00c4280c0d0000c9a19001351100542e49445196580300c200c2000c0e1511048200395051a140000303483c030004140130b005c0c01c01100006007443c403c80d0010010344d2425002c001d403094000c3c00c074554900c2a5049281 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 880395683 1106 880394577 880394579
    0x14190507050c060a0b011e09090c090512010c090e220816061d01090c170c130207141b120f0109050303070f050a0c08160206030a06 58
    0x20502890040f04180715049140d50401ca01c91042680c400d0b1001c2948030102d031000052201c04004291f0021301044241c00b1500a81d909014a061520b030556442020a183e0b000040518440365511210015440e4200408201500410b5051401480c002c4210004030302031002c00216903910149100822010b0b1045944022400e030352040102075519000000d0210004461a40311040e400401c65880501c075040b8100c3d0000f10386c114062134102420011403103048d1000045c058410f1490007504e0384a280200c04807035035001651003132b060608580440c01d03000864a0358100c4440781c5081403500701d03040380b020f00444403030080f040211222854030948184022403542041d08181c02e102010018511a2031503480710006900440d00803991803203280c05c1c00340031074501040036001ca41780c90050981c98000015041c101e01c03040e00004c81c2d42d00304885c04210b60b84c562034 = true := by decide +kernel

theorem cover : BRFrame.Cov 880215827 880395683 := by
  have h0 := BRFrame.cov_init 880215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 880215827 ≤ n) (h2 : n < 880395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
