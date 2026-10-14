-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3745
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:33:30.250613+00:00
-- url     : https://prove2.me/submissions/7dceb4f1-827c-4d26-a043-96898ced5a43

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 673381294 ≤ n < 673561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 673382544 1250 673381294 673381297
    0xc0b070302041d1005060c010204050f1002061501020304050d15061202060a030504151404030806061c1e0e030406032711010e09100914100501050d020c030a0c050c011d0105 76
    0x1160b00f045900400d0341d5400046d4503074100004910f0301c0d0354002400c101e80e2800020b104400081601d48081d102c0d0449000303034442c0c0e001020112905505038a4002981c13081c0125070246c18010f003102225200c604064029840041c48848a00e00d0100c011900709000d4400044050b0b009122915050b954502203000d00320261080325440039908503403100664074001d400c1b24031055000000700d440d0505005140b420040d003c0350049100f009400e440c1080d1202e4800c070070903a40f9003c20707075142c4601c00c15101100b2541c400c003c0c0c1d15040080c011120044014011a04660303000c1c880140030307034a42601c6540f10300904c45d150040c14075540000b02642c0038095a04014100205420000004a000a10304598403000103502d08428018408107106000f210f125000d041032103894000c1c030b8010201d035a802640c0c140702010400c1840ca242c140c04075228044000152512556011805012100588c1c1c3c121b68502035002100055407013010010282044045e071402c2072a004401500c15 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 673383794 1250 673382544 673382551
    0x90f0603170c011503080a021b0109121e030509190609090c032307020d02010209030d05030903040f0906090e01020c071e09180c0e16080c190c0b070302041d 69
    0x407075480701d0104e210705009218480046009007034055403807204010081c00c1607003592150400844144800040b0b9a002c802001a2800503500180c0042d05081801400700703040003911081c540100c41c2d104055200c00a0110004e05403180c3d400c10024003d0500c04900a006a17400203400003002c0045003c40d8000e5407008250b81000120f03000004004400e0302c1c01d45580c08a0500410184402c40f5410040020840384620003142001e40c40b0300001c0d00c5001314101d61081080100105030012030a104031001440622040c1240e42d5442d5407020141c403291040c901500c1c500704110451a01c10300031a00c082000101038911030f800c0000d00c42c0c100181e5112000d24a03920701010550200e0386c800c881e00d2060940150780c1980e09032800b40c0300070340b080d0080c0603181d140d5010b02144641080381c41c10320315164204013806507a0781c500e4800c1e40c02030109034544d400880410444141d0403004c1c4c9164a070061401c05840c1d5036a91041e016032107984034405510a03100a10401141a2500031341c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 673385044 1250 673383794 673383817
    0x406050a020910020c09010506120615090a0602061b04080d14040f060909051e01060503220b100806090307060b0f060703180609140f0102012004090f060317 69
    0xb000c55190214000368441c0058801592100b28a0916031515804c07007401004100c0d801443e090b101031000a41181c041c1c00140601009001144c00000500980312281c2d0082c044240150356048006d598803025180840100d41784401c80941083c0c000844056039124001040c2106000d00111500b0f09180880000c4540511011424511010b0b40034000c0031035550303080200c2d06119442d02240e401800e00350072000700c141c15540045078841075a04441090070f00756126a20501200008001c0d58400c495100003221071030200621101c000b801041c0708052030b05040d03205d02007c0e5449000f994100da25a20031b010304000100c85c1d070040340d45554050500e402603072550000c103c1a40200d202100898120303440303158240c0c40c840030100200440d14040e820207103051000e208000c3d203802014013a04500c6585441c59000750003014200e6198941e00b03442c90780051a00341035801c40c0c01020784c2c842c1000c0300300030303c80658040c0e142940e401251142000c24074501e11112580315440001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 673386294 1250 673385044 673385047
    0xe13060f020f1b0c1f12140402061b0706050705060709081b0a0b04080106081504020108010e0c070b241915170106090302040b0d170f09060f07060e0a0b0406050a02 72
    0x6191141d517003481d2a1041e2441d155200e0200480107000340400101e40303803081d4509000440b15060540e45103411a405595465696602c141d94000945020303030801c00d680300c2c1103000030f86958883c0080078040d006109550345516104000c440e1075800b032142c20300c00d130b01007406080300200b04604600351840c020460000c030340e83d80095000d6908280d0010205035503890702009880d84c1409038144101c1c030090a040320f4a0254000380403a80306004400424540b0800035030007110351011510306c190881c4412340589018141c0404860f15003140c01001d050151015982d03013403109801e1450880110802030b054208a04200529801038920081081200440d4040004400c030540a85110b60755000d440e0302b9401480b003611034000110f401741d00c41026186c0450b500106000f1840c0060700050364900c0e0000c1010700360b024030042c0366030050b00050811b4505060700b000703100071845444280b008001c02041c040d100d0040c1d52015208141450000e000101703d5808107500001d05800103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 673387544 1250 673386294 673386313
    0x509070302060901021009290f010b070c080129040b0901030b10030209070e1801080c010c0503130e04020a06020303040201050315150301080604170a140c070e13060f020f1b 76
    0x186c0964103840b0301921000c208000e640c0426824094600203030101180c0c0c10260b082203a041004402c05128002e0148e10110b002d204000d00f1581031340080007003074028490b600c0708140e02481120900c0042101e4025116a030041d41824001c00c40f904500070b00320b20890303282d501c1d121080c1e0402060030803e008252004001a680c0001e42400303942c6540d12155451164001c0c059000502c850140034007030010010020910005400c160114084c41c1c40d982c440f210745890352460242800d02d01e000300e222036010a50f2117001808034455070080f50584030f00c47ea03449040e030300d0f480159000380c0064020800103d04c01046482401c00c08005400c010029812400710340c81d50300b003030304110066003000007071205000e110b42c81c00304a80390340104a8546401403001608075003170100491a80c0101040da100c1d91700b4203008132001032810b15080903661a180e2403c0343c070102689000c580342868940d540c401286144217a4a6410b0990411441c000c4c0c1805007113440c0c107400048032030a10070140b11 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 673388794 1250 673387544 673387573
    0xc0f0a060f2d050403050105150a060f090b0c010b0102010b04060b0a0810050307030803072705190f03080c070602010c091403010e0a03030e0c010813030e060f0403200103050907030206090102 84
    0xb40404600c00f0380e0740984031030451420909403079014180e00403a0182d0038000580703541350481d2004803100f606003c46005034900d0f05981150640e840100c50110204030b060b50305806400500c6404002d9000f00044801481008122051070150800b00c0c542444140c1c41180250703021600b02c001c96000d0003000d60f80340000382c07500c0c49035002112804004000c1c032a80c01c1d04450014042610404100e07604032010f000312522007420b10030301d07115100054151144148040c000d0300076001c07260502140d10788a0406e4281680001d03409070281c03080b030800098151042c89591101d4019076a0403001c80c0c648040d0300303204a1941910340c0e065523941161000c8000810290303041510984004ca080c1c4c60500000381012100786d1a541400580c01c01c001441c3c015055101c41103078903051000d400220100420814010411036003c180000100841809962a94401c02680a03e080203141d441c2c031004406075541903a20300240d03400b170f18041c001864441c0107403e180106204442040490288 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 673390044 1250 673388794 673388867
    0xa06050703140105040504053f070c06021f0b1201020d090b0a0c1223010f0810020c0a030804240b090108060601020a0f031704050c0f0a060f 62
    0x920002007a610079411400070040c2080350f00504c01150100150301c1c06444080d00e600800f540d211004510705607441c02000b40400408074241d0354500c5945c40c0c0601d401468180e440303c82c0c1910000d4041000061031440029000b1035a40c031070426201f82c0d101c80c070f08840907000b0700380c1d0903074080b014080003008207000f44041c081c901c8000102107404401c6040c1810b040d24041d090248090401070494641a004144014113000308040007450440490042c0c55150780c071107010303808442c0d0000004050000240790300650340c2d001c00792074011a140484004074401c00f001c1c4c11045e0420026100402d029110441e8428010441e0044080c4502d08861000c03148080480100b5980c0680c0c508078148440364030f0140600100800d0141409000070b0343e18008050010410300c151400241014403501607002900820384560340182007514190b80c0360351041400a00036007080e028032185140548940c811900b181d114200d40640c010300031a082158071300f59903900b0865103099640c10080f82d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 673391294 1250 673390044 673390051
    0xf0e01020a120320040f030f15050106050a0915081315050705120c03060a1a09090c0d0e06010608070f020102040506130519030209130201170f15040203010f06050901020a0605 77
    0x9800181d0380380b107018a48480d642c003c401c24801300040c0710034403014092600b90420389800410580c0d080714139160180303102c040c4150082d00c20f82800000203090703402001510300380c4602d0303c0b04541d981d203400d0b8842180c40c10895100014515801152820301d083d0b107600510350103a410300a1302d400b0b21011070180d4006a84020000388001407406950404131442c90300207043e060214514140a000a4000522401900c1c80e002d00505d800120801d6a0200c400d042d202070110f003450301d02244010101d07001304c0c1c0c01c4805282400302209c1c2582e00401c509040c0d6080d41c5a504c01600e0f215400c0794142c1d1211100c01c10b640d800c00001c43d42d07945200282082850030614409244c1c14007050100340c00c0f11414800000740d405005000681e1000481640400c100c0140350a03208140012601800d00c42c125820040032107045c408a2000c40540a01c03588400741440328089031300080c070040b44400d21440441001001c0c062141c4c0b40308400a0115050510444a458815807581c8084401c240c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 673392544 1250 673391294 673391297
    0x2010806040e1e010e0c1f051905280c0b0a0608030d0906060812040509070e0d1a070c0c050409020a0e0106020c13020f0d050604061806180603030f0e01020a12 70
    0x643c81c0510381c2c809004141c01c41c0500c3d40030b42585120040800c40460400452507080b1130800081e006240c07141c0161140b411b110041424999134608001c0c1040c0d004220000c001c0c48602c0800d03803e0b00c110f0116581c4a2216030307440f08648201d44a5031100f01e40030b482d5800311600c500700021401c41c2080901003c0130011400984c444c00d42c40d24030101e030801d61201804c1e40102d01c1c2c00440002c000b00780c0f000c8501c15030710703440141d842881c01c445401300a00d03e070ba88030314210b41c04000c2c0500d00010805031041e9641d0304c000d40e1a01c2344244c81c10b9000150042240d4810b20040c401400c1582103030388840d2015242c18001034580c0e211110001090308040010390190029502c275280c48012415201a22035085107082c502c001540c036a44941030020311499200e00114009031140ea0181000b005400003c2070413040380200e8401604051141c2d10110b03c0040d81408541d50f80c0c0300340e50880f98140c40e1134588143c00c40042e1b0f01415006990b030305502458501ca4081401b20741c0c041c0003191784d0b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 673393794 1250 673392544 673392583
    0x1905060c03090f012f0102090a0b07030801050406050a0302120c060a080702120909162708100e0327060304030801180903021f0b060703080105120109080702010806040e 74
    0x8000d12100d001490503203810017800080c50905a00d0710342102d0b52801041c1e184201d41130603098514064410b4540044c0c101425010014403c00104090061148650303a8221243d82e22420001070300c45a0103032a91145150f441040145400d00e126018600c0c0042130383d0b1206408400100341360411524403002c5003d05041024680c0d041c844104441c1e607101d0035a0504191501041518400408003c610011684030700c07103042c0150010404144e002c0f2034101c00c10744031000c02d041d02c80305120383c0443e17200b100340ca02c04261880c06002c0303041000d0700065007005000050b2507800b032719401e1400d4411039010108841d035181c5400442c0721b54004d4440c802154508040c61504101c0c89880e14445031502c018040000c1d0301240000e40745203544088950740030603041c00c01c001c100000c0c1c04c551120000480100f0540c100c030001c0e040310f01c11654461490100300e030080c281d5804510042104200f006030000540c02090040e070459000b8000180991421326424549001c41600b11601d415 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 673395044 1250 673393794 673393807
    0x30305040e0f070e1e031006081005160c030909060b0306130506011e023901020a03052218050a0e03040f1a0c070f1805040308061905060c03 62
    0x401c401070607000265084940c2d16454901001011240091600c5200c0c0c02c1c5c9a040410080080d0324841307280b2001000c0d0380a45040b01502d030300600181c4030b0300c800fa000c3c0c80409420301500d4880d69100700b001d403c0004a0009869044440d691440001c81c04e000d59840003083c0105075100f240007515110350007544c0d80c20400300304802c02d068034189452140c00c0504108659a1000644a103a4041b403220b0b807000d40301e61002c1e414440307034401100002400c0e80c0c502c6d048292078015010025902e1075074600c0481c13800d004988600c10ac07400900407450411040951900442a09040404e5150b803504035a031a40141c2d030703640c075a0130341e061f50158840091150301c210b24414208025202c1c1c0086180a10740301c1140d07124403843c42000814880f92000c012808040c00442d0301d00d18059060340c003c2c503103d00b01c1c005080c003075000302200d0040b00c00d4804815031991007014000c03605a21060040d070b49c2c0310100210340b01044d0070820028251040000d017a22000d010300742c03502c9094046c5807540d4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 673396294 1250 673395044 673395059
    0x203070b1b0601170118021f020c040908190206090d0f0e1003020901032702041e0c20070303090b09010c0c0906050117010e130f02150a030510050927030403030504 72
    0x1004114109883d000c4080008010307504c040c09400110840c2354403124000c080c4c3c0d000c0e8140700413803540319041418034149504112803100109044201c008044422801d20402203944000c22180051158804000e050f0007a02030b074441c100b140802d103807682c22118190040713401901910072501c0880e801003070581840da014080d103450300104407421442d940981701e6129800c1c0506174080c0c0156a50944140c0000c6003001184014064400034400c010f024000101040e190042a440f048262207460340c80d8480861180100c0e03406554903070102e810032103100c2036030f03001c0203005040c000d80b070950000141441381c101c0000c0c94040340014100b40b0300400502810b8140802050040020005010780c0030054081a0842032007110350300305904603d0b005020304038514010350300c400c071480381d00069000e10008101001c40340c0d4090107a5110003d80e01c90354000c07070080990041c001d100044104041e0a409085036145c20038803001c10803140780880c255800358105400240c00040d0510498 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 673397544 1250 673396294 673396301
    0x1060806030a080a030207050307021c0201090902070b0115020a0b0c0a02070f030f030e210106060e06212e17031603050306121912020a0203070b1b06011701 69
    0x55020300b4400c491a95800580d10400100300c0506a002c030701d41d010301104200352621300742d0103403485001c41443e4102c85980c3c81211012400204400d03000705080009000380d41c8515404102c0040c0b603401c00d007400c40c0c20152072007104214464100e03500c020510320f03034225018000310f4102c01d981c1c1c0b0701c2c810028113041041d00609500c9c40c03a04030801c005440000c0a000c05a0145058000160a000007602108080f08030314800004220550647d100c10742c0a482251901d0715400840b0a66200b031201a00034813403125644a0002d40000c0706040821000b0750041084240010b082c90078081c0e003d00b85101c1c0341c20994000c0b03904040c0324034a844259404038894070340080d81841c18060a07c00c41c0c418a0b003004080000110103c0c2e01600da0344d15850f0180001e80c00c1d1124940000303a03500303109445030790540b451100c40c00c40e04a03c60001c60044101d540240180c46102d0820f4999075441e4455640f0000740ba06640294501c5e40007405041d01038212420300708100d030390124541d401d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 673398794 1250 673397544 673397551
    0x220f0c02120a09030602030705220e0f0603031206150c06150d0b070f020c04060305010c1e05160203070909050a03021b011d040905030f0c150108030a080429010608 72
    0x70898200700781ca4000381c0000312402160390080001d640da582c2ca03001200c3c107025405c094010480c150030f180d003092803444844020b480000465000b5030342d4078860303420941410b842442d0107410401c0341c80c6c50f4043d04141641d00050160082105107104d148008807a480a11448500d4001d00184240160f411003400300c070545c12501e0080500040c0c032007403c00030300501840284444920032561071070013404248003035040107004001c2103941c4c4c140f01c1d0103000c180e0103000016822070003410321308406401c203545c802050f650701d5003445014503500f55070f001d103480140d91510a900d0001016150f40c010682110b10403030203041c81c0340641c80d0103883d160680010500d54258403e5026513a680100d10861004103901014098400c4501140040071704030000b50940c0400109640108459001003c404036490221810b1082c1e0a8003002c402c80280140c0105400401050030941d100301d2640390480d00030070444c11071b210880ea0054074449401d0741520603c035504c004214254020907843d60 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 673400044 1250 673398794 673398823
    0x60316020c060c2d01230a1b050906040b0c0a210e101e18080303040209040b0903040906031101170f04200d05010b0411041202220f0c02 60
    0x1440f114110064641c41d2095034022545408062801c10054240c0351081c81c0b035101d0000c10000c5243d05a603840c005000b204095415000c1e0045202c200381c0740301d99604641001916800c2100d20001119254007054829174004028000803030200340c440010440359800c1c40041217238007514900800b00302d0b80026407000d00c1c00c0d044004071105402c9821851141401c03900e030006000c9428040d1400071700c1105201d0005090780d0090708081d0401410400d240703024805960303c41d03032000850340e60300c0102c80003904610031802103000a0748883c625034000e103221081d6410720b510780280720300701c6070075900a031741003540d00c00c107034060f560030005881510700400e0b80c00a40e860700d10001046e60b000503100601450030480c1e20500500300c55401d068a541c0104000414052410068083c00540300440e00c55850041180c01800b80d000c1160115040c2d8140742c0d10030391054080040c000c10495052a441062810440141185101d150360507400c1d8134001880704c1500800900c1c00220301040030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 673401294 1250 673400044 673400047
    0x3060606080c03060607080c0610050a0f0b0909040303090b090d1b08090d020609031203040b0a05060a14041103040b0a050906060f0d021810030314040501091503060302060316020c06 80
    0xd900c00760802120344c80301d4140da0b400c2c1d80d01c10900d40040b2503c6003441c09040b901542003070180e40030100d035000381103c03000c84c0d06410a44d00d4485c01e80c2221010b2081c2c5202c2482001030300440d043c0765944661103400781c140041d030b40505840d2200c2100085404038541e4014482d18003081d5008012055110b800103400601d4280655030501e40c0d12464040a214004000c8050115038484048901e46407026040d191a171510300c1550089400c1503808542d00d607409000a044050340f0710941d4400c2d07000500d14180c1c0e038074180c0d001c91580c2d941c4910f550016120514400d555042800460040b0311030800000c0a14220000e00304542d07001d17040314180c0c2c1001d01480085d43e0b07603141d8282c45610440b8103900000083c800101000780035503018240c00045820442014034510082d0110380c082d03103800c68100800b028a11503842140100c5002c640005030602940c101d0501d0b080d0b40285038140003412984076000070b0000e400444000d40520042d151403080700d5814800a0907955003942c209 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 673402544 1250 673401294 673401301
    0xb0a4419060e0f040609290c091f0302280e180a151203030902180105060d110909091015231c05010c081e01230312040306060608 57
    0x40c1648031020f410522590075500104082c011540c3c0a6440ba41c0e2011140e40307540c0c13880c0e81d03010760700024511f03c0025140101c000b0b00741030030b4007003212901364000b040c560a00d54062551101086200200410594207002c61800b182800d03180641480014204410111004800510000031213410900a600403516110000c0c50030183c0c40e00101d0701607022030721345a040244001c4d00d9407507101d2405040d0807044e080505405600240b41c1c2d41c02500da005003048080112051720a0a10540d500403404108011039140e0550055601c145d40800310707031038151002c0010709220401c4d1004007880d000308207007001103501e510800c91088080f46101c503d4516102c610070303a409802ea8400c0e030120985c1210a0240c1d00c00205420500100d10111012905802c2079402410500342c200e0110700c1303a00201e01a1501031000b840b4249442d04070711640d17030030f141d60b445121051034180c0e68418220340c0005035940c0d05012607140401c826610503102d502d103081072000d561f810f038441c6080c8202e08003403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 673403794 1250 673402544 673402559
    0x9070f0807081305060f0f060607150513120e031018060906020913020301080105070e130902010e060409151e0303050c030405060408010f060b0a441906 67
    0x500c0d0701c0681030800030225a16031041c03949001c0f002400900c2409003001b000080203042081e10f0203000c503401a0552a0b9511051000c60312034907501424060003d00c0e01c1140c0075889c1c2040c1d5018041d9540c2008203002c41d61894a43c41d401e5031241c1c003084d402195030146040030008080c2c50000c41f6428000e12503e002105804299210702604003500c540c00ca009001c0107804031211703080c014100404e0240401c1c2060004e400a000c2c6400315406c00000c200c101d489803841d04d01d00031008100104c03000f690703d4400000c10241c90100d0600c8101881154541d0343c28010340020000c240c008520550080e195011fa20810f4001d001c200e070f03400c0304000d00d601c8400034190560380e0509200c0c1c5d403440910703443d41c6140910750103607031301c88000117002c220b141042d00040c0c0c00c2890281e05204107500d59155040e180a14019180041c1082d01d20700182a200f07a0701010340108200000c0b814100c0092440c840050300300f12000e5990000c0038070100d454004080041c40000c004100030840c1402d55 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 673405044 1250 673403794 673403807
    0xb0309011b092106061d070207061806050c15130203061003050c152503110106050f04021b0d03050405060c0403050624031005061008010b0405040507111b09070f 71
    0x1c43c05485140b55039100802c036080c2c1c000300292003600000200294103502030381d80c104e4100e90b01c50050048280014081e070050b00d0704400f030644500201091402c082048030550880a046c060a02c1381c074182070320440f22100e126015440d0002d11160100090041c14a010380162003181c2c2030b40d00840801c045440850941e0714514212841074030011030a10b02c41541c0140842140c6d070b01000b092024031305440150014181c5e100303403a0b025009114a6165081742e120388211600800400e038198074500d007039401003050504400c2d0501e261000180014075042c851075402c4080b035a00d005110500204001150f40466042d0801c2d140c5801c41d51b417240c07194009000349110b0a1490100b03144107e40b0b41c8045001000030f0115240d038a0340f021500050102038500c1402220b040000701c1a581c0329565a40c161104040010300d464130300350034030008060040045c2d0400500c058080d000c0c16041c4041845030503c20002c0311149205001c001c44568040d0199083c44886403c40341e000b600300d003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 673406294 1250 673405044 673405079
    0x6150f0305060f060d050105010602101406150f04090f05040c170c01080a0617150a090807020f010513031a0a020c510a0905250b0309011b09 62
    0x51201920344480002c515540c01c403045c010074075424000081a8594005a200c0c60207030814000e02829130401d000c0c80d04c0c160141c4541d45c10001c207a241c8262005980020503d0095585110f0b240940c0c0e92035000886082c40380c2c1d80a5113840d50203000074441e0181480002c1c0141d4890070b000e90000400c07403507840395a00001410f008110000800800c0c003544014000c10640b4448002ca2450303a072030b55210070608061082082902000c104214264804c8026127640031002d03524124460b020010314a00200100e41007020400c81d44580c0d0b10400140c00045200c1d41d10400b510f40748400959111380c005007170352081c0c1d01c1800402c60b20380c4005203254890508803c0410301a840301700301181030035007040a0200c40b17001f40a0040c52450102c10f580c000104061103202511041e881c08281d40c0c0d0302c0c0001d40140d1090f0704c000c0c0710101031645088140d07884c41081103120350340c2d40044442d0b0000c130342c208066595480304005101810805060100881c60a0b058031420130000c2d600c10000407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 673407544 1250 673406294 673406311
    0xc10020f030a18020a031406090c01020a230304060c05070b1606020a024608041a0c1b010201180b01180b03060a2013090908070f06150f030506 63
    0x307403c15800c1c8800001c1d440b940075005040809030a840c1d080c00c907103280c040c43c00e12050f4072230038000400907800031030b8003100b40405a016004442290300c03500300351082c203107003541802928002c100100d0410001480200f1045d140c0300080040e900300350341070076000c3e4032451581c00c0422003e05404103c601001d0785d02d6001c50f00603110034203d0000c91a120b0384880120499030030a0400c202008d0300303407428106080b42032180c00d0303003102c01800c40c44490446400034010841880180030b84418403503402c14103047c08000d203003044100c2c440245400002200c1402c0b03441c050f44d104507203581c203000d02c04072840040084c0c100d45c0d00c039070348224002d04c051180000d90003c11904900900312034021001100b4014101caa890500e0368440004026109954820348a0529212a41c041d00c4040d10095a44c00c08180f000300d20f490120400b43c241e032003044810070400c000710341c0000c041740d640c090040c5c0035000002d80c2400c482007034a0024242d80214422100b04034041000400018074281c0c800e411 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 673408794 1250 673407544 673407551
    0x50a0c0302100515030c0303070f021c0503030f04060f1506050a0201060308030903030106020601050117040201210203090c04060501051c0906141603150302090403080712110c10020f030a 82
    0x440c1012800c1c5041d2411201205040005104002034041421812801d0032016a400b0b2000c040c20150345e44203006005000d02400d0030140007511f000ca00640c8203045800d041104015070b0b58135241594070840314009100d103c5014002804128418507440c01d0041d001009100092044890500b102d1710a0004000001401c049054401e401c00f41c0215800344d031241c1c0707909082d05000c1c0c507600240100760061042d0343c0002040d601c81c0ca040300000c000240c4840c059115030700110f07100700000c400c090001c800d00c0d42e0742d42040c80c0f0744015032040b07120001a0805112034405c10054840d40d83c416030400a0900a07100042075810b610701d00444800c100040401c6e00d4980400540710b4000e640c5e028081c1030003000030704c0c20a0301551030050b100b80c1e002c000c2010014040300c203007040c45c00042e4224002c60005030000c2d0007103101a4005086091008010a2440704082a40c0d8003400c0100402c0d03020541c4003190204000074076110024050550601c01c014000c48500d02004240b109800d44 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 673410044 1250 673408794 673408817
    0x31e0d0207050904031e02071e030b0901090308040b060a0e09030a1701230d0c0609181503020103180b0702070612050f0f13080a05091801050321041d07110d050a 71
    0xc002110080009417400c04012704420f00c02403844d6024441580e0405c105c100240e01c4200611410100c1c0c2c4d4142c851a01ca038440d500c9100440c080205070503008940c118000c41d000081102c0d03a44a02c05e01341c02180d44991000000f00056044500380010350045001403000c1d5500000302c005062406024000c001600000580300450980c8050042e15401402040700e580c00b290100c2a0f40340880c4030350034114070002102c1100c00e01406c60707808682c101c20501c0103600c40c1c1c100c400c605a0140c00140b540702d2684500c032019074141d40c0400542e20100e000c1203101d40119603040301c080c0c2a03c08021030f14180c401c203581084002c0c9651702030309203440001e40c007c2034015a900e105400004c42d83e02c07111680c0b07000e01260300031480503102e601c800c0241d954080026000506940e40a005006540c1e40c0c511061a006490700700c0e00c01c20b401c184404121110700101c0c01c0096180904800c0803030400d8500540500300481c2003100b16080841980c2101790032000301c030b598a0252a086040e1813 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 673411294 1250 673410044 673410047
    0x1060f03092a060801240f020c04051501110c1c03141909091b0e060c030f0d052202010f0908011b02010605030d140702031e0d0207050904031e 63
    0x10480c6440851903414008002c0a001008600c2083d00c0306a1900c62031640c0320340c0700704200c5400040105020080c4602803070301b28815011402241c00c81d00445006840c10350015043c1c560842d0480c0c12016101c1000c7c00c19a0702c0b010413420340341c804016214130100000412900d60030110000603400f408400c582c20148a40c64604c0d0108000c03e40a8a9240c1c03405650440040c2c0d203d440c0c00550400c4010a03070400a00c1800407a22071003046004403039900f00107446000080e501558014028842d40051003024001004201012402d8a50344d11800e4011400c554001c3d0035485421209414178034020400341c03e03103444030340900701403c08501e5030030126940362003600509910f500304005d13000c4c51046405400e01c11110368000740642d6465400381940c99020b28900000600310640e10401241d8000c020301000c0e0025098802000d030b003220754019001a04071148240d840341c0111050558180300320f001a01044481c1d174103500b81ba07100200031134006043e44120204003c01d400e03005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 673412544 1250 673411294 673411313
    0xa0210260c0f071109070905101808030a030504050105070507051009020f060c0a03020c0102010c0207091a1513050d020f04020a091e03031706060720060f0d0c0801060f0309 76
    0x40c0d01986220b03590880c1c4e00e04840742d02d205040460250a2110200706518080d8450b1307820341c5c4001d415003021207203984040324030300181c129807454030348030321004a14030b10184010000110280c5000c12541014a022801c4802c010724072803c0120911071400040e00c0405c0c09140301282000c0414a410a400000d1401d2807500000364071030000034621460079804100707003851170b000703400340c4030307003100b100d0041e802d03034099111181c01604403020601070040c00b80d01c030f01d080c4021900b07e01400c02400c4045948071316400c2c039010000e5404a00e44a00c041214018000351000742c503500d0105d0400d80c08240d4880d485210a4030481e00812044450b81c42000254010441a80041c080506580b2006030403060740c0010780020780b90041c01e4407614009182207000c1d58015004038070388540c0f81c41d0b1040c01280c0620500c034503d1000401d0b0490740c0e845002c2c08807021009240d503551002e02582d6801c0300c00081c00101800b0161004011040e04200d0788100030314a404c1c041249086850000d100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 673413794 1250 673412544 673412557
    0xc0a140c1f1509060302011101090206030a090503070c0e0612241e0403090501020d08240307030c09050106200c0105210f04020f121f0209120a0210260c 67
    0x4182c54410016091820341c00c2101164001e80303880c8440d6501c40710b081c0c02d0714201c11002c0d41240d002c00115610000710341c00040140d00030070580f400d1190716a2020000c18036540b001e00c04201441c14440c2c586000d40c1c01e006003001031001000e1204a03455001090005415100c020446400000f512441d00c1490815204a0354100c4149460b00785400f80c003030030490081c03034014400d405140904a005400c0740e801103150000d50101d00340402220758224184d0300d030850b014007880d4800400542113494000c0649030a9402150940c1402c00090410010a81804424a1000e8996829000424072100c00c03070f42880c1c03c1e81d80340780859501c44070720343d81084100003000380070801000c03000c0e40c0d00b038901862080b00d00340154031200341004402d0000d074a4440e07035600a625041031044000c8001e01c0029241707440581802007640000e669812042c0302c4501c5030b0082d541c4101140381008841010300e0035401c2c9403c5003c0da45005515000d55005a40c10310f0208401041101d91480280d810 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 673415044 1250 673413794 673413821
    0xf060518160e150a21140402040c030e0d0c1205071101030c09051201200f030705030603070509041b170c061303050105010611010b1f0804020a08060c0a140c1f 70
    0x203036510414801000c0c1d042010390181201448254200c88100034046e101c50144000c1c0b504d0407640351a006c01004000c1c0352840002e069a80108103e400024882c0400d0340040c2d890307c2030200c00900700324008000440040b410400200401c81c0000c0c143d00044a29038400c0c47c0004005e0120780c81a100da01c02500155031000310615000c00ea01c030150081d010403070044008880031050000480c01e28040c86002130241d07281400003c1c20284075802441e0710110042c1120721803030741e401c04200f0151055030182c0e01d8280c25000070001c02400e00d400390007004085948550000b1000100c0c0d01c0380c5070450b0562080300d0014090b006100d0301c0d06101c1c0038507040700080200303595402c0302034607800c0d0107a0f10f8102d0b542040380012242c3742c88410200c0e4505419030500d01c0101544e011030f40d03848020320481e4400300c0c40402152600e0100085441800c20800b40d607540c005d07881c0007405c03001d0102513401d00203808200c0c030384c50365401168131100f445480b003040c802441826145800380c00e85042e03a0f0b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 673416294 1250 673415044 673415047
    0x70e0d02130e0c150c0c060a081308090a090b10020f0c1002070801020a020c010212120408030604020c2a040605150f0c2d0303060114030c04090f060518160e15 70
    0x4000ca82c1074002817250451202c11910b03603000d203205011281c000c4250a001007410302001404250780180500c200c140f25102c15440e2407030303180000b0524103560700074010b0300c1c2d40e441e00c00c050b07410456804001400a400200380607040b170a0001c1e5584070300311102e03000d01d043d0109100c1e023034000c00525000d010100c0c029502c0b410241d100035a2040c0c1d1040d110300510401300e2103a6655140000c4a072850402c4d003003054181c3d5240c40d5002d5541c805050b440d0401e60800034007100c0c1c4020310110080c040324940302110000404c042d8100302594600a622980c0342610800c043c0d40c0d080a0702c3d80f42200389607030700e0b11445105d42070700b00350243d0400c00005001e510f08166404200f43c1c550403209640c076644420111242d48900c1d5a0b0004541050100b4402a041140300c002d41000d50b50150411002c2880c041e180e0414400780d070700b141c00c070516840d1592000d11052401000c105012003800c4103416440c40e050843e89240041c40505200340700000e0400382c1c145d102c0c46180b0701d0103600100c506 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 673417544 1250 673416294 673416319
    0x3040603092d022106091b091e040830100e04150912081e01141905041a0907020f0d0c170403030809060702010c120b0301091406070e0d02130e0c 64
    0x4613101c3d0040c00412040f107e0301e0900e1030305da1912005541c001d80403464241040c2c0c403548001c000c07070031024000b9509601305100c101d0100400549002c400240300c403120122082c0301d400014203107400b41085c0c03145042042e051140042a050043d0311039008405042806c44e804400d400900b50b42d81c002e03005402058541803500d41102e04a40203180c01070610b803401d60601c000d6441e580c001e0151048440d0141005001441c0411a1101845040550741c044603178550002d0115190711301540a94824018914560301c0c10752341040e031040326800a0014100340c000e0302611002a2134113001404440b040401c00d101c1e000001038040050811070a0361141c49050190400070201c6d0f4203046403040380d000034200b510602071602614943d44412182604100408014202c001900380d0950358541702c88001c40d100700741c203108100952002d00803031f00b0b00a030000e09448040014500034080a164000140c07a21807159808203c0d442c1c0000704100400000e80c20311088264044e03001c100010007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 673418794 1250 673417544 673417561
    0x40b04080703120509090112060e03040f0315050103111e031b03010c02010e03030105010f12091406010b0a090306181a010501270608090f03040603092d022106 70
    0x81d00a80380502040300441100d80d400311814400c01820310340201000f001044403011038100d0f11209407003100042607180000c2440c44c915045580300c0381c1c0c00c02c8074034010420b10001c0034100c0755203044007109201640c116280c0c080c038807a07030080742c1e4001c9012003601c0c03040c012080880c6010302801820344010720100800410450b4400450350720030f501c0c02400030b800d00d00511900001c00203540203581140c2c07030030340151006003a55003400240300e018601c0c4900c51700c052081c0c1e60b4841c03061903036140401c00040081d241c10300503000580c0030b11040100007a91500031413510220f9a202d480440c4003600c2c031102c82096144040010180d100b4620b2a00c0c1c030820101b41071b0b0603a02d082e65080c6828444081002c038800800b004022201c0e90a4010b00640e8031400481e980541010704403240d03c03400c0a41c0c41e00d558030550002d000243d58500300d00401c40f0706145840d14122400d20a000d100016845040c03006010070000d1256100d609090841442170a40e0702c1d0b4003044405072050380c58400321 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 673420044 1250 673418794 673418803
    0xf040e1b0d0518010b0a091a1203030f07050c420f0c07030c0b070c0c080f0106060824011202040f08120c1e1005070f08010f0b1e040b0408 61
    0x16550800b0300c940c07002c9490324405200b40c480b9404002d099502c46c9181104440c000d1412035150a040003050810700c800f515070201c3c00c840000f004005590303e203007481b40510031941c040e12400070010200015018a100042c180c030004014031156800340041c211030210392042c025881c5007a184000b410074061b0007401840303118445160b00c0d04c3e09540c0b405840e40e880d118000c0010041507101c1a00c4000c81c082513501544010706051000180c100c5803030f0440c0f000c4007580b021003141c1c450080b100408100380a814001c02c1075041040c0e840c24990800c03a100140900341011072200b13464420040da20901c054001c241c600c54085560b1a22200e0403044145140600403003403280340d004006601c190004c441c601c401c0328020f0300c180d0b1402c1640b0a40c10750400020030701482800000341c0c002c8042c2c801c55001320f055482d402c218010401e0081c24821050380903c01c1403140e0301081240d080c5040881d164244404101c03a43c059200055041c2c0e0700454120020246010502056010300000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 673421294 1250 673420044 673420051
    0xe0c130801050c0a08180304172803080a0b091303020c0a12020d05010e1504060516021216060c02010e19020307091e0e06011502030f040e1b0d05 64
    0x1812550540c65403081820307240c080d64100440902080b02d03041280c0300340c06140c0c00403102c01d2070a214280803203801d851a045600300000403480d55418160890301003144141a075101b481c0c1185450300b4940507000d1081a81c40602481000300028441c00c040e40e01640800200404c125203a043c03c00c01100c2d003403540c26046000d40319001080e840c0f4948031011504482c230411a01c3c1600790142c1c01d020308440c1d40042201c4564a40d040c0c2d003000c0c0000c2c0b10f8000c1c1d010040b03103401004e2078a400c092051701d8000d4040341d060021818002000d69010900700283c2c458801d00319a101c10140c5861940c101c2c448000d80340d03a01d090300c40480940c0c10741001c00014100001c8407260300403115280041200408000d505500c8043c1c200300048854008141c000d1902c1d002e00820003045007590182c1e03104100b02c120542264006104200c40903401011580040c4011800c04800742950451840741d13024082c0c0304208040080c0103103007558403500942c041c94003016140d404515002000e0201903 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 673422544 1250 673421294 673421317
    0x30601030c230307230703030234061b0815010228050105061c060902150c0d1b080301090b0d080a020d09091107062c060f0601020303040c0b0a03060e0c 67
    0x2102043d034a00b01215809880c0403941c01e0746c9005015917042d0f0080d40803424400c414084034200040e848203403110321589210711380f44a41d4182c0c542c9000c20031100740d4480144e0402c040b80d4088202a8031000c140ea020303030442010303485140c200d00140d1828111114078541095005c3d03201d400d81400f0041094043e00c00c500a00140e21b40104004c070024a0b61000944003000c0c2100b8004100107401003008a40050655440801c940b61185841e91203010201c005a100703032407808015500c2504030a480c000c0d41c613420048120f0380d860028912062160903140f50f01c3e8540400c2d65a1840075203c03441c0e42c4140c80543d10007011401944606030001e01401080c030000c80010f0b54015406246401c80181c41d0140c41c08c0c0003651641c0042100c4c0e00a1284411402c1421160f16000b2000614440103000140030502e000684990001001040a4115001442031100140459172000c0540c0d464101d420744500030450210001c11556100300740c01c01c03480061100f03800b0007100511148484 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 673423794 1250 673422544 673422557
    0x150c060109090f03030c2d09060e0607060207021201140a0c0e01170a0e01060b0903160b030f09100501120218100b0708040909050d1b08030601030c230307 68
    0x8404401049a002c25409400000d02e07885000010b03110f94481d80300740d00c0e02e041c04842005400d080741110f5400c00d8410b400c0000120441c2e501c40d402c4041030009107500e1506808000050000c60344070f016544005200a030041410401c6698004204801c0b0105600030861080c0942441050500568060321024940255442d0031031103441b0f0a8440f4006844000242c0c908619200360510014190319400e80e0710010000c5a040c00c0c0502002000c489a14945800c140006c050826a0030362a80b030b20310b0341c061401c01100301d20304281e83d0b0020300c6000741d8011381d9680006c141407074048101032405904d0200045035a10402d541c006440e0b000b503c1c01002001c0c5580c4408030450241d0f0004284e2501201c2008105454401030681390b101e40a4a4141940c0784084015124a11000c0322540c020342d132030f0760070b0a40c852001040b070400f070403014840070081e45440340c0350310015200504054840790740d64003003802a10b00c0001e641614110421a60800d145140550030036142d18000512 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 673425044 1250 673423794 673423799
    0x90315060314061e04030216030303020a030e0a17210103061a0102061e090307080712260103080f09060c07060f0c03021e07030b0f070e090708070c11150c0601 70
    0x400183c1c95101d070440f410b104071000c034910003518480c0d100810807411403080107580c401c000302100e50400194843c3c3c40250b10b8020340403003d800e03210704e0030100c1700c203501c0107138010046000d0704100c0b00b0b011400c60840b55070752100003502d800760300103000034514590300034000410441d070380e440300c2c0c048500c0059000200700705000498403100103451131603c510450300806032011000760890b4200307580c0c2d01140e03e8140c0c5a542c4c50341c81e4102130401c1c1da80c40d9160707400a07140364018003480b45a405007031228200492400048400c0350f010700014050070004203414001600075421200000402400c3c1c030341740ca401650195803000c440c0108000240703c03840c006086401101d003100880c2c1d16401030580354444a20031b20b80c0c038511024124961240d100008042410301d404c5034007414004d6144022442c0c8810301030445002c1c45402da000d80c8844003080111a4040f00064011803586400410f0390b07014102003854040b501142036225500d002c0c072800d074a42c0240140303504092075080e266aa0b9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 673426294 1250 673425044 673425083
    0x270628080c010e0f180702030c0109080304060509071203120f06030b060f0a151d040204060906020f0304142101021801120216031206080615030f070503100902010903150603 76
    0x4ca00c1406821507000c01c0350710107000b2040c200903841081171040304e0400401045450035120709480c281c0d841000003061100b440700c07074003e4a51103810320004190141c6041c50307802e000f4016035400740c20403030000100c10801c16590481d24401c1c454410920840b500e90604054080c1c094860620407103e0004540c40c0d8100804458225910054200e034101e4200000380e641d22020000501c1a85603003172080000d5803980b001d400603045039981d041000f81014000380c40c003803401100503c15881404100f140d949500821618160b096603100000d01d0001c54110740e400c5019103c0c996540080f0303040152409041580b503040000343e07120b00319603841d20b400c80c0491203510403541801000182c00e001082c0200308d01210124480c40000740700e81c0d40e104441c01c1c030700150780351344880f00341144d441032910302001200451203920018003107031854a00007076610301024540649094803081e90005680c007402481c002141c0000358003021074003584020000b0714030780c00219164039404041e1440c46 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 673427544 1250 673426294 673426309
    0x1f1203080f0a20070807060e160902090d1212410708130b070207140f030c1002011401090c0215040f081e07060902270628080c010e 58
    0x403c1e0703030101c1e2105440c1d00861482640300c40803d40f000f000800800000034401d2040c0c0c42c0c140c54090250802d212401403100d070b1010030744c1c42000c3c243d00600c085103a56452181001415900003151f80c4034203c0c4c01d405580100b0b400604040035494403480c1c0c986500b22081501c0040150620120106280d0360619a40107815044045800e00303d800242801d02595807035070020090340090441e8005a0b580764817204003200c1e00d200503003100f10100648012107582000e9118221981158102c650000c0b0340e4851a40c001284506180004120503c0c000e500070624804840c80401c15580c540454001030301a030100c040041c8504803c64910041481c0168003c5501c000d0342c1540321000d0700c41c0b4019402103903034949402907202d405294190910010001244144400b280031f21980c01081540d141c7c0d0b0b0144200403414074001c440070311140341400e03480901201c00342209400000c0460300003040b4000100310518074140841c001c0000219400f640c4026aaa10f9443c0b824400b4030540 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 673428794 1250 673427544 673427561
    0x180106051203180f030d020106090605010518130b030106030f020f09010303050a03051e0403021501050306011a03090f010507210b09010b092202040812070503031f1203080f0a 77
    0xe80040c08801143c41d1420050b031a400c900070540b1101e00c082c21300280c1440070b0300d02c4003000740c0e5541c0e20402645449000700e8000f003d007424a0350410030044a80b8545460040c0e4052003031108650703a00380314100e9802511202400f9008024290312803034003000318081284203911500007894502014074003501040c0c140c95042c6d48071410702408a809602410024220400890345411107440a03c81c000f6100c1c8194080e44c020040942203481550003000181c110030300941180006100c0ca9a071034801c50704420064400c90f9981d5503200c1c542c0c0c01c0c2202200718841d15402c00e0300703000850f6130000180004440c150040d61032503a080c0c03a210111001c0a01007a0010b03100001084206d046501400484002908850f200c400000c84139401d040c0400d9240b2900342d0104050080d5402040300c142d0b00303103442d0541841d2929507200c0541c7c2e40030041010000c101c40c84401e1486845c42084540104500407902c503910402d4034016120800c1159440e40481c241702c0000d03001402401202d50 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 673430044 1250 673428794 673428829
    0x160e0607020d0b040807050d0504060f0309020922050706020a020108070e090402090a020d0509011b03050603250308040e07110115050103110c160501110a0b060d03030f020318010605 80
    0x1d25490b07540386010f0320350050054880503410302500b80455401d1280c0900307000b0300e903911541e0314144400038201111800c40c28003003510302101440107844400d03035140c00c84180b00104400c05413944460340c488807201002800d0b80604000002c0c5c21350005040003106100341c07030300d0005594401007200d503000b4084407964060000408030340581450161180c1054400501600c6c0c06688040301e01690740c141d4080031580c0d524044c20141ca1b80d100c1084000200300d01c1e041c0103a082007000203070303a440143d000b2408002580040b003820084088040007c0d030740000c0c0d054485039983e13040c071100328040303038040007003001611104144803040c8039080c18000a406000182401d00e4011401844003614180f80c0384010010011032540410041207100d0312041400045820540010b0001e2413024825134036511036184100061a00c1040302e0b8885c1090b00d001d4080307101414114060404c000c0350b2890580b0000c280040e506182d048020164401c10081c4202640c0c0c4040c0410000810754150 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 673431294 1250 673430044 673430059
    0x90204141c0303091104090f150c05120c040512010203040303050c04030f0311071e080f1c03150b040303180e07120b30060106020109170d14160e060702 67
    0x2070009009502c03840000380545069409040d11002003001c90310403072416105071484002d00d1042140040e584402d40c90101070500c01d4889621000d00709020701c003c3c02034003556040000d46484a118256402080c0c000c043c08000a0301c8a00d440c000c0d0302c1508c0030303070000e0704060002b01c00500355000c0302d0481398000c804c60000229a1000c84a42e080da0340c48035034038010501d000512000101480310303559001642c060b00140b80240640c0f926070010700c4031280c0e0300100c550704103040700a40b8803102010642404591800500c2c4110072074507a0b40c000d450f060802003008001c0c140e0100b400341070310709100c0c810f403c0d0396102d250003001d040382107841d0400115506082071108140c0c0e000301032541c0c0003138007034443d88183e48000b043d20b03607196544103980341c071550280c603242c2c0007007080c58010f0680340000c1120f800c05468110b4121140c00c6450462840007819415a909907402a60032134a0000c1c02c1c401070070100208100f40311202441c00018a0354035000c581454014115a02d0550003003528 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 673432544 1250 673431294 673431349
    0x21040902030a09020415140a151b05030d09141203060f0f0301090f0309090516030207051c03060501020c010e0a030605130f0c05120d080a1503060609020414 69
    0x802079800140041181d5880e83c0304a8010307111802490400c00b81940080d40181c24861903414030004440c2d1540714001036441040f08001a04501d21060030b14038000c07129050944401c0c0d8080d0030150000c00b1440001940b48001d0182d40c0801d4001d031060016400d20540201c0e02e580d10070b040643c05030a183c04102045440c540305081d500c041e500500681000e02c00741000900719110610241c07082d00701d52103034030209503101c00030034040d00c0028810421070a02c0c0d52441e105481646554083c9940000e18030203000d010005201c8507079800c08038000b01401d00800902030210380c0704481c0580310b041c6040f0140c0d0f003c2c080a0900784000303012540482c0ca103441e580c004d0480500201400c0b000310a240010815500004070b4035405401c1030365038185804c05000f50710b8200b00070740c1240d802c610482c4031126032000c102500089012008140710440100c0450b0740429940000e15041c80e00700005108801600a03008480300b00c1041c100c2209a5028003421b0341a030380040c80c4038040c0c01d210 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 673433794 1250 673432544 673432559
    0xf01060806030c0306090a06050c0406050d0903030e0607090302010306143604200d050a020d24090c0f0605070f03030b0402030f0a0e0f0d0c020609040207142104 71
    0x159a400503000b4110303240002d80b0300201e801c185081e6038080682c1c01203100c4806100650040315004444200b510b850140360420080c4503000385001c00742d226484820711010325100c1d81100c2c5040f024801540c0701c07410040000b401a00c0c052000f20f011a080650000382050000c0d985041e24a0160401006222180107000c1d600183c0c032200b207100c00d80e4920321000300c20340d00c0c44a100d244140003850b0f6000c07906001051511104031098030940a81c940100052800b291442041e541075038000358500b8546410440c0410489201c100784a0f141d003000c0c1c402c0015001042c2090041100b5110151529140c15941c0c45030300030306001c03401c01c200101c001510f0807000d90015000340380000c0c1414450340064140ea00a940716a440c43c810b10a0100422991240307051040142c00140030846808400303a4071801d19280d250203100c84483e104081d9100c00e0112603250340010b0085681c0c0c15070f8a45801c040e010458056801d10500c2c283e07065880440c04a40851440000b101d82801d10b05182c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 673435044 1250 673433794 673433807
    0x9030b040507081204080c0916111e1515060a050d06090c030e0f1b06090102030d0e0f06070c081902010f0608100b060f0306011115011d070302030f0106 67
    0x1119948954070000034400402e01000d5104d9000b20001a03441e0700d0f08041610b030140c2480030034440e0f41d0000601040355003102101900b22100c0c20711410310841c58a1180c03e0482d800e00720741c41c0e0400d484240c82c1800300400c1c914046044102502065103800c84075410b11511500c00940155041084030100b50068011300500d9a90100100f0007680f504c880505441442c201c0101194440442c02005003084c0040301300c0c2c1692800a10350007030480b0f00c03252481c02020703005000c0c0c00300103207103049640f003842240c01e807000c3e0301d5060201c1125548161fa0b58416004100710303902030348000c01e56a5200740c090800d1250070020320360419900a0841d042101244a5601551341c1d8907290207180d62140180d0008200c00c0c0d005d001b00350101004041036404410050b44589410004000502d02480030780780c2003074003072812030901c080e00036081c0d2408424074040080c15425200020b01101c510140559640e5911840c6689407900641501a8001070b6007224002c41a50014040300c0c2c8a0751 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 673436294 1250 673435044 673435051
    0x61d0901090929040c0e090601170a0209271507050306040e1006140114070f1703040c0311100c060c020c130b030c010219081c06140910050109030b 65
    0x82e84089600754241c42c840003003803280f24001203005024200014010300e02c0000004110f4462016810b2404c8205aa1201c4c814010090510a0003e02605a010402074280300e41e60291400c201e9080100c0e240030348080c801030480500b2542240c111030b44c40301099507070415100384501c000c0b90320303000000c2d0340541000340786030707041070b902d514034030702150100f203c000291819100020b485042c035200e481c8980c1004045414003c590720b940d402c81211b0011141c1843c3c000901004044240c5811500d0080d90b50b03036606070042c04024042409004901041101d1060343c418400a03030103028041d81c04019070a805c0450074190000c4040b40301c1c5e070840c2c08808524410f4071080c0c0c0000d00002c24a01d88401908038117079440c1071091060404002640b0344035001d000400d190b120035003908104200c07150008001030760101c4c107501c00d9400d4101920060300c80250034440c99031a020003e19407d1010403030b52188030301c0008200068807003140c41040c0c0d10180e542021881c10340d00c81c24a07125016 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 673437544 1250 673436294 673436303
    0x804060509011b0f030c0305100302061b0708030c06060406030b01050607110603070c0219080d180b0a0f02010f09050d05071401050a0b1018060e030f010c030501061d09010909 77
    0x1040007800d0845400c140001c14195600d0303131508504445001003ca8400ca4881d030140f51800d03080c8100640015912412240e046844036030f9a400201049020108008070024a1043c2e207008038001c100400a450b0118019084030010f5407940100b0064801c244000b0708260b240c1340040c0010708013400100526402140500b240004100109241d41c0c0300311a10000215110652400c504e004240c42c1ca00e40c1c0c50f0541c203807065081140301c5858030b00c40092507081c41080c03070904950800c03500b00301e0000c2901e0401180c85284206014000c0703000c0e1740442e00154a046402c10850145100701c40079035070080000c107515030040000b540c01e907000c403105507096800004d9601ca0f4420034019103205611520780030944e00050814408844042d449071400c2c81110b015410f180401448440304940e120319181d0305090b0b0a0340400d042c00d445400a50f041c1d403d1400d0300071003a4241c3c015504841da69600c081a0302d00940703d18502080d645104da90100c900d100410500165410070442c642c082c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 673438794 1250 673437544 673437551
    0x80c0f0909010b09040e0105040213090f0f03020312010b07050709020a0513080c010806030a0809010e0607060903030b011413050f0a080312060108180c0904150f090203010605060a080406050901 85
    0x55000007490588240d100399411080090421a00c0c2402c1c002d442c142c600c440c00030f004d00d0a0550002d100c1e840c036190310000099503080c0c204184010304c001c0e0100280c11565100c0214800d0400075140d40c461200084805500000028540d40304c1d0100d4a2854000000d00381c2c0d5800c004920010394050650041004403c1c0440005c009601c02a81c004150b094014a42c0003040c000240c0422001807103c1c3c801c0d00701400b507001103118041101c420450900c0d00c0000e030000e16001828a00454102405041c035004150040640542c4401c240a0090b240ea12071a030180d48882400d1154400c11200303c103604800f0482c909068070b4060141e50000c20343d081190b100e100e002d2442c0c011100d0b04080f8000b1406004155800190003900003001c2216a0301c005150f5815540d01c0c00001802409002030000040c2800312440401010500c88901400001c540d030055002038a00c02c2001d91183d4a42400003a852415030200e84030715410340c95800e660b59484c0c07a40001040011300e524855502c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 673440044 1250 673438794 673438807
    0x11030c1615030b0a09050601031b080f0105060310031506082401140904110f03070f18021801121112150a03150c05190905031507080c0f 60
    0x400d01806440000030301903000e0041c507085851011000300c103a01d405040c80c004072000a44c40d44018941542c0d140c8002080a440d8000103d0080c0200c0124070000d1030382a031020b030f07003943c0000414000d00e03091104540a980395810031410b4402a2146c0c101d18081c0141080010503075415000400602600091a642d480e140507003451103c0240707a408194281c10b2495043e00d504005001d891000303116400040c4803c0498890600604050081c1a45489040c41543c0300300ba030b00303e04500603059802084d075400c0000402202da01a036201008000f03103131310404150380b0035602c0c08083d03001544651840000150781c00808120140c94050f110800d00341144880001051400c0300180410785901e003850340401c1c02c4440303148040c442c5040c048104041440ca1040300c000090070800001c0303400c680803050308d491043d908030380030003507200f036490503025002004003007140c0003900ac0c4c41c0900411303006400210f408555001c007168091001c98000d600a1000e40404458480d02d0740c074007031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 673441294 1250 673440044 673440067
    0x50f061c08040e09070f0f06050903010b040e0c0a0608040503162303091018140103060f080109060e06091f090506090a1211060415060e0a0f05010e06090402011103 72
    0x2d001e5042851800010b40030320010110410200c4014102100c0961001c1d04041c031017403491515204c2c2808000020490b80340b02da8081d0300225400c94002d004000042c191442ca0b40c0350381d19040302d1449010307c0440000d1550081c0b003102d11030b81d840300207945003c2800300f0445010031480d0f003e4a003510003138022040103004000075084201103000442d2142048000c0040042c42c01c01c00700c00b0080c6464036119190f10b00c011031403e0303d0183d11150000409140101c008000551050b1100e088854002034052010740c00103100c03d010344014410124007003000e5580d410203071070207400382c0c0c4002c95000d603165000c900b407010100d10810114100c6001d44516140c050181ca00b13190350340001c2401c00802040c0c020364102640b00c0d040600d10401c1a01005445500040c00070f001080380080c1040185000d51005002c0c144040401800781000c0f0f907002c0050156207407454440e0326100c0041041c0140051041c810300d0001c00341a2180d03100e5004599140d1000744200480c80107004464001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 673442544 1250 673441294 673441297
    0x1009170d0e1b100e0315061216050a1e090207030c021807020c04200310031b031115070204152106060b0a0e1002030f07061d01050f061c08 61
    0x100b490385201403156120342e00704181070503450b01280034404034566080168030041002151020b40380c940320300980c2c64501080300040b441e0560315090003000d049080304400151383c4400d8a10540740316a00b030f510740a0f00f03902d1008c034030480382c04601c04d100100404041c503002070154601ca0f280000e0000341c0c50307001c2000d943e0f0544407524007551041c108030f40f040d81044481140c3c1030441301800003140c20707004509082c2c600d500540b0790800000000e8038034090542d03144001c59001d0301c80c802880d4201030007501c6d0713500d42c041101c070500e249040c0400c6180c40c2e038254041d0184455140c1c03401205030b080100400c84600c1c04071492505000000ba400c0c1040c0602040c500c021054103c1c82d086807401e207040f40c16a80080220401c148811080c69911100c4040d007000152400100380d44028401e0307183d0300400e01107c03107a400004004040184a401651040105000780e0800c10029100300f0700343d4408a60203c450425000012030340d281044000d89804000b083c08450b400310381c1c8509109 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 673443794 1250 673442544 673442563
    0xd0c09110301031104150611120a020706020d0c02061801110d03020a020c010801080c01050a050403051207030e0f010f031143050705040c140307030c021009170d0e 72
    0x200040080c00a00d111a8070502e000b11010000406443c04654006c0000d000c0c02080003842c400d05101c0440800110a20325041c052942c3c6031840c0100095413000c9a01404005008a140c84000540201c0580e60210307030041420b401c00d02c1075000d240c0c105441c0c400050402c255204038449100081c80041108402c50385d01680d00c221900b8044c0c03419043d410b100d4100f01038100100520a004580d008560302c0920b045580d4665690017100d06001d190005403140c05020f618143c83c20702c00c00100b03901882602c070090596064401c000070a40301500d21408588000b22500100303220fa400914004d10403d031103420110117040d4100b50304101c2c2c2c8541401040210840c55009021103802407104109c100c5c00728419507640c03415121000c1d441054025916030352030801d83e1380105041c1c03071866008815903403a45460308005000c2c24403190141c003d0f000d40b100400e21a082ca02554090750303004402c6054407031512401c0c6100d5403101d070000c41c52640d01c4101e80e201d0681403000051 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 673445044 1250 673443794 673443821
    0x70803150105040914041b080a0f0807080a110d080c031f0906032301020301050114030a090605041a160c15060b220f1409041a1f0e150d0c09 62
    0x8103240c98a1f1001803007204821110754150048010064041c0000c0c0c40e0b034003242e1080440130444c00b580b620201368000c000c40144803220100710100c64560084115140b2a0004122590b03018541403e40e50b5200581d848458000104005900021031100c0840c51040c000c41e041a156565a240c0c02140c00a07041100c40c5030610200c83c841e640007e0780d0080821b040002146154035000021701101c00c1251141441007002c00018900c0c06190320038111560080c00a204a20341442c02c20b82c0800000050510030300c2480109031a00506a141007070f40102d91210070130a00d03151035826140d51103001105e0203d07100d000c0482d0002c03612003d411072040c10040d028810b040400724061010035a04912640c03040c100f4100311035402000301c0b10750940103540c800c0381c0351610b007454100c00181030201c0c21209040390038886407911a03807440704546036002c1c4103c1600d4880624401070141a15a044a4504915051514071380204400141c51217040388940c55580d5950303e42c140c415036400ca12 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 673446294 1250 673445044 673445081
    0x31608191104090e0102091f111b10020c0a120807060c05072001050304020409060e0a0825050a061d100f0b0f010804060f09081b0708030708031501050409 68
    0xc110f030b966008601e0072020000080d41020311f0100454003030700100c3c1103c01e0803000004050002ca0098120342109040070082e11900d202c1c070070340464050443d4900038019030070200c4a1840302c0c070200306001499801800780c0809842c11024640c8100d44d007109403610f88080061100145141c0f14040e0740e4a001d03180d054030b510b00340c01d00540c04560f01010019141d19040d0443c56682e20204581d803282e4100c500141c1c00c2c1c2c1c03a0800c580100f80e00708000d6100d1150340c01c4001842500f2000d400c81c0c0602900351030502415200d00246a10483d0340140341340e21a02440c0000fa950f9004584004200c4098410162130b00c3e400d02d15141170701410030701c090b5440031601042082409410400f02040e1902107a418101c0300081105000600160946585225003a04032070b464010b21060b42d00122007a8488100c440300300001c100f100941a40b41c400c8000000d91042c0c0807080c0d418070754000e43c0d11030a40e0388003087c2c1d010840c0d000005a0410104000c00b1510040704d1003610060450045600d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 673447544 1250 673446294 673446299
    0x5040c120e06070908030406050d020d09060e010b0405010b090112020c03090312210c0d090507090f0204091401050d260301030302030a030c080907062717010c05031608191104 77
    0x60132031a501e400401030798108020500c99a81c220044401d000e0340c42d4401640d039044080d00d04010068280000d00700c609000801952071030542115a50740f008aa0402030360f66244001c040b0b500c1003402442c0404e50004900c00c22030002d901030324200380507a06407860224000e000a00b41403900000e043c05000218102c500d5455000010041d0316070207086c901e5a040c850015036050040650200c145515a4180001c001c0c062250fa401801c00c040306100700030a04002d20069002801521317803140c42d20b220600603420f03082803281220006401100d1070007441e241c8864407404082d1040380e0b0380701c50b062000c00707540c110001d500a60003540030310344400030b141c001420b82d07805105040c1001542c006010100c2c0001c50303001c00f01e841c1e90801c01c5441945c031403100729420b0f540f45440c1a40603080400100398044000782c04c00d08603204000c0005180881c0c00740c4d001d000541c0c5103603143c48054001820280650901c0342c000e03000d2405581010300c0c4060900c181da4201100c1c190240000c20704 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 673448794 1250 673447544 673447547
    0x37080a12050903070b06060c070305070b221d180d0c15050919060b090403030e160f14030a12120b061c020313170901090603021305040c120e0607 64
    0x2010340119910b000703503103802c500f03444000030744201400705032041c80300090728203600c0c50405c10722005503071181c04e560780d03155651290030b025080020f913000c102405210140803c21082d86420076911002d45405509801c1a1030b1010300c03400a01c0d294405450000c0e0030038201080280003800b05069403410000006072a250720031a5450f400c0c80d0f031107400c10041c8034030000042002411885190010112020030f41014009440140341c1680c0014586090005141d4546c000c0a1214442c1088980e01090701781802c002c49298444c01013929800340c000c1c458030300d0102d0003142d0f2601c01800c4814880140e2902051a201c5110358000f080303403140700c03406242150145241c414001c903403403030130441c000b59000c5070004035051003020716a0010008071000220a12f45011a402080310610351107a0002d038840b952100c0c10107804143c007030310006041e0744240203c035035079806820341c1c4820304d1800b001d1002a202c0d003180e075014499950a00d407000f40885c4902c2c410b04003114020304d07280c10314140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 673450044 1250 673448794 673448801
    0xa06030621031b122705041806060b03010312021216151a030f03040315090201020f06040506010f09061503050703110c061923090a02040c0e030f37080a12 68
    0x2000d19480d03800116080d804040c090345c0c82c11200b042c1e42c041000c9001124800780c801d1040c40c02040d403458058003140203641c0001a40c1603901c1071998a10304d081c012416a03035220000780111036007030708000c0180c038400e250b085581042d104251400c1e540140103030902c191240d10011000b150796035603c00b0040d18081100c1b0303100c0b0480b02c0c080c628140c110b803105203101e0203483d140c40707c03581c40c0c030610790031a4070030001d1034010280b0b003050b1846821300d407070540e0300c1d00402c0c0f184000c180d0300041d010400d015984030f45001c5841960110f01d4540d075002054016000003801002815500c04000d140a00d20500402041d1080c1c400b80029260100c00314800041c80240c021036130340750011010b00342d4280d0214031000811031030400c0703030395450003402807811400d01d8000b9002070a00700340c0b2402a4101c1080401c244046040d5045040961001039882542e5401c4441848107149583e1113640076030f44100c07601042460b180440d2800d07482e001004e41c402041d030b500044000c804000280b10301d10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 673451294 1250 673450044 673450067
    0x15030f0b04020c21160b0a0b040501060c121715090903040f03020d060b03011b0e09090303011503061203020a0b070905030705010e040914010b0a06030621031b12 71
    0x1c034110300300b883c21854580d4a1303000c031a04403003504424151440008101050b02c00407001004440c003540294500103038146070540b039044100d400c080342095907241601407541038512642d58040300307562640ba25086030038561260401d00841a44901c0441c550045192091503104075003050a032140041c082000c800402905103900148002d2216006031580c030411290119148170300c145c41810044004e09003241d420381d05618120400100300491200c0c40380030032040d1506080b100c0c0c0d6206026040b40212041e1803507400400052100080008200c2d903501c92a02e40003408a440e2940c0103a02001250240c025074402c5d1811000c00a6041102c0da101c41c291510200081c42e142c08170759200e40a004003410320540c02039000c01c0d61a00e9000140407034009881c000d1030804034003018000d2915000942c000c040326034001c40e50500138001c03001143d0300c2c01c80c9480c038480ba0a12804143c0d00c0031108800300207401030700d007040c0d25403100107071141405031410502d0b21107003010150400704800c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 673452544 1250 673451294 673451299
    0xc0c0303050c0d1103040b091314010918021807030905030301030501092112020a051c0905010c030e06061905060d060e010906030503031303110f060613050103022815030f0b 76
    0x408010304c0680c003200340c804461000c040c194a8011403400589542e005041c0404020700d04025041b01c4c00754150b030b85049070a1390320304001c0141810741c9030b0070501d07000c42e01940104060420400022611103d154401240d140c00120803103c0d950740d508580c0207a04c00e4400340e440f01d11003001d002000d101d0854010b0384a076a000080364810003e04002c2c0e0992070b4035500359010800100c0c140c003805c119020181d20f164800c40714135080310340c40024243d00f00c2c01d6039190329055403003100034003074804d921041144400401d0a07a03a04810050f41c01244e2141d4012034948610015540c0c842c9005008550645007021a109041c0f80103c51800c405030b1100300d020341020300803c0030400210880e90054002d2900700750b02071036410242c3d0f15403803107601c1c1c00c0c09100b2046060b291001c00b04180b80507040c12100482c0e022540350110041d81e8003800040d5100e0048451004101083c03400103044a0300c20004074102d039918220000d5441c10b0130321050200392108034130501001c00c5d10560103105001c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 673453794 1250 673452544 673452557
    0x30302070c1d040609060212090a050705010513050d02032e050c04030305040b0d060b0d090605130b0f0405010b04150611061909020409060c09060816140a0c0c0303050c0d 75
    0x7400b001402501002e800584056600c0303070068207000c0240c0446001d01d03400854648181420003040da40d454181c40142c89078004ea030030100344c541c499001c44610300303600100100e00c0c0b030800381040300505000c2001c82e0b041c402c0ea1032000303401d00106106007501d04106948107044840300007580035654000e040741c141360000c010901c0001d80140946e0300382c2c1d01c65102c1d162104602d401003801006103400c4144031680c007041140300c0031204e4100300e2009114070b60900c400d450700b60342c00800c0741030070a0050402007100002843c89071081a000d500501032400465802000c43c0440e04546451540c6001c0c0003a0000c184442900100080c4e0300c102058020007043ca02a01e580e2008500000c40c0fa0f000345d29416010103541c2c0343d420440c18981c201c001009040c400a0000c0e18a1001e840756002085003d00001d0810b01c000040320450159911900d40007603a42c0f01a00d4190310029000d0248a11aa10000480c440c03540c0c0d17a021f94841c0d106c1075030301c01da000302052601011210740f404000d0b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 673455044 1250 673453794 673453829
    0x12011d0708070b030c0304110a08062202061b030d11040303080f0f0403030b0d05030c071a0711100306091d0c100e09060a1508040c141c1e030302070c 66
    0x1404a9034400d401c410000e481c0d4540e450006231000c40442c500303030702081140c1c02103000720340450034500580c050401010200d80c00329a1001040704404069401728050001080104032030745c100190f02c4070305042e241740c0481252403100319912185d100424045c04035090003007582007591180c1011032039968140030b291042c0171000303000006100508140d00c2ea01580700680b541c01d038179816964801e0680c1d84800e031222403030b55580301e240b1030443e105228075152940c04079100c0440f4415034001c1d54403085040c2e840c091207101059009a14209541ca00d4001061821803040c188410031580d5101103041d55030040340c1c5490082c800b2103100740c0c0c0e6510500422a04003c46003244c1e030058981a10903616200041c0100b030956101742e401c180c176400e0f20102194032180051249200f20451811241c640c00e005100d61b21864030550410504a0000701c4500c17810f031201a242c0c800c104400041c18100304a1040c000c51440c100c020940216182d000c200c660b01040c0043c0200592100040781b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 673456294 1250 673455044 673455059
    0x20c031608010c0503042f150d0516090e0c040f091506180302040e1212040b0703050115030504020d051b04140c0316050c0a0b19052412011d070807 65
    0x14105040100701b1501f0883e502000301400d044214948401000504c1c101e002d006003c1e0389a1164015800041c940070000b0010742c04604d2148040d0501da440c1c280c1c0714100a014803949a02a014159030311091000150180b103264595020340600d04012400410303401c51a040c00b0456000740d02404900b0611070000b1114011060880781c04460108044410040311030400a10345001460078000081c19011182842a01e60045204814188140d0303200401201258000e0166458503514034903401565846508502e401900041c0340f49000078817651102c0c80c000d516446060080d081c1e0146184038a0180b10783c9441001a40442d800c500e004054800b003840020050340506200c1c02111014610420a40340c82000e02c0307048601c16022405d21410034001180c150621702c0b003a01d110010010036000d40d5005800182c031003100220744481e490448403108840b80c0c0c206800403a14038042d0760901500200c00281c41b03600c0c1440d0716002040d41000455085208103030700080ac10403850 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 673457544 1250 673456294 673456313
    0x15030809040b0f0607081309020c0a030309031b0605071101110703050f040f060818010e0a120201021c05010306060501020a0f080d020c0a060b040b030a021f020c031608010c050304 79
    0x6030088600290320388032100001c2800485208241d00100c020813040d00f0000b540c0018205140d000203810710300c0f0340d5242164268460002d902d03000340c1000c443c000000e4041c0d000103141c3c52003400c0803d17020301d030346400615846003294103484154584080c00100c40d04404a00001e0200c48000c0c804074200751440c940b20b100f034010040c01c0181c00511132866045d001d040d90040d2400160b0a141266030748001000304038182d88071103c00c140441d414501480501c614220503811801502c4d0241c8981c80e401d1410f044004550159502040404511400d080b600064148a01e000041550450603c1401c803082c0d90065410355000c81d58240204850041c1000d031340d40e10012080d511a40d102401e070190043e40c0301d07006184220850385003089840e4000d50603011041c0c03000c1160444400c10540c1d55a5000c901a410030a41e0b81058030401c00031980c0305140d511401106d140c403e9205c0402d2030712880309080780019403400c505104042c400ccc056001c400f4201d02d0160f08504003a141e22060 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 673458794 1250 673457544 673457557
    0xa08010e0c1216030b130207020a0b070f0f03050c030d0e0d02060103080f0d14010b1b0127021801030510060603020a050d0b040f06090e070b040e0708040f0f15150308 73
    0x540350700f128500b40d024869004010b032181d001e0702c903990409011100f84c019401c24041248a02002c0c000407a1100c40e050654010a4110180d9992400c668907230501c103210381c10003902081010412020300140800c01009590f000f41400078200ba1844906818a0584484003003103411a80042008c140e00c00241c802c42691404695541c868404041006046642c450100c01070f00d5000058612109406811344034461842505401c0750f00400608940d0242c40801c00100004025103440400051907a21240b01503c0910158480094041d10201c264000c071111350114034240b584003400d0080200074080f904007507003401d0100c0c8029103a070062241c607110855403400c180100c2c2d41c0c0d0b5003207005410201c000c1001000c0d1160201406480c0304411203065104122001414040c81c0f81160700312421007921010a88406404446014000d4400d4480000307081609011800852000b070300749110310b0440351400c030380f000d0b0b036003c0d00c14404100c060031448003400c102103000ca00c121500d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 673460044 1250 673458794 673458811
    0x605090412180915080d091520060c0403021c1106160b01080c0301110f07170409020415110d020a0803100b210c030408040308130302060a08010e0c12 66
    0x1401400c1001610b0090203034484007006082011040d4402010550b440c180c40001050354049040c039542944c00c400244906210251940c040c036054621807246007a0103190712024510310800c1c0c0b66601e28048068400c4420030200150400845c0780002c20301c54984a0118800c1054046450300744000049200c582e0194000003541181103010340d02541107036a20008a88442d61200540740e03442220741c142a00962811103021003402c0d400041c1c0c0c442d005610607007440c02101d903851915800b807829034050fa000c4284800300f20b40c0003900103040541510b2101c44189100218010b01811b4202840c10594001c01030041c40c565020500300201900140c606580b40c44912001c03000d90855030010585050100b80001c038400315046188881051500c000c40c561605400030983d0320060b03500400900040104100086a000241800e161902c2a50b034047e580e03500410743e00d50044090304001a131000041c44480722016000d5000008441014101055a00c1120442c4400342c80ca60 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 673461294 1250 673460044 673460057
    0x6071b14160617061c0206031602060c0c03040506090a18020d050a050609071103132408090d0f23030405120301060e060c1903080403080f0415050a11040b04090605090412 75
    0xb810085d129145000c0c1380c0c003800340d907924a00950041142100710400724014004c07500840e400100000c107a803c00c0305814080d600d09880c1008202441d800341d610a9000000c280300010314004103552240c00d44030208016030340c0e019104410080300c60040041c4040fa190030180300b1a40c075011961980001203040114280c01000340303039482c1d130090000c500303552020140041113100b024080080645095000c0842e20480c000003654014403c680000c070342d900901100641d60303c2680100404003103810320000c1c110980c602e120010b440d200e20007084050001c240020840c04201609052003030010356400d550410000a0a000546513058803c1001103004400300f82c2c18400100480080341551440e09030b10f2030040c01084003182c05030007041a6400280500324198005441150b02c04007134400090141c074203c005103805048a841036603289024031590420341c00500103401307040182174640d45000101000d59070180c120b80d010300c800d5814003001842014071403248040d24203100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 673462544 1250 673461294 673461319
    0x12011508060f010905100906030e010203150613030602030c0a0f030b03030414061216230a1101021603021c0311160f060f060906080f06071b1416061706 67
    0x120741d1500380b50082ca034008103465100701b40a03000720341001280e10586041c441c01100c8001107080740411650741403021440540043d00740fa0101c0100703c0c02208200c0104c00e242c590b16941d08a0700201c8540c00e003200d000030515283c5422a01000c06110310b450b051040781c44060129071030f030059106183c0ca5118251000c400c6586100903565941c04851040d00700c0d1400015a00505c0c404100c1a40847c0040640222482c1060007074940150b407144407034038060140004136807082d0a24a05402958280301d0042481d48813845085035501036402090b41e058902d210b4004031040b18601c4c400d2610304511850011010425616041651404400e070440d150506090080c041c50000300b9003803502c1603842d01800c6a510404c16103070740c0358003004625210b00701d080c0d6135684011443c00b240c0c0000d001032941c0303220301c0d4008450a041014200d189820f5992186844204090f0414a41124120180c0c862040c010070340200701031700e8004043c020380a104148103030060a500d000fa601d007503c5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 673463794 1250 673462544 673462547
    0x40c05011403072a0602030c0919140112020c19020103060f08070512191a0a0b0108040b041b06050c0d090b0d0e030f1605100e1009020f03030a0512011508060f01 71
    0x414100d904108190341d289008d41004001f81d101880140c441c5003804070202c05040361008200031369000600b84141c07070726030b03d006581000014002400e0160204107080003048103008610128140580f100311220551001505454072070300802c0040c0903000e004c001020300000c00c2005c032041624100001d00460f00c2d150b060505100c9008026841243c1c214104501c14001d41e0783c00c40c0070341001010351651045103080e00d1411056600103910328001c0b4000c03911207a1401d411520900300c10b21861080c045554641c03015501000204102240041e40c10780c00740036040b4603010524000c810789080a0f03c20f0141d00690030000c02c0150340320340c0400b060400b001120440d99024905607200c0e11103c082c20104461100f0480d000e029907005165038000900940c0383d11a80c02c000782100c000719222400080c406030304143d074040b00503404040c1e9910144010301c0140126903c2e5640c80c8081c1000780e03002075040c1e00c16207020904000300850b0942c8542c54641019003100d8140303251698400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 673465044 1250 673463794 673463867
    0x1c0e0a0f06110c0304060915050324100210050f010815090f01051005120c0604170102071203061d0f0c0901030b040c091509050a0302090c0c010203040c0501140307 72
    0x4205504003000910f4410368000000940219002d40d625501c0da030391a40c03c101044119018a0404240180049411070000100d001546510030380080204011070000594040c80202494050f070001c80c7c4642142c1018000d01c4c0e80301c20100500c0c1d441c2d51414642e542d6a400200c2c1041c07070340c3c0b410300c08155054802d02c000c40011180300000d1041d4140402c04e40703082d1059116a601c80d10b05038501049403500070541c402c5079100180954245460003402c2c540c01d138030700060500a03543c01c22030200010251445a038144805990002d071271818000e01701c0e00c400c203035900b40d29000109002c1000203421210702540c80175260661a88070f506850058000e85042520310f03901c00d003004160842c859004d00c1480031030b4880e0304212402c3e82c001d04203440d60700740d03801019005045800309001500300000c260350030440f4510a10700e03240488000a007260410f580c1150030314a0090200240d6034405540c070b0001400e20026461800c01c500054403c205c10a10311400000c0c014000c0b802c1e0040d01d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 673466294 1250 673465044 673465061
    0x1b0f0314040f030503032706180a050a11030f031215012f0c0402040f030204052a0432090403050d060b030f09010b0603040b0a0204030c09021c0e0a0f06 67
    0x280344842d425124906242c4035082101c2e100181810301d14203240c500040301c5c0c503007002074506024001c952114202d2144e00700d800000824640310304004d1070001071040142d030101c0c50164050590328a980c0d001c06080c4644c0c0c11010980b0750052141c030a131000690300c0203070400302c11581200400040310050b0b030100c03143e006890313a00c4403115107002d440c00307070088035010040c40906440040501c0d0b0108800c902650203800041141c101d420300050826038041500009882d03201d10300c0051505100900c290141c84045008002060810103403070a070905600c14a845100d80c2c03180700c1c00c41c0003003101c0c40d03c010020384603001e07131400320b000d040c002c104035186030700002400d1158236220154034419a0054801c00301c290020000560b61020611400000044c0244118610b441e645c8410305042c1001e009569526802c10000000030071481b5017800818a216025841d0a8042c24481014039042403804000c1d0070580044260b440201d280040700d40e000f0540c0f40191024100380c8010300461 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 673467544 1250 673466294 673466309
    0x70603050a060b070312050610020c0607051006170c030a1104020304020a0513090c0e0708010b0a1101180b10050a1701150f050901060309080904110d1b1b0f031404 72
    0x904d09051507408014042c0c1a9030820090020b070b1103503018000d800019803800750043e007240d1152240d43c80d00e038000740403860050045540000407081031508842c41a8084800d04080118411046205010b0b445001d0004c070042c4c40741c0d81c15500c454a0110003105050b20580c3d0000001d001c540d5041003040190401038490000c0440c41003000d0000e02000000369075a01600384001102c408292080d8450344556590007056464103000714000e0304403104590600c0307031120384c03000c1609091140c01c2c046140740044061301001e82c2441da0f00c082025000701f0341d4140d030620601450301e90003001c101f2104000f20428040818401c00ea004010000d0003174100b03850b00304001040161007143c0420740714100c640d610b0a907a03540e0260121240140010640c0409002c004810f00c0d2580c40804023020342c544041c9071204901d60803040b50080560004d100c2e43c82c6441c29070b01a070150842c001c010743c1007100c489024964542c004034100101000381008912039165184040c00e41c25200200500d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 673468794 1250 673467544 673467547
    0x7110402130b0d06050d120c0512160b01050303090a0314030405060729040c030f08040e0901060e0105010908060a0c030e0607032a1e092d050a08070603050a060b 71
    0x560418502ea03922030007003040f03010f08045000c5410301c1c083c1d48852410b9400420b56030a000d40220650700124100c000b5a201e0060041030020059044010700c882c180e00102c0b0030300f08044d031810041101b0706810150190f8404e201701e00040e1140074218042c0c9400c014000d50014140c1c8034240f45102e9a04410340001d000302e5501c00300001340c551141d0011081d00684184160f419881c03218802c2240c000c2c2034040341c0e04e020004100b80700714070304210f8040d0305c01c14a415100e03c19a4000c0740259000d4040341e41d915000c01048807088540d41c050300007480c2440c100351800151503920b40001d4141100d2564687c0c3c0200b445000c0d0b40075a01d19064038043c0c0d02245845440603000b401c030011181a01148203114010709155200781d83e8424480c0d0b1581d507141590084c2541401d01400540302c10b114050001190700c208200c080107451090035001800c1c00c54105c1200c200030810340c8030034090000c00500340405140810060103590b180e1900040300e540e84203a0368064492039101c640d0b085070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 673470044 1250 673468794 673468799
    0x337020c0f04090b01121e140616021e010b040926030c0315030a0b01080a0c0506040305120d090f060902010e120601052112030f010f08030711040213 66
    0x4010a200109000440d807100075070000c00c0920041d168182801050343c51004014414000c60500d0401040d02030341040d0412200e4108180031440281c1042e50311400510503440d244e0002c0190301c1d8407030180200d101101e0170f4282c0280d9500c0c1104c0c8903100e1015208020000e00000f540000c101100040040c000c000d190306103030b02c0d450301c031200044522041402841655007444122401040441c400c140b03143d680e00015440c2000040000703915000f54038501020a5100101c0c0f40039183c040c02078419200e5a2600c145440001e0380503e0203a1010301040005c20310105a600401e00c880d1030302661b131407001c0101da000300110b42d80145a846a4001e2900f032000e01d074020303801140b00b83c95400305074445000300b18050291000319900c55001d000144440d0818422006000e80b12614510f013106101140c2c0d170410001e1565800007040100070402c00720807030500e0034014a482c80480302c0050600c00c0c11500ca01c5401c0303001d4440549156030386010380f80d5a0441c1c04030300f101c4080c40708494 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 673471294 1250 673470044 673470047
    0x90c0f050d0e0c210f010204050a0522050f07031802100c020607080720031b010e0109080708010f0c18060f0519120c03020c0307140a0b090d081003050337 68
    0x2900301c01041302c140700d100380c416000f03d0b0501c2250282c40001781a211800c3c681810015a51414407595a130440f00304800449843d440c001d41d401410380c85030703003010b038501510010225242103580031010710900c1440d0025071165a80c4820000c0140380040104040e400851828818090024a10600003400b43c090228086054a011045412108210760710408040c1d680c00c09140c007800d82d141d04980c0c03694944c05070340070b044114418140000f0386642c0744400c50070500598020300c220394492036a030914800510501c035a0401c20308101e04210321190200004070383c1c8ac0646814400720007900d00409008509440d900c031046a41e0590150036124000c20403540c11200d9800e160a080c003103026513010b4000c0e600083c48800065082c01c62a40300c102c1001c1c6031490061190160b508444007054050307540ea0302c149085001000009526407006141107001001c04400390310310081400090008011101c82c2071511a940c0da10400d2003000480101d404520407031038111002c3c2006189 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 673472544 1250 673471294 673471339
    0x102040b131401050c250f0f050907030e0604080a0c06050916080d0e04050c070b07020d12140f1509090a06050a150b0d02130609090c0f050d0e0c 64
    0x90b41c01a03851505a2003041c01514180180c0a20028681000100049006240e03880c000f1000440001c440300642d42c1c1d0300f2004c40e000541000803001d880e22400d2089003030400c041c5810020b01c0c5020012404415202c0b51a0140508000d018001c00900981c4482c80342008828042e00190104000c0c1040d2461a0b511030240505040c0070f11a001c000a82c0708000c00ca280c2200c4003034542100c03007000c0174104801048020071141d548102402501c002c101131503103039846141990010001404159805003181040d560004151420680c407200701984441c6010b0304100e50f4079140c4482d0721012100743c02c080e0b1683c41c0e00c1d0002c0010742040328030b0034005011942c0d031340200b00402458441081d034034140c5a10034806101c02001560402095072490020716561146410040c2080d4407000d0091024040350302040000b000ca102c00d05c4101c1c40c80c41520050026030905420502540102a00c140940001c3c08003e81d943d180100540206120001400c0d6004201800106081c107072408074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 673473794 1250 673472544 673472549
    0x90a0b0319020108010512070e010f0e0a06080d200d02061b031608042102010c111603031107080f0609011805120f0d09052b140304050102040b13 64
    0x7807140035466410003080701100c0350050380694488141c1d85c204424485254a00800707085144520000001c803806080e190341e002c3c050141c20610000c0c0341c001803480c0c83c178000d003591400501d0007034108604e041c00100300403075841e0350421b00000104814a0f1004000d50381c119080d5020725540600c005a010505a11a40c005240400c2c10369514481c0d00d0035020444090f40700e00f00c81d0a0692400d405118841e50061160042c21f11044c0f880c582018400000c80481d00540e440d082c1e00140b1507000440020b00038180001170003000c000840b00e0010000c030348405801d101810241909150040c003040024101302c40440700001c0ca000c101a90313540003191042c41552030011075060300c200f1456021001740d0404024400e8271010075a8900c6540b014140c0c0504141c200602c650349020b60150f40da1060044000d031500b4050715001c08585011444084002910403094052098100741500d240820207005652282e03203e04d0960b0080c800d82c0c000c155602d80c04100102c280c0b800714a250203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 673475044 1250 673473794 673473799
    0x515070306060c0b0a020708090a090902030705100e150c0109050c0405011203090905060105090a14150301051309060e16090c02070b0f07030c02150c01051f030305030c0702090a0b 79
    0x740a42d24401201c410a00d0f01004143e0004c403408210320382040e0f000b901d00e80c1d01030359009203005134500c00156242e109030b00c0214244c0c2c82c2c288000940c07906000340402000305492040340b14504110040a4111256400b4415981403014a800980c00001da803149a0684002c00000210b41000d035a644050743c00c8901c124201000802c8084440203a5540c6c1985170715802d0050307050108000113840c1c0140740781c0c1040021720a0b00c200341d4402503030700024025042c50080441c28001800400809148104260703070041004010a88480607110541d600a420008d484420b0f0f2034070001900400c4044880342c030882040054408440c401282254047d030070402c1181e050703940503030b21881c1074410354207041000e00100c03030039424a10050004a102e4541083e0040e110703400121010b80c0c030182104600d00106016800320320900c40c40d6003060200500402e88507090343d0b008804c1203075000c02010418040082662404240140d94416a009100d030f46d0703510f05007034044001c4c840d8445c205d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 673476294 1250 673475044 673475051
    0x100509071d0d0209070f110604030f11060402031207050106090e0607110c21010b1f030b0f0d02010c0312180c290c03090607230f0703170705150703 65
    0x8400c0e14040d442c151801c0c0d400303421028150f40f401c5040c0c411801ca003032060306020701060500e45241c0709114441c8580d200381c44d0468403610b805030003407401564035601c1070a9030061090001503980010604101201c030f9042030340e0b03105240742c2280944407a0b4018035140c2d0400f01c1c0c1004144010030814441c0d4603591390134a00c0700e1400d42c041e545101d0369015035003111804084080c105040006a1941d030507071400480c21014100c00b242605a492074a2100703090640c10000c50342d0740c540520000602c00b140d03003807110507024000030101c0c0c1c030407e0f000b81400500f0786200700b01400b400c03514051004085003002070030b1500e0446403c10202d50011620040c3c001c10200341c80400d41c4030480824001c0002c02c2c2d40c03031000781140c04540c0c001c1d5141c00051100344110311095035403400400031070f031148040c48490b15860030316245440c01410071011540000031030b1140c00800150381400c694004e40046141340907a03554209920540202070900d00440e0010042d8100d0300e007105001e94250759042 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 673477544 1250 673476294 673476347
    0x3060c080906071d041107030305040b0603032a0f07060e190e060f03070503100e100504081204030c21090f0b07021212030129090d0b10050907 63
    0x1601c1d02d0b001c540700e2010850b203010708400d4446082003c140c2d250050400100000c2c8145521003580051204600080e160720400c0104440114a42d401220680096007450114540034800040300400450b482c1110761250001584c2041200580c0f4110400da4000e81d4a443c0f000b03201940c030070640740c040c1000300311108480c83c1410085c0d08480917009000e40585903d0100301c8084030343e000d016454800e224020030940e07002c1c40a0f000d444000c040000d40001010026401c0c2100d080c1a40c1c843c0e0300e070070704003c003041040003215071040c08000d0090041d82c0d1442d0983c4c5c0030120050107800c0426400d0025100d6001c00d0010030000f0003078031410300c1b0596850313171890000030b07a002da9416000305005550040c01c00480c002c00413045041038070000302165003009200c0c1c00076445809400c544004103c0380300407200549020b4040700c0a00c0c0d18100c8181d0102c0d6814010030320040102509100103060462030b4480030024003801084a411030034000401000e0015120309103520741c200c003616 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 673478794 1250 673477544 673477561
    0x40b04150810050a120317090a14010c0212030c070b010312021b010f030906060803180111030703230915031e0f04030f090801090c0e0c070507230a03060c08 69
    0x80324200e803c02052411014100030b84e8512500341400c2c11003d00071241c615000e400c8400200f24455002100205100012410b00e901c0e03600c00321407180b00c540d152a510f00c0300c16a0216060410955104161342c0e25100c1038518020b0744070342003000d00544c80000010003001030212070320100c40143c0e030880c0c0c0c0a012011403101d441c0e407030064160100e02e0b448440b807051800b80d0094a40c01c0e011b070a00090b03160303407000c1036410360b0302c04800018052009020042651380159403a00b0011103c8001d43c140855590050400c0d4140084d030f01460424403041d00c4ea8a05140031100040c0026180c00c41d4036070860032460040e00140c0f0030b9800f03020b20084012860000341d42d060b12403074806008540310b840b1038078299003c12040313903031008003c0c07004004140100240103000810703104007c090320451406100c0c1d11100c034040d080310703c40f03d001c01103c07020900002e40007094035541075a2611401041c1c0c2c0c9100004600302c0001d401020484002043c0a2164450b42060f90a9114440039648682e007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 673480044 1250 673478794 673478821
    0x5030d110a020a0615030618141b040f0b030a0b0103060b060708030c09120f03071506050609120705180a0b010f3f020c0d02010213090b06040b041508 66
    0x1d25001640a400c010000c2091508801410729602c08542d16650b00e80c2c840d007080e11104081003440f0f403100d400c040c0410000595030410000e03524054036080305588078000c0640082c0b131655102d251240e45003400c01d07a1b19031118404040040850b0301e50120fa2501c2160380401f4441514454074040c0c041000f401c10342c04a4030760036807040c1414a59541e44444400030f0300118495074011034003070019050910100107402240c00807000640e181c0d60685488540b400e0b958540c06022800c00008029a490b82c2017900c107485402c03a0710010007045c3c20741d22443c000e2a80d00040d4813005010106900e4a4050442800f4a500c1d0a0038400303a0703140801582d008017605102030004000f150400904075210428a18448001010b4403450940800f0380c00103400c14140350b41c0c055400101442d074a2410000c189224010340001e500f0454100903070040e0740340b10b100344801c15407205000c9100d5641d407003c40700601b0304d0a07042c0c0c0d01c81703459560075a40c411880c0c00d00000f03c2c0400e03011410f03c0000300d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 673481294 1250 673480044 673480057
    0x180f01030213030201080915040f050d1e0305040611030a020c210f161a070215010b19050d021b060a0207050a060b030307060507021f020c0309010806010c0f05030d11 73
    0x1c0706650280c43c650044032011001007140c003141c0649015806507054002d0114015800f64500c88886119402c040c1d041884521140050201c0c400003011704408451800401015074140002c080c2e44905110029000b4600c407285010f4000007000ba2100079540602402d85d0004100c8196032081030010110981e4803081c41d40b0103000703002c40a1100c041800816a40403161304800042d110340c1e5801007000910300704007246081c030390108030071aa810800401014042d402202d06e65150074000c400c41d105441201040042113103400e40b1050013203045034207440f030a107021543d9584034180061503035801455044c81d4000d50780441c0c000b500c00c0c020703116400d0b001400307001c2c540000c2e83c80c40000d103101c003982901400188031030382c082825482120302c185403580150141908008402d4843e242942442e07103003910501110420700c200009a50640c0c0080c00c102c601c5440e0100140c5042050f1a0b0041210420000030810800b011000c0c000e91102d001050000d000310f41c0e01c8a40c10b00481 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 673482544 1250 673481294 673481317
    0xc020f0d050c12090f1513060512070302030f041b0f0306090b0c1c0f090f0b0a0605060a0507061a030a050d021b0d0201030f0b060a09050312070b070c0314180f010302 73
    0x1072160345980e1401d8054021b030840240d003450b01d0006140405a082d07001030384480c1c0407074404030324084001072801207030754040e4a5150451079890140c9845a140f540500302a1071110454a0b2401d00c44484203280003604001180d035072101e81da0b140400180ca0302d200300711015a08140072900051030307081a101c054071032202e4400d204405222540c02000c507a082482d41503190a00c2c08040307602c01c1c0a0304171007402041c50401c02d20784020780342e00f07a5080703500450040d88100600d1001c2a40f00040e0b0f2001a400303000410781c00d034480d607403904064803031961651602941d0f416508106000a20211181040c0c081d203401c0f845208a5040021002c0030b240d03040480f99840c400158401c5d0f00503c405881e032400002c60003c08004075450350413a03010b203000300702d644809010600d4204000d00000f00c1c150b198038074000c42a940c038901c0100242200c81400794102000d010180079028411008410441e42c40d01e0700c0c0e19040380e0380da00f51404010f0b07003c1c046c030006140762548640200c55405445 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 673483794 1250 673482544 673482559
    0xa14060105030f07030f0e0318060901120207020a090c0203040609050a261e030a030501050901034b11010306030302060106051612020d110106060806040c020f0d050c1209 75
    0x784a14183c000100a10034410181c0d688105041d134030700c9114489200f242c00c3c0007580c440d440351081d5901240070000c0103204090074080a00c0342ea90283d503040c81e1900e160030258a030121351010030f1911109810481003241002010450503600001030812241c0583ea0000400c1c0d8a0b02486507000c903078021a170f108803015008880f100d414900f840080580325040b07032401840031178824000240c000e107204031034100180c19407178190315000b8540584022a1b00103c69451b656503055803007240c00c1c030340301a01c10301030150940b0080d5140c0f00034641c420768807003501180c01c02404900014200f104407040d6078034a0a81d80603511038890b070b00c00e80c2d6060300141982e03420b140003901e458200400c4d07212500e000480d014000307170044c89004008030094000305200501716001500c9400440240304490303161050030012182d01c04c0c001d036000715007501c00040c0f180044004034108104142c00c00007610a50324682c042d20750000c010005a1421016a40600202543c200d0701d4400d408005910505 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 673485044 1250 673483794 673483801
    0x1d010e0412050919170c09150d0c0f0f030b0a05040302151902070b01050a06020a0f031404032010022a0301140106051e03012105010617060a1406010503 67
    0x1d000030481c1103030050111300c3e2188021000311000f2001d40002c2503c039062605905981c0d4100700040d50b0b420125030540661500d40f061030020b040d03141d02c1e90310070700f0502d1001040c082d0480c204005001c00740b4200d91007589a4003003084003012440f04884c40005500086c80b41141846858041c0703078194058580281300c0c1c0040d415100c4090502c03103900c502d0f03803078030200001240300a2004900c00c031044d2220b585403c040211109003a8405401d6401004942c00000e901c06080c3d2200790f030505040c98203218100070440c090090f80c1008000b0300590398030b4243c1c108020500b41010100710b5620200e0703c48520200e03103407144855061401020001c07048440c0d0945980200c0d42403015000196020b640d01f071742036844e00282c0c0054081100010704a8480c420031141521800001203240d145500d00904280f40c050074038040a900b001c4a1184400c102080d003040e00148200b10400724403400c1c071044951200030649a0400007450000f964022001800d0214422201611000e00319903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 673486294 1250 673485044 673485047
    0x140a170708130b0601090801090b0405010b1f050d0219030b0f0f1c02150a180b1206040f0e0105070e130507050a0f030b090106200c03100c17011d010e0412 68
    0xc1026001c1c81c18081c1041c1b02081d90300742440351b41c0301c0f0350107010075505030309090030080c0c02c45513001d034140c0c0030740d41b195448060501d0980e00f4440755000c910b4600c0e81d90040045410003401500d504c6030390f85400c0400c400209525400594000404031a440210794542c1d007007000d6a105030402542102c0540c0c5040b03880044204640c2034640007500520f2500310580b500c443c15441100c0e5500891035415030000d10f0001041504050446441d0161401c5650a2800b240c010300070500c911954a44801d8101d590b1145c05c501c10315000c000080c0281d040569007d410f0007562120726008041210540760081e03824050b29010390060380302c00340b400f40c2d0720030100d80d0350481d01401c009058484800364150b071103048803075008052030340c0c0346482110000300f205018031141c042540c45600c201b5816100d640c01203068072501142e84000144d01c07028403016600751071408022452000602c00004100c01c0400740401e0043c030b200c0710301c40e140c5e80b07492030002d107403d0581d8041c00c440c00203d60b1a843d607 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 673487544 1250 673486294 673486313
    0x506072d140f0706051017010209030a02210d05190e150310030b01061d0301091a0702070f081b060c25050d060b010327080a140a17070813 61
    0x20440c04040c680751103481d13290304c000c0d280c0903246074a048540c028204514110000b0300e620410351040254603140c04000000e070703524500080030380700b584492807895a0f481782c450078515004001095425040303294101601c00d402007216070072440e0841d0004400b091060b0361400001f04010301e8805c8210036000034203003a400c028542c1c0040621018003001003842514507500078191076650051545410406003000d03c21940c0c101c2c02a8182039039100014440c0280c020007800b60504509035a0f00d00c07004a240603d10f41c00b000402180503400b2a1019001c203081884802e0703c10811804170029043c80014400c240d206982508942c0003440300c250180c4031072084550009850300d403e6210000180100101002164540d07501d6449010035600b6028412078440100081189408441203a4541c000d545000070458080000c092103e940652003142d41003900d600c10503203911040c04080e0110005000c2945040c1c01c0c0000246502d10600c1854404e0035080008003070340c02283c0d19142c10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 673488794 1250 673487544 673487557
    0x161110020903031606022508180103020d0c180b07051510051c03080609060a06111e0706020105091f180503160c080d0806090709030506072d14 63
    0x5001c1041120244138080c254191200d01a004c010b966500020381480c0494031450004035402908100d100030030b0404041d1071025900307824007030a80c240680120028800d11800300003045c5030800c0c0903526035000300035a062020000004841c281c9a460800460252071001009a8403244180c0d80003000410410b80041003202410704041e1904002503880c5010080460103481000c4840d05050740021415006002170303c1001e040d00340f00c000b146101c521030040300c040c40002190641130b20000c20403aa0890b0401c544c0e1498038020515007a15000144528801503003024003241855901141e6010103002d0b080c8681c0560f00c051b1081d030080d103140984044940c8400e8404404201c0900040104007902d038001d50340000c0034a01100b46102c26040145642e00c450b600186090300701c402c4540001007240c0d4903800740e5500c20215818401500003c1260080b0410f10102c683c02101d0324030210000f00d41044840c6115800581200741030501e0b00014201e4200206603007500c0c00201034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 673490044 1250 673488794 673488799
    0x10809120313080403020a09020d0c0f0806010c03110a06020301080d020303061c051e010c120e0a06051320040e15010504050a0e060103150b0102070f0b090604090e01051611100209 79
    0xa0a503a46c000400c1c0c038401d0b0740202d82031600000d1039015074100e840707444001d051500300040740c51103690000b462904000c000e44d0500404034031100515025140e0141c03407924200031a6607281c9540b8040d0302a40080c89159114030503405e18050070381c004001d40303100d190050480407594070399020581c01f1000f03c1c40c09940a01130200c0410011841c0e0701d006407074070b4005001140303002002400902100713028850540640c60907030041c4401401141980b5400d0704014045070a44500350b04000c1080c0c90740c40205101440345488840c01890004c20320b08000841d000c105d1145c0d5000c5503500d964044000402464000c0014065444c25501680e08144080c8000840c00c81c0d180c00d40781f4141081c2c000f51450380114140088080d4180100508504284064003030a858281c0e0b081500403103000d04d80c012800807400f08820741315001520020000e600e428420240741011050092005554891030202190a50511580036a01d4044c1c103000082c000d00e1022112441e12000b904090a000e9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 673491294 1250 673490044 673490047
    0xd030509030f07141207050d03030e15070306150203121504092a0513020d0b13052a12040f080c0d0206090a120e0301062301080912031308 61
    0x8100d510100041c0004025840040c00d00c103040c0900c1304003d011081c899480350303070071100ca00c2036800042500c3c1c0480b0425107003a07031214424a41030700980f005400001480c460180b0350f6100f05001c0c2c1e5928090003071500c0070014551101001360783c000380c501050b005680104103c04204d00080c0300c07264000301658404041030802c3e0002070556680300d4081d21303010082007250301c07420038540000b00755403612140301709064502000325896108203d118008a640880d001900104680045550010051000d1071444105500728010002030321000a82003021051044010b6100340703c000301415882101d05054122113800c2d2070300d1f0010003c882e940c102c4c0040100007180356018000f55010800a407056103200c0c1c200a00e05580205111a1a400901e40074040b07101641140304290040c0342504410ba250404070b4003401d1507038001142c0c0c60600480c03000c001c8094001c1c40c500e035426611142c80d511500411940d51608000d140c2d07041360f041010511003c5c1705007410242c240b08041e020f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 673492544 1250 673491294 673491307
    0x1180b10090e01062d1a0f040e0406180818040e1c021c0503060918060901061712030109090203070b0703090f050d1502130b040b091c110d0305 63
    0x40c0240c0d0607800010b50300f0ba4560382d05001e440c2c84074200506500c0c141c202680c2000003410b00c1d00d0030003103074412000c0c0c01c51000b024001d050b8503101100c98901c4031401c090364a030341e03030000c4003c60141242e083d10a1840d103400d9170783c1c3c028800390540d4141d400c480405c1c1080340854040c441011481041d43e03100303540d001d8081054006010202402c03868075000f00340342100d0311010b0b080074801c10b40c5a06508141c07100100e90b41e00402175075000502a60900810340e14040c8180d4500394520f0308800303901c50724040082c0d440054000e402900c9106a20000744640b142085554100080035942580001d000610240c3c41a030700c03125500d0300080407903101c00e42e140a840d5490b030081c042600010081c4009000403603d00401000030b1500391102d03064110039486c1c41200014140f0840160750300050410021500e90341e40700040c1051380c4000795a150342c1c4030501ca103540004c5005029880c50814410a180b02008032030220790030240c071070410b180c00f10820501c20041d400840c02e008051000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 673493794 1250 673492544 673492559
    0x30e010e0a0b0103020109080303070f120209041503030306090e0703200607030c020f0105040305060a15080d02010f0b2b0218191a033f031801180b10 66
    0x1c160509016010044843d41580001050708a03641c002020300d80c402c0050241865021030381b542541340502e00000380c186415440c4010f48207a22006078001d00b0310100f800012209003118048900ca910304128940e56000f0840c20785802100e441016003000e0b00403c081012143c1005915956046c898000c4541d000000d80f66001140203500003500078420204500b0f083c4192100c0f4002401c207641001c0c0b4650382d00d035940c1c0c0002c2c000380040740c41d8030701c10020b40030410310356001d88642415102c043e0009a0024000c00c180700c10020194202580b100c0d0500b80303500030115014051940340003901e8403d8030000c1002442504076000400c0780084800129680c03d098011404d4421040c03e41410004160a403088403002d80a00c85680754800d4550360002150b204517010101004498094194003864000c011141c80d4413a4225a4202d0400c1e40408001c600c2413080c0d448074000c08100484840c03c031070340d0031900c0b2601440700c62804081804070552941c4210752109460382252102030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 673495044 1250 673493794 673493803
    0x6043c091b031e0b0106030b0f040c050c0715020303010b2b06080d020c06181206070203091f0c11130603060501150e03031b0f010c08060a080d0f030e010e 68
    0x18000d8086081e0340306004100e00c0c0981d00790240314003254040e001255840d4900c204106100350410b042d40d444001c84141c440c02e500b0908054014010002c1e036070450b0000c0c205510040c08448640503500d00422002c404011000d0200c010368021421030b0b007804505085907100042288010030004064a500215440e001c42c1c442c40e401404201189404506031a00c09207801c2c81040d90051103604c507041d103501d000e44018010400e107140c15940c202010a800441d0842c00590360700848081000c1a0f0300000141050313035051340c0031078020381c0c4d141b9032036003c041c1c2c0079191000405102d0008041034592405900300d030402000703c1c1e03281803043c480d0303811a07049a0085030301c0c503102c0e4010800c002540350b4040311490b42d81007034910903102c84006526403040080c121800c680a0b416103d011104018890546003500001c02803030b1552140513050002c03c4034501d102d618809008101c01401080740130030034030607407111410450128004c1d80640010101ca090965840e544496071080410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 673496294 1250 673495044 673495073
    0x170a1a0c070c2603031306020a090515030412050301060e012303090f0705030c0d0b040f0f0804050f060a0509090601020f1212060303070519060f0903050306043c09 72
    0x40c140d212145a4039036240c10f000388619648031540041c003c1140c825000c00c109082964011070050752100311140a4a200100f40c0085401986900d500340c40d6070300c080700450203a40500c6096400340c0048604480901c8240a054000340000c1409403441d4045c0d002c400b00d08a48040781c0d108402081400040e07908201d611100940c040070140c6401c000a00c200c0016010940140075803002103004600f4403024050003d0450f481e020000b01480034080400c00c5403a40040707955000741c400c4c1081c1e5015001802407070b00c61400e9003000d04051a2010841c5c80c010030503140d2504100000701000403160000313020300d0540c040c2a0103000c01c403400344400b401c03078a1202041e50300c030f103c1c20b070603054003035002458580668420040000845c5000070300c40341e1645005c0c180f4400001c0761410602405a000c8076000603420500181e0825800401844c031030719080e1010001e51040c041e0400d19030b000d15232440d40c9504801d0340490505507035051107844000794240031491104960702e00d0130468040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 673497544 1250 673496294 673496309
    0x5091504081306032c030c0102040308070308010902160206070606031e0b0609040218130203010c110c0406030b180c0a0305010b09090105010b0f03090a1209170a1a0c070c 75
    0x54500e081c1c07589502102e0180809190401075401d110b144c16180b96a0b80c1207108060f04c25032542140031608108492a400a62009546071039580c546050650852001103012071412000400c070a1494820b8611801052855400303244043d000c1c0a0242e101c124140c07109a141c607004404181003036002200040041500d0946103a117090650702da40028050520664900c4180000f503528080e260f50055140e022034880c035150350440f450b070103000c1100250154280b003c80d00c1c0f07042c0c20951111400a0241c1580c80841070b03035042008030b070450b0000074403201400002ca40302c04d0b5086c1c0c401c3c111910550031125121544000140c15100a500484903a91200d40246060900000301d0b5002616140240115414000d4a0925000d03040f02c038501c1100100019215020401034400301c1600110844884c8040d941c00400040c3d043c040e8102d40b1000c0a004c0a1005002459003002c5402540d10180003611303500341c03c0290b001821054414030300780243c2c0302090707050103244001c202c030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 673498794 1250 673497544 673497547
    0xc0c0a0b0403092108030402040e070f0603020403031d0d08030606070602040b0304020418030c0f081b011506020f060609041a131b031a0604020f0408060103150615030509150408 78
    0x5000301c420405084c07500001c03002c080c0a00c0070b000103000c5010359411130b604550200d46411540c100341e2030b1280030f9001e80310346412220300203001a00340d401002603a002ea681c00c1928003c8001c1d00425081040e0820b0f00403035218034290110f00b00c0b01c061604000c0040030149440610740b2506c0913030700240c2180b080301d20004248000c500d001d00c280c4804c5507003e442000030071034645020741032515002010704100c00c191040d404000180046a079141c00c8000d11320054060b00380114028254095074030000780f410070000c01c08500008558a141419200400c0d507651801c0500500c14030180084074800d0540030914144108481602c0c4141ca074040d0804003a415810007289a05440010f4020036481100900c04a074401b440c16602400c0005844281e44611001c14002e204880703030750fa0081004180800da0780c1c0d000c5100c5040701c0c0542e106410094240c81d580d004c4441038482c203681d13020308803400c1290394080d40005610010310303030a039603041c2c09242d005440c0400450b4103c034403550 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 673500044 1250 673498794 673498799
    0x100507020c10180524090406030b131703100303050d11070f0303062108070f050f0d02070506040b04180204050303071a0a06180b0609041406010f0e0303030c0c0a0b040309 75
    0x10407088200034a000c0301c02c185c0f06621664610f64144800f000c40b03042004c00141d80044c2d482e240c000704021580418690410320b0090801542032810420403503580c0444900c0140031040722050700d0150160085107400280303140c0e4103580c5507005040f0350b0b07c2c1e40d0b02d400003589821b07042005412040d016104441c105400d500e4000d00700c0e000348d00602070781400c0050b1f0010f080c624030180303200e180d0311003800d43e540d00660078410680d201a00d0010203900c80c21229008000d008142c00c0201000d603022100c8440d280d00c1040710307a0080d0701503101a94011b02c010000c444000e5800700743c412401000600c0c1036162400719045602080017030308d4582c000c07401c903600f035500c20040552060a051080000300e003480344028014089158003480360f51a200a55115610982111040c1200034000c20002c500c0344c9810340350203012076041c3c2c0483d40f540e603082c1180c3d0251031640603044004019500e15079501c0702400c03c6800030854001284500100600020856010140100d00a0311903161461 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 673501294 1250 673500044 673500077
    0x7020105160203071a130209190e0307120e011205090c01090914042009010e010801051602071517092d030f030a02070c140102061503100507020c10 65
    0x1000414400440d4000c0020101103a0400c107002c0c0c1d1200ca500c0750a000f9142e45800d51b400c02e4640c04082d42c07001c0b8500520100020400103800b118407401000d00160000b809015202c0c010140d0240a940207000d14160152042120300d0300c0160504040000844041c00310302200d8013103030007100681c80124440415a00018000000e060b54101030058000030b501c20095104068401440c0c04102e62074078003408294482010300010140c40350307000e503075039a00d1606c0c044000e202e43e0510794030b4000030443c4d08a4103141518449110340003030049515101030301e503e05080b0417135001009455032801d040595400f1000d80529840d4000b4108003502c00c2091602115000541041c2250107100c00f90100001c0180c45c2000c3d03902007003580380d0341c07070482c110040d114207040241204440c0c88046410180003021441c200c50030380c21030300746946881406001001034440680d041c3c0c0702840b020208141070300555403145407441610200521100440d1414040c0c4070701c9804124a543c02c01c81c10b0307 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 673502544 1250 673501294 673501321
    0x60f010215100302010305420402070803010509070c0c031403070804080a12020d0e090a140103150506090402060d0203072705190e010605070c080703060e0105060f010e0d1a07020105 80
    0x26880d01c046034000d40c4200700803c1074a030709002c0308c661b020000940c40c01c0031003c414061031005001550380e00030a290440a80e4000d004040c483c1c1503200106100c0d51007840f225480c19030005486031800e040d03442e0b03040441d4a022404080d0301c0708100300030018600700042c00080403424011b0843c424107241122030b006460194000715400070744d081408640c026040250420251001f00042e180c000b5900040c154441d8015110700080b0700020400400c0c2442485c9241240c00030030068941404000180d081910081e520240a2000c5515070403554001d50300040b980c01c00015144040818507040400d600c0f070444103c0181078100000e05210100d0800e400740700444004e16414001441e000d04410b0055004001000ca1a0801c0248651401018060001c11500b41c0e9659240000280c20032000031030041d401e21011568a041a4002c3c00c07035030344161100040182c10b0f606100e00d2480c0f124054404c0c0c1d401440d040e0a081103844c006004007581e50010a00b0f292045101040c1d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 673503794 1250 673502544 673502551
    0xc030c03021e1f140a090e0a020a080a0209130c0807030c230903120c030405040c050a081b071a070221030115050d0f0605040e03070b060f010215100302010305 70
    0x41c40380d148109442d5540c111a03550700c003820f02c0250648aa001400c0300c00c2d15010100d8203800c00005008501e09802c05454422101116003001041d0b852881001c1a4055807000401144005003c120610003540281c111a10098203400541c002500e0801c01d0346d05528091022622400034040c0c1c80e90b140c003812562100a08000051001440490804006039081c0407400c982c003240da80301c29038045c0018034141010b060381c0354440c03108821090710380e841440351520852a03c9440d09441c0e0266090f194a460107031540903542c0c1e50090020600307443c0a0955506c503008104400000d104002a59041404415409014500140060320301401c0000c080904400d45c0c2024542d0180c03281201d0544580c2c904110300c50340207071002d079080e0144541c0d0902241c200400c2e140d41580d564000412a01e04560a004083c07510403560348910900320084d05240e00d80e0b0014140c0d05000700041c545083c18411a003187c19408400c5410741d409a458107008061580100155030349409010382 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 673505044 1250 673503794 673503829
    0x140706030b030303010510050f030f06030c1210050703061509090b04060e070c03030f0e0c130e03041703040b04060818010501052209021c03080c030402030307031202070c030c0302 79
    0xa590710400041d54034001440786030301c2111800c41061400d8403802c10f4800303c01151a5294890400c502c0c0c44d2074003442141c210b8000d1082c0100c0da202468914800308a070704070000601006150510b118025110080c0600285034481f84002148050403010b00516182641c0c0d00c00c1c51414040c0f20f4003540d60b40f02d50b080c42a41005400d000e4400c403203d505e070300418141082e001c80001442d05401410719001c803c01411301c0d03c4040c001e079050228003c025004200c82c90b981c81d81d6002c0790314081300d81074400d40c800e9070b1040c003040c13103038441c103000041c0740d01024401c0b01c1c14983e0315880700d5a10ba1140d080180040d0a00042c04002448503030201405510400280103e40c1000301007401742e0496240e1941c6403c900400309000c0364150f01081c40250040d000e50101c2510948400c14124074030811800124000001207106916400b40c9014541c01809907152081c161003c45009190310b8003090026400c08ca4000000d0842c41100000d500c5044a040700f1403450040000310200c1400c80c01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 673506294 1250 673505044 673505051
    0xf04140d0219260601050613051801090c090e0112060237090501080415020d06140a080601120b0903120103060902041b0905100309140102030f07020f0a030f11030714070603 76
    0x503c003001260b403a05442c820354803e5103994052420480591090f40a0b45d00311007441543c02c0d425030f90b900628180c1c0e50841d0140141021071104079000f4640340300708000340f504140140042200c03d411a100b0300c0c06200090305080300c03501c40e030207002910b21030301c04200440d0000000300005481c020342d240a46007000d28015103040700190015500070401001c165070040d04101887c07081d0305856100b000c4040c1000b03503503100e0701ea6010140040c6800d5106420094001034250000146241a14a03000b4180c101c00712903a07644040a101070000100303030200b1312180d12002d070b8400100b07009500401010804010b0340c0103100803a006640d5404a84000c0006405925000450f903030032100240c5481d0050a107158089000b0240b40d44020142c41c58070000c010044d105401441c0200c00070b01d114461900e4034001640e8134403030001100d40c290400c10060340842d01036030401004461901381101603151401d500c0e07055900020040303419400940e0000b4081e042004404090541403c081 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 673507544 1250 673506294 673506359
    0x10e01140f03060105070b04112b0803250206070f08060108070c030201111c0c0503010815090c09010909060e03040609182a140f04140d0219 62
    0x300c00a1080c900e40c103107080c1002000c145a41d10490807104a01e8111030305e4001070510340b8182d03200300030810545208510107400e2030030705e00c0f00c2c5542d138000380712084010012139400d98422406810080000340c1941885400e641d007034140d0b208040524102e82d018011a01c3d124501130905104d0343c0440080180000811806907008541c07203030401f0060070070500800841c81c04a003d802e400b03440919058001c240780a807c842e41007041044049058248450008038800301c1c0c060000b40724150490b404045c41f001d032841004001500f04c036403201600d0380d0070009404038003a100203905c06512580d407001980c060080382e00c034480044031a04080c516040c03400c180100704818030f0080c901c0144050040812083d450350040041200904101c80c54013100c5000501038151403d115011440c0b25508003000c5000200703e488030ac0c1000703040c41c01c150030300c400d50781031603020700b502a00b12008410410242c1c2e5801404018080724210410400781811070542950184101287e071002000401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 673508794 1250 673507544 673507577
    0x203030a0f0b01080606030615270337080f1c050606090103020a0215040c03170306130b0111012c06090d031503120302030709050609090f060411130302010e01 70
    0x4c081c1c000c0421076800c4d480740c81c0c45000407401c2ca02d882e015a90a040016140b80151076001081c2c0703500c003c403d6205241c100c541c24161075081d07100b103580500c032815030344a808480540901c003901c0304200911003040f5059071268500c1e40b00f801c130203a40e6000403c6081e403025100c100e0012803003e40a0501a03410b00001041041c0100c0f55242d050680118161410501c02c000358140e800c0120217540385030a02e402c11540c01c0070b00c2d0109807802c0c00b440c0030b1101c41000c4001180d0099001402040c07000c09004140d00c01001c05451035810098080c0d5007109040003401114182d1456007202c03440396205c0d00c0380400c0c0c0b800088501c41c842d000036041140500d00171601d410f017048030341800b0500007040c0c1c0309085d4084980e04001d115041c14507000b03200d181c1c940d0203148958015290440120b403203504010060240040c02030340701e0f0700d650016100803506000c0075000350000d03001048582c2905082155030300030000c02d50650301c040b4000c005541c4e04c80d00308901a102800c0058080b504100e1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 673510044 1250 673508794 673508807
    0x501061a090f0402031302031e0f060708070c0807062a0c02010e04090c270b0a030f141908070b0a0b030303070f140c160b040f05040f060b0a0203030a0f0b01 69
    0x2c1500c2a82e01000141d60007160b0304900710041d900400b618016143d041041c0842828007040c41d1051003404107a02c00104005017460140c4502d0301d40710401d5985400031101e80a442e00216045034040c0100310001c3e40718002d4030b002c5000258007080443ca5400d00d80c20000b03c3c4c040900805c00c0d2004400301507608941c20155490007038034046500056810095408a110b5000b45008446000c0c1442c03000d4090000c9550445031585c24802800c1c514100000741c6000d00000e4000341554442c01e0005180c110b4034902c0d2050481070758543c034240911500810601001a540b55200103010300c2040040036110703600942400042207c1c103074000c0800d940b804014003140620080d1000d87c2501401140000d44540744100d9159036141c105101503220090414404002caa10301404142c1104c408107480503120300c1401d00800c903252904000c05882d10000c074482c61703680c0f0303000807880c182d4844c010b11b05039505d41c00075036403420184420300231100c20040507205285400e190f02444c3c1c0e400795 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 673511294 1250 673510044 673510069
    0x28171c091202040e0f0d02060906070206040210050307090806010f0504050901061d04080720240d0c141204021c0c0302060307030219030615080114040e190501061a09 73
    0x290000360315007800d13010610384103110242180030f2040c0111780840b41c1d80004c0d0b243c8900703c44021f9500d01c0d01c1701602681e6039842514002e40c84852040c201501904c5203000e164880c41510b01048007030740d10400281022030030380100784000704042d0188014105406910740115211000b08600380c5444000901b54450303909003200b1041540108040c81f02080640391410781051403140f1402280130311b03a000d105401225801481050209000100c850b048aa2030580d480302c01c9180c011340d442614001c0100034801c07018071183d5004600f4545c1c3c60005000d580c8412043c101440c1814010444031200031000002e900c52030b10140c000041c00069182c04403581502d4aa840392140711041e0068044d002c2c121403120721499045169070741c541c01020884007405007a40d030203180b00c181221041024082c84038008000c600360041e90806074803c000b1120000c0c180c0f5912a0400c000c0405c0d903814881c02d0315240c0d1100c0062220000c0a201d108080810070920740c0303031907440c0000c6449218280c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 673512544 1250 673511294 673511299
    0x106170d1107080d0503011d06030c09180604050a031103040f0306020f070813060e0105120609130206070804060e040b090a051005031218010c0228171c091202 70
    0x82055200c507550400c08030014060703000c2030b1624500d03407a900610b50b420905c107134803108a40c0401d220b00c41c400c1010450180e240a005041080c07901c0e0203001032164040c12941c100302c84030380c1340700d460700b014007015004608c51005040c2d146030780d080c0148000104c06403610550000c00c000c000300072520b00000c046a030312200c0907884583d89a284003884c01121000b4091200c0041c515400c8052425440c0654080703894401c51003509200443d628041c80200c4254600300b080071034914940140b00d1648403030040c6040407015402d40c00b003195900504403c484904012505111b181d801c0034280c08aa8016982000000b1b0307044009110340c88040d143c5a00c480d070390f0010070201c3c0604202c1c00e02601c00641290002c0c1d03141404803c40e40d02080e680c95481c4605040b0141030b40c45030754103005007500200280f18606250440d14071407000a0410441c0031181d403000121207220001c0e0341e01c000c41800c094003000d09024504454424603002200030130039000e0b018007404684078504181103805 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 673513794 1250 673512544 673512557
    0x40209060324190c0507031107060c0b0603030f2205010807050316021c0f03110903031b0a0f0f03020c0301060308030703020906130f0609080a03050901120b1504080106170d 76
    0x1840c030503a00481100c1c03e101c104038204069041010b810200901d046071081d9a1022180a00c2041c65200c0595000c1c80000a8041c02c958001c544040c802513084134005094034501501560761740c40507031113006600000b0b26080ca00c198080101182e4500415003820426554680508028548e101c02042603649011404402c40168801c0103441205400f120680c82195281c80003c0c14044180984600080c2048104460704038a031007681c411355805002141003181d07072104801d84040416003400144960754083e400306108031099030b2400d000391202c010079566810300034104035030380d200d082c0030340e04110741000029410021030340c0c0154240b40050b00c80b00318a0000d0a80d10031600700041c0b1605080000c15406114a043c10480f41251107003442c40e95210142502c51070002c8010303020883c00d0010740081c1d4055802d0099400150708000b514480341c400143c10b1030718204061f02c0b10303040420240706054003442060050003209207040011040c60180959036205c0301011010401c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 673515044 1250 673513794 673513801
    0x301031106180a0603050a0b010e030a140312040b0f010e090606010f050c060c040e1b0a050706230601080a0207020a0315110f0c010f06051003092102010203040209060324 75
    0x158440070030041d2001080000f1560340c6010040140100342d400264561511407010219070150303002c81c8031220080c0203820b01361a191682074a500c2007803007051244c0000c0001102d41c0d180300a58a206600c01d51100b501030030110202d0011620581010507403e0290040c082140d6001515540c051400d107040d0541c0d990354003049402c1e0103036100c40c1e0703158407405092200580c1002c02900c159103980c40c104120303554900d000c0d210b604680b440000411804c0001c400d81d684140005e00c50b99010b1319012500344024412214850101c030942181d02540d0000c1c003040d03690003081290800b40c4e1040560901646070006102844640300080811039451403203411858150400e00d019062500416115040a5a0340100758092003502840b9440c10f6403903181d12065104080698074047c0000f089100d21080aa0090880d00415a411088400340001c40c001d01d18400003070b03044c50b600158903401d261051040c001e0002d40410300c0fa0300711a03030a80d0503c01e207420511741888110342c040b42c540c6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 673516294 1250 673515044 673515067
    0xb04020412030306031a0c030a02030606040b1b1e0309010503090a0203070e040314120606160b090c041404120c060f06030c060f0e01140a02102f0301031106 69
    0x4540c0d809048144904a104030515403d60310800880e8041c5480014000c1c0380440450000e1044401c6001c40009101240c1e0700050343e4095544501c01070000340c94580c44e50540c22858200440c04800e80001e4908216200f074140300000120080c01060309c540400728102d1a202d0055900b128100800807002a841001c00c02941c41400e4018003a10f43c180d0f1200c5003162141c01c200e40940100d110124403080309210340007111200045400b516407952104020001c241c0e10804907050300104042d0300b100418854035443d40100441e02c01410800c0d001410303c0203a600701900c3c0401420392404101c0810351403180d595820b1b54914051801c5002031a02c40024000d40b1070640a003440c00310040100500845002c00344d4240d922200f0701404405401c43d5065a041911400910f80c0180190001c580d080075144c3c44881e0b00589512807012030400040f00c0741c075030b0f040c1c03144880240c01842070b00f5650540d120030040c071301c20b451466042d511540c0760014117256050040a000500f218000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 673517544 1250 673516294 673516297
    0x1809080414040b0a1203090b09130908090414011703210c1603030b1302030907172401090e2404020d0209040b040b0a0e1c140c0f0615010e040b0402 65
    0x12200034034422015445484a15502c4c0d00100d0440107e20f4014000c64504944030540c1c810040041128004c54203200b041001b8222944084070800010b00011040b0750301c60083e07200f582c08180f0b65216961406403490f00042c070a00500a01d6002084080740c00d00c030a600000c03111b11400804002e0780c54118080950b4460b3f0089006a0004022100c0030558141c1000028060448060400c01c0d07106e2030710300880c4030603103901050f039002000400050f1000c00b50140141001416075400001d241d03900d2801120085010180800002c01404076800f144504600785400d240141406091581541d040c00803510b80340c501001054009411551403620701e99906070302529112490400d0720f0039203a0b0302800e50301190102608400610038603503a22610154a43c41e030001d12504408146d2008480c0c83d00c8101c1d0100010360495080c1d4400400051860310b12010040c4080004600c5407814402d01824400000d6260311031f00ca0503aa0090b903075401190101c07000a6000c02d2803002400a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 673518794 1250 673517544 673517561
    0x12050c03040b04030303140c18040f0609200f031f050d0501020703030f0b030a0318030501182108070e0f0a140f27071413180908041404 60
    0x1034400020042220b00c5080003030404c80b403183c0c8041c0900c4846064843c1031510850316080c4240f0180305242041e8058500c8464115002d840060f008604075202e20680d0074540004c84072039200c40f401d450051443d4185003000344c0902e0751905121a0705a200498030014014500410800101c0296645e410a40c80d008001c010040e4481c03003083d03d85203021303400071201500420325080520500d414203015546461000801401c40521983d80030b50351a900d0100040858254501c0400015000d10031564520441e0084291244203840d18880a00400d04100010901c55581d5800c280e04059099040089400c1c640d007280a1400451080300d004802a94054003541000031401120552040700c40b005803000381041fa9400f080c045254002c62000038091480902c1d0030039003400f014005d4000c0e400f49060301044001c007d5030000d070303041101c1c0000407100030030007080a001c8800103140e20541d610018400c0740c0c0c2070707100c60030740b40a50b01c43c2020355607842e540d07001c4694603a07100c01e09 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 673520044 1250 673518794 673518817
    0x215071803061d0c01020c190b0a08010510111903031b080a060e010f030308090a06140708010e040b0a27060f0c0206010e24090f06040c0c0f1205 64
    0xc56900c2c1042d10180c0700703a844641d6040220f40c42c034002d1030b4001c1941075100e03d06030014100d244902003404038071280b0f5003da9840762114600445c0402d0320000801400e0182e82d1440c0c41c0b9410001001000c8100800c00010701c440009a4503c440d03010501c0c10700c8989061701d41481300c00701d040560240c6a80c0d500e070a81212580c42c288803164006104034080d18070403001b0880c958640c5542c010400080c000d0f400b040d51782d45400c1001074828000c056000801074203440b42d102d010396880040d1020303100f003030150b081c0c240d080013155a406200280181081c2c0d509481c2400c00b900c400c46440c001911050405454540c425400c0e5007490003022100568440c07015118072a040841c018808400e00000d032070f0034206d80022039440095464140c030000100341400380c5402c48600c00b104108136003032000c1d1110f40040115640c452140394864130f1010151155843c1c12000c2004035680301c2d12220500140004001c007080c0703540c0b41038071002e42c400c1b12004501a01a01941d1a00a8050f00c0300c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 673521294 1250 673520044 673520087
    0xf0c1903060c171609270213050a0605040618030b06010c0302010e15040b01090605011d010201060302150306090109020412080c0c090405280807020f0a0e0a0b1c0201021507 76
    0x1008001c26600110241603d681d450041620345a840d4102c0550180b200c20701c21b15240194070b4012203074000c00c6118800e1580017246c554540c045007950b44036500030000302c1c4010408003e51078220300302039401c00145000e12100b0381141c0c0c0e200240704000c0e102c0303410001190300305000c150007503211052000c0d443c021035107240f44040d40c46591110450702120003a400c10300019007030b8018054003050740d90584903c1c040041101620211102810070b0b00d045640381c1c200000580c0760000510015400040c402d0b981c0d01d00b80b414004400c0c0182c1c001c1821600c1000108180d100501207407800591020740710f0b80c0c079400060301d40d2400c1142100c10364004001400d110800c100000c0032072003800703c250f082c28030320040b182000400d00007039000b81c4100c904004080051070240105550303294014090440b458441240c10381084040f140d2080d0103035152600a450301d403405803071103c1d400c0750010603120103113640003d441c1c407803407200d4a00f0107020700d002c2451240035402003901511000c1c14203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 673522544 1250 673521294 673521301
    0xb1804051602102708120a06091b02060606070c0b192717010f2c12070807020a03080a031401170615060c0307050f0c1903060c17 57
    0x40303458091251000c400340c45800340c00b080e0030780c490056152681d698860740c0e99040c1203444003d81c80345844c1084485540401405c1c100c3c1c2960083d071805280d400c0340002e90b45081410400071a07500302005150b070110340e01e0624885034001021a44039000303541c030648a00d1a0315240300300d0280c94012802905000c07c0214070100b00c0104910581c0f050342e07462080c0300c80001e040e8440200c1520f4020304840d0104203104104440000c4542514076000000d2100d150b60340d002c048580380030034100d00300806d015651102403000030a880800302c0308058a880040841d185025205024000f0082c1070702007148400c0d940d9121850300110b4201c824103a0794480ca0f40020002c00642002000b5030400400100301903200c05815840404144002c0241e03032100944040c140e590b100143d513110b402017100b9901e0800900203801d4003442103004200400c130f0b612409080c10420030020317000c0c9040800010f41741681b0140801180d41000c40042c28030748a42d003c80340c580135a25081620721040091 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 673523794 1250 673522544 673522561
    0x121002070506062103071e1a0601090f060c060c020304080312010e070e062a0d09090c0f0c0803070c0b040f02030106060813061a101d06090a0b180405 66
    0x2000d2041400300c4200c408511311004003012031110b00c1030380c25a51705c1444900001868505c0706018603400d441440d09866440d030b5001c48140c8407107035070841c40c8641f50a22545581010a13000506204800700d45941c2c1400300060803042c4542018011503165090046003a00a00484000e00040420740350b45500b0744100c003541107001e10646080c07080410002d10420301c24003100d0ac070310038000c10300351a06245400039920701003000c440c109100d450081c0050407503c1085488500c1c80c1507218511128940807611007251071a800480c20f000c0c80001175606503500221b0016665401502e0b540c4035100c10700c0c02caa02e0300c60340000500c1c0d500d4140620007480089038206000600c02c40c020b026043d149c0104480104e000e0300e4406400a08000501c0080c0d155041303030248512050b04041402100320000b5002242d1a030141d0100703124024116640d05c4803014803080071070680b00d50b0316004000c00801c80c60030f410312900c4072821003c5030048058508022a6491900040003800f079424001c06 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 673525044 1250 673523794 673523803
    0x1d1008070f060e1516020f040218010905031212040503130609051c0c1206020f12011a040f0e070507060f0b18010b030610050d0c20060f061210020705 66
    0x2d00300114000b00b49004041c9413000c401c5440d0559519254181800945000b00c0007016840407603100320b81e2075000c0c22584503031001e005c4210121191000103901c0304005040c0a103203030031060007900469812905500d15400b141d0450030760091140a694860400b6030a6004140001c201012031240001e4420361114680f410385004440d10721000960310250704400ca21001c0c01080d03081000c5007089500b5103a004050b80c10f0086902510f0329581001c0c40b01a640410040070f80c604030600103001a20340d19021342c0000c004010f48514007410009240c0c3c4140803407151001a1070500e0014910510900a07a0503241d4420002d00c9005641c5c1e0070031016117400c64070300780552040440150300088017800c08c1d04035480320100500e103844000c140311001c3d600c3c240340c3c01404020070490321881c01a11516141c401c0d41d42d00e4841c0348243c801c80f544910102c054a0310641e10510134061049204400b00d0741024080b601035280310885500241131483c400e8071240980e201181100900c1030105 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 673526294 1250 673525044 673525049
    0xe0a02010f0302090901211b08010608070308031302010e0904050616020703081801090b030108010203041a0919110301021804050105041b030f18050114090303011d1008070f 76
    0x80350441d2080c1d00440403003ca0240b01c2400d0b030b01030340d00c9004000403e40810400e04002d06d41103054810f0400343c4514000c5000e010402d102d440c42c1c0d21003007003030b10020301c11040540880c00180440e0ba01c0d41e141d12103030340000b8000149170080001c07a0411680500f802ca0321901c0d000d4030910380b0b41b030300d03007055038684c4022220103409120100c02c030909180f0100f03002c2d007036a07880a803860a09074070702c4180031710210482005040c0010b1880c041000c04424020714002d00c46800090313540d1a0a01c1c0c07844000351035007482c0c408001d001051004e402c0380841c4030040741c400307201c0316a0202d0250a0070011001d109000741c2d0154030001d1695641441e203200029280820744051156903618024042103503654504145ca0111060034112001d00c00c3e00700c001040e201c000c0c007080c2e04860080086240022500803100c5e03039500c15000e02400c0b004100140d000076010061400c5615220a40b950750003840c410a92088511001948410002c4040c001426804007100d207116110400787d0050002030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 673527544 1250 673526294 673526297
    0x8090102100509070b0c030d0222050604050a0312020109170c070f0302011403090f161409010b04150c0605040b01210809010e13050c09010912020f220e0a0201 70
    0x4004001c4503005014080c003d07241007004007419860400c1440e00f9030445170280c00b43c0e0000300800ca0001e80e5900261807824021120305000c00406004145e42e07004541c403042c09041c044c0010000c0740d0f0f0707901c1044203c035044480c83d4005001741808a004101c0284010034450045d2010803d5003c0c00c0f02800d07001841c001120081074407544135061146031440700900041d0b00303c1800c1c601e6807030b40b00074503005241102200e410440a40101b403c04072108121144003224103010802081c007040e00002e80031081d07c940ca0f107541030211484036441140901030038000014442c0d20105d1160700885030390358002c0020402402c003850111712008003841081c4c0c0c09407120b840c0c10b00d129003107101d0705012a0301007030003481e0050388801540c65080f03e2201e00d600408445100c038511840303004c0c140c4947e41c000d0159681e54135000c005000031105410022804000010329070040e241c1d40c6c850303919181c007200c04a80b81d020203515074000e820300180c40b030403240c00c1944280307484c070000900c0000700e4401d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 673528794 1250 673527544 673527553
    0x10060503010b010311191b0f0b07030504050a0210300b0102030a0207031b050907022d0c040911150c1207020f0111030c0304120c050603070c06050613050408090102 72
    0x150b00110306607283c045810501e40004c2262500080c00282500d010800710305048038510801419191b00c41c03134241c0309681442c0140f4030b101c00c00c012411110382c40b8001d41001c015900301034491540d40c03621078100a0064007551195400140103d2045902c000c1600041c82d4201c014803215007103510600050182a0070041209041d40c00407082e21030166160380101001d81c0303142c842030403248101c0034240a00c4c440c11400301d4552500604648904034a400a040404100d09601c04220f0040166490b50301e44201680d90480d0108800c40c401d0b200311808900c0a00310f040c04900e116a5030041039100e400c000304100e507901001c02400c003a040d0381040d0303941c03021004200c59191080040096200e042c0482c25134030780d030150845801101103a801c0b282841c07090480e80389075a00075046180a80010402d083c10004800c0c900e001910040e00c041e400d5003040c900c007404203200140300411782a21180000c01c5a21044c0340968440400e050a2089091604041805501440c1018018001c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 673530044 1250 673528794 673528811
    0xc150a0902180a060509090307020114092404050303040621140a050406271e0b28020a08190903020c0d030302120405250e0402011407051006050301 65
    0x55114664803a500a0120012074020001d0500820703801040149000d0350359001150342d49032040c0181c4a07150010041d80d541c4501c0c0000740480c50340084c45016000200035010341130700c4025203e86061100c0501e00302c034040706e050b004041d00070b81d003105800d448082800142c03180c0c4201d2000902c0c12600300d003240c2104a0b01c48c1025100500d045a1841a00d507001c00c107102100d500940d8017602404000400d0008c3d18084224000750b13081c100c0070a020301d0280030a00030411044002000f22001d0340300d1a0490303540718605c00c10001d182040c0c1c4100320503060150f41c0c4521040c00224134000003150784003000b0300b01811075681500c2c0a88000d0002c024654040c05a2013206400303500b64009044000e13030702d01082520000300d0412400c1607000d100e004030311690b20035120302070782c850000f6207405100500034030040c010103842c40d209008000b0341001000070016200d0307009a020300c0d000b031058000c00d10a0f0000d101d50040103207144144641da840541d4550712020590302c0840c02889240d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 673531294 1250 673530044 673530061
    0x703080c040303051803100e030c0f03120f040c09060f0f050303070b160507060203040c050f031c231c06060c050c09100b07050c09010906031e060b04020c15 69
    0x9039001c014041a01017100c40d103110549406aa000c010040032100058188031036181600e940e80c90400c0240d2000c2010241818280410b4400c841d00340c3c002c40c1000d601e11602510384202902c142041c01c031180c00f19040c01500640300c00540204c071001e0000ba640d031103c034000e0003928442e41660b800b1112000c9002e140110440b4282a0045404403198607000c81190f98007060544081c00c0c86400c01147c1d0000300707280040c510490060002c0c02c03080d031404050002c00201e10b00d15900c81e41101c08189002ea241f40c0d11490744010500e01a4034002c00844041c1d085510340310496a40140852403a5150f51512a4418514031100e014440d1b5642c80e84145d8002c0030a10703000713000c0d4100c004005c9160410806160b485a000a103a003d403542d03950b5110300b681e1110740e0a4480d83c0191407030340407908200700c0d00f03401071090b035404100440c61a00c842c121002079076072588124501c44040002e01110340c0004a011800030801c660fa600390010785a036500c040e000000b40c0f0f07041580000c0082 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 673532544 1250 673531294 673531297
    0x210702180c0a1805100201060f0918060b040b0d2003060c0d09020d1205030403031404020d0308040204200405031c08181203070e0315011401051b0a05030703080c 71
    0x1d00007101110308103424008180c95607012000d0981c074605245600080594900d0780c0d503220b42407141c0001903000e0030603840c0c0c1c13003a1070306800c00c0101c241085098103901020411215010b030b005400020320301e00340c0c400500505900072400c0c0d40964110b006c182840341504600d20841900320406103440f800350181900c072202101c1180d1407400601100500e90a2a04a880450710007010300200d0b100968905104041c011580f030000b0707001000b00b02c20075806210f40c8089a0440c1ca2804803482c25a0010300c80b540c0b00203005041204501c0442c0440d1280d40090012600400c0903090007403200c41c4481c4070385c00230321510303109100c3d480015011a828980c1100c61604655419100d90340c1c40201e0002d01340840c1c1d100780d0a100d855000b022031001e50303000e980100c02c0c50740c400c800340081e0304c105894143d6460410010030741c5400104403035250540c030010a4002801c110761551100c4002244400d020302c0c00381010f00582290b0420004040020300c00544281c80e01c00c1562603620028a15 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 673533794 1250 673532544 673532551
    0x30b1809010f092a1715070e091b0c060103141006140909030c031303150507080415020903070e0402010906090b1c0605061b06092d21070218 62
    0x200391044000304074104203880c032a010301421685110260395120368900794218401911741d015084003800c01d00c5443d140000c0c64010400b442d21071399501c03a030300018107142000383c414910012140d0185a4003401841952424031340c070400e0700d2556940781071004801c0b41030404414280140d03440004070004902c24041034614069162180b40c1ca001e081c081d01c154090032840d9103100c140005203080e0001c10042c66007000502c2401c0140e880c41c40d080e14a40e80010800c44c0c0b141c2031400b00801c942c0e000c400ea946c01030b0811881e2108d001c3c0b81100030028030a07482402d406015000011070440c6207078104e94001d9100ba6184140269603003002c507844002030243c200c030800308106100800d020020903110008000030300040c0d0070b655100044c2194001c001e01c1c900c0c3e140e209200b400c4080140300032944404060050700c0105450090b0344602c08000f410a005124001360080700717020b00300010322803d49060040c0d0980c514489208205801582c0202e1080101c2c42c8221280e807022000c0900 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 673535044 1250 673533794 673533803
    0x71e11100501082e0e0c1306030201020c0a0b0d0c050c070e01170106050102102a0210060b0c030403020121180b090a110d020103090c0f080c0f03120a030b1809010f09 73
    0x110100d0540300201401c0380c1c0300d04075070710b00c80d00395003000c0d5649969040041fa07228070310008115140d8400a410b10541d154000d2044036060401c0040801103011207010404841c3c0020f0504d2440f0001c2d24140900c001c05591846403c1011079040c020445e002d051b100c48a04c0702c05288000f4006a00341c46242c0102401a0401c2444d2a48038190703400c20f00d50084000c07030480c003103100d0320002061401d504480100503031043c1c40403540415180f04800c042d202c0a41c5040c5405a000b210031350320703c200d1100074100240091069003600101429000c458002c036414044030055000d918108a45984159042ca04d201c0101d98040340010f0034002d040d074041403080b02c0c0200c900c200400300126581c141c0c14181c0b10030ba0703c4001110800c0400150120150281d8280d05180c201c500d403038885c0d07040a00901d16043c1c26110b6540000321302c1507160340040801e560301c0e2000c03070460252802c050032581260040b1507001c4200c940c0c04459101f1b02400000b000740c0400351300345400340c0b80a55000b42 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 673536294 1250 673535044 673535113
    0xa0503030711061f05190e0a05071209110118030b090703030f08100303030203131406070f0e03060f19050403030218061309050705040e0c03160503071e1110050108 72
    0x2c0d03400c150544213503c10f1441206c18031103030341e0b080400324000101d0386a00c7d55a554020072840b01d0300030025034029015000204146011584c4881d20903903080d00c03846c18011450000701852518640c1100610b500203240c070345500700b01d024650384100f1404101d020458150400c0801c500c50008507110302004c030705913800d5902d184c03000d400942c005019010f0712204440240040f452110f0861060300e0081e00800040c03500f00c03001170105c010180c444080205002c02c406440d0f03400502d898100c1381c06001d400f40c94a60030305003480c284119008c034100f036080400704002d058055000d080900074846c519045d030032491082140301e204801030211401c6004105100c4c0941c2039004a5200b48541480d07841c1c203480d41d03e03070420070b2022110040ca842d00002007004849166008065508090410314114200814040c00c0800045041c440c1034010b016100103003031103009007044d854108400c2c0c0e000f140300c01c010540500070074041c022440c0710301c5941c211400c410407465000041015041c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 673537544 1250 673536294 673536299
    0x209280e04080d020d1b120f0903020304030b061207060503040c09052a090d0f0501110c1e341418062e0306050d03050a110a0503030711061f 62
    0x760080d0481c4d8481c002007503854480c8120b0a07aa07022446c1031008a48408555074503542c071a42c01d07201d6800c99140c806080051010020343c0001c2694107880d0b2003c0400759950b01c100c08200d99100f200900792040c800c600c400100c0310381140c011030045003e44445c1843c180c44076818000e81d0b6094030b820001c6038080c0940c541e840300ca04420100400154000c51800c4000c0000a4a0021004054603030300c0c180325603c0704200003445541c1d80683d03040d40041c11700c008503400a8903800e00d10520001c0310049007107032034240402d01204e91000028100c103a0b41d100031484484459030141d071f07981d4201400ca40003041d0240c201982d1003201900401c4102d00716441d0b90740d41e1540101401e96030f003003500c16034410322024250030720600751628511440202c2100c01e8000f01941e880b0780c415070007021100c2c9500007281c2d005044541c0083d907420210b1002c551500050b14040d01448060807500010041c00003007a0301400f031641300300714081107e14075159210100d42001c99640d1100c803021241c0c108 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 673538794 1250 673537544 673537567
    0x6020906070f1b050109030b1915080f0a0807030c0c080d030207030806040504050709020f040810020a0f03090b010506210405010e070506040e0f0c04030501060b030f07032c010209280e0408 83
    0x8d41d807000b10900c00c1070001c001f02200e0001daa1102d0420012a002844180610310041254112850300d440007808402c5032500d81d10300724456120050200081e038020300c814040100180801800d004e4220b40d04541c040400800075001604210002050b22022810519290080ca030207503030414060030510f450112694020742c0003051848400301c6c180000500c0d5501070088021403060b01d00d003d80c0c0c8401c040d80040c800c0c3e0b2074401035418985480406000f0403081c0c401c11381500c40903201c0300c0da110000d18140040141c210440f84c50310820000300810071106411108520340380c90100c2e501c1549500c00c0180c0ca02542c0900403030b11402c080040c40b0780e407241d00b0982d000301ca6240d03071900d016100d448032403c0d282c2c0c98200c41d0789148000117021419904012055110300c0b140b07010002c400f50031078a40310340c10410174101183c802c56100e0790054807080d811110214001880404103594040441c900800b45100d0714101440840000450003948403e640c880d40d88030160074a0100755440d03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 673540044 1250 673538794 673538813
    0x60306071d04060e01180e070e01030609030c051b030c0f03150709030b130c050a060c1403040b0403150506010206060306180c040c030209090105040c0210050406020906070f1b05010903 81
    0xc200b07900644490000803200b0540c016240a0482041a40141480c001c048800e803007454000b00000e42c0440780801501c04a6040241500d41c000808240c0d600340c0c5c10b0485c2d64080154002d0300074002c2c0070300d820800310402c01c0e0000c40d540c03d5051f50070311851402000800707100946216003680140010845000707940d464142d2104041c00c045200035101c1d00c440030030000440e01c05920021070003400040c024042c440d040240000c5071a15102400c1a9004255103003804005000020038005043c501a050066a0103440d541102c20380311951ba05124421641040c406040145005e010030869440401c0a0b841020023070000c010944a1048035020b900050f107100549005101030311801c3d40d00e90141071840d0301c45950151300e40307143c0d9003005854034040c1c0c8514403551808084010740c603008105100801c1800000003410369a03402e044010740700d0300100a03400078000481100300705c855080f00c0d1032540548804030800070101c1c802040030806025141c0401c81c842010400181c0086 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 673541294 1250 673540044 673540097
    0x819020d0306121509060e060a0501240507050c060a090e0f040c0308030721230105491203020408070b07060209030604050c1302072001020313081506030607 69
    0x50000b17032144140d11030b68120741194168841070b8000310107001c09001d81d40140c60140403000c0300305075445092204220440c0800340005d00384500130a45405000c400d01c42200d044001920903581d0b0b02c1003140080c10b5101500401c0d074a03040220100303000d425440002e0b0b11456110ba01151000d003140c0352010700e81c000034042c0042000c20908140ca15880e1983e8002680c01040041018105221040d062083e10b01910708980310071001003000d691007a404040884002c601429004400c80c103409031501c1c4000c071060549998241e14a041160400710861940106480c01000347c0b081da00320280c0c4100d205034021680006c1c0184504802d0300000c0c042544500d03001440c00c00309901190800c0c808807070030f840b6508009240c10150401c0308041e403101e440540304601e8400c2c00e64071110860600403001d10042a071903141d50081c0d0007001101c44014010800040299841012650301c03d08208003444040110000c5540c50400185aa000b06400d4440e094402c00f203017a400031090400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 673542544 1250 673541294 673541333
    0x4110a1403070b1c14010306141509060f1503010801050c1c05100302180106200316050a0c0e160903030507061a0a030501090b090a0c0b0f04030819020d030612 70
    0xc1200030354120300781c8501780840308415817801c015031440c00c241086450035141e5070a40c602c840b04000c4118000c10b618209450304482106080d04c500b4089088200000290750f00240c40c1c0d0740c05540c0001031030103141240c6200009212030fa44004030041c2da80160314030110359180118030341c1280842c50304402e82c8031548510498982d9604c0d000147c070f0816042d409030409080d040103200a50303101003844403041445042195418810800300e60703031b118002e402580b001220145600300203003400381c034080d83d810002d20000e99448d025191000441540d010000000320fa850070300c0a8000e0786150700700c0f038140d15001c1c2000c0d0261a4907000c3c0061100c6007120541c240b81d001700507541c0090041c0558000c6d00000340b685482c0c54403002400d0013501d821031a5100c80c46440000709207804039000e583e040b150454580c2c000030030024160140c2e4000400e102070110b1000c040841c40440030011052039821944005507404095046910b00c2c041c075130b81c0704220011607003c242c1c0c2000048041162 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 673543794 1250 673542544 673542577
    0xc080a02010f11071403031b0d09020303031807122a150f0206011202060708070f020604171006151407020d060507080c0f0d0b0d020904110a1403070b 66
    0x195407407a4121907240142da600c904003c2440000d000900f244058041c880030001c5196003000c02546510700000c0b503041000c23010018410a0020320b0fa0083c1c00001d5010b030440f61a81013094066124060040400301503200c4e6440006180200d40c501803801030700302e407054641ea42035180701060180781108a500e03440c0c100e4000510048901c104407540c0c9500d507a14800000c0005c002410b004040c0e000c0c0010002d00c00d03510001d42e03130304000c03a04c0483d44007003107e684a05602c7e15117102c0041d0000a0350004011400181c00e48a403c2001d4007154000c05a680d8516948841c0d01210f1182c018580d812180200f2007500f01e000314000c0d80801c2c0104240e174101941613000510b203260354101107810303940303c4050040e8107811050316600111210501d07400c0180c1e0004190440c09140c1d41d00503215102ca4058400740c44030110401c90703680240c048481c80ca4141007c0e862554003826003401102079002c0081c4204003184c0501a590000300607001040c80d01d60603229a40100f4030318443d0300c41c0d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 673545044 1250 673543794 673543811
    0x4060f030f090b0403081602061603020702180c09040609140403110c0904050304051c03020309060a20010b09090327010314090d020d0c052e02040e040606060f0c080a0201 75
    0x50fa802142c03046111366a1035100349450901e1045a410700d0340448295480340043c881106198040614020004d190041e11480540001b5400d000d02501c0915005040c05c03c0c4210004058010100500d080c0c4084c401a82c1c3d50240c0d80c1152608109600340740c0f0108045030009120301c000e2041c0400d0a8129020044c3d01800103903100320075a0111425440050108205e0a10882c142c030032010182c28140e0740d0b020750310003a41b20300ca12000903100708000500c0f0030031607004040a24241070040e03109003081da013101100d0b00900e01c01c0c201a1240c0c0c0000c00290402800104450b95600c1010017107401c003c9903210001c003802c68103030f1103040c5600c441d0340ca46c20100445103907204811040007050f0540f49408080d007815039001c0c189040060840d0200085000000c8001c140004a42c01e00101000000c01070303444c144c071103882e45aa078000a00003a50100c0185482d02841c00b4110400285907038090030303612800c104540902243c3d454507550089061140902075100031400080303010320 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 673546294 1250 673545044 673545053
    0x40206090312090901060e06041503020f0f031b090f040914010e24010b09240d06030b0606210c07061b021527010f020711090a0204060f030f09 63
    0x20860ba203114a08280483e41c1040c5140055100e4010200e90402c488403041c0c0c880807400310f101c2c9015242564901c0d0a0300c48180d8031a40c11141d40181d1000c0068950f0410046442d1035402071311801001c1c0304034480001c602c00040c0498081c400014810005c4600d1103081c040509510300381030f600850402c99070781190000307006407002d18603a0005407100200c0c4000c04482d80c46e5448050340c4c1d20f003d440060044000a400b142e01164048881100c1030f00081030300103400024000381c4211142c085a001c10505064004000b607902c6403000141c00d5944c40d0500c0864090995440c0400e050340e04004500d03044a82040e030030040300c6406514200c4c00c0e03105c16050320b29007601458201010100d440d49640d0620862401c14030850030300e041b034142440300700040b410b80c440400c011841c0103110002e85100b5482400d03a088102c01c159241c1a25040401f4107807075a891a9000b15401c0d00043d8418a0074402c82c2c058802035114000c8a2000d90302c110014584400320803042580c0d04080408039 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 673547544 1250 673546294 673546303
    0x37051305071a031b0c011e0e030c2805160905090c010e13020706050c0a03061217090d20010306080706081f0f03030f030605060703050d050402060903 66
    0x41118012400900406192191612480d50700c2248a003107082d09101d60034500804a84d0010685a8075500c4d101451015078841d00c2046036120041d0301e01080004001e02d0351812000504c104d000402c207084d012900e45803244101c0303040d40c9654000c0c0a0050700c6003111041c58a001d400100d1a500c1c40700c150395214549002c00c030240c1880d544045d0100000f4609000d6540d100c010a0040c0c42d41d072680c90000790003803201d989142d110b5190f41c0c6010840312040c1d4140d071115604804203014508002174a841d403980310b04000b500103410004040340c14200ca14020ba4815803011207200035803888070300001103422081d502680120310f081d02201141c128501e858001308441121001409004009000c80c2c450b41d01c12030740350700282020018550060052603000c3d00c54404640c21b0100103040086411803900540500c0704166008001d00d03501a8844440d8503d549041014984910030003046001d1a8001400038508000424603480c041c0c10958012b480034080604080d007500009090 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 673548794 1250 673547544 673547551
    0xb0f19020615010e100f02100204030b06030607180b1c1a09011703070303020c0a0c0f08010f05010e1501030b03010513050606060f0f03041e030c060f053705 69
    0x1640520180b18866124001c00c001412090030704090507140c80c0c0120f01c4003070550f59402c09224440c00140081030090240c10b01e0303482c40b40400c555076500d0b071900280c04e9906480c518024072440c80090480741c0560650507003142d10402d00b02c100c0b441c0400c0200d150740032000030420a180389960329040440b034001c8603510000e18a07a0680b108000040c414000c505a10541c01d881c40701103c480840b40110488200c82c1d054500035a41759a000c240c10703e001790400e4014901200d0300e80000c1c0042c04807400c41709a840040003400000c0141c1c1e0120155480be0041442200502c40030032403501040c44000200641810041080c4050b40f00103801c40702d003281c0010600d16958410b40401c0b200744001c42e8405003c485203403c0c6120510116000d01400040c050940c00000102c1c080c00042c00490306a4a0003008a51840110340350003040034018420031503850341041046045140f044c0101c1d4451500e00e00c0c4484807984075400c10030035883c40608a00b1031051a009a0900b2149000f0310b4407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 673550044 1250 673548794 673548797
    0xa090b010803312c1605180a0503070b03040b070201020306150d0e01060f050a120b06040b0315010603020d060905040f06360309080d05040e150910140604050303040b0f19 75
    0x1454104086510040c440045c074040035148051803d4442d19000740640300100fa115190782106980700c0c021500b5200142c110b00d40c14814594002000c1700200c00961007248103007400c81c1c2d40d80b102907050303090340001d807401640210000d04070824042090040c0446030044000803400714212140d0900312045904013001c1001c80d09001d1140d410880e80b450018050038150081c0d80c102501e4040344820b020708918441c9844045e11510f03650100414404250040d041020b103594070f8001500960081500b040c0050070041d0000780000c2a129841c401da400c500c52170880d07801995182d00505001d40640030400e800c150071220001329005101000401ea0b40c0090300303a0345c50030080c14580490b48204c0151340310640784050302c3c2d0302034242c4080f03d41032002c039104c03602d405040c1540441056800d98002c8031200800103084840040c2c1030840b2513840b0241c1c0740707411440900510348200d02440e138041e070040004000812811005004400c2400203950501e40d42c20300709500c08600103a54070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 673551294 1250 673550044 673550099
    0x60c0b0c1e07030e01110a0b011205010920091302010e090405032205040e03040605071b09110706050f13020d02030705061c06060305060a0b070f06050a090b01080331 73
    0xc015600014000c002403d00401050034180720323603420300c1d4950305000e0345140a842008050400c40c09401003e0540c3d800070a03450341640800780e072500d1a081d405a6882610031102180d9036040581200e81d0058041c4d65161655540c4410300080c1400940300f196684810450002104008901c4403411104c80e0004a8500e25202c02c000c256260709401001c0764004010410006401000300c41d1320315440102212404414240400c0340841540000400c500740385000c0c400340500c1d0300401c0440c3c0f1a60b020805ca4850300101d2060510844184001c0280841c095015180500b84561145e100030219280c194440020508075040101d4051410f0b4460023503c10540460240501500d81490b003000039191010009418499910400c6084000021a9800d0044c00d0300c00c5207955810100900c641e0901301d075400c008100c105800e0f514054002c001042d4a40c000c802c030303036502d042d016138030700d403580358442c2042c620810f940385aa1000c88c0c0d2a001a070040e4201800d80405a030361140d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 673552544 1250 673551294 673551317
    0xa17010c020c04020a020d1206090507031b210209030712051f0b03070905040302010212100828061d06040b16020d020d0f140c16060c0b0c1e0703 64
    0x80d181240070344105210f180103014003844e041e0300203820184110079280050880900d411490000d2240d900042513032400e0208000d55660140c200c070710b03e208105c01c0080100304850301111103044031840102141d0740d02c400608007204540180a4840008041d2a921613484120b0340b02c000101101701c9183e0464551301c001e00340412401d076041160300e041800706074140030019444104602442000d9552100401c0605100f5410354401c160281900882c078100765140080d89a4035105001c00d0303200b000114440300f004411400481e51030b51a03c84803c030495540c6002030944003140e2000351000b00003000c4035440401c4224040c0340580a10320550402002c180e0410f42102101c00030b40d4001961010265400288580741542c01d24001c072088552032021a6070700c05021541000c440b001c500007900120114007240300a28046044246603036172101a03d10b410200d101411840343c0c0c500103804040c103000140111003140741817000000c00c40c00400010f410104065000402d0217105 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 673553794 1250 673552544 673552547
    0x170106111023060a1203080726010806010902090a090905160306150905010b0703080711100203150a05030a2009041a011a0a0c020307080d020d030f0908090405060a17010c 75
    0x10b95402881c2510695101d5041000c5000000c4c02d243c8020104001e4000241403103104140f4151001407a84c0388e00d4400030b041c0782103148508280200d6882d0b0040d04000a2a084540308659203200c0103086200203925008801d03004040d218403c3e610f0380210340c0405254401038a000e00650710420700040e218044240740007000354960420303030f0b8040c5050014000da9800070143c4901036411302e4504526a102503040300e4030380542c10300c0400c61080c0c403040c0a6042154000d103100d20702da000215540001c880800c400025035110703807078054010321ba0380320109048011240c4064801d201e1803082c180514086031040500300d5050359205510074140650b00b0151142600400642c0042032190410981c403100a10030408614103024642e1403280c1151030a0214400a00b99402520010320790040080c5d2a03402498900000910744810201c00710b1891080511a50300080d00071704100640f000d000084c44040c1c0030551009007034a000070758608420441289141e25400070070101d20b007000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 673555044 1250 673553794 673553861
    0x61e13080c0f01020a2705092d1501020c090103020a2d1502010e0a20010e12010209090c070b0103080a03090204060f081e0c300a121701061110 63
    0x401c0f001074124000422141c2d48000310150000300c810a1a89e02c0701c0301e00815088040700004681c0d04c0c0381c401301049031004090ba60140c402000b03800b40c4044c3d14a03c0d0030450410350034040254404070400301840203600c00b03040c4261042d002d42009469070044c11962884000c241d10090f51201c13400c1241181a9080c010303c51007011150051092420550780c444011000614280010b008280c2d4442160701c0780100061902c070240454100d2000f1511a038083c3d8051140079011700c0ba80004298941001812640d042d0b420940d45021a403c623600e2a003541d00c080c82d41802c040d2145400c4004d41d0313540c41168006c101204450018034600130201c0d0600c4212011850494201800c000801c40c0c041020804200d00710780b52044010f00f9140148503003039140004030301d22103840c00e810040c0f000094161406005080d911000300c130521040f1210002c05107a9102c082c81c22004005403402a0251885070b0384520a580d04002d51551840440d5002103654070750415000c4c0000103100c4056 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 673556294 1250 673555044 673555097
    0x19090605090f15210633040b1c061a0d0f06050a0902060a0305070f0e060d0f020715090309050411071b171b060406170402060d02070302061e13080c0f01020a 69
    0x40340c03071407107681b20644c200c0d40c800c0d8420040d0080e5280d0042000560340c103450941c107800b070329110403c5c950050400b07400400354150348094041e52900c2114040c640b0380291015a540400c240d0240d444c10303528000a0324001c0c0000f001c0c16142c1c0b1543d0300607960340029019041c800d503000241840c180340f00901d86c058a0203038100348041c0c007880301200d0700d80c941102c003018441070005c1000914141e114009202d442d10180005500707482201c02c40f00a038101d804207502981e500c19039192180708100840d250761515507000d000c10044000010324240009400030030712500d0403400b80d078070301b440398610201000c4804250040a1001d00c006000340801d013441000323451150609042c510301034449500506130088003021100010119500e001c03c59a8a00c0071070740541d256403562401940d14401074807440240003e4403806590325900c1c2e00014413030000403804100e14109500d0340d40c8640c0c440d0989400c5030280e0840c213034041009000611000c0d0380b580e2a25108110008901c2e0407031403a2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 673557544 1250 673556294 673556341
    0x10501030b100507080c1903090602010c0923030d020a200a0315060b040308030106270b090102012912071d06010e19090605090f152106 60
    0x4161400c0e07141e01e015041c0b85119802c007181e541500341481c0000e800b452a502c24981b0072201500ea1007010180d802e00001e2003611801041c0751548410790a0381c400000c1b50000640800303003002805100382c940034500340300340c0203419004a0300d0701290504618101c00000740e070100b4a460200029400100083d4000028681c80302c09020002202402c0034070000d0f040028402c000c0d107011600c2e81c088030041188a80b010b43d01c9a0724584849113400900c14280800e5034001c1440a0319081d50425014150000003140018109140f8440d01e400c00c0a01d80e0445d90707120301144e505819259100781142030072480104e030050b8601000901201c000d01a10940c001c08410082c44020703081008040800c4240114190780c1c200c0101c031f0b02d0000303046103644003103211010118401c03800d90100940c6e41d04030b41403040790b072114140708921409071845d00071040c18000160a1845c4520f403500d110700c3c0145180314004035204024421511800012007070340121081c016444030080740c8035203500c40b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 673558794 1250 673557544 673557551
    0x31b180803030c070b041a010303080f0a090c09111c05010f08162105011508010501080102270607083105010206060f0a090608010203041106030c0a030e01020405120c0901050103 78
    0xe01c5280884e00491400804224008000c0380401408102c2200388038101140d150180da176030f0400916420040d0761410844070000045030002c3c04c14090008065000002c101100f842c0107416402401d0300414185404410b1090160454184038800b14100e074000000c80c065052945040e0950f00d1a80020030b00d900500c100c076000e188030b8484000b19000b1035043c08000c0c0c91002e0171101d06140c0040240b040d4a4004a00100106004242c2c140c0310520007c100c1a0380b140e109034200d100b584030b903c91152425203101e07010b0a1203866800041d0b4050703e282e0a00d01503688520140c0c002d4044901d06800a0140000600750100c41b40d10304140d00d050450440d244c0340000c2c0d1a0030000c0c0491f806480c02d12504801c0d511658402401030000040410000e0781e80c80c0840e0003904141c8044072054502c01700c02181c1d141c0602903900030303541c0c0c0d9803262030912140c0d001d03402003960b0301012035155001d00c00040c0643e10050600c06000000020b401110440c00800c880040c050b084141814903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 673560044 1250 673558794 673558801
    0x40c0201240302210c060703020307140f070905060a1a03011401030b063a090b0a020f031f0803041d06150d0f06030507030305090a3201031b18080303 66
    0xf580d89002650704c83c0040001040f0160640c0182441c9465078101c0d0080000070328030013010381c008018120700d401040c40e038a15090300b0701d1890300c4600c1038007094803e502240040c0300150407980900c7d0072280043c024808159540c0300544802c5e6050009101c450011004000b10111a4031583c1070010074031b000c0002c041008001a443d0198449001a0b040040044034009403a801c4405240c0139002c02e040d84200a200c25a018014042d02250800d00030380200e03c02c000e5a000765100c0441080119046644280120042d8042581ca88501d00412800040c000100740010005002e49006190070208008008117040d07002520070360042005106400d91001694255092090017000c08a41400709038403802c060800c40c0c01c080e01c58007a400c4000100341e0004020042030303205480842e281c0d643c402141903082070152041111500c12542c1d032000e46441813814200c1901414002540d02c000c205640340007203031900e0f40c8085a13440810051001f1003600742d070014480c10004519515 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 673561151 1107 673560044 673560049
    0xd1a09040602031602010902091605070b0a0204060f1701090f0204030206130305010506030a0b07080c0715050106021006120206030a061d041e0f030f02010b040c0201240302 76
    0x88101307030031032264a0041c01118449500100303100000e99071182c104070740200301d014140802c0020800300c40000d61246020340600d009c40c8005885a0408901a01035085040c2003418010090082c21802411400070b9064414401c80491806412214440a80a03940000354404d40c049001d002d6107425102041c216801b440080c01a5180c00301815180c103c1c2c044043c2c44802c080d800202128040c03520355803c11078041c0454074049103901d40c42e07540f03a88030700c5a1111945480040000c02c2d8100700c1042036000001c8200300b06460032805c00c220746080900240200c1020000603041c0e1081d43c03100c0010403200381081c03502c2c40d01e455040c00e0500e00300c404440d9505000201c00b0041034030724151841540c082440000c406aa4a05844280011078000700310740d280d9104030f4182c0c540340980410303e9290380011584000080702608980c0310662002000300c1d81c108200050f9 = true := by decide +kernel

theorem cover : BRFrame.Cov 673381294 673561151 := by
  have h0 := BRFrame.cov_init 673381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 673381294 ≤ n) (h2 : n < 673561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
