-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0743
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:32:14.848642+00:00
-- url     : https://prove2.me/submissions/9a757e3e-0cc9-4e4b-86c7-1db1db40242c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 133453237 ≤ n < 133633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 133454487 1250 133453237 133453241
    0xf11070303092105090414010806070804060f0e0c03060a06060507020609040f05090703050d0206190218061318090215030c09030607170f040b0112030e0307030609140d12 75
    0x7241c11030300400b5003e03440020451480c040304900803140d440940e507a04203814413040d51001c00c1c203c250800c4620041c001000003160481c1e02952901e0b0a01242d030716800d08001800260f1080e003403540c5405a60901e112011440d0700c504081541211260f444044500080300d01b14411a00040c00620148006250000c000c1c20100001031020402440c0c1d901e107001102d1080c2c3d901001c55008045c100104002485103210b40e58050014050034a8020b0042d04030303681000300f01c0b030199400910541324484c500010040c031880584260385440d9000001e102046d500e004400c0441810065264010058010250384c0c0303501a21080ca406684175154100d0742000e01302c0b0403080c40a10801500f503c04114040c0300701c60566442c010154450484c071110b4001914407442560503100b044003045035004d2140c11100380140481421a43c0c1c1021281110030400e06613143c002d50b50b0000c140300da42e41100740494058540044004001000f007507559599060b10000700301007002c1c60a40715419 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 133455737 1250 133454487 133454501
    0x405070206090c0d0c0e0a14011508070503090f06071d0409081209030409110315030d020c090c2b0b0105070308040b060f0319060f02070309050904080f040609090f11070303 76
    0x19105000c0150b2610001d1618000840c0c2c1f410800b543ca403035112851782c050304240d004040011000f488074500c403400400e5500001c00402c107005000003c00c604500c10041103800c5180700c42603c405007420b0400420340301c0102100075003444030303515242481c602849465902980085c24501c5d02440c01c1120103441002030500410740824072002a9417040b9014481458110450441d900d103007204089042c02c0340454000d011340c2c81a4000c034541030300044c1c0140030007011201c03d02103541e4070017801521f04ca00007a1218100c01d158000d2084003206a0343d04852041c0d60381400362100081c01142c45008540028000803c2d800100b00410000400d030340d0891409000007030b00312038040220f0315241c3c1c4500301080c1a0411400981405180e00c00c08940c040c0b03d030011361410020f0384004000400a024451140c690381021500700850601194414244500080c0d00c1e1aa9040302410708911449071031022401c1c1016800507000302d103e1213040203240004542020703a9900d00710028000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 133456987 1250 133455737 133455743
    0x702090414030a110106150c15110d02040503010608060610080a021e030717090d050c1006080a0c0801090c09020901020709050a1d1209010c0f120804020405070206090c0d 75
    0x1000c00e100760480c009000801078119079840d1260f800240307400c513908648181d0300546000c684254440440c80d801018020060780024414903000200c961311002400e04d9010002004400904045a2046500680110b1f070085008008880d0f42d160000d40700c440444541e584140459001c8902600401d84a40c016554003001420030003001060340c200c2e80f1550102443d10804010800082d03440988039810820319607200307441d4100301d02c1c0650303a81908810f000601a001c695540210320070090740b040030380342d0070062014540d070300041c544a845400e81510006110100818900014010148640d5003d02518900d501d0213480c400203400c102e08060460040d5400000c140c00b19018060048420000010743c4603015240009000c64040d0101d07499041102a03c0c0f603500c1000903107581500c213082c00707020403846240024880440c20f400420044070b1200c0d01c04070940c41403040b0b108903c292400c0006c0e4445600981c3d0f151000c44198446a201c1ea41c039490078208200e1148003e44 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 133458237 1250 133456987 133457003
    0x4110901111f27050c0d030e1917010216030305090c0a08010506030c030c03060c03060d05100c080f061f110111030603070b0307120203100510020c0118080307020904 73
    0x2144004601084003242d000000154545161002d030070707002060a90082c400b0009036001030034560700d464490201046251040425030b848005050046260395400500141081001c10b010b4082000080d042d01880585115040c80b4424600b814404c80704c0f6034480c030495003409a032990f030840140c4801044681140107242c0e040105403600503980e400380c800040041480e25200c0207051500e083e0580d0240710364411140c0b080c0f02d45011902d40e40100d04600c0803030341c9a8039030000c41c0241900c204000e00718072504501c1f1411940319400300c205014540d80d1100a620303245d02c203809801c030030380d0403030b6000d5000c4100c0c03404043c2a0300700d4480c000d014100741c030610181280107402c5442d45c218100c02e0503000030070404c60b440d050080c0405400d10101076401c40c20301050042000510800c071500703265001002c507481110280104c001454001d022841c90700840b4402034442070900c00881c0402d482c1c1c0c1014142c80c540c9100a8203072503030440218281003540d000c005031190b0150003510454 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 133459487 1250 133458237 133458253
    0xc0504030506040302010c08090703020901031401090f061506080105030d120b190302120a0b13060b0607060c031b050f0304060e0f030c070803091309020102010f060f03050c0411090111 81
    0x3103041c0a503503c41c03800ba40001520704403941014102d914010320011654102c0442400140d030b900000c6415030740c12180495032484101501d030300501e0382800281200c071485400c00c080115541002030449074001c1d2511006a44090945000d0020301030103038944c100c10440301d40148900b1120002c81c02544010885041e207201041c0b03d1800a821000c1c014a002800e205500f002d070988200b130000e0350020440300381d40d03403941c4900000c0644800060b1803030480b04000d024964022464504008003155a5048640b41030f000400e0851546030100341012084180400512089090301200791600c92074080c0305a14014150300051045840307130b41c3c50810184041c000c11944650714a000d00542da03e080b0400d605280842507808800643d108200d01111502d4400d0015a005000c04d408103101801e4401030f40502001e4060741d0b082c81c903140c0002403a40c111040d40301100e000704184e412144249042c0400e90f4078881106030280c1c1c0820504502e544190402c3d04070503c84010f5407441 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 133460737 1250 133459487 133459493
    0x9130b0604260307021f0c120f020105070306030c2601020a0503040201120b030705060714010509030d0c0215060105090a08030c0c0117040b2e090c030c020a0804090c050403 76
    0x160080d82000c0202d504070050401032114841142500c010004021400d01c0c1d00c0e50700088040c041a000c9070b40d180a20031003407050ba40954012081c50358402564140380b42c10300030003081441e40750240d000560a02001c40c0849000b8400e21007629007100441c1070403400c01041c407404031a081e0403100a4002c04c688003d07542e60a1020700350f01d40c019074409960b410540001440704001000e2600101e10341460354000da5030008030b06c8100d460513201945c881c00e56007030008201c0450700c0d44541550824041000c607140100040426080d60841045540e01808041380d41d0542d07000d80c501d20f03404030000300b5030359030140c0058280960001e01c00440c01d40c481d000706003075400001e1010213075400440800380304d60f0003400303901080340900c50083e1940381603203c41e100326101508200559940c00150554401d41c96003125003070954004020902d503580014500401d1003440ca1000245040007404c00c0d07500c0032586e002403036048688541810b04041d107440c01040002808800d02204000c00400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 133461987 1250 133460737 133460749
    0x9030d11040812030c04050925080f1023030c031c081b0d09020301020412030203091905090c0a0207120f0b06010305362a010302040b09130b 62
    0x90a4004204640c40d2407914008602e0300754041c04103840b040f02801000700c0311441206441c210345040700c0b905040e0701c40103005200c1151402d618106d860910925643c00f94018650794020700e0060800c0120b0340e9100303544005104a030040000101c4096403040030800c0748100351890400040599844404910003c0e15240d03400707080c090a540c2c14440c903e0001c6d04050015030040d0f000302030f1b190845032400f17172400c0c1d03101c0c207a00a042d00750340342d1050040d510254141c40160140c0c81c44180303104180d0030042c3d502c4d04411103035442b5050f120440074001d41ba00d0180c80480c0c01c017908001c2c40d501d40c184046a280c0250010004610034a040065824402505880054040c00c4004083d504604001c44600001014203044c0f605090074820f0307003052403211840c20340d000c603c2e992030010940d5000a4242c0780380c907040c943c0e00c50740e860b94120318000041030514040102c0386080707000b5040015400c1c1e02440c0b04440a120040c05102c0142c01e00301c80c003c40c1c5d801c4c00b85c80040e019040c0000111 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 133463237 1250 133461987 133462001
    0xe03040b13060207051e0d06060905070309050f1b0904030302190504140901080d0c0f0b04050d0f030b06070201030c032d06060903080904110d020c06040201030c18030b09030d 77
    0x1078590451a81045a15014069280940010384503801100302c28984005040c64130f403840ca00610141c18400103019080d80312070040c05421000f48103030b050100380103000e405d10301020b884c1d6004038000c004144030009901d1440301c1411a603100121000c2080000108004000b034040c903400b000100e41040c60b5440341c100d4240151a1191110b082200e91b81210708030b00c1d5a180101000070050102d078000080c0c40141e130601c0e141c0460704200b0751400105034040d60030f004120045c210148405c10202040401002220b5966000549803203503084013903414210440d60446000c00c00c01c40994400d41244a42d13001c45d003404589001c11502420919840413074408101c6540388802408401c2d074010b841c001c00302440d02c41121401e40e103414405214a20200c0d02c200d603030344009142002c0107030550350b6502c810300046482c1c1e6402c100c0f030364468070103c80480c00a40382440e0b04000d180141410744075800c1c502c8103005042e0865980c401c1c0440003515060940c80305018030101c00b10756006605e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 133464487 1250 133463237 133463257
    0x6021603110f1912290a0e0c09010902220f23121608030a1202130509070903020a090219230708040e0112052104030609080307090b0313060e03040b 65
    0x421544860408840d00f10a90b40d05031410706141040d2542d5045d25982960005000fa40c006110321040403414a000d10b00201d240d0031840c0c42c000014010b070580d0291513041b20354040032901704a800f200e56003442882c021060144e400301405c1c84107981c50b0703120b00001003142c5803100c18541c0035030000e280c00c8022900e4002591103100c13042c40c6c11261410b040c00910f114402981801d9a90030301625003a5403030780f5414125408151001e04084502e008001800040c0001000b400e007000014080304490006a000b4071b01c4480004070960786108a5000c119615030744003644201540c00c5665807882400d00340f2b0050380106a0881c45401c000030214144529a010780d10f514101d501d03003000405070310224460380c90600840c0450030200301d0660075101e01100c84000c01c034914143c01e05000b140c0004c0d20701c5152150020800c2170341c100450159409031200a2059561400c000c480e1104840c24021441c1d118410700003e80030380c2100c40d648400b41c003a40d007402d407958010300064009007000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 133465737 1250 133464487 133464509
    0x207050109061b020c0d02060708030708010815010e040f050c03010204121b060c0f030908010510030b06090403140903030403080a08010609060507080f0903160308030106021603110f19 81
    0x260420889100d400e0f4180801242041040050790b4080e48814609075450701070708086044c00210b65600007198a801d038800702542e00c0c5c0c20124801400701030240a1a042845213a40401840c810204840e040b5000c0350410032444e9202c0d500e41c2c4104d08000c40484d0607200d03000c00d10415a400303001401c0501a0048084850091824030400c024210040310f5182000b04030207120140d40401d000100a030040500300c0494803074a412642040c0980c4512041e51921050085181ca619146d108a0340958a070061030744800040000784041501c00070302007144062a0800c03100c0480180404a078001c080d6814a6a6922a141c60b0360000e4025400034541074010b2001c3d40e080351035540134200c00e00c0c145050010a9a56004a2107540d1842603801000301c2c0800950f40c0800101400ca404c1d0900440d1359956803410304541e401c20300540c00540101d4526004a8440f0213251044941100c41d4202509044051008074a0326600150f0410008005207965400c484003000040002c500c1e1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 133466987 1250 133465737 133465751
    0xc01032d0c0e0405040803150d050105130c080303070e040c02030f0f040510020316150605030d02150114030307080f040506070b090d0c030804030f18061101050702010209011403100902070501 84
    0x1482845904100740c403ca142c401804041914002030343d41c0400c408809504010100d400100d4106512100030304943c01e2508110b211020108003404092085060180c180d4491022685a000c200d92001c001604040e84000e9407070650401810785003140141c901c0c01c021034030442200e81c030401444d4004000001d0400c413a082ca05001c030f400f09510301c040c60810f081240c5c0c0c0650b911080c080a000b01e848080b0403000d00a03982d01500041100908071419105100c0c00039449a5016150b81e00d44ca40180000640e80380c200190710b03040b04001c01452420106582d030007600d0700100c000c0b1414100a000104154032203000410b40c03d8042c009807281803074810b140f07502d00152140d81b40100b2502c0c0310701c03030002a0465074094110764541081e225000c40200104e80c0d4031024429812440d40041300001c0e816006050914034403c1c16009005079136900c1d200b6401c0c0d10411250034001040802c02c0070174010140003840d0005291010584883d60380c020303103030598102d500251844d03599414 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 133468237 1250 133466987 133467011
    0x11100213051906050903190f0b01150203040902030406060f1e060302040b091201090501020d091e02181807030308070e04050609070311120f011706090c01032d 70
    0xa58802418221a8003a080b940500c96001c891058030810090200125408580d41e40038040e44051030184003181400505a04007508106401e46081c0c4401c004000041862001c150040103e1000b41c1c0003180f070113280000310b100035800180280d4000741e80e000c0c0800c00104814200000b402e183c440d031028030100315515240c22311140e105c0418184100010881040e040003507d0900780704031444510044403242c05409880c070480001d180303510000d01d20488040c0b60f485080f515010f44024503c589400a40d185140401c1c50080c0d403124400d40d1151100a40180c0681d0080420f1a04440851035010113850040b40d5002140824800700801002c1f640c4900142012401120180103a08102c2c0118500b01000380010003055110001c0400c1500d00310221407102c1c83c109100c06a80c030b01040b54400a00e000c4c01000019094240603900c40310700050380f03074060150240942800c2c55141c006400400c140d1041c1590450b1990b01c07505802520f800d400d503094000a80441c084180d85 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 133469487 1250 133468237 133468267
    0x301020412141b0a05060715050a1b05120c0306030a0b040f0327031101090308070f03020d0503091039020c030102040614070c0308070f03080a020703080f07111002 72
    0x5150a1451400020001c10790391038558010440c4c1c006c6c1d6096548000302e061031a2064008a4000c18603420402441a0300041c3e41c0104000c1c1800b40000c07000d520800302c220f800c3d03c54414502c101c03d00c050b01082220002100540e0440300c000c00f12958400710760b4605415002c21503055500714080c020b02800d00d5001b00c614001090704201b017403580e10014010110b400411b000c01703051001504a900c41c240d004525580295800140e03603171701c89210b0701c0c102007880d0700c1850440040c069040c01c00c6c0f0f11401401034078007a554030700242401d4007142021800804490741c0728445a00b10100d41c403401c000040a0203410005500407400401090002031324083d075903003a440c00303030388100030810516901c8bc00381406803514100107a43c079940c41c1000d541100c0c442d000900708010000350b200c104010b011a50152a100351919a003e545482e0a00d08030b004114010340070070303ca40300203908051000d802e10b40c070460310304000c5030090060b8929894801000b0300880b445900050524043e031040e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 133470737 1250 133469487 133469503
    0x6010e0604051303080403110111040b0403021005070c1202010909020c060a0b01022a0d0615030b010603050c070f03110712050c060a02030f0f2104030305060306070f0e030102041214 80
    0xd0540c09202006544c00600394000140003030104410000001d2030720a081d003000340400303600c58005858544500c00b00b06a0303406031000703d00c00c040d60b58810040303a010758291221160001c0d0100080c80c58009000074251920004904011010074007141000d25480500001c00c08880103165516046103104d003241c11110f1000d0543d070214403258000d14440c1601d0054042c0010555141c7d0048404165094400355004100c18100356440d0101042941b00f41c0c2224059010b5a4a42e66030301c405804854041e5803c1080300c0040040d100496001e0b80010b41c1c09100b03181070403c01420850703150801c001c541180c0c1550000300f1568090140c05c10070b0f140c13101001c403040740c90950450b0020f5540d02c51f41082114401d0042007806200080324191005551500300c005100582611064030212040b1421800b00f0700c0d00c00403642e20b05000884a1085403152160f1803441581101910111011040d107641136400b00000b160f40030500c01251103d901c9060000340d075540081c44a42001c00d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 133471987 1250 133470737 133470751
    0x30c080c01021506040f06080709140112020109060f0c0218101406030f130501090b0711160506090a051e010e0603091506040e1f06060e22090506010e060405 69
    0xf11440b003c0c10f0084070426600f001c422240010013402952800c2c0c05400c1d03d80c4101c4250203040400214610705030019520421341c21403829a82ea00c420800181d001510400790008100c80001c0c00900c0c00b901c25020f01902c54180340041000d194005001210b0b06800074030308628003414445507000780628400541010600804c56420b03180100f10203010080012543d008403402007071040c00400105030070b0715044402030054607118200714058a030141c88000020b1140c070000c40f00c040c408920340300d84220446003000700514040c100071540c0c01880c02c00c1d600031950000022a941c0d42c2400304c00d00b1009403041c554280701c0340b0001d00b612610222035406040200204140c41e40c0224911034054548964001642c071070001080c02000c058902031018418050b644003421091044d81510881d081000d00200361186d1040b103070104101c46403074100440c40f6a19054901c960082d0001c04204003000844800344d4582902d461420303030007004606d4030700d800d0007411309080c0506640100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 133473237 1250 133471987 133471993
    0x9050910030c06020c0f0603130219030b0f0106020d0e01020102040f0810060b0313080a02010b0a090b09060a060f0e130603080310090203040803010909030c02150408010509010606050304021e0604030c080c0102 92
    0x5885c022921075080104414818100000010481815480310000568003d0304030303102d22500100402440301540001d5400c500390070000349400406100482c140e0b0b406601401c2e07a03414607a801d032108088660013a055540900001c641c850901401c0ea0080c804000200042020180c51200f07da550303800c4422500c00402c20040e4080301484269001c40c5c2c0320300841d0740c07148100c40c102d006000d000c00b115070054040da00001c5d0380300f15410460040c0c204445059554403054200615081144640800311f000820009001406054a48a620f43c00b40c41854084103090b005021034103990022204001c02100744582100c100d00c0c04030141c1100d03101185103090603154005240014402c0c0314000d41c90301001e008040c401c040304000300e54041c0038120010191880e05070140c11900880c8100d6107010001002c5903414010003085907403581b038031451505daa03020f014452280c0d0055160700c011072004144a41c40b128010001580a00c80d0085554141914182049050060141158 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 133474487 1250 133473237 133473253
    0x30a110c061b01021315032a0c03120906060f1502030f07140105010f080d0e1f020a1b030213090507060305180a05010c11150703050709050910030c0602 67
    0xa00c0c0c8008403200058030b00d11202860302c040903014064072480e480c040c004030321140005404009100d02a0320959561400d011085010302c048084441c82d5443c201c204103009000a4100d0140040316003140c041d10340782c82c081c403c00d2000c7d800d494643d0f000315512a030307418041101c00c01440680014003102000d0100031688450b00960324050314103240c441c1100041e4070400c12800a49125061a4450003800550f0756680b141e600002d01c0e105449080c001c00e04031503e601e00c190300c540036850008041c50030b035180801c0590388094040e10f482c01035110790444071011607072201240782c20780040c0c4610000c0754258814001015007582403055043e040200c540002000460701c40281c07021480d0000c0c059480040c41d0350310005d0001c050341c1d2800380c54020818030506410008070350f032040c0c584840c0e020590300800d030b41f03040c14118a5250894100880e405c10701c01d400441d0030480e54030b01404181e85400000314948001c1d03074403548440c0584030800801210303c000200400d40740c0007401e100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 133475737 1250 133474487 133474489
    0x706050f09061e01090b0f041409100204030b1503010e0f1f050114010c0804050402040602250807030807260d06090209061b12030408070b06240a110f030a110c 70
    0x810700c18005c81e46851340364810046180c680d80f0364940c404000400a006624402504101e07503041520540c040340100403900c0b032000164000c84085030b038002100b00c9641d5980074800250b8004043e080d074595203c0000f001000010496a01c11441c6180906400d58072005101c1401c2d00c107490402031781d402c09004104c6428640c03d51121329200b82046841d0806078a0a9021440b031034000a500c50710100700811016400100810840a036100c4440015407141c0058034407103c0d441000d80c42d0340444006d00c0001c0032603025003061846051460781e10750440e02c440c19841451601141140030100c0c0c4208455039502600d0b0041903410001c52503d80c081021602511481c422150802428480382a454008012000300c1c10001009191a82402c1c54188002d42c01544241c8241100030040360b020710344603100803400001045422041003090b0480c0566400400040c0c003400403003001014600402d01c04184082c607403002a5594204440003c0c1490544c0e0907418159800700d01c441c0c0306 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 133476987 1250 133475737 133475791
    0x4110a080f0601080f0414030310061b0b011a040b0d1e2a050f0f030601020d050a12051504050103061509110301030219170c010e2d01050706050f0906 66
    0x401c850144009480c1c0d540c1c01c0c0a081d01c06420942e00300b6200010401500c8040e2103243c20a0f1122682c41c0c0d20844444071010100c03541c083d50140040d8dc91100401104040c9030b1403100400001040b9820245c2c2c07000f142c01c40390030008001c0d4169459068001007001c0304d02c03124028400c0e6800402072000350301850415100d00031400e0707084444440301403500501500503138032440c80d43e0302030340e03030303c00c62a0301440d16a0000e0760540c2c054801d0b04c0682a0140c01102078546809041d61041d00c40201e00c0071800103040c1c05040e040503400c1c0e4581003109500c940c0103090196003e500b02040d40d803150702440d00c840c01d650f8051081185041c0003c200901c8800c12a4110780d0101c5054642000340d031040214032469510480b0040300300154401c81c103401050120f170b07100f403d032a402e56541c05a018001144002d4038070469121100804903070100880051036031113541850014246111941c0d80c004840060b642c48400700702c8002005640201041156804403108902181d40001030201c501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 133478237 1250 133476987 133476991
    0x40b070c05060a0b010e04090f11120309130e0607020a140109050c040c020f06040c0e0f0621010e011410140607260d02030405010b061603081504110a080f060108 71
    0x55441c0c403030140130301a0703100720311b007808004005104006001480c81c001050001c5000102d03407120703080c00074108500c4c0054180002c407040c80702035840c000d80f0400300009102030010101d09155030300704562158400708009071089080781c00a10101f00c1a04141c00c10402c20b01404410368104508000041c1d00032400d811030210560300442e071008046400d0741080004d5a000d4001e1280d02c0c100410b000342420840101c0d030401162256a45804007400308042080320716981016070910050182c18078821000c0310418850000904119040510b5080d55142080510b0348850001030100300250000f11000801c844401820103114001c0450300600444c14003070014402003200003e50040f02c03a5103009072003100b000d980d940320200c006000941040e981942c00d0342c602481440790742031090865900262a045005d00801076030780c1101c10741c41c0100b0f2100319481000c400a0203455900551048504041c0b500751540d00001c402051074800801c0d0121003240d040a0200e2a40c01804a070303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 133479487 1250 133478237 133478251
    0x170c040504080c06090a0303140708040212010f020c07031401020405180903040f0603020a0f030c0827010501030501020702130203011202090c09030f030c010c090f0605090a0f0e040b070c0506 84
    0x1141a6640c0c2c1480c502c03d00075429618001c0c000d00042055012021901c0c9503e54402c3d202089018130300700d00710000d03900480724000402c000c42e01140262030814800e490001500001040420642e0300c100103981080c04201115071002c0030510801450380b00d034084407542c83c4021814a0310f00390024040d9403d13004c500d403030740d88814041030070800306100303d402600300303c00908155561050001e00030342c0000ca1080000d208180c015075010310034040d80030b83c0e91065540f6010742d00e07006182040844502080c2c00d07102c0c010982e10b6071404c82801480d00841c090380c001615421540180128115500500860240704000521180c4a03414011310306036010b0b6884e285981c3c1d5016a91042e104108c42180d15118903291052510400001046202041c9001b880780f56680103003500c03000c04074052030f14010403078041844000d00c80c0d07020300581c4000609603401c10313a890b1300941c0c200c0f5080d041014807448490801c41444114400c00c0c3c0c1181313061402c0c0b8588003507500d48946486010703241c3c1c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 133480737 1250 133479487 133479491
    0x2061503011e050408130303021506031614040225060e0d0c030f0c02040f05060a0807061d01031509020d0515010e13020d0609060302031005060a151404080309040501170c04 76
    0x2103800d000c03826051b90a451512440307480c001d9200e040107503403913003084070700712417480302d00c001a8283c14082020300015a0080c0f003100c0960800480c0b2144001c10700d5515001982404030a060050040c40705410301450000034030003034002c0c00c000094401c421b4040314260b01141103c3c00c1c99a20440f103645c8180c151400000c030500c8038004813448080e1302000380d4440d0800c0342414034440c40c0d40c031440c06004121401c00103550740310724080e00c0761107030300c264030224a00041480ba900200300da00c00e0620703014580010b202e40ca00342048821b550700e03005014115408184c002d070303921481c070459400460001810300f900081c140002d00d500c4d640744032907000e5604801d0350956441c02e501500d190304c100341000d010064a601b030602c002c280a2000f81d1007440b80c440c1446902c201c40c4201da000700c0000c2c5c00c801002c0d0410001c005040408008902000404001d6905164598000d04040d2503680c000e5661160a80c00b000191f84041e00040d0200c1d00d5104c0600880c2000030b61901c0241007602c3c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 133481987 1250 133480737 133480741
    0x6050a030906050a0e010b04050c1c020c030403051e1203061e1c051b0d0209070905061314150a0e030715053406090503070f0302061503011e05 63
    0x800c4016107503000d0024240341c200020310140e032015400c03d520780030713551008000c5a0304a004000036100290b911584212082040c0030405020a40c0d40702d42d6103052001518154401e5012455680315030303c1501c0307a81044245100702c00780001d1a0301443c40d14802809500c01e603000e05a0544400b601040c031500a0b180c00d08041c543c0da50000b00710300d000404101c800c095007003070311420307603101d4104440c18019541c914486d01404040a00c503108041c042d600000441e50900804800140c19103051000da0381000032196107003c0104400032050364000c088070300d05146542800e0b40b1b1100301c1c1c880e6850b03100c1c01003152044025074048040915001e03800207042400f007810512030781c00c107010689100c09001d82d20f9402c40010300d05203039200141060480f40d04000a80b04c4100c079940184051500050f0340820516003045a4003805601030300d19000095070bc00c00107141800c0100c0244c1c02c80c03020800410b410800c1c940c80c20100790b0090245540040300d901c0c00110b100d541c80b40c26651800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 133483237 1250 133481987 133482007
    0x30e010807120606020304170105010e0c0903070f0609091103070806010e0d0b101406040f030206030a1e0b0102190f02040e160902040e070c0201020c0405070e0406060816030203040c0605 82
    0x4601ca5a0101c2c441c10841d0076104c4100a403294054044c2c800610020000441c01c0f500501c0f61604035200d4402c424859150302001a100b54800c668070340d407502c580f01000c920007848400da10010485921403980441c5095440410380307031400c403040282030b42802005069070b0004821a8000002d28000712482c800400044240000c128003500035101c420802900d1001c413542c45013074030150014105030346065002c0003004e00c980e024418103110550700400060403c0000b541d0050707078119000c14800c00386105040d0850154541044003078640003160090358041c085444442ea20b642206092500b03900d03801048086a10000c0c0074568035980190014424080803401403034602c0b10000455460b42010040d4100d40203040b0f5030500240030076045030048500d4480150f040e0007409904400104020050400801e00c0c000d0203846902d0080070790301d5204100244c0343c41c0c1c850100900340b40c0c15402c210814210b0764003c0c98810018040421400c40c0140122101450300540e01e02040d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 133484487 1250 133483237 133483247
    0xf0f050c1e030d020a03020c010513020307030b09100906020702011701051c1a240d02010c11010c06060623090d0b0702012702031c09180e0a06050612030304030e010807 74
    0x296603280c00c51005c11004034195040d0000e00c03030002c0c080d0091210351071b05a203840c20441150002503150b40035040410029070400d40d4141d120380c6a1041e07404100e0f107000700c40b040c0d8403074480495005600060031411980c0016421810903002e18103c8545c4d81801c0200d03443e015103102c25400c0303145400403002002146412061282170f200f44403001801d10703941d44060314011440d8139001790300c40b0b09221824141039290300d8107150141d4030078a46411684981040d0002041080d042011000c00c04010621500486d40100150741c0c07100d0207e51280202644100100040e02c2d03100320410641e045642c40c40105085e16800c040000401d884511069006007040c0f003172480a007441040d5292072414044000d50b10900070f50588004509061800b40070040040200c00402e4007c403040c03011001604035042060610140000c0000d6882e1001d03290490101003282c1c000c1d1039004211003414050103c904142c01e6a000f5411818a96000340100320841c020b1410010740c80b0011344184d01c10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 133485737 1250 133484487 133484497
    0xd05090d0804060306051c051209040e060408030a0606080910231006030b0103050906010618030203030705030910050a02120f07060510030b06030d08010506070507030507060f0f050c1e03 82
    0x21001c407556855075108040c0c003030061481014401c140c00c1c20700c00d94613401c8404110006902c20040e11070900000d5030f00341580c01111906400030b40e254803014a90408000c524082c90288903101c0d20fa1401000da441502c169400100401204505210342c128002590500c40000ca480204141884401c0d00705c40130100300c0301c40514407100b01407001e076103403880c000425200e580d80c05010b0b1f1701010300190b090f00c0c000c1d5404602c0d540208010042240304020700b4101807116281c040c010359503500003e01d984c01003081658142c000244000540c900800d070030806a0850601c2401d0881880c80030b9111200100080c40d2001c0008110003066045801c550681b0fa0240040201d03007402c008410a8101c940011900740c010080802c4080c5400500362501da1520781d10510140c2c2008103100d032503046018200c1e0a481200c5020000640034004800a401c60303603101d1804604440300242042000c0d1881c0080c000108614204243d000c0f0300248401c442150204140c01c0800ca81442c6200d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 133486987 1250 133485737 133485743
    0xa0302061b03040f0303020106090b011d010e0d080924040905130f0501050916120201030e030f0301062a0305030a0b01120c020a0b061206010303080c09100816030606020d05090d 78
    0x80064007080c41c5821801386401e0728060b9000300702c040d03158840307001101c54201071103000c80d54550190000a1548038054403244040c50301c9203070300030362002143c022582184112810880882c09000314203107a01da000c1004400910441548100c0b41460540e12540c0102044e00f03413203000103200400004070384c01c00e0644c0581c180340c4c034032040e0902074028007050300c20500b070f8041c680e600c011031070441100801f9243d140721a00399007841c960041d030081880444c0c4903c02c1c0001d01056901c40f08510146000304002d849030003201240304081040ba4280030f03004e07068405401140008603a100d4240d0390710424908002810501c0c400c0180d80046240a010454608184040e00d01ca640404c1803410030f8414041007045444060420000c482052528207142d4030031401000031922800440b0b41010002800500d00261071001c62580e0201d0f06211002c03500b528144201c4c20115420a80601c0d4a4501001000d040000003522820b41013041b004201011424040d155503c40410740c030035074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 133488237 1250 133486987 133486993
    0x30c050f0d030603031e02102c0609190b150607050703050705031e0312070c052b110c010f12050a051b0322150e06040c05010e0a0302061b 61
    0x4075030018007811a42c007007100080c41c0402c0035070484144170813041c1075410340d07005041c10f800700c01520002001c104c4003071080d903420f000404240f66500640c0303e00002818014204529002506074544131644400d0034001c900792480e400454800b00740c90381c2000114191741103080c06040040c00a01410401803c02c4c0141c5400100708080055035a0856809501703440700e803540c2101c441441c200751541c002c5560810441a0400c0f040c4184066001b04141001d0940d2030341c40d00c441e840d200c0ea5100340d0642c5501c8170980542c01c0c1c085484c07860302c0802450709409241c100752110b6190242d010f5001e0522003510a101c040c41e0148126402c0c01911060030003851614000c1d4002070181507811b202c146030031040c2e0048144255080302c0c0325135500b005204207403440c140301204803603440c06d05171100c140f400316100000c0c045009004109101500a04090030241003081000310550321031414007052030541c80301912601e9003407085980403079115444003829803030408080002100213103540 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 133489487 1250 133488237 133488253
    0x60405030313030c12031e0c080708031e011212020c040207050105040209010506120f130605041b05062b0603050114010815060904060b04090611040e1b07030c050f 72
    0x40781d01003902140c4c00750303400b00300d9242c0d142440303251090304100c050001902603100208000144084989000c201e1510996031011600c1d540d005811411007114142000018020318050380419404208210f6407903500c1945006d0205250890002c40100700e03299203154030007014024400a01d030940054425543c5510501d0014004d0008640c200e01c0342d40d12400202d05401c1031001d80c0ea4000e545105586681c41da40c040d08003110f0014903038405400e000945000041c540e024a5004a114070500c420406012114a03075521090700501e00602d424400c01d503108134a064003a0b04201421041054a04000d11a81c0074002541000d0300a6090040358100c0a01c10011a4101c80eaa4800c1d42d406a5881c9056207100e1029070b50194040101c1010a0200e0a240d01214450394010400103110001e569404140c528000d820b0070020008074080042510610a15901002a8000340f800d02d21541401e8514003480d40050108401007110b1003c02034204060b54088425404441c50b00c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 133490737 1250 133489487 133489507
    0x150c031403010b070201080c0a08040b0408091003050f060d1113020c01021912060e2d09011d01050907290f180f01091502070b03090708150f01030807020604050303 72
    0x7513880100100c0c00601d406000444c00c59150090b2030503015142da0b482040d46480c2c0300d010b032480019005840b210020000d4030b80b40e987d00c1c40e6024003407406803400b10303e41c82c191400840221004001c1406210b4440c1c070f1000145141e1243daa4004040310540701014005640c03070b0007801003624038040d6620004180e05001000c0030301808403929070b81d45036050200d0080d0182641d1032031043c0305007828000c012030f121241e00007906c0c5105101903c2080c0030418191080ea091384155000c05642e555801c2070b82010051080c0031fa1480c0b0004000c2c80b440c2031400034165100381c00e03c140b030050310b04d40740d00c02ca810038100410300030340100c002010340b00c0348080c1002d5000e5110840c58540402c100951840c2814007100d00e40c0c806c1416110b04001a103000e074940b0020341041c88034000c50103031060211b02c65800a028502a403105001800c00070b09060a503440c04031010b108958024041d02049a08407104009a043d43d600100070f0791036142c1403012030703c0c80c09a0381006616010128140e902 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 133491987 1250 133490737 133490759
    0x7050c01061a041a071203021c0f090c0f1d06030106030b160305060a0302030d030504050c041e050108011e0e12120412081915051f020c01030204150c03140301 70
    0x1034130360711080c0309002c0e01c00c02e40e1100b95100300b0100a02c42c0104040340c1c10b00d00e00940c00740444004030740800300800c0e800c03d400d100300d524040c603626031150f55031110340030b203d14454000080c0c80400c01e4050028103200c41c15032140c6400d000c24070403401e040002981768030290003041c010350340a6000c902508140d9980c042103030200300154004ce00c0c010000b4180d14006240307100f160740240142824110a400850280400800c141e5080c810329001c6090350312244100440e501615242c1000070036582c4116099600c1a84160070b141c0c1090f0001c00c09483c014041e466481c101c60700022504449046181420005000500c1049004c5411076410600301d40861190744240300810fa8580041002d40b0542c1c0181c803608100c0103064402103180100fa031155850410755807218200769500c0d400141c80744100000904910340b03110b002e65003560104100350b02c40354242030660070035042001101340c0d82a9004c02104000c8032400b0001818081c1d0750428000400008441d41c9603120030810345 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 133493237 1250 133491987 133491989
    0xc020304080c1e040203280614040e0c060a02010905031b0d020a050c120a0c1d070804050a0b07050c0d110705030307080327011503060509030c0607050c01061a04 71
    0x2050081c072144070000c0c41d1071010080d2440b400e120f8588241000400d210080d00005e04102d4183c2c402012074070403a0b85c5048078480807581040c00316685023801c1490070420b5a2894080c021400d2592700422564040780040480741c040d0354403a1110f80104040b805040501806003080c0000682c5901c8821144580e00f803524420040f20301401002070200d80c2d41c200202c014110b5044600d00840910708140610720007095034003114201503080e2111900038042c0e80c06a2240a29201d1030390040c4800017032203600203514113100386289030944500351101580f040041c06410007200080520303004800f903c4680d03610301d003216440011100050440041a1036150300d40c819407400180711320b4004100d0f00401d603c031210b642035403a081c1280c1c4a002c0048616a1041c66460f68103200d850248190b143c41d1148d40415800c02d803560030950204d0f5405030030f43e80190400c00c4490410000000c4964101c1d125182a0741d690115514460040c1100d400034008981c80312407140343c01074002d004d08 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 133494487 1250 133493237 133493249
    0x20c03070804060c0b0705031b0c07090509070609050d050a020409061b0e12011107140705061309050115172203021011030405070e06040b180f010b0a0507021903060c020304 76
    0x4481b41ca071600700b5a41404115000401059000d0564009200d010060441c40a02c00219007120340c642c0b9545d02600c03000c5800d080c0c2035101c8803007080515442042200207000a86440ca8500b070280c40702a201c860060020340641c2e141e419281c200f1072940c2c0541400d4400c0d01c0c82d1610b90403002030043c20241c0d59440c0318810b01c3e0000003141010010b00c65200a4031310300300711520300a610399401601d0001944802c031140034281c0d0014223900d62800812603c82c082c2d4000d01598100303d980011030394181c0007064004140c54028501a401c2018000e241c020203c2c070750800d0741c640030103440c2a03602c80c0d142402c443c50540c00c1c400701a00003070095202120f18500307210098505404000e54001150044d0144d4030108040180d01c40912481303030001c4010344040b0b080c5030301c40701103031a07095513650514900310400104040d4000c0e0040e628054135a12403014508005260002d126009441002c0d02c02c14103000110744000842c80d4200040d5803003403044c004814040d0300a5140c0d00984106 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 133495737 1250 133494487 133494503
    0x12050606030d09053003120a0614060301050409020a050406060201092a05120c0d0f030e0306010311040b030a12091a04182c01060906061110020c03070804060c 70
    0x41c1c2d5103003da22181c0130f480c4040d080e81c41c114014040b002e00032401c61007024132001c2d0740052405400051000f0520404040d04100b594204004154100d030080d5004010040781c07a07030016119900c0004890455100301c4000c9145d038100d0001440d120410391101d0ba0080c644840006d0ba142c0640014608074019010100c0c0c2c8000030f20500400382510a241e2400c1d50544024002c0e454411005c81c0345a00c100c04880760b800408000c100c0114901105945103c0c1000c2a801010b502c00e100801804003500904000d51456881603040c4100d500075500c51520741c40400c04c0303a1010081c0c103c00b50f400102015403208421406400f202250045803081400c3c1e08820f03103075541d80400c0b5800c50345050415408034042c0748600d0014030346601c1e020403c2c1a140100480c2d454051401544030200400010f00c103454800110b040341c8043e84210140214141d000380c182c500880c040b0090004c2100242e914515501d1007410b61041c00402092010b01040100341c140d803048009403828425842 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 133496987 1250 133495737 133495753
    0x20f1f0e180406020c0304080712020922060b0102030c10050f0105010f080403030b04110a09061d180601020c0a0902030a0b0405061e0109080703081e120a020307091205060603 77
    0x3480a0811540401c4a001c0003030740201e0300003126940201050200141a00e00b00f580f00c4581c113040030107540c0111100e81000e13400d0029450045c425640110710580102401c1003918410400d5070345450000d01034603900c509950301c50b4000d1048a5202403908245c4180f0000e44890100508040d180c8a102d003011100101d640c0d40202c810150b036541e1078460380744039600c0350b50480c007526400507140c0e00680c50b41c462268143d01d0f9030103404944c1c000d032200e0404034142000201000e44d800040c1c0c41280c100344030300e203041d11a03490103038080440300c41c040400c0d558100141e00e484501d403201c070b0b08488810f0000a28001680c0914010b0381115814001c642a44080000303944058075420740c000f02c6091504043c002c50080c4440c070b00d0701810300410b0a40c0d00ca00140c245030266009492003400020540001200d20a03c521050194a007040c10150070519040c08000300074204040d4590000205000ca40a484601d00404c03c0e840120b0b060280c5240a6844d50f5040c2c0e0858007070301c00d2480e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 133498237 1250 133496987 133496989
    0x203220f050f0102060411030312162705060d0b150d06060903110907020a080307020c180c0a08090a0602071a0f04080f0708070f0f05150c0301050d020f1f0e 69
    0x4002c0c4605005070300404103034485131101d03c64007503000c0300d6a600d48410000407502003001841c591044a5202c089049154915409400320510302405000d90381004c0010a0800e5a840c02c9030a603002940c41c15181c60003149030500811254003040d600c0000404441d05103181c6d04020144031940600c280301d416502c2d00250b8844a4901009254449240401c20182440c10400364080c08500c1141c3e0300c0c4007076407507050440c0d00640395680186c000c400413800c1c506042001c151110707000194202185000c0600b03031994000c203a4203104010ba0701d000708403050030410034081190341105085544012030710300060756060ba440040c20400415000454000740082c03028403a075080b81c032903480d00c103030600d44010300c0c0d2021034221001582488910080f5010603005615144101d603403200e0782503141401482c101e080007144800781114020859045c5a003029241120401d61704544011020320014568002c9085ea0a402c90070174024640342c410b00c1240303130180b81c880e500e500100c002284 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 133499487 1250 133498237 133498249
    0x1406030d03110f0a020c0901030305031f050d060e0a0c08030a0806040c0c02010e0a03150f0605031212070c0f0c0501120608060103080a110714030c0103020309060f04030203220f05 79
    0xb1000c605959051020103403028a180082c00801d00c80c0c810f440000740d010000600900c800e1f00f0607000560080204402110309a004550f03401428168451b45460040056442000382c07000404043c2c60b060b00520b5070004001615505a1181c50f02c852603032035511142d5a80c02a40c1c120300046c0c010703404502e07181004c5c800c035044440070340c1e07034502400711a07001582c031031b02107844190b00080181e0001001c9a084c0700c2400c51290443d4011a4281d00b001017a0190b81d900d410031886508242c581444071900c400882d10078130304c086c18480041d60341d00010386a500c26044081c00c0c20488041c242c040001c007212500c2590005d803104441c4000c2e5407a141304440f40350148400c00d0340102d0040c000b10f0402e401905203042da0340740c103081c45841000d11a088c600303141d20411480d071000c80019074034981403048404104080c0303000c50651500e00744103581c400014002c5540c441140d004101071610920403205060003c56200944080c0d00e225540000c0311840b40308c064030342c0890f000c1030070325142c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 133500737 1250 133499487 133499501
    0x80a05150112090819020309040e19062a03090b090c03030708090d06020703020a0605010518070c02010e060309070602120c0c09100801050403081e0603030f0f0d1406030d03 76
    0x41e034500304030140b0a00003a0040007503d03010f4907003050500000101c0c0301c40d00c1d440d0004807003981c051901c4400030010302096680e1048143e54603040002c05220a050b00454444425000200410040308466000784818209071141e03078002110700480c1802e40c0c040d000304046500c50032515129580e841c440d82c1c0ca8030001e080b501d40c55081000301c1c40120f00b01501501c01c9100080031884c44035410384e200c408036444017008402680260700e03400d0900242d07102d40390041c0000c0c0c1d240201c400a001180c11110b500a02030030510805001010a5900c84d85890340c13190340113080181d69040040c44142e81d6001072203608014850040b0503103001c646001600d00780e05800000380949040c200c10800c0040004001d101c510707440784070026400c00f00340600f500a078080d4036002c104c0d05060301c480c00032151651001c06030030040f0003800341c503850000441d0001c05c0805039003912070200c200c06407181d00c0360900108820707050124003181c00448020b030700d00581003102201c107107401d4094180c1c1a1152 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 133501987 1250 133500737 133500739
    0x90f0c0313030e060c01050405070801090c2c01031103010c0c0c120201121415010203120103080a11010f0e010b1801180609020d24030c031719080a0515 67
    0x1032000c14445820151101c4038244070781000031505601c0004140710350401281218140e44030002d101c180074003480910050414107000740074000d41a1104c4c145102e1509c078108000e8070078143c12842003056811150160304500c044c1c1b1413944e682c00c4c5460090851100907100e54a040c554031112070040d40075100c03495004000000f01d070306d0148803112005000a0a9060201410650070320f1081840713a5a000360030094041c446007445c0b11121030590f00c20b800035040d90310403c00c01c21103400c040112030450350302660f039a50382c030200d100494160140490281556080030400c80d4010926009008040c1040c030080201000640030405001c644900801d501c0f030031600140311307a482000c801c0c4521820b00202240701d9a80303e040d482264010150754200036a80c507156a810802e582c5a20145802d0402c10140b03036003143c0b81c914030000310340310080407076109540340380c03000301c6000540d260300141c00450b92114a41d0320340504140c0e0b00b1240c2003411494800003d99081c841486514a100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 133503237 1250 133501987 133502011
    0x4060e0f03070b01051309020316230102210f041205010c05030105060313020102031209010c091e050423090303070e0904120c0201020a020405070509120c031c140711090f 75
    0x1280c0001e1011001504d07014000f0316480c1d00f00c1c0700c090b0303c007003054003041a2b455100524241c60106029071807030100ca00d00800000c500c1c207412203030385e0000c0c020107181400950000d100c00d2030b40f126038540c40f603018144c0c0c1840002c500011015014121540d601d03004500900c82c900d4940c208450178402400740701d9215000380085070095008100c81068144103004583c9016495200b903126602c0c112104017245e9181d03841c0b200c0280e405900080180b44295030b80d1000742d150b05252003104010300656004641c0d41c2c941107140030400c0061300103034100240701038550900000c429181c1c0c2c001c484040100c1c0e000004a2550305100c2c820a03c00c03500004200c060040100003141e0b200c50641003a8110310609064a0160b07036248601c0c6c3c0100f00603107031103603104c0d03488007440342001c4c0310b0f0f542c40c0c00f80e081549150802d440206405201c0a154a4504c0107854114001d542e1911492251103d410010801004100b2a840032850003802101c0310202c030f0751a55445005214100c881d851444 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 133504487 1250 133503237 133503239
    0x182e05100308030405071d0702100c080106031505090115080c0c0d0e01030f06080304060e0414070503041b1220010c030e0409020306150406060c080306060703030b030604060e0f03070b01 82
    0x31140d40203590424442c1040d600441c0e56180005500d005110f070100000a4000a01c641230380c04200c0c20903e070b1214001400066000900604140414825030051644505022041d001682030b43c4000c1d0074000e08240d01540c46079941c0647c0342402d0309410101d550003020a03142088002581c0510520b000103203c4401310710720450b09000a61600f40c107041d11500034898a003168040c0c040605000001992190301c0c0400051004002c041c1941c00789140c1030b50b0301581d68103100c1e5643d10083c103040c00c40d41ea07140c83c9448070340d18003040c0307600f46003e4080c0c2d00800c03895001e1001c144680e00810145603048102d202021748109a00b5145001c6142d200d040c9000a00400c041a03070002c0080002450081c150042403e14200311010051a0f803410400101c80c82c19203e0100505890320b0101d040715036681d9a031000d0300c000382880f485040c02103141406c00d4443d411512401d0b41c090305540c80390519142c4040035062440401046005074601521000400019a001950400f50388901030b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 133505737 1250 133504487 133504493
    0x4031505160507082704020705010906051008070b0c0a020604030b1006111903020c0301020706021b030f0406030b0406120b06012d1112030c040e06090f040209182e051003 75
    0x10b03005e0255550078083c04c2c02102800d0381e9910207849410301034000400c10140710316010080b641c004215101c0a5194001445054070000300107003a507450844465039003100c440d61b14a03102810308020350080d8002400300c00c2144042042d4064088003405a180d5500e4100503684501c0aa00c140c4003a48540781c604900c2c503d100600b54005c2c068015035500c4030440d4007203820ba031301150090f61441d40001e10700384a843c2c0c4084900640c0c0701040030303508080030140401c2c0b0a00c101d110b008109901c80401e1011503947c0e5010b80c1c0209400c4074840710403c0c1d94a408101c4107411100301d40454034548400110000400b010b180d07402000081020201440200380c400031720010340d1015610070303d2028400010030030019801091810140e40e02e8600e08880d4041d010402490342c1e006509440c03d020042c20120f900e2074000e81d0440307050000303554061202c2e41108405204029a00c40c94080e52100040300c80c1198070744031000580a104c4070035001100a03180c1c19031301000c03071a40c04800bc1000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 133506987 1250 133505737 133505767
    0x305280308061e04020408030a020601090209060306091905010f1d040b0105060d1d070302030f0c0f01032301090b040605040e03192106090b09071d04020403150516050708 75
    0x1030512038141020f40480001c02040032a00325800400042c0e00020302c28603042d0301040300a00400f1544401e43c9002c28a07404160b0a000240100b8014090840825401440b181d009a840b160002d402c222a6940340c104076049802386c1304210080012050742c04480c006001440c3c401ca0704080f0600581e46000d083c40b01c150700001094105a9a83d102c80c6583d00214140c4032491500b440201030160550041504010300d01986000d01c2d40300724101002a190184080396884003400c000a80038108510700d0202c0303ca45200c10810500c070070004c00d90300e6981e4000410744409490400091b40c4840a00007107460f02078640c03c6560060013041c40d40840c1c030201d8140e4002612706040041c5594a01a080101d2000d00c07034407580d10380f0001d00c40780c0c0b100d2050301c08036003040703402e080c035800e140302e000e002d030f005a401c214113018000024000584036a0110741c001c690080c0824555142074902600420f415503c03003100000c0742024180003882802585e1410b5000071000c0e18045280f210b141c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 133508237 1250 133506987 133507009
    0x513120f0308090a0501140601090b0316050f122a0c12030a06050904030203040602100c050304020f040e030409020418090302030f03060103060e04060207060c05040b09060f1201030528030806 84
    0x90f9480307184640b07000a10207000d210002e001c1d1208494440c18400009042d50007950040c2c4e24041c41442082901046140d00380f1070030038142402c50380c544841d04414450b200c7e207200030806a4482d030500051070300d41503020280015000c00d43d1103880eaa88080d15544c400d081d494607440e8400b80d800005540d00e8001503400c400b1041c0f0006040d5550804030310212821117040c0c0c09600301190800080f50140310042062540c404104013440c0c014001400c03602010740040e00943d000ba410704519122a40182004004041100d89980d41d440005000c1c2d4460b000c1d0b514090b208492041445070540031b150b00341503064015505110b111940c164054200500b00c60415440d224001403c850301031285001328069540035980e016182044815280403000c2d0314200017003000b0400c0604223400c01e8803003600c1c0031590942c4d1341c40c0da6480e011090107100358441a20340700350000000c02c40c000a040300c003501e0140001c01100803480d43c40000400c883d0014000c11604c00000d2001d14001c1400c0c0c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 133509487 1250 133508237 133508251
    0x3030d05060d14031b0c1005070c0b030a090201090503070608071206050603070c0515040510020c010609060b0a18050a1403031c0510080a02102307030513120f0308 72
    0x1207030a200503200c09201ca442c5050b0740c0300303c4d000002e20300303490780140c40070b684013200c920000c1200c03c450801040907013041c854003d0801030080b40080800c03004001c004000c25980443d980c03a070601215502c004c11104204a001c21080c90000515041c089070400c21030b081925840800e9680100945180709240c2a694441c1c2e500c03140494240c0d46c52000e14000d1503290f8803240c545440c0e1414078a84180c076410000c1c03c550782c40030040040c100007840c40c0f000174034a4000d03803a10b119841c16070150941d50020180503003401300c04100d1044100260805000554400c2078800b9060500181080c2900035650401200007003030000c3c14440780c0c07030480440c019040364640415403580312801c4001388400c01ca40398a078010f00407080310000d4484050300a603400b60018441507400102c1840a4400107000c1c045011400b40442032903060b0346482c41c10b20a9030b29511100e03450b00070100c4c0d20400e1198102d401415010070b40e0991440448907469022000c440002460303101500d100400034614 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 133510737 1250 133509487 133509499
    0x1908040905070c050d0f03050f25020a05120309060c030c030103171c05091b06090d0f020916030606080103120c060b0d0503030414010b010f030b0a0504020406022a03030d0506 77
    0x10f0009042013246006028035aa0b81680094080000805680014200e03408400031a420701038151001803d0090046403100c2481c00026000310a81c101010341c0c00281450041404020b0500080340c0203600c2408440c040c1c403070300d568185038814a070006460584d866a030074001480054280001c2e21550041d51700d900303040030405039141358150900400b260100d6142c4040c0405007008000d1a488140c103402100411401040460b20750b0140c200024454507910002000f0f002c201007030402c0103034024041c1555032400020800508100d440e003040007070720303012001032154070881c0500e06070f9500c0307108c001c0d812101c424201c17984c14074035200b80c540b195a4003003898141d0360011101c0c8294444d4000d10380f41c0c50304dc00e0041c0036207402c90924015074140801c0300d0b220b030707400b00c01d003101700350349003000280f802e0b001001c070724107150350f40050307030001e10000700403030001e80005500c140081d0341c0f15912120703028014107840320003005910942650090006103808542c2d41c015660104001e010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 133511987 1250 133510737 133510757
    0x7020103110307020a0302070b03060f06030a0204080f062d0c130915230609150702130209120c090c160f0303020c0610030b06060c01020d0606020708190804090507 72
    0x140754000d600a603865000759005107007010805030140141001861506a4581546404070201e082d0341205d00c0c0c40c1d032045400000051041110350f06a4000d018500c007103803209020390f540b8a03581c91040d960403c400038142901444c00e207400581040d2300034401703602100ca4940642c88a40790300490030320b400c0726641c201c0114440100c4d2113200494441d510415601c1840d000214034001909803034140a5404900c0c41038207604c2c1c000440d14001e4090310b400c180d41c10051680d04181c003a8542c000c2d030248120f00400121120741e005440d80307400c111205201134841c1000c45079140c100c00780143d040600d0000103641440c214000d041d44060b0000b0f441c0c812000e0f80e0381c0081d500310060080340802c0e801305050714909401c00480e0391002204054509942c110303100d0051703c0d10000c14180c86030380002744801c6070150039015204062012502405810b4540e03030065158290342c06403905500c1081840801d048a070101c00c5411030708070320703001d00c0e041c24211014041d100092000040c0040041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 133513237 1250 133511987 133512011
    0x504020c100c0504091d0307020d0c0308220e060f0906010c080c0706020d0f02120d0207020d05070501080601031503060506060c030f0913091e1110032004060f0507020103 75
    0x68035802d07240c5542d2143d855040040070300440d100300d8400c107a180344400c0c0d04185507000004a9000d40d80454219003400c0720752400900030302c556003004200d0321020505002c484a204074148092800c51b109101d1542c171145140b07041e4204a80d1036600c0440b03c50520400c3c100b0700030302900000d040c500b80d0117400d030342e07141c82c181980701000d0304443c2c2e4003250303041040d0741e414090313800c1c0d841051400900025140c10025644c489099000c8000301c80000c44020058003035040b500525400703031299000a4680c10000d0b2642c0c5030340b07d00c07801b00b4490f0000403d690320a2050070841c841d03068000b009181180c580c1c90003000002c0803143c01400400518265800400160a078200001c51141e5281340000502c00e0f10201a502c4281480c00c0524107000100441140480f071907000080224903c11410311858403000251455002210940b090000c2039241e040300441111244100c080c599294910709014032441c407400300000da44d42d1308650705910501c02049a00d005250205440744514 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 133514487 1250 133513237 133513241
    0x105220506070f050c0a1d09100c1707022107050111070506070f05040e010b22060c0c0b031501110a05031908060409080a0c02041107061d0c0a0504020c10 68
    0x704003510042820001c2604102c0304100380d005e00386090320398916041c030b0500d41000305214070410904044c01e001c00100480c200300024420b5880c0907505000e039164045015000300715010720003000c0c65840c00001d000c24000035212425105034041da00d000070901d008086550080e11046070655201c6c01410080700300170001d02152030041010f0314581c200000050051001d04482c030091003c20310082082c81019455141101c0c46034041039034802c500c480006c1740404845180071a0950f03141d020131002d904c01e205105030f501c02c601c01408151643c0007045a40030031140f02503481c4d500740d01c2500f00e510541d1103100304641e18080303504910440c0d440604580200c424046048070030380300400e10329401140f294024030151400c2012080c1d41c0c981708814820321946005001440c00c0c0c010071501d50b54400b070031800148000719140d40207403410030060400b0940b540c00c2d042c0c5800e107000c0e0f2860049250600d0000080020030102c0c601401d04c0040d40016081420f40d0007403041c4840709840b24 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 133515737 1250 133514487 133514497
    0x10e0a0e07050408070f0302180702011401090501060207080307020f040b06070609051b06032703071709030c100503060d020a050607120813020307050909011b1d0f0105220506 77
    0x40c1c030b4040c0c40f14100054149440a140d005a04000c0d840340d007080580c0ba560300928101c10103009200c2e550f07940c05030680c050181c1c0c0010b6216800c2d007400001e010021680032605803007803503003a99a02556003440d599a40034a940123540480c6441909180b071405500c42d060300a0041d00007030901c02203032210011202116016542d903046201200402c504e02013440100172400c44802e800c40c2001411060400190151003914000d507280c0b1b0a000d032400c0045d107405a5000d14102960000800384a04035004a0f00b101d00a11491080c890a0314090060384c01062aa03a2001d003550750780020007103000e14140059030032840d0550003080c00d0315014000e006440c000e0000900d01310444030014a0094003d00c42d01c00300c6030342100140140c0e070202d60001242c008454141a9803a403101c45030061009800392404402080c00440c0c0542d000414240b0100e05104840d49015841062044013000e400e101030024000700001a028241c40009403901c5500350101d80001c2d40350404203500d43e00c6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 133516987 1250 133515737 133515751
    0x3060c07060c091214030c01020f040e0f01030302060a0f020d0e01050601021608100203191b0e0301060f150905030f0114090a0807080c010b09010b040306050a0c0e010e0a0e 76
    0x1001441a00740445070040c0c18142c1001c2c60014681807501c81d07603044070004864000d001420b01c402501071076008106564800d54640002c566800003961141c2441d0b003c0c0c4107000360b1058180000743c4102c24184c03524107e9425402900c82e13a074913501d100c030043c0024a240e44400e50300348034202100d04e40d8400c1001244101c400001c0c54184400003903e070480c1a4407882400c2c804400070301c003608010038a002a881c00300d41c05a02c9440c0d6030b2042082c0c401c18600071080d14034221011580a448105508180c10151030b1082c0b80b0383c240080c5802c0e1625030050764004000c42c582005080d40c161954101c444640c80c100d80040c0e102c4c40001d00b40f09000e4007a0301c00d69100d007160881101c10140003604801c010006240065695682d44803900070000080c09904020542c00181e00d402e41201500c04070003001000f03291b07105c04ca841610b4210340000d07545146840e0009041504601c0355404403e01070f202c01d03189807040001141c204015000d42e40d0080301145002034042d294030060307406507230 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 133518237 1250 133516987 133517011
    0xd0f090810020a02100903051b0a02040f05061c03090314030903010e0106050a0816030327060804060b090402090105100c1703070e01090f09020708040503190203010606090501020c0402180306 84
    0x268440f4000e00c1d0180002c0740d0b00c203036442c01c41c0b4180002c1c0c03c401110405240c0d00351440c0c80ea0b03000091282441d4031004041d40150800c155800058682d5001c9407059400b1504640841703803c552081c0801d002803001808a0740c4400c05201265140300c05d800c1c5034003805d0440345043d008401207425540b81d02c54061440c0e44541082c840d501e00400c41301d010780700c0c80c0c00420600004155120520600303101c080c0920070a10002e031644e40080d8041a401a4803c2003c100181e48847c010404141100e09440e041e2400740100802d2030082e500c240541e800a01084899007840c080105219100705c101c014480c4d1040490006281004590386c00d400000762191285003090000d4081450b0008443c104132103080305100750b803242020303001590013001c3c006844203900e2400b081c5d103216030b800160341840740c1c1e60341600c1e10040e20384c450720aa2090b0000d01005a60b10400c0e155104503006250160704840184e142e07500307080e070242c407043c50084007603030843c1c1441c0d0101e030400d1026146030082c0e00c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 133519487 1250 133518237 133518247
    0x30b040f02041b02010605010f17090f07060210060e011401030b01052101050f03060408040e09030f1801140301081905030d060609090e0705060a120902130914010b030d0f09081002 79
    0x11380a00c2040002c0c4400e0900f03681c1071044410007011004500782c0c1c1d141c400c1075840407420000c2c00b00444664840104110340007a5205c007030186d62a074080341c038401224100b0001055040300442c606040f41c031a040000355480040c00150702500d4400c81080c1040014459011003444150f40340484111940c80c40f0455410803082c801c003407490148450082d40014248800611800708803022169130055100090b120b0f007e6103070940c801d0706a07900e80748101082801b8003034020302002d048114240c0b55500904843d0950f940b040c0024800d111550b0030203040700d0301810020500809561148003034074940452048180110b52064101000041c003000e82032241c00d84503c20b015061070f0941c014500145444000760705442211800317402c00031080b120003050b04103a00041400c03030b0700600300c145051942c4600401012a05020f452524484c0080000c83c0018802c0b04043c180c003602074051420003050a85a11460301442d404110091600103402c8205111008503055021000340e954 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 133520737 1250 133519487 133519541
    0x2040b120901020f0304021504080703081804061415130f03031103030f04030f0c1731050411130909060e010b0a030b0a020408031303060509060709030b040f0204 71
    0x40003003207501d6580c4104007038259400d80b1302c2075075401941242c90400b030b1000d0710030058090041d40e0184900f0311400c8004001c012061000d00300c80407203140d0558140a00c0343c20803080e140340d8881d6000350070044000300c00e503007019180e5503014801050110324000181951360042407031940b02d02000e41140f4000e10425034002840a50400040300450039414080e64002a078a0013030b0004043c08054018002c09600403100c07181c80c0b079005040d80b4502c03181140b241016038803881300740a0211502d81c00c0302080380900c5013001c00682961940a0060038101400000d1034171021078046c902c010f21140d2014000c00707100304080e06d5240303400303d086119403030100182c0d055500603002903410b004e11240142c40e0460070b40116900520044801c0c2c41c0c82200d03900034401e82d003014515000002c0c00e08081e20303500211100702c0b4412041000a95a01040652140c1d415504a40024000c0b1400c0002c590304c60036050b040b900800010078040201d5000400325041c0c1c0146904911410f4152401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 133521987 1250 133520737 133520767
    0x915020301090c1e05091804050a12020d02030d0e0102070f060b040506090408091e0411031b0a0912020f04020301031416080a0f0c03020d03020a110402040302102102040b 75
    0x120031103810b00c40f8148140e048040708210b64181034131304200740803405200035038481012135a0070f051f41a5442280c01c050a025031100c6604d101503404400461509904502c0040c91300d5042c011540503504020340790164601031301c9060f014400175034007481100301140200a4422203140b150a00040000b4490144803e0b640024600c604c900881d034200400f1507002802c560000320121684240c0c0f004964051b10303148034000207250050716140c241d9100803203800003907002d2941e41107284400f0030041940d811502c5080101d50002c0c0040800708402ca407592640c1c1942032008100b02115581e2901040c200c0e00300340d0041c0d458040320b4505031071062041c048400b00000f072503a5a50b509007001c0c0c0e5595a0822007000401e03c050003030780c4000303005125140034081c5600410300d2610460a050095541200d541c055580d8030501909139070500e882c2c0b08a800b00e0358042e04540184a0341241a1403600c400c142d0420749079000b00c0d2074110308c00c60348028000744c586018800c2e1554510b80041e81 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 133523237 1250 133521987 133522001
    0x71808030f04121416061205060a0509181b190302011d0d05150402011d0a030b04140706021b04291305090303060913030807080604091502030109 64
    0x2090381041101d40d52900994007102e081d18000480200b45400c01c0c42d01004000700000922510b0003030315444140c0c00d048a000310126829079440521600000010404860b02030702c21070352004c1280030400c07581c00c102e421250300c402c0c1884020020300d005002c4505110f00410100c421014444100d21607140100341c00b003d000391107202180180c00c650020308100a840306d6000b109400d0002502503545818450f03e4555004060350140340b4142d01c05048400140c4040780403650802002d84281c2082d0b41c0e1070f082d40d100034081046603207181c980c282c100e0070261058030300311000140031840b5103041103801c0007000d841d401007840c1210303403140b80141965508914800c50404204512034140c940c003091060b1425100030f04d1600300d00300000c0005001c100c0030b00f40241401d041190180f00440035600c1004151440411039840d8150341e40b000c807060900401141c06900400d8280b445103c102e40c0c0000c01a00008105000d80c03070341103940c40710114a4020035000001030018100c603000b590 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 133524487 1250 133523237 133523249
    0x3160c050a0302071a030405070e0901091b05090609090316030905031f0f0b0a0902090a05030d080901060501050a0503041506050d2103020306031203071209060e0714030d0c0203070e0718 82
    0x142541021b230760701d90300d5200a11030412203001c21000705000f0102917003d4840c150307101c6000342c0340200030040c0d62250181c901c0723001d200d9182400003401508242c104a44550346076070255103170620043c000c0302d014080c02416420051124070100d0103407802c10510f6040605942c030f945803050301e8081c0c41e0607560038017807124480741410002412500c6039100b800a50310088405612240d03801c01041000e9101e50200354984207a42c04500c0b8244c00180807802685204024001039480b0740054509210b420051000140100005008159401d0159541c0c200b83c0001181c129940d0740013030340d010b11925081d074542e601001280f4804212448414024605080943c218500310700042c3d250301740386000005102000001414541c80382d84046580c181d4150204503080c3d0b01d0030803034000e2030b200f84010054818808003017081288060b0341400150300600030a0810051201182d0300c40203c00200c0c0c040c8210348010503a020b00b0001d441c030964095560000c403101520b140010440c46074002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 133525737 1250 133524487 133524539
    0x81b01030b0d03120f0c0807031a0904060b03160824090303012601110403120e0a09020702040908030411010f0801030804030b061207060e03010c0305060603160c050a030207 76
    0x100c00d0a07114505401034041e0141444640305684d8003c5901406680c212244000d01c0d19011025042c1c1100d803c50188045a4003009114140c0c80b210065003030700002258040c03c482c000500080c140d80000e084940047d00b542d450f4451541110404809900100103e40128401c01c10020269000c02c0488000310810035081c102510441e4807440113000d0880600540c420403c00300508080c180089038540e0000c115000c1c0c0d844c1c3e01040da80140c00100d43e491038948084035804d20441c1014184800146640006454001c41100130741c80440200d811944940000000c141e00c0b1001d1403103070b03008407100884440748000041551100501d49824405048010700100301da400070f070f03800d80c0d500249900487d1034410004d4403000100305440e45034841c051001c10b54690140b014003c8050583c002d201c03216043c03100740c06840c0100e645c0798000f2001d00028404c003006e10782c121490026802c207040f036503070170740c0300c080c14490003d5083d000740e404081c0800c4400c0500d01c07010042c110400039 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 133526987 1250 133525737 133525751
    0xb0f0705010507053c090a030b07020d0f02011406120a050102220b03040f0204090314070302071502071a030714030a06080601120f02010e0f061c0b01050f0a0c0807020a081b0103 78
    0x3001d20f02d880c1e12914201c0803507020400c06c90645909807107101030f58001c00c02c003040c4d260246009503100085c4d29108000f50102c0d24440c400d0380140640e01c035100a0900da89541d42e205001e2080c40046000100c040d0710452201c1c4020920030b100800b044a1003402b888181d2031001d8041d00040166445a0b103403190402c1003001040b400c01ca00ca601070341c102c2d07000c07444410b182811a90031901400320b016080b8001615000c05800141003011110005e00c03000c01200610b50990f00d070306442c40f4040825003441c07d58001d1880383c800850340301e000350031f107040242c91b540d0070440d182c0c0003102c060241555485080c000c4650400030b007030040051310030b0b1000e07164460340d07503803002d007c48800281070160302c0c10310400d156216036100250600240c07580792120820040f110140310101c0c501617040d0324002440010b544200c0880c0c5000e44a410054039140070302c3d20888030321a00840a4808040034810140140d0300c0c0540c0300001e14022004003401134181c010341164500e01000d080c1803500d0004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 133528237 1250 133526987 133527067
    0x100c050306030d17040609230c180105060a1119031107080307080d0504020f060c01020703030e0309030604080c010e010f090b150a140f03010c0f1205100b0f070501050705 75
    0x42079109902c06c20110311540613203050f15400440d1003503658660300c4454261981500000c00042e1000221200030724604050003000100c42c0c02e00409401030030400075254a079018201141c00d40591004803144001c09089200303a1540b6518100c0000300d00170140d00090804200d59000380c400003014615081443c1d40700801d6100e0f0350104544c844d11500000c065580d94400c0021001c0c0c098070f160b40d0341f0f200b0b03a03100b4000e600510089010030300d04142c1c2105510000280e0f041c0c01c81c00b038001c20382920385450f140081c0d040000c4a02c050364030382031003010f02c01003801880f486100503800440d0f07545080c58101c0390004001c1c5058610240c0b040e007482c96682e19003001040b90702140c6c1801c180d82c071140208866045203055190103600382400c0014150307010b00100c1818100c0c1d66501c84290241e61910300380c7d0340545070000d03504550b24051000c0318a4a0042c0304103a0201d540314905401962074500f902d5040b00c03008081035000c100907d43c45091219503441c050202000c0b03a401030300754 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 133529487 1250 133528237 133528277
    0x21f0908070e04020306070513120f05070611010e0304050607020103151e09060501020c030a1202070308030f151507170d0c1205070e010801030807060b0d1203110301030f021002100c050306030d 85
    0xc411140a8201c040ac58800d00c094100502c0c00207801c20199401640c681c0300140c405908120f49803859886d01c1513402203168007000352030540e88010100c1c0c1c6005601e40045003d00225032aa4010300300315580050020b44041482c1080d400c40c03024044c00070307d04161001140c541c1c4e4005030654018070840c52840d0303404190381981d2944071034450380c07070758650000b2403030030480b034200070300c60074000090105182c944100c9900c1010411410109801c0b400144043c0704022100701551b54018801407001812408540034401000041503080c11415842e10301995000c48861010034905010340000c034940303008056102900781006221030000000003004200140300c041d1100300d000c0340301c0042040710f4001c420102e400034003d09009800d42003c810203080c0400540200b8501030100300a01e880c00280c9040f0b0b500001203107044101ca80070302c410b00da0300030a26000c5004607000b0a103040c51500c2112500a05959429120314290040c9481c0400e0940440d040c007600204104640c2086 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 133530737 1250 133529487 133529489
    0x4060b1309020301051e0a0f1e0f110a0c0f030507020d0b07030b01051606020f09040213140d020f010815090108070806010e090c12030d02030f0402091003021f0908070e04020306070513 81
    0x2c1440008c0c07403101510004002c00300e80b000c0740c2668070b110000d0b50307003609079400c82580d0340c00c10441040007001d218001426481404004008540c40104003008284180d103c521313147d00a0034205d240126a500082001c1d110740009c4448160200600c05100da0520860015030802c2c00c1513072400c107040701d0450204407184001006107800042c0c4a0320520404103403206081c01800a5447e07d4009082e441041c4039405140021450426014a00d107000300b40710141c030750098a20392441c800d02004440c2e0b180c006120b00d100c5c0316448401e22082d150b42031424000c1c180c0201403d8024105040541004010790050030b005e03100400340f051901d4041403020311524215117406011090740100750035070107800c0410074494070100800001b2841c20307003001d214900c00c0f51416466541c845540b84070310300f27600000c0d4010a6050500c54501400c2c802414180c1c01402c0c200000b50391482c1440c6089a550041c2d0110031000c4144021400d00700042500f0407001d00b041800c0000740d06d0010202203031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 133531987 1250 133530737 133530751
    0xf030c031911032412030c0607020604032a0c0806010501030c020303060603060d1502070b060a06020d0e0105090a170c090c04140d021503090d020709020901090e04060b1309020301051e 81
    0x100c040300c1c2130219060005884405800b41100700b1032498013882c65100e810241880b20300340240d0700003d452510205901c0e21a6515441e64007212131121381814010500070500011041402e0300d020108a030303144900c0c010800c1d50010a103540c100800102030f10520b106102c2903500500610a0a982c1c0304203aa0b44070500b662141021800c5003014241060500c0750b00e41c085d48001010381c1440203001c81544a003c0c2919101983c036031740c901c200c0c0c0e40d003a4040300e1400188116240c021561180d0004d1502034401406621a55191590a0300946040d140c0641550002900d03482030b0504001507a401f503c04800117041a1806010205580702e1100b00e078480d030b04e0030140504550700d00000341a00030380b00c040d1607102e2a00060282daa180c1012900015103d00b50000030303260060b0089400c000410b0f91060780b46403904100f00d40d421800f40c400c07a2800e81350201c08815850b0b88040a080c00d003007070b00110761072041740141801c648014005410a070050340c6007165466040e610b07030b038100340 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 133533237 1250 133531987 133532011
    0x906070f02030109021306090b0909060a1d0f010204050415030206160f0b150f040204060905042f121609030b0a0608061915050a0b0705030f030c03191103 68
    0x10041c4000703801801c0881d0025440040000f0541c406101da600c0481925a01502000300d04800c40c2000384001d0101c4002d0480ea1050000584008941d0402e0409a00d200000d0421200c500c00c0c0c60b08201246034090034036075000c20100568640384c094810f8410384207149441260550300854510320810402d81d1f0704900b100710034010070915543c0b100c070180d08500b070300c441410301d04512504071748a0300031079100b10980e401044091a00e17100b1a011500c0544842c98040e1410041c4400703040545d500040d00c442c0f03917481d00c01036001008803640200403091000d5690449100c2c4500d00c0c00d004c0d020b01e4141005510a8170203a8102440c203050382c0d00440c20310400d68030604000054041038000003810300a21081c0035940c003886108458a11480b4801c1c8070384080c1d501c0360303138014000e03219550344a10070200402c82c0900c80da0081140303d014906592909031103180c0c800540d8800c0da0000c0418800004106072f0000b103c429081d8440a10424040755a501d41d5058880c00080c0014410341 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 133534487 1250 133533237 133533263
    0x6120f050601090e0c04050904060615020105090615030c0303030106021c0201060503030d0b040b1801090e0a0506070f0504080d0503040c060203131715011203081303020a0f030516050d14090607 85
    0x1c03546002e0741e00600380140b01500900c0c1c6403818ae009000c161080300f0806030b600184155050060149503c9043d10300014022680d032a0540d038901a80c0c1640c3c82c2d00760003680b03d2241c10351000d200a5010341b10070b800a02541c80025074242d150b200d00c040d0030045915243d03083c01030340c0d0017100320741d144102a400072501d101150700060041c40380004d8184d0045262041401c03505800f01042d040340c0007010100b000c11105d40030640c446030403820082441d004080002d002c9c07409900f0845ca880700b14540300d400e00741c039a141c4514004040809402143c00030081004002c004112a009440f4901c084c40c10a850801180e070511400d01441c0c034040d01128003084901d20412012401c2130400b444a0081c0d6500e0114030040c6c01078020580001d1452400100301c00245140305802ca40d150380203000118864403602a440c00c0d0305000c408110b0104583c200d400d0000c0245000b49004070043e2400c481c801101030408025880400200740d03040c0b0041402d40d6840c810390701c031036420034007100c100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 133535737 1250 133534487 133534501
    0x40f020306220320010212060301060f0509010e04050a02130e07050d211803031d0306101a04030c06050307020f1209060c01020c031c0b030102042403110406120f050601090e 76
    0x1a40c241c0e560b603c4c0a602c085441804009500e4029018142c20780082101c1512200850740040d800e00455420400980c0108102c401c2120101c0c2d1042c010002d444003000150300150391100c82c60311030150301d9101c106c5080e68103070a005400050000f160f02c6808900c00c0da5844098100d0a00740d5141000c000d40e907040c25038003030381c0c241d034900200c003d41008260b103a141c0030b00400d001b0007949450110744012441103041c00a60035000703c0b820700a03080e1052900340c84203101d40d801c2d8080701034640107202c004001401541c0b22005071205880e41600d0303182110340246401e240c4c2558054a83c0107100214503441c80034200c4055500030380d1410750b0307007c10485a50182c41503002e61143c9200001d04003103034015041c801d0300c030046110001c2c404a095002014242d004d1406400301c0402c400d8040000d03000e104200e1080e412990074003084954401c070300c851b0a074100b5840500071644140800d0b18032403051080540880c3d8540c800c0200d8246080020801d030040d002e8600c0250f0301501007401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 133536987 1250 133535737 133535777
    0x6010215070302180f011b080705150a05094909080f07050901060806130507080601090f0b03010605030702030d0608070f09050f0411040b040203040f0203062203 71
    0x500c04601880c2818060401402075001d10005400082e0041e0b091684e890154001c54540030141c0d80c6c2c1d205180191083c04400c080d14500300c480100400c114000100c09200b8a20202041c20174010305d0b18020814005880004101c02025082400c42a200201040d240e5503601155602c21085100c3d003c00442180d000c05451450300d00450864164260302c021604240c0d0469029a40002050005207680b2000f43c040c45d0b91040600e001402003901c05e11039241d001c00000c000509550b01d20700b100c02119000c0d280d4100094410082003480d507003040f035440c02001111300c50021a8a03000340c02c09a4041800f44c03208114001021840c00d80c405c000f6600a001f0803407041000c17565803d08039581d100d0701e00c2006030040c3c0c1c002001801c102c140c0b00300307480390031501c1d110300c401e50f1181e861040702d40010240a42c003d42c1d03828820802c0c0c0b170704d201840c4901d10540310380d103100341c1d42e004051802c00000c00c04404082449403464442c43c4001c6200c41080e03240c05e104da1500080c1c00c014030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 133538237 1250 133536987 133537003
    0x909150105120a051e19050c090415050427080702030f070b04090c1b0312020c0a0b010e06060304030c080703030b180a05071b0f05010b0a08070603060e15010305060102 74
    0x40340036110300602681e400c2d182e01c018041c81c0000f040401c2000c0c0000c0150038030748206c958280b46415000240062141d80d000298888106061107182c0101c0c200014101c50400120a083c1440d00206116905040c40358918955046010721460015096226500341c1c0c00b410041109601050b01001c5440400c0452110740340101a00c1070941c80c1c2c04550150340080c4500030740c80b804d0003050b05150340508c0b40c0b200445401c90b218202c0d40801e460a6801c0c80c3c007518142e900550800c05000114006d100f10f0281d184201c090506a500d0003240a034011001303801c841c415403080061000090f000400300f4800e640c050481d035142c590605080e401400040c0c080307600005130703a1011002c60303b8214828841c0300e141c0c1c401c00c6140c881c244211041d1912409001701d10403e00300170b00c0410103030561402c001d0300c268008120310030300d840440e5407548150703c20a996882007406001c1e0540600484009d0008804c000700b485c5801c0c02c0500740716900004040c145544c42c001316200b41d02c2480300c1c032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 133539487 1250 133538237 133538257
    0x60e0d020d020d0b09030315010906090e04020d12050c0f06150118030f0f050f011406041a0415060207120c0e090a021810060915030213031a0a0c03020909150105 71
    0x122480c901511500d81b0b95104490000203070403d42559071180d8041c004043c192010f5a88101c84582040c996010135003000d00142d90106030307402d070400051070114518100c48055550280c507078920b04070786494080d56090380c0103150042401c11005440c0f000030321511710024039110f600d00c03005004103041030f05580c0000d81a801030003000f10a1200e0089002c040e2071040044440481e901035a17103080360002200c40c02c0366065040030803181d00e0150444d2808000101019251942c1d460000e0200c07040c0c00c110914400d4407400400c0807a0301404003000400c02410000c018a04554a413070403c5c900e4011103801c0400100410380035401008505111507010b00160400c1c00040d0005030324000860b041d030505c0e0b4080b0000309880703128006100c1152003504000090310219007065020750080c12402080d0803c20034000081840e00448901106c04408070090904000005030280d070100c9040206240c0104200c00890f102c180c600c640c82407000400540004c042d1004036074030f200e0718000d4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 133540737 1250 133539487 133539503
    0x40c060e150a0e2403010302010816140d1805060703050f010e0118020c0d080f0603030c060a02250f05010b040902010219020307120605060901090e330103030e0901060e0d020d020d 79
    0x3c0c4462500c4c1100850599000762201e03900c0d40d0714000414090b110144104000451160442c01c40010311409009241134445000c81c0c01050b1990320340140401d21710540e0658094800c0c030100541501c11280c12041e003080112056060804011242c807061007030386412540c0016241f080255070341075076203000740c64040d903000d502c8050340140b0003041652010182d41c024000f207003007031600104483c134040855018041ea65500c03074000000303401c151b0f8501403c0200a019481038030102d121043c2140c8102d1148102e4590381c10801d086601d03041c4a540200e250903060b0002d80c1e000100003000e0f070405448088015551b202003410003445603c0303a500403040c0507014003041100d40000c0d10600041e26a200141c4c0d0b0740e003410090300c11180d8a020242c0040680f440d100c1c1440c0101d200b107042104c4c806003100030b500200e1103000c500b6401500021610041d0010310b00c0e00481c00c1d80100705915000502c40145000120542c003a0200207128907c41c1da409001c54070f036102000c00058008100c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 133541987 1250 133540737 133540789
    0xf08040611030f06040605031c18030203010c05031005030d121d010203070e0f060f09100302071e0b0601021f0213030804030c1805100312030f05040c060e150a0e 71
    0x441d40a54056900c03600c298201b6401059600b0001415111422001804600b1000301c5806441b580900721400b442060b21030408405a1424010803410196039a903090f600e140c400344001c82c500507038000500c2500010003030001c4662000025254480c29040011a49a9a20f110b00e15800c8800709103115400881040b1000760030940d40101520150f130381e83ca0710f2654400300007440c81000c2c2c0702d042041c42401034400c20704200381100c0d9045aa41401440c0a2241d04c0d008a40000c041e442641040d10781e0203c4e0401403000c1005402401c28001800803050107080071021100d400070401040b82e0100325500140040b020010040d41c00050301d81d0388d280ca80c10f01080d04141401b40790003060003504c081c0784641c000e209843c8102c6041111950507030460b03482c00c1c10286400360010825032030302c4100038660914840c060050344540e64510b4040c1c60f0a2002e00340c0c40713500003980d200383c181d840c0c0840803d04131011200c0b0952580b80c4525082200000901d900c3c0707000c6c01c100704903011192 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 133543237 1250 133541987 133542001
    0xb01170a0f1109011205060a0b0a0c05060406050415020306100327080a090803030103050312191a010306080c060930010b010210060b1606060504021c1406010f0804061103 75
    0x2c02095003101c00e9075021080e40c01d13080441d05580b01a03800c0d0750007680d220010031190340d000c80603010600310b40c0b400c074080302c1d815241d807880d2500585064818540c3e460900003040301340812485818807020f17041d421450040005400c06901c09010b00c2850780766444011400c609a41841e0b0401c540405007000d1843d50821003444d0704100224000f1500c00c02c80441c044c0700000582c0e040ba9030010081d4540010340200b13028801d03014050341249210003142895182ca503004083c54400540310708824509000300060580c0c2c3e1310f42c000c604075000515016030700c1c0c4a2070100c90001000340c58403000368015100741d1244950140c0c0c4044040340400300004940019084109900c00980c2181d040b8510501e4100032240e003031107807c0e99000108100b49050940740300608500303000d50800200c0990f80c802003010f1340d1001c0309070141c40c00c415004032585100c5104060f04440e80c4150704c2c00360301d08100042c1c50f070b241500310b9405002004000404003d00e0303812a040b1140d0341000e154490401d12 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 133544487 1250 133543237 133543271
    0x20d02060c07031a070207030f060908161406072102030603210c0601050a0605030103060e0c0310060503061311010822061b020a03020606010c060207060608060103030908010b01170a0f 81
    0x1103180804e0500080100e00103d100252920070350f500240404030008882e03403004020280e09404880300d09043c401c440c104c0c990b032040707405042e0094001c52645031013040d10134106a0000d1103132091215000640d060040c103818410b56851000e4001a40e949515000038035040150540401c0d201040c0d0740c0a0300ca040000290404101c00c40840b02c1e180d0b2170320100000c070112401032a002910620040012640503048480c00d02c07246002d0b1100c3c02e002101180c10100802c040d06002d540b15501003201b41801c10143d60700401855080c508921903030759240c031107403511b840c442c10403c1c0c100c00708450341b0703662145607a54807900c01131804503030342850200041d1141100740c21408500246004500d40003041c0301400380e1b0300d0341c0900002c1d40d40340b0064401005000050303074041d500f0312240c0001400307485480058855200289503079031551500602440454010b0507040c0d0600c81030303101c580d0300070038184080000007940509541d10b810100b0000c2c00d4580313100305c4441c20203180c05140034400c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 133545737 1250 133544487 133544513
    0x21e0616021c090509160e0103050a0e15071209120c0c0b0309010c1d0d0b0702030d02030a05091204140103020a032a03110a02190201020111030f0105100318020d02060c0703 76
    0x517207600b2110390720350f60610801d548043c090342c040340540d102411150322950180b94081c22007400012000d2841660074600000c03c1403c55601698406000c0030381c2e0400846142c0d010001d0050080f144995907a2010030250390428003444a559029401c103c900002031000c0e00d000d440240c0c80e4500440304901070840b5203140d40c04501101800032040b01441d100c07152501000d842102c5952a42d95038003130200000f030034030702140020b01161164a00c1c070b0000798024010b034100481d807400c00403a0103007031201d003c0590740c42000c2000b04001035000050780703000060b401d081c01600c0e0020100264013500a20f1140c42d407206100d404003244e06c0c0440520100a17001d540e0820507480c4840b0351403010701c1031440c50f902503441800b104920503604d02c02900400c1c81803002050445144c0203400c0e141c9c200352509002c10361b0301d10060005080098080e01600d03680d01e0244120310061340540307120007050348081d00805036100002c080d5210710040b24500c049460440c0c0c045507076405e0203000a242 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 133546987 1250 133545737 133545739
    0x1207023c010e04020901051e0d02070f050c0a1d0c0d180b061905240a2303010b0301050105090a05120a140c1c060b090c0703021e0616021c0905 63
    0x10700d0000241014805e0b500b0780003068403500d1900f41b04000c036200d15490400c8800e45d01c5030030401a11000203600140000740e1145545240c03024003460014108044408401e0080300d14090810100b0000c000b5130040c11089440e94007a03485490081020b8803400a190808508001d094155842503408929140380900e0b20718200340c803001c0420400c1b005800601280303820200c014441c2c0e29010700440011217080360203030309044c094100010550400705065010038002c0409290a080c9060740c00031005c1c0888803a40f440d030421411110380c0c0018000d950420501049501c4541c5403018401c024040040c0040d02c55a407144109558025000045620540d441c841c216172690014003a844500024203540806400e507031541414604078500b51100b80c0c5070800d411440c0c844400740740c05007070b2112800d0754681280c1006031900104103000e0300d01c1c0c2400080c12041c058040385039500040f9007401410380c03a030071f00d030700324a000c1c0340c10100c415401c18500003200d40c90b04045520200c40c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 133548237 1250 133546987 133546997
    0x30b0703090804140109031a04050f060606070f030e030615040e1501090c17090c0108090a0f111912020a050d05030a050702130513050606031207023c01 67
    0x910280228207071014044020038000e030501007400040100c00701c0304200035045c5403d95145559440700700380c09240c0c00c00143c0414800c82400180031080c0200203100000200804013400e0040100d00144540303d0007800f00f58007861074500305807258040582d1013500070120381c0941052003003248081440307440c0d0317441a89005107a852505012854030202e912924042441f68680040c40d000f51016454410030411114060108200380c3c11100340903540c414001d03c980040c00300054a0048083c2c501c1105511140807000061011280d10021944c04140301701c80382d9841c4003050392004050090803400b0001d49004c603005145d42c8000b44c10314001c540c1c40700056a00c00034080ca00c54464005001d607001000402141802440200015803001d8011224916110041700417103901351480c6000908880d4a4020720a04000c050b4210f801107010b05100e01002c02120181d105c0d5110003801640610b40c0304080502c0003ea9540d030070a038910000401c5950144400810010855107021031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 133549487 1250 133548237 133548241
    0x91e0f1602162102030d1806080c1801030e0a0b0417030c04060c0c170a03090906080d0c0203070e0c0307020f030f03041b0b2a0105071e0c0203030301030b01030b 71
    0xd44001440140034140200140d00c80e400c05488140031080c41c44544120120100c6410050301c080000b41d0486015030749a00c03d204002040400c40da646600c2a010002ea11003405108147c0000304c03011304060040491103000c2d140c0c0140c01410f10b9407031829641c0a44070786070b400c0c41070340c04100748181d1103a81d2000409181e403040082c54082507a242908200c248807c1c06200d000340d90441015005810340181140e48070140c107005c0300d400c0ba4892740c41d000744446030200754100d01e8070809042040c10601c662428049030656403510041c0080420613004007820546d1010f01200003c7c2529801407215460507842c01000b0f9071090782c90b48010302c01c060009469000204c03d81da91301401e107850350320319251034076a00025840c4c04240709008002840000d1541d400f0350091a00c10030001d014580c1c8078242c08116440354040d075000c6e983e03034100020410b42da54016a5150340d80c0403901c2c4100c0c14000e15008464600c00414003d4040c88000008001c0c000540d03151412640b00e206044219 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 133550737 1250 133549487 133549531
    0xe0609030a0c0308040f020a0b04150e0f04020d0608070305060708070305060d1103250503010b0108130204020c0a0c0605121e01030305030702010b0406030809030105011a09091e0f 79
    0x9120350341c1c0d000001084030140c180060300c504440c40c1c000c0d019514440380e000c0366400050b5142c0c0b082c0e114801481d4005410040ea241c0001440f2450600c1d044c50b41048403690086128068180700c003600c1103900240040c22503402d64001806058450704a83c0c0c01c6441e49081030f540c900640b42c070f6011401110000e240f82e8407030300031a84154005008061034440503507039107180b90003505410f580350180802e406030940e030310100100c000c0c460401d00750742a40b07494103050846501c40d0806040120300d804010300141c5652081c0d89142c0d06580041e0b03580da20030546428155511001003241d85900c4001880c82c1d48040602404450b18141d0780d9151200301c000103030900140340e030380e5000b083c1070b004002180c055005141d200001d4000480c440301c45000040c201c60058004690001003c00e404140d0b007403d22400f80074002c8806101800b12541c0b501070f0382400390f6044a44105404400100c2001042c2e2980c40ca135150b03080c0c0c064250400b02e4580c00171080895025110400c0071a100c0d042c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 133551987 1250 133550737 133550743
    0x1e092e090f02210703060b040b060a02061803070302120d0905060717010e061806030705120a060c020706080a0b0102010f1118150f070203070b0c0714010906050a031a130e0609 77
    0x60030340500c018880c3c10728586c3e0314005403110700900350780b20344d507141a007100783c030790704018520342400780d02a0ad160303c1c0242540840385000c524030b107029441485000c0c0081d0300003171040d118018107c805912601e104104030040c042d140b200a00b03501901c1c0500000f0781d0400d60300481e60200303800c400c045a8031987c0c5048801c030125000c907030220000c511321116042e060300890300640050142e820040e02c48001c10b41600054041009a500100802c07042c00104d215512240302c562005d440ba031403901d64001c080c2d8001801c0304038a250307508480b075000d07030013540841132410020400b8003520a00a014801c640c024207a140150002090b030204585802d03c140c0003201941c64aa6003031510040403000542c10400b0101e07051b00c110000403588051500240030307850000401850742e1800d24000c07404415545034118180150044117224a035000021b540926030b0300c4c5000180201c0c048015a81c2650a000c01504540030084454034441b40b5001951040c0c2070908407903441d1100b0340c44a035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 133553237 1250 133551987 133552039
    0x7030b190219030606020d17040c0e010b0406031b080c0a020f06150f01090b18030109080f0715090206030105100509100315051801090b120102030f1e092e090f02 71
    0x313114800794031403107501523190540040c001c50f6a41c1c90640c96a0307503000300e5803003030b042400c5284000c40c00704101c2d603040c02010901b0f002580100075100396082d0140401c0406402e4004804003c640c01a050388208544600300c0d0011040314014201251800080017103e00918041c41600b03640541e194003176001c603401c403116203080c0c61800301f0103031445581445c0440201d6055403954807480100300f260014066200d403c1c48510b580f0034141ca0104040c00610300d80c0ca442500707048092015a4038a01502e0450f4010f4407400420415048120313198800d03c040980c1c403038600c1c0f08004105505501442d143c0400054440a4903103a20403c0824641c071810503010848540c0184034010041e00411004540a4584d0881c44002105282a80c104585801040d0704000c10842c2c485600c0040d0b800a55542c01d82028a05028035800d856030180003441c4814070150400e509403c080c02c0c4003000400101008228420341803501c1c910402d02044164407070320800c0c100e401c9815244610b10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 133554487 1250 133553237 133553263
    0x80a0c05030d09060614120c04020f070b0a062c010e04111207030501050a0b03030904020c030f07060506030c040504051c0e030d05030a0501050a0b19200c04110a0207030b19021903060602 82
    0x8c648210303004000c0a0341c40301054000c01c0a0900c40c4e80c000445030320209024207400000030072014103213200404d00c000d40d00110389071107884498541c0500680000b8605440611a003004141d40750b08260250b01800306201e5001051a03d00c0010a800400c0075002e50f4400c0000380110303180d800d00041619500e070031242d416041000046850f10b8103900400f0000041e030f007034900300440140c0c1c42030b46030407800060f6000f903111820006985014420358a600804941c10011800e0135140c1c10341d40ca040c690000c5080e560180c100034114018803041000800003000c40b030b81d041c40888014219002900c0010303280c0e04000010915140a24020007030325001251941406a85000e510010b18203e1032a4140314070f81601410381410541903100175080741c001000c0702e0a003601440200c42c500c00d8000c003100814001001c0c81035000c80c1c440704507600540456203e8440008080644107a10355003501141300282001d038411015441403407861032924200720840d643c2c030050307840e10799001e540 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 133555737 1250 133554487 133554493
    0x70b0916061b05060709080d03050f0a050402030f0615010801140f01050a0e03120c10050106050f0703031b080708012702160203100609060909080a0c05030d0906061412 74
    0x707201072840740004082444490100d501c1d080c01689440c1c0c10807509590000000b038071108107000048081204000d2411545400c1080f498a1078520f0000c05010704030243d40d071b89030804103003990740c00c00c08002d5520420081e185503092240d02202090081400c507400309240c3e07400040c07041d454101101e256407001c1c003050480300a401c011552075100700c1410051007120388c120700050314108000d80c1e038040014801c0c0c1c0d03140070b0044031034503000108401140300e45c2000c005201c041d50080c00d448881d81c00c248020386402c040d00e001d50140988242686480340803000003100603a010380e0003409003810341c031000d0b40c03a40c9072038040d40d051103c0040f80042c14011058028810680c1d0300400d070300c6100030041c082008103940024144061003201000f0b864454205010f940d102c4e100b808001c0c4084c1a0030001c2403a1136989070703554011445200180155807460a017409800e00407074030340c5040c10b030040290f00d0382c0d80380010044c030b900d004010300340d101c0181300445030504089050001c1144001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 133556987 1250 133555737 133555739
    0x6021f060b070b04151a0112022706040305120316112a2707030c0c150204030812040c060819091502040f0e090307020901120c05090a02070b0916 64
    0xc41c1110703400640101c402d030a0350008404210007030f120b080c1c0300d00040c0281341003406e0100001052403112506180e420b6204115a1074100380c80e140c51000010b01c028424000d440c20000100b43c1e01840e030000c0c000b40600c0e07030020003070821a402140728040c03031a0007500e625403425040310100182c40090603a60302502c8000704030898065100018000e00848515032000d09020403030034060040003802c030203560603801c849000c1ca078503400d1740441c10b490200608451420020824440e02c18090b02c80d1040100e1700513903400c9901107034003464024481a9071401a10805c02800c10102d4042d50b507102c2c20741d0301007421403051840b18050181c41c0c5010b0b440d403090058a100900e8803000869200e41e00783c1480c248520300f400600700130408511600d0006140206003a20628010051882900200060130041e075400314101e0555590b0f01084007c05054906009100071503006982d000c2e100104020800e004c9030001c004403445400740a00c607445d0303001c80c01e42d00d105205048500c01041c00e4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 133558237 1250 133556987 133556993
    0x16050705010f020a030f14091e03040e1006030f020703080f0a091b030c0b04050102070b13031a1501140307050d0207020402040e1605030c0f0307110706021f060b07 72
    0x10242050901910000031802c110b5240e403022a0f020f888848042919001048440e12076031040083d0b1141c400960000c1c0d2600860440c7c03140500c0481c0302d11000ca1051403070041e0410001e81d00a8078410b00703040c0c940d09000155002a800b18898140001d06088407003d4030901802a100c40981c56210500c2c079480700c000c4581405001040410b001c4e954081d81008900c04501210b0507940300707040c04001c81d096003002e01458013280c0114010b0902040100b0040e640090489c08843d032101d469511f0300d4126a40c2c0700042d100c1d80c409030042142254085040c0c480300b00c803a015000310440c2041310ba80040041d20000441441603ca5410500000d5442070142d8014007200d460141e0051078101c2a42c0010203d0700280c1106603009000400c00c0480ea6500c4402030061602d41441d906500d01046100d1280c421100c00030440400880800c5800d401520000c180c9021101034a2540781c581000a6135040170141048000c440140280c0003880d46125617410b82d6032080328a0300d03181d40340d1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 133559487 1250 133558237 133558247
    0xd0512070e0303070b0a0204051905030c19030f120e0102011b0315050d0c0302030f060c0711060c030703110c01030608030405102c010e0105090f0d140706080a1416 72
    0x80d0312282c0501040040c0f8002649a0b1340162042240c0c400050302d40741058140015941c0840d03213a400580142c00a0010795000503024099007021280d00b080940d040032010803501440d80300801048070010601c0c204881c44060207a10951591048141c0c00c00034012801d0361030b042a804080107400ca65406424429084030007010136144101c0c0ca0541d50f000458012070001a054805041c0d6000500031803a080c0005003c102c01c00000385120300f04680c0003081d0b40705850300100b00c0d500240120044d40c0704d41c402d032140310110b4000e40351500000c2c103000e0803148091000c0c0c1820300030104040010342c041d03c21003081d6100d40005508081c04c0ca03040c40840340c810301c4543c0c00c0c411440d901483c20300f140000c001c3c4100d11a0250441040380c034001500009801c0e940c203060104c00c0c4040030480e100c1c0d80701101e0900d400c0790144003a80c01820032100089444a030102c2d240203440021031340036085110540107581c410b000b00903c1e1401c80071800700483c2a60602c0200c440c0e4107405048610030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 133560737 1250 133559487 133559507
    0x120f0112030804140d18090b09010e04050c060703030e07080706140d060b070c031104020909070c151802030f0127080c0a060504061b0807120b09010b0c0d051207 71
    0x1a1554801c00c01c0c4400c0b0b0302d180005e152800740c001180190100c032204040f1654000509240c0418000400207200142601e0414050011b481154500003001d005c001c01c8194015000940250780d229054203005000d00100600c55034240301d240070014180b54000b45000448080740d403450841c0010140d1070758aa0b03c40f04190352955118440803a20252010082c102d203032103114807000840c07a51604812003211060aa440340b0b00c188103038500b079161400c0503580050f40d4900540461941d1414000810140103000c02e007525241c0182a007501900c00c003400680214126029141980c00c02c50a8400e40b1040381002181002c0e07094005d0422500035030441e100e00300440c00d1120b40010705151005001056861540320000d02080c401644600440300720b81c1803556010800d01d680146c1542c4001e004502000001c2d043c094044405038040404004024003039274030380d65a95500551a008004205454001c2c40f4804407582d0041c0101c40d400f1070a480d240b00c6a9495080c20340d08a00300b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 133561987 1250 133560737 133560743
    0xc180a1413090c0801150803191407200a090e0d081305010f0b01141204110d0c08010507080702210306040905030c060907080111030a090609080708120f0112030804 72
    0x10340c2d0350000054680401503002d00103070000025500359800c2542440c03007141d40940c2c01c0350001c01c00c0703104c54155020004207006a50801006402c103e0500c1f4403980b10306107025250398451000302c1c8070700c0341c0b04034035840c81642110402100e90315038192070111000c000a07034008d0391001c2041c7c81e10f18090422580e00121200c2303da801c070900b540b265400c1d25070700035006000e1b0303607507505a001940c0c0014084194841ca200540d0500c1c40b000c0003440008000ba001410052061005801e603a6550100324603681e032042030300e01d4bc0390396a10182d0180c1026035580012030303000400514081d00c0040e4100c0c40442049680341c00e04011000140d19601c0070700f2482d0803545440300e5402080c1e0800003071214541c404008c003e149405060542045015006401e00c1d9040000404a00c68548141da401442c0e119000407210560324014008298020300104050404030358203062040000103000c3c020b43c00629101c465903006d40d000c8440100f4016200e903c9010000000424400d400c46035000d0703c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 133563237 1250 133561987 133561991
    0x130302010617030d06060e091824010f05040902060a140706020711090f100e0c09090f0114030a0f03050a020f1b030f0615010c03170c180a1413 63
    0x307114030700c03544984000c102e6010107500001d41d000c800d0190748a02001003429280108003100d441d0002034000310080c1c140e0105035111032650481d0711050014030185580492080340180c5103204007600681c00744604200c82200d000300007010304240c0240020668003c080900e84140300318155905602107510b88090001444101c001072201d20090a54131b015498010384002100c042004000006100024041d1004240203032416030500c3c00d003d40348040c0040c0d41c0c556074004e50800501403c1c11460380300f81001c0920400c030384840c0c0d601d8145c2d03e0541004200114034004c1c0340d0303154030382440140000407204000c40400d2140c0080c1c00e0400c072a2055881001c40810418a0b0000005440641d440303100c40043d0146006c0180821014107000948810329140880000e81e03410b000d2983d05004450103107108040c8501545200081d030b0300c4880006050008216605800400d40200703c000d001c41d11019924216801c1000c40b200d010000010403070301d905002c0000c094482900d0925 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 133564487 1250 133563237 133563239
    0xe07020c221508100c120b0d02090a0c1b021c02010c0209070e03100b030604020609190806010303030c08040203060c1602090c031006081303081e040c050a0f0506031303020106 77
    0x49880c0100500c8989a0409420181c103202c14942130050715004075559500d008030742c42445070060030000d1501c201500006544402038042140315010900c02035119980f841040306a82c003c0e07002d441e04001a03a208803010702c03500b844402d1580c1d074017800381d4014181c4030712070300c08100c40c0c01e00c0210510601d01030300b80381c0c2b550380454611002920758401244040d01d241200f030904102041d95280b00c035105014400c010b0303020a44590014101a01600d00090401040e403268410718101c0e01c5c000c91840e040c0e5036203c0d08a034a0314000c0c0000c5000a05103011003014074401c0b1551070107950024082e00e500e40b590104015260b01186c0001e0300481e07890740c142c0c0544c1d907506605114200e11200d0345d6036494440c1701e01e0520301160300001e0600c003200041c022404100d09132000d60700d0745818802901c0e2160040620840001801f5080c13800e449000c00c0704004040c00c03800200c071015240c0ca042e1a489106420300d0310024080c00e90080024000226440d241a40c0012410300a0000003101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 133565737 1250 133564487 133564549
    0x190b100b07030207051c020a030b0711030706050403180b030a090212030c0102030117070e01030605150d050d0f030e1b0a03060207030503040b070c08090f01170702070f0e07020c 78
    0x3540012000b0380141c0c004070002c0104d8101400f2025110070204100001e004a035400140310280b10300018002c0c404280010300756034000c5c032011810b11240c0c81200d845001a02d032440180230115011400540184400440b94404074107107410f4131003164403142942e0b0303a41070300c000400d4bc0c16001d076030180a000031854003020500c0181060b190751000940c3c0e07981014130b085040c003a051000e503010b44c0f080404124031203140885905403a442078001c641c40d242c44150318a4140240302c540c1d40221083c0010f000c0000003d44041403500c5920f0b602221075a031003042d002c890581508001a0f040588190140c8005007049100280b000703011844203600d07070b240c00c0202e030003a40045010800c000203000c180710180c0c0410b0342c0111075180492400011b59604c13800d60040c0c1807607a00a1002c010303400d00c5030380030707180d80081c0e40d6981440c0d884610300210020b64442d0396224205d42214041c1d0049040310340c071241d0500c0b0360040d4004100d042d55510900405058542440e1211803807082c10b1914 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 133566987 1250 133565737 133565759
    0x2011709070e1e18030307051803160810060501020705101205130c08030f0405060d1d0c011808030a1107181401050103050403270902030406020d0608190b10 69
    0x81400c203c540c000054030300c01181c40305030040c0ca141039018003840e501c41c1940300002146d52082282c0781480d1650000e55280c3c803849041ca000c40d50500480f820140e26241d0740d114030007101d40c0710040b100883d41440c0d003402200c1440c0900d50041e0001c44050282e41016031041814140601e04610b0240b070022107070303003260801d4818100302c00410a10200780030309080e43c03002600090303024503d030000506409441d4403a0f4802d80d030040318049240c0d42244501c0d03019075822844581c004e4040b204890190340c403001004025404900b44190195103030085c0d006180691341644011860076004000c1981c2c1d012401c15003405906c581440454800380f00c1602000c0411460030109140c144000030300c404040503009181018906010000440e5106155210307003045640101c034001d0340f60105582c4070705581c001c0200180000144810810f00d40d00421f412841c1c100c04000c02c5448549154444048000184070500c0d181e031018041407034101507980206010210010301940c850040103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 133568237 1250 133566987 133566991
    0x909151312080c03070c02060403080706060e0c0f0904091112030d050a0c05030402010c111c060c05030402010203070b0601090f081b01020706020706050d02040302041107050c0d02011709070e 84
    0x118800501a0304410003051840001540049051054003883e100708070014a00005010340e04009008240300c095445800840380a160040c508913602ca00c06e040000142890b48034001c00342e40010005200e810307500c02580c0107040b14804451500d1129410040600807500d02903e007007400c051000071a43c1c490a0030f072400760320600035644070742034491010101c90300244802c0859003400040355880b9032207003c881e441942400d007000003031030741d007042c40981d01c0202c02203030000000300007070040c015502522015a0312070307141800712600001040f10300d40400d48001303025900520044002402e2904034550002062611806455130354180300840b540592000180ea04024600114200e14084070346085100f0f00040c00350a103407100003541c3d20400c0c800d120403c0b00200e001e10201485070111401544c0080041c40a003844208400e40c0382d20018080b01e10b440f80c419100c91a041080c606010550141c45000da5241400c01d409604540200091054002c0950100380694900c2c19a8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 133569487 1250 133568237 133568251
    0x105070908010e0307170c0f070609090b06131a0d050103060207030210110f0705010605030a11010f090f0306020325021e0601080a0809030709061401090b0c060402090915 75
    0x81124038140c911421a800144182601d40041005c2004102202004401d11044074600f581d603640c400c0072242004800c120000b080d0240820020361260300603031050549040100c01c00c0b070400c1c814200807040c4140c074000503c03007203140c90401000714580900c04600340380090851405114201040484800341c00481d206035004c5020750a2541c108007498144015900803c4001075200c1e90701141d01981a9140703500303d0002c0c0f01000c1010a400000c024100641202d00c0618107141040c1030040e50505940003903030f84652001924481e25981080700c4030508800301a40c00d503144d02020394001440f804040c0140c981c2c0b10401400560f58400c40180c80c0d0291680340780d1580d01d802d251004200d403842980c80341005011503078012419021036a030096240783c0c1c071240000070900349106944295420b5107044400140b0900041500c3c454500c260b880300030043d12043d40510a0144103410100ba80c07211000400505094420720b40144180040300c068804406207002e503c1c204030360103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 133570737 1250 133569487 133569497
    0xa1a1f0f0911070b060f0d05010905070501030c020303010f051003021c05010801051b0d0b03120d15270905010b04020c03070506010501030e061b040b0301031a06011d01050d0e010507 80
    0x8200034400d40c442c854500007050301c001d241000b070751200c4603c5900609607503c40c0c0456101448a99500700b41c65030980c1d8408001c2c13201d440f0a05015444400c0392203410f0100c2e02300343c02004120310110490f416520301c1800c1c60000c505000610042542404081c01495400c024052030031503550165095518661404200c82d03051130a80c0c0c2c01d482d00036280401441e04420003840c4c61400f1020b0311040c50214200113023410003540041e14203180002c102819000008500c405400360340c02400500c83e00082d0481060b980c0d040e0190461102010f2000d03200040c0f81d8101108810f0f081055030798056000426240007040003c0c00700e80c0240d408031880d41c0700181e01e0081003004d02440d8018282400c0c10440204008a407035110300c0d0040c00391041c042000d074140c9401e940312041c0c4d00a4000008051f4503981c40340b410f004c015101502000c05020540c001490562251060100d070340326220030025041c0d030702c5c070040d129500304040c2d10700c81945400c107a0400313070380c2481468411600fa50b11 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 133571987 1250 133570737 133570739
    0x408010903030b06040605070212010f021611012d1106070504030204060e040c120303230702010509070501090b0c1c05120f060a0302090a090b09070f080a1a1f0f 71
    0x2000d0b044031100c43c80c403402104248800c0004076000816101c0c00e0b5011fa0b13a03007810009202500b4010000280171064151011404c541c001400d0298440d040344941c02c080880e110701c40040d03135441504082d0860104240700004004180310b10304410300046800c10f4065011803113450340c00d0083c201c030900c3c0001d0f000700c0c0130400d6190078002c1d03000814096030041801e0600340c03140f2145403150301544441a001400300001c041c800c1d4091150818107008900c040c00700c140c00070700b440900796003040040d82400c0c0841c10f41500410b11104617041615002280381ca4294a6a00c9800c25032603401c0601540010398810302202000400c15041c5a48075a918004d502c02c070b680c6400003503d00480100f040c0704000d801c2d143c0540c40003c0e250115a040b803c3e40d22000c1c0c2a000d40416040184034000c0e000a0081c45140000d604041d501d0311090305120507268040103030380d0b21100b5005482c60000c18040c4e42140c100a01c11904080724405100d020b45601c400c0f211007400590141c1d0241031a540 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 133573237 1250 133571987 133571993
    0xb090103060c170f092503060e190b1023041d0a0b010306060b0a0c02060f07140f0106150903023f0c060705101104080706090302040b030c030601030b04080d0204080109 74
    0xc04e1404030750101130701075403014481d08086c031220703103010003000e045d42d40080440c8070004001110400b100391142d032106c00c0c1e6a240c086240e0605403603200a00c607a40401054003241104440c401031001c0091f900d0020881c401c21000c1c02d21030000e0b14194444882d07103403541c08280000c80030306004200003100707545580b82c01421a842c0c0c0d8000409c003001845129811035000c0c424010064048a0f0291100200051341c0b0740c3e072043c41c6004081003074002060f0480c110200d0b03160201c0c442c080c006c00c00d046d0748030300402d038580602107190001402c0315011320042c074103040d0403000000175030240302001c02400d2019180004000305002c19910256640590410800140008210035a200d5003022456901d89554080e801b5215002a49503214088522030240c21388008140e00000c0701c08680d0b4a0304090300701111800260b028900f0044030304020b04000810301042400500101060b03840c68603203802280001d0030440e41705c8010466071072102d55500182002e0920100005140103c41c030b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 133574487 1250 133573237 133573243
    0x1e0c070806060a0509040c09051e04031107080c0f060f460f03020901020a0c0f06080604050f06010c06020906030403030b12072306090a06031d010b090103060c170f09 73
    0x141c412171254402c28200400504041445030840b0311680020860743c0301d5003a1140c80041018024070388010640c104001c0c964408243c1a010b99000305071209651034090058558516500181c0c015810901240b220b06181d0018588582d0485c55541400d52209501c401600d44581a0680c00c0c005583c60900590444155640d190141150420b507101c4c0c2d00081d11540c01032441c003050681c04500711410764003e200299415900c0108000c143d07844140b412032078003a138064a800200344038001015818148140d6008410103c05c19000c0d07500d0400450b4100000401150556000e10204038561140005140107922035180800c42c0d8105034203100172204641d40e000c0704d40d80700600400040c441a001881d4000f482c881c4648414070001c003144861140c7e40803550484581000001c0c82c0342d1503806040050207007404115414121800d05098070381d031082040d80030040c01c00400020703405034010031800515050090300c2481480f14004094004c559004001c10080b0410290320344c14 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 133575737 1250 133574487 133574489
    0x5130e0609030702030d050d090b01030506100602010603080d180803011508060f0907030b031f0e0c18010501030f0e01020705010b090705070b0606030901060f06030c0201150503031e0c070806060a 86
    0x3560042d0704040864000aa8907401c000c00e51044c050005484041e000b03007504651117040e0460b11303410583d42c9d2481d00d9076551078126507101c0d418900e40400b04c0c0c410b00c18003032003003203d400600d50350030550b0800c10340340188540c4404510008120024100081c11800514002d005514840c0741c03807040c52102424908000b8480c6101d103d44039000020750303840c3c0007001e400c505c407031400043c10300c0c0d410046454000c1d0270301000d03200e000b08642c040f2960b00743d800ca6664116104140c031014500b070810f1100c284c40d00d94040c501c082002005100070b5100394096040301d0720b100340c04070b608081603401d07a0899111041c02c2d074269441d492030650710f0a05402c1301da0000007902e021440c0116a840f00f9900b1480507101134418800000402d000d14425000300e005001c80d82d01440342c240d9181d00c041c000300790820043c0092750a0402104c803c6200c1004201120b6000d006540381805070444920b221400550004903503405000c09803031002e003044980090304240004208904117142000b4100400e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 133576987 1250 133575737 133575751
    0x3091b01111c0201060503070807081b01080a0b030f10050124020d030e0109060207120e01050c07091a2107050d170a210204140402030106090b1305031603020103230c07030905130e06 80
    0xe9400ce890f40d1150940c2d40c0108800030005050380008000b070306100d500044072140340300705184a616070300c040d1b02c40c50480c0d0601d450783c4d62041e41106001901e0844034098005a0091580340c05000e000380c1120340414645c60001a0103c401ea5401e4101c2c0c001001c2542c0e45403c6594646200d6000521600c0040742424441d09004d40c4114141c2c0e5140c160061480c030f50b865080140000c0031030005081c10081c01495504182070568284004028a000e1000948115400084e075401e181040c0310055400403884076111170494a0003e00e1340c8064526820040d101082c0f007410410714500c0c10f41e00e1520280569258501543c0c01c203d080441440c91003684100010805550006011012981d0f00801151104400d021005480400354002a0940540040e00c0c3c0012440b10124065078800d032800c01445031000e2014031403a0f000c4800d41a4000582e02280b10300c1d0418005d400000c0c402e14001c9021601e070300c0403401d0400000540f404440e15284c5c50700288000344029035001ca4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 133578237 1250 133576987 133577023
    0x30c030609060510050a0b0d020403020405010b0901260610020c09070504050f041a0d170706021c0507091403030706061205121c0f020d0203091b01111c020106050307080708 76
    0x1c181707000560014a6445445042c5000262403411600c072601514021500200204803540c2c1d03549404c05641c1c0294542400101c1103840d0a000c3e003a0705c58590041d2440d0540700300513070340c3d0300144070700d406003043d15106622541030103980300e640b50b45075644107a60769513503e901c07079191009001e800021442500d00c15810070301c1c03083e030300e100543c01c0c050400310440300d001444e012414405004028000d11010260000681109020f056001070006c0b04881e030300d1500d0b4071004501241191821742c0c9000004541d41c404010300341c080c403207031700c44400000c0684e49000c029a03680d074115401980820302048021b660b94050203420b1114034020341f031070440b4510384141d44494014400810824028142c3e44070481840e08856034142c07003112440741c500719541e08183d03c040e56a5044e482d480c2c0c0e20790391400c110f40e0055118240581901203c0c000404140708c0181d00e2026038640c0102d5902150360b53700000525030340130040310b0000c12076100074040d501c0c108010316044c18030b02265007030001c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 133579487 1250 133578237 133578239
    0xf0e10090c080a0327120b01030203120408060a05040206190206060a0f03030f120906090b041103070503100509030c06190f15061b170913060b070f0507030c030609060510 75
    0x2504000c102c212800100e0404040c00b07401503000e60420300c686c02100898240340e040800300719400d100356040c0d078003c40807288003108800013411036100d503000322011b50300100c021501d04dc885401590b00144000d14142c01c000c078251141076581c032000885070050303002030280196411b1a07110100a130441d2500d84001034295100601100c12881160041250100c660350351900e650344500d03000d41e4040001e21007580c007801c01c40c2c00601d042e54103658460803a140c491081c40c0001d080303011108040c01500c1861910461400144401404880b0700d0204100702e108110003030020314881c2e2009200d81019440030902c480c01c075030358401c0c41100b291030f040e00e040c4820b00c009607035402c662052810404c1c0a0540490004000035100001d040042030b19580514000d0000a002031110944802480e00d03000300c0d0001c02d55030b10707100c1e24141302010070500021460981841c0032a9000c2c50440c0d1070a0758940e03600010a5207a40161805035851017404100b200350300605401040800340c1c56551 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 133580737 1250 133579487 133579493
    0x9110913020414250c0606180f0605011b0f0c060305010812030709030b0414060c0d0b04020403080706020c122709060102121e040b09091303120f0e10090c080a 70
    0x3100d40340d8007034400f1040900d440c2480b620824030320740406c4c0d03c16000e0006a541e00712041789010400c110000f6941010050752034150184548421130303a0594071360f94020501c1c00b00e1440300c98101001d8610302c001440c40c501242846d0203044c0141043d03a00000c9642c54030300350381d0906c2d07807244402103c800200280150a9805512107060340d403c41c1d45218651503d2a0145400e24615800c1e821409400108030b500351402d4042c101c160340101c000c5c000780402008220481c8203600005203400c0080c05024041041940030306040140b0408031b03284041c800c001c00344a40c10130052005440741d00c0501d090100c003402c031110158802954025446c0c00e203500042d403550020000031388041008132f000041c080c1c16807070002c0350b40c0b0000380140d0b030389442b0011840c01e6400455141d000e950160046488104840310b2401140c1d095682c01ca441000c100c4000090842603034107103000f80c0c80701c0e030501781c001c2c041c0204060580c10f8000000d900810346446d402031401c950280007a60042e0401d0004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 133581987 1250 133580737 133580761
    0x103050309060d0f140403140f03160509031204140a0302030309040c02070f29030c0a031104050a120c05011b0602090307030503040b07060e0d0f0309110913020414 72
    0x100e410704980003900c803d900b907a0400204aa140c2c1c0344000c0307003081000d402c07a8002c0240b19010b28001d66426000181036810001d04e44103840b484c1c1400e11003000090388280b0407a9211050b21401c0c94800d1900f2591400a0b10309510428129142c80000034200400d4072900c81d662034516046d0b800031001032454000940f24003c01a07842d0146441d042e191581038828040500134108901c1c8200030b0340e803a00c20b00c3e101809005916218601c4a101d40e0352070b07e04c440709503849180e008200f81d2502d080b640048020b82007444d00c190026200344400328150b40c445c200309015040c0b4a10b0b440320512141407a1101142d55800b035410300c03500c00c55008140e680c0403c1000030941240c005030366400e41d000840d260200f680d1024203140804030740800c952411100130310109001b18028441c0720600c485054a9400d42c58200000c156038600a0036291301079000500b00c10301400071500b81030030350400701d20850411640f161840115a41200171858284142e0394410ba040503119100e00d030004036800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 133583237 1250 133581987 133581997
    0xf06050f1c05070801020c01051f03030f022a1c0b130c0b04060203131d0f0c0d06080c100e060301050d05070305030a02160b0910052a07061701030503 66
    0x4068081c0c0c510055881c00309280081090354000111602e5541d00c1070068000d412081c2c0203131081d400d190114084007401e40008904040d498294502c0c0f61460f0780c1900c00c0340120b0400f000758020b43e0f15610407459004200a541c2005800d401c440d16420420440030b0480812150251101d107018240410984110305c4e07030182ea00c0104214801c020705100c0591341007a402403d42c1c001c0020041581c55000c0701500d40804048100421540c0b501c405c15420540d84c528071900881440c0002da12000c0d100b062a000101215140d20305060068000c0c1965551f170000501603000c7e010300c141508040a40d900c64a82c0c914049035011800000114184010f118039803041d981c10000c2c2c028400c05103d000c000395484400c07207aaa1b10300071400703910303100440d2040c0d60340800c808001400e00050011580d022000601c504920340030910709803480d0300402407010441104141d4990214012401d1440124004000300126031802100400070129445041844220321004000044000060795 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 133584487 1250 133583237 133583239
    0x6230103020c10410c04081504060216030e030609030a1d06040e04060b0a0e070806040c020f0a030305150d02031b040f14040201080c0310091a040204030b09010f06050f 74
    0x11130145031100614904d10641c07160500c0c1c5141405034001c0c1c50005a100c03d221032a54168849581e03205550481540034901c640041034208101d4000d044079501492a03220380700358001400d140c210102c40b01c2d03220740c0003c00c0300801c001341d9a5035010724042059590100810006628080803110018020442403001c034030f404000054046d00c40d5502c01c1650094103140300c07184810f00c0c050600c1005886840c0c581e0b8060300702c1203c0811580241c801d0984148820348552065884003402c3c0701c02000003038804000c500501200d550702190510201c448a8040d42c0c010505051101c03001c81d06c94805101544502440282c240040c0c4021800031f043c1c00c03030b00e0700031600c00080c003001c1406000301350b101c482101d24190002a26601c004038050045000303036074882e115600e14215258034131007518810301c80d2642540c01c215440980e0002c1c40e841e41841c14202d00c0240540c0844c080c0d8000b074000321401044003041101c0b9030f009101d0310328000c48001d000d00000349487c012941c201c04c030380c07001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 133585737 1250 133584487 133584491
    0x5010c020a090e16090204050604230307080114060f1f0909020d0609180201050d020f0415020a03020f030405011d012106050a12020f011b0606230103020c10 69
    0x10080d50368014801004208040e003d1210028000545803690a078030381035448110007801c0420100e415200741d4040e607002404d0380d441d0504114000450f10b603401d40e1100c0441142030000e8140c1c03000c1c00200001c1c8903920000c03902036091b110315042d680d00100b40d42d00905d400c2100d00c0746981c034108a0089162600608121071804d100110340caa081504103c00341030002558000102142c1e10000460b02c60030410443d40c0ca4200164844000c1c07800080d001800902020758007038201da006014080c0d403000101c0c6001d5071100100c5070204100c0a0801680190009100f0706405201405183c800d8501031440c29007440c0000e803c0b1010108164010803089424038800c0e4010060300c4001c00070707001082184074241c41c015015181901542e401000c04000004918907030455102100d0b41c020310000e224142c0200454110018000d040c0d030350032200030400085401841444060310382c6c4900303a4004c80740d0340501d890000c1e0700c04006d81058410044826010340118801816503040100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 133586987 1250 133585737 133585757
    0x1a09070e01170c070b15090612010902030703060207020306010b0301060203070b040317040501050114100e0613050a030506060406050d1221020a02070e011a0d0507120903030b04110a090501 83
    0x1290b240070041603100c0301000450900c01600d0810000d04169440303161102d6641e80c6080440d1150b8030a203091903004016400456151710f00348981054000d48000001000f002d036800180c50101281d105a40c09a40000c901003903050a101490251050721a02071541d494110300969a201352800906100d5040b00418200751241a031264030805c40c0d0002d111a041504000f8000c00b003e1084244402d4403e491041a040000d01401d0030401a21103624202091090009a0303000e80c0100300d0301c515480c8042519503904645201860042c0c009060928101c02800201d8003036403c400d214080c414541400030b03a48008441c1e41600710b25251a4014030550900c604440e1010020400c41c00070a101c50055800101c10007103600c2c80c4001c0c12030340d030f07070701c541c4115041c17209281e04c01c00c0c4003005140c502812941110390080c5d8103150071140900311500c0d620455003280c40440019841d25040404c1e0714240c005c815802061000c6c02c0c1c81e108030341d0700140c03180e903040c4141414004000c103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 133588237 1250 133586987 133586989
    0x50405010c06020715050f07021b0a03030305090c0d1202010e030405060d020c1f0b180c030c031b0403030309050607031401060f05131202012309040203040206090a0e07031a09070e 79
    0x48103a02d880880e045c28000f41c1058000b10340c811004440c078800622450782c550030040481d40c9400d820b041c000d001c0d5040f29085407000ca026142c020480c022500c610600e481d0316032500c03043c1e465424000c803000d01130f11a49a900900f5521406035401d03d40e842440284682da0f600d80858519051340d41c001a615405505842d0503e80d060800c80d030620f400010f0303195141881e4101840914040301d142c48002c6140001c60810042070300e03043c45580381807000a00c03400b40c2100942d040704403102504440c6070b418030071001c01d80c000c0e041100043c1c3c4505a040401004002c200d800003900c2c14103010007002480c0141c10322105200e480c08005000440250042c0540100c0e00a40e00203000c02018688402d11101c242c422144201d00160f030001e2084030903499a070442c402000d42c8038526103400c0807e000c11010750070260090b41c1c4800c04014000680ea180c1d0240c42c010001c03109660b040c0d2804070005012940d07550340401001210b81441000e540e51202480c1c4d02c00964200a115001600 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 133589487 1250 133588237 133588253
    0x702100e010f060e01150c050a030309020a08030c0102040e070e030c0613030206070506060f10020a020904020a050d030206011a0c07150917100b1c1101030e120d060501050405010c060207 82
    0x11201c0e511490301d8800704035241180044c40c10707148401c1c0c061039913038090300d411948900302040141140d0409106180040e1181d00800d50729400184007034030280d101c407401b40c20740c2d00ca480840c610340e42c00a42000f034004400aa140d2119143c100f021500380b030a40825114183c0748007442c45003100080d00c2020b400c502e0844c1001e181c01a0526031142060701e4180d603543c000b901c000c1d00c544407071580440503280000c4200c400c01d01550240c1404242c070f50a1041016010307000700c2c0e0110307014401182c19141c0c50200c03800743d0702075402800c45500d006400441c7c0315080e850081c00542c10040e824404200050b08003c5842c441d06444201c080c0c041c0c03c40e20301240790010045610009800d10024400140039610707000205000c1014443c0081040406090b805441c2a0100089001008110b00319814000880103050100e041d403462103c440c01c0440d04401684ea501000c1514400c002c0329104201c050034080c20154130305030500e000604280300060340148410b80000d80761701006018 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 133590737 1250 133589487 133589501
    0x60e01121506030b0f0a031a090a140a02090f0132150a03050601030204030c030f0f021306030b0a09030806090c0405040603150e150c0901020a0f0302150106080702100e01 75
    0x110048402603280c80b4014040c1c00300f0740e81e081c40744959040c08681480c104080500300ca40c080600f0b1507444608843d080b10b070600504024031406145c9403032300400c0001031000680c0c082c40d4013410340c5030072034810000103c2002c0e00d070300c680d0403040300148a01c0c86800c42c5140200003000d102031103010035040b0f80200008117079640350403804c2d91200300d05202031800903054050294034140b014bd920744004504038040c901c4068541c0041c03880410204d41c0d03011a509060740601c01030607082c50340d43c0104030401480310b00211b040396103074010002d10107c081041e801c24803200d8288203001d05900c0050144402030442c902c074190341070200340d11401070f07400c40d0002c0c1809042884070b03e55908060b00c40710354030703c2d940140604200014201c17000c08140051911422000e4607c1901c5d01049200305030000e4807010f044d4824500b805000c90350322410303400c0d0103101c1d50060903040c094401c1950781283c10303484a02070000c5c82091080c03a540100300103014548a4000003143c118450141c0e0142c221 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 133591987 1250 133590737 133590761
    0x70507050a0c080718020702030c010c020f19060207050102030f120c12040c05040609021204080d06030b190b0a2301090e162a02040f0e0303070c03020d0801060e0112 73
    0xb294000a01031601149400444d510765113030402a20114511000768801d95000a5050308194000d90385176001d00400e040c1e0381e0000e0020030704a20308101150203100007542448410401140406c691340d410002c64024040070710295060625100b000849800380d111520300c0489142c001503544100030040c1c660700b00c0c07000812000c5051604200601ca220390180714000c0d8102400800c10b92028002c881459080414600040e5600e444012503500400c1d986143c56480b0240040170500b0312510318010410100400c542c0901c4400c107204a5414400b200c6c028188110f0030800b107144990703068662250781c03d014020526900c01225006069081402c1c0401c84005218020b103150406140148868540b01e42c039000089449622503500003d0355021f0301d80c2c500580060030f0680002e81796070540040414411040c4e520039003950001c03118000051126520390b000e141d1704008486061915080c5241030354140720005242c0500f0404042c1803000303030010060142c180c3c3d0b01c04910340031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 133593237 1250 133591987 133592003
    0xe011113060215010e0703050601050904020a03051f0e010b030a0902040e0610061e11010603080f1312030e0f01090503011d010e011401180608120301051305040308070507050a 77
    0xc00308080302000d0160050800520844807180c1801040b4640e45050710b82151052500355500c0c10102e010303100c01000c02e41000300a001d82c080b291102c0c00681441503a07628040385901e056040e6110000320881084000c3c480380070200302c1104402003c0c0d054030f070b400310003c0d0b0b29514800207201604400c50000e40042c9407015110901c1c3d00422818000c0b4520002d643c03040344d507054110303124461a0080825081854050321a86006503400711762000c00350004184556030343c50b910a95000001d1001e064040011420320340030710941213002070b00c0044000720201615440041c000004405214012a5a040c100c03011307038060310101006003c000c009000781c6143c0c051100c01800c100c000320f00c4d99030034403030f0243ca551010300a660361901c020960b120319a00c2d00f0300100b40b08c104198004002c60b0b0b92440412140002d100003200d00382c400c61a40e90ba54500401d00044480c2e14021258003482c00f014040001d13400103083d500040545030454455445080c8241019211036004000007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 133594487 1250 133593237 133593247
    0x160c110d0f140a1101030903090b13080d05040f060503040303090b07020f10090209070e061902010603030905030d02060c090604050d0b06040e06090307060f0b04050702070302030c030316060e0111 86
    0x4200e6540c1c0c01e101e5031241120310346004041440aa40b400100300080102501020b40c3d400703035101354444036205029260904003240d0359481d040042c0d224450300d9464803410f010901983d9010031180d84400010320301245800d1070300c102c56083c00034074040c0404010000020400b4180320341c10101c40c0c2600900d11500c0c1d42008900070b55281d00da014510700602510080d02c46072a200d03c5102210b5801a100c6003066980180c202c44080042040e030354000e00520620007524031000007070402c0a0940c00000b40e0500394140541403082c7da81c4828801d510070030000365201c0d808107000c0d401402c4401c25549400705140050700038003980e048640c201d4036510512007401005180c450003840c0a4900300000b8015200194627008220b5192409e6881004074000040d1035034085180005416000101c82151800090540364191203a1005901c544000d0080d0b1600307012a40c0c400002724019450100c40c100b4040741262400d0300134201c90f0781e86405c0c0c03004903020f400040040c0b805c00c2c41e071a611 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 133595737 1250 133594487 133594493
    0x405012319200601030302122506241e2126070c0f030209070f020a021203030f0a18020f180103030903050705030706080a02130807080a05010f05160c110d 68
    0xf410b09110642c014820410341340040080e0000301c0f50702e1448216001c180e20700038440304100001c1140100e078056580d000c0080740c00c0d104000500c0039641052541d0700359161540019240c802050701d00720620900004001c4850640d0b00c1582c1001c0000d241d88206441e030070982d06000d15140007141c2212852064020720580c000100585440350401c6d4080c991a102c110111500d507001c000e4000703420304007040d060707070007529406040c1c61a4812500c100e2100c0e400b06941904004200320140d00c04002e2103110552034100b5035100034039001c00c10401700124051100b08000001c060701450840c0740041c1a900da00510141d040180b40b522500340d40d4929004052113118441a1020b0190742408610742ca00828844100d40055030394103616101c00c00d0a100950048482e468559a4030900042e143c2c4148500170090903c00d000c1d00c400461400c1c07003802e6070120242000c00c0d40c0b03058100b100b002001109045141d1961810005144007403400d0200c441c0503000040d03000c00740782101c0c010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 133596987 1250 133595737 133595743
    0x111503100f08120f160f06050103110d0b06060a0306150207031e020a050609030307051509010f090f2a0b1b0d1e0c02060f040501231920 60
    0x11148000480d003600d640d2110010780f101d540c0ba2054400040c01c2006185400e070400c003404482e9003070700aa403000c94495480c0381c0003481c000d00c1101c0d40c50b101c1004009100d002010300c000c000c4140e92941d02c14800395102c903500741000301414400c2074041200303032001e442940020702420400440b00e590381c41c0c6c81d0000c0d550f03050700d2204031440026448821600010380c92040d040c1680505900501402c4c01e0070810f103500701c0000d90b50544024003140c0c2c041441040400130303070514000040403608090b40400d0a503100401c408042c0b41c140003030b10001440c1c4144810300c4a070802410280710310030749a07006d0900c1d940e0003201c40c00d81e5540c0d404203100c50045c0040c99000328089115040d0200100440d8650f4030742014940410815a820b20703550702c40d20240c440707440a501d0001d13403ea40c0c0b0f90003d0000c0d004850441e201c0c090108044c415540c004a0400c0440e2890100101003e094a1000c243c0c0c07051404007400b28220601051050b801103034004050b583c000194401140040c1e20703155 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 133598237 1250 133596987 133596989
    0x3090f03041d07020f06010603020a0e040507120b0d02030a0228030302060924070e010509041404020909030f1c0603022d0603090312090a0605040b25080411150310 72
    0x1810b01c0c0403507815030000414000e188550b03805090181c0c83c1803070580080d0000d011450600a4480605c045907880d8820903108125646030380c121401c140e0a5042140c100c002910b00542a40d114040035a800140b41000154101c03101743c0381030482480030130025031142800d01d2071000b08034007204241d0007203807062041c0c21700e81c200d888502c05040344176122114000780340700305040b0320089440e184c4100d091074070241043c140719141000c40310200c3d044401d508203d03481441000c0902003180340031204160808102d01c000c6061030a01040e0603002e2080c410300081c42401c159241403159403a811070001103070014000c0030350200115800310001d44840d920f458108110341402c001c0e02c1c00400382c9018030301c18002103007082000391200107a00c41c06000301280f0f201d2909020f001546074000d15100340c1c4104070340115400c080801e205040705000280849840c44850700814690101d5070039803254110181d8450340c0d6200000c02c61140400c04506414107000003049031510208402c14 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 133599487 1250 133598237 133598279
    0xa050409230102120f040606030b090705030f0d0219060e01110306040b03070f0512030915071703040b0a09060e0129060c0a030f022a0a05220203090f0304 68
    0x8a50500c281c0c00e168201c1c456034410005106005020500001c01200130301c1d4401d214840005035581c032501c818028100450300580c6581c8100b5040c0300c0d60a00307104040f10000220018040e009032800d021b5110b031000c60410100888000f081401c3c491680c1094404a1992008201450854820082c40d44c03048400724055820607204919038100010240100c51407100c8140c9410700b030104020314080f00b004020600d200500400103180d4844101181410030440c9040c0d41d440e040c43c0440842e84424a40c1040cac210500402011130610010a5807054402000007076090440c60304100401e044541c41c1c034150b103445d100c81100e061000840030350704215090460354121708030811201d48916503200e9100d070006164040001c1c012071481c0f12091042c01651580780707810035051790150101811400d81d10208038022020f040012541000e4a0705803503c1c1c3c003d2104104c582912521020503c03842540000040e0b920748081c030000d14843e91902c1580d80e01c40c0d40d45070416200e038410180c9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 133600737 1250 133599487 133599533
    0x3060f0102070e070203180607031409190f060207061701050609060c010231180203040507050d061e0b0105180303090a1701060b12150a0902030a0203091b0109030605060a050409 78
    0x258214504231064401e0f460385a5500d054000b48903581400d681c014a05054020b02165441c1000c020840e4071800a440c0d8000c40700c50044c60070b00000c1c64072500d03503c4101807119101045100b00001810700d819078209a80320ba55680c1d000c40031840ea407058150b9010075500c040b81c40c02040041c0510144000143c00d040c51300d11120704860414107210b482215079020b900b4051050040c446d8000d95032143c051001c3d2440d607070343ca90103c1c0c040c0b00c1222084559035501c4001d80b5100c0c2200724080e031441d103c010104103280e200380002c0d026102e180201c0381d040300340c60740c0b44e005540c08004440346501d000d0200f0019581c0c50b940b0150300c0f282c080c510300032542040004074401600d00e00f030342c0a8014000b40094540ca6102e078244400301e5507120140c000d20900340100300d06449000841c064000014010380d0391501c41d441a052107004031007185482c507107604140c9280e91042010301038a07000000020142c40d043c0010310a4600c42d80240e030080e0030241c0c40c0f4248820664a080341110741409 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 133601987 1250 133600737 133600777
    0xf020d06080c06070b0c04030b1602010609150e0a0b03070b1213020f100306080303040c08010b0102301902070617130b04060f09050607020c0102030f03060f0102070e070203 76
    0x45500c1d07201c0c401d607103038101c3c00a2000f1404918090300640e040401e00448a26198032070301c9041051b80211204030848608000b000c40050f4244210307002004526020480580040c0d614114580d9501c0f0b9644401d8031040406c0151071a640302c02c82184009088818081d961803590045421001075903004103070400002c0c403401e000b00c1200285079030080000f09245941c10400a10100a040030301c00c256842e50040758500c42000210702890080900344916494501094252110000780b203045403c0780c1c0003031510110303e0700c4d0780441e064503d16403490074803d4003070704966000d00810020456071403c4400300e038540200340c0c0342c03d40320036a8803051a07000d00071000741001003c3c2d540800070740754490100d010a03203c40200340c00c00c0c0310720b20100d60025010303041800c0e54807089095a032500854280005d170b036010400d8105040f000e002550170540305010744405800020003c40c000c120f61a000c5256038824803012010305030f1004c0c503642a00340300c40029a07981214025580031009800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 133603237 1250 133601987 133601999
    0xf070906020c06030a0c11010c181202010e010f0201091b031202071203080a060902071101110a0201080103170f190f03060b070f06060503100b030607110a0b07050d0f020d06 76
    0x2ca4400010780070340003c0c07641d11343c409100300a10343d8010311420060b2143e12104c00b0903080c0100d09080702d1540c4d5091404002e8800d09400d81c4081d40140465446081c00c80f0051342c0022400183c05001d0800d04043c0040c0303030061b409401603450040c0f80e04628569000d0f14081c0d46000000c1d24000d007041300c00c840c11030405981d50201401101a294000790855000030300c03c41405501c02d6985001140d004c0c3e460507200140d8000c12403c903080c5441001d00b1116513032168944411021140052407110600c1d000078001b0841800082c0c0100c2030110090041040b5400716001041c030079490b15581c000c0000200000001d201c611800100100f000b141e05920901815040e41e5003108176528001c12540d911101240d40281200c1700c546447e000a0319603410301a0b1198902d4400b404183c1c20254400c16041200080828081c80399482001070500c400040201d8000d501061aa0241d00c440300c040d40e8601a06502031621400c040404820300303501c2c0c0203004c40014030a0244a12500c5035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 133604487 1250 133603237 133603243
    0x140412080108070e040507150e190f050f0409080708040905010609051e01020a0c140307050d050309011409060403060b031009120e0609040f060501110307020f0603040311060f07090602 81
    0x21065540300d0788100d0040c130001c2201d040c0c450f04244504200d0f0700169603000040c1d000c2c400044141c004c20300b4550310750480d05042481d00041041991122101c030708094003810000d009000f594010b03086c0170765981058580ea4001502c10781c009180c1070702c58506140c0100c49a12038001c41800340c2c00c11000141450145014806507000242001321184440c036612304034a020301c5040e0b04600c50788900d80e0208001090300c0002d011000000540034407000145441d01101e035100d14002c010401d1136101180c0003005941c0030400902e08603070000000790406100b400788043c59980640c0000e0004204900c9030f000d01000c01040c0d080e5a001c044a40c00b0700e08031841e40301302911030f4003107940350007246111745401c0a9030300c40106201e0400311b221010030121004041d401340e0f8196030746400c3c4070b01d6070040002c010601d0001c004515010985e40030400c122500e0354400d0040d01c000c4041030816000d00390039070980030018111146807800320a10240030f0810b448a2001c107030900c038041003852002c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 133605737 1250 133604487 133604489
    0x1080a02010c0204090f26090a030303051f0e0103020108180604170408010f141605040501080709090f09110303040806060f0102012915070b0703050901020d1404120801 74
    0x4014122204458005444442d803210003207a00c0b80c4e4808042000400360205401054041c0a80f62035035000c40130705a655000a1000c1380d8000f201303100200792507131036050140a6a90515020a05481ea10340c51a21105c502d40910004601c81c0404110100c0b41d6000c00c0c102c0c1d001340d031442c0c1c081d01c1e6486a210060f65032880900d068021000182c04600e0421502003044039030601180781559444129084820b02e10040c0d48040d168142011100c56107031205801c11840014884284441d0070003070050310503407080c036051100440c005080c41e801041070718000c2040110510040101e600d20b18000d1841c05000c4416055a801c0b82207981000410390341034176003010007442c858403600c2c20411443d051400140c1159240c9081d00c51015450009410302c0141c03045038a02440c40d542084840f01140043c07a0300e00206001c2c840100710082c0320107401003224240050640c6a5050b224064030800300030031507460a03c24203503001c449842d51140300e035004171007075038007194662411079400c042 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 133606987 1250 133605737 133605749
    0x2090108060d0309050d0501050f0603060708150409060905100c05090f1c020a0303020604030f0503160c1a0c18030601080c01180306050721050108030a0f090317030103051501 77
    0x26030001652a092044124000b14007034102080d441e980c4500042452070750060449169441d8000d01c240c01100b010280d801c081c0c02c5000c2e01c8a40303400c050003420800c009082c01c2c011745410300d010060361101e901545500790405000e000c6e86180b424042d0b9181404c0e400c80d28030070300c4c0820040120f44294140e98800d80300800c12194480ca0004229010342070b214410302100108100070011f80e107110030000194801e402800440c6080d00300508111f60b28000750041c00810000c200241c03002820003840042c46017840c14591030581001c6141074051000601e810001e02c081c4443c0100ba940070341103210340c52148508040d11a000d05445400030721a040f40d550100c54054000e60054500d881045054080311462507074985030001034460598120003ca421441000d1104102c0480ba82012814100030b02017540751149007607480c450000000b04000c85c451040000e42d00c0f800a1900450700a24a134401034081c046c256882d40c028401141d071440703040c4031a6080e510303804103e030407504 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 133608237 1250 133606987 133606997
    0x6170f060123040918030f0503090a0f081303060605040e0f0a0f2108040209060d03020a02011b15020a170f01030201080615160b0601030b0303030c0f040509070e0310020901 76
    0x200d606031054802e104925032905441c0103100c0400c0644081c405d1207810b030610550b03810502e406050240c0070180000030342082040800810840da10005808400c0c241c2c8034200140c070f00000d003410000c078003c00125a141c865070900000c18402c180e00b00d0425504100c408000384c80c50151890790303d803c0c0850401c0f043e004011440c01140349a291000342500440801c82e0060000b030001c441d44c09c03000c17a00008210784005120540c1001042180c0c4050f050302c0d04c2d40321080c2910081d60742c1d0a1128028104a45c40001142c0d4442040d4058200b0f68448804824500c804010390041e41041e150342000440c980401e5140f112002c00141c081d000c0e10300c2c03140459085800442d00c0700802046250094140044d030091082c03114002c0030340061959041c40480300b1460720085800001d0210b074101810701d24040800e0b5404000c030f940112144080c079607210031041090000d401540d110340d0307000741020104041c20b5046000d10b5041c482c200d0a50300500c00a94488049000702001c95000071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 133609487 1250 133608237 133608257
    0x1e090513140610021f061203020d030b0604052d1009080609120a0c05010204030209012606090c0d0507120305030403030f0c09050402070201090f14040b030a031403150a06170f0601 79
    0x4003a5401e090000104402c00328807991903d10b440961f0320b1804080300181c2c050ba40c4058a29494401e90f034074240219901e6103858941400682c401d01607421410394410074540a00d20300e17096141c1442c040d00050015580504195805441d442043c07081060600800000410009010032803e00c0c03000d10704601820a070345c03482d04071a65242e010080b600c540d0300300804005070b600d41160f14001c00700c00608800c101c42c240a1741481e405030b41040c00b101d074401d074203202c0c482c1c00203e450482d0b4441035075919048655401c0c2a0f140c40340c2c652202d00001040c49100d03062542c41001540b0580c02620203121038a901d0010808a6030240f01c0c141c00900c040609014500d0503030018190315005151a003841034a41040080d0460a54005c0c1c1040c0c25841c100382c46170030325001f1070491101c11000703848956040d48024010002c0c55283e80b41c185400030001f50310003912007d4049140c40984403240300d0352980d03030140003030300540684619042c2000014204903600400a4821103040e5038025240b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 133610737 1250 133609487 133609513
    0x308060a091104051f022805061005040e150105220606020a0b0f0601021f0e07090c0201060603021207110312090606040e010515130f15050906030d1e09051314061002 73
    0x1a91360b04007c0000c400030900d900c00704604102050042e240120b54000301d0b8581002c000c2241e04031103030010250003200400c101c40c00c00c58001411542c0650310611080c2c401052099580402840d403107806150410114003070b0303400961610315500c40c520903401c0d034442c1c40d02d03400746a204440c1240142d001744d00c0040f00910f901018143e84a25000205200340f00401850034103810780c01201030580c0d00c0080c14150381c7c0c2405940e000340001d040c11498203900803080054608010400c0c0280280c22401054402c810000c4a03040c55200d0802c401500380151100d480b002d003580e5051285080500d03549004506210b1580100503992102d0b8000490ba4144030760300d442061a15125666007031040311020240c01001030803172090341d020000500b008100101c3d101c0150000b406903000510200da01c60300080b20f01c00303c9241d00b030f8038080400c02400c1140c19aa0036048290068566840d141c9102480c0d00101001c0d070500c109030b4480d54804080c040810043c186507001a440b5000e08128 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 133611987 1250 133610737 133610773
    0x9030906053c0703020a0209100b0306150405030a060203010612020307050712050904090c0e0a020406050706020705030f04170606240c160803030709060201060f030308060a091104051f02 82
    0x701c00e40e03420845000341548802d00030390001c00741900560440340312a02180340000c8481c0d44408030f03a4400c56a00d0900c141d45000b808000e01050054080020403941080e9000580c0d00802c0018200d030519001e914040010307400038401c0f0310100d00b100112000f00c040d0340c0240c901c154030300d07a2400d00b0007030a920f402da084200c0d8043c10050000401c6016610f44075801809540d601031060218014034042d64803c160a00808a01c3e40d54418002807001542c060119448142c100801580710049810280d04505c62138113540c02030040081c0c00100f0405e044e2000315000044ca060b554503079220b4090240d1070b94000208600110300c0b0250300400031240015101b082d61050460341824003d8180c014094a5500404e2035a4400300c104898986e000794840701903c00c03440244581841d103d100403000d502408001c0c140032050300007402c02d0302c59110880c000d02400d60140310071a2075141d00c910a0f030280c00703840d0040721803000c01c203003114140b600d128240341c0b580d0040441d03003507142000ea2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 133613237 1250 133611987 133612057
    0x50f040209041d010207050f06040201080609040510020a0c060f0b06030c0705010905010f0b130c08010b071a151509060306101b03050d0b0d03021c020c0409060903090605 75
    0x142c0103960710304242164100908103050300c2421800103030f641400d4100285081d0071000044810382c0030008020050740c2c0040040c0d0413a4095803424a15101c0c3e1a241c1d041100301001100f41070700c08644a4540b40d4058003800019000c1c03130042101d5440328480400745d80c034280145400400400c00302d409900c0c1e6600412500703019a0001510f074180340d0b81c042c00e4500030401040307000c3d2501481400c40c641a203109107451001281045504030200b4040c00c1004144940d0307100c0100070604e8414000c0704240c0104140b59011002a02d29058210482892480c500540198004c0220002903c035400880c1d00c4450014130103411a52001304011202a0079081a000c024001030140c0074060310000741d40303025202e0b40301d440d2103400e030081c501c003252440c094a500c9908a400d4407800310b46c01198420702c0904591207180203c80c10074090340744c04501701903242c025141c06204001d004603903102c60b056921aa9500d00302d2640c8030000c0f1034034080c01d1a039071a40b0b03031100006031195a0000c9070355 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 133614487 1250 133613237 133613239
    0xd15120c1a07050a080301032306040318030203150a05010902040b180301060b0315030c09010b0d050709051206041202010e070e04060914030d0c0f2c030a0c1e050f040209 75
    0xb07180c544581d0f20b842c1002d00c1000200c840a00100c0140304020300f01c040144002c5155541c600d0504e6419501c0340d81d0b4070084c0c40074060142c0170700f0800d5102180d034042006160041c0445190002e0100076541d440d0003203500107001c501d032030b001040c4802603001725811a10070008441c2801014403c03044440d811190003980756607242000030780407000d800039620521580000301000300070181858103041e100c5c00000d1084440f6001070100c0118281984d80314003060500241d45d5a4202d402c1c0c44104547e0041c941c003031188007000c1003082d40011803502c2a8819681c07062180540c620a9003071f1204900900300d2500300c41c03428040444502e0031030303070711034040c4002041c4c0040907141e070b410005415082c948540c100280c005840c480c18007c0c080e4815452a100e11204460b0000810340b440d0b400d580020719840c0c40c000d0160106001c60001e281c07200800740d8081140310b00c0c0100034444a441601840040280911042500d54030010112080608034081c5280100e041000035030004140c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 133615737 1250 133614487 133614539
    0x3010608010e1006080c090c03040609051c020f010612140313090903020609070e15030705040e0d020f070b040303120213090204080c061c02091201020d15120c 70
    0x40c548024020510291403070b1015029000031001080c05a03a22900620555803200010b80340680341c083c1c181d81d00800c240c007210707100d8581d4503105001d055540d1014107076206605044460241215450030001000d030219400c03680d00b0001282a49c0312441011030650380380829801080c9002c0d5404289401c040950f40360001903650700180c890b0340e8201c016070705e680b0b81002081680401105400024050041880c40e00d4102c105680410080400042c000c60840c80022600c040250001400e4010400d00c00180541895a40c6481c0c00c4140d030300500c42c801c40d4000500c0003052040c10f030307003603800350521707050554a007071700c04580c09031400e40401d07400c100c01c40518804608030406080003800140c0d444e85481c405510f03280c40708120a1250908010344041c10280307413050840d8070303040300300076131601c0c1d0042c0080c8491111200351001d55000154589a100803a400340d2841c0b962a40d56608617901c40c903691410262040000305207154540f01880703103403111003002d02c00380308407000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 133616987 1250 133615737 133615739
    0x101a071112060f160206160f03140a0e010c080906040605060a0b0a080906010602070f0311010e0d0c051003050f180c0a0905100801110a0509060d020f030603010b0609031b030106 78
    0x8158544a000c031031100c02820f042c0280181d2200706410740d0400c40d06440109403e09000d00c445a078000701906003001d10103e40640da9225020340c000c8900c0580300b92441c40c4900d00301c040c440c040c20712010074000075480c2405000c091401806060f000300701440052110384c1e210342e2442c00401c07015240070b9004203240300c0003070640761131801000d0107051980c80e07440905228403082c2c9010b4041e0032807010f41d00000c00c00d0150404940d10401102d420609c0040c542c1084c80042e18409608005075800c440b001101c207082c080c002d5854011078400356141c85c040749442c1c004504130760046c1c9180010030351000c00f00d40019480307000b030020000c0850030303500d445001c14006030000106621226803283c07241d08004040301c60104d0b407030040048400a008000c401800400148210500387d804d1120111340d11886e910b41c241074560000002c4000c540e40c800c10b0f820705405801c01c03103100e44290308098110001d41031180c117461a00001070010409000501d43c1c4054070b000e1001015003540d0f90f404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 133618237 1250 133616987 133617019
    0x70308100e0106020f0c0f0312070c0902030106020a051504020108130309090c09080609060708041b0f0b0306031b030318220b030d09140402071104090308101a0711 72
    0x7244034001c008980007410b0401c1600c000b1401c181c4d4416000c1e02c2074404c0c41075610700b5200030840380802c06904618981d03a00d114030303105110318090703004104500e20200000c5504c1d80c00140000e08507005d48100c600310700a00000d004666411a0000c2c00918020040f80290011500031100c8500c20b091010203180c451f400b07202100e440c075408500269444208009101040c03203529040003048020709601c2c5001080030f0b000d0000a00010800400500c808055000c0701c003070b410142c0b5001c589442c40740d5603142105850741068590724401c0c0158056134a400ea2061b122005250024001e0750400450001203510b607802048482d405c04520301c0011999211000145c103401c15521001a801c4405402d25141c0121481240240048003100380400c1042c401d6403543e1000032900566904a00d2504120300e107a0041001c0d0403c5c2464007540c10181c1103011a0301c140074280440510300da40e4030b0b0041c4010421198540e052030b040000e24042542c6002141c2d076050090035080c00040a21 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 133619487 1250 133618237 133618259
    0x9061602100305100905010b090105210112140c15030c0d05010305030c1c051801110312070806040606090902130e040f03030c0804033c020307060b04060b07030810 72
    0x841c0c4000000d59401c20420301034400709044024000d844010003580d13040c000000342d50721483d547c40f4103011010811000c00d8408084283c60303400fa1020560741960f50b02c040245100525000301e48200440f68440004000042d05010141001b0308031503a200a2240c5044254005496031080300010400010a400d403406401d0085200d50003c56a0300e442c00826800d00c05009400d00054441c1c0c80005c25850f8800165407400340c4482c900d40d92080e038500181c0c1c0e448800081d02a0601000c181d200c14030a00b00b4503644200c07150748582681da941c02d0b04101c01c40c2c1050099001242480c0814041084a0341c0a404049489005109081d813039090f0100420000c0b50201ca50512038101c40c010154036001e80d80041d051401c003800541440e03500030304800240c081190a40303851030b002c0c80e50104030a03000c01c918829003d82c200d941d8090b80c802900d9500c8908160b45050412210780401d051506ca414110b829903114581003158940e000c0b00c0300c0002400160801e6100500800c290b1010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 133620737 1250 133619487 133619509
    0x2210607030903092c0114010804060b040f0905060402010305060307060c2a0e0114010302070f110d1b050a1d1b07050319120b01050a0302071b060207030203071a09061602 75
    0x8617980ca100d95603150802c81145205070002d613030b07850582c084039040b41d0708940c155070030a51004012503520201b00219006002c20b014400c9110300744030909050041c08074400b4002c5d4002ea07400d01541d40c0d0704041c107568048510034003000841200c0310034081201520484000000d83e981c07044624108080705100c0c06041d04902214540b80004000c62140c11940d45100b62007820150308003d11034840c1519400340d40d00203001040710344200083e50341e038a40e4a0320f4840e48000c0c43d88142c03c655a40081da03019900a0500030008400302203107840f84000d25120454014041030150343d144615854060806011a001c1c44410b0224200140c014406414084370482010381241c80001c0020100220b804140c08001d242c00c4950520f660311070111004012907040140c0c0e100741d289004018900412004080880741c0c0001003815540480c82c0d10480340200e00700c1d0300494650b440c084006403c0b8a0710011340c0401c129650807400c1c0000a401104a2000300328094034154000c03512803000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 133621987 1250 133620737 133620779
    0x1090809130b06030115120b060d0b0117150109081b0d0f050d02010b0a051027120510110406020619091509060e12030f0a06050a0603090221060703090309 68
    0x51b48a000242c2c642c00701070800c03107405040040c862440b048020810303038825264400f4280e502c4500780c100c980d008074203074490030848580d00005480c2000300b060104241c09903da0004203400d80c001484d402c0020080103440482d030075080d01c1400407003001203842070242c00715484020040001c0c0420f0040c4540100704c02c0640002c102c41c54440e0030440c0c2090317580c1100d4407603c00c14a01828072648102d040c20340d00e00350640c080d244002d0901207214141c287c0e00400403603003084008020050041038170041510880018040c80031000c0c0d80d90080c0c021030041c0801640001c0000e401e5003884008843c1090050740c001450340c51980b03450501e4043c140d8281c0a154030355040030200002840350800404c0303450041d101c128111071030144944030140031003103456071160200b190000e0603802100100401040310621564490020703001d400c0e580e1042c1e106a2402c59115402032420f810400015200009040c1c1965601c0c0207400400307000380c0035810071441d904003140c0d00700394668450000c04 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 133623237 1250 133621987 133622009
    0x2030a060504060507140a031a100509100e130207031b0308061503090d03050405010e0d0903030909020a0504050d030e04150302240403020105072f030f01090809130b060301 76
    0x160904000003513440c0035042070100118100100c030025252030603075100c40218075010400201c20b4041110710300403e0a40c030761254103484c0b090b40e11900000204004003094070660418038105405a80745564070002a8200c0d000c00b00c000c030a41020360042034035901c03a0520b01c8a07280302440c41d04d245042c08008a000c1b4010b403090007040c0c902044039058003103418400303500d1840e00c1c4440039102e0800311240c1d0305043e110b0b0302040812000703410901c0c0800c50142111298148500c0092200340d462105501081c2c0a2101040780c82003802104c1841125403626840c01d464201448690b090400090b020884e0081d410f08569a075030203940d002034000e6504100c1c1c44e040d401000304000841050080d03a04010340080300c8294003606031801c03030782c09080583e00d0b0000f500b001a846444079031015501c000b10a40c0c64030038081a05030032600300c016004c950482003045201800c940c018440605480c00a0100f0102c030303d460b130002854907800b0718003c5811500c0001061050b0000e07000310000c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 133624487 1250 133623237 133623241
    0xc0705010b0904050309040c020c270106030c020d0c02010507060908090f030105040209161202030705180d200a080303040510051308030105090a060503030d0b01020d23031302030a0605 81
    0x8400d000e8480803410803074009540b82815a541a41c038460300b11203500403919000d081000c0c0d40203100c00ca120040191074520303400e50304200e088a030380301812644d445e01a100004907100d8400d00c58907100d0020740d00107100310108038505880d0b02c072039244100d0400c03030304011200004001e805078a81c19031090002c2501c981c00c00c01008841c40820b582980030340c3c507080810015a59180302d060304095800307c0724541d030102c0642254190803e0200c002840d000106100400d40d21100520080044a10642c03441688408200510b0f18101c00030340303680c3c98441441140340110070381c0043c02d100102074111a81d541d504160450700f089500352042c0c0c02c00c0b425010348111602540f50710503901c41e007201d440801c95070386200710301040c003800340a128004001942d14030710758068005001c3c02011a138071080d40c40050340c05440549606c6005000e508840c0300000e004400d40310110803030741c00080400f1a4080e4051032070300014541212021406529005030314148044400b45000c0d082c04103180c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 133625737 1250 133624487 133624493
    0xb0d02130905061b090f0f0904030905150406020d11010612050606090a0e060705070302010b0925080601050f070620031e01230f100f030b0607030c02060304030504030b0c07 76
    0x30150080841c540541c60148142c00201200c4c105d030b690034070469064a100a60202080000d00d1564519800007281c0b030a00c030601d034020004604594084a079150b50f81e1803402403034854003482c40303404090380c040c1552848883c003800380c0b0110310049000010f0100c0d55040c2e0100c0d2140420f034241d546401c5901401540c1c203181100d541d2143c082035051250700d074085041c95032844c0051101080100c041f80190805200b900b2002115100038003200d81410441e02d156001d0460750b0075600051444e0501c0042c55014000861241178146c54a900308800c42d55018215401108111021543c4054900581d940c606006003018500c46e2030f5a124545004503080a03012180204540d0803840c004006800d85413a022000c80103c040085418000c000400c845c95041078400c0c0e480070308071001c1c80d80c1d142d01c022001c2c0e103600f0680e401d100211420301071000a04c00c0343c00190000ea071004a04015042010085420512901d405c9203000c1d500d484207025003e040d41d845059030b50014643d818 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 133626987 1250 133625737 133625743
    0x6030b010306090204052d131a041b0e0a030501050a06050109090b06041a09130c030605010e0901030212032209060b180906040905031602040c02070b0a030b0d02130905 74
    0x540f071200c0703086252504110001d500c070350712103000b4809144039111100071220540010110404054a424a012400400400609040ca1032140708a0000d4007032146882c241c01042ca100012521006031420600000c45528890b0041907400002c2c1c00720010001d6424480c0e10b1007450f007408001403280c240030005140b240c803640680c80490415801c0e922682e5603404484c01c490444a1340b030090004120207a0060243e40f240726030029400120b42440d01c07054010401400003940c0403c000d0303480703c0054401c4041001c03a66005a0305c44010f00060420014000401c40c2d11403c49003007050480c020a07021404401001e1b942c0f40382c032010000180b850056002415081195509090040c04460f480030381b01c0b100c00e0320aa0791741011a0130b549540d03104014803a081010b0341c0d80e820540211001030500c00c00200d01031480c117400002540d1004c1040c02c2034443c2c00d0040c07850501d601004070050403080103202e501c0031202c510740005956070003465401e60300d10400441c00e4150707401d1080c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 133628237 1250 133626987 133626989
    0x111070e1509100b030402010905040207060b0a05030d0512070516031101060e251101020f13061b0f02010905060a11150105010f080a0603140610120804060f020a020a06030b010306 79
    0x402030b9410300c00d100701c00f902e0303007038150036141d200320380c0d50b120382d40d5000480b00d0400ca41d00c601e4000c0d01c0014244240b000c55004240e20400a81d07040d18456500c50601d65984203c255200018100780807103d00c2c1c9006c000c06903008070003440d00500313014a40c0b8410a4280503407070200d02003000300301140d041c5002800f0300d100600c1e42d0500340010f0710300320b1150880380040c484d00c410842150034070012440d0099140904603020080215110784600c4134a560661004031042c2c030401c0300c00d00000701300d80304190204640071012a5140c094100d580e0b410448252440200d050000148000c10345494803000307482d42800390340d01d10700342c03c2e00c41141d203003400d00a0700050308000d0303403100621450b40c100c0001206a4039918001609580d828880001851281c2004140c804a0703605014080c90003d5404d00804102c09211070f85a5a416044040740142800a00784502804100203a90044481c18141ca0b000d0050f2000e0040e10703800580c186807690410f0010075900d491540c295607061007550 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 133629487 1250 133628237 133628239
    0x1401150305100b0313060e0a1e030c0f0f0206030f070807020d0807140d020a050c1c0c0b0603150a05100b04031518060614100503130803060111070e15 66
    0x802d007807101a8003050301a03802800390200001002c1401202c14030015014150003120800c5000b191032002601d42d13041758825180c490400a210407a03488060030300016660545494081a503a581d0b1180c02c414000016074481c008245090302580303e03030005600c24400076407881a140b420041c060f240040c040c242c142190710074440d002c1429048240070340c021805003400c2c8001c0e030400062301c45500c036421016140c94000b1580740180e94200b005001e20840c104191070030466810100f0204821400604c030010f0380010302d10000c241c0c03400d0740c2600010040c007070742e41d88601000701d0180100e0a684c14190141d40d4000c000740c00c440031000d40058512003102138030705891074448440c1c2903005081003100381d540d600031041d5110010050105194420003e016556a03403402d0802141544030f0300303010300301a0701d46160743d038071840480788100100a60252500c1641d10f60381c4590300020440c2e4140101c1c1c25019422000070070184005005844d0201c07541e14040980c013001201000e445 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 133630737 1250 133629487 133629491
    0x105070501022b0e1b06220303140a020703150905060f01170f0c040507030615050a020705040b101404051c1a0618070509040e010c020105010b040605040303050d0e0114011503 77
    0x71072640d07200850807005ea83e1a00c004660002e000c0000250300c3e11030600d45003220542d00c6050003c2a40c1040c1d085c040740c0c02500c4261068241568400c914031503484440d006800040060000039080821820740307450f440000500131480707170394040c9487d5003512942e110400020040080098184140f1410303024800604944c01c80c000e401565841d001d090390b8450703603c550000711071502c03d030300c200000e050034005800400001900038160703a009101c084014081c440c0c02207283d040c0f070b0040e100b0414010300184188101e00e074040f10004c0782c41c032000e070320100100000185031b502c80c00075829145154036a424012614500030541c004242407500072086c00404214899a402444402d00f1004148582c03580d0b640d904111228030031410b106900600d8603605074603119056100c0c091030314268000f089141d8948017060000d0180b0f02c19000021001c0000b400020300c250058001d18140442c04140c0003581522340d404d50f2402d4403071950310a428030041150291075840e0f850280c06505003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 133631987 1250 133630737 133630751
    0xc0305090f0708031b0a05030a1701080c06030a02130b03150a0503010b060909040606090203161b150f06080304030503030402151207110a0210020d260f04020105070501022b 76
    0x3e0740ba4000c076155420018180d410740005090284090312095920400f50303680c4051408001e05000d080c2c4802c070551508000011070141e0700090030014000f00200720504569400742c3c400d0180d809400c1c40c0c02d4003561280005030304010000035500501d2041c3c0e8030607a44510009002204c0c0c0303207a001307604c02e030305211880c0c1654803454101c80d1131103010b60391554642e91b181400c03000f0b00001da021540f080d10000400200a2448840707859460090703807030910b802405c5c0d0074000b9260304038001904410a0b40c01c80b000c9a840d55005400484102c4130100781542c0c1c031503280f8156001035000b139505800000800085282c1001d200d86001841d100385810450440070240203402c009205409001c83d40d03000740180381c1c08000828405a00a00c8901e1305480710300c0c000d448941004441d40131403035481d524440e40c801c05032404080307403130007000d02c0c02e941e610070462a2011b000307042a414009c04100f0b801c0800d00030b000404410105010000c0b10312401010801c1c8840c5c8040d200700341d40d241c090 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 133633093 1106 133631987 133631999
    0x30f090f030b0a0b010503041505070c1505070e1905041806090c030512090102032a0a080405010e040b06030402240c0c1504050a03030507030c060c0305090f07 70
    0x40a1107640d0003130700191154042a81c0003480c410176500070001d442102d9010650240652600c60982501030301c401d00750f03400042e19401107584442c2040030541d000014417011a00565440c24548403c040b10302140c1242e0045a114640f5211024010366038000010040b6422420821000c0b410b80351510b1070107c107200031038003802526400c030204000319090324501c1d10183c0166140459181020a081103c5500200700c11101206504404c004005440ca903d1040441d20343d5242054009442c003006085410300c682e003007510881e019241e150550703801960594002026130000303d40d282040400c080e01c83c00d00310021480e2480c1c48400100407240000c01da400c01d800108440420509100343e00400c1d82180d002441000041e20400c0140445030103454401002491036071502d05481c03000c011940002d4881040c000007210601038008205076020042058916205c = true := by decide +kernel

theorem cover : BRFrame.Cov 133453237 133633093 := by
  have h0 := BRFrame.cov_init 133453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 133453237 ≤ n) (h2 : n < 133633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
