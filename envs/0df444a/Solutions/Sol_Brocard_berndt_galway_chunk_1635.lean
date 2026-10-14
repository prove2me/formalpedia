-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1635
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:58:36.148228+00:00
-- url     : https://prove2.me/submissions/f032ebce-2338-4d8f-abb3-b4785bb9c15d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 293884892 ≤ n < 294064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 293886142 1250 293884892 293884901
    0xc0a1502060115030204050915150c19020a03050105280b0117102301021b0612101206020a02160302060f160f050607020f0a0312020d02090d05100b0103 67
    0x440d00503101a900745480d04241d28600d8225000b40b6808000004194442c01c4c0e40c6803141461451080500441d18100305000640003080c0107406424018110b0a11010410556121800c9003107078007181c403480401c01d080c0080d072020b00b082d403820081207200c040c5000f003d100003c4402e08030989446502940c0c049540803012940050680411041c0c1c0300b40084842ea013220102c80c01480c01ca80c0d480c416800024200d452251b660302c000030314803007960104400130748541820701601e841040e10300803d845014001010740b0468010010486401d000c1d0103d0019084443c3c0500c0294240e003822130195100d03c2d0800700504c80e1040d00c0e0203041c070120812094170340c001c009a142110103d05122203800c441881c0000b0280c90302072800046c1c0c1421050592032094000e40103519100a000e4240040b468500c140344d00100a10000a83c0c04a030b040c00c242c2d6a20f20041c0c0301e03030021b5a844001e024003280550030031281c40c03424040c8607000640c2d5414031142c9105201341c81c904d4004500b550b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 293887392 1250 293886142 293886179
    0x105070315061d01050315040501060203090f120d080601120e150a021e0f0f04030c05030d09030f0209040f052b0e0f0d0602120408040303020601090207050604120219050c0a 76
    0x10407940f200d19036290302c140020740d00504040f00f1505110f00c444005070488500b03a0241c0c4c090b81c800680e41510b41000c6015641c103000031251500c1e400c1c604190940c85652200008041040c403c00040e1203a02486916085018042c1d0402880d000492134554030b4540300c9a48409511400c00150400118001c4890220b100003243c1519414010050380d5a00102004510004240000c1c08686101b00c0503100030b5014210310f40c0b000c1c0c6010103050401445880c92820002255018000304d00701e08080e4005543c19290350b0842e40c0d440c10a4107501004440c01017107405a84480814114000c14820440d00020400e4900340030500d025500c89907550803084c0c1004406031b0380d42c00d915184400102c0140100d00151500c040a001c1d48a080001c490440e5040310114061040c140c6c10401d960141000b140c08620b80300003519003945d0b80030000e03c001c003c00c400c00c8041c545244203005c1c40940e250b0740a44042c660156180298544101681c514003480b814100020b000e461f041003910070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 293888642 1250 293887392 293887427
    0x1060c021c020d12090b1614060115140f0c0607020601050406120209191b090828140f0109050c09072001091a060f0108150103020d0e010507031506 65
    0x4005444c1c0d00c1071450700311008101c05110a401d80003615240d88402056a1070000c5140202c424030b0f4980180c5038140111030000c41c0e80711038010b1106100c50b0f66034a840c061182030240203130003411940b03045e510400441c40c0540c01c2c08154402001c0d0f0020f44240540d00903000e035503150f0f0321101030004031a2940b095000001d000c000e8640035003441070189812840b52007498070458031502820b000c0d5400e00c544030341208501100b4101042d0300c9810b420103002e01c0e00181c1003000c80080c03c00340c90300c01008030030707286001840700008202d50841040e40c000000703402d50b0311001a4040032402024207000940f0036014074000580e0364601404610300ca41c0140d11041c82403200d517032610b105081c8a40b6400d496650701c42e140f4000c103195203001d110000c80c0310008500c0e45491418030004290806240341881622814891030305545c1c5642c522080342031900680b5800318440c0c2c203010349900425509554680700030f2041c50799042c5c005284400040c1009401c25070780c0c110407a201c0341c4d0411000c81 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 293889892 1250 293888642 293888659
    0x30609090a0321150b03061002060105060301150c170c0d0c05030a0f02070f0801020307030c0f0c020910120b040b06060f04090506060c030a0207080c030307050303010e0c070b01060c021c02 83
    0x34111040006043c0e00b1810180004502c3c1c0440700c00b610f01c28080d00400c0302c8080100400046161110295a02c14041e1001c3c0040d0b5161070042141400180501c184040d01c9c8520000420f1146c0c0c000c403141c50300400300d170300e5401c40041c40300440e038007038202d0b204940500d50000d010140035100f034a00f030301c1d80140110314203141a10b0450305640c945040c14118041e1100000b00c5034111706c0b000021746128400181e80e400c10400103000c540c5148030316401c0c050217204414140e500a00791056698054030b41d80019540d01d103002c888215650422001401980403d034240122800b9242c8254481c44100c0ba05841c2c840421189008014100c0104001000240a203280c0c1e0b802458100c10040c0c402c0c0d050503040702c401c50a41c1c220b5104440141e00c01401005801001c110190549034150055441c0902e1a2152901d07807205005803100c112452011429181410301162001c94000754403201c1561a854020301d01c416810090344601c158114040340000fa540c0400b0392213600034003018 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 293891142 1250 293889892 293889917
    0xd0e01080103080711130b03010c1e080414011d0c0102071206090206070807030f0201050c03190b0a0306180303050a270201020c090711210307180f0b030609090a03 72
    0x890f079a1204108036452085003408041c151501001241d801041c01408183c540441d000d150864032100018020031100007900c100000c4a00040b080080103032420640320350f03407410020324880071880405a10341c80c0c510b0740080380403c15007442c1030000340c0e02541c0c8100c0c03040d001280e69180b00d000b41c0000d50103480d0100300107001507000801944c80504a181480744585030000d054000900681c04070310240130000000c0d5084c03261301d85c0644041205c9041d03003402414196200179014025454030fa0781e109580c425a10405a0700045078891418400e03842103410b806203642c2e840c24201c000c2401e050100f00d8071141409010351030300002480c40780c610500b05143c0d032840c1d01000203906500500041d4070441d2035400600d88918001d4844903d41c40b10940b01c0e904c3c0218000001c4000302d62180502d4003c2241c1302102c0c2c11101600d80644031861070017685801c4003d56001c00c003507c14544001072042c3c8000041c61182004440240d5213035612007440392141c2442c03034020f000400d01d8101c40c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 293892392 1250 293891142 293891153
    0x60906010b070f02040507080f0708010e060103020702211e12070f03052208070801021602090907090203040b01180e0c100302070803040602040e101a03071716020d0e01080103 77
    0x2c2490b20700034098036031800a1034000c01d080f078070103880850000380c0043c03c100c00c1190b00108030360006800e2400e44291740c5019030381c02e68490050420740c105500000d05000b995580d46100c428011a550901006440d072003041395200c452404841814044101403034421402107400b004810b82c4040d101e14101c403558410b1800200c1d070300106c081c441c0c03d2180c1541e2200710304850030007204d540c01710300710300341842580c6107420126130004116a004101024544e0400c0204004980d41511031091030b84542c2c0000382000c1446d0081030f051413011041005001010070351604803003070100e44c24503680f20700e4010019140310454010150f8088070150800b4204a100d042c1082030f28036005050946039a220400ca51041e02e0030303111710b90040b500b03000c0090314450031070f00191310030075903004c0e54030308288c1801c48044929030b4414420f000c000a20030600842c140d5254041c180b00f070018600d0f04420b50200308034945107030001803082c0a00c600341a400b801c20100c21040584030340c40c940e072956851 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 293893642 1250 293892392 293892397
    0x6081516080a090611031008060907050a0509060406080a050c1008130b07090510031406010503010305070b09150406110601080105010f050f18040302100e0a020108040b04061d0a030908060906010b 86
    0x1196100c0d07444083c44001e0318101d006e175024001078001900501d01d48070281d4a003080282111045401c95482017240341d464407140b0040380d800b910710048558851000500a00c12688000c00350b000d18840d2204000012a9144a040084509290150700c10508440d00d10080341d216050800039010400400da8454102c0d034045464500b181c1c080d40c0351008640e000d82b0b02d03184600841d07140e5466805580c00514520761003082843c1c0760b030441d07145480e085d1f5606083c1c8038101001d01d0000d03091900b034542640255444200c0a806540d8a80c0d07002d0003030a4511650301d852603402600004180040c041c003c140c1240c480743c1c885d00c0c0703d0b1304260800005100c2c0d4105241c4c042a051400003101110b01039141c8202d0007074014241000a01c3d44080940d021020100d5881c0c01c10908880180c3c1c1007000950015004540e0408a64070b501d003140041010b840000740305082c2d008281c1d0369000018010303512920079aa00d8001c2503035040c3c5c0070740e1140c09460b2460160050720041c02000a80d102 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 293894892 1250 293893642 293893661
    0x10060c08090a080d0903060506100219030306050a030b010603290f03030408070b12010f03030801230405090c0424050f0a3317010302090c0c0106081516080a 69
    0xb0000003aa95204102e26180d1544406001710308111010030510138117115075648a5800d031140902c003040c50348001d40368140300d040801c1b140c0c1e00c06a44014144650312102c0545805404ea40f415134503030824550400c07092040b03100103420603501d000d00407641041001085a441d00c43c03000401110200a050b9075040c7c4119050700c4180000120b256042000500410210b580c40740d64503002c48010007844c078140c2054006d8090160108006540560003a045450b4050b040054881080c8050704c0300300f0480003654000d0401c000e000e60441c0209041c02c600c04115009c021002c0d0021003510380d81c6234281d00c10300d110b003d20001c2000b82000c0e0100c0d68100c400804118031b403074a452021103050500f2440000050043c1560001c5035691100012000141d05005444680c0c2804041e4003020501009000301d28282c08511403040003800c2c0c1e041c03c81341e00c009100c1c4a8450502c80d507204202c05191000307035031500100e0b2004581d49890040e2080c0c60b510908581e40d86559070780500b54040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 293896142 1250 293894892 293894899
    0x18010e011a012d23070606050901080303280c0e0a09060513020306060705070e0714030c18210a17030402090f04020105070209040b0403020706050c0705010e0409120507050610060c0809 81
    0x1401c14148005012114403140210130700f0513200c910906000084034a540c000c2405001d0300350041c005241d000040d2a4003030504000b086860310a000e000d5078000d0200300310400c0030f0502e41c1030701040780c1040503071156500a4885030241c6950384086825681203100e21070300300d1080d9295030400380c482c1d00150750006001d0000340c5860b81319070301c16281181c030750f102903c1c003d018030500241c030364031004250b50100100c015a04509105101e26514030036514000407602103607007155580c0d11592503400d0a0441410000d410791101940c0585a040d0514203ca0000300043c0c0310101d1f141c0f0005a034020ba40140c000030403a0f07203481406903400c0e4050000e9040c0038050041c8001660340d0200d20744074030303c600038040b001c0c101860701a01d40744c0302e50480802d200c014080d2410328440015200d04840c42441d00b080207003220004103009090103d406041d80c0329009082200e00d40040080442d20b20400c11200c16903a00101150041c5143c068400002d6035030081d0720102e41d104014010050004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 293897392 1250 293896142 293896157
    0xa0f0c08070c2306091011120d060614040f030825030507021801060815060d02030c13060f021e010b0306150301140402150318010e011a012d 62
    0x20788406020b00901c0d03105501200b42209040707001080004008000401540e0722400c103900d100004101000c50114807041000082e60000b020b0020000c0f0070904881e8060243c0e105100340b4400003800d0f0500482c004520010f4a20303900002c02c404880072116411002d14000e800c603a10b801c4142d0026640c5080300088030400780b031801e6211200310140f0702c280c40d0280c0d25506441030046038002201e40030b1104690500400485400007005c07607000c0b480c081452101703401e4200207842400307030903401300101c1d102100b001140b14a2070020005441e480c4c41541c40c43c0e41e6074034215801d110207600c4d680142c00003608007422000c41d801c8109441d18807400414007503110b4001c00e00d4058100c610010f6070503032154441f0300c2e090a20410304141024002e0051514044d004110202a48000d01d00c0540740080094a103000420138950280700b284000d000c0007810301c07070303841c00703405100e013415030580d5841004580ca40c0142d40340d541c0c4800784100000302040c2040a400e802103140401d40c14800c01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 293898642 1250 293897392 293897407
    0x3160803070c06020409410702011509051008030f04060807090302030102032403070f050d050c0a060207050103050c16121e080a0608071805041106120703050604020a0f0c08 76
    0x40d130010380007600003071300c0026014110a03034080c1542104242d1410403d10a83c40e1100c4e0344070090f070499800600b182c403a06507101d690040380189480d034044000350940510100d0f034051980c0103240a4103030080c0421026840d1a011a03d038495201202000c000401c82000118050029141e1000d0542461103259a8079000b081c2603a00403210f2283d81c940d408241c0002c0c1c9480d00210303141e5001500204511030038a143c904141300b06009682c40740400d1040c01040200c1000f00e00803071003000e08007488980d031740d44029649428034098a80801c3c20b0000068407512400140c4844c41e6604400145c50075007619800042200c0d608d842040108640c0701c40718607119019103200b040684d588003180d42c64200c0090007151030135040312005400c200c2003001111455201c0c40100010408006610384403490504980d41d01c2040d0f95820283c045442040c54240c2c555152003448945c0301400f5a0383c4a01c1080f040717101d422005004035107054603904000e0701c11521010105d104100440c039010b00c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 293899892 1250 293898642 293898653
    0x70c0905160219030909020418050702010e100b0d020303122203090b0a030e03031305240601120b090f040218010807090c0e03100204061202070c030b060105071202070f050303160803070c 82
    0x80340d0086001e40200c12105103c107609d40c81810b900044d035200801102c9050580c2d0b9441d070003512946810707662152160b40d2282d0300e1841c01085154010100c1e661807291088102d2140b20440d9010441d00030601c03100d020440200505c000140e0664034242c8560400b48420600c0d009182807030304140da9084007100a0ad01080294010b03003200f940420315000368a0451b00d00000c060548640c5081d1803801d080908a050030240c0003842401d004c040380000307441d10030003060302400c2c1c507078080d00b10414003500201c0300180380d000b540251042000d0062110074044061000c0c468180035034031000082103c012030390311000300144a40303030688044404400092800d0329803080c0c400300d5a030020341003140d990804196528110351744401e50070a0171a4540300d03041161403102808420031b110002c0d92980c4550708842003c0d40c01802e02030030b22140c1e00000d50301c942e24021290700b0748403540701060614001003034031261507403400d140e07411002607514400a50006400c01c2e00788210341958000140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 293901142 1250 293899892 293899897
    0x40e2815050702011524050c07212114030f070806210d081e04021903050d09080709110304080711121c090b09040b01050f070c090516021903090902 65
    0x750386440d84000c1b030300d09440019649104007a49040c0507040024400109010440700304640d0664540c656410f0b5402c400b440c2d42082240c003d0000060550540014800503066809114280d4031400107841d5910801c4040c801955801e0481410b10300280000c3d1251540541c4180003400011f2540207860101948048205ca010000d400407440802c26030b0344076850380c0c0d020001c04a66155049604400c072a0242d000d00040e0091000344288580503021403404402180d00404507450a0314500c2d00801c10315403030041070141d0284d004001482051801241190030098594920790b07120395440c00500c6d8080001102d031a40d1100b440c50b41603541c00c51200c04982c41a01404030008120800c12030892100246002d20000c0c0c0000c3c80300d40380680903944488019a400100c0712041c800580b001d00408400d001c0041c00010484200301250620700220f40141c40c0078402074540442214031441015448401a480b11a000929400110f0b11401160107401c040400585807200901071f42e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 293902392 1250 293901142 293901149
    0xc0b04061d0f101b0b060415030f0311070e0c072a0902070c0e04140606040c080c0d060b04090903110109030e0d2603040506060d0b07110c040e28150507020115 70
    0x7507100710400006d400d16010300a082d01001d65809003090950f40e4500c5091b10581001d42000300c0d007900c0c00ca59240410800c1c01400d603400103c040c40c0f90401141901c0d600c002800c83c0e82100c1503501840d200100d0401d03d8194142901c0000c170a820301c2280c0000390441d000650700520080e03000684400041c0005004034002c417002c526a440d041a034070702d07000000d4a024041e5243c5125042e480b41d001c00c42c0c81d00140a8201242c1d40e80540380c8210107054550000451038000003400580c6040c1c55000280c4d0300e100e51030394501807011024140c2203c145400150104400c4c846840300c1e894646240c400c0540309000104a11070583c03501410111895043c1445040000501c01808402c00183d503004200f120042000c01e069590714800050141001c0107020402009030702924082c8120314919401810170403009003a8070703d541d658051043d581c0350250b0b00340c49612049506280e8585501c0c0c11504011908014003030400c010320005002c0403c55503505412140d803510b2080c010003c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 293903642 1250 293902392 293902403
    0x706060608090304030218090c090108060a2f0a0912080904060b1c0c090503060c07062f160816030306050102030a081803070c0b04061d0f101b 63
    0x1103030410102810309640507204041c55801800108016a03078100f0f00030f80a015260264400d8540201291034011b6801c035880c1d000b003049001260315080010381c0742c869040344006108200c0e10901c100c68005083d0801420181c7c0e02d00070303a40715035160000b480c4081841c130f04070503400c0d0b4418043d10301605000c811034000000103040030740c40c5403d0240b90f002c3c0c1281c0800d01c0c68042e6084404c40e14400340f00e080c4a5041c0c5800e0075403c2d0b10b01071444071006003406002d80e80e0903d0990400d08aa602001f8210b0310240791840d102210302541e01c681134141c001c1c0c0340b0030007640c1e403080041949412500c1d4404c5a407040400100020317480b070014054803400050000010000c0e441c01070151b40d0705401c00c904551040c0003c18840754002202900554944280e035800502c0700c00b05400c510078500045c01d0820210302c00508a0740b004020011a6480d550b01038114100c10740031074aa44803201c90b180c0c003664008442810385800e4054500445d154100417003145803201104010700260041a190f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 293904892 1250 293903642 293903651
    0x18010b04050301110f090405042301050f1b0a030905160b0c01240308070f0812070e030d080f0a060f1401091a040b030415020301030c14090108071502010902060706 72
    0x28a0500340104c0105906401d603a40c100208062194114025845050301c9079442d000030801b400348560310541e1140e40f240340d13040007840304010140600000d8450120039520200000c013131180380c04a941c2c004d5500e003800d82c40d00301a80c1d000c0300a0b200707044094446000360342c03010740310480c145009002401c0c45070f400c42d203030001c7da030015084820700744565403040c3c207980302c05106610340300c1d03031005480e440220b10780ca40d07000c0d090082c103d4800c00c0d0700405003800002c09540c002c1c1078032449031280e0b4459840541d070b0140c0006240d1501180f00c0c508020400520114040c0100843c0e10703540500c1c00340e0006907080d500c606d5000c05020950240329101020545c024055a012050801400d200c00c5840094403000e803203002c892003241310b4112580000f0002c502042112095081c1990400070255102e507101d0404907086c0e41507204150462a030800010754a06240600314100c407818070141680c2031a0800e0b000c681d480090b5848115541e445420b00180c2c1e524000e40140c7d40103050024 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 293906142 1250 293904892 293904899
    0x10606090e0f060307060f050f12090607030212040308060d0b01061e020c1503040305070b040516050415090506010e04050f060f0102120d020906090d061a0f0108040209040218010b04 80
    0x401d80006050034602c00c00103400c001050700c00182d2003084480514089186c21011001140c550180005143d903000000070080c00c0f00f100805124012241a0103607521030700c03180c1095080b445007810b00c0c1c00443c101702c00100881d02580605034892009080002d00e101507544944000100342c000e00d021592804000840103003940300c0341c00f5122103000408405e405040099008031040705039440c8104c0c0000010201845032080e142c031281d20001440d41da09041c5002ca0300c9611003100b8410081c5c07e820002101d160034003c1c2d02c94000640e0700ca12041e4203086000004c0c100040030f183c14018131881203c450f031160b06c40d4602c502c01d03110407440310b41015801c010800c0314002125045500405949a0301c140305001c07148000444c3e00c005039542260b6010680f24054501090390040b2401c0c2c03644203000a40e041901c1c0a80441c11105003c450041008101682c1201482c002410700d00000c0c010700b0b080408540060006207900b4005062401c00700300b84100740c211388903003140400d042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 293907392 1250 293906142 293906159
    0x1b0d0c09091b120203060609070e03060a0f0c030204051f110f030904061d0a022d09030c0919090f08040303021b0603160804020123070c080a0210180801060609 70
    0x340c01500b800c1840b09034a505540020746e46441c0901541c2c40f400c01c620105101714010f1002000244001e001d89003549009010b1000412100480e404400c1c14100e41d0740c0d409100f44201e4050791070060070407580044e0700c207001c0030403801502e01c207060210504da44452203e00b0001616a90f14800085940302d100c0410321054a00c41d40c400f4540c032003140a005890b6004910013035000c3c01d403410045c0c40310007094030540c01c1991000e2280a81e80710002c64040440081c0040042102c16070403905102d1080c014801a810111001c0c4480394062442c0814a080c90f00300d2444140120f6095200c07150b9501d0b1101c580c0d205a1003200564002d0711034003da481c1c4402e4504003068220340503411440c09100e03140034032221a0303c600801164100280c00c580c0568440311004400d10800204112081c2c00007a060703001400643d80507012480010f03140100040c0008005d90151800c11140500360041d40c20300311a2220741c40d4000c4641000c03a00341024810300000f000300740d4403a0f200c02d00d0210721 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 293908642 1250 293907392 293907443
    0x31005040b0a142407030903030315050604050f030106180516030908180d06090b0603010e28020a030b04080301031104090c03080c0f0102030a061401021b0d0c0909 72
    0x3101d014282d001c60070055607603190307801803000c8416a0007035020540d070f4011080e400300150300815555000303d904000d140d07109850b28152032213900c4c00c0010306010308900d04412554496260703c11001c03c4240500e0800028107030140f04041c0c00403440a450f03090801c0c507460000030751f2003069522810000c0c400400d00d41c540c0d030f1a0040c181040203c0103500c61b0f50300d9104044d0b51004444001b002e01c140d54403016008100c2c02d4003da420405242c0d9403600b400406803e58506100307601300302c13a05040d000e0116014002a64062805810000102001d4040d4480d9038080c0da1164202c40d0000100d0042e010051049108480b502d030f581d8110710346007440c0c4524840d054000c03071401d03403c400080c100760300d0b0109903908000c0e41034844042c241402d1402e55001c08020320b55002005004400d8119040701c4141d0b5040001814131020307500049a0394140c07002602051004100c110226080c4880d8804035240511000c003130040e204c0d4100f43c2511a03141e003c03605841e04c40d40c03607451180314511 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 293909892 1250 293908642 293908661
    0xe0c0901080f0f0103060c050f03070201051015050301140109180c0801060e06030a0504050c030f1509010c09170a210801080c010c080c010204030b0c0c1002042303010b040203100504 80
    0xe4030000b0b040140f0320158002c0140801400d040d65890040c0c03a05009006136414009142c0301c01c1c0d524030f04010003c0c007070030701510008024070304100c012980610481d0f005044000b540e072001d007917070301e4001c10040003500005030703e05010110700041121f1625400d0191a032407040b0021a200c02a100c00801300e642c141e0100c82001064440103184d0f40d43e640481e17801000410020600303480302e04183d0304200841c0105c50345803084189103203243c840844d0b0103401541a1124044942ea052480c50917507600ea10ba042c0002c01600040c403c0201070000700c0c0151000c02d0490700e040308169541e8000c0300010242040050050402115460348028124050034041c00508001c48a84c00060318a00610b04001c02100d00451500400203096040d10015500300c0058649420b0034010f0716020f0380007190b4a480c2c0d00800f01286880394143c000c07182280c507000d0058440601140c02c036510b80c0c54030144542d0654817010704070855503c82c005103014614140300040400d1920081000710380796482c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 293911142 1250 293909892 293909911
    0x3020c010305011a070606050909070f0504050f01060c03050408010207030e120a080f09040b10030b010f020105100e06040905060a02030118150e041b0e0f091b01180e0c090108 77
    0x4014072500310001913848900e400400c0840c1c44004615204024103081d0b00802c4e04102200300700510068002451800c54000e0350f00744bc051500c0b442400181c40d800c99100e60200013500040100c584a031404080e843d01034581142000d49403003000782a41d200c6002540042c0401c5125241d61404154000742c511002004022102c1290781b032180da4044e0601c291000300011807500d4898443d608075480c400401010b9540c0f1a9002c40054020700340c00c034000b40000d011002e04040710b80144030f80b9000700c3d001c15000032a03c1c0307010b01d0880f400c90000c009582180d01d0ba400c0100280080050034020401070001584030340c100454051189001c00d108600c440c00c20600e500c00c003210b07407040d40645d0360040180301c640e13846041410a4100880710034001c00e001001c000341ea9104004041d000d440040410003c0d92541d0f00d00c10b035101440390540c2408031041d001e4105641c0030749012242120404901c40586035520010440301400312107030035035018000f40e070b1040c3c1d60344442c5490340040f40c003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 293912392 1250 293911142 293911151
    0x4050109080307120305070e030f161d0f06061c050105010e0d0803191503060f0605060403110405071b0308010312030509030d020906070c09020c0c01050405010212160506040c0303020c0103 83
    0x2502d0b03030a013454502d94140305065442012400e00c0e07102d503800b032030f540d1030150403240303484150984150341d00c0d000301d00d401c101d00d5152030204840320b000340c0c5000d606103102507941d49074a48401c1d80c1400384002d003800303601000402c03040031651094405207500003043c030030028807985404005000809004540e134401c810300b05030000060315510070799420040010b80501410b503600300e002e00400d80c42c81c0b1242e1500c040400042044100d4001d00b0340901544403d12215a90b0010300001b400341d400000c103107618001d02500c1c00d0400d94070071544484146061010300c054040081819401903078260f0018200300014402c1c03000c40b01e01200005890303c1c04000310318080003003d0f00c03030041010600d40343c1e80001e00c2141c2076507400e069034000d0390400405120780713580d840440020750100141220302c1c041c1da8010410b941c001d0043e90125a0b060b0003078080c0d400c02540c0b0100c66404500c03200b0301825940e0140c40811300c208041c500c594803031200c0c0c048490039424007915284805e20310a0416041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 293913642 1250 293912392 293912407
    0x71505090d0f02090a0219080907032a05010c020907031812051e030f040233190806031b0a0b0301030f1a0c160816060c1b080f0307020a051002040501090803 69
    0x4e9458141e00907c2407804074032585610f8110307402c202040d0300c094100d5250744040302140c0740c0e000152060007000841010403507543c100549000000c02c20195201c48088001002a0b01a03082950301c580c204e011041518400e907600881c0310b40100c0c04100181020401c8541300740442d2070990048042003000b030a502c2c0082e4030004d80980208001d004880c520455120102d44881c442c0d44070f0620f800e00240070725804500c02403038002d071015100c5424580c05407440c0a010f02036036401100082e010386100d0480810400010003402c0d1a180c02c140348402c0040c1918180000c4e50185201d01045120307410030703050469a0201c1031012171101c81808083c4105508100304803070b2100c1411900420000f40c0781000c00301400f50f080c82c0100c0c045101102d50800925a100904d0300130340e03440c6c8a820482034170031500c03102e000710001081c012003003208040100c0313072401641d40103e5a10449103181c410365101da003084400040a490780e9004034041c4115a0040d007000c028046441c002c60030402d6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 293914892 1250 293913642 293913667
    0x40801111303111503010303020c130e07090510170606041b0219030e030a03170106031103041115070303020909061203160606050604060804060c0302090102071505090d0f02090a02 79
    0x41c14031000b44264641c0f003d0103003640b00c2c802d0140001c0102e2651a80360340c3e4a0070043e4039460350b1008148240060031340c0728841003052040d0800f2205040081403158142005400213201c00341c04140409042c002c0001c80d08111102d4440307540380140074103e507082120900050360401b20651810048000c2c83ca81c080b42d0010b103211609481c000e204507070100c90708003690302184c40113003e5058000c4865082c10b254020340140540745c1055120100e681e81c03040114106c800101d201c4051120400c049004510b035000f46141140c0d00610742c1410303030224040350101780d105000481c0401d401040d07400035841d04000b450380c40320058412484903209111083d03100c0c41200110a00d0030041d1042d00d040c41003a40c00030703015000c05807150b035a4503210710020306041000c890407900b041c01c040040c0140c074441e000792940c662042e002425000c2c104505000d07003820090320b000401c80148aa05016a220030a500200b401a006440d14210700c0c010701507050740c010701c40c8802c1d5004105a107448803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 293916142 1250 293914892 293914927
    0x1e01090206070809010c02060307030902091f06080c0f030906090c03070510031802030d02250506070206070302030c010908190c030813150c0905031b0112020322050304080111 77
    0x10f51084586603100700c07400040e560002c0415001e508a40b02004002c03600381c250f400703050703420b008840c2c890f10341e41e0318005091313012404440c443c921100d00904002c0c080c01074048503040b0fa02040c0c0b0a0034aa50800c02c00c0503600b0403240c0500c158020010f11400400c02e100704c08103020160007038105942058041a070720054410b6070010169250041c2c4514803100f102d02c02500d50060607140032405840740290340d0910788003410006003d56101c0c1032105c001748840e404450024080343d0411282e9000c01035640c000f40c0007641540010410303000c101e5403e120741007866200380409921105201d1746a000c0600c940c250005200311a403001c8086900f1000855001c0c0021406986d14206443c05801d5125801e00002c0b50b01d00340303001c0862468010580a044c6ca100f80d0446809030f6502000c02040722035140481e003c00e02030300052030400c80b15001143e2010002600201042803070500c4a0403504440c42030f40c0d25000490306000c3c0300401c1c02080400c0030400140381c10110290103070107008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 293917392 1250 293916142 293916157
    0x191406060c0a020a03262d1e040f06020615060d0b15040914130f06110a081008030702130504030918020703030b1203071416081e01090206 61
    0x2144046001121a41d0800215800310307030103803910251554134503110f5034101c0700c00f1018084020700ba0f0100ca0b402c00d5281501d580c0040102c1c40d41c2c8005400b10f041c1401c0c011040c00810002c0104410914440c82c8484034080c031411008483e80c0d10300d040161000024282c205104540202041c003030150001840d48604034400c036101c1d40c1d283d080c0d0904070000d0100b501c01c5600042481031681d4885008030241c007c50312114010f00c142812449009400c2100b159404104c2c0d0303c0c085140c0210b4495421030800c988203003030025010003040d00c02101501700d9011140023070380c160100107441405092800090010000940c14602281e0020340000070940d210050701d9982c10003c1c080c1031213403407a040100722140000d07c01580c0625610065030046030298046810010306501070b007020101142100c4184002e0740c02c00e09a03a03038444030410101c0004403188103001000f60414a00c01480000b494000d00600c031003010541400c003040f082000ba60101d9250400960162b243c40c1e088807504c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 293918642 1250 293917392 293917399
    0xf0105181f09051006030606080403030f1806050702100e0a080f0d0204030c09050609040b01030f030201110a0e03060906091c03060b0706050603101505040b0402120a05191406 77
    0x395222000480d0407a541d1039400040ca07480e60000812901c00da1000e800b500000c0c04400700a61180c6064041c0e40043c8108800114028001804207200384e103d0044140c20140105000040306803100d100c24180505880450340c80c02444441030301009034041030700c0ea0031000e00c940800241c255403111200302000d0700d210300c00038903e0024211181141c00c00e007003052046444030340760704000f81c08803006d00509a00900d0312002c501c152520028141c0300d82d921400c4d440d490780c00c42ea100a0301c0041c00604074295900d49020019910302100600034400856031201c4003084484105494501d0141c410141600408103222410b003010031854a40d03082503200c03020380302e4501301c110b000b00400d070b02462142d45c0200d910030421505400c014000e1030100c003107179040740c684201c40044480d070402015218442ca20b0810150410382c00810304000d0003840141800c0d8400c0c1e46183c00352080b11035034800782e504c01c2003041310a0300f801407480c1d1070400d02040041c07080c0003004000c29007010301190311 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 293919892 1250 293918642 293918689
    0xa05030a0503130204090809040b2d0301022502030f0c030a020609040e01050117010b040501080d0507290403030501080607090303080a0f0509030309010e1f0915090c05010801060302070302061501270e0f0105 91
    0x46480035011123f0001440281c042d107000304007416901c81c81342440807072180c05880c141d03140003032002034000d49903c002005805041c00907804c01c245540010303550741e003240c0c0395007a0166001080c4a641c1c000d1841d0780c0100b0b80100008142401c40e5411421540f00e20b18100041c0a0b0a400141e401500701d030034204603950714003030700708403a000d461040340180c61031411419104070109520198026131003034a00703000c42d0f601d90200945440c82124075400054107200308001081c41045d5894128040c0c036000580d0308000c030407400503140115401c0350a50f1000007480b2840750244140a964402c000180188460011040c114441c6800030220281e03101c0500400b8040c4440424280341c0140600304070040540c0b50050542d01c2500c41ea0340031410310b02c00010414001e000715454194981d02400f141d03035071003000224507940d4240c0c06042140e203083c10f403c6001811400200440303502d01040c50989010794200d0407100c000e01c460214aa100010030076a240c2040c10100800031080c4285c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 293921142 1250 293919892 293919979
    0x40602090a0b0c0307030e0f0306191d1b0904030519020102090909150f010b2203051504060c260603010e0610080f0a05030a0503130204090809040b 65
    0xc0c0701041c0c0303410092800000140c48060070100100403d185032194555030440043c050810804080500c05650160030520002c0e045031002c0111403003841e20b0080000e500070032015505030283d805052408183d01100c021031802d02d00e02c0d101c1e07040030000c03141e0f0f030302c01c2c80d096800505a009489080101c5010b022001c0031460003034066425202019004420a14010a40c00e51351000b141111020299000105421240d07518000d41620149460701e07140000a00c2e840c0d003e520240e00c1f0303035403000c41d5034001700001d501884520500d003151240804541000c2c24001c00f02e07001c42094105112402460b070b6802e64141c1e100d14200040082451075036695080030a02411141070800030a000300d80800103100101200c14041e03c1a64088032003540700543c5c2e19548015801003e0001c1d482840080080340c0b24038000c5521007a503170791030340d05000c1540c0031a0540f404108212070616001c10740d004241090310a0545641d403c07036440402c49100001180000380b0882c20026a607140400030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 293922392 1250 293921142 293921149
    0xa050403060524010306030b2409010305010203090610050a0312180801020a0e150d0b012c31021308070e01090534090e0f0402010e030307030804060209 67
    0x15001550420301c14032140c5050003c00d590400095558031008030220360482d440d521920400054a81c4001b9403180c64903854041068035048860581c040f82520009048523241e00d1034880c000c40c410000582c40381411218242009030003016030042910041c4204015502c045e0720b0b104682e0080d80002a80540c4182101c50000300c5083d102032001103a40012000c60550003441740ca030090b03540f001e030350080108000a4100c2c0e207000000743d040c280b080420352400c1d0b5004081c4000305052030400c0c42c440010100358448251141ca91000325000c0705811f0f07052040c0c1781017100c1614074900400c1c1124001c40d8880360074240102c4070a607400306024000e460030500c2c21000d021400215907806640d860b204405003000d00403603180e2414117001c51050391031412204101044800400880d04001901803001c4050000100800c082118001210105203003e136000e0081101204d05a1801e0300024103101540b5800c1800f9500801c06040070940c0000c4054201d6407100c0301603074600030036002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 293923642 1250 293922392 293922397
    0x50c040f0b100e130b130f0b09040309031208190b010302041a0702040c0504081005042103051506043506090d1101110405060703031d0304060908010606140a05 70
    0x940e802c612000610361081e90444a45049a502291511011001c10f103030f40003902c00d0590700301d401814804005815840c0b13500800025100d8040000f00100710400180b040501a03c069001c655030380820310600c0301a0b003800c8403051a80c02c080300e81d0f06209004060f4240b08003108007000fa039546540702d4585c842d404440040c0400f28000c0f44a00203841344005a522040c0c1c100c0c4100d107405191142e05000d041075808883c10480681127000d4420440c0003d8071000344100c41c3c50901c25066070640c0503160011003c01116500056180b6005482190042400c1c4205210f4030061108004502d10072940d014010300101c06607444d038050700310481c28007101c0101143e090103038504024a4070000a10b81102c00419030798002224142c4400c80c0c2200e10540058007043c00411082c40141891401860510300c245000100d4601401000d10441a08409c05041d500300040400020703511450b4500500441d10080100c03d00e0000b000c0d00344901311021041450011800c40d05180c0a00203 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 293924892 1250 293923642 293923661
    0x21b010c060e0706030c09050a030f0b0a0906020415030c14030105121c1e0309120503190608010204090c0e030d0e01091502060106170403021b060c0a05060f13050c040f 74
    0x440e00c0341a00c0b0600035000c0c00206c81c2890010700707138810001c0d0614220151000b1a40c01090001c0100e0b0151960103100f40024000300e640b80d02e4100c1d0390006091440144010040e02c00d00a17400c1080d9a0000c0a4800d1880504100004500d207906416441c10484c1d0444d4022074080c1d258032012540c550405826000d40160b0292034408410355903005040c460b9607202090b0056280742140c0d074154101c40f904130015010001c58216009010b01075400dd40d04107400c14002e0400a184904400c20345160390004e5042c0c1e500842d00300700305245800f03150034002150a01009040c5c009010a544480b051350207400c01240803a4100c20380d015204440141c00b8006c200f600040c41d50001030344c0c1e42d03000c0c410700d0001240d84400a0394034020300c074114041c941c036a020342109426100a1290021841c0f542c0d0360260040240d02c444e48420040f82a141703200b48090805445c0c00c0751400301c8500020075002c4090405540c1c0c0000aa02241002c0880702c12030b4005041c98841b00c50300f009024069 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 293926142 1250 293924892 293924921
    0x31f0213031403131203090b0901050c0a201e1e0d260708090906030f031204200907080903040302120312010b04050d11030102070512040e07021b010c06 67
    0x4502c4240041c007100511800351268003d46507142c1d22038054581010b50351000e0b00203140803106001c000426401071044441c145481810004500c0455062908510b01202c920402000359003040300e040c510350603162822504401c01141c03003180d6401304000c0c0c000e00c0d4411628848c1c000b00400240003d0344101d24050007440c58408185070550f0702e262904d003240c0d11008070421082c0c10100c84002c0341e01469100c5115030420340d541d014452070407000b0346a29032602600f5000e01d00c0050801c06850155501c0b8140c0755141003506100c20740d810128242d8040f4000c0850329648c0c0d843d00403110f07402258030700d004031150380c0b481c8500d8150300071a00020340c84a0051005600701c04004082c1000801d4404515000d90361000c50a01d41d100314852183c01800c9180c0900105040c2d2003411a0368034040c00161a0685c83c0c0e0318207003032242400b1001c0540501207001c0c000800032031200342d8821500d000908810040c250f0713042046045256480c10010a0711040d003c000380354010190441404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 293927392 1250 293926142 293926163
    0x102060c0a032f04170c0f041e0f0c11150c030a0b13060509070309021507050102040305070b0a0914010c080c010e070303050a2606042304060906050105031f021303 72
    0xc081e9062940d0040c40b803408003441080803489030050101b55035207107010050000022102e4902400080c0c03491030300042103616009030080d81c100c0540030b18032aa1800010001c0e41441544c009810301d20b05003241052a0700c19801c84c00a441807010058004006800e415160f42e03860444002611040102940000400c00c4031300480031250072640523a0f004541c070004650705e4840440440d011100c003c0d41c807104105011400b41442d00052882038000e100140c41d250326611010300d401926803040c6040c09000884545095010840341d01400c0320781065028401712900003459130148800260805600003a40021b50b4400d62002c0348c814245d00c15580030954a04009d0015000703a68070b40042020901d950b4130080300d000600b414444d024240351003075221036040c0801044002c00300044000340002031080d0583e4100f04911442c466080443c0f603c50501c0d10344240c45042c2d02147c029803221280f010012113040f090104408450401a00c5840c81c010803c450340c40c50b4006030042c07550 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 293928642 1250 293927392 293927471
    0x905101814130e0d1d0901030b09010b06070f020f09010b191707020706030e120f0a0302070f050d031401060507020d0302120f03061c0210050c1f0e06060102060c0a03 73
    0x8a010390a00045860b2921148014001718018038026095a603002d6042c4006000107404500319507000703110343c000090b4040000c0041000c1d82c0c4001025244124100075072002c6241c040000410003c06030b901203081c1d4580041d0480c80e000b01c030355406545c00c0003004485101c0c41503205040c0204004545416420203c801035110092400f4400020703051010b00b40f5400e400150801c040094031005500d4400c240c100801213804c0134040004140e002c224807804a05880107500c500e5005d540039129116040781e001d0129801409100740f25003250300100540340e00f00e001d0341d111980542d12840204628030f0124100480344503d000500c40102e1041010029800650700c42c040903507002da108032503d031406140c11308086000b5840b006400900740345030310500c00391018130141011205860f445c000d091160b0a00021039514440e45c80c5100004140d0810180c0c3c0c00801c2030014150700e00707040d2000e1105114000888043c1034507801c15005d06540065801c90749141e5590400d9070780103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 293929892 1250 293928642 293928671
    0xc030601140f042c01110901050904020c01020f0c0607080103030e010806130608010e0c0303070507060c1104061d060d150c1106010914010911032403060403090510181413 75
    0x8003200000f1114803200400780702071105200d041c6e01603d0030b4a0050034202e95800444141d804640304503007180e0284100c10a0420034005046000d0781d080c0c03d95120700601042c1072402d031000300000704000e08540100b020981000300c8000b41003081c41d2801d503036034402011032140400580c80201d098580701c2c00103281001036100c072485003511829100c004006504260f0b80780121a0090030540000f42c0c104903160180d03960a08403403052604454030300503000020b00300c444652264608407201e10310b91803079001c80641c0070340c40344003122440d87c80c401a444003003030b08100d4401e210100b0b0b90b403115482024041d9007040d0113000030404450640da124080c03030000e0007003e68510040c05078000046601c4e201340c06052030032810646810308580c1c0e0605c0c0100b07200d001c000b200030f160824412078082620140304040c031681c041d8588d6180701c0e183c83d0074402450700d100c9103902081200e565950f024605101d1040c00c0350146040200d9a0071100f00007890381c46122902240c00c0c0c5400d110301d54160 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 293931142 1250 293929892 293929931
    0xd03020c0a26070e070309020a0b0703090f0506070b07110f070f17030a050f070303020919050901090902010c020405040507180f0510081005151309050c030c030601140f04 75
    0x14060400c0054022858400e10b039180030750b02810290000c101d000410b03181c03196007c0d1440310300007080448841d1355603014842c00e078007209007640001c0c038204050144126484084004003c1a20042e2804000d40c03204040d10001420303010800844400d00c01d2b01000030800b030150b103800030703090318000f5640d243c0710f40c02e402a600c680c20f42e014004840c4c41840001000366003011603680c0311946040203a1126252990018000f10241582406400007648840380c071840054101c500011166040100304178034070505034880506203062081400050744e004058009450341503c1c017140e691581c0c5083d6040040075007040e04004070303200e050a4105600d400c420081190200204804c1d01c0301d9642c0c00c1241707154016030720b840e80300c0d5042003107410480d131200b54445400207010160500540004160007010010000c0d001c1c4c0300c1d10a00c041c84800d200258038400d040b00100350800c00040480c1e1654014882d01035040b00d03040d0528515210940300e280740e010024401c00c080510204009e502c030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 293932392 1250 293931142 293931179
    0x60b030d020c0f01050306101b060f02090109080c012c12060a0b03070f03080d0e03040b040302130902280b16110a05060f090409080d090b0c16020d03020c0a 69
    0x3240000c00c40f1074194012800c40b0f009a01c05840180000f114010a41e13804024042c600301049007410780101080c200d100c0da030158000303000d000d66120402030005113903000716000303080b0913003102040c0d002d1a1f0304a0000180c20000b050703022030074441851f400c00b541c03050741c28258000710034000c8240801c00100c0c0702031154107902c0c410041d55002c0002d150f40c440d02da014030f1080c909594818808140c0040c007805580c1c51401c0007160441d04036882e6811341d00309502c40c4036400d10116040c41149088060300620b002282c004012215550700080d080440010450000a2802011815512205120801030803001c500c46560b8546a210802503003c604420358000003001d101414034940b038910b443c100ca800600c1d080c100140c1d60709118595020310455648540d603165090001444403004e8034a40f41d148800003000c182130300700243e148900030b1410f6200d0f00200721003882061841c0c10b11641a4054980b18410b074460315046e0b103802012103040d40e1200021500042d14196a80c240024 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 293933642 1250 293932392 293932399
    0x909010605040302011e12021b120c100212130302030705070303050d06050103052401110a050304030b0c0304200409020d060903030b0103090308161403070206060910031509060b030d020c 82
    0x7122107040320219480c40c110783c6c1d82c001411010081071030403e15000740400032851180c56130441502c1c5003451403c240800e60911541011803020200705082c81014803003034032a8002c0d860301c04c3da500003040c1c51a0080c410030103102c200b884502454820003e64035425440404c94500c5600d03400c010349550000d01201c85500c1c03c2103008030ba15407003405031318051820f2840201e16001d0700304030342403035942a405607410402e00c01801c2e011000c040003c0701441c2d000c0c201a6586904604141c1c41d01200206166050300042052000040c242810a0720141c07000b00c0784d40c1d41182d60f0300058003074250f940011b940051040301c00e0042c0142c80d4007545150b40300c4e481c1000311110f0301d001523081e034003105005000b194070303000003c080640c0e6203024800b032255890080204134164003581d1158106462450060380034004001c45170401c0c856541d0450a940b0403060100d00d1940c81c407800002044400c0881629000004100101c41d0424211000010195244800300b4200256201c0c151603605e4030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 293934892 1250 293933642 293933657
    0x90f06090105100b0f03190f2a09080709050406020d022703010510050d02030a12091a13090c021e0a02010905120703141009030f0806031c1202090901060504030201 72
    0x5810310310100b1034030300c070101030100e0382995501c1f5084c4442d0220005010500381c0c4902c802c01140b0241e204142e94500b000b0f10392031040d01610701010031180081040c10610040303040034410903000245810440702c2c0e01c000031450f5645c40c03400e000a8026060140001c0c0e00104105401c41810420107034006405c10071080c441e05041c1c1014240c42c0180c030812031020000d04240142d040806201481c5800601101c01e240000daa5410f15200c14110718000222140d4092040200c011000b0b940c1c0d081604480e42440008501b490004006100303e190281c0e44000310710499000b40000e116019192202c080e210780c503008010740392851810128002458010049801e1610501c400055001301c1c0040c0070b0282569a045030041980256654512070381c403032807444640da030142100c06c600c82d54960105040c95900540545009040b0501c00d4000003800061811828040540b0b031540e460b100d900050a11880f000a206d03c5000f183c0210107900082500c6400c5002042128070030b03a90050f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 293936142 1250 293934892 293934899
    0x601061115061c0204150605030415050c0901050306040b0907050310080609070605210a1b02150f0c0904050a020a0905150406050a0e0306041212060518090f0609010510 74
    0x100014411598298481e10110b043d040b1101003109504980d4409400040e00080341800410100340a80c40702000070400010042000b841041d80307039074184043e8050110307007403451000c0b44501600000c0350402102100081c030580c0d81e40c1040c65201d60240ca000c1e41b504004070024001d5000301c86c1170030202c0d841140000c07030a100080313143c440c288103400380c240103041c1141180c0560100a85084445164003449808540f41c921907004150710180051034480710b0f0024540c034603414220f4020340d0030451120501b04c4502100359400f10ba09030b900d50403546c1d410941f9925015500c070442e0040c4c544010041c1c440c4455000700f10244042e2528050b0ba9078942c204440c80034800e8002e00400000e0008019481c02000501084016806c14285d000e805c00040ba190100848040e0b804100250000d03e03034a8110305810301d81100481c0600c1074905080100300d12540702025000103802c0740d40040c8a2050500c40d0240d02e02540043c5c8130141001c1e40d016018020548030320044240812001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 293937392 1250 293936142 293936173
    0x6070209150a081f1d0601080c0109060503010303080a0e030c0d03060302090105060a0c03080a09140c010801090e0705010c0203031201030f0b0a020301150302160c060f03050a0b0f0909070806010611 87
    0x1000a0030900d24142d0000304d002504000744c1900b458280c0b0310384500c0254201c064090218034041e2260308001e10454005000041000b004d947c8040c040c0602080184046580301c440c242c1c0c007840410011482c3d541d00c505a07032452140e540070080c140140a2481070f80c03a80740c3c00031811a03000b12012032080c2d0300c69007000f16a114007244030021403000c6070480000780c0203201040d400021203c0010300c01d4081e8442203e880b0721500301d00c1507504064502c004640c1c100d90a2030160007040d400b00185401075481d65590805809010306200182c0c05807001c40d50100200c40c0c0314044146184100d5959150210b030b42002554126480003035000001ca01ca08203100b902e0482e0503d145007590404103010680081d0710400000c42040c0b0003042c2070740400c0500d460140200542e5641c101000d51901008040720005001c84030300d2410f01ca00c50f150b40e42d900c5040b5110060480d0190348030b46695204620b03011940d030004195000b40343c000201c0315040700b102c5502c4038035102071b40c40d000c5002038003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 293938642 1250 293937392 293937403
    0x3080a0e09010b0901052a070b04060f02010902010e040e0102040b12010303090902030f0a09141203010f050a03150209060c06090d030f05070c1e0503040e0103121e050906070209150a08 81
    0x2e240000d206110ba00d4074854104d5124142d50540e203100646102d84107c100e05260080e0000c000e940f20000c0c1c1004425804028068800e8030b91000700310700440c41d40002c100715841482c60f40320720703110702c41e50310342aa013981100c0040c1200018903a44011030a400c0c0d028030b03000d00c0141c1c0855256100002c070b012250084074813030141096014065030b40d080b03101c0300501580c0c806440d2141440d00605801c032040054400d41101c1881301900ca43c94044140401a4036400c424000c0155080c1080015001c58442080d01c080800168840030b0040208800e4056105001401d00c664428080b000700302180000c180042a6411f004030300403038105c00d0903948280d5401c00026601c040c02c0b0081000304508000700381400c50700341403000780b603124640395410940241c11540040c83c01003041010020042c1e481600c03900b0044548000c0f000c0715081c012552130514284040092000010303942ca50807500349a6000303006411604242490440e100c00985445016124100c1c0200e1000c20000c0c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 293939892 1250 293938642 293938657
    0x170406080606030a0204090c0206010806062e02120a0306030b06040203060d0212030c030c01150e0106020712051501030f11030601050604090b0f12060403090f0b0306011803080a0e09010b 82
    0x40d40451600c5000c28001550300040480d01050741c280004074143c0542c1c060041c1000c01c42d801081e035035041441d020705041d0b000e400548100001c46803070010201c0514280d603104862101030204101e408805d1341481c1001c141c1c024a0700c80018a059425050360262040c4d030f011701007041141e551502800200e20080c2da1644e0300a440c00c0b406001481d280d4810400c000c066002d5078204800b8134181403454008841c1c4e03009030f03515240b421090381d00500c1d500c0002c0c1032320600303450302d9403503c14041d480b01c8060080f80d6511031190548424481e04110620b0498202d05101c0d100303603901d05200b522003649540440304235140700d01c40e284620b0000343c103074140c17140240968a07251500c001305005081d40301c1415005900c58515810954510408000980c0d0f15000f50655203490b01d0000e1600041d41c200351b02000b00d1080900200c0103110950780d1000c0300b82006140701d007211214140780400c0e54801443c144000a6840c15661f0108003035a40c22800d07524550203076254016014940100034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 293941142 1250 293939892 293939897
    0x1203021e030a1b0c060f05071215030206030109020c1002090a0509100b03040305090f030a0c0504090f081206090c040f15021e160504020f07032012090f01020d20010f050a09170406 79
    0x5127410180c249c40d80300d011b04c416218481e40c05982d0307035804540160001d80c00003a006a0204d03c004480c0000c2c080c10b22180c0ba0400c04618000300c040004108003168002d1320f004121020001d0540c01000281902621521802503102d01d0070340347c000d20b030340d0100441c00c1c041e010200c4c4c1d03200c8034180010100280c50f40250f1444146041030b0900c00100b24030740007961002c107203804071004908002c0040c161507501c13a03152082032418405115000401921680114070100300402980300b5803505501940d040010300120084080400c80c03501c00d06c0c4000c0120340c0305a031071404070031b04006003190791920300d03500885816949408020890040f48000d20701c0c2c1a0401400000074481c403c4490700c0050014030a443d00c004c00302030782c80e0480c0c052894140050003d0381d40980c0c40c1c021a0004420310903c001d210341400c840c002007095100071201301143d01403240d030820a480a41056004240303501c4100801d1900503000800741c83c04100943c0c0300c14681c03143c0482c4100d050101c0d42aa074164 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 293942392 1250 293941142 293941157
    0x5010e0907050a0201110414030105010605030f070e12010e0a0c050409080414150d02120604090201050a08061201090f02090702120703050c0114040f1203021e030a1b0c060f0507 78
    0x51000b51071a078098010041155621010800c001c4621405040a400b40c00b110922100b206000d050841d441030b000041484018003c0200c4108000041ca030320488c2e91905c0c0040f0161440400c0c0881448244071005e942060100304e80107000052070f91000e40240420b103e1142d036482400b00b2500c0c010409002848200400c0c0b001010000080080500103400d18402480c4c00130603860340c2d000000701d01c1d41d054000410700d0710724050f052015003014046030100302054103a40081c103c5c2c480c0f0003140090004000c0003c1d01070b95101810810580c2c000001d008030395051402d000550245c0200f00c1c07040791a9008110418400118101d03000c904121003850071165441c141d034038be0010496a141c1c1c1d0b486032506281d03a108400e04c240110b00c203900340d5068900c2850b1030940c460551002000300341c4188603900c82c40002c0091141f898442c0d0002d80d0f600e40300c00451701c0c06005030441910140c00340b42d000c181071a074051103440c2401d000d00070401100360499401c0040c0d8030300b602c031400001e102 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 293943642 1250 293942392 293942401
    0xa0c09020c010f0c0e0405090c21010f0b0d11040e0601151b0b040b04060e030417100506010e0f0f04050c19030b03070302120118080c0120040b070804090e010209010905010e09 77
    0x154041c680220790302045401419550780000c0002b4a44a480c0c10134003000c4200201200302401424101c0440403010300102c0c0b0940049040c2003001940502101c070180300d0406181c98503409000e9035142002650002d6854810081e0304503141040040099590214032803801203910f140200240c0c48501001c490700c650319511800d080c05481540c410740e94260741500c0744004c100500040000c1c0901d10014283d9904460030034440c4d11150491909000c00c0008507030707200c0e240b00340911084803b0b000103000303d404245460340c0181c2c502e420610704401d10040d4501e00000d004001c0903201e822286072000d1100b10250740302081800d0f01a48440400c0c00146060815440c44500a10000a14002500d0310107614075000c40142c601c5400011240c0110a0030b01aa1910408a1080d642c0001c0d031131500c00d0182c4036900c90451080000b155000400050320100d40040c20207082c14040d03d80080320a5000b540302c56500c2e07011459a00000501e54040e10602c41305800c020030700005c079510f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 293944892 1250 293943642 293943649
    0xc040e0304030828020c090c0a02060105090c0c1005010504061a040e0a02090306070c0501050c090a03060209060705030a12050f01050108040605060a050607030203130b040b070f050a0c09020c010f0c0e 88
    0x1422030031110304640c030346001610b50340c44054180844e142d0050180400c100305205a168000d0811004c40c0f00802015200940000f0b110f41160001d84900c84d040d0381d02614071185014003400c3e409140103250f4100144120340c0c00c003505171101160b08100180c0d440344071a88200740140700b550282c4050008203c256101500c0c103a014240c07036005032410b510303200000d00303010080344e0000c081b403180e200350000d1103000d1103155441524074926a190803088d030002100003440e480000e05540e0001110010b9454041c1510000d65100c42244c0e112003400c074001d40414803100855a0080c5410002880424005c8623907040347d10684034000c10f501c176611040064600140398a40280c400b1100242d140c171000001c100d00c81c0203901071900c0b822107000f040201803150748641c0c0507134800e010a00424040307904441c289a440029000003922510701a407c0410500f07010708448402d40c00001c20107019001050541101802040a0708042c04a40304865403007902c2e40001d000070404910b5803d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 293946142 1250 293944892 293944897
    0x3030406020a06110417032a1e0102040e090d030b030a0201050a081b0d020d0e060417070c0f33080112030e0d0302031b03040b2502120c030c040e03040308 68
    0x342c41d06504c40c501900c41d140d904510245201c5000c25600c0000c0888080684502c80598840540e408034004c2c0c0f0012182c41e501c0b002440c600b44045580110007c05401c03d40c100c0d4000c0c4200c481007030715403809045160712058440d01030b0300400d0034600c05e4036213480d000c240d1510155058540c03d00780600c0741e4044445081c028104840c002401d00880c20461800c400351030f401000c1c0b0b10141c0d503a58900c1012003a249140004d2105a0040061100140c00388070409490070b2180c20f0f1544407034150414844421580e4050420703504d01110200d007400c420b8815294813041c0c420607811000092400503489480c45180600003441e45e80103200b404170490383d049040e8081e10f0114100400c07000000e400458501c007c0f00540c2c000030b5500c05a4400702c04900004098101030340c10103145c042c610019104883c40c01c0c80c01d096444014190400c80c074803506280707801038110031302030340b41c40316642c0e507200c2104045100344680211103047c4d00d024000c42132400c800a001c0e5003080d01d59514603071140c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 293947392 1250 293946142 293946161
    0x4030c021207170303040203030a030504021f020705150c0c060904140a05041a22020103060b131404060f0311041806050f0123010807090b0a08100503030406020a06 72
    0x40000100503956140a00a070046200007030103038249440004800507a001600c0da9103504180100300c056174021041d22611809810007243caa669840003400d6558a00410f410303540c2200011007082e076000901d80c090f0380003900c51880100c2ea8504502030f500500c000d85800da07000320107100f85410603a0140400d28405000880e0303ca880702c8480119120441d580701c0e12554440030401802102c45130f0720640d208100030700d16582046c01d5403412180c60500c1100c60300f08540b03c0070085902c254850b0f001096103405490311058100c08482c180704644c800e001d805110344c04bc001c0d1a00e42485a803007140c2c0702c0002510b04500c3c3d40c2d034071784414011141d12584280e6450081749288980e05800c0380480c45240d00150919003000400001c88040c0c1100007807020170300d40c074060848409032816a050003402d00902690318080e085030502907581001ea0b11800101d110f0500301d4015440c280180c15000040c0704a540382c0d02416901d001707501c80e007001a4413a01803280421019809040c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 293948642 1250 293947392 293947397
    0x91e01050c01020a020a0c05010912080711060d0f060501021b01110c151b0105011208030402130c090f0b07030f0f020109020301090305120f0c190309020d0308040209130512030403 79
    0xd00381030740e0744503089030041d143c0b10015130071101c0240100044080b03a6409030a0908141e000075080804502c45482c0020000f411000005100c1003803000c00c1031288540d0b00c0080c64580c0d115100000c3c100504962030800d005142004c201007000e40c000300726048000102d90554030540c007483c2c01142c120340448040c861b01d00444600620315101c0c98051180c00c1d5905101c155a01c0d190184680d00012014074100c050b45014018003c0307071058564218826042601907803261264000940c0d0401e4511009602a00e480709080703000350051201e1081781c8844410900e940e503100029105407041890040010f4440b0034402c0426003e42e01961040d901840006156038450b80881d084506030b21b000c2d004507a0111b400b6681201301c2d45000c0d8041680c0345803040030308201c0440105402006120415031046001311040d4620070340c02030395116001407802d140521130741030180407800142e40a1f801540c5c184000340c0048070045500003102d0707002004150260601e2780d02c1d039281d080940100c04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 293949892 1250 293948642 293948647
    0x3020705031c180e13020f03060405060f011401091a0d060303031d1f020304050f0f031201090e100f090c0e0402091311210114090d09050616021f11010b06091e0105 72
    0x7da03601e007000a544180d00c031300300411560400d015000e2852105130702c80550000300801050041e607000d1001000caa185100c132820300305181c210310007a070003039002c086130540c42c101e80041455410b03002590740c070184c130103040d181050601c050354403801040190352908000c5c8120380b040035a103500850740b01e80500240c500545555007103900301303a02e520400f501503102049660348106c030351510b40e004120800042011407903507a18692a0304102c000101c0e03181e901c43c1c20403080c610980040001c0e07503001c0e5025610b1520345c0390740000303d42d058030140c0c040d400740300c00924003450f20900c000800d42c105e17030b50200500710141081950341c9201501400c0340a030040740301c1e00315403d004450740c00c0200c3c080c0c0b00a500e05920702610308403044400d203040291024040000752118012110b0034036001e202d46021131014008100c1c0e5800c001c1042c10492011440e500c00198072114070300c001c0e128140240072690810f010043c2c640220079030b890740071206007401000811402c092001d1000c06050030750 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 293951142 1250 293949892 293949919
    0x1e05070213020f0738040b090715090311040903050315061e0705060601090f17160b03090601050118050d050c03010203011202130c0807050703020705031c180e1302 72
    0x6a83d500052003c590701c1032151000b8507000d914021259018090503600e480306140c0c2480e60b0100003018001804545162022600da500e052020602411054a101078a00603444004010900c1e45c072055945540c90803000c01140340602401c1b42c81034041c1d071803d045407181210340030201c0561080303d92000e010026035000f81c03000d604400c000981511919210b44450800c80d05107680100400c1c1040004071050190140201e080300c26200501c010502000c0958042450642004540141070300360030000030300c84909000a43c4141a50300c1501e61a0340da41005480301100c4181d40c00306c20403414010300c20f908200320181d000c54041d000700c5500c0300d200c201080c22130784280c1103a6031100c00003c5010a508002c0c103280c2002c0315000080180e4480036100400303200b0b001d800403007001130004098041c0341c42003011402602c8010103403541000d2104c0213400d00210301d0000030101340aa14800f40300d6140d44681d404a8006101030b004a5540c9107810702400c1072a40d08aa10200080345070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 293952392 1250 293951142 293951167
    0x60603010614040e0c0301030b090109020619020106030804260706050a0f050702090f07020c03160e040c0806190506030d090b1e03100e0c0309120a200d1e0507021302 73
    0x22401205c4203003c0581c0e81d415030905000706400204000c1c005c0e07040c0807940c1c0060b00e0b0841220b140d48000c0440b0000100080b800b01c3c003404056002800710303c1d0114011660401ca504081c071030f045020b040c10700c00403034031108030f480d41c42c64480c00001c0f49050002100c0c580c09000311155074515454a40e00d40300340d075030001d0b450ac101900c440050f00e405404200c000da40411120304805000c400906d080544605443d40303540c07540c0699039070003000001103410001d000d1202d0001d080ca00c41917510914000c250f00e69288042c030f9800d050141040041082800c0111f0051100300c801d070b503441e100741e0600d00051034581c8020078800d040e641032418002d00d1995000910f004018032131060902e180341100c85a10348001500611007088200b00740070401c0d80008180d81e00f1302040000a0b140d482104054030b0340c0319204010610780301c951600460081e00800d81e0340701c03500c240c8c030ec030003803070018107400d8ac440c0d4041207031240402c40410002c0e02602e0001c40c070101da00d0607544094a89407001044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 293953642 1250 293952392 293952419
    0x121a0409060e06091902060d0b030604080304031b1a060609040e0303191b080a09120f0f050301081e031b160902132304060f030b010e06060301061404 66
    0x5032151030b07442da40100500c03000d00000382c001800c0d6000700410408034480054910210304024070502c80000c3c1e842003d406508801074051008055030305a18181c148450306a0085504400150760502c0e248412020361031585002501301d00752202071848601c4451007d5409404294003c400340700030035555880c0d00034031440e4044072010703580702d0a041d81240401c0d0003200c040f4a0315800d02040d80b0302c1040303903610008030100341c0c034200185884030b510340d0b0010310051801a01c29070112001a040325084000c1d02042d408580c0d90140d4440181d000702c910740401c0c011402140c000c114118036240074a540594a05e8600c0c05803403034145105854140b4040004007410150009a500c030810807014030010000e00c1120010351074800b40c0d1014654080c520301032440c200d4103008180380c0c1c058420240124000d0003030700412a05032107030302c801070010451004450310754981c800400c20b103040c0005980503c01c064150350a40e424000e05441503c0030142864140c0070030310000a0030ba15845c2d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 293954892 1250 293953642 293953661
    0x6110d060806010b04120305070804120f12020607050d1523011805010f0305041104060924080a0b06030a0b0709030c05180103020f1c0501021201060807121a04 70
    0x1403030340c0c07038001c6041c10500b0581c012004480c0c144410440c844100c0500703da00b039031515000303550305080e00d4249000d0140c2d8000c1a48404019050800c10011072048108580200b020315402a0b403000c1c12a500d1204a405000040b02442051148a16604032410a5404203050400c0780d4503000d00044280c240040c1e558003000c0a8105503c55070040d0b039103001030100c1180040420308220001c1c10509040d4a10410159200c0004003440000011403103081d0000300306000c0940e42e1421400070700141115081c06003080381041d4501980c1c84540011140b140c070182205200f10303220384900c403038020700068150040001442c001001c00315a00d114451a8550050340f0742181401c400c0221a504014024103006c4024503505502c0e000c0c184c1101da04581041d4a0010440411490110410041c10001800104a0070000c047d000341c403c240062680c4151030fa60746100301c580319000d9130034070082104642c12440b07000d119084800f0315504c82c2c0010301402c0820000c50220f40c1ca210 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 293956142 1250 293954892 293954917
    0x60b01051219061d160504031401050106020118051b030f0706031b08070519020106080a0c030b06060f04030b0408040f0b12070e01050d021c140406060b0301060c030c0611 75
    0x50a1240b2034014802d4401a00b011241010490040780c110740900b0341c081c190088403080400c1c1160070900c00d204841c05075601003010b203004007020100c01c1c087c0c5000e00030b500255003440c2c0c0b0245452403440f5080d110300e410500601a10365000104002d60f08813820854050265100e01c01c2c4210003040307140e008048035500011081080c100c1c90300c1c0752252000140401c00100248a10340394440b040d5042e42c0800c42d0242c41004000c40300764010a0b595004291078003c5050000c1441640c01a40c4100c80c010a40c40000c1d5944130100060b51080e00d4104100d25400e110510203c2c805443c0c045d401403081e40b80f07501d825101c002d100c003c1000b1707a014034141540010702624200e8000c0340d031500035030a41001c4202a42c1100041c20382d01801c00700040440e40401c1e0304100310000701f00b400485443c0301c4100004d8140090120103110f0840c3c0a07503010381000400a441d803203040489040756050342d501c00524205550894030b00c1031b8403e080c1e51480d1682c03105010300196600904000f071101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 293957392 1250 293956142 293956171
    0x1d0402040e090111090a140d2001020f0a0305030403050304060e03040905190e0c0d060f02040902041a0906090405090313230108090d050a050f0d0c080a18060b010512 73
    0x10342c400c50964070319054490340000144080c2c00c09031684c00d112015544801d501d43c09081104000c6080102c499a0103010840c60940c440b0354054540b1158843e04420b07404e50f40c807101c805800550b0b0382071600e070060000e5000c100203070119208002543d0090700c503944c04100107800e400403c2c61a00a42c0240025070b58030303000e01c082c1d41004400d48409080c3c10005011041584018689a9000118460041c9220009502001010340c4001c00200001c5800c41d20f90b0744a4810038025001400743c5441011090f0743e1001141d42c0c00140d4242c8031008102900c0c0c00320102c05d0001800e0701070702c401100d1000340181c43d1711958460f41d47d030141010050300103400154000341d41c5821500d40d01141031051241c00e03c01e248034081800c815501d02030502980e2049a2007080300e142c800e52001c0010100c002c03514207246000c80d04541800403081c1d07111780380b03034541c080d442048410030b87c00c01c0742c90550101b030700300010000d070805d111461050420908110b2042c0132103800b030a04451468001e40309 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 293958642 1250 293957392 293957401
    0xf03060112091518020a03060f0b040e0c01022e0906090501141515040b090607050703080c1e0606040b030309060a050409050109020a0503040b0a060f031b090e0703031d0402040e 78
    0x103d01c11440c0e0304ca00c0c0032074070b0403800d0580c01140c4c4610450201403d001c1e11510b08a60964090b00586000c80c0040c104009400203881003c0d1202c00c2101042d005014a48448032a0506d5140c0180c7d00103200f14201c0c001a01c2e002c445009100e0307020201d07410f5031660450742c00701d8404e2043d00190300c000c240d260103610303003500c180400c40c06030b04c0264071810f101d001c3d0005a50740349068805a942000425540d042200002500743c054002c3c018150b1085500110802c158100940880a06c007002c0355402d20403580c1028580308800400b850320350040001030528640358001c201c845801805503480d1200a4010480c590b00c680c4010021034000201046101e4041c85a1801030411140c11420072100c140c00800510001e00050701e02046e500200b00820362030351254004100410141a040b035803440d042c0314020b0620400340181100b140001079500d818041c05d003c001c01a800b8020341e90031550b040d00d1030501204c0001f0442e100c1c1da42c4d1141c035212840204054010142c006200303161 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 293959892 1250 293958642 293958683
    0x10203160f06110a0816020a0206090a150512480a091404021207050d0e01051602060f090624091302101b0803090109150c03060e0c0f0306011209 64
    0x10060410310024040e80d01c080c1c00d00d51f0214800309140d9045070015030b640440c0001400c0c2c0d2495421040365250701d0f400518001c3d070008010540484800b16104c0f150341c2c0e1020300f0a0b85898640060311400f600c41d115103401318201246070180a41d070b5554517500b081c24290781c41076040610041c0c0402d50b01d0b40c00388a1850002076029420104550942c41c101104420300034042e4068a01c1e401d00001060b001c54040703180d0170214100f81200c000700b100c1d113017814420501443c24a45035015008400c04100345801c044c1101d40b150013094010030b05a00c820040c9603400d03405922074607920200983c0401c80c2d56405412502501c090349110751108102d004000f0b40800d440041c90500c010030f2519609101c910041d4180e603600310001584a542d902019400360001d10801440150000a134a0342c180096100c114070803969a0100034594803106d106800136000d58207020000014004c105088054000855003c18103140450101c9070213440c1030140c420b1000200d64801410081e96840403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 293961142 1250 293959892 293959907
    0x10905060601021005041a06150d0227010806130207170c01060609150c14030a080a05060607030507060203070314010f15030204031101110c061c0c03050402010203160f06110a 77
    0x1400040404ca075007895901c4e0311554a00c06149221f0002060008490740d940745400b01400f4102c491441d5641c81061850009511400700c100741c482c0075a07208c0100041d081c0b2040041d8606851303445c06504c0b03420070081060f4040801c0442c4940800002d000960382ea0710039119140d0007086151100c01c034116084c00d488250f0030050400500410400c00342c03543d00c040326082c0c00e690a0030341000303049091400508501e01030510603031100040c1004c04a9100304103610400d2090b80c100225111101005128440d041011303000032000d01103100459110b900454200d0000d00f0300088a0400f81549448508260300202c5000b00780c000c10000049640ca921040c03852901d2b013186414115075400c51030300410380f050b6041102c40300340d011180104100d021807088d03004141c10744907192054201641c4648a25031108075040c800c0c2150054000d01449015680c160091420072a401d544a00c110307500b16004e50304c004030040c058010400074495030b591040c400c1c40c8241d40d140134400182800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 293962392 1250 293961142 293961163
    0x50d06140c0c2e110306040b060c0d0302090d020d030518030c06030a0e0708071701060504020f0f07081909030212070303120b0301091e1209030209010504110c01090506060102 77
    0x107120030400b4002d51803000c82d81600e8001c10300d01c9400004441c400c9000114030f508107030041c4502c0c0c0f580d502c100c0401030018612500c0222000c2c04169400e90a0218a000f0240c5511154ac0911070350302816019030041c0044a002034028000b528941e0001500481102c03c103601060300040c02c40b02143d07440c02d0380301184a00b5801004c26000903004203285100084c03d200c8041e81d03501c10924002070500080c8020a1501c00b20341c403054613280111101d03181074031000300340c1d8640f400002d003d0429000f5103c055050b00c10203821300760305084400d619440f05100b00ca00c00801c0001070202030b103803106d00681c090195240c103840e6065205100c804002071050040560010300704000007a40000350601500d0025000704101103841d000c2405032550440007829506100400c0b150018a04840f407803190140c140b141e806084048203981e02c1447d80400303500644450014030460030315804c664882c9050319121440c02040c0002c0c0303803c45401002c2243c0380d401401c1809800c4da41000b009908 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 293963642 1250 293962392 293962411
    0xc0d09180e0a0b06011101060f0617090a240f090b090a2406030b0c211603051302040e0705090c090102030313020d050319090b0705190c050d0614 64
    0x20701680340d00a50b69a070040030040c150190100021318691007005a01c03020700f0080006e210040d00c0e154050002221406488005030351200003048059203150071a009042c600080c02e500301c80b17504c800d2030cc40d542584140856900121144800090b80304400d5401040000090001c00c90710f850883c80c2009841050307140d02120320708000c00c810f6807960542000d81600170181e201c8006420b4050201580060051100036040080100403170004001c0f28200484086c0020303440000909031101c2074a0220024050181f030040e094000d07070100d40c021010001e200d0410513168001410b841022444421942100030100003500b800d445260f00a41079110087c1004541760000350f8901000388008402ca8003500f04c002951640d8080d025526000802c0d0b81e5a103500100709110b010502036200d0004152000c00503102034900280c5801070760001c054860150703913050041c001d503d0180d064030b28581004001816599600d19500041e02c95000420751f0700311005400071f8064001e0614a1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 293964892 1250 293963642 293963651
    0x7050109051e0f04290907080112030f02150103030c06050f07050f0f0912060907061404140429040f0605031c0e04020414030f010c05030c0f0c0d0918 66
    0x110004031500b050094903050741c0b880b4400140c0400a0f024000c1c090000304284039140c075500c62140c0c2060320ba030055406450020032600c803a807040b210190300344240c40c20301ca51400078000081c840c8000300e40c61011803048483c24000c5403401d111500080e4070880101d29005109000c0081b03c0c00750a500100001700440d40e8609107502418510810001c04600c20340051441107060000b019960f03503000280c6000f40c0507012012555071070b001550f200300e8500c00c40d070001542911540e110110f1207030200a5900b0300f4906504210010440400d80e07500c070b51500001003000410601c040c1c903800343c00038001c59401d60601480116445401e60b21140303030501030f091001d9180080c0d10b481d001c0341001018458945c070b420441da039207540703503545900a00010f00000c90181e000c0024005200c2101610f814548442c00d490807140310304c00202c045281070000503039080101000e46000311161160515100000d0340180c10907440d04540000f0803c8480140443c445c49181403861030b0307241e1802c01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 293966142 1250 293964892 293964919
    0x105070201051b0918010303090305060f0105060f0a1b0503030703110304020a0b0f07080d1d030702010c0b070207030203031b010501120503030604020f070b090109020f01050427090803090705010905 87
    0x1640380301d92042d40701010f40050810043d4070b8088070303104026410300400c10076503103d1400501c00d00c00d51105503410300c14030000c168030b00a0718522604a400c024455031610000f840107025907000728070344601307110410340c54001003e9030060f80c0c90084d10500c040c540d039107040d41025003101c0d000c0d041841d20b44024010480183c0350069030405441d00a0782d10790700c40c240c00c3c001151301c3c400c44100034201200032408541e00d4100d504005c013840003242c0c510010648901c8016039a014912000c0e0004142d14090008160121041900b0510510546c0c1d0041e403a500880e02c1d5a10034030020703107800c07100e0314900b030344440c00e2103035602500420648940c0511240c440a54a01000e80510f1145074002122802d90000204990466500600b14640c81c54030581c100c0c02008419001c0c0d025191072588840103600c1002100c0c1540e11410500002c2882088000054010782145039805641c4401ba8000328120714069071058000704010f2025509000c00101b02d41c9055000c18010294100b004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 293967392 1250 293966142 293966161
    0x405060415060620161805070503070e042708030a140c030c0c010f110a020705010302040f03060914010e0607090f030c090f0f0f0b0414090706050307020312070f02010507020105 78
    0x103007a940b104100e424030b241024504da50800250b84003141d030b69400007200051400025511145401c12924200100c0c0d50300d200950f007620080303802000007036664141c0c0000e071400b5032000b00340c035101140f60f07000e440903042c0031610790104070020395818002008000104801e07000c0c0c032981d901200000040c509040e44d0b64881c0d80005001103003d84404110304540c0c0d203095011030740180e00c00308144800c1c00d04c080c042d1030b164006d0300c0200040c00742c0b03900400c00f0350182c02207c04803250010b16142072403454031104001c0011883c00c64042000d10308100240409005007410004001d0180556003005180604105400d40c46070325400d03c031030010404151482846003c81300f64103800700d1016540000c80c2c00030818078020594041c41c2c00184000303140c0c0307a4441d06843c0010b40c0c08204003260030340c119800e581d045804410ba584074005c240311151069001d9504401d050045905103c51080b86244d04001201d04000003824401d00f9025141e09014184e0441c60a000030050ba040c4000702 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 293968642 1250 293967392 293967407
    0x906051e04020111010902100f1806020c01030c020a080301140109090b0d0321050901020d060f0b190c201302070b070f090e13020f0108010f03151404050604150606 72
    0x641030001541c02140b403a5130a401c8000e0103580245405039034101c0110191a1900c202800ca0000300f26900b810941d0b985152103009071691034004102503c9035800450141104002da86c5c01c500a901c25600043d0258000e1030181c80c5603440020090100c500052000d1081d40c00040003d0500104510340e0b116003071004180d942510744020b102203000c514070729161403031102240442c40d16080205007001940034103500250101c0034040d0a40c1d403030f511008010103010740111180e0400051003c1150900c1e2031080e402c080c20708404c0300e101501c404101d4254140d03202e4019801d002c10285601e0412280c440d03603000a83c003103042203200d840e0503070500300c01450031060190340214001040e00400c00400206840031010b111403902e1040503035102c20448089002e1000d007101741d400d641c09203040d00e05132020a0030f0324003501e1454995800040540c400706032000e5484500780e09000c042c8006900c41c0703019000808050404e0f181080e064040c003c0c0e08419680f4200003440720759486210f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 293969892 1250 293968642 293968651
    0x20f070b03040f080c0312010501111f02030709080712051e1009020f0303040306320a05060105070f03170105090c1b0102040923010608010b030c070c0503010f0906051e 74
    0x30042c2c6008004d240502080c0700350116000c86100c041b450982211201242c2c0341070340e41c282e8540344a4054003000c6503a44440743e001e07195100c00b052040a282c0a29809154001524034214030415a1410180c0c10f0100d250010b80d140f00090304081d0610408008003110350380241c41007502002e1120780715403218003c103003140c0c100e91174184981c1036555060041d6043d540080959a445940e89040d0b00104051007044e0000351206201c0070400d80c40d085c24982004048441c010b441c5c4c0c1d690030341d80c01058014070131810b215082c031075100411191416507140602c03a85410b90030070003800d803c01e00c1d001c050b031140b4400c500703080c100041c00c8003440a886081e5107003000c03551452800f0762030390f001e400b4076080f0b1000e4900d817001c1c0c0c0309282c800d20000c00142c029460340c10881c0c0d0303e502086481c00001d004014108404002140110302400028034060303003d1000b03c00503d80b50f400007420b40701c2c0d100d45681e010b5241c004100a1111501c00c0c1c0e82c00ca6003046a8840d03848000c8100c1c001ca560040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 293971142 1250 293969892 293969903
    0x50f0f0d0e04181b08120903152a0301090f0e0c041d0307081e070302061303050d0e100b010207120209090a0501022106011701231f020f070b0304 64
    0x243c0c011008030290803414070560158901c1d10704104502c6070780180c901c0d48140c0c40ea921844084a03c403403514811500b41020290203000c2d289002000211510000b5000d4042e20040d444200f50307244021300400f141250307100f4241d95a503d00aa811709541e0301504d8001c0341440c044030000001000100015003207810b40d40401c00c0501000388016501d070758224003030740d4000011044100b18201c0c00520314809100d4003400c0d2499400928406030181c103030002c01580c8413070041007129400d0414401c0c0c951103171a00701c1c82e14004121003010707500850304280c69035001408000ca00c0c0300c1c60241142116080c4014903089203416207a01c01302c201c0c404068090b41011010590400040c4081d40c80f040c2c00c54003e56886600101c240c10300c0c1030801c400300c424031624002c60b501e58892131144024016030961420143d00300301b40581d8000714a6240410814070158040d11619400320f41e0301e15007841c44440ca08412003110180c00e05500c01004603043d009000c091166100c0d16094940064010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 293972392 1250 293971142 293971151
    0xc01020d05043828050103020907050403050604030c0204021b0a0309092906071a040c12120e1309080c01060e01051f090b04030b061905060a0806150304050f0f0d0e04 73
    0x400100e18038000d42d041c00c0c1904000c5006000c0e413070194109a04036403003500e8000b4140d4900d001160356000d1400001c1c5143c000d4000700d0301080c41070070f01c01d061600007040185416010441d80c064030200c08000300343c2c0c3d0440c0401800341904142420020141080240003e240105040050420a4041120080500e018400c840d2605406c0c0d8500580c0480190104000c0c1c0901d00c208031401c0314115540149604082402000c400f20454031aa200e8107d1004500141e019500005032221080d001142100c002c1d51803100c5010746008180294041c079501c204000d009400e4807141c2c0c106001e0b444402c070040046849800d01c200402d03148510070300d022403401104544038a1a50301096000d040803a0101c28004a00e141c42d004440c200c420072242d00100c1d0030202c140c42503110b103652015080c080d14007120700034030030141c0c40500100320019080300d1b4064000c80e0782054a09543c0c07980081095110450100146030140c29000020f040c08514100024608098000b03120700070303501d6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 293973642 1250 293972392 293972401
    0x901080408040e07091701140f0622060512030c0c0d061517100b01050901030905010b040f021b070f03020409060f09060b0103140123060c01020d050438 67
    0x70a09039406400a002da440c400e040001004101403080d00540c500400c40761512902c8030014440e900c2007007000d0b4002240c0d5900c000744d2207060800144201c0c4c201001061082240040c2013104070304d0320068000041d468207103801c2c08401500180d208242e41d10030850890102800100800c0343e14007183c1d410054072040c0f0b89880030342460312402e000400c12280100e4014032911030b090000c00c0100454248005d214110f0041d50919481c250200384200801c62081d4400c1c0c0000b80c4840c0031308000f042200412010030102c0da081c80765520324a1740407441d102401c0117642d214868030143c4009006450402d10500710007007292000902c9195100c05070410842d00303030040c1c810b440390050b00f00a000d02134100040036209100d21580040d18011030f002c25141012743d514161070f07440d0041c000362510428280e0302074000c1641d09a200c1400d00c04840c9084090000300b010061403140407aa07414107141074407c00d10780b0704111103401c031001d02d1701046a008908000c00101c00340c403021800d446 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 293974892 1250 293973642 293973653
    0x12301050307290d050402010f36030b0f01090e0703150c031b0906091d15060408060c28022a030d03150b16030e0f060c011401060503090309010804 65
    0xc501e071140b440f000b0490361460040b5030710052080e4001c0c4c0311040620362500040302c9440011040c940d644001c000740d68110b001d411120603070000e4020305400181e4803900d4103044054201d5601202442175001880241128080c0072202e81d0280e005001003400c41c0d40301901c8030341190081400700e5482c12029a01442038124440d04c40e20a8001400203c41880007021682c10b802a04080f64080a000403070500358210300c603c0030341d400001451074440b10325400360060341e5454154072030014840030550040c280001d81c01a0b200d40700701592421501100369150350074000e2246100703040e201d840c0303000e03402040d00804030b94100f110303144a10301049445020385006100640520070303d80941820343e0598020050309001c8440d070001182d031604070f03c019100703040c000c120700046081d0401c00a401a0151009103400400c1da00e0780c0148440407810b260407000d0540056074640b6100d4a0041c48002403601404040c90018511714101c40c03456034903c140d5640c07038100104540000c1c03e009 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 293976142 1250 293974892 293974949
    0x3020a060e0a0b040e0702010c02060702122a030d1b0c020d05070b0d1a10050405010f021005160e030703110f011b0b0f0f01030210030209030c0a0602012301050307 72
    0x14440032004e80780c40c0c8407907003d1032991049584002640c603141d0030a0741c0c2c5000090540c8079072103603402000001728040c0036103041d0300451855502216280145800c0002400381c102500107440002c50310b41c1461110382c410794040e015041440900c10424101c0c0a41c0710301c50030b04d15501a10460018a50303803601d1382c54180f82d0341c0450f528960210740380700303d411a030f0041091881a0300b0003228407007003641040300c2c02500303080c04404150104404c01681d4000c07101e140c01120940183c0324114121960601682c40485100c1d403440304050340c40d40c80c02d412030004503913240241d001708038080c1140e442421104441003290f1160f0090003c0c00c506a00c610018582c5000303c2c80c100141800520b4800200d990654100041040800000e010408801e103014101d0b074000b004505002c1e0000c10a0300250300c500d4004d5010b02407100c4056450b1580050074006040b290300004206d40c081051494011442c0e02c8107254281003001001f2956001644106176401554001e50180c142640004041d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 293977392 1250 293976142 293976149
    0x61d12010504050718060e01150203040306050103050d03110310180b1314010501021c030f09021009031202010605010c06231905060105070b040b0c090d1b080703020a060e0a 76
    0x640c204010042001404190001105c40000c4080303002c034000000541079842c40d004032a91031107500010003403007100388104020a030300c90040c0d91829031030361240d4040c1d90302600261400d610010300c40754419814440d01e48441c03445124241141400799021240ca078191050400808807450400303444960380e804240c0b0305900400c1c2c0c5000032510b05000c000383c80c1804080c0707191603040000140c2075002260868010040a040d103040080d114802d40c0144951001100e01955030844540140c8807070880541128258070742d082800c0c6103141c915071114a5507110021641403440400403070b600302c0c20f512002c9a1240000c0b902c5049a6441010240789684450b0504c40c0303e4103000c2602d61781c0049820070b450104080c411556150019520b03840f41100061801c050000010b005c11155400950403c5240d100c0b203180007078010018415800c8d6800c282c0b83e20119040580714040300c00c5c0b05000030f16440c00580460361450f00060307154041840760a007400382010158221b0303a00c105600001c4c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 293978642 1250 293977392 293977429
    0xb0402010207150e030d0f140313080a0509030705030106052413030f050c040506010921050105100504050f0708270316030e040504020a091d01020d0c140301061d 71
    0xc01643c2c00900a841d5140301500078003807401080e10052080c5c0d8860280c62071522025608584503618502e15030008240b601120140100320b00007400e088000d01101e03066644041e00c485e120006c00d81040410b5105512980c50b00c1407c010580343d003100343d020b20b9403526101c00c40d0013568107045170070301c100c40011052450402c0b0102c20407118511000d817050144040711221a1140c090000701c58069900e0303030204056101c07c2182c10b54804c90509505080c1d441c1c1c00603100d65642c3e4509541c0180c82d094883e1542940a2019040034818254407034600c85c1d03205d5031414608400307400e541c0b001e0403030414620301080424524000f00c0f061214074142c01e04480e5550325001c00c44200302c68050381200000c03600c10301b50000c1d2400d409020f00072074000b000c100495103050342441c010042d4820b40b11049080e01c8a60060b00c0e007e10141c101c80042000c0440e1040c165040200740040364071042880000500c014400241d11810404070b140c0f0300728604084182d5400061038000c50100f04022 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 293979892 1250 293978642 293978669
    0x62d0103051f050705040311030c030a031e2c010207031b0e0a0b010e13060512010207030305070f020706032007030e031e1f09140705090c03010806040b0402010207 72
    0x80100024110440c405a80794082d0309655060740001030b1002501c3c12400038205110500c0454184041e12050002c003c0455856140a41c042030a0030090442900450148050712414100341c1d080d200c0c44024502d4103c07031095800d0580c80b070b03000e0200421008403036035644203a95a4000c115040180d600b00603030f90318601c038102c0700809400ca24040e9800e0a2072110102c0e91801c060301418036101d8051719004101d095200c140600c1c02403500c1940d50141d220b20700000c41d42c03500d001108c00c094004002580d515040e050240c2640d2000d0415401c10403044884109268089080b0b03060b902980b801003a4207054040b500522189145e905800c400c0008400c0304150700805240c070f82c0781090342034500c2a00408803032550b01c241b826140d01030360071140940c8000303d10641034008a1400d5800006c00c20900d07200c044071904452003085a65200e40414405480d081441e240d2003071f03620011900d5507050084540e00c035940500300820102044000c90708581c000d01c8060003030b000441040d603 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 293981142 1250 293979892 293979899
    0x1005010c17090d0507330f120204120c080601050603040f0807110603070e030c0109050d03081305193302180603071805120c01050307021c0801170a0302062d01 70
    0x4070b11490b0303d0f00300d407100034400c0e51b945600b1a00300075095151588035202c11140c10f607401c1e180c1071680108002d00681c06c100c0425180c4115003800740075802032216030405030030308007807901d00101a00028410082841040001000d81d0000c0030110f5008151545030759441c0341c02100350701c240200b280e2000d800f0040080c040da12011203010a2421012070702c64040790300065440150300d015260708034509412400210f80183d050b01c1d00000700e0244007500030f1198485505003a0070b0410b04e0a542c0607d115201400940030800c124540048500903141d40145085400c410740380703007280003035034022580346071441c50a542c00602d00d1014102e40e0350303031503d0000241030480b50111001c004000c800c0100d180d007407500d030000506401100400000003444015605a000100450308611618403080c805600f0385484109000c680c0d1035005495040400034116000c4c08844100943c2c80340a000c00400c4c3d00081e01504841c007070b003110000c01e0041603622020301005c00c07001c000320316000001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 293982392 1250 293981142 293981159
    0xe0a0f0834090f1b12020703090302030607081e06010504120240141b0f040303121a1003020f1204232a010918051005010c17090d0507 59
    0xc1540240d141020402c442c1c040071005150803039102c41c2c20004091005e03502d9002e40d25401003076098000d0800300c01199503903000034035192003100c02000140041050100d80500e0000c1e440629072004441ca00910380303100000e002d0b00492203103140f2144c0600c41c803004e540702c014840e65110f41900013844060b285045001201010800316034100e071540c0440b0903154214400c1100e106e51040403101c403525000c0d200074145a521465050f80501044800625131103003000304001d52003512071001c01059000356808440680c80d2030100845803002e01c00059450080b020301c070380d8080c20300503203030303841b56540c0c0d140c0380614000c000c600d5080d44140001d02910301c5c48200009000d60001c0e0987e80070461850f1039542403042402000100c085c041400c00900701c0000404006140c004140d60f0b0311002000341c07100760b10100b440b40b0741d02c0381884901c00303164110300c0142000782030006600d0f540769250300c4962060103010100c6080400c0c030f244140e545903c50340d00c0c00e4118044030307826600c1d1081c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 293983642 1250 293982392 293982401
    0x6030403170108030405221b0306030516060c061508010213030605130f1713171219080907030b101404060605040e09070e070e0a0f083409 61
    0x15041d00018000081c0003a80041200e040e2200075044807251444401c2543c07070b452850b0a0032450799150590002c901c04203080407003d90000e540c0208095140d81050382c101002050840c4c41c440010009200c0c2c650041150181513910450000b9a4106040c0c0c0076402212504000391035400000c03002d280c0c4206140120136030740105000c0049445400740e00041035113508000b80b048001c8074010303012070340964070701c620702003286121403400c84a200c82c0c0b1040841600700303821503200300c61005210007080224007190051100781c070b172070800152041c4005401c2000d010017000354007000a5500e96091041c44000c681c40340301e1218a0810103400341c801e4031580142407031a000072506221030715090003820101e80034ce41f2101d01d024102400403c0410700204004000e05c03440900040c3d80c2104075500d40703c0c034481d6440c2054078400c1410484c0200e0b00354480d00881011304012311010a01049002c40b900e42042040c0c00c620f02002c0c091040380038054180c0b48080c41140001d842c0015402 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 293984892 1250 293983642 293983667
    0x1506030108070317250c030813210302101e020f0a1805060d0c0c02150a0e0103050105180403110d020106050a090e0a20060d020703091205030f0d02040506030403 71
    0x3d001c0d0312074100924210341390050751503200c11a403411010f9245a104d00b2001010680542c0307409a49541b21b45038005030341e210180c95a00705448800411555403c084071a51640810302a0100c80c40c071520700035030350302a138a40304006c0d9984001c410401000c205c40030741c0454520344259154a14a40e0710b060300d400244110b008038181d42c40010310b511074054401c090b60310041007103051442090f580700081222551140900c9003104c2c4400c0566107840075407210001d02035041d80e803100c85581c01000008529460307410306017440c00510260380d03880c00030071441c81030700782c0620345070340d50b007821140060340040c1030b0950b000b40e21403074041c01d906401c00001e492081d2482180346681c0c216010881c1c90400004210b60440341040001030034145003420900524110788003290070701c0c00082c420703600c914400155540e0001c1c00030205a003101c500c200034610301d07007402c41440c1252541c90700d0b8444c0c0b2405140c94a00081c0071400c04266a05803409420003600a5860303180524001e0500c2847c2d54 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 293986142 1250 293984892 293984903
    0x210f0b040201020c0a03050a0602090105160f060f15151407050d08161d0a05060c0307150204030201140306040f050f060a0b0406050d1503061812020c06030f15060301080703 76
    0x4d10207a1030f82012009003040b240c0c0b10b8003d140700d00707054840d44001e402030007010f4108401044242d00405440001c1e2189600440150555901914141044407180504140c443c0e0810714612050f445607080c0d602101c2c25920b283c030888406000c11215010010030b6210700e0200860100140800094885903a209623101d00115846001c01e840c001045c1c0c5039900c0c0064000d5a54103204d00075640a82c8010b04081c03e039206158031100041c100e6040341e6058046688080340e6807082c803e00c018040f48089411400714581800c580009010003404418001c00280000106149132101da101c0201e0a940030700401160401c004505024078059410521944411001250030540c1d00119421a101519141c0c90103c0b900380a030080c0c8043d076042824000ca191001020400b24003070303150b00e41ca078146c0d41030b550540c41c80d150740b0b04442d80d000340c01107512400e0f80c009240c840d00101c036000203504104072103a07562118400f0700b44205082040e080807004c40005285c24001400c80143da2150 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 293987392 1250 293986142 293986153
    0xb060108060a0303030b0312030a02130f0305300a0c033e010603150c02250501030513060c0e130e0316051002040f0e1f210f0b04020102 60
    0x10001120114015079445900145100c0d00b040064040e9126500003a406016148080050100038510f5007088030359010b0588c0010704290018090a070328070103442c2110740200c2407412b40e2030b03041d41c9009e48c0200340c90b81381140807071512846030280340e0b0700c0e0f003040c42a0b0143d44013040300005180081c01e590403408120160a41c1081400301c0000044543c00101c1c905900440c3e6522071140b14071011179101595a50702001c8046103440a202071300b03400c004004140d80030740b4800245441e0f402d044100055039640d10740c0718078520000481d4222202440e01142d43e846014442c100d28640e40c400030100d0f8074106e8608041794006241ea5070403581150229440d1b4007110448060302c00390a103040e8140c02c200209980c80d2940494001d68601560448181b2400e1481090883e4007030b07000003203601c010702410031800b4018405140d21018542c80003400101020941207600c100d40103103400c1001c400c000c0c007000c16070040c0c5800c0d8036400c8801c24000c0306a40c04c100a0b11b9a09460a0b03006020342c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 293988642 1250 293987392 293987401
    0x60204081c110c04050604020c010203041a0603030f27031903030b120601050d060207050d08040203061e041103011104120203060702010524031c02011409010b06040b030618040c030b 80
    0x10711001e02c03441d600e1101400d12545120108401090020080d41e8000da0900c460f071362104003480a54800c40c400c0d045100314a0442d2000b03040e041d00240320394400d034010420701d03000f11145415900000d91030500765040042c00340740782111905410045c2d405100e01d03202c8002506d44103054401c2d2a0007920b081000f02070400500c030308000c8044240300103510100040100781070514035055564052000141420354a5072030b1303824504a1001d0b400001d00000038030007540350600c00c041d0000072010816501c503841e071074405241c06008001900b010070185413003000c0d40342034200003d00480d0f090220703510fa80301c044821600d582d048042c0d000b840f60701c0018141d14014401e9a000b07851803801225252820429000100c4a40950076090f00422403011203181640c014105400e00a40000c9120f280d1240d48064011000f0007040581c0e05143d024403140d1104000c42c2c0076621404c0d92555603070346101c0820340c66203814a080e0304460300c100401050160308048041524843c0501c041c40362107 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 293989892 1250 293988642 293988647
    0x601030b1005071112031b060703051308130b0f040f0911070b0a0b0931120c11090901020712083102031204050f010203040e010b0c0703060204081c 65
    0x7000340e00c04000c268100a40700100722964003088641c0d20052007100030b0188490701c0703030950b006a04410008a6100b143d00340b4080103000d07103031f071000c081d02c0d0800c020f103000038240048880195000c4e084c0c0300c00040302c1c0c1000203641043d03006030460440b515501d0100d8030401b000c075403103482400e90f106005680030510450501030700c00a0070f42d060321141403003040c1d181da0080c80c201401080c80143d6850781204030341c0715003195500c05e0042d808500d01d48076003101000751032450152188400600412440000341c2c1254200003114000d00c0c05d00000c2c102c6290110009019094880d8089040c0b400c00c04102c0d0150000c241726032060b8282d41d040c00740c500007030321140b00540e60074900f1041000001c5c0c0e138030024684100c40c8803900440407500c80e26074000c40d0070031401581d11034110b2030004d4203101e9070800725409072041d842032005514003454801d280103003820600540c590000e001640c2d22581108100d45005075800c000c1c21555240d40e400b00750b98580c581103034000e40020450842c2203090 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 293991142 1250 293989892 293989909
    0x2070f0512030f03060117040b0103060b19090c090909080c0106060f0c02061c020307171003110f0d12030e120a0c0f02060d060e04150c0512040c0306020d050601030b 73
    0x11a0a0700a5082400141c01020990001403a00b41000700c05a14800020051035030b8501440c019800e404055065003048402e8501740f60081d405032040340400040014940d00c00310864003400e000281062814104481d00c440c00e62180540506240c54002442a0324008100e00c6003c80000c21540d540e80406450024a510390207000c104108003900140c2807041c0180740348125400130080365461048050100c0e0001c0d40c1c89000204141c04440083c20203460141d086865007090018507440d40d9a1840c6c1d00c00c8a49056009000000142c2420b440c1d801c5102c900c1039001c048a6500c042c2c02c04010b004100f200d5040e9214400c0c080c0d071381483c01e1810304039045050640d540c0c089806079030706c64407000c8070310040c200c0c1c0001040040400141261180c171010304403016034540c0504213410200d4003c100614411207052a0000d1102c8890b04481220841c030400702003420a90341c0c40c2000e29646401c0d510281c5214000a17485002c204190700c200d00c610700903207041050040c0da40c148038814 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 293992392 1250 293991142 293991169
    0x1d0306040203060f0a11040612060b041809020a0902030c0307090e0f04120e040f0911030118020d050a06051005240d0209060418290607120c1202070f05 67
    0x1504002c001c00e907070800d022000c590040c170201000c90010300111007180c80e030b407040c1d10030f9000500c0c03000812108051405024000c01031100da090400f8100702c60941442003189103080400d646440040071911900200001042030040454a0745086106115698000c50381c0200152020402250103a0442003240c0210204051a840c1d80d80300e42d030300c8107140b040003038000a000102481400541d00c0380182e03880c1011800d4080382c05081d520300015580540d103405403203079040202c001c6200380f00c5400d203408590101c80c442c99012180c2001800d103441280e01400b5107040100b000302024a82c90785800b11001038520307c8c4200f0164940d008468011039103242161810004240c00400c40e4001c0c00540400a000c5450f041c0c0e01e1075400804410810740c50f240350344941c41c0ca900c149480e0050405040c0f4400a400488e000c00c000500703900c9030840c0200807050300241d9240062148608141140e0f01c4450062002c030719600181d41e0702c1140c8540c1d020441d00c494045918203010141c141c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 293993642 1250 293992392 293992399
    0x604050703020f04090c1410020715051e030c03040233030a0b12060a141b0a050904020c011d0a0309032d0305090102060a060302030c0f040b101d03060402 68
    0x303040c01c0d6402c2004020500d002654819200d42c03ca0002c1002e0340720200040071040320301034000d00e030346003409443d000f41c000810541d00840d500f000341d016080c031012a0300b1003620b80755640d40c2078802c0070b006400114a20704803048020040018200704d610081d07000d14022a81040d4242e000c100481d61402c0656012103d42403540f00d074825042800302642d005000c1c103d000c42c0f201080070102d80e0000114411200960084c0700784a000c070040c0c4070310202088910040701032890f0000c2c0c00000240c442900800190000640c00c14291203101540d0340858000c005542c0e40340c580750104e000c1c01c9510505841414001040c031040070002580c0c0414a506407903d94507949944c90304494815120003599031010002c04003522504085805448140310781c503615107035020300c0002460a80014030300d0105070303d003e0040c0b016a0b00010444c010610032500000d4101465000c1405401003146071a00116001d05580820742c203c0c00082d0303602641c0d0a1a0310300903110b802c0507071701c03002524007940 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 293994892 1250 293993642 293993653
    0xa03060b030c34030e040501170703030c0312110a0906090f0e06060c1c021203060904060b03010917120c03010e160e0a060801030b060312162d14060405 67
    0xc0e007031410307070408221a400003812002e8200c69000842c440450550840000e84a5100301003a49444e1047c240908a40344043c00d00f814005a190740c1c0b100d05000c0034090121400619003018071a10b60480000301070340040c4500b081012a0b24155007040d85c0c02c402060943c41c1c04202d00d07104200803000c0322803812050010300d00e02011566400400b03024103401490070800540460010450302e55159071600710a8214202500000e0416000108422102d0400c00c1407040c1075641c202c01c0c0e0b8129821800001e107245070200064010400010b0080036401c00d24810300551840c0e0000c1c003c0c40d0140c0d03601110310b070340d40548041580300034010b03520755440d200c0104003580d0382407112007440607081c2408080700040c41c0c00164000c21942c020400120100c0052080200071a02c60f42c00c004154024030b8800c0f404028013082e805407082c2e0940f0600e1060b14a402c0c003020240c1007100c64007181881e046d0081e60080407500c140708501c2035440401504010046070741c0003c841d803046401c07601410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 293996142 1250 293994892 293994907
    0x41b03030c02100e03031804020c01050705090a0f0303020d12090b04080309011d0d0e03120c0a022814010203040314010501080d09060903031202070204140a0b0a08060c07060e03030901020a03060b030c 88
    0x100107c0030b81c101c0a0300b1640c00c0c0410152181c00348a040d0080d125902c1d16a110598034040007046080c3d07411040c80106007440400c002500011440c03115111400c00c07030940000c20030520010582d070b08025190001030340602040c00080070085004890007002032200707018100d0000b030100740800b1220354640c011602c1c035400c20b11445941c0d9840c180103003a621008192201c40070140c201e50448602c58025030780341c034114648840c401ca4640000140d4480c0c034410b400c15021444860b12414850305901c0e4082c803250381c424811600610f60202020041c0d0765281c400c0b03030007000d00b40202001d9118640700b0a0440b80503010940c111103260742d40c0c08459080d643d08988003000441c465011503000d200c224011b0341c81340078240103821002180320741031030301c0c2c4221001e46070b448005c00e00481c3d5100b4148080340f80404c280b0f41c0481003a118035038038001c51620000801e00044a0b000a01003c800e01800c8001034000300340740c10203540c0030b020107525088a0502407006490f45003042130200b1405 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 293997392 1250 293996142 293996167
    0x11030301150504081c020606010903150506041803020a050c010207030b1602100603030e090f01080c0603130506070c12050a0f1b0606090b010909020906090603041b03030c02100e0303 80
    0x1070003050300520700b803410156180806071078101c80381921468620311030751103000c8550400540358400f03024a4002001e500e152103400612030701c0141c0407100c548480000b03c3d280c940390060701e046114075030a010501c1d0982402500d9142c0c0745c40c03c0350507004001e2207a581c0d40c40050007105403904001d0005032502e82503404242d5020028030902035004a0422002400f078612600c1d00540c004e81315a6510300c100010003030315a40c01003800000040c00d0300140301104000410298002007614516030383c1e100d007152107004000001005005209030020001015800588110039510415100341511a52101650140940b608180000320401c40844170b0078883c2e4880409a1607041c6011a103180035200c510654a454000000854644141101c0340d41e001d840c0c4402005020411418007003a0400189a849990751145c4200d50200103c0c0500c001c0340031041340307542050261a043c03035a03440c01800d00b40b40150264415020790210358138860240410340c030b104800601840c50f112518084 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 293998642 1250 293997392 293997419
    0x30c030311031008010f14060d060e031603020606091b0c0a0206040f0503060108030703020a060b120601090b010207050102010e150c0c070e06150315060c031b070f150e01030b0609032b11030301 85
    0x25207007550bc078003c00d28080000d10082480e001c83d1007030300c082c40d0300b28140a8a410030180502c1d025446c0300b410441100640400044003924108045a03298802800107107843c84010000c0d600050000e0000b4000d04040c000c0c0003110307010360031b650842c0e0b6038130303003054407809120405005030300f1a052001c005001c5134011107a2400042c0000c824a40c1ca11459140c54000d0704803203600c0d9524400302d02150b0b010030010b8004c2c2401d10080c49445403100c9040e8949a01e800d089000210580205039110414400d941000618008440a565540ea4103100c1080c041e03890f640110b14003824005000401c804583c41025109030844560543d0418441654018060840709010034407a0300418489024001791781c18500e40140500350a00020502000b8154440701c0c1f66200100070964003900450903803544002400d000800c0503088c07000c039000b482100060760b03241c0140200c070540c4800007011a0005010140d180c4160b002203402510005030a0200214540c018801044400380c0442c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 293999892 1250 293998642 293998669
    0x5090c04061803350d05041b06052a030a0806191d090c041415030703120c0303092108180304091a220c030507080103030c030311031008010f1406 64
    0x4070a40c0c65250b0000b13090305a00300b26004030790651100c0502c424030071260043d00c1c1c0c2800070712155980c0d0b1302e03041028283d4801d040d5000107501550314990002d8034180d852a62403a008000d40c3c0d5035140f504c1c1d004221150456106108120351000e0700712001c0001c0d20a02a11403031071144188007004d01d520b0b41d4000000304000b10034421052603060688070b5000300062400308000d14581820000017031080386c114070308818000d5005880420110703900d840380c40782c2c641a5045c001030151941c203086014042c482d10140019501074564a600a18a400d00d5142052550340f120140c98100c8207d1000030303600c4180f102e55005202c18860602158410250b4100f810040c80d014014000458101c407280844030001c1c021101d000c60390561540a2121101220701d8100305601e030008000d13100f9003040c00046c003000003d403211760406000b507010b40d48114400c0d241d0b64032454003010004105e42140100d4066508140300922114020700448854039202c85003c0c0d42995060b080c40200c549051 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 294001142 1250 293999892 293999963
    0x905012405130f1e050306070507030f020a02030601061d0111030315060706060602010c0f17181014011d010b030a090f0b0702030909011710050c0405090c04061803 72
    0x640001d4503030f41c0001c02d2402040d035511044080c500a004a0001c2407150f40214002e4101d5030070055090b502800701e0b00055070500b401782c0ca680d10070204915280034400003d4262060100204501d038003d40001b02903c14031044605480c03004c8011a94850f0140e800241ca074814070115002d24201203500c14a4030700680303a24242496602ca84050362001e41c8400090b0755a8141002040c2d4020401c20041815050140c14407092000c50480e404009090360382c15021741000d0141d550082c04920300481d07a61400b80000b09a03440c0c0f0700c445150a215142a5294000ca2940b14a000c00c1c2124100c4107910991415503840d459090040d2080c18021698502602a000000f543d800d05243c010300056004603240d88080b424041995010381181081d01840c65800c11001000280c40e850215400000304081d15154210145405150070480e4000002c00c104000c0d64070180c0a03000b00c4e0f01550303441c0016118200c0302200c2040e28040036061158071660704041a00264a00c0c5d40f00450340b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 294002392 1250 294001142 294001177
    0xf080a0309150c170c0606010503011202060a030209030a03030608071d0c090303040f030c09050a110a0e0303040914100b0a050d090201140304060e0106061e1211130905012405 77
    0x640d80c90748124030600135002d00700d102040351411400100041e6a201034282011840e55040c8098000314000c41c00e4024400c8100044030040140300f42c0560703a01280240458903450003500c1c014010f014a401402683d00c268600040d069400c2d500c030402d408000294000240c076041d580e0521544141c0f203040d094441000001a4105161004002103000e980c10404032800c02440000742c987c050003d24441c1c8c103140c2081d00e5030729120111502c8000c1400c0420021540d440030a055000b960301c04010549030641d0000e1100800100620484d01c01c1015114540c4403002c001840c0201d80c00480050700c1446901202c0c03e039540205000c030f005042900740424a01044001540202c5084405540b81d8501d90311100c001d018000140a04e810094000349415200703507603481180c44a0701c20080e00c0c000820300c00c071165100f40b4000c200c0410150780c2d0414403010b45140f00c014490402c5240c50080001102003a0900364103c803c641d0301c00c0c1c9804150401d0803101a0440d400004951516 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 294003642 1250 294002392 294002417
    0x6080414030a050c071517071e0e1503070e091032030615130b03010207140d030c120207050c120c0414100504020a1101050c040f080a030915 62
    0x300054500c182040d625981c1e2812900030711342c1480280d40c456075101c2a110b480c40d5900d07801c51201c1c0c0030b0650011480003030313985188003100c000c0d00c207c403803188600d42e280007011072507406241c02c1800c1500340c1d44841021459a980c40f05031000700d481c640000d090070802c507018500514000e4024903520504008207840d180c5402441400f4440d103a80c44100c2070410400580042010901510480183c20301e450954021417012810000c11441810401d03140102100c595000759a03115001d0000c40d242c600514001b544003030901400640d40c4034021020b11554807901444810028030342d41d40c08044c01c0003c0400181d0041101154180500d0040b9002c0340c46031402155000f00c402c004002d009041d50603c000c0701d46122900c1d005498240403c00a00200000b0320f048540c250703001640ca245100742266410600e03183c48980d5402d01c000e1012801800b0003030400c1d40e03c2001c4001209640794100c0e681ca05540c04002d0100f40030813010491520304120100200e4581d04040081c02c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 294004892 1250 294003642 294003683
    0x11a0c0114012c07050c0106030c08012003162006040b010302041109090c0d1503080408010b041e240b1210051804060f050a051905070504060804 64
    0x8020060403010420780c004002c0034809480a82034504088081d440300041e650103000c0d00b010043c00042401400242d102103c0001d40c4010025a0000c106040305900c0b01300480c044c0002c0c1a4070300b1000b030b59408640c141c5039044100c0740a5510326089080340707100b005003a1640b070001ca04480c4100c028154084200806101c1548100c0c803d003013003642581988100300c216000c40484070b94403c8103000c1c0c804191907410702540c20094540103180c880c0810404603002d0302c145001c124184203044000000c000341107002d0415601a1b0009000c003810240520045980c4042c0241c0d800d004442d003c4007545040c0e0114904140000500d00140203103a480c0e02c0b08001580801c44903603001403d0681407016070401a00050f0071080da0103075919010000d501c07142071200c000c5583c140c90020804110340e941c042d010445080106004525007500ca48004203002c4076408170480d40100382c0600c2907902d2040911131641c50300c81508150824030304030b035611401002129829591100c2500004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 294006142 1250 294004892 294004901
    0x40f05070314090d020a032d08070908060c04060507021f0c0c05040e030a14040e040c0501020f0a0b0c0c120f030103020102120f040b0c010f09030e030106050117011a0c01 75
    0x5500d07100419031002404419401c07560040881880360441e10140e601e00d0341c0450034040c1c0c55003502c1d042080024003000d01114119204c60518020000314207911601d4002411511540e140d44425040c25542c0300e91079102c1130b00321440d10599074208014064140940040c103801b41c0080c240b2031303025000020f0740200310300b03003114040481c03001403100d02009010010400035007000d560901403c03402006180ea41e0141d0710b5100d0601140e032000c04203000d8413906940050008040102160400c0c1c14185004409405064014043c44050504003d00002c039004044d0380041d03c030015a41e406501602500406140900340c0250000741c806401c191014007110b035a04848180e5a51461001a141c40d080059141c10640c0503c00240c0710403120302a0b038201c46000220f5682d0700e20307801005005040c0100f06155413441c000c1038105055004040c2c20b00c0036070581c0208400350712000199150024018029919070706540148006c0e0070250020140f07844007580070b81480e4002d4906401d40c0d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 294007392 1250 294006142 294006151
    0x5030a020918060f060403020a0605031305071508250f030f02070830040b070c0203150118060524070804030f120507020105070605040227060f1815040f05 68
    0x200e480000f840050b2500d100c030248100021520603140502d1039011803002c51035440380b1401d101010001611620f4030092800010390701c88140e0301d4035916a14813011002010146900040220300000d20003215990900b2159600d0051806080e20a802c101e5030051011004c504050f02d90107456400e41150002e40b81d000c0c03042c22450744910782c110081c1d40407046000c01509481034218440403200508050603005904544a07a22a41d02c0030800e0b01d0f20740801000942511074401d0301d50743c89503e0741d04107050310851400c43d01c1640e025001002580c5260050360760007540d5031a4032266049072184409516800300c4840c0c05d000c440c2d00d41c0001d41d042030b0f2082c0c0d10400c2e016408010018841c680d0a03080d0030b54180f030313030824451f40c00080c43ca00864a00415150342d44001c05d0a43d41c521010002c80c90002c100701461104900b250080741c182662154000c3c041c0141041040c038007840211000200c100464035181c1d200d0318042011a0002a556041941c40340081c52951142c0901ca204 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 294008642 1250 294007392 294007429
    0xc130f0302101e0e03031b160504150b031008070807081212010b0304030903051c08060906030307170706020703030903020c010c05060c09130906090c08070b040605030a0209 76
    0x491450051000030001803818104006000e9086500400e0250611822050720300d0620381c085010000711b8658800d4105601c210040200c000040c0701000442055030840d01400c0c0c072495990364180025035260024517900b42078861000d2021282c4175001d903034001c4103040d580002c1655152440d0034460340c0d070400711032a08440d000340100c2104000c17081d4044010840c05180a4a0310981210400d060250b001c4c0081d0000c04035086c03610822082000d150090b0035290721358828003440c071211142d10446008900c10b5800541d003403038010515885010090040e503e00401036844001e40c0034022a900c809040c14040000400c030325202904250340309803400140707400c1904010385010139070128a810004100d61305800101e020640580211520322020346690002c00000c11202c0f010341121821032070803140009024803504001c1c0c5150049501c0d03000c068a4185080d116907280c080c864021004110400007580700b04021a48908418401801c1050020010780d60130078001a8186 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 294009892 1250 294008642 294008669
    0x7050411030117071a0a030f0c120b040908090d0311030c0709050901050402030c011809090609020f030d05120c2109010506180103060c050705060c030f0609060102150c13 75
    0xd6a51030309810101900c07000001d2a0b21840c0080345c21517206210440c0c18201c0c0041800d408441c007c0c0c00003414154150418040c40e021408014030306401030101900e950700340300a045207030405200340c440460700700540701e280c03800c0f00c414000e0b0741c1b4030000f0860401030600f0032228001001d00140259500910180c001140b5214905090ba01c0150090032280d00d4802404011703503000032402600030080c20041d1103e4107041c101c8524081c01c0c0d1010041d40e040606400c1041420703400f8603069442101e442c6a081410030a25544906494085020883c208050310605035070f215501c1c4e1100e49500b1007850000f002c80300d042c03410004001011f0408900c014046006400c0c0100350744424203680716120b542c103940d0140c880030070621010b040f04d0341c0c44440b158a01d00c5441103510080d0001d040b6500da0070702003a2280140d1045a40a9110f80c6400c00f181c40c610b48804441d000c0d4070141d00800d0300341c1d031003a214000040c0180c046050702c0c1c4208018056a070740310f5004001809550b0030a40c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 294011142 1250 294009892 294009899
    0x10e040c021b060c06040318060e0d031202041203020a05070608010506030a05100b0d0e06150d030e130207080307080109050103020904060c0c020307062003070c1203021002030c09010e03150c0c070504110301 91
    0x51448d503458200c0c2041c4111a100c412aa484128441140c15014602805a105840c000b04000d106542060340f00c01c03189440c0e0400c0c50740004401184e28803900c11541c4c16035032034500b101e03050020b0041da0340c44002080440e41075089500819000a505000001610758595800c19650f00c040070016030f007911002c0070940010b041c0a055800354082580000707800f243d20002d00d000c90000f100074148400160208401e4079405a000012804250115a1110141050140313a0001c072a00f03400070381c4402c0040381000c1a03001d80340c101caa001c2d0909a080d01c45a0300c01006d091000f07111001c0180345442900541d40c01c009030701c02400c0c291200007460046118222080c0c01c10015803416500c20880032001074429050b80048480b07411003040300300c0e05464100c1c14055003000c0e28954078004010310a40c0d0340054001c1921070003d0300c0d504d201540e8402410744403803108841f401d010305c3c140c00041c51071180c0c800401070300b140303030013030303501c80784c4c454002030101e46140c1d8554049690100060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 294012392 1250 294011142 294011177
    0x3071214013c06060e100f050a0c0309050907080132060903010209151305040902060313020102031309050a0c030e06010605031302030109050601080606120705060d020415030506010e040c021b060c060403 89
    0x35181b01e981440c1c50b0018002c22200a44584240200e900411451029910a140c803412405e400391100402503c803138100010000d0541500b030261820100c01c0104000010301ca5034921454100340300301d0308010034100000c0046c030b80c211540700364065400308407040302c0b9a507404c1d2070f48a0285c1103001c03980700c0da8101d0440e205400c103070f04400d0145240c2141c0300e015079148800c0e640d0040110640001100f01480100d055001c0c1210303c5d030f0602c021002c081410030702c0c3d4020303603c21180004c0402030352103081411019a8800d01010100b80c010f0707130040c8007280c49500215404400c4035401425174000f41e0200b400c60343c04c00c600b0f903401d8000320014090b0b01003d02c121908000111815004000e014004645038205886028070490001803603182c1090103805a4008000d0710400c0e030600e80310480050b0181c001215107a0015072812100000c619103803007940b80a14641d0700030314983c4810044000303802090703074001d6132040c1d050001452209080010710b108500c02d503110b00d031168015030369 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 294013642 1250 294012392 294012409
    0xd0608061602061b1c021e04030b07090e0a0e070506161e020a09090201020c090a0c02120f0a030504080f0a0f080a0b060a0305040c0503071214013c06060e 68
    0x50303480710241c00107141c1d240c18820944151341922817440c0b20711410301600d54004c3c8a1440c465078121080c5107200000e071900006401242e028a4124400c1c0c1d44180c2c003141d010791103025100b00750b401030b804502c540b0400c1d4419000c0a000c1801c039006c06031220009007581d00314903204009101200384c2102003101d88000005540d00c01c1050400000059002071880e1007203009007401242d459400c40c0c2561310801c480b508aa90103081d50455090441c000342c098031215280d0400341c461040c0b1000300300389040445801c4100c210190b8240541034070218050301d0f0142c003e0f03440c100f090081524900105004014001c00c9440399016281020790241010400800d82e455031450028040c0b50f50310b81c88200d41400c6030700c0c5030001e03559499180c82c82ca40842c58002c0394051054080108500308001b80c405807460180140c158603c401d001a0790a0300c10340751078481016400303100364501020403481c0c15406081000700060b000440d0107c00f0484a15500080000c0c51605c03c1006a0608241 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 294014892 1250 294013642 294013651
    0x1a090a1403070510020405030a030f021218102a0320030c060a090b0105090a0e01060f050117100b130312030c09050d0b010e190203040602030405070509040c0504020d060806160206 79
    0x1d40c1087e241c2800251a40100d810240601c484150b0203c43d0f580300388103203100c00c40003240c031030380b10b1000e4108440f406210021050041820315040c0103440c0c0036036051490b10561100014076003014441500c0d51000d518021014400c110034000c004002d6484004275a56007000216104d2010140c454a0003c0161080304070034540704200340890400320415054400c282e503154403544440e240342d030007803001802d160055481d1100c0030840381ca0884040d0100c4000343d031640442010a501c0d49071800080e00e2044c108480031008000400300301c406801d0724134600d02e0204040b9a81d071120003070301130307007142c110002a500c0c0e40715009030b40c01440300360107003505a42c02e1000842903a58941c00c0e01041c00345218003143d1200262020805c03180e03070008101001000d54aa06043c50248081d420949045582c0e014814001c21541000b6010610440c0c20450009050f40ba080034803000f5071009040c4d54500c0d4070394a01051824082081d94054002484000380c10710080c400207041c14070151 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 294016142 1250 294014892 294014923
    0x130b1503040c030602031915090c091206050402060f040e040201020d0804030f080a150605042306040e0709030c080604030311130506180307030b040b06010207031a090a14030705 78
    0x900c4041848602c2000960f6402440143c3d40d032900301d02504140c07041c241c1002000d040c81c800b860314001e1042e181c0d080b124000350500000104100565a0700b283d401200720f9040068900d2010079696082190082e001802681c80e1900b0005140b4903680950041e4440c00240d0302407004650f4104042546604c5074a0842c560b814940d42c0140954081d1006504000301070000c642c41000715440b00e01e100407042d5205061a41d105005041030300319100d20303071130254074151b400038981041c1c014988103080108810318060401031161206680503016000308580517074003000180761144908003400352100104a1464a4600202a01c0b900f8102e2038070f1580502c0540381c21104d4001c001c007983c1c0100e9581d41c4483c0400648514602c1c0710f005240e0500c03a01c0000018899010059800b490181000d050103036910030040ea41c1e5032451000070200c803505034503504000c101c10b00981c6c000c014042569983c600d95211400d01c1000c2e6082e0495070740001540c441004410850424501c5681 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 294017392 1250 294016142 294016147
    0x10203040209010915080f100501090e0c0603071818150e010501120e0105010f0305071403030720100f120501080c01030509030f160201080702060f16050702130b15 72
    0x540c0402c0840c841846034076a5142c07590b0070080c420701d41c1604440540f07040c50446c0c040d03482da03c60690742c802c2d01c05945241c507072408001040c044c009000d10011524030030001c20040b503580e020310003070398001003c103810020b001e40b504021409050002004080d044016210800030140100448050384c00307070031103043c4003002003080078084200c040c111102402c1551401541ca9048405000290740701c8415518100c004075020310502003010030b0b6801881111040c548034a0502006090203041d5941640188510000200032419000c9060044c4403c21600c01400000c02e030800c640425007000300b0640100d04000039408802400e0b4154003180501c9a545002035554075500852a10703810951200005a80ca0008004480c400780c02c1c00281c0d980e0710942c030004070711090210422400074140801103140c0d61b200154081c06031030009404c928503211102041c100c01041540312050000520660016036101c03146403869421004011403904440307404c020721030b42080031980203420113 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 294018642 1250 294017392 294017401
    0xa1d060a0f140412020601080d1409152109160506070507120b010503150606181c03090504180b130204110403120905010f140708070f0c031202010203 66
    0x518650019441100001c4550341040040d001d08102d251018201c6140c00510080090310245154241c401c0c4e82130752100e0341c0310703200141c4a003100307031400300025140c10903295607016210091194007802040d050380106900c6034841960098080031880d034071001445203100340b928002c6944180303408040d003c0075401d5292078900c03645074050340e8000c64020801c102000010012140500401143d000120346107142c802d42c8501c09024950290040005c00c1131302210811845000c2c0342d004000301d04001d01c2c0015800310103520b00006074440d2001288841c0c01e140d4817040000c05000780d40b200301050a020a00c015117111001080e414035080780b0200c080f80184185c02d812a100c10400c500f030000900004010f411101302c941004200000c0000400900140c0d000316851152500703500b076955400103495003c106a6850041061800b000e060780c20120010409103101d941d0380703814401e03507458544c0129040d15040325810a085000c3c000d001c0022034080c0441010704c025495481d1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 294019892 1250 294018642 294018701
    0x901020106150f18030c0f0602100911060a0306030c1e0506090d0305031803031306050609090601061119050f071e0b030405010f0903030204050a0b0309070312091802030a 75
    0x1850032100c002c02c004c031102c0d40d540d4120f501d001c50046400590001c03100e5201c400c0c4410b20142813040030302500c1041444120350006001e0f20240c150080e6480d0842d06243d010303c140790b44602281010181e65520200c00a40303d071490502400c1d199140b070941c2c1643c891800418503242e001184900310601001c1a1179076100c00c4050456814501300383c0720b4a079410000e10050b41c0100d203072483c0c040441080700480e1408803180145020340d2080c800d9803210800d000000d40c09444982060700702100600440340941da00210030303929041121345128154009060700c1c40b50701c00c12a89a0010034001c0c40200c8200f04603800791041e01d00801801900e10100a016403892088042c000380c044002000c0c06400c0d880081052070342203051261345400d1600034004e510074040c151003400c1c992800314041d4283e1042c2c91240c14104024924a41107071101583d03038014010050400c40d440f14003144220005500c0f101c50391514801680386d0508000c08000e44030b8001e052840088100103801c000301 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 294021142 1250 294019892 294019907
    0xd021801170d050c250806010905150609090604110c070308090108090d020c130e2e09020609040b150d0f0f05060102031902070519180504020907030b0a090c05090102010615 76
    0x107508030005ea082800141c8a8841222a40400300318000c100000a002a081d00070310700c1000c8281091a595004000300001d0780aa280b8142e00100074400088441c1403650005050910030100b007801c1c250703081c0c0c00c1841c09080d50004c03110040c01080602075540c111003480e4000c9041030280004103041c410003540c40c4040000c0910550050300c400c3c4070f0b0340c02d550002c2c41e1112900140c41c0004101030782d00c0300c44c0891502e41d100182c8070f01c0307040306203031110f01c81d000d00c85071f00420072441c0c100e1500070070000c2c09100c0880c5510604d44828500030440410080643d50a0480301180c40084c0c0f0003040d003108e55012401c4c001ca4205030130440d050703a01204441d01a0b0b600c120f03148444844020892070710f42c4c03d4100da41c014081c0c8a6040034524281c451404452068814030059881c5044040a842d400c0d00c000b500245c400d008a405140203403c002902003000e01142d0340c80d590f4010f00300a60b0b4104054101252002135500603650307081c09a1800340520007200b00c0e84880525009018a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 294022392 1250 294021142 294021163
    0x20d0c120c120815040506100c17120a051006121e050903090f0a030803011503020f161a0708010b090409050106030503030603061e060d021801170d050c 67
    0x1004403840c14620354007589084600c1ca030040c2c0e856410b90340d990720240820006884048041105600e0285286024002c0600ca084d02404c1d00b018088902015100303019041c0f012240c00c42a6400351100012600180205c00da48808824550030003551560071a40003801187c1110030100302402440d404c03641c1546444022140055200000b0490380c2c40c0d5821215081d801c141004144080d00d00c000000e001510741c1144d039252001c401c10100802014a07110042015105000401288a2054601c03101d48007074100903142c62100c0141e0340b00eaa1017007521001c0e80703281140d64410301ca0442610100e07a034904000d009281090500601451014499540307603210004180d007841d00d454009110103607002009101154407850019107036081220003e000380302d03036000a80091f100810301d40095406010112540e200c04080c0100c801d809a001d80c3c10070043d4000c2c0544040e0190b110b4020140e0760700c4606034001d840d680303500b0a00e514682e0802c2081c18881005a43d42c041aa480074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 294023642 1250 294022392 294022403
    0xb01090e1b0d0507270e0d030e0316030c06050c0c0c0f030a052a0d110114090603040c032a0e06012102130b0a0f0c020a0902070c0e07020d0c 62
    0xc015914000b44500701c410500410a010f0f00c1400910005000050400e1141500b41018192801d8420310100c032000e0040601641c08002c050403580e01a50000700d00d560010280c910703010501540b40c1000740505011000079500031440b2087c04001d209541d00a80b00e2003600d413400418110850b601e8402e41e0000b4421201001040e9146d07a040082c8200140d0103003e07500805060900c801844c1508040b491844541001d55036840c600302c0c211300b540c21342c07140800148400310030046441e0340c240381400c0780070101040350035156900e80c009103204511803e0f00a03000d0381540303030020109408245c045130440702c0349074440c080d0390742c07503001300a44e03402e0300c80c2e00141d545540048440001506800c9411211940c00c2241c0b0011038000700b01e83c000000702c010a4903035800c06c0009034810300b080040000c0007030b002d072110b443c483c5680506a60005040c01d50740d6403225014022030348003081c1150580c0c02c2810030008908280003240d4050042d0029042150410310060810340000384014039 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 294024892 1250 294023642 294023683
    0xc030402010e120106030605042a0e0415020c010b15041d0c0909040503040303080601020c0d03030507030b030f0d0e040e0d0f020a050303010e01183303080a0207030b01090e 76
    0x4a5194403c0509118103004000d002d644d959060002c001c01c420344080d200036051868034420850384030041c0780c5c030307494200000201d9444c2a0903401c6e00000a441113813040314001a25510400a0000e050642c880d00c00020741c4607107010030030083c50a610380d07054501c03105000800234040585402e41e4410b070355900d030f090544d983d030202c200d445c41611a4036900080660511050003800005801607a00c80d0f00c8113480d5444d680300690b5512180420b40750300000d14004103000034403d800c8107170090392a0034040341d443c000d4400242007440d001940a41544540c01d00c1849950107440080709001c240c0e01001540c100c45851601c43c42101d600d0300c00d0000c000c0070a04001c0c070030041b0700c40c0c198004d0160381c2c603541c4403480b485810f042032050300c80d1107407003502c0100d941e0030314440c00c0914a12541103031459000520560161403080c82555a490340b880c00000119800b00004c1c00305204940c041c140310f07030661030301c071406038010f800c1003080501c0e05048607244000050600c0309040601e03003810 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 294026142 1250 294024892 294024917
    0x509010509040906020c0d020307080d09050c13051b04050f061c0e0c210a0615090203010305011d0d02060a020706091a04050d030902010813030c2001090b030c03040201 74
    0x3945031080550958000d4503200c003460600601e83c0c05000e03007200207419100e4000c07540004030799078040e0701c20241c47e91104001d4800c130700105500a0242d6480340d070030364002c054994009050310000b030380c43c260640d84030f808020040342d68500c0710543e0500351010743c0c1401d040401090701100203650803030080d44001251010061441031440350951160010b00c11955505511070b102d0700044c0219001d004091044d040d02004203140100f4941e10600034514850300791036a00c0070b002c40503280250500e0b43c100c003003a140071038001540070718010400890101d410030220400384050380e40000d1590884601402096170114001d038000d4040400903031a14860706110b001814000c1c0c008007074074080c100c00b000202403130510130300c9103000b84103a503490388a9a0007541a00e1301400000d00250760640010f000c402c5d0845901020703802440c054004040075550064580100c100c500031900d110415010a0341e1300400010180c00900292400d505000030f00703002c02d000180000f41030103105180310 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 294027392 1250 294026142 294026147
    0x1b021005040e15310504061d01140108030c0304170c060c012313031124150406060909090228030204050105060703091a071b1d07080106050901 63
    0x4a0160007524509082820001290541596083c03042d50240b41110b6507840140da4081d03500803101e5040040002d91141e081c00760005202c000c008641940e0344200b03035240c0b046901210030440360480c0002841d028031002c1c1002c003801c1680100080c2d4002c0110390b242c02c00200a5604481c00d00c203004c520f41c0392800006040c4042312f0140341c0c2001000ca8810141e2005400c590750a600ba00310240104232400100b422030030040703801c0034000203400310b8100024411180301c10011400825103580c900481391a100d0208004012241c00500000344154110492980c0014040072601041450318100014068201c03d04c961303203000359214440306c00d54960b408011000d41141d441180010020013503c10900343c1c80c0001c1e80500d113000c00209090600317004841012340c15071070f401880c41c90001c1c24115013180c0200440c001005004480005600200389454402500007214013142084c1c0c038a40405600d021f4110300705102070905c0002c03504000b1044c150360f41894481e5540c0d0048005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 294028642 1250 294027392 294027397
    0x100513030203061e0901050402030d0c030c020405010801020909150f1c0209010e070306060203071a10090204060e010815011706031608030a0f020304060f1d040e1605011b021005 78
    0xa90140222001c102071351403010382c2c08a1590410503c04030340d84800024608a0341d040341c00942540c0100c40170203a0a02480b80340072054401d190500d5200400c0e4081000e983c020307803150f00e46070340108844c4101d20f0101250ad5000507498012221150100001800e00c03407030f24029805260080b2050171800c10350300f150b107070b81c2d074010344030503600d594601883d207821340101c0704880045c1c03519101040140c8040f00b1240d4658201680b001d1211500c840f040800c5405041d904418440389000501c901150011704020890303a210224804141000580780950050a10101c50780c00380380b8007410f85c3c1045800c5240d12010303004051a941e600e000c00c0c604441c01c455010b4000b04c0180001c3c02c0340340040140341c0d4030800c0da05c08000c5240d041060782d90b4040c9014070004a089541a066098840e4001e2420840742442410008505c04046000c40720b0080082e0075039000300c1000081e200e45440c140d00108401c0ca4204000c54071300d10380144506481200a20590f0641d1403041003500c100103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 294029892 1250 294028642 294028649
    0x109120b040f110409030c0303180c18021c0905010b040203090616051c0902030d0503040c0e0405160806060103050c09010509013e060a0501050d15090503040f080606090105100513 79
    0x1041100131913a003405000c7d000f00c40403c030006070520a01c0d085a0006500004540d6030088403007544608107508141341e14645403100084c2c40d400d010300894543d00c501c85d07200c842c0e0070003c000340c04803042c2030140c02c3d0380f110804603000e14010802c0c4040da0000040300341e801800d2180c011141c2e444c52804541e0381c440c1d00e5412250700034108034810a21616800860fa0510132011517800b20404001a145c0d400f085034081d002c0403450704104203880c840c2004030307030191140d0240c0e0441030b6004c1244041e510150080c2859521050800c035003560144602908540c46101d541d003400ca10740c00003007a5106410a1604200d60000300a0414000e808907042c440c031843c00c003082618149000581807805c4043c03007100d612440c3c1c0800d21a041c6c3d803103094140d0b100500300d90621845078460842031200c000c481b1403040c0d5070b50500c001081c41400030b8000b80c0b48140e01801040d262640702842c010014104920a08600004010596402c039001c0038800310341c10600e0b15120b403003801a100710200d92 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 294031142 1250 294029892 294029899
    0x2180402030c042409151407030905010f09050f101b12170601020d0e060c06101401020c031509120721080601170a0204050613050109120b040f11 64
    0x1040c0b010744050740c8054030540c1d4450f203134450040c80b800b0740c5205140109669801207a01140b040c084154202d160f601142d045041652000044200600c619484644243c1c0010840103081c0115a44407034500c0b071b92401442c010050508110015001014081089104142c01d83d0010300150269461490001c10340880c8924240203041007003215280c04400b0001800410150721440c3d9842c0305680500c006a004012000d000708040d03c0c00e180311407200340c1c804000d00905468501c104601849111400c1c0c1002565282c112003500001708200d000341550045000c5d1645900d000805104048041e4190312694450490b140d051000e0b03d483d8200c61200042c5100500c154070300080344034108400c9601c030514007810300302d030121820342c1d500b40015036020480304c08040d801e400b545c1000c030807071006107003076a07400c0000c1d000d034060741407030091501c3c440c410051581c2200f641c20040c0510b021140303444a00703030350f00880d41100400003040d405200403a5010302ca4016080c201045015 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 294032392 1250 294031142 294031147
    0x17070807030b131e06210f0f050d21092406051c020a050a03020f09040c050a0f0f0605042907120c050610060c02060c0c03030403230109030504030602180402 69
    0x1413510700340704081c1c1c40c42901c9640c100080050745040c0144041174600c0041810f020403c81d95039401c01c9403813102001c0d10700322030046840001c01c00c2032055044041c0340f0f4488214000310180440308090f0150f42c904400d070300c0d0013502000b158020f00311443c400e40f01c0c24160b80894001c2c043c040280482e400c05500304c0070720f650042c5401640c101014200d4003c0311901d4160380c0e210704202910400c0d0100a405c0001c03500400c03268205115001e070070500c00e80b1302c01c41c42601d4001280c06201303c6d45c021004840400301c2080358441d203400c0d40018052a181844c542810031001e464030f40300716051401c0d0440c041000c0e5403000b0700c240943e4215030303200400b900291840f8100401400c20400300381c03643e0080b403010420500c01c00440004075a25511802a0042c2e11340802196401100100300390380940c8003004140da9080c070090000d544244000f480020318000c1c500c02444824660b450f0607807410010302c000c00d0300441a00c048070750100000da5222640102d500300d100090b400b1a0300f09002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 294033642 1250 294032392 294032411
    0xa120e07120b0703060b071e1406070210140f0705030405010f020d02040305100e060703180b090f0f01091703091c030b1201090b010e060607120504030317070807030b13 74
    0x1824102c40c040e29903035800b480510741307405a21015105c1c00303c00400c1c100710400c0c00b8420f0720510340213040003400340c01c2c8010440c00640c5154209801103c2020060f00207140c80f17070300307043c040c030540388044850fa400382c45a150107014410b0b1800c0c01b6048100b481400f00005003002403d40140d204000300d2241903407170302500001d440c040d4006000440c0d0f607005009085507107650724070802001d0300390000105082c0c1c4513240c1c198000e00c541003051150a44071000100420701c03801000b80503090800c02000814981000182840d401c1406098130340d040041440100b0b058100c9134140e261000b412076074a4482800007490800418101e080089281120001241d059448600c0d10401901e20200da80f420000f034500300e501c0040014403240100005001003c840c8a0040e031200025200c03030716203802e41d25160b03014038140302c070385d00040c03400541801055070142c580b0b221070034002c2c00074910b03040004e030150210750010058010540c0e0388660881c80d0384c0b501561480040381c1e940c200300c3d140c007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 294034892 1250 294033642 294033653
    0x510030509030c15011502030c06072609030d05010b0a0f080604020d0c0c0209011e090b06070213061a04051008040606120c090b030606150703020a150c090503030a120e0712 76
    0x3440b60ba1410543c0f40c0c004420b447c004411180c140003160040c04450340c44860940b0003111841c081440326894000083c0302d140040285d030b000c0c41007030000b1511070a0f59540c13101500c10507000b05062060502c038032034146030040c043c104400c41505108a80b541c4001c0800c00a000303160350548224100744071040e516030410b002d214040d000380c0f03620320306230f0701c49205201d40d640041546880c051070520402455105070301c014200c5600411a514008041c0c0004c1c2c00c06148a143d56503d59503486e04201590b00000e1005081404040060800389010005880d90000920107400c0c03000810000d03080140d05da002c00040c00c03035507600b546150401d01300142d186041d4064071442a03c0c0c400f450340c69140c005034141c03003500b0003001c106001003258010052500950740c114194483c907280600029004249120074010f104400a01501200c60081808810f40c1c01680250000c111305007900c0d921114207040c1c80185403012910b03c1810a071f65180c84030070350201c1c1d080d00603940504100f10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 294036142 1250 294034892 294034933
    0x120f0311040605120a05160806060705030a020f190218090a0c0602010f0e06040503040b0c070f14040b090402011409010504030204021810050406081618080d03150510030509030c 78
    0x4a13410f102c0c5100e94400140340101d59055407081001c4405804001c204c0c0c0c4107a03a15130703103c54050841f03402c015083d1784040c60b64005803c600b001da0460121a180e41e84100502e2106019680440580301c2c10364022072542c00000c001c3c3c0c0756014600340081c0032041c0400016015640c401c1260302d96a50b0780304000e0081202c00c1d440b02200c2e007030401241004c01c00203040ca01442d0804007541c5005d182c01c502030619400201d6a40d600d000303a81d4001100e2210071041070081c00b20071543c0d2840c103030000400003103800d40a100380c85440202e0510015036484084140b00d6070b9000c5a042d52420160010b0700c9901503580000d5000d400002d40003031880c05030f54440c078103003400d40f84141c1500306440145d403035000d00e0007001c00003041e0b40b0008001660f14490102010322500341100710a800c0040300102003071980200d00710380d001201c41b12500b5407512440c07500e5240030507030034030150406000442d54020305042004041d15030021a032001014012681856445001c940c01e01842e09004000c20303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 294037392 1250 294036142 294036157
    0x151103062110022203050c01030b0307080105040f0b011e050f031011180d0b060d03210e060703020f04030206090f09090a031704033207210c120f0311040605 69
    0x920121401814010300d69000300d042c5ca60001c040c01204042c8001180101000b0020f01d5040c482c40c0000104101c080c0b08160086015081c0380c000d01000d810310f600c082c40c06a1040700c908001d90303055280101c0986007201030300e804588016520f074030800064905841c8024145246240144070b04200c1c0301c44000b0300000028002c031010300041441080821001d0344006818159100c3c000741c01442d1112110390f01c03512a082c5003443c14501c44000d07001c8102084000c5d50169616058884c045080140542c003510500d015480c04450202c044554011071000a004030004200350680382c2d21200301000c400d0015100094a2500d9132160b40e840754100340540c045188040c83d840d081840c4070280f446580c141e102e42c004490b200880070000a0404824040140400c070021150354901d8014001c4900840c42525040d4085803800341107107101641070140145190201c001400b200138049042c042410882c50039803502c8402e8010384072280c0d045c0c540b0703840050049441c94025001d0f2040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 294038642 1250 294037392 294037417
    0x60610090b0f0408120a0807030f02070804080c1e03101508030a1808010c080121020303190201150321020c150406030b150409020714150415110306211002 68
    0x14004411002c0040c446c6080001c0007400c0940018562030080c1c001490028090b0f200501c0c00c901030300c4100c1f0a802c16000096607401202500410785029500205002690f800e841d0300002d144000a90307a04503c108040d0054503403504643c2e000900155100800350001502d40c0d8001200307000306164140c07000402600d0f51a00e006c10343c160148220301030380d8800e4030b038604aa403d00c02d0f030120003092405c0b014505600c0c801480016203045c0050950180c081811640444d402c62029007503c07c0090b0b07483c0080c240000400c0450f036003240f04500c240741100d043c64400b40c0020120b0500c1484801e50307401a40100c9480d142c0e0480c08010003c5803c55a01000b4551b550700401104103940002c1ca00c0e9504103100504c810383c4558018000300384681ca0811401c0c00c1c24811608152241d141d81402071482d8040105001014403580215840c030f60701002030230a40200b0441502018100c14000d1458100c441c1c1e000b44407001680a41e8540e1045400d5014610010f00180d400725100541 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 294039892 1250 294038642 294038653
    0x4051809100b060a030b03100f0515010c0803130c030f0b0412050a0e0603070504090e010c030e0a030503010608040f020904120e0102070506090f04060302090901050412090602060610090b0f0408 85
    0x1948a05118051030b95200a01a070310305012104100c019111401049505001d000c00440d41c2031918440c04091a10051010401d850504e032480b0750180c0311400c0070305104800e401c01c0002841401100d6100d40c6d00c81c0e4030b0102d051141480126140c1ea9000205492095042c0034140100d070000700c6e10a0340309861030541400c07400402c50301c50003001c00130350120b00d0b544205a02c6280c0b80016503404089803401034141641c1d650f0800c140e480606200c540b6954070b00c049840070307500d03009003101d4025100c014800240160b40003081b911051003010200f108550205082001060070000800e40092070050181000d0800210b862492503602d00030580069411869500108944046070b100800540c140380f001d000f40400c00080d28411a48103a82e01030100050b0344000c0c10a02a4900c6070001032603241c5840d002602c50042400181408a40501005100d0340022001d43c071a00c00c0ea112446031070a00401d4404000c00e41000505c038a000c92240ca1088881c0301420440d1900700444a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 294041142 1250 294039892 294039913
    0x90f010b040c020d0f030e0a1103060601020307021f02010f0e030a0e121e0109140706020c04061401030b0f031b15040305030301050907021504030801090b03060c030a09060204051809 80
    0x858002c0305000d0096000070b0901400c40d802198601c1c0280000d085c04200001c200046900b0000220411150725207001e00088190904000c1d60360301013005c0c0015854040b241d000a283c0c0040d01c1d41640301e908820031000000e074400c0d044031042600c10142030110710b050034401c50b181e421075688440065440480005c40703140c0b549501003030b1030000c0c0141264141d1f0380c445a80903158080c240440d50b40b1040d50400260045014100c400d04000c003030041d031424000c0081c10001400c10540c4503038104a800e00600f14084020b0145410908001840c5128400814030030360351254170661500400c621560510407038031954240701c1007101c2418121101080054482c000d03400f019102c1d41c8140014490760504150664010320a401220781403640c80450000c54001158118002002000100440d00c3e090041161450007200501010314101c0d550300c1190100900718000346032034884031010b00c02503a044030302034100503084a2035000a0450301e42100d40c142c6540156204100800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 294042392 1250 294041142 294041149
    0xe03040b091306050906060717040f0618151209020901140a050102010908031602030408030c01062102010c03030f0b0301050412080c031312050d150302030d030c0206040b09070b03090f010b 83
    0xf542680c2c0d0051072441940c6841d018000c441c1c00c22441141c5000c1d4260a642c2c00075002000340009000d01d4031044103030b600346400101001769052210503880800f400c2031180d007102003915101d014461070b121142262200011000d8940602d001e07400420050002c41c1d00c80e4080811900c01d1401d8a07144021541c0c0d8004900b22124100e010301800c00c1400483c40701140107002ca920300306c1c0c03031044a0a040d141c103415800c5030301400c0c1404c216951500100010810748140704c0307a03001401c200c1c406061054001030b0240c50298030007000c065581d280c421007841c00e0b5104105d10200035000700518540380c038140406081484025000c40d00d0500052003281201088a1003400105502c015a000542d6031034040e454048030603040c00014091748004203081e20a203008924044014946140b035401458145000000c1040405003005a44200660000703230a607041039211800b1032007aa01c0d0400541031201541050744000e0b400010701500060014905544c185004000c20102400d003040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 294043642 1250 294042392 294042401
    0x19030e1207081c02070206030c0c060115120507110a030806090609040503190c021008100501090807140402040306020c061b04060c030507050f06090a1a070c080d0e03040b0913 77
    0x4002d140b00f040341c0041c40301c1e114041c40d041460703d10f000d030070003100c0d0f07001421503001240ca200351445d01144555641e801000880d004151034401c14060700d401c0d401c014003004041840c40170300c0761201d0115040d18400c52072141f00640703040503108081094500248100410749003c0e10400341900481d103149030030011580a00d50100065151068954205400c0b0038440004818807a08130403260150b1140061402d240d40903a80c0c480e02440d1050f00c110300c03406540c02c000d0400440490500403035030b0000724101566418099410f00c014be807400100a4400e50300001c10450007c04c084c0c5146200113207050080030b2a108a0044d080300c01400201c500480c410070300080e00545541e80403900500c000c02c0c5081c02202690b1200d0721165985103000c20179141c503103555001403d20014001c5100704501500900901f2807514141060010400403054a019081500008a1480c015107aa1004203290500b40a89031103d594000030310719034000010560150401e100d030071850409034400c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 294044892 1250 294043642 294043657
    0x90b0603010b18281d0a030207091107050a03030e0607031523150a270b031e130606050d230718090309060c05060601080c19030e12 58
    0x44010020880c049040400e1805007401c1c0e401d880458a03001007503222000c05100c66202440802d0340d0f05030072180c80c0040c280f02405c04841d084007901100090b030109514040300c020300404600c035544624041400c2c440c82c2030081c00c1c0e105000b6808100754064000070ba0b110003200560f049503507070341d400f40c0982e1140300500c0d00c3c00f40c0d0b0620a011209021107114041940144000303182c0e2025404100100d10b12036112070b1850010a50094035039001c0000316540c0c2c0e056000c252260315500035807000850500035021005004070002c1c6681180c2144110441c42d00100009541040d82d1031034600c004103c0e007511014100400891103052642e101500940d005034440c00d16202c4a0301044903440b4122040b040b80103003200003a40b403e0031041c48566111014000841a0180c135002c0c1111003180e100d14244002803421501007900070400e203910100c00c0c00c1c1103030a0b9490702120312072845aa0110342d2404035446d50034003420703459400036003d41203007812100c1140824540030354074080c006 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 294046142 1250 294044892 294044899
    0xf10060e090a12050c0a0303062c010b0304030c020306010635060103090501020906040902030105040e0d0c0305070201170108030c070b031012060f0513050c1807050a0207030b0901090b0603010b 85
    0x10203003000881c01c0c030b00b406225110b440d180d42484038601a172410041c5214041d030002e0340310079040c07104007034000c25545d4084440c2c0d03994030043c00f00061007109140510a2903001070022000a040c14003546180d4041a401001c0d1010ba40c0c4a02001c1c20880450340100c0d0004d00b256041c11040842011518074426580c80789503081ea0f60303c0044000d40007140d401c98840d5024003822120b1b403264801b0700b0203011002000f40c0c45c1c0d810310b410701c0100c0e4021101019154020303d00a5960b07900304012854061301403600c0e958a0740d103400140c1c0c007070340c809000c1610303030900c41c000154502000c000b41a51007019010344800683d1868084598041551a1030a11186840c1000b0b0f8070381550000d034402d1300c99500800c0c0050090755503001c5950840d2000c8803584d56007803250810000380004280590215610140643c284542c40c1c3c250030002e10b01d0051202c0010480c0c7d142c0d0081220170001c56006191803414070f4401c4056001e006000c0c2c04603100b07036042d00410030524040c000c4819010025 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 294047392 1250 294046142 294046153
    0x20a0302191a160b06030a05061819170d020f04030c09053601090b07030506031c170603010e0105180d080c0d02031009060308120702010504020a1401110f10060e09 72
    0x1512451504c40b005020107134544107803102c0c81c000030014891244604590002212969a01d600d80c1c1c0c01c01300600c10800e000c08840000c5000544000d0003040d02c0070b01c0c2c8100740c0c0c07a04010030f42c0310000e200760440c40c0d80380c02c0c01050020030071a040c11300c24266054104140b01944600c45100e6402c01c2442c080f0301e43e804100c5903003d5500c0020300f94000307000c0550010540044546171002824400c0d6069400240c48070100003042c182041525152421034141d1680f013441d00e1001002d2004c0c0710380c0c1d1851048544003141c2e041c1c2e402d411003101d20700c0c40da0080046042925800500300020b4007111480e01410100c603414600800b0100c0c42582da05180c83e25111000d44108025800101518800750340002c020a840d516032194002940c0305540716903442c4040e0002040d1910004c1682c0b045a040c9001c00c001070b11060085130440e105050101c04407035800c0c00507a103000540302d042d001440f03212070800b0000000108045480c1202c4410850581c40390b000710001030007121414202c0d44036 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 294048642 1250 294047392 294047437
    0x18040c0902160b09010c180602070e04020d05030a02060106080c0f03010504090c0f0308040503100b030c010c050c060d050a050108060f0c070609020913140303010f030807020a0302191a 81
    0x280c0c0060124079100302c140221108140e5441004030001e039519041a950746006860660300305542540403140d800c05102c41900d80840255104c50f580506250340d030707403030010404641701d10001d40b001e154403000f07503a2640d454000003555201c09104038000100341102166009508004a0f2299108030204d00c1c6181e0901c0d0500000e049440d2301285c0b180d120113070004103881d2032883c6d003001d1132184003120342d542e10340802c2515080300300d40c203081010b15004004043c1e5400080360301c5040e00a0824150010b540c0c105942041c400d1030f036640d001500028544200c00340c6030711051180444400c10002c50341c030703801e146030740e64012207a012810390b030880031403c90181c000160807030130310400010800ca10300342d01040820a05a43c0094203d00d24a02c0504000c0b025a01014004008009500f95071411507140c40d129540c2c88050101140014008295283c8000d2100038680190403200d04113802103c840821003140302d0703401400b0500c1002c90442d000d020890704090070941c14445c41058 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 294049892 1250 294048642 294048659
    0xa17070908033711100203010609140a090e030d110906220302040908030402011706010233010b090111010b06030c0903010e0d120c021203010915121118040c 69
    0x804070f0140342082c04044052801c00c4603070310004003040c50341d5503040750410410318540740005807003d80d689a401480103001c00d6134008044c10131a07000200b14102c0b006602c020501c40d80e556000101d41c075007032160426800784c00000800c1e00d038007681d100b00b012400418208000303000f08504e09600c00800c021481284100c01a04400d104081c9901d1400d66a02d9000030100c489950b070071141400c0100c2000155030b004840c0008824035034008015601d89480000e45581c1c604030041d07080c0012048055034004c419410000c503e80000c01c055072540c49180c00f07101508401d2100b8009416902e14560561042c02448410080a80011300b140c5074000040810381000302d800790550740e11858003900c04410002031081d900103403668070001440820b11400e451a038141e41c81550700c840800f230944040b01007204d04445021900040303644019403001107a50140d88117022190b1115000320601241e0500d01c103015030100c514107000b4400c50114140b10700c00319005021020034500c100312890 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 294051142 1250 294049892 294049927
    0x80306010c03051b06010f050904030903080f0d0e0601051f0210020d11071103060601050a020c0f030f06040818010801030f06050901020d1a131404030e03030d020a1707090803 77
    0x140700303003856414103500011000c01d0144c0240300442c280d2080e0010000c0c500620404d0018110a80303002e0014a0103840140400340d00d44001025660001034041e408090390040e2003482c0f01d0000c1c28400c042000f10310725520402070140c4c903c5072845403c501c1c000d2407881c04031200080c07141c010300400c006480c9407100039000384224072080340d111208400704460820062840d14458404031280c00318000078035140400c0103002d50f05000080100701d0b04240c0005030256994800c0321490606c0a0310f0740441d0500d0741246020900c4d1040f52305100400c407042c005004855480400c1c07101c1681c4010044035030701001c0c40041d0201e0070602d4100040b030f030301d600041d0b80a040b0900140c034041681d03454500300e130754461200d0b8041c0c040c6140180e00d840e26104d12103200307406403410720210200700c441b900c07400c0003d8001000c0c860b070b8810128164400340700ba5105140200f40443d2502c1c0d03042d1001d0002c9140002000d001409100000c2105004000050540f004400154100702d00043c4000089 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 294052392 1250 294051142 294051167
    0x10e06061902030a03060603050c040504020304060e0a14161203081b1303020109141c0309030b07091e2304020d0c02070f0b03090a0210030e010c031a060708030601 72
    0x528204190341881400507404410038000d5402103940d0490380400500b100c100ea00300304100b500341001d024084140c0000c0d2010398008030790050366612280f521000820b4507001107082e42c01032000b00c0e8240001040b108600caa040ca06803190390041045440d47d200c15402070348d210f00003090100002ca80728020180d4409a001e6030951590001200c0e0707401c0350061403510b12118202c0b00d041c000c65a10407464001003202d00b101034200200b03180085c454480d8180b510260300c081c1c5c4114402e041c0320b41e06c1ca000943e040b00560009003009103000784441224000c85031802074420381c482c0d4864801b0701980481d1082200c802003241c1c11010700d246144c1c60780d03070954419001c0c080c04402c2581c0e485440351560b125002005003615140c041494400e40d0751248c200000b090040010391040441c00807403040e412518019818000f84090b00103080b50044081250728141c2030861854042d4442402d038250f100700300e6801341a500030030039180324140004000040034004210954010404450b04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 294053642 1250 294052392 294052399
    0x1240819021c150c0311160314031e010605030f150103060302030f06040c05031209040203130f110f03121603020c120105151008040f0602040801061d0c040e010e06 72
    0xd20020b90b00c07a42600d0091050340c01c8a003000c84540d005103903108503200b0b080c460400307021400c080c1004800e280100913224070501c1d40b603881c0d901018440e10241c8226029404201e4981c1011440003403115045d80756004015007180011600502860680c0c7c0300d485035141980d616559520407034080c104021100e4149a01ca80001c4010794041c00001010f400450081405107024204404400703026440140650480c1a00c01000760040084034080d400c1a074003d45e407519141d8462051286104029100b480d48140c410700304034000c40145045070b422102c00046182c1c80d03040544504c07000311201041e800c10030611086485e0010302c8800075000e40107403106400c500c400300b4403188048000c0070781039560b48104684100c0c210b00240b04207000740d032140100341d400d900180c4181005030000d0000b440c05044141044250340441d000b40c94268020311582d82d03154003154034442c050240200341c41c0010006070088c40301e030090b50129003008240c4034090b40707401c4c500941caa4024000d140c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 294054892 1250 294053642 294053659
    0xe15030313060809101112090709020a170f070c14071a190e0112020309073204021206010f18030c03050c0d1203020c0307020307080124081902 63
    0x20303411806103a10040c16241c03a03c01d030a00d44910114248954035000d013080526000551802d8818102628050314500000700c00b6905c5144025140c030100d0340c800d0310214000180460ba03164010310213840b000e40b01105100d6911001400711030035504440c0040041d000c0c80c0d2000100f88420200307050b007200e180507103111075226103191044107415507180850303080000b003541d4001000020f00c061203405e80340003105100a600000c164a2034152180b201d42c0d0007002040d005c060034000c010042c000c607000b00100300403000d224500c013512610005280f03203150000320911704150003200d4485400d0550000e895551400568110f0a0078042a08000030310012180e4188903001c90009103000c0c9036041141e43c03552400c5031405074540e80140c040c50011140b440000c17149502903c00e0000c605000d600c540c4910082451070041d100043d501d4481c02200054942041d130240c040c1f43c0d1701000d00c442d0241d07801f46964a00301c4520078087e203a448803034807825050785d00240d489041d10042036200c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 294056142 1250 294054892 294054907
    0xe090c01081f05180907080a05060402041a10020f0706021b0d03050f0301180b030115030b060f0a1806170a06020a17040308010501030509190b0705121305160e150303 73
    0x2136100b83c888030300341c010a2803081445600e00c4100300301e00003440034000908902000e541e44c540ca42d00c001e88024020f948520000380346c4c000b031007a05000710101a000340400160007070000e668a0800244403510b000e81480407900c5480400d06510040300d020052440b08003030002e00280920300c040c141e082120030320004240b060400000c60007008510702460030203030303000a02c808441200011034800e80c54501c1344001201661144000c49420402281d842d540e200c02141c0c0078040b441541d9403001c0302c0c40c80410088003101c14007250507501401044161740718200303100f0b40c40c8540c018560f01d0f03000048540000b4103603001001003c03060718140300c805000301c17104000341400b41e40c12000b1510000052015503490f2103003076406501b08000b04240c840ea13040300c410503019030350050300d004003000014104078084c0301260010b00076041b815289103031a2805001c0d1402c0d444003140d00b8084c00c01201c00c0f40b901e60171000c0580c0c50741c020a0249465000b08003a0301301190319400c2c0c141c0014400316 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 294057392 1250 294056142 294056149
    0x1509050607061b0216060f1b020f040e064309170c09060f06070f020f1f1101021c050a061e05010e0405010e0402121005010f0e090c01081f05 62
    0x40d0000354180d0001d08902d176556081c2424025a0b4001d071040000f28000d20080e41d602060f1030522002043c8040380318100e81c00803500c0c5210401e07030540c1090510482c01c1c010a40041c07401c0c400c1a00d00c000c140082801511907607924407140e8096002c44107190240e0224020308440d1800d00102d00b000c1c144155102010891155120b5141015030085002015642420004268401d41c200c0712a010750107070f40b0003e0107034081c994002d018035480040050840d02d0b040c812a040e09402401c00b511920201200d8410141c1c9407030071000528021b010341000d950500aa031200903000c0380c1c01070480f200050360380050200601b01ea000310745550000640d140d406c220b00b00540e500030380004203103040000140000702c24000a60040f0b140c0001000469681c07400300750410f0381120000c02049041400c0f9281c9020380840079034091400000140282c00b0400010440f0b181086070582991402601c58a911044800ca4041008000040c40380b01414a450480490802070070b5401c40e247c1012 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 294058642 1250 294057392 294057431
    0x14010e060c0a1706030d0f03020f07080307120b010e0d0816080331030f09030c090207110f0a1415030108010209040b0a0f0303052b05060901150905060706 68
    0x40034903003070000890815241d48070500742602d8400c920300d01c01d942000b80c003196449a841c0448030422243c41e050380c202510035011030f240d10358440906a20b0310814104252a540300350380b1400414119842e0751000c070030900480360280016128002c24841100034080c62004403d0121b80c42c9404214071024042d1090103032603842d0051b41e20903240d2400b051203013026428150f80b6a440c404000b80b800881e00d13074008103030324180c1c949000045a40017a009903400506600000c04c440750b49003000c91b4914444d070150ac401401000c0307102c0700520840030700c4030750314001000580004904800b40140851a1600d00380060060081b84045541c200e40c10115042a00152000d9400154554945c90140910b10043d10700300c40400449280c489a0581d00071940710040601a010907030704100c0501103141c005550b10901443c0c501142c403c5020001d000c00c4420b68881e400f00c030004207803203e4002c000120720f65607417641c1c40e4150030001044003a80000c41c04964442d19860384c0944901c00c2c400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 294059892 1250 294058642 294058651
    0xa0b150d0501051009030b1807030c0612050f040f02090603030d021b07051215090a06020408011e02030c070b0c1603020601031406061e0102070f170c041814010e06 72
    0x4001070254140b03010400d6840300b070804501080840c900600200f511040865008100300c000b00c0b0380581c80c480c0321401c0640550010b03022000c00e80300000c5640d080a68114044034041c005c010581d0741c1400e51003100d0080e44d01500d503022440c01580181003a08009411180050440381891f036142d40c000180c3c0e000e8410f07013064408401c0c1c1151000f07000c00c41440903000444480801c000b031890340b03d40d10404010144241d036800c00108461440034840700c1da495412140a550721510f8040840c080c1c04c03150003540c896209841c14103401070300c1d031007600c6c003410080623864640a0203854040305008090000444070000300002c02020340516240b0550501c01d07009030445615508044050180c0044a06111f800500070042c0a41c8c3d08013642403204041c2c9100622082d5000040303103400b074a0741155038103400201c008a84211000d0a116000303050100721205010041c0510087d9a000540d07441810303240802100000c003880c41d810146046480001024061503e4040c0361079802c0e82c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 294061142 1250 294059892 294059917
    0x405040e120d0b03070510080601140d060b1c150504020702010311030103030e1009030b06060c15090313090209030a111203030f1909030906030c02010212180d02150a0b15 75
    0x107081d004513050074400c04000f03020071035582144000c00d240107012000300404442c100100715580103802803109040e115000500074040010940700c0c1d00100d2280d01181e041c60046d04000c1094034440903602a0640b40e0242c200300304038052800090001941020900720706140c1c440022501100402d00036600131070080da20100e100c44c45000780040c00b074100582104122190006001103107050303c0040e00000250f400555418940d08802d00701350790440d2811000075941d00348200a280000500764411a10500e178180341d55600859080b4410f42c40c004da01034120003044004075155080048200c5070207800030200c407141c030104074199801100c0442d480d806002c140510f4101c0c003910074078000b01d142400c00800080ea200a40902c1c070902c104010540c0b520030740d12405100b2340664022821360318003001c1606102e600c2d1844140c520103034602c10b03c1a405054165440090455001440700803903440584034111000c1c042c005480c110307030b00321309140c1c1e80c0320607002424020f0003514442d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 294062392 1250 294061142 294061151
    0xd1404020f0a0f0308030a0216051b06071110140307050301031703010302061603021908030f16050703030902030705090f0f0705252105041e03080405040e120d 70
    0x1881002100c00c1100209400b962064400b408120228445074040e250408582c1c0d45950f03c20718071001900c10801a0000264660048004c0100005040b480070007030083c1802000100c009218880c000c100010300401410340c03070010f172410401060104e07034000e03141c030780d40e4140e1885000c00b03140e0050f0b95510020724000b0040081c00154060304c0701040c46525924a59459a00043c00c14014000da608018081c0c20710042010300070004d4100242c0300c211030043c505902d0802481607001201c06034144100c640c0010500e8420401c111090189038942500b0110301d03440071801420303030301d4049800d8441c4900c0400d040da40d2140c15445101b24038428012458401c001011642c006803511003405000e1009002a55400300e5005004104c1c0c40c0d02120710503981040c0d000700b40c1c040b4070342d01f04a5280300c206601c03c0e40b001c014000d0360f541c1e040c0c8100da114400036200c88c05c0c04500c0041c048110610090015140c40d0300403210504001003211420f0f20f030074240d4405517028554014206588 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 294063642 1250 294062392 294062401
    0xb0406020d051204020f31050a0606020a0314040f1203021504080d0906020405100f0815030d122009030106090b060301031e05060403020c0a0b0c0a03030c050d14 71
    0x1000310449071421481c0040c10001c1032241021810703c05080203208482440b130000d0030341c0700c0c03a681400030003000814020b0804250a40c1180003003001002c900103040c00c1c00114191a1360292408a607000d60047c00c1d07803001510300b1a8030229186100000d10741c01c02c0002411071008885a014159003920300307000d81048d1501918041d00c800a10180101348801c01c40032407078031f9003680e81c580f8925070082080211840d00308000e00c281e8020344e911501c3c03000340320f000c1030f482905001c4504558641224a03101c00e21815141210840459410f83c002d40c03050251074403412501d9091034940001142c10a5044031040500002c0d070001d401c03091011417001180d2500b4024a0010130001504100210540012450b144814000903100e1003d08442d20354490341000d542800d6900202520010708007171400035212807000e0182d9205005800c0d011690640580c1101d2400c02c0820042c034490035103981c207a01130441d05480034140101401841459580c80c000ca104550700307a49640320700c0c41d2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 294064748 1106 294063642 294063647
    0x30c040806100501080108420403110d0f09091a030a06050f0f160c064718060f1507050106093c060b0406 47
    0x801c0100003900765101d1030441954400da80346852666100c2c13241c0e03610391405014406040916000700c1e4407061000c0d151070000e0006101c048040e2448074030001c0c40d04222015000700d01011509081d8640034403102d84441100d003030030011200c00c031400911002e05ca00641521030343e10640d00c0303410810b00c5124070300d803a002000c981d90400381f8a8228042d20068820a0385100d0348004542819905083d040c49400312424494890410b1a41140e441140d040d0075145981e07605039440d1884a01c2016800101d2841e2503889290091003403003031840101e42200f03004105d2000051030a07a02c2c803c5017007820740d100c5003443c1c0689441b0b000840f40001915070561040000b0030345807007101a00041c0c0b0085000345c0003084010364031440742c015100380c10a118125a03403105c1691040c403409110354903512a004480c200308524088102c03c41e042c1b40c001d07010143c2c01103420441c16a = true := by decide +kernel

theorem cover : BRFrame.Cov 293884892 294064748 := by
  have h0 := BRFrame.cov_init 293884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 293884892 ≤ n) (h2 : n < 294064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
