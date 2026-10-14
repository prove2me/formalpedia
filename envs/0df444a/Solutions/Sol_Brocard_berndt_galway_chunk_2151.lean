-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2151
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:48:19.751626+00:00
-- url     : https://prove2.me/submissions/00d4b03f-a475-417f-8926-2b1f938d46c3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 386690647 ≤ n < 386870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 386691897 1250 386690647 386690659
    0xa110a0327050d050d11030c04080d03110909040305070210050301080f030301030b070825080615090a05060d140f060312030910090606050d050d1803150b0d20 70
    0x70340a06a0801200e20182c22800511030a1000403080d6580d83c05480d14620b1551502500031407440ca4200550040071940b03072003581e032450504202d081c640350341030046c00c050070445034201d41002070f030a03a018680100d88ae070855880f80c5c80c0645803442144030094104d4040c2d00c4007001e09030000f02443c103d8000360103440c1c08049504200340c61344002d0000800d58410440071030756141c0b00f402896070140244004a062800c88000814009090329020300015480020007841e0b086c0100d41c85495810700c4001400d0140b00400600c00c1e410700c1c0240d9024242c040740184001505801180c10402d001042d0300c80780c00c040aa1000e9041d080300e46902a00c00d03181d4001802c5d00800882c2d225584200140002e10701d1a0510740142c80d80040c280da281d516040085156039440b5480400346118000500001841190284c120b0300c03128403034515084202c408201040403900e0041210440d1207000913810201c400191135100d42c5e010144c102e0042c41c5100ea0002564264200c1046c021251 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 386693147 1250 386691897 386691941
    0x703120902130e0d020d051b1f020a030b0a1d06061b010207020406080a08160201090f080102120109060f031e06050414010513120809010f0c051c0212040201080a110a03 74
    0x400c4c0e03a180c12001ca02400940200040840b4180d9100e02304074034401d910070b031141200c5401041c03501c004d80e08044034180354002094030510790107100b80c038031004003550440c0312507282400440c035200300e5404601280340941c0010740180e480d10304840d201140c44154401401044e10082c1c001d4100e1042203002d949032000214010000013070341e1095a0740410b443e483e0441c3d102d80759480150a0100300e05101050102040c0da0301201440310292010400068461201c488201c070105010303844410100d107008030074402c0c000e1135800d2f4402c1e2500a18100c91003818207405059411040d00080c0500b40385c94281700030000d401116a60070140785c1d0003403150761100d290f2008200500308005001005c016507514850380207a02a6a0004410000088101103403c030352041d030f03200c0d100304c10008500003030b050408034143c50702c03070f0020302c1124046003411010144038854600c0580080c1c1071001c0100080d1081509801c548044002001c0d00703a01c610300841e000c0c02a10070142e00c0c004404c500c2c40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 386694397 1250 386693147 386693173
    0xe100203091f06241b0b040b060a03020102060a0b030f0d0203041a12040308090102071505061504030803070e0d050106121505090a112d03210703120902130e 69
    0xf1070f810303185641d81c0001d114220039580180d080d2050742c40400d21040300320502c0b02e4010070f40c403200454040c4c20034060a180500d070069a4540040c40d40384201100c10051015036030010703500f54420008a4002801c10740c400020345020181c00c50f00b03095104d2022000e002d6540072000c2d00c00c07200c940200d5501c009508019440500503240345600c0e03050340b18000b50200788100d0300a070b08107400c0c0c00014030f405550749800c03443c0c4205410020b2082e031a00148801401c02c15288100c0007070750020942030a09583d21100b1a103c013070a00c00c100101001c424000e40d5070101640c801c2603100380204015596a0280f00e05110207070b800b40c031041e2904603808038888950003074900c10440000508083d01841c3c2d01c4442c5001d140c400d4a0300052017810500a003040c1c0700b5260440b80146142c112210b410341c0416160956004001c1044062221614101444801600d06850741340c1805000b0f41a0028420018509000041d501c54800c1c00e610b02030034403e5018101150804044c1c9e9100000d8503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 386695647 1250 386694397 386694401
    0x6060906021209062b0504030813030503040f08130e01050f06040b09130b0628020d0c030f0c12051902031303081b0319020106050a0f06030e100203091f 67
    0xc2c0c007036a0b00716402c000500c1d4900d055001850101d0681070f01c00148104031541c4500c800840b5450380b5101d50b660184028141c200500c03a500084018001c1443e91030380c0d40041244c04090b10003840c5d805100044010031006005480714060321100c0441030f199175443c580d480e80310a10a807800b4801e4484880c041e414090200c500f0382303441c1103401d4504003c100501c884e5000c04400742c000385542d4098442c180d9664002801d0215404100c220490200140c0940091004400100755801f051243e0340b0103402c0140c40d0030140c1c060420400407049880c043c0c2d04001000b40c001e1801d00e85020010b9096007101c050002103000b408203c60581c010362085c0e80d00d20803000e4010512401c0306007000016141c0008102d607800c019906c5a0b91840c038000329141d500308250b90132040d0b8618025038061642481400d0040004a03080341916141242030510302203280195410585c9500c01140c008808001c1c0e0544003e04160071543c034502800c000b905c51180714012960241030300f0701c0c10142d00041c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 386696897 1250 386695647 386695663
    0x24010c030f0f03090510020d0b0f0a120302010f0507271809050a0b040c061115010302150c0a08030117060108031b192102210309150a0606090602 64
    0x5070701c0708020404070710000d46540e80801e03404410181c540346410000350080c04054060448440e015031600881c0740c0c0c1c0f10540e000300e181c1c3c41c05030520034451081c80d03a0300040d803030845415030310300303017a84056080c100e002d00b003095000c100650411040c40340310b60307102031208000740d0102c42d42d001800c03229400410085807881030340150b691808240100d171820394040c940302c03407141c6d04640b0800e00a5640050005e81101e040e102048605800c1006907000b43c1d458641000900c040c1020344007403403a4150500f0180030103401403030940081c01c0301c002080c0031509050400b0040390010041413410b107140d507009029880e507400120900040c58580051154181e505050280d030802801a2880c1c800c01c1d070184501c3c0c3c0b280b144002c902c040400315144004940d0043d40301051120401c54008016100550004110351003290850021440c0f900906440e00c01d8030759180e0340c0d44501c000c10b4500805c90a0720002d4516603000c0c004049499800041151241e80f200701d541903985800340c3c2c80f0089 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 386698147 1250 386696897 386696903
    0x11090a151704051b04052a090a031202010e0f0604030f030e0102180f04090f080703090b0d0606090b030f060d020609180901060503060f040305031909060905120306060d020c011424010c 81
    0x2184100d1f40707803d20704268104206680d10040c10036182000058a002040c0e0003601c0f50328007130034600010366080c000d03000203ca260004041c8007200b04c44103542c5000c0140060f0810a4240241745a58465001401c1701040039000350b45900c1c20a50f110104025003540500c02c0c90459088081c50030b09000d19800305401c55141d84040c165034841800e0b503030103204101c0c00c0008241000c61452040001b81483c1e045406001680c01d09007a400381a6541c59044440300b02e80038400c0016130700d4400036030703680090700b41c41b5040c091400c0e1003c205039018143e03178503920401040f000200c1801c0904114032444803a4020b100c00340e43c81080c592114400d4070a5082c0e12220400200407900640080da00400f0b002042aa2000340c02c440c1c1d400c46a0521045803c1d94681860600340001008698404019040901e28505200000503007d1007580405ca4030144c020408a144070f40c00c0d03100f0901c00010b81250091482c1c41900c1d903145400b200120001e903080c000003070303200b9403040710160645030f8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 386699397 1250 386698147 386698171
    0xc0d03080a1523030316140d030204141c060c0c030e0f0609010f02070305070e0f0709080319020106091401080f0f060f06030a020d05010c0311090a151704051b0405 72
    0x240c001c035070003401c80015100381c141c40201309031102517001d0080b00712a00c0c042d1147e202d12290f4200302904111a080a171000c0500600041c0020f01e9240c003a03640125003110611008140a001e040c10111034180161016203014549011540c20440d0302c0c01240c0300c0da071402d00311200d400801c0203000d180040c0341d4120030301380101f10b0194000d02c1441c40760300c031900454148a680741e803520b1030044250040700c81000070303000380b203c900c40901d0300a801a0050924102660505501c5039590141080c401c0e418242c1800d100c001e54000e6210001600948009110a21000c540c1d02007120702803154004078031420281001c0742e24007040905080d04000b000e00601d4441140c0303454580005480c1c00e42c140103208400c001aa2501c107030b03000841c810000403038829100a40601200c0d143da5002d03045a204025401d0039aa4440c40c820035100301ca64104c11155114808031400881c442d850807009036204244000d015002034240c02c1403603280c117107482291071701052006803070064410641c960b03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 386700647 1250 386699397 386699429
    0x20f011a190e1f08060a1409030a0e06030604111306020d050301080d03110f0d090b0106020d090e041406180c150316140d05040b0708010810020a020c0d03080a15 71
    0x30422540f200c1100441401c0a004035182c1c15030070300b0504181d5a40f040180d440000140680c4a2801503600c41a4200518108449810050300640142c0c41051141c0e000000151782c0d80d803250301c50401c0b2402c100c1701c5921180c03d04080c1e030f4028a1401070002500c260142141c1c91489181101d0580d00240007505d803215072040c0540c00f600c903d401000440e4402e00140c103864034844098642e80c000c10300b001c1814007007030400824215045c0c000008641261007007000c815048540402250071000a06100b5074807810304a04055106284030700600404050041409258020741c210b201042d06030fa41203140d2078100002c03085c400d5005207103010107000044101c2c44644a40d40c0200e030904207072141950140380c021403607000c110682c060540d03a1041c442400b050103006640500113060036a215410103c01070754460399401016042500000c1c0c2481e0030b44203120302c03001600007070214400c0b0301c01c0d49030140100a003151724280140c50010048064000c05822100f19850030081d10021 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 386701897 1250 386700647 386700661
    0x3060a060303120507050d14040c09060b0a050c070503070b131d3d030c080303070516030908060106031d01052719080406020d051216020f011a190e 65
    0xd02001403844062210501103511003244c5400b0303072019040002041da000c0d09c0c0901c0c00751011200c41d042024410305e010710900100481303a08541c0b284150342041501c44080082c80c03850700b070030350f0032003509800b5041000030303612000b402030006006c0d44002421001d4031000300d200d6400d0551450740100045074045030001062001d04008407498540b801c041e04414203075900710114041071a42c0c0c030b036503408041043c4030700f4540e00d4014040800145145040c2072200811501550b12044141d001c1d1402c03031030805024400010040c1054000d0701c08646e541c0c880a0000c01100301440710450703048541c030034401c40620031035108209020b00355040d04004c54000c0c3c249503071451300030444d210380e0030b070205855940700d01e0156061054480a0740c8909125000b401d200c10806da03101030040c148080c480402c00d00c0d003620303405407100030421042020744008a01d4a0b0018045031601d503e0141c080095a42d2010650103444e01502e01c11003003500742d1581c1035616014450b80348540300d590302045607 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 386703147 1250 386701897 386701901
    0xf180d05030717090d260703110403150f0c0c020a06051e0403050c03070e0c07080306010926070b0c100c0521091203060603040b060102100608060603060a06030312 72
    0x300b0450314202124007022005030300c08040030340c0e03c80ca20b0340c001602560f00980c400310502e5026502072481c988080320700206100550f000c1c2418050548070f050b9101201941819600150b0f04820b16071240500c0000000c010200c50500e40983d0b030421502241c250700801500300b40c0c5502034a071b480780b02d01e0514103c40640241d013544000004001c41c01ca00b0100c400080c002441c0180301400641d2054400c00d450322400d640510ba524410300200104150700109032a60360360043d80d04e0b40d0360340e250001282c01041c20b070401580c013210014141040400a05d01c5414041c1c29012181c1042c0c13200d203000d00d14001c0d002080180da110703180140f0141a9034010141c08110380c00c003241070040040c003860300e103142600340075100300d08003082040d03035441008250b0354250740000603132079800d0110101d452440000d2026011448032004650203904c2085560180c138109481008881d4403050560b0700c3d1030341611030070703c00d218442c045240ca00d090703c210310840340c0c03540f07c8c0d40545005d001ca0f040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 386704397 1250 386703147 386703151
    0x3110f1201090809031b030703060b01031e050406050603011b0302220608070216050609040c020705061614190201080c1c0c021926070807050102030f180d0503 70
    0x50080e204a9082103110030901400444a101d640781d162036071030000601d0310309260700415180c050780011501c43e20351008144641565000b2070040307171203aa03050040e0702403d030031b429070b1f80074103a00041403403411003d81c07056004900c10001800541c45460406003640c11201a07071201070050f00c1c2580c1000d01982c02031603260068168040d1111414005040000c0544d0101c03000c03800c62010004481e905100e80348e20500f4800c5a400100e0500011441c14015180460300503030341d0300b506912603402000100d00910000b02850742d611080031180d8a060740401d011105480250140b1409440104058200645029440141c86055001181c4d1220701030180c0140004c104040030500320002041029054003400200b03000d04480300c000d20745442412200c405018411211000810402070090030040b0003030354503070b000250700b02111240314104008100000000340c080070880d041d00614070680d414581e04285507203410050a039000c001c1010300041e0004403075050342c5c0380900b0280d5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 386705647 1250 386704397 386704399
    0x2010e0a0332040305010c1205070203370e040c080402090604090c1d011d091e070503030c100b0d080a030c0509121509030a05090907020120041406030103110f 70
    0x4410030b400b00511020f500c0354109039602d0751500c0c15508186d03007204d01900c0d0f042081d8004c00282c074104e03000940741c0c01b4501401d41c044a002d0400740141d10400004000303011448001c82c120080c0c004060190700403510100c1c003450425036009030070707801016402d11941d006003d8030001e83d00c1c4c6040200401d1b07101000c40740400030700c0004c15148002912090040c0688450800b00d5060000702100507140d007040d0148fe1000c44104104404003240390154444003001c240c1d089a8003020850420038960441601444041120081400005108480300d86c22010400986070300c00c050082840c586000a4910002048000c03d628800d501209003030403546080d5080c0280e110004107015207c10114400303620030548845200c5a03030314800e03005000d504c0114070704075a0000150a03801070844441c8118412000251018003c0d082007030a1400b9640561200ea082c544880306500117000303101219040b40c0c5610064140320003140e041e03d410601071440c0514a5017001761400f03c28103c5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 386706897 1250 386705647 386705717
    0x110a1d0105040812070c210204090c122003060105010c03210509030d0c032903070308070503030702190f1509082106040603020a05190e100602010e0a03 67
    0x6043d91061200d02c2c1014445034103580e84448030304007810040c1c0180c01411081800304003515031001d6850070903622641c151004201c00c0000d08280070b900c020b0307610010624001d404a001000386a02c0880112259a80b03c3c1160121000074555107000900402d40031400701500e4101207402a1840d0340e501e4142d151515070b03100c000c01614107450007a10326400303503400461803402507401c60180c400174450515040040c0400304c0315214401484000f0751506c05890302c0803644075103081c801031019640005400c0d1b69150546801681c9901c00c43d0100014040c003043d001c11002a10404580c3d26008440510790500a0715807082031400709161640c80b6640b249028002410714004d0655080068000720ad80b07100c00300c800d500041c00a01d1244150f2500406100507929900d420003616410384260060f00d5808070040700304040c45d0024440f03040c80404001001a84007419020344400c1d500a002654440d100141e841d40350043c000c010420205005104c01074202d0099820f0b00b660310340c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 386708147 1250 386706897 386706899
    0x17030a08041721130213090f05030307020c0907110303040624061214091209180a0603030f08070e0f01050d090606050418111e03060712110a1d010504 66
    0x10315040c2d5100c2400da100b4100007200a0300c0351400f590620f6401024100703e103071000041d5001070f07941c001403d06200440c1c0d880c44a4002c0c0494503500342a582e030302004a036541c2c2403404019681e1780d410700207984240d402200240c003962290a21041d620b460400030341c00e5480e2a03035030034060030802405a90400040c88070100302c8420700d5041c0014207054450300e4850216034400000e481020301090845e050503001d011500c07a002031501502903d00b8412611400c0040000b902811104440c4400f6005d490a200c51442c0a40c4010201c07031007915104101e940582042e2501c8008444102c04101a5002d20500707003000b4452403100030051410900e030242203040c0400b100c2011000380c0c1c0319540c07000c084c402d80c1824880d03d0130b68901a007151041f0f28680d940c1d00a581111030206000d80849134120b908440350418800c100350000341a91128603210000600054294255894032070a02034050a80c84038582200c0b86080c40740ea80366240314601008902807032004403003c0c100202040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 386709397 1250 386708147 386708183
    0x171204060c0f21030c02060108031e03130b16020106120305030402100e120c040605030102040305030d11091002030d05060105190810030b1303110607050301170703150903080117030a0804 82
    0x4490025144107840014131030b01450317402458503c0c141c0040f05268001c00108241d00c107102610004810b640e5020b5076030b582e03904101c000d00e00b095a4002c2050701c2d80030a1101d000240300044d100c104485c0d0003000580e40d1074048001100c0e40010140c040b880800205016080c41a4041c818042a09148401c0e461003804181e00f003103281404030903600091041d50301441d041c024038000304404c40080d030601d411034983c1620317489400c0e03000f201c1594965240e403607451804250383c000ca4000303040c0951510003c030081d440360300100032840742501e486d000034030719805401078896070721403001c80544400300d1007420380300000068071451040281000c00000103c075140481c0c841c090003050511142007a2601406814014080751b019030060420030800941c0302050324110b031058001154007003100c114142c204050754002800c1c2d0303040d036170720013560f09503542000c0043c9210390b8400c0c185a98801411400c50041b40c1c030008507130000c110010703241c0e1043d44801c1c0c00901551010400c0080301c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 386710647 1250 386709397 386709443
    0x8150411030709030c330c02100804030206061519052502120609031e190228020a090507020f0105070e10020114180a02030601171204060c0f 62
    0x31169800070f8501e0380107008000c03401c0c40f071000820b600003090080324000040c1044060003039111601ca940b05860110701d080c03142150400c81c40c3c01600e40c051980585a008010709000c0394154007504c58030340812038904213205550321b84804a28010b040c007542003804960400c0840520302002014001044000c404030f40600460300050000351912503c6d1041c0242c45618242180c0c013500400e0803c90015000f00031124210f50381d2200d41c1c1410307881c1490b080c4602038110001d000080e941046202540c002901000d03020380316180070b010028042d50b088000700503d100030f40000c2c003803500f0010030315190421500104140103544401d0303107650020b42111001c07620031001445580828400c1e00b40101c1041402e41e4a1000388500c1c1c0c9001c010301c151840140c200c2051040055461b4200b4006210340d0007481e074014251540c9580d01c10410342c59a501c250b07095024096800f5030201b000348682118200d030000d4562014080342c54642100c00301003160160b491800103200003440500e09 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 386711897 1250 386710647 386710651
    0x1206050a090e07060215010621020a02060f090106231f0e010f0305130f05120409090606050d1709040603240b0405220c0b0a1e0509010815041103 64
    0x110303800080982d11074550702d10b002d00130741c042c90541d04036002c01c0d90103070a000c4c0354034159184c5040c4a200c10150004001c20b0101180e10b429043d0f1000c07902036100703507001c10740070700030007502c405d4281903141c07202001e00300c65007442019540454040c1000c6494103e803070240d64800000c1c109620500024000b070389a000082803800000d4418000c05a10b41c0c0084e120f04c4804040d141c10003d80c42c1140704980715868200d0701400d06010304c0702d0641002010030080140c44210b8420ba515560b0300c407500d802810600400b1200c0508024010440e4200003c024512540140c500d4000180383c062070310700343e84641c01c00c41d0495145d04012000c9651026042c41195150000703c108184500e1110100c6000300c2d4224810360504040c00040d0888841400494071206840c560b6001140390406025441d81c1c0700034511603011130718554944d0040d90407604810741201c40d01841e0820b1400f140c40780f0803408402d000c5410b0a004c9010342428414589807170030003400014080034904501d40329a00b00f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 386713147 1250 386711897 386711909
    0xc030a03032013090c0320030a0e0102130f09150512010b03010c121a060414040e0607021c03020415050d0b0301090c080d050403150504030212040b0a08010b13061206050a 75
    0x1040c2c010011801306100304001c240c3c80d49400c0081d0324104070024981c62620014200491000c80441c007003036601e40c820084001c102c0021540c80c20004101c08414000e40300e0b02080000c4084001040790b820b0141080100d200060511b046040c00700708060404c101c00c401c0c0c102d6594022400b25238070244601c1d080311026031140580c40301d40c6483c16095880708544c1c1b004043c08415144d401e6200d1505a03000c0e20701003e906941ca41c41007021800501005c0c00c4070b0700504c128030a00c40242c1c0c02050b50108000300042c005042c07200b40505400768401c1e0f10640301e481c820109007401e602d00c250040e006500c128070000c100300071108002406e548100300305884103035041804110140042084c02190b6a036410f080b810180b550b1200c04428800004c80b0390260b031940001420140300b404041003c8420030012a202c0e174480300101c1c0950040707410f07200804c000070700100d41c51040d1001d43d203000100c54881d40c005410403400f1100c01040c0d840d00c43c0c0c03860300d568002c034007652082100c001030a2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 386714397 1250 386713147 386713177
    0x1106090c0a060e01090504020a0513120308061e0d020d1203050603010609090b0c0310050a030b0f07110307170904020d0b040f0c140a0504240e030c030a030320 70
    0x900030080181c4960503902a0081c03007140798501446076007000c114030032200121401030700e820040105640920501c11401c0d40b5403800640450044100d10988500b580260386140c0d0f141d40344024010400800b1104070018041400701c0c103c0351815500030701040348058000c41850005990707072050a610000f614010a80310420007170b03541000d104400003030094000602030f0030034a031101010542c016158105030714000000500d2210181e02c4a0003c100c09410000d05503660b0810101e414015074092401004443c00b180e031892290a1000035440c044004d035260581c0765442d00103c1080e130b0b0400400c40c000b44006160360b074441c0701405181b096140081603050840c010441200c0ea00c100481030186003004130002c05134804c800e14114080400800d81d40c1610701c00a84943c0034641c880110726890380d0801542d00700c0750740701002d000ca880d102d0b17001c515002410180c40700d00303c018250301580201c00305000b003446a04455682d0b082d41e605411404c0e200350320001d0035801840400200c403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 386715647 1250 386714397 386714413
    0x201020a02040204151e0f0507050a0b01060c03032319090b07050d0e071202130b030304260c0907050706110403060e0609030708070609240b030705120715110609 71
    0x29040200606014410340c0f0003110b0098119028140d01e0310502c7c2c0208120011907403100b00030b0100101800150802030b14840c560f5290b000818041070084110000b904042d0303540030074803812500d200c02c400303000c01414443d030300c41808203c8140c8244c020b051040d2a41e0b02e440201e40c00040e44c6000c0c2c00e0641d0742135560307040e0881c031505482d81c605c0c024031258040c6904000b101200780c40720480301d60480f042441880321036500c60141c0540c510070750f4140400140003500c0000c100301da10118580403240520401307091003c80e1141701c0300740d80580118035400040d4540c2d03c030b02d008040e05d520500340050f04004046242080d6082600200c45559481c0c5040f207441401300300036031344006514015454076485640d000498026000014489070302c400002c01000380ba0203c1121b400005202d40c0710504e48070600e0005003e80310500c5029004480000c42d81c0d0802040303c1c0503816596005046940c40d0100d81081c03d64840400d00c1003102002488403428000cbc1310790303402943e54800400d002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 386716897 1250 386715647 386715689
    0x40b04090b190b04080d0c0c0b030402030307060507030207020a05010507020a0603020c011503052b210e10140a060501051608070206030a060f050d0218090309060a0c0c0e01120605040201020a02040204 88
    0x2001c6ca4892100c2484504007401d00000d09242d804016601c1c00d40c0c2c2c480d00d0b6107d83c40480d00e1401b4a1070300070041410001040380c002da25902a01103d402112441d06442e84c480043d5071900c10a00c2c042c1d000168000c0c00d001c55406a001001104008000041c008140c80404d45113810950802c513800d07008400c40799080421200014002c140350744544d6105040000080d207620711200100711407440200841c1a0200c0f075500c007640f031844500c02c0d180413900d24050f2070000c101507403680d00041e01c206c011030000f0040e40b2070303102500d406841d010720b050032107a0b8440741080386802c221480d4600300103900068540760061070145424030310215589040080602400000da04410f000b20b80e0f1254410241e03481285010300000400304182035510782404050440c403605ea00b65801040005400a2450f40940c0c60300c0c00d10300030001c1c520390a441c1da41d06852102d0030300c20482100705503155100810001c1d0300264000348140102c075107201281d408030b130aa801c2640009007000c00600040d40d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 386718147 1250 386716897 386716903
    0x322150c0206011508070e03071208030f161209030306050d080c060f06031009081623010902090a0e0a0c1206110c0c10091a03070e1002060106140d1401051203040b04090b190b0408 79
    0x10ed44040480103d2140c0c10002e00a003030038001802181e84a001d8103080c0350207984404050800500400c07450000380c1000c510960046034010000d05c2800005052159141000d40c026400207010704604031081d94820003078035102005a602030010000902d039207010041220003507200301d581c850032038041c500c03151170820b00400200c21641010700c1f100040e0f850b6034001e0b40c40340c4c01c040f0006a8250000b48180307042c0f54040018541002030401107071800750482d001d194035200c1c1d501807101c0900000789034481d01800505164030784c040040b2450a01d0000c0d0301d00d424003540e141840000350b4490144a8180c4100c011541202c0000f0602c051075a014460500200040e16001c441d215010402941c0300b0b0144203134001c001c255420115074000600444e40f036540f45002c01c1c049003400f0b0403021040442071103118800d03004420442011003010007998111103d10300d60301d05044c43c1411400142031040c0d90305510000c0182c2040300841654a128068000c0444250300c0d5802e152180703213 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 386719397 1250 386718147 386718151
    0x12030906020102161e0605190f06030c09020a11030424030902010c060f0e1204060305090604050a1e05160f0501030e030322150c0206011508070e03071208030f 70
    0x2164010003040d00e100daa07440300c25440952180c105c05240400c0412488401d85045009001c40e043c0b009228218030381c100d40413000219498100100b65030001d1034070485a992000030140c101e01c1904001c001e000ba8090802041c04c0c2c00c10400c15121440803a046511607040300d48043c455608244165004858484000a1074103080100c00c0003600040c22002083c40c000300169205c0f80c0c1c00e5246402e40c8c0100e5a401160350484140222099417200d5907081801543d00092622002038100c410000b032907400707542c2000c040d00c0006259110300060044450103243c0701c07100703070701080c00042d0200000040c00d540716400b115194209003a1003901c2180d1f601c030341c0c101801c144080c01071603030110840e50801829408941c81105c3c0382e001c00c0002c0003144001e008074400520004500d249a00024107040c1180d013036669581c2c079800380f60306401c466080c0034005000381d00000c0c000c4c1d0080c030301880365200080840e141c0c03581e5441002c02c120400e9004480e00e10b00030007401a00d0418002c865 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 386720647 1250 386719397 386719409
    0xd08091c0605010b0a120f06080d03050412030507050f0d09080706090b180c010c050a060204030c0609150c1b080d02010b010914060909040807060612110306040203250b04120309 78
    0x1c0e141c50080e601c010b0030514580c000301001c0b566001d05034200051980aa230040410006861003880440405801000e00300d0b010b55414030543c400f0503e0520902c02d2520a16131521124104250f82c0306007259a048090b1150500366959116808904100060a01c00303120b0180820740d02c4403445e110126443c0542440087d01d00340080514258001c10b082c52205020319010402161a0600a280c5541920b01803c030900c0002c011007801202030808003940d0090711102d84195441060081d120070030b030400000a4040d144520014400050b461600009844172604103501c1d2040079061401d00c1c552800581c0d95003644203131319600b00c0d80c240c0041c4001c954041e120601003010410f50b11402d51500d1042403460000380811020300c060781d14094210740b041019944800b400d44989594071310603182903e5401d0350000c1c52400150340c42c4510741c06800342600c500d140380c0850a094a42d0410300130107101072008912030007050060001002404050052010541005844110203030811 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 386721897 1250 386720647 386720669
    0x809030312060319030f180b070309050a080309010504030b0415050c09011d03071a212e03030305131401090b01121e08070501090606051507050c0d08091c060501 71
    0x20300486d07040f0703c0d060b00c2006641000c120341029203074810039040e883d40110545d000085840000d0591007005842501d10542d082c0e1420ba0711101c081e40c0c1d030b01a40c103081d0f0000d107040009200117503521a44030703080b0b03120b0384003840c940131102980300540c1ea040f035014400c01004108041250380c0300088100c8101a041281d1050107103c0109488110301d0080520036100309164070a000d1219085940c0d0514840c6524500e140303888808141010a80e880100b003041c0e0032038010100b0002945015090200140300100e918659054000d45030080190320b106214444203808a000300e015100c51030083c07000054a2000c600e0701e03500b260410b1704075290a001742203081000542030445410780700940041c031010442ca07072410142c01d1281d001d00410650a1010060070040716400c50700a50b42d040391100a4694404040071086c01100300252059100e2051580c107030070403146148860b400744003500c0c074203480d10700072400740600c500080a1a807004404031007408264413403617015000d0f40c588 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 386723147 1250 386721897 386721943
    0x16020414091903050909070e03070807180204060c03081902071506080a0507120203030426010606022e09020306090303010918020d081c1a030f06012108090303120603 73
    0x8099002d02d000d4940614546d001191825005c0c095000c0c002c0302c010100c0d4502d6440b4003241d5250101c0e44284918624400703482c40b40100c0f42d000703a034180c0310036a9a0a070040119101103d03a110302416550315100c440406010900d01c40c0010916a80554403000100f641800c0c844220761055000d11420b03007092040f04000b41000c03900808035021032800007081c000ca4000a23041d4803495104040d00040405e43d0640c0102c10b464200108517580020000669111020303a10341d0b8000e01e68144c500d206900030200045400007180c01e521080c280010f4444650740481d01d8588141d901c6504c51340040010091120240a092241c20002e03a03007072201d48090703021a043c0200c61800624018011800c0942001d030051002804600814144000825401c540d0510130800c640f190082c060300000ca082903000181c03140c12640404101d210b642848078004254000100048412600030013058426540400141c140d00001d036003012418101203042614040305540201e00010000e55 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 386724397 1250 386723147 386723153
    0x50c060a020f03040212031210031103070b04090e0a050304030c0e150a051005190e151215010908030a02010c080123060a09120b07090b1e160204140919 67
    0x401d494002d076043e00c1e09035031b1101585a4600714002c0c01080e1541c070190f0400c0203a141c0196003410202c0307004000034050b503003200d03051607241e0003640100000450100001c21a404a6920604400c054842540c10b183d1650b9542800c560140d441996514900c04082c0016407004128a8201c50354070607449000344c44001041c1c41903138a00c44c640c8544084a410407656008400312801000680303000c5007505d606202c05400580140e8070540a0791120b803410111000c104202c8411090740c104142c01641c07400340c030409142030350490a04101d51004000340c030f00c00401c0a00308083c441e4001165404120400038101d5405a1096000c0d510b4140c80340c0e00e580342c45101c0350190b40161a840d6603140403000030303903400650354000701c0440b1040a1a00c280520000c43c10700481c1c2d2a550180d48990341c205042c818084d0449248000550115010080e01c001c801402c0c402c100080c40400f02030140c0024084840640103040700400010800c42c6111041c0501086144030f6000c02882c200661 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 386725647 1250 386724397 386724427
    0x150a12080703030b0306100603050402060f030414060a0b0307140102070b040303050d050a0c0c0b0a06170705040507050a17090a140109141209010302090a080a0f03020c10050f07030e10050c060a02 86
    0x110601d000d065030ad0012400395100c0004440c0ca01450440e8565241010700d00251103514006960340360340245e6012a0805006024042170b400e40140200246420a070798805400442d400090540c4070344c01b0001005200d00002d000214002d8603510307140c03010b41d01a42d00780c2d9402480a1880362801005490982d01f1601d40311400b6040304201086946215908004003969081280c214054030303107030486104001140d03016500c0654007400742e5224035006842c0c60007003940c0140461540c098500b0640c2d400c240319176014181d0300494201c0c2440d5114403c1c007542c1d06c08121504c3e51518544418403085c1c84480020350600001012014402c81549185001e00c2c0301c15410141c000642c110707241e40710041e05024000250907201d050034946880202e264509408402500402d8100c05036482d003039007440c5110300380c2d1b1181444e00501c030f40d40e408d0075806228110184401078109003500c0d101d03141001640c140c2500c9555840c01c401800a03e0410020300c0f1f0040c41d40108a1070800c04206 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 386726897 1250 386725647 386725649
    0x305060603010f150e060415090b071a0717040f1109091009050703020301020309300a0309020310050108070f0e0907050409020d080f1207020102030609150a12080703030b030610 78
    0x1034084c1020100308020072155003070000040c1c1c0e8403100120380842c075803504034a510b120710045e4680c044c0d0983c0d030b102c050400c0e000700480036184144911004c581949810740c03886d4000b46c42d2a154074034140d1205071001e5480d0980c0c0507103000d00700000b0b120402075001c4850010b44811260140145070a1036580e40d40c881c0049911440c1e511086038104000d000c01c8070030065540280259120310342402030a9a8080b0194a070300490441103111040901c41583e11480c40b00c0031021070310307260101c075090b0702800f4014002c0341c040c45007030070070403119a0503c41c0c14007034113071070015240701894020309032503043c010b80141121068503014811401c2c0001404070483d0000e4034041000720503800003620900c81c0380c501400800d000502c4075003041c0c1d03810041c0081c9613900240070036034498144c00c80c200d00045403000d40140400010400301c100c811102403404600529480314151100005d0544017081c1d0000c4420342808540c510415405006072102098150020081868411039080c004505 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 386728147 1250 386726897 386726909
    0x40f0e060a0b01020307050a060c140c1203130b07091e2304110301090603050d0806030a030c051c05070203010501060f0804150b0a060210051605040e1302120d0305060603010f 77
    0x540c84610031541d0091080d0b81b50070707030020140d454524140c00e124001d4800140d0820005032030b540c0c0c12a40500e19800d07160704003110b40082036506140400141e05900280014259044001c02035002070481096507104034103030b036502c0c42c17107a10f0880c8021460101c0c008030410f803020500c052081035190540c4600840302802e00100171320140011900030300c0a82403403030341c003a00000042690100340c1c2014080b05d110b00201c4280300b03412481100c1d0120242d4556034513801905503480400d00c03078090804594042d805440112103a042a50040c0d555540310030049000030440e1000d52a080c07207001d004003241c1c103052009ca005050300401c40d0030001d0008000525001d4004645169a4801241c01d80050075003400c0a444410181d91410403121502c0c0d4203007440c0004503c02451341180c0403840c500e40710036007402c0c01c000401151010007400300c40c50842501c204009a959050303900030303142e11a006000c1600c8840700040944200500450051800f000100400761100103a2001c07104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 386729397 1250 386728147 386728151
    0x50609011d030f150702060c0d0203070e10030b130207052a0a0308040503061006052b090605091612020603251d0f060a0c020627040f0e060a 62
    0x315500a06071090290011035054822642103441c0c2200c005001400340d44503a84421680e036076039030202ea650700f003200c015291130802d01c0705484101e16038006e90b030865568141885083e440c00041080076200ca04283e00080e22240010b501d0304003c51a400d2524022200354a406d020f525480d50302d82d16048966049460841884611582400410380903078006180303c2141c3d580381071550700e40d0018000e0310f129004440215034040003800045044881a49680d41462080d6440071170050070f510403070140c40034a01034920703c22644d1107480407080c82810009000c0c280910003904e000390b16011000e003034425084c03d1210904040081c01c11a0f41101c001d503507a503509501451454405154108080650740c8903183d03150800d81c0406902c1c0d0820110345000242003c02c900150311030081500144104417102002e8810740540f80e04034000380c000c0b8074000041944142ca1402c40e1280b5911810885440349285094000d402d41c00c40007402c24000e944210342d21585948010700302c1c0820503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 386730647 1250 386729397 386729417
    0x41d0402011103040b0a0f170f10031a04050705011416060905060f07030507020114130302161d060901141009080d0c050f07031203050907170c040b060405060901 71
    0x1a02c14100742031503a5880b400c0d030740c4441e518804040c40360001034100380460f031400c40d000c540510400c08031014101900a044594448401180d040700c805070620548103011100400840c0504602220345100c41c80c45035081c1c41c0034107203d404d0100340c1e0480703410490510740000709203181005861010301d07800000c141c1c0303e100b464a0001030442e8140100240209802c02541c5640901d04c41e1081d00c041c1c03002e020315070700da01c0300301d0885500d00c41c0d1800b003420b040003140140a8808420100d940300740100c950144a076140c17400d101c0100e5100c852580112107400e29022a2480320366004041510f0f024081c0d4108400800120300d80500c03103000700b031100f1901d86214407512a40005040f114196500a0721001e80241102d64004040d02c061003160300b0005441c50000c4c2800450350009400d201c00d40b85050114080d000240a62140e449100404078ac2e003903061f450380318040014001402034880c5a0284003d81c1c12006005120f25030034041000103495007401c6400c00c00d030034a0503907421 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 386731897 1250 386730647 386730649
    0xb0c01020403020a091d160e09071a0d0c0e011b05010b040216290613061d151207140d060f0e060c0304050c09090312090102041a041d0402 61
    0x900540d0b001950120705a400020b241400b58070a125a5001c2d908156103080c0d204c400e20703a6841008015001c620111100b00072810a50340c040d90003881400a5408155450400403482c00c1c1c540d20000c031a0b10001409108000c1070721800c503c204440c2072580350709080500180143c08604031000390b2100313041c0303441c04001c42035214041c1c4540c01401151207070f03a100a03038911a80d480d030b401c841c61541d0b501c23150021007070310f020300702e000500d000c0c40f00d120381c0d80074144405617985a2071040805e444e000c01142c03c8600c40d0700c054440f81c000c403003840c2d80e15103400d0b005d86806554410030b0043c3d40240c64000c9112001c19000144d50b410100d64092654503408030700201e05044000e003005240c070100c41280704080d0001c20122501e40300703d6506490f106203007103442c40181c80060032540a10554000d500702009403035480b0040d901500e052401704800722155190803142001039944c0040c0030f10100c4120840c405411203865640c41c103107400c00d504400c41140200c2150010b00c1403000040031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 386733147 1250 386731897 386731901
    0x251d060705011a10051207050f3612100c021603050a12050a0801140d050d08061f0903060b04020c07060306150e100f0e030312011a130b0c01 62
    0x3080d80d000c1d0081140552041c010030b414200091458480c008105040f030301c0600c56400d64150003484a068441c0d512800025200e552000304051800e807000d06c110605054034622112200072010400e0a20441d4042d443d66940080c46801e07214140640d0aa81c50101c0003504880c0ca0b40030710000101c11810450aa141c019040e480038801030200d42c0100c03c1280118101da4458418101081e0b104000d10064039140608220f003000140010010003a140407201d410948140207132650409800c161a0f9030b0510f8503501100001c0b403022001e00c500c07814094805898041c0614102040218506004001e00607030321001e00304603100c20b8078402c503585030342c106c456100d290802c0b1600c5655588024010702050f11401c2000341402402200e003034015100001c4050004020f42d0040d14815802e480b1000c20726004030820040c40075540043e1010001414a172066400e20300c065031400ad0810488400a861608114412f00c0071007030a241784403041c0103035401c11801ca610761411605440c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 386734397 1250 386733147 386733157
    0xc0e16030b1f0513090507140d140705090a0605030114040b210f01060603091a0910050c071707052112013503040b0d0b0a0b03251d06 59
    0x44036a10400d41c182d4240c008004101e09048000044880359807000300e18211901201e80d40c001c40da00b202000d40c0c0c0020704000745840b00c01002c000030354202c24004d031666035030129030120101d100001c01240030715011a0a1000b07240a00d03110f4915810f00000c4500c41c1c0c0b12404079409076440fa0382d140e155a841034502000c003a1858100c440154415007203c0c0d44481e102c035904090751801c0c5000c248640b29008036502c843e00301d40c09141d06240908200c1c0b4219001704050010b02881017851212001402001d01426050704500d403240fa290408102054040e005117070620010030410b00010030129489040210308101201142d00091100e0070f01e00c102d01001e003511300d1940000c5003560b40e40c40310b04202d00f18603442103014441303064000c0d2030b0030302000003003521307841440104941c0f45004000c0c401040b108401184510fa54404181008510f80000c0142035010041101860303002c00000d040702c00c100e010304a201701e4400701400e80b01000c085000084800b07010840a51aa0021a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 386735647 1250 386734397 386734429
    0x90207200f0105091f030222030209040b07050d0c0e0a06020304031703040f150203041406062101020706180201230706022b06030b0601170f040609080a0207030c0e16030b 75
    0x201a178618030010002e610030040c1661400c0001450f50b1040d071b0004200040d6a030140c44020107441c2e1341c440800200d0300800420801c07008000801501c40c0074018910000d071207441320001d085450701008540801500240210f500c28001000030512540d00e60060800c0c1e1546640d0701c1d1a03d0504605035401c00788040d01420406070410101000d5600440c451030144244070101000380c0c00308d580b20342c01901d480364000c150a40c0500c01000c1c2d000e884400103420000140f80001c940d172a002070382c507580e40750344418035070829410540d60410055611076512025510b500d805905082c203060103920805000300754085403d42d40c1c8007002460010402591030303440342140740d415a0350054400d03800108d48211428010642c40c0d4024195000e031b08007449401101c940d101420a04028001072042d0355403907d50340c032000820800d10042440200d0742d40540002411400d01031061821075002128a14104040245205500c01000111140c40c81c020440003c1c00b00081e40c030340c506074452 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 386736897 1250 386735647 386735689
    0x20a0903080f120c041526090f0a0605040506060a03080406080c040504060314070b03060d0b060607081b010e0d0c02040903032a0e0910030b0a15090207200f010509 72
    0x401140b0851348058800c444001840c05a000c40c031040c211010811a5080c000c1c2960340d40444e008032a64201c044e80c011101d0342115240c2103d441c00c9803800c681d8103003d03504699224144000d004080c00b44aa02a2064845000080c85c595540c00031f07114512640d1704000517440810b00e2a03c403a07084900500c001003050001540b00d05102c40e503040c3c2c00307803018000e12608000164800e0350400b681d214410052440c403007000b50340c892101c0e6074001401e1962000e070420001000506e210301500160103008407003694101c1040c201802c561a40005110541c00003c1c031030b0405501c070900011003541507030b01090076016442e007030300901603c13030201000082510500c0005541650a0703e04404c265680c50081c44002040c090b25000c10340e40c48401c00742c2403000b44049841c0c04101c0e500007609800000e00c540305038104038612941c58000001460b000901d00c4103010040b660800003503003881d24a058040320200160411241022150622a01045102c0c103a624042c0a440c030011620744 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 386738147 1250 386736897 386736901
    0x3091c091d0601120209041b0e01021603020306071b021509181b07030c0605010305011a060a120c020c040203100f0e0c070b270703120201020a0903080f12 68
    0x2025140c04054040e5002034100a0340c0c000314040c8000c440e90140c0c1c0c040c0c40b610100d0180b038050802a501540350746030001c2d01c3d500c45205036200540c1035814035a1550b01d81a4880502d00028141241443c0c50000c1030b02202c01440981d0b00403604640000d00c42c20702d494192444a540441004524400fa5100116001003681d182e502e0300180501101114004010002495400450f00083e0392940304541540705011550540340c005100303250090500504000c02e80d075030340782511002d0700201c5860351600b84a8050050600024450301411507801d800d04018680040032291084442040d9940760608400c4480c02404442c4090001030020b65592601c12003000802c0e010b0f208001910303400075030000d26074850281042c094202c0031409481d04a55072140f44c0030280140a82b103c40000c8045100c51400001c6070312018941d16001e0b00c03c00346182042801003c840751a00e00f903900411201d000268014003000940341c0c0452035035114035101d0114400c50040780b02e80c0565043d2103007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 386739397 1250 386738147 386738203
    0xa03110d0e0105060d05280803040501140a020304020d0b1b13080c010f0c0b04021c0b041205040807030305030901020d0509060103060c0302130303050c01110a030b0a0f0501020705060309 82
    0xd480400030090000d1384490341800080c1609160152890b042001c1e40c3c0ca224181815900e02030504241c3c0d2038a0364515102c1000a5106a500300c4050f1b65074000100d00c1d0b000300001d182d000d4100320045083d807905401080c5160071580d0000c00304c485101c0080c030155068000811301d240d900f80308070789504880e0038003901c2d2140d82c0511449845100aa03488030742c0701e022204000c090981d81c0501901581d5140100081c0103402264000b540042511412407c889090700d41da025240702c44546c2001d01b0311940142107030400d18100602040240032802c6c1c00560031003225414501a50380703036542011640280110b482801e8480e0a000c14000c01401c006029410303a8090b81b4104840b61703c1000650483c41110703480f40041d0321041b410800700340202c003c3c0010302c0c110300002c03071454401c0700c1030b808590000e0001c202085d0340d440c402c0c4140c00d0040204000c6d140a52400d00d54500b03020020790b0310b47c4140700d600d00c00c650002c0015030710b59007848034040000e28030000c6d00c60414104 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 386740647 1250 386739397 386739401
    0x609130906090b090c04200703050c030904150e071715060f07030306050307090e0c040f020c070303180b090603011a16050a030f03150303031d0318030d0804080a050a03110d 76
    0x805040d00c00c605228204151403c01c0480110121092017804c0c078152140c2ea003078409401c1580700c0cbc02940418804d80b00c0c01c0c0c690340582c5050718091f0510f100c0017401c0200481c44503034040c2081c0100040c40b4030140380d0036101d40c5800e8005050b400c105201d0744081000820a10030031107000c040c1e40c0d000c14902e00b0036030143c0181059603001c8040c0d41156846c2c1d10244101d4240007203a285c668031640100c1c83c1410190311407606803110020140c81c00e40318100c420b2901c110b55100310b00007240c90080181316095442d201e0003400c03045400c240780c280b100300051054001802a9016044502d1000c04405080c0003100c014010181c5a204039494600b0a41d40320b440325801135010844400c0d1140030f4601ca0b10454003074048107a40c0321a00743c25500e00b140101400b005100844c400120035100d6003400b00080d008500240c00c41c44403500d4207030189401c00c441c40302600b05009400c07051100142e00c920a58032161400d140050f1262003400c0b0031006000500074003d6107100000c1c40e504a06400d03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 386741897 1250 386740647 386740663
    0x90501060e060d031b020a05031f061502062415031b03160f09090e0f120c03030a02091306030f020a30060f05130b060609130906090b09 60
    0x100500c8642039890106125079580508002000516591100c0e015000c1c0c40445e43d01d094006414200000d843c2c3c400305e482c1072507181c1d03564080850860302200407081406100d014100016001543e4000000041e42e6200058013200003100007500c040040c0c0c4145420080310100180b059101803078608050410b503005542c80300c0c41c20001101c1e030303802e240d11404070b90042010755100300361040c1c194803ca48441290809504002030b2040c0000c1c0c06100c0c0c014141c1c5074a10340043c290104042d001c0d18504000502c1c0111021414040800c4180e8084152940b00070708410150b922000c031000141d003d90b0740440303600c1640c50301c0008070910041c1e6295038451031090740d035650403640fa408031850000c9a017461001c561841159445a585501c90307214a407442040046070f4045281d0808041c0da104903042070203200b0f21a103010601401620081e000402030750b0852600320048080f03044140d403140b03c00000b981b50a91b000030070045600641d0f40c540c00001503070b41400c02d00c8000b0f4482d024 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 386743147 1250 386741897 386741909
    0x607080a090e01140a050909010f0213140306090c060d090507060f1112030a0c09080a080307090603050c0f070f05060411040f0204050d02040e150f01170309130510030609050106 78
    0xb100110303982209009030780010b100104000051403402040060310310006003012130a5407101000d10050010740050580c01d51240c03445003006041a4600b114144061031091080d802141408800040424000b07143c0205031800da40e1040034012200c0640480740b0003c14500c5401000140c441d84114000140340315951180360010720200100d07030303072403058440d40403004040010440080455211001d2030030fa500b0701e81c07030043c0d41c1d00040d801e04100e003c065034000340000820102030f920012031030240140b400d04001c11300340078a140d00e542c05100320001206000140d11000d000100c03603141006c2d5849001c8401601d00361800c411425031840d24280154100007013140f210006009503802e656001d0b0080e00c1e0b02459408000152030b00091003200c90060040c03203d10100301a03200c2c0d214158044600541c2d5141c0104110038414110000c2c0c0b1642003030000e6242a55001c19405180d026084049065180c00c27000140c130403a5a80014080c0d4903180e4003004005040d00500100d8403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 386744397 1250 386743147 386743169
    0x406080c040e2b140c0d0914181302061908070921060e01021c060f08060f040c0e0405010207051504050c040c03020405031911010201180b07031d0606040b060f180607080a09 76
    0x6540c00388980c041c1c460350101584a02c034414440c09d041c02c034109003544440050084030a0703503a1900490103c0c0c3c8250103000c810540c100d40d204200d50841003158000c095840c1026a0515200110102d1a09200040001c440d04010202409501c6d0415001c03401c0c0340c0000c56565100003035000000107454035613111581002d40c0002c45003620107249049a205402901580e078440b04440305000005000700c80074101d6940103d00c0000078041c25228602c16000143d031540c080c04c1c15450101f550f4600e1031480d05c40f104200004101042a40102c0c10503100400c103500510010340280c001c90f04080d4044c0704086546001e00c08420340050114055010f010390701551134012820790700905e81c20411079565601140008450012043d800445482c0000f034407440c04810602c607129640c0d1181d0554481810300005241603c5408030307505085032010714241024034802010b014001d00300c4007000311881d0700b00340c1d62914001c0f0351689a01060080d1384180d4500b0140c5024041d0141c1c04040c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 386745647 1250 386744397 386744399
    0x103030302070501020d4805130f030506070e030705130e01060509100e0c0a023004090506030d08060f06090103111b061602030d0513020406080c040e2b140c0d09 71
    0x380b00ca03c11000c1c0080060300d0101c021f6100390242c1d050351250404120481c402d407030004007142c0070036151001d144140701a00607810a103e000b402070300d016004a10940040d601040546d0720403448400042e4449004070b039101c1c0855042d40185656802590004d13880b0742080407030420f03100044140c400307282003440151583c1000c0d040314000d0b08070131380c056804420b900403002007510075004504191b05d80e80801a01c000798070700b081c0d00150701042d481500c03002030250b145014098140340714454135081d5880d240c080300041c450300c890f00e0454080c48000440f14a280d209411071000d582c0d00403600c43c2c2d140000010501e280501441883d050702415021413000c1d411546001403200544d8029420401c078041d884004080140c40103209000c1040710f038006032214056800180003050117050387e40d21034020300c0280e821600e110281e68010b140c08181c04601d2200802e20b500d14561101d06004400005466041100480006006002c20307600c10340d000006960340c071041390f940e4603c560b07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 386746897 1250 386745647 386745731
    0x6080318040e100b04230f0c041a07060b2d130e0c0a06180b0d0e010e0705011404121203180c06030c0527010207120c0806060901030b0103030302070501020d 69
    0x140806e409910600d5030741d000400daa80101c040c42c0340d0011038103414240703440d9403481c00304015521211820135862002c50340c1000d2080b03074464000d507800c2c10b9414902200a0301400c26650718207040b10440c60800428039042919500141d100c3c2200d240f070300304500f14070f1400d019500c050740004684250310aa0780031a01034815132241540b06800703040074241c14201990502190081088250b280d59154411805000240168105040388502410125052500051441d0081a101501004108410040c05c0515040e4800103608081c20444001150300201e01401c02031a40600034543d80c4030b40301c2071124000400040b0303025500c04011891102400f036800340910300b6a81034052070101403089040c0b03c07c000112086052058810040d103445e14140d001c503420a0681c1d41c074030318241c10300110004005c9103803c04421a5446000c0d2b141d50307a0804d100505000040401d40c0101c0d03c00c0c1044401d405589401150703030424003209000c801c5850090012258072502191507081c00541 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 386748147 1250 386746897 386746931
    0x20d0b030a02010f0809160e04150c020309211609050603070e0a09170301090906050a092a0b121905040503090d03021204060203090a0906080318040e100b04 69
    0x41c40d0b03040e142c20030342000241c1c06488401d4002c0100419005188500f18200300c0510040041c22885204901a0a01d030030282010034030358001004091410680f5407215400000340e902c2203500700c810060300c5075008a40140380d44520014103551080c00101545500521502c405648401e0b4040015a0b16102050342e10303c07003482070300c41c2c525031b0202051003600d16411a0200314021400000c201280c48046003240c4d10981c0141c407601e03a03c01d920400c2000c5d84c010542c103c540c40e41c0c103101401e915120b1001c0201f00348200035108a0003a02c074103001c00030b251913100422040414030780351504141903200d00c040440305052040301c2074841ca00421900d1081701d00540d0060015428480c607101444001921000c0c181c055109840201464160703800007130000e0005507010310385410000060004000058200d48540360034043c080c408003074004107940c02c2007211140704c250114000302007401000a158038140c1c0b4014416200f0030344005800006488100f1345041124900305100198 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 386749397 1250 386748147 386748163
    0x21071a0910110a03020f2a0d11030f1c05070507030f0c030806060306010203040305011d01061212120204240f051e09012a0b0f010605090915100201020d0b03 69
    0x20b81950610840071910b10036809071032465400b4407424500412403404c403480121034060b00b5800c1c150501c01e05180c400501c0b14641c0b900243c2040310000780740b011301c80d80780d004150710b0718031203800426000556015141000444e000c820002c21407801c0003003000340030780e124480a801080105407100d00c10707841090300c00010b9402d075031015010303100c4a080000030351015140c9030443c44240f1011000c50401c0c4141c64250801c1825000b04020f0b9000e15802d4510a0344611030310001c101c041804199040c2c59174620800c68078040a03d0030701c54007c00000c0c000c0c3c0d04104042c011580e0b83c0501c1017281c0c0c0c0301c3e401503021510340c01103803013004100b00c40c14070a0340241c9110f40042052143d11589440182c2149001410108644405204006940f03400c0c0240f654070440e4402503c1c007849001080c164000c2c6101d01c08100b01e40c100140030304584070300104140a800f00750002809005008100f80c00b072a0020b00c2058207d402c080000d020750003110407212010b03d00100080140381c0014100e0b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 386750647 1250 386749397 386749421
    0x51003020d0312140903220f090f0608121228021305060405010e0409080f0c0303010906080309011b02030c04020c07060212070b01060507030903020301020f0a08090604030221071a0910 81
    0x940f0742250b00841d00203140c0800030070070600364080f1f00032a03868006122407014202190002990403880040d060641d400c60b44580c9482d00a404020300b07811003082240c072801401d206d80d08103600c800d0000d50f031b6401c5407981c000c044e8a4080c0368802d1403200d44c0082060300001c036641114561a00204012445039120341808140c440744d4006442c101034003c014a540501030050401a83d1715003098580e01810650883d500004018440800a8031650001e0074000004509001c40e000000c0d124100030511144000130070030b0320008540e400c0003c1000003030003400564582c04503418403a950001d0b0b0090102501880c0c03454514203000406030381d40d07a074009810081f035900e05503095619a201c01030070b504128843c10f000c805a182400101440e2508000b800d90f210310b4094010204a0040c03c0a601600203400384030200307078000b0301403006000b00d111200d0a1a4803039030070b40452080000040100800d007010006040e0054034552054400c07c0a8a141462a5005034119480e880a407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 386751897 1250 386750647 386750653
    0x8060a08030d0c030b030a1b080c210307050f0d20030a030507141306090b0c1c02033c070812060406030b091e0309090406051003020d03121409 63
    0x140321042c0a604991008070250500245d2144014042401c1503000708094805c9142c1c5200802004201c2445100a00303900c0050129920800001400760501c02c28280720801441c0b4105041e82051007146c0d5029800b108440d80e1389800c14006403500108a21040860700c2c0c3c800c2186c9039944d003291800d48104480c0070b50310780000303d02d0907401440c0150883c410080c6906c0404100203c0a008140c050309100103007101e0752814000030442d0099800000c103258051001b41aa0b2000158030f0b14050201c3e2600202880100d5040740745000d00485414129056100d80300008c00070305c81c20b140e40c0204900e40d1000c440c02e801c0b8181d03504c6156401040f0141c00c01c41205400c401544641c0c20107001000826416620b03128001a5801641e420400c0d4224905006090500c8056400405c00b004051810a0850030010301165001000039008030b848000151a079007209001c1005180d00074044200400701d803c00030105246e10f4a101c021901e03000c071654020b044000010b03c0742c030b440401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 386753147 1250 386751897 386751907
    0x6181506051203030a331a090f09061c0b0907120302101112010305160602010c0c150605040c08010311060310052101061404060b030c0306011d0402070f020108060a0803 74
    0x110800414100000658910505c9400441c0e810b1244d01b1800c4c00300c0c18440b8014a5042400086101210b14031074030310010308000329a115100c200d102c80499504a0700a082e13955403102298003940c1d800250409803440c60900020040c50800440c0a00c076020f0450f0340c0d40d5160f100c241c2c908088080b000d40547d0004100904000c00b5810a9032407000b03c40125040462030b84042c1e8032104281c01c111680e405c0344000148484203039004c24002d10540c030081c460140154009406000c407400060100071540000418000c8203411a00041001500800c41a040d05500402401007800105c450290060140501c0c2c80d206042d01d01030301c01302d0300c0106224602006c00c20896004500035400030503492124420f000203104210041094180b811010460001003104684a0380c102200120b010710500405811100540e0ba02810a0031300f482502c0c41100c029042128206c3c0c80f960050001070188104014510030200e114402c0c4c9903408262180804c02c04446124040c1890650007804 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 386754397 1250 386753147 386753161
    0xe0705150c07120f060c210e01150f050114091c050123060f0102060103170717160204050f070206041101170c090a0b040b030406090618150605120303 66
    0x1010100e00078000c03198969615011015100349016068603401c40901300b00e024400030340528003107200140303040310803042c041c40808044690351b1540b904407540c519074800140400d601a210389005040d0080d041550380007440a0140344e4000d03d800100240e150504240c2d40b842076440c02c0400400f00004100b002107410b41c00306464509840c00c1d034880c440e0203600500c070444503006483c0800c0149481c81d0480031f1006106e651032504d030440d449035004001050b0f040c01c10b10f07036149c011030403a80da445907810840189003041c141e50021101c005041a4a8403010742801c80d018400c0d40c041c09280d4031511124a2000200e6012002d0303000200003500182d00b544028500c03150504000e5030560529001d414640300488681910500006c1c14407001c0c903040088100a0510200c0e892402e0b041c1030003495180000740c0000c01440e00c0f42c62010810081d600000d003140000c2403040d254070510b042c00c40b420002c2610403201246031a401040c070381024071288801183c03400080d440e585540f5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 386755647 1250 386754397 386754439
    0x3060e0412050a09030b130201030b0111100b06040323071205060f1b0f03010e09030403170c0a0b16170c091905060c0a03020d080403090e040501060b0309010f0e0705 73
    0x669403d0400089510200009404215242c064283c22417411861034981c400074084407441c2c40b105043c00750380d80340203045d81d00000d51810000200304012911001070800701c3d0f101d01580c0c0000713051124050540f69038440c00c503070b422254602a01202c261682c0c40e05141c040c0c540c43c41c0081d0898018800280054180e141d00540103200012a000c18145098000201d604094242c3c88030304130001c010003903243c00080c00c0ba0000c1800001e9032a0502d960344c0d071240c1064031480c030300f16003030045080c0b4400c1405000700043e458026994082500d030410702802c20811600c80800882e192060004103000440c00c02c51003800b1000d5540c0c42d00b203200c001c21900883c0858038071440540800040780c29112107004d000b0707082078480140410125860301a06080241da40300c8100401c0504000200c0d50100c1e9503011141000c09504080c0c5890521502612241e0409407925800006001d0100d40552003480c264180c00010411200140c05560307d4480902c506a8022051001498414905 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 386756897 1250 386755647 386755657
    0x2101406060f031302040e030a0e0a0b0910020c0a090509061608060d020d12020a150903080601030f020d050403090609080705060a0e0102030c07120b060f10111908040603060e041205 80
    0x40400da407144c0309039130010f03007603407150f0710303000025007022440120194105035800c42c8070f101115030500c19070038200500300c01d00502e00c10078802d15401c108651080d0007884850303c00c1c100581301d00700060b1a10b20010142c0340544007030045100d410006080b484a509518440e01100e9848000c1038480e0170030000103529910f826a4001e425240400001c1c03c3c141c0305001c4e030030b035a4024114400c03042c00c010845c0b4800300040d004181c00c00c0810b600003580030f28101d501c1202400d00260000314040c00000900508420412440c9008140000e0640007400a4102c0340c1590701c1d45441900d9603032003501c6404600c985034220070300340000c107525030003480c0c0f10b0711610b4188101c0e404d000540b6070307461414201d40e000c2d00c050840b500c07250003805030745040c1641c4103600340c40d10204406100d01080c1e000c1d516074400e1b410080b00c00300c0e000415400380441d1801540a270411000d0b10305505103000c15030320030310420002c2460401c00144002c501d00040e8415038008061003018110120140c440d40c0c81 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 386758147 1250 386756897 386756911
    0x110904051e1005090609010e070b040302060a050702030f010b030d05040807140117070309031412040308100503010204030303051801060b0a14090a090b010e010203090a0b0d0e0a0302101406060f03 86
    0x190b030968180b0b000e40c2d2203810b1103550301e07030700421050134251042da08680620021244c11303000310300140030b100074800455044940c107541580d40c80c0051242101c1c41d0180005c02035143c06540b26104030704005400040c0f0304103049050350b0011442583c161198856803003081c00d250420700c403c0120944000142a46a00604061030782c0040c1d0303070f0955185802200c22001190341c1c0c81880c0d080c1a4081c102e40d15200d000d44109182c105011042954114000c00040c20401c00c000018a5116003c02c038000401d0090000d6445648918025024120407681000341203000020034003106414007441c0c0071103101081c5286003a00724242101c0d18020310071040341003603080001c45501c5d11030100c0c5500401018038000b54401d80500010104650303421081e046600501409526a03103003e1540f0854440400d01961850800280c0f405081d06070b423100d0700340c041c0c03920780014150049081c21540ea000c4200304102c5408a0103071007800400d40369550442c034140604d14000402000079908202 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 386759397 1250 386758147 386758153
    0x3190204020f04080d170f010509040203070f0b180f0d08030c0c0d0e041506020601090e0f0a14070e07020a03050703031404150b0109080a03180e0a09110904051e 71
    0x80005940c0340d40c030950040032203074017190b103040c4200e80c018101e030a8140c040c3c004030314500300b1001e500e03001d41060180074460162000410110b50741001400010b00300d8403405030b170a6a94140301c5a4503040b01c111021402d034100d0810945285c44034800103610f0f07008000d4080381c3c1072500c60a010b81c000410103c02c000041002440071002004407214071341c00365403901d21000140c801d02c4151180480c0207071241c81801d000f0300c00244c0204600e0b054900d1074000061401c3d1514400c0c0c50403140141c18002802442d4450041c040c0350400d106400240c81c0494130382d030740d9498a984540c0c100712001c0e0010303000b8412082c0002e10810040070b00900034540400c1c080c007c02090300b20200261011900b5205c0c1c100b0108540156024146000320709003042c07040507160025040e02c808180704003c003040307800200107030441c2c4070380071282c060003c00c104031b01c00340342c5869034200400d010b180c19640d08402c2d402e8200c103071604a010b2403040760303c8000340c2907114107802d0706140150600c0134035100740 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 386760647 1250 386759397 386759407
    0x3120a052211011103030f0606030a1d0307120507080909060d14150601090605071518030203070303150302010509100207081005041103060c0a0e220504020f0a050319020402 76
    0x3802040204480d60140840030b144642da500050200c0c101512650f4041d0402d0041010b05038114644503032190302510016a41c0c1c4d030f8402e012000b41814425803c10303109010600d020349100001034021588500003030b030700180d0003a40955142c059000d0041503d0010000300802c3d041003001290044009003054012549030359800e0305909030b021400e0501d41c0950400010740c282c94540c90741242d2700303081c2112810700300a0300411520a4141c040c2442408600c01c85c1f0861680d8010703200301c1c8400501040000b203a1400030b4403988084401e07000603040510041240c1c12000090741100d80c161102841c00100343c00303108051100144c400c00754058107000080d003000031f00202e00f91900d0b144000070ba52400745802840d0f0110405024060391101d410005510014022501582c0c40380c100742d4503480e080300003c0c0454044924081c500a14543d90314140441c940080c0e00640c401c6034140c4110304d421042c8640c2d4039051182230350681c0100310000507000140c4175a610309001501c058901 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 386761897 1250 386760647 386760691
    0x8180607060c050a030510050102070302221e050106080f070f02070b0307050705100c200c100c0b07030504030203091003060911070201020d0309020102100c0e0a0306020a020f03120a05 81
    0x8403407001d6400081800041e070948000d42c175208099024400a160249047c1005d000030740d02c2c0038a000090041d441780784003440403031544410300b060305400c0c0d10a010f15800d206200101c00c810036203000040e4108000401c01d58040c2d03a00c14803a00008256401c82d90790544100d81c100741c0d5400071010340c054110086016400540214800c0029480c1e207130707503014989051807401c0c005038030320f03510b2a24040103200019132040e20f204035151080e0b00c200c011030410150030309261285280b03913484215070700b400c6140d9030072680c0412258080d0802d61816901d0705020b600340c0d041260010010381040256000750729240c03103103000c0c40245143c0000d40945442c1d01204032002d01c3e030030402c4203502092a904541c0c1c10458003401603003501d42440101156070001c1c0d07551201a40d66071805032200104450207129000020308a00000e000c2c0000d2075490a04400940c088519a0014003c507042d1424040e0000100ea00c0d80160b0081042c2175980c4842c00c01c01400003415203440d01c86a64888544 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 386763147 1250 386761897 386761901
    0x305071a09100b0a03020603060a0b0c060601110a020f010f030f0509010207060c0906080c0702060903030712090501051c0e0c0d030f0f0c12030906020d061e0b070818060706 76
    0x226030303200480403030390410003401464021041185101c1e68100349008501d501d8145008088030f9054440030384a4548100284004800303410030400500046000d41c0c4000e00090618018202a00e03404030718284031010f29141c24080ba001f030f41000c500c0783c441790b00d548500b884480c00700443c60001070f410040b11401c0c099510030380c2c0141e4169000f00d0400300b4001507104203030480c1080d041042c035151038241d01400c10700008152190300385020407a001075407200c100b125203011004080d00d070345400625045800901098003103001400111001c0b8595000d03008503090307100c0c407030039000c00100c844501402900e4107082c1081d150040040080c06925800e038041e400c144252034881e0000d40c1c20200030402070940d240390742001003902285000c106248050040f6274110718020800429a04002000e44503d4404c03540d0a49040d00025003445100b40da2030503400121305141d215035490044084a004003c4003404003081005031041481e50084201d03d15140582503d051664640712070007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 386764397 1250 386763147 386763173
    0x90e0c3d0e0607020d0b270c0a08151b0706020307030212060406180905010b100917011512050a14030c061503031b120406030b03010507021c050a09030c0b0909070c110607030507 78
    0x47d643e4410400c80b546484c11003080c8000e450900001e101004011160100090021b0f2071300384c803901c091038400c1c5040b9954046800003a0000d00035562400c008000400079400144458031517003c850100760f25140502402c0203d80700d110240c10382070311115490300180b020b40401c0302c5c103660714442000291a4500d5000a084080d11a5203c0903d41904000500301c0550395400d103901d09048000c060072540d0085050350b68150600d001c034101032070800d1a011420002a029548500381404580d9001009255022401c4141d0b0306503101c1c900e004110300040140c60794141c00510850881041e0243c61080440213101150840c3c1b003405005032940d800394020400007a10740340c511480b4102401210f0b044405840208954a103203000c51041d4420b14100c60104100015407140300ca1090707880f10003440d00401001c4940c1ea0b1615002d8459000c180d00500807602c00001480490147c2c11a04a445c0c004100280e0340701980c0800c00d180c0e0224400b2001d0100c1446001c02107030001c00d440e1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 386765647 1250 386764397 386764471
    0x1091b0e010e0f1519110304060302070302161503060902030402060712021905073308070302040503070b0c01060e0f041106071a010501020601090e0c3d0e0607020d0b 73
    0x83d035504046170005c001c507440308210018485070082089589900208590403030b5030030700c1c005031112000d01c0c0c22400c02c04c072485003107600e040f21840410302c4100070b04152044101901d04221071a07403001c02d40268042107a0195024900b0300c81040442c0d8011602d55144500d88184d41c0d003541030290f8514041501282501d40398880f00d001d01950460300c21803001040d18440003c210000212501500e0303000d10010020015000082100f040c004d4060350040c25006003078480b102d861341d4100c1401e411480820159609180000900f10416000750340596036042800846941e03e4807001c2030400d4848846070840c00800420020444891042d000c2e020f4400402406501d0301c0002440c00344103812001050349415894241030300009104e1845400c281d0b20728009004c68010401d013052410541e8810300142c6030b80c3c03900c00300c41034a102d00540c00c50b10b41e44c0d01144404240205030103201e00094002c2800016070010418030490f41c2da1100c01d91102111158440000308140d0f411441c0f58 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 386766897 1250 386765647 386765689
    0x204030f0f1a1501030c020f030c06041a040302100b130504060209040614060a081005030307030206160315030816080c1011070203070b030c071a01091b0e010e0f 71
    0x8404014036080400d180a00800940c152400c005000a81600f00d0803079880c141a541d24400c0b010364028499400b16039600002d0320345583c059540d41d0b803266411141124900b10022a40c0c00500e50b04140f28040d0340c056009044540c0000f00c0400201003129a02d9803003041038100c1c034420305d52801100c0c03295101d1480940c0b200031800502095400b141c10142d40708401c1142c103c1107450b800306a03108003550789401005500d88018048005205421032501408000303038080506800081c014040c1c3c200c850080100808283c045048030025200c903201d44c20f000c40100040342d03400300984034103c402031070315041408950f2a141a41d2200280e45400d80120301c511310279072100d20455100500110303005141040310342c0001e03207450780383c0140701d080715021000c1592000404141c2c0c1040d94042400e503200107a0469046420000b44906420107050000039101c0030090840c2d0304520000d500c5040c20100080b005554a0450540303140d0000811207148217256909a985003070000a4060 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 386768147 1250 386766897 386766923
    0x9031e0903102715050403030617060105100807051b0d0909050103020a12210825020606010e0612040b0414060c0a0c06021603020f0106090605010504090c02010204030f 74
    0xc1c03608100302c41203031850591400b00b05140300700020340042c0340f4010144810b52074030101d1500d41c495000394054440020315100410003010740652202d03007a11040403004d00b106402c994080d80d503034002d00459410000328061001007074007404000b90805030a003080ca0900e25075200b44069a255240481042e6010081008070203401100320400303090344c450144815811030300401c44c2c80d40541300d9907400c001c410303131b00c1400d0020380c0392070b4844a000102c40300544040004002c0c240c0e0401d8500d000c03804101004004606035018a816030220701d50003902a9544040c01516414415180b154124070b0400c8076031042a164006144540d200b4400020306080508013804604180e00d40c5440301c1d4400010f200b80f0710780b0b00003601c020400307a07c2c01e040d69214a150880c081d0048900e032a031962170010958080613000b00e405005943c01034020010a41c3c0d412801080d21018864540810400c100c10300507441c0c180c100c0c403581b4103240005440c1603581c1d41c0d8110318041815050315a60907001d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 386769397 1250 386768147 386768149
    0x506070c03060e010b063f01050915010e0114220801051503100b040603061107050c0324040602070506070507030314060a14042c07050d0b0c0309031e09 67
    0x2040c3c0c0b4006007544020004516400c0104e072482c0300b2a410044141d000713842545000c5c1920251a03008542042c5003028201545007075003041100b030145501c01c030a01c2000502c080d50180440c80d200d18160348052840e0b80403801900c502c0348002001d000c0a40030849028030410600c58803d6901080202581ca18580b284107804c688014042c007401626603141d24189981c0024000790801c88161700151084607580042c0041400754001841581001c5481c00c0008501c0040c0040c24041d0b0141e94000101c001019140c00f0310b0740035240240004012168210343e41452207a005119040051402550b84c8446161540880e65000000c0001418204040e4140550f80c58100e03900140d99450070400c00141c600c181a008a4b00c01484110102101e0382e0342c0e8114107107d15401450b5840982c41d01414820041c908507401194480c0c441c0000e01b40c01c0503c50084240e400648810464030f13094007620844d0300190441d00d5900c400e00144010b940300c1c0d549803c0400045260564591000c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 386770647 1250 386769397 386769401
    0x18030e030a02061c0e0a03080106120b090c090d060f0e120309060604020a03021905040501090f03050303060603090703050f1e030a0804110d08030f09070e16180506070c0306 76
    0x1120550203500410030000040e00d03918250f49815100c8825030310112602c0f59035a000b480d0700781400c4000d106880450b400c0c107400509140c10b0700c1c1c0c95602c4494075003150300c03181c040d5110020a80c0d00030b8010000609a640d24502811b004040100074020413400ca80300c0d2801c1d2911404a0380070309680300c1e0102100c0300c040001c01120902110f40c68118078140348040d44131040140520300480e000070340b11000c2c510a40c1120700c201c50400209841f07902180c40223105800c030340182804a0b55070040400c2c0d20300001c94260407240d01400561541d80d030041801200d0308090800c0e4005e1007550340120010381c3c10300c151104c901643c0014a0340070b0882141c14a0107030401010035460f00204a039102180c0d010702d910b135225402075410150305400c0400724004200d880c0028056440100500c11b2101985007014016075541048816a5413501509422000140c40c006200c400c40d00e1641442d40c003402da00b0000000c0e04144a4002d5900c5002c03409591040008480004403010300f4002c12241c4c2c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 386771897 1250 386770647 386770667
    0x6030f1d0705091b03010603051e0a140c040f2303032809080d0e130f0501090b0603130b0c09120a14061306020309030d0c020d110307030905040b0a05041803 69
    0x50010749601a004440d01c1d44c4d910041c0156010181c55000250740c80d410000035600f40c4940307042c1100145420301d5581d00800d00e890216400f03141d1a0003169400d00741405441c181c550b2505c122482c00d00d440c1c0c01044d4211080c40c16209260000c541c004595403d0029000003800030704081000301c1401180c8419084040f20310080c05072095040c4011540010301c240719003900d0618045401080e000190720741440d4400d44141410945049508212074200504840b03803d81d00f0321040c5001c004000702804100c8038104400f200985401c0464a0401d001390020030300303440940390901490104104103040c0703850318040e60001c1e05081c104060320340c01d44140a074044c007502d82e0307082c401d8681d4900c6030380c004c0107842d1940102c085000d0402c24400c4884a81061904100090300004080c0d01c96918614a01c04070ba5090341d1031b80d0148001c0111240254141d484964250400b01000020310320524901e800c0080c13500c020800b80c40f039129030b1400c2007a501c4100850481450003e04a20507 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 386773147 1250 386771897 386771911
    0xe0405010f05041509140615090a060e0708070905040203010902030601080a060608010b0f0d0507021f05070c0f240e0c0a05031002030405160906140303031006030f1d070509 76
    0x42d000400010031040d00c00c40c0030724420814007007500c441900f80000100034442d0302c281c0314050581804a461700c0150703400a00d0b241520100b00c541d4817100c017503084a90381d11983e0229100742002510091180b40910341c00b40c400c0c201250290f44600200f022a0001d030401c8501030750000604c085c540c3c1040b03d031640510250030510a160a200c0c0040265170184a411140c8001041821800702c1c40380a440c1c001c1b6210b17904020514043c1e000940c2c078409400865130030032071502e00b440d852000d030080d28401c102c40d444810390301410b5914074000f6845000c0550325104840005000d10400980031601c0715038561022a0703024468185600345a6100d51031031148081280c01c02c45510040348104400001e580c1c01626603455050241c10604800345c001182c070448540840c3c0c00c2d216034400010b40b1600c072136944484c0041c41c1030699a02c025691481241d1240f1000c014007486038006030040c0088410114466404c9600002500600451824a5000341c5010b00c11801d080b0003056000038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 386774397 1250 386773147 386773151
    0x103030e0f04021c0b0d14060627061c060c080105030c0307030f060209030a080a2705090604050403050f0f0d050c031e09120a030e06181b04060f0e0405010f 69
    0x18820510071078410400f07500105649401980745d565451040c0b880d42c0703940082c0c0030400e88108010305522030a041358054030030b21806400100440c55084020307444c001d1000d4201c1c80d51a148100219045a0000348680900da1800c010026480780141d448000d01d0741c07039094155060008050034048002c66032130183e0b0142000b0400f1a001084c07204446070400300c0160f079050000c000c01d04000c1150700207400c034640003851002582c0e10100070f0500a0f9035107640c80b0002592110b106070003056100352980241840b002c62079624190384100d800ca0f00c2030910714a000600d101e0b507802c540010030900c41d0380300e001c1404030307250016000b00d5500c481541106171441c684650b0050408404c070920200c4005414002258000c04100001d851024043c5c890303183d030034552004002d02420340010060f80a900e001c030b1550099000342c13124070f40ba80f90207051000041342040244403088c0c3c0d10b2580c4140c4801000134107420340e90300c5c0d00c0907040c680d038608810b1034503040c0207081d1803c800b50410103c2c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 386775647 1250 386774397 386774407
    0xc01081006030207021f180e04020f090604140106050721021c030b0301090605041b240e06030702061807030f02280807090b0102030705060403030b0303040e0103030e0f0402 76
    0x612803801000e075850350a0040c3c0300c07040c500202d10028403c10740340030008008110824400c1e00140e400303000740f0b040c10300302c42ca030b0b03031191100086648182c6000b5006890312482034120316292404550140e000741c00061410031100c1000119402a03100340003051002405000f40030303840613400541c0d151207400140ea94095a8001e43d11040107801c3c6100256045c07144a40318801e80113007041400050003404501e06a04205000341002d9804880e005808485aa4003102c4403030ba0fa02100d0070808200e6400c1d0701e20740c0c580712100000c45054100100c086800c81c403561124083d50140c407595000340130920f0180b03816103460300e4001c0e4088442e84045420000600c400c0604e02000e41c3c190303810f06040141c4410316110070140c03000a0000c408403c0086420301c00090305200b2140200d000303001582d02c800040e0b8407445142ca01803c26040345c0c1c0040c0100740030790403950080302d0140c00c07a031505a0380c1044800100e020782084000a007070048141d020300e429807180c1d0840c43c04440440c680 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 386776897 1250 386775647 386775661
    0x206040c0b0a052206110c010801170307020306090616091212030f05150f010509060403020d050f030307050a1e02100c120c0314010902040815091204030f050c0108 72
    0x850254451820200000280d000ca824031842c01e41d44602a2020400021307110707000d00140c414224000d02000500030050401d00c404009201c000352081030310741c1003071a406e10140c110382d80f00f5840340d000b840c48104010703401038508001086c45102a9000390501d070500d03080c1d03440c410700c24625a90404c00fa50b641030050b0807204501c080d20039400407155030190700040301940035014600c3c4001c81070389450104801040c911882c1207000700200d60041102e074203d001980c1601440514a80000051005100604141f2101803141c0d000304100d81c0f000108030899031840c0d1088409030005103002c900154042c2c1c0022001c0e902d8072120308080c008184003c4000c0d038410010209209241d107820030000c0b018000c840c03000740c3d1143c1d44020710141c981c1c4071014010382149003140505106290000601400d1442590300355000c04000c3c0845885c00362070554018400b422441c514040c001c80901c04250150040c0000d500c1615100c0201a1070704243d410800958101d40c103000c000301c03c000340c2e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 386778147 1250 386776897 386776913
    0x11a030106050310030609080903010c11250902040b12060301090210051615061403190b090312040b09060a05191d0d020102040e090a030207060c0311060a0c0f020604 73
    0x55903214540345440f42c1d1001511070b10004e280d800906881e140c0320078001400308090003402010310580c000e10829010300c0e401c5944076405a142d10040d0040d2203080341c506e00690f9901740000d02d9110f4641d80c0c80d21615900b08903802940314105811001580c10000006800e13820392200d0118001c01c441d1085802007941c107499045081c00f0000002211801443c0004241150981046242141001d15410040205101c3c040c0400c0102c01c0180ea0303400e4035000a03025080f602082c9980c403542c8007580c801641036009400c20301c55001c14850f91007a000d20080300d0b413046000c1e001d99034260400c000b10a080800c06000000340358204000c0055401d21406407a44462084600007045510b10080081c03030080d00f02003443c10f010354412100c45075815000341c070070f5402a181c810615220f640807665281d0100e140280587c1000c5c100b04445405140030003a694040e0400340311b0210307940c04240c107141c0e085440c2c1038005d903100c201000c3c030b690001a00190f484140014965410aa101c92070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 386779397 1250 386778147 386778149
    0x11b08030f040812090f0106083c0d0c0b0a0504020a03080901020705040213151e051b030d0603060c1b060b0d020607030804020310020a120504031421011a0301 70
    0x7010081004501084004021580341d402540c0c114449400e11800840d02e6078206800c0000e15800c00b00003180019010548030b06078a039084a03403010070100d5904000000c404030305100c03e50f00e41e1040101d40c1800307118070042d00800e03956840310081c19140c0050580e801400740c00100c1d241c201004010f03150111148252900212000d0302d9800100c0100c0c07a01c021a0007840d009400402c032001520040441c080c1540c0d0118030036954454020b40481c2c18141c058011404004c00902c2c00d01d04900034002400281c9401042e80303502c00c02c00080c04d00c0e65228038007900e03e072943d40d00c04006020891140c1c0c010b0030705901e4040f013340c01464200304100408640a410140d5170300c0040c489585000d0016955540030b0300064451846003005400002d0488003070380223014100803030303500d044203100311100510b051300c4a80c43d449480403850300901000707004a040c800c44404071014180104054003040b0702ca030480c8181c90f0b1407148070044030705043e4005011102c40114942c034603104d80c000d0728 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 386780647 1250 386779397 386779411
    0x20316080d0c0e1c05071d240603130303090803072c010f120204050a0b0c0c040504030c060903020a0602030903090f0604060207060f0309150603030809062707090e0102030105011b0803 81
    0x4004114146031303040c040d45610025000c1542407801a070a400c8042d101e00c11100917008c0e1012040c071a142c00d041b100001d642990003601040003844c01440818141041400391500042140c056541d680c15a031080c1e0309800419003003129406240d15401000c0400c41c48501ea2400415000e400602020040b800241c203219030380011040810b2a1340c188c40050600800300d81056139160010202980031f1200c10410b805001c1c803030740341c034201401024080d5600d075a0f03500c007020541e108c980040030b1a100071000c5001c1c10004001203846400914028210000510781d50b21241d0300f00220400700c103596500078402444200202e58010460004503642030516000c01d0704e01c403000b14000c0101c072500400d01c4d40041c800c020521110b90002065a11a031210312a90711012441a13a03541c08440b028004410354100c50b41084030700d0f00c001280c480002c120b894040e00d4803948000d5070b07544801c1e6225a940800104215a48522400281c99140c1c0700140d05042d01d444094261200038400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 386781897 1250 386780647 386780689
    0x3090f0a0221010b0406060f020d02060709090506010e130f0c0e090103080306150f0d0f0b090403120f0e010e0d0f05040e070903050a0606091b050301090c020316080d0c0e 75
    0x341c4074203412611404c50014000c100710307900c80760302920041c88820982c00522030440b9920764035000180582c0180c446031141c240d01072070079110a01400d80244154100f00003011610101c0e101c1c0040140124446040854250b0a00310114200c403046900d80b801c000302d40444401d5034550b004e200c3d0641340c104550a80c5c0382d0798000880d4081d00c207a02031407990b6000041c004005603003080030346803929006100b030051000355042130040c3d42414801c0f940c0514540e0200f00040e005d005551120f01d042940800c00d20b14840d807010844110034401c1c0c00c20b0351201007484054505015a083e240502d00300940408042c00c030090990045010361400500300b4000305103054003a80840005561090454413a2902c030b243c42c1024001c41c0c030800b03003601d007080040c155410f170301c030400b04046449980d904e007103038a0441054060110380300c2840a6000401c8280c1c414681e5004214150b4010769981e540c46074900c0b41ca40864091821541c200b000010144046079650041c1d40107160848591f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 386783147 1250 386781897 386781949
    0xb03030f0715060305030a02030d05010e010302060909090c042c0f030a03050601170103060e06010b2d070602130614160f0309150e0307050f01020712050a0501020301060503090f0a02 80
    0x1079500501c03da40000d82107110100d40c1c00704142c0d0000081401c0c51400c0c6040c003090b41c0e0341c4000315066200313001c001e61020302030014021505141c0310140d0b0102082045403040b1405201180c03c840d2011080091806d40c40004120034460b0010001e12201c044024410f01c220204400d80328040d140f1400101130311180810007580c0300708022402c41078216a01241c03540e4074a420030082c8241403100d100c5000e14000007900d540f42c642942c01d080f00c605480d481500150702210b1110b040c004520920000074072801002c61442d10107070420405111402c584103040c40340180440c03254036001003c80390f0801c04924404c0c0190800c1841d10341c0080300050412082c40c040d100d40e00640c000541e1400c6584400100d41d81c0250301641c1101e00390706a0b0191a04e5030180b1003000700440384140036a1190004000c610041c800b9541c6070380c00749003640d581c50550f6540900760f0340280d00031340c00034a0100034012441030a010251000b40b081009100011407070b80400d5105a28480031007800055080c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 386784397 1250 386783147 386783183
    0x60d060e01050c3c160f03030902191409071707090f080111042d08071403010e060402100c0614040303140c0304080a2609010b03030f07 60
    0x60041111440244401c0c680b89518007455000304c0c4a80c40c0c150105008481d2010000f02c18528415040f440326410000714401070015078000e03040415004040320401c00030a103030904084c40d20744a541c0128165050b1300411612180303500010180301e00c5076004014a201089035030219040a031009001e03583e41d00d5082d2000c50034505110342c41003003d4208100c42e03a0204880c000c0e076649000c10350743d40e9103803c0c80c10700321500c030f00201c0e0b4540d1007048184208407c445c142c4081c26618076024045a0801a001c1d02c2042154030441e1140d08c8404240a01c003000c07a07032280300741d1040c0e0007046082180c0a20039030b02c280140019024401c050031a401c0742e80309007140001c0503009003061002117544030320b130340a803982114140d0000e031500b250182414855006240285400c0f400741d411916251541d52842e030111965000340200d50144403c112203c40c0c06080040c601111a00e86203401f064003400d43c0c0001030650b2098000700810300365103401109a0712607e820004041101010b15 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 386785647 1250 386784397 386784401
    0xa032d0b0f04050a050402041b230708070302010b030c0d050c0d031206060e1005030f2e290f07060203090312091605030703020108010b0310090c0c0c1a03060d06 71
    0xd88116003080c2028104030051415400c410300442c800d84040084042d16030a102400c2000c5009d000000d6149911900546103080c5da080c02c0701c020305050349030000f00e80da80c2a155209803421805030751118600221817400784121144000262140b844641c4656a07543d21036081020b01c0344905071140404040c9072040e0301c5480801d043c06420841d20340c80740c0c0050100f80c44d07842c40910600c0e031102c4078910640310384280d0380240d0300c03102071800302e40b103d041000d06001c4904811202004116500407198038288480f00140394140c0c10102450700b080d44494404a4114160045002041540081c410b01c008540400342c01440040e00c82d111130042c1c0f03080d03110318000c1c074060803100c1080c410b000d4404680400544504071900000d26034440905840d000d99200203408103514000400c8001d0740340000715440510103404400c0c543d1a100d03008211080003680f50001101c0c0f01b0003004000814441070050415001c074044001c0502c1200c4a07a480300800d003c0c001c0364040c195108001980d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 386786897 1250 386785647 386785669
    0xb1509070c03120902330c030901080a02071b0806280b010e090109020a09080d02031911150709140306011205150c0d0b010804170901020c030703080a032d0b 69
    0x404044500302e28401940f03805a00403000511b60046620043c041788810088880c008542d9000e1800c013442a00150359440f80208004240c81d02005800c0c0029200110400d000d00a9841c045842d0705000041e807038004d008020300040c4000071000f15071582c040040c2c4016940080c0301003401140000101e9038950840d0710543c22101c80c030008620403481d83c010b481030320103580d00d028180c0d940c1d80c100ea554222007031034900980c00c02c0103804a484030402e1480001d4544d42400c4800041080341c00c0e02c1c0000c91004900ca140041c424064500d6001704610001c180090040701340540344000203850752018402c0c00b100e003425100c0c2c542049418080d40030b40700702407003021080f4506055441d01580c013189072802c04034a42036030705441c4d6000302038490007150040385050309680100500e0800b5804400c00c2c030305501c940c29010010b40d50400c8101c0243d807007082030507111084c503000a02960701c8070408400889006200c0c0c00c000544c600394291f00e490515000c1040c020b40c90216a80b0550 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 386788147 1250 386786897 386786899
    0x170603061b0c0109050f0d17040204090609020904050d14040302090c030709150507020406050108010b070b0a0e0106080c030d0327032c010e2b020f0603040b1509070c03120902 77
    0x904ca20b00b03040c0301c0042807400d240e4460b1000c1d01c0d0951903001007224061441110030482080500204001d424140d0103005070900c10000090030140640014120200449080340e00303901c6a003a801619074003041c0901c0c0012800345c95030070642150300041c4031703043c000c2508410b1140800040c03242403195200d0401880074080300754561841041c02042540107100a0307001320304110002545e54411940303541226064070410f410050380d95181c1c110300c10060480c0e0300342c80d110f1001c0416031a0a20418000707107460802001803200181c149810250a003101c41c00b81450400091111001800041701000a03454030100130802ca00d810343e021100103440459804070001803401c01001d105044a181c0b00907202c05449000b50001c01583c800890801c08411030399103220340c541d943c24200c2242a62000700380e02284090796003c00e2680d081241d003030315503c2e0071005000e00c1d0340112070b00035a010301c142c030700c5141864850805001c001480c1c40040030840f0380391500040d0501ca60040d407a076a8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 386789397 1250 386788147 386788151
    0x5030a032304031406010b03042003120c03130e060a1206090f11040e07180e0f01050a09120207050303250c03050d020106090218091b04090507170603061b0c01 70
    0x80c0f2400e040030200c0e100d90082003a84102c10000c01c040c0c500d07200303481c803030b40e0712240c2c50103012001107550002c0b80d003011400390903126403c510300740321480001503d9405c000700015510b403103484106903818403556200a89200030101407000a49030f20111500342c80718032080858036030041c90484020481110080c000d0031142d0041d03020408009203000180c8822201070060325241280b03140c556800e88203a40c2d84902c62201034032001090b0b0401c0b08000e02120985d04d40300c548a1800d0300b07403441140c0d41c2806640da040c061040028440034054010b5040c40108007850400000c240d4a00c28100505414180000a146841050074101220304d40c084000d0740410b6903845e01036a80e20413942c181006d5402c0c090302207000c041a10944600c80300c2d40058142c03218502040c40194a006811441202c505040354145e034103c4d1401000202080140001c0f1807810765001448100301640c06900e48800c40240304150360b001854503004000f83e121034004180005001c0544c2c46840722004241d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 386790647 1250 386789397 386789399
    0x307081c0608060a0c020f1b03071d01060f0504060503010e0411040c02060610031a040c09170709150501120507021f060509130f060c020a210e0a05030a032304 70
    0x390002c0398070703405030513003103014032403030300044d8041c2d84605801d030f5441e803141d00020f14110390a0600b409060003400280a6034021a1501e0050544032080c090340d2040b5407c0d4001040810b501000359a1a000185021801d0a041c142d0013442c0e40f2040c401d811741230230504003060601161801e150001d0000500400c98440c83c3c0802035160042101c030f083c4100b281208404000d80a402000340814040c48084c20304010002080b004080302c00c84001000220035011800c406911183c00140e0710440c0141892440c1094080a42e001036920f03000d1820303290010060f990700003001940348800840e0118a65940700381c120700d0507048074000ca003064640c81d59500e00254a500c200c1c1070740d500350751301d600710b66480001400c1c0303d044000082c0340215000c14900400e06651064000304110301c1900c004c012070752520f642c5400031a2020900c5050b42c201c03540c00c4d43d00400307d0441d440c0b058488000040c40e000003e500c0d0808400040c09101a00c403416250342200842c000510101e2030b201ca842c0d07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 386791897 1250 386790647 386790659
    0x30103060510050a0513051005090c040e010b090d030302070501090803071107140102031902011407110c040603080412030302041e080708030c0304050103320702010c030204080307081c06 82
    0x3820055628810b184240407022541d0b040a24001050740d02c081e00307071101141c1c0320f03200d40020240249180c610b5444c007d03021030aa40d80c0c00d1084d002e6680c05100c241c6031800c01202464002042e07205804a6004000c56411515400685000c0c983c1509005842e0300b0207003401405043c3c00c040040110b0000000c202c44960080400480d0b20301400444a60549640710588031615915826000d81c0c000c3c0000811060f182c0710008040307440380300106400c20007021045001c801600c40b00046810b02900014000e4204070361490350100310707014040c05103141c6420310240325500a160001c0f141c000d0003002e0500030f404940050500004400780b07941701d031100c000040a80e01601d4118040c600d0000b500110000640f10030429400c051450507260000660042c0103248260300004072803612000b00c03019150304109079040c1082c0017806132821040003401c40d070b080f41c1c982060503c140400d000700308000095a50309944054141d07541d11001740450309040f03450f55410109400d0003004100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 386793147 1250 386791897 386791901
    0x4530f0a050f12041403090307121b27090503090d08160602122d150a0902090f03070f05040b0d0f030c020306010602030f03010312021f0b030c040905340f0e0109020f1c020f03010306 80
    0xc03c403030311080c1203c84030b23300300010755940100141c11070f03100384141000e030702e040c000a00010f84150360a0f86400e200b101c0d0b60a40311001c020541303c0d40d0340800d02c000e4030840e4291240d0700040b0820000005c0c00b60b01c00069400018410001039049a01c00290040c40b0380c0d000d4a00800c4001e01c0c00d0035a60799814000041d600241c85d45010304010703200c02905041c00170322401596103408050303045c41d0801042c070005001a40da07140d0301112607a50704c40030a0402182c01c1c0b40900075a10080072203150300505241000c180c0c095801c542c1b040054565554216040d42e042d030740c0c05844802d401a0f00304e030480c64181440c541031a0b81c68840c60303071a0450156400145207000c19030a44041c10544010041201c154042c00340c01a0030103c0e80518840401d41400054a800c8621f90598034001d0903500d908491900090980c000e112010700c4541c40c50708082d80101440c0200354a030441c032044264881c0035544100c00316041c1b182200c2411408c5070151840407400744440c0d52070350394078205040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 386794397 1250 386793147 386793179
    0x10b2a061602010b0d051027110d300e0d060222080a150c050910020703080d020405030c040513020904530f0a050f12041403090307121b 60
    0x186514085200c8040f034100b820110705140d000700c14419007103498403071a0240c4900302d0130b2a030206202c2000000100d01030f806104280c00c112f546081c501d01d4038440303a402507011100d50305102c3e80302d04048840c0c6c1c4003e64042969031004026864901d10150a50030b401e80c001e203026520904000800c03501c0e400244080d03841e01504c03411420014501926040310480340d807038400a07008000385007442c00c000f040c01c0d0741500b0b50710448000c3c643d40c1d01d80d0740303054000d001d007103003065000a810440c0d4a030030001d103203a804040301c04020a09058801d031513080d41d0030034000e01035462400010f09001a6500085a0090788079107501c1040d900c0c02e078040344514900800d090a007421040120102c4180101c502c1d0030b11168001e850801a1942c1d40c229070001c000c00300c100300c001c2000207241200500984640d45103464080c91038241890000c1d1468184042051039501c240014103440e5400201d240c220b9001400039840d0340140c1c00d1001c100c8031b01c440302d46d00710b51124070009900203061009035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 386795647 1250 386794397 386794423
    0xd060e010e040b010f030b010501050f12090115050301061d040812040819050703021513060e0102030126070509061309200a03030509150909010b2a061602010b0d05 72
    0x540e81e00c1740d045041042c01e42c00042c1c81c0c01c0f050001400709500900080040e6001d1414003420710000c850b4404406d44100e030514016512800c2482a1041101c80031020f07000c218024040b43d81001505034102810b0b0a140700211002c00200701441040390860311100d00b41041888030b45050305008640d64803200b01c0b41b2000b808a0300c01d1801921400550341c0c42941035019010340d0003096540c0702000c0c03000d001c116074034111030308840006034944500011400c2040015803203624040341035080400c2d12450344da01d82d8042c0c0104040c024082000020346804403a418030b5602e60801040c560074503a400191420303d03121102040c02a10b6150ba9888080f05100355503401c0e5060034400c520000748070007001b194050080c00100e01d0540c0d40d154140c0c40c02174415041c44803c1000492240e000e03030010040c500000f1b0b00003000146114040103010300b00c1920000c400700c014a048d51004001c0c910f0010700101411034079800d04c00e400c80d0008840003080054100c84a00f411901da40d4083d0400c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 386796897 1250 386795647 386795663
    0x60801030b0f040201050304060b0f031f05010602010209010210020a17011733040f020a0b1b030f0307030b040605100504140d030c120c0501111908040c0501050d060e010e04 76
    0x1004005442402c42c4119410307540c0700d0a5498540e5048080c211003081c00b80d100040107880803080c0c50400050540302c0550501941c0707210300300c004030b08561042e0848001c590040140c504243d03000110f41032046031442d40181e03517440007403080302c0342e190103001d10801d07052100001410156940c0c41241c40e04c1810f003038980328058125084050304960031070f0001076680c2c0e5011401a00600c03006603115008414800b000c54086c1e0001b40800d109400810315200302188070149411048259001d0907038810007186003000102038400705001c01840d9004042e110300c0e4407540f41c0c031180c201100420000c2c1c03a5540069132243c000c0c140350054000c0200c3c648041c08000090300d4103c00090050350140c0b262050b1100d0b83d203d580029800078400c0060094104903c00043d10920521600c0340c920361541c1c0e00c0c0e181d1903206004503801c020010702040116810700010503a01c1c00314804a030707001d0900d0b6036980c40c25031079030340501510b91200881c100c002c000001d80541c01480036208620800e8a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 386798147 1250 386796897 386796901
    0x30509031902010818012003040c0b070201050708030604020706060311190e04120c08131505070c140a0504020c07060905031902040209120a0f02090a0b01050304260301060801030b 79
    0x5518280007041d019002a4019011a4000b11200110701c01205a880045140e2010358084182c1000440d200078055400100f0807052052001001000e0000780145501e803140540000309240101503000e09100d000002040d20b0703030340d40e07070448840d182e000d4003e000307103644c80c00d0000c00301e5401d0100c47d000e200c405c0d19261807041510326840075924000241c91072a00c0716182d003180c0e1110300702001d050004004090000c25506800340c11171940c440500c9070140d080070a00542c80c01400d4224092042c2031002d88005814880c042040d61120941c0c3c84107a00800001079642c110303540401c1e0400d00c0000c0e40100600d02080d0107055490035260180550f60320003e0641d075181c94000d10b548045020203a13001460aa0014810180e0040071080b010380030318421030900184101c01c4501e980c1c0c40081e0f00850502d00d400e82e620010030711080180e4090200080d0881c400200014074041281d03070003201c1c0304101d40b1003210080070b00d00c10a881750f071120300181c0320020a00041d22141c4500c80 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 386799397 1250 386798147 386798173
    0xa060e09070810020c12180a06142d0a0503150d020102070306020306040b060d0b040b0a06090b03060604030803072a081614060901091a091f0e030703050903 69
    0x141d600e0403a800140203004030940d60346a41c00035082a2a032013404c2c02240c0c80b10b042c0c040000301500103421100c3c113085820400030200051071420b580709005204144c1046d0414090300010785c0c46d143c5a4540e0141200c42d442441c07540ca00e00e520182440f440302140d6180510360041c040c51003501c0f0b00b480d00e00640b01c050f04000d4891400781c0024010380c0b01c42400c0c0000307502600650b41000e009480402e00400e5880054001e810080e440f075001da54031050540306242a0040f062112401c0d1054200b84d400c0050017000480d9600410b00110400070100c0c545480c0c3d6821580115045007a040d2681010200284200e001000018212000020440340800c210812500780c50380700190910f0112400c416510b003070b100030010307904030200d503c000124907014080e0031b215101d50000040d134a1180c1c500f078101d200d6044030301010b007040d100401880100c0050004140c48101541c41821840701030324070301400c41208003441602002c9810303010503030800050400f485044041c1e8201e02c0700c0c08 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 386800647 1250 386799397 386799403
    0x60c03070b090c0306010b0f190f031404080301060507080c060a0b010f210f0b04050705090109080c09040f0503130f06030e010b0109170102070503120406052401050a170a060e09 78
    0x540c1d02d40c19000170004003c6611036074010074444940c4e842890a003040318086202c2c440038080c0b07040c0419001ca84400302280e0507c05c10b0a501c0c0c0d0034408182508041d00c5040b140e01050041109000c000035100302801018000e4500e62a407182c101c5689280c0400d13410041c0c4070849603180802c0480000303074100c600428a01c004803220b00c094021441c0d90b2a040310203002401920141b20b41c0c2d45000032100d0f1628001c4c1e910402c0203456059858069800041440c04264403074602a003204d5100030701640c1e03507410a82c0007500059400e1451501381002e41c103504c240d548442001c040c50790009903003400d00150074112216900e007008041a600d00440c203882c4441c0026001402200303040c0300c0c0d19103a25208900c205110001410b041081e070710350785164440d841503030640e4a81c1e003c01081209034014103038828415214490f0014003500c88400384c80e01c8501c0c0f581400360115410143c984500d0300140402103000215810742800034072031000300550f0150008003900400022150306c000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 386801897 1250 386800647 386800663
    0x100605010203070b040605070e03011b0905010507020f060a09080a030c03020c04060e1803131806050f010207030f111302070606090b0303071709222306100e060c03070b09 75
    0x40441c0c2c131080e0b07a441d92017030300410004002c0760500c849012200d40d1b40d2024450961698440b00a054180d0005074002d002c500745e5500c01c03030400c14100f11800060700d03000341602540380c0683e0100d490700c40e225800d407440046234000c44524419046070344189948202d03064100c0b4020340035108144040f07001d1000391001c5004070a510020a808034142d01d500701d04d4801180c1d21582540c2c1020100c411744010321080b0740c0840c500c07401409845c0212440c0b4400e001c01800d088648044c0d9206040020303440700e10301c1c84003070500c0101a02090500100102c604004030004000130b07107640c5c0d1918040000d400c80341090f00c090340742072030110301803c851180960460000f4015828507000740d036841c2a20706050555100238809002d1f00c0d0558499605110004ca194450000d881140000542c21110354001c1c0c1e068104c2e41d9000d041e20700034120030850700a041034841541c0c0401c0c144c0c0c00d0312100d4002c164580c00c0700b8009034540110b50084054003174103110700c0b02128691100c03003205a8600d40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 386803147 1250 386801897 386801903
    0x1b0608040b01030b1e0a06051f020705011103040f0603090605090a0201050301050f0414040c1d06060406030e0a0b0411030d05031e0423070f09090c0b03091002070510060501020307 79
    0x14440180301091303034200d0695219550070928814240b40c80e080901281c01a250010b000c1e031101000c3c0850b140c005860503414000301c51810b900c04000000a6840c0100d100319814400c012040c0d100418042c821140508000c0c003039440307200e548640c024000c0c504001c2c15a5218079101c042091460042002c8130b0b0790360141c0d111801c2d0390a050820603000001c1803d0baa01c41e0703407100003005c018501d03c0300d40c1c443d03409419030304020782c40c18150702000014412800702c0244031400b0408199100026a400c2c0c0314149400904c000c410800e05107048903421020f00a840d840f4100005c00c4407409252944180c00d40c165503015403104004c0d2018003050317440d04d8130341140c96040241d160002901990090080c41d000b05a209842c1c01c410f1010300a040c001143c1d0010b41c8140100d2140380640030092201c40070030052525a81c8480b40c801c0840d0007504622140000401c55511041015041c04460940b0443da18522850550354480b0701207451360b0300d2800c290300081d04e9800801a102145e030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 386804397 1250 386803147 386803163
    0x81e07020f040209060c011104030203120a09030b0c0c0313030606090903020c1203070b0a09120c050d120e070f03170304020a091107120206101415031306091b060804 73
    0x140c0c01c0420029421114015401400c24000300350010070034050502030101c400301d1280c1c4c40703003580140341c00c24208600402140d50300b005500c6d0250342c896803031404c40380c00200d0600d1541301c00f1350305481d03481109101a40c5101c0401c5030380a01c0c0110503031404892080e00c5c20000c1d6a5103a406005490b0001c90180c0507030440114104203041001e6410034803541c140c103807480c001c260b6035192351246098030b006a05d00d0380c810480742000191a0400ba80c8115424481d000c5d80c0140d40d41d0b031b501c041100d07052080105440c0c14912005154102e589402da58005a40105031207001100c0080b02511041d2003402d00d20035016624803800c0204da02a58000c0c1140c48040d01f000400d01c080c02c0840c0c81641d0192040061f071000c03c080d03001d402d80814030b0358083c2000d801d01c250800036900880d0864034000015178410360540c0da41c004c1e40380c80d0446500059459980c1c9964100d1081c000c844098140b9081c03084800800030303641d0381c034150300d0742400c050343d4600e8985100310380c0d550040354001c0c2809 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 386805647 1250 386804397 386804419
    0x6090b0a06031a0607050f15070e030a0c1203171315060b0901180b0304080d20250209010b03070f0f0504090e0a02150406030b010c120c02030316081e0702 68
    0x30a0460081000354080c400312402c00c180c1e00002c91900902d810703d0210223816800b4451119480381e142010031108800412500e011f64072841c9010000b0310400d005200b00f680b1410425000354900006030114600c0b601651034801c401201e030340682c0da0704440d842414051220520107a1090000782d03000040700d50300301f40700c030001524010b01c1c4a00941d2821a00700e00000d00152800045100da8410b03074900c5c0d22440c0b01801907050b101c200a501ca45c1c94110031450601c0d02d04901501e101c1459040003100480d030309902d021041d042168065040705140300041522641000194018241983d484010410107072048515824400007200000d004110800922031590062180384004009840c950409a400948450428035100f142c826001c101003000707035090310900900700304c2824a50080c03006503a803c44101c030b03a801d0500a2040c1c100c03040045d500c0800035a81c042d0f20011500104441c03c0c10081900c0d00600340c81801c042d91041c2071380328400c005050310300c1c0650240c18500f041c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 386806897 1250 386805647 386805649
    0x301030c05150403120e1206130201270801020307021c0c0b040c09020a021e0304050d02100c050607090305070f0b0703030b01140f07050706140d0509010f06090b0a06031a 75
    0x307a001a00300703220b9071609200102c0444e010411200b48101070ba2074140041848500f0700880604521500314a6013040c01001409030b60300f01450100c0c0e5091070155000400e092644600503004030304a48003031020600822003850550045010b00340da86c0032180a10b18140411003e5095100d00c03400288485020b1000100040841a0020b03c0b58000145260721401410126042015000010303030140d0150b03100b0000c81c0320b0031030100800300c01440c607080c04c041c0230500540000600034050317030320004501e1503244030750f40703c0842990000c191807090070603610091220b480340c0020703940c0d4003400800003007082c80720078110110744040b0141c03414400c076910103a008007100590035051240e00307995000c17070009640c000c0c56042150b03845641c607088a070811915102c5076401a0090048040e811001805810b0030396055007600203012803d5a905134109000d0000340c205183c4290030b1800201d142450380c1c100c111178500a82c0d00b02d81c0700b95100b204030706803905180c4c0714001e030724031031f0000c009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 386808147 1250 386806897 386806909
    0x50403091206090215070b0702010203060303040302120102071704090b03030a0c15090227010b0702060712050706020d02030a0c03050c190e060c0c030706050403050d0c060e010507080603120301030c05 88
    0x8042c0101c80c0082e0f0f80300c444d00840e54131028a40419442140003407408100005500d459401424601c02141180340210209569100d1400041c0c802c01e6405a10310b1007040c25012900e0165200c448603601c10034030a400040340e00325000740c415003402c1246420082c14001305890f82c0e1041a503402c91003911a1b180c5107458912030600c0a80a521500c9550160b100d03816491351482c4120705810030050862800c000164068100601c000c070104503940c0540da40c1000e0352603241e040440060703201d4002c402503c452041c1f4070004c110328004501c40b629410340d0380c060741c031402c6034086c1071161505440046045030004c6650101c03c000c140400c018540814840e041408050b044c09440503030620001402a0414550801036a0040110642600301807007003800074241800d0413410039041d0b03a10369032a2004a03004030200041c9072030041c14049607403c48121842c04900800440c00c3c41c50000b856144203d0f800c500030301c40c21848000745091042120f04030381e040300300c2c2d58002c1c0c104020484 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 386809397 1250 386808147 386808179
    0x1502070b01140d320106030503042705150a050906090109020d0902040f06150906120f0612140d090e0a0203090c03100516090303120f0e0706020714030105040309 71
    0xa0841000703c60388000501280c08015003111460681040014007460102051665603882c1d1084e410701c04d042000079030001c26074040e108071b0701c4040340210000e010f40f01d180820b040e866000070308040c2442040c03040310300c180d18280310644d030a205072130b100c10a0121115003591a50b4000000f00c0041080e491503901078400e241403c2c01c00728010400e40c0000e03050300c1701d42030318031185a50340e03608010303010200030405449030090800040f076528141c2c0150801c0203081c0a240700304c0d11100d4a03c2d6004e207940c0700e58060000d0100028001e40103080413107546100b840303150030510440748400c1180703008441c110210b0311800c140071907664681c041500030303420280a80f01188240c09a01e8203a6405004052410028010020f5149003507903100f2464034403455024180015160280003003540265040d16184011401080f494036182204009142c1e8240c011264060000003103061036010403000b04840d500c0151100007540e080404d401c8500541d00140420840b1108100c0100e030080008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 386810647 1250 386809397 386809399
    0x501140f190f060314010506031f0c2f01060b0412060e2b122c07030b0c09010908070821070606030303060e0f09072105030a08041502070b0114 63
    0x2040190007401000199081d40d00704603017401c4004d800d4120b4030001d1140c41d0307200d1310490081040c14810152404684c80c4861000c603a40d0300e44040a1900b8018281844006080f04103620f5102c00c2ea071608190a2080303503d0609e6509014000a1100c60322040d1000e45071517410403a20300c240ca58584006201074038142c1c41c0c2e809400d580054101c40380324400840100c405142c2c19040802c00000d2000010041d01d00c0b5417484c24026640d104014a0349684481040745022007903100c8286540c900510350344002d1000c65101c040025011000d0003030092080700380c1302c071010355440d003284079140c1e1414040c4000e15400360400b462945c403a04108900102d07907000492502e02951222030070703500190003e4004c640c54132020010356402e0104140c0c0840615480d1240e030801901d25038580380144102c01400c1c0c1c2020050180f50341d132a42c02c80e64141c0c40000c80340e44004d441c0010388000c00c11101030755071000c810003c0b0455591030007145c6003140e122240032490781c02d100c1c2c0d10020110b890711003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 386811897 1250 386810647 386810651
    0x40c0806011b1a0a0606140a0503130807051204051e061e0714031206010e130209221a0603090613080c060423030c030f030a0213030c030501140f19 65
    0x40001584020341c03160191a407004080381c0c5e281008406015820301694000c2d40040130004501496404003e50303400c4443d0b481c003410a00e03668101802c0074022541c0203401360245100104000f81c90704000c0003203c130207a412601c103c142c20a11041c0413502c5507a903420003001c1011108420010203405032103400000c0d410300300340b00d41e1900628500481d200c0c180c154400280000101e101c4040719a10090900c1c005049a0605000c1210240007a201d20324280d00070540d40815980e01e10b003d0a42c580014100d0400800418180c0142c00d83c800e80504000d1903002c2d51105090400461344076214120007041d43e503d810841c10f0042c81101e0b801c3d5643d402c1400718042041e4144041c078000c1d401420b082c04026800c000c107191260603090321801d40e41c01080303403031101c60021050341c08009840c0000c0b0385036601e08403130101900c1485030080000b10404808020055a2160141641e0041000300301d100360740b611195401100780c2d500c0641100316400152071065880c44808004020100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 386813147 1250 386811897 386811923
    0x8090a0806090f011116020f011407050606040606030e0601030b090a0b0c0306121605090c0d18031407021c17030108070302150403030f050f0405031209040c0806011b 73
    0x114246481503969180b190442d040c0000d5401003400303040e10450540c100d0618000f1407003074610035a500c0150081c058a000a00c015403030b80120382103810b59a00052803582d588607071402c02d4588400301d81d0780744214984040410024420701c105071040611400428450f420760711110000100109401c10314130408542c10002200170b004180209861065140c803814000101700480840b59685089a07102480030540011800a21001c0b00d00540d032000250b1500181540d280c4076041070407045a041038640c80d420b1074590740080003030340607543d40c860754400703111103090354498298040d42c00108040c50920840650300310459072403041014100000b21145440c560b500240e02007061754001040800039030914100408803072a0148a807803038603003507903001761005050050080401c1008100552500c16120803100079000060840d44981009507055030142d214507119801641031040d09140f4034014003109010300c605840d440c7c48440b000001403402e429141060787d800050b858 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 386814397 1250 386813147 386813159
    0xb0f0c01150b2b14040201110607140a030f091109010b0f07141e0d02160b0f0319060f06030b030607020a110607020a0e0109060f060f030213080624120a08090a 70
    0x101c1c41521094003134200f2114070385400050f02c4644107891240880d0003000030403102c1507202c2d50340f028440b40386512a444c1c8250100c11002401e04002d002034040c501442081803010100001d500014100c81c04803244c0c2e21001d0300700d401e0041261042050038240140d0307000607080116902141140c0c8116150400442aa0003040c200080031300b00390b40003581c5010505606004000e420344550281c10308043c030704064415248600240305400400101c0070482800000310070300356002e90207005108498a5182c1030088600b10700c18400440d1410100c5c945070709011403090312541464000d02252402a12440d80c01d510220405500400030040000184e840810050191030740030031086481d03040810800486084d03400c4045100001d580400850b64400c0e0044180d00d0240380258a80312345007420030300c100e210740080030140100360800900d2032586c1b8483c2c80c00c1e03001c0c41d01030428540c040301703002c2c42d465100042207184c1c00840e818000f04104900030319000b81d000c1c128920f111b90b141 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 386815647 1250 386814397 386814401
    0xd09060902061305090c07020913050708030c01020301060810080c010c11060d0605041503170703030609020a050c0709020a02031b0703051c0206090c2101060b0f0c01150b2b 76
    0x1030790850300780c03103543d081c006410b101245c02d0b4040c03410800305140074416000600301040c0200111511305040110404200c4188500c02c010101001120746481410300c035140030350030900540000440220001380144d00c0940d486048a134400d010380800700ca8000111482c03a8068420394612400c5580c222242d00c462004040e081c00228000070408d040404110a803803a800300030300035440903030b42440411130350000014004402c02806680d08035603e000d0340504410b030b0043c000a4404a000035031b082e000401003008050381010b881006840f6402c803001c901a204180c00168010b000f016020340b120503211845000103412078440d10750700d59030340b881c0c401002c00d071204c2c200140300c06080054041013a66046400d6030007403d50040c007480840d00b800400415845201c0103064681c00c0c00001703500000c040c00c02c00d21b4165448490692541d816400b142c040e001640c03900301034008002a91146105640071289501e141042210341c0d6021504040d0a4100d0054100301882c0895514 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 386816897 1250 386815647 386815657
    0x1902062203080c1609052203020f0106090b0906040c091815060512010914060f040906090320011e0b120607030914030307080a0f0b060c21040602030d0906090206 71
    0x25a00a02e11560440c0305079130741200580c00030580030b082001b0b10564090602080501080700c01e4840940312090034102c0c90002c5002a0b400c9035442e1071408203c81d00c50340c10600c000d80f401e48480c3c0c51521607805010459690116400c000780600b0000d00011503034510540c400014010301013056420f00c90310388000c40c0c1c258031103000b240000520802c8a03a00541860043c00c8042c0c080041005510302070742000401441c00c0e1051a0004448043d641d9560003c8241900140c042001c11305500e0080c024899010700c452241c0f80b08150011201301c140030f4090210002994400e02c41c0030070042d18083c1130909070035907000300c008c0c4100310040f2042084502c9181e981e030303000c00c3d00121130400003003d023120079603494070344c00130010070210903006a4a42d401680c20304c00084c001c00700441c844010714000100395401080090103035039100c1c000490310b00c007008800c4520315440e002c1140d5480b078400c0d4450b020141e00140800d00316001150300c0560301501540e0041400782c01ca0340041da050b400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 386818147 1250 386816897 386816917
    0x708071b150e01050c0403050307121103070f02010305090309031207022d01121a010e0406080304030f14010501120b07050415020114090105010b090f1c050d02190206220308 76
    0x502c44103101c6a650034080d86401c82500c549191900d810743d241c041d00d80c45901809000d261140d016100104c0c450b900c3c52504c01c46d07a6041c0d03600d0700180d25180c5603424007160140d0000e820440070070401c078030100840300b041000900400340c2100d41e0b45d0598590304004000c0e80e010788118410a0380c41010203002103c400480b0020340955460000507007440d101500e202900b62501d1002c84070018168151622454242083d44807002c100c030010380504040e8000c03001074000850300108008030a45a80d041e00d10864503110900351001c030702707400c80b90244518403c445038000648085508200746ca50030018034642207145c02c0d11803c8281a42081c03000540c0142e642d040c0034038802e22480d01c800d030440d002e00000e11039949070003403034120350040c5204a0300c2041d9854481600360340300c0407960000c0c160340001c440c10140c40d0030f180752260361101030000503001c0d59440305420190a40c03c0c0705040d90042140c4d05054036000b5003418044017544440302d004800c00c0220108503404007038414106 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 386819397 1250 386818147 386818151
    0x12190809030d0c0809100606051623100609270c030b0c03040b0a0506031e0705030a06090b07050301081902030a05100c02070501230a05041706010504140708071b15 72
    0x14040c017541d00c1d0a1600e54200c0c00759180440a10101d07a1000464590042e51541009141d01500b081a019141c5410810784003150b90b0b01c4015521001c2a00b600c4802c28903c00c12416540340301321030588100e40840303905180122f61138040080003643d01c0a945006020401c1015100d43c2d454000343e000399442c4034081004001c00c010407408202c040c1d805007900006001074104180442c0c2c8d6401d4152009444001c03255162094030020081c0c08000c0100508941e10f1030030b9400c0c07100040500c08410b48840584d44000b41005000301c007224102c80d22140101031060501518150090401504980c1800746442040105200b0015000011126000000c4410306040088d240a120b64403132818007416040381d1859558203602c140c0b0344005074462503980d04014000b1201841241c100071550100e241d20054807040006005040e1002603e0403c055000800d503503c2c070b144200c4210001900c0440001e480601c07985c0ca4074101886641d141034904020341e191701c4800310b18901d40c035460f5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 386820647 1250 386819397 386819401
    0x6060306020d0b031c1229010f0807090e060f09070e10030605060f0304110a0602010b0312040b07230d020105060f090601050304061503080403080c12190809030d0c08 73
    0x10b42d55100308100b214045000780980d4010801c40c4090071800e450500912100801116440036290402011000c2d42d10303a04c0003600302c4501c444a00c54812000034009440303c101c117058203000340c01c52401026107840d404052460b01d0400944950001c002c590445c00490641200380c441d0b01c0010700036135190715040c24052070001400180f108a02d110410142003000c02c000986800e82141c2c03001170010201640c0b5501c03810044034480d80c000001d600560a240d000910035419802303110908002c600ba50075441050500040c5070241e401b581508010400c10100000d60031000040d4a0a052213081c0c5041d801020041c01c1c01005404540903075190820445640742c1b0201560700908201d401003901c0c144003000070803500000780000c000540c3c800780d101c0d113940481b00e064011a80281d48645c0c494403031502c80c1c89600300f40d04c0002d2611900c1c98268808070b6a500323450890b0001c2000d0076000300c0c4101e040b1030142c0090020072984c041040708503104030807806042804511600c41d083c0758 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 386821897 1250 386820647 386820667
    0x90a0b012903220c030f0b070807030605010f0509010e04050112050609070e27070902041d0415020d1107060c090618090504150c0320070206040605030408070606030602 74
    0x18201d21654000d006000c200304040240441008241e40204000c100d18840c8286025000001d040d007010740b4210294428001b0040420102c80c4500419a113904035500d500c5401e0f01034031480d005140c089000c400101982c0c2c0d00c03030005803c0c00070301450000050420400814115202a0843c0f91a04140c4401c28184541004456040400b582c0140103140c03504000b4196050045c00700c00411440300b100980c05c9007002d1040c5c00e510514000d80701c1c0c03990340d582c840c002075000d4442c8181464404640040066001003220703c41c0d0b4000076807804845143c0441030095201d820450205907555810f03d00640f020700103001500e12a00d00000d20341c0b04001c01822898250b40038a0401c007040c040081c000110200010407a404001d01142c203848a141074000c2014428a480c9418503000c00034200310340c55001000c3d13120280c44d104605079402800b441c010301c03420304007a4103e5030030801001080d100b14021540240501c83d040c4c00c200f03240d51030301d06131059680180c0d00d494012a481e206 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 386823147 1250 386821897 386821949
    0xe0f0f061c020415180506130306110d0c030e0a080a020f010509150c0a09031104090204050f040c05010504030201090e0c04030210020106090b01090806153c1203030f090a0b01 77
    0x2001c132242041d0544a02d0003550b0040d4903054080c1c1402580c0200d940d0312300c1c0c080071745800007542d0b0080d001d00c22103400b008074002607013141d001b03034006a08000d90f05107238501030300c03e00404001e00005022045030946a1a03016417008154000f14403940314003142d026001c1c810340d401040e409000c0c10300c2c10b50f62042d00c10710710350142100c4a180420050680242e40005403902100c1d070003080b80c00e81d05003c10000b002002d682c2806504542842c0c108445002a0003a952141c0c5c03150048c107100b0307038940004692030b020341d01009000c981c41c4407061140c02520204c6c40c0e03100e80400305031403800f500e03a03000c942000500044180982c0d100d60090001c1403503800741c0240c0385000e280c491203603071800e4403040d95010043e103044240e150301c100300c07412500e5038118a20107040da801900540081e00002c24461b6800040620310081006d0055140f49014442a5000c104510040d403c50b1101000c5401c2910045e00d405124440d002d8410000344100714000e00903d06000d104c61242403620860038 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 386824397 1250 386823147 386823179
    0x1b060912061b040b070f08040e070c050628051b04080307200a030209190203100306050a0506060a140405100806011101290d02120604120e0f0f061c0204 67
    0x30700140601013404410303d41000e4440007a00301003060010406030070140c4051040740c0010600105e072204100316560404a401c1c080c40c0b0800c11191241d803417400c180301c041c1220806400f5031100e40841070040c4800c1d00179036000305c480400c030302c000841049448134a40c8140e000c9002078201040b81800d01c042e9000e0768007550b908140d00702210700300340001444e2900c1404002d10400b0700380702090f1030300e00309082825124504442150b480c01d000301d0100c2e100d0901d2008490843c14000051030030426409100d01031240540142e045c802c40080c140c402c240504c944000e4444c1c02d0000292a5036100110000c459040c0c5401180c1d0031305100050035044024036a801c9031f81003941c501c144103440403982c14011142e042000b24903507441e00190700e052144401039405100041c05100c169400306420f40140c0c8a110051201c1c98500820340350040103040f4954010903005147d501030401182e0440c000c04010503603803800542e55240400051000ca1034105294049800d128039514030000c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 386825647 1250 386824397 386824441
    0x4060315140d0b04110907090807050f060711030a0b040b07080c09030d1101180501020a080717070302030c0906130303080109060e0112110a030602070606050a03051b06091206 77
    0x10755415401c01007500041c10400080c984089440000c05000b45600c0ea06480703207006001c81c2141c100100300505002e0380f0702035800180514400016103140c42075001a520f0006014142404141d485800c00400301c040f500780c1502400000d800018465000180f045224203c4510709051480c03000345a450010910321250700f0401c00c50025036400103c8401c109100e03c0d1a04009845801182c050024200bc1c0e9180e205503802c01c6c01004010340107481c101f44141d46064459454038000c42d090305c0458000241d070103030140454800c0340319400450b8019000e510085c038012100010980560010842981003040b440080c01010760140e8030341d0052442c6801403001d1800c0180c00c81c00300c0703410702c20070001903140e5643d44100580c114140008400c0180b81403549681c0f401d202011794000c102c100c0d202480e05401140e103103800341110701030765001001001c0c21224208051a03c82e5050180e950022017481540b000d5590503d001641080300400b400090400307413911000071140710030758 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 386826897 1250 386825647 386825669
    0x3110604030804111507020f010e060a0809010c02070f06030504050c1c050f060601050909182a0a0e060105090d140304230102060403081008031306301109030304060315 74
    0x905e40f4400002c00d90300342940440d409080741d510040103031030490907031110707a03040340c008030307120b0a6540c100324054800c014120007842640c1e80844200d840e280d660144800d84240c0300c0d82480039603c40e40c0096805403140c402c0b501c02d210448001141c1e07402d5502c0d44181d08031404102010444148050354901c143d0800a2078a400c0c1100003030024042d80104600800d4050006007007140d40e126a0304484c804034094890308003054803500d9400c00e40000441d0344110003164404c1508110140301c5c00c840a02e5900c1c1800e469500044a0f0395002e901c88540c00031103044d4440104500242ca8601c10403080f00955403145070045c2c0c90024a090444d0002c441c03400c0c103010b11540d0300450280d031701c1070345072401d0603455076030301543c614101490f0442c241d140301c017041401c42035180044000a84549845002ea52426042c1c9c1031143c03103038400f84142c2c16490421010810a0303a070840c031449810100c405003020782c44408289580c110350301090000751100050116100c418811138080e1841d05e03d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 386828147 1250 386826897 386826919
    0x1c0e0406060e0f0a030f06020405010206090c010503041e0c0b03011404063503030a052205070b0904062304050609090c09102310031401120311060403080411 69
    0xc1c158240300900b403030040a0b80b000c540101e54400c05500055503205508070100c001c00e0030444003d41180c0230b0640944200c1c0007080c020480041c2c490f00088059444a2550b0380c0e80d56490f00f000708401e02c488074070003108881c40014010b040c2c02006000048101a100c0d89428190401c0008006243d4015868442c3c02e220300204030a2100640d0780c1c40340c2007051340c0000c1c660009916101004584680004000e00c00030340042d8000600406150350141015003016451504000320000000e1107540070081c00c101e0805044050802e614000380f000407101c0c2d84400c03113142243d102c0171008400c0c0801d62a0b103024a458803c880d003010080e5100790251903c0007603150b42c1c1945080d2107114040b5a00010380c1160340c1c1501c003000c0d0128101503540d4401e000081d81d8252402c0400354400c2d800c18a180310903074030910a111881c030301322030010f20316403a107040701080315602e134400c0d420000c18004190b030810040100f180503510903550b0120528013418030440710300e100c1381d800d8030070510a15 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 386829397 1250 386828147 386828159
    0x7170619082401060323040c0f0b120109020a0f0c0816050709050109091e060b0a060507120503060307050d05030d02040807080d090302101d091602060f01030308040b07111c0e0406 79
    0x611384100000d03a4400c903001f900c590806800340c50807940040c590209611000c0391062044c2c02811054151260782105a6200c00e030050aa004075410200010b246441c003c1c07040340b188000120712805000224074050300c498800c2480020901c0c15100340e48070003800c0200020600c2107038014a00800200041c03485a1f8138a200d00781e011441c40d05400b904903001080c481c45500c29002e408000f02a415a2659060b002d02a0741004805603516104406811102409402100e01c02c00b00240500020703802c1208000040060120070340c0d29100511080d520003c0510080001d000084010445103117000d02103490022130202203020010900c0b401c00040c1c5511904c00c02034109818500040348403502c02106075400d00a949a0120383d0303005005014803e1600c00c164a6081c0d420342d01e0f0b903524421080c155032020f200c01000140c602000502040030003182c3c0b608840c9a107444968a01b450610500e0020305040c00203541880f1900d00c1e216030717040319010001d040152400d00c52285412 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 386830647 1250 386829397 386829431
    0x2030604030807032c0d090807120305130e0415020a050d020d141005041d0a11060c01060308120a05061f050906041805071706190824010603 62
    0x26000078103004040340420403c2d4000e4001411a244c0038030941c14162503000040103030000c05162100034000c500441e2400c0e0711034105141664200070041c400d643c54101580c400aa0f40c0405804006050260964024810720140010194800000c07514203003401e11603072245911a000c8000340c0b04012a0480581240a0369500044020016284d42201c41040c000e04207a80c040c450380144401045441200e807510b4030140d580c165020098240c0f05842080351100305c030b110042e10341c0407080004c0002c00d051b204541180004d0445414040d800066174250f03200c58108030354696010031140030041507488615070101560a052006051040205050301c00303103000b20710400e005806840500340a034040702e40c3e02c10302418503540c030741d510100b00d4000205c2105050119003040c0104420521a0305d41031060007003a03122081503140d020070090348803d181032040113807500c1400080c5010041c403540c40070405403800000a0f25107041c07800e0000c2c02c141c1056007032510304240e81c40850303850 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 386831897 1250 386830647 386830651
    0x2090f16200109031806020a0b01050618031507020c04050f0708062107081c140c1507021506010801080706140d020f040306050703020403080d050a090b0a140c07020306 74
    0x39081c018400c000a070300303072900c190150108004640c2045a91420994022041d20f0180c201c100148000f54072043c2c22030721520250f4018001059200041c070061801e00000d001807040c071482804a0f0000c04d002c01e0030070220481280b0082d050804110b140c42d0117124200d140b0004840400c080d00e802a100014800040c06c030908000c3c0d0704000409640702c029159083d01c150f4603160b205920b81c20301d4a80d561169004032207560003845005880401003010b40019540070307450f044621110f544903403009030410601a00b05200300c03444492400c0028451341e0154005501601308102c000e00320402d0100080d052034100680d402c010406400040b6003802036440342c1c5031170b54500e100d59813078100078015101220081e41c400148010035422910062049900c90781e4180b061f076a550740c040e4228040c43c48003404041e030400210720310982990055034085400b0f03d00041400c3d550301c0e03014005204603040300c6c00d1565000800035590405c1c1100f03074000300d04040c0c03d25222150340070a45030980 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 386833147 1250 386831897 386831941
    0x3190605010f0302100f030e0105391608040f030c0504051806070e03070806090a050f03090603060d050f07092009100305250207060e03030903070e280902090f 70
    0x20121140201b03070300c290816000c0007080c000a01c41814805119003c80100d41520700900c0d064004d2620090301c09003d204410700c1e1034520900f800c3c44008040203020443e80304841420f0204004940c0d0200b400780c100180d40500307000c0071501c0c10030b42400100d910207040090004e2003400b80141a060001e0f815601000b14903007a6095041031011a1a226103500000c2150150308100800b5400000e5001c0e0501d009504440115903100d00b019240e100d1010110341040d010400100c07141085801142103602c520212040000c828034200c3c00c3c00f006030090281d40d502c0e03041c00d021020004a04198144a08602034904039165001440c2070181d40c0c2035006254441e40000c480c568465030103040d104440540301600001218025200c00042c015030303000c6004031110115505000081d16607400d805401400031505102c00d045520900429003441d600c070304142c0e00301ca01e811090303c000368605400003060a100302d104100c04008010424400c4800180c100905440380021580040e41 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 386834397 1250 386833147 386833157
    0xc0506060f0402073504140f011713110a050306010e13300807051e0c01110c01060b07020117040602040902070b04030e100c03030b060903190605010f030210 69
    0x441002107800f03400b0b40074015009001200611500e820420803110b24000c9903400074601950724050b10030b0b03c0c0a580030345d1000855100240c0e07118200b4910840c0040b6050420500b054455800742d5502103041f100420074101c909003600c10880c50300301c416030051003125a1307402181000e02103941c450051080e00429003035180414000742484105912058001046200840c07001c1d06c600000d64100b1440c2c5602d903521003402034098803401c250360180d2403a0b40d40c0e0389000b03020b44001100c0d2180740390010806004220f44074204400744544091007000108103610303030342841040c500711100c03540b00401c2d84400300545001030f0f81c81400d000303001000c1c052485a907215400c05100a000e00d400c107202051001442c101402081d400035841548a6070328803080390441c800303000e248100742d000d10001c5425640824002402074110400c03000018051a0420b890b00000a19140c41e012080e80302c11071904403041402414020346025040200210300118590380c04190b03900c94040e140b84c2001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 386835647 1250 386834397 386834419
    0x6091501050d090c030c0614030c040504020d0b040c0906030f110a0c0f020a090209030c040c0e1309290a0618020c011514010e010c020306041212020f030a0506010c050606 75
    0x1916034020343d40c080d0402c0b4156181c94036440c01c203083e140280034500110f0f10032111040512221000c0340d1145550a041904251609050102940208041c104581d4807915940d00f20341b103900c2240040100741d904c614880e440d100001e4122808280d80942403414005503030608003d1800b140c004a200d4074140500441c00c2c2443c00d07803008002030080d4010401d18001590620035006420300c0c88045090314100303010070b4208402c4851401c1500041440111401224039081181022003404080c000c0b0f02040c59641d0003105a95416800d0580207031000001c1443c40d110308444c1d03100e0850003040060509105201112012800402054540000d4000107800080d0403010a40000301c609140781501e8103400640c41108180c21800a1950141d01a907503110705024101150017078051728840d2a83d413645d02010760100d001405020b0300320706100440300c40e031004280340c130012612103840b0b040c825044802c1d100050b24150400c005c801d42800840c40c0826460b801100840b0340082c50 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 386836897 1250 386835647 386835667
    0x36190302010c020a0b040e0a1b2f0f061006020a050322050409060c02060a063005060406090c0501080606030f10050307060909110309030729010602010c080609150105 73
    0x13492680100343d007500003081c0080c00c121442541401501e030804148280aa03150452204070140c40021000801002c0c84002c49004d41c14002c2e0415983c00c1c10a110350b2100481c68a4954403a560241990000c010843c81c0c00402c0610400b600b4548040e041900081e20f13140c0d0303640034500f46a20070182e040245078403c0130000f1084000c09015106105006081c18908010500c00d8954070140c01040000364031540d0500c500f03019141004800040420030040c641c1011244440c503c280940102c641800705104000c040d00ca140b10703c50101e20104146071034416180e5a07404107050107001c406101407640d48006070303980800d40400600d9545d903400660304104425501158041c020104003258940e4000340a80644004900500142104c041c1a00d8039110840b40d1301d0058009000b8140010729200e040039000b407094410103000c882d00400d0354090301c030a03417008002d23070340d00c040d5000d08603002981c141c0e0116044880705107a00c0d190080740c00124001d80c43c07604002c0005602e03244 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 386838147 1250 386836897 386836909
    0x31b060c04060f0c02040c02030304151104090906060f0b03011505040b0f0705010603120f1d010207050d0303110301090506030f12030115050d09050c01021b0d0210030236190302010c02 81
    0x680040047c40000803406010303440b0784c010348040e00c85862081d009407068100b4003c1d50042d000c842525441e00e031400038000001d044c140c508944150302e401c0001442c1102400c80b0b000303449a45d441c581e4a505d00000b4080c480c807607040303200c00d00c51f042c401000003100e001f040e540c802d500084c420f541d0305100c2c94168014042604018010b000c403088907000a5446886212121110f03110310011100c52064a0314a24040d405140140d10007041400703a81044090710140341c0c4070b402c0c0414144120000566140c1090b04505c030603541e00c4082142c189401c0080314481c1c1e1041020b480c2010448617150064032050140c0d01c040d001d51242489444c2c4118110341c00f5404091040114001c14500503407100c3c449010701c0d00600c41e014070180ea1030407201b600141c00c440100b030404030145907400d100840c0c200070030f04801d0550a118804080d0040384034070340080c400106c4180c28200300860520142150541c0c180a088401803102c0003e00c070028501c180ca4090a2401f20341c1d000d0b20010319 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 386839397 1250 386838147 386838167
    0xc03032a09141c022d040e0601080a02060a0219110135060f031905010e061006030b0a03140c0301050c07150e0102070c0801061a190f020106080708031b060c04060f 72
    0x244400c079005c010440d40a070501c4103890448211800d0000316060304502d603451900b070084004c0e0f034101120b4100185020001006466414010384210300c20ba90322601c66640000f1081d241000e00d5000d1603415a80b00021140322070554012480d4024440c0c5400165110303110880d0501c0c0c00940454903a544c0c00c8040c100d841e1009080751803020000301300041c0041055022201503003000340b05c03014200042100340c03050480c802d9094010b031409004a01400b0f0b507075191074102002520100104002c205040300c1400704030010407030032098009060031110000d001e5001000e007444283c0000300190b50f00c2944a0684501040c040703498290f960091051200003030009501c040001410381040d00a80304407a1740d032900a000345040b00304284107116100d044455031701c2080c08140414020b8070130000390180c0380300002c0e0a0743c481c0622860f00c119038000c0100e80c0d10200d8042c44099840740002028001c1801800d520308180305500960b025502038481401110384015404a1080003648 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 386840647 1250 386839397 386839429
    0x503010602030a12062c01080c062205090a0e0d020c0f090415150608010603021804090c052808031306080c0f04090b01110109030206070c03032a09141c02 68
    0x714010302c0040c036281211701004200d040100c828000000d042c82301280c40410050f001d850302d45010744c81440d01c021220119508070260301310324008145611a0300c1440e01c6401c030613000141901400c900d042ca01031501d2641d400f154008211210740b6252a0400a04020140c83e595400e448902c0c000c60075800f01140401002c1c5081089421884420252812540b541d2a40a0540d80350038048003a07204001141d01010100c2040514508042d4000f10071136008030402880c4644990000d15078241c1d40501c500003100504185200c3c1c01c1c9401c0714070041130b840c00150701d01140c103150209000c030703103100c2c2d401448044400680e16500003000c8400c580c00680901d0340d00c58498074102c00a040709c4248030f000551624001d44201c034144500c19119800d0340041032944d442d10340032606040c4160b030032001c00d5114102041203102c10840d200b0540b0004609049003100e00c1d01c0101500c690360b03c007800040110700359403510340700c084405a001c0f0038410704040c110110300204080224900c0d00c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 386841897 1250 386840647 386840669
    0xa0e030406051c0e0a200901030209040303020712030f0c0e240c1002040905010605091e18040f1a0f0615120702010b13090b06060a180b040e070503010602030a1206 72
    0x18403a229000704484c840e19210b00b0300040054403101010410080d2414680d807c001240d0050000d4909401842c0d4000d10914026240a5040d07031007440080c01c08003590086500e440c5c0e0120100018012110244103516028a0451440340010b10b02d000d20740681d4407945403650b445800043c41c004480c0011124003c48503000c01030a40603000f94428451501403500c2c010001c181c2c40c0c4180300b246d00c4d450300205107001640681c50703510300a80c224600594015061503184d034000d00c0c440011340c8280d004200c5400d240b60981820b003e00e040c007640c0003054141040c10012a01420700f52a90095000c1d6580f2a02c1c402003142e25400c2d10a084e4459011a404070811000c80c3c2d0540003c0b104407070a0f221241c01d80f00c000c20349410788030394000041100c0c00c3e00c4001551820110b010748064000b62070818020031601e4081240200541c00c50383c407080000906020f20407000e1190b5030480300910b0268919031414078001d4507805040c20140401c55a00100140f86429400601c00b800c029002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 386843147 1250 386841897 386841911
    0xb060910090b070c0305010b010c080703080a1e0e01050603030c0d0807050d0203010801050a0b19050609060f0a05030403020607081b070c090f1a120c09090703081209060a0e030406051c 81
    0x1d00500aa100441311b42d07082200d01601944648541c2040e6540000d0f8a42030401035030b015100120000c02082c0d229640f500f880c00c403c411a0072001100e052000c000980e005481141401e649004045500070341c0300f0414a40c2d070000c0001d52701c0f41e06a148c070701420740d9214140221181e1103403c0540715918004000807800032810b502990151050300802c00c034007040d1340c00b8000040150a00724801440d0407404110b05d040550040945480040515107814075500501c11140c000c404494006280481000101a010400c40c0e8001c0e0403030070580300d24a031490441c590903401e4104400c20076030106001e0100040c40d044d5401038440000140300d80307441e105405000307001c40401401312685881e95000c42e07080c43c0940071801c800c0341021b00700c3d002c220000d0191825018050005910618000001080c111310250010910010741c418003030a2080106d1315240c0040d03c5030451600e00360004028020020403a02142e0310350610030345501020106c7d84050070a404054482410220 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 386844397 1250 386843147 386843153
    0xf0d1a16020c0108072c120303040c14030307030c05010209030f1609050103110f031213061205090d0809030903071404050906010b070f062d0c030b060910090b07 71
    0x5a5840348046a402c4440d9161030000440e800e030301c180c40328004150107500f91400c4118030350020701da0380d41c04161854428007407004203900d0b4420100c070318440e805c04401d0100308580500f81c800104a0314914541c10380118000a03101d00c5603040c01002e02007200818001c00c03100390103a41030f0000081c1501d042d451a5103c1c02c3d280c0f1548040b5485050282d0004654510980300d128103a0340c20041b100031841c035510130700a00f0a40b52041a5161080003400380d40b10b80c80c9002041d403030303909190f0602450720701003001d0b10300d420b50a03c10002d1b50034a01000320f04a00041e00a0010b9170514180c2680e84031524507a08500c64100c090390140914940401d1b0510f480411649070001540c081100da070701d00c20403540f81c2c01c00b802600b002c0b002c1001803e000c0b5a003c04c00585440c0190400201d02c0d91a800c4074413038003207681030036080c042c0300c55401c035211140d03100f80e03007030700401d410306100880c0d400b00003406500c241c2144500c920070f2039030031a0fa21031040d44400041c0c050f201d502651120715003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 386845647 1250 386844397 386844421
    0xf0f0507030b0103020c0c0f010203041e061d030615011209110f0901030b1801020f1803120309120313050105010e1609030f060f0e1204050a140f0d1a 66
    0x8500c400403038140021038100354401c0c400c695010403058080c100f060f02203410406d0740b04a0101007070446c031091001040802d030071400400c40c0b049480e8078044c120715061380908400222040800c01c1170800030890b2807918041011039015040b07960010109014200588000b4028550030003660314003034205d010010189040d070181402107c0c40f041c075515010406c5071810f02400010f0410040d0b90208902d0002d40c400c4e4004d4403098030000d400c103484003001c00ca19401440c1d101107102100101042d070b0303082c240a140150800343ea009403079131621030700e40c50740c03980000d00c1c21255200020001341448403441c0e0703001d0312581c0030f4002c2c081d07965900310040c0d40f09420384505c149002003041d109400c0b0700801d5040c0071240c0c4421008482c08940c2c5503407002f400c1300c001f05840540c45071400401c0450a100c204174622201ea042511181000300748102c041442d00b00745d001c4c2452180f05480b556910000190b569800c86030241c2a403c9c3c0d1a100e5a240c0c0c440e0011040440c070f450500009015807 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 386846897 1250 386845647 386845651
    0x40b0718060c1a09030703120905060703050f09070f061206090e03130e010e04020616021002060117030306132703081e04120305090a0b010b040312020703031704060f0f05 75
    0x52603800c1001800c905000840d40c0d004d88611500d54400c010030400203010746c0408890b1015001d00040c10b030740c03036150103003009421a90700e40042e90707541c02c000605a1061030b10703170003507080d20091480c3c0d4288041140c428920b4052903040c0080901d003004949513030b8024001a146004051111642c800300e69540c80d0440408000600c1c04588081625000403441c28129541c80382f280d405503c0303503004d00c0410741c0001200c2c01508030108030040903885004520060500c540e00811042d898070302c54881c410030405052010350001c20a0040d00d80d606c80460488400501e03000070b803150120b048203455107282c4402507900100d5031007036040c15040404240701d0341040d003a0040e509040b0455910301c030801c9900400070032440030050300081c481d81c03000b940120303018100c131910300c06900c5819544000740c0c800112440000b5003841000078040a4408500c00341c00144816421903074081d10310302488036881c0424031014009028000560082d0700880e0300a08104090710400c1c204102500c1c1c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 386848147 1250 386846897 386846903
    0xb0409050114150a0503040c030209040c0602010c0e011e03021201080120070209040f0c050616121812060b121b2d0402090402130303091d040b0718060c 67
    0x440701250b03481c0d060420544520501c10300600346880c44101d020f650641000d041500e060030301c20700100042c0c036441e070850300441c0128041c0f0340503031402d04001c0c2900e0844022804100404000440e03990704500d107142034181c004000840c201c50319070101d0090003100b1003c42d51880040c000a100f40b0194424160081d600000c442078140300a0144054490034200030340103000074002901040703a101760618840e20402c0075008981da01c400040403600402d40c01e000d20701041031401c082011100402c0740e683c42d5801c0031b4501801003500890020054400d45803001d2031828074501700801540f201070703402e0340202412500e07052503900983d16107002070a0224810034024921482c980f942c010300d070201c8142c0301c4000b18481141c0f074065143c0e000d0880303034100341c00b80000c0c0303010745d600c0c0043c2c141c401450701c003014118078505008001c800d80b0740c41088450302428030f00c480700c0c2d00c81488a50098100c598858581c55201d412503c92441208a45103050042d0f004030303e260b4410004000140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 386849397 1250 386848147 386848169
    0x6130f030b06010306150c05100e0c0109050a0b0319021303110126010b09060d06091407030506130902011809050916240c0f0501020912060f06090606040b04090501 72
    0xb49240056007150054000e0100f0607a4801d0420b00c070b2880f81100003d0303d40b182c0150b4078440c0180044030207448440300720b01c645400180c10b0800c1540d21004000050208484d41c0c20111b1a0031035400c082c0c4400f5100001510b141502c18100c1d40a540455145a008040d00081d940d680d05004c81e20701034a0014500140c0c4510104001d20406c000b110081c110020008500c0e074607050401a02d40c2c01180742c2604000f060011080d110100e1045c603005041e2994003041c0d40c208000940400080108a1410701d40b03010140442c41d107410f82ca95000c0440070f0000a0b00420a0005a401040300c1021070950000075502003200003040d00900d016445107011503004080e0104240001402030045427004540c0d1a054481100100c3c5000351000301e5041100c51065180c8035541d20340501041900c2036900014040320714100903070300102040c078483c042c1c426410702d1002c2c50303007403000540340c540300e441d848001c40e1066481108503002048402c0ca0385503034607514007114000c0c0609200b6800301c0301c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 386850647 1250 386849397 386849401
    0x8040311010e0f010206070806010c050609010608011404080306010c06060503010219020f01180803070e27070c1112011b0e150403080d0507090f03200604150c0206130f030b 76
    0x200301160080f101c440305801911090341e820034110b4042030028013881c10898001103030310201c0c4052008601490010b000418024289800c16080da003142107401c409050a03404c000105162206594024109103000c0c5c0340c0920302d00b0100046c1c51a5048154913520008541040013a521a0051144025001d6512050000c2ca5450032036084c1c889a10780c5040100c141400590301d400110361203440c4e07040a49001d0002e0010800c216103d411200200d80304825080d0310480c141d18140e171120032440d0408000d15240c1c0d8400038814440c1c200340c01442c05400102c0c802c0e200703400024038200103442e810807000c42c9002c01007001c0d5480c04018010600e0803503440340d2001c01d01c12503041c0c9420280407032030581005036107002000000d11207820495408004140480c40314400030045005a4422440916400e005450a042c01c0300c824418202008100020031203510103203805800c41c149045200180d00203c0c41a1064101980140e58070f601d000c11041d8407000f0417015a030085034515070355 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 386851897 1250 386850647 386850649
    0x5010b030105062b140109140105010e010302131a040f080303090c1c0b160305090606150702040b1c1403030403020307140319080105040c03020f040608060d08040311010e 75
    0xa0320080c011503800120400000300064440708402a450301d00740080c04900401c488008219400480d05040b0b0f19280001005441c8881c0984000d0082000c14903600354500400600822244103d540c140f68000c50182d01c030341c07128600023004050f180800c101000303028030807030503640c020301400c1d12410310282e01003843c220001c1541c0c807a0096000510b0310484107810001c0d620008000c0602d40c00380c5211080000f1a56032a140c09160031141503000d1600e200760150030f40e000104901c2443e4800000c2102556030b111403607645c1e031040d020507a03a8035400e00205014240c10560103420103000504d00c540740e4030390b919420351307035001c0c541c4c1c880382120780800c0c1d40e2241b10035600640140d0003400fa1202040a0050071030031909600d04581c9000c0c003001c81581d82c1410140f110000c0382a40d001041b682c10940a80010302d505442d003140f078583c0241c414802409039000e80c10030042060000b95850300d074283d43e4006103411298070b6450b10380e28600741c510710202160040c0090301c4142c800c1c800d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 386853147 1250 386851897 386851919
    0xb040f09020301080d0e03031902150a0e0c04020d0209060301120b10060804060c171e01050102070b030a0e0f1209041413030f03110c160f0303080f13020a08100501 72
    0x160f03002a8080c00ca00b5a50719011165004418406e45e4140010401526200d00e800f14000c412080b640180210070901481000711410080640f80303800d0900b40185142e44c40807031741d001c0c0d0100441d030041e1100711004410b4001d0298540c480e406c21800000442d00d080c4040f003101c0c11a101d00c03007101076a6204150182a09194840e00e000301e480800418005071480d00921804506485d2125407210200080421808152031186030000c0f522043c41c001c200219140d0702504003800240305003840c141c83e03002070b0300c40101078030f6466541b801d2901e002d500500c42c68002101c0c0e001190000308440002c030500c0d40c81341d003040784514a440203000f485040380034440c1c8241000601c0311803980e00350301c003034072600002c8202d40201941c0c0c1c0d42c15080d80f40c01101511013407121400501340da5006040c05850344e606504031460500300400f040001030f07800141d1fa070740103651658400c0c403500d4407407860b80144040c000003540454129404140b0305000030300e411405000c0b60090000740d0340e503008000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 386854397 1250 386853147 386853149
    0x1104260601080c0603160e06040308091008091005131217071805010e0103090c15031404020307050d0516060512130507060f0e060301030309080f0d1b1b0b040f09020301 74
    0x1410041c2480041c03840d0686c50070503200c3c44114107000c01d2044621001640340d600c1390b00308440e80c80c2c0c08035400b43c3ca42494951140c0701d040908004d01d060510507040b69a800500140d6602c0f1038840340000c101141c1410001212580040c0d00c50304d2b140392840180040700500c003c003940d0108003000846441c0b0904200c0c40740b403290144000c40c01d0400c0700443d4855551080079050580340c0c00b05000007032030f580100740100455060741c41d000c0c040c04001400d0354001d0455030b10402d40b210510015a801040d02001c40c0d00445081c3c9a14080e442e000f81080d02d0b50313482401401c000500047d810390048000c040c4800708856440c125914100e006a8040c0c40c14000740c04c0740d1182c00140800c50240c1014403c00300d0604100415500240004240d03a000741c00440c0000c54075001049994004c100340b0000c08800d0001c0e051310100c030382004059441101c0b0001c0da050154a902c0f082c81001c4042506d41e4200882c1d1418442d15201c0b0481681d0051041000290400a001138a440d80307100707480c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 386855647 1250 386854397 386854399
    0x12050f01050106030b090f040f03050c01140117010609020f0f070f05060c09010e01020a0b0a0203100f140307051807050304080f120103110103020717090f091009050a02120a1104260601080c 83
    0x9d8a00304d82e00e044496030007504450b500d641d07031000b5000103201c024241ca4000c011403082d50414400c4d9555181c259071b400d41c0710b5040c80c1d0040c000c034000030070142c041d14140303041150140d854030b2035800e003410301e000201e80c0580580110001d0100071113000f40100407242080e05e900c1100c3c0c07040001260f503610350100c06412202c0d01350118007124150b800039600508070050084001342c0b030f030031120038803120340d0b000025024901c110380342c060074144078900040000715901c50001d030590b0b10010040c0c40c01880f4408000300000020200100e040a40d028121100c41c220f440f024011015000c80e0b00a0009445a0080c1081c2140b9507109000704c4940907031205662600a990f00180050b41e00031038030305548990f00c400301c0c0c0321030b40ba80351a180c442c04844e120704880e185010751417022180d014082c1940c02e4010003004200054042c070345038011004020000307002000c0c0d034403000c41f0300503034200c0e82038100305146100c0c81b10002c02503145c0c80c85c0000c0a844003030742d80f6864681d441140c83d60f16 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 386856897 1250 386855647 386855663
    0x1309230c0901080a0b0303041805070201051605090102030403061a030c040b13270302031803010209090f0612070f050306060a060801050112060b03240405090712050f01050106030b090f04 82
    0xa030341540b1038542550400020301d0017041003e64400040e003507800540202400707200414103044c0019a0f07014043d00b0000c0c50001308a5801e204180380d509500d60b10401c0144100041c01c8012a48200101c42c015600f20f1170810030407000c1c902919240545404041c807921942100d1012072800788981c0108400003819541240850301d500c0c0040c1c1211036008000048000107528141d01c2d01c1407040319103110b64061551031a607080c05150840e511010907000340c0c418070407402c690700c1c0d601c82175400c00045a8010800e07940c1c0000140e03200c10f0031002c59050f004041c0001b418401021420701501c1c01103080d98407660310001400076406842c8580702c0080c04600c010461940291104086000002c801140d4191140c1062542c3d901c1a500010405032855807450080e000102031400e4400890301070000303003045110a5940c10050140d0b07100707440070f603600000b0080c04100b8020340ba1480c070000e004941e5284800b81c01000002c480901542000002468021a54010b82e125984c05446 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 386858147 1250 386856897 386856907
    0x3060c0414220c0309020909030a200304030809041b0f032315060f072004091106130819020901080604080a080c0918010816120f02061309230c 63
    0x30102600b403c65114050541e034150110241e1100314456208041c3d501c0215038408011500070509110802c04036090890107407a00e03041000481120300701c1b60088503030b645444051002600030028000c04455240c9040401c080c034a4010403249940d82c00350b00c0401119405403007141ca0744550303d0050903507c0b4040d000a00a81b06074165040e5008040c241c0c5003041c0e0245040b407103e84c8254030564085a41c00b11400b46210078031040031140c0313001d88051006c1104d556a20120b0070300001064819000030558100003055606c0070340007040104122890117803c2e4084103502003600e4010f0340103540100020131241e400084d01801141e00c265924641410b42504440004000e0031002c40000104203500803960783e16940031402e0b42051a80c2995458002c0981c6003400100074a0480c0d01c1c1c0340c2003000000940ca5031044460b4010503040100d03503091000402c6407198804800d1000c0c00c034040070507920384031f42c1302e03403585104844900d0940170380b040d409840c80400c580019980c001001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 386859397 1250 386858147 386858209
    0x60c0f021201090c090203010504050112050d0e011806080603010f0c080103080703120507020f0d0f0207051903060606081b0306090a09050c090115030b0a05010504170c03060c0414 79
    0x1180d1411403032071000004030b00e00c09507501d108661140e8007541d02c080d0040014003151510f4800e40303005000c0344910740c54000f81650364586940c06d5030b40720010310000c0c071007058099001e14030500060307a820102c54001e03921548090984e1b001510b480e8043c0d0f203400034002d400c001d41d21460141c04101c0e1145000f81e0301c0c4d680c1791401948101c108038100521030030f00c4010652a40078850080d480c94001d000003000c0010704510300009003162504000078072510b1025280c0100300141958020fa07081c60200b42180b2050700d440c401a44024182c81c504040003c0d00c03540303d07283c10b004185900392003480e1902d070001e01c22207000c280d4800354400260f10118211100c40c0e03010821061048007601d20004401000551300310302640811502c4103070000d1600352a0741845410b80e54002282d01c40c407141c1c14440024560700403401081c07158801c070011042614401c00c1180c1807194000d08880c66458002d404035060b4205208000600004d85244525442c0c070700c0c41c000d01c0340c101d002034181a0700c601d8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 386860647 1250 386859397 386859409
    0x100c08010e040c0308030a1e06050f0f06090d0819020f150103030504050120010531080d020c1c200c030604290c03061221030a0e0d08040b01060c0f02 66
    0x61f00401c2c80c907130382c0d48840c9404451801e40d00001c3c034109000084c0c192400042c011a00c1001c1d44c2d0070b01c01c0c8070b8000616141e42d5001c00b43c40c0b81e14010342d01c078000c0040b00d14000f010b62041400d6040403407440900000703400d03400a09a0a400080c00c00d480114407030700c900c90900b003c04e01000b000701c1c5003880284103951180700219a450f00c01c0c00e81c061030152a1490340d0842d2000d440010741074080d4450762150340910002e2180c000c401c44070142d2200301c03603101d0710801e010f044d40d070b01d140c6a00000c010000074810009030303071209180041080005075084002d050543e0158140c928075900360301d0310100707600c041040c003403510010f4060a0180e41d2a40d45980c812245c01c0301c107002c042e01d4842000000c0494814600c10320703200d4800c80d50303414000300f0480361022810000c242070340b2104401e01e43d5010700340800200e07640a5101ca440784c44045680b0b014100360240804284904565000300e61390010a40380507a0040305981e0481e62103040486080f058180090400340c03404200c600141408 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 386861897 1250 386860647 386860651
    0x5030705250605161b020603060d031e02010f050601030615080702122d04080703110a12230f0316060f090c0e0114010c021908100c08010e040c030803 66
    0x41c0d000030215045540e44800c0724800ea52250315419001000d1036810380044c02c0c101a003001c0020304640781c02ca40d00080c01c520004042c9401843da1403000b5080600440454510344060740f000c00e10036248c140000d008000c2200c03039844040c141404070303d9650080c880d0700b0a0ba43d50000303004451500b0401075400c072801a04807000c500c41c1004521822242c0c00c090b11108000798101c2c80001c007800c16035030000c200e49035402c0c0880000c03c4208085640024440701b100d0340000046c00188801001441110881d80280f01e01c40e00019030f101040059009100740c900500981003008880d040c07445d554640c54050090940d100f0460307107a01c01e15003204009c29910400e40810b801c60b0400403542a52141c0302c0c204c7e00311a4100c428408209d8000758603014217206801e1403404070034540001c8c4124090308010b400b400740b2203030f103511144070501101e000e0310320a803c51b001452006003207c02001d990280714002030a07400089809154500403a0081ea0491401700d11942940c4941029601c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 386863147 1250 386861897 386861947
    0x51018031d09010816090501061707020a0c03240b0a0501120b0a031101110118020d06150f08010e030304321203010f090203090a0305090d15091205030705 68
    0x29001c112000c55071164005030103480c060000d49108000035030756904a02140d0002034440c2c6c1002d005001303147d4840c40c0e21a9030740580e0362081710b40c1c9070050164101048040d01070030003004414044148549483d4050603150f03060040082550745080080440700c9200020780d0003008507004000541c401e00190071005a0700c4800900307103440000082c020750700b66000300c540c0d0703241000c503034030646c1c000070300c80b2019035942c000388080001032200107140340d8029002441291060441301c2171143c6584103416510300300084035a180e4540c0b84521000c04079114036003c0b58200810340b4a03914000c0181e031301403640488000c0054440c80c2c0610904001d504450381110701c08800452400010020070420100802d9686d980c4c0d410b100ea01801e514030b6801c80d100c124010070501041d00310000d4020b007555014038005486103110b00005584c080c03003c03400380560705003044080c0c10b415964441d4074070394411040c4100034609c0f100152103c2c0011135184c0302084050082084140b800145401c0b4510 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 386864397 1250 386863147 386863187
    0x9120c14010e1e010f2a0f0516030c091a121603080c0c0a03030206180c1e04051501082a0a0804020103050601050c0706050d020c031605101803 63
    0x30140108015200100e034140000810b444100301c196003150188042841d20310b405002071038121110446030041071b0b00703152640403442e10941484182c1d404402000d40c41410b980701c40b00349120221181e0b0950205071501111070100040310255440b4642c41e20b4800240d60a4a013032220401101c980708100140641c00b4610300c024840c40c0200703551014500c62100142c070340c1c80302d80941d8030b0a007811104900070f0711164404d202080e00000c180e03510109161401c80a02c0b158881d072424048665541c68200c0400042c14801c03900010498269030015901009103507280840c02d02d00d40c044041f0b50340807551102c041030860b0f0400d181003264070303412882d21000d0910081301075419408022944000f48a48092204640e0b1502840f034000100740380c180c1c20305400d240c0c0c0c0c6407101c50a20130181031200c001000d5044483d607405441d10301e035012040c0c94890a268541d14003e030141241262680205d0780d83c0c042c070044501c00c1d84452505181078148140e51640c0070788004604410b1064882d03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 386865647 1250 386864397 386864417
    0x32e15050301020c1605040c090b1b19061b0c0f0305120f0406150e0604020d18050a14030a1e0512270303040503070303050705071b050109120c1401 65
    0x14030240004d0505910030380003040550300d1215070349610700d142c1d0041485941040d5681c1180f650000514090710001c840c000d5444109200e180307041140c2c4000300e207a40c0120b9005403581c42c0b0a040140c452806607105101e8014654040c040a01d034202004020442a1400f1404038030382030000c0345054400d0419a01d0b0080d0751102454548007180d206007240200d00400042084074050303441e40d040260f101045c0541451400c00322200c0041c0854043d60303011030b4036010054541c00c800c0044011a0084100d11524140309441e040c0c0300b170050300c00c0544c0b0b40c1c940542080c00012211030403020390307034103138030ba0889145001d01500c034840081c100541440031405a03203441c0982c0b80210f1042000740380740014820b21801900c5048007115443d04107008101c0813400100480f010700303a15180002d500c2d501c0034026a103a00800402078010042d00050300034103e5180d40c003000b07650702600c4081c0d82d6540c8110034000040700d0030b0000d00100006804100640303000d04500700312581414001895 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 386866897 1250 386865647 386865649
    0x1504080706050c03041d180619020d0f0618051008030702060703090b0a17090a030c11010201060e0403020606190501021b0a2d0504020909010608041a070c02032e1505 73
    0x40b0322140b4002c260b125a0750500c0001146406201f1000850b43c0242c881842c2102d00904564080800c800103070340c0018400c510088154042822203104600401020340c035a031001007803440d40340c0240b5001d8a8400411307100f0900d8054a000c4406d000c0c001d5182c03806d543c2c280142500095011400d2004885010840790b4129024046800f4240e907413441403a0034028030b040d85040680980d00c07070703007081d0098804250b0000c800f611880d003014503000040c82c0da10040b80100340e503a010a40c1e40d080305042c00b08165011407520300801c401c4034603482840f01e4824686050b4034034443c07640540c4c0460b1008030b082d40d408240412450380100600e0880340d5450f41d44101010884c07007010724031f00d01d4580f400952411081200544401d441c114248401113001c950380d02418040c0b80180803903200082c0c1040907500d810144000c2241c4180c9150801340c070040c04c02c9403040d80c22446070051301400810401da01040300340201c0e1000c1006691a141c3c1654001800c5400d86a1245500843c1c04912 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 386868147 1250 386866897 386866919
    0xa0504030b0f04150203010501050906091c1a06090601200c0604080304090f051513060f09060302031911120705211006060206040b0a090605151504080706050c0304 72
    0x4191031a40302d41ea8180f40c1864200783c0b60360201d101c00d5041e032040c0010310031a644201031310000301d0b060312041c0c0d40f4203240c0001a413402c0c4480400f4101c51003807580c0300410041c0e140000c04a104203041e850340d6201c80c000c00844510031158180021480304100c03840601c5204460780042105065034000300300200490307140da225810070750043c0d0000404200ba43c02c0c51242008410613910200400d007040d0008105042401c291648200d04112680c240c3c1c9805e40d001e80018406000845000799840c044a0050220307032105a1090150058488000c03c02c01c42d40016103a11841c0301c40ca44c000081000716400340d1000f42906031003071443c0030540d901d450902c41c04e0b0313558100d15040d0f03001004204501d40f480c0040c00070802410007008110907900040c515070080e2384100d815403141d99528005e80200440000908501c3c10305040c00107250b44000704010b44d61003502d40e2690701464000b0302d0880c1c482e9100300c0f6907542c0003400c01c000613846600500a0110640b050380d142079690140150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 386869397 1250 386868147 386868151
    0xd0503180109110a0e1e1008160e0112020904120212030a02070b07020d050717070515010603110f0f090607020a0f0e01090c050d09030306080a03081009050c030c0a0504030b 76
    0x240d0449a500f01d008a8546050780d00000c00c42c414100200b0301e80502c17018134042860111418190441c0c000c5031550800c0254000601800b030116407120b901880509165002846001d405c2c1a0100021039452252030b00e0703c40e140d80240902c1070948543e0380381951103120800200850040300ca061700c03030620003402036000f5070f02810b004d620f40090341808082068050a41c030b0a545c8100d44110605800005540b4216081401e6881c8100c143e2100691071180310401003035401100e607034898980509102c54169032640d50104400404050390341082d00c11000f46984090040c03101060040142000741190340340649400d04020007603000c5031894075180c00001d851540904144100c079081c092160040618080502c0b004600c4000944544200404241c8054850201a050601980002d0000d1440340d00b1030307582ea512070038024140321043d210f40310300580c542d500090045907070003524050906800300703a1131901d4800302e40b1582c0e4810f007080000e00006010000225180c180013174 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 386870503 1106 386869397 386869403
    0xf0b010203041503050619030305070506061e1201060e0103050a120516020906030705310b03070501050d110f0702030d08040b19060b0c01061a0c0d0503180109 70
    0x40c47c0d05d80f50100c907100c002c00c40303040081010342c410700a10169000e01c4c00e4400e180c0700c030020440000f0f4a40005115898403004502051510054000c000d0741000000203034aa9980c1910f00c1c507034426401990030781c009440e890140610040081072410035880c2140c0b0700704110788580140392810300080d010340c010400040c4280c40800184002d084010982450508260410501c00d2a0809005080840c0710b4041042d182280070704c02d80708a00901506055003000011980c030340140200d05012a04d801c603480030490754100500404c25000700055490b000f50060528102d0602c0919007040011800c020109503068155500040000c0441d5000d10080303100c017014205d10741180c2c00c442c6000954ad400302c1e50542c8160101d50034141540503600c507a0b0301440341d50048201f0710700f880c7c02112000e440320b403042c0300650f40702c41c006500314a04400c1e000c181d402c41d507942c0000c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 386690647 386870503 := by
  have h0 := BRFrame.cov_init 386690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 386690647 ≤ n) (h2 : n < 386870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
