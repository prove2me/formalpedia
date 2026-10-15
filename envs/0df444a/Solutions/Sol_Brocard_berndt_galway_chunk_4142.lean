-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4142
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:41:13.477514+00:00
-- url     : https://prove2.me/submissions/8ab8588c-31bb-4af8-b987-e3b65282a200

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 744784172 ≤ n < 744964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 744785422 1250 744784172 744784189
    0x120313061d15011d060f010c0311011401180c0f0305090a0807080306040b06071109060d0f11030f030a05040911040312080a050a0603051c21060311030c0109090c0c02 73
    0x341d8184640b051545420041081072401030888111040d00c0b00800910307485040041d0141a03003440e0020084000c1e05060340d20518034030010903d07508100c801c00e1356041d400b1415040380c41490350000c0c003103100905541242c0b00c040250740021107407212142820b22940000b500008150b0660740c03a00e480d540c0d0b14003d40d1190324215103904011041102515040c4500391102c481551080c0c944052a41c03a400c052982a1446101c2e80c000300202c0c0c2585c496a83d54091a43e100f502080c00101e02e0822000c403595240d036581c400e22441007207054a001c08400c1c2d0b5120119038983c03030b080038100615070002e0040c1c55480d80225009001c0000800c1c1c0212030b030f10b030041f20f07512203000d24200100d82d48142d4030000c02c880c1055041035805c10006200007115400c00c40c085a580c00080c0d44150304840400103291b0030200d45410a00c90204444603501c84401c40c7d104054111280070402c0902da01e070120400c0b20b60225070500410002c9850715003000b50224200d03d82020500c095500190840 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 744786672 1250 744785422 744785443
    0xc0402071b050f01050301091a09090102181c02010809012004060e03060105090f04051e100b030610060804032a1e1104020c010b130509120313061d 65
    0x40300307000020326007120705081280a03040a88007404000300d40d000207045440103200f42c085103560380c4190220301103025007034100702c640200744410908052100a010307400448500303410415510f103030051460100c040320000cac0138213840c07000c10050940054886d11001800c521145d500e0b032107421684131107a80c1d00d11000a5000b105915a428248000c00b10381050030071034025404040144101d075941c407202c60388407007501201c4040740d41d203180c25400c00c03044042c669011024074507603c1c41b0a0022400b9840300c2048a000c00010742d0764410150340ea001036034150f0303840d804080305205142c42441a9944180a81021208c1e13004201c040710025500001e810445525034660100702b05011480510724012140d00050b80d102c030781c03199107145a641d406540b0942c0e002a1250884100307402014028034000c2045c0d540c2e454214802c5c5c00b40c1001ca690701010f00661402c0051080b100098030b004440620748003001d03080d6691500001d100c0341503003011038a409490060850402c002c0560751 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 744787922 1250 744786672 744786683
    0xe072006010303031b02010e120904020c010c0210140408040902070309030f050304050405090f0d051305040f02030a06050a030809061e0c1b03030702151e030903090901050409150506030c040207 85
    0x740141741d01a46051060200d4401103904000046620700380000c2c15251400120204c16615584840042e0007440340c404520040c0d420b1070329036082d880c0c000c1031a02c40c4107280700d014001000c0b0000b142c0c01c41c01c002ca40080c041d000038042440a4149036011f00482846400c0040c60039407203489056620340044001ca8541c1c2c0001000c0c40141890b0142c1da411250850080800c105070219150b142e10400030120f003048004980041d50800b04007800340102406442080764000c169040c1020398003c80d08544101d00b08900010b590421841314003c698114a1240c2007100c410200840b82c0d000140e101c00c0d208094003842e21981804008050104a8400509518a01b40b101130f242148101056100f5001800164056150305242c510201510203001d50380e554230780d40d861400c0148030000401c01d94040204800004000010304238408211003011740c42c2c1e80c3e01c0c101700640d0b1421a0040c54002010300d6291f5002c01070b000a6000140181524101500c1e100404c040340c001c440107855 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 744789172 1250 744787922 744787931
    0x424020301090f0513020d170a0908120405010219061508060a06051516140f2811041e0c0c0318050a170703080d020418060e07200601030303 62
    0x400038a441103c00181c610b880a02603864448428500c219a511020b40501420421070041107080700501c0102c0e00c82081007034a41148040c0204400348074080c03501d45100b0f540150340940503000580e01200e105900030070f07005040c4940d8a01030f0340001d004440b11610345403400300006031030003d800a411300800030809480c01c80c81c8001a2003855018901610340b0098091401c0d07241000c0751200c09c1e1074503401000542924101c4080062089c0440307540c0507010481c0c5815401040380d0790442820303d00e111415041d580300c240000d044c40030040100c141003000c4890790809400180e400340d0070580b100280c600941e8924203035103c01c006803000ad5143c1e1301c40740800d501b200f459800441d070ba11682c14414108004188800348a0003032100707410711140740345001c00341041184049d5030b105004544401762103a503d0040d410a00650400d814000d5038a91800e0300c61244504680b030b00c4420380b00d1900c0f003001c25a0341903d268a252088817851402d080503200420145000354441d030b40005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 744790422 1250 744789172 744789179
    0xc090603080319022b14041101030b0112111207080c0913021e030a060e090a260f0d06050603090d0305090c191a0a120c0512041407060c0b0f0424020301 67
    0x42154442c0c440305410386c0c0b8000601010401e541c100c02a410028200018005007110040e40d582c0018400204070500b84903140c1501c0700b01c0b20261100d10040c0d401c05801c1d17160603a044e100c51204032420820218117114850440ca09030040740e10710650040014a08240e440310041c442c080030020401802c0000b00b445901e0b441c0b4400e403c020044044520864240751580d00d8455015a601504d80c00103000003c00318030120203e10301007040350415640e0380d0000c50240d62246c0040350b000304250301d481000526402c0003021a0301c0740c00305a0240c46130580d412030580092a02900b0f101c0140f06989085a10351281d1740c0390380b0001200b006411b0703020700c2c00300e204080c000740d0201518134210511440ba030f00c641082d400391070034084070b202142d80c07036141c02c00300c6e054007a008040305407841f1903003408240000d4041171004201c01d441500e9100b520b4410031b0310421580a0002c091000300310010300343d10000e010046d04140300740d15900409124880d5000c2e2080320781000b00e00303540d0000040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 744791672 1250 744790422 744790507
    0x230309010617120904020d0e0f0124030302031902070f031110090e0a0e1f0b150a020a0803101527030f02040b0d15090c09060308031902 60
    0x40700301e180b9031006100902c3c016015405601a1440040c0103d40100e080f18506040d034115030220001e400c1280c07981904001c0c03460103400802c40c549603444001ea003903c5a119030680d00000c0d0303500741c0c009614003501c0e8504414500005101242140100c0c0d40205a0001e032600000041d030140045c44d01400d180810800c0500f1003600500c1440100c0707c041000100307684000f81d200715444000685903040001d41030911208242031502c107a428040ea240070140341d404075580c4074080d2003298034503c0c0e58822400701d118041040016070711203087c11000a014500442d441341c80200d601c003000307a0b1182c255941c0f490076111080440c841c08405148804c0c402503001d0424050040c0b103009515648941010b22003049010340a41d0300c1d2460b5001d16201c0303400d5000010390201c0c480c40404a560b100c4002011144411541c05009400029032000240140016650041243d62640d00d41803100f1802d41d50709440303100784580900c080062200c080d0b000c1c9101840c000019a407904011409 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 744792922 1250 744791672 744791699
    0x120c030b131a090d05070303020f070311010c0e01120c0e030d02030406020d0903021003020f130e0a0b0f100f1419080a09030903031409030f0f19030804032303090106 73
    0xc00c0c4001c2c1081c10802c21076070000d0114468409030600a542d00c0150034114084d20070b1100790f00b00c02c0da001841c40304255104c2e0540014004442c02081803031803540045800f044150525800580d4a400780440c208440d44520280341290510409000d4100f001c20304001001041034091b03000810100b0040d60103100b81c1412088902d0550141030a503400500030100e240b90040c03c241d80422940801c4c00c03e07078102e4402c8440201030102c82035071000d074141c6070402210002c9016003007000d190700a0500d40440e008481c1c1c01400090407048810040b5001c00c900b0050808201249000301141d0144400818400c231600c003005110010f4000c0c0600080c1010380018501cae0f181601100119900003001c00030f0b60350610304801d1241e41e9002d20b00c0c0d0350040d480307003039858050802041055140018548070031040d480550b0a8020303041c0720b03c121680d81c20f40c0500400c3e0040f0000780060f12540c039802c2d0010510038468050f500701da841c044660000c88505105a56614060000301d40310b989 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 744794172 1250 744792922 744792953
    0x501061412060702030a0c030e19060e0a26070302120105100f05010507030f02011104060207181b0e0d06140702060c1c051009090302030406091a04120c030b13 70
    0x30003990610fa64000d5a0f4400c100e0707140c04108030a43d00c03004143c49501601e00504008100b506105041600a0030025040c41800003107814043c1c1d09880741001c1c42404110791003000a000440b142044003850304d244040080680d000d03291010005a6803240684804141500001498600b40121808101c02604540d010760f40c5d501040005070303031040486540329414070740864001407c0c030b820781c00341906140d080c5a034200410b0224000380d00060400403500140109200072454100842c1150081c5d9201c01004070119020130107140a80c0f0826015070025002008045442d12880100d40d4a094411705445e6440c0c14045e06941c104503140e004104280000c0c94461840c03540c600c803c0c4880100001142c80d40001903102e030103040008020850000103121044103450000e499078054091003021072a000d402040c851102c51002c00907661a140b1546451304000718480d4106100d1422201c8040440000c00021803011010f80511441c0ca1917052a81d2185440e0b00540700004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 744795422 1250 744794172 744794209
    0x305090a052d062506060510030e01060f051807050f070602040503060601140d0e0307082d040b070605190c03020d0c0206100501080403090f060f1205150f060705010614 74
    0x100c0c0c2404d19404801a02c04003d000c41c00c1280c0103040e181c4580904050750006a00c40710344200030001d1500342e080043e0b112000300c001c1203120385a5520303032800b10382802145d41180003504010100f82c840c01d01c1c0e0b13400c012203081450500185410444e2580c0c000c40d022100706030003003420489403c0401007a60065000d00788091075640703d5081c030350103015541c0c100d0313520394450001c45545201801103070ba5103604000c00a54a0a40b010340d4a1b4440c0790f10b032102d03c54011400d4030010728400b2010f4070b05a817040e09040345407030900d40b031704006020702030b0600d10148091540d41421550300d10072040f414640f07803401b50326003010503819021900807046410554002d441000640103061041d0801c0c1c07042402c103e1856200c50030f0454029903250404181d12101c9100030844903000018080355140369995007035100443d14040d4242d40080e50100d94580003442085070034600951081c1512502424850501c00399480712800d442055100d054400340119071250b85090000a2120020405 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 744796672 1250 744795422 744795427
    0x40501030b0405281e0c08011d1b0412030e03010c0912062c070e0105122e02040e0f0a0207030915052a01060801060f030305090a052d06 60
    0x440b0b0500b04103000c42c08082c240c41004e03600580003843e50060313051240c21141c00c61480000c00c088030091a0f041c802101194a41c00001031241440b00c21403250b120a400075200c58481d2080340700f2041e0030303411038400f190042c4008510b0400c0070a064041e28081d41d40c3c0c0c4c52000e205400e00d07084030002c0100100b04003002405001012070a0403c00c14141d01820000f80507c0c4034007009194513001461900079403030490011030b040c50000c0c403031040d9020540c02c1034040e40ea54003040007200301800d006540ea0894140b00e240728070030811150b07402240d0a4181206007002d10030108aa010303801c8410b89121a2092040e45c00c51503029030340c84942034004514048458401410400380f43c400e1000006a0100f40c43c00c06108105503809009013807941408101c50000702c2c0c48140700d1070100700543d881c00c0000180f0300014040c0c4400c031941a1580303c031260845c3c07000c9800781c2c041c40a9a420010300c400020f219194008085556202c03400c0c4c1c103640101c00074002070828041d401861288205 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 744797922 1250 744796672 744796681
    0x180102010501140d0804030c0e041203052e0f15181d070c06020d020301060e0f0a0b09030115171b03030306010c0f120513060c0b0f0c1e040501030b0405 67
    0x10300d000143c0300d00d011500f24100010a19000029105a0300003c0240010900000e000e1410444090103284034071106040c0d00022002282181c4d002c6440f02c81c2418050101520100d400107901c1c0d604001007405440c6507240c100f00342100704079901441c101d80c0000c1244090321f070704c088151115404040360401c90752802c840082c141500d81c40d1400c03c4074111001c00c20b114024035144007e1944680290345a04426500c0c00c000d4109104110100e8580602e800c01c0703280041d01300e2407080c1e00420b4075421600788100078003150040302d1040e0705907582d600030554410170030071044000c02d030150300b040328550f403a1651820007000031140304a0508040d00960f869070040181d0fa0300510030311300304081d41100d08124900d0507075400040d081403c15491017a01e594840b00801c0b00b810505500f030b420641c2c82c0021581c20401d020060440e100b590b000c141c82e401900d50464015250b0103445041c01c0e2128000342080942c62000c480040700080e040001e56014000c040c008082140d0420a5141 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 744799172 1250 744797922 744797939
    0x70b01030305090109080f010605010e0111102412030e060a12050c07120206150d0c0b0310030506070203090411030c0d0c0216170f010c0516030c08030c180102010501 73
    0x106000050070b1120124034084141d100790908001020217404580488a003000410300a080d140502030002d031446000207500c1d40204000180c010760800107080090400325040300401ca0b44024182c090309002811508400c3d00400d400a06042c40100444042d41d15018001151110300d550069001348621035050780c02940c07100c80e01403c04404039060352071000346501885590760081c080b101c11001c4216050f0300044076481148280c09a040d01542042040f007980040000148840003200702400070201c4840515000403136455201c107100d44991f909801d065048944400603840404c504280c0d2402d4090110034440001c0381071318508040140b46024811400300000e25629503a6244049200b0082a03100701e6500c40c0008c000c03030303c2e6109400003170300e0440701110601c00ea250f2034110340810702c95403803c8007068503a40e18020b00c290b41e080c0f01b011502c83c1941440134151300300001c00e40400c000c610a80301006420340c5c440d2401303000c403c0b08032100e03103181c11a03242c000140b00c03894 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 744800422 1250 744799172 744799193
    0x40e0c090f22060b01020607030e030d232805060d02060901090b0a050714121e04050d03050a08090a030801090e10090804062304050402090f220e0307 66
    0x1d8540c0c1c0309403107a600c0c0007261801e449603410300c41e06006821501c0d8107101103903100d80e20341c003026401d13140b003a1101ca400328103580d110f00164406820803c841841c1c10b585510008400e80154180102003040c1c442000d00d40d40102c0e80c0449080c0c1082c03145000e03495500c800e40e0b0209010070b04018604016010a413204061040280290300004061100d6800355140400034461079100950b40d03052140c0062080d004010f00b00c0c1d8a0030400a81c410030b890100e03000300d42554101c102e80c2056640c8071701d6a0b02030380a0200094600341000302041c2c80e210320a088084e14000d031034540d03030b402c68004020001c800040c81140700d078110021040000f5409031403141100d29000020840d484807100040c1080c400c1e10540f001585401125000c1004240c098800c40c0d407140c541c0c1c1210240112800401c031211407000c20828400c000c1484035107407540c094840d0304409000f252050000002240045c4210543d01c4200701e0a9a4052207454040c05101d00f01c41090000c0d605180340c9030745048085 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 744801672 1250 744800422 744800431
    0x504050a120e0d260f0f0319020307020607140705060f090c09010311040c050307050d021605060a0504020f061602040207051204060c030f0c023102070b06040e0c09 72
    0xc0c04260520040310707100d481014240e030342c018a8039000c80b41c54a0700714281881032600c44800301034882140104881c05065900000040803102d1820310620901d43c0d440d0320060480d034001d02e58659041c5070980707500c040d511540071600205080d040403130015180b107003400b0380c4070b40d8002d04000c004c000820105080e50010316000c80000c8a4407001e1003a41402e250a44c3c0d035800c1800c10000006000c4541c4001d4817850040d02c1c01c000b0f0748803020088820744021641c24010031410014102d803102c1c0d40c1e0040401034508440140780c00ea1541d02d050400d5801e4502260598a4009002c00e6203440d6020108642c002c82d2072910b001c8280700400e001c840e0300300c1d01904c01d41e808110b40c01400402d010710040001c040c89901c1e5103541300da4000c0d146100303408060700000d640f1004012407501801049050300c3e00200790407014106c483c44e4107a075021803540080c4c5004d4044202084140500152040030701c55075080d0218906a800e000456542201c01c420701d5001d0030a12841e81c40b0340300a140c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 744802922 1250 744801672 744801683
    0x203150a061b060b1c12090f031205120114040e0f0705060309031b0a0303060807050603040b100b0301080102090f040603020105070803040f020607141c05031909060f0608100504050a 80
    0x741c007041d08029000380700548407541c019003008000c181500040701e031740d15030601c9100b1540400380c0c842801c4444456034043c0c0f00c41c01150020500c0852039003800300140d844a40b80c0709292200100603024210b02c280d000d01c00c0c01070003045104051402d805507840c4440c25034001c1c030241d1070004d40980d4400c40752091501030740002000c180c0e004414012210320503801c008085140d045012402e0fa070f00c030001000d8000074942040480c00300e0020408000315040100b1050a648031030f11015400e0801404142c4560b0b00d0074800241c019807070700514000e00b000c8000584588001c400d00c924280715150711403045140000030300040c0e03040b5003621681c80e00060107627100c0c4d40b07628003007110102c0403102030b41c010720100700042044030a040c1420404010340990ba211131224003501040110809014003140c4207100140d600c003410b03590410190381e408808681c1022170348408045941c80038420350180c1c3c41e0001400400e00401c084d44010035030f100700300460303d411b0316030588450482000408 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 744804172 1250 744802922 744802967
    0xe030a0e0307051002071d01050a090c051b1f0b1323010e06120105040f02120c1801080f07140105030a141311010f08131707060203150a06 61
    0x4580ca00b0011000a00380180c0f00039803224082c800a582c1e001c1c40c1c03140064900403940c005840c0e2000b01702c214100c49000d04048c02c41400c1c03440c4007001d042c80c1d14900003040340078001d809040103058a400d0401d03140002a103811140ca41040304030441e080d0b44009098180080e61200740c85420010360801801c0c0b000107410f00d19102003c80000d441e80c580c4040b80c2500700041406d603000002103000d034000312450800c075203140c0030781400ea940444e00501516201000030000d130810b11000e071f8900441e2020740712602800320000e0300c6c00055540c4030595400300c60062191f0603003002054030500ea404d0051a0aa1400c224080701d250342c0c4249a04000c1c020021510016880d0060f44e00d4816913040c007407161801240c0d641421038010416900c6a4103207501010759409a2030040d80042d20fa5610707102940c604003822800344050000f00d43c00480c0000c005454640003014100083c0302e181d01590b0f80c203040d11210690065808414840c030502881001002e4120954807000c0088165290 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 744805422 1250 744804172 744804197
    0x60a2003060316080321090a02010c0507080304060305060a0e0615070c0e07020d020c010504140411070f030909060f12060b010e03121e03062202070210030c0f030e030a 74
    0x2410444050800c3c050b40d086104040b44921021014010099021000b6901e20350805400440c402003603411146580250030100c015520407586451b51500074800c6540299446c84014907652107588200300180c2c0d1102406054501030000f5401003602d045028224100500010860189500080204400040e9046c10002190361050040011460712842480c00010103074448040c604008014020201e5840c0d080d8040d00c20b8030f065889522401181c1c0490b001801b00074403030459807039560384042c03180000141c050409001400d10036910320441a1a000d004401c0c0c89198125208101804d007041c0040703c42469000c101e190400f10108846500c1001614500c03100840c09400d8003c402803000d90304011030041088281c40320621021948802c1120400d02060300d4459024108210a03000300050031607122035410315900c0146008020341c002413028402c0154180425100c0e40c03008205e0390408031800d284141814140407561440c280b80f07442c2c0c421240400f040c00325005601 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 744806672 1250 744805422 744805429
    0x6010611150f010e0a0c090b0d060308070305091003110909070c021f020c031b01260406050a0623092815060f0212031e07080405060a200306 62
    0x88000706005600040e07400d080c40c001070048003d014001d2006215800308015008520900c09802442c0d92410703560790900c40c814a0980c04601420b001c951a014040041114000140415407203034942582d80c1e00103105001000d150100f0032400e0500c1c12650055154a00d030807541c030b6000855120007103540e01e00054034203c0c008907010b5001921040c1c881007040e000401e0440f03c810f0b0350210b40346844181c003090340c3c2c2c1c1c03143c0c040341d10540c04140624031554020118403151070000c41e24600440d0722980c028562490445003954125112010300180308100c0c071a604c054200d110710303104c03215201c0c444c0c4281c600e1560869802505044000785c1c07038011441201499102c00610000164081003864010704015040c02d04a81e01c05240051214059861100100c4031600501550400d03000d100202e40c000500d007a040074000b840c1e8500052442c00741903c1040c02d510b0b81c0c002130a003801c0443c9403010051a41d241903185c0200144240d01c44040358070382c80c2d0301c10f002e90b41c0c03641d41d11f010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 744807922 1250 744806672 744806683
    0xe0108030403174b04050907140c0703030807171f2303060603030922270b06060913020708070606230d080a030207050f03030a0609060f0806010611 65
    0x4000f02400f00407404400c40000b0f41c640500030305403051130f5102291940391181036209418400c0c42c0140100700410044c00e281500ca03038850000c4c1400041c51650f9100b00029070301034a244840c9400c110b070b06000301600300c0f0342c9681080c607034503109240d18203081029107059000382581400051846404100d0b000c1d2401c10b201400200860344c0102034841031758030b00d4800c1800a0751003802114006070050400100b03a4a0b0100000c080c14421107000c8402c4c0090015150242d0f000b85d101c4180c02480f44440c09400701049a690311034100d441da904080310b0740e540203000036100c0c0c0001c00c281e038040e58616000301e524050402005a0346c3c0042e2500040d6403081580050040c5e041031b90015011103805400001079101c0e0b0003c034100c6070380344100079001e814180000c142060900041d09014400d80c058500e07184540201e9010000c0c0c0c2d8203180c903581086078210b01c0d95464010512608a20780a0f0300014010b9002d0040028202400561240c00500841c0204070003a4102510074408009 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 744809172 1250 744807922 744807937
    0xc0303090204110a05070510051527070f031b0509011b0b0915070e09011406090307080d030b030c09071404030c03030c1112151306150f0e010803040317 67
    0x1000f555400d08010f0103881604416415a024041c1d841400c1c0b0000550103030910492502203a218100480400c018002524020341281039203410b050400c0b00b00d88550b5140a46900d80b228008603007020740040a483c0041ca260080100000d0100c03005034000041c1c17420b100b02400c0940039500d045181508038240404007408400c0b2290500c8500701001c2401b50f019101780c2801081940c444c0c00079900c0f01134030a0342d250072100400042011040d14800d1041030003004000915042003507000a240040ca50401e007500d0b0007110340c42d0440c64041c42046400d8100307402a0996840c11400544082e000030004000c0c40302c1c00f40080c3c500b5115008075000f8503401803800e1012626030a00900c480d10118080b1000011441e031070205203080401490b1051081c001086001c5001c100030300b00d104064017450002420340343d40c1d00051124000d481d80d03141a484040c4420785018090007214445520100500c1030001c0148030740c80c0d0120403201541d4000f42c080ba80c90042d102166031520a045 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 744810422 1250 744809172 744809201
    0x20a0216090905070803030f010302040f0f020c010608071505030a1815240308030411030f101a0d0510021c1b272d0b040e090606010c0303090204 64
    0x401241d980426400a00080d005030210f0340540d44984409035644401e5484020004454004100524141c1c108111380c1c1700941d008510703401f41251900c181d80102c0c001e514540d4461006003c15042008010001d0100098140e2000f40c4420301804030312021b00410035150700c80096031b01040e007022311014141e5106090480311041288144001c0003001444240b58944034980300c60074051840f09000d0f81d401805080c51501c9a6a0b15004158018046900342c0180312482c00d08920601540ca00d01c0c803e0500800c6e01c1c06480b030090711f004004644248504042283c85021130380008400400e1522010700581d2403910350540740c0c1484800040d42c036801c1c01c00c40540d00300813510309100e001440d561900b122120800580210f14050b071440103c100140344010401180e490504c2c0552420042406582c0c1c0386003e02c4038881d00f451f4202114129000a041001c0c0c2c25608445038040d22030320250005003080e80008110035a03000e4090101601c82540d68255500c90b48210302d06000707203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 744811672 1250 744810422 744810463
    0x6060901080a060e0907060318020a06180b16060506100f1b05060a0b040c03140604020a031d071503020c0a030509061b1b0102011b030e0a080a0503060a050f1003020a02 74
    0x400025071b02c000310f004005c0020b04010f00d141c0504034095601a159034018002d140c501e0515000b140c1103146114000c0092125034000180000303008000c003036900c00a203540205102904003001a60701c05081c46004075001d50008254940c00311240600700080e10300a00614130200110902c0c4c1d18030700c409001303030142c4400c0c00340d61421540518a0107400f5a4140459a10100c081e81126480e038603004011140c50002901490a54010401e04040d810000780d810801088000c0c2500385110746c290f030b40c1c0701003c1840000890b11640321500354514007940f908803c0c03e0000e4035030b01614002424031030080352030041503640b04d060390f1a4103486411000208214a110707a52440c0035a450b524000a03c0d00c0742085520600981ca0142510740800103545440358086005103a81100c0c041140508000000040d00000c000e0a000026603909502d9003005005c100340c10040f41e001e64854600406540c600340c55032006001051528100140c460a02d0701060b4240000d8035210f68040e11036 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 744812922 1250 744811672 744811681
    0x3120f07090812070b13030210020f13181521080708070b070f030e0705090604090203030403030302210402131a12070801060806010819111017060906060901080a060e 73
    0x4081c084c161480c0070f103c4071881e98030303180e0395a0500e0803a014040d0058000c03640c40c4203951038503001008010070b981c1c0c078a4901540c01b0f40300180000300f50040e42400c90382c0180d1848800003409920044941d52056410680c5071102d545e646ca4040319050b880340c21000196420300140c181900c2004d0381041c1519556403051400c0350b45100f0845004010600842e00710740307454800d1068280c0c400c64000140503050034441040382c07007400145001c0d405520740c810f000040e202070003d0401544681c9015807a071400241c00305800502c13064086c07038404120700708009607803090004803814900007000511900c4106c4043c00100f0150b8040b500305a480b42c2c054124640041c500c82201c2498008111142d01d441002da1503140030310444020703501c001000c003c60060018200b42e1548070320a02d607410356030480800c000440380d41c1c00e000818010130690241845907400d107580424110b130000210300e840270004509001e00000c0745e042080c0c400000d080300c0c1c0b490340604003030200840701c1c480c01d191 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 744814172 1250 744812922 744812953
    0x609020a0b03012c06030a030309020a0b0703020d03180b340c020f0a031208070c150b010201140c0d0e0a210f02121204050c150d0b010203120f070908 66
    0xb0706110540425466904425038403040352205d0041c400100a094a0074998404601400c007452003641e02103607100000074014503040013031004601c00c5e00504101040c11101404a0b00000c402c45e400041805941001940302c00e0001e50201c81501d24811240d408554200c071003000c44442e1149030740202203003900c0ea03000100c2c0c0c0ba9491089900c9600018088180140561607101c01131402010040d6100c4c1580144d030440c0c1d000840380717400881411107440c0c1040c03c144001d0782d20503141c0d40303a2011802d96420b0207642c44054140341c05294509140d2502119441340300d40444806a55544488000c403090007124407498000150411291440600c90401d48504030034001003009201082c0110307001189601403503003000d02c6907007403400f00f04941148150080080f03075240114107401c0d00350359691111013008402900b20341c0d200c04034851400c0c01c4030307140041181594030903c2102941c040c80c1100592224003034581080581f0307008010b0303691008642000c0b025000d148d144405404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 744815422 1250 744814172 744814199
    0x9070e0a0e0f0322080c040b031009061b0302030412140c030f12090601060203040303080c0705010c1107060e0307090b041e14010b0301080a2006040602150c0f070609020a0b0301 78
    0x1ca44c02088800a5101c884240c0300c20071510400400390080c408041c1e00340b42a030b00200d40901c1c06029191400c01880302c080440300c00003412254143c0c0c0d0800309811240703072040c02c104524981803c51a506042e100c0c0541481141a26000c1044a20400c0070180200b41507480c80406107080347d1b120078185503c0c02d44c035080222204001c0301e041c00054060307070f00005e01504031803194000d1031406045481c02c40d80d2200081021603d100700300b01d1100020340034030602c0003501007a51411662505001114180f0841398030401c00c02140003040d0070070380d1380410483c0841d241600d000401662210119024043d00c444000c000d00262007200d103440c1e2180c01804001c104168200240e07030300c1b20788030140342c00203004420b12076010740781c18000145441c44110360045200040030b1028040c80000301c640d409a0003850050704154500c40d040c002c0c44000766013018110340e105003480400c025090343c40c010b94101921250312103589405644a00340c040b000382003102110760b500e40c1c507081e007440c440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 744816672 1250 744815422 744815437
    0xf03070f1413020a0c1719081801061d1b0f03011409160e03070806161701030201020613110d030e03100b0109260a05010b0a080609070e0a0e0f03 64
    0x46290900121541c9060b00c04c54060340c0701074807189015145920381c0c9203032001c0802e100100d070711300700810f083c00164000342564400240e918100149010741805210341c4414140c12a01d0f030600c1000e0140c0c2c00c1038030452403041d0500d00d14004d140c3c0d503190603440420303901c0c41040d0700603c0021154500d03c40a00190b05850506120b01100301481080c0051648110380c2c070030509800170520b5088074403890440840c080c0080031901c145454400f5141083d0060365448403200c04441403160300c9070065005c0034543c8802003044c1c440e42c55a00086d403a02c4006050030105008840c0f52001c10076040c0c41003403042d13405070001ea4a0718462602802c801340d0400c2c418401d2194200c3d9864921060080408019069543c000c2c80d42c9020207000c03d8035003904105100074410300304d80a1900c0c04000d0141d0701c42c014000030808a01100520452004941082c1d516801100820420800001d10f0904075034450b41c0c2d83d882c0340c1d242910f080062429907a01c903018081c102141209080000180011 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 744817922 1250 744816672 744816679
    0x406030c0f0512012d0905060f030a0804060807050d05011202120c150c0a0204090602180306150603070905120f0c12070b0705070e040812060f06090f03070f14 70
    0x4040d0081c0c03054a2a004020300c800c0c80700d030620018050300c00d54002d2051a100a4803100212a290003520602451603402140308a5500e03000c00215152010a07100980001e4014100c107a90f01d03200c03a100d512490080070180142032000ca02c40510960444105088800042007156190a03080290150f6600d0a0303214010408000042000c00b181c1e4590140780104641030440c0f0402680101c0c2d00300c243c40c010b00d40103900551000d41c41e20300599040c00e102d4580182d0b02c2500a12500c1000014180940031394040c60801c81e03154601e10000c890040116989500c0c3d03914041c045507041905d400c41600542c0701e0b0240c2c400150b0004291000c4451306c410f80d100c5c000c1c09020700943c03a100c3d03451200c29a2107101e0070004003403080000c050280c003c9090360071007615880f01c072082d04400d072421142e414000035071803101d01c04504103d80002c004c80d00d600b2401d0b907600c00a0001d0041810151240d5020a52421181e4080001e68000c01c8401001e8040b03c0d41c8088881c106005004040e01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 744819172 1250 744817922 744817937
    0x90702010e0c0117060904080c160312050304050a14160b09040b0108090a0f05151f09051e100806070e18060a03080a0207081f141605070f02060406030c 67
    0x1980030300310004248045444d8503c4564440080280095024105566059003040700c5c22481000b840f200284000d11051200d0b468514a003c0d01c804107098481802c1202c2402403100081c0042100400ca9401c0300c0c54200c285299120542001c1c031038110f400c0304440655000a0204501c405000b81c510112401c0110080c22801510b00500840351803103260030100c0884001241c4420988800d0f004104940007080e016500a184c1d020644800e14241d640700b0800080100035040c0303902900c04a207052001341018000115080004d40f450650040c030f40c40050040e4a414402800520340c600803280c050a004c100646a002e5051100c0c0c020718001444801180f0b500302c00310301800020709006205840c645400010b07800010040086014560000443ca075041002444000e88101c4a039800f071036000e52081290103810403a101c41d44078100700300606031a980c1e105040d41183c103106544d1406481c0040c0145111800207501400114000c0740742981540881c020507980d40781d00c0ca = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 744820422 1250 744819172 744819193
    0x40f06030c030e070510120f0903360b09030f0a0803011805010810021e0301030501140a18170405180f07110604021908030c010506040513050705040515090702010e 72
    0x548840480c060250042d1906c3c45d2224110710812020a4001c1440310010300603600990100a80b9142103003540050030b080543d074448031031240507018070310700d0300340811108218650710984c140702c91295420794030010583c622252420b0003c80c0d110700382d070410388207110036910700390030960000c1c05400307030303417102d170228103c01c60910b10070581a10355010050031643d0007082c0c000003030b52000003910303e46030100f44d003d00c542c1040350185018500c91f100200340c1c0303172210612004419000b004007200754100300624080c1142d42c615210b210740c10041101d0424a4541d640c3c0641c4680e501558010341c1d0303494000c56032002024040d020f100c0300000c0d0016500c0e00345088079400c003901000212a000320010500501c0c0102c07512000c1140424103005565442d0421303030031500120b03c0ea20380c03651603001b0041d0342c0c41c01d0702c500d507031000200da08000601c089840f402c0e41ca070003501881e80101c0c3e403800410301020741291500200740000f4402545031030940802400381c082001d85440034400c440802 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 744821672 1250 744820422 744820451
    0x80a120e030406140313050303071e0e0904170f040b07060506060a120b010e04050c03070228080d0e0d02490c060c0f09080111041a040f06030c03 64
    0x140c049074000d07503d032130345903818140c54240c1e588003030700c46035035034031401040000104144050346c82021075445820307040400c0030b00036072004a207a00c074104003c0c0340460540b4540e51080503d400c99000501007200d001c5100a01c15113102c1c0c1c44030181c0040300400d0000d4031035540b00052503800d108060510068443c941840700740c0c010440d001000c507002011070050103e2940c807280711540e05162080f11256020f02090450703c0940f45805c2c0c9800c00410032520f20740401424203c000d51810054000510174203c1c01095442c420040450300e0000c1d2405481403035402441503540c05100355501046c1e81440030351784e81204294800b201ca00c4689040d010151003224200700100359500031a0583c0341d8103d82c80c0e005507034140c00c0500030250381e6000414650b10416134243c50b2034544101102c0c05000c0900010040d40c81400c10713a04144140410450030401e8800b00e0b406030407030a06165001a83c0030150180f900f08080c01c100903d80010425415044664003428a8030108058868038885 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 744822922 1250 744821672 744821677
    0x15010c140703060e0a14190818060301030f05010e060c250c270e0a030c0f0c0801020a1209021003151a13080f0a150b0402180102060612070311010507080a120e03 71
    0x190b907007c1c9074021003040030880000051140213030101d4504000516074000400a8000b030304169a4498816010710405c0740910400d098000c50a0040029160400d007021042c07040f890f10b46c581d0b45040003285603c440100007881e240783d11030844100a51104004c000120f50b40f85205001d40305003c40e0000304803240305203100c08200a01a04100c00140c9040c0ca00113001c40c4100d40040c0b070030003c000481e40b645085000340040e02c1c0090f82c1c4100308074006110320f5010010644551401c0030305401179484181d2a03540001500300844d00000381c1c110090154807a5000e0368400c24590045640200401e0041c002074085248540030f00751100c4815507202d50201c06800c407544880e101c0c00114581602280e002c60140c200441c0d5034000320081016604010072690001c0082c03076420010390307018020164049000d4500d100c0503034510004590790100c1d403001804038011070640341c5050748954122660320707400c00d0a0a981d010001c000500310082804201c20071032a2001280c0034403408401c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 744824172 1250 744822922 744822943
    0x20306100e16050909070903021302040608190b090c040501140906030a0b2818050c03180a0c031a0709060225080d051215010c140703060e0a14 63
    0x42215982c400707000b82a52050340c00440180700f000d00400819135250f0548911a035001e80d15100c1380352451050100324800003824000340c0380140001d000e1140d115502c0c641c456201140e041c42c0b04014150540209078030031541c3d821980c1c82c02040743c0701055400901c2198002e0303a0b20400b15500c1c400f107004d140030703100a1560040d010004502034915507044151800c0c030060221000d500c5801c2410a00c89240592116000c0088002c002d01d074103c00040c1c0030140000810f00283c0740c6400e01c040c0703900c0020a0440c40010030300342d00e540d03600c1c20090360007990703172002d45460000d48034105010720f01c0003042801d964440b01000500c01074866281002250190340042032803207154200c0303030024000c4120f0702c00011100100002c00320020001c1a0704a1047d03215642e4800c034540b28034410b2000185501c1415460004002540c0d038071031090203011b0340003252480105070001c0f8140c202000c5a0014100509114030001d0443c002300c2d40c0e440c01440b80c12084c1c518802900000d894191955 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 744825422 1250 744824172 744824189
    0x607200604021503060f0603011e1505040b0705010b0a090504110102010c050414011209030e0901091503023618060f0f07020a20040b0303031306021c06030b0402030610 74
    0xf5014404240c10f07801075504484020311403189000180c02040c0503400907405910084d41c0640c110607010b100c0344806000d4001c4113502143c400800a029242e4402c91141000c0304200207031000510500703601020112400a0990001640d505508005460291821349040e0300081455603258014810f02c0d001d541c09480d86030419240080000c2c1e41004421707406e041c01078108091030884864810f409140d4403076255003101b030084005100440005800c00c140c2e003858041460282e0b09038414a41c100c0307904035045000d41901c485464056800308180881040600340c1c800d0840e600c43d41e62510800e4900d01d031400c0701012043c01c0395681c00030785000c249a1308c05c3d404207000b5515a4011a88030526004480040e0307919552209094211660400909084e032103d0090386400d004d0784445040440085082d800c0c90900d1f41c07141c100100005000710b030f0000c1c0000400f05090210316a10080501c00c21090381c1d24203014035012400c035400c9220f80582000500e2400b274030100003081c0d0300380741c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 744826672 1250 744825422 744825439
    0x5040507020307020f240706021e030702030d02030a020f0c060910020f0313060912020c010906170a0c020c1801030c080111031b07020a061110110921060720060402 72
    0x52001285207071b1005030410404442c0320006441010003000560b210341c0c00140c1e035404882d68508240303002d0b85003200c43c039010824403500035030010030b51780102d401140041c1d50351146996200240300d051b030030074015071010580c10501000030070014400c146240c00d943c914580e1181d040220b100e0469408140c220038404030300080c5152048110441c803c2600080c5103441f1307100c1c41408464846408010b0340464002ea074256440244a40281070b14100790b00000034a50140e04001c000801900d09030740e0b20030455106901c03c01c13013403002c000003500812000c03181c0c10100758840d000b40400c2da000c07004000c00162013001403250711141d50344442214119160742c0070318145c6807442c100441c150441071011802580e92020b165000b00b1140e180e848660034520411820415814400481a803a000488503e000e0101c120390082c03404480c012400c4408091080e00c0c200790704140e600c5480f900c4108010150003200c00d42c07402c0d03401d8241542c107000d003803d11551460110340007074010010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 744827922 1250 744826672 744826699
    0x10e13030c02030c060f031509161b1b05010201051005010503041b0b160b07030c0228050709290109060503060f0409200108010f0501110718060504050702030702 71
    0x242a00740491480101590300d40410306000904070b4101081248021000005220b00b02090341e601c1045420182c4101c075041c42d08000420344250702e08000014044064100d400075107101c4036107408039910a481c40300c0190000300e2684510f0003402210301641c0f8150216400042400001080b5541603481c00c1c51540c80f60b548849144410301001c040400c121008251142200c02178a14008845504100340760b0303d0503d2020303110045c2c501d07800c0c5460301e01320009455022403d80d02c10b6a42c440a00c1c040e060707148504148410001c006000c6010702c000c082141c50164107d0394800e030003c44000c0c003a400010107241d2000b06840c3c15808114011030400c8a00d004030f0155070710090052640d041c034400f440102d000e0354100e00c0c2c00c452401d0446401080c40c0c510b81c00002c81c8600c20f28029883c2d60610701d2001c000031080c010340303060103050b40e82a01c40030300c100305940141410102d030b1041a03d0307100125003e0881e9000d0b4901c1182030034005802c0c14400800d80c0c071680e40003130001307011554 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 744829172 1250 744827922 744827927
    0xa1410091d03070605040606060302090d0803090a05160305060f01060807030902040e160501140703020303060409020d0c0312021b011b02131107020913050607081e0702060906010e1303 81
    0x55541921181100101c8945540609102400d4582e00030a000308841c5886d260160848815410204c203061040c88424902c1e1500a0204166607008121551302d03117480c4600c3e4070300809e40714010520b00c540c1d29070051000d00c00b00203804a034880c1d0f0072241603445090b412181c0c400d00b402241c000444090000c0d8126101c0e8101c02038690000d41b0000e43c0c400c40307080c91400c2141e4955158240c0185040800c090350b840114244070000400081d400c0007540e5030003d44a01c406000350b0312483e03c94036480103654455404070060341c0d04c0054014241c1e41c030f00d041308080103019a21000b60040d21f56840d151103003580e40508040050350f6440604807003c10041030940680700c244c1e00101c411100084c604084e100da03202c0c000e400c00095440b0103842c410414054801044454002604000e00c40098000610b85070400001e0510040a13550140c00c00f441c044c00031550540307060035005010704030742c021a080b4014040d9900742d60345a83c803080e55012a81003542e400e0f41802d010001480400c0c0b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 744830422 1250 744829172 744829181
    0x9020f0607120c17070b060118050319020a08030c0a15330b0a20010c0509011101090501111b0a020609010f0509030f1c0206100306020903031209060a141009 69
    0xa1258101d1003a400d08138840395020380094208a40200382c06040c001d0035a0428004207010404411030340d401403e000200344c407124609a0280c004d030a49040c8404c40d512070401d50050440350040326200c09049107101d0742c40044403015540c11007170144211000d02c0310f002c1c07044802d940006940b1000103611440d4004a03100c54400d2941e00f10000110b6800c0c40c0038001d201e802056900e10000f08021082441107061206180b0f50341da14014080e04603542002c16100034030824200080d11098042c3c0044c09042241d8004105510345035070040e011038418082c02c0417600b840b200b541140c80d4070360015900c1e00c8141c8007940c000c1c01800380226562045150b4003420110b0301c0d1060901841201003898147c4108005445801c00400c0744510400d00b81914241c04461001741294204020705117040c01c9140006000107030000744140c0c01c0d4038100304451500081d414540e640307240403500c503078542d02c01f079860016150803c5043c0c80492400001503001c1c414801e520140a4906102c480080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 744831672 1250 744830422 744830447
    0x9040b1503010c020c0a0905011a0c0a05120a0306080d2703020a0e2a030106050f09090a0504151a0603060a17160905070c060c02010209040f09020f060712 68
    0x103900c4940200162020701500c2c190000326001085003105040800040c64000e4108980d41403074a030040140082c045a52045014000c528a036150710307125005041000048003d00148503e941341c00c09844a43d005044409641ea01000b5580d11a403a0641b0740e1945201c0100182e00040c01040c801401d50b5403006000c84c9844401030540d9a60114142a813560300c5500e540c1084000c000d9040c100d203000070702c1c0c01da0421002e092044012903040030b502040c060001000340105d8920034500f8a04122183d0200040454540346011007030040940b901311801c41d1410032880c00c02070441d085008103203110341461364800101c00c103942407211640000303007810390140300701c400015400302c110038002d0704002ca03101500c1420300c4d40301700d0116841c80d0b900882d4110b1500003000b12156014625104183e440480030824100c2c0c26403c03400780c00380039440c0354454907060344000c9072242036100e0401c191090f12403110030600d04081010ba4000e8034005000004170340d03041100140b1822156a04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 744832922 1250 744831672 744831691
    0x13180e030703031a12030d050a020304020907230f1b01020309120306030304050a1d07170106050a0e030607030f0e2d0708010f0c0e12120a02010605100c1a040209040b 73
    0x138800700300040031140c42d445400d03581d0f00300054014200c2c1e0540035a69101c684010158914105035010400c402001406002000811103400038000309000d151001d10320340d408481d440c0e014081e18030509a1004070015110784440d0b0713501c410410113000ba64440e080840c003501035680c04828189040c2c1c0018041c0394075000030003011885543d8032603800d01800d4918501000e0705502c5114100010010307001d01c1c14401200b9408442c503144013101410758100b4900aa00c03084020b82c01e0764509259010340750316024220822040c4e0383d01d940f1a0a81030001e840170701c1400d10007940251111800d5500b440207180ca20150049180e03070148200c0d0b01c2c04450122925103a031884c2850855100042d00c2c42d0181e119240000302e10307408108414480704c200d6103804020004131a00d07035180b4030100c43d4684041d01058258a1078000c0d0f002c003004050290002800701c4603a14003c019013803080045078a540402a1503a01221010000c1d11a81d07000d0905015519583c0b2440c515000c010310035200c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 744834172 1250 744832922 744832961
    0x10051209010221040f020103020a03180308070f1103070809030a202d130e07080109120503100e1005220c0e010206060d080c0313180e03070303 63
    0xaa148200022842040a0303400140c0b80c0d41c0080ca01c650b2001c411035016060411081440b0118604601d0f400041e542428010790700d4114038800d90140c40c07052481b8851004003101d001c141500300d0506032086046507141e49000b40341e50301c1074402c0c1d40304c0c00520b09154024040e000003d00603000904035a1002401c0f200e1821306ca9441c62119120000c5180380c10325000200c009504099510300f5403c80c04c5861075141c46424010488801040d102162007244500720784900c100740c0740c4c40107020a0403102580d42c240e40b0713104200d010f042c0601d011250313545d00032500d03d2243e1180050301e0042c2100d6100344040d51815012403011840900203803825481400009041e543e400b08040b0400285008040300101e6240000200e4103050b04d4035040c401016680010340c0e9011503030a90102c030031902806105800d0a008040d0b0003400884110f0b840009900200c14405d83d00410460b050540307801001c0f0180d41e218410380e1540075002e00c190b802840101d001a019401c041109051140d6810 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 744835422 1250 744834172 744834187
    0xc090e0711190507060c051506040b03010c05070c1e030b09010f020a030c0e0a0b0d09080c0d050c010c090b03070e040906060b041e050a06120212041101020d0212091005 74
    0x281480d95008a000704004050b40300410401c3c00c0c0111001070285041c40800c10856807640340d250740440011141083d00b640006081e0b035111390010b8204603024000b000394400b2440c02420790341c03005000741c52480000d41700040b521800083c03c2e020491018801aa940c0b5580c1c3e0342080c480013800c100000d5481306030b102e5001c219840642100c003107564004c40c49540711900640014010300f01c180c05550001c600f80700340204031080f111303401001d410008e0491918101750466004200b6013029034065000c00c00300455104006e45100300701c05008100c10000c180013514481c1407485031822010301800010040350040d4504011040c1c098804101c520a0f0f66801e003c9801d2508240108280802d0a0102c5c0f502c0b04640f43c0e4080005400480c40d5080400142404034a807282c6000c008210851411056550301520030101c101c0303400c020030f420a071611004c00c082e1194420f0040c4142080b42e030b0818030002e140d00d0b1502c11422114a4400304005000265024045440500c4400c00c16003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 744836672 1250 744835422 744835457
    0x10f12090f1a010b040b090a03020414010f0e011404050702210a1101020c0307060b0a030b04081b03090a090c02071d250e0d02040b0402120115030c090e07 68
    0x401005101d0528074458050a01c0c1424411480440103011a000703640103200304901c0904607025594603881c0c2549a041e01000201501d07800c0c0c1000f50010b040c014103600148900d05041d050b150303d00c25040c1c0e05c94595502c030300e07040d10920500304404400380410340141065404140c0020701881544d4800b95400c18050b0303480030400c0040b44680001035508001079014410101071041c002c0290302e066078280704a643c90003007a41c0907007101e9541040311095510340303846900540e8407840e541c5440c98079007042c0000d50400c0c542d02411191414010200750750200481f50b10401c001c11034240641480c0380c010040c003e020134a42544070b2808003080d03281d45120314451740d41c100319a41800746081290802c180d89804c1090340b00e4000d81c90000b180713030b03008150170343d503140144c1c1d1892030940c20f400054007030200d240a15801610000b03406000000382034409040e9081d11040c00c0b107c81492004400b00c0c2c000f22440c10015409040501000e0180e040b040d401103441d20f890180300003000c540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 744837922 1250 744836672 744836681
    0xf090409060c020a030806150717040e01080723130506040204120b250f05130b0703050c0607090807050603130218100506040e0609040c0305030309070303080123010f12 74
    0xc40c1c015034000013240c2c0815070701c070b00d006174411800d0751049166005100259264090308400400d540c003640302340b00c2115600303400e0f54024480c0e1554007a240d41d484050f40d48641082c000d244008281d10044010404850301800c0860400703016000c088904404410040038050314003680650200400190500c01c0c041c4c02425034000e2401201d94142060741034440500c0408500c8811040d041c0300c0b280c03a4020b09400000000e40c10070aa4550307a030340b842d00d201314586c1c10481e5a5840490031400381075000010b025511008411a0550344030940c040d50b41c01d6292040c1a51760780310501c18003450070070720099500612040700c000700740141940000d1a10300b035800780340d460204400410075064081480a0020241a1841443d00e402c2150103842d10800031301c040d000f00001800b041c100b2400850180095800030141c1c0d4490402c1c40009850300300502c0250000380302d030400411210014803065078501c1c80c00705100303a582202001074030002c1c0d200c4404001d101242c952400d01001d10f019 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 744839172 1250 744837922 744837941
    0x120a0209010605090310051b0a170705040608243c15030709210606060f091a0301032d060516021b0f030717060a0b0d080f09040906 58
    0x143c003915201c800080c1403408807002d050300b2819042c4824000c10407040e17000f51300f8000c4c401708183c1e51401920b4040e0707686188040c8115807121720340200003400703900002a0041d00d1843c1e07182e01d002d40321010303101c003000042c00642c0707030300718642c003401c04180381031244000300e81c0031084801010303254400c541441038115410b260741d84c4511510440c1a15260103d59020302c02d5081c10b41c11800c0c0420010044200f130300481038045040d640030800c550700799012000e140d900001c24041e00c0e440c0c110042002071421240008a2801e1901045108524414144a900c803542d02400c6038a180c641001c07461411600141c032201a5002c803285050440c070004450340109000f10345400c0000f404550540c00d01801d4045402040032039007141a64a0241403500c4102c0d650360a24124400081c1080160744c85000080711083d1094071215001c00d1040c454110710310b040001ca84414107000c00040e0b0410024002441000100c0000321120b010301402200584001f9541c4007656070380c000c40c0c0d103514 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 744840422 1250 744839172 744839177
    0x30f040503010510060e0402090f060d060e01050114030a18050d0923030d0f1101020c070503250b0307140d0b040e19060e010b0a0e090d030b0105030105120a02090106 73
    0x80a2125040074091030390000080410b034851945809030041c581e5118404240c89650006040c01d41c0c1d03a0780c0c411170103a0b6040102407031b64501c0e04055a1006181078070840101410001c000a920340c0a0a0524004c01407480800d00d10740c0c450301c00c2c8004103000b1580440203050114005c0204104000d85022803400d51941c440c2c0604080c0300d1340b40340191004d04922181c0040c1c8590007610f01298942d00500141810480501802005e44111000f44075083d80f541c40031400c501c030300400040404c200e07070055003620502c140303d01c00108661440d002940d9180c01c0c508040121180c104003c1d50300001c2c2d441d16180205049040000700c0d806141100c40450300c902c001e05861601c1c1c410301d40c00411030002000e42c4d1004800f03071004904880005070405503154002c0100c80804c2d00200e1b08810014480e40299884191180c0740100076142c480607441a910700b00381c11400703885400302000c4140c66480c1140e02c4c00c0c0c10440c95121500c1000080d010b04002240181c070b4601c0100e01031300494 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 744841672 1250 744840422 744840427
    0xc0209130210030e0c0123160b0c090d11042a2303040f0309120c15180b0d060302090403020d11070e04120c1203050603100522080f0c1c081510020708030f 68
    0x5027420a40d003400a048085030b01030070411505207075602e502c0030402c203620209085032f0140c040001402400c0d210041c2c4492010368101d0118842c003141c0035a869034094170703030000070b444c2d401e83d0441c400b1620301c030502d107070704100080380201d00404076400800380f0a02e8001412038030b818200e45d003661030303000844160548a4061002c4e50b880080c80720505001e10b44142c0001082d100ea02c0080300e14481e40031300260000390102c9800c4a03801c0346000d0742c1c0151284420381041c2c54000d40e620000350203640001e0382c130341e10354104032808200c2000301c95941c240305805446070348034440071a890386283c4007444044100d40001807207424000d14404ca503030720700203a1494204103050400d051805118642e038602420401c40e544980340c448800c2e10300f007a860000d02224903010b4014840c40103c00e04000000c5441e00340d02e180000d8901c00000300c440304d54a41102d1721810f898031141075840083c416030541c00c00c0040d0800041104c000c40003441199200e40d51a0b55150442d07100307030b5020000c2c40c1c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 744842922 1250 744841672 744841717
    0x110a1e03030f110a0303020903010b03030f090103051008070306110918010f1e09091403030f040204060e1608040204200316230a0c0209130210030e0c0123 68
    0x1400b072516030601400d007192491045119191900f5062100070103141e40461b0040117034409500420040001030101e039629110200b5210140c1c110560700390021b03040000282c03040e07440401440849100340020300c1400c0c1903a170784e20080d003100c1c104000f0101d402d00c0707443c82c1e03540c40040f10111860511305d00d00c020750512410b580d9420513030308120744140941c91501e203080500201c0d6011180c03c0c90f07000484003c18a0b1142b82c404100d4203100c0c40c0d100c080b081c050704450824509001724401c403002c1000a948904018000c034044402c1c0c2c0b0703214482c00740310000e90700494010354030510003040000c0b0030f05201046406030b0b0301c0c4100d4070100c03107002c010403201048000009080a001e0706080c07405c080c40c902c6211404040a01404952102099201495005407840c62619070b00030500038080c500242c8800c14641c4a54040c2d1083c2c414080d0341c10501d000b4030500840c0d003101c1c0045c040c040e424000640c0d10b6103465840600e0080c100d030603e050307106454040e00d0381c04410850791398242c24 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 744844172 1250 744842922 744842927
    0x30b091906060e1014070803010e18150718050303211f1203030608030a08070f0906050d0b0d1406040201020714061e0c0604030e010327110a1e0303 65
    0x201e507003060080c4a00100d541680d652001840008801c2c1d07490144400c00c035603068140c40740125580104151004000420300c407841d0161984509840708154010400d83d5000c140e131114443e160300c8828280700041004c151240c507804200d21100040c00740b1302992440031138030750381c060b200d01e07a00314000000144c402880c06100540002c5803403c800b407650450a0380c10081c0e45140301d062107440045e1003c000305070187c1c100000421040050701d480e042008000341a001d401c41704200010580544144030b54000c04201068a206945550400844800d5403000f4550704403c40c0c4d00005400c00303040013629000d00c20a10780b415002030300e400c0c1001c1c40003900d8034004d17400c60241814498440001a120801500c006103042c1d1200402e544180d00c03402944d1003400c81031100da015080c10041419080050003054600c2a42c041204000414414030503e0b415003c1060518004c90460302080c40300000d82000c1070002c20100085503070300013541400504801d000d142d0640c40808209254 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 744845422 1250 744844172 744844181
    0x50d0305060f0d0b010b0304020d0609230d1722050d0e0a0b030a020a090503011d07151d030102210a180503070b071b05010e10020a021507030b0919 65
    0xc0094039803040180441e80e56031310081050141c1054104040005010341d55107400a400898010600300030850542c184828610302038250755401d020b4440c1e0424210360000307001010450301e9502d17518498034000317100d010110084c184134080040c084164500402540128007000c0c4104002d161032030324080b01800c105400c100c103522502940c481003050040071011a80d00010041c80181c0d502041340381a074810030f85400c501d400d50318001154007511071030000c400c3c100c0c0702c01d003c81c1d101542d0307039840903042907100c40e00c040002c440c00140d02d11100b1b2210000c000f4100100007505010000540300c120440f07140401982c5045c1100b40b11801d4210320603070540b41c05807035040ea1a00020b032115a502d00c940c1c070300205000b0344175000541481c480c0314600e1811103a8140c5244206c82c034100580642444c1040f81d0140c081c43c210200c0042d140c0c821035014542daa005400d1a403990b51005d4404500200120705040d125410342465a41741c4000b5840b84102514180d080b01d0052842c1c0c1c03c07203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 744846672 1250 744845422 744845449
    0x304081f060510030b0d0819110606031504140319170c04030201051b0f010c1b030f051e03010b07140601030804140301020c0a030c050d080412030e0a050d030506 71
    0x300d18000007880140c95407440c540f4808000e0802245050120000c03500c0800201e40140078040041074182c0100c0d5200e00c144815082603403010800341200c102d1780d031200400d03221160705900400d10000642d002092160b0300a010303081d901d006414100006040d40e0184601405200d0b400088028181d0020444011840ca4404041842ca403ca143c059180300300e0002a040c89000b2030300c0303541040c0d01c11901036140849026103655881002015020b410481d80040106c2e008100c0c9602d0b40c1115640d02c907110fa050360f1a1010210080816103c1d9030015851503244003043c1940468090110002c6009101c9003140344d5803031165007801205044034003c04007064111100410100d07244c3da0a6030203460075400340ca4500510800002d0081c80354007148034a078086c6460480030b254000e503d00c00c201d80584156698424110812503560070304440c01004144004801c0036514030a078041c042c4554aa401c0b40c00e89800e50311220b02e0249602151000a9169010001d050406042d81e1241 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 744847922 1250 744846672 744846733
    0x70e0108010902070b1b1b160b180103020f0408120910110a1502130b6601091e020d0b070e060d05040308130b13050c03030408 56
    0x14030466039500e0300c030707400c010b0106c05400c0d41c0c1c03001084415003004c044134140e640810390810544003180301e43c1e0701c2e0381d0016800500d40c0c019007030019080001c182142c400c50340c1c4030400b00030300e010704c00103500035001903c810514102c144008142c00a04019140036102e4107110385864580c1c06040203c07016420300610200103909410b204d0411000a009804d107034002040406c584000b80104001c0c040c1c512a64a005044070780001c0314000b8000410032031000d1003080c42800943c1601480040800d01d030400065001604048180090007803620382e507490b000c0b0021207540d0086000c2040c00e8030300160f00c06075560b18000d030402007100005644212041040090b09201e0b8002032000c050140c40600b406007c0800124141e108114000c007020300100915110600d5098100040078103d80031400700b890000403407440303600ba070150301400d035000d0a07018050b61501803808501d822550300b16520b00c15110b85007101e030b40910280015203240402040c92030041c42448400f0303902280d00101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 744849172 1250 744847922 744847927
    0x90519080a08180a0e13140d0c0203010b010f080f060f0d0803191104050603090709020310080c0f0d11040b120309090c07020102070b2206053001061d0306070e0108010902 75
    0x350003c90215035006c541c000d04550881a00d0904882e40c404404c1c481c08107014903460841c84075001f1007a03c100d10700a4008008400c558001501d09100f2400241c0c0450b8800d40028040ea0301944000c1c0c0c410030140000c6080001c000c0443d4083d9100703201164114000b2041006444241c500000e0014031200c1c240003909110f4080e4516100d40d00408d401341c14000000390030f50800f040b5070001018848011903881c50401154075600704a0700486c80d04e8001c0300781c41d000c1d0f40f030527115054085100810700c44003024141d550440c2020110362694101e9255040c00e445640c030020362003c00405203000d10368464440301007090b1450000c048042100003130248c0c1c1c4c00b50f40c0c0081d00c0b41c103513034542e048556240c40703c1c0d000d07402e01c94480103100380000d0940c00100750342d940000a05140c0c1c41344c4620251039502000c6048000d250308404526915407000100a51032243d00600c8010b0240d0107003003280c0300c0d61800700f0b0808008655000104903a0304a0075203950b4003401460042c00701040450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 744850422 1250 744849172 744849179
    0x902040b1e0402070c210506010603060806070507020f1801050a0509090d0f17160908031602300303092e0b1503090601170d090519080a08180a 63
    0x4105010070041402180e01291110402025080d0100a00540c1d16171020705020907019281c0440040070888080c050480002000350180c02800d041e2040030000e02031a540320a42100ca51b04618000d030b03880301301800100c0d07031600c58107100c01045401c02074542956060406101208515602c11405040308a08000c050640443c011000c440d1502d00b80d0052111240121400d500c400583d00b840403501c400e100e0401d03001c5400400c10a469140c0519450b5100c070b45a03103c1c080da10100141c1c00c420b240b40b0380180382c5031460088110210b203000a0540c44034140700c003559040da0b54199036500000074007070058010800d084c0c41d0720369900c030424641c000009400f031000c1d10541104900da222403501c0c190350303298a42165181c4204c0d05981e120310301810166601e80c020300c14a40c10014100140302c12040c049000c80340107419482d503925962418080c482e641034080d02505860402c2e80001ca5001400d2000005650041c40c0d05501c408600b04c00c80014040000424841c1c24003007000c2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 744851672 1250 744850422 744850459
    0x140a06150806060d09021f0f030b031507030213090e01061a04090c0e09090309090903190806040b030307081c021615090b0106110c0405040305030112060f0c030902040b 74
    0x158040b00a8030807546888155150343c0240030340f0030000358040305001c0c0c00ba81c0320410110010342c220180c3d5070740d61101f801c41001d44c200c5024198130b40e007640010464010081c43c800310705130130045910700180f41c1a40044411109000d40c0c1103894036649404601c20030547c24014480904400300d241c0002440192555401c2c1c03003035101d0200380c15110300400344c0041c0a214401005c200141600340645000320381e0036107a60104083c54880e41c12a804540450400000e0315030400d54145090314407011160306403a46180203280e96881504c80c1290380f41e03501c042c03000c4c2200510402c0c0d03c90b180ca81051414644000c504103400720a441030051200e01d00d0040501c03590780c0d0700603680409442550742c000018068192002c0c0441440310000a8516482a20b0f2200031104c0c2c0181c40000c1c601c07800b004180c4e002520003070000350091005010102c1c01c842d101c01034a1007000c00003201310302c80d100c000968130b46650300400700f0f41d90415202581001c0c003500b10b11040c1110500302105045886 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 744852922 1250 744851672 744851687
    0x1050901051e100822030e280305030408060c1c020c2505031209031506031c050316020a0201020d1b0c030606050301111603051309140a0615 62
    0x22a441070040306503003030340010340c410403408100c07000d4081c0b40743c0440504007070400502503c12001c000000f101e102d0044614070701c01804117615603104500c46456404000700525a5100a910240c114000e11800300392414154021486480919160380c540415503040520050040348046020441000c1e0031800c040d070044440c10991006071168080041c0b02d1404021013114641044d4409018075103a1400b900d14007190002c80484003521070300408612140a80b00416130592300492648043d844070300300907540f0500243c100d8040d940390b81c0d140d0300f004083c8d469000c080341e000010f00101d1050701c000e203d440745007070004000200c103642c0000d46d1908034120581c10061212441105013031960070141103990030043c0c208072113032241040e17001402944942c52107907203410396404c040e41941007075035106414011081c80c51905524290340703580c8103001100a0030210700d00815515650312401c402015070000e5031085252903406102250305a81101400040c0130040712405a0311002c1c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 744854172 1250 744852922 744852929
    0x70807090504031e0e0a08010b06160618030302072120031b153603090405010303080906280b030304050a060f03050c03240d0204181a01050901 63
    0x1a055071181011144001c0412409500800d80749516504da940241102c40e00e00084a0310b1081c9641e6245c25400c80b40e034282a281c00c03040c1845001203000741c0210803003180b801070303401151440d4001c0e8030300150910365000300d0100b5800701d0001d00b44412044007400030780000c10211002d0501c241c0c09041071071404905410f114213200c0701c80440c04248142c4140c189030200740001403d48075030542e10b035000050390000d81441030000600241c80004403042d000d4640050142c0c2c0c150400c081051200510184103a80c13104000810850b00d50f0300c2294021030090352841d107203003004150b49003011009400244504c85000c01c1e01c4044510110700402c044802c0000240461144040380c218022548520750242d00850000f03141500a204405402c00b140e13810000c60ba40c901c03604c00c90b03003c01c0da09104641010281403d8610b90480741d142203407001002e2450340001680001c0643e41009003005a06000000d0b010030403c1c00b0188100c0d0700903681500c8030541c103010110340029070511 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 744855422 1250 744854172 744854189
    0xe0114010e040c02161712131224090605150105090d0c0b0c0601080d02010c090905040f060c050c0f011b36050a0e0f07030e0f06090a0b0702070807 65
    0x2115403070540c020481002c001c1c030030140007105c80341d503840000300022241402c010705019030b44000c022098440201c0705408410600c48a0160a1106101c0e0380030106004844041158030100c001c24050790210404100145010499180c03d14001e010350700098581c0e01150310000c005000eaa03048015038480240645011f4480400c6040440b100c84160f13100010079940029060340c0c07001c010030860305032262003044404844580108908891030490008009031003160140001c010030b82242d90040d000301282108206991150341c100c03441c030030700100401c00010b043d090b041d2046c80400c80382c034007910003001084503086044111001d1018144108400c20802650030a003540f00381035007050600d10303050803a01901e141a1041c54600401d807262501c40c000141c500441c03441d56218080d0303128040711030348544805078090070a6411480710f602800f04603554035030003080614450408040201106903103802d00d40c1c080c110250000045412482088c41030050002d040004c03180d055 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 744856672 1250 744855422 744855431
    0xe0f030304200d0b010308030a0f0e070515041211010311130509060612010b071a100816080d080415230c0403080a0e03101109120d020a0206070c0306150e0114010e04 73
    0xc02e00b1001800052b901902141c502403a80c00c5051000503100b0558000f034a4850102a4200022580e40140e00c1003000c0200c00700f0049001a0051504030201030042c10007140c0303404844055000c0b508a403102110b02601302400300141e241101103240c0082c41552101e103094081200d1241d1540c0500500c61140000144401001148940c40382d030080d43d0140b1030585d050408680e118901c0500c603103100d80c03154101126044855420800440e101d1200502111541200907079451400a0095800d0884002540000c01041c050440d083c44410300bd001c20446150105001c010098900001c0400c01c0c001803000035a01030448404641ca8105403070740b03000c00b4000030300c0e01c21719125102005040c00c509520404c0054003424000c40211a00180c1c40518074116985103041c010b4540140c1c085070301d01c00941041c50080452500480a440c0c1c115142e4a0780e0b1b050310b0b0350800103801391180003c04c2000708106041507000d082013101b080c2480512100080c010a0701d0181c1a11030b5684 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 744857922 1250 744856672 744856681
    0xa0c2a02040b060d060f0f080d1704030905090a0608010608030702030c150702030a030c140105070206071107170a032d050f0705100b03160b0d0e0f030304200d0b01030803 75
    0x100c105032031454818040502c17403540c0318010744504403000e1242c0040c80c4105000820320354008130303101e00080c82d180d580c0d404a1190548072800c4610180003503050116116010443e911174600f013510609040ca070214416140002c00d5085540319404186180c00078040140181d4012884d0203039503404039440c2580701780503071691069105401c002580340c0710300786010003019003000d0340303000141c050702d0381151506072108954247c650841c0c840b80103800003000103075910300076071402000b404074000700e58405407517410460150381401d071b00300c050381d0150441c041010b5110032660410384151258138805001c000410b800d44000b094400188100401c800f90982403e82c1540c03c81c58002084a2505004892180c0281540c01c0824001d000361015030b41a0305003c1da900341100c031303151f44041c41d00c0c04612122000b080701c4408007000c0c0c000c1084446500340200042d6014a0260807505071030a0205550015083c200e141c0a0082c2503d0000b20301164140820358110b0307811060303070783c0d5940e034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 744859172 1250 744857922 744857929
    0xc0206030a0c1101060e0a05060405060a0501030e0307020d051e070e010b03060414041203060801060e060d060b03070b0a030c030b030d14090a061107060c0b0703150506030a0c2a02040b 81
    0x1801c26882540ca445d5002a21098428032240965445082000a0307101d0308203100c1603400840b02213030440b40d080420232403940700b54401c0b403143c201901036034104007150340011101405d5603000c0c7c030980e019100303ca07003804006110414040444008010282c43c003840026100414800d2405480020000501340d40b0b49401119103c01181100b111a06e414541512403002040c01000028034019010411050511400703041e100101c000b81180c0c3d0b00d001c204203100907800022500399407240e40c4503030300d030324200040005042d1b82041c203074468a0001c4014211910782c01c0c02c40c101810444815410340340414000603003022031400c5420f03110403050b10b920a12643e1121500012000000201c040c1d0220000b12080030140903244a5030f9a0001141d02c025a0240680300e8034015011640c0c81d8007d81c0300e2211000304803502d40d80e0395606c0d000194550000ca40c1500b039035890707080740c22119a20905210b5804110218005400d103000a1001841d0001d04000e00841d600c2c44c0b603411310f0340c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 744860422 1250 744859172 744859187
    0x6090503040909080c0607050a2a06020f040905060904120e0d1509060e0a0302060112050c0301060b071e1707080d0f061503020f03040809040f09060b0f010c0206030a0c 74
    0x25600e0b00501c000c0c2d60524003103a60b64001100421140240e50100303130038074856000c54030088180e81c1c6250320700d11422145541d1301e2048001d080500b42100c107200000d08640080c00c0e400d41104505610303646054112000d9620080142d071041a4113800c20001031004a40300e42500d12515280e60170b8802200410440081c1020240019450042e86880520b141d0002c0107c18441c2c031050154081c400c0c0d489035110a030b0040100542c1108005000440b001e00141020a0080040300d0310700300c0c00c90100b42191499000b46200e000c0008103030741444030401040c0501c1c000b100c040b052002554a800c04020140151030040c100700003060b1003400440d5003030341c041d541e041c0010440800e143c40d44200070504c0344244602c0310b6107402c01d402c0c103501a10a440904400c100103c0c81c60703442c0c0c3d0350244a0b0340318803980e59125680d41c0c80000640030300e11602d03d110b442404c000520480b6002000f0030030318548045030421402c001c490b40140c84000c240da0300701c9021180456110183c410646100c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 744861672 1250 744860422 744860429
    0x80717090d05010510090501030c17100501091a06070b0117101b0f14071e060213051306060c0b040c0305160e0a0b030d0e0a0b07080d06050603130609050304 69
    0x607603503030091070611006600040c00b44001004554a0a90345c01c400780c2610424032000d010700700580c90401018107203a8042c40585140300580362410305a00d103080441700d00307030400154071355509580f043c008540c2d004031542c12411500c00342440e40540e11811850014001e0404801043e0708881c155003040240000800780c0c210140509190b210309800e0200c000b4882d20006004400e101c01050b01508a5010310100c0441180c80c1c079901d9202c41403980c1d00c240e82640103d00d1000b0b4000400c405101070181860541916980d0354a01070401119106584c1148880307890450100152034002c8040d03007416600c556041065070300c40c1000b00e0850050391014050707000b45032840c42c59522105041091b2512842c0145590b01c2d442d111104a850705461281c141d44030310070306190513004003403150450000500f400341d071681703d440080444d00305010448144001081103032004a80f809084003030203042e500c00b41145410201c8662540341604090322495a450302035090007030500131a00603 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 744862922 1250 744861672 744861679
    0x12a0e01030e030a0e1e01080c0705071502030c0106140a050d1106040e1602010501030305040512010b12150121150f021204061805030f1c0903020f071208071709 71
    0x49000d0904050440c0105100142c07164040400e82d46c04d4214100c1405554107042e592100786a4854003440720f60b910459041d981c504c201c0301e00044050000340303ca00a0581a8051525500256005d9094401a070066488110100d5603000a030700c802c0d05103800c031034040701d840f0000000b509143c0140184280b840f0381005000030007140e207241110956001d11072074110b494046c105140200d00b08c503000e00008000510403c800c020500c1c0119048aa5490781d400001369007040300b000403e01c400250380c03120103400403408000e440081d80c1c8030074018130f544609809102400f00400303990020b1a00000d204a8a03009000305ca00e0003540410400c14080c0811035403107600070121907c440d4115011600b90b070404aa20016182c070002040a0130350000044d814140e20012109103030300031841070300070810a600b0700c02c0311040500800710700500907000385c40d607081c02390282410f00e0010b0f00700318242d560085102000507068012600b82c0768102c8242c811034801c11151007074602ca80031006070b1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 744864172 1250 744862922 744862927
    0x3030b100504030309120201021b030c10110f07181e0213050a0b4306020703021203070e0904150510060206062d0613030b09012a0e01030e03 62
    0x10050700403004000382c1c0d0007070720751101550303507452000711041400800900507007092603060300f0f80c500c0c1903210702803503001000e881c8070f0f00688000c82c4192200e401004009215142001403e8a00380603503c000002000034086480c10314401c03410712055001e0105505640c1e00500d030303480f1030185026400301a450700075541c3e84200603032103080b54004e0241600c030341450070340003070680484000c68585600c50181510041004403e02c40303000380c0e00305a03840c1804102c0c480302d1003096140e0003c510a20030803005803a00810304000b40303414580e82d10b84140490400030300c0b400383c1d040318842003aa281100c5000159959240480500741e030b03180c11646041c02d1009103d911304031104001d050b542ca950888003555241010400c1c0044002c9041410f01407104444401865500380850000b04c090041450b160600c280302098103c107600a8585070510820300072000002c1c040c1d031a408001401101e040408040b0b080d1202601a10f43d4050140340d001000d45640241c201c2030000a10780140d0385c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 744865422 1250 744864172 744864199
    0xe010e04120504060804020d02030f0a0501050f0f010302090a0f1b0c050f03090f0f0f091e010609030b0c0a02010e030f0c0705150f0307030b0a03060b0108091c030903030b 75
    0x408402920100c0740a41400261541c140c807420a50b01101d030150b80f185450b4903580c080c803854001400050303815008204004904401c00c002c1c101d030080c4110000185440c255012015510005d440b804039940720000400c0544e8903155010b41044a40c2c100040f2808510105002007442ca1410515940c00306824036216401c02c1c01c4541c080d0058081d80c10150003903141a0322441144071180c0d0040d0054020301003414408102d410709103000c2e10044100700d00a0010301403940072100c50064280b141e0340c180c500301d0000c03485d03401400981001c1c25141d017555110080c0d030300010401c00b15658040f91107286540f00350030411036001c080c020f803039650260609600c02503109000c00c1055104110700040c00f41000e05420b0758011041c5241800c02d034000304039240c6644082c03d103104150300d82c0d500c4040c5580e1143e95000035445240300141110202e000034000c004024004000c43d0400020b0710120808241901c4039074805240001e460810303498203400800d10781034400c0c1c000f51200300740c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 744866672 1250 744865422 744865439
    0x10504080f030c121501080702010b0603070e03030d0515120127110a060201061d060a140102070314010b041a01021e0a0f1a061516020609040c03050a1104030203120a090e01 76
    0x449003540301f80da812800d03a0f00c0342c20070b9099903004c0001c6504000208002501b892045030524003206004041d60302d0040f810213880c064407016908001d065851004440940c6005074244008040c61402880801c402240c400841245111140c40300d42d1b0b0042081c04209402c41e4030101c803000200443c0e411500c0c0c25000380281418041d42c20366603130a80f981c040b44c124014065200f41070061100403000d09019002c038240010802e11419845501000300010300401c400b40440c01d2110000291003491000704002d4490b61b03850018850510070300e00019907408120001d003c2400103520802d0035104002c0c3c0d1421000100c0075207002c5021400c2c104002601d865018412503207031001d0a03e03102c100400502c070040d2440110085000c220742c009200000555403c0c0500084c070550400754040b02160a8070f002e1a40200000d80d100d0400c0f13940300b01449600c00820b070110501e82032a00319070102c2e80c0c0320600f41213041c0380c0c000820b00d03e10242c440c0545501602c0414145522940e43d40c815 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 744867922 1250 744866672 744866701
    0x501050403021b06030103060e0120090103060e0628090903030516080105010903170f0d09060f0b060a0309020d140a140a151805070f031103010504080f030c12 70
    0x1100140241903041e41103002c401c0c50b0203c1d18500034549469a403070b41d91481d00800c00c0e4552040d86549441c01000e100d440081412095200750b00480d5454150100050448005810042c644216081400801c0d107a6210080f0b01880e00c5510140c6410603100e452407c0c54140d00602d80c45045c0b6517824101503154201d54011171600100200700c100b0340e401031341c00403000d009103400500a074004001145680142954040d030049d0000c0ca040d024058981055201003048109182c4401c00310080158601c04c02480c414034a070308001401441c000200b15104100c042c008058880c2900800d643c2c03900041544140d00107003405100d002c4058450700c80381a68815542203d490902155040c0081001c2440740d030b1111034000003081c03082002d8000c0a4500489441480440e11707000014810056603000c3c1109503c1ca200b010300c0c43c81c2c0694000c0300302800501990409060200244001d000ea406c0590a464159100c1e500e400b01c101d15800382540702081c03140700718248001c01204011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 744869172 1250 744867922 744867931
    0x90a020d0e0a170a0c0c0f1401080702030901030f0b060c01091203020a0c032d09080f030c0c0907050f0711041103040b071103071b091d0703080304021c050105 70
    0x1400101e071465071090716006104800303421070554800141d003203043c3e4001499100d4050410304007041c22919a03100a06013a041f1103565005a1818000108549400c00d1124001d2070218500c0ca441c100085d1a4050302d10f065051640343da0006042c280f8980001e502404040c00c40c07601e50301c1c2c500c1c602e8046c1102a6090b511080341e4904190014401c0c021264801095211050041165a01100e054407192100d008600070034501c0404415250001c480840031030f0390b030142c61070401c0522418030402c02610009503004101c0d54403040004240e4054054084441c40c1540c0d5484005517214032400355100041d49000a441c8100810314072204090300f800da4040014a82d203214105c5107101c19500078100e24600b20004143c2072140000c80004c00d501c10640307061100503680c074040d541c03100300408904010600280103005140c41042049001d0340c41100381c0f0705034120750586555aa0202610602c80000003400b50346406076907051003a060f0030f0b056171400850403d24000c240c00e85 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 744870422 1250 744869172 744869197
    0xd091115070314030a06030b1608100e041203110a03150501140909150402181009150509031504081e093105070c0528060b0f090a02 58
    0x55940034002400c80640304401d0341919a15540120112100320f070740c1009104540c02a15000c000c030000340d9a0940710700030302e80c00e186441025580d07100a003629a00230300c1102c9490810380104a1200f100d4080303a00180c008170f660801d03c85009088000e85130b00200f075a41c1a070000b459056507507160303004c0b004450815030000c0300c403521400110f03500c2600310402000c1550074000440f9600d484421203030804e1010704500d54554400022074140e0b00f00000700031420b110b41c00d40c0040e60510862135004401103141c19a902401e01003071a1203001000900b000704940881c0c3c601d41c030348003044920440403402000320854986450210701c554420001d0011901180e01c0740e0030350421181c01da40561344010310784000e0031542906003820091b40003146d041880c00c1c948071003402c241c52241c1409080a41d1b0b464546244a0500c40c0c603103542c0c2d0141102e4020713440c24100030008014405038200c1c0c1d021402081580354000008e080300c0700e4502090303000d9148018071003041039940c020070003c0e4054 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 744871672 1250 744870422 744870439
    0x16030e160315270b071814041d06041202030c060c09030d020c0609010c061407080412320c01050a0213080a080406210c0201020a030501080d1707050d0911 68
    0x100940441106009508028648814461000156144d0819900c01e045207484850040c4401c0c88480019050740000606002d160030000326080600800d03d030031641036115102490307104031684e52580c0c0107001030441101801580450b91084c4100da0350200101c00715101c50600c0082d21400d030744180d801c43c0c8a03103d58199080c0107030000ca206042c029000303090038144000304005481d8030314039410071a84607640300324008000d1017a0080c0350140341d50341e803080c140f86000d18010044016a01005052245030b0000010f0020b0f01d000407440c80c040e03c2180e00030640042c0110146016400d0141c40d0795080c00d0800c00b100413154040c2c02251004101910015515540f0a0716a50f0401016207904d90800c0244030f0540540404140c078086100c4d00308650480a01035000c607403401400d000142d400040010a559040c00f071a03003d442204060100420907800c00b90001608001d4400303151603460000310907500800070f41c0d0003946011010312107902249404d140c032200201c001403007040703203 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 744872922 1250 744871672 744871691
    0xf03070e0408190806091f081002070309060c0b0105011223090712081608071b0504050a0b0d030e0307080124091517070b120402031516030e160315 65
    0x184c130710a0081d00080c0103280f9588444040c00e03103c0358032004240e12424880e0b000181504d003004083d642c00c0c1c80e10001a22101a45001000114564004010400c0101e0001c0120300d0082c00c1c0c81c111002400d101004143d0b800c800d0b8042c1c800c6154040051004c08000301c0401541807240c2d00ca03840b0481914101070b15031400400c002c681500180003140c09000d1a008220646940413142d806299900c1c00d00090780d80c1c02409d441414a038080c4180d0301201009142014012180c201e0310104050044809000c0421240c00750b226000c0c08200c0084000d40e680d80b41400508040c0c400500207104880304080088103020b034007031182001602a1070009010703240c0d0300c1002484000e540c040324a1a01c1c0c24007101464041c20803040c0c4d0350041d24400130340c90700796070001c003020f06202e0845e00c2d01e40b40c240101420f1008241c548503a400c040c0b400c1000c21652081144030000d51803c0016800c8603e090003494200001c15a00700d244030488003000380114802c102000c0c4003100c0d424082c8160 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 744874172 1250 744872922 744872927
    0x12030201051b250b0108030c100c080609100b04060c02121507050f0d1406120115090f060b07051507030b010207030818030618120304110f03070e040819 67
    0x406440d00c111204103000f80d003002c440c2e10703001c1805541c60b041a1182c00e10395803a40300b0000b1080e400701c010b607480041d2550b98158140400c01c40d0068200c0c040011000c3c1c000082d003070f58030080c41c2c3da100c1c4200360b0002e5a5000c441c42e0280c01f0700f440310b00c801e40310f03600c41001412000501e407082e803180700000d048000c4200009002c0c101d1415040d4040282d0720394a005448030340000c1522181c181092003000310102c05c5108103002a0000724544006003000c2c03052003181807907030101d0a0564100005042d00015000041c0e0440d0500c0400140c02245031840c2c600800769030300b110070900710005000051040006170f410003a803601c2d002c0c8030281c0b00c03030000341c0807540c2e00b080c4c80c0c2c051f8020541c10000300b50844003400d58040d16060b024011001c10300040d05103a0100d909028423482117444500ba18020090400100700c020f0400e03196050a4440200804600b00362610400b0701c0c0108441c50703101484544002c2440704031400031760816150550160b0082e40c00d4281132540402036200c0d161 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 744875422 1250 744874172 744874201
    0x2030105010207120f030f20010b010806061201151b0b1503061b0a121515021603081b100e1b1804052103010311040902060f030a151203020105 63
    0x6174040c4007458482e40c0f80d5016a4620307501d2044806120910344d5180d07900100b90b140403034030407901c0d000203241070301e48001400000c00a03011a0040106004e80418994141e078140d042d105c0000b11a0407c00c0505c004441040700a2200320100000100b0300041004030b40b8a2401000d56020124000703040b041030565401c012950510303403181c01d4021100c00b1914000500c8040d03c90703c2e1404041207151022800da90000d0001008030102c00020040102000800714101f80d90b0301c05080285504001303805194018040500f418130001016900f800954503034200c4400c101c0240c07800380d11100340d101c2c0148410044000240a4485801101d81310f0b002c6040c07061034000c2c803401e1042038800c0c0e4030102910090084070b4621800b050031324107420360060b5034500102e84105d19604c2d81540342840ca07450a54200c180201c1c04c00d000f010060340e4071026079404045480c280b1381c0b02d85d20402c007500030741094007081d9900820713034002096600111a580c458240644c0003400780e51108540010041c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 744876672 1250 744875422 744875459
    0x106060c08070f0c0902040602030c0c0103180b100305010e0303010609080a0b0c0d0906062304050405030304030815130f0b0312030c090103110a09080601080a12030b041e02030105010207 82
    0x85204100e800d0000700c951050300880d81c014035006564a1701e58881008030f074040e0b0085005a0302c003007800000c2c4101040034a22080b0207280074007804030401148020745110031002000320b080440001c50341c2003902c08640040d9001002801100c814291503a240e034800e000700c000060041101042c04200065030b0905180c0c050112501590350304180306140c0c00510070700104a0b21020300c200441d0041c06500040d05240b400400310442010721000000e07075042605024a042c4030402020413800300a503603101d505410302804613600e0021406c11660341e02c2e0700303960209404000641740e240c540d01c00c0c01000395801d02040002508000c059030b89001d0600d00030400750810004044100b031070058041030b4818100851103101c0c1451510194108020b00000514044010405003c1c1084614010921100500103042d50340d00c03001400f8080e00c092200781034a880034070304a034407184c1c461034440c8031281040751a10380ba030b188140654000e2246c00d00521546101003054440542100b445 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 744877922 1250 744876672 744876683
    0x31603020633010315030606091d030f03090f06040506041203180204150b03041109060d081801110d090303020601270c03090b040503030a060e091005092d0106060c 72
    0x2005250480b512240241c00040750406450700c06080c83d0480511a910203980f190502144040c1040d01003822954480300705510003085003c600b00071040802141d62641d0918000c230360325611103002614024400559400f28402e01080005000011558a00462140104044145041d8412802d41c0e40296180464032268540c2000618080d40001c4c01000d541e121140d2082e13644c0a400c919410840d02a14104414005400e0364900f01300e41c0303580000c0031109000d1820207034a40403031038007420200030002d1512002074900c60b0b001d84206900c43d207111040301e10b001c44c0c00c440140314290130f1004030058800e003000032410000f20041404039038069200c0441c903541100e000c00c00340800d6054001415035030740104020604086045d407046005400450743c03420300c0e0b0201c07000c8440917408039803144020400e120380200c010541c4490b00c9920f41000c0354039240c81c1d030010b00388094154a0b030304c600a00b507030346025074119403142c8186c100c41000070004260f80e06410348082c42600700042c00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 744879172 1250 744877922 744877981
    0x10203040b0c07110d2d05010606030917130b161a010530030a0906091202060405130b04150905180d051806070c21020a1205010e0316030206 62
    0x3842e003040001c0600c0140200741d000301d103a4000b020144500c80c06a00040c51030001b00c824001d10109002d47c800501e10fa1408100050b950f4480591080c400940020407060006480d140301c04ac10b0585405000303004d514560f2501c85150710042900c00c1441110700040c0142020007070794441c41c0150480d100500b030003070000c0c03042000c05d201e00c0c41c8510081100c00030008a00344010204041d04a0281d075859401202d8100351000d8600c600ba0303882044c07900c0c80201c01d680161903030030075101200ca0541d104d040e640c1c815840d03040130781803070b0030043d03046450701c00d241c011110140210310894076040e008001507112000c054210b01c90300140010b003940a06c12113000c0710310510003821010380e80d088145ca10300c100f03800035076a81d003c0d40342500c104011100070300c51280e003440c0b0b074044505098044c548050450307001c503070108024465060a508100520403d00c442900500c40158810082e80d5a031107030040e0010900388400405d0f0014801c100001d4884a40c0d400800d41c060b821780203001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 744880422 1250 744879172 744879203
    0x5040b0a020708041d091203012709051f060b0708120403090f060201020315031f0c0216030c031a130605060109030f060507080c12061009080f010203040b0c07 70
    0x182d030181d40212044101000005119445040b0040310943c00c182d451840f41000d441b00c0f45031480c180b03002480c0c64020030040040041c0e01d007141800f000d07030803500307406208010f030450300030036962601800c14007595450400210024001e5101440ca110713080107904d480e02c10750310a502035410000c0284508001c07099141d60000c1d121603006109190812020b5103d0080e0200c800d80d0354841c0026030b40200a00000d88a80c0e00f03000d000700e000790b0041141810104261a03419454081d00c400d1079030310503894022030b10034024040410905005a513040e60b6070710b003031043c401c07061100762605820301032580c500c98a50442a0300901050910301a559101e860300f50081901820780c2d41400034040340007000500c200715012140d4000c0744006031519140402078142c000040141d00d032148100840c804040c8800003503a044402a228121604156030341078880d082e0301e401c6032980d40b140c841d8101c5101815001140714511441d600100c0d9241c01000720468001c50b000245503014599502 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 744881672 1250 744880422 744880441
    0x21503070c051c200c1203091c020105091509030a050705040b0411041703070b070f030b0f0a0317090d12030b0402190e010c08031e180c150403170d0f05040b 69
    0x858540c100c2000d0321440c01c60000025203912003c140701c606c6410100f0764410f1460100c1031220fa49585000070070714085a0760000702240300398903071588a1003c0c0000a20314403000303029036081083c05011100c04186a0500c160703580d003d4440c66110b242000d40e001102d042900402a40c07543c806107440c1410304200600b41e14402001e10751586201c240300d6800840c10380520305c0e0240b5559161050744259280380101610f00340c10005000d154044100032039511a401c0c0e403006c0741c0c0c001c200c5241c0c201c0d00e01010343c01ca124a220301c1d94803c5445001c0d805106100c1201d05444099481c10003412103860144010f0380558048403071704290141c20700000c2401030300341c9280d01a0502d001d03600e400240d680c80003d44c0007512424260020b8220601940764007110b0340b0f401c07916030107802c0f100d84c14540c5c1d256034a00c101c1012074021803444048180002d202425240510b07400040b0a01c0d500d15481c400c080c642154000e040b5003801d045000709840d52502c24540559046009002c3e1950380078100c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 744882922 1250 744881672 744881717
    0x30e03010e0334030c0312060f030506060f2119030201150f150c021801030503180108090703030c030c080c060f1305150c040506030a050403020c09011d04021503070c051c 75
    0xd0b03040c4003007001001c0040700a442523102402002000005240c2141400d519001c4002c0501d4041c1000c10b41c828466912110b81310441c64000e9000c0c00100c41c40d0560318100101d0b422148507854910250404041c2c064004124400c0c0e14480352240d9903465250402c249040d1144142c10802520301c111854400c0014101480c00039082403070b1000410040c00030307004241e009560640010a48440404104440b00d000100900e4646003030b0501d681d209480d900e19110090500c850414000101805a45042c2075203420801c540d4071041c201582a8891004076030402150600100186042c0d4030031000782000354221008080710150304966038107070180a00041060403061000007038542d40c28000358403414030000d010606041514003e072a214407041ca00d84290240030040c08100141170412070800890071300d081e4a9121800850030003500f80000084496000041002c000e40200340551010310500441e000c41c0c50300100d0590000f444280f500003d03581001e00740405458120 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 744884172 1250 744882922 744882947
    0x10f120303110310030b0a0902181308070303141803030411030c03010606030209030d0e060f030402011701060c12080114091e01290f03070804030e03010e033403 71
    0x100042d0001090000441c59001161400a14851940b00f0310402020f170040c140c12410001c000c2c404000264009880480c03091850359000440000146070341c01160f00c40e0283d10f400c0040603503a040302c0c0c2801000343c4003c0c441e15094820a0003c60607051801100b00c80100c47c441c06941552070b40d649441c1d01003010851503034988142d0384624455642031090300018521a100180d0307500c40181030600b4124400015001d00c07601d9000802242c441901329000916000a1a0b81c4c035a640c0c130050702c0042200d40075031f10805103c80045442504054200012405010350381550440548200c4407a44240a041100018281994640d04003840c0f070540220125488200320f15040b8a034142d4074109902c0301780400405640014103c0001601c1a01c0a4440c0440d0380b400c3c2070349a6154151101070a810104084000014141351240122261f149070081c02404500701502031240d82c4e81220290000303203440c0100801428078407042e4446801c0c00030414400541d29500c007a00c00518600 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 744885422 1250 744884172 744884177
    0x50703030b1f09080c06030106020a08160c0b0c1902130911060c01061e060203091c021003050a0c030203040218091203070c11030307020a140607050709020c0d08010f1203 75
    0x1003960071814081c0300b00c041c1c514581d58601015140010417868400301400080c010301c03042005000325079000c2461200340d0f0300843d00564070020803047c815503d10310f140140c108200c0701c00c003144200742d1400a0810400101c00c98140b04081c0d5214000d440340b00d00020b40c040307107488414109510980212500340d00602d01c0130340d05a090000b2807483e40c4042c915509a95441c0c070140701212107005403248200f41c0c0340794041c00c0360030283c0203950b03445003849640c4103200e410000c2c2d070080c80c00101c1e1440d003640034150459141e5070000141c060070041d00c40890440c24440c2030303805a4403c0c400e0fa0703ca560000e0203074010444a40a025010001038032081c07030741c00352072074003000004003100550180e1000c0e59800040c0580707051030b1120784040708034503210390000c0101c54003503901c4042000c26107803100b00445045a207000084d0b1548102200241640a4080f00066400c1d01d03502804201c000c4400340c549006190b2011100c03503800b4042c11000310340581040c4061641040105039451103070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 744886672 1250 744885422 744885439
    0x3150f1017100504090f030807090e042003030c0d0f1d10110a05061b0f03060108250302070218060d080703051215040606030e030f070c271506050703030b 68
    0xc2004c901503509100d4160344c100b8503580340034109584140300c1c6600001c2480c15100700b50030b005242400141c0908007a141c4101c3d000c0c0b1000c045000c2a0822000030000c044070303542c08294895035210501400480081260080c46145481c081c001020280c0303408800040b40d02d8452040202c0381075095841c01c20084d0101000c042084100809044a402840204011300d04000440c42e480e010640900065506000c2c0740b00c00c0c0d0f52071044d80e40100b0f003401d1103509541c0c1d51100c644540d04001c0605214141c0c011123440c01031301540140502030083e00d0006051f1040b000901d034801040d40d1194002000307860fa030010402c40000b034041035209162030303460201c003040b04060f003c10079280d12107080d0441c415181549450f11461005080d04c5c00e040c080350b54800c0c401c0e03403240203c0c1e2040d01c001d04002a82c104102140c49004054100c000e00e04411104101000c401030714500c41075811035180036030070705024451203005800c845455403403500d071144958085018007a11014580c000030750 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 744887922 1250 744886672 744886679
    0x2070608091513150c0e01030b1305010b09040506060a1b0c08010203010608010e0a06080d0c0320010225200f0d0602031005090c160c090203150f101710 67
    0x984120b10301840c3c901104450300c11039814414a07403048503e80b119014070304402d031440d5039005280364a01e1002401c0020b488400d0034041a02028202c41400c0010720700000400c0020310f01d4068039820100f43c07000c00281d038130748060100d54851041140e010074440043c1044082e00031403022082441240c0b003040d03855444c502542aa0801c0c2c20410115810f1401070180508000b4210341c00708414005004c0b040c5030488450f180c450345003074101000100e10301e51081c140640c50081800e4080401c8021b00444160658002d410180945000c0307e550300810603481104118030341115004100d00b07952148500701038220740c040210303283d0001074200340503803e95240310065803070a0189070056628900600c05014000158020511848602052104080d1050242c401305a252048400082281d003011086541d00303521451f040382c0000100643c8800e00611007850340000e44211161030011000c001103102c4225010700014a59840003c0700031014003104c1c1c001200500c0c1c2042680c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 744889172 1250 744887922 744887953
    0x20d03021b180c0c1f0504031b15020c030f0415140a090501080601030b030a0b040605130f060239070b040b03041b1a040e09060f0c0d1103130605070f0207060809 71
    0x5e061001c0a80a0392802044141a002515003c0f0072459003000d031006500d550301c1c00041c0d00e088051182d081d42c042460408079000b001166148000110020f0304e4995480d4000c01508e180c105800010748200310004a5607401c200303684680e41c4603201c010000c4d081070b0044802120007480241050b0715540b900d07404c2d81303003400813405090003142d2030340c214905428000d058a82c09041a4082c02d549404000400c0c5174003400101540d00c0301c0c1c09a9a524204d01e0ba807400440d482c1034400e5404083e51381d50740d820700c41c0c4284031503981500035a102d5580e80c0c900c205041c0614072449070303959001c1001070000754121070a418031402c0c035110440520384580340c1130311500401008950700000001c1c144140014a12090350001e1250000d08091904078401c4a0010029060140022000c83d070342c50f20340c403690809030031111f500600e140c032454564104480c41d0082c103816a170003803604010400c054856102c102419a440c0c000301185841e190046a0b400001421415039026550003981c1010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 744890422 1250 744889172 744889213
    0xf0815070c050c09160e0a050f040207062007060b0105090f120109060219020f06042f090f1807032103060503071d010e1014010c020d03021b180c0c 65
    0x41110041c10700c4040c0e1054090580341c3d0b506d034940e01c5030884103030400aa1b40d60301034030801c0420688000d03031a10318500c0c020000d040245a940300c4405488080c0880d919600094401540101d60520040c5401c80064a4604c5010b260a070000c42c04a141c0700f02d070400d4088640e248024000014400b4150340721642243c11103015490030034500100d0000141d41007101c09094241c0e03002826203070601e030303a40581301c01032489444460044d4106162040c407c2c3d46409980960182c9240d46501d4094180c0c039100c08216000d00303041d2044008400050b90008019003565408a00015001e8800304070804440d8900c030050201603d0385004182d0781c42c2401500010106c165112800c1005012004140241604501c1c1e03d945402c04110302d25007003114100480b03609070300010306641d40f880101c6408040c0d1f0000f139001070000340c40d1020540c3c0010b41c100d00700c4c0a00c0103110848010700400000021010022144542203008201c8010f0010003c0c1210001d5108803240c40f94280404d0605c0d8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 744891672 1250 744890422 744890431
    0xa06110d060e100911040e0c04080316021c0f03030b041d031218071e15080604060b04030f08090d02030604050d090608190906061e0f0815070c050c09 66
    0x10205081406800b0083d403074030f107001d0044202c0034070105d00340201170300c040c6c0030b1440399101c02c51843d008074241d0180e4500b154090059502640d5890541e400e1401d40c007203160740b0403030044003420f4410f0b5510305041c488880c2c040c0d01001c0c3c0c41148829480071000b43c8251102c1c183d1045d603e5040110641e0a405001c2c2e080036410b0103140c840301f8460580818100080007403001c1050749511140000010502c001030b6025032100b090a5103005612410000154100e0400c43d83c81c1c203008270300e240c0c101c80d0152090700111001c0c00380076182d808451103030045e48401000c0c10352003440c000010303400b800075140114020b0150000242140c000920748034050b50300b55610b070012001454003070f9200c0003840142580782440d08541c141580c07102502c043c0410b502c140303d551032100008010381600b00c0802007051a901420340c40300000c03c10004146442000c1c00c0c403105241c0010140c1010845400060340802c00303c906640e1040242c2d035030000810119200d000307100d6042156940d41042da4080d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 744892922 1250 744891672 744891689
    0xc03050c0a0c08010f02031003140a080d020304020406051e061b0102210f040f0f03030e0708010c0806040606080f0a0902031507020d0c150e030d090b060117090a06110d06 75
    0xc6494004030302e013191005c030b001c00c801c50b004008003d0221030b01c0b110070003201e612528038606401110001810b2a104c80d40043c090301c2c0008605e1101d100035000b95004a00803642001510b956a04000d030350300800c52010101030241d1407101d02c926100d030103820300f010380302e95003807144000c40b2007a42240e100d8a00500a1f8505665041e80004c0580700740307500403c0c40000c1a1982015280d80e010074240d580b004202605651074501014829044419001c4100041345c86098135034840501074075048504500245280000540c58030b018040d00c811951070f134030b81c84c42d0747d103e5a40b607045e1104024504a80c003502c503c840d0b4016202045140c8069464020100d04c508180c01c00908204010314031741c0801000020314404160007100d400c2004044c91030004041e03c8886040342140241008906200e181120031400d12003612086842102c01b6a96480c00b010040408607405509940d030b00d01036032104000100090103079020400800da80903e55041100c0105140c0a4840c1601300480 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 744894172 1250 744892922 744892943
    0x1093503120103290c0a11070f090c17060402071a0406061703030f1f08060108031201080303011d0a0207150f0e0a1109060607020306040305040f15020307030c03050c0a 74
    0xf40403254a440240002066242003c4250b0781c8445131107a4024000301c61407200040c0b0002060b003d000c9008022182c007054510841c3d4840042000402e00c0c80b92461107800c03c003003030302080e00c40c508900201c0105603003e0865110b600603c0f0007908810800c9402104824625002014180b00d503441944100310101d400d504040c034400c0d090850f0524010158001d20510442c00c00b5202000d601203119186c48888100301d00c40020300401550010101e40900030000c01d03095000310003060999964480c09009907a6039201a607644000d10858003001c4a50541040303a0020a0000740c000100d80c40150074424203881d4417900c032410f80040f41600c0d03a00e50300240c10220034028442e03c1080310000c0d0981d40550386030803841c0311220030700d07034403a030708810004500c4d550700000d5941840d0013500300e072111b107000d10300600700b40e110f80641044048130740c2c40040c590038072a460505c1400e403680170b581002d22070f031f4064070b03031012080003207040c80710600543c08128000c0103c50892805541c0040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 744895422 1250 744894172 744894179
    0x8070803040510030c050706152123030a0522081f050601050d0b040917180f010f050d092406120b04020d050c0d110906010935031201 59
    0x40003520350f1010741c00d1500340044624071a80000c190741a01d5084007000c240380103440a40e000707040d403603007050040c21101c2d507140321004800c95a00c0c844c90301c00c0340954918140c00800f0034006801c0e5080c0c6107d0b030f00c01c00c80c07104140d01c220050111007140e403101c0c4000c8203106440c01800c5000303801601069000c210301080d843d11014580140103200310080081c2e0800c040024102e02c9213545106200f602c5440200ca9030f241d9078801380004d904207420202c0b13a060600c0d691000d600006a90341c1400700001244071a2130521002418114141c503948242484100d040d101500203d198000c110794501004010842d04060010095244040c0394500b001140b40801258820f40000c0405003c040e40240003814035801d50340c1064044540c942102d40c1864002c0c9460000e00301d032a0000030403402c00c801c21103455042c504246003140c000245559000045845040e83d01c940c1c01e500041000000f00800d41c040801c0c21200400c2146e40f0300000280780c6461540040312001c2d000b200c420040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 744896672 1250 744895422 744895429
    0x1511070e040809030616140c03040803040e09060a14060f040902100816031e0905070915060e011815020c041d070807060806060d1d0a15180f0c080708030405 69
    0x4e55002000124006e16081a00401040c0890700344400607079450020b2114200d01c410010784005200a1013100d6496840302102c803000c0c24290f600c00d01c580300b010041084c0901034010b13480169a00221070a542d500e034810454248844a40c1d19086a511040380001d0b0f01c9003010361101c90244d4071140326074242285807a150707400c0340c3c0c8000c040614008035a482c180004a1154540000250110754460300e41805030411859a101e000d00303501d0300782521201c16114a82500315035458a0b4000c0714001c0714010344019014240500301024122814031411507074001800780c040e8607204a841e076100700d0000c03078110b51507015280d25030340200408903c0140f0401c0004041e2240d20007820255103040c801a21503040980f02c54841c100c04a0680420103465116103088280030141e900034000350717210baa40310f903c03250040e214081d103550403690300c98107802420f18200c2400007030b12007803c0f00c0d00c030740b103d012811500300c569000700000050308604c01c010001c06023031203001841e41d4a1600080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 744897922 1250 744896672 744896683
    0x8151c03020601090c0c06270507032f0d0303061a0301090506010507050d050306030118060b01030c0e030c04020c030c03041508060a031505130204151d011511070e04080903 76
    0x400081c10150645e4810794070440178040c1c10342c060004a00c0724a6030001c0f00034000c03c505000c1c400d00c0008440428014001a600222030007811b810350310101a51015a41c84401142d020f01d52000d101c02c0d041741c1c10440c0c842d10380c0501070300e00040d96503180c20007007884120310030070101c070400088014840b110143c800c0d07503003209090810b2072822461766280c94a0303100d14600c07a400e04c100130000480d00d4400790015420311000000d05401c020040c07411000400454007030b940000d00d41500040c04500400400c0100400100101101c075000000c000c081e500ca1301340314403640800d10031400c1d924410006031018010001c1d1402d03100c1158900108a05401040300e8400c00181d14200082003c0f000c3c45002c07120b8941011401da03640764100c1c400050340b000000c2d041860410110b04940903100304100b0354484e84030310304682c0110140184141c07000e0080d08001d501d441202c10906005840e040d11103610721080e0f030611980c0e03a00b400c84071340c0100c0d419503c00000159640300c61070180070703 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 744899172 1250 744897922 744897929
    0x5010f060305070b041409090a05063117090f120303072a2d060c0e0a050609090613060b031501050c0a030f020703050f0321010b0a08151c03020601 65
    0x8082d410a071810f030600040700b680b241547c0c01910094085805481c050154003540c1d90000221499070801c0c00c158440360391001c020304512070b041020982d500e9030035000d0303000307550b0051000d00c124915094080444d6003c546510f6000448412601090300c4500391103039104032010145459140505000d01620016105006d000d414610f400415004002d80704240a41208160100010004205a070311442c110314082b41714a920f00c02d0b0802c040e90b0012002000503569010a24592106100c2210114040c41e54400402c0c0410085800c100070103035801103005144601206015500004450032608600034040001081120120982ca100c0310400028600b0500d1322080c44007403a103a4250b007100900704000c60004081c0c8034403c009890207183c102c0140d0702666101610903650754814240d0707000464400b50080a4054400310160407940118002031828051507411900d0042c01041291141040d902c400015250b200070700318032410b018641c440042e02c41c140a480c1050590 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 744900422 1250 744899172 744899189
    0x9070905010b03041a0403091e0f0b0901090306020f091009090515060d09050f01181401020a0906030b0103060e0705090f031621020909060f0c0f0702060705010905010f06030507 78
    0x8113000014480421941c0031854818280c0b4950301e440c6001c03a41401a40e00401c005281500407900302600014004225080760f8028107080317550f400d5141c1e403400390300d0300240801d25818040021408980040185001413100145404c548100082071074051150b08400158103a400380215202c1d4801d154110f040e038200200031500304c5000415034440c0c03102d002c0d0056103036070b6901c013003160400c6841d09220720100240309210b01001c08824001d0b1442c019601c801035a180d2610105061003240c0305402d07030341e031035003c418140a4107501518807003040703904040e5a0710000034034030380419060303028001036515650b513000c03c041002090040a00c125200340c1040781061117640b0300110050880d103620882228651000c44424180749580b8800ba4105440304c041010f03081d40824264412550003041a00c1c03034644541c140054040c1c80c10344d0b1440340d0208108800751030840c2c00351908910510020550074620340d1482c1c2507804030005440241e407500420b004110f028400c0c2c00103170080c0f0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 744901672 1250 744900422 744900427
    0xf0e0117061512073602030c070b1509040c061d090a11190507031716080a020c01060f050103200318150906150f0901260609070905010b 60
    0x1a0700b400c400c1d10103500702e48a0400820302ca9040c8a050003050001c2c40420a044410100324003005d0a810171440f80151040d04c0d0025116070120620a81e4055403401244a051003003d80e1501180940900900880c80c45050043d2260760340300143d9202e075110303000b81180180b070402c014000c0100081e0300b07400304510b200d80840644689105691041c1c01c01004030b104241610f00e464148110403110288164541004460941250003000024880d948000f4404641283d010329610151118940444005001080144100311054024105440051420030007000c098211549030f4440282052a124200003541e0540b054200c1d24640307200341440c158500e10102d002e0720004001103103102c00341d0b125091340d0101304a0b201d4140210742c00300686040000b0341075030b6010304a0321403151211192583ca01c6090099120400c0040076140b443c1607403c0000c100f06111403540c001c1401408807450b00c1540c00304000d024052803004c1e014015181c20300c8204000d9840582084036050f008 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 744902922 1250 744901672 744901681
    0x170c030403080c1c11030403020606010507120327030e03060604140f0903090907050403110d020907110f0a0f29180a06060b09090a06050d02060309070f0e011706 71
    0xb01c290300803c0848042e580f007003041d80a85201c1806030301d82c03840b5440c046041100400b03031002107020320300940850301d060f81c400c4011209440b500f030005003800d0200142080c41070003900820000b065042c54143d5044000c00040d0080700c820905400003015400c0035021070400380b20b03440d0001c8042e6001d112045046c02da40a0151019007811080c240000c00078440650520a0f688160001040d0040700d0400b442e0080c0950441c0c001a140e429031000c25038402d15104558907a5240e000d0801000755450503010303110b60800401c800740c0c80c0a052100d920092041c00f014001c0c5202c0d10301395044601c107003400c0407000014003030943c0107848041d80d611540302600959601812264640010600104115051400120b801030940e400c00d00c010480c1d06e51071001e4070281c00150703440207466441c403580341c042c0c5116224558101088601140140c20500c00459100d074815045404c05640c94044c0f02403809158002107002203a100144140ca600c20000b6581301c0c200d50041025040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 744904172 1250 744902922 744902927
    0x602010213051e0d0308010602070503031204062f070b09010509060c0d150e190b060a18080d030219020606031002221404150e0f18010c170c030403 65
    0x1078502800f8420215500c850700c2403008a04008400c680140086440030b1007480c2c0601014400e0060070094000d02a0100e0f950030f001041d60281e02000040740c09a40380c513101c00c001020403608074144039920780401b09001000c0d22140b484410086d2095968116074200030041c00760252100c4400c1c1d0404060104900700054620f070001500791b99a9628175003114000c00038015080c10f50040305844000245902e162442a840f4803004028088503a8220140310f045405510543e6481300c01401815040c1c1d04c100c1311425810340b105004400d15458241c05441c0c000c2d40011840020340000d0084070807035107000c4611124003640024034041c02c003903000a8031185d80c00840c041160340844e1090180802c807a200703459551002143d4220b64699142c20f40008072034640f6400365081c81c41d025100040c1c00e1420003180c1e001e0303c8101d01a140c40c61200705018024000d030080c9100084c464041c0c080a1052000400250301c40d60580c51090040444800f0000c24100880d0018810040880d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 744905422 1250 744904172 744904207
    0x3021c080402031c050706090648091706040c050d03090b09010e041503021509220b031609060f0803030a0c03061d0a0e010605150906041a03070906020102 68
    0x1403c1340c0200350b000b0003000201c505000f80c0d04094401402c2288200501401d58003074120868070b8100344168203810034150801014000303114440700150303004040c18008020501000c449d142c5010250b00341d07074410f59020040d200805000c60381010052000300a5040d1945004000a4500d03008030800ca8030040c060914920442d690410002040c100c075070b22843c1d01c60041c0d4401842001650801400703095024000d000072070081c0c503401c100841d000511401d94100c40340040c07500020302c0e881d0080b01c05075414040c0c500b424503156140c006803543c0030300a943c10030640ba81410300451808202d003003a5007032a84800d50704403503068140b05920b0701000301c9512007440d0764040f51070050182c0c11401000075501c40ca1544c0944030039403590041098007140146a40c03442842242c14440c9004e0032521030784038007a8800081c0e41444101b8ac6800040c00d2800c40061040707040c16505c280c4e0600da0022a110303100c0c541e01c00402c0204c65600500100041c003000c0c0300071800d001c0340c003200140c1003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 744906672 1250 744905422 744905443
    0x80c031002030a092f042705030f0a1e090e0105012007060f02061509060d2a0e070e0f0f130c0201020406020601120302030403150f0903021c08040203 66
    0x6640002c0040d04460254010211841c0d10410354080e44000b070303c05a24411941c20f0000c524002c0c040c083d6000e144c075000d0f101071450015020041c40040d002000802024400304031114002400b249041c1f0348250040c00001800d0740b604013000b041c030740c804034400072403500110030700198a900f4001d819034018560306407036003824001c442c08002e0b440c801007054030000742c2c4d01c5807180080108402c1c5c1d010034030302d011100d06d800301d50080d00c610f01c85000300c42c00040030035040740c0c1c984d0026040b480c00c04d86c90012a0701912088052040a0707045580f24841d210b5904000301e81d50102308202d0f80c09400c0b40e544070045d0725100c0c904000c0a40004c5400001d00c0e251445aa40c40306451303099503c1101059084641d03040c01c00c80309801d140080c1c041d400910508025014140c00081c2e07008080e02d00c24882030740342d40a1071415080d41d07144152140800b500442c9540d03201e040d0b20400700c2034424031284500a800a007800e0b00907545070b40f03510580c0f84160041040c3c0c80141b00043e00c0020302000c81 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 744907922 1250 744906672 744906703
    0x70b0f070201020f010c02070f0b07050a17041508060a0b120601050d020c07381c06050306190606030e0309060d02070c030b0907060f0f030902130603051501080c03 72
    0x194441400100c0c5010000113088105528010040c62900e40010f0340308100c40c81c7d003d96802c0380d50f44807606030b00d42c0100c980c0a4010740103800000b00081340e100c0c558035400c0e000603880e400c00c5d4030717150800020000c522002e00860100c4052007443c0c038203022003800511080d6599441c02c46031071084000118041e00d218184400440e00072000c0b90241c059501000d4403000701c3c2c4040703554840003a146050062949e4010b1540120942400d5207441c031903c10b411044607451400b496003c000f117080501985441e0510703505c000114181e507050110038003601d000d101d44000c1080f0440c2e000200c80066000800303042c5400d91103000d9240100665507a4281100c4d0030b500c0f2200d189102c0c5c080d20640f140180464400e031008400c021b03031000c400d4012a000c00c100d80410340c9408054075030210100c501d801103481c5101e0701125520941202c058544054540a410031001140c241601c400d908100c0c1c25400030403007a14a10f0424030124010000d01d0003c2840c203030b460000c40c0c1c031520103900200c1c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 744909172 1250 744907922 744907927
    0x12070c021f2f01020d090c0608010308040e06150a02030d0f0e07170f0f0d0f03060302011409120105150102150609012108120a0b040e120903010f060e010314070b0f 72
    0x7030340c581c0107034840b842c280c2c40300203556510500090300c008101c083c2c2c6c215162102c2a00100780300c1e104070007103816a58850b6031140f07480d0514034402140c02d4010800c0340c1c400c003034400501c3c034900044040d0030492801d4008545801d2410ba44005070303009200d0ce070805902d071404401041100050807000c079a011400344082005800c1b0b0182004030b20522241d1a2142030a4000201c3c0300003000d10441c2c80942d1024482152501e0445c159840c5210290008540014001030380c8403503801009402c0c401046080110045807420f802d450742103c0000c0c0c0c140003401000c0295805010200c030703034a001c0826050340c0c5002c0c00003445152040c0034040800108483c4410041042d094805941c0c1d0400005500e80c0e50500390303210840300031600e25101c03504007103007124242030500030194441d440801922002e1520440d00310282c1140180360360564071955a03440c0c0d00c0480c40380e0006003011100c182800d60450500351441d070b5030070100420940c484503080226849510541d400018201d00b11903 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 744910422 1250 744909172 744909227
    0x31302060d47210304030c080d0f0f020c030706030f0f05010b12060109030503040e04060b0915060f0403060905010f0c080c040e0606043c0803070b0c12070c021f 71
    0x201d0105000c0002e1200c05194010781903c04800005081181d00c100355650790b4917100d030b012603120b600c80b4041c3d00119890104028842e80508426000300c042481199032a61004002a00c0c03c0180e50104000c20fa5450041c10780302c00c00c2c000d044102181c00d10511031945003c40c85016889801400038003080e0079004a0300c240e00c105100d100640c0c00104998542d07407106d031180b04040c4159403c940c06850400406081d051034003900e4441e0303a1004a07958250320f018188a0207a0144107480710b448420400031001419602c80c9890300c41c06040001503640c003258051048480c00440c20b024022080100720402c4400c100b110282e4840c0c82c5040750a13103c090100300240201d8026001c40c400035182408003400028a68a034426114003507400e0354080c0003100341a40c06030003400e5154104011480105008844086d0041112542d00b4030f058950200d4524074507041d21140300113216038022006500d48940303124152080140f4a4071a00e880204c00b9048091504050510750030121402 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 744911672 1250 744910422 744910429
    0x61602040204050d060b04060e070c020d1518060c032f0405060d0c02062d130f050d030501050603060d030c03030b100207030209010902070309050105031302060d47 72
    0x42d00204030240c0450381030260751810b00050180c802c0c2850082d4a4807000042c0c000700c808031107014a000d52034030300410f0041e40912945441004042d00c0e0f843c07064010510100c00340c030400112200e411550901e6001d9840c1c410300b41c4d45003007000401c041c01c00b0b041c460407121003200d000b140044c516203540401810029030030716004d25403003142d2000c004640c1d0f10694039141c00100315900190309079000780d17550001d010002c28100c1e118038a110017400204a41d00840906283c00008906d2131078441162955102560005e01c0000c40d0344d80c0041e0340610030035801d801070f17501400e422146903095141080206036211401c0f00c01500700403c40c2041c405040c081e40c080c202045d000307010803654883c04140a5980c64080c40700300e00071954180000380c460070a20070b035803615a2542d9080c014900c2d0174011903641d000a04202c6ca140070b50a11000140d58080023030602140d215004543c41035401b08010020072041c48190115402460611030300861030188021b0204020102c40c9850800340030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 744912922 1250 744911672 744911677
    0x40b0a020f150103021927090206030408070b010f03030507031b06110c0d2606120f2a030627070b09100f140307050f1c0b0409020616020402 62
    0x58940500b0700b1500001070703140d00030342c1601d0081e501c54903820a04d120203041c6914034490540b08584009400f8144040c10f00d08001e00c00308550045100689078002456943c4280c40c1280c1d00313640004d4a104102604900e5170050103040d007041c600d41c2c6142c6020b0b1982c441c22000500304030301d0f80c10021445014640500700503400003000c0200b0303000d214803848a030b400720400301c1d002e100305444d043c145449902ca0441424200c20000340c0d401d900800c030b00200c4c3c4041c201c141d00c05400416101c00b91701c00c1160f003e00d40001c6000388141d032841104c80b464800c8540000f024810f10940074202034600181c81e41d040007150800228030340840b10b880460901c101c04041160007a550b00081c82134a8801a080c0f840040301c400c1e992420f8148251200c080c8000060003188a80c40b554008104140c0a950312000d982031952030f00b052005900a141c0c0222006103c450000242d06054440b6108221060106450400c4400c05940026000b80280003070715030a45010120481191a107406 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 744914172 1250 744912922 744912943
    0x60a030e100603060e0c0f06030403090503100902010f1b14100c0203040f1d0c030402010509040603050105090607020d0e0f0f0a03031d040506010e01030b0f1903032003040b0a02 78
    0x1681c01900c5010550070107881c0b144070a80b82c0509208245403540804a02140004001064030026040d48000d000c0c2c00c0c1c00c01401501408210600010b85032400d00c80020b170700852000c0010071f801d0700d02c00541651410f1101004100803c2407104c4504180320410b007109401000407440340d003216094a203000d0769950038484c06030601150f0700d0740d550008094015202a02c040f186581c1e100c41c1c849442c4c030b807a001f00e05040403008010030900500d10303004540090041c5046446c040d1144089000d641d420f51084446a640b00100120365170284403498210324148047d00b40011500c90040004044418080c441c3d0003031074820089503507022840301442e101500410720241d070b90501504000508050007900e0b08e50394440842840c3c01c2c07207401d2140340161214110310002c04011801005845034030b941104e03400b425100320307640f41900440d00444181030004001d00754a40200f40c01c00400c110002c540b0000c041d001001404406c0d41c00392600c4040740c1c0d0b114030401d00200c0ca400038019 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 744915422 1250 744914172 744914201
    0xe04090c15050703120b0d08070c050607120e03010c0f0e060d0507050c060106020c0607110105090d080414120705090c1329091305540606060a03 64
    0x4000074040d0031002800800f802601c0d035070b00d100b46070103c441c02e4810100b612544002003010141c0050300310700c042c00440c1c0c008d00a6071542519030022440d643d004001c16203815858403030700204260b2041190a003040d094009010441c40002e002d01225490700340c542c1800024410110a500c0b200d00f61207040682000620180c28110740250440c0c1c0070554000050046030008a012400080c1801601c4005450f00b407030000b8640700c03905000c02028076a41046030401400c01c00390340702403100d1020303030191801c40e903118a0192141002c5000b8640070303000312004244c0420040000c10081d044500a40300b440d12a0b644100d0520248608500d03142045403000c00840c0c0c0011500508841c59078a08a4282019005044210070702484004640c041410350360529144010f400c0389420240000c4810090620748001001810410110007602e105200b81c5400074000c0481d650340702d20b07040340c254219022000d500354540c1401410540550300c0007810f0b64403248030b541f08cc4100130910 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 744916672 1250 744915422 744915449
    0x110403200f040e0c27071e140408010c0921020a2d06110d0302030f06040b011103040e1906060207120c0905070c02040e0f250b04030b18010c0e04090c 66
    0x106102d1491700c0c01032465501e4984200001d15050144d100c048012000300e0401e16244203000c4120750140c0030f0f44a0320b000e02c000b8040010044002d01803005e143e101078580302d11b124102400c0d036842c1409111605c80458000c510703100942c40d4104400c06440b1032030320107001c0000c11110300c90a2030408910510101900307c00144c03043d40a032000f880f4000c03500946200c0311100038110181d0005455216039513051101003555403070240d001d400195010f04050605800c08203109003580c1103540b00a50001000c820000d80c2c0c00c4581e4458800d01110a00308013240c20060001c0d515940d60141d40c0c00312005182e45024018291031460040090740414810b43c038181c08000c2c8900c1e030b0030004a0040b81001d00c6e05d1101440811044032250b620401406a83c8100b00e98040d810b10140e28009405460100880d084014500400245000741000d440742d08109404414000358100f03035071000d900d0071900c070040952003051002403c004a50101d40507902d41400010134082c0d5000541c880c810 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 744917922 1250 744916672 744916699
    0x5060703180b1204060e06071b050a02040c17060303040f0e04031b0804090e06060f06090d0c08010c18050d0f060213080127170307050d110403200f040e0c 68
    0xf4014442c4164030501080c0149441c0c90030701c0d5a81c8505440900118465040e0624600803e900c1c412000c3c1c010011511441c07001d40110b400c480380d02c3d00d0100001c401503140045094200d0907603030406026002075103494900a04c00d14903c065001c3c07540029003032000719042c14810034203030403d44c42c81c100180301100140b501c2c5120f039104d8403450700198206018846190000705510703218000252610018100100410101d40d100a941507440800c8080d0000030500b00c1200320050200701d000004e6100301c545014008440c14804c18070034181c0c00c001401580ca5200321952425030101d0058800c550500c2e10f10064003c41d0021a013100783c4140c0010010015003040341400205107400d14a0301e60003608420b05566400d000d0b1003034012004041c1c02000c50350096500103400d191807030410040414443c2a0b48030b0704640740c6413020102d014014080c0d5410f150b100c07040740c94200081650140040351051003207005c4544916591060000440418000c00714071345801406940d10a24 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 744919172 1250 744917922 744917947
    0xa050705030c161e06110a0b040506060f0603010b090907031e060e0a061a0c0a05161d190c030b060a120b0d0510090609020a030302010c0201050603010605060703180b 73
    0x160008000d9070f0040740000062100c00e186606201c0030052810503001c1d4200502a500c0c0c54502807046402d10a43e0b80c1a00402c0e481450240a10702c00c20141143e81003810030482d12035400c0c8aa144500c40c10001080a10031a504a81c0310510079a00b000d034540d1114000e03402407154203080004d40346500e44400050900d548100151509400503111940f500c5084c00101e501034051005201c60138482d03405903054000203081c1400490381141c9441030140e4590f030402c3c0c05210550711030510440103001c803008410303620781e14100d502d45161161030448041c1503464007000051000656035030340070000500c2500510100c0d403020b001c56584001d0b00c1e5009185182210017106501d00d001c98441caa0319207550340303101c0540c0102c000c0c10007018400100c8001e1201e95005c0700c6040c1e54008050068482142d000004c501940000410941e400006402c0d1100202024403907450f0080610081d0355180a48140b01e8041c07400c0c9074003012400b080303c00d0b104250000e02113404082174031003c2c1f02 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 744920422 1250 744919172 744919183
    0x9060e01022b0f020706140d11070b070305060d0f02060a120606090609050307080d080c0910050903100903080a020d021b07060906020303041e02181f06050301080709020a050705030c 80
    0x402c036550a40143e0804000700c0e194103a40c0141800641583c0722002c04510034000f030031100603001d00016203210003840e1050322381d02c510001c64034138199104019009400d4816994000340030745e0140400c00d15079880c0f0300c1703500016000920414010034642510b9200d2400812040f240400400c012030b26080090910b144500c030b030900186900001060600f004030ba030b10100c842c400020010220540300566003214024107201c030038001400701103010baa50042081114001e42c40b903540e9a03c48005160400c54020401c0300801c1c1000c03481c00003e035110220ba54084054280180c8030616141180042d00c50403050705050200d4001030000f030900032400740104c40103501e0349100140c0c3d0381c000380d03141c2c08201c50180000180e10466204c1d00031a0345088001ca10084c00e409200130202c0000464120603283d5140b010181a40d8035042c1d010301d04150f01a00003401c0c1507055625120007141d9030005c0303000d0503d034a44c0120708641384c24060020f440c005603001040c0d0307844541d46405c0350f0f5141c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 744921672 1250 744920422 744920503
    0x70e0907030e0c03010e12031b13050a140d150207020a0f0e0f090318040b090f090607020a0b0a0c11030d02180406240909090b0405070603020a09060e0102 68
    0x501406a62283d0342c641440f40503046c040540c040c180c01068203a00f0201c54000030040090034962441800540c00c086005084c07604440e548400814104024484814095084000c00480e07a00ca05a19556443d010303010300e03a40604081528440114040c0203030003841c0300250040e2905002081d9070318101c40180954481c1820000c145d40c81c00101020840e00790340e44d88068104100910045800c200d040316025800362000c6140c1040d01c000c28200c00c4121103900b99a0364401c20303c08494024400a40c004c400f40c4000d14040c0050b031108081000c020300310b04130a9039074800407200c450042005100064070002525110440c002810010b03520403179542041100c08100b07042149403d108990aa0308480c20301c00f09132800444485102d0717210451030b000d012442c3d00005003030b42d1601850246501c220307000503039420140b07805464500e954001c4c1c002d02d0b006200c2044410762004280003118158504400c2705a15080142d04105a41400c2c0001c003800240000c101114855004e104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 744922922 1250 744921672 744921701
    0x72a0819062304110402071203020316050f09190e010b120105030d05070212160b0406080a090206031306021c0c02060609160f090510020a0516030515070e090703 71
    0x3a80e10b403a0700c20841540440341d1160003018880468042440a5103140340c0070310145c4018a0f00c482074407040b54180310b46040707000098002081181d448025084848030014504115080c00101086d8004602910310303164062481e142d420b5201d20707441a0800300600c00c00c4001c0007556102c03d4600d01035031107402941082440e050000070541030004030001d030040c007075841d40e003040203603420051035000d043c0d1400700c1e6214010141541c1070844441c0e50003450a40f0f04940c1c4c41c2e29003000580321000080c1280141da1506c3c410340050b0b2100821241d0040c09400010056111480d2000080c015540c0c603c030301c1ca480d9a1912001882ea5100c05400c0840d41c085403c00d0340c4450410100d076808603070b605810312100d00c1811440d07004048801114549003400202c03161900c2c0450f003210304100a42d001640604036400a104040c081c0c101d00407151103c1221041c21600e03881e42d9807200c40c1c049613580240800041e25940700d041403000044004000700404d0501440c001c02402c9100322182d00c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 744924172 1250 744922922 744922931
    0x303090f082404030c0b0c0309010e0c1e030307080a0806090901020a021f110304050325030507080306010323012103020601140d080c0303010e010b072a081906 70
    0xa6a090010300c009084050070b000c1141101c0611006000c204090021024030640140050019104c081c1c59031003036a89081c029100d1070094080ca00352140010714005c40d0304400e00c6075121352a6000c0442500600f82070010b883c0405401192071071040b400068189c84001c00da030041e1903400107080b40540002c88000920307850390740d162402c0384150800310016030701100c0808400c0d03054182c6045403103500c1200241c061050801f41d646a070003150220b807142c000180d01c108490444804908800d044107080150852035a405491489405030142809901000041c601e038402e40098203d000020000d4a49401283d10210311890a000e050312a02c41d03001088034106180352000a081e030140d00600c5c0c20b920b0148050f10058141c0d11894002410710401e0f4045440c01005044031325020005664942c5050030203021541c060300a00c8000100304101e40201d842c001c0c1900400051408520003075125421406548186078071400b07141c01800c4c002e070301c0e60240070442646140903070780600 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 744925422 1250 744924172 744924179
    0x1030501060e01081f0f0e010912030509060109051012061b02031e0313020301051f050603011d090f010e1023010b071419021201060303080115180303090f 68
    0x6100e803200340211310503503101e00c109026600c079a620f40340c0080040315000642e40c2030001c040341615209404203415071f4488954400f000001c0c1c41810040b0340c00c0c5010451400c140454a0300c0e28010b02c581c0d50800c0e110401300300c00d4051070075640c00a183c41e1403a44000d08291030407401901d0145400b1040c4c0284500b01e000c030600101c105c4000501728092a040a01100710341a06600050706250152820804040046c0c030709110f014092540000c0035221041c0103000340c549046e07190062070003900280010040c481059800541c01100100080c400c0e0760b5403045146003803404005003a0369802d107041044400b101182031014100045000e103c005610404440c0740664244200307031540b600c0700100305807448003020b0a000c41c415010305000c0040100d0091030200e00c0788690703c6014007000395404502d400c00f002618100c4010080c0030f84e6140d03417400b03400b03010148545940c1e000c0c5480003540036032003400e42e0240c40001c010703c0c00000382c0b41d0038003c1004006001e1103403801e200f8940030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 744926672 1250 744925422 744925439
    0x1e033406050a110a05010c17010609081f0905070f0609050301090203030904270b151c060e07030c080c0a05150306010c03120e0d14132c0702060103050106 68
    0x140980d64561121403034954140001c99a03d028603d02d001e02c0d010b0860fa0b00c002078002e010b0189035036059030301c176101e10904a06508023454103034000c0e0140111540100b14002d40400c0c10f071304401c00d0f0078500a0750142c48080402416003c540100701e0700650101003401d101c0c9144950641740640e0756019881c0e100c000340b50072101c0202010b9071590051065100c14075058102071082ca43c0c803e0b0030b0010030542120100a150315003000c4821103502d001700100d40005640c40703040c003c4129180512407015026440c404845101c01400e9540c07100440d0343e6202003040304600441d071052156284a0303460920684920b80d80c50384500c101d0b03400d0030014517458000c4004d002500b8008840c0d00e503888800041d1051084031104030b05104007400d810400c0012482003613840c90f51007000c0d10000d1140a002041002100c0c40d0301d808503c1405201c04640a15140100b52480f140b03d503101c40300e0a0955a200e06a0741d40940c100d50303046000c01c5803503580480ca82d412a8440d0000f806844e841c0d1082 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 744927922 1250 744926672 744926773
    0x80a0e01060605040b13120c180501060e12030412050c09060306070801210f0803041211100b0409230601051806041d010e03071106030f04021e03 64
    0x218000203c0520060100380d6064004040001402c1500e0b05026079a001203d4800c0e0103130781c1038402040310402084420210b809a0507008484c060403c0030b03605080340035002618144016001c1c07103586081480740b54040045902030310794124220b500102c41c0c50025a540e024943c800e0158000d000172a0306818002000d03030150255842d419541d0303003042088003c610020045a01c6414051200c0c030205260914019881707014502c05a560314044c1460550020740704440e4080042c01101040f545801003004031380b5461084010411120001c0018040d04011802900e151890645690805135140c00440e803250342c48140e5255a03a84c40801040b10b0082c445202558150380c0042c0d840d00e002da124110510300302103038031480c0752403c00d03442c215449001c42d8015540b00203908010b02903140c0c03d034504c9120450310286146001c248030300710fa403400383c802030089207020105180c048140703000d07000c29000541165840c1480302d001015030070580e00f0780c0003006210740c0c6080903514803030705 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 744929172 1250 744927922 744927929
    0x10305030a080901060321021b030d030b190b0903121c05060d0f03020d090b130b070f0503070b07030f090201140309010e15010501090b0c0604030c060b060703080a0e0106 75
    0x103541003060822007511400390040c10240c0b0381d5650240800002c01038020340b4002d1030307607035503c2d404581d00c1240a480c103200b030200e0755039899030382429a00641d4002090743d10030200d8031340413581403013036400303d842e0034400b1144400760039900d24003056010071003004d051441d004070204d8070805c007000d82e4024248549000a140042d41a6510018400316001680c1160001d042019200f0054940d908101d41c01c03041180140c00c51403c0a00c0e01d0751006102000d040092400e80c41d05c0c409401d4403440031042e01c00d5202180021a0003814010202c84051002d5085802d90ba03036501c0600d40310210050031607580c001f113407138801c50f44026240e62042d60340d0709506071038862441e060281c55001e1904001c002800540d201c0d4959541d010301485120401c0d41d280503005099418640050004d0889412030500e442c0c2c148420444c0342000101d0540140e05400d028004403000d04044000c0c0500e601501e40012001440038205a44190b9840c850960100100000820b042c1543c0c02e03100c280c807 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 744930422 1250 744929172 744929183
    0x30102030411031908070b040336080f07150309080d050601080c0702130b1201060915050d0b0a020703050d02030c1b03030912090604030605010315050114012106181e02030103 77
    0x1086c070000582c40e5040c940c000b8068105540c40d40c030013041d10384d80400e480d8441e0605d4400e5103042e44000484074201c8026021400c0949005c000078095140d0300c880300e1007800d40c9417088144080d01140a50310204480b03401000c0d42d55a26082c00c400340103014180c5400340014884000510140f5940d130586086a82c010014a07101e0101000c1e5809000729241d5a81d00101c900c4100646072400d120360801080241c801180c548401860110b4401e282d90009020381403140f514800a200d01e03c0441e03101451010040e110501c0e0b0904650340c0c042c558000030702e544000140601c81e030804015044990314a0050f031070b200100070b245510303800165280d400720f9010707400d6070f421408504003030103d5070005003540b03081a90300e031140d0007610b40c282c3c82076802c0d51400300f103c8458001d0b8050355002d0030244010108103400b10300001d12410911000c9040c40701103200c03030220513225170840310062058680d010b130707048038810150b07004080094401e100360038148054211450707a8001d50f8100c94120 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 744931672 1250 744930422 744930427
    0xf030a080a170411060c100f0c2304150504050604030305090909070803270414060111070e010501110a0c060302091003060312030b0d20010e01020c030c1509030102030411031908 78
    0x1c10a0000d031b074000d1664400b043c043c0d1440803402d00d202d480391407005030001d5400709181d4000d220141c00094100c4040c9a6074011061040d0a91002002c55080b0748000902c4a03521010038002c40312805a0b4010303550155001a0020a00d81d01a01401d10800700311690441a1038242c0c0c91691401f5a1140368400d420a01040d51030206030a54a0925048070440d07442542c01c4a0014044418910307410109030112006c1c42155640322100b200c0f0089544014601c1030300341800c001d0031800520905040141007455112640ca050192050242c0d101030032140842d00c50001070043e400c4020024050440908140704252082c0210421240c1040400c50064482441100a017022032100d0303400003021011100003807444d003000360019254510504803801c801e40010030610359040518110362080c1c0c1103002541d404980c0345405881140c00c180c8548200c840d603100f900840408603815403012081005020541d9148024420100c0c03d40c1d001c414411031041d03a0001701c490160104605 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 744932922 1250 744931672 744931703
    0x10c03050a0201110c160501211d0105070206090c060f1206010302070c031121061f0f080c100810060e0a03020901030807050f030306100c020f030a080a1704 69
    0x34a00801c18000d1501c004a800041c0480c5210799911004512a080d84410107001500a24030301044c060103007481c01020644040344440000a0008d00c55800c0540e9a4400d14101800e204141127180003580244004e16043e00c02030f454107400c40d0380c000039006002400303102c0d01d01030080300c1c00078805183da40d05000c40d4001c00340610b140241031906240e400c00c20702010941e031031207040055100d91040310501d06e0b40d00038421500d080314004200b20421a0280400e401c0118440e648000030401060020322114584044442d09500200d00864005400319010201260005c4a200b0503100a40813807444001210341000480e000083d9a01d03102c0c0620a25103c0d034032500004c00004c0181d271460340c480c4c00040c00700d0800c4c0e2003280c80250008001007045428040e02582e50240ca0266040d490072201142c042c142803410b1404200003401d40000f10b40d1450f00381c0070a0000681250300e04034840c038145103503030b02003611000031a21416422240d250b207841e010b44240ea120711511112080c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 744934172 1250 744932922 744932927
    0x816090e040c0b04032a0b0708090a05090c09091003050d11011116060b0a08070b0d020c0a0305033c09011404210302030c03130c030602120a06060806010c03 69
    0x8050411110320740320100003e000003807000600095402024100444001d90f81c0f0824004040b0310141d101c1c0301c2440c800c20a60310500145d640f4507070800102c4c0da4406c00034001400c42c103c1900031541c84240e2005100009036404c0103030042000545000081ea1202a411a4401014400188203034004140f0808003072289031042c10048404001048081380c492001ca07254224580155511114202203014090a03010f0150700c0c0405480a814040c01e0140b89030312500d407402520090500016145400e01707555044400b4155481c0981e0a001002d1400408590040d40e130140752082420580c0100c2a01440c40361120001031001500b100030300c1c040c02d440303e00090a80c2c031a9503a03110001001c0707140c1604035200f103200300c811003000003a006803510402030601412003014030510810040c1540302c0301300d80c0c0105001162103240704440c503080041d01c4150300000e04441c00441ca0b064280e01188101d1f018001e9500c0a1000c0c54440c482100e103e001160801d000440d911885408030b030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 744935422 1250 744934172 744934199
    0x9080a080a114b0d0c1a150a0e0915090313030b07090803040605030a1104030f05060a050a1104030809030f0712110d02030d0305150d0f050c0109060507240e030a081609 74
    0x1845075606c2560300910390f090f40800c03041250014409004c031080d00500e0b19108000e00b01520100484000ca410b00001150fa80d120401c02c2c0c8203c00000008107403200000c0058548076012220b080070441c3e00d03407405104105090381c1d4040840e175000c1c80802d052001005072416a00c1680d05d045c1140d844a00d02405042d646c0341e0b00013180c004000c048041450744202003244c9000c0c00081c4100e041810074178040318401051030030354620300a070500758012000e044600720307a00100c9007500c50f00f40f00300003400c3c8235038050641100e1107844000541c56214089110815014864412513902d404003880000705a41200960541080301c1c11007146002e98041500002000b260901405298010804060b44108141c512208441c104400c014040003000c600e503000f8071b8146010fa15000300500240100c4000030a56100d44a6014002c22191214103c6410304e80c0140103030015142c0c41501c81c0e0254102c2400210380c41d002511202d41d100e01c580d6601c0b419a0b84000039841c01da042c503100b8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 744936672 1250 744935422 744935447
    0xf0305060411030a0218060a1d030708010e070305120a0905130608010c1106100e18120a0e0909070f230909010b0109080a080a114b0d 59
    0x90b650b81e80c0365000c0715082c07028500c21058001e00595a519554020403100714001440d44210320801c1208050f40c0c1c411128205103283c240003032000c03200c400000741051515042800c80c5c0d13283c902e1107402107100042c0a41220300660544112050200442d40984580d40c183c0d00130503030340c48040086045c88a0b03524451120000300140742d03a02d884d078550a41d500340000d50000740c0c0e10800219080010b0000da9041603951044006c52481c00488002d08070004200078400c20000800f0313080c0c1c8a050018525200c5202a19540c9059880f0050000d000c4484400c4c001c2810100050901c40d0000d02c120030f4569400c014180d0a1030140341a520740c0c02e0036050b099481c507081c2001c0e441e4407112440b0340a041d0a6001060100d03503c0c000415100b4240e019420710303401501e40c8000310301c4c40c104580d5400da540c07501002456200d10118a0208202000846185005031000d070030f101c102c4101d2905403100e1001d07420740c8011500c6050a40040030010115041040c0d031010480c0100e4807030301507 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 744937922 1250 744936672 744936679
    0x9030a050709230103120503071e17010b0a1e02070305070e010914011d1806040b090c0d0305120a09020a0b13050d05030901030e0322090e010b010f030506 68
    0x14520195611800c1c00e050303501541da0346450f4024a0221207020b0b80030001c224109041807200d41c55038460b0200709580800490902c1800408030300e4403489200589402603540d0507140c1426034007500240b0708584010700d811b80008603130000c1000070790300c01103d0301e103c002c0d56550f03461300c503016001010135401d00401c01544512078000001403001c1c0300610062030070f001c0c0020550b1510301c0d10820382320080f0600c410403c5020042c400044402031030010705c0e000700d8081c15199140f030740d000704ca03807680407000403031380f1810040000304411248002d1050350b40c441600c0c00a40a8000e106446030010230090101e142800068223a01c201d65005601a200e1203000c04d2040094020030078440590300b04840590340090740e84030484072040002d00401099030f903081d1005080d150180c890040701c98450416803a240346045810f010010b4484039640300703000d03016540d40b40c200c2c141411654800c10821909110704400042018464408220302c180c423140800c1e054040b00301c00134980148081e50 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 744939172 1250 744937922 744937933
    0x905161e031e0603060605031c11211801090f0320120708060f01060504050f0a09110414060403210513030602030402090a0515130207080a020114070c0809060903 71
    0x6940c0c040702c1c014420440c41c108006485400c0d03003485004d9803d503801050080c0d01c40d0009989103044102d9100b94181e00c0c0c078084000700c00c1c2c028802d0501d9080701000014444c100303160514a401e0320020052030851000031120000940010748050001c0d20541da01c591400c44200003080d5240c041e14a200c812808484801c58428000b41d010b940c07220304038100c0d078815a418420100204041600140d41c900070503015858004c0050079880b55004160203202e1038004201d00d511441400800b51a10040612000c00c03184406035094100d842940207910214003e0340c40d604200e4100c41c2969007000540781000d0401c41d112001580d540881303c200003041269a21007041e8910360f001a501c5501c0250342c3c1d08150040003e0010b014103c00301c1d25150a00b4401400c080c0c44100b840c141c0309541c964210f500480e5000000c2c080c090000e040d06100207907a030032031581075204006840b505403045240380c03545001110703840c1207010000e207100320030403000c00a450443d01400f04040000c0880701c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 744940422 1250 744939172 744939191
    0x6180118030f02070b0c06180109021e1908190c08030f1b0d120e0717151806011211030307060b040b18010e0408070803100905161e03 59
    0x2212a000400180d000a50b040540048141c0c18840180101a01003020b800e0059032102c0580303c1c2405041d180010200c40b24442e00544290041054590010812810007800c9580c0b0403144000040c031600c901c400c010610007090f031402d0402c043d61101001815a00c6480728002c820381140007058031129180e020025110100b04010603000d80441800e42e00c0d8881c8980e100c1100340040f003114459007000745e0b0161410340c00800e00312200d60804010a440048044681c10413003140c0100070080c050395803820283d000013448128108a4030305051071070361500d020308802c0c4854140c940150300004010000e580000104550b281e0240300c2810860042c180042d00e143d028031800c0f0b80403500d68851814a1a0502c2144136110b8180c2c0c07908c25a2208045280000005000303030f41c0248901c2c0c0120f828050701030155400150320402280c5c0c2e034200443c01c1003030008c41d1301c9541090350504000448000300751516614043d5681c07101340058030000d05a11619040003810b404155031841981e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 744941672 1250 744940422 744940451
    0x8031204020612040302010c0201181214040902070c05091b0f0a2a0203010b06090112050901020f040303110111120408090112061203140a080609040c091a19030302061801 75
    0x121300642c0300740c00001e5405100c0d000a82074036190060300d10007405194000b03000c41c0381c0d440c071842c0390850340c42d0041e126900c081d070210040c01a6000888440d00c003141c3c8504002403030702c55100b81c40007102e403031205a50b080c502d00e0526005e0400d407a030300d130401d121942c503840b162409400c0514444c02c00351015000e1000c0d01612040e40c1042c40d0200c0b620003c0c4000354202846020a440ca0944982d8540080c2d01c0002e0410740c1f40d41d804078041661000080e407400301c00c1d419038103110100850543d031155a820010700c0602c460383c0715a859441d01d05c0361500030140300111000118030403100002e03a6580d485544282d0040320140381481104d281040c3c6900c240d110380b030080d10340c030350220004105074180100505091246d046980004000401a0390780005c08603510140880b10b00b0030300e0b9200d15141003900c000d58400007400341044003108401c20502509003100b0816500c140140007030801ea240286850f03c4042d01503003009020031600700700e429a0a210354600c80001c43c5070002600b0300e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 744942922 1250 744941672 744941707
    0x7080a17490515010201050402011407030c0f080a0f08060a09020904140109020a1b020307050913150605010e0409210e030304090506010809031908060a031a041209080312040206 78
    0x40c1d2409030341d11010403040d441c007400340e00d840356402e10082103103240a0b400a40039500030125103410004c040f5101d030425208110018205034480e07007424080750a890301204541282340784c41d0201c4c0205026545191040c042284100c0e0700030320a0403000e2030800c954000350300511140746c0054407000c42401c1300300080f000c140280245003005070398485200c4010403c6164600100001d0017181c034041c00750340c00040c5e01e000d0343c1c82115601581e46506141c0d154200000800500084442c003c2240300840c50307222508070b490a8072034410f008084d0040000b200c01107140200103a00c818088242e07078410b07030000b0507100d0b418200b2040aa804000084c42d507000341d40551030f06601d41c0c1c204540c07541c0c0548240e410002c14001581000d0744002c500c1c4040d5403181c264010013280c44002500c598480032035000079900180003038503000302c840c00d000404004440a644000b099082c2c41d002c64400d540c41c0d000c844154014500b081c031442c44660822401820983c2c1c842020b22546e461900100705 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 744944172 1250 744942922 744943057
    0x3020d020a110d05070b0612010e160306050c090306070e010513082109030a0609051006171203150f0a051203030a0e03070c090209011107080a17 64
    0x40342e25112415561561401e052042d140042103818000c1800003060000e07101d03040310701104c2c6840d210018500313070f50042049000511042c0f10b0f602060042c0d10000042da420f4034000d850620843e55035002d1040359106d44120340e5013542c0132031700003030b100741c4200341c07216004078140340140c6480042d02d0304020b007807040c0c0c0210107903400c160200c072002a07003280c0000150302103c480d241410101d0000a448942d1040003600144d00c6440383c1082203024001c6421603484d1000401400d07458007100c0d6200800132026103594030802c0780080c0c00c03121040582c0c2c4500c0c3d403200700354422607800050100c024600d1000395000404440040381ca40c0ea00340b041078040203100300850301ca02d8501103140c1591054a00101c003a00104600c00c0810a88401402a200383d59005684d401d01440122100141400f841d081c1e4000c180000c1100100800c01555140c050300c3d0440303101c07181c907070503200701e11846600013a00e8240403d00700210a000750120540d000e2035035203944101070103110b0742d40c00a0035803 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 744945422 1250 744944172 744944177
    0x2150702030d14090a080d11070c080105070215010501112136010503060d053c0703140f1005102903100801060e0403030c0212091003020d020a 63
    0x50303281da100790350b8030503142c0c003c3c10098510860304040d0820f94440c80c0005016012001c0040c2c411000e00040d04401413a10004281607074851003410009150005801081280d500340030100b031001c2d00c0081c0052200c407401040403056482c0030700544a500140d4044000c80c05070701c1c901c03440070f02440081d480095142754015600c0750818254101c1d110040700740107401d40c69010012402c030f0234640784000d0b84000c5c00c20702e5583d01c4810018000d6500d2220080c86c031b00c1040d0f024810b01d110802c410138910720011421842c0080001138100707600180114000e00d0307011640410215000d16000e8403440c1803003058411260080c00c0d100d040c041e02100b0940042d88501c1882003c4085108000c0101090041c0160000c28000b00d01510340000022440030307000400899620300740b40d0b045000410b11240200516643c070075092501200440e0b095001ca07150402e0800c02d18004560b002500c031145000c1841c0c03040749400c1000308004032640004040c0c0c24000466010000d1004080c604400e4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 744946672 1250 744945422 744945427
    0x307060c08010501020d020a0b0a06150c02040f1806110f16020114040b09011413140906090103020901121a01180501151b0f062a17070f0215070203 65
    0xd040c080c01c0440181d1005045500403408504074a90100e203072070307038140c1c450404146525a00b14800c060802500850707000941c0d0b50f0071400583c1c102041d15036051086e241800360407240310010301181c1c112010b07076448000034002c00c0009103140d8003550b55174040040e2541000300703004208510ba04900041600c048400c001d0501350360708446c0600001c099003d54625042c03d094004065001341500181401080d03418608075802e09001d85120141c14080c8541e584d030b0b02c1c0c80d8110b809121120303241c003036400000880d02a00380301005c5810381e034000e080c0c41030366460440304c01121540a4000c0d03c5c80c0c4c0ea891b050541c003024100c1164028000d8203651110000101a040222507040e4080d2100780308409072082101e400c4403c9201c60032403803840c0200d0081c24203100150b6800b50200030580e070301e03107050880d08003d0700d4401880348154800c00b90340e80c5408072040c0d686d80c005e05414440c1428120009101c20303c40e03190100810315038030684041e01c21340c007200c440c144025116207002d85c201 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 744947922 1250 744946672 744946691
    0x30a0c08030919080a1205060a1e03060e0706110a081e0904090b04032c1014030903040317090901030609050c1203031909150c1b030c024e030706 64
    0x10340d801121010b46c45003040a800e001c0c0004911200c50311402404000d2060301c1300c02081154866001590004400d000c0c4e808144101c503200c6038940900000729500004647e5035880000e0700d01400d940c40344115240c2812801a9110500194241c65900c4000c01c6a9205501c86011300d44080b481044000050305042c90050198410f00e2038a0080841c0d1440510300103060031300e4584501b0054504041d600325403503044032440412101d00000e50800420b001c0c10400000081007180c0c040c680c000000069100d100203140710304810540d00185100060012030240ea2004406078481c13000c44540e44440d01c080342e40d8500210543d000380c1c00220402c4650155111040e5229424810400041d00c165840903200303c108040b2503199941e90b00860401030085581d104000c41c035120300b45620041e841c00600d2503001d190100d0051200544a4a010140607200340841c940f509270361540c1810807041101c020806000600260b05c030500c1c1d118850001d0000f80b90f43d9014100c00702d0740c1082e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 744949172 1250 744947922 744947927
    0x18061306120f020c07050111150f070e060406020d05090d12030b120d090b09030a1403091305070503041104061a030f0f0f0c0c070b121008030a0c08030919080a 70
    0x240400c0160b002c1c0100300c000c840c0b50300480ca05013600c1007420b255845030060504075240000c4a207001e00040354010a20212140003030000c0e208001da5a07071802c5520f150005d02807940114400c080c090790215046c0f14038980998081c1035242c0014045104600303440d00e4000d0b0b462503041c01c080101f591101e00c00020309103180415003031500c2200a01070400c201c0301c003c15803c2c40e0f10038845c2c801d0011801e44650340d001c0c0700701182c903030b009003429011540c48c441c000c4d181e90040c50b01d40d1103803800703010700d03480c440c0355000b924401c403000e0b03c0311425030b503442c1c807041d90326200d41040550040d40c0c0d2801090b0603c0d00700400d401c0169000301da0340c882c581580303411200c01c005482070041291810802c200303ca1801e408550281822128030303162460380c01114641a2180c014410452011404c0c40800c24030602444c42075040228a00040d503031085101c2e240d201c0c440c440340011f4402201c0c080030448107001980c0202c0c10078101d81c2e20740024010101e00b80f04a1004031544040013030074192066 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 744950422 1250 744949172 744949181
    0xc050d0b010201380409080406080a2c150117010e010203040809120c090c0d0f06291303060903090b0a09031203090b0f01170307081806130612 63
    0x4100b80000c0102c10101c01300314407114000303984a8601c800582e440d043d4039002101038801058042c0040c403e0080518043e885a040b50080070005003124000400500c450700800344020140141c210038545404400850107900503005d085501c95401500640a800b85480f802448003410986141300715038159403d40c0ca626041440303e0307006200340030202c6c00314070450342400c80c00c40c1d0400680110b10255810002c040307141950003001801042138600c2044024810304c02442000c00950840300c246000f01c1700e142c01103184151845000d050031602d5400510404104510943d04044200d0940c0f4044215038000f1034045450b030301500c04154002480401512004c8001c40c101500d900005021406070312028040140080c40000180c0c042ea110725007458006000501503d4440f03011091440300780704070540c0c500004600c0708450000710a45d0341641c0d00c03041a502d45826a00c03c0c01580d10000030721a07110204011a0700c40c0004011a0740c001c000b551248000002000c03000e80444 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 744951672 1250 744950422 744950441
    0x305071d0c090118080a030c0b0a09050709180b04141e060c0d06030f1410091106090a050a12060c0504060c02130b0a0e0405060112050d08060609040c050d 68
    0x2a41035a05201c56480385005603102200b081c07801d2405800c10400c1c4c12200701c2c456102d0340c0135008110f0300d1000c0c19801006004001d00a81c0094070350784825030844111a0056005407441d0000c440c184602e01454000300c140d034242d131401040031552601c03009400081518101c41704642c40d903180450400c14480c5110314a01c144061140c5081c5d4402640c440100601c100c04807640003500341503052055101c0b5000c0c60b00044030098410340d5191281200444035542001c1d403003130402010f0036503101d004d0850017a42c481c49140c1070340d24060520109403c01c10321160f109109090108058548040302001030400352070310290600c2a0420804460010020204104040100344001500000c886a0140e8181c4191105803410300b4103030002c0034286844d03940700c0c0011078009240e803c41d0702c4050140f8090300650b281c59076101d66121000c41c82c80b83c002d01c580c1101309020a141c1c0107200069010402821141c680140c1c40c0001e42100c80180394100444c401041000c000c07002d5101c1c0d030222 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 744952922 1250 744951672 744951719
    0xc0a050f160e1911030403030f1112090717250b090111100c020f101a060c0703050102191b150b0a08070e1e060604140d0c030507 57
    0x3858108012018a40300342c0100e8910079442c40208506404004840d10382d401e8101c410011041c0c941d00c050318940c000e903403d40000f824441e8060b804103030746c80b03901c3d80482813650181c982600c0080d006903401005202c400940580c070000550354140b8182c2a445811200141c02c103c100e80d0801020304005102c00000340c020343d8002c3c8a0041c0c020104d40c801078003400d051000e56024400645440e00c0e48141c101450b090115241c0c3c240e40000d078107252580c01c50f0644512105408440d001c8500c00c00212030a0312168034240480d041000042207000c1c020310580f13035074548076280c1d90700b660300c116a0b099038401e614007124081684407150b40c540c100310103c0d03809000000d464151104500180340d00026540e40c82c0412103540b07a1075144d0080c840c440a669056503160740700200e8036030850740c030850503a0044110034001c00300700b901c4e40700d40360040203607041c0346c00c03c246110300021261009800c160580941408150800b1000c40290301c20b100800c6e1140c02d2030f490b01c40d10010032040000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 744954172 1250 744952922 744952933
    0x2031518010b13110c0d0203030603010f0e030d021605010c0c020901050f2b1a0108071a120406091b080d020c010504140f0907022503020d061109060c0a050f 69
    0x150360740700504000c1c3c0303904560b000320310703060285400c60300303403080c0c100c01041c0d1702c91680e00c041d84640202c040c40c4203100450082010350f03524682c0d0740c140c5030300b550707082c1d10350300100a021410300c51a4042c020750240e081115102c07001c2540c0702402c5864428507071001c0351124003018214a044502c140c0501425190300c41515164408a1050390365041c1c0c040c00080f0100018003114000b90358429101c0e0000e01d20400410800742180090031300b805080340c1c07070154090104103201340d88106100b444001d50914a00744202249032031071200a03108441e417540314108c0f000498200c3c180000d1045050150003440383c502401e640c0b0700302e40381d000c1006541000c860f940b81680c015040e00c084a55480c0c3c00102a00c240c4005014940001d036415131052000c03050082c000e0340010b280d100c000b01c128402c800044030628803041c0e0b1006110096110001401d081c001070310a070041030710994406803e9042001c001e001440e250400016820641d108c4060001400010000d400c001c8402201925 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 744955422 1250 744954172 744954191
    0x1801061508040303050c0d0906020909010e040f0f03091a0a030c0201150902030c070b131a19020a020a12050c07050f060708030c0c010612020f090108030414030a0203151801 76
    0x1003440e10300a1000c3d09040e920000548901c400b070003142c181c20815042008091031a150460084d00000c500d540100c809900208a0a180122844c02180c104000035510900b50f51401326241f20160101c007040106040041c000c81035a801017070201070481407030b89405c190500141100c905c4000f000440e03050a0900c0d02e14100303400c0710000e4410310b60000d030b0389542d0b117810700f00c0c5807107600401400c5402102c2001141c00010500500701c80c8039400e4003010100e0002a40c03504c1c4c40c240d681c1c40d4140c5200030b0029406035a58001c11348800c050040c1d950740c10b00d42d00e031820070084100100f004a0b500090503610744a0a01c02803000d07040031036040010003200408202e5a0140183c002c11000000010880c41c4134501c040d550001c03100002406800d403620039244040d06c210404a00030f621410300100685403000c005030580c4c0000e002181070601e8400340340a40d11074800215014083c0c0b850410260305e0621a4040a072501e2004404605100c40102c00c021080e01d242a0aa4509600718 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 744956672 1250 744955422 744955427
    0x19080d11010c02060609061e06070605011a1809180d08090c010918020a051308010209040c030b03060402091f030606060e030d080f070908160e1503250e18010615 71
    0x540d0000e1064541c40035514a03248c141c001014010455a4403003408240b4000f0003801ea001507050720380050684113510300240c40503419000c1ca168500d021040300c10030707180710300340442c84a5010348550100404c07000324032102c60410103e9062040010000310070032000c0402001885140403081c80c0101c0390078505001c0085265203040c001140b00d8000030030120780c030710500550b688910700d480d0b070086203680c88000ca4000c0d440700b031030640964100b8164001e182c1c0640b00c1c1c0c800c01c1001601910060382c840d0308008580c2c900418408040c110314004e076910103100c4400304040e610510b00025018107003440030f400442d4900d0b015102e81c0c0700c2c010200a4507848040700b07400040c400910401030f01e5000c021b45000f101c07034100b01c0f010b114030f50a904854260740d500c43c0071110b500f20403011a85030744104100308903c105180c0e4166014010301940c90a61003031164249140c4107007002013684410030300654010540326031701042c950a00c00e4018aa0070b2140030001d03e400c0228220006014002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 744957922 1250 744956672 744956689
    0x1030e0703020d080c0c03030a0f020d03060608161e02010b030f0307200105250b0a0209030703110315070908060a021306050304060b04020f04030308180c19080d11010c020606 77
    0x620313001c2c000c2900e101c4a20100140c4c0007034000101030325101e40c01613030010b20032117011070000e006100710444000807500a101b08000c0c1e9007a60740c1d407500c50307403402d13000d082100a0300003000c100040da020a40b8400c0030008400b00c0c0303200b02c2e0b00204202408604061510400c01000c0249070400c20242c000142c24220416207005507801c41e410b250501e100584250180780440108030504080105c4c09034548212081043e00ca02c3c052201c40d120241407004038051160744a806611075002031001c0365a0303880c0400c5003080101200c04485421212002030301040d200e00010809c14141800100e1003801010392100e1009011400c14040300c41040f03000c00c0c41d104040910000201080c203000c3c4641007407000c031101800c29503844544ea000710106500c580f1060f0001503541001c01c2064100c10103600103030302540c6c0106000640300041088481e2030000c00c003131140460740c1c0000d4642c0c003402030380c488444503280e070080d504a40915600b0364100025043c11504004200542569000003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 744959172 1250 744957922 744957949
    0x10c0b040f0813150c050c1903230d02010903080112050f010501030525050607021c0b0103060911032b12020c0a02270703180b0405010b01030e070302 66
    0x45596110360401a031050404003014240c010000b84031110b189844000c402192908024201c4501d14604111405039052000900c260044450300040b45000d0413600c015081c56150302d45c08507540d9443c080016065200d48040c080d80d03000540c00c1c0081400b1141091655000034000407401d81d500810126050040101c442880c62201c0180001080300240165407503001300150b58482c00c0c6070350f44040d490350f50b104040d049800d01d10050b030382c0105001101c201400c11800c01c6a25400c00040c480710500c101003469440c2c0614000ca11500181d5000354081d03c80060030440605090760303400d00b0f03521540c2c003950111f00703204901100c502c69148248007014a680c2509003010b02107510340401c0500240660022a01c0381c656800032502c5290032340b0132101e0303801200200400b8409480e00392010110100110000351100e40a6003121003403195042054407050050381e1402b44280c419070f026106a0340d078050b0440c0035601442000098801c081c01403905a1540d070005500c8042e030030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 744960422 1250 744959172 744959183
    0x605160c060c05190e0316030203060a05070201110d0c090e010302100f020f01090c050906030601080d110309041b030e030309070b1305040905060901050a020f0a180b04060c0b15010c 80
    0x40da1601220f10450540b088085410310b00313540318035a08402008200d861030201c0c1b00780030310311441e50003080c1e04a10100300c030b6000c1c020301010350754003002c60024013005041005554071032044c400c40b44095801080c00211403200050007034014840100b400703940d9000034010741c1c21840117202581d500f00750382d6003031855450941d8003034400943c00c0342482c440d905035542079800d200c1c0b00000c1040e110b0416064482c1541d04224940d00c0f981056071301d420a2180da019900a42c41402c043c41c0701c0e07c01d08201c141d00e1422640740078120400306044a503c40e4581c00300300c00903c07581c09141d516010b145440000d010007581141058044591521100e106890154000088422821001c1854080203000013401004400540c1c1042625424115508449946848000b07900e40788244281c3d01c1c4002080e42c03541c203018001c2005d8a102182000d410f042c0580294005082c000b2500100301805259455a41d074072201e150141c0405000f50008985400800c0400d605036030110f6804400c80c3c020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 744961672 1250 744960422 744960431
    0x50c120a0902090a1406060a05031b0717030901050a0e031903060b0c0616260c0d060807080d08010509130206040f0e070905031b01030c170a06030605160c06 69
    0x50040324018a0300ea10700942161a120030000d0f08800b60340f0407032000341d40329048001e0f07503102c00400100c0c0c070403501c00c640440d406001080406041c02624517403240011031945c0707031160684501d000068400c1c00b155040500100304050601c0a000c0c064000444130404e20101c0782c01b8110300c1d26402048044030002800c106545041442900010000e1441d03182035aa640c0c16005180d0b00e07980c0468003010001402c112002c400341c42251106c10010100c680601c96584441c101d100202018200c086c10103403c1c0216032003041c42e88200e8005080100c01002501d1420708118288400100c429003442140401002a529070360009984582d50361401e0354113803118400121503003e80d0300000032000602c080070410380101215036010758803540b40d03c40c1c03040d83d42040542d03480b0102e000082410f00d910300b543c210350180e007151100c41d41e0747c02c00701a11240280031000000307003195031000441d1a14020000c0c40103c1c402c481d0803112000384180f075000e803084050700482000000401c2d01e50f40b03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 744962922 1250 744961672 744961681
    0x1170f12090a030f051c2105070512100302090c0c100506040908030a060f0b04150809012d062115020405090106120b0a050f04090c1d040312050c12 65
    0x15a01400040c50b4080c00744039030b282403405e0640d51508130090700c13110304441005000b1014010328140300110041050349810b07201d2070041c01b01a040203043c1d5010700c41b041c40340440c42d443c082032080c8124010500092014507500400038250720142002118260810020202610121302002203110015001c2031503140d046c042030007480b04a0002e80b042c2c90210502c442d600440d007082c02280e855040d80c000003a110400d84086200307510454803200044011b940c1854080e58515500c160349070000903200c1940c0802c0f0000a81720421030221010180811052000760301c50040034105000c2c2d0828140e444804d00e8500d4030191901811192507401c2045000611781c04035006000c1c05070250b00f541d60365030005454400c0b480b030800d07059410501e80680c1c42c01d041c0b14403012180010300404400e00c0391070610005080300702098a03522a0340341c01180d02c080d0ba40400804c103411100708070040c40e050900506e03440310042c0f41c2c1a41824a800e010070301500e0b809407121406103407031850540d1078 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 744964028 1106 744962922 744962929
    0x60609030204050615030a0902041103072003070c0909050c0f0604180605040204061716020a03080c09100504090c0e0a300b01170f1209 60
    0x2181040000d032a040d080b5540020019010400030350101c400b0303202d9130f80200c4105440649500e4000114180b0b889401100d0f4002071582c0d0450900c00c3c8001c0c400710928031098102409040c3c032544000080c400c80e641594400c5aa40c1056681c2549502401403503005442c10300584541d0482c900b0401c00d0751301d1021004241900d8941030034441a00c24001850211800d43d452401280e2071302c49100800c0034152a0f16004511007003030b641040c0c0d88200402d8188403100706032040d05041c5c0c00003903c0c4503035645818680c4040e0f441d41c0364504d40e40a9034080a601c20015241600102e4000c1e00800a884510b030061102200740c200c107944d0042e0800700e00c0d8214007600020400c264548030060f01c020f400300301350080264010000d06002880400c10348111060900410000b9a0003000d15084106200504108120f10119584800b1050540c203802c06002410b054240d6 = true := by decide +kernel

theorem cover : BRFrame.Cov 744784172 744964028 := by
  have h0 := BRFrame.cov_init 744784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 744784172 ≤ n) (h2 : n < 744964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
